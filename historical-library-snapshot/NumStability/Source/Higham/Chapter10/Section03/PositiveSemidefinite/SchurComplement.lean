import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter10 Section03 PositiveSemidefinite SchurComplement

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyPSD` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Schur complement** of the (1,1) block in a partitioned matrix.

    For a matrix partitioned as [A₁₁ A₁₂; A₂₁ A₂₂]:
      S_k(A) = A₂₂ − A₂₁ A₁₁⁻¹ A₁₂

    We represent this abstractly: given A₁₁⁻¹ as a hypothesis,
    the Schur complement maps indices (i, j) with i, j ≥ k to:
      S(i,j) = A(i,j) − ∑_{s<k} ∑_{t<k} A(i,s) · A₁₁⁻¹(s,t) · A(t,j) -/
noncomputable def schurComplement (n k : ℕ) (A A11_inv : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => A i j -
    ∑ s : Fin n, ∑ t : Fin n,
      (if s.val < k ∧ t.val < k then A i s * A11_inv s t * A t j else 0)

/-- **Resolvent identity for the perturbed leading block** (Lemma 10.10
    setup): if `M` is a left inverse of `A₁₁` and `X` a right... — more
    precisely, if `M * A₁₁ = 1` and `(A₁₁ + E₁₁) * X = 1`, then
    `X = M − M E₁₁ X` exactly. This is the identity that makes the
    Schur-complement perturbation expansion pure algebra. -/
lemma schur_resolvent_from_inverses {k : ℕ}
    (M X A11 E11 : Matrix (Fin k) (Fin k) ℝ)
    (hM : M * A11 = 1) (hXi : (A11 + E11) * X = 1) :
    X = M - M * E11 * X := by
  have h : M * ((A11 + E11) * X) = M := by rw [hXi, mul_one]
  rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc, hM,
    Matrix.one_mul, ← Matrix.mul_assoc] at h
  linear_combination (norm := abel) h

/-- **First-order split of the perturbed Schur complement** (Lemma 10.10
    engine): with the perturbed leading-block inverse written as
    `X = M − Y`, the perturbed Schur complement decomposes exactly into
    the unperturbed one, the `E`-linear part, and a remainder carrying
    `Y` (which is second order once `Y = M E₁₁ X`). -/
lemma schur_perturbation_split {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (M X Y : Matrix (Fin k) (Fin k) ℝ) (hX : X = M - Y) :
    (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
      ((A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12)
        + (-(E21 * M * E12) + (A21 + E21) * Y * (A12 + E12))) := by
  subst hX
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.mul_assoc]
  abel

/-- **One re-expansion of the resolvent inside the remainder**: the
    leading remainder term regains Higham's second-order form. -/
lemma schur_remainder_reexpand {k m : ℕ}
    (A21 : Matrix (Fin m) (Fin k) ℝ) (A12 : Matrix (Fin k) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (hX : X = M - M * E11 * X) :
    A21 * (M * E11 * X) * A12 =
      A21 * (M * E11 * M) * A12
        - A21 * (M * E11 * (M * E11 * X)) * A12 := by
  conv_lhs => rw [hX]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- **Lemma 10.10, exact form (display (10.16))**: for the perturbed
    block matrix `A + E` with leading-block inverses related by the
    resolvent identity (`schur_resolvent_from_inverses`), the perturbed
    Schur complement equals the unperturbed one plus Higham's
    first-order term
    `Ē = E₂₂ − E₂₁ M A₁₂ − A₂₁ M E₁₂ + A₂₁ M E₁₁ M A₁₂`
    (with `W = M A₁₂`, `Wᵀ = A₂₁ M` for symmetric `A` this is
    `E₂₂ − E₂₁ W − Wᵀ E₁₂ + Wᵀ E₁₁ W`) plus an explicit remainder in
    which every term carries two `E`-factors — the `O(‖E‖²)` of the
    source, here exact rather than asymptotic. -/
theorem schur_perturbation_exact {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (hX : X = M - M * E11 * X) :
    (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
      (A22 - A21 * M * A12)
      + (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
      + (-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) := by
  rw [schur_perturbation_split A21 E21 A12 E12 A22 E22 M X
    (M * E11 * X) hX]
  have hre := schur_remainder_reexpand A21 A12 M X E11 hX
  simp only [Matrix.add_mul, Matrix.mul_add] at *
  rw [hre]
  abel

/-- Entrywise bound for a matrix product from entrywise bounds on the
    factors. -/
lemma entrywise_matMul_le {a b c : ℕ}
    (F : Matrix (Fin a) (Fin b) ℝ) (G : Matrix (Fin b) (Fin c) ℝ)
    (f g : ℝ) (hf : 0 ≤ f)
    (hF : ∀ i j, |F i j| ≤ f) (hG : ∀ i j, |G i j| ≤ g) :
    ∀ (i : Fin a) (j : Fin c), |(F * G) i j| ≤ (b : ℝ) * f * g := by
  intro i j
  rw [Matrix.mul_apply]
  calc |∑ s : Fin b, F i s * G s j|
      ≤ ∑ s : Fin b, |F i s * G s j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _s : Fin b, f * g := Finset.sum_le_sum fun s _ => by
        rw [abs_mul]
        exact mul_le_mul (hF i s) (hG s j) (abs_nonneg _) hf
    _ = (b : ℝ) * (f * g) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ = (b : ℝ) * f * g := by ring

/-- **Lemma 10.10, second-order remainder bound**: the exact remainder of
    `schur_perturbation_exact` is entrywise `O(ε²)` — bounded by an
    explicit polynomial in the entrywise bounds `α` (of the off-diagonal
    blocks of `A`), `μ` (of `M = A₁₁⁻¹`), `χ` (of the perturbed inverse
    `X`), times `ε²`. This is the honest content of the source's
    `O(‖E‖²)`. -/
theorem schur_perturbation_remainder_bound {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ)
    (α μ χ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) (hX : ∀ i j, |X i j| ≤ χ) :
    ∀ (i j : Fin m),
      |(-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) i j| ≤
      ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
        + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
        * ε ^ 2 := by
  intro i j
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  -- entrywise bounds on the building blocks
  have hME : ∀ (p q : Fin k), |(M * E11) p q| ≤ (k : ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE11
  have hMEnn : (0 : ℝ) ≤ (k : ℝ) * μ * ε := by positivity
  have hMEX : ∀ (p q : Fin k), |((M * E11) * X) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * χ :=
    entrywise_matMul_le (M * E11) X _ χ hMEnn hME hX
  have hMEXnn : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) * μ * ε) * χ := by
    positivity
  -- term 1 : E21 * M * E12
  have hT1a : ∀ (p : Fin m) (q : Fin k), |(E21 * M) p q| ≤
      (k : ℝ) * ε * μ := entrywise_matMul_le E21 M ε μ hε hE21 hM
  have hT1 : ∀ (p q : Fin m), |((E21 * M) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * μ) * ε :=
    entrywise_matMul_le (E21 * M) E12 _ ε (by positivity) hT1a hE12
  -- term 2 : A21 * (M*E11*(M*E11*X)) * A12
  have hInner : ∀ (p q : Fin k), |((M * E11) * ((M * E11) * X)) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le (M * E11) ((M * E11) * X) _ _ hMEnn hME hMEX
  have hT2a : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * ((M * E11) * X))) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
        ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hInner
  have hT2 : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * ((M * E11) * X))) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
        ((k : ℝ) * ((k : ℝ) * μ * ε) * χ))) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT2a hA12
  -- term 3 : E21 * (M*E11*X) * A12
  have hT3a : ∀ (p : Fin m) (q : Fin k),
      |(E21 * ((M * E11) * X)) p q| ≤
      (k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le E21 _ ε _ hε hE21 hMEX
  have hT3 : ∀ (p q : Fin m),
      |((E21 * ((M * E11) * X)) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT3a hA12
  -- term 4 : A21 * (M*E11*X) * E12
  have hT4a : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * X)) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hMEX
  have hT4 : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * X)) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε :=
    entrywise_matMul_le _ E12 _ ε (by positivity) hT4a hE12
  -- term 5 : E21 * (M*E11*X) * E12
  have hT5 : ∀ (p q : Fin m),
      |((E21 * ((M * E11) * X)) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε :=
    entrywise_matMul_le _ E12 _ ε (by positivity) hT3a hE12
  -- assemble by the triangle inequality
  have h1 := abs_le.mp (hT1 i j)
  have h2 := abs_le.mp (hT2 i j)
  have h3 := abs_le.mp (hT3 i j)
  have h4 := abs_le.mp (hT4 i j)
  have h5 := abs_le.mp (hT5 i j)
  have hsum : ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
      + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
      * ε ^ 2 =
      (k : ℝ) * ((k : ℝ) * ε * μ) * ε
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) *
          ((k : ℝ) * ((k : ℝ) * μ * ε) * χ))) * α
      + (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * α
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε
      + (k : ℝ) * ((k : ℝ) * ε * ((k : ℝ) * ((k : ℝ) * μ * ε) * χ)) * ε
      := by ring
  rw [hsum]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2,
    h4.1, h4.2, h5.1, h5.2]

/-- PSD diagonal entries are nonnegative (general-`n` public form). -/
lemma isPosSemiDef_diag_nonneg {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (i : Fin n) : 0 ≤ A i i := by
  have h := hPSD.2 (fun k => if k = i then 1 else 0)
  simpa [Finset.sum_ite_eq', Finset.mul_sum] using h

/-- **Entrywise bound on Higham's first-order term**: with entrywise
    data `|E| ≤ ε`, `|A₂₁|, |A₁₂| ≤ α`, `|M| ≤ μ`, the first-order term
    of (10.16) satisfies `|Ē i j| ≤ ε (1 + k²αμ)²` — the source's
    `(1 + ‖W‖)²` shape with `k²αμ` the entrywise scale of
    `W = M A₁₂`. -/
lemma schur_first_order_entrywise_bound {k m : ℕ}
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (E22 : Matrix (Fin m) (Fin m) ℝ)
    (M E11 : Matrix (Fin k) (Fin k) ℝ)
    (α μ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε) (hE22 : ∀ i j, |E22 i j| ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) :
    ∀ (i j : Fin m),
      |(E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12) i j| ≤
      ε * (1 + (k : ℝ) ^ 2 * α * μ) ^ 2 := by
  intro i j
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT1 : ∀ (p : Fin m) (q : Fin k), |(E21 * M) p q| ≤
      (k : ℝ) * ε * μ := entrywise_matMul_le E21 M ε μ hε hE21 hM
  have hT1' : ∀ (p q : Fin m), |((E21 * M) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * ε * μ) * α :=
    entrywise_matMul_le (E21 * M) A12 _ α (by positivity) hT1 hA12
  have hT2 : ∀ (p : Fin m) (q : Fin k), |(A21 * M) p q| ≤
      (k : ℝ) * α * μ := entrywise_matMul_le A21 M α μ hα hA21 hM
  have hT2' : ∀ (p q : Fin m), |((A21 * M) * E12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * μ) * ε :=
    entrywise_matMul_le (A21 * M) E12 _ ε (by positivity) hT2 hE12
  have hME : ∀ (p q : Fin k), |(M * E11) p q| ≤ (k : ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE11
  have hMEM : ∀ (p q : Fin k), |((M * E11) * M) p q| ≤
      (k : ℝ) * ((k : ℝ) * μ * ε) * μ :=
    entrywise_matMul_le (M * E11) M _ μ (by positivity) hME hM
  have hT3 : ∀ (p : Fin m) (q : Fin k),
      |(A21 * ((M * E11) * M)) p q| ≤
      (k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ) :=
    entrywise_matMul_le A21 _ α _ hα hA21 hMEM
  have hT3' : ∀ (p q : Fin m),
      |((A21 * ((M * E11) * M)) * A12) p q| ≤
      (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ)) * α :=
    entrywise_matMul_le _ A12 _ α (by positivity) hT3 hA12
  have h22 := abs_le.mp (hE22 i j)
  have h1 := abs_le.mp (hT1' i j)
  have h2 := abs_le.mp (hT2' i j)
  have h3 := abs_le.mp (hT3' i j)
  have hgoal : ε * (1 + (k : ℝ) ^ 2 * α * μ) ^ 2 =
      ε + (k : ℝ) * ((k : ℝ) * ε * μ) * α
      + (k : ℝ) * ((k : ℝ) * α * μ) * ε
      + (k : ℝ) * ((k : ℝ) * α * ((k : ℝ) * ((k : ℝ) * μ * ε) * μ)) * α
      := by ring
  rw [hgoal]
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [abs_le]
  constructor <;> linarith [h22.1, h22.2, h1.1, h1.2, h2.1, h2.2,
    h3.1, h3.2]

/-- **Strict diagonal argmax is stable under small perturbations**
    (Lemma 10.11 stage engine): if the pivot choice has gap `δ` and the
    diagonal perturbation is below `δ/2`, the perturbed matrix selects
    the same pivot. -/
lemma strict_argmax_diag_stable {n : ℕ} (A E : Fin n → Fin n → ℝ)
    (p : Fin n) (δ : ℝ)
    (hgap : ∀ i : Fin n, i ≠ p → A i i + δ ≤ A p p)
    (hE : ∀ i : Fin n, |E i i| < δ / 2) :
    ∀ i : Fin n, i ≠ p → A i i + E i i < A p p + E p p := by
  intro i hip
  have h1 := abs_lt.mp (hE i)
  have h2 := abs_lt.mp (hE p)
  have h3 := hgap i hip
  linarith [h1.2, h2.1]

/-- **Deterministic complete-pivoting choice**: the least-index
    maximizer of the diagonal (Lemma 10.11 pivot-sequence
    foundation). -/
noncomputable def diagArgmax {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, A j j ≤ A i i)).min'
    (by
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin n => A i i)
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j => hi j (Finset.mem_univ j)⟩⟩)

/-- The deterministic pivot maximizes the diagonal. -/
lemma diagArgmax_max {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (j : Fin n) : A j j ≤ A (diagArgmax hn A) (diagArgmax hn A) := by
  have hmem := Finset.min'_mem
    (Finset.univ.filter (fun i : Fin n => ∀ j : Fin n, A j j ≤ A i i))
    (by
      obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
        (fun i : Fin n => A i i)
        (Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn))
      exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,
        fun j => hi j (Finset.mem_univ j)⟩⟩)
  exact (Finset.mem_filter.mp hmem).2 j

/-- A strict maximizer is the deterministic pivot. -/
lemma diagArgmax_eq_of_strict {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hstrict : ∀ i : Fin n, i ≠ p → A i i < A p p) :
    diagArgmax hn A = p := by
  by_contra hne
  have hmax := diagArgmax_max hn A p
  exact absurd hmax (not_le.mpr (hstrict _ hne))

/-- **Pivot-choice stability** (Lemma 10.11, single stage, packaged):
    a gap-`δ` complete-pivoting choice is preserved by any diagonal
    perturbation below `δ/2` — both matrices select the same
    deterministic pivot. -/
theorem diagArgmax_stable {n : ℕ} (hn : 0 < n)
    (A E : Fin n → Fin n → ℝ) (p : Fin n) (δ : ℝ)
    (hgap : ∀ i : Fin n, i ≠ p → A i i + δ ≤ A p p)
    (hE : ∀ i : Fin n, |E i i| < δ / 2) :
    diagArgmax hn A = p ∧
    diagArgmax hn (fun i j => A i j + E i j) = p := by
  have hδpos : 0 < δ := by
    have := abs_nonneg (E p p)
    linarith [hE p]
  constructor
  · exact diagArgmax_eq_of_strict hn A p fun i hip => by
      have := hgap i hip
      linarith
  · exact diagArgmax_eq_of_strict hn _ p fun i hip =>
      strict_argmax_diag_stable A E p δ hgap hE i hip

/-- **One complete-pivoting elimination step** (Lemma 10.11 state
    machine): eliminate pivot `p`, zeroing its row and column and
    forming the Schur update on the rest. Dimension is preserved so the
    stage recursion needs no dependent reindexing. -/
noncomputable def schurStep {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else A i j - A i p * A p j / A p p

/-- `schurStep` preserves symmetry. -/
lemma schurStep_symm {n : ℕ} (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i) (i j : Fin n) :
    schurStep A p i j = schurStep A p j i := by
  unfold schurStep
  by_cases hi : i = p
  · by_cases hj : j = p <;> simp [hi, hj]
  · by_cases hj : j = p
    · simp [hi, hj]
    · simp only [hi, hj, or_self, if_false]
      rw [hsym i j, hsym i p, hsym p j]
      ring

/-- **`schurStep` preserves positive semidefiniteness** (the
    completion-of-squares invariant of the Lemma 10.11 stage
    recursion): with a positive pivot, the zeroed Schur update of a PSD
    matrix is PSD — the quadratic form of the update at `x` equals the
    quadratic form of `A` at `x` with the `p`-th coordinate replaced by
    the minimizer `−(∑_{j≠p} a_pj x_j)/a_pp`. -/
lemma schurStep_isPosSemiDef {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (p : Fin n) (hp : 0 < A p p) :
    IsPosSemiDef n (schurStep A p) := by
  refine ⟨schurStep_symm A p hPSD.1, ?_⟩
  intro x
  set d : ℝ := A p p with hd
  set u : ℝ := ∑ j ∈ Finset.univ.erase p, A p j * x j with hu
  set z : Fin n → ℝ := fun i => if i = p then -u / d else x i with hz
  -- the quadratic form of the update, reduced to the erased square
  have hSquad : ∑ i : Fin n, ∑ j : Fin n,
      x i * schurStep A p i j * x j =
      ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * (A i j - A i p * A p j / d) * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrow : ∑ j : Fin n, x p * schurStep A p p j * x j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        unfold schurStep; simp
    rw [hrow, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hip : i ≠ p := Finset.ne_of_mem_erase hi
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hcol : x i * schurStep A p i p * x p = 0 := by
      unfold schurStep; simp
    rw [hcol, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjp : j ≠ p := Finset.ne_of_mem_erase hj
    unfold schurStep
    simp [hip, hjp, ← hd]
  -- the quadratic form of A at the completed vector z
  have hAquad : ∑ i : Fin n, ∑ j : Fin n, z i * A i j * z j =
      (-u / d) * d * (-u / d) + (-u / d) * u + u * (-u / d) +
      ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * A i j * x j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
    have hrowp : ∑ j : Fin n, z p * A p j * z j =
        (-u / d) * d * (-u / d) + (-u / d) * u := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
      have hzp : z p = -u / d := by simp [hz]
      have htail : ∑ j ∈ Finset.univ.erase p, z p * A p j * z j =
          (-u / d) * u := by
        rw [hu, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        rw [hzp]
        simp only [hz, hjp, if_false]
        ring
      rw [htail, hzp, hd]
    rw [hrowp]
    have hrest : ∑ i ∈ Finset.univ.erase p,
        ∑ j : Fin n, z i * A i j * z j =
        u * (-u / d) + ∑ i ∈ Finset.univ.erase p,
          ∑ j ∈ Finset.univ.erase p, x i * A i j * x j := by
      have hsw : ∀ i ∈ Finset.univ.erase p,
          ∑ j : Fin n, z i * A i j * z j =
          x i * A i p * (-u / d) +
          ∑ j ∈ Finset.univ.erase p, x i * A i j * x j := by
        intro i hi
        have hip : i ≠ p := Finset.ne_of_mem_erase hi
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)]
        have hzi : z i = x i := by simp [hz, hip]
        have hzp : z p = -u / d := by simp [hz]
        rw [hzi, hzp]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        have hjp : j ≠ p := Finset.ne_of_mem_erase hj
        simp [hz, hjp]
      rw [Finset.sum_congr rfl hsw, Finset.sum_add_distrib]
      congr 1
      have : ∑ i ∈ Finset.univ.erase p, x i * A i p * (-u / d) =
          (∑ i ∈ Finset.univ.erase p, A p i * x i) * (-u / d) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hPSD.1 i p]
        ring
      rw [this]
    rw [hrest]
    ring
  -- the cross term collapses: quadForm S x = quadForm A z
  have hfactor : ∑ i ∈ Finset.univ.erase p,
      ∑ j ∈ Finset.univ.erase p,
        x i * (A i p * A p j / d) * x j = u * u / d := by
    have hsep : ∀ i ∈ Finset.univ.erase p,
        ∑ j ∈ Finset.univ.erase p,
          x i * (A i p * A p j / d) * x j =
        (A p i * x i / d) * u := by
      intro i hi
      rw [hu, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hPSD.1 i p]
      ring
    rw [Finset.sum_congr rfl hsep, ← Finset.sum_mul,
      ← Finset.sum_div, ← hu]
    ring
  have hkey : ∑ i : Fin n, ∑ j : Fin n,
      x i * schurStep A p i j * x j =
      ∑ i : Fin n, ∑ j : Fin n, z i * A i j * z j := by
    rw [hSquad, hAquad]
    have hsub : ∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
        x i * (A i j - A i p * A p j / d) * x j =
        (∑ i ∈ Finset.univ.erase p, ∑ j ∈ Finset.univ.erase p,
          x i * A i j * x j) - u * u / d := by
      rw [← hfactor, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsub]
    field_simp
    ring
  rw [hkey]
  exact hPSD.2 z

/-- **The complete-pivoting state machine** (Lemma 10.11): stage `t`'s
    working matrix — `A` eliminated `t` times, each time at the
    deterministic diagonal argmax. -/
noncomputable def cpState {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => schurStep (cpState hn A t)
      (diagArgmax hn (cpState hn A t))

/-- The pivot selected at stage `t`. -/
noncomputable def cpPivot {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (cpState hn A t)

/-- Every complete-pivoting stage is symmetric. -/
lemma cpState_symm {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i) :
    ∀ t : ℕ, ∀ i j : Fin n, cpState hn A t i j = cpState hn A t j i := by
  intro t
  induction t with
  | zero => exact hsym
  | succ t ih => exact schurStep_symm (cpState hn A t) _ ih

/-- **Every complete-pivoting stage is PSD** while the selected pivots
    stay positive (Lemma 10.11 stage invariant). -/
lemma cpState_isPosSemiDef {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) (t : ℕ)
    (hpiv : ∀ s : ℕ, s < t →
      0 < cpState hn A s (cpPivot hn A s) (cpPivot hn A s)) :
    IsPosSemiDef n (cpState hn A t) := by
  induction t with
  | zero => exact hPSD
  | succ t ih =>
    exact schurStep_isPosSemiDef (cpState hn A t)
      (ih fun s hs => hpiv s (Nat.lt_succ_of_lt hs)) _
      (hpiv t (Nat.lt_succ_self t))

/-- **The selected pivot dominates the whole working diagonal** —
    what complete pivoting means at each stage. -/
lemma cpPivot_max {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (t : ℕ) (j : Fin n) :
    cpState hn A t j j ≤
      cpState hn A t (cpPivot hn A t) (cpPivot hn A t) :=
  diagArgmax_max hn (cpState hn A t) j

/-- **Entrywise perturbation of one elimination step** (Lemma 10.11
    propagation engine): if `A` and `B` agree entrywise to `ε`, `A` has
    entry cap `c`, and both share the pivot floor `ρ > 0` at `p`, the
    eliminated matrices agree to `ε + (3c²ε + cε²)/ρ²`. Iterating this
    bound across stages propagates a diagonal gap through the
    complete-pivoting recursion. -/
lemma schurStep_entrywise_perturbation {n : ℕ}
    (A B : Fin n → Fin n → ℝ) (p : Fin n) (ε c ρ : ℝ)
    (hε : 0 ≤ ε) (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hAB : ∀ i j : Fin n, |A i j - B i j| ≤ ε)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hdA : ρ ≤ A p p) (hdB : ρ ≤ B p p) :
    ∀ i j : Fin n, |schurStep A p i j - schurStep B p i j| ≤
      ε + (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
  intro i j
  have hrhs0 : (0:ℝ) ≤ ε + (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
    positivity
  by_cases hij : i = p ∨ j = p
  · unfold schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold schurStep
    rw [if_neg hij, if_neg hij]
    have hdA0 : (0:ℝ) < A p p := lt_of_lt_of_le hρ hdA
    have hdB0 : (0:ℝ) < B p p := lt_of_lt_of_le hρ hdB
    -- common-denominator form of the update difference
    have hkey : A i p * A p j / A p p - B i p * B p j / B p p =
        (A i p * A p j * (B p p - A p p)
          + A p p * (A i p * (A p j - B p j)
            + (A i p - B i p) * B p j)) / (A p p * B p p) := by
      field_simp
      ring
    -- numerator and denominator bounds
    have hBpj : |B p j| ≤ c + ε := by
      have h1 := hAB p j
      have h2 := hcap p j
      have := abs_sub_abs_le_abs_sub (B p j) (A p j)
      rw [abs_sub_comm (B p j) (A p j)] at this
      linarith [this, h1, h2]
    have hnum : |A i p * A p j * (B p p - A p p)
        + A p p * (A i p * (A p j - B p j)
          + (A i p - B i p) * B p j)| ≤
        3 * c ^ 2 * ε + c * ε ^ 2 := by
      have h1 : |A i p * A p j * (B p p - A p p)| ≤ c * c * ε := by
        rw [abs_mul, abs_mul, abs_sub_comm]
        exact mul_le_mul (mul_le_mul (hcap i p) (hcap p j)
          (abs_nonneg _) hc) (hAB p p)
          (abs_nonneg _) (by positivity)
      have h2 : |A i p * (A p j - B p j)| ≤ c * ε := by
        rw [abs_mul]
        exact mul_le_mul (hcap i p) (hAB p j) (abs_nonneg _) hc
      have h3 : |(A i p - B i p) * B p j| ≤ ε * (c + ε) := by
        rw [abs_mul]
        exact mul_le_mul (hAB i p) hBpj (abs_nonneg _) hε
      have h4 : |A p p * (A i p * (A p j - B p j)
          + (A i p - B i p) * B p j)| ≤ c * (c * ε + ε * (c + ε)) := by
        rw [abs_mul]
        refine mul_le_mul (hcap p p) ?_ (abs_nonneg _) hc
        calc |A i p * (A p j - B p j) + (A i p - B i p) * B p j|
            ≤ |A i p * (A p j - B p j)| + |(A i p - B i p) * B p j| :=
              abs_add_le _ _
          _ ≤ c * ε + ε * (c + ε) := add_le_add h2 h3
      calc |A i p * A p j * (B p p - A p p)
          + A p p * (A i p * (A p j - B p j)
            + (A i p - B i p) * B p j)|
          ≤ |A i p * A p j * (B p p - A p p)|
            + |A p p * (A i p * (A p j - B p j)
              + (A i p - B i p) * B p j)| := abs_add_le _ _
        _ ≤ c * c * ε + c * (c * ε + ε * (c + ε)) := add_le_add h1 h4
        _ = 3 * c ^ 2 * ε + c * ε ^ 2 := by ring
    have hden : ρ ^ 2 ≤ A p p * B p p := by nlinarith
    have hquot : |A i p * A p j / A p p - B i p * B p j / B p p| ≤
        (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
      rw [hkey, abs_div, abs_of_pos (mul_pos hdA0 hdB0)]
      calc |A i p * A p j * (B p p - A p p)
            + A p p * (A i p * (A p j - B p j)
              + (A i p - B i p) * B p j)| / (A p p * B p p)
          ≤ (3 * c ^ 2 * ε + c * ε ^ 2) / (A p p * B p p) := by
            gcongr
        _ ≤ (3 * c ^ 2 * ε + c * ε ^ 2) / ρ ^ 2 := by
            gcongr

    -- assemble with the direct entry difference
    have hsplit : A i j - A i p * A p j / A p p -
        (B i j - B i p * B p j / B p p) =
        (A i j - B i j) -
        (A i p * A p j / A p p - B i p * B p j / B p p) := by ring
    rw [hsplit]
    have h1 := abs_le.mp (hAB i j)
    have h2 := abs_le.mp hquot
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- **Lemma 10.11 (no-tie pivot-sequence stability), full stage
    induction**: if every stage `t < r` of the exact complete-pivoting
    recursion on `A` has diagonal gap `δ`, pivot floor `ρ ≥ δ`, and
    entry cap `c`, and the error budget `g` absorbs the one-stage
    growth `ε ↦ ε + (3c²ε + cε²)/(ρ/2)²` while staying below `δ/2`,
    then a perturbed matrix `B` within `ε₀ ≤ g 0` of `A` selects the
    SAME pivot sequence through `r` stages, with stage states
    `g`-close. -/
theorem cpPivot_sequence_stable {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) (r : ℕ)
    (ε₀ δ ρ c : ℝ) (hε₀ : 0 ≤ ε₀) (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (hc : 0 ≤ c) (g : ℕ → ℝ) (hg0 : ε₀ ≤ g 0)
    (hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤ g (t + 1))
    (hghalf : ∀ t : ℕ, t < r → g t < δ / 2)
    (hAB : ∀ i j : Fin n, |A i j - B i j| ≤ ε₀)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - cpState hn B t i j| ≤ g t) ∧
      (∀ s : ℕ, s < t → cpPivot hn A s = cpPivot hn B s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  -- the budget is nonnegative along the run
  have hg_nonneg : ∀ t : ℕ, t ≤ r → 0 ≤ g t := by
    intro t
    induction t with
    | zero => intro _; linarith
    | succ t iht =>
      intro htr
      have ht' : t < r := Nat.lt_of_succ_le htr
      have h0 := iht (Nat.le_of_lt ht')
      have hstep := hgstep t ht'
      have hadd : (0:ℝ) ≤
          (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      linarith
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨fun i j => (hAB i j).trans hg0,
      fun s hs => absurd hs (Nat.not_lt_zero s)⟩
  | succ t ih =>
    intro htr
    have ht' : t < r := Nat.lt_of_succ_le htr
    obtain ⟨hdiff, hpiv⟩ := ih (Nat.le_of_lt ht')
    set p : Fin n := cpPivot hn A t with hp
    -- perturbed stage selects the same pivot
    set Et : Fin n → Fin n → ℝ :=
      fun i j => cpState hn B t i j - cpState hn A t i j with hEt
    have hEdiag : ∀ i : Fin n, |Et i i| < δ / 2 := by
      intro i
      have h := hdiff i i
      rw [abs_sub_comm] at h
      exact lt_of_le_of_lt h (hghalf t ht')
    have hstable := diagArgmax_stable hn (cpState hn A t) Et p δ
      (hgap t ht') hEdiag
    have hBfun : (fun i j => cpState hn A t i j + Et i j) =
        cpState hn B t := by
      funext i j
      simp [hEt]
    have hpivB : cpPivot hn B t = p := by
      show diagArgmax hn (cpState hn B t) = p
      rw [← hBfun]
      exact hstable.2
    -- one-stage error growth at the shared pivot
    have hAfloor : ρ / 2 ≤ cpState hn A t p p := by
      have := hfloor t ht'
      linarith
    have hBfloor : ρ / 2 ≤ cpState hn B t p p := by
      have h1 := hEdiag p
      have h2 := abs_lt.mp h1
      have h3 := hfloor t ht'
      have h4 : cpState hn B t p p =
          cpState hn A t p p + Et p p := by simp [hEt]
      rw [h4]
      linarith [h2.1, hδρ]
    have hstep := schurStep_entrywise_perturbation
      (cpState hn A t) (cpState hn B t) p (g t) c (ρ / 2)
      (hg_nonneg t (Nat.le_of_lt ht')) hc (by linarith)
      hdiff (hcap t ht') hAfloor hBfloor
    constructor
    · intro i j
      have hSA : cpState hn A (t + 1) =
          schurStep (cpState hn A t) p := rfl
      have hSB : cpState hn B (t + 1) =
          schurStep (cpState hn B t) p := by
        show schurStep (cpState hn B t) (cpPivot hn B t) =
          schurStep (cpState hn B t) p
        rw [hpivB]
      rw [hSA, hSB]
      exact (hstep i j).trans (hgstep t ht')
    · intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with h' | h'
      · exact hpiv s h'
      · subst h'
        rw [hpivB]

/-- **Lemma 10.11, source form**: a matrix whose complete-pivoting run
    has no ties (gap `δ`, floor `ρ`, cap `c` through `r` stages) admits
    a positive perturbation radius within which every matrix selects
    the same pivot sequence — the "for sufficiently small `E`"
    statement, instantiating `cpPivot_sequence_stable` with the
    geometric budget `g t = ε₀ K^t`, `K = 1 + (3c² + c)/(ρ/2)²`. -/
theorem cpPivot_sequence_stable_small {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ B : Fin n → Fin n → ℝ,
        (∀ i j : Fin n, |A i j - B i j| ≤ ε₀) →
        ∀ s : ℕ, s < r → cpPivot hn A s = cpPivot hn B s := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  set K : ℝ := 1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2 with hK
  have hK1 : (1:ℝ) ≤ K := by
    have : (0:ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by positivity
    linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  have hKr : (0:ℝ) < K ^ r := pow_pos hK0 r
  set ε₀ : ℝ := min 1 (δ / 2) / (2 * K ^ r) with hε₀def
  have hmin0 : (0:ℝ) < min 1 (δ / 2) :=
    lt_min one_pos (by linarith)
  have hε₀pos : 0 < ε₀ := by
    rw [hε₀def]
    positivity
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro B hAB
  set g : ℕ → ℝ := fun t => ε₀ * K ^ t with hg
  -- geometric budget stays below both 1 and δ/2 through the run
  have hgle : ∀ t : ℕ, t ≤ r → g t ≤ min 1 (δ / 2) / 2 := by
    intro t htr
    have hpow : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    have : g t = ε₀ * K ^ t := rfl
    rw [this, hε₀def]
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity)
      (by norm_num : (0:ℝ) < 2)]
    calc min 1 (δ / 2) * K ^ t * 2
        ≤ min 1 (δ / 2) * K ^ r * 2 := by
          have := hmin0.le
          nlinarith
      _ = min 1 (δ / 2) * (2 * K ^ r) := by ring
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := by
    intro t htr
    have h := hgle t (Nat.le_of_lt htr)
    have h1 : min 1 (δ / 2) ≤ 1 := min_le_left _ _
    linarith
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := by
    intro t htr
    have h := hgle t (Nat.le_of_lt htr)
    have h1 : min 1 (δ / 2) ≤ δ / 2 := min_le_right _ _
    linarith [hmin0]
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    have : g t = ε₀ * K ^ t := rfl
    rw [this]
    positivity
  -- the geometric budget absorbs the one-stage growth
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        g (t + 1) := by
    intro t htr
    have hgt1 := hg1 t htr
    have hgt0 := hg_nonneg t
    have hstep : g (t + 1) = g t * K := by
      show ε₀ * K ^ (t + 1) = ε₀ * K ^ t * K
      ring
    rw [hstep, hK]
    have hexp : g t * (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) =
        g t + (3 * c ^ 2 * g t + c * g t) / (ρ / 2) ^ 2 := by
      field_simp
    rw [hexp]
    gcongr
    nlinarith
  have hmain := cpPivot_sequence_stable hn A B r ε₀ δ ρ c
    hε₀pos.le hδ hδρ hc g
    (by
      show ε₀ ≤ ε₀ * K ^ 0
      simp)
    hgstep hghalf hAB hgap hfloor hcap
  intro s hs
  exact (hmain r le_rfl).2 s hs

/-- **Floating-point elimination step** (Theorem 10.14 pivoted-trace
    route): the fl-arithmetic analogue of `schurStep` — one Schur
    update computed with rounded multiply, divide, and subtract. -/
noncomputable def fl_schurStep (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else fp.fl_sub (A i j) (fp.fl_div (fp.fl_mul (A i p) (A p j)) (A p p))

/-- **One-stage fl-vs-exact proximity**: with entry cap `c` and pivot
    floor `ρ > 0`, the floating-point elimination step is entrywise
    within `u(c + c²/ρ) + (c²/ρ)(2u + u²)(1 + u)` of the exact one —
    the seed of the induction that transfers the exact complete-pivoting
    invariants (pivot sequence via Lemma 10.11, tail domination via
    (10.13)) to the computed factor. -/
theorem fl_schurStep_close (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hfloor : ρ ≤ A p p) :
    ∀ i j : Fin n, |fl_schurStep fp A p i j - schurStep A p i j| ≤
      fp.u * (c + c ^ 2 / ρ) +
        (c ^ 2 / ρ) * (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by
  intro i j
  have hu0 := fp.u_nonneg
  have hrhs0 : (0:ℝ) ≤ fp.u * (c + c ^ 2 / ρ) +
      (c ^ 2 / ρ) * (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by
    positivity
  by_cases hij : i = p ∨ j = p
  · unfold fl_schurStep schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold fl_schurStep schurStep
    rw [if_neg hij, if_neg hij]
    have hd0 : A p p ≠ 0 := (lt_of_lt_of_le hρ hfloor).ne'
    have hdpos : (0:ℝ) < A p p := lt_of_lt_of_le hρ hfloor
    obtain ⟨δ₁, hδ₁, hmul⟩ := fp.model_mul (A i p) (A p j)
    obtain ⟨δ₂, hδ₂, hdiv⟩ := fp.model_div
      (fp.fl_mul (A i p) (A p j)) (A p p) hd0
    obtain ⟨δ₃, hδ₃, hsub⟩ := fp.model_sub (A i j)
      (fp.fl_div (fp.fl_mul (A i p) (A p j)) (A p p))
    rw [hsub, hdiv, hmul]
    -- the quotient magnitude is capped by c²/ρ
    have hquot : |A i p * A p j / A p p| ≤ c ^ 2 / ρ := by
      rw [abs_div, abs_of_pos hdpos]
      have hnum : |A i p * A p j| ≤ c ^ 2 := by
        rw [abs_mul]
        calc |A i p| * |A p j| ≤ c * c :=
              mul_le_mul (hcap i p) (hcap p j) (abs_nonneg _) hc
          _ = c ^ 2 := by ring
      calc |A i p * A p j| / A p p ≤ c ^ 2 / A p p := by gcongr
        _ ≤ c ^ 2 / ρ := by gcongr
    have hS : |A i j - A i p * A p j / A p p| ≤ c + c ^ 2 / ρ := by
      calc |A i j - A i p * A p j / A p p|
          ≤ |A i j| + |A i p * A p j / A p p| := by
            have h := abs_add_le (A i j) (-(A i p * A p j / A p p))
            rw [abs_neg, ← sub_eq_add_neg] at h
            exact h
        _ ≤ c + c ^ 2 / ρ := add_le_add (hcap i j) hquot
    -- algebraic form of the error
    have hexpand : (A i j - A i p * A p j * (1 + δ₁) / A p p * (1 + δ₂))
          * (1 + δ₃) - (A i j - A i p * A p j / A p p) =
        (A i j - A i p * A p j / A p p) * δ₃ -
        A i p * A p j / A p p *
          ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃)) := by
      field_simp
      ring
    rw [hexpand]
    have herr : |(1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃)| ≤
        (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by
      have h1 : (1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃) =
          (δ₁ + δ₂ + δ₁ * δ₂) * (1 + δ₃) := by ring
      rw [h1, abs_mul]
      have h2 : |δ₁ + δ₂ + δ₁ * δ₂| ≤ 2 * fp.u + fp.u ^ 2 := by
        have ha := abs_le.mp hδ₁
        have hb := abs_le.mp hδ₂
        have hab : |δ₁ * δ₂| ≤ fp.u ^ 2 := by
          rw [abs_mul]
          calc |δ₁| * |δ₂| ≤ fp.u * fp.u :=
                mul_le_mul hδ₁ hδ₂ (abs_nonneg _) hu0
            _ = fp.u ^ 2 := by ring
        have hab' := abs_le.mp hab
        rw [abs_le]
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2,
          hab'.1, hab'.2]
      have h3 : |1 + δ₃| ≤ 1 + fp.u := by
        have := abs_le.mp hδ₃
        rw [abs_le]
        constructor <;> linarith [this.1, this.2, hu0]
      exact mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
    calc |(A i j - A i p * A p j / A p p) * δ₃ -
          A i p * A p j / A p p *
            ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃))|
        ≤ |(A i j - A i p * A p j / A p p) * δ₃| +
          |A i p * A p j / A p p *
            ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃))| := by
          have h := abs_add_le
            ((A i j - A i p * A p j / A p p) * δ₃)
            (-(A i p * A p j / A p p *
              ((1 + δ₁) * (1 + δ₂) * (1 + δ₃) - (1 + δ₃))))
          rw [abs_neg, ← sub_eq_add_neg] at h
          exact h
      _ ≤ (c + c ^ 2 / ρ) * fp.u +
          (c ^ 2 / ρ) * ((2 * fp.u + fp.u ^ 2) * (1 + fp.u)) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]
            exact mul_le_mul hS hδ₃ (abs_nonneg _) (by positivity)
          · rw [abs_mul]
            exact mul_le_mul hquot herr (abs_nonneg _) (by positivity)
      _ = fp.u * (c + c ^ 2 / ρ) +
          (c ^ 2 / ρ) * (2 * fp.u + fp.u ^ 2) * (1 + fp.u) := by ring

/-- **The floating-point complete-pivoting trace**: iterate the fl
    elimination step, choosing each pivot as the argmax of the
    *computed* working diagonal — the algorithm as actually run. -/
noncomputable def fl_cpState (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => fl_schurStep fp (fl_cpState fp hn A t)
      (diagArgmax hn (fl_cpState fp hn A t))

/-- The pivot the floating-point run selects at stage `t`. -/
noncomputable def fl_cpPivot (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (fl_cpState fp hn A t)

/-- **The floating-point run follows the exact pivot sequence**
    (Theorem 10.14 `c`/`η` discharge, stage induction): if the exact
    complete-pivoting trace has gap `δ`, floor `ρ ≥ δ`, cap `c` through
    `r` stages, and the budget `h` starts at `0`, absorbs per stage the
    exact-perturbation growth plus the one-stage rounding contribution
    `U = u(c' + c'²/(ρ/2)) + (c'²/(ρ/2))(2u + u²)(1 + u)` with
    `c' = c + δ/2`, and stays below `δ/2`, then the computed trace
    selects the SAME pivots as exact complete pivoting through `r`
    stages, with working matrices `h`-close throughout. -/
theorem fl_cpPivot_sequence_agrees (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) ≤ h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpState fp hn A t i j| ≤ h t) ∧
      (∀ s : ℕ, s < t → cpPivot hn A s = fl_cpPivot fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hh_nonneg : ∀ t : ℕ, t ≤ r → 0 ≤ h t := by
    intro t
    induction t with
    | zero => intro _; rw [hh0]
    | succ t iht =>
      intro htr
      have ht' : t < r := Nat.lt_of_succ_le htr
      have h0 := iht (Nat.le_of_lt ht')
      have hstep := hhstep t ht'
      have h1 : (0:ℝ) ≤
          (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2 : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u) := by
        positivity
      linarith
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun i j => ?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
    show |cpState hn A 0 i j - fl_cpState fp hn A 0 i j| ≤ h 0
    show |A i j - A i j| ≤ h 0
    rw [sub_self, abs_zero, hh0]
  | succ t ih =>
    intro htr
    have ht' : t < r := Nat.lt_of_succ_le htr
    obtain ⟨hdiff, hpiv⟩ := ih (Nat.le_of_lt ht')
    have hht0 := hh_nonneg t (Nat.le_of_lt ht')
    set p : Fin n := cpPivot hn A t with hp
    -- the computed stage selects the exact pivot
    set Et : Fin n → Fin n → ℝ :=
      fun i j => fl_cpState fp hn A t i j - cpState hn A t i j
      with hEt
    have hEdiag : ∀ i : Fin n, |Et i i| < δ / 2 := by
      intro i
      have hd := hdiff i i
      rw [abs_sub_comm] at hd
      exact lt_of_le_of_lt hd (hhhalf t ht')
    have hstable := diagArgmax_stable hn (cpState hn A t) Et p δ
      (hgap t ht') hEdiag
    have hFfun : (fun i j => cpState hn A t i j + Et i j) =
        fl_cpState fp hn A t := by
      funext i j
      simp [hEt]
    have hpivF : fl_cpPivot fp hn A t = p := by
      show diagArgmax hn (fl_cpState fp hn A t) = p
      rw [← hFfun]
      exact hstable.2
    -- caps and floors for the computed working matrix
    have hFcap : ∀ i j : Fin n,
        |fl_cpState fp hn A t i j| ≤ c + δ / 2 := by
      intro i j
      have h1 := hdiff i j
      have h2 := hcap t ht' i j
      have h3 := abs_sub_abs_le_abs_sub
        (fl_cpState fp hn A t i j) (cpState hn A t i j)
      rw [abs_sub_comm (fl_cpState fp hn A t i j)
        (cpState hn A t i j)] at h3
      have h4 := hhhalf t ht'
      linarith
    have hAfloor : ρ / 2 ≤ cpState hn A t p p := by
      have := hfloor t ht'
      linarith
    have hFfloor : ρ / 2 ≤ fl_cpState fp hn A t p p := by
      have h1 := hEdiag p
      have h2 := abs_lt.mp h1
      have h3 := hfloor t ht'
      have h4 : fl_cpState fp hn A t p p =
          cpState hn A t p p + Et p p := by simp [hEt]
      rw [h4]
      linarith [h2.1, hδρ]
    -- exact-vs-exact perturbation at the shared pivot
    have hexact := schurStep_entrywise_perturbation
      (cpState hn A t) (fl_cpState fp hn A t) p (h t) c (ρ / 2)
      hht0 hc (by linarith) hdiff (hcap t ht') hAfloor hFfloor
    -- fl-vs-exact rounding at the computed working matrix
    have hround := fl_schurStep_close fp (fl_cpState fp hn A t) p
      (c + δ / 2) (ρ / 2) (by linarith) (by linarith)
      hFcap hFfloor
    constructor
    · intro i j
      have hSA : cpState hn A (t + 1) =
          schurStep (cpState hn A t) p := rfl
      have hSF : fl_cpState fp hn A (t + 1) =
          fl_schurStep fp (fl_cpState fp hn A t) p := by
        show fl_schurStep fp (fl_cpState fp hn A t)
          (diagArgmax hn (fl_cpState fp hn A t)) =
          fl_schurStep fp (fl_cpState fp hn A t) p
        rw [show diagArgmax hn (fl_cpState fp hn A t) =
          fl_cpPivot fp hn A t from rfl, hpivF]
      rw [hSA, hSF]
      have htri : |schurStep (cpState hn A t) p i j -
          fl_schurStep fp (fl_cpState fp hn A t) p i j| ≤
          |schurStep (cpState hn A t) p i j -
            schurStep (fl_cpState fp hn A t) p i j| +
          |fl_schurStep fp (fl_cpState fp hn A t) p i j -
            schurStep (fl_cpState fp hn A t) p i j| := by
        have habs := abs_add_le
          (schurStep (cpState hn A t) p i j -
            schurStep (fl_cpState fp hn A t) p i j)
          (schurStep (fl_cpState fp hn A t) p i j -
            fl_schurStep fp (fl_cpState fp hn A t) p i j)
        rw [sub_add_sub_cancel] at habs
        rw [abs_sub_comm (fl_schurStep fp (fl_cpState fp hn A t) p i j)
          (schurStep (fl_cpState fp hn A t) p i j)]
        exact habs
      calc |schurStep (cpState hn A t) p i j -
            fl_schurStep fp (fl_cpState fp hn A t) p i j|
          ≤ _ + _ := htri
        _ ≤ (h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2) +
            (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
                (1 + fp.u)) :=
            add_le_add (hexact i j) (hround i j)
        _ ≤ h (t + 1) := by
            have := hhstep t ht'
            linarith
    · intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with h' | h'
      · exact hpiv s h'
      · subst h'
        rw [hpivF]

/-- **Factor-form floating-point elimination step** — the update as
    Algorithm 10.2-pivoted actually computes it: divide the pivot row
    and column by the rounded square root of the pivot and subtract
    the product of the computed factor entries. -/
noncomputable def fl_schurStepFactor (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = p ∨ j = p then 0
    else fp.fl_sub (A i j)
      (fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p))))

/-- **Factor-form one-stage proximity**: the √-scaled fl update is
    entrywise within `u(c + c²/ρ) + (1+u)γ₅(c²/ρ)` of the exact Schur
    step — five rounding factors (one shared square root entering
    twice reciprocally, two divides, one multiply) against the sharp
    Stewart-counter bound `γ₅`, plus the final subtraction. -/
theorem fl_schurStepFactor_close (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) (c ρ : ℝ)
    (hc : 0 ≤ c) (hρ : 0 < ρ)
    (hcap : ∀ i j : Fin n, |A i j| ≤ c)
    (hfloor : ρ ≤ A p p) (h5 : gammaValid fp 5) :
    ∀ i j : Fin n,
      |fl_schurStepFactor fp A p i j - schurStep A p i j| ≤
      fp.u * (c + c ^ 2 / ρ) +
        (1 + fp.u) * gamma fp 5 * (c ^ 2 / ρ) := by
  intro i j
  have hu0 := fp.u_nonneg
  have hu1 : fp.u < 1 := by
    unfold gammaValid at h5
    push_cast at h5
    nlinarith
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  have hrhs0 : (0:ℝ) ≤ fp.u * (c + c ^ 2 / ρ) +
      (1 + fp.u) * gamma fp 5 * (c ^ 2 / ρ) := by positivity
  by_cases hij : i = p ∨ j = p
  · unfold fl_schurStepFactor schurStep
    rw [if_pos hij, if_pos hij, sub_zero, abs_zero]
    exact hrhs0
  · unfold fl_schurStepFactor schurStep
    rw [if_neg hij, if_neg hij]
    have hdpos : (0:ℝ) < A p p := lt_of_lt_of_le hρ hfloor
    have hsq : (0:ℝ) < Real.sqrt (A p p) := Real.sqrt_pos.mpr hdpos
    obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (A p p) hdpos.le
    have h1a : (0:ℝ) < 1 + δa := by
      have := abs_le.mp hδa
      linarith [this.1]
    have hfs0 : fp.fl_sqrt (A p p) ≠ 0 := by
      rw [hsqrt]
      positivity
    obtain ⟨δb, hδb, hdivb⟩ := fp.model_div (A i p)
      (fp.fl_sqrt (A p p)) hfs0
    obtain ⟨δc, hδc, hdivc⟩ := fp.model_div (A p j)
      (fp.fl_sqrt (A p p)) hfs0
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul
      (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
      (fp.fl_div (A p j) (fp.fl_sqrt (A p p)))
    obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (A i j)
      (fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p))))
    set C : ℝ := (1 + δb) * (1 + δc) * (1 + δm) /
      ((1 + δa) * (1 + δa)) with hC
    -- the computed product is the exact quotient times the counter C
    have hprod : fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p))) =
        A i p * A p j / A p p * C := by
      rw [hmul, hdivb, hdivc, hsqrt, hC]
      field_simp
      rw [Real.sq_sqrt hdpos.le]
      ring
    -- C is a five-factor Stewart counter
    have hcounter : relErrorCounter fp 5 C := by
      refine ⟨![δb, δc, δm, δa, δa],
        ![false, false, false, true, true], ?_, ?_⟩
      · intro i
        fin_cases i <;> simpa
      · rw [hC, Fin.prod_univ_five]
        norm_num [Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.cons_val_three,
          Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
        field_simp
    have hC1 : |C - 1| ≤ gamma fp 5 :=
      relErrorCounter_abs_sub_one_le_gamma fp 5 C hcounter h5
    -- quotient magnitude and exact-entry magnitude
    have hquot : |A i p * A p j / A p p| ≤ c ^ 2 / ρ := by
      rw [abs_div, abs_of_pos hdpos]
      have hnum : |A i p * A p j| ≤ c ^ 2 := by
        rw [abs_mul]
        calc |A i p| * |A p j| ≤ c * c :=
              mul_le_mul (hcap i p) (hcap p j) (abs_nonneg _) hc
          _ = c ^ 2 := by ring
      calc |A i p * A p j| / A p p ≤ c ^ 2 / A p p := by gcongr
        _ ≤ c ^ 2 / ρ := by gcongr
    have hS : |A i j - A i p * A p j / A p p| ≤ c + c ^ 2 / ρ := by
      have h := abs_add_le (A i j) (-(A i p * A p j / A p p))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h.trans (add_le_add (hcap i j) hquot)
    -- expand the computed entry
    rw [hsub, hprod]
    have hexpand : (A i j - A i p * A p j / A p p * C) * (1 + δs) -
        (A i j - A i p * A p j / A p p) =
        (A i j - A i p * A p j / A p p) * δs -
        A i p * A p j / A p p * ((C - 1) * (1 + δs)) := by ring
    rw [hexpand]
    have h1s : |1 + δs| ≤ 1 + fp.u := by
      have := abs_le.mp hδs
      rw [abs_le]
      constructor <;> linarith [this.1, this.2]
    calc |(A i j - A i p * A p j / A p p) * δs -
          A i p * A p j / A p p * ((C - 1) * (1 + δs))|
        ≤ |(A i j - A i p * A p j / A p p) * δs| +
          |A i p * A p j / A p p * ((C - 1) * (1 + δs))| := by
          have h := abs_add_le
            ((A i j - A i p * A p j / A p p) * δs)
            (-(A i p * A p j / A p p * ((C - 1) * (1 + δs))))
          rw [abs_neg, ← sub_eq_add_neg] at h
          exact h
      _ ≤ (c + c ^ 2 / ρ) * fp.u +
          (c ^ 2 / ρ) * (gamma fp 5 * (1 + fp.u)) := by
          refine add_le_add ?_ ?_
          · rw [abs_mul]
            exact mul_le_mul hS hδs (abs_nonneg _) (by positivity)
          · rw [abs_mul, abs_mul]
            refine mul_le_mul hquot ?_
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
              (by positivity)
            exact mul_le_mul hC1 h1s (abs_nonneg _) hγ5
      _ = fp.u * (c + c ^ 2 / ρ) +
          (1 + fp.u) * gamma fp 5 * (c ^ 2 / ρ) := by ring

/-- **The factor-form floating-point complete-pivoting trace**: the
    pivoted algorithm as actually implemented — √-scaled fl updates,
    pivots from the computed working diagonal. -/
noncomputable def fl_cpStateFactor (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => A
  | t + 1 => fl_schurStepFactor fp (fl_cpStateFactor fp hn A t)
      (diagArgmax hn (fl_cpStateFactor fp hn A t))

/-- The pivot the factor-form run selects at stage `t`. -/
noncomputable def fl_cpPivotFactor (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n :=
  diagArgmax hn (fl_cpStateFactor fp hn A t)

/-- **The factor-form run follows the exact pivot sequence** — the
    `fl_cpPivot_sequence_agrees` induction for the √-scaled
    formulation, with the `γ₅` Stewart rounding contribution
    `U = u(c′ + c′²/(ρ/2)) + (1+u)γ₅(c′²/(ρ/2))`, `c′ = c + δ/2`. -/
theorem fl_cpPivotFactor_sequence_agrees (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) ≤
        h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤ h t) ∧
      (∀ s : ℕ, s < t →
        cpPivot hn A s = fl_cpPivotFactor fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  have hh_nonneg : ∀ t : ℕ, t ≤ r → 0 ≤ h t := by
    intro t
    induction t with
    | zero => intro _; rw [hh0]
    | succ t iht =>
      intro htr
      have ht' : t < r := Nat.lt_of_succ_le htr
      have h0 := iht (Nat.le_of_lt ht')
      have hstep := hhstep t ht'
      have h1 : (0:ℝ) ≤
          (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 := by
        positivity
      have h2 : (0:ℝ) ≤
          fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) := by
        positivity
      linarith
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨fun i j => ?_, fun s hs => absurd hs (Nat.not_lt_zero s)⟩
    show |A i j - A i j| ≤ h 0
    rw [sub_self, abs_zero, hh0]
  | succ t ih =>
    intro htr
    have ht' : t < r := Nat.lt_of_succ_le htr
    obtain ⟨hdiff, hpiv⟩ := ih (Nat.le_of_lt ht')
    have hht0 := hh_nonneg t (Nat.le_of_lt ht')
    set p : Fin n := cpPivot hn A t with hp
    set Et : Fin n → Fin n → ℝ :=
      fun i j => fl_cpStateFactor fp hn A t i j - cpState hn A t i j
      with hEt
    have hEdiag : ∀ i : Fin n, |Et i i| < δ / 2 := by
      intro i
      have hd := hdiff i i
      rw [abs_sub_comm] at hd
      exact lt_of_le_of_lt hd (hhhalf t ht')
    have hstable := diagArgmax_stable hn (cpState hn A t) Et p δ
      (hgap t ht') hEdiag
    have hFfun : (fun i j => cpState hn A t i j + Et i j) =
        fl_cpStateFactor fp hn A t := by
      funext i j
      simp [hEt]
    have hpivF : fl_cpPivotFactor fp hn A t = p := by
      show diagArgmax hn (fl_cpStateFactor fp hn A t) = p
      rw [← hFfun]
      exact hstable.2
    have hFcap : ∀ i j : Fin n,
        |fl_cpStateFactor fp hn A t i j| ≤ c + δ / 2 := by
      intro i j
      have h1 := hdiff i j
      have h2 := hcap t ht' i j
      have h3 := abs_sub_abs_le_abs_sub
        (fl_cpStateFactor fp hn A t i j) (cpState hn A t i j)
      rw [abs_sub_comm (fl_cpStateFactor fp hn A t i j)
        (cpState hn A t i j)] at h3
      have h4 := hhhalf t ht'
      linarith
    have hAfloor : ρ / 2 ≤ cpState hn A t p p := by
      have := hfloor t ht'
      linarith
    have hFfloor : ρ / 2 ≤ fl_cpStateFactor fp hn A t p p := by
      have h1 := hEdiag p
      have h2 := abs_lt.mp h1
      have h3 := hfloor t ht'
      have h4 : fl_cpStateFactor fp hn A t p p =
          cpState hn A t p p + Et p p := by simp [hEt]
      rw [h4]
      linarith [h2.1, hδρ]
    have hexact := schurStep_entrywise_perturbation
      (cpState hn A t) (fl_cpStateFactor fp hn A t) p (h t) c (ρ / 2)
      hht0 hc (by linarith) hdiff (hcap t ht') hAfloor hFfloor
    have hround := fl_schurStepFactor_close fp
      (fl_cpStateFactor fp hn A t) p (c + δ / 2) (ρ / 2)
      (by linarith) (by linarith) hFcap hFfloor h5
    constructor
    · intro i j
      have hSA : cpState hn A (t + 1) =
          schurStep (cpState hn A t) p := rfl
      have hSF : fl_cpStateFactor fp hn A (t + 1) =
          fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p := by
        show fl_schurStepFactor fp (fl_cpStateFactor fp hn A t)
          (diagArgmax hn (fl_cpStateFactor fp hn A t)) =
          fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p
        rw [show diagArgmax hn (fl_cpStateFactor fp hn A t) =
          fl_cpPivotFactor fp hn A t from rfl, hpivF]
      rw [hSA, hSF]
      have htri : |schurStep (cpState hn A t) p i j -
          fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j| ≤
          |schurStep (cpState hn A t) p i j -
            schurStep (fl_cpStateFactor fp hn A t) p i j| +
          |fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j -
            schurStep (fl_cpStateFactor fp hn A t) p i j| := by
        have habs := abs_add_le
          (schurStep (cpState hn A t) p i j -
            schurStep (fl_cpStateFactor fp hn A t) p i j)
          (schurStep (fl_cpStateFactor fp hn A t) p i j -
            fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j)
        rw [sub_add_sub_cancel] at habs
        rw [abs_sub_comm
          (fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j)
          (schurStep (fl_cpStateFactor fp hn A t) p i j)]
        exact habs
      calc |schurStep (cpState hn A t) p i j -
            fl_schurStepFactor fp (fl_cpStateFactor fp hn A t) p i j|
          ≤ _ + _ := htri
        _ ≤ (h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2) +
            (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
              (1 + fp.u) * gamma fp 5 *
                ((c + δ / 2) ^ 2 / (ρ / 2))) :=
            add_le_add (hexact i j) (hround i j)
        _ ≤ h (t + 1) := by
            have := hhstep t ht'
            linarith
    · intro s hs
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hs) with h' | h'
      · exact hpiv s h'
      · subst h'
        rw [hpivF]

/-- The exact scaled pivot row extracted at one elimination stage:
    `√(a_pp)` at the pivot, `a_pj/√(a_pp)` elsewhere. -/
noncomputable def schurRow {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) : Fin n → ℝ :=
  fun i => if i = p then Real.sqrt (A p p)
    else A p i / Real.sqrt (A p p)

/-- **One elimination step subtracts the scaled pivot-row outer
    product** — entrywise, at every position including the zeroed
    pivot row and column. -/
lemma schurStep_decompose {n : ℕ} (A : Fin n → Fin n → ℝ)
    (p : Fin n) (hsym : ∀ i j : Fin n, A i j = A j i)
    (hp : 0 < A p p) :
    ∀ i j : Fin n, schurStep A p i j =
      A i j - schurRow A p i * schurRow A p j := by
  intro i j
  have hsq : Real.sqrt (A p p) * Real.sqrt (A p p) = A p p :=
    Real.mul_self_sqrt hp.le
  have hsq0 : Real.sqrt (A p p) ≠ 0 :=
    (Real.sqrt_pos.mpr hp).ne'
  unfold schurStep schurRow
  by_cases hi : i = p
  · by_cases hj : j = p
    · rw [hi, hj, if_pos (Or.inl rfl), if_pos rfl, hsq]
      ring
    · rw [hi, if_pos (Or.inl rfl), if_pos rfl, if_neg hj,
        show Real.sqrt (A p p) * (A p j / Real.sqrt (A p p)) =
          A p j * (Real.sqrt (A p p) / Real.sqrt (A p p)) by ring,
        div_self hsq0]
      ring
  · by_cases hj : j = p
    · rw [hj, if_pos (Or.inr rfl), if_neg hi, if_pos rfl,
        show A p i / Real.sqrt (A p p) * Real.sqrt (A p p) =
          A p i * (Real.sqrt (A p p) / Real.sqrt (A p p)) by ring,
        div_self hsq0, hsym p i]
      ring
    · rw [if_neg (by simp [hi, hj]), if_neg hi, if_neg hj,
        show A p i / Real.sqrt (A p p) *
          (A p j / Real.sqrt (A p p)) =
          A p i * A p j / (Real.sqrt (A p p) * Real.sqrt (A p p))
          by ring, hsq, hsym p i]

/-- **The exact run telescopes**: after `r` stages,
    `A = ∑_{t<r} row_tᵀ row_t + S_r` entrywise — the Gram assembly of
    the exact pivoted factorization, with `S_r` the stage-`r` Schur
    complement (Theorem 10.14 / (10.22) exact skeleton). -/
theorem cpState_telescope {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hsym : ∀ i j : Fin n, A i j = A j i)
    (r : ℕ)
    (hfloor : ∀ t : ℕ, t < r →
      0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t)) :
    ∀ i j : Fin n,
      A i j = (∑ t ∈ Finset.range r,
        schurRow (cpState hn A t) (cpPivot hn A t) i *
        schurRow (cpState hn A t) (cpPivot hn A t) j) +
        cpState hn A r i j := by
  induction r with
  | zero =>
    intro i j
    simp [cpState]
  | succ r ih =>
    intro i j
    have hfloor' : ∀ t : ℕ, t < r →
        0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t) :=
      fun t ht => hfloor t (Nat.lt_succ_of_lt ht)
    have hsymr : ∀ i j : Fin n,
        cpState hn A r i j = cpState hn A r j i :=
      cpState_symm hn A hsym r
    have hstep := schurStep_decompose (cpState hn A r)
      (cpPivot hn A r) hsymr (hfloor r (Nat.lt_succ_self r)) i j
    have hS : cpState hn A (r + 1) i j =
        cpState hn A r i j -
        schurRow (cpState hn A r) (cpPivot hn A r) i *
        schurRow (cpState hn A r) (cpPivot hn A r) j := hstep
    have hih := ih hfloor' i j
    rw [Finset.sum_range_succ, hS]
    linarith [hih]

/-- **The fl pivot-agreement hypotheses are non-vacuous** (instantiated
    budget): with `U` the one-stage rounding contribution and
    `K = 1 + (3c² + c)/(ρ/2)²` the exact-growth rate, the explicit
    budget `g t = U·t·Kᵗ` satisfies the recurrence, so a single scalar
    smallness condition `U·r·Kʳ < min(min 1 (δ/2)) (ρ/4)` — which holds
    for all sufficiently small `u`, since `U` is a polynomial in `u`
    vanishing at `0` — yields pivot agreement and state closeness
    outright. -/
theorem fl_cpPivot_sequence_agrees_small (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall :
      (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
        ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
          (1 + fp.u)) * r *
        (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpState fp hn A t i j| ≤
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) * t *
          (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ t) ∧
      (∀ s : ℕ, s < t → cpPivot hn A s = fl_cpPivot fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  set U : ℝ := fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
    ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
      (1 + fp.u) with hU
  set K : ℝ := 1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2 with hK
  have hU0 : 0 ≤ U := by rw [hU]; positivity
  have hK1 : (1:ℝ) ≤ K := by
    rw [hK]
    have : (0:ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by positivity
    linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  set g : ℕ → ℝ := fun t => U * t * K ^ t with hg
  -- the budget is capped along the run by the smallness scalar
  have hgle : ∀ t : ℕ, t ≤ r →
      g t ≤ U * r * K ^ r := by
    intro t htr
    show U * t * K ^ t ≤ U * r * K ^ r
    have h1 : (t:ℝ) ≤ (r:ℝ) := by exact_mod_cast htr
    have h2 : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    calc U * t * K ^ t ≤ U * r * K ^ t := by
          have := mul_le_mul_of_nonneg_left h1 hU0
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ U * r * K ^ r := by
          exact mul_le_mul_of_nonneg_left h2
            (mul_nonneg hU0 (Nat.cast_nonneg r))
  have hM := hsmall
  have hmin1 : min (min 1 (δ / 2)) (ρ / 4) ≤ 1 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hminδ : min (min 1 (δ / 2)) (ρ / 4) ≤ δ / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  -- the explicit budget satisfies all three conditions
  have hg0 : g 0 = 0 := by
    show U * (0:ℕ) * K ^ 0 = 0
    norm_num
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := fun t htr =>
    le_trans (hgle t (Nat.le_of_lt htr)) (le_of_lt
      (lt_of_lt_of_le hM hmin1))
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := fun t htr =>
    lt_of_le_of_lt (hgle t (Nat.le_of_lt htr))
      (lt_of_lt_of_le hM hminδ)
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    show (0:ℝ) ≤ U * t * K ^ t
    positivity
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U ≤
        g (t + 1) := by
    intro t htr
    have hgt1 := hg1 t htr
    have hgt0 := hg_nonneg t
    -- quadratic absorbed at g ≤ 1, then the K-recurrence
    have habs : 3 * c ^ 2 * g t + c * g t ^ 2 ≤
        (3 * c ^ 2 + c) * g t := by
      nlinarith [mul_nonneg (mul_nonneg hc hgt0)
        (sub_nonneg.mpr hgt1)]
    have hKrec : g t * K + U ≤ g (t + 1) := by
      show U * t * K ^ t * K + U ≤ U * ((t + 1 : ℕ) : ℝ) * K ^ (t + 1)
      push_cast
      have h1 : (1:ℝ) ≤ K ^ (t + 1) := one_le_pow₀ hK1
      have h2 : U * (t:ℝ) * K ^ t * K = U * (t:ℝ) * K ^ (t + 1) := by
        rw [pow_succ]; ring
      nlinarith [h2, mul_nonneg hU0 (sub_nonneg.mpr h1)]
    have hexp : g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 =
        g t * K := by
      rw [hK]
      field_simp
    have hdiv : (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 := by gcongr
    calc g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U
        ≤ g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 + U := by
          linarith [hdiv]
      _ = g t * K + U := by rw [hexp]
      _ ≤ g (t + 1) := hKrec
  exact fl_cpPivot_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    g hg0 hgstep hghalf hgap hfloor hcap

/-- **Factor-form fl agreement, non-vacuous form**: the explicit budget
    `g t = U·t·Kᵗ` with the `γ₅` rounding contribution — one scalar
    smallness condition, holding for all sufficiently small `u`. -/
theorem fl_cpPivotFactor_sequence_agrees_small (fp : FPModel)
    {n : ℕ} (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall :
      (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
        (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) * r *
        (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    ∀ t : ℕ, t ≤ r →
      (∀ i j : Fin n,
        |cpState hn A t i j - fl_cpStateFactor fp hn A t i j| ≤
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))) * t *
          (1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2) ^ t) ∧
      (∀ s : ℕ, s < t →
        cpPivot hn A s = fl_cpPivotFactor fp hn A s) := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hu0 := fp.u_nonneg
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  set U : ℝ := fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
    (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2)) with hU
  set K : ℝ := 1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2 with hK
  have hU0 : 0 ≤ U := by
    rw [hU]
    refine add_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (by positivity) hγ5) (by positivity))
  have hK1 : (1:ℝ) ≤ K := by
    rw [hK]
    have : (0:ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by positivity
    linarith
  have hK0 : (0:ℝ) < K := lt_of_lt_of_le one_pos hK1
  set g : ℕ → ℝ := fun t => U * t * K ^ t with hg
  have hgle : ∀ t : ℕ, t ≤ r → g t ≤ U * r * K ^ r := by
    intro t htr
    show U * t * K ^ t ≤ U * r * K ^ r
    have h1 : (t:ℝ) ≤ (r:ℝ) := by exact_mod_cast htr
    have h2 : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    calc U * t * K ^ t ≤ U * r * K ^ t := by
          have := mul_le_mul_of_nonneg_left h1 hU0
          exact mul_le_mul_of_nonneg_right this (by positivity)
      _ ≤ U * r * K ^ r :=
          mul_le_mul_of_nonneg_left h2
            (mul_nonneg hU0 (Nat.cast_nonneg r))
  have hmin1 : min (min 1 (δ / 2)) (ρ / 4) ≤ 1 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hminδ : min (min 1 (δ / 2)) (ρ / 4) ≤ δ / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hg0 : g 0 = 0 := by
    show U * (0:ℕ) * K ^ 0 = 0
    norm_num
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := fun t htr =>
    le_trans (hgle t (Nat.le_of_lt htr))
      (le_of_lt (lt_of_lt_of_le hsmall hmin1))
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := fun t htr =>
    lt_of_le_of_lt (hgle t (Nat.le_of_lt htr))
      (lt_of_lt_of_le hsmall hminδ)
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    show (0:ℝ) ≤ U * t * K ^ t
    positivity
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U ≤
        g (t + 1) := by
    intro t htr
    have hgt1 := hg1 t htr
    have hgt0 := hg_nonneg t
    have habs : 3 * c ^ 2 * g t + c * g t ^ 2 ≤
        (3 * c ^ 2 + c) * g t := by
      nlinarith [mul_nonneg (mul_nonneg hc hgt0)
        (sub_nonneg.mpr hgt1)]
    have hKrec : g t * K + U ≤ g (t + 1) := by
      show U * t * K ^ t * K + U ≤ U * ((t + 1 : ℕ) : ℝ) * K ^ (t + 1)
      push_cast
      have h1 : (1:ℝ) ≤ K ^ (t + 1) := one_le_pow₀ hK1
      have h2 : U * (t:ℝ) * K ^ t * K = U * (t:ℝ) * K ^ (t + 1) := by
        rw [pow_succ]; ring
      nlinarith [h2, mul_nonneg hU0 (sub_nonneg.mpr h1)]
    have hexp : g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 =
        g t * K := by
      rw [hK]
      field_simp
    have hdiv : (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 := by gcongr
    calc g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U
        ≤ g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 + U := by
          linarith [hdiv]
      _ = g t * K + U := by rw [hexp]
      _ ≤ g (t + 1) := hKrec
  exact fl_cpPivotFactor_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    h5 g hg0 hgstep hghalf hgap hfloor hcap

/-- **Neumann-style entry cap for the perturbed inverse** (resolves the
    recorded Lemma 10.10 `χ`-as-hypothesis delta): from the resolvent
    identity alone, if `q = k²με < 1` then every entry of `X` is
    bounded by `μ/(1−q)` — no cap on `X` needs to be assumed. Proof by
    evaluating the identity at the maximal entry. -/
lemma resolvent_entry_cap {k : ℕ} (hk : 0 < k)
    (M X E11 : Matrix (Fin k) (Fin k) ℝ) (μ ε : ℝ)
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (hM : ∀ i j, |M i j| ≤ μ) (hE : ∀ i j, |E11 i j| ≤ ε)
    (hX : X = M - M * E11 * X)
    (hq : (k:ℝ) ^ 2 * μ * ε < 1) :
    ∀ i j, |X i j| ≤ μ / (1 - (k:ℝ) ^ 2 * μ * ε) := by
  have hne : (Finset.univ : Finset (Fin k × Fin k)).Nonempty := by
    refine ⟨(⟨0, hk⟩, ⟨0, hk⟩), Finset.mem_univ _⟩
  set χ : ℝ := Finset.univ.sup' hne
    (fun p : Fin k × Fin k => |X p.1 p.2|) with hχ
  have hbound : ∀ i j : Fin k, |X i j| ≤ χ := fun i j =>
    Finset.le_sup' (f := fun p : Fin k × Fin k => |X p.1 p.2|)
      (Finset.mem_univ (i, j))
  have hχ0 : 0 ≤ χ := le_trans (abs_nonneg _)
    (hbound ⟨0, hk⟩ ⟨0, hk⟩)
  -- the sup is attained
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup' hne
    (fun p : Fin k × Fin k => |X p.1 p.2|)
  -- entrywise bound on the correction term at any entry
  have hME : ∀ (i t : Fin k), |(M * E11) i t| ≤ (k:ℝ) * μ * ε :=
    entrywise_matMul_le M E11 μ ε hμ hM hE
  have hMEX : ∀ (i j : Fin k), |((M * E11) * X) i j| ≤
      (k:ℝ) * ((k:ℝ) * μ * ε) * χ :=
    entrywise_matMul_le (M * E11) X _ χ (by positivity) hME hbound
  -- evaluate the identity at the attaining entry
  have hself : χ ≤ μ + (k:ℝ) ^ 2 * μ * ε * χ := by
    have hXe : X p.1 p.2 = M p.1 p.2 - ((M * E11) * X) p.1 p.2 := by
      conv_lhs => rw [hX]
      simp [Matrix.sub_apply]
    have h1 : |X p.1 p.2| ≤ |M p.1 p.2| + |((M * E11) * X) p.1 p.2| := by
      rw [hXe]
      have h := abs_add_le (M p.1 p.2) (-(((M * E11) * X) p.1 p.2))
      rw [abs_neg, ← sub_eq_add_neg] at h
      exact h
    have h2 := hMEX p.1 p.2
    have h3 : (k:ℝ) * ((k:ℝ) * μ * ε) * χ =
        (k:ℝ) ^ 2 * μ * ε * χ := by ring
    have hpχ : χ = |X p.1 p.2| := by
      rw [hχ]; exact hp
    have hcalc : |X p.1 p.2| ≤ μ + (k:ℝ) ^ 2 * μ * ε * χ :=
      calc |X p.1 p.2|
          ≤ |M p.1 p.2| + |((M * E11) * X) p.1 p.2| := h1
        _ ≤ μ + (k:ℝ) ^ 2 * μ * ε * χ := by
            rw [← h3]
            exact add_le_add (hM p.1 p.2) h2
    linarith [hpχ, hcalc]
  have h1q : (0:ℝ) < 1 - (k:ℝ) ^ 2 * μ * ε := by linarith
  have hχle : χ ≤ μ / (1 - (k:ℝ) ^ 2 * μ * ε) := by
    rw [le_div_iff₀ h1q]
    nlinarith
  exact fun i j => le_trans (hbound i j) hχle

/-- The computed factor row extracted at one fl elimination stage:
    `fl(√a_pp)` at the pivot, `fl(a_pj/fl(√a_pp))` off it. -/
noncomputable def fl_cpRowOf (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n) : Fin n → ℝ :=
  fun j => if j = p then fp.fl_sqrt (A p p)
    else fp.fl_div (A p j) (fp.fl_sqrt (A p p))

/-- **Per-stage defect of the fl factorization step** (R̂-Gram bridge
    engine): the fl update differs from
    `A − (computed row)ᵀ(computed row)` entrywise by at most
    `u|a_ij| + (2u+u²)|r̃_i||r̃_j|`. On the pivot row and column the
    computed square root cancels *exactly* as a real number, so only
    the divide's single rounding survives; on the diagonal the
    `(1+δ)²` of the square root is absorbed for `u ≤ 1/8`. -/
theorem fl_schurStepFactor_defect_bound (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i)
    (hApp : 0 < A p p) (hu8 : fp.u ≤ 1 / 8) :
    ∀ i j : Fin n,
      |fl_schurStepFactor fp A p i j -
        (A i j - fl_cpRowOf fp A p i * fl_cpRowOf fp A p j)| ≤
      fp.u * |A i j| + (2 * fp.u + fp.u ^ 2) *
        (|fl_cpRowOf fp A p i| * |fl_cpRowOf fp A p j|) := by
  intro i j
  have hu0 := fp.u_nonneg
  obtain ⟨δa, hδa, hsqrt⟩ := fp.model_sqrt (A p p) hApp.le
  have ha := abs_le.mp hδa
  have h1a : (0:ℝ) < 1 + δa := by nlinarith [ha.1]
  have hsq0 : (0:ℝ) < Real.sqrt (A p p) := Real.sqrt_pos.mpr hApp
  have hfs0 : fp.fl_sqrt (A p p) ≠ 0 := by
    rw [hsqrt]; positivity
  have hsqsq : Real.sqrt (A p p) * Real.sqrt (A p p) = A p p :=
    Real.mul_self_sqrt hApp.le
  by_cases hi : i = p
  · -- pivot row: exact real cancellation of the square root
    obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (A p j)
      (fp.fl_sqrt (A p p)) hfs0
    by_cases hj : j = p
    · -- diagonal: (1+δa)² absorbed at u ≤ 1/8
      unfold fl_schurStepFactor fl_cpRowOf
      rw [hi, hj, if_pos (Or.inl rfl), if_pos rfl, hsqrt]
      have hkey : (0:ℝ) - (A p p - Real.sqrt (A p p) * (1 + δa) *
          (Real.sqrt (A p p) * (1 + δa))) =
          A p p * ((1 + δa) * (1 + δa) - 1) := by
        nlinarith [hsqsq]
      rw [hkey, abs_mul, abs_of_pos hApp]
      have herr : |(1 + δa) * (1 + δa) - 1| ≤ 2 * fp.u + fp.u ^ 2 := by
        have h1 : (1 + δa) * (1 + δa) - 1 = 2 * δa + δa ^ 2 := by ring
        rw [h1]
        have h2 : |δa ^ 2| ≤ fp.u ^ 2 := by
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) hδa 2
        have h3 := abs_le.mp h2
        rw [abs_le]
        constructor <;> nlinarith [ha.1, ha.2, h3.1, h3.2]
      have hrow2 : |Real.sqrt (A p p) * (1 + δa)| *
          |Real.sqrt (A p p) * (1 + δa)| =
          A p p * ((1 + δa) * (1 + δa)) := by
        rw [abs_mul, abs_of_pos hsq0, abs_of_pos h1a]
        nlinarith [hsqsq]
      calc A p p * |(1 + δa) * (1 + δa) - 1|
          ≤ A p p * (2 * fp.u + fp.u ^ 2) :=
            mul_le_mul_of_nonneg_left herr hApp.le
        _ ≤ fp.u * A p p + (2 * fp.u + fp.u ^ 2) *
              (A p p * ((1 + δa) * (1 + δa))) := by
            have hge : (1 - fp.u) * (1 - fp.u) ≤
                (1 + δa) * (1 + δa) := by
              nlinarith [ha.1, hu8, hu0]
            have h5 : A p p * ((2 * fp.u + fp.u ^ 2) *
                ((1 - fp.u) * (1 - fp.u))) ≤
                A p p * ((2 * fp.u + fp.u ^ 2) *
                ((1 + δa) * (1 + δa))) := by
              refine mul_le_mul_of_nonneg_left ?_ hApp.le
              exact mul_le_mul_of_nonneg_left hge (by positivity)
            have hcoef : 2 * fp.u + fp.u ^ 2 ≤ fp.u +
                (2 * fp.u + fp.u ^ 2) *
                  ((1 - fp.u) * (1 - fp.u)) := by
              nlinarith [mul_nonneg hu0
                (by linarith : (0:ℝ) ≤ 1 - 4 * fp.u),
                pow_nonneg hu0 4, sq_nonneg fp.u]
            nlinarith [h5, mul_le_mul_of_nonneg_left hcoef hApp.le]
        _ = fp.u * A p p + (2 * fp.u + fp.u ^ 2) *
              (|Real.sqrt (A p p) * (1 + δa)| *
               |Real.sqrt (A p p) * (1 + δa)|) := by
            rw [hrow2]
    · unfold fl_schurStepFactor fl_cpRowOf
      rw [hi, if_pos (Or.inl rfl), if_pos rfl, if_neg hj, hdiv, hsqrt]
      have hcancel : (0:ℝ) - (A p j - Real.sqrt (A p p) * (1 + δa) *
          (A p j / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb))) =
          A p j * δb := by
        field_simp
        ring
      rw [hcancel, abs_mul]
      have h1 : |A p j| * |δb| ≤ fp.u * |A p j| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hδb (abs_nonneg _)
      have h2 : (0:ℝ) ≤ (2 * fp.u + fp.u ^ 2) *
          (|Real.sqrt (A p p) * (1 + δa)| *
           |A p j / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb)|) := by
        positivity
      linarith
  · by_cases hj : j = p
    · -- pivot column: same exact cancellation, via symmetry
      obtain ⟨δb, hδb, hdiv⟩ := fp.model_div (A p i)
        (fp.fl_sqrt (A p p)) hfs0
      unfold fl_schurStepFactor fl_cpRowOf
      rw [hj, if_pos (Or.inr rfl), if_neg hi, if_pos rfl, hdiv, hsqrt]
      have hcancel : (0:ℝ) - (A i p -
          A p i / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb) *
            (Real.sqrt (A p p) * (1 + δa))) =
          A i p * δb := by
        rw [hsym p i]
        field_simp
        ring
      rw [hcancel, abs_mul]
      have h1 : |A i p| * |δb| ≤ fp.u * |A i p| := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hδb (abs_nonneg _)
      have h2 : (0:ℝ) ≤ (2 * fp.u + fp.u ^ 2) *
          (|A p i / (Real.sqrt (A p p) * (1 + δa)) * (1 + δb)| *
           |Real.sqrt (A p p) * (1 + δa)|) := by
        positivity
      linarith
    · -- off-pivot: the multiply and subtract roundings
      obtain ⟨δb, hδb, hdivb⟩ := fp.model_div (A i p)
        (fp.fl_sqrt (A p p)) hfs0
      obtain ⟨δc, hδc, hdivc⟩ := fp.model_div (A p j)
        (fp.fl_sqrt (A p p)) hfs0
      obtain ⟨δm, hδm, hmul⟩ := fp.model_mul
        (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A p j) (fp.fl_sqrt (A p p)))
      obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (A i j)
        (fp.fl_mul (fp.fl_div (A i p) (fp.fl_sqrt (A p p)))
          (fp.fl_div (A p j) (fp.fl_sqrt (A p p))))
      unfold fl_schurStepFactor fl_cpRowOf
      rw [if_neg (by simp [hi, hj]), if_neg hi, if_neg hj,
        hsub, hmul, hdivb, hdivc]
      have hrow_i : fp.fl_div (A p i) (fp.fl_sqrt (A p p)) =
          A i p / fp.fl_sqrt (A p p) * (1 + δb) := by
        rw [hsym p i]
        exact hdivb
      rw [hrow_i]
      have hexp : (A i j - A i p / fp.fl_sqrt (A p p) * (1 + δb) *
            (A p j / fp.fl_sqrt (A p p) * (1 + δc)) * (1 + δm)) *
            (1 + δs) -
          (A i j - A i p / fp.fl_sqrt (A p p) * (1 + δb) *
            (A p j / fp.fl_sqrt (A p p) * (1 + δc))) =
          A i j * δs -
          (A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
            (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
            ((1 + δm) * (1 + δs) - 1) := by
        ring
      rw [hexp]
      have herr : |(1 + δm) * (1 + δs) - 1| ≤
          2 * fp.u + fp.u ^ 2 := by
        have h1 : (1 + δm) * (1 + δs) - 1 =
            δm + δs + δm * δs := by ring
        rw [h1]
        have hab : |δm * δs| ≤ fp.u ^ 2 := by
          rw [abs_mul]
          calc |δm| * |δs| ≤ fp.u * fp.u :=
                mul_le_mul hδm hδs (abs_nonneg _) hu0
            _ = fp.u ^ 2 := by ring
        have h2 := abs_le.mp hab
        have h3 := abs_le.mp hδm
        have h4 := abs_le.mp hδs
        rw [abs_le]
        constructor <;> linarith [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
      calc |A i j * δs -
            (A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
              (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
              ((1 + δm) * (1 + δs) - 1)|
          ≤ |A i j * δs| +
            |(A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
              (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
              ((1 + δm) * (1 + δs) - 1)| := by
            have h := abs_add_le (A i j * δs)
              (-((A i p / fp.fl_sqrt (A p p) * (1 + δb)) *
                (A p j / fp.fl_sqrt (A p p) * (1 + δc)) *
                ((1 + δm) * (1 + δs) - 1)))
            rw [abs_neg, ← sub_eq_add_neg] at h
            exact h
        _ ≤ fp.u * |A i j| + (2 * fp.u + fp.u ^ 2) *
              (|A i p / fp.fl_sqrt (A p p) * (1 + δb)| *
               |A p j / fp.fl_sqrt (A p p) * (1 + δc)|) := by
            refine add_le_add ?_ ?_
            · rw [abs_mul, mul_comm]
              exact mul_le_mul_of_nonneg_right hδs (abs_nonneg _)
            · rw [abs_mul, abs_mul]
              rw [show |A i p / fp.fl_sqrt (A p p) * (1 + δb)| *
                  |A p j / fp.fl_sqrt (A p p) * (1 + δc)| *
                  |(1 + δm) * (1 + δs) - 1| =
                  |(1 + δm) * (1 + δs) - 1| *
                  (|A i p / fp.fl_sqrt (A p p) * (1 + δb)| *
                   |A p j / fp.fl_sqrt (A p p) * (1 + δc)|) by ring]
              exact mul_le_mul_of_nonneg_right herr
                (by positivity)

/-- The fl elimination step preserves symmetry, given commutative
    rounded multiplication (true for IEEE; the abstract model does not
    assert it, so it is carried as a hypothesis). -/
lemma fl_schurStepFactor_symm (fp : FPModel)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (p : Fin n)
    (hsym : ∀ i j : Fin n, A i j = A j i) (i j : Fin n) :
    fl_schurStepFactor fp A p i j = fl_schurStepFactor fp A p j i := by
  unfold fl_schurStepFactor
  by_cases hi : i = p
  · by_cases hj : j = p <;> simp [hi, hj]
  · by_cases hj : j = p
    · simp [hi, hj]
    · rw [if_neg (by simp [hi, hj]), if_neg (by simp [hi, hj])]
      rw [hsym i j, hsym i p, hsym p j]
      rw [hmul (fp.fl_div (A p i) (fp.fl_sqrt (A p p)))
        (fp.fl_div (A j p) (fp.fl_sqrt (A p p)))]

/-- The fl trace stays symmetric from a symmetric input. -/
lemma fl_cpStateFactor_symm (fp : FPModel)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, A i j = A j i) :
    ∀ t : ℕ, ∀ i j : Fin n,
      fl_cpStateFactor fp hn A t i j = fl_cpStateFactor fp hn A t j i := by
  intro t
  induction t with
  | zero => exact hsym
  | succ t ih =>
    exact fl_schurStepFactor_symm fp hmul
      (fl_cpStateFactor fp hn A t) _ ih

/-- **The as-run factorization telescopes with summable defects**
    (Theorem 10.14 componentwise backward error for the pivoted
    algorithm as actually executed): the Gram of the computed rows,
    plus the terminal computed Schur state, reproduces `A` entrywise up
    to `r` per-stage rounding defects —
    `|∑_{t<r} r̃ᵗᵢ r̃ᵗⱼ + S̃ᵣ ᵢⱼ − aᵢⱼ| ≤ r(u·cS + (2u+u²)·cR²)`. -/
theorem fl_cpFactor_gram_backward_error (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hsymA : ∀ i j : Fin n, A i j = A j i)
    (hu8 : fp.u ≤ 1 / 8)
    (hpos : ∀ t : ℕ, t < r →
      0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t))
    (cS cR : ℝ)
    (hcapS : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |fl_cpStateFactor fp hn A t i j| ≤ cS)
    (hcapR : ∀ t : ℕ, t < r → ∀ i : Fin n,
      |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
        (fl_cpPivotFactor fp hn A t) i| ≤ cR) :
    ∀ i j : Fin n,
      |(∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpStateFactor fp hn A r i j - A i j| ≤
      (r : ℝ) * (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) := by
  induction r with
  | zero =>
    intro i j
    simp [fl_cpStateFactor]
  | succ r ih =>
    intro i j
    have hpos' : ∀ t : ℕ, t < r →
        0 < fl_cpStateFactor fp hn A t (fl_cpPivotFactor fp hn A t)
          (fl_cpPivotFactor fp hn A t) :=
      fun t ht => hpos t (Nat.lt_succ_of_lt ht)
    have hcapS' : ∀ t : ℕ, t < r → ∀ i j : Fin n,
        |fl_cpStateFactor fp hn A t i j| ≤ cS :=
      fun t ht => hcapS t (Nat.lt_succ_of_lt ht)
    have hcapR' : ∀ t : ℕ, t < r → ∀ i : Fin n,
        |fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
          (fl_cpPivotFactor fp hn A t) i| ≤ cR :=
      fun t ht => hcapR t (Nat.lt_succ_of_lt ht)
    have hih := ih hpos' hcapS' hcapR' i j
    -- the stage-r defect
    have hsymr := fl_cpStateFactor_symm fp hmul hn A hsymA r
    have hdef := fl_schurStepFactor_defect_bound fp
      (fl_cpStateFactor fp hn A r) (fl_cpPivotFactor fp hn A r)
      hsymr (hpos r (Nat.lt_succ_self r)) hu8 i j
    have hSsucc : fl_cpStateFactor fp hn A (r + 1) i j =
        fl_schurStepFactor fp (fl_cpStateFactor fp hn A r)
          (fl_cpPivotFactor fp hn A r) i j := rfl
    -- bound the stage-r defect by the uniform constant
    have hdef' : |fl_cpStateFactor fp hn A (r + 1) i j -
        (fl_cpStateFactor fp hn A r i j -
          fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
            (fl_cpPivotFactor fp hn A r) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
            (fl_cpPivotFactor fp hn A r) j)| ≤
        fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2 := by
      rw [hSsucc]
      refine hdef.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left
          (hcapS r (Nat.lt_succ_self r) i j) fp.u_nonneg
      · have h1 := hcapR r (Nat.lt_succ_self r) i
        have h2 := hcapR r (Nat.lt_succ_self r) j
        have hcR0 : (0:ℝ) ≤ cR := le_trans (abs_nonneg _) h1
        have : |fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) i| *
            |fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) j| ≤ cR ^ 2 := by
          calc _ ≤ cR * cR :=
                mul_le_mul h1 h2 (abs_nonneg _) hcR0
            _ = cR ^ 2 := by ring
        refine mul_le_mul_of_nonneg_left this ?_
        have := fp.u_nonneg
        positivity
    -- assemble
    rw [Finset.sum_range_succ]
    have hgoal : (∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
        fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
          (fl_cpPivotFactor fp hn A r) i *
        fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
          (fl_cpPivotFactor fp hn A r) j +
        fl_cpStateFactor fp hn A (r + 1) i j - A i j =
        ((∑ t ∈ Finset.range r,
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) i *
          fl_cpRowOf fp (fl_cpStateFactor fp hn A t)
            (fl_cpPivotFactor fp hn A t) j) +
          fl_cpStateFactor fp hn A r i j - A i j) +
        (fl_cpStateFactor fp hn A (r + 1) i j -
          (fl_cpStateFactor fp hn A r i j -
            fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) i *
            fl_cpRowOf fp (fl_cpStateFactor fp hn A r)
              (fl_cpPivotFactor fp hn A r) j)) := by
      ring
    rw [hgoal]
    calc |_ + _|
        ≤ _ + _ := abs_add_le _ _
      _ ≤ (r : ℝ) * (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) +
          (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) :=
          add_le_add hih hdef'
      _ = ((r + 1 : ℕ) : ℝ) *
          (fp.u * cS + (2 * fp.u + fp.u ^ 2) * cR ^ 2) := by
          push_cast
          ring

end NumStability
