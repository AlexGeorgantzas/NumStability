import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
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
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement

/-!
# Chapter10 Lemma11 PivotSequenceStability Endpoints

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Lemma 10.11, first-order Schur-complement identity (Higham §10.3.1)** for
the displayed perturbation `E = γ · [[I,0],[0,0]]`, which acts only on the
leading block.  Specializing Lemma 10.10 to `E₂₂ = E₂₁ = E₁₂ = 0`,
`E₁₁ = γ·I` gives, with `M = A₁₁⁻¹`,

  `S(A+E) = S(A) + γ·(A₂₁ M² A₁₂) + R`,   `|Rᵢⱼ| ≤ (poly)·γ²`,

i.e. the exact `S(A+E) − S(A) = γ·(A₂₁M²A₁₂) + O(‖E‖²)` behind the source's
`‖S(cp(A+E)) − S(A)‖ = ‖W‖²‖E‖ + O(‖E‖²)` (see
`higham10_11_firstOrder_eq_WtW`, which rewrites the first-order term as `WᵀW`
with `W = M A₁₂`; here `‖E‖₂ = γ`).  The pivot-order-preservation half —
condition (10.17) ⇒ `cp(A+E)` uses the same permutation as `cp(A)` — needs the
complete-pivoting operator and remains an open foundation. -/
theorem higham10_11_schur_perturbation_leadingBlock {k m : ℕ}
    (A11 M X : Matrix (Fin k) (Fin k) ℝ)
    (A21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 : Matrix (Fin m) (Fin m) ℝ)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hM : M * A11 = 1)
    (hXi : (A11 + γ • (1 : Matrix (Fin k) (Fin k) ℝ)) * X = 1)
    (α μ χ : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hMb : ∀ i j, |M i j| ≤ μ) (hXb : ∀ i j, |X i j| ≤ χ) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ,
      A22 - A21 * X * A12
        = (A22 - A21 * M * A12) + γ • (A21 * (M * M) * A12) + R ∧
      ∀ i j : Fin m, |R i j| ≤
        ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
          + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * γ)
          * γ ^ 2 := by
  obtain ⟨R, hEq, hR⟩ :=
    higham10_10_schur_complement_perturbation A11
      (γ • (1 : Matrix (Fin k) (Fin k) ℝ)) M X
      A21 (0 : Matrix (Fin m) (Fin k) ℝ)
      A12 (0 : Matrix (Fin k) (Fin m) ℝ)
      A22 (0 : Matrix (Fin m) (Fin m) ℝ)
      hM hXi α μ χ γ hα hμ hχ hγ
      hA21 hA12
      (by intro i j; simpa using hγ)
      (by intro i j; simpa using hγ)
      (by
        intro i j
        have h0 : (γ • (1 : Matrix (Fin k) (Fin k) ℝ)) i j
            = if i = j then γ else 0 := by simp [Matrix.one_apply]
        rw [h0]
        by_cases h : i = j <;> simp [h, abs_of_nonneg hγ, hγ])
      hMb hXb
  refine ⟨R, ?_, hR⟩
  have hterm : A21 * (M * (γ • (1 : Matrix (Fin k) (Fin k) ℝ)) * M) * A12
      = γ • (A21 * (M * M) * A12) := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hLHS : A22 - A21 * X * A12
      = (A22 + (0 : Matrix (Fin m) (Fin m) ℝ))
        - (A21 + 0) * X * (A12 + 0) := by simp
  rw [hLHS, hEq]
  simp only [Matrix.zero_mul, Matrix.mul_zero, sub_zero, zero_sub, neg_zero,
    zero_add, add_zero]
  rw [hterm]

/-- **Lemma 10.11 first-order term as `WᵀW`.**  When `A` is symmetric
(`A₂₁ = A₁₂ᵀ`) and `M = A₁₁⁻¹` is symmetric, the first-order coefficient of the
Schur-complement perturbation equals `WᵀW` with `W = M A₁₂ = A₁₁⁻¹A₁₂`, so the
first-order term is `γ·WᵀW`, whose 2-norm is `γ‖W‖₂² = ‖E‖₂‖W‖₂²`. -/
theorem higham10_11_firstOrder_eq_WtW {k m : ℕ}
    (M : Matrix (Fin k) (Fin k) ℝ) (A12 : Matrix (Fin k) (Fin m) ℝ)
    (A21 : Matrix (Fin m) (Fin k) ℝ)
    (hA : A21 = Matrix.transpose A12) (hM : Matrix.transpose M = M) :
    A21 * (M * M) * A12 = Matrix.transpose (M * A12) * (M * A12) := by
  subst hA
  simp only [Matrix.transpose_mul, hM, Matrix.mul_assoc]

/-- **Lemma 10.11, quantitative half in the operator 2-norm.**  Upgrades the
entrywise `O(γ²)` remainder of `higham10_11_schur_perturbation_leadingBlock` to
the *operator 2-norm* `opNorm2Le` — the norm in which Higham states the source
`O(‖E‖²)`.  For `E = γ·[[I,0],[0,0]]` the perturbed Schur complement satisfies
`S(A+E) = S(A) + γ·(A₂₁M²A₁₂) + R` with `‖R‖₂ ≤ (poly)·γ²·m = O(γ²) = O(‖E‖₂²)`.
Combined with `higham10_11_firstOrder_eq_WtW` (first-order term `γ·WᵀW`,
`W = M A₁₂`), this is Higham's `‖S(cp(A+E)) − S(A)‖₂ = ‖W‖₂²‖E‖₂ + O(‖E‖₂²)` with
the `O(‖E‖²)` error controlled in the source's operator 2-norm. -/
theorem higham10_11_schur_perturbation_opNorm2 {k m : ℕ}
    (A11 M X : Matrix (Fin k) (Fin k) ℝ)
    (A21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 : Matrix (Fin m) (Fin m) ℝ)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hM : M * A11 = 1)
    (hXi : (A11 + γ • (1 : Matrix (Fin k) (Fin k) ℝ)) * X = 1)
    (α μ χ : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hMb : ∀ i j, |M i j| ≤ μ) (hXb : ∀ i j, |X i j| ≤ χ) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ,
      A22 - A21 * X * A12
        = (A22 - A21 * M * A12) + γ • (A21 * (M * M) * A12) + R ∧
      opNorm2Le R
        (((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
          + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * γ)
          * γ ^ 2 * (m : ℝ)) := by
  obtain ⟨R, hEq, hR⟩ :=
    higham10_11_schur_perturbation_leadingBlock A11 M X A21 A12 A22 γ hγ
      hM hXi α μ χ hα hμ hχ hA21 hA12 hMb hXb
  refine ⟨R, hEq, ?_⟩
  set b : ℝ := ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
      + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * γ) * γ ^ 2
    with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have h2 := opNorm2Le_smul m (fun _ _ : Fin m => (1 : ℝ)) (m : ℝ) b hb0
    (higham10_7_onesMatrix_opNorm2Le m)
  exact opNorm2Le_of_abs_le m R (fun _ _ => b * 1)
    (fun i j => by rw [mul_one]; exact hR i j) (b * (m : ℝ)) h2

open scoped Matrix.Norms.L2Operator in
/-- **Lemma 10.11, leading-coefficient spectral identity.**  The first-order term
`γ·WᵀW` (`W = M A₁₂`) has operator 2-norm exactly `γ‖W‖₂²`: the l2-operator
C*-identity `‖WᵀW‖₂ = ‖W‖₂²` (`Matrix.l2_opNorm_conjTranspose_mul_self`, with
`Wᴴ = Wᵀ` over ℝ) together with positive-scalar homogeneity of the norm.  This
pins the `‖W‖₂²‖E‖₂` leading coefficient of Lemma 10.11 (here `‖E‖₂ = γ`), so the
source's `‖S(cp(A+E)) − S(A)‖₂ = ‖W‖₂²‖E‖₂ + O(‖E‖₂²)` is fully Lean-proved: exact
leading coefficient (this lemma) plus operator-2-norm `O(γ²)` remainder
(`higham10_11_schur_perturbation_opNorm2`). -/
theorem higham10_11_firstOrder_opNorm2 {k m : ℕ}
    (W : Matrix (Fin k) (Fin m) ℝ) (γ : ℝ) (hγ : 0 ≤ γ) :
    opNorm2 (γ • (Matrix.transpose W * W)) = γ * (‖W‖ * ‖W‖) := by
  have htr : Matrix.transpose W = Matrix.conjTranspose W := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply]
  show ‖γ • (Matrix.transpose W * W)‖ = γ * (‖W‖ * ‖W‖)
  rw [htr, norm_smul, Real.norm_eq_abs, abs_of_nonneg hγ,
    Matrix.l2_opNorm_conjTranspose_mul_self]

/-- The displayed Lemma 10.11 perturbation `E = γ·[[I,0],[0,0]]` on `Fin (k+m)`:
`γ` on the leading `k×k` diagonal block, `0` elsewhere. -/
def higham10_11_leadingBlockPerturbation (k m : ℕ) (γ : ℝ) :
    Fin (k + m) → Fin (k + m) → ℝ :=
  fun i j => if i = j ∧ (i : ℕ) < k then γ else 0

/-- **Lemma 10.11, `‖E‖₂ = γ` for the displayed perturbation.**  The block
perturbation `E = γ·[[I,0],[0,0]]` (`γ` on the leading `k×k` diagonal block, `0`
elsewhere) has operator 2-norm exactly `γ` when `k > 0` and `γ ≥ 0`.  This is the
last elementary ingredient making Lemma 10.11's quantitative identity fully
self-contained: `‖S(cp(A+E)) − S(A)‖₂ = ‖W‖₂²·γ + O(γ²) = ‖W‖₂²‖E‖₂ + O(‖E‖₂²)`. -/
theorem higham10_11_leadingBlockPerturbation_opNorm2 {k m : ℕ} (hk : 0 < k)
    (γ : ℝ) (hγ : 0 ≤ γ) :
    opNorm2 (higham10_11_leadingBlockPerturbation k m γ) = γ := by
  have hact : ∀ (x : Fin (k + m) → ℝ) (i : Fin (k + m)),
      matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) x i
        = if (i : ℕ) < k then γ * x i else 0 := by
    intro x i
    unfold matMulVec higham10_11_leadingBlockPerturbation
    rw [Finset.sum_eq_single i]
    · by_cases hi : (i : ℕ) < k <;> simp [hi]
    · intro j _ hji
      have hne : ¬ (i = j ∧ (i : ℕ) < k) := fun h => hji h.1.symm
      simp [hne]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- upper bound: opNorm2Le E γ
  have hupper : opNorm2Le (higham10_11_leadingBlockPerturbation k m γ) γ := by
    intro x
    have hsq : vecNorm2Sq
        (matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) x)
        ≤ γ ^ 2 * vecNorm2Sq x := by
      unfold vecNorm2Sq
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      rw [hact x i]
      by_cases hi : (i : ℕ) < k
      · rw [if_pos hi]; apply le_of_eq; ring
      · rw [if_neg hi]; nlinarith [mul_nonneg (sq_nonneg γ) (sq_nonneg (x i))]
    calc vecNorm2
          (matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) x)
        = Real.sqrt (vecNorm2Sq
            (matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) x)) :=
          rfl
      _ ≤ Real.sqrt (γ ^ 2 * vecNorm2Sq x) := Real.sqrt_le_sqrt hsq
      _ = γ * vecNorm2 x := by
          rw [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ]; rfl
  have hle : opNorm2 (higham10_11_leadingBlockPerturbation k m γ) ≤ γ :=
    opNorm2_le_of_opNorm2Le _ hγ hupper
  -- lower bound via the leading basis vector
  set i0 : Fin (k + m) := ⟨0, by omega⟩ with hi0
  set e : Fin (k + m) → ℝ := fun j => if j = i0 then 1 else 0 with he
  have hi0k : (i0 : ℕ) < k := by rw [hi0]; exact hk
  have henorm : vecNorm2 e = 1 := by
    unfold vecNorm2 vecNorm2Sq
    rw [Finset.sum_eq_single i0 (by intro b _ hb; simp [he, hb]) (by simp)]
    simp [he]
  have haction0 :
      matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) e i0 = γ := by
    rw [hact e i0, if_pos hi0k]
    simp [he]
  have henormE : vecNorm2
      (matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) e) = γ := by
    unfold vecNorm2
    have hsum : vecNorm2Sq
        (matMulVec (k + m) (higham10_11_leadingBlockPerturbation k m γ) e)
        = γ ^ 2 := by
      unfold vecNorm2Sq
      rw [Finset.sum_eq_single i0]
      · rw [haction0]
      · intro j _ hji
        rw [hact e j]
        by_cases hj : (j : ℕ) < k
        · rw [if_pos hj]; simp [he, hji]
        · rw [if_neg hj]; ring
      · intro h; exact absurd (Finset.mem_univ i0) h
    rw [hsum, Real.sqrt_sq hγ]
  have hlower : γ ≤ opNorm2 (higham10_11_leadingBlockPerturbation k m γ) := by
    have h := opNorm2Le_opNorm2 (higham10_11_leadingBlockPerturbation k m γ) e
    rw [henormE, henorm, mul_one] at h
    exact h
  exact le_antisymm hle hlower

/-- **Lemma 10.11, pivot-order-preservation half (Higham §10.3.1, source form).**
Chapter-label wrapper over the complete-pivoting machinery in
`Cholesky/CholeskyPSD.lean` (`cpPivot_sequence_stable_small`, built on
`diagArgmax_stable` and `schurStep_entrywise_perturbation`).  If the
complete-pivoting run of `A` has no ties — a diagonal gap `δ` at every stage
(condition (10.17)), a positive pivot floor `ρ`, and an entry cap `c` through the
first `r` stages — then there is a positive perturbation radius `ε₀` within which
every matrix `B` with `‖A − B‖ ≤ ε₀` entrywise selects the *same pivot sequence*
as `A`, i.e. `A + E = cp(A + E)` uses the same permutation as `cp(A)`.  This is
Higham's "for sufficiently small `‖E‖`, `A + E = cp(A + E)`" claim. -/
theorem higham10_11_cp_pivot_sequence_stable {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (δ ρ c : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n, |cpState hn A t i j| ≤ c) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ B : Fin n → Fin n → ℝ,
        (∀ i j : Fin n, |A i j - B i j| ≤ ε₀) →
        ∀ s : ℕ, s < r → cpPivot hn A s = cpPivot hn B s :=
  cpPivot_sequence_stable_small hn A r δ ρ c hδ hδρ hc hgap hfloor hcap

end NumStability
