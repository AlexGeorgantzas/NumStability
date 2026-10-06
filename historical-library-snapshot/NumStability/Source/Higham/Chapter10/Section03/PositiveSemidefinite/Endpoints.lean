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
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
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
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound

/-!
# Chapter10 Section03 PositiveSemidefinite Endpoints

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Equation (10.9)** source-shaped statement for van der Sluis scaling:
the scaled condition number is bounded by `n` times the best diagonal scaling
condition number. -/
def higham10_9_vanDerSluisScalingBound (n : ℕ)
    (κH bestDiagonalScalingκ : ℝ) : Prop :=
  κH ≤ (n : ℝ) * bestDiagonalScalingκ

/-- **Theorem 10.9**, source predicate for pivoted PSD Cholesky
factorization in equation (10.11). -/
abbrev higham10_9_PivotedCholeskySpec (n : ℕ)
    (A R : Fin n → Fin n → ℝ) (σ : Fin n → Fin n) (r : ℕ) : Prop :=
  PivotedCholeskySpec n A R σ r

/-- A pivoted Cholesky certificate remains valid when its nominal rank is
    capped by the matrix dimension.  This small structural bridge is needed
    because `PivotedCholeskySpec` deliberately does not bake `r ≤ n` into the
    structure: when `r > n`, every actual row is already one of the positive
    leading rows, while the zero-row condition at the capped rank is vacuous. -/
theorem higham10_9_pivotedCholeskySpec_min_rank {n : ℕ}
    {A R : Fin n → Fin n → ℝ} {σ : Fin n → Fin n} {r : ℕ}
    (hspec : higham10_9_PivotedCholeskySpec n A R σ r) :
    higham10_9_PivotedCholeskySpec n A R σ (min r n) := by
  refine
    { perm := hspec.perm
      R_upper := hspec.R_upper
      R_diag_pos := ?_
      R_rank_zero := ?_
      product_eq := hspec.product_eq }
  · intro i hi
    exact hspec.R_diag_pos i (lt_of_lt_of_le hi (Nat.min_le_left r n))
  · intro i j hi
    by_cases hrn : r ≤ n
    · rw [Nat.min_eq_left hrn] at hi
      exact hspec.R_rank_zero i j hi
    · have hnr : n ≤ r := by omega
      rw [Nat.min_eq_right hnr] at hi
      exact absurd hi (Nat.not_le_of_lt i.isLt)

/-- **Equation (10.12)**: outer-product residual after `k` Cholesky stages,
`A^(k) = A - sum_{t<k} r_t r_t^T`. -/
noncomputable def higham10_12_outerProductResidual (n k : ℕ)
    (A R : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A i j -
    ∑ t : Fin n, if t.val < k then R t i * R t j else 0

/-- **Lemma 10.10 / equation (10.16)** in honest form: the perturbed
Schur complement equals the unperturbed one plus Higham's first-order
term `Ē = E₂₂ − E₂₁MA₁₂ − A₂₁ME₁₂ + A₂₁ME₁₁MA₁₂` plus a remainder that
is entrywise bounded by an explicit polynomial times `ε²` — the exact
statement behind the source's `S(A+E) = S(A) + Ē + O(‖E‖²)`. The
leading-block inverses enter through genuine inverse equations
(`M A₁₁ = 1` up to the resolvent identity), not assumed bounds on the
conclusion. -/
theorem higham10_10_schur_complement_perturbation {k m : ℕ}
    (A11 E11 M X : Matrix (Fin k) (Fin k) ℝ)
    (A21 E21 : Matrix (Fin m) (Fin k) ℝ)
    (A12 E12 : Matrix (Fin k) (Fin m) ℝ)
    (A22 E22 : Matrix (Fin m) (Fin m) ℝ)
    (hM : M * A11 = 1) (hXi : (A11 + E11) * X = 1)
    (α μ χ ε : ℝ) (hα : 0 ≤ α) (hμ : 0 ≤ μ) (hχ : 0 ≤ χ) (hε : 0 ≤ ε)
    (hA21 : ∀ i j, |A21 i j| ≤ α) (hA12 : ∀ i j, |A12 i j| ≤ α)
    (hE21 : ∀ i j, |E21 i j| ≤ ε) (hE12 : ∀ i j, |E12 i j| ≤ ε)
    (hE11 : ∀ i j, |E11 i j| ≤ ε)
    (hMb : ∀ i j, |M i j| ≤ μ) (hXb : ∀ i j, |X i j| ≤ χ) :
    ∃ R : Matrix (Fin m) (Fin m) ℝ,
      (A22 + E22) - (A21 + E21) * X * (A12 + E12) =
        (A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12
            + A21 * (M * E11 * M) * A12)
        + R ∧
      ∀ i j : Fin m, |R i j| ≤
        ((k : ℝ) ^ 2 * μ + (k : ℝ) ^ 6 * α ^ 2 * μ ^ 2 * χ
          + 2 * ((k : ℝ) ^ 4 * α * μ * χ) + (k : ℝ) ^ 4 * μ * χ * ε)
          * ε ^ 2 := by
  have hres := schur_resolvent_from_inverses M X A11 E11 hM hXi
  refine ⟨_, schur_perturbation_exact A21 E21 A12 E12 A22 E22 M X E11
    hres, ?_⟩
  exact schur_perturbation_remainder_bound A21 E21 A12 E12 M X E11
    α μ χ ε hα hμ hχ hε hA21 hA12 hE21 hE12 hE11 hMb hXb

/-- **Lemma 10.12**: abstract `W = A11^{-1} A12` norm bound. -/
theorem higham10_12_w_norm_bound_from_cond
    (W_norm κ_A11 : ℝ) (hκ : 0 ≤ κ_A11)
    (hW : W_norm ^ 2 ≤ κ_A11) :
    W_norm ^ 2 ≤ κ_A11 :=
  w_norm_bound_from_cond W_norm κ_A11 hκ hW

/-- **Lemma 10.12 core (Higham §10.3)**: for a positive semidefinite
    block matrix with leading block `A₁₁` inverted in action by `M`, the
    solve vector `Wv = M A₁₂ v` satisfies
    `λ_min(A₁₁) ‖Wv‖₂² ≤ vᵀ A₂₂ v` — the quadratic-form content of
    `Wᵀ A₁₁ W ⪯ A₂₂`, sharpened through the Rayleigh bound. Choosing
    `u = −Wv` in the block-split quadratic form gives
    `(Wv)ᵀA₁₁(Wv) ≤ vᵀA₂₂v`; Rayleigh converts the left side. -/
theorem higham10_12_psd_w_action_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (v : Fin m → ℝ) :
    finiteMinEigenvalue hk
        (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j))
        hSym *
      vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
        (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    ∑ i : Fin m, ∑ j : Fin m,
      v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j := by
  set b : Fin k → ℝ := fun t =>
    ∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j with hb
  set u : Fin k → ℝ := fun i => ∑ t : Fin k, M i t * b t with hu
  -- the inverse action at b: A₁₁ u = b
  have hA11u : ∀ i : Fin k,
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) * u j = b i :=
    fun i => hMinv b i
  -- key PSD inequality with the appended vector (-u, v)
  have hquad := hPSD.2 (Fin.append (fun i => -(u i)) v)
  rw [quadForm_append_split A (fun i => -(u i)) v] at hquad
  -- identify the four blocks
  have hT1 : ∑ i : Fin k, ∑ j : Fin k,
      (-(u i)) * A (Fin.castAdd m i) (Fin.castAdd m j) * (-(u j)) =
      ∑ i : Fin k, u i * b i := by
    calc ∑ i : Fin k, ∑ j : Fin k,
        (-(u i)) * A (Fin.castAdd m i) (Fin.castAdd m j) * (-(u j))
        = ∑ i : Fin k, ∑ j : Fin k,
          u i * (A (Fin.castAdd m i) (Fin.castAdd m j) * u j) :=
          Finset.sum_congr rfl fun i _ =>
            Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i : Fin k, u i * b i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, hA11u i]
  have hT2 : ∑ i : Fin k, ∑ j : Fin m,
      (-(u i)) * A (Fin.castAdd m i) (Fin.natAdd k j) * v j =
      -(∑ i : Fin k, u i * b i) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  have hT3 : ∑ i : Fin m, ∑ j : Fin k,
      v i * A (Fin.natAdd k i) (Fin.castAdd m j) * (-(u j)) =
      -(∑ i : Fin k, u i * b i) := by
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsymA : ∀ i : Fin m,
        A (Fin.natAdd k i) (Fin.castAdd m j) =
        A (Fin.castAdd m j) (Fin.natAdd k i) :=
      fun i => hPSD.1 _ _
    rw [hb]
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsymA i]; ring
  rw [hT1, hT2, hT3] at hquad
  -- so uᵀ b ≤ vᵀ A₂₂ v, and uᵀ b = uᵀA₁₁u ≥ λ_min ‖u‖²
  have hub : ∑ i : Fin k, u i * b i ≤
      ∑ i : Fin m, ∑ j : Fin m,
        v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j := by
    linarith [hquad]
  have hray := finiteMinEigenvalue_rayleigh hk
    (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym u
  have huAu : ∑ i : Fin k, ∑ j : Fin k,
      u i * A (Fin.castAdd m i) (Fin.castAdd m j) * u j =
      ∑ i : Fin k, u i * b i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hA11u i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [huAu] at hray
  calc finiteMinEigenvalue hk _ hSym * vecNorm2Sq u
      ≤ ∑ i : Fin k, u i * b i := by
        simpa [vecNorm2Sq] using hray
    _ ≤ _ := hub

/-- **Lemma 10.12, norm form**: with a positive Rayleigh floor
    `λ_min(A₁₁) > 0` and a quadratic-form certificate `c₂₂` for `A₂₂`,
    the solve action `W v = M A₁₂ v` is norm-bounded:
    `‖Wv‖₂² ≤ (c₂₂/λ_min) ‖v‖₂²` — the source's
    `‖A₁₁⁻¹A₁₂‖₂² ≤ ‖A₂₂‖₂/λ_min(A₁₁)` in vector-action certificate
    form. -/
theorem higham10_12_w_action_norm_bound {k m : ℕ} (hk : 0 < k)
    (A : Fin (k + m) → Fin (k + m) → ℝ)
    (hPSD : IsPosSemiDef (k + m) A)
    (M : Fin k → Fin k → ℝ)
    (hSym : IsSymmetricFiniteMatrix
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)))
    (hMinv : ∀ (w : Fin k → ℝ) (i : Fin k),
      ∑ j : Fin k, A (Fin.castAdd m i) (Fin.castAdd m j) *
        (∑ t : Fin k, M j t * w t) = w i)
    (hlampos : 0 < finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
    (c22 : ℝ)
    (hc22 : ∀ v : Fin m → ℝ,
      ∑ i : Fin m, ∑ j : Fin m,
        v i * A (Fin.natAdd k i) (Fin.natAdd k j) * v j ≤
      c22 * vecNorm2Sq v)
    (v : Fin m → ℝ) :
    vecNorm2Sq (fun i : Fin k => ∑ t : Fin k, M i t *
      (∑ j : Fin m, A (Fin.castAdd m t) (Fin.natAdd k j) * v j)) ≤
    (c22 / finiteMinEigenvalue hk
      (fun i j : Fin k => A (Fin.castAdd m i) (Fin.castAdd m j)) hSym)
      * vecNorm2Sq v := by
  have hcore := higham10_12_psd_w_action_bound hk A hPSD M hSym hMinv v
  have hchain := le_trans hcore (hc22 v)
  rw [div_mul_eq_mul_div, le_div_iff₀ hlampos, mul_comm]
  linarith [hchain]

/-- **Display (10.25), componentwise to normwise** (Higham p. 206): the
    componentwise (10.24) bound
    `|E| ≤ γ(|R̂ᵀ||R̂| + |Â⁽ʳ⁺¹⁾|)` converts to the operator-norm
    certificate `‖E‖₂ ≤ γ(n·cR² + √n·cÂ)` via Lemma 6.6. -/
theorem higham10_25_componentwise_to_normwise (n : ℕ)
    (E R Ahat : Fin n → Fin n → ℝ) (γ cR cAhat : ℝ)
    (hγ0 : 0 ≤ γ) (hcR : 0 ≤ cR) (hcAhat : 0 ≤ cAhat)
    (h24 : ∀ i j : Fin n, |E i j| ≤ γ *
      (matMul n (fun i' j' => |R j' i'|) (fun i' j' => |R i' j'|) i j +
        |Ahat i j|))
    (hR : opNorm2Le R cR) (hAhat : opNorm2Le Ahat cAhat) :
    opNorm2Le E (γ * ((n : ℝ) * cR ^ 2 + Real.sqrt n * cAhat)) := by
  have hG := higham10_7_absRT_absR_opNorm2Le n R cR hcR hR
  have hAb := opNorm2Le_abs_of_opNorm2Le n Ahat cAhat hcAhat hAhat
  have hsum := opNorm2Le_add _ _ _ _ hG hAb
  have hB := opNorm2Le_smul n
    (fun i j =>
      matMul n (fun i' j' => |R j' i'|) (fun i' j' => |R i' j'|) i j +
        |Ahat i j|)
    ((n : ℝ) * cR ^ 2 + Real.sqrt n * cAhat) γ hγ0 hsum
  exact opNorm2Le_of_abs_le n E _ h24 _ hB

/-- **Display (10.25), the absorption** (Higham p. 206): from the norm
    chain `‖E‖ ≤ γ(r‖A‖ + r‖E‖ + n‖Â⁽ʳ⁺¹⁾‖)` with `rγ < 1`,
    `‖E‖ ≤ γ/(1 − rγ)·(r‖A‖ + n‖Â⁽ʳ⁺¹⁾‖)`. -/
theorem higham10_25_absorption (γ r n cA cAhat e : ℝ)
    (hrγ : r * γ < 1)
    (hchain : e ≤ γ * (r * cA + r * e + n * cAhat)) :
    e ≤ γ / (1 - r * γ) * (r * cA + n * cAhat) := by
  have h1 : (0:ℝ) < 1 - r * γ := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ h1]
  nlinarith

/-- **Equation (10.26)**: stop after the first nonpositive remaining pivot. -/
def higham10_26_nonpositivePivotCriterion {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : ℕ) : Prop :=
  ∀ i : Fin n, k ≤ i.val → Astage i i ≤ 0

/-- **Equation (10.27)**: residual-norm stopping criterion. -/
def higham10_27_residualStopCriterion
    (residual_norm matrix_norm ε : ℝ) : Prop :=
  residual_norm ≤ ε * matrix_norm

/-- **Equation (10.27)**: alternative nonpositive-diagonal stopping criterion. -/
def higham10_27_nonpositiveDiagonalCriterion {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : ℕ) : Prop :=
  higham10_26_nonpositivePivotCriterion Astage k

/-- **Equation (10.28)**: relative diagonal stopping criterion, written as the
equivalent finite-entry form of `max_{i>=k} a_ii^(k) <= ε a_11^(1)`. -/
def higham10_28_relativeDiagonalStopCriterion {n : ℕ}
    (Astage : Fin n → Fin n → ℝ) (k : ℕ) (ε initialPivot : ℝ) : Prop :=
  ∀ i : Fin n, k ≤ i.val → Astage i i ≤ ε * initialPivot

/-- **Equation (10.27)** abstract termination-bound interface used by the PSD
error analysis. -/
theorem higham10_27_psd_cholesky_termination_bound
    (residual_norm matrix_norm : ℝ)
    (n : ℕ) (u : ℝ) (hu : 0 ≤ u)
    (hstop : residual_norm ≤ ↑n * u * matrix_norm)
    (hm : 0 ≤ matrix_norm) :
    residual_norm ≤ ↑n * u * matrix_norm :=
  psd_cholesky_termination_bound residual_norm matrix_norm n u hu hstop hm

end NumStability
