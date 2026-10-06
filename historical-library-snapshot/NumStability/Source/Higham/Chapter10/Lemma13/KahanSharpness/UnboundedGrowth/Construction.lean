import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
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
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Construction

Canonical destination for 4 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- Row action of the (10.18) matrix on the leading block. -/
private lemma higham10_18_row_cast (k : ℕ) (α : ℝ) (hk : 0 < k)
    (x : Fin (k + k) → ℝ) (i : Fin k) :
    ∑ j : Fin (k + k), higham10_18_matrix k α (Fin.castAdd k i) j *
      x j =
    α * x (Fin.castAdd k i) + x (Fin.natAdd k i) := by
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.castAdd k i) (Fin.castAdd k j) *
        x (Fin.castAdd k j) = α * x (Fin.castAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      simp [Fin.castAdd, i.isLt]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.castAdd k b).val := by
        simp only [Fin.coe_castAdd]
        exact fun h => hb (Fin.ext h.symm)
      have h2 : ¬((Fin.castAdd k i).val + k = (Fin.castAdd k b).val ∨
          (Fin.castAdd k b).val + k = (Fin.castAdd k i).val) := by
        simp only [Fin.coe_castAdd]
        push_neg
        omega
      rw [if_neg hne, if_neg h2, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.castAdd k i) (Fin.natAdd k j) *
        x (Fin.natAdd k j) = x (Fin.natAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.castAdd k i).val + k = (Fin.natAdd k i).val ∨
          (Fin.natAdd k i).val + k = (Fin.castAdd k i).val := by
        left
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor, one_mul]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k b).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have h3 : ¬((Fin.castAdd k i).val + k = (Fin.natAdd k b).val ∨
          (Fin.natAdd k b).val + k = (Fin.castAdd k i).val) := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        push_neg
        constructor
        · intro h
          exact absurd (Fin.ext (show b.val = i.val by omega)) hb
        · omega
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2]

/-- Row action of the (10.18) matrix on the trailing block. -/
private lemma higham10_18_row_nat (k : ℕ) (α : ℝ) (hk : 0 < k)
    (x : Fin (k + k) → ℝ) (i : Fin k) :
    ∑ j : Fin (k + k), higham10_18_matrix k α (Fin.natAdd k i) j *
      x j =
    x (Fin.castAdd k i) + α⁻¹ * x (Fin.natAdd k i) := by
  rw [Fin.sum_univ_add]
  have h1 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.natAdd k i) (Fin.castAdd k j) *
        x (Fin.castAdd k j) = x (Fin.castAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.castAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.natAdd k i).val + k = (Fin.castAdd k i).val ∨
          (Fin.castAdd k i).val + k = (Fin.natAdd k i).val := by
        right
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor, one_mul]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.castAdd k b).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have h3 : ¬((Fin.natAdd k i).val + k = (Fin.castAdd k b).val ∨
          (Fin.castAdd k b).val + k = (Fin.natAdd k i).val) := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        push_neg
        constructor
        · omega
        · intro h
          exact absurd (Fin.ext (show b.val = i.val by omega)) hb
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have h2 : ∑ j : Fin k,
      higham10_18_matrix k α (Fin.natAdd k i) (Fin.natAdd k j) *
        x (Fin.natAdd k j) = α⁻¹ * x (Fin.natAdd k i) := by
    rw [Finset.sum_eq_single i]
    · unfold higham10_18_matrix
      have heq : (Fin.natAdd k i).val = (Fin.natAdd k i).val := rfl
      have hge : ¬(Fin.natAdd k i).val < k := by
        simp only [Fin.coe_natAdd]
        omega
      rw [if_pos heq, if_neg hge]
    · intro b _ hb
      unfold higham10_18_matrix
      have hne : (Fin.natAdd k i).val ≠ (Fin.natAdd k b).val := by
        simp only [Fin.coe_natAdd]
        intro h
        exact hb (Fin.ext (by omega)).symm
      have h3 : ¬((Fin.natAdd k i).val + k = (Fin.natAdd k b).val ∨
          (Fin.natAdd k b).val + k = (Fin.natAdd k i).val) := by
        simp only [Fin.coe_natAdd]
        push_neg
        omega
      rw [if_neg hne, if_neg h3, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1, h2]

/-- **The (10.18) matrix is positive semidefinite** — completion of
    squares pairwise across the two blocks:
    `xᵀAx = ∑ᵢ (√α·xᵢ + x_{k+i}/√α)²`. -/
theorem higham10_18_isPosSemiDef (k : ℕ) (hk : 0 < k) (α : ℝ)
    (hα : 0 < α) :
    IsPosSemiDef (k + k) (higham10_18_matrix k α) := by
  constructor
  · intro i j
    unfold higham10_18_matrix
    by_cases hij : i.val = j.val
    · rw [if_pos hij, if_pos hij.symm, hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      by_cases hd : i.val + k = j.val ∨ j.val + k = i.val
      · rw [if_pos hd, if_pos (Or.symm hd)]
      · rw [if_neg hd, if_neg (fun h => hd (Or.symm h))]
  · intro x
    have hquad : ∑ i : Fin (k + k), ∑ j : Fin (k + k),
        x i * higham10_18_matrix k α i j * x j =
        ∑ i : Fin k, (α * x (Fin.castAdd k i) ^ 2 +
          2 * x (Fin.castAdd k i) * x (Fin.natAdd k i) +
          α⁻¹ * x (Fin.natAdd k i) ^ 2) := by
      rw [Fin.sum_univ_add]
      have hc : ∀ i : Fin k, ∑ j : Fin (k + k),
          x (Fin.castAdd k i) *
            higham10_18_matrix k α (Fin.castAdd k i) j * x j =
          x (Fin.castAdd k i) * (α * x (Fin.castAdd k i) +
            x (Fin.natAdd k i)) := by
        intro i
        rw [← higham10_18_row_cast k α hk x i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      have hn : ∀ i : Fin k, ∑ j : Fin (k + k),
          x (Fin.natAdd k i) *
            higham10_18_matrix k α (Fin.natAdd k i) j * x j =
          x (Fin.natAdd k i) * (x (Fin.castAdd k i) +
            α⁻¹ * x (Fin.natAdd k i)) := by
        intro i
        rw [← higham10_18_row_nat k α hk x i, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [Finset.sum_congr rfl fun i _ => hc i,
        Finset.sum_congr rfl fun i _ => hn i,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hquad]
    refine Finset.sum_nonneg fun i _ => ?_
    have hsq := sq_nonneg (Real.sqrt α * x (Fin.castAdd k i) +
      (Real.sqrt α)⁻¹ * x (Fin.natAdd k i))
    have hs : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
    have hs0 : (0:ℝ) < Real.sqrt α := Real.sqrt_pos.mpr hα
    have hsinv : ((Real.sqrt α)⁻¹) ^ 2 = α⁻¹ := by
      rw [inv_pow, hs]
    have hmul : Real.sqrt α * (Real.sqrt α)⁻¹ = 1 :=
      mul_inv_cancel₀ hs0.ne'
    have hexp : (Real.sqrt α * x (Fin.castAdd k i) +
        (Real.sqrt α)⁻¹ * x (Fin.natAdd k i)) ^ 2 =
        α * x (Fin.castAdd k i) ^ 2 +
        2 * x (Fin.castAdd k i) * x (Fin.natAdd k i) +
        α⁻¹ * x (Fin.natAdd k i) ^ 2 := by
      have h0 : (Real.sqrt α * x (Fin.castAdd k i) +
          (Real.sqrt α)⁻¹ * x (Fin.natAdd k i)) ^ 2 =
          Real.sqrt α ^ 2 * x (Fin.castAdd k i) ^ 2 +
          2 * (Real.sqrt α * (Real.sqrt α)⁻¹) *
            (x (Fin.castAdd k i) * x (Fin.natAdd k i)) +
          ((Real.sqrt α)⁻¹) ^ 2 * x (Fin.natAdd k i) ^ 2 := by
        ring
      rw [h0, hs, hsinv, hmul]
      ring
    linarith [hexp ▸ hsq]

/-- **Display (10.18): `‖W‖` is arbitrarily large** (Higham p. 204):
    for the PSD matrix `[[αI, I], [I, α⁻¹I]]` the solve `A₁₁W = A₁₂`
    is `W = α⁻¹I` — verified by the row action — and its action norm
    `α⁻¹` exceeds any bound as `α → 0`: no bound on `‖A₁₁⁻¹A₁₂‖`
    independent of the matrix is possible without pivoting
    structure. -/
theorem higham10_18_w_arbitrarily_large (k : ℕ) (hk : 0 < k)
    (C : ℝ) :
    ∃ α : ℝ, 0 < α ∧
      IsPosSemiDef (k + k) (higham10_18_matrix k α) ∧
      (∀ v : Fin k → ℝ, ∀ i : Fin k,
        ∑ j : Fin k, higham10_18_matrix k α (Fin.castAdd k i)
          (Fin.castAdd k j) * (α⁻¹ * v j) =
        higham10_18_matrix k α (Fin.castAdd k i) (Fin.natAdd k i) *
          v i) ∧
      ∀ v : Fin k → ℝ,
        vecNorm2Sq (fun i => α⁻¹ * v i) =
          (α⁻¹) ^ 2 * vecNorm2Sq v ∧
        C ≤ α⁻¹ := by
  set α : ℝ := min 1 (1 / (|C| + 1)) with hα
  have hα0 : 0 < α := by
    rw [hα]
    have : (0:ℝ) < 1 / (|C| + 1) := by positivity
    exact lt_min one_pos this
  refine ⟨α, hα0, higham10_18_isPosSemiDef k hk α hα0, ?_, ?_⟩
  · intro v i
    -- A₁₁ = αI acting on α⁻¹v recovers v = A₁₂-column action
    have hL : ∑ j : Fin k, higham10_18_matrix k α (Fin.castAdd k i)
        (Fin.castAdd k j) * (α⁻¹ * v j) = v i := by
      rw [Finset.sum_eq_single i]
      · unfold higham10_18_matrix
        simp only [Fin.coe_castAdd, if_true]
        rw [if_pos i.isLt]
        field_simp
      · intro b _ hb
        unfold higham10_18_matrix
        have hne : (Fin.castAdd k i).val ≠ (Fin.castAdd k b).val := by
          simp only [Fin.coe_castAdd]
          exact fun h => hb (Fin.ext h.symm)
        have h3 : ¬((Fin.castAdd k i).val + k =
            (Fin.castAdd k b).val ∨
            (Fin.castAdd k b).val + k = (Fin.castAdd k i).val) := by
          simp only [Fin.coe_castAdd]
          push_neg
          omega
        rw [if_neg hne, if_neg h3, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    have hR : higham10_18_matrix k α (Fin.castAdd k i)
        (Fin.natAdd k i) = 1 := by
      unfold higham10_18_matrix
      have hne : (Fin.castAdd k i).val ≠ (Fin.natAdd k i).val := by
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      have hor : (Fin.castAdd k i).val + k = (Fin.natAdd k i).val ∨
          (Fin.natAdd k i).val + k = (Fin.castAdd k i).val := by
        left
        simp only [Fin.coe_castAdd, Fin.coe_natAdd]
        omega
      rw [if_neg hne, if_pos hor]
    rw [hL, hR, one_mul]
  · intro v
    constructor
    · unfold vecNorm2Sq
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    · have h1 : α ≤ 1 / (|C| + 1) := by
        rw [hα]
        exact min_le_right _ _
      have h2 : (0:ℝ) < |C| + 1 := by positivity
      have h3 : |C| + 1 ≤ α⁻¹ := by
        rw [← one_div]
        rw [le_div_iff₀ hα0]
        calc (|C| + 1) * α ≤ (|C| + 1) * (1 / (|C| + 1)) :=
              mul_le_mul_of_nonneg_left h1 h2.le
          _ = 1 := by field_simp
      calc C ≤ |C| := le_abs_self C
        _ ≤ α⁻¹ := by linarith

end NumStability
