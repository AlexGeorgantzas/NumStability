-- NumStability/Source/Higham/Chapter08/Problem08/SingleEntrySingularity/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Algorithms.HighamChapter8`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.MMatrix
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder
import NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.All
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter08.Equation14.FanInExecutor.Executor
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic
import NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.Aliases
import NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.RatioWitness
import NumStability.Source.Higham.Chapter08.Problem03.UnitTriangularSubstitution.Bound
import NumStability.Source.Higham.Chapter08.Problem04.MMatrixSubstitution.Comparison
import NumStability.Source.Higham.Chapter08.Problem05.InverseNormBounds.ZInverse
import NumStability.Source.Higham.Chapter08.Problem06.ComparisonInverseBounds.VectorBounds
import NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Bounds
import NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.RankOne
import NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.KahanMatrix
import NumStability.Source.Higham.Chapter08.Section01.BackwardErrorAnalysis.Core
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBounds
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.NormBounds
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsLower
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsUpper
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.AllOrdersEnvelope
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.Factors
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds

/-!
# Theorems

Relocated from `NumStability.Algorithms.HighamChapter8` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.















namespace NumStability

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

















































































































/-! ## §8.2 Forward Error Analysis -/


/-! ## Problems -/

























































private theorem higham8_8_matMulVec_scaledBasis {n : ℕ}
    (A_inv : Fin n → Fin n → ℝ) (i : Fin n) (alpha xj : ℝ) :
    matMulVec n A_inv (fun r => alpha * finiteBasisVec i r * xj) =
      fun r => alpha * A_inv r i * xj := by
  ext r
  unfold matMulVec
  rw [Finset.sum_eq_single i]
  · simp [finiteBasisVec]
    ring
  · intro c _ hc
    simp [finiteBasisVec, hc]
  · simp


private theorem higham8_8_maxEntryNorm_pos_of_inverse {n : ℕ} (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (hInv : IsInverse n A A_inv) :
    0 < maxEntryNorm hn A_inv := by
  rcases hInv with ⟨_, hRInv⟩
  by_contra hnonpos
  have hmax_zero : maxEntryNorm hn A_inv = 0 :=
    le_antisymm (le_of_not_gt hnonpos) (maxEntryNorm_nonneg hn A_inv)
  have hentry_zero : ∀ i j : Fin n, A_inv i j = 0 := by
    intro i j
    have hle : |A_inv i j| ≤ maxEntryNorm hn A_inv :=
      entry_le_maxEntryNorm hn A_inv i j
    rw [hmax_zero] at hle
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have h00 := hRInv ⟨0, hn⟩ ⟨0, hn⟩
  simp [hentry_zero] at h00








































/-- **Problem 8.8(a)**, converse singularity condition for a single-entry
rank-one perturbation.

    If `A + α e_i e_jᵀ` is singular, then necessarily
    `1 + α (A⁻¹)_{j i} = 0`. -/
theorem higham8_8_rankOne_singular_update_den_eq_zero (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv)
    (hsing : Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0) :
    1 + alpha * A_inv j i = 0 := by
  classical
  rcases hInv with ⟨hLInv, _⟩
  rcases (Matrix.exists_mulVec_eq_zero_iff
      (M := (Matrix.of A + Matrix.single i j alpha))).mpr hsing with
    ⟨x, hx_ne, hmul⟩
  have hmul' := hmul
  rw [Matrix.add_mulVec, Matrix.single_mulVec] at hmul'
  have hAx : matMulVec n A x = fun r => -alpha * finiteBasisVec i r * x j := by
    ext r
    have hr := congrFun hmul' r
    by_cases hri : r = i
    · subst r
      have hr0 : matMulVec n A x i + alpha * x j = 0 := by
        simpa [Matrix.mulVec, matMulVec, finiteBasisVec] using hr
      have hrow : matMulVec n A x i = -alpha * x j := by
        linarith
      simpa [finiteBasisVec] using hrow
    · have hr0 : matMulVec n A x r = 0 := by
        simpa [Matrix.mulVec, matMulVec, finiteBasisVec, hri] using hr
      simpa [finiteBasisVec, hri] using hr0
  have hprod : matMul n A_inv A = idMatrix n := by
    ext r c
    simpa [matMul] using hLInv r c
  have hxrepr : x = matMulVec n A_inv (fun r => -alpha * finiteBasisVec i r * x j) := by
    ext r
    calc
      x r = matMulVec n (idMatrix n) x r := by rw [matMulVec_id]
      _ = matMulVec n (matMul n A_inv A) x r := by rw [hprod]
      _ = matMulVec n A_inv (matMulVec n A x) r := by
            exact matMulVec_matMul n A_inv A x r
      _ = matMulVec n A_inv (fun r => -alpha * finiteBasisVec i r * x j) r := by
            rw [hAx]
  have hxformula : ∀ r : Fin n, x r = -alpha * A_inv r i * x j := by
    intro r
    have hr := congrFun hxrepr r
    rw [higham8_8_matMulVec_scaledBasis A_inv i (-alpha) (x j)] at hr
    simpa [mul_assoc, mul_left_comm, mul_comm] using hr
  by_contra hden
  have hcoef : (1 + alpha * A_inv j i) * x j = 0 := by
    have hj := hxformula j
    nlinarith
  have hxj_zero : x j = 0 := by
    rcases mul_eq_zero.mp hcoef with hzero | hzero
    · exact False.elim (hden hzero)
    · exact hzero
  have hx_zero : x = 0 := by
    ext r
    rw [hxformula r, hxj_zero]
    simp
  exact hx_ne hx_zero


/-- **Problem 8.8(a)**, exact solvability criterion:
`A + α e_i e_jᵀ` is singular exactly when
`α = -(A⁻¹)_{j i}^{-1}` and `(A⁻¹)_{j i} ≠ 0`. -/
theorem higham8_8_rankOne_singular_update_iff (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv) :
    Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 ↔
      A_inv j i ≠ 0 ∧ alpha = -(A_inv j i)⁻¹ := by
  constructor
  · intro hsing
    have hden :=
      higham8_8_rankOne_singular_update_den_eq_zero n A A_inv i j alpha hInv hsing
    have hentry : A_inv j i ≠ 0 := by
      intro hzero
      simp [hzero] at hden
    refine ⟨hentry, ?_⟩
    rw [inv_eq_one_div]
    have hprod : alpha * A_inv j i = -1 := by
      linarith [hden]
    have halpha : alpha = -1 / A_inv j i := (eq_div_iff hentry).2 hprod
    simpa [div_eq_mul_inv] using halpha
  · intro h
    rcases hInv with ⟨_, hRInv⟩
    rcases h with ⟨hentry, halpha⟩
    simpa [halpha] using
      higham8_8_rankOne_singular_update n A A_inv i j hRInv hentry


/-- **Problem 8.8(a)**, source magnitude formula for a singular single-entry
perturbation. -/
theorem higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (i j : Fin n) (alpha : ℝ)
    (hInv : IsInverse n A A_inv)
    (hsing : Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0) :
    |alpha| = |A_inv j i|⁻¹ := by
  rcases (higham8_8_rankOne_singular_update_iff n A A_inv i j alpha hInv).1 hsing with
    ⟨hentry, halpha⟩
  rw [halpha, abs_neg, abs_inv]


/-- **Problem 8.8(a)**, source "best place" criterion:
if `|(A⁻¹)_{r s}|` is maximal, then perturbing the `(s,r)` entry gives the
smallest-magnitude singular rank-one update. -/
theorem higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (r s : Fin n)
    (hInv : IsInverse n A A_inv)
    (hmax : |A_inv r s| = maxEntryNorm hn A_inv) :
    Matrix.det (Matrix.of A + Matrix.single s r (-(A_inv r s)⁻¹)) = 0 ∧
      ∀ i j : Fin n, ∀ alpha : ℝ,
        Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 →
          |-(A_inv r s)⁻¹| ≤ |alpha| := by
  have hmax_pos : 0 < maxEntryNorm hn A_inv :=
    higham8_8_maxEntryNorm_pos_of_inverse hn A A_inv hInv
  have hrs_pos : 0 < |A_inv r s| := by
    rw [hmax]
    exact hmax_pos
  have hrs : A_inv r s ≠ 0 := abs_pos.mp hrs_pos
  refine ⟨?_, ?_⟩
  · rcases hInv with ⟨_, hRInv⟩
    simpa using
      higham8_8_rankOne_singular_update n A A_inv s r hRInv hrs
  · intro i j alpha hsing
    rcases (higham8_8_rankOne_singular_update_iff n A A_inv i j alpha hInv).1 hsing with
      ⟨hentry, halpha⟩
    have hentry_le : |A_inv j i| ≤ |A_inv r s| := by
      rw [hmax]
      exact entry_le_maxEntryNorm hn A_inv j i
    have hentry_pos : 0 < |A_inv j i| := abs_pos.mpr hentry
    calc
      |-(A_inv r s)⁻¹| = |A_inv r s|⁻¹ := by
        rw [abs_neg, abs_inv]
      _ ≤ |A_inv j i|⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hentry_pos hentry_le
      _ = |alpha| := by
        symm
        exact higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry
          n A A_inv i j alpha hInv hsing


/-- **Problem 8.8(a)**, existence form of the Appendix A "best place" answer.

    For a nonsingular matrix, there is an inverse entry of maximal absolute
    value, and perturbing the transposed position yields a singular rank-one
    update of smallest possible magnitude. -/
theorem higham8_8_bestRankOneSingularUpdate_exists (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ)
    (hInv : IsInverse n A A_inv) :
    ∃ r s : Fin n,
      |A_inv r s| = maxEntryNorm hn A_inv ∧
      Matrix.det (Matrix.of A + Matrix.single s r (-(A_inv r s)⁻¹)) = 0 ∧
      (∀ i j : Fin n, ∀ alpha : ℝ,
        Matrix.det (Matrix.of A + Matrix.single i j alpha) = 0 →
          |-(A_inv r s)⁻¹| ≤ |alpha|) := by
  let hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  let rowMax : Fin n → ℝ :=
    fun r => Finset.sup' Finset.univ hne (fun s => |A_inv r s|)
  obtain ⟨r, _, hr⟩ := Finset.exists_mem_eq_sup' hne rowMax
  obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_sup' hne (fun s => |A_inv r s|)
  have hmax : |A_inv r s| = maxEntryNorm hn A_inv := by
    calc
      |A_inv r s| = rowMax r := hs.symm
      _ = maxEntryNorm hn A_inv := by
            simpa [rowMax, maxEntryNorm] using hr.symm
  refine ⟨r, s, hmax, ?_, ?_⟩
  exact (higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry
    n hn A A_inv r s hInv hmax).1
  exact (higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry
    n hn A A_inv r s hInv hmax).2

end NumStability
