import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# AugmentedSystem

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 exact transformed-system
    handoff: if the two triangular solves perturb the top block by `DeltaR1`
    and `DeltaR2`, and the transformed right-hand sides by `Deltaf1` and
    `Deltag`, then `[h; d₂]` and `x` satisfy the corresponding asymmetric
    transformed augmented system.

    This is exact algebra isolating the triangular-solve perturbation
    composition; it does not prove the floating-point bounds on the
    perturbations. -/
theorem LSAsymmetricAugmentedSystem.transformed_qr_solution_of_top_perturbations
    {n k : ℕ}
    (R DeltaR1 DeltaR2 : Fin n → Fin n → ℝ)
    (d1 h x Deltaf1 : Fin n → ℝ) (d2 : Fin k → ℝ)
    (g Deltag : Fin n → ℝ)
    (hRt : ∀ j : Fin n,
      ∑ i : Fin n, (R i j + DeltaR2 i j) * h i = g j + Deltag j)
    (hRx : rectMatMulVec (fun i j => R i j + DeltaR1 i j) x =
      fun i : Fin n => d1 i + Deltaf1 i - h i) :
    LSAsymmetricAugmentedSystem
      (fun i j => lsQRTallBlock R i j + lsQRTallBlock DeltaR1 i j)
      (fun i j => lsQRTallBlock R i j + lsQRTallBlock DeltaR2 i j)
      (Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2)
      (fun j : Fin n => g j + Deltag j)
      (Fin.append h d2) x := by
  constructor
  · intro row
    refine Fin.addCases
      (motive := fun row : Fin (n + k) =>
        Fin.append h d2 row +
            rectMatMulVec
              (fun i j => lsQRTallBlock R i j + lsQRTallBlock DeltaR1 i j)
              x row =
          Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2 row)
      ?top ?bottom row
    · intro i
      have hblock := lsQRTallBlock_add (n := n) (k := k) R DeltaR1
      have hmul :
          rectMatMulVec
              (fun a b => lsQRTallBlock R a b + lsQRTallBlock DeltaR1 a b)
              x (Fin.castAdd k i) =
            rectMatMulVec (fun a b => R a b + DeltaR1 a b) x i := by
        rw [hblock]
        simpa [Fin.append_left] using
          congrFun (lsQRTallBlock_mulVec
            (n := n) (k := k) (fun a b => R a b + DeltaR1 a b) x)
            (Fin.castAdd k i)
      have hRxi :
          rectMatMulVec (fun a b => R a b + DeltaR1 a b) x i =
            d1 i + Deltaf1 i - h i := congrFun hRx i
      rw [hmul, hRxi]
      simp [Fin.append_left]
    · intro i
      have hblock := lsQRTallBlock_add (n := n) (k := k) R DeltaR1
      have hmul :
          rectMatMulVec
              (fun a b => lsQRTallBlock R a b + lsQRTallBlock DeltaR1 a b)
              x (Fin.natAdd n i) = 0 := by
        rw [hblock]
        simpa [Fin.append_right] using
          congrFun (lsQRTallBlock_mulVec
            (n := n) (k := k) (fun a b => R a b + DeltaR1 a b) x)
            (Fin.natAdd n i)
      rw [hmul]
      simp [Fin.append_right]
  · intro j
    have hblock := lsQRTallBlock_add (n := n) (k := k) R DeltaR2
    calc
      ∑ i : Fin (n + k),
          (lsQRTallBlock R i j + lsQRTallBlock DeltaR2 i j) *
            Fin.append h d2 i
          =
        ∑ i : Fin (n + k),
          lsQRTallBlock (fun a b => R a b + DeltaR2 a b) i j *
            Fin.append h d2 i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [congrFun (congrFun hblock i) j]
      _ = ∑ i : Fin n, (R i j + DeltaR2 i j) * h i := by
          exact congrFun (lsQRTallBlock_transpose_mulVec_append
            (n := n) (k := k) (fun a b => R a b + DeltaR2 a b) h d2) j
      _ = g j + Deltag j := hRt j
/-- Scalar extremal branch bounds for (20.18)-(20.19): any singular value
    between `sigmaMin` and `sigmaMax` has positive branch no larger than the
    `sigmaMax` branch, and its negative-branch magnitude no smaller than the
    `sigmaMin` branch. -/
theorem lsScaledAugmentedEigenvalue_branch_extreme_bounds_of_sigma_bounds
    {alpha sigmaMin sigma sigmaMax : ℝ} (halpha : 0 ≤ alpha)
    (hsigmaMin : 0 ≤ sigmaMin) (hmin : sigmaMin ≤ sigma)
    (hmax : sigma ≤ sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax ∧
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
        |lsScaledAugmentedEigenvalueMinus alpha sigma| := by
  have hsigma : 0 ≤ sigma := le_trans hsigmaMin hmin
  constructor
  · exact
      lsScaledAugmentedEigenvaluePlus_mono_sigma_nonneg
        (alpha := alpha) (sigma := sigma) (tau := sigmaMax) hsigma hmax
  · exact
      lsScaledAugmentedEigenvalueMinus_abs_mono_sigma_nonneg
        (alpha := alpha) (sigma := sigmaMin) (tau := sigma)
        halpha hsigmaMin hmin
/-- Strict scalar extremal branch bounds for (20.18)-(20.19): any singular
    value strictly between `sigmaMin` and `sigmaMax` has positive branch
    strictly below the `sigmaMax` branch, and its negative-branch magnitude
    strictly above the `sigmaMin` branch. -/
theorem lsScaledAugmentedEigenvalue_branch_strict_extreme_bounds_of_sigma_bounds
    {alpha sigmaMin sigma sigmaMax : ℝ} (halpha : 0 ≤ alpha)
    (hsigmaMin : 0 ≤ sigmaMin) (hmin : sigmaMin < sigma)
    (hmax : sigma < sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigma <
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax ∧
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| <
        |lsScaledAugmentedEigenvalueMinus alpha sigma| := by
  have hsigma : 0 ≤ sigma := le_trans hsigmaMin (le_of_lt hmin)
  constructor
  · exact
      lsScaledAugmentedEigenvaluePlus_strictMono_sigma_nonneg
        (alpha := alpha) (sigma := sigma) (tau := sigmaMax) hsigma hmax
  · exact
      lsScaledAugmentedEigenvalueMinus_abs_strictMono_sigma_nonneg
        (alpha := alpha) (sigma := sigmaMin) (tau := sigma)
        halpha hsigmaMin hmin
/-- Scalar magnitude envelope for (20.18)-(20.19): when a singular value lies
    between the extremal singular values, both displayed branch magnitudes lie
    between the smallest negative-branch magnitude and the largest positive
    branch. -/
theorem lsScaledAugmentedEigenvalue_branch_abs_extreme_bounds_of_sigma_bounds
    {alpha sigmaMin sigma sigmaMax : ℝ} (halpha : 0 ≤ alpha)
    (hsigmaMin : 0 ≤ sigmaMin) (hmin : sigmaMin ≤ sigma)
    (hmax : sigma ≤ sigmaMax) :
    |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
        lsScaledAugmentedEigenvaluePlus alpha sigma ∧
      lsScaledAugmentedEigenvaluePlus alpha sigma ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax ∧
      |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax := by
  have hext :=
    lsScaledAugmentedEigenvalue_branch_extreme_bounds_of_sigma_bounds
      (alpha := alpha) (sigmaMin := sigmaMin) (sigma := sigma)
      (sigmaMax := sigmaMax) halpha hsigmaMin hmin hmax
  have hminus_le_plus :=
    lsScaledAugmentedEigenvalueMinus_abs_le_plus
      (alpha := alpha) (sigma := sigma) halpha
  constructor
  · exact le_trans hext.2 hminus_le_plus
  constructor
  · exact hext.1
  · exact le_trans hminus_le_plus hext.1
/-- Scalar ratio envelope for (20.18)-(20.19): each singular-value branch ratio
    is bounded by the extremal positive/minimal-negative branch ratio. -/
theorem lsScaledAugmentedEigenvalue_branch_ratio_le_extreme_of_sigma_bounds
    {alpha sigmaMin sigma sigmaMax : ℝ} (halpha : 0 ≤ alpha)
    (hsigmaMin_pos : 0 < sigmaMin) (hmin : sigmaMin ≤ sigma)
    (hmax : sigma ≤ sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigma /
        |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
  have hext :=
    lsScaledAugmentedEigenvalue_branch_extreme_bounds_of_sigma_bounds
      (alpha := alpha) (sigmaMin := sigmaMin) (sigma := sigma)
      (sigmaMax := sigmaMax) halpha (le_of_lt hsigmaMin_pos) hmin hmax
  have hsigma_pos : 0 < sigma := lt_of_lt_of_le hsigmaMin_pos hmin
  have hden_sigma_pos : 0 < |lsScaledAugmentedEigenvalueMinus alpha sigma| := by
    exact abs_pos.mpr
      (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha (ne_of_gt hsigma_pos))
  have hden_min_pos : 0 < |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    exact abs_pos.mpr
      (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigmaMin) halpha (ne_of_gt hsigmaMin_pos))
  have hfirst :
      lsScaledAugmentedEigenvaluePlus alpha sigma /
          |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigma| := by
    exact div_le_div_of_nonneg_right hext.1 (le_of_lt hden_sigma_pos)
  have hplusMax_nonneg :
      0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedEigenvaluePlus_nonneg (alpha := alpha) (sigma := sigmaMax) halpha
  have hsecond :
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    exact div_le_div_of_nonneg_left hplusMax_nonneg hden_min_pos hext.2
  exact le_trans hfirst hsecond
/-- Strict scalar branch-ratio envelope for (20.18)-(20.19): an interior
    singular value has branch ratio strictly below the ratio formed from the
    largest positive branch and the smallest negative-branch magnitude.  This
    is the strict version needed when later spectral multiplicity arguments
    identify the extremal condition-number branches. -/
theorem lsScaledAugmentedEigenvalue_branch_ratio_lt_extreme_of_strict_sigma_bounds
    {alpha sigmaMin sigma sigmaMax : ℝ} (halpha : 0 ≤ alpha)
    (hsigmaMin_pos : 0 < sigmaMin) (hmin : sigmaMin < sigma)
    (hmax : sigma < sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigma /
        |lsScaledAugmentedEigenvalueMinus alpha sigma| <
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
  have hsigma_pos : 0 < sigma := lt_trans hsigmaMin_pos hmin
  have hsigma : 0 ≤ sigma := le_of_lt hsigma_pos
  have hsigmaMax_pos : 0 < sigmaMax := lt_trans hsigma_pos hmax
  have hplus_lt :
      lsScaledAugmentedEigenvaluePlus alpha sigma <
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedEigenvaluePlus_strictMono_sigma_nonneg
      (alpha := alpha) (sigma := sigma) (tau := sigmaMax) hsigma hmax
  have hminus_lt :
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| <
        |lsScaledAugmentedEigenvalueMinus alpha sigma| :=
    lsScaledAugmentedEigenvalueMinus_abs_strictMono_sigma_nonneg
      (alpha := alpha) (sigma := sigmaMin) (tau := sigma)
      halpha (le_of_lt hsigmaMin_pos) hmin
  have hden_sigma_pos : 0 < |lsScaledAugmentedEigenvalueMinus alpha sigma| := by
    exact abs_pos.mpr
      (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha (ne_of_gt hsigma_pos))
  have hden_min_pos : 0 < |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    exact abs_pos.mpr
      (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigmaMin) halpha (ne_of_gt hsigmaMin_pos))
  have hPmax_pos : 0 < lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedEigenvaluePlus_pos_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigmaMax) halpha (ne_of_gt hsigmaMax_pos)
  have hfirst :
      lsScaledAugmentedEigenvaluePlus alpha sigma /
          |lsScaledAugmentedEigenvalueMinus alpha sigma| <
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigma| :=
    div_lt_div_of_pos_right hplus_lt hden_sigma_pos
  have hsecond :
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigma| <
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| :=
    div_lt_div_of_pos_left hPmax_pos hden_min_pos hminus_lt
  exact lt_trans hfirst hsecond
/-- Balanced-scaling scalar ratio bound for every singular value between
    `sigmaMin` and `sigmaMax`; this is the pointwise branch-ratio form used by
    the later matrix condition-number bridge in (20.19). -/
theorem lsScaledAugmentedEigenvalue_branch_ratio_le_two_sigma_ratio_of_alpha_eq_div_sqrt_two
    {alpha sigmaMin sigma sigmaMax : ℝ} (hsigmaMin_pos : 0 < sigmaMin)
    (halpha : alpha = sigmaMin / Real.sqrt 2) (hmin : sigmaMin ≤ sigma)
    (hmax : sigma ≤ sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigma /
        |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
      2 * (sigmaMax / sigmaMin) := by
  have halpha_nonneg : 0 ≤ alpha := by
    rw [halpha]
    positivity
  have hratio :=
    lsScaledAugmentedEigenvalue_branch_ratio_le_extreme_of_sigma_bounds
      (alpha := alpha) (sigmaMin := sigmaMin) (sigma := sigma)
      (sigmaMax := sigmaMax) halpha_nonneg hsigmaMin_pos hmin hmax
  have hupper :=
    lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      hsigmaMin_pos halpha (le_trans hmin hmax)
  exact le_trans hratio hupper
/-- Source-facing scalar sandwich for the balanced-scaling estimate in (20.19).
    This packages the proved branch-ratio lower and upper bounds under
    `alpha = sigma_min / sqrt 2`; the global spectral and matrix condition-number
    bridge for `C(alpha)` remains a separate target. -/
theorem lsScaledAugmentedBalancedBranchRatio_bounds_of_alpha_eq_div_sqrt_two
    {alpha sigmaMin sigmaMax : ℝ} (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMax_nonneg : 0 ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hsigmaMax : sigmaMin ≤ sigmaMax) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ∧
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
        2 * (sigmaMax / sigmaMin) := by
  constructor
  · exact
      lsScaledAugmentedBalancedBranchRatio_ge_sqrt_two_sigma_ratio_of_alpha_eq_div_sqrt_two
        (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
        hsigmaMin_pos hsigmaMax_nonneg halpha
  · exact
      lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio_of_alpha_eq_div_sqrt_two
        (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
        hsigmaMin_pos halpha hsigmaMax
/-- Diagonal-entry lower-magnitude adapter for the (20.18)-(20.19) spectral
    route.  Under the balanced choice `alpha = sigmaMin / sqrt 2`, every
    supplied diagonal entry classified as either the left-nullspace branch
    `alpha` or one of the two displayed singular-value branches has magnitude at
    least the smallest negative-branch magnitude.  This is the branch-list
    certificate needed before the reciprocal-diagonal inverse candidate can be
    instantiated. -/
theorem lsScaledAugmentedDiagonalBranch_abs_min_le_of_alpha_eq_div_sqrt_two
    {ι : Sort*} {alpha sigmaMin sigmaMax : ℝ} {d : ι → ℝ}
    (hsigmaMin_pos : 0 < sigmaMin)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hd : ∀ i : ι,
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    ∀ i : ι, |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤ |d i| := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    positivity
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsigmaMin_nonneg : 0 ≤ sigmaMin := le_of_lt hsigmaMin_pos
  have hsigmaMin_eq : sigmaMin = Real.sqrt 2 * alpha := by
    rw [halpha]
    field_simp [hsqrt2_ne]
  have hmin_abs :
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| = alpha :=
    lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg hsigmaMin_eq
  intro i
  rcases hd i with hAlpha | ⟨sigma, hmin, hmax, hbranch⟩
  · rw [hAlpha, hmin_abs, abs_of_pos halpha_pos]
  · rcases hbranch with hPlus | hMinus
    · have hbounds :=
        lsScaledAugmentedEigenvalue_branch_abs_extreme_bounds_of_sigma_bounds
          (alpha := alpha) (sigmaMin := sigmaMin) (sigma := sigma)
          (sigmaMax := sigmaMax) halpha_nonneg hsigmaMin_nonneg hmin hmax
      have hplus_nonneg :
          0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigma :=
        lsScaledAugmentedEigenvaluePlus_nonneg
          (alpha := alpha) (sigma := sigma) halpha_nonneg
      rw [hPlus, abs_of_nonneg hplus_nonneg]
      exact hbounds.1
    · have hminus :=
        lsScaledAugmentedEigenvalueMinus_abs_mono_sigma_nonneg
          (alpha := alpha) (sigma := sigmaMin) (tau := sigma)
          halpha_nonneg hsigmaMin_nonneg hmin
      rw [hMinus]
      exact hminus
/-- Nonzero diagonal-entry corollary of
    `lsScaledAugmentedDiagonalBranch_abs_min_le_of_alpha_eq_div_sqrt_two`.
    Once the later (20.18) eigenbasis proof classifies the diagonal list into
    the displayed branch shapes, the balanced branch formulas supply the
    nonzero certificates required by the reciprocal-diagonal inverse theorem. -/
theorem lsScaledAugmentedDiagonalBranch_ne_zero_of_alpha_eq_div_sqrt_two
    {ι : Sort*} {alpha sigmaMin sigmaMax : ℝ} {d : ι → ℝ}
    (hsigmaMin_pos : 0 < sigmaMin)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hd : ∀ i : ι,
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    ∀ i : ι, d i ≠ 0 := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    positivity
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsigmaMin_eq : sigmaMin = Real.sqrt 2 * alpha := by
    rw [halpha]
    field_simp [hsqrt2_ne]
  have hmin_abs :
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| = alpha :=
    lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg hsigmaMin_eq
  have hmin_abs_pos :
      0 < |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    rw [hmin_abs]
    exact halpha_pos
  have hle :=
    lsScaledAugmentedDiagonalBranch_abs_min_le_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      (d := d) hsigmaMin_pos halpha hd
  intro i hzero
  have hpos : 0 < |d i| := lt_of_lt_of_le hmin_abs_pos (hle i)
  rw [hzero, abs_zero] at hpos
  exact (lt_irrefl (0 : ℝ)) hpos
/-- Reciprocal diagonal-entry bound for the balanced (20.19) inverse-candidate
    route.  If a supplied diagonal list is classified by the source branch
    formulas, then every reciprocal diagonal magnitude is bounded by the
    reciprocal of the smallest negative-branch magnitude. -/
theorem lsScaledAugmentedDiagonalBranch_recip_abs_le_of_alpha_eq_div_sqrt_two
    {ι : Sort*} {alpha sigmaMin sigmaMax : ℝ} {d : ι → ℝ}
    (hsigmaMin_pos : 0 < sigmaMin)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hd : ∀ i : ι,
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    ∀ i : ι, |(d i)⁻¹| ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹ := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    positivity
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsigmaMin_eq : sigmaMin = Real.sqrt 2 * alpha := by
    rw [halpha]
    field_simp [hsqrt2_ne]
  have hmin_abs :
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| = alpha :=
    lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg hsigmaMin_eq
  have hmin_abs_pos :
      0 < |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    rw [hmin_abs]
    exact halpha_pos
  have hle :=
    lsScaledAugmentedDiagonalBranch_abs_min_le_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      (d := d) hsigmaMin_pos halpha hd
  intro i
  rw [abs_inv]
  exact inv_anti₀ hmin_abs_pos (hle i)
/-- Diagonal-entry upper-magnitude adapter for the (20.18)-(20.19) spectral
    route.  Under the balanced choice `alpha = sigmaMin / sqrt 2`, every
    supplied diagonal entry classified as either the left-nullspace branch
    `alpha` or one of the two displayed singular-value branches has magnitude
    at most the largest positive-branch value. -/
theorem lsScaledAugmentedDiagonalBranch_abs_le_max_of_alpha_eq_div_sqrt_two
    {ι : Sort*} {alpha sigmaMin sigmaMax : ℝ} {d : ι → ℝ}
    (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hd : ∀ i : ι,
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    ∀ i : ι, |d i| ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    positivity
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha_pos
  have hsigmaMin_nonneg : 0 ≤ sigmaMin := le_of_lt hsigmaMin_pos
  have hsigmaMin_eq : sigmaMin = Real.sqrt 2 * alpha := by
    rw [halpha]
    field_simp [hsqrt2_ne]
  have hmin_abs :
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| = alpha :=
    lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg hsigmaMin_eq
  have hboundsMin :=
    lsScaledAugmentedEigenvalue_branch_abs_extreme_bounds_of_sigma_bounds
      (alpha := alpha) (sigmaMin := sigmaMin) (sigma := sigmaMin)
      (sigmaMax := sigmaMax) halpha_nonneg hsigmaMin_nonneg le_rfl
      hsigmaMin_le_max
  have halpha_le_max :
      alpha ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax := by
    calc
      alpha = |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := hmin_abs.symm
      _ ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax := hboundsMin.2.2
  intro i
  rcases hd i with hAlpha | ⟨sigma, hmin, hmax, hbranch⟩
  · rw [hAlpha, abs_of_pos halpha_pos]
    exact halpha_le_max
  · have hbounds :=
      lsScaledAugmentedEigenvalue_branch_abs_extreme_bounds_of_sigma_bounds
        (alpha := alpha) (sigmaMin := sigmaMin) (sigma := sigma)
        (sigmaMax := sigmaMax) halpha_nonneg hsigmaMin_nonneg hmin hmax
    rcases hbranch with hPlus | hMinus
    · have hplus_nonneg :
          0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigma :=
        lsScaledAugmentedEigenvaluePlus_nonneg
          (alpha := alpha) (sigma := sigma) halpha_nonneg
      rw [hPlus, abs_of_nonneg hplus_nonneg]
      exact hbounds.2.1
    · rw [hMinus]
      exact hbounds.2.2
/-- Source-facing condition-number bridge for (20.18)-(20.19): a witnessed
    positive branch divided by the magnitude of a witnessed negative branch is
    bounded by the repository `κ₂` product for `C(alpha)` and an explicit
    two-sided inverse candidate.  This still leaves the global spectral
    multiplicity/extremal-eigenvalue proof open. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_kappa2
    {m n : ℕ} {alpha sigmaPlus sigmaMinus : ℝ}
    {A : Fin m → Fin n → ℝ}
    {Cinv : Fin (m + n) → Fin (m + n) → ℝ}
    {uPlus uMinus : Fin m → ℝ} {vPlus vMinus : Fin n → ℝ}
    (hInv : IsInverse (m + n) (lsScaledAugmentedMatrix alpha A) Cinv)
    (hAvPlus : rectMatMulVec A vPlus = fun i => sigmaPlus * uPlus i)
    (hATuPlus : (fun j : Fin n => ∑ i : Fin m, A i j * uPlus i) =
      fun j => sigmaPlus * vPlus j)
    (hAvMinus : rectMatMulVec A vMinus = fun i => sigmaMinus * uMinus i)
    (hATuMinus : (fun j : Fin n => ∑ i : Fin m, A i j * uMinus i) =
      fun j => sigmaMinus * vMinus j)
    (halpha : 0 ≤ alpha)
    (hsigmaPlus : sigmaPlus ≠ 0) (hvPlus : vPlus ≠ 0)
    (hsigmaMinus : sigmaMinus ≠ 0) (hvMinus : vMinus ≠ 0) :
    |lsScaledAugmentedEigenvaluePlus alpha sigmaPlus| /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMinus| ≤
      kappa2 (lsScaledAugmentedMatrix alpha A) Cinv := by
  have hC :
      finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A)
        (opNorm2 (lsScaledAugmentedMatrix alpha A)) :=
    finiteOpNorm2Le_of_opNorm2Le (lsScaledAugmentedMatrix alpha A)
      (opNorm2Le_opNorm2 (lsScaledAugmentedMatrix alpha A))
  have hCinv : finiteOpNorm2Le Cinv (opNorm2 Cinv) :=
    finiteOpNorm2Le_of_opNorm2Le Cinv (opNorm2Le_opNorm2 Cinv)
  simpa [kappa2] using
    lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_opNorm_mul_inverseOpNorm
      (hC := hC) (hCinv := hCinv) (hLeft := hInv.1)
      (hAvPlus := hAvPlus) (hATuPlus := hATuPlus)
      (hAvMinus := hAvMinus) (hATuMinus := hATuMinus)
      halpha hsigmaPlus hvPlus hsigmaMinus hvMinus
/-- Balanced-scaling lower half of the (20.19) condition-number route: under
    `alpha = sigmaMin / sqrt 2`, witnessed extremal singular-pair branches give
    the source scalar lower bound `sqrt 2 * sigmaMax/sigmaMin` below the
    repository `κ₂` product for `C(alpha)` and an explicit inverse candidate.
    This combines the scalar branch-ratio lower bound with the local `κ₂`
    eigenpair bridge; it does not prove the complete eigenvalue list or that the
    supplied pairs are a full singular-vector basis. -/
theorem lsScaledAugmentedMatrix_singularPair_balanced_sigma_ratio_le_kappa2_of_alpha_eq_div_sqrt_two
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ}
    {A : Fin m → Fin n → ℝ}
    {Cinv : Fin (m + n) → Fin (m + n) → ℝ}
    {uMax uMin : Fin m → ℝ} {vMax vMin : Fin n → ℝ}
    (hInv : IsInverse (m + n) (lsScaledAugmentedMatrix alpha A) Cinv)
    (hAvMax : rectMatMulVec A vMax = fun i => sigmaMax * uMax i)
    (hATuMax : (fun j : Fin n => ∑ i : Fin m, A i j * uMax i) =
      fun j => sigmaMax * vMax j)
    (hAvMin : rectMatMulVec A vMin = fun i => sigmaMin * uMin i)
    (hATuMin : (fun j : Fin n => ∑ i : Fin m, A i j * uMin i) =
      fun j => sigmaMin * vMin j)
    (hsigmaMin_pos : 0 < sigmaMin) (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hvMax : vMax ≠ 0) (hvMin : vMin ≠ 0) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
      kappa2 (lsScaledAugmentedMatrix alpha A) Cinv := by
  have hsigmaMax_pos : 0 < sigmaMax :=
    lt_of_lt_of_le hsigmaMin_pos hsigmaMin_le_max
  have hsigmaMax_nonneg : 0 ≤ sigmaMax := le_of_lt hsigmaMax_pos
  have halpha_nonneg : 0 ≤ alpha := by
    rw [halpha]
    positivity
  have hscalar :
      Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| :=
    lsScaledAugmentedBalancedBranchRatio_ge_sqrt_two_sigma_ratio_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      hsigmaMin_pos hsigmaMax_nonneg halpha
  have hkappa :
      |lsScaledAugmentedEigenvaluePlus alpha sigmaMax| /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
        kappa2 (lsScaledAugmentedMatrix alpha A) Cinv :=
    lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_kappa2
      (hInv := hInv)
      (hAvPlus := hAvMax) (hATuPlus := hATuMax)
      (hAvMinus := hAvMin) (hATuMinus := hATuMin)
      halpha_nonneg (ne_of_gt hsigmaMax_pos) hvMax
      (ne_of_gt hsigmaMin_pos) hvMin
  have hplus_nonneg :
      0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedEigenvaluePlus_nonneg
      (alpha := alpha) (sigma := sigmaMax) halpha_nonneg
  rw [abs_of_nonneg hplus_nonneg] at hkappa
  exact le_trans hscalar hkappa
/-- Equations (20.18)-(20.19) `κ₂` upper-bound handoff: supplied orthogonal
    diagonalizations for `C(alpha)` and for an explicit inverse candidate,
    together with uniform bounds on the displayed eigenvalue magnitudes, give a
    source-facing `κ₂ C(alpha) Cinv <= L * D` product bound.  This still leaves
    the construction of those diagonalizations and the inverse candidate open. -/
theorem lsScaledAugmentedMatrix_kappa2_le_mul_of_orthogonal_diagonalizations
    {m n : ℕ} {alpha L D : ℝ} {A : Fin m → Fin n → ℝ}
    {Cinv Q Qinv : Fin (m + n) → Fin (m + n) → ℝ}
    {d dinv : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hdiagInv : Cinv =
      finiteMatMul Qinv (finiteMatMul (finiteDiagonal dinv) (matTranspose Qinv)))
    (hQ : IsOrthogonal (m + n) Q) (hQinv : IsOrthogonal (m + n) Qinv)
    (hL : 0 ≤ L) (hd : ∀ i : Fin (m + n), |d i| ≤ L)
    (hD : 0 ≤ D) (hdinv : ∀ i : Fin (m + n), |dinv i| ≤ D) :
    kappa2 (lsScaledAugmentedMatrix alpha A) Cinv ≤ L * D :=
  kappa2_le_mul_of_isOrthogonal_diagonalizations
    hdiag hdiagInv hQ hQinv hL hd hD hdinv
/-- One-diagonalization version of the (20.18)-(20.19) `κ₂` upper-bound
    handoff: if `C(alpha)` is orthogonally diagonalized and the reciprocal
    diagonal entries are bounded by `D`, then the reciprocal-diagonal inverse
    candidate satisfies `κ₂ C(alpha) Cinv <= L * D`. -/
theorem lsScaledAugmentedMatrix_kappa2_le_mul_of_orthogonal_diagonalization_inverse_candidate
    {m n : ℕ} {alpha L D : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hL : 0 ≤ L) (hd : ∀ i : Fin (m + n), |d i| ≤ L)
    (hD : 0 ≤ D) (hdinv : ∀ i : Fin (m + n), |(d i)⁻¹| ≤ D) :
    kappa2 (lsScaledAugmentedMatrix alpha A)
      (finiteMatMul Q
        (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ≤
      L * D :=
  kappa2_le_mul_of_isOrthogonal_diagonalization_inverse_candidate
    hdiag hQ hL hd hD hdinv
/-- Balanced-scaling upper half of the (20.19) condition-number route, with
    the inverse candidate fixed to the reciprocal diagonal in the same
    orthogonal eigenbasis as `C(alpha)`.  This removes the previous need for a
    separately supplied inverse diagonalization; it still assumes the complete
    diagonalization and diagonal magnitude bounds. -/
theorem lsScaledAugmentedMatrix_kappa2_le_two_sigma_ratio_of_balanced_orthogonal_diagonalization_inverse_candidate
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hd : ∀ i : Fin (m + n),
      |d i| ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax)
    (hdinv : ∀ i : Fin (m + n),
      |(d i)⁻¹| ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹)
    (hsigmaMin_pos : 0 < sigmaMin) (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2) :
    kappa2 (lsScaledAugmentedMatrix alpha A)
      (finiteMatMul Q
        (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ≤
      2 * (sigmaMax / sigmaMin) := by
  have halpha_nonneg : 0 ≤ alpha := by
    rw [halpha]
    positivity
  have hL_nonneg :
      0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedEigenvaluePlus_nonneg
      (alpha := alpha) (sigma := sigmaMax) halpha_nonneg
  have hD_nonneg :
      0 ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹ :=
    inv_nonneg.mpr (abs_nonneg _)
  have hkappa :
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul Q
            (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax *
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹ :=
    lsScaledAugmentedMatrix_kappa2_le_mul_of_orthogonal_diagonalization_inverse_candidate
      (hdiag := hdiag) (hQ := hQ)
      (hL := hL_nonneg) (hd := hd)
      (hD := hD_nonneg) (hdinv := hdinv)
  have hkappa_ratio :
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul Q
            (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    simpa [div_eq_mul_inv] using hkappa
  have hscalar :
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
        2 * (sigmaMax / sigmaMin) :=
    lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      hsigmaMin_pos halpha hsigmaMin_le_max
  exact le_trans hkappa_ratio hscalar
/-- Branch-classified version of the (20.18)-(20.19) inverse-candidate
    handoff.  Once the supplied complete orthogonal diagonalization lists only
    the left-nullspace branch `alpha` and the displayed plus/minus branches
    over `[sigmaMin, sigmaMax]`, the balanced scalar certificates prove the
    reciprocal diagonal in the same eigenbasis is a two-sided inverse. -/
theorem lsScaledAugmentedMatrix_isInverse_of_balanced_branch_orthogonal_diagonalization
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hsigmaMin_pos : 0 < sigmaMin)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hd : ∀ i : Fin (m + n),
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    IsInverse (m + n) (lsScaledAugmentedMatrix alpha A)
      (finiteMatMul Q
        (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) :=
  lsScaledAugmentedMatrix_isInverse_of_orthogonal_diagonalization
    (hdiag := hdiag) (hQ := hQ)
    (hd :=
      lsScaledAugmentedDiagonalBranch_ne_zero_of_alpha_eq_div_sqrt_two
        (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
        (d := d) hsigmaMin_pos halpha hd)
/-- Branch-classified balanced upper half of (20.19).  This packages the
    diagonal upper bound, reciprocal lower-branch bound, and reciprocal-diagonal
    inverse candidate behind a single branch-list hypothesis.  It still leaves
    open the construction of the complete eigenbasis and proof that the printed
    branch list exhausts the spectrum with multiplicities. -/
theorem lsScaledAugmentedMatrix_kappa2_le_two_sigma_ratio_of_balanced_branch_orthogonal_diagonalization
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hd : ∀ i : Fin (m + n),
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    kappa2 (lsScaledAugmentedMatrix alpha A)
      (finiteMatMul Q
        (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ≤
      2 * (sigmaMax / sigmaMin) := by
  have hdUpper :
      ∀ i : Fin (m + n),
        |d i| ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedDiagonalBranch_abs_le_max_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      (d := d) hsigmaMin_pos hsigmaMin_le_max halpha hd
  have hdRecip :
      ∀ i : Fin (m + n),
        |(d i)⁻¹| ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹ :=
    lsScaledAugmentedDiagonalBranch_recip_abs_le_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      (d := d) hsigmaMin_pos halpha hd
  exact
    lsScaledAugmentedMatrix_kappa2_le_two_sigma_ratio_of_balanced_orthogonal_diagonalization_inverse_candidate
      (hdiag := hdiag) (hQ := hQ) (hd := hdUpper) (hdinv := hdRecip)
      hsigmaMin_pos hsigmaMin_le_max halpha
/-- Branch-classified balanced lower half of (20.19).  Combining a supplied
    branch-classified orthogonal diagonalization with supplied extremal
    singular-pair witnesses gives the lower source certificate
    `sqrt 2 * sigmaMax/sigmaMin <= κ₂ C(alpha) Cinv` for the same
    reciprocal-diagonal inverse candidate used by the upper bound. -/
theorem lsScaledAugmentedMatrix_singularPair_balanced_sigma_ratio_le_kappa2_of_balanced_branch_orthogonal_diagonalization
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ}
    {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    {uMax uMin : Fin m → ℝ} {vMax vMin : Fin n → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hAvMax : rectMatMulVec A vMax = fun i => sigmaMax * uMax i)
    (hATuMax : (fun j : Fin n => ∑ i : Fin m, A i j * uMax i) =
      fun j => sigmaMax * vMax j)
    (hAvMin : rectMatMulVec A vMin = fun i => sigmaMin * uMin i)
    (hATuMin : (fun j : Fin n => ∑ i : Fin m, A i j * uMin i) =
      fun j => sigmaMin * vMin j)
    (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hvMax : vMax ≠ 0) (hvMin : vMin ≠ 0)
    (hd : ∀ i : Fin (m + n),
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
      kappa2 (lsScaledAugmentedMatrix alpha A)
        (finiteMatMul Q
          (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) := by
  have hInv :
      IsInverse (m + n) (lsScaledAugmentedMatrix alpha A)
        (finiteMatMul Q
          (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) :=
    lsScaledAugmentedMatrix_isInverse_of_balanced_branch_orthogonal_diagonalization
      (hdiag := hdiag) (hQ := hQ) hsigmaMin_pos halpha hd
  exact
    lsScaledAugmentedMatrix_singularPair_balanced_sigma_ratio_le_kappa2_of_alpha_eq_div_sqrt_two
      (hInv := hInv)
      (hAvMax := hAvMax) (hATuMax := hATuMax)
      (hAvMin := hAvMin) (hATuMin := hATuMin)
      hsigmaMin_pos hsigmaMin_le_max halpha hvMax hvMin
/-- Two-sided branch-classified balanced (20.19) condition-number certificate.
    A supplied branch-classified orthogonal diagonalization gives the
    reciprocal-diagonal inverse candidate and the upper bound; supplied
    extremal singular-pair witnesses give the lower branch-ratio bound.  The
    complete eigenbasis, multiplicity, branch-exhaustiveness, and extremality
    proofs remain separate obligations. -/
theorem lsScaledAugmentedMatrix_kappa2_bounds_of_balanced_branch_orthogonal_diagonalization_and_singular_pairs
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ}
    {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    {uMax uMin : Fin m → ℝ} {vMax vMin : Fin n → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hAvMax : rectMatMulVec A vMax = fun i => sigmaMax * uMax i)
    (hATuMax : (fun j : Fin n => ∑ i : Fin m, A i j * uMax i) =
      fun j => sigmaMax * vMax j)
    (hAvMin : rectMatMulVec A vMin = fun i => sigmaMin * uMin i)
    (hATuMin : (fun j : Fin n => ∑ i : Fin m, A i j * uMin i) =
      fun j => sigmaMin * vMin j)
    (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2)
    (hvMax : vMax ≠ 0) (hvMin : vMin ≠ 0)
    (hd : ∀ i : Fin (m + n),
      d i = alpha ∨
        ∃ sigma : ℝ, sigmaMin ≤ sigma ∧ sigma ≤ sigmaMax ∧
          (d i = lsScaledAugmentedEigenvaluePlus alpha sigma ∨
            d i = lsScaledAugmentedEigenvalueMinus alpha sigma)) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul Q
            (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul Q
            (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) ≤
        2 * (sigmaMax / sigmaMin) := by
  constructor
  · exact
      lsScaledAugmentedMatrix_singularPair_balanced_sigma_ratio_le_kappa2_of_balanced_branch_orthogonal_diagonalization
        (hdiag := hdiag) (hQ := hQ)
        (hAvMax := hAvMax) (hATuMax := hATuMax)
        (hAvMin := hAvMin) (hATuMin := hATuMin)
        hsigmaMin_pos hsigmaMin_le_max halpha hvMax hvMin hd
  · exact
      lsScaledAugmentedMatrix_kappa2_le_two_sigma_ratio_of_balanced_branch_orthogonal_diagonalization
        (hdiag := hdiag) (hQ := hQ)
        hsigmaMin_pos hsigmaMin_le_max halpha hd
/-- Balanced-scaling upper half of the (20.19) condition-number route.  If
    `alpha = sigmaMin / sqrt 2`, `C(alpha)` and an inverse candidate have
    supplied orthogonal diagonalizations whose diagonal magnitudes are bounded
    by the source extremal branches, then `κ₂ C(alpha) Cinv` is bounded by
    `2 * sigmaMax / sigmaMin`.

    This is a spectral-certificate theorem: it does not construct the complete
    eigenbasis, prove that the diagonal list is exactly the (20.18) branch list,
    or identify the supplied inverse candidate. -/
theorem lsScaledAugmentedMatrix_kappa2_le_two_sigma_ratio_of_balanced_orthogonal_diagonalizations
    {m n : ℕ} {alpha sigmaMin sigmaMax : ℝ} {A : Fin m → Fin n → ℝ}
    {Cinv Q Qinv : Fin (m + n) → Fin (m + n) → ℝ}
    {d dinv : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hdiagInv : Cinv =
      finiteMatMul Qinv (finiteMatMul (finiteDiagonal dinv) (matTranspose Qinv)))
    (hQ : IsOrthogonal (m + n) Q) (hQinv : IsOrthogonal (m + n) Qinv)
    (hd : ∀ i : Fin (m + n),
      |d i| ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax)
    (hdinv : ∀ i : Fin (m + n),
      |dinv i| ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹)
    (hsigmaMin_pos : 0 < sigmaMin) (hsigmaMin_le_max : sigmaMin ≤ sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2) :
    kappa2 (lsScaledAugmentedMatrix alpha A) Cinv ≤
      2 * (sigmaMax / sigmaMin) := by
  have hsigmaMax_pos : 0 < sigmaMax :=
    lt_of_lt_of_le hsigmaMin_pos hsigmaMin_le_max
  have halpha_nonneg : 0 ≤ alpha := by
    rw [halpha]
    positivity
  have hL_nonneg :
      0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax :=
    lsScaledAugmentedEigenvaluePlus_nonneg
      (alpha := alpha) (sigma := sigmaMax) halpha_nonneg
  have hD_nonneg :
      0 ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹ :=
    inv_nonneg.mpr (abs_nonneg _)
  have hkappa :
      kappa2 (lsScaledAugmentedMatrix alpha A) Cinv ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax *
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|⁻¹ :=
    lsScaledAugmentedMatrix_kappa2_le_mul_of_orthogonal_diagonalizations
      (hdiag := hdiag) (hdiagInv := hdiagInv)
      (hQ := hQ) (hQinv := hQinv)
      (hL := hL_nonneg) (hd := hd)
      (hD := hD_nonneg) (hdinv := hdinv)
  have hkappa_ratio :
      kappa2 (lsScaledAugmentedMatrix alpha A) Cinv ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
    simpa [div_eq_mul_inv] using hkappa
  have hscalar :
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
        2 * (sigmaMax / sigmaMin) :=
    lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio_of_alpha_eq_div_sqrt_two
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      hsigmaMin_pos halpha hsigmaMin_le_max
  exact le_trans hkappa_ratio hscalar
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    source-shaped condition-number handoff from a complete branch enumeration.
    A complete equivalence for the displayed plus/minus/left-null branch family,
    together with min/max branch indices and scalar range bounds, gives the
    two-sided balanced `κ₂` certificate for the reciprocal-diagonal inverse
    candidate.  This removes the separate supplied `Q`, diagonal list, branch
    classification proof, and extremal singular-pair witnesses from the final
    handoff surface; deriving the complete equivalence from an SVD/nullspace
    basis remains the source-side obligation. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_complete_branch_equiv_and_extreme_branches
    {m n : ℕ} {ι κ : Type*} {alpha sigmaMin sigmaMax : ℝ}
    {A : Fin m → Fin n → ℝ} {sigma : ι → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (e : Fin (m + n) ≃ Sum (Sum ι ι) κ)
    (iMin iMax : ι)
    (hu : ∀ i : ι, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : ι, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : κ, vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : ι, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : ι, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : κ, k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (hsigmaRange : ∀ i : ι, sigmaMin ≤ sigma i ∧ sigma i ≤ sigmaMax)
    (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMin_eq : sigma iMin = sigmaMin)
    (hsigmaMax_eq : sigma iMax = sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r)
            (finiteMatMul
              (finiteDiagonal
                (fun c : Fin (m + n) =>
                  (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma (e c))⁻¹))
              (matTranspose
                (fun r c : Fin (m + n) =>
                  lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r)))) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r)
            (finiteMatMul
              (finiteDiagonal
                (fun c : Fin (m + n) =>
                  (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma (e c))⁻¹))
              (matTranspose
                (fun r c : Fin (m + n) =>
                  lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r)))) ≤
        2 * (sigmaMax / sigmaMin) := by
  classical
  let Q : Fin (m + n) → Fin (m + n) → ℝ :=
    fun r c => lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r
  let d : Fin (m + n) → ℝ :=
    fun c => lsScaledAugmentedMatrixBranchEigenvalue alpha sigma (e c)
  have halpha_nonneg : 0 ≤ alpha := by
    rw [halpha]
    positivity
  have hsigma_nonzero : ∀ i : ι, sigma i ≠ 0 := by
    intro i hzero
    have hpos : 0 < sigma i :=
      lt_of_lt_of_le hsigmaMin_pos (hsigmaRange i).1
    exact (ne_of_gt hpos) hzero
  have hQ : IsOrthogonal (m + n) Q :=
    lsScaledAugmentedMatrixBranchVector_isOrthogonal_of_complete_equiv
      (alpha := alpha) (sigma := sigma) (A := A) (u := u) (v := v) (w := w)
      e hu hv hw hleft hright hnull hAv hATu hATw halpha_nonneg
      hsigma_nonzero
  have hdiag :
      lsScaledAugmentedMatrix alpha A =
        finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)) := by
    simpa [Q, d] using
      lsScaledAugmentedMatrix_branch_orthogonal_diagonalization_of_complete_equiv
        (alpha := alpha) (sigma := sigma) (A := A) (u := u) (v := v) (w := w)
        e hu hv hw hleft hright hnull hAv hATu hATw halpha_nonneg
        hsigma_nonzero
  have hsigmaMin_le_max : sigmaMin ≤ sigmaMax :=
    le_trans (hsigmaRange iMin).1 (hsigmaRange iMin).2
  have hvMax : v iMax ≠ 0 := by
    intro hzero
    have hsq_zero : vecNorm2Sq (v iMax) = 0 := by
      simp [hzero, vecNorm2Sq]
    linarith [hv iMax]
  have hvMin : v iMin ≠ 0 := by
    intro hzero
    have hsq_zero : vecNorm2Sq (v iMin) = 0 := by
      simp [hzero, vecNorm2Sq]
    linarith [hv iMin]
  have hAvMax :
      rectMatMulVec A (v iMax) = fun r => sigmaMax * u iMax r := by
    simpa [hsigmaMax_eq] using hAv iMax
  have hATuMax :
      (fun j : Fin n => ∑ r : Fin m, A r j * u iMax r) =
        fun j => sigmaMax * v iMax j := by
    simpa [hsigmaMax_eq] using hATu iMax
  have hAvMin :
      rectMatMulVec A (v iMin) = fun r => sigmaMin * u iMin r := by
    simpa [hsigmaMin_eq] using hAv iMin
  have hATuMin :
      (fun j : Fin n => ∑ r : Fin m, A r j * u iMin r) =
        fun j => sigmaMin * v iMin j := by
    simpa [hsigmaMin_eq] using hATu iMin
  have hd : ∀ c : Fin (m + n),
      d c = alpha ∨
        ∃ sigma0 : ℝ, sigmaMin ≤ sigma0 ∧ sigma0 ≤ sigmaMax ∧
          (d c = lsScaledAugmentedEigenvaluePlus alpha sigma0 ∨
            d c = lsScaledAugmentedEigenvalueMinus alpha sigma0) := by
    intro c
    rcases hc : e c with ((i | i) | k)
    · right
      refine ⟨sigma i, (hsigmaRange i).1, (hsigmaRange i).2, ?_⟩
      left
      simp [d, lsScaledAugmentedMatrixBranchEigenvalue, hc]
    · right
      refine ⟨sigma i, (hsigmaRange i).1, (hsigmaRange i).2, ?_⟩
      right
      simp [d, lsScaledAugmentedMatrixBranchEigenvalue, hc]
    · left
      simp [d, lsScaledAugmentedMatrixBranchEigenvalue, hc]
  simpa [Q, d] using
    lsScaledAugmentedMatrix_kappa2_bounds_of_balanced_branch_orthogonal_diagonalization_and_singular_pairs
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax) (A := A)
      (Q := Q) (d := d) (uMax := u iMax) (uMin := u iMin)
      (vMax := v iMax) (vMin := v iMin)
      (hdiag := hdiag) (hQ := hQ)
      (hAvMax := hAvMax) (hATuMax := hATuMax)
      (hAvMin := hAvMin) (hATuMin := hATuMin)
      hsigmaMin_pos hsigmaMin_le_max halpha hvMax hvMin hd
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    cardinality-based source-shaped condition-number handoff.  This constructs
    the complete branch enumeration from the displayed count
    `2 * card ι + card κ = m+n`, then applies the complete-branch theorem to
    obtain the balanced two-sided `κ₂` certificate for the reciprocal-diagonal
    inverse candidate. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_branch_cardinality_and_extreme_branches
    {m n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    {alpha sigmaMin sigmaMax : ℝ}
    {A : Fin m → Fin n → ℝ} {sigma : ι → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (hcard : 2 * Fintype.card ι + Fintype.card κ = m + n)
    (iMin iMax : ι)
    (hu : ∀ i : ι, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : ι, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : κ, vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : ι, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : ι, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : κ, k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (hsigmaRange : ∀ i : ι, sigmaMin ≤ sigma i ∧ sigma i ≤ sigmaMax)
    (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMin_eq : sigma iMin = sigmaMin)
    (hsigmaMax_eq : sigma iMax = sigmaMax)
    (halpha : alpha = sigmaMin / Real.sqrt 2) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)
            (finiteMatMul
              (finiteDiagonal
                (fun c : Fin (m + n) =>
                  (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c))⁻¹))
              (matTranspose
                (fun r c : Fin (m + n) =>
                  lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)))) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)
            (finiteMatMul
              (finiteDiagonal
                (fun c : Fin (m + n) =>
                  (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c))⁻¹))
              (matTranspose
                (fun r c : Fin (m + n) =>
                  lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)))) ≤
        2 * (sigmaMax / sigmaMin) := by
  let e : Fin (m + n) ≃ Sum (Sum ι ι) κ :=
    lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard
  simpa [e] using
    lsScaledAugmentedMatrix_kappa2_bounds_of_complete_branch_equiv_and_extreme_branches
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax) (A := A)
      (sigma := sigma) (u := u) (v := v) (w := w)
      (e := e) iMin iMax hu hv hw hleft hright hnull hAv hATu hATw
      hsigmaRange hsigmaMin_pos hsigmaMin_eq hsigmaMax_eq halpha
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    finite-extrema version of the cardinality-based condition-number handoff.
    For a nonempty finite singular branch family with positive branch values,
    the min/max branch indices are chosen internally from the finite set, so the
    theorem surface only exposes the source branch data and branch-count
    identity. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_branch_cardinality_and_finite_extrema
    {m n : ℕ} {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    {alpha : ℝ} {A : Fin m → Fin n → ℝ} {sigma : ι → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (hcard : 2 * Fintype.card ι + Fintype.card κ = m + n)
    (hu : ∀ i : ι, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : ι, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : κ, vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : ι, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : ι, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : κ, k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (hsigma_pos : ∀ i : ι, 0 < sigma i)
    (halpha :
      alpha = lsScaledAugmentedBranchSigmaMin sigma / Real.sqrt 2) :
    Real.sqrt 2 *
          (lsScaledAugmentedBranchSigmaMax sigma /
            lsScaledAugmentedBranchSigmaMin sigma) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)
            (finiteMatMul
              (finiteDiagonal
                (fun c : Fin (m + n) =>
                  (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c))⁻¹))
              (matTranspose
                (fun r c : Fin (m + n) =>
                  lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)))) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (finiteMatMul
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)
            (finiteMatMul
              (finiteDiagonal
                (fun c : Fin (m + n) =>
                  (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c))⁻¹))
              (matTranspose
                (fun r c : Fin (m + n) =>
                  lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                    (lsScaledAugmentedBranchEquivOfCardEq m n ι κ hcard c) r)))) ≤
        2 *
          (lsScaledAugmentedBranchSigmaMax sigma /
            lsScaledAugmentedBranchSigmaMin sigma) := by
  have hsigmaRange : ∀ i : ι,
      lsScaledAugmentedBranchSigmaMin sigma ≤ sigma i ∧
        sigma i ≤ lsScaledAugmentedBranchSigmaMax sigma := by
    intro i
    exact
      ⟨lsScaledAugmentedBranchSigmaMin_le sigma i,
        lsScaledAugmentedBranchSigma_le_max sigma i⟩
  have hsigmaMin_pos : 0 < lsScaledAugmentedBranchSigmaMin sigma := by
    simpa [lsScaledAugmentedBranchSigmaMin] using
      hsigma_pos (lsScaledAugmentedBranchSigmaMinIndex sigma)
  simpa using
    lsScaledAugmentedMatrix_kappa2_bounds_of_branch_cardinality_and_extreme_branches
      (alpha := alpha)
      (sigmaMin := lsScaledAugmentedBranchSigmaMin sigma)
      (sigmaMax := lsScaledAugmentedBranchSigmaMax sigma)
      (A := A) (sigma := sigma) (u := u) (v := v) (w := w)
      hcard (lsScaledAugmentedBranchSigmaMinIndex sigma)
      (lsScaledAugmentedBranchSigmaMaxIndex sigma)
      hu hv hw hleft hright hnull hAv hATu hATw hsigmaRange
      hsigmaMin_pos rfl rfl halpha
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    source-dimension finite-extrema condition-number handoff.  Under `n <= m`,
    supplied source-shaped singular-vector and left-nullspace branch data
    determine the full branch enumeration and finite extrema internally, giving
    the displayed balanced two-sided `κ₂` bounds for the reciprocal-diagonal
    inverse candidate. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_source_dimension_branch_data
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n ≤ m)
    {alpha : ℝ} {A : Fin m → Fin n → ℝ}
    {sigma : Fin n → ℝ} {u : Fin n → Fin m → ℝ}
    {v : Fin n → Fin n → ℝ} {w : Fin (m - n) → Fin m → ℝ}
    (hu : ∀ i : Fin n, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : Fin n, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : Fin n, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : Fin n, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : Fin (m - n),
      k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : Fin n, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : Fin n,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0)
    (hsigma_pos : ∀ i : Fin n, 0 < sigma i)
    (halpha :
      alpha = lsScaledAugmentedBranchSigmaMin sigma / Real.sqrt 2) :
    Real.sqrt 2 *
          (lsScaledAugmentedBranchSigmaMax sigma /
            lsScaledAugmentedBranchSigmaMin sigma) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha sigma u v w) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha sigma u v w) ≤
        2 *
          (lsScaledAugmentedBranchSigmaMax sigma /
            lsScaledAugmentedBranchSigmaMin sigma) := by
  simpa [lsScaledAugmentedSourceBranchInverseCandidate,
    lsScaledAugmentedSourceBranchEquiv] using
    lsScaledAugmentedMatrix_kappa2_bounds_of_branch_cardinality_and_finite_extrema
      (m := m) (n := n) (ι := Fin n) (κ := Fin (m - n))
      (alpha := alpha) (A := A) (sigma := sigma) (u := u) (v := v) (w := w)
      (lsScaledAugmentedSourceBranchCardEq hmn)
      hu hv hw hleft hright hnull hAv hATu hATw hsigma_pos halpha
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    source-dimension branch handoff specialized to the real column-side
    singular values of `A`.  Full column rank supplies positivity of every
    singular branch, so the theorem surface only leaves the real
    singular-vector and left-nullspace branch equations as supplied data. -/
theorem
    lsScaledAugmentedMatrix_kappa2_bounds_of_source_singular_branch_data
    {m n : ℕ} [Nonempty (Fin n)] (hmn : n ≤ m)
    {alpha : ℝ} {A : Fin m → Fin n → ℝ}
    (hrank : lsRealRectColRank A = n)
    {u : Fin n → Fin m → ℝ}
    {v : Fin n → Fin n → ℝ} {w : Fin (m - n) → Fin m → ℝ}
    (hu : ∀ i : Fin n, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : Fin n, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : Fin (m - n), vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : Fin n, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : Fin n, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : Fin (m - n),
      k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : Fin n, rectMatMulVec A (v i) =
      fun r => lsRealRectColSingularValue A i * u i r)
    (hATu : ∀ i : Fin n,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => lsRealRectColSingularValue A i * v i j)
    (hATw : ∀ k : Fin (m - n), ∀ j : Fin n,
      ∑ r : Fin m, A r j * w k r = 0)
    (halpha :
      alpha = lsScaledAugmentedBranchSigmaMin
        (lsRealRectColSingularValue A) / Real.sqrt 2) :
    Real.sqrt 2 *
          (lsScaledAugmentedBranchSigmaMax (lsRealRectColSingularValue A) /
            lsScaledAugmentedBranchSigmaMin (lsRealRectColSingularValue A)) ≤
        kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
            (lsRealRectColSingularValue A) u v w) ∧
      kappa2 (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedSourceBranchInverseCandidate hmn alpha
            (lsRealRectColSingularValue A) u v w) ≤
        2 *
          (lsScaledAugmentedBranchSigmaMax (lsRealRectColSingularValue A) /
            lsScaledAugmentedBranchSigmaMin (lsRealRectColSingularValue A)) := by
  simpa using
    lsScaledAugmentedMatrix_kappa2_bounds_of_source_dimension_branch_data
      (m := m) (n := n) (hmn := hmn)
      (alpha := alpha) (A := A)
      (sigma := lsRealRectColSingularValue A) (u := u) (v := v) (w := w)
      hu hv hw hleft hright hnull hAv hATu hATw
      (fun i => lsRealRectColSingularValue_pos_of_colRank_eq_card A hrank i)
      halpha
private theorem matMulVec_orthogonal_transpose_mul_lsq {m : ℕ}
    {Q : Fin m → Fin m → ℝ} (hQ : IsOrthogonal m Q)
    (f : Fin m → ℝ) :
    matMulVec m (matTranspose Q) (matMulVec m Q f) = f := by
  ext i
  calc
    matMulVec m (matTranspose Q) (matMulVec m Q f) i
        = matMulVec m (matMul m (matTranspose Q) Q) f i := by
            exact (matMulVec_matMul m (matTranspose Q) Q f i).symm
    _ = matMulVec m (idMatrix m) f i := by
            have hmat : matMul m (matTranspose Q) Q = idMatrix m := by
              ext a b
              exact hQ.left_inv a b
            rw [hmat]
    _ = f i := by
            exact congrFun (matMulVec_id m f) i
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 exact asymmetric QR handoff.
    Assume `A = Q [R;0]` exactly, `Q^T fpert = [d₁ + Deltaf1; d₂]`,
    and the two triangular solves satisfy perturbed equations with top-block
    perturbations `DeltaR1`, `DeltaR2` and right-hand-side perturbation
    `Deltag`.  Then the lifted computed pair satisfies the original-coordinate
    asymmetric augmented system with the two occurrences of `A` perturbed by
    `Q [DeltaR1;0]` and `Q [DeltaR2;0]`.

    This is the exact algebraic bridge needed before inserting the concrete
    Householder QR/RHS/triangular-solve bounds from Theorem 20.4. -/
theorem LSAsymmetricAugmentedSystem.exact_qr_solution_of_perturbed_triangular_solves
    {n k : ℕ}
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R DeltaR1 DeltaR2 : Fin n → Fin n → ℝ)
    (fpert : Fin (n + k) → ℝ)
    (d1 h x Deltaf1 : Fin n → ℝ) (d2 : Fin k → ℝ)
    (g Deltag : Fin n → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R))
    (hd : matMulVec (n + k) (matTranspose Q) fpert =
      Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2)
    (hRt : ∀ j : Fin n,
      ∑ i : Fin n, (R i j + DeltaR2 i j) * h i = g j + Deltag j)
    (hRx : rectMatMulVec (fun i j => R i j + DeltaR1 i j) x =
      fun i : Fin n => d1 i + Deltaf1 i - h i) :
    LSAsymmetricAugmentedSystem
      (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
      (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
      fpert (fun j : Fin n => g j + Deltag j)
      (matMulVec (n + k) Q (Fin.append h d2)) x := by
  let B1 : Fin (n + k) → Fin n → ℝ :=
    fun i j => lsQRTallBlock R i j + lsQRTallBlock DeltaR1 i j
  let B2 : Fin (n + k) → Fin n → ℝ :=
    fun i j => lsQRTallBlock R i j + lsQRTallBlock DeltaR2 i j
  have hA1 :
      (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j) =
        matMulRectLeft Q B1 := by
    ext i j
    calc
      A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j
          = matMulRectLeft Q (lsQRTallBlock R) i j +
              matMulRectLeft Q (lsQRTallBlock DeltaR1) i j := by
              rw [hA]
      _ = matMulRectLeft Q
            (fun a b => lsQRTallBlock R a b + lsQRTallBlock DeltaR1 a b)
            i j := by
              exact (congrFun (congrFun
                (matMulRectLeft_add_right Q (lsQRTallBlock R)
                  (lsQRTallBlock DeltaR1)) i) j).symm
      _ = matMulRectLeft Q B1 i j := rfl
  have hA2 :
      (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j) =
        matMulRectLeft Q B2 := by
    ext i j
    calc
      A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j
          = matMulRectLeft Q (lsQRTallBlock R) i j +
              matMulRectLeft Q (lsQRTallBlock DeltaR2) i j := by
              rw [hA]
      _ = matMulRectLeft Q
            (fun a b => lsQRTallBlock R a b + lsQRTallBlock DeltaR2 a b)
            i j := by
              exact (congrFun (congrFun
                (matMulRectLeft_add_right Q (lsQRTallBlock R)
                  (lsQRTallBlock DeltaR2)) i) j).symm
      _ = matMulRectLeft Q B2 i j := rfl
  have htrans_base :
      LSAsymmetricAugmentedSystem B1 B2
        (Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2)
        (fun j : Fin n => g j + Deltag j) (Fin.append h d2) x := by
    exact
      LSAsymmetricAugmentedSystem.transformed_qr_solution_of_top_perturbations
        R DeltaR1 DeltaR2 d1 h x Deltaf1 d2 g Deltag hRt hRx
  have htrans :
      LSAsymmetricAugmentedSystem B1 B2
        (matMulVec (n + k) (matTranspose Q) fpert)
        (fun j : Fin n => g j + Deltag j) (Fin.append h d2) x := by
    simpa [hd] using htrans_base
  exact
    LSAsymmetricAugmentedSystem.of_transformed_orthogonal
      Q B1 B2
      (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
      (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
      fpert (fun j : Fin n => g j + Deltag j) (Fin.append h d2) x
      hQ hA1 hA2 htrans
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 triangular-solve handoff.
    If `R` is nonsingular upper triangular, then the concrete forward
    substitution solve of `R^T h = g` and back substitution solve of
    `R x = d₁ + Deltaf1 - h` produce top-block perturbations bounded by
    `gamma fp n`.  These perturbations feed the exact asymmetric QR handoff
    for the augmented system (20.15).

    This instantiates the triangular-solve part of the computed path only:
    the Householder QR factorization and transformed-RHS error bounds remain
    separate open obligations for the full Theorem 20.4. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (fpert : Fin (n + k) → ℝ)
    (d1 Deltaf1 : Fin n → ℝ) (d2 : Fin k → ℝ) (g : Fin n → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R))
    (hd : matMulVec (n + k) (matTranspose Q) fpert =
      Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2)
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n) :
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R
      (fun i : Fin n => d1 i + Deltaf1 i - h i)
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        fpert g (matMulVec (n + k) Q (Fin.append h d2)) x := by
  let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
  let rhs : Fin n → ℝ := fun i : Fin n => d1 i + Deltaf1 i - h i
  let x : Fin n → ℝ := fl_backSub fp n R rhs
  have hdiagT : ∀ i : Fin n, matTranspose R i i ≠ 0 := by
    intro i
    simpa [matTranspose] using hdiag i
  have hlowerT :
      ∀ i j : Fin n, i.val < j.val → matTranspose R i j = 0 := by
    intro i j hij
    simpa [matTranspose] using hupper j i hij
  rcases forwardSub_backward_error fp n (matTranspose R) g hdiagT hlowerT hγ with
    ⟨DeltaL, hDeltaL_bound, hForwardEq⟩
  rcases backSub_backward_error fp n R rhs hdiag hupper hγ with
    ⟨DeltaR1, hDeltaR1_bound, hBackEq⟩
  let DeltaR2 : Fin n → Fin n → ℝ := fun i j => DeltaL j i
  refine ⟨DeltaR1, DeltaR2, hDeltaR1_bound, ?_, ?_⟩
  · intro i j
    simpa [DeltaR2, matTranspose] using hDeltaL_bound j i
  · have hRt : ∀ j : Fin n,
        ∑ i : Fin n, (R i j + DeltaR2 i j) * h i =
          g j + (fun _ : Fin n => 0) j := by
      intro j
      calc
        ∑ i : Fin n, (R i j + DeltaR2 i j) * h i
            = ∑ i : Fin n,
                (matTranspose R j i + DeltaL j i) *
                  fl_forwardSub fp n (matTranspose R) g i := by
                apply Finset.sum_congr rfl
                intro i _
                simp [h, DeltaR2, matTranspose]
        _ = g j := hForwardEq j
        _ = g j + (fun _ : Fin n => 0) j := by simp
    have hRx :
        rectMatMulVec (fun i j => R i j + DeltaR1 i j) x =
          fun i : Fin n => d1 i + Deltaf1 i - h i := by
      ext i
      simpa [rectMatMulVec, x, rhs] using hBackEq i
    have hsys :=
      LSAsymmetricAugmentedSystem.exact_qr_solution_of_perturbed_triangular_solves
        Q A R DeltaR1 DeltaR2 fpert d1 h x Deltaf1 d2 g
        (fun _ : Fin n => 0) hQ hA hd hRt hRx
    simpa using hsys
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 RHS-perturbation lift for the
    triangular-solve handoff.  If the unperturbed transformed right-hand side
    satisfies `Q^T f = [d₁; d₂]`, then a top-block transformed perturbation
    `Deltaf1` is realized in the original coordinates by
    `Deltaf = Q [Deltaf1; 0]`.

    This removes the abstract perturbed-RHS hypothesis from
    `exists_exact_qr_solution_of_fl_forwardSub_fl_backSub`; the remaining open
    implementation obligations are the rounded Householder QR factorization and
    the rounded application of `Q^T` to the right-hand side. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_transformed_rhs
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (f : Fin (n + k) → ℝ)
    (d1 Deltaf1 : Fin n → ℝ) (d2 : Fin k → ℝ) (g : Fin n → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R))
    (hd : matMulVec (n + k) (matTranspose Q) f = Fin.append d1 d2)
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n) :
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R
      (fun i : Fin n => d1 i + Deltaf1 i - h i)
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      Deltaf =
        matMulVec (n + k) Q (Fin.append Deltaf1 (fun _ : Fin k => 0)) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h d2)) x := by
  let topDelta : Fin (n + k) → ℝ := Fin.append Deltaf1 (fun _ : Fin k => 0)
  let Deltaf : Fin (n + k) → ℝ := matMulVec (n + k) Q topDelta
  have hQDelta :
      matMulVec (n + k) (matTranspose Q) Deltaf = topDelta := by
    simpa [Deltaf] using matMulVec_orthogonal_transpose_mul_lsq hQ topDelta
  have hdPert :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2 := by
    ext row
    calc
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) row
          = matMulVec (n + k) (matTranspose Q) f row +
              matMulVec (n + k) (matTranspose Q) Deltaf row := by
              exact congrFun
                (matMulVec_add_right (n + k) (matTranspose Q) f Deltaf) row
      _ = Fin.append d1 d2 row + topDelta row := by
              rw [hd, hQDelta]
      _ = Fin.append (fun i : Fin n => d1 i + Deltaf1 i) d2 row := by
              cases row using Fin.addCases with
              | left row =>
                  simp [topDelta, Fin.append_left]
              | right row =>
                  simp [topDelta, Fin.append_right]
  rcases
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
        fp Q A R (fun i => f i + Deltaf i) d1 Deltaf1 d2 g
        hQ hA hdPert hdiag hupper hγ with
    ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsys⟩
  refine ⟨Deltaf, DeltaR1, DeltaR2, ?_, hDeltaR1, hDeltaR2, ?_⟩
  · simp [Deltaf, topDelta]
  · simpa [Deltaf] using hsys
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 RHS-transform handoff.
    A fixed-`Q` Householder RHS backward-error certificate for the computed
    transformed vector `c_hat` supplies the original-coordinate perturbation
    `Deltaf` needed by the concrete triangular-solve theorem.

    This is an adapter from the QR module's RHS-transform theorem to the
    augmented-system solve (20.15).  It still assumes an exact QR relation
    `A = Q [R;0]`; the matrix QR perturbation bound remains a separate
    obligation for the full Theorem 20.4. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_rhs_explicit_backward_error
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (f c_hat : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (c_bound : ℝ)
    (hRhs : HouseholderQRRhsPanelExplicitBackwardError (n + k) n
      A f Q c_hat c_bound)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R))
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n) :
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i : Fin n => cTop i - h i)
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      (∀ i, |Deltaf i| ≤ c_bound) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h cBot)) x := by
  let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  obtain ⟨Deltaf, hrep, hDeltaf⟩ := hRhs.result
  have hd :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append cTop cBot := by
    ext row
    calc
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) row
          = c_hat row := (hrep row).symm
      _ = Fin.append cTop cBot row := by
          cases row using Fin.addCases with
          | left row =>
              simp [cTop]
          | right row =>
              simp [cBot]
  have hd0 :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append (fun i : Fin n => cTop i + (fun _ : Fin n => 0) i)
          cBot := by
    simpa using hd
  rcases
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
        fp Q A R (fun i => f i + Deltaf i) cTop (fun _ : Fin n => 0)
        cBot g hRhs.orth hA hd0 hdiag hupper hγ with
    ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsys⟩
  refine ⟨Deltaf, DeltaR1, DeltaR2, hDeltaf, hDeltaR1, hDeltaR2, ?_⟩
  simpa [cTop] using hsys
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 concrete RHS-transform
    handoff.  The actual `fl_householderQRPanel_rhs` recursion supplies the
    bounded original-coordinate perturbation for the right-hand side, and the
    concrete forward/back substitution theorems supply the triangular-solve
    perturbations.

    The theorem is implementation-backed for the transformed right-hand side
    and triangular solves.  It still assumes the exact relation between the
    source matrix, the fixed Householder `Q`, and `[R;0]`; the matrix QR
    perturbation bound is the remaining QR-side obligation. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_fl_householderQRPanel_rhs
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp (n + k) n A)
    (hA : A =
      matMulRectLeft (fl_householderQRPanel_Q fp (n + k) n A)
        (lsQRTallBlock R))
    (hdiag : ∀ i : Fin n, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hγ : gammaValid fp n) :
    let Q : Fin (n + k) → Fin (n + k) → ℝ :=
      fl_householderQRPanel_Q fp (n + k) n A
    let c_hat : Fin (n + k) → ℝ :=
      fl_householderQRPanel_rhs fp (n + k) n A f
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i : Fin n => cTop i - h i)
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      (∀ i,
        |Deltaf i| ≤ householderQRRhsPanelBackwardBound fp (n + k) n A f) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h cBot)) x := by
  let Q : Fin (n + k) → Fin (n + k) → ℝ :=
    fl_householderQRPanel_Q fp (n + k) n A
  let c_hat : Fin (n + k) → ℝ :=
    fl_householderQRPanel_rhs fp (n + k) n A f
  have hRhs :
      HouseholderQRRhsPanelExplicitBackwardError (n + k) n A f Q c_hat
        (householderQRRhsPanelBackwardBound fp (n + k) n A f) := by
    simpa [Q, c_hat] using
      fl_householderQRPanel_rhs_explicit_backward_error fp (n + k) n A f
        hready
  have hbase :=
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_rhs_explicit_backward_error
        fp Q A R f c_hat g
        (householderQRRhsPanelBackwardBound fp (n + k) n A f)
        hRhs (by simpa [Q] using hA) hdiag hupper hγ
  simpa [Q, c_hat] using hbase
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 QR/RHS/triangular handoff.
    A fixed-`Q` simultaneous Householder QR/RHS backward-error certificate for
    the tall panel supplies the matrix perturbation `DeltaA` and the
    original-coordinate RHS perturbation `Deltaf`; the concrete forward/back
    substitution theorems then supply the two triangular perturbations.

    This closes the implementation-backed handoff through the computed QR
    panel, computed transformed RHS, and computed triangular solves.  It is
    still not the final printed Theorem 20.4: the source-shaped componentwise
    `G|A|`, `H_i` bounds and final constant packaging remain separate. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_solve_components_fixed_backward_error
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A Rhat : Fin (n + k) → Fin n → ℝ)
    (f c_hat : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (cA cF : ℝ)
    (hComp : HouseholderQRPanelSolveFixedBackwardError (n + k) n
      A Rhat f c_hat Q cA cF)
    (hRupper : IsUpperTrapezoidal (n + k) n Rhat)
    (hdiag : ∀ i : Fin n, Rhat (Fin.castAdd k i) i ≠ 0)
    (hγ : gammaValid fp n) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => Rhat (Fin.castAdd k i) j
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i : Fin n => cTop i - h i)
    ∃ DeltaA : Fin (n + k) → Fin n → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      frobNorm DeltaA ≤ cA ∧
      (∀ i, |Deltaf i| ≤ cF) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h cBot)) x := by
  let R : Fin n → Fin n → ℝ :=
    fun i j => Rhat (Fin.castAdd k i) j
  let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  obtain ⟨DeltaA, Deltaf, hRrep, hfRep, hDeltaA, hDeltaf⟩ :=
    hComp.result
  have hRhatBlock : Rhat = lsQRTallBlock (k := k) R := by
    simpa [R] using
      lsQRTallBlock_of_upper_trapezoidal (n := n) (k := k) Rhat hRupper
  have hupperR : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal (n := n) (k := k)
        Rhat hRupper
  have hdiagR : ∀ i : Fin n, R i i ≠ 0 := by
    intro i
    simpa [R] using hdiag i
  have hRmat :
      Rhat =
        matMulRectLeft (matTranspose Q)
          (fun r col => A r col + DeltaA r col) := by
    ext i j
    simpa [matMulRectLeft, matMulRect] using hRrep i j
  have hApert :
      (fun i j => A i j + DeltaA i j) =
        matMulRectLeft Q (lsQRTallBlock R) := by
    have hQR :
        matMulRectLeft Q Rhat =
          (fun i j => A i j + DeltaA i j) := by
      rw [hRmat, ← matMulRectLeft_assoc]
      have hQQT :
          matMul (n + k) Q (matTranspose Q) = idMatrix (n + k) := by
        ext i j
        exact hComp.orth.right_inv i j
      rw [hQQT, matMulRectLeft_id]
    rw [← hQR, hRhatBlock]
  have hd :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append cTop cBot := by
    ext row
    calc
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) row
          = c_hat row := (hfRep row).symm
      _ = Fin.append cTop cBot row := by
          cases row using Fin.addCases with
          | left row =>
              simp [cTop]
          | right row =>
              simp [cBot]
  have hd0 :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append (fun i : Fin n => cTop i + (fun _ : Fin n => 0) i)
          cBot := by
    simpa using hd
  rcases
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
        fp Q (fun i j => A i j + DeltaA i j) R
        (fun i => f i + Deltaf i) cTop (fun _ : Fin n => 0) cBot g
        hComp.orth hApert hd0 hdiagR hupperR hγ with
    ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsys⟩
  refine ⟨DeltaA, Deltaf, DeltaR1, DeltaR2, hDeltaA, hDeltaf,
    hDeltaR1, hDeltaR2, ?_⟩
  simpa [R, cTop] using hsys
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 concrete QR/RHS/triangular
    handoff.  The actual zero-aware `fl_householderQRPanel_R` and
    `fl_householderQRPanel_rhs` recursions supply the shared fixed-`Q` matrix
    and RHS perturbations; the concrete triangular solves complete the
    asymmetric augmented-system result.

    The matrix perturbation is recorded with the QR panel Frobenius bound
    `householderQRPanelBackwardCoeff fp (n+k) n A * frobNorm A`.  The final
    source componentwise `G|A|`, `H_i` packaging of Theorem 20.4 remains open. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_solve_components
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (hready : HouseholderQRPanelReady fp (n + k) n A)
    (hdiag : ∀ i : Fin n,
      fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) i ≠ 0)
    (hγ : gammaValid fp n) :
    let Q : Fin (n + k) → Fin (n + k) → ℝ :=
      fl_householderQRPanel_Q fp (n + k) n A
    let Rhat : Fin (n + k) → Fin n → ℝ :=
      fl_householderQRPanel_R fp (n + k) n A
    let R : Fin n → Fin n → ℝ :=
      fun i j => Rhat (Fin.castAdd k i) j
    let c_hat : Fin (n + k) → ℝ :=
      fl_householderQRPanel_rhs fp (n + k) n A f
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i : Fin n => cTop i - h i)
    ∃ DeltaA : Fin (n + k) → Fin n → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      frobNorm DeltaA ≤
        householderQRPanelBackwardCoeff fp (n + k) n A * frobNorm A ∧
      (∀ i,
        |Deltaf i| ≤ householderQRRhsPanelBackwardBound fp (n + k) n A f) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h cBot)) x := by
  let Q : Fin (n + k) → Fin (n + k) → ℝ :=
    fl_householderQRPanel_Q fp (n + k) n A
  let Rhat : Fin (n + k) → Fin n → ℝ :=
    fl_householderQRPanel_R fp (n + k) n A
  let c_hat : Fin (n + k) → ℝ :=
    fl_householderQRPanel_rhs fp (n + k) n A f
  have hComp :
      HouseholderQRPanelSolveFixedBackwardError (n + k) n A Rhat f c_hat Q
        (householderQRPanelBackwardCoeff fp (n + k) n A * frobNorm A)
        (householderQRRhsPanelBackwardBound fp (n + k) n A f) := by
    simpa [Q, Rhat, c_hat] using
      fl_householderQRPanel_solve_components_fixed_Q_backward_error
        fp (n + k) n A f hready
  have hupper : IsUpperTrapezoidal (n + k) n Rhat := by
    simpa [Rhat] using
      fl_householderQRPanel_R_upper_trapezoidal fp (n + k) n A
  have hbase :=
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_solve_components_fixed_backward_error
      fp Q A Rhat f c_hat g
      (householderQRPanelBackwardCoeff fp (n + k) n A * frobNorm A)
      (householderQRRhsPanelBackwardBound fp (n + k) n A f)
      hComp hupper (by simpa [Rhat] using hdiag) hγ
  simpa [Q, Rhat, c_hat] using hbase
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 matrix-side source-shape QR
    handoff.  A fixed-`Q` QR certificate in Higham's componentwise `G |A|`
    form, together with a fixed-`Q` RHS transform certificate, supplies the
    matrix perturbation `DeltaA`, source witness `G`, original-coordinate
    RHS perturbation `Deltaf`, and the two triangular-solve perturbations.

    This is still an intermediate Theorem 20.4 statement: the matrix
    perturbation has the printed `G |A|` shape, but the RHS perturbation is
    represented by the existing scalar RHS bound rather than Higham's final
    `H_1 |f| + H_2 |\hat r|` packaging. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_higham_qr_and_rhs_explicit_backward_error
    {n k : ℕ} (fp : FPModel)
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A Rhat : Fin (n + k) → Fin n → ℝ)
    (f c_hat : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (cA cComp cF : ℝ)
    (hQR : StructuredHouseholderQRPanelHighamBackwardError (n + k) n
      A Q Rhat cA cComp)
    (hRhs : HouseholderQRRhsPanelExplicitBackwardError (n + k) n
      A f Q c_hat cF)
    (hdiag : ∀ i : Fin n, Rhat (Fin.castAdd k i) i ≠ 0)
    (hγ : gammaValid fp n) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => Rhat (Fin.castAdd k i) j
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i : Fin n => cTop i - h i)
    ∃ DeltaA : Fin (n + k) → Fin n → ℝ,
    ∃ G : Fin (n + k) → Fin (n + k) → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      frobNorm DeltaA ≤ cA ∧
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      (∀ i j, |DeltaA i j| ≤
        cComp * matMulRect (n + k) (n + k) n G
          (fun a b => |A a b|) i j) ∧
      (∀ i, |Deltaf i| ≤ cF) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h cBot)) x := by
  let R : Fin n → Fin n → ℝ :=
    fun i j => Rhat (Fin.castAdd k i) j
  let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
  let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
  obtain ⟨DeltaA, G, hRrep, hDeltaA, hGnonneg, hGnorm, hDeltaAcomp⟩ :=
    hQR.result
  obtain ⟨Deltaf, hfRep, hDeltaf⟩ := hRhs.result
  have hRhatBlock : Rhat = lsQRTallBlock (k := k) R := by
    simpa [R] using
      lsQRTallBlock_of_upper_trapezoidal (n := n) (k := k) Rhat hQR.upper
  have hupperR : ∀ i j : Fin n, j.val < i.val → R i j = 0 := by
    simpa [R] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal (n := n) (k := k)
        Rhat hQR.upper
  have hdiagR : ∀ i : Fin n, R i i ≠ 0 := by
    intro i
    simpa [R] using hdiag i
  have hRmat :
      Rhat =
        matMulRectLeft (matTranspose Q)
          (fun r col => A r col + DeltaA r col) := by
    ext i j
    simpa [matMulRectLeft, matMulRect] using hRrep i j
  have hApert :
      (fun i j => A i j + DeltaA i j) =
        matMulRectLeft Q (lsQRTallBlock R) := by
    have hQRmat :
        matMulRectLeft Q Rhat =
          (fun i j => A i j + DeltaA i j) := by
      rw [hRmat, ← matMulRectLeft_assoc]
      have hQQT :
          matMul (n + k) Q (matTranspose Q) = idMatrix (n + k) := by
        ext i j
        exact hQR.orth.right_inv i j
      rw [hQQT, matMulRectLeft_id]
    rw [← hQRmat, hRhatBlock]
  have hd :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append cTop cBot := by
    ext row
    calc
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) row
          = c_hat row := (hfRep row).symm
      _ = Fin.append cTop cBot row := by
          cases row using Fin.addCases with
          | left row =>
              simp [cTop]
          | right row =>
              simp [cBot]
  have hd0 :
      matMulVec (n + k) (matTranspose Q) (fun i => f i + Deltaf i) =
        Fin.append (fun i : Fin n => cTop i + (fun _ : Fin n => 0) i)
          cBot := by
    simpa using hd
  rcases
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub
        fp Q (fun i j => A i j + DeltaA i j) R
        (fun i => f i + Deltaf i) cTop (fun _ : Fin n => 0) cBot g
        hQR.orth hApert hd0 hdiagR hupperR hγ with
    ⟨DeltaR1, DeltaR2, hDeltaR1, hDeltaR2, hsys⟩
  refine ⟨DeltaA, G, Deltaf, DeltaR1, DeltaR2, hDeltaA,
    hGnonneg, hGnorm, hDeltaAcomp, hDeltaf, hDeltaR1, hDeltaR2, ?_⟩
  simpa [R, cTop] using hsys
/-- Higham, 2nd ed., Chapter 20, Theorem 20.4 concrete Householder QR
    handoff with source-shaped matrix perturbation.  The concrete rounded
    `fl_householderQRPanel_R` panel supplies `DeltaA` and `G` in the
    componentwise Higham form, the concrete rounded
    `fl_householderQRPanel_rhs` supplies an original-coordinate `Deltaf`, and
    the concrete triangular solves supply `DeltaR1` and `DeltaR2`.

    The remaining gap to the printed Theorem 20.4 is the RHS/residual
    `H_1 |f| + H_2 |\hat r|` and `Deltag` source packaging. -/
theorem LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_householderQRPanel_higham_matrix_solve_components
    {n k : ℕ} (fp : FPModel)
    (A : Fin (n + k) → Fin n → ℝ)
    (f : Fin (n + k) → ℝ) (g : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid :
      gammaValid fp (n * householderConstructApplyGammaIndex (n + k)))
    (hdiag : ∀ i : Fin n,
      fl_householderQRPanel_R fp (n + k) n A (Fin.castAdd k i) i ≠ 0)
    (hγ : gammaValid fp n) :
    let Q : Fin (n + k) → Fin (n + k) → ℝ :=
      fl_householderQRPanel_Q fp (n + k) n A
    let Rhat : Fin (n + k) → Fin n → ℝ :=
      fl_householderQRPanel_R fp (n + k) n A
    let R : Fin n → Fin n → ℝ :=
      fun i j => Rhat (Fin.castAdd k i) j
    let c_hat : Fin (n + k) → ℝ :=
      fl_householderQRPanel_rhs fp (n + k) n A f
    let cTop : Fin n → ℝ := fun i => c_hat (Fin.castAdd k i)
    let cBot : Fin k → ℝ := fun i => c_hat (Fin.natAdd n i)
    let h : Fin n → ℝ := fl_forwardSub fp n (matTranspose R) g
    let x : Fin n → ℝ := fl_backSub fp n R (fun i : Fin n => cTop i - h i)
    ∃ DeltaA : Fin (n + k) → Fin n → ℝ,
    ∃ G : Fin (n + k) → Fin (n + k) → ℝ,
    ∃ Deltaf : Fin (n + k) → ℝ,
    ∃ DeltaR1 DeltaR2 : Fin n → Fin n → ℝ,
      frobNorm DeltaA ≤
        gamma fp (n * householderConstructApplyGammaIndex (n + k)) *
          frobNorm A ∧
      (∀ i j, 0 ≤ G i j) ∧
      frobNorm G = 1 ∧
      (∀ i j, |DeltaA i j| ≤
        ((n + k : ℝ) *
          gamma fp (n * householderConstructApplyGammaIndex (n + k))) *
          matMulRect (n + k) (n + k) n G
            (fun a b => |A a b|) i j) ∧
      (∀ i,
        |Deltaf i| ≤ householderQRRhsPanelBackwardBound fp (n + k) n A f) ∧
      (∀ i j, |DeltaR1 i j| ≤ gamma fp n * |R i j|) ∧
      (∀ i j, |DeltaR2 i j| ≤ gamma fp n * |R i j|) ∧
      LSAsymmetricAugmentedSystem
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR1) i j)
        (fun i j => A i j + DeltaA i j +
          matMulRectLeft Q (lsQRTallBlock DeltaR2) i j)
        (fun i => f i + Deltaf i) g
        (matMulVec (n + k) Q (Fin.append h cBot)) x := by
  let Q : Fin (n + k) → Fin (n + k) → ℝ :=
    fl_householderQRPanel_Q fp (n + k) n A
  let Rhat : Fin (n + k) → Fin n → ℝ :=
    fl_householderQRPanel_R fp (n + k) n A
  let c_hat : Fin (n + k) → ℝ :=
    fl_householderQRPanel_rhs fp (n + k) n A f
  let K : ℕ := householderConstructApplyGammaIndex (n + k)
  have hn_le_rows : n ≤ n + k := Nat.le_add_right n k
  have hsteps : 0 < Nat.min (n + k) n := by
    simpa [Nat.min_eq_right hn_le_rows] using hn
  have hQR :
      StructuredHouseholderQRPanelHighamBackwardError (n + k) n A Q Rhat
        (gamma fp (n * K) * frobNorm A)
        ((n + k : ℝ) * gamma fp (n * K)) := by
    have hraw :=
      fl_householderQRPanel_R_higham_backward_error_gammaHigham_of_global_gammaValid
        fp (n + k) n A hsteps
        (by simpa [K, Nat.min_eq_right hn_le_rows] using hvalid)
    simpa [Q, Rhat, K, Nat.min_eq_right hn_le_rows] using hraw
  have hK_le_nK : K ≤ n * K := by
    have hn1 : 1 ≤ n := Nat.succ_le_of_lt hn
    simpa using Nat.mul_le_mul_right K hn1
  have hbase_le_K : 11 * (n + k) + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hbase_valid : gammaValid fp (11 * (n + k) + 23) :=
    gammaValid_mono fp (le_trans hbase_le_K hK_le_nK) (by
      simpa [K] using hvalid)
  have hready : HouseholderQRPanelReady fp (n + k) n A :=
    HouseholderQRPanelReady_of_global_gammaValid fp (n + k) n (n + k) A
      (le_refl (n + k)) hbase_valid
  have hRhs :
      HouseholderQRRhsPanelExplicitBackwardError (n + k) n A f Q c_hat
        (householderQRRhsPanelBackwardBound fp (n + k) n A f) := by
    simpa [Q, c_hat] using
      fl_householderQRPanel_rhs_explicit_backward_error fp (n + k) n A f
        hready
  have hbase :=
    LSAsymmetricAugmentedSystem.exists_exact_qr_solution_of_fl_forwardSub_fl_backSub_of_higham_qr_and_rhs_explicit_backward_error
      fp Q A Rhat f c_hat g
      (gamma fp (n * K) * frobNorm A)
      ((n + k : ℝ) * gamma fp (n * K))
      (householderQRRhsPanelBackwardBound fp (n + k) n A f)
      hQR hRhs (by simpa [Rhat] using hdiag) hγ
  simpa [Q, Rhat, c_hat, K] using hbase

end NumStability
