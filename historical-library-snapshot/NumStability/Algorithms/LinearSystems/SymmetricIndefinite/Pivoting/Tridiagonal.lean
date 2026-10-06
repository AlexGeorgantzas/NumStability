import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# NumStability Algorithms LinearSystems SymmetricIndefinite Pivoting Tridiagonal

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Bunch's symmetric-tridiagonal pivoting parameter from Algorithm 11.6,
`alpha = (sqrt 5 - 1)/2`. -/
noncomputable def bunchTridiagonalAlpha : ℝ := (Real.sqrt 5 - 1) / 2

/-- The tridiagonal pivoting parameter satisfies `alpha^2 + alpha - 1 = 0`. -/
theorem bunch_tridiagonal_alpha_root :
    bunchTridiagonalAlpha ^ 2 + bunchTridiagonalAlpha - 1 = 0 := by
  unfold bunchTridiagonalAlpha
  have h5 : Real.sqrt 5 * Real.sqrt 5 = 5 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  field_simp
  nlinarith [h5]

/-- Bunch's symmetric-tridiagonal pivoting parameter is strictly positive. -/
theorem bunch_tridiagonal_alpha_pos : 0 < bunchTridiagonalAlpha := by
  unfold bunchTridiagonalAlpha
  have h : (1 : ℝ) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  linarith

/-- Bunch's symmetric-tridiagonal pivoting parameter is less than one. -/
theorem bunch_tridiagonal_alpha_lt_one : bunchTridiagonalAlpha < 1 := by
  unfold bunchTridiagonalAlpha
  have h : Real.sqrt 5 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  linarith

/-- From the root identity, `α² = 1 - α` for Bunch's tridiagonal parameter. -/
theorem bunch_tridiagonal_alpha_sq :
    bunchTridiagonalAlpha ^ 2 = 1 - bunchTridiagonalAlpha := by
  nlinarith [bunch_tridiagonal_alpha_root]

/-- Algorithm 11.6 source decision predicate for Bunch's tridiagonal pivot-size
strategy. -/
def BunchTridiagonalPivotChoice
    (σ a11 a21 : ℝ) (s : PivotSize) : Prop :=
  (σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2 ∧ s = PivotSize.one) ∨
  (σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2 ∧ s = PivotSize.two)

/-- The one-by-one branch of Algorithm 11.6 exposes the printed threshold
inequality. -/
theorem bunch_tridiagonal_pivot_choice_one_threshold (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one) :
    σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2 := by
  rcases hchoice with hchoice | hchoice
  · exact hchoice.1
  · cases hchoice.2

/-- The two-by-two branch of Algorithm 11.6 exposes the strict printed
threshold inequality. -/
theorem bunch_tridiagonal_pivot_choice_two_threshold (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two) :
    σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2 := by
  rcases hchoice with hchoice | hchoice
  · cases hchoice.2
  · exact hchoice.1

/-- The printed non-strict threshold certifies the one-by-one branch of
Algorithm 11.6. -/
theorem bunch_tridiagonal_pivot_choice_one_of_threshold (σ a11 a21 : ℝ)
    (hthreshold : σ * |a11| ≥ bunchTridiagonalAlpha * a21 ^ 2) :
    BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one :=
  Or.inl ⟨hthreshold, rfl⟩

/-- The printed strict threshold certifies the two-by-two branch of
Algorithm 11.6. -/
theorem bunch_tridiagonal_pivot_choice_two_of_threshold (σ a11 a21 : ℝ)
    (hthreshold : σ * |a11| < bunchTridiagonalAlpha * a21 ^ 2) :
    BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two :=
  Or.inr ⟨hthreshold, rfl⟩

/-- In the one-by-one branch, a nonzero adjacent offdiagonal entry forces the
accepted scalar pivot to be nonzero.  This is the local nonsingularity fact used
when the tridiagonal factorization step divides by `a11`. -/
theorem bunch_tridiagonal_pivot_choice_one_a11_ne_zero_of_a21_ne_zero
    (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.one)
    (ha21 : a21 ≠ 0) :
    a11 ≠ 0 := by
  have hthreshold :=
    bunch_tridiagonal_pivot_choice_one_threshold σ a11 a21 hchoice
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have hright_pos : 0 < bunchTridiagonalAlpha * a21 ^ 2 :=
    mul_pos bunch_tridiagonal_alpha_pos hsquare
  have hleft_pos : 0 < σ * |a11| := lt_of_lt_of_le hright_pos hthreshold
  intro ha11
  rw [ha11] at hleft_pos
  simp at hleft_pos

/-- In the two-by-two branch, if the left side of the printed comparison is
nonnegative, the accepted offdiagonal pivot is nonzero. -/
theorem bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg
    (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hleft_nonneg : 0 ≤ σ * |a11|) :
    a21 ≠ 0 := by
  have hthreshold :=
    bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have hright_pos : 0 < bunchTridiagonalAlpha * a21 ^ 2 :=
    lt_of_le_of_lt hleft_nonneg hthreshold
  intro ha21
  rw [ha21] at hright_pos
  simp at hright_pos

/-- A source-shaped variant of the two-by-two branch nonsingularity fact when
`σ` is known nonnegative. -/
theorem bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg
    (σ a11 a21 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσ : 0 ≤ σ) :
    a21 ≠ 0 :=
  bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_left_nonneg σ a11 a21
    hchoice (mul_nonneg hσ (abs_nonneg a11))

/-- In the two-by-two branch of Algorithm 11.6, if `σ` dominates the second
diagonal entry, the accepted tridiagonal pivot block has determinant bounded
away from zero by `(1 - α) a21²`. -/
theorem bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa22 : |a22| ≤ σ) :
    (1 - bunchTridiagonalAlpha) * a21 ^ 2 ≤ |a11 * a22 - a21 ^ 2| := by
  have hthreshold :=
    bunch_tridiagonal_pivot_choice_two_threshold σ a11 a21 hchoice
  have hprod_le : |a11 * a22| ≤ σ * |a11| := by
    have hmul := mul_le_mul_of_nonneg_left hσa22 (abs_nonneg a11)
    rw [abs_mul]
    nlinarith
  have hprod_lt : |a11 * a22| < bunchTridiagonalAlpha * a21 ^ 2 :=
    lt_of_le_of_lt hprod_le hthreshold
  have hdecomp : (a21 ^ 2 - a11 * a22) + a11 * a22 = a21 ^ 2 := by ring
  have hsum : |a21 ^ 2| ≤ |a21 ^ 2 - a11 * a22| + |a11 * a22| := by
    calc
      |a21 ^ 2| = |(a21 ^ 2 - a11 * a22) + a11 * a22| := by rw [hdecomp]
      _ ≤ |a21 ^ 2 - a11 * a22| + |a11 * a22| := abs_add_le _ _
  have hsq_abs : |a21 ^ 2| = a21 ^ 2 := abs_of_nonneg (sq_nonneg a21)
  have hlower_basic : a21 ^ 2 - |a11 * a22| ≤
      |a21 ^ 2 - a11 * a22| := by
    rw [hsq_abs] at hsum
    linarith
  have hcoeff_le_basic :
      (1 - bunchTridiagonalAlpha) * a21 ^ 2 ≤ a21 ^ 2 - |a11 * a22| := by
    nlinarith [hprod_lt]
  calc
    (1 - bunchTridiagonalAlpha) * a21 ^ 2 ≤
        a21 ^ 2 - |a11 * a22| := hcoeff_le_basic
    _ ≤ |a21 ^ 2 - a11 * a22| := hlower_basic
    _ = |a11 * a22 - a21 ^ 2| := by rw [abs_sub_comm]

/-- The two-by-two tridiagonal pivot block accepted by Algorithm 11.6 is
nonsingular when `σ` dominates the second diagonal entry. -/
theorem bunch_tridiagonal_twoByTwo_det_ne_zero_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa22 : |a22| ≤ σ) :
    a11 * a22 - a21 ^ 2 ≠ 0 := by
  have hσ : 0 ≤ σ := le_trans (abs_nonneg a22) hσa22
  have ha21 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
      hchoice hσ
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have halpha_gap : 0 < 1 - bunchTridiagonalAlpha := by
    linarith [bunch_tridiagonal_alpha_lt_one]
  have hlower :=
    bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ a11 a21 a22
      hchoice hσa22
  have hdet_abs_pos : 0 < |a11 * a22 - a21 ^ 2| :=
    lt_of_lt_of_le (mul_pos halpha_gap hsquare) hlower
  exact abs_pos.mp hdet_abs_pos

/-- Entrywise inverse bounds for the `2 × 2` tridiagonal pivot block
`[[a11, a21], [a21, a22]]` accepted by Algorithm 11.6.  The inverse entries are
`a22/det`, `-a21/det`, and `a11/det`, with
`det = a11*a22 - a21²`. -/
theorem bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound
    (σ a11 a21 a22 : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ) :
    |a22 / (a11 * a22 - a21 ^ 2)| ≤
        σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ∧
    |(-a21) / (a11 * a22 - a21 ^ 2)| ≤
        |a21| / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ∧
    |a11 / (a11 * a22 - a21 ^ 2)| ≤
        σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) := by
  let det := a11 * a22 - a21 ^ 2
  let lower := (1 - bunchTridiagonalAlpha) * a21 ^ 2
  have hσ : 0 ≤ σ := le_trans (abs_nonneg a11) hσa11
  have ha21 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
      hchoice hσ
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have halpha_gap : 0 < 1 - bunchTridiagonalAlpha := by
    linarith [bunch_tridiagonal_alpha_lt_one]
  have hlower_pos : 0 < lower := by
    dsimp [lower]
    exact mul_pos halpha_gap hsquare
  have hdet_lower : lower ≤ |det| := by
    dsimp [lower, det]
    exact bunch_tridiagonal_twoByTwo_absdet_lower_of_sigma_bound σ a11 a21 a22
      hchoice hσa22
  have hdet_abs_pos : 0 < |det| := lt_of_lt_of_le hlower_pos hdet_lower
  constructor
  · rw [abs_div]
    have hnum : |a22| / |det| ≤ σ / |det| :=
      div_le_div_of_nonneg_right hσa22 (le_of_lt hdet_abs_pos)
    have hden : σ / |det| ≤ σ / lower :=
      div_le_div_of_nonneg_left hσ hlower_pos hdet_lower
    exact hnum.trans hden
  · constructor
    · rw [abs_div, abs_neg]
      exact div_le_div_of_nonneg_left (abs_nonneg a21) hlower_pos hdet_lower
    · rw [abs_div]
      have hnum : |a11| / |det| ≤ σ / |det| :=
        div_le_div_of_nonneg_right hσa11 (le_of_lt hdet_abs_pos)
      have hden : σ / |det| ≤ σ / lower :=
        div_le_div_of_nonneg_left hσ hlower_pos hdet_lower
      exact hnum.trans hden

/-- Floating-point backward error of the scalar Schur update in a tridiagonal
`2 × 2` pivot step.  In a symmetric tridiagonal matrix, after accepting the
leading `2 × 2` block, the only trailing update has the form
`b - c*f*c`, where `f` is the bottom-right entry of the inverse pivot block.
The rounded computation `fl(b - fl(fl(c*f)*c))` differs from the exact update by
a residual bounded by `γ₃ (|b| + |c*f*c|)`. -/
theorem fl_tridiagonal_twoByTwo_schur_step_error
    (fp : FPModel) (b c f : ℝ) (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 * (|b| + |c * f * c|) ∧
      fp.fl_sub b (fp.fl_mul (fp.fl_mul c f) c) = (b - c * f * c) + Δ := by
  obtain ⟨δ1, hδ1, hm1⟩ := fp.model_mul c f
  obtain ⟨δ2, hδ2, hm2⟩ := fp.model_mul (fp.fl_mul c f) c
  obtain ⟨δ3, hδ3, hs⟩ := fp.model_sub b (fp.fl_mul (fp.fl_mul c f) c)
  obtain ⟨θ, hθ, hprod⟩ :=
    prod_error_bound fp 3 ![δ1, δ2, δ3]
      (by intro i; fin_cases i <;> simp_all) hval
  have hfactor : (1 + δ1) * (1 + δ2) * (1 + δ3) = 1 + θ := by
    have h := hprod
    rw [Fin.prod_univ_three] at h
    simpa using h
  have hs_eq : fp.fl_sub b (fp.fl_mul (fp.fl_mul c f) c)
      = b * (1 + δ3) - (c * f * c) * (1 + θ) := by
    rw [hs, hm2, hm1, ← hfactor]
    ring
  refine ⟨b * δ3 - (c * f * c) * θ, ?_, ?_⟩
  · have hu3 : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval
    have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
    have htri : |b * δ3 - (c * f * c) * θ| ≤
        |b * δ3| + |(c * f * c) * θ| := by
      have h := abs_add_le (b * δ3) (-((c * f * c) * θ))
      rwa [← sub_eq_add_neg, abs_neg] at h
    have e1 : |b * δ3 - (c * f * c) * θ|
        ≤ |b| * fp.u + |c * f * c| * gamma fp 3 := by
      calc |b * δ3 - (c * f * c) * θ|
          ≤ |b * δ3| + |(c * f * c) * θ| := htri
        _ = |b| * |δ3| + |c * f * c| * |θ| := by rw [abs_mul, abs_mul]
        _ ≤ |b| * fp.u + |c * f * c| * gamma fp 3 :=
            add_le_add (mul_le_mul_of_nonneg_left hδ3 (abs_nonneg _))
              (mul_le_mul_of_nonneg_left hθ (abs_nonneg _))
    have e2 : |b| * fp.u + |c * f * c| * gamma fp 3
        ≤ gamma fp 3 * (|b| + |c * f * c|) := by
      have hle : |b| * fp.u ≤ |b| * gamma fp 3 :=
        mul_le_mul_of_nonneg_left hu3 (abs_nonneg _)
      nlinarith [hle, abs_nonneg (c * f * c), hγ0]
    exact le_trans e1 e2
  · rw [hs_eq]
    ring

/-- Source-shaped version of `fl_tridiagonal_twoByTwo_schur_step_error` for the
accepted Algorithm 11.6 `2 × 2` pivot block.  The inverse-entry bound converts
the abstract correction `|c*f*c|` into the scalar budget using
`σ / ((1 - α) a21²)`. -/
theorem fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound
    (fp : FPModel) (σ a11 a21 a22 b c : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hval : gammaValid fp 3) :
    ∃ Δ : ℝ,
      |Δ| ≤ gamma fp 3 *
        (|b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + Δ := by
  obtain ⟨hInv22, hInv21, hInv11⟩ :=
    bunch_tridiagonal_twoByTwo_inverse_entry_bounds_of_sigma_bound σ a11 a21 a22
      hchoice hσa11 hσa22
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error fp b c
      (a11 / (a11 * a22 - a21 ^ 2)) hval
  refine ⟨Δ, ?_, hstep⟩
  have hcorr : |c * (a11 / (a11 * a22 - a21 ^ 2)) * c| ≤
      |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c| := by
    rw [abs_mul, abs_mul]
    have hleft :=
      mul_le_mul_of_nonneg_left hInv11 (abs_nonneg c)
    exact mul_le_mul_of_nonneg_right hleft (abs_nonneg c)
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  have hbudget :
      gamma fp 3 * (|b| + |c * (a11 / (a11 * a22 - a21 ^ 2)) * c|)
        ≤ gamma fp 3 *
          (|b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_refl |b|) hcorr) hγ0
  exact le_trans hΔ hbudget

/-- Backward-error form of the scalar rounded update for an accepted
tridiagonal `2 × 2` pivot: the computed trailing Schur entry is the exact Schur
update for a perturbed trailing scalar `b + Δb`. -/
theorem fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound
    (fp : FPModel) (σ a11 a21 a22 b c : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hval : gammaValid fp 3) :
    ∃ Δb : ℝ,
      |Δb| ≤ gamma fp 3 *
        (|b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c|) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b + Δb) - c * (a11 / (a11 * a22 - a21 ^ 2)) * c := by
  obtain ⟨Δ, hΔ, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_error_of_sigma_bound fp σ a11 a21 a22 b c
      hchoice hσa11 hσa22 hval
  refine ⟨Δ, hΔ, ?_⟩
  rw [hstep]
  ring

/-- Uniform scalar budget for the backward-error form of the accepted
tridiagonal `2 × 2` pivot update.  This is the local bridge from the Algorithm
11.6 inverse-entry scalar to a one-stage normwise envelope. -/
theorem fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hval : gammaValid fp 3) :
    ∃ Δb : ℝ,
      |Δb| ≤ gamma fp 3 * (Amax + Amax * κ * Amax) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b + Δb) - c * (a11 / (a11 * a22 - a21 ^ 2)) * c := by
  obtain ⟨Δb, hΔb, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_backward_error_of_sigma_bound fp
      σ a11 a21 a22 b c hchoice hσa11 hσa22 hval
  refine ⟨Δb, ?_, hstep⟩
  have hσ : 0 ≤ σ := le_trans (abs_nonneg a11) hσa11
  have ha21 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg σ a11 a21
      hchoice hσ
  have hsquare : 0 < a21 ^ 2 := sq_pos_of_ne_zero ha21
  have halpha_gap : 0 < 1 - bunchTridiagonalAlpha := by
    linarith [bunch_tridiagonal_alpha_lt_one]
  have hlower_pos : 0 < (1 - bunchTridiagonalAlpha) * a21 ^ 2 :=
    mul_pos halpha_gap hsquare
  have hratio_nonneg :
      0 ≤ σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) :=
    div_nonneg hσ (le_of_lt hlower_pos)
  have hcorr1 :
      |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) ≤ Amax * κ :=
    mul_le_mul hc hratio hratio_nonneg hAmax
  have hcorr :
      |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c| ≤
        Amax * κ * Amax :=
    mul_le_mul hcorr1 hc (abs_nonneg c) (mul_nonneg hAmax hκ)
  have hinside :
      |b| + |c| * (σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2)) * |c| ≤
        Amax + Amax * κ * Amax :=
    add_le_add hb hcorr
  have hγ0 : 0 ≤ gamma fp 3 := gamma_nonneg fp hval
  exact le_trans hΔb (mul_le_mul_of_nonneg_left hinside hγ0)

/-- One-stage `1 × 1` trailing-block envelope for an accepted tridiagonal
`2 × 2` pivot.  Since a symmetric tridiagonal matrix has only one trailing
entry touched by the first `2 × 2` pivot, the scalar backward-error bound lifts
to a `Fin 1 × Fin 1` perturbation directly. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hval : gammaValid fp 3) :
    ∃ ΔS : Fin 1 → Fin 1 → ℝ,
      (∀ i j : Fin 1, |ΔS i j| ≤ gamma fp 3 * (Amax + Amax * κ * Amax)) ∧
      (∀ i j : Fin 1,
        fp.fl_sub b
            (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
          = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + ΔS i j) := by
  obtain ⟨Δb, hΔb, hstep⟩ :=
    fl_tridiagonal_twoByTwo_schur_step_backward_error_uniform_bound fp
      σ a11 a21 a22 b c Amax κ hchoice hσa11 hσa22 hAmax hκ hb hc
      hratio hval
  refine ⟨fun _ _ => Δb, ?_, ?_⟩
  · intro _ _
    exact hΔb
  · intro _ _
    rw [hstep]
    ring

/-- Local index of the first trailing scalar after a leading `2 × 2`
tridiagonal pivot inside a block of size `n+3`. -/
def tridiagonalTwoByTwoFirstTrailingIndex (n : ℕ) : Fin (n + 3) :=
  ⟨2, by
    have h23 : 2 < 3 := by norm_num
    have h3 : 3 ≤ n + 3 := Nat.le_add_left 3 n
    exact lt_of_lt_of_le h23 h3⟩

@[simp] theorem tridiagonalTwoByTwoFirstTrailingIndex_val (n : ℕ) :
    (tridiagonalTwoByTwoFirstTrailingIndex n).val = 2 := rfl

/-- Offset embedding of the recursive trailing subproblem after a leading
`2 × 2` tridiagonal pivot.  Local trailing index `0` maps to ambient index `2`. -/
def tridiagonalTwoByTwoTrailingSubproblemIndex (n : ℕ)
    (i : Fin (n + 1)) : Fin (n + 3) :=
  ⟨i.val + 2, by
    have h := Nat.add_lt_add_right i.isLt 2
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h⟩

@[simp] theorem tridiagonalTwoByTwoTrailingSubproblemIndex_val
    (n : ℕ) (i : Fin (n + 1)) :
    (tridiagonalTwoByTwoTrailingSubproblemIndex n i).val = i.val + 2 := rfl

@[simp] theorem tridiagonalTwoByTwoTrailingSubproblemIndex_zero
    (n : ℕ) :
    tridiagonalTwoByTwoTrailingSubproblemIndex n 0 =
      tridiagonalTwoByTwoFirstTrailingIndex n := by
  apply Fin.ext
  simp [tridiagonalTwoByTwoTrailingSubproblemIndex,
    tridiagonalTwoByTwoFirstTrailingIndex]

/-- The recursive trailing-subproblem embedding after a leading tridiagonal
`2 × 2` pivot is injective. -/
theorem tridiagonalTwoByTwoTrailingSubproblemIndex_injective (n : ℕ) :
    Function.Injective (tridiagonalTwoByTwoTrailingSubproblemIndex n) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  simpa [tridiagonalTwoByTwoTrailingSubproblemIndex] using
    Nat.add_right_cancel hval

/-- An ambient perturbation is supported in the trailing block left after a
leading `2 × 2` tridiagonal pivot if it vanishes on the first two rows and
columns. -/
def TridiagonalTwoByTwoTrailingBlockSupport (n : ℕ)
    (E : Fin (n + 3) → Fin (n + 3) → ℝ) : Prop :=
  ∀ i j : Fin (n + 3), i.val < 2 ∨ j.val < 2 → E i j = 0

/-- General zero-prefix support predicate: a perturbation vanishes on the
leading `offset` rows and columns.  The tridiagonal `2 × 2` trailing-block
support predicate is the `offset = 2` instance. -/
def TridiagonalLeadingBlockSupport (m offset : ℕ)
    (E : Fin m → Fin m → ℝ) : Prop :=
  ∀ i j : Fin m, i.val < offset ∨ j.val < offset → E i j = 0

/-- A perturbation that vanishes on a deeper zero-prefix also vanishes on any
shallower zero-prefix. -/
theorem tridiagonalLeadingBlockSupport_of_le_offset
    (m offset offset' : ℕ) (E : Fin m → Fin m → ℝ)
    (hoff : offset ≤ offset')
    (hEsupp : TridiagonalLeadingBlockSupport m offset' E) :
    TridiagonalLeadingBlockSupport m offset E := by
  intro i j hlead
  apply hEsupp
  rcases hlead with hi | hj
  · exact Or.inl (Nat.lt_of_lt_of_le hi hoff)
  · exact Or.inr (Nat.lt_of_lt_of_le hj hoff)

/-- The zero perturbation has any zero-prefix support, with any nonnegative
componentwise bound.  This is the base bookkeeping object for recursive
tridiagonal perturbation assembly. -/
theorem tridiagonalLeadingBlockSupport_zero_bound
    (m offset : ℕ) (β : ℝ) (hβ : 0 ≤ β) :
    ∃ Z : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |Z i j| ≤ β) ∧
      TridiagonalLeadingBlockSupport m offset Z ∧
      (∀ i j : Fin m, Z i j = 0) := by
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · intro i j
    simpa using hβ
  · intro i j hlead
    rfl
  · intro i j
    rfl

/-- Zero-prefix supported perturbations are closed under addition, and their
componentwise bounds add.  This is the offset-generic version used when several
recursive tridiagonal lifts are accumulated at different depths. -/
theorem tridiagonalLeadingBlockSupport_add_bound
    (m offset : ℕ) (E F : Fin m → Fin m → ℝ) (βE βF : ℝ)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ βE)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ βF)
    (hEsupp : TridiagonalLeadingBlockSupport m offset E)
    (hFsupp : TridiagonalLeadingBlockSupport m offset F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ βE + βF) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) := by
  refine ⟨fun i j => E i j + F i j, ?_, ?_, ?_⟩
  · intro i j
    calc
      |E i j + F i j| ≤ |E i j| + |F i j| := abs_add_le _ _
      _ ≤ βE + βF := add_le_add (hEbound i j) (hFbound i j)
  · intro i j hlead
    change E i j + F i j = 0
    rw [hEsupp i j hlead, hFsupp i j hlead, add_zero]
  · intro i j
    rfl

/-- Add two zero-prefix supported perturbations, allowing each input to be
supported at a deeper offset than the common output offset. -/
theorem tridiagonalLeadingBlockSupport_add_bound_of_le_offset
    (m offset offsetE offsetF : ℕ) (E F : Fin m → Fin m → ℝ) (βE βF : ℝ)
    (hoffE : offset ≤ offsetE) (hoffF : offset ≤ offsetF)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ βE)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ βF)
    (hEsupp : TridiagonalLeadingBlockSupport m offsetE E)
    (hFsupp : TridiagonalLeadingBlockSupport m offsetF F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ βE + βF) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) :=
  tridiagonalLeadingBlockSupport_add_bound m offset E F βE βF
    hEbound hFbound
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetE E
      hoffE hEsupp)
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetF F
      hoffF hFsupp)

/-- The specialized trailing-block support predicate is exactly the
zero-prefix support predicate with offset two. -/
theorem tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport
    (n : ℕ) (E : Fin (n + 3) → Fin (n + 3) → ℝ) :
    TridiagonalTwoByTwoTrailingBlockSupport n E ↔
      TridiagonalLeadingBlockSupport (n + 3) 2 E := by
  rfl

/-- Supported perturbations in the trailing block after a leading `2 × 2`
tridiagonal pivot are closed under addition, and their componentwise bounds add. -/
theorem tridiagonalTwoByTwoTrailingBlockSupport_add_bound
    (n : ℕ) (E F : Fin (n + 3) → Fin (n + 3) → ℝ) (βE βF : ℝ)
    (hEbound : ∀ i j : Fin (n + 3), |E i j| ≤ βE)
    (hFbound : ∀ i j : Fin (n + 3), |F i j| ≤ βF)
    (hEsupp : TridiagonalTwoByTwoTrailingBlockSupport n E)
    (hFsupp : TridiagonalTwoByTwoTrailingBlockSupport n F) :
    ∃ G : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |G i j| ≤ βE + βF) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n G ∧
      (∀ i j : Fin (n + 3), G i j = E i j + F i j) := by
  refine ⟨fun i j => E i j + F i j, ?_, ?_, ?_⟩
  · intro i j
    calc
      |E i j + F i j| ≤ |E i j| + |F i j| := abs_add_le _ _
      _ ≤ βE + βF := add_le_add (hEbound i j) (hFbound i j)
  · intro i j hlead
    change E i j + F i j = 0
    rw [hEsupp i j hlead, hFsupp i j hlead, add_zero]
  · intro i j
    rfl

/-- Lift a perturbation on the recursive trailing subproblem after a leading
`2 × 2` tridiagonal pivot into the ambient local block.  Entries outside the
embedded trailing subproblem are set to zero. -/
noncomputable def tridiagonalTwoByTwoLiftTrailingPerturbation (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → ℝ) :
    Fin (n + 3) → Fin (n + 3) → ℝ :=
  fun i j =>
    if hi : ∃ a : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n a = i then
      if hj : ∃ b : Fin (n + 1),
          tridiagonalTwoByTwoTrailingSubproblemIndex n b = j then
        E (Classical.choose hi) (Classical.choose hj)
      else 0
    else 0

/-- A leading-row/column index is not in the embedded recursive trailing
subproblem after a leading `2 × 2` tridiagonal pivot. -/
theorem not_exists_tridiagonalTwoByTwoTrailingSubproblemIndex_of_val_lt_two
    {n : ℕ} {i : Fin (n + 3)} (hi : i.val < 2) :
    ¬ ∃ a : Fin (n + 1), tridiagonalTwoByTwoTrailingSubproblemIndex n a = i := by
  intro h
  rcases h with ⟨a, ha⟩
  have hval := congrArg Fin.val ha
  have hge : 2 ≤ i.val := by
    rw [← hval]
    simp [tridiagonalTwoByTwoTrailingSubproblemIndex]
  exact (not_lt_of_ge hge) hi

/-- The lifted recursive trailing perturbation agrees with the source
perturbation on embedded trailing-subproblem entries. -/
@[simp] theorem tridiagonalTwoByTwoLiftTrailingPerturbation_apply_embedded
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ)
    (i j : Fin (n + 1)) :
    tridiagonalTwoByTwoLiftTrailingPerturbation n E
        (tridiagonalTwoByTwoTrailingSubproblemIndex n i)
        (tridiagonalTwoByTwoTrailingSubproblemIndex n j) =
      E i j := by
  classical
  let emb := tridiagonalTwoByTwoTrailingSubproblemIndex n
  have hi : ∃ a : Fin (n + 1), emb a = emb i := ⟨i, rfl⟩
  have hj : ∃ b : Fin (n + 1), emb b = emb j := ⟨j, rfl⟩
  have hci : Classical.choose hi = i := by
    exact (tridiagonalTwoByTwoTrailingSubproblemIndex_injective n)
      (Classical.choose_spec hi)
  have hcj : Classical.choose hj = j := by
    exact (tridiagonalTwoByTwoTrailingSubproblemIndex_injective n)
      (Classical.choose_spec hj)
  simp [tridiagonalTwoByTwoLiftTrailingPerturbation, emb, hi, hj, hci, hcj]

/-- Componentwise bounds lift from the recursive trailing subproblem to the
ambient perturbation. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_bound
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (hEbound : ∀ i j : Fin (n + 1), |E i j| ≤ β) :
    ∀ i j : Fin (n + 3),
      |tridiagonalTwoByTwoLiftTrailingPerturbation n E i j| ≤ β := by
  classical
  have hβ : 0 ≤ β := by
    exact (abs_nonneg (E 0 0)).trans (hEbound 0 0)
  intro i j
  by_cases hi : ∃ a : Fin (n + 1),
      tridiagonalTwoByTwoTrailingSubproblemIndex n a = i
  · by_cases hj : ∃ b : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n b = j
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_pos hj]
      exact hEbound (Classical.choose hi) (Classical.choose hj)
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_neg hj]
      simpa using hβ
  · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_neg hi]
    simpa using hβ

/-- The lifted recursive trailing perturbation is supported entirely in the
trailing block left after the leading `2 × 2` pivot. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_support
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) :
    TridiagonalTwoByTwoTrailingBlockSupport n
      (tridiagonalTwoByTwoLiftTrailingPerturbation n E) := by
  classical
  intro i j hlead
  rcases hlead with hi | hj
  · have hnot :=
      not_exists_tridiagonalTwoByTwoTrailingSubproblemIndex_of_val_lt_two hi
    simp [tridiagonalTwoByTwoLiftTrailingPerturbation, hnot]
  · by_cases hi : ∃ a : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n a = i
    · have hnot :=
        not_exists_tridiagonalTwoByTwoTrailingSubproblemIndex_of_val_lt_two hj
      simp [tridiagonalTwoByTwoLiftTrailingPerturbation, hi, hnot]
    · simp [tridiagonalTwoByTwoLiftTrailingPerturbation, hi]

/-- Lifting a recursive trailing-subproblem perturbation through a leading
`2 × 2` tridiagonal pivot shifts any existing zero-prefix support by two
ambient indices.  This is the support bookkeeping for iterating the
tridiagonal recursion. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport
    (n offset : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hEsupp : TridiagonalLeadingBlockSupport (n + 1) offset E) :
    TridiagonalLeadingBlockSupport (n + 3) (offset + 2)
      (tridiagonalTwoByTwoLiftTrailingPerturbation n E) := by
  classical
  intro i j hlead
  by_cases hi : ∃ a : Fin (n + 1),
      tridiagonalTwoByTwoTrailingSubproblemIndex n a = i
  · by_cases hj : ∃ b : Fin (n + 1),
        tridiagonalTwoByTwoTrailingSubproblemIndex n b = j
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_pos hj]
      apply hEsupp
      rcases hlead with hilt | hjlt
      · left
        have hval :
            (Classical.choose hi).val + 2 = i.val := by
          simpa [tridiagonalTwoByTwoTrailingSubproblemIndex] using
            congrArg Fin.val (Classical.choose_spec hi)
        have hsum : (Classical.choose hi).val + 2 < offset + 2 := by
          rwa [hval]
        exact (Nat.add_lt_add_iff_right (k := 2)).1 hsum
      · right
        have hval :
            (Classical.choose hj).val + 2 = j.val := by
          simpa [tridiagonalTwoByTwoTrailingSubproblemIndex] using
            congrArg Fin.val (Classical.choose_spec hj)
        have hsum : (Classical.choose hj).val + 2 < offset + 2 := by
          rwa [hval]
        exact (Nat.add_lt_add_iff_right (k := 2)).1 hsum
    · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_pos hi, dif_neg hj]
  · rw [tridiagonalTwoByTwoLiftTrailingPerturbation, dif_neg hi]

/-- Package the recursive trailing perturbation lift with its ambient bound,
shifted zero-prefix support, and embedded-entry identity. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_bound_leadingBlockSupport
    (n offset : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (hEbound : ∀ i j : Fin (n + 1), |E i j| ≤ β)
    (hEsupp : TridiagonalLeadingBlockSupport (n + 1) offset E) :
    ∃ ΔR : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔR i j| ≤ β) ∧
      TridiagonalLeadingBlockSupport (n + 3) (offset + 2) ΔR ∧
      (∀ i j : Fin (n + 1),
        ΔR (tridiagonalTwoByTwoTrailingSubproblemIndex n i)
          (tridiagonalTwoByTwoTrailingSubproblemIndex n j) = E i j) := by
  refine ⟨tridiagonalTwoByTwoLiftTrailingPerturbation n E, ?_, ?_, ?_⟩
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_bound n E β hEbound
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_leadingBlockSupport
      n offset E hEsupp
  · intro i j
    exact tridiagonalTwoByTwoLiftTrailingPerturbation_apply_embedded n E i j

/-- Package the recursive trailing perturbation lift with its ambient bound,
support, and embedded-entry identity. -/
theorem tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support
    (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → ℝ) (β : ℝ)
    (hEbound : ∀ i j : Fin (n + 1), |E i j| ≤ β) :
    ∃ ΔR : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔR i j| ≤ β) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔR ∧
      (∀ i j : Fin (n + 1),
        ΔR (tridiagonalTwoByTwoTrailingSubproblemIndex n i)
          (tridiagonalTwoByTwoTrailingSubproblemIndex n j) = E i j) := by
  refine ⟨tridiagonalTwoByTwoLiftTrailingPerturbation n E, ?_, ?_, ?_⟩
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_bound n E β hEbound
  · exact tridiagonalTwoByTwoLiftTrailingPerturbation_support n E
  · intro i j
    exact tridiagonalTwoByTwoLiftTrailingPerturbation_apply_embedded n E i j

/-- Any index with value `< 2` is outside the first trailing scalar after a
leading `2 × 2` tridiagonal pivot. -/
theorem ne_tridiagonalTwoByTwoFirstTrailingIndex_of_val_lt_two
    {n : ℕ} {i : Fin (n + 3)} (hi : i.val < 2) :
    i ≠ tridiagonalTwoByTwoFirstTrailingIndex n := by
  intro h
  have hlt : (tridiagonalTwoByTwoFirstTrailingIndex n).val < 2 := by
    rw [← h]
    exact hi
  have hval : (tridiagonalTwoByTwoFirstTrailingIndex n).val = 2 := by simp
  rw [hval] at hlt
  exact (Nat.lt_irrefl 2) hlt

end NumStability
