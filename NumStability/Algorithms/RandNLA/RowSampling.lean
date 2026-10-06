-- Algorithms/RandNLA/RowSampling.lean
--
-- Floating-point stability infrastructure for the row-sampling
-- meta-algorithm in Drineas--Mahoney's CACM RandNLA survey, Algorithm 2.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Algorithms.DotProduct
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.FiniteProbability

namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2: row sampling

Algorithm 2 of Drineas and Mahoney's CACM RandNLA survey samples rows of
`A` independently with probabilities `p_i`, and inserts the rescaled sampled
row in the output sketch. Equation (4) gives the norm-squared row distribution

`p_i = ||A_i*||_2^2 / ||A||_F^2`.

This file formalizes the literal sampled output matrix: output row `t` is the
sampled input row rescaled by `1 / sqrt(s * p_i)`. Unlike Algorithm 1,
Algorithm 2 does not accumulate repeated samples into a single entry. The
probabilistic analysis therefore studies the Gram matrix `Ãᵀ Ã`, which is the
quantity compared with `Aᵀ A` in equation (5) of the paper.
-/

-- ============================================================
-- Norm-squared row sampling probabilities
-- ============================================================

/-- Squared Euclidean norm of row `i`: `||A_i*||_2^2`. -/
noncomputable def rowNormSq {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  ∑ j : Fin n, A i j ^ 2

/-- Denominator for norm-squared row sampling probabilities:
    `∑ᵢ ||A_i*||_2^2 = ||A||_F^2`. -/
noncomputable def rowSqNormProbDen {m n : ℕ}
    (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNormSqRect A

/-- Norm-squared row sampling probability from equation (4):
    `p_i = ||A_i*||_2^2 / ||A||_F^2`. -/
noncomputable def rowSqNormProb {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : ℝ :=
  rowNormSq A i / rowSqNormProbDen A

/-- The squared row norms sum to the squared Frobenius norm. -/
theorem rowNormSq_sum_eq_frobNormSqRect {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    ∑ i : Fin m, rowNormSq A i = frobNormSqRect A := rfl

/-- Squared row norms are nonnegative. -/
theorem rowNormSq_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : 0 ≤ rowNormSq A i := by
  unfold rowNormSq
  exact Finset.sum_nonneg fun j _ => sq_nonneg (A i j)

/-- A squared row norm is zero iff the whole row is zero. -/
theorem rowNormSq_eq_zero_iff {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) : rowNormSq A i = 0 ↔ ∀ j : Fin n, A i j = 0 := by
  unfold rowNormSq
  constructor
  · intro h
    have hterm : ∀ j ∈ (Finset.univ : Finset (Fin n)), A i j ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (A i j))).mp h
    intro j
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp
      (hterm j (Finset.mem_univ j))
  · intro h
    apply Finset.sum_eq_zero
    intro j _
    rw [h j]
    ring

/-- A row containing a nonzero entry has positive squared row norm. -/
theorem rowNormSq_pos_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) (hAij : A i j ≠ 0) :
    0 < rowNormSq A i := by
  exact lt_of_le_of_ne (rowNormSq_nonneg A i)
    (fun hzero => hAij ((rowNormSq_eq_zero_iff A i).mp hzero.symm j))

/-- Norm-squared row probabilities are nonnegative when the Frobenius
    denominator is positive. -/
theorem rowSqNormProb_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (i : Fin m) :
    0 ≤ rowSqNormProb A i := by
  unfold rowSqNormProb
  exact div_nonneg (rowNormSq_nonneg A i) (le_of_lt hden)

/-- A row containing a nonzero entry has positive norm-squared probability. -/
theorem rowSqNormProb_pos_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (j : Fin n) (hAij : A i j ≠ 0) :
    0 < rowSqNormProb A i := by
  unfold rowSqNormProb
  exact div_pos (rowNormSq_pos_of_entry_ne_zero A i j hAij) hden

/-- Norm-squared row probabilities sum to one for a nonzero matrix. -/
theorem rowSqNormProb_sum_eq_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0) :
    ∑ i : Fin m, rowSqNormProb A i = 1 := by
  unfold rowSqNormProb rowSqNormProbDen
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  change frobNormSqRect A * (frobNormSqRect A)⁻¹ = 1
  exact mul_inv_cancel₀ hden

/-- A row containing a nonzero entry has nonzero norm-squared probability. -/
theorem rowSqNormProb_ne_zero_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (j : Fin n) (hAij : A i j ≠ 0) :
    rowSqNormProb A i ≠ 0 := by
  unfold rowSqNormProb rowSqNormProbDen
  have hrow : rowNormSq A i ≠ 0 :=
    ne_of_gt (rowNormSq_pos_of_entry_ne_zero A i j hAij)
  have hden : frobNormSqRect A ≠ 0 :=
    frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij
  exact div_ne_zero hrow hden

-- ============================================================
-- Exact and floating-point row-sampling updates
-- ============================================================

/-- A sampled row of an `m × n` matrix. -/
abbrev RowSample (m : ℕ) := Fin m

/-- A deterministic trace of sampled rows. -/
abbrev RowTrace (m steps : ℕ) := Fin steps → RowSample m

/-- Algorithm 2 row-rescaling denominator for a supplied exact row probability
    table: `sqrt(s * p_i)`. -/
noncomputable def rowSampleScaleDenWithProb {m : ℕ} (s : ℕ)
    (p : Fin m → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt ((s : ℝ) * p i)

/-- The row-rescaling denominator from a supplied exact probability table is
    nonzero when `s > 0` and the sampled row has positive probability. -/
theorem rowSampleScaleDenWithProb_ne_zero {m : ℕ} (s : ℕ)
    (p : Fin m → ℝ) (i : Fin m)
    (hs : 0 < (s : ℝ)) (hprob : 0 < p i) :
    rowSampleScaleDenWithProb s p i ≠ 0 := by
  have hmul : 0 < (s : ℝ) * p i := mul_pos hs hprob
  exact ne_of_gt (by
    unfold rowSampleScaleDenWithProb
    exact Real.sqrt_pos.2 hmul)

/-- A floating-point computation of the row-rescaling denominators
    `sqrt(s * p_i)` used by Algorithm 2.

    The probability table `p` is treated as an exact input law; this certificate
    only separates the square-root/denominator computation from the final
    rounded division used to form sampled rows. -/
structure ComputedRowScaleDen (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ) where
  den : Fin m → ℝ
  den_abs_error : Fin m → ℝ
  den_abs_error_nonneg : ∀ i, 0 ≤ den_abs_error i
  den_abs_error_bound :
    ∀ i, |den i - rowSampleScaleDenWithProb s p i| ≤ den_abs_error i
  den_ne_zero_of_pos : ∀ i, 0 < p i → den i ≠ 0

namespace ComputedRowScaleDen

variable {fp : FPModel} {m : ℕ} {s : ℕ} {p : Fin m → ℝ}

theorem entry_abs_error_bound (dhat : ComputedRowScaleDen fp s p)
    (i : Fin m) :
    |dhat.den i - rowSampleScaleDenWithProb s p i| ≤ dhat.den_abs_error i :=
  dhat.den_abs_error_bound i

theorem den_ne_zero (dhat : ComputedRowScaleDen fp s p)
    {i : Fin m} (hprob : 0 < p i) :
    dhat.den i ≠ 0 :=
  dhat.den_ne_zero_of_pos i hprob

/-- Scalar square-root perturbation used by concrete row-scale denominator
    routines. -/
theorem abs_sqrt_one_add_sub_one_le_abs (delta : ℝ)
    (hpos : 0 ≤ 1 + delta) :
    |Real.sqrt (1 + delta) - 1| ≤ |delta| := by
  have hden_pos : 0 < Real.sqrt (1 + delta) + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + delta)]
  have hden_ge_one : 1 ≤ Real.sqrt (1 + delta) + 1 := by
    nlinarith [Real.sqrt_nonneg (1 + delta)]
  have hden_ne : Real.sqrt (1 + delta) + 1 ≠ 0 := ne_of_gt hden_pos
  have hsqrt_sq : Real.sqrt (1 + delta) ^ 2 = 1 + delta :=
    Real.sq_sqrt hpos
  have hidentity :
      Real.sqrt (1 + delta) - 1 =
        delta / (Real.sqrt (1 + delta) + 1) := by
    field_simp [hden_ne]
    nlinarith
  rw [hidentity, abs_div]
  have hden_abs_ge_one : 1 ≤ |Real.sqrt (1 + delta) + 1| := by
    simp [abs_of_pos hden_pos, hden_ge_one]
  have hden_abs_pos : 0 < |Real.sqrt (1 + delta) + 1| :=
    lt_of_lt_of_le zero_lt_one hden_abs_ge_one
  have hmul :
      |delta| ≤ |delta| * |Real.sqrt (1 + delta) + 1| := by
    simpa using
      (mul_le_mul_of_nonneg_left hden_abs_ge_one (abs_nonneg delta))
  exact (div_le_iff₀ hden_abs_pos).2 hmul

/-- Exact row-scale denominator certificate.  This is useful for comparing
    theorem surfaces that charge only the final rounded division. -/
noncomputable def exact (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ)
    (hs : 0 < (s : ℝ)) :
    ComputedRowScaleDen fp s p where
  den := rowSampleScaleDenWithProb s p
  den_abs_error := fun _ => 0
  den_abs_error_nonneg := by intro _; exact le_rfl
  den_abs_error_bound := by intro _; simp
  den_ne_zero_of_pos := by
    intro i hprob
    exact rowSampleScaleDenWithProb_ne_zero s p i hs hprob

@[simp] theorem exact_den (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ) (hs : 0 < (s : ℝ)) :
    (exact fp s p hs).den = rowSampleScaleDenWithProb s p := rfl

@[simp] theorem exact_den_abs_error (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ) (hs : 0 < (s : ℝ)) :
    (exact fp s p hs).den_abs_error = fun _ => 0 := rfl

/-- Concrete denominator certificate for the routine
    `fl_sqrt (fl_mul (s : R) p_i)`.

    The probability table `p` is an exact sampling law by the project
    convention.  This constructor charges the non-probability arithmetic used
    to form the row-scale denominator: the scalar multiplication by `s` and the
    square-root primitive. -/
noncomputable def flMulThenSqrt (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i)
    (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    ComputedRowScaleDen fp s p where
  den := fun i => fp.fl_sqrt (fp.fl_mul (s : ℝ) (p i))
  den_abs_error := fun i =>
    rowSampleScaleDenWithProb s p i *
      (Real.sqrt (1 + fp.u) * fp.u + fp.u)
  den_abs_error_nonneg := by
    intro i
    have htail : 0 ≤ Real.sqrt (1 + fp.u) * fp.u + fp.u := by
      exact add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) fp.u_nonneg) fp.u_nonneg
    exact mul_nonneg (Real.sqrt_nonneg _) htail
  den_abs_error_bound := by
    intro i
    let x : ℝ := (s : ℝ) * p i
    let xhat : ℝ := fp.fl_mul (s : ℝ) (p i)
    have hx_nonneg : 0 ≤ x := by
      dsimp [x]
      exact mul_nonneg (le_of_lt hs) (hp_nonneg i)
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (s : ℝ) (p i)
    have hxhat_eq : xhat = x * (1 + δm) := by
      dsimp [xhat, x]
      simpa using hmul
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hδm_upper : δm ≤ fp.u := (abs_le.mp hδm).2
    have hfactor_pos : 0 < 1 + δm := by linarith
    have hfactor_nonneg : 0 ≤ 1 + δm := le_of_lt hfactor_pos
    have hxhat_nonneg : 0 ≤ xhat := by
      rw [hxhat_eq]
      exact mul_nonneg hx_nonneg hfactor_nonneg
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat hxhat_nonneg
    let d : ℝ := Real.sqrt x
    let a : ℝ := Real.sqrt (1 + δm)
    have hd_nonneg : 0 ≤ d := Real.sqrt_nonneg _
    have ha_nonneg : 0 ≤ a := Real.sqrt_nonneg _
    have ha_le : a ≤ Real.sqrt (1 + fp.u) := by
      dsimp [a]
      exact Real.sqrt_le_sqrt (by linarith)
    have hsqrt_ratio : |a - 1| ≤ fp.u := by
      exact
        (abs_sqrt_one_add_sub_one_le_abs δm hfactor_nonneg).trans hδm
    have hscalar :
        |a * (1 + δs) - 1| ≤
          Real.sqrt (1 + fp.u) * fp.u + fp.u := by
      have hsplit : a * (1 + δs) - 1 = a * δs + (a - 1) := by ring
      calc
        |a * (1 + δs) - 1|
            = |a * δs + (a - 1)| := by rw [hsplit]
        _ ≤ |a * δs| + |a - 1| := abs_add_le _ _
        _ = a * |δs| + |a - 1| := by
              rw [abs_mul, abs_of_nonneg ha_nonneg]
        _ ≤ a * fp.u + fp.u := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hδs ha_nonneg)
                hsqrt_ratio
        _ ≤ Real.sqrt (1 + fp.u) * fp.u + fp.u := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right
                  (mul_le_mul_of_nonneg_right ha_le fp.u_nonneg) fp.u
    have hsqrt_xhat : Real.sqrt xhat = d * a := by
      rw [hxhat_eq]
      dsimp [d, a]
      rw [Real.sqrt_mul hx_nonneg (1 + δm)]
    have hmain :
        |Real.sqrt xhat * (1 + δs) - d| ≤
          d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) := by
      rw [hsqrt_xhat]
      have hsplit : d * a * (1 + δs) - d =
          d * (a * (1 + δs) - 1) := by ring
      calc
        |d * a * (1 + δs) - d|
            = |d * (a * (1 + δs) - 1)| := by rw [hsplit]
        _ = d * |a * (1 + δs) - 1| := by
              rw [abs_mul, abs_of_nonneg hd_nonneg]
        _ ≤ d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) :=
              mul_le_mul_of_nonneg_left hscalar hd_nonneg
    have htarget :
        |fp.fl_sqrt xhat - d| ≤
          d * (Real.sqrt (1 + fp.u) * fp.u + fp.u) := by
      rw [hsqrt]
      exact hmain
    simpa [xhat, x, d, rowSampleScaleDenWithProb] using htarget
  den_ne_zero_of_pos := by
    intro i hprob
    let x : ℝ := (s : ℝ) * p i
    let xhat : ℝ := fp.fl_mul (s : ℝ) (p i)
    have hx_pos : 0 < x := by
      dsimp [x]
      exact mul_pos hs hprob
    obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (s : ℝ) (p i)
    have hxhat_eq : xhat = x * (1 + δm) := by
      dsimp [xhat, x]
      simpa using hmul
    have hδm_lower : -fp.u ≤ δm := (abs_le.mp hδm).1
    have hfactor_pos : 0 < 1 + δm := by linarith
    have hxhat_pos : 0 < xhat := by
      rw [hxhat_eq]
      exact mul_pos hx_pos hfactor_pos
    obtain ⟨δs, hδs, hsqrt⟩ :=
      fp.model_sqrt xhat (le_of_lt hxhat_pos)
    have hsqrt_ne : Real.sqrt xhat ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hxhat_pos)
    have hδs_lower : -fp.u ≤ δs := (abs_le.mp hδs).1
    have hfactor_s_pos : 0 < 1 + δs := by linarith
    rw [hsqrt]
    exact mul_ne_zero hsqrt_ne (ne_of_gt hfactor_s_pos)

@[simp] theorem flMulThenSqrt_den (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flMulThenSqrt fp s p hp_nonneg hs hu).den =
      fun i => fp.fl_sqrt (fp.fl_mul (s : ℝ) (p i)) := rfl

@[simp] theorem flMulThenSqrt_den_abs_error (fp : FPModel) {m : ℕ}
    (s : ℕ) (p : Fin m → ℝ) (hp_nonneg : ∀ i, 0 ≤ p i)
    (hs : 0 < (s : ℝ)) (hu : fp.u < 1) :
    (flMulThenSqrt fp s p hp_nonneg hs hu).den_abs_error =
      fun i =>
        rowSampleScaleDenWithProb s p i *
          (Real.sqrt (1 + fp.u) * fp.u + fp.u) := rfl

end ComputedRowScaleDen

/-- A support-aware scalar relative denominator-error budget.  Rows with zero
    sampling probability have zero probability under the exact product law and
    are deliberately omitted from the denominator ratio. -/
noncomputable def rowScaleDenRelBudget (fp : FPModel) {m : ℕ}
    {s : ℕ} (p : Fin m → ℝ)
    (dhat : ComputedRowScaleDen fp s p) : ℝ :=
  ∑ i : Fin m,
    if 0 < p i then dhat.den_abs_error i / |dhat.den i| else 0

/-- Effective entrywise relative row-scaling error after both the denominator
    computation and the final rounded division are charged. -/
noncomputable def rowScaleComputedDenEffectiveRelError (fp : FPModel)
    {m : ℕ} {s : ℕ} (p : Fin m → ℝ)
    (dhat : ComputedRowScaleDen fp s p) : ℝ :=
  fp.u + (1 + fp.u) * rowScaleDenRelBudget fp p dhat

theorem rowScaleDenRelBudget_nonneg (fp : FPModel) {m : ℕ}
    {s : ℕ} (p : Fin m → ℝ)
    (dhat : ComputedRowScaleDen fp s p) :
    0 ≤ rowScaleDenRelBudget fp p dhat := by
  unfold rowScaleDenRelBudget
  apply Finset.sum_nonneg
  intro i _
  by_cases hprob : 0 < p i
  · simp [hprob, div_nonneg (dhat.den_abs_error_nonneg i) (abs_nonneg _)]
  · simp [hprob]

theorem rowScaleDenRelBudget_entry_le (fp : FPModel) {m : ℕ}
    {s : ℕ} (p : Fin m → ℝ)
    (dhat : ComputedRowScaleDen fp s p) {i : Fin m}
    (hprob : 0 < p i) :
    dhat.den_abs_error i / |dhat.den i| ≤
      rowScaleDenRelBudget fp p dhat := by
  classical
  unfold rowScaleDenRelBudget
  let f : Fin m → ℝ := fun a =>
    if 0 < p a then dhat.den_abs_error a / |dhat.den a| else 0
  have hf_nonneg : ∀ a ∈ (Finset.univ : Finset (Fin m)), 0 ≤ f a := by
    intro a _
    by_cases ha : 0 < p a
    · simp [f, ha, div_nonneg (dhat.den_abs_error_nonneg a) (abs_nonneg _)]
    · simp [f, ha]
  have hsingle :=
    Finset.single_le_sum hf_nonneg (Finset.mem_univ i)
  simpa [f, hprob] using hsingle

theorem rowScaleComputedDenEffectiveRelError_nonneg (fp : FPModel)
    {m : ℕ} {s : ℕ} (p : Fin m → ℝ)
    (dhat : ComputedRowScaleDen fp s p) :
    0 ≤ rowScaleComputedDenEffectiveRelError fp p dhat := by
  unfold rowScaleComputedDenEffectiveRelError
  have hrel := rowScaleDenRelBudget_nonneg fp p dhat
  have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  exact add_nonneg fp.u_nonneg (mul_nonneg hfac hrel)

/-- Exact Algorithm 2 row-scaling contribution using a supplied exact
    probability table. -/
noncomputable def rowSampleIncrementWithProb {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  A i j / rowSampleScaleDenWithProb s p i

/-- Floating-point Algorithm 2 row-scaling contribution using a supplied exact
    probability table. -/
noncomputable def fl_rowSampleIncrementWithProb (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (A i j) (rowSampleScaleDenWithProb s p i)

/-- Exact Algorithm 2 row-scaling contribution using supplied computed scale
    denominators. -/
noncomputable def rowSampleIncrementWithComputedDen {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (den : Fin m → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  A i j / den i

/-- Floating-point Algorithm 2 row-scaling contribution using supplied computed
    scale denominators. -/
noncomputable def fl_rowSampleIncrementWithComputedDen (fp : FPModel)
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (den : Fin m → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (A i j) (den i)

/-- Algorithm 2 row-rescaling denominator `sqrt(s * p_i)`. -/
noncomputable def rowSampleScaleDen {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) : ℝ :=
  Real.sqrt ((s : ℝ) * rowSqNormProb A i)

/-- The row-rescaling denominator is nonzero when `s > 0` and the sampled row
    has positive probability. -/
theorem rowSampleScaleDen_ne_zero {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (hs : 0 < (s : ℝ)) (hprob : 0 < rowSqNormProb A i) :
    rowSampleScaleDen s A i ≠ 0 := by
  have hmul : 0 < (s : ℝ) * rowSqNormProb A i :=
    mul_pos hs hprob
  exact ne_of_gt (by
    unfold rowSampleScaleDen
    exact Real.sqrt_pos.2 hmul)

/-- Exact Algorithm 2 row-scaling contribution for entry `(i, j)`. -/
noncomputable def rowSampleIncrement {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  A i j / rowSampleScaleDen s A i

/-- Floating-point Algorithm 2 row-scaling contribution for entry `(i, j)`. -/
noncomputable def fl_rowSampleIncrement (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (A i j) (rowSampleScaleDen s A i)

/-- Forward-error bound for a floating-point division. -/
theorem fl_div_error_bound (fp : FPModel) (a denom : ℝ)
    (hdenom : denom ≠ 0) :
    |fp.fl_div a denom - a / denom| ≤ |a / denom| * fp.u := by
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div a denom hdenom
  let t : ℝ := a / denom
  have herr : fp.fl_div a denom - t = t * δ := by
    rw [hdiv]
    ring
  calc
    |fp.fl_div a denom - a / denom|
        = |t * δ| := by
            rw [herr]
    _ = |t| * |δ| := abs_mul _ _
    _ ≤ |t| * fp.u := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
    _ = |a / denom| * fp.u := by
            simp [t]

/-- Forward-error bound for one row-sampled output entry using a supplied exact
    probability table. -/
theorem fl_rowSampleIncrementWithProb_error_bound (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (i : Fin m) (j : Fin n)
    (hdenom : rowSampleScaleDenWithProb s p i ≠ 0) :
    |fl_rowSampleIncrementWithProb fp s A p i j -
      rowSampleIncrementWithProb s A p i j| ≤
      |rowSampleIncrementWithProb s A p i j| * fp.u := by
  unfold fl_rowSampleIncrementWithProb rowSampleIncrementWithProb
  exact fl_div_error_bound fp (A i j) (rowSampleScaleDenWithProb s p i) hdenom

/-- Forward-error bound for one row-sampled output entry using a supplied
    computed scale denominator. -/
theorem fl_rowSampleIncrementWithComputedDen_error_bound (fp : FPModel)
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (den : Fin m → ℝ)
    (i : Fin m) (j : Fin n) (hdenom : den i ≠ 0) :
    |fl_rowSampleIncrementWithComputedDen fp A den i j -
      rowSampleIncrementWithComputedDen A den i j| ≤
      |rowSampleIncrementWithComputedDen A den i j| * fp.u := by
  unfold fl_rowSampleIncrementWithComputedDen rowSampleIncrementWithComputedDen
  exact fl_div_error_bound fp (A i j) (den i) hdenom

/-- Exact Algorithm 2 output sketch using a supplied exact probability table. -/
noncomputable def rowSampleSketchWithProb {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => rowSampleIncrementWithProb s A p (samples t) j

/-- Floating-point Algorithm 2 output sketch using a supplied exact probability
    table. -/
noncomputable def fl_rowSampleSketchWithProb (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => fl_rowSampleIncrementWithProb fp s A p (samples t) j

/-- Exact Algorithm 2 output sketch using supplied computed scale
    denominators. -/
noncomputable def rowSampleSketchWithComputedDen {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (den : Fin m → ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => rowSampleIncrementWithComputedDen A den (samples t) j

/-- Floating-point Algorithm 2 output sketch using supplied computed scale
    denominators. -/
noncomputable def fl_rowSampleSketchWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ) (den : Fin m → ℝ)
    (samples : RowTrace m steps) : Fin steps → Fin n → ℝ :=
  fun t j => fl_rowSampleIncrementWithComputedDen fp A den (samples t) j

/-- Entrywise forward-error bound for the Algorithm 2 output sketch using a
    supplied exact probability table. -/
theorem fl_rowSampleSketchWithProb_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (samples : RowTrace m steps) (t : Fin steps)
    (j : Fin n) (hdenom : rowSampleScaleDenWithProb s p (samples t) ≠ 0) :
    |fl_rowSampleSketchWithProb fp s A p samples t j -
      rowSampleSketchWithProb s A p samples t j| ≤
      |rowSampleSketchWithProb s A p samples t j| * fp.u := by
  exact fl_rowSampleIncrementWithProb_error_bound fp s A p (samples t) j hdenom

/-- Entrywise forward-error bound for the Algorithm 2 output sketch using
    supplied computed scale denominators. -/
theorem fl_rowSampleSketchWithComputedDen_error_bound (fp : FPModel)
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ) (den : Fin m → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : den (samples t) ≠ 0) :
    |fl_rowSampleSketchWithComputedDen fp A den samples t j -
      rowSampleSketchWithComputedDen A den samples t j| ≤
      |rowSampleSketchWithComputedDen A den samples t j| * fp.u := by
  exact fl_rowSampleIncrementWithComputedDen_error_bound fp A den (samples t) j hdenom

/-- Forward-error bound for one row-sampled output entry. This is the local
    division kernel used by Algorithm 2. -/
theorem fl_rowSampleIncrement_error_bound (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n)
    (hdenom : rowSampleScaleDen s A i ≠ 0) :
    |fl_rowSampleIncrement fp s A i j -
      rowSampleIncrement s A i j| ≤
      |rowSampleIncrement s A i j| * fp.u := by
  unfold fl_rowSampleIncrement rowSampleIncrement
  exact fl_div_error_bound fp (A i j) (rowSampleScaleDen s A i) hdenom

/-- Exact Algorithm 2 output sketch: output row `t` is the sampled input row
    rescaled by `1 / sqrt(s * p_i)`. -/
noncomputable def rowSampleSketch {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => rowSampleIncrement s A (samples t) j

/-- Floating-point Algorithm 2 output sketch, using the rounded division for
    each sampled row entry. -/
noncomputable def fl_rowSampleSketch (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin steps → Fin n → ℝ :=
  fun t j => fl_rowSampleIncrement fp s A (samples t) j

/-- Entrywise forward-error bound for the literal `s × n` Algorithm 2 output
    sketch. -/
theorem fl_rowSampleSketch_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hdenom : rowSampleScaleDen s A (samples t) ≠ 0) :
    |fl_rowSampleSketch fp s A samples t j -
      rowSampleSketch s A samples t j| ≤
      |rowSampleSketch s A samples t j| * fp.u := by
  exact fl_rowSampleIncrement_error_bound fp s A (samples t) j hdenom

/-- Perturbation from using a computed row-scale denominator instead of the
    ideal `sqrt(s*p_i)` denominator, stated relative to the exact sampled row
    entry. -/
theorem rowSampleIncrementWithComputedDen_ideal_rel_error_bound
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (dhat : ComputedRowScaleDen fp s p)
    (i : Fin m) (j : Fin n)
    (hs : 0 < (s : ℝ)) (hprob : 0 < p i) :
    |rowSampleIncrementWithComputedDen A dhat.den i j -
      rowSampleIncrementWithProb s A p i j| ≤
      |rowSampleIncrementWithProb s A p i j| *
        (dhat.den_abs_error i / |dhat.den i|) := by
  let d : ℝ := rowSampleScaleDenWithProb s p i
  let dh : ℝ := dhat.den i
  have hd : d ≠ 0 := by
    simpa [d] using rowSampleScaleDenWithProb_ne_zero s p i hs hprob
  have hdh : dh ≠ 0 := by
    simpa [dh] using dhat.den_ne_zero hprob
  have hdelta : |d - dh| ≤ dhat.den_abs_error i := by
    simpa [d, dh, abs_sub_comm] using dhat.den_abs_error_bound i
  have hdenprod_nonneg : 0 ≤ |dh| * |d| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsplit :
      A i j / dh - A i j / d =
        A i j * (d - dh) / (dh * d) := by
    field_simp [hdh, hd]
  unfold rowSampleIncrementWithComputedDen rowSampleIncrementWithProb
  calc
    |A i j / dh - A i j / d|
        = |A i j * (d - dh) / (dh * d)| := by rw [hsplit]
    _ = |A i j| * |d - dh| / (|dh| * |d|) := by
          rw [abs_div, abs_mul, abs_mul]
    _ ≤ |A i j| * dhat.den_abs_error i / (|dh| * |d|) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdelta (abs_nonneg _))
            hdenprod_nonneg
    _ = |A i j / d| * (dhat.den_abs_error i / |dh|) := by
          have hd_abs : |d| ≠ 0 := abs_ne_zero.mpr hd
          have hdh_abs : |dh| ≠ 0 := abs_ne_zero.mpr hdh
          rw [abs_div]
          field_simp [hd_abs, hdh_abs]

/-- Total entrywise row-scaling error when Algorithm 2 computes the scale
    denominator approximately and then performs the final division in floating
    point. -/
theorem fl_rowSampleSketchWithComputedDen_total_error_bound
    (fp : FPModel) {m n steps s : ℕ} (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (dhat : ComputedRowScaleDen fp s p)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hs : 0 < (s : ℝ)) (hprob : 0 < p (samples t)) :
    |fl_rowSampleSketchWithComputedDen fp A dhat.den samples t j -
      rowSampleSketchWithProb s A p samples t j| ≤
      |rowSampleSketchWithProb s A p samples t j| *
        (fp.u +
          (1 + fp.u) *
            (dhat.den_abs_error (samples t) / |dhat.den (samples t)|)) := by
  let Comp : ℝ :=
    rowSampleSketchWithComputedDen A dhat.den samples t j
  let Exact : ℝ := rowSampleSketchWithProb s A p samples t j
  let Fl : ℝ :=
    fl_rowSampleSketchWithComputedDen fp A dhat.den samples t j
  let rho : ℝ := dhat.den_abs_error (samples t) / |dhat.den (samples t)|
  have hden : dhat.den (samples t) ≠ 0 := dhat.den_ne_zero hprob
  have hround :
      |Fl - Comp| ≤ |Comp| * fp.u := by
    simpa [Fl, Comp] using
      fl_rowSampleSketchWithComputedDen_error_bound fp A dhat.den
        samples t j hden
  have hdenerr :
      |Comp - Exact| ≤ |Exact| * rho := by
    simpa [Comp, Exact, rho, rowSampleSketchWithComputedDen,
      rowSampleSketchWithProb] using
      rowSampleIncrementWithComputedDen_ideal_rel_error_bound
        fp A p dhat (samples t) j hs hprob
  have hcomp :
      |Comp| ≤ |Exact| * (1 + rho) := by
    calc
      |Comp| = |(Comp - Exact) + Exact| := by
          congr 1
          ring
      _ ≤ |Comp - Exact| + |Exact| := abs_add_le _ _
      _ ≤ |Exact| * rho + |Exact| := by
          exact add_le_add hdenerr le_rfl
      _ = |Exact| * (1 + rho) := by ring
  have hsplit : Fl - Exact = (Fl - Comp) + (Comp - Exact) := by ring
  calc
    |Fl - Exact|
        = |(Fl - Comp) + (Comp - Exact)| := by rw [hsplit]
    _ ≤ |Fl - Comp| + |Comp - Exact| := abs_add_le _ _
    _ ≤ |Comp| * fp.u + |Exact| * rho :=
        add_le_add hround hdenerr
    _ ≤ |Exact| * (1 + rho) * fp.u + |Exact| * rho := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcomp fp.u_nonneg) le_rfl
    _ = |Exact| * (fp.u + (1 + fp.u) * rho) := by ring

/-- Support-budget version of the total computed-denominator row-scaling
    error. -/
theorem fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
    (fp : FPModel) {m n steps s : ℕ} (A : Fin m → Fin n → ℝ)
    (p : Fin m → ℝ) (dhat : ComputedRowScaleDen fp s p)
    (samples : RowTrace m steps) (t : Fin steps) (j : Fin n)
    (hs : 0 < (s : ℝ)) (hprob : 0 < p (samples t)) :
    |fl_rowSampleSketchWithComputedDen fp A dhat.den samples t j -
      rowSampleSketchWithProb s A p samples t j| ≤
      |rowSampleSketchWithProb s A p samples t j| *
        rowScaleComputedDenEffectiveRelError fp p dhat := by
  have hlocal :=
    fl_rowSampleSketchWithComputedDen_total_error_bound
      fp A p dhat samples t j hs hprob
  have hrel :=
    rowScaleDenRelBudget_entry_le fp p dhat hprob
  have hfac : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  have htail :
      fp.u + (1 + fp.u) *
        (dhat.den_abs_error (samples t) / |dhat.den (samples t)|) ≤
      rowScaleComputedDenEffectiveRelError fp p dhat := by
    unfold rowScaleComputedDenEffectiveRelError
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_left hrel hfac) fp.u
  exact hlocal.trans
    (mul_le_mul_of_nonneg_left htail
      (abs_nonneg (rowSampleSketchWithProb s A p samples t j)))

-- ============================================================
-- Random row traces for the literal Algorithm 2 sampler
-- ============================================================

/-- Product probability mass of an Algorithm 2 row trace when each step samples
    independently from the norm-squared row probabilities. -/
noncomputable def rowSqNormTraceProbMass {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : ℝ :=
  ∏ t : Fin steps, rowSqNormProb A (samples t)

theorem rowSqNormTraceProbMass_nonneg {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (samples : RowTrace m steps) :
    0 ≤ rowSqNormTraceProbMass A samples := by
  unfold rowSqNormTraceProbMass
  exact Finset.prod_nonneg fun t _ =>
    rowSqNormProb_nonneg A hden (samples t)

theorem rowSqNormTraceProbMass_sum_eq_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0) :
    (∑ samples : RowTrace m steps,
      rowSqNormTraceProbMass A samples) = 1 := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun _ x => rowSqNormProb A x)
  have hleft :
      (∏ _ : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          rowSqNormProb A x) = 1 := by
    simp [rowSqNormProb_sum_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ i, rowSqNormProb A (x i))
        = ∑ samples : RowTrace m steps,
          rowSqNormTraceProbMass A samples := by
    simp [rowSqNormTraceProbMass, RowTrace]
  rw [← hright, ← hprod]
  exact hleft

/-- The canonical finite probability space for Algorithm 2 row traces with
    independent norm-squared row samples at every step. -/
noncomputable def rowSqNormTraceProbability {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A) :
    FiniteProbability (RowTrace m steps) where
  prob := rowSqNormTraceProbMass A
  prob_nonneg := rowSqNormTraceProbMass_nonneg A hden
  prob_sum := rowSqNormTraceProbMass_sum_eq_one A hden.ne'

/-- Trace-support predicate for Algorithm 2: every sampled row has positive
    norm-squared probability. Zero-probability rows have zero mass under the
    product trace law, but this predicate is exactly where the floating-point
    division model can be applied without a denominator-zero premise. -/
def rowTracePositiveProb {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) : Prop :=
  ∀ t : Fin steps, 0 < rowSqNormProb A (samples t)

theorem rowSqNormTraceProbMass_eq_zero_of_exists_prob_zero {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps)
    (hzero : ∃ t : Fin steps, rowSqNormProb A (samples t) = 0) :
    rowSqNormTraceProbMass A samples = 0 := by
  classical
  rcases hzero with ⟨t, ht⟩
  unfold rowSqNormTraceProbMass
  exact Finset.prod_eq_zero (Finset.mem_univ t) ht

/-- The independent Algorithm 2 row sampler assigns probability one to traces
    whose sampled rows all have positive row-sampling probability. -/
theorem rowSqNormTraceProbability_eventProb_rowTracePositiveProb
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) :
    (rowSqNormTraceProbability (steps := steps) A hden).eventProb
      {samples | rowTracePositiveProb A samples} = 1 := by
  classical
  let P := rowSqNormTraceProbability (steps := steps) A hden
  let Good : Set (RowTrace m steps) := {samples | rowTracePositiveProb A samples}
  have hcompl_zero : P.eventProb Goodᶜ = 0 := by
    unfold FiniteProbability.eventProb
    apply Finset.sum_eq_zero
    intro samples _
    by_cases hbad : samples ∈ Goodᶜ
    · have hnot_good : samples ∉ Good := by simpa using hbad
      have hexists : ∃ t : Fin steps, rowSqNormProb A (samples t) = 0 := by
        by_contra hno
        have hgood : samples ∈ Good := by
          intro t
          have hne : rowSqNormProb A (samples t) ≠ 0 := by
            intro hzero
            exact hno ⟨t, hzero⟩
          exact lt_of_le_of_ne
            (rowSqNormProb_nonneg A hden (samples t)) (Ne.symm hne)
        exact hnot_good hgood
      have hmass :=
        rowSqNormTraceProbMass_eq_zero_of_exists_prob_zero A samples hexists
      simp [P, Good, rowSqNormTraceProbability, hbad, hmass]
    · simp [hbad]
  have hsplit := P.eventProb_add_eventProb_compl Good
  rw [hcompl_zero] at hsplit
  linarith

end NumStability
