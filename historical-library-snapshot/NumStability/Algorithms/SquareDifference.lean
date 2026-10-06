-- Algorithms/SquareDifference.lean
--
-- Higham Chapter 3, Problem 3.8.

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.ComplexArithmetic

namespace NumStability

/-!
# Difference of Squares

Higham Chapter 3, Problem 3.8 asks which formula is more accurate for
computing `x^2 - y^2`: the direct subtraction of rounded squares or the
factored form `(x+y)(x-y)`.  The local theorems expose the standard comparison:
the direct route is bounded by a majorant proportional to `|x*x| + |y*y|`,
while the factored route has a relative-error form proportional to
`|x^2 - y^2|`.
-/

/-- Direct floating-point route for `x^2 - y^2`. -/
noncomputable def fl_squareDiff_direct (fp : FPModel) (x y : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_mul x x) (fp.fl_mul y y)

/-- Factored floating-point route for `x^2 - y^2`. -/
noncomputable def fl_squareDiff_factored (fp : FPModel) (x y : ℝ) : ℝ :=
  fp.fl_mul (fp.fl_add x y) (fp.fl_sub x y)

/-- Exact difference-of-squares identity used by the factored route. -/
theorem squareDiff_factor_identity (x y : ℝ) :
    (x + y) * (x - y) = x ^ 2 - y ^ 2 := by
  ring

/-- **Problem 3.8, direct route.**

The route `fl(fl(x*x) - fl(y*y))` has an absolute error bound proportional to
`|x*x| + |y*y|`.  This is the cancellation-sensitive majorant. -/
theorem fl_squareDiff_direct_error_bound (fp : FPModel)
    (hγ : gammaValid fp 2) (x y : ℝ) :
    |fl_squareDiff_direct fp x y - (x ^ 2 - y ^ 2)| ≤
      gamma fp 2 * (|x * x| + |y * y|) := by
  simpa [fl_squareDiff_direct, pow_two] using
    fl_mul_sub_error_le_gamma2 fp hγ x y x y

/-- **Problem 3.8, factored route, relative-error form.**

The route `fl(fl(x+y) * fl(x-y))` has the source-friendly form

`fl = (x^2 - y^2) * (1 + theta)`, `|theta| <= gamma_3`.

Thus its absolute error is proportional to the final exact magnitude
`|x^2 - y^2|`, rather than the cancellation-sensitive majorant
`|x*x| + |y*y|`. -/
theorem fl_squareDiff_factored_rel_error (fp : FPModel)
    (hγ : gammaValid fp 3) (x y : ℝ) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 3 ∧
        fl_squareDiff_factored fp x y = (x ^ 2 - y ^ 2) * (1 + θ) := by
  obtain ⟨δadd, hδadd, hadd⟩ := fp.model_add x y
  obtain ⟨δsub, hδsub, hsub⟩ := fp.model_sub x y
  obtain ⟨δmul, hδmul, hmul⟩ :=
    fp.model_mul (fp.fl_add x y) (fp.fl_sub x y)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hγ2 : gammaValid fp 2 := gammaValid_mono fp (by norm_num) hγ
  have hδaddγ : |δadd| ≤ gamma fp 1 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ1)
  have hδsubγ : |δsub| ≤ gamma fp 1 :=
    le_trans hδsub (u_le_gamma fp (by norm_num) hγ1)
  have hδmulγ : |δmul| ≤ gamma fp 1 :=
    le_trans hδmul (u_le_gamma fp (by norm_num) hγ1)
  obtain ⟨θ2, hθ2, hθ2_eq⟩ :=
    gamma_mul fp 1 1 δadd δsub hδaddγ hδsubγ hγ2
  obtain ⟨θ3, hθ3, hθ3_eq⟩ :=
    gamma_mul fp 2 1 θ2 δmul hθ2 hδmulγ hγ
  refine ⟨θ3, hθ3, ?_⟩
  calc
    fl_squareDiff_factored fp x y
        = ((x + y) * (1 + δadd)) * ((x - y) * (1 + δsub)) *
            (1 + δmul) := by
            rw [fl_squareDiff_factored, hmul, hadd, hsub]
    _ = ((x + y) * (x - y)) * ((1 + δadd) * (1 + δsub)) *
            (1 + δmul) := by ring
    _ = (x ^ 2 - y ^ 2) * (1 + θ2) * (1 + δmul) := by
            rw [squareDiff_factor_identity, hθ2_eq]
    _ = (x ^ 2 - y ^ 2) * ((1 + θ2) * (1 + δmul)) := by ring
    _ = (x ^ 2 - y ^ 2) * (1 + θ3) := by
            rw [hθ3_eq]

/-- **Problem 3.8, factored route, absolute-error form.** -/
theorem fl_squareDiff_factored_error_bound (fp : FPModel)
    (hγ : gammaValid fp 3) (x y : ℝ) :
    |fl_squareDiff_factored fp x y - (x ^ 2 - y ^ 2)| ≤
      gamma fp 3 * |x ^ 2 - y ^ 2| := by
  obtain ⟨θ, hθ, hfl⟩ := fl_squareDiff_factored_rel_error fp hγ x y
  have hγ_nonneg : 0 ≤ gamma fp 3 := gamma_nonneg fp hγ
  calc
    |fl_squareDiff_factored fp x y - (x ^ 2 - y ^ 2)|
        = |(x ^ 2 - y ^ 2) * θ| := by
            rw [hfl]
            ring_nf
    _ = |x ^ 2 - y ^ 2| * |θ| := by rw [abs_mul]
    _ ≤ |x ^ 2 - y ^ 2| * gamma fp 3 :=
        mul_le_mul_of_nonneg_left hθ (abs_nonneg _)
    _ = gamma fp 3 * |x ^ 2 - y ^ 2| := by ring

end NumStability
