-- NumStability/Source/Higham/Chapter01/Section14/CancellationOfRoundingErrors/Algorithm02RoundedCore.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Analysis.CancellationOfRoundingErrors`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.Rounding
import NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.CancellationOfRoundingErrors
import NumStability.Source.Higham.Chapter01.Problem05.CompensatedLogarithm.Basic
import NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic

/-!
# Algorithm02RoundedCore

Relocated from `NumStability.Analysis.CancellationOfRoundingErrors` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Cancellation of rounding errors (compatibility module)

Compatibility facade retained so existing imports of
`NumStability.Analysis.CancellationOfRoundingErrors`
keep resolving. Most declarations moved unchanged to the canonical Higham
Chapter 1 module imported above. Twenty-seven declarations remain here because
their private identities or dependencies on shared modules require the original
module boundary. The module's original imports are re-stated so consumers
reaching identifiers transitively through this path retain the same surface.
-/

namespace NumStability

open Filter
open scoped Topology

/-- Source-domain radius for `y = exp x`: if `|x| <= X`, then the exact
exponential value used by Algorithm 2 satisfies
`|exp x - 1| <= exp X - 1`. -/
theorem expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le
    {x X : ℝ} (hx : |x| ≤ X) :
    |Real.exp x - 1| ≤ Real.exp X - 1 :=
  real_abs_exp_sub_one_le_of_abs_le hx
/-- `x`-radius exact-subtraction fact for the Algorithm 2 subtraction
`exp x*(1+delta) - 1`. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hcombined_radius :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  let r : ℝ := Real.exp X - 1
  have hX_nonneg : 0 ≤ X := le_trans (abs_nonneg x) hx_radius
  have hr_nonneg : 0 ≤ r := by
    have hone : (1 : ℝ) ≤ Real.exp X := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hX_nonneg
    dsimp [r]
    linarith
  have hy_radius : |Real.exp x - 1| ≤ r := by
    simpa [r] using expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le hx_radius
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_perturb_sterbenz_radius
      (fp := fp) (fmt := fmt) (y := Real.exp x) (delta := delta) (r := r)
      hsubRound hyhatFinite honeFinite hy_radius hdelta_u hr_nonneg
      (by simpa [r] using hcombined_radius)
/-- Compact source-domain exact-subtraction fact for Algorithm 2.  The single
smallness condition `exp X*(1+u) <= 4/3` implies the propagated Sterbenz
radius for the subtraction `exp x*(1+delta) - 1`. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_sterbenz_radius
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u
      (expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
        fp hsmall)
/-- `x`-radius version of the finite round-to-even/Sterbenz exact-subtraction
bridge for Algorithm 2 equation (1.9).  This packages the source's small-`x`
language: from `|x| <= X`, `y = exp x` stays within `exp X - 1` of `1`, and
the rounded exponential perturbation keeps `yhat` inside the Sterbenz ball. -/
theorem
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hcombined_radius :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          (((Real.exp x * (1 + delta)) - 1) * (1 + epsSub)) /
            (Real.log (Real.exp x * (1 + delta)) * (1 + epsLog)) *
              (1 + epsDiv) := by
  let r : ℝ := Real.exp X - 1
  have hX_nonneg : 0 ≤ X := le_trans (abs_nonneg x) hx_radius
  have hr_nonneg : 0 ≤ r := by
    have hone : (1 : ℝ) ≤ Real.exp X := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hX_nonneg
    dsimp [r]
    linarith
  have hy_radius : |Real.exp x - 1| ≤ r := by
    simpa [r] using expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le hx_radius
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_perturb_sterbenz_radius
      (fp := fp) (fmt := fmt) (y := Real.exp x) (delta := delta)
      (logHat := logHat) (epsLog := epsLog) (r := r)
      hsubRound hyhatFinite honeFinite hy_radius hdelta_u hr_nonneg
      (by simpa [r] using hcombined_radius) hepsLog hlog hlogHat
/-- Compact source-domain smallness version of the finite round-to-even
Sterbenz bridge for Algorithm 2 equation (1.9).  The single condition
`exp X*(1+u) <= 4/3` implies the propagated local radius needed for exact
subtraction. -/
theorem
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0) :
    ∃ epsSub epsDiv : ℝ,
      epsSub = 0 ∧
      |epsSub| ≤ fp.u ∧ |epsLog| ≤ fp.u ∧ |epsDiv| ≤ fp.u ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          (((Real.exp x * (1 + delta)) - 1) * (1 + epsSub)) /
            (Real.log (Real.exp x * (1 + delta)) * (1 + epsLog)) *
              (1 + epsDiv) := by
  exact
    expm1Algorithm2RoundedCore_eq_source_1_9_of_finiteRoundToEven_exp_x_sterbenz_radius
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u
      (expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
        fp hsmall)
      hepsLog hlog hlogHat
/-- Compact source-domain `gamma_2` core wrapper for Algorithm 2 on the
finite round-to-even/Sterbenz path.  The subtraction `exp x*(1+delta)-1` is
proved exact from the source smallness condition, so only the rounded log and
final division factors are charged. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  have hsubExact :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        Real.exp x * (1 + delta) - 1 :=
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_exact_sub
      fp (Real.exp x * (1 + delta)) logHat epsLog hsubExact hepsLog hlog
      hlogHat hposLog hvalid2
/-- Relative-error form of the compact source-domain `gamma_2` Algorithm 2
core wrapper on the finite round-to-even/Sterbenz path. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  have hsubExact :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        Real.exp x * (1 + delta) - 1 :=
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_exact_sub
      fp (Real.exp x * (1 + delta)) logHat epsLog hg hsubExact hepsLog hlog
      hlogHat hposLog hvalid2
/-- Rounded-exp-produced `yhat` version of the compact source-domain exact
subtraction fact.  If the value used by Algorithm 2 is explicitly the finite
round-to-even value of `exp x`, its finite representability follows from the
rounding selector rather than being an external hypothesis. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  have hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)) := by
    simpa [hyhatRound] using fmt.finiteRoundToEven_finiteSystem (Real.exp x)
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
/-- Rounded-exp-produced `yhat` version of the compact source-domain `gamma_2`
Algorithm 2 core wrapper.  This discharges the finite-representability
hypothesis for `yhat` from the concrete equality
`yhat = finiteRoundToEven(exp x)`. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  have hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)) := by
    simpa [hyhatRound] using fmt.finiteRoundToEven_finiteSystem (Real.exp x)
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2
/-- Relative-error form of the rounded-exp-produced `gamma_2` Algorithm 2 core
wrapper. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  have hyhatFinite : fmt.finiteSystem (Real.exp x * (1 + delta)) := by
    simpa [hyhatRound] using fmt.finiteRoundToEven_finiteSystem (Real.exp x)
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_x_mul_one_add_u_sterbenz
      fp fmt hg hsubRound hyhatFinite honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2
/-- Finite-normal rounded-exp version of the compact source-domain exact
subtraction fact.  This consumes the round-to-even normal-range contract for
`exp x` to derive the `|delta| <= u` hypothesis used by the Sterbenz radius
wrapper. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  have hdelta_u :
      |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
      fp fmt hyhatRound hsubRound honeFinite hx_radius hdelta_u hsmall
/-- Finite-normal rounded-exp version of the compact source-domain `gamma_2`
Algorithm 2 core wrapper.  The relative-error bound for the rounded
exponential is derived from the finite round-to-even normal-range contract. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  have hdelta_u :
      |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
      fp fmt hyhatRound hsubRound honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2
/-- Relative-error form of the finite-normal rounded-exp `gamma_2` Algorithm 2
core wrapper. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat epsLog X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  have hdelta_u :
      |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_rounded_exp_x_mul_one_add_u_sterbenz
      fp fmt hg hyhatRound hsubRound honeFinite hx_radius hdelta_u hsmall
      hepsLog hlog hlogHat hposLog hvalid2
/-- Finite-normal rounded-exp/log version of the compact source-domain
`gamma_2` Algorithm 2 core wrapper.  Both the rounded exponential and rounded
logarithm error witnesses are produced from finite round-to-even normal-range
contracts; the subtraction operation link remains explicit. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  rcases
    expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
      fp fmt hu hunit_lt_one hlognormal hlogRound with
    ⟨epsLog, hepsLog, hlog, hlogHat, hposLog⟩
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
      fp fmt hu hxnormal hyhatRound hsubRound honeFinite hx_radius hsmall
      hepsLog hlog hlogHat hposLog hvalid2
/-- Relative-error form of the finite-normal rounded-exp/log `gamma_2`
Algorithm 2 core wrapper. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hsubRound :
      fp.fl_sub (Real.exp x * (1 + delta)) 1 =
        fmt.finiteRoundToEvenOp BasicOp.sub (Real.exp x * (1 + delta)) 1)
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  rcases
    expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
      fp fmt hu hunit_lt_one hlognormal hlogRound with
    ⟨epsLog, hepsLog, hlog, hlogHat, hposLog⟩
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_finiteNormal_sterbenz
      fp fmt hg hu hxnormal hyhatRound hsubRound honeFinite hx_radius hsmall
      hepsLog hlog hlogHat hposLog hvalid2
/-- Finite-normal rounded-exp version of exact subtraction using a
routine-level finite round-to-even subtraction link rather than a pointwise
operation equality at the produced `yhat`. -/
theorem
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz_of_subtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta X : ℝ}
    (hsubLink : finiteRoundToEvenSubtractionLink fp fmt)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    fp.fl_sub (Real.exp x * (1 + delta)) 1 =
      Real.exp x * (1 + delta) - 1 := by
  exact
    expm1Algorithm2_fl_sub_eq_exact_of_finiteRoundToEven_exp_finiteNormal_sterbenz
      fp fmt hu hxnormal hyhatRound
      (hsubLink.sub_one (Real.exp x * (1 + delta)))
      honeFinite hx_radius hsmall
/-- Finite-normal rounded-exp/log `gamma_2` core wrapper using a routine-level
finite round-to-even subtraction link.  The rounded exp/log witnesses come
from finite round-to-even normal-range contracts; the subtraction link is now
one routine-level hypothesis instead of a pointwise equality at `yhat`. -/
theorem
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hsubLink : finiteRoundToEvenSubtractionLink fp fmt)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    ∃ theta : ℝ,
      |theta| ≤ gamma fp 2 ∧
        expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat =
          expm1LogRatio (Real.exp x * (1 + delta)) * (1 + theta) := by
  exact
    expm1Algorithm2RoundedCore_eq_logRatio_mul_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
      fp fmt hu hunit_lt_one hxnormal hlognormal hyhatRound hlogRound
      (hsubLink.sub_one (Real.exp x * (1 + delta)))
      honeFinite hx_radius hsmall hvalid2
/-- Relative-error form of the finite-normal rounded-exp/log `gamma_2` wrapper
with a routine-level finite round-to-even subtraction link. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz_of_subtractionLink
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hg : expm1LogRatio (Real.exp x * (1 + delta)) ≠ 0)
    (hsubLink : finiteRoundToEvenSubtractionLink fp fmt)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (honeFinite : fmt.finiteSystem 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ))
    (hvalid2 : gammaValid fp 2) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x * (1 + delta))) ≤ gamma fp 2 := by
  exact
    expm1Algorithm2RoundedCore_relError_le_gamma2_of_finiteRoundToEven_exp_log_finiteNormal_sterbenz
      fp fmt hg hu hunit_lt_one hxnormal hlognormal hyhatRound hlogRound
      (hsubLink.sub_one (Real.exp x * (1 + delta)))
      honeFinite hx_radius hsmall hvalid2
/-- `x`-radius version of the local Algorithm 2 `3.5u` bridge.  This packages
the source phrase "for small `x` (`y ≈ 1`)": a bound `|x| <= X` gives
`|exp x - 1| <= exp X - 1`, the rounded exponential relation gives the
combined `yhat` radius `(exp X - 1) + exp X*u`, and the existing local
Algorithm 2 theorem consumes that radius. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound
    (fp : FPModel) {x delta logHat epsLog X : ℝ}
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0) (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hcombined_radius :
      (Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u ≤ (1 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x))
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  let r : ℝ := Real.exp X - 1
  have hX_nonneg : 0 ≤ X := le_trans (abs_nonneg x) hx_radius
  have hr_nonneg : 0 ≤ r := by
    have hone : (1 : ℝ) ≤ Real.exp X := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hX_nonneg
    dsimp [r]
    linarith
  have hy_radius : |Real.exp x - 1| ≤ r := by
    simpa [r] using expm1Algorithm2_exp_sub_one_abs_le_of_abs_x_le hx_radius
  have hy0 : Real.exp x ≠ 1 := by
    intro h
    exact hx0 ((Real.exp_eq_one_iff x).mp h)
  have hg : expm1LogRatio (Real.exp x) ≠ 0 :=
    expm1LogRatio_exp_ne_zero_of_ne_zero hx0
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_perturb_radius_bound
      (fp := fp) (y := Real.exp x) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (r := r)
      hg hepsLog hlog hlogHat hposLog hvalid3 hy0 hyhat0
      hy_radius hdelta_u hr_nonneg (by simpa [r] using hcombined_radius)
  simpa [r] using hbase
/-- Source-domain smallness version of the `x`-radius Algorithm 2 `3.5u`
bridge.  The side condition `exp X*(1+u) <= 4/3` is a compact way to state
that the propagated rounded-exponential radius stays inside the local
`1/3` ball required by the denominator-free slow-ratio bound. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound
    (fp : FPModel) {x delta logHat epsLog X : ℝ}
    (hepsLog : |epsLog| ≤ fp.u)
    (hlog : logHat = Real.log (Real.exp x * (1 + delta)) * (1 + epsLog))
    (hlogHat : logHat ≠ 0)
    (hposLog : 0 < 1 + epsLog)
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0) (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hdelta_u : |delta| ≤ fp.u)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x))
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  exact
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_radius_bound
      fp hepsLog hlog hlogHat hposLog hvalid3 hx0 hyhat0 hx_radius hdelta_u
      (expm1Algorithm2_exp_x_combined_radius_le_third_of_exp_mul_one_add_u_le
        fp hsmall)
/-- Finite-normal rounded-exp/log version of the source-shaped Algorithm 2
`3.5u` bridge.  The rounded exponential supplies `|delta| <= u`, and the
rounded logarithm supplies the log relative-error witness and positivity
contract, so the only remaining analytic side conditions are the source
small-`x` radius and nonzero branch facts. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0)
    (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1LogRatio (Real.exp x))
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  have hdelta_u : |delta| ≤ fp.u :=
    expm1Algorithm2RoundedExp_delta_abs_le_of_finiteNormalRange
      fp fmt hu hxnormal hyhatRound
  rcases
    expm1Algorithm2RoundedLog_exists_contract_of_finiteNormalRange
      fp fmt hu hunit_lt_one hlognormal hlogRound with
    ⟨epsLog, hepsLog, hlog, hlogHat, hposLog⟩
  exact
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_x_mul_one_add_u_bound
      (fp := fp) (x := x) (delta := delta) (logHat := logHat)
      (epsLog := epsLog) (X := X)
      hepsLog hlog hlogHat hposLog hvalid3 hx0 hyhat0 hx_radius
      hdelta_u hsmall
/-- Source-function form of the finite-normal rounded-exp/log Algorithm 2
`3.5u` bridge.  This rewrites the exact comparison target from
`g(exp x)` to the Chapter 1 function `(exp x - 1) / x`. -/
theorem
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal_algorithm1Exact
    (fp : FPModel) (fmt : FloatingPointFormat) {x delta logHat X : ℝ}
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hunit_lt_one : fmt.unitRoundoff < 1)
    (hxnormal : fmt.finiteNormalRange (Real.exp x))
    (hlognormal :
      fmt.finiteNormalRange (Real.log (Real.exp x * (1 + delta))))
    (hyhatRound : Real.exp x * (1 + delta) = fmt.finiteRoundToEven (Real.exp x))
    (hlogRound :
      logHat = fmt.finiteRoundToEven
        (Real.log (Real.exp x * (1 + delta))))
    (hvalid3 : gammaValid fp 3)
    (hx0 : x ≠ 0)
    (hyhat0 : Real.exp x * (1 + delta) ≠ 1)
    (hx_radius : |x| ≤ X)
    (hsmall : Real.exp X * (1 + fp.u) ≤ (4 / 3 : ℝ)) :
    relError
        (expm1Algorithm2RoundedCore fp (Real.exp x * (1 + delta)) logHat)
        (expm1Algorithm1Exact x)
      ≤ (7 / 2 : ℝ) * fp.u +
        (((3 : ℝ) * fp.u) ^ 2) / (1 - (3 : ℝ) * fp.u) +
        (fp.u / 2) * gamma fp 3 +
        (2 * (6 * ((Real.exp X - 1) +
          (1 + (Real.exp X - 1)) * fp.u) ^ 2 +
          (((Real.exp X - 1) + (1 + (Real.exp X - 1)) * fp.u) / 2 +
            3 * ((Real.exp X - 1) +
              (1 + (Real.exp X - 1)) * fp.u) ^ 2) * fp.u / 2)) *
          (1 + gamma fp 3) := by
  have hbase :=
    expm1Algorithm2RoundedCore_relError_le_three_point_five_u_plus_exp_log_finiteNormal
      (fp := fp) (fmt := fmt) (x := x) (delta := delta)
      (logHat := logHat) (X := X)
      hu hunit_lt_one hxnormal hlognormal hyhatRound hlogRound hvalid3
      hx0 hyhat0 hx_radius hsmall
  simpa [expm1LogRatio_exp_eq_algorithm1Exact_of_ne_zero hx0] using hbase
private noncomputable def expm1Algorithm2ThreePointFiveUnitBoundScalarCore
    (u : ℝ) : ℝ :=
  (7 / 2 : ℝ) +
    ((9 : ℝ) * u) / (1 - (3 : ℝ) * u) +
    expm1Algorithm2Gamma3Scalar u / 2 +
    (((25 / 2 : ℝ) * u + 3 * u ^ 2) *
      (1 + expm1Algorithm2Gamma3Scalar u))
private theorem expm1Algorithm2ThreePointFiveUnitBoundScalar_eq_mul_core
    (u : ℝ) :
    expm1Algorithm2ThreePointFiveUnitBoundScalar u =
      u * expm1Algorithm2ThreePointFiveUnitBoundScalarCore u := by
  simp [expm1Algorithm2ThreePointFiveUnitBoundScalar,
    expm1Algorithm2ThreePointFiveUnitBoundScalarCore,
    expm1Algorithm2Gamma3Scalar, div_eq_mul_inv]
  ring
private theorem expm1Algorithm2Gamma3Scalar_continuousAt_zero :
    ContinuousAt expm1Algorithm2Gamma3Scalar 0 := by
  unfold expm1Algorithm2Gamma3Scalar
  have hlin : ContinuousAt (fun u : ℝ => 1 - (3 : ℝ) * u) 0 := by
    exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  simpa [div_eq_mul_inv] using
    ((continuousAt_const.mul continuousAt_id).mul (hlin.inv₀ (by norm_num)))
private theorem expm1Algorithm2ThreePointFiveUnitBoundScalarCore_continuousAt_zero :
    ContinuousAt expm1Algorithm2ThreePointFiveUnitBoundScalarCore 0 := by
  have hden : ContinuousAt (fun u : ℝ => 1 - (3 : ℝ) * u) 0 := by
    exact continuousAt_const.sub (continuousAt_const.mul continuousAt_id)
  have hinv : ContinuousAt (fun u : ℝ => (1 - (3 : ℝ) * u)⁻¹) 0 :=
    hden.inv₀ (by norm_num)
  have hterm2 :
      ContinuousAt (fun u : ℝ => ((9 : ℝ) * u) / (1 - (3 : ℝ) * u)) 0 := by
    simpa [div_eq_mul_inv] using
      ((continuousAt_const.mul continuousAt_id).mul hinv)
  have hterm3 :
      ContinuousAt (fun u : ℝ => expm1Algorithm2Gamma3Scalar u / 2) 0 := by
    simpa [div_eq_mul_inv] using
      (expm1Algorithm2Gamma3Scalar_continuousAt_zero.mul continuousAt_const)
  have hpoly :
      ContinuousAt (fun u : ℝ => (25 / 2 : ℝ) * u + 3 * u ^ 2) 0 := by
    have hsq : ContinuousAt (fun u : ℝ => u ^ 2) 0 := by
      simpa [pow_two] using (continuousAt_id.mul continuousAt_id :
        ContinuousAt (fun u : ℝ => u * u) 0)
    exact (continuousAt_const.mul continuousAt_id).add
      (continuousAt_const.mul hsq)
  have honePlus :
      ContinuousAt (fun u : ℝ => 1 + expm1Algorithm2Gamma3Scalar u) 0 :=
    continuousAt_const.add expm1Algorithm2Gamma3Scalar_continuousAt_zero
  have hterm4 :
      ContinuousAt
        (fun u : ℝ => ((25 / 2 : ℝ) * u + 3 * u ^ 2) *
          (1 + expm1Algorithm2Gamma3Scalar u)) 0 :=
    hpoly.mul honePlus
  exact ((continuousAt_const.add hterm2).add hterm3).add hterm4
/-- Literal Landau form of the local Algorithm 2 bound: the named scalar
envelope behind the source's `3.5u` estimate is `O(u)` as `u -> 0`. This is an
interpretation theorem for the local envelope, not a concrete exp/log routine
instantiation. -/
theorem expm1Algorithm2ThreePointFiveUnitBoundScalar_isBigO :
    (fun u : ℝ => expm1Algorithm2ThreePointFiveUnitBoundScalar u)
      =O[𝓝 0] (fun u : ℝ => u) := by
  have hId : (fun u : ℝ => u) =O[𝓝 0] (fun u : ℝ => u) :=
    Asymptotics.isBigO_refl (fun u : ℝ => u) (𝓝 0)
  have hCore :
      (fun u : ℝ => expm1Algorithm2ThreePointFiveUnitBoundScalarCore u)
        =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    expm1Algorithm2ThreePointFiveUnitBoundScalarCore_continuousAt_zero.tendsto.isBigO_one ℝ
  have hMul :
      (fun u : ℝ => u * expm1Algorithm2ThreePointFiveUnitBoundScalarCore u)
        =O[𝓝 0] (fun u : ℝ => u) := by
    simpa using hId.mul hCore
  exact hMul.congr_left
    (fun u => (expm1Algorithm2ThreePointFiveUnitBoundScalar_eq_mul_core u).symm)

end NumStability
