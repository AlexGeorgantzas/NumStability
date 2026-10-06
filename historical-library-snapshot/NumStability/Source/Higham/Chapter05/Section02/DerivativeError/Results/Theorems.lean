-- NumStability/Source/Higham/Chapter05/Section02/DerivativeError/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.Ch5DerivativeError`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds
import NumStability.Source.Higham.Chapter05.Section02.DerivativeError.Basic

/-!
# Theorems

Relocated from `NumStability.Algorithms.Ch5DerivativeError` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# Ch5DerivativeError (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch5DerivativeError`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- Higham (5.7), first-derivative component.  The rounded Algorithm 5.2
derivative output differs from the exact derivative `p'(x)` by at most
`gamma_(2n) * p~'(|x|)`, keeping the value and derivative recurrences coupled so
that every coefficient perturbation stays inside a single `gamma_(2n)`
envelope. -/
theorem ch5deriv_derivative_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 - polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) * polyDescDerivAbs x coeffsDesc :=
  fl_hornerDerivativeDesc_snd_forward_error_bound_coupled fp x coeffsDesc hvalid

/-- Higham (5.7), coefficientwise backward-error form for the first derivative.
The rounded Algorithm 5.2 derivative output is the exact formal derivative of a
polynomial whose coefficients are each perturbed by a relative factor of size at
most `gamma_(2n)`. -/
theorem ch5deriv_derivative_backward_error_coefficients
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    ∃ pairs : List (ℝ × ℝ),
      pairs.map Prod.fst = coeffsDesc ∧
      (∀ p ∈ pairs, |p.2| ≤ gamma fp (2 * (coeffsDesc.length - 1))) ∧
      (fl_hornerDerivativeDesc fp x coeffsDesc).2 =
        polyDescPairsDerivPerturbed x pairs :=
  fl_hornerDerivativeDesc_snd_backward_error_coefficients_coupled
    fp x coeffsDesc hvalid

/-- Full Algorithm 5.2 (value and first derivative) forward-error theorem: both
outputs of the coupled rounded extended-Horner recurrence are simultaneously
bounded by their respective `gamma_(2n)` absolute-coefficient majorants.  This
is the packaged printed-strength statement of the §5.2 rounding analysis. -/
theorem ch5deriv_pair_forward_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).1 - polyDesc x coeffsDesc| ≤
        gamma fp (2 * (coeffsDesc.length - 1)) * polyDescAbs x coeffsDesc ∧
      |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
          polyDescDeriv x coeffsDesc| ≤
        gamma fp (2 * (coeffsDesc.length - 1)) *
          polyDescDerivAbs x coeffsDesc :=
  ⟨ch5deriv_value_forward_error_bound fp x coeffsDesc hvalid,
    ch5deriv_derivative_forward_error_bound fp x coeffsDesc hvalid⟩

/-- Higham (5.7), first-order display of the derivative bound.  The leading
term is the printed `2 n u * p~'(|x|)`; the explicit quadratic-and-higher
remainder is `((2 n u)^2 / (1 - 2 n u)) * p~'(|x|)` and vanishes when `u = 0`. -/
theorem ch5deriv_derivative_first_order_error_bound
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 - polyDescDeriv x coeffsDesc| ≤
      (((2 * (coeffsDesc.length - 1) : ℕ) : ℝ) * fp.u) *
          polyDescDerivAbs x coeffsDesc +
        fl_hornerDerivativeDescFirstOrderRemainder fp x coeffsDesc :=
  fl_hornerDerivativeDesc_first_derivative_error_bound fp x coeffsDesc hvalid

end NumStability
