import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Higham Chapter 6: Euclidean-norm differentiability

Source correspondence for the differentiability prose on p. 105. It records
the failure at zero and the corrected real Frechet derivative at nonzero
complex vectors.
-/

namespace NumStability

open scoped RealInnerProductSpace

/-! ### Source correction: differentiability of the Euclidean norm

Higham, Chapter 6, p. 105, says that the `2`-norm is differentiable for all
vectors and gives its gradient as `x / ‖x‖₂`.  The displayed formula itself is
undefined at `x = 0`, and the norm is not differentiable there.  The first
theorem below is a compiled counterexample to the literal universal claim; the
second is the corrected nonzero statement over finite-dimensional complex
Euclidean space, viewed as a real normed space.
-/

/-- **Counterexample to the literal Chapter 6 prose claim.**  The Euclidean
norm on the one-dimensional complex space is not real-differentiable at zero. -/
theorem higham6_euclideanNorm_not_differentiableAt_zero :
    ¬ DifferentiableAt ℝ
      (fun x : EuclideanSpace ℂ (Fin 1) => ‖x‖) 0 :=
  not_differentiableAt_norm_zero _

/-- **Corrected Chapter 6 norm derivative.**  At every nonzero complex vector,
the real Fréchet derivative of `x ↦ ‖x‖₂` is the functional
`h ↦ Re ⟪x,h⟫ / ‖x‖₂`, equivalently the gradient is `x / ‖x‖₂`. -/
theorem higham6_euclideanNorm_hasFDerivAt_of_ne_zero {n : ℕ}
    (x : EuclideanSpace ℂ (Fin n)) (hx : x ≠ 0) :
    HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖)
      ((1 / ‖x‖) • innerSL ℝ x) x := by
  have hsq :
      HasFDerivAt (fun y : EuclideanSpace ℂ (Fin n) => ‖y‖ ^ 2)
        (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hsqrt := hsq.sqrt (by positivity : ‖x‖ ^ 2 ≠ 0)
  convert hsqrt using 1
  · funext y
    rw [Real.sqrt_sq (norm_nonneg y)]
  · rw [Real.sqrt_sq (norm_nonneg x)]
    ext h
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul,
      innerSL_apply_apply]
    field_simp [hxnorm]
    ring

end NumStability
