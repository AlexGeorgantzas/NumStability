-- Algorithms/LogExpProduct.lean

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import NumStability.Analysis.Error
import NumStability.Analysis.Summation.ErrorBounds

namespace NumStability

open scoped BigOperators

/-!
# Log-of-product-of-exponentials summation

This file formalizes Higham, Chapter 4, Problem 4.8:

`S_n = log (prod_i exp x_i)`.

The exact identity is harmless, but the computed method is naturally analyzed
through the relative perturbation of the product and the absolute perturbation
of the final logarithm.  The real `log` stage carries an explicit positivity
hypothesis on the perturbed product; finite overflow/underflow behavior is
outside the abstract real-valued `FPModel`.
-/

/-- Exact log-product expression proposed in Chapter 4, Problem 4.8. -/
noncomputable def logExpProductExact (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  Real.log (∏ i : Fin n, Real.exp (x i))

/-- The exact log-product expression is just the ordinary exact sum. -/
theorem logExpProductExact_eq_sum (n : ℕ) (x : Fin n → ℝ) :
    logExpProductExact n x = ∑ i : Fin n, x i := by
  rw [logExpProductExact, ← Real.exp_sum]
  exact Real.log_exp _

/-- Source-level trace for the `log (prod exp)` summation route.

The elementary `exp`, product, and `log` stages are supplied explicitly because
the repository's `FPModel` records primitive binary arithmetic, not a complete
elementary-function library. -/
structure LogExpProductTrace (n : ℕ) where
  expValues : Fin n → ℝ
  productValue : ℝ
  result : ℝ

/-- Evaluate the `log (prod exp)` route with supplied elementary/product stages. -/
noncomputable def logExpProductTrace
    (n : ℕ) (flExp : ℝ → ℝ) (productStage : (Fin n → ℝ) → ℝ)
    (flLog : ℝ → ℝ) (x : Fin n → ℝ) : LogExpProductTrace n :=
  let expValues : Fin n → ℝ := fun i => flExp (x i)
  let productValue : ℝ := productStage expValues
  { expValues := expValues, productValue := productValue, result := flLog productValue }

/-- The trace stores the rounded exponentials supplied by `flExp`. -/
theorem logExpProductTrace_expValues
    (n : ℕ) (flExp : ℝ → ℝ) (productStage : (Fin n → ℝ) → ℝ)
    (flLog : ℝ → ℝ) (x : Fin n → ℝ) :
    (logExpProductTrace n flExp productStage flLog x).expValues =
      fun i => flExp (x i) := by
  rfl

/-- The trace product is the supplied product stage applied to stored exponentials. -/
theorem logExpProductTrace_productValue
    (n : ℕ) (flExp : ℝ → ℝ) (productStage : (Fin n → ℝ) → ℝ)
    (flLog : ℝ → ℝ) (x : Fin n → ℝ) :
    (logExpProductTrace n flExp productStage flLog x).productValue =
      productStage (fun i => flExp (x i)) := by
  rfl

/-- The returned value is the supplied logarithm stage applied to the trace product. -/
theorem logExpProductTrace_result
    (n : ℕ) (flExp : ℝ → ℝ) (productStage : (Fin n → ℝ) → ℝ)
    (flLog : ℝ → ℝ) (x : Fin n → ℝ) :
    (logExpProductTrace n flExp productStage flLog x).result =
      flLog (productStage (fun i => flExp (x i))) := by
  rfl

/-- If the exponentials have componentwise relative errors bounded by `u` and
the product stage has relative error bounded by `gamma fp (n - 1)`, then the
whole product has a single relative perturbation bounded by
`gamma fp (n + (n - 1))`.

This is the standard-model composition behind Problem 4.8 before the final
`log` is applied. -/
theorem logExpProduct_product_perturbation
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) (δ : Fin n → ℝ)
    (θprod pHat : ℝ)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hp : pHat = (∏ i : Fin n, Real.exp (x i) * (1 + δ i)) * (1 + θprod))
    (hθprod : |θprod| ≤ gamma fp (n - 1))
    (hγ : gammaValid fp (n + (n - 1))) :
    ∃ θ, |θ| ≤ gamma fp (n + (n - 1)) ∧
      pHat = Real.exp (∑ i : Fin n, x i) * (1 + θ) := by
  have hγn : gammaValid fp n :=
    gammaValid_mono fp (Nat.le_add_right n (n - 1)) hγ
  obtain ⟨θexp, hθexp, hδprod⟩ := prod_error_bound fp n δ hδ hγn
  obtain ⟨θ, hθ, hcombine⟩ :=
    gamma_mul fp n (n - 1) θexp θprod hθexp hθprod hγ
  refine ⟨θ, hθ, ?_⟩
  calc
    pHat = (∏ i : Fin n, Real.exp (x i) * (1 + δ i)) * (1 + θprod) := hp
    _ = ((∏ i : Fin n, Real.exp (x i)) * (∏ i : Fin n, (1 + δ i))) *
          (1 + θprod) := by
        rw [Finset.prod_mul_distrib]
    _ = (Real.exp (∑ i : Fin n, x i) * (1 + θexp)) * (1 + θprod) := by
        rw [← Real.exp_sum, hδprod]
    _ = Real.exp (∑ i : Fin n, x i) * ((1 + θexp) * (1 + θprod)) := by
        ring
    _ = Real.exp (∑ i : Fin n, x i) * (1 + θ) := by
        rw [hcombine]

/-- Once the product entering the logarithm has relative perturbation `θ`, a
final logarithm perturbation `η` gives the exact error formula
`log(1+θ)+η`. -/
theorem logExpProduct_final_error_eq
    {n : ℕ} (x : Fin n → ℝ) (θ η pHat result : ℝ)
    (hθpos : 0 < 1 + θ)
    (hp : pHat = Real.exp (∑ i : Fin n, x i) * (1 + θ))
    (hlog : result = Real.log pHat + η) :
    result - ∑ i : Fin n, x i = Real.log (1 + θ) + η := by
  let S : ℝ := ∑ i : Fin n, x i
  have hp' : pHat = Real.exp S * (1 + θ) := hp
  subst result
  subst pHat
  rw [Real.log_mul (Real.exp_pos S).ne' (ne_of_gt hθpos)]
  rw [Real.log_exp]
  ring

/-- Absolute-error form of the final `log (prod exp)` perturbation formula. -/
theorem logExpProduct_final_abs_error_eq
    {n : ℕ} (x : Fin n → ℝ) (θ η pHat result : ℝ)
    (hθpos : 0 < 1 + θ)
    (hp : pHat = Real.exp (∑ i : Fin n, x i) * (1 + θ))
    (hlog : result = Real.log pHat + η) :
    |result - ∑ i : Fin n, x i| = |Real.log (1 + θ) + η| := by
  rw [logExpProduct_final_error_eq x θ η pHat result hθpos hp hlog]

/-- Relative-error form of the final perturbation formula.  As usual for
`relError`, this is meaningful when the exact sum is nonzero; the displayed
denominator is the source of the method's loss of relative accuracy when the
sum is small. -/
theorem logExpProduct_final_relError_eq
    {n : ℕ} (x : Fin n → ℝ) (θ η pHat result : ℝ)
    (_hS : relErrorDefined (∑ i : Fin n, x i))
    (hθpos : 0 < 1 + θ)
    (hp : pHat = Real.exp (∑ i : Fin n, x i) * (1 + θ))
    (hlog : result = Real.log pHat + η) :
    relError result (∑ i : Fin n, x i) =
      |Real.log (1 + θ) + η| / |∑ i : Fin n, x i| := by
  rw [relError, logExpProduct_final_abs_error_eq x θ η pHat result hθpos hp hlog]

/-- Combined composition theorem for Problem 4.8.

The conclusion returns the combined product perturbation.  When that
perturbation keeps the logarithm input positive, the final error is exactly
`log(1+θ)+η`. -/
theorem logExpProduct_composed_error
    (fp : FPModel) {n : ℕ} (x : Fin n → ℝ) (δ : Fin n → ℝ)
    (θprod η pHat result : ℝ)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hp : pHat = (∏ i : Fin n, Real.exp (x i) * (1 + δ i)) * (1 + θprod))
    (hθprod : |θprod| ≤ gamma fp (n - 1))
    (hγ : gammaValid fp (n + (n - 1)))
    (hlog : result = Real.log pHat + η) :
    ∃ θ, |θ| ≤ gamma fp (n + (n - 1)) ∧
      pHat = Real.exp (∑ i : Fin n, x i) * (1 + θ) ∧
        (0 < 1 + θ →
          result - ∑ i : Fin n, x i = Real.log (1 + θ) + η) := by
  obtain ⟨θ, hθ, hpθ⟩ :=
    logExpProduct_product_perturbation fp x δ θprod pHat hδ hp hθprod hγ
  refine ⟨θ, hθ, hpθ, ?_⟩
  intro hθpos
  exact logExpProduct_final_error_eq x θ η pHat result hθpos hpθ hlog

end NumStability
