-- Algorithms/AitkenDenominator.lean
--
-- Higham Chapter 4, Problem 4.7.

import Mathlib.Tactic
import NumStability.Analysis.Rounding

namespace NumStability

/-!
# Aitken Denominator Evaluation

Higham Chapter 4, Problem 4.7 asks which algebraically equivalent expression
should be used to evaluate the denominator

`x_{i+2} - 2*x_{i+1} + x_i`

in Aitken's `Delta^2` method.  The formal comparison below isolates the
parenthesization issue by treating multiplication by `2` as exact.  This is
the source-level comparison: if a concrete machine model rounds the scaling by
`2`, that rounded scaling is an additional finite-format side condition for
the routes that explicitly contain `2*x_{i+1}`.

The recommended route is expression (b),

`(x_{i+2} - x_{i+1}) - (x_{i+1} - x_i)`,

because its standard-model absolute-error majorant depends on the successive
differences rather than on the nearly common limiting offset.
-/

/-- Aitken denominator in the source expression (a):
`(x₂ - 2*x₁) + x₀`. -/
noncomputable def aitkenDenominatorA (x0 x1 x2 : ℝ) : ℝ :=
  (x2 - 2 * x1) + x0

/-- Aitken denominator in the source expression (b):
`(x₂ - x₁) - (x₁ - x₀)`. -/
noncomputable def aitkenDenominatorB (x0 x1 x2 : ℝ) : ℝ :=
  (x2 - x1) - (x1 - x0)

/-- Aitken denominator in the source expression (c):
`(x₂ + x₀) - 2*x₁`. -/
noncomputable def aitkenDenominatorC (x0 x1 x2 : ℝ) : ℝ :=
  (x2 + x0) - 2 * x1

/-- Exact route (a) equals route (b). -/
theorem aitkenDenominatorA_eq_B (x0 x1 x2 : ℝ) :
    aitkenDenominatorA x0 x1 x2 = aitkenDenominatorB x0 x1 x2 := by
  simp [aitkenDenominatorA, aitkenDenominatorB]
  ring

/-- Exact route (c) equals route (b). -/
theorem aitkenDenominatorC_eq_B (x0 x1 x2 : ℝ) :
    aitkenDenominatorC x0 x1 x2 = aitkenDenominatorB x0 x1 x2 := by
  simp [aitkenDenominatorB, aitkenDenominatorC]
  ring

/-- Rounded route (a), with exact scaling by `2`. -/
noncomputable def fl_aitkenDenominatorA (fp : FPModel)
    (x0 x1 x2 : ℝ) : ℝ :=
  fp.fl_add (fp.fl_sub x2 (2 * x1)) x0

/-- Rounded route (b), the recommended first-difference form. -/
noncomputable def fl_aitkenDenominatorB (fp : FPModel)
    (x0 x1 x2 : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_sub x2 x1) (fp.fl_sub x1 x0)

/-- Rounded route (c), with exact scaling by `2`. -/
noncomputable def fl_aitkenDenominatorC (fp : FPModel)
    (x0 x1 x2 : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_add x2 x0) (2 * x1)

/-- Error majorant for rounded route (a). -/
noncomputable def aitkenDenominatorAMajorant (x0 x1 x2 : ℝ) : ℝ :=
  |x2 - 2 * x1| + |x0|

/-- Error majorant for rounded route (b): only successive differences appear. -/
noncomputable def aitkenDenominatorBMajorant (x0 x1 x2 : ℝ) : ℝ :=
  |x2 - x1| + |x1 - x0|

/-- Error majorant for rounded route (c). -/
noncomputable def aitkenDenominatorCMajorant (x0 x1 x2 : ℝ) : ℝ :=
  |x2 + x0| + |2 * x1|

/-- Route (b)'s majorant is invariant under adding a common offset.  This is
the formal cancellation-aware reason for using first differences near a
convergent limit. -/
theorem aitkenDenominatorBMajorant_add_const
    (alpha x0 x1 x2 : ℝ) :
    aitkenDenominatorBMajorant (alpha + x0) (alpha + x1) (alpha + x2) =
      aitkenDenominatorBMajorant x0 x1 x2 := by
  simp [aitkenDenominatorBMajorant]

/-- Route (a)'s majorant after adding a common offset; unlike route (b), it
retains the offset. -/
theorem aitkenDenominatorAMajorant_add_const
    (alpha x0 x1 x2 : ℝ) :
    aitkenDenominatorAMajorant (alpha + x0) (alpha + x1) (alpha + x2) =
      |x2 - 2 * x1 - alpha| + |alpha + x0| := by
  simp [aitkenDenominatorAMajorant]
  ring_nf

/-- Route (c)'s majorant after adding a common offset; unlike route (b), it
retains the offset. -/
theorem aitkenDenominatorCMajorant_add_const
    (alpha x0 x1 x2 : ℝ) :
    aitkenDenominatorCMajorant (alpha + x0) (alpha + x1) (alpha + x2) =
      |2 * alpha + (x2 + x0)| + |2 * (alpha + x1)| := by
  simp [aitkenDenominatorCMajorant]
  ring_nf

/-- Route (a) perturbs the intermediate expression `x₂ - 2*x₁` and the final
addend `x₀`. -/
theorem fl_aitkenDenominatorA_backward_error (fp : FPModel)
    (hγ : gammaValid fp 2) (x0 x1 x2 : ℝ) :
    ∃ θ ψ : ℝ,
      |θ| ≤ gamma fp 2 ∧
      |ψ| ≤ gamma fp 2 ∧
        fl_aitkenDenominatorA fp x0 x1 x2 =
          (x2 - 2 * x1) * (1 + θ) + x0 * (1 + ψ) := by
  obtain ⟨δsub, hδsub, hsub⟩ := fp.model_sub x2 (2 * x1)
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (fp.fl_sub x2 (2 * x1)) x0
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδsubγ1 : |δsub| ≤ gamma fp 1 :=
    le_trans hδsub (u_le_gamma fp (by norm_num) hγ1)
  have hδaddγ1 : |δadd| ≤ gamma fp 1 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ1)
  have hδaddγ2 : |δadd| ≤ gamma fp 2 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul fp 1 1 δsub δadd hδsubγ1 hδaddγ1 hγ
  refine ⟨θ, δadd, hθ, hδaddγ2, ?_⟩
  calc
    fl_aitkenDenominatorA fp x0 x1 x2
        = ((x2 - 2 * x1) * (1 + δsub) + x0) * (1 + δadd) := by
            rw [fl_aitkenDenominatorA, hadd, hsub]
    _ = (x2 - 2 * x1) * ((1 + δsub) * (1 + δadd)) +
          x0 * (1 + δadd) := by ring
    _ = (x2 - 2 * x1) * (1 + θ) + x0 * (1 + δadd) := by
            rw [hθeq]

/-- Route (a)'s absolute-error bound. -/
theorem fl_aitkenDenominatorA_error_bound (fp : FPModel)
    (hγ : gammaValid fp 2) (x0 x1 x2 : ℝ) :
    |fl_aitkenDenominatorA fp x0 x1 x2 -
        aitkenDenominatorB x0 x1 x2| ≤
      gamma fp 2 * aitkenDenominatorAMajorant x0 x1 x2 := by
  obtain ⟨θ, ψ, hθ, hψ, hfl⟩ :=
    fl_aitkenDenominatorA_backward_error fp hγ x0 x1 x2
  have h1 : |(x2 - 2 * x1) * θ| ≤
      |x2 - 2 * x1| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hθ (abs_nonneg (x2 - 2 * x1))
  have h2 : |x0 * ψ| ≤ |x0| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hψ (abs_nonneg x0)
  calc
    |fl_aitkenDenominatorA fp x0 x1 x2 -
        aitkenDenominatorB x0 x1 x2|
        = |(x2 - 2 * x1) * θ + x0 * ψ| := by
            rw [hfl]
            simp [aitkenDenominatorB]
            ring_nf
    _ ≤ |(x2 - 2 * x1) * θ| + |x0 * ψ| := abs_add_le _ _
    _ ≤ |x2 - 2 * x1| * gamma fp 2 + |x0| * gamma fp 2 :=
        add_le_add h1 h2
    _ = gamma fp 2 * aitkenDenominatorAMajorant x0 x1 x2 := by
        simp [aitkenDenominatorAMajorant]
        ring

/-- Route (b) perturbs only the two successive first differences. -/
theorem fl_aitkenDenominatorB_backward_error (fp : FPModel)
    (hγ : gammaValid fp 2) (x0 x1 x2 : ℝ) :
    ∃ θ η : ℝ,
      |θ| ≤ gamma fp 2 ∧
      |η| ≤ gamma fp 2 ∧
        fl_aitkenDenominatorB fp x0 x1 x2 =
          (x2 - x1) * (1 + θ) - (x1 - x0) * (1 + η) := by
  obtain ⟨δhi, hδhi, hhi⟩ := fp.model_sub x2 x1
  obtain ⟨δlo, hδlo, hlo⟩ := fp.model_sub x1 x0
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_sub x2 x1) (fp.fl_sub x1 x0)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδhiγ1 : |δhi| ≤ gamma fp 1 :=
    le_trans hδhi (u_le_gamma fp (by norm_num) hγ1)
  have hδloγ1 : |δlo| ≤ gamma fp 1 :=
    le_trans hδlo (u_le_gamma fp (by norm_num) hγ1)
  have hδsubγ1 : |δsub| ≤ gamma fp 1 :=
    le_trans hδsub (u_le_gamma fp (by norm_num) hγ1)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul fp 1 1 δhi δsub hδhiγ1 hδsubγ1 hγ
  obtain ⟨η, hη, hηeq⟩ :=
    gamma_mul fp 1 1 δlo δsub hδloγ1 hδsubγ1 hγ
  refine ⟨θ, η, hθ, hη, ?_⟩
  calc
    fl_aitkenDenominatorB fp x0 x1 x2
        = ((x2 - x1) * (1 + δhi) -
            (x1 - x0) * (1 + δlo)) * (1 + δsub) := by
            rw [fl_aitkenDenominatorB, hsub, hhi, hlo]
    _ = (x2 - x1) * ((1 + δhi) * (1 + δsub)) -
          (x1 - x0) * ((1 + δlo) * (1 + δsub)) := by ring
    _ = (x2 - x1) * (1 + θ) - (x1 - x0) * (1 + η) := by
            rw [hθeq, hηeq]

/-- Route (b)'s absolute-error bound.  This is the source-recommended bound:
only the first differences appear in the majorant. -/
theorem fl_aitkenDenominatorB_error_bound (fp : FPModel)
    (hγ : gammaValid fp 2) (x0 x1 x2 : ℝ) :
    |fl_aitkenDenominatorB fp x0 x1 x2 -
        aitkenDenominatorB x0 x1 x2| ≤
      gamma fp 2 * aitkenDenominatorBMajorant x0 x1 x2 := by
  obtain ⟨θ, η, hθ, hη, hfl⟩ :=
    fl_aitkenDenominatorB_backward_error fp hγ x0 x1 x2
  have h1 : |(x2 - x1) * θ| ≤ |x2 - x1| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hθ (abs_nonneg (x2 - x1))
  have h2 : |(x1 - x0) * η| ≤ |x1 - x0| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hη (abs_nonneg (x1 - x0))
  calc
    |fl_aitkenDenominatorB fp x0 x1 x2 -
        aitkenDenominatorB x0 x1 x2|
        = |(x2 - x1) * θ - (x1 - x0) * η| := by
            rw [hfl]
            simp [aitkenDenominatorB]
            ring_nf
    _ ≤ |(x2 - x1) * θ| + |(x1 - x0) * η| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le ((x2 - x1) * θ) (-((x1 - x0) * η))
    _ ≤ |x2 - x1| * gamma fp 2 + |x1 - x0| * gamma fp 2 :=
        add_le_add h1 h2
    _ = gamma fp 2 * aitkenDenominatorBMajorant x0 x1 x2 := by
        simp [aitkenDenominatorBMajorant]
        ring

/-- Route (c) perturbs the large sum `x₂ + x₀` and the middle term `2*x₁`. -/
theorem fl_aitkenDenominatorC_backward_error (fp : FPModel)
    (hγ : gammaValid fp 2) (x0 x1 x2 : ℝ) :
    ∃ θ ψ : ℝ,
      |θ| ≤ gamma fp 2 ∧
      |ψ| ≤ gamma fp 2 ∧
        fl_aitkenDenominatorC fp x0 x1 x2 =
          (x2 + x0) * (1 + θ) - (2 * x1) * (1 + ψ) := by
  obtain ⟨δadd, hδadd, hadd⟩ := fp.model_add x2 x0
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_add x2 x0) (2 * x1)
  have hγ1 : gammaValid fp 1 := gammaValid_mono fp (by norm_num) hγ
  have hδaddγ1 : |δadd| ≤ gamma fp 1 :=
    le_trans hδadd (u_le_gamma fp (by norm_num) hγ1)
  have hδsubγ1 : |δsub| ≤ gamma fp 1 :=
    le_trans hδsub (u_le_gamma fp (by norm_num) hγ1)
  have hδsubγ2 : |δsub| ≤ gamma fp 2 :=
    le_trans hδsub (u_le_gamma fp (by norm_num) hγ)
  obtain ⟨θ, hθ, hθeq⟩ :=
    gamma_mul fp 1 1 δadd δsub hδaddγ1 hδsubγ1 hγ
  refine ⟨θ, δsub, hθ, hδsubγ2, ?_⟩
  calc
    fl_aitkenDenominatorC fp x0 x1 x2
        = ((x2 + x0) * (1 + δadd) - 2 * x1) * (1 + δsub) := by
            rw [fl_aitkenDenominatorC, hsub, hadd]
    _ = (x2 + x0) * ((1 + δadd) * (1 + δsub)) -
          (2 * x1) * (1 + δsub) := by ring
    _ = (x2 + x0) * (1 + θ) - (2 * x1) * (1 + δsub) := by
            rw [hθeq]

/-- Route (c)'s absolute-error bound. -/
theorem fl_aitkenDenominatorC_error_bound (fp : FPModel)
    (hγ : gammaValid fp 2) (x0 x1 x2 : ℝ) :
    |fl_aitkenDenominatorC fp x0 x1 x2 -
        aitkenDenominatorB x0 x1 x2| ≤
      gamma fp 2 * aitkenDenominatorCMajorant x0 x1 x2 := by
  obtain ⟨θ, ψ, hθ, hψ, hfl⟩ :=
    fl_aitkenDenominatorC_backward_error fp hγ x0 x1 x2
  have h1 : |(x2 + x0) * θ| ≤ |x2 + x0| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hθ (abs_nonneg (x2 + x0))
  have h2 : |(2 * x1) * ψ| ≤ |2 * x1| * gamma fp 2 := by
    simpa [abs_mul] using
      mul_le_mul_of_nonneg_left hψ (abs_nonneg (2 * x1))
  calc
    |fl_aitkenDenominatorC fp x0 x1 x2 -
        aitkenDenominatorB x0 x1 x2|
        = |(x2 + x0) * θ - (2 * x1) * ψ| := by
            rw [hfl]
            simp [aitkenDenominatorB]
            ring_nf
    _ ≤ |(x2 + x0) * θ| + |(2 * x1) * ψ| := by
        simpa [sub_eq_add_neg, abs_neg] using
          abs_add_le ((x2 + x0) * θ) (-((2 * x1) * ψ))
    _ ≤ |x2 + x0| * gamma fp 2 + |2 * x1| * gamma fp 2 :=
        add_le_add h1 h2
    _ = gamma fp 2 * aitkenDenominatorCMajorant x0 x1 x2 := by
        simp [aitkenDenominatorCMajorant]
        ring

/-- Formal answer to Problem 4.7: route (b) is the cancellation-aware
denominator evaluation.  Its proved standard-model error bound is controlled
by a majorant invariant under a common limiting offset, unlike the route (a)
and route (c) majorants displayed above. -/
theorem aitkenDenominator_recommended_route_b (fp : FPModel)
    (hγ : gammaValid fp 2) (alpha x0 x1 x2 : ℝ) :
    |fl_aitkenDenominatorB fp (alpha + x0) (alpha + x1) (alpha + x2) -
        aitkenDenominatorB (alpha + x0) (alpha + x1) (alpha + x2)| ≤
      gamma fp 2 * aitkenDenominatorBMajorant x0 x1 x2 := by
  simpa [aitkenDenominatorBMajorant_add_const] using
    fl_aitkenDenominatorB_error_bound fp hγ
      (alpha + x0) (alpha + x1) (alpha + x2)

end NumStability
