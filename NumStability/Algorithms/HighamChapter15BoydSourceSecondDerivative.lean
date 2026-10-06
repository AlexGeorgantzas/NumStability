-- Algorithms/HighamChapter15BoydSourceSecondDerivative.lean
--
-- The constrained second variation used in Boyd's local convergence proof is
-- an actual second derivative on the exact composition domain of the literal
-- rectangular update.  In the nonsmooth range, a vanishing coordinate of
-- `A x` is allowed only when the corresponding row of `A` is identically
-- zero; that row then contributes the constant-zero function.

import NumStability.Algorithms.HighamChapter15BoydRowwiseDomain

namespace NumStability.Ch15

open Filter Function Set
open scoped BigOperators Topology

private theorem hasDerivAt_gradientFactor_affine_of_two_le
    {p a b : ℝ} (hp2 : 2 ≤ p) :
    HasDerivAt
      (fun t : ℝ => b * (|a + t * b| ^ (p - 2) * (a + t * b)))
      (b * ((p - 1) * |a| ^ (p - 2) * b)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul b)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfactor : HasDerivAt (fun u : ℝ => |u| ^ (p - 2) * u)
      ((p - 1) * |a| ^ (p - 2)) (a + 0 * b) := by
    simpa using hasDerivAt_abs_rpow_sub_two_mul_self_of_two_le p a hp2
  have hbase := hfactor.comp 0 hline
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    hbase.const_mul b

private theorem hasDerivAt_gradientFactor_affine_of_ne
    {p a b : ℝ} (ha : a ≠ 0) :
    HasDerivAt
      (fun t : ℝ => b * (|a + t * b| ^ (p - 2) * (a + t * b)))
      (b * ((p - 1) * |a| ^ (p - 2) * b)) 0 := by
  have hline : HasDerivAt (fun t : ℝ => a + t * b) b 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) a).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul b)
    convert h using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfactor : HasDerivAt (fun u : ℝ => |u| ^ (p - 2) * u)
      ((p - 1) * |a| ^ (p - 2)) (a + 0 * b) := by
    simpa using hasDerivAt_abs_rpow_sub_two_mul_self p a ha
  have hbase := hfactor.comp 0 hline
  simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using
    hbase.const_mul b

/-- The literal first-derivative formula has the advertised derivative on
the exact rowwise source domain.  This includes both kinds of formerly
missing zero coordinate: arbitrary zero coordinates when `2 ≤ p`, and
constant zero rows when `1 < p < 2`. -/
theorem boydConstrainedLagrangianFirst_hasDerivAt_rowwise_source_domain
    {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x) :
    HasDerivAt (boydConstrainedLagrangianFirst p A x h)
      (boydConstrainedSecondVariation p A x h) 0 := by
  have hN : HasDerivAt
      (fun t : ℝ => ∑ i : Fin m, p *
        boydRectActionCLM A h i *
          (|boydRectActionCLM A x i + t * boydRectActionCLM A h i| ^ (p - 2) *
            (boydRectActionCLM A x i + t * boydRectActionCLM A h i)))
      (∑ i : Fin m, p * (p - 1) *
        |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i * boydRectActionCLM A h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    rcases hsmooth with hp2 | hrowwise
    · have hi := (hasDerivAt_gradientFactor_affine_of_two_le
        (p := p) (a := boydRectActionCLM A x i)
        (b := boydRectActionCLM A h i) hp2).const_mul p
      convert hi using 1 <;> ring_nf
    · rcases hrowwise i with hi | hzero
      · have hderiv := (hasDerivAt_gradientFactor_affine_of_ne
          (p := p) (a := boydRectActionCLM A x i)
          (b := boydRectActionCLM A h i) hi).const_mul p
        convert hderiv using 1 <;> ring_nf
      · have hxzero : boydRectActionCLM A x i = 0 :=
          boydRectActionCLM_apply_eq_zero_of_row_zero A x i hzero
        have hhzero : boydRectActionCLM A h i = 0 :=
          boydRectActionCLM_apply_eq_zero_of_row_zero A h i hzero
        simpa [hxzero, hhzero] using
          (hasDerivAt_const (x := (0 : ℝ)) (0 : ℝ))
  have hD : HasDerivAt
      (fun t : ℝ => ∑ j : Fin n, p *
        h j * (|x j + t * h j| ^ (p - 2) * (x j + t * h j)))
      (∑ j : Fin n, p * (p - 1) * |x j| ^ (p - 2) * h j * h j) 0 := by
    apply HasDerivAt.fun_sum
    intro j _
    have hj := (hasDerivAt_gradientFactor_affine_of_ne
      (p := p) (a := x j) (b := h j) (hxcoord j)).const_mul p
    convert hj using 1 <;> ring_nf
  have htot := hN.sub (hD.const_mul
    (realLpPowerSum p (boydRectActionCLM A x)))
  convert htot using 1
  unfold boydConstrainedSecondVariation boydWeightedPair
  have hout : (∑ i : Fin m, p * (p - 1) *
      |boydRectActionCLM A x i| ^ (p - 2) *
      boydRectActionCLM A h i * boydRectActionCLM A h i) =
      p * (p - 1) * ∑ i : Fin m,
        |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i * boydRectActionCLM A h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hin : (∑ j : Fin n,
      p * (p - 1) * |x j| ^ (p - 2) * h j * h j) =
      p * (p - 1) * ∑ j : Fin n, |x j| ^ (p - 2) * h j * h j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hout, hin]
  ring

/-- Source-facing second-derivative certificate on every case admitted by
`IsBoydInnerRowwiseSmoothDomain`.  No derivative identity is assumed. -/
theorem boydConstrainedSecondVariation_is_second_derivative_rowwise_source_domain
    {m n : ℕ} {p : ℝ} (hp : 1 < p)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x) :
    HasDerivAt (boydConstrainedLagrangianLine p A x h)
        (boydConstrainedLagrangianFirst p A x h 0) 0 ∧
      HasDerivAt (boydConstrainedLagrangianFirst p A x h)
        (boydConstrainedSecondVariation p A x h) 0 :=
  ⟨boydConstrainedLagrangianLine_hasDerivAt hp A x h,
    boydConstrainedLagrangianFirst_hasDerivAt_rowwise_source_domain
      A x h hxcoord hsmooth⟩

end NumStability.Ch15
