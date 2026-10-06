-- Algorithms/HighamChapter15BoydSourceLocal.lean
--
-- Source-facing local calculus for Boyd's 1974 nonlinear power method.
-- Boyd's Lemma 2 differentiates the normalized dual update away from the
-- coordinate singularities.  His Lemma 3 then distinguishes ordinary strict
-- relative maxima from *nondegenerate* strict relative maxima: only the latter
-- give a strict linear contraction.  The printed statement of Theorem 3 drops
-- "nondegenerate", although its proof invokes that strict-contraction half of
-- Lemma 3.  This module formalizes the concrete differentiability/linearization
-- part and records that source distinction explicitly.

import NumStability.Algorithms.HighamChapter15BoydLocalStability
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.InnerProductSpace.Rayleigh

namespace NumStability.Ch15

open Filter Function Set
open scoped BigOperators Topology

/-! ## Smoothness of the explicit normalized `l^p` dual -/

/-- The power sum underlying the explicit normalized dual is Frechet
differentiable for every `p > 1`. -/
theorem differentiableAt_realLpPowerSum {n : ℕ} {p : ℝ} (hp : 1 < p)
    (x : Fin n → ℝ) :
    DifferentiableAt ℝ (realLpPowerSum p) x := by
  rw [show realLpPowerSum p = fun y : Fin n → ℝ =>
      ∑ i : Fin n, |y i| ^ p by rfl]
  apply DifferentiableAt.fun_sum
  intro i _hi
  have hcoord : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) i).differentiableAt
  exact (hasDerivAt_abs_rpow (x i) hp).differentiableAt.comp x hcoord

/-- Scalar derivative needed for the Hessian/linearization identity. -/
theorem hasDerivAt_abs_rpow_sub_two_mul_self (p x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => |t| ^ (p - 2) * t)
      ((p - 1) * |x| ^ (p - 2)) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have habs := hasDerivAt_abs_neg hxneg
    have hpow := habs.rpow_const
      (p := p - 2) (Or.inl (abs_ne_zero.mpr hx))
    have h := hpow.mul (hasDerivAt_id x)
    convert h using 1
    have habspos : 0 < |x| := abs_pos.mpr hx
    have hx_eq : x = -|x| := by rw [abs_of_neg hxneg]; ring
    rw [hx_eq]
    have hrpow : |x| ^ (p - 3) * |x| = |x| ^ (p - 2) := by
      rw [← Real.rpow_add_one (ne_of_gt habspos) (p - 3)]
      congr 1
      ring
    simp only [abs_neg, abs_abs, id_eq, neg_one_mul, mul_one]
    rw [show p - 2 - 1 = p - 3 by ring]
    calc
      (p - 1) * |x| ^ (p - 2) =
          (p - 2) * |x| ^ (p - 2) + |x| ^ (p - 2) := by ring
      _ = (p - 2) * (|x| ^ (p - 3) * |x|) + |x| ^ (p - 2) := by
        rw [hrpow]
      _ = -(p - 2) * |x| ^ (p - 3) * -|x| + |x| ^ (p - 2) := by
        ring
  · have habs := hasDerivAt_abs_pos hxpos
    have hpow := habs.rpow_const
      (p := p - 2) (Or.inl (abs_ne_zero.mpr hx))
    have h := hpow.mul (hasDerivAt_id x)
    convert h using 1
    have habspos : 0 < |x| := abs_pos.mpr hx
    have hx_eq : x = |x| := by rw [abs_of_pos hxpos]
    rw [hx_eq]
    have hrpow : |x| ^ (p - 3) * |x| = |x| ^ (p - 2) := by
      rw [← Real.rpow_add_one (ne_of_gt habspos) (p - 3)]
      congr 1
      ring
    simp only [abs_abs, id_eq, one_mul, mul_one]
    rw [show p - 2 - 1 = p - 3 by ring]
    calc
      (p - 1) * |x| ^ (p - 2) =
          (p - 2) * |x| ^ (p - 2) + |x| ^ (p - 2) := by ring
      _ = (p - 2) * (|x| ^ (p - 3) * |x|) + |x| ^ (p - 2) := by
        rw [hrpow]
      _ = (p - 2) * |x| ^ (p - 3) * |x| + |x| ^ (p - 2) := by
        ring

/-- Away from zero coordinates, the componentwise factor
`|x_i|^(p-2) x_i` is differentiable for arbitrary real `p`. -/
theorem differentiableAt_realLpGradientCoordinateFactor {n : ℕ}
    (p : ℝ) (x : Fin n → ℝ) (i : Fin n) (hxi : x i ≠ 0) :
    DifferentiableAt ℝ
      (fun y : Fin n → ℝ => |y i| ^ (p - 2) * y i) x := by
  have hcoord : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) i).differentiableAt
  have habs : DifferentiableAt ℝ (fun y : Fin n → ℝ => |y i|) x := by
    exact (hasDerivAt_abs hxi).differentiableAt.comp x hcoord
  have hpow : DifferentiableAt ℝ
      (fun y : Fin n → ℝ => |y i| ^ (p - 2)) x :=
    habs.rpow_const (Or.inl (abs_ne_zero.mpr hxi))
  exact hpow.mul hcoord

/-- The explicit normalized dual/gradient is Frechet differentiable at every
vector whose coordinates are nonzero.  This is the coordinate domain used in
Boyd's local linearization argument. -/
theorem differentiableAt_realLpGradient_of_all_ne {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x : Fin n → ℝ) (hxcoord : ∀ i, x i ≠ 0) :
    DifferentiableAt ℝ (realLpGradient p) x := by
  by_cases hn : n = 0
  · subst n
    apply differentiableAt_pi''
    intro i
    exact Fin.elim0 i
  have hx : x ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    exact hxcoord i0 (by simpa using congrFun hzero i0)
  have hS : DifferentiableAt ℝ (realLpPowerSum p) x :=
    differentiableAt_realLpPowerSum hp x
  have hSnonzero : realLpPowerSum p x ≠ 0 :=
    ne_of_gt (realLpPowerSum_pos hp hx)
  have hscale : DifferentiableAt ℝ
      (fun y : Fin n → ℝ =>
        (realLpPowerSum p y) ^ (p⁻¹ - 1)) x :=
    hS.rpow_const (Or.inl hSnonzero)
  apply differentiableAt_pi''
  intro i
  change DifferentiableAt ℝ
    (fun y : Fin n → ℝ =>
      (realLpPowerSum p y) ^ (p⁻¹ - 1) *
        (|y i| ^ (p - 2) * y i)) x
  exact hscale.mul
    (differentiableAt_realLpGradientCoordinateFactor p x i (hxcoord i))

/-! ### Explicit action of the gradient derivative -/

/-- Boyd's weighted bilinear form `[g,h]_x`. -/
noncomputable def boydWeightedPair {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, |x i| ^ (p - 2) * g i * h i

/-- Explicit directional derivative of the normalized `l^p` gradient. -/
noncomputable def realLpGradientDirectional {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    (1 - p) * (realLpPowerSum p x) ^ (p⁻¹ - 2) *
        boydWeightedPair p x x h * (|x i| ^ (p - 2) * x i) +
      (p - 1) * (realLpPowerSum p x) ^ (p⁻¹ - 1) *
        |x i| ^ (p - 2) * h i

/-- Directional version of Boyd's normalized-dual differential. -/
theorem realLpGradient_line_hasDerivAt {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x h : Fin n → ℝ) (hx : x ≠ 0)
    (hxcoord : ∀ i, x i ≠ 0) :
    HasDerivAt (fun t : ℝ => realLpGradient p (fun i => x i + t * h i))
      (realLpGradientDirectional p x h) 0 := by
  let S : ℝ := realLpPowerSum p x
  let D : ℝ := boydWeightedPair p x x h
  have hsum : HasDerivAt
      (fun t : ℝ => realLpPowerSum p (fun i => x i + t * h i))
      (p * D) 0 := by
    unfold realLpPowerSum
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        HasDerivAt (fun t : ℝ => |x i + t * h i| ^ p)
          (p * |x i| ^ (p - 2) * x i * h i) 0 := by
      intro i _hi
      have hline : HasDerivAt (fun t : ℝ => x i + t * h i) (h i) 0 := by
        have hline' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
          ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
        convert hline' using 1
        · funext t
          simp only [Pi.add_apply, id_eq]
          ring
        · ring
      have hbase : HasDerivAt (fun u : ℝ => |u| ^ p)
          (p * |x i| ^ (p - 2) * x i) (x i + 0 * h i) := by
        simpa using hasDerivAt_abs_rpow (x i) hp
      convert hbase.comp 0 hline using 1
    convert HasDerivAt.fun_sum hterms using 1
    unfold D boydWeightedPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hSpos : 0 < S := realLpPowerSum_pos hp hx
  have hscale := hsum.rpow_const
    (p := p⁻¹ - 1) (Or.inl (by simpa [S] using ne_of_gt hSpos))
  apply hasDerivAt_pi.2
  intro i
  have hline : HasDerivAt (fun t : ℝ => x i + t * h i) (h i) 0 := by
    have hline' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hbase : HasDerivAt (fun t : ℝ => |t| ^ (p - 2) * t)
      ((p - 1) * |x i| ^ (p - 2)) (x i + 0 * h i) := by
    simpa using hasDerivAt_abs_rpow_sub_two_mul_self p (x i) (hxcoord i)
  have hcoord := hbase.comp 0 hline
  have hprod := hscale.mul hcoord
  convert hprod using 1
  unfold realLpGradientDirectional
  simp only [Function.comp_apply, zero_mul, add_zero]
  unfold D
  field_simp [ne_of_gt (zero_lt_one.trans hp)]
  ring

/-- The Frechet derivative acts by the preceding explicit formula. -/
theorem fderiv_realLpGradient_apply {n : ℕ} {p : ℝ}
    (hp : 1 < p) (x h : Fin n → ℝ)
    (hxcoord : ∀ i, x i ≠ 0) :
    fderiv ℝ (realLpGradient p) x h =
      realLpGradientDirectional p x h := by
  by_cases hn : n = 0
  · subst n
    funext i
    exact Fin.elim0 i
  have hx : x ≠ 0 := by
    intro hzero
    let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
    exact hxcoord i0 (by simpa using congrFun hzero i0)
  have hf := (differentiableAt_realLpGradient_of_all_ne hp x hxcoord).hasFDerivAt
  have hline : HasDerivAt (fun t : ℝ => (fun i => x i + t * h i)) h 0 := by
    apply hasDerivAt_pi.2
    intro i
    have hline' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfbase : HasFDerivAt (realLpGradient p)
      (fderiv ℝ (realLpGradient p) x) (fun i => x i + 0 * h i) := by
    simpa using hf
  have hcomp := hfbase.comp_hasDerivAt 0 hline
  have hexpl := realLpGradient_line_hasDerivAt hp x h hx hxcoord
  exact hcomp.unique hexpl

/-! ## The actual rectangular Boyd update and its Frechet derivative -/

/-- Linear rectangular action, bundled continuously using finite
dimensionality. -/
noncomputable def boydRectActionCLM {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin m → ℝ) :=
  (Matrix.of A).mulVecLin.toContinuousLinearMap

/-- Linear transpose action. -/
noncomputable def boydRectTransposeActionCLM {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (Matrix.of (fun j i => A i j)).mulVecLin.toContinuousLinearMap

theorem boydRectActionCLM_apply {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    boydRectActionCLM A x = fun i => ∑ j : Fin n, A i j * x j := by
  rfl

theorem boydRectTransposeActionCLM_apply {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin m → ℝ) :
    boydRectTransposeActionCLM A y =
      fun j => ∑ i : Fin m, A i j * y i := by
  rfl

/-- The explicit smooth formula underlying the actual normalized-dual update
on Boyd's nonzero-coordinate domain. -/
noncomputable def boydSmoothRectUpdate {m n : ℕ}
    {p q : ℝ} (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) : Fin n → ℝ :=
  realLpGradient q
    (boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)))

/-- The concrete derivative operator in Boyd's Lemma 2, represented without
postulating any contraction property. -/
noncomputable def boydSmoothRectDerivative {m n : ℕ}
    {p q : ℝ} (A : Fin m → Fin n → ℝ)
    (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  fderiv ℝ (boydSmoothRectUpdate (p := p) (q := q) A) x

/-- Boyd Lemma 2 at the level needed by the local convergence theorem: the
explicit normalized-gradient composition has its actual Frechet derivative
whenever both intermediate vectors avoid coordinate singularities. -/
theorem boydSmoothRectUpdate_hasFDerivAt {m n : ℕ}
    {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    HasFDerivAt (boydSmoothRectUpdate (p := p) (q := q) A)
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  apply DifferentiableAt.hasFDerivAt
  unfold boydSmoothRectUpdate
  have hA : DifferentiableAt ℝ (boydRectActionCLM A) x :=
    (boydRectActionCLM A).differentiableAt
  have hgp : DifferentiableAt ℝ
      (fun u : Fin n → ℝ =>
        realLpGradient p (boydRectActionCLM A u)) x :=
    (differentiableAt_realLpGradient_of_all_ne hp
      (boydRectActionCLM A x) hycoord).comp x hA
  have hAT : DifferentiableAt ℝ
      (fun u : Fin n → ℝ =>
        boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A u))) x :=
    (boydRectTransposeActionCLM A).differentiableAt.comp x hgp
  exact (differentiableAt_realLpGradient_of_all_ne hq _ hzcoord).comp x hAT

/-- On its source domain, the literal `RectPNormPair.general.xnext` agrees
with the explicit smooth formula. -/
theorem rect_general_xnext_eq_boydSmoothRectUpdate {m n : ℕ}
    (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0) :
    (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectUpdate (p := p) (q := q) A x := by
  let P := RectPNormPair.general hn hpq A
  have hyof : P.yof x = boydRectActionCLM A x := by
    rfl
  have hdp : P.dpOut (P.yof x) = realLpGradient p (boydRectActionCLM A x) := by
    change realLpDual hpq (P.yof x) = _
    rw [realLpDual_eq_realLpGradient hpq (P.yof x)]
    · rw [hyof]
    · simpa [hyof] using hy
  have hzof : P.zof x = boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) := by
    funext j
    change (∑ i : Fin m, A i j * P.dpOut (P.yof x) i) = _
    rw [hdp]
    rfl
  change realLpDualUnit hn hpq.symm (P.zof x) = _
  rw [realLpDualUnit, if_neg (by simpa [hzof] using hz),
    realLpDual_eq_realLpGradient hpq.symm (P.zof x)]
  · simp [boydSmoothRectUpdate, hzof]
  · simpa [hzof] using hz

/-- The actual source update has an honest Frechet derivative under Boyd's
coordinate hypotheses.  The proof uses neighborhood stability of the
nonzero coordinates, not merely pointwise rewriting. -/
theorem rect_general_xnext_hasFDerivAt_boyd {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  let W := boydSmoothRectUpdate (p := p) (q := q) A
  let L := boydSmoothRectDerivative (p := p) (q := q) A x
  have hW : HasFDerivAt W L x := by
    simpa [W, L] using boydSmoothRectUpdate_hasFDerivAt
      hpq.lt hpq.symm.lt A x hycoord hzcoord
  have hAcont : ContinuousAt (boydRectActionCLM A) x :=
    (boydRectActionCLM A).continuous.continuousAt
  have hgp : DifferentiableAt ℝ
      (fun u : Fin n → ℝ =>
        realLpGradient p (boydRectActionCLM A u)) x :=
    (differentiableAt_realLpGradient_of_all_ne hpq.lt _ hycoord).comp x
      (boydRectActionCLM A).differentiableAt
  have hzcont : ContinuousAt
      (fun u : Fin n → ℝ =>
        boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A u))) x :=
    ((boydRectTransposeActionCLM A).differentiableAt.comp x hgp).continuousAt
  let i0 : Fin n := ⟨0, hn⟩
  let r0 : Fin m := ⟨0, hm⟩
  have hy0 : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    exact hycoord r0 (by simpa using congrFun hzero r0)
  have hz0 : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord i0 (by simpa using congrFun hzero i0)
  have hey : ∀ᶠ u in nhds x, boydRectActionCLM A u ≠ 0 :=
    hAcont.eventually_ne hy0
  have hez : ∀ᶠ u in nhds x,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A u)) ≠ 0 :=
    hzcont.eventually_ne hz0
  have heq : (RectPNormPair.general hn hpq A).xnext =ᶠ[nhds x] W := by
    filter_upwards [hey, hez] with u hyu hzu
    exact rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A u hyu hzu
  exact hW.congr_of_eventuallyEq heq

/-- Consequently the actual `fderiv` is definitionally identified with the
source smooth-composition derivative, rather than left as an existential
linear map. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    fderiv ℝ (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x := by
  exact (rect_general_xnext_hasFDerivAt_boyd
    hm hn hpq A x hycoord hzcoord).fderiv

/-! ## Corrected source boundary -/

/-- A strict maximum need not be nondegenerate: `-t^4` has a strict maximum
at zero but its quadratic term vanishes.  This finite witness is the precise
logical error in the printed premise of Boyd Theorem 3; it does not challenge
the corrected nondegenerate theorem used by Higham's word "strong". -/
theorem strictMaximum_does_not_imply_negative_quadratic_term :
    (∀ t : ℝ, t ≠ 0 → -(t ^ 4) < -(0 ^ 4)) ∧
      ¬ (∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, -(t ^ 4) ≤ -c * t ^ 2) := by
  constructor
  · intro t ht
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    nlinarith [sq_nonneg (t ^ 2)]
  · rintro ⟨c, hc, hquad⟩
    let t : ℝ := Real.sqrt (c / 2)
    have hc2 : 0 < c / 2 := by positivity
    have ht2 : t ^ 2 = c / 2 := by
      dsimp [t]
      rw [Real.sq_sqrt (le_of_lt hc2)]
    have h := hquad t
    rw [ht2, show t ^ 4 = (t ^ 2) ^ 2 by ring, ht2] at h
    nlinarith

/-! ### Boyd Lemma 3: nondegenerate tangent curvature gives stability -/

/-- A nondegenerate strict tangent maximum is expressed only through a
uniform negative Hessian gap.  In particular, neither contraction nor power
stability occurs in this definition.  Boyd's nonzero-coordinate regularity
is supplied separately when this predicate is applied to the concrete
normalized-dual update below. -/
def IsBoydNondegenerateTangentHessian
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → ℝ) : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ h : E, H h ≤ -η * ‖h‖ ^ 2

/-- Restriction of a derivative to an invariant tangent subspace. -/
noncomputable def boydInvariantRestriction
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (T : Submodule ℝ V) (L : V →L[ℝ] V)
    (hInv : ∀ h : T, L h ∈ T) : T →L[ℝ] T :=
  (L.comp T.subtypeL).codRestrict T hInv

/-- The tangent derivative transported to a Hilbert model carrying Boyd's
weighted inner product.  A continuous linear equivalence is used, rather
than an isometry, because its norm is generally not the repository's default
Euclidean norm. -/
noncomputable def boydWeightedTangentDerivative
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : Submodule ℝ V) (L : V →L[ℝ] V)
    (hInv : ∀ h : T, L h ∈ T) (e : E ≃L[ℝ] T) : E →L[ℝ] E :=
  e.symm.toContinuousLinearMap.comp
    ((boydInvariantRestriction T L hInv).comp e.toContinuousLinearMap)

/-- A symmetric positive-semidefinite operator whose Rayleigh quotient has a
uniform gap below one is a strict contraction.  This is the spectral step in
Boyd Lemma 3. -/
theorem opNorm_le_one_sub_of_symmetric_psd_rayleigh_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) {δ : ℝ} (hδ1 : δ < 1)
    (hsymm : (L : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E, 0 ≤ inner ℝ (L h) h)
    (hupper : ∀ h : E,
      inner ℝ (L h) h ≤ (1 - δ) * ‖h‖ ^ 2) :
    ‖L‖ ≤ 1 - δ := by
  rw [L.norm_eq_iSup_rayleighQuotient hsymm]
  apply ciSup_le
  intro h
  by_cases hh : h = 0
  · subst h
    simp [le_of_lt (sub_pos.mpr hδ1)]
  have hnorm2 : 0 < ‖h‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hh)
  have hray_nonneg : 0 ≤ L.rayleighQuotient h := by
    rw [ContinuousLinearMap.rayleighQuotient]
    exact div_nonneg
      (by simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hpsd h)
      (le_of_lt hnorm2)
  rw [abs_of_nonneg hray_nonneg]
  rw [ContinuousLinearMap.rayleighQuotient]
  apply (div_le_iff₀ hnorm2).2
  simpa [ContinuousLinearMap.reApplyInnerSelf_apply] using hupper h

/-- Pure tangent-Hessian nondegeneracy, together with Boyd's Hessian/Rayleigh
identity and weighted self-adjoint positive-semidefinite linearization,
produces a one-step strict contraction in the weighted tangent norm. -/
theorem boyd_weighted_tangent_contraction_of_nondegenerate_hessian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (H : E → ℝ) {κ : ℝ}
    (hκ : 0 < κ)
    (hsymm : (L : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E, 0 ≤ inner ℝ (L h) h)
    (hidentity : ∀ h : E,
      H h = κ * (inner ℝ (L h) h - ‖h‖ ^ 2))
    (hnondeg : IsBoydNondegenerateTangentHessian H) :
    ∃ c : NNReal, 0 < c ∧ c < 1 ∧ ‖L‖ ≤ (c : ℝ) := by
  obtain ⟨η, hη, hgap⟩ := hnondeg
  let δ : ℝ := min (η / κ) (1 / 2)
  have hδ0 : 0 < δ :=
    lt_min (div_pos hη hκ) (by norm_num)
  have hδ1 : δ < 1 :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hκδ : κ * δ ≤ η := by
    have hd : δ ≤ η / κ := min_le_left _ _
    calc
      κ * δ ≤ κ * (η / κ) :=
        mul_le_mul_of_nonneg_left hd (le_of_lt hκ)
      _ = η := by field_simp
  have hgapδ : ∀ h : E, H h ≤ -(κ * δ) * ‖h‖ ^ 2 := by
    intro h
    calc
      H h ≤ -η * ‖h‖ ^ 2 := hgap h
      _ ≤ -(κ * δ) * ‖h‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hκδ (sq_nonneg ‖h‖)
        linarith
  have hupper : ∀ h : E,
      inner ℝ (L h) h ≤ (1 - δ) * ‖h‖ ^ 2 := by
    intro h
    have hscaled :
        κ * (inner ℝ (L h) h - ‖h‖ ^ 2) ≤
          κ * (-δ * ‖h‖ ^ 2) := by
      calc
        κ * (inner ℝ (L h) h - ‖h‖ ^ 2) = H h := (hidentity h).symm
        _ ≤ -(κ * δ) * ‖h‖ ^ 2 := hgapδ h
        _ = κ * (-δ * ‖h‖ ^ 2) := by ring
    nlinarith
  have hnorm :=
    opNorm_le_one_sub_of_symmetric_psd_rayleigh_gap L hδ1 hsymm hpsd hupper
  let c : NNReal := ⟨1 - δ, le_of_lt (sub_pos.mpr hδ1)⟩
  refine ⟨c, ?_, ?_, ?_⟩
  · change 0 < (c : ℝ)
    exact sub_pos.mpr hδ1
  · change (c : ℝ) < 1
    exact sub_lt_self (1 : ℝ) hδ0
  · simpa [c] using hnorm

/-- Powers commute with transport by a continuous linear equivalence. -/
theorem continuousLinearEquiv_conj_pow
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (L : F →L[ℝ] F) (N : ℕ) :
    L ^ N = e.toContinuousLinearMap.comp
      (((e.symm.toContinuousLinearMap.comp
        (L.comp e.toContinuousLinearMap)) ^ N).comp
          e.symm.toContinuousLinearMap) := by
  induction N with
  | zero =>
      ext x
      simp
  | succ N ih =>
      ext x
      simp only [pow_succ, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.comp_apply, ih]
      simp

/-- A strict contraction after any equivalent change of norm yields a finite
strict power certificate in the original norm. -/
theorem exists_pos_power_bound_of_equivalent_contraction
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃L[ℝ] F) (L : F →L[ℝ] F) {c K : NNReal}
    (hcK : c < K)
    (hconj : ‖e.symm.toContinuousLinearMap.comp
      (L.comp e.toContinuousLinearMap)‖ ≤ (c : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ‖L ^ N‖ ≤ (K : ℝ) ^ N := by
  let S : E →L[ℝ] E := e.symm.toContinuousLinearMap.comp
    (L.comp e.toContinuousLinearMap)
  let M : ℝ := ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖
  have hc0 : 0 ≤ (c : ℝ) := NNReal.coe_nonneg c
  have hcK' : (c : ℝ) < (K : ℝ) := by exact_mod_cast hcK
  have hlittle : (fun N : ℕ => M * (c : ℝ) ^ N) =o[atTop]
      (fun N : ℕ => (K : ℝ) ^ N) :=
    (isLittleO_pow_pow_of_lt_left hc0 hcK').const_mul_left M
  have hev : ∀ᶠ N : ℕ in atTop,
      M * (c : ℝ) ^ N ≤ (K : ℝ) ^ N := by
    filter_upwards [hlittle.eventuallyLE] with N hN
    have hM : 0 ≤ M := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    simpa [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hM,
      abs_of_nonneg hc0, abs_of_nonneg (NNReal.coe_nonneg K)] using hN
  obtain ⟨N, hbound, hN⟩ :=
    (hev.and (eventually_ge_atTop (1 : ℕ))).exists
  refine ⟨N, hN, ?_⟩
  rw [continuousLinearEquiv_conj_pow e L N]
  calc
    ‖e.toContinuousLinearMap.comp
        ((S ^ N).comp e.symm.toContinuousLinearMap)‖
        ≤ ‖e.toContinuousLinearMap‖ *
          ‖(S ^ N).comp e.symm.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖e.toContinuousLinearMap‖ *
        (‖S ^ N‖ * ‖e.symm.toContinuousLinearMap‖) := by
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ M * (c : ℝ) ^ N := by
      have hSN : ‖S ^ N‖ ≤ (c : ℝ) ^ N := by
        calc
          ‖S ^ N‖ ≤ ‖S‖ ^ N := norm_pow_le' S hN
          _ ≤ (c : ℝ) ^ N := pow_le_pow_left₀ (norm_nonneg S)
            (by simpa [S] using hconj) N
      dsimp [M]
      calc
        ‖e.toContinuousLinearMap‖ *
            (‖S ^ N‖ * ‖e.symm.toContinuousLinearMap‖) =
            (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
              ‖S ^ N‖ := by ring
        _ ≤ (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
              (c : ℝ) ^ N := mul_le_mul_of_nonneg_left hSN
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        _ = ‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖ *
              (c : ℝ) ^ N := rfl
    _ ≤ (K : ℝ) ^ N := hbound

/-- Strong corrected Boyd Lemma 3 endpoint.  The Hessian gap is a pure
nondegeneracy hypothesis; symmetry, positive semidefiniteness, invariance,
and the Hessian/Rayleigh identity are displayed as the precise second-order
regularity premises.  The conclusion is stable power of the *actual tangent
restriction* in the repository norm, obtained by transferring the weighted
contraction through norm equivalence. -/
theorem boyd_tangent_restriction_power_stable_of_nondegenerate_hessian
    {V E : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : Submodule ℝ V) (L : V →L[ℝ] V)
    (hInv : ∀ h : T, L h ∈ T) (e : E ≃L[ℝ] T)
    (H : E → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hsymm :
      (boydWeightedTangentDerivative T L hInv e : E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E,
      0 ≤ inner ℝ (boydWeightedTangentDerivative T L hInv e h) h)
    (hidentity : ∀ h : E,
      H h = κ *
        (inner ℝ (boydWeightedTangentDerivative T L hInv e h) h - ‖h‖ ^ 2))
    (hnondeg : IsBoydNondegenerateTangentHessian H) :
    ∃ N : ℕ, 0 < N ∧ ∃ K : NNReal,
      0 < K ∧ K < 1 ∧
        ContinuousLinearMap.opNorm
          ((boydInvariantRestriction T L hInv) ^ N) ≤ (K : ℝ) ^ N := by
  let S := boydWeightedTangentDerivative T L hInv e
  obtain ⟨c, hc0, hc1, hSc⟩ :=
    boyd_weighted_tangent_contraction_of_nondegenerate_hessian
      S H hκ (by simpa [S] using hsymm) (by simpa [S] using hpsd)
        (by simpa [S] using hidentity) hnondeg
  let K : NNReal := (c + 1) / 2
  have hcK : c < K := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (lt_div_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c * 2 = c + c := by ring
      _ < c + 1 := by simpa [add_comm] using add_lt_add_left hc1 c
  have hK1 : K < 1 := by
    rw [show K = (c + 1) / 2 by rfl]
    apply (div_lt_iff₀ (by norm_num : (0 : NNReal) < 2)).2
    calc
      c + 1 < 1 + 1 := by simpa [add_comm] using add_lt_add_right hc1 1
      _ = 1 * 2 := by ring
  have hK0 : 0 < K := lt_of_lt_of_le hc0 (le_of_lt hcK)
  letI : Norm (T →L[ℝ] T) :=
    ContinuousLinearMap.hasOpNorm (σ₁₂ := RingHom.id ℝ)
  obtain ⟨N, hN, hpow⟩ :=
    exists_pos_power_bound_of_equivalent_contraction
      e (boydInvariantRestriction T L hInv) hcK (by simpa [S,
        boydWeightedTangentDerivative] using hSc)
  exact ⟨N, hN, K, hK0, hK1, hpow⟩

/-- Concrete source-facing *conditional* endpoint.  The first conjunct is
Boyd Lemma 2 for the literal rectangular update under his nonzero-coordinate
regularity.  The second is the tangent stable-power conclusion from the
nondegenerate Hessian data.  This is deliberately not advertised as a closure
of literal Lemma 3: invariance, weighted symmetry, positive semidefiniteness,
and the Hessian/Rayleigh identity for the concrete formula remain visible
premises below and are the exact open source-strength structural boundary. -/
theorem rect_general_boyd_tangent_power_stable_of_nondegenerate_hessian
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0)
    (T : Submodule ℝ (Fin n → ℝ))
    (hInv : ∀ h : T,
      boydSmoothRectDerivative (p := p) (q := q) A x h ∈ T)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (e : E ≃L[ℝ] T) (H : E → ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hsymm : (boydWeightedTangentDerivative T
      (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e :
        E →ₗ[ℝ] E).IsSymmetric)
    (hpsd : ∀ h : E, 0 ≤ inner ℝ
      (boydWeightedTangentDerivative T
        (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e h) h)
    (hidentity : ∀ h : E, H h = κ *
      (inner ℝ (boydWeightedTangentDerivative T
        (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e h) h -
          ‖h‖ ^ 2))
    (hnondeg : IsBoydNondegenerateTangentHessian H) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x ∧
      ∃ N : ℕ, 0 < N ∧ ∃ K : NNReal,
        0 < K ∧ K < 1 ∧
          ContinuousLinearMap.opNorm
            ((boydInvariantRestriction T
              (boydSmoothRectDerivative (p := p) (q := q) A x) hInv) ^ N) ≤
                (K : ℝ) ^ N := by
  constructor
  · exact rect_general_xnext_hasFDerivAt_boyd
      hm hn hpq A x hycoord hzcoord
  · exact boyd_tangent_restriction_power_stable_of_nondegenerate_hessian
      T (boydSmoothRectDerivative (p := p) (q := q) A x) hInv e H hκ
        hsymm hpsd hidentity hnondeg

/-- Generic local-convergence consumer retained for downstream use.  Unlike
the tangent theorem above, this older whole-space wrapper takes stable power
as an input and therefore is not itself evidence that Boyd Lemma 3 is closed.
The calculus theorem supplies the derivative of the *actual* update, while
the concrete whole-space upgrade remains a separate source boundary. -/
theorem higham15_boyd_local_corrected_of_actual_derivative_power_stable
    {m n : ℕ} (P : RectPNormPair m n)
    (x0 xbar : Fin n → ℝ)
    (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    {N : ℕ} (hN : 0 < N) {c K : NNReal}
    (hc : 0 < c) (hcK : c < K) (hK : K < 1)
    (hfixed : P.xnext xbar = xbar)
    (hderiv : HasFDerivAt P.xnext L xbar)
    (hstable : ‖L ^ N‖ ≤ (c : ℝ) ^ N) :
    ∃ δ : ℝ, 0 < δ ∧
      (powerAdaptedSeminorm L c N (x0 - xbar) ≤ δ →
        (∀ k : ℕ,
          powerAdaptedSeminorm L c N (P.xseq x0 k - xbar) ≤
            (K : ℝ) ^ k * powerAdaptedSeminorm L c N (x0 - xbar)) ∧
        Tendsto (P.xseq x0) atTop (nhds xbar)) :=
  higham15_boyd_local_linear_of_fderiv_power_stable
    P x0 xbar L hN hc hcK hK hstable hfixed hderiv

/-! ## Concrete Boyd-Lemma-3 algebra

The results below are appended rather than folded into the abstract bridge
above.  They derive the weighted symmetry, positive semidefiniteness, and
tangent projection directly from Boyd's concrete `B` operator, and expose
the exact directional chain for the already identified actual derivative. -/

lemma boyd_weight_mul_inverse_weight {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * |a| ^ (2 - p) = 1 := by
  rw [← Real.rpow_add (abs_pos.mpr ha)]
  rw [show p - 2 + (2 - p) = 0 by ring, Real.rpow_zero]

lemma boyd_weight_mul_self {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * a * a = |a| ^ p := by
  calc
    |a| ^ (p - 2) * a * a = |a| ^ (p - 2) * |a| ^ (2 : ℝ) := by
      rw [Real.rpow_two, sq_abs]
      ring
    _ = |a| ^ p := by
      rw [← Real.rpow_add (abs_pos.mpr ha)]
      congr 1
      ring

/-- Boyd's concrete operator
`B h = |x|^(2-p) Aᵀ (|Ax|^(p-2) A h)`. -/
noncomputable def boydLemma3B {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) : Fin n → ℝ :=
  fun j => |x j| ^ (2 - p) *
    ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
      boydRectActionCLM A h i

/-- Exact weighted Gram identity for Boyd's `B`. -/
theorem boydWeightedPair_lemma3B {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) :
    boydWeightedPair p x (boydLemma3B p A x g) h =
      ∑ i : Fin m, |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A g i * boydRectActionCLM A h i := by
  unfold boydWeightedPair boydLemma3B
  simp_rw [boydRectActionCLM_apply]
  calc
    (∑ j : Fin n, |x j| ^ (p - 2) *
        (|x j| ^ (2 - p) *
          ∑ i : Fin m, A i j *
            |∑ k : Fin n, A i k * x k| ^ (p - 2) *
              (∑ k : Fin n, A i k * g k)) * h j) =
      ∑ j : Fin n, (∑ i : Fin m, A i j *
            |∑ k : Fin n, A i k * x k| ^ (p - 2) *
              (∑ k : Fin n, A i k * g k)) * h j := by
        apply Finset.sum_congr rfl
        intro j _hj
        have hw := boyd_weight_mul_inverse_weight (p := p) (hxcoord j)
        calc
          (|x j| ^ (p - 2) *
              (|x j| ^ (2 - p) *
                ∑ i : Fin m, A i j *
                  |∑ k : Fin n, A i k * x k| ^ (p - 2) *
                    (∑ k : Fin n, A i k * g k))) * h j =
              (|x j| ^ (p - 2) * |x j| ^ (2 - p)) *
                ((∑ i : Fin m, A i j *
                  |∑ k : Fin n, A i k * x k| ^ (p - 2) *
                    (∑ k : Fin n, A i k * g k)) * h j) := by ring
          _ = (∑ i : Fin m, A i j *
                  |∑ k : Fin n, A i k * x k| ^ (p - 2) *
                    (∑ k : Fin n, A i k * g k)) * h j := by
            rw [hw, one_mul]
    _ = ∑ i : Fin m, |∑ k : Fin n, A i k * x k| ^ (p - 2) *
          (∑ k : Fin n, A i k * g k) * (∑ j : Fin n, A i j * h j) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring

theorem boydWeightedPair_symm {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) :
    boydWeightedPair p x g h = boydWeightedPair p x h g := by
  unfold boydWeightedPair
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem boydLemma3B_weighted_symmetric {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) :
    boydWeightedPair p x (boydLemma3B p A x g) h =
      boydWeightedPair p x g (boydLemma3B p A x h) := by
  rw [boydWeightedPair_lemma3B p A x g h hxcoord]
  rw [show boydWeightedPair p x g (boydLemma3B p A x h) =
      boydWeightedPair p x (boydLemma3B p A x h) g by
    exact boydWeightedPair_symm p x g (boydLemma3B p A x h)]
  rw [boydWeightedPair_lemma3B p A x h g hxcoord]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem boydLemma3B_weighted_psd {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) :
    0 ≤ boydWeightedPair p x (boydLemma3B p A x h) h := by
  rw [boydWeightedPair_lemma3B p A x h h hxcoord]
  apply Finset.sum_nonneg
  intro i _hi
  have hw : 0 ≤ |boydRectActionCLM A x i| ^ (p - 2) :=
    Real.rpow_nonneg (abs_nonneg _) _
  nlinarith [sq_nonneg (boydRectActionCLM A h i)]

theorem boydWeightedPair_sub_left {n : ℕ} (p : ℝ)
    (x g k h : Fin n → ℝ) (c : ℝ) :
    boydWeightedPair p x (fun i => g i - c * k i) h =
      boydWeightedPair p x g h - c * boydWeightedPair p x k h := by
  unfold boydWeightedPair
  calc
    (∑ i : Fin n, |x i| ^ (p - 2) * (g i - c * k i) * h i) =
        ∑ i : Fin n,
          (|x i| ^ (p - 2) * g i * h i -
            c * (|x i| ^ (p - 2) * k i * h i)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = (∑ i : Fin n, |x i| ^ (p - 2) * g i * h i) -
        c * ∑ i : Fin n, |x i| ^ (p - 2) * k i * h i := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

theorem boydWeightedPair_sub_right {n : ℕ} (p : ℝ)
    (x g h k : Fin n → ℝ) (c : ℝ) :
    boydWeightedPair p x g (fun i => h i - c * k i) =
      boydWeightedPair p x g h - c * boydWeightedPair p x g k := by
  rw [boydWeightedPair_symm p x g]
  rw [boydWeightedPair_sub_left p x h k g c]
  rw [boydWeightedPair_symm p x h g, boydWeightedPair_symm p x k g]

theorem boydWeightedPair_smul_left {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) (c : ℝ) :
    boydWeightedPair p x (fun i => c * g i) h =
      c * boydWeightedPair p x g h := by
  unfold boydWeightedPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem boydWeightedPair_smul_right {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) (c : ℝ) :
    boydWeightedPair p x g (fun i => c * h i) =
      c * boydWeightedPair p x g h := by
  rw [boydWeightedPair_symm p x g]
  rw [boydWeightedPair_smul_left p x h g c]
  rw [boydWeightedPair_symm p x h g]

theorem boydWeightedPair_x_self_eq_powerSum {n : ℕ} (p : ℝ)
    (x : Fin n → ℝ) (hxcoord : ∀ j, x j ≠ 0) :
    boydWeightedPair p x x x = realLpPowerSum p x := by
  unfold boydWeightedPair realLpPowerSum
  apply Finset.sum_congr rfl
  intro j _hj
  exact boyd_weight_mul_self (p := p) (hxcoord j)

/-- Weighted-orthogonal projection of `B h` onto the tangent hyperplane. -/
noncomputable def boydProjectedLemma3B {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) : Fin n → ℝ :=
  fun j => boydLemma3B p A x h j -
    boydWeightedPair p x x (boydLemma3B p A x h) * x j

theorem boydProjectedLemma3B_is_tangent {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x x (boydProjectedLemma3B p A x h) = 0 := by
  rw [show boydProjectedLemma3B p A x h = fun j =>
      boydLemma3B p A x h j -
        boydWeightedPair p x x (boydLemma3B p A x h) * x j by rfl]
  rw [boydWeightedPair_sub_right]
  rw [boydWeightedPair_x_self_eq_powerSum p x hxcoord, hunit]
  ring

theorem boydProjectedLemma3B_weighted_symmetric_on_tangent
    {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hg : boydWeightedPair p x x g = 0)
    (hh : boydWeightedPair p x x h = 0) :
    boydWeightedPair p x (boydProjectedLemma3B p A x g) h =
      boydWeightedPair p x g (boydProjectedLemma3B p A x h) := by
  rw [show boydProjectedLemma3B p A x g = fun j =>
      boydLemma3B p A x g j -
        boydWeightedPair p x x (boydLemma3B p A x g) * x j by rfl]
  rw [show boydProjectedLemma3B p A x h = fun j =>
      boydLemma3B p A x h j -
        boydWeightedPair p x x (boydLemma3B p A x h) * x j by rfl]
  rw [boydWeightedPair_sub_left, boydWeightedPair_sub_right]
  rw [hh, boydWeightedPair_symm p x g x, hg]
  simp only [mul_zero, sub_zero]
  exact boydLemma3B_weighted_symmetric p A x g h hxcoord

theorem boydProjectedLemma3B_weighted_psd_on_tangent
    {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hh : boydWeightedPair p x x h = 0) :
    0 ≤ boydWeightedPair p x (boydProjectedLemma3B p A x h) h := by
  rw [show boydProjectedLemma3B p A x h = fun j =>
      boydLemma3B p A x h j -
        boydWeightedPair p x x (boydLemma3B p A x h) * x j by rfl]
  rw [boydWeightedPair_sub_left, hh]
  simp only [mul_zero, sub_zero]
  exact boydLemma3B_weighted_psd p A x h hxcoord

/-- Exact action of the actual derivative as the nested normalized-gradient
directional chain.  This discharges all calculus hidden in Boyd Lemma 2. -/
theorem boydSmoothRectDerivative_apply_directional_chain
    {m n : ℕ} {p q : ℝ} (hp : 1 < p) (hq : 1 < q)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hzcoord : ∀ j,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) j ≠ 0) :
    boydSmoothRectDerivative (p := p) (q := q) A x h =
      realLpGradientDirectional q
        (boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A x)))
        (boydRectTransposeActionCLM A
          (realLpGradientDirectional p (boydRectActionCLM A x)
            (boydRectActionCLM A h))) := by
  have hline : HasDerivAt
      (fun t : ℝ => (fun i => x i + t * h i)) h 0 := by
    apply hasDerivAt_pi.2
    intro i
    have hline' := (hasDerivAt_const (x := (0 : ℝ)) (x i)).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_mul (h i))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hAline :=
    (boydRectActionCLM A).hasFDerivAt.comp_hasDerivAt 0 hline
  have hpF :=
    (differentiableAt_realLpGradient_of_all_ne hp
      (boydRectActionCLM A x) hycoord).hasFDerivAt
  have hpFbase : HasFDerivAt (realLpGradient p)
      (fderiv ℝ (realLpGradient p) (boydRectActionCLM A x))
      ((boydRectActionCLM A ∘ fun t : ℝ =>
        (fun i => x i + t * h i)) 0) := by
    simpa [Function.comp_def] using hpF
  have hpLine := hpFbase.comp_hasDerivAt 0 hAline
  rw [fderiv_realLpGradient_apply hp
    (boydRectActionCLM A x) (boydRectActionCLM A h) hycoord] at hpLine
  have hATline :=
    (boydRectTransposeActionCLM A).hasFDerivAt.comp_hasDerivAt 0 hpLine
  have hqF :=
    (differentiableAt_realLpGradient_of_all_ne hq
      (boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x))) hzcoord).hasFDerivAt
  have hqFbase : HasFDerivAt (realLpGradient q)
      (fderiv ℝ (realLpGradient q)
        (boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A x))))
      (((boydRectTransposeActionCLM A) ∘ realLpGradient p ∘
        (boydRectActionCLM A) ∘
        (fun t : ℝ => (fun i => x i + t * h i))) 0) := by
    simpa [Function.comp_def] using hqF
  have hqLine := hqFbase.comp_hasDerivAt 0 hATline
  rw [fderiv_realLpGradient_apply hq
    (boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)))
    (boydRectTransposeActionCLM A
      (realLpGradientDirectional p (boydRectActionCLM A x)
        (boydRectActionCLM A h))) hzcoord] at hqLine
  have hWF := boydSmoothRectUpdate_hasFDerivAt hp hq A x hycoord hzcoord
  have hWFbase : HasFDerivAt (boydSmoothRectUpdate (p := p) (q := q) A)
      (boydSmoothRectDerivative (p := p) (q := q) A x)
      ((fun t : ℝ => (fun i => x i + t * h i)) 0) := by
    simpa using hWF
  have hactual := hWFbase.comp_hasDerivAt 0 hline
  exact hactual.unique hqLine

/-- Weighted-orthogonal projection onto Boyd's tangent hyperplane. -/
noncomputable def boydWeightedProjection {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) : Fin n → ℝ :=
  fun j => h j - boydWeightedPair p x x h * x j

theorem boydWeightedProjection_is_tangent {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x x (boydWeightedProjection p x h) = 0 := by
  rw [show boydWeightedProjection p x h = fun j =>
      h j - boydWeightedPair p x x h * x j by rfl]
  rw [boydWeightedPair_sub_right]
  rw [boydWeightedPair_x_self_eq_powerSum p x hxcoord, hunit]
  ring

theorem boydWeightedProjection_eq_self_of_tangent {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ) (hh : boydWeightedPair p x x h = 0) :
    boydWeightedProjection p x h = h := by
  funext j
  simp [boydWeightedProjection, hh]

theorem boydWeightedPair_projection_left_of_tangent {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) (hh : boydWeightedPair p x x h = 0) :
    boydWeightedPair p x (boydWeightedProjection p x g) h =
      boydWeightedPair p x g h := by
  rw [show boydWeightedProjection p x g = fun j =>
      g j - boydWeightedPair p x x g * x j by rfl]
  rw [boydWeightedPair_sub_left, hh, mul_zero, sub_zero]

theorem boydWeightedPair_projection_right_of_tangent {n : ℕ} (p : ℝ)
    (x g h : Fin n → ℝ) (hg : boydWeightedPair p x x g = 0) :
    boydWeightedPair p x g (boydWeightedProjection p x h) =
      boydWeightedPair p x g h := by
  rw [show boydWeightedProjection p x h = fun j =>
      h j - boydWeightedPair p x x h * x j by rfl]
  rw [boydWeightedPair_sub_right, boydWeightedPair_symm p x g x, hg,
    mul_zero, sub_zero]

/-- Pythagorean identity for the radial/tangent split. -/
theorem boydWeightedProjection_sq {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x (boydWeightedProjection p x h)
        (boydWeightedProjection p x h) =
      boydWeightedPair p x h h - (boydWeightedPair p x x h) ^ 2 := by
  let c := boydWeightedPair p x x h
  have hPtan : boydWeightedPair p x x (boydWeightedProjection p x h) = 0 :=
    boydWeightedProjection_is_tangent p x h hxcoord hunit
  rw [show boydWeightedProjection p x h = fun j => h j - c * x j by rfl]
  rw [boydWeightedPair_sub_left]
  have hzero : boydWeightedPair p x x (fun j => h j - c * x j) = 0 := by
    simpa [c, boydWeightedProjection] using hPtan
  rw [hzero, mul_zero, sub_zero]
  rw [boydWeightedPair_sub_right, boydWeightedPair_symm p x h x]
  dsimp [c]
  ring

theorem boydWeightedProjection_sq_le {n : ℕ} (p : ℝ)
    (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1) :
    boydWeightedPair p x (boydWeightedProjection p x h)
        (boydWeightedProjection p x h) ≤ boydWeightedPair p x h h := by
  rw [boydWeightedProjection_sq p x h hxcoord hunit]
  exact sub_le_self _ (sq_nonneg _)

theorem boydLemma3B_sub {m n : ℕ} (p : ℝ)
    (A : Fin m → Fin n → ℝ) (x g k : Fin n → ℝ) (c : ℝ) :
    boydLemma3B p A x (fun j => g j - c * k j) =
      fun j => boydLemma3B p A x g j - c * boydLemma3B p A x k j := by
  funext j
  unfold boydLemma3B
  have hact : ∀ i : Fin m,
      boydRectActionCLM A (fun r => g r - c * k r) i =
        boydRectActionCLM A g i - c * boydRectActionCLM A k i := by
    intro i
    simp only [boydRectActionCLM_apply]
    calc
      (∑ r : Fin n, A i r * (g r - c * k r)) =
          ∑ r : Fin n, (A i r * g r - c * (A i r * k r)) := by
        apply Finset.sum_congr rfl
        intro r _hr
        ring
      _ = (∑ r : Fin n, A i r * g r) -
          c * ∑ r : Fin n, A i r * k r := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [hact]
  calc
    |x j| ^ (2 - p) *
        (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
          (boydRectActionCLM A g i - c * boydRectActionCLM A k i)) =
      |x j| ^ (2 - p) *
        (∑ i : Fin m,
          (A i j * |boydRectActionCLM A x i| ^ (p - 2) *
              boydRectActionCLM A g i -
            c * (A i j * |boydRectActionCLM A x i| ^ (p - 2) *
              boydRectActionCLM A k i))) := by
        apply congrArg (fun z : ℝ => |x j| ^ (2 - p) * z)
        apply Finset.sum_congr rfl
        intro i _hi
        ring
    _ = |x j| ^ (2 - p) *
          ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A g i -
        c * (|x j| ^ (2 - p) *
          ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A k i) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring

/-- Stationarity `B x = λx` makes the projected operator depend only on the
tangent component of its argument, i.e. `PB = PBP`. -/
theorem boydProjectedLemma3B_eq_projection {m n : ℕ} (p lam : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1)
    (hBx : boydLemma3B p A x x = fun j => lam * x j) :
    boydProjectedLemma3B p A x (boydWeightedProjection p x h) =
      boydProjectedLemma3B p A x h := by
  let c := boydWeightedPair p x x h
  have hBP : boydLemma3B p A x (boydWeightedProjection p x h) =
      fun j => boydLemma3B p A x h j - c * (lam * x j) := by
    rw [show boydWeightedProjection p x h = fun j => h j - c * x j by rfl]
    rw [boydLemma3B_sub p A x h x c, hBx]
  have hpairBP :
      boydWeightedPair p x x
          (boydLemma3B p A x (boydWeightedProjection p x h)) =
        boydWeightedPair p x x (boydLemma3B p A x h) - c * lam := by
    rw [hBP]
    rw [show (fun j => boydLemma3B p A x h j - c * (lam * x j)) =
        fun j => boydLemma3B p A x h j - (c * lam) * x j by
      funext j
      ring]
    rw [boydWeightedPair_sub_right]
    rw [boydWeightedPair_x_self_eq_powerSum p x hxcoord, hunit]
    ring
  funext j
  unfold boydProjectedLemma3B
  rw [hpairBP, hBP]
  ring

/-- Under stationarity, `PB` is weighted self-adjoint on the whole space,
not only on tangent vectors. -/
theorem boydProjectedLemma3B_weighted_symmetric {m n : ℕ} (p lam : ℝ)
    (A : Fin m → Fin n → ℝ) (x g h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1)
    (hBx : boydLemma3B p A x x = fun j => lam * x j) :
    boydWeightedPair p x (boydProjectedLemma3B p A x g) h =
      boydWeightedPair p x g (boydProjectedLemma3B p A x h) := by
  have hPg := boydWeightedProjection_is_tangent p x g hxcoord hunit
  have hPh := boydWeightedProjection_is_tangent p x h hxcoord hunit
  have hPBg :=
    boydProjectedLemma3B_is_tangent p A x (boydWeightedProjection p x g)
      hxcoord hunit
  have hPBh := boydProjectedLemma3B_is_tangent p A x h hxcoord hunit
  calc
    boydWeightedPair p x (boydProjectedLemma3B p A x g) h =
        boydWeightedPair p x
          (boydProjectedLemma3B p A x (boydWeightedProjection p x g)) h := by
      rw [boydProjectedLemma3B_eq_projection p lam A x g hxcoord hunit hBx]
    _ = boydWeightedPair p x
          (boydProjectedLemma3B p A x (boydWeightedProjection p x g))
          (boydWeightedProjection p x h) := by
      symm
      exact boydWeightedPair_projection_right_of_tangent p x
        (boydProjectedLemma3B p A x (boydWeightedProjection p x g)) h hPBg
    _ = boydWeightedPair p x (boydWeightedProjection p x g)
          (boydProjectedLemma3B p A x (boydWeightedProjection p x h)) :=
      boydProjectedLemma3B_weighted_symmetric_on_tangent p A x
        (boydWeightedProjection p x g) (boydWeightedProjection p x h)
        hxcoord hPg hPh
    _ = boydWeightedPair p x (boydWeightedProjection p x g)
          (boydProjectedLemma3B p A x h) := by
      rw [boydProjectedLemma3B_eq_projection p lam A x h hxcoord hunit hBx]
    _ = boydWeightedPair p x g (boydProjectedLemma3B p A x h) :=
      boydWeightedPair_projection_left_of_tangent p x g
        (boydProjectedLemma3B p A x h) hPBh

/-- Under stationarity, `PB` is weighted positive semidefinite on the whole
space. -/
theorem boydProjectedLemma3B_weighted_psd {m n : ℕ} (p lam : ℝ)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (hunit : realLpPowerSum p x = 1)
    (hBx : boydLemma3B p A x x = fun j => lam * x j) :
    0 ≤ boydWeightedPair p x (boydProjectedLemma3B p A x h) h := by
  have hPh := boydWeightedProjection_is_tangent p x h hxcoord hunit
  have hPBPh :=
    boydProjectedLemma3B_is_tangent p A x (boydWeightedProjection p x h)
      hxcoord hunit
  calc
    0 ≤ boydWeightedPair p x
        (boydProjectedLemma3B p A x (boydWeightedProjection p x h))
          (boydWeightedProjection p x h) :=
      boydProjectedLemma3B_weighted_psd_on_tangent p A x
        (boydWeightedProjection p x h) hxcoord hPh
    _ = boydWeightedPair p x
        (boydProjectedLemma3B p A x (boydWeightedProjection p x h)) h :=
      boydWeightedPair_projection_right_of_tangent p x
        (boydProjectedLemma3B p A x (boydWeightedProjection p x h)) h hPBPh
    _ = boydWeightedPair p x (boydProjectedLemma3B p A x h) h := by
      rw [boydProjectedLemma3B_eq_projection p lam A x h hxcoord hunit hBx]

/-! ### Normalization and stationarity identities

The calculus below uses the corrected smooth-domain hypothesis that every
coordinate of `x` and `A x` is nonzero.  This is stronger than Higham's bare
phrase that `x` has no zero components (and stronger than necessary when
`p ≥ 2`), but it is exactly the domain on which the explicit Lemma-2 formula
proved above is currently available.  The nonzero coordinates of the outer
input are derived from stationarity rather than assumed. -/

lemma boyd_holder_sub_one_mul_sub_one {p q : ℝ}
    (hpq : p.HolderConjugate q) : (p - 1) * (q - 1) = 1 := by
  have h := hpq.sub_one_mul_conj
  nlinarith

lemma boyd_holder_sub_one_mul_sub_two {p q : ℝ}
    (hpq : p.HolderConjugate q) : (p - 1) * (q - 2) = 2 - p := by
  have h := hpq.sub_one_mul_conj
  nlinarith

lemma boyd_abs_dualCoordinate {p a : ℝ} (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| = |a| ^ (p - 1) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg a) _)]
  rw [← Real.rpow_add_one (abs_ne_zero.mpr ha)]
  congr 1
  ring

lemma boyd_dualCoordinate_ne_zero {p a : ℝ} (ha : a ≠ 0) :
    |a| ^ (p - 2) * a ≠ 0 := by
  exact mul_ne_zero (ne_of_gt (Real.rpow_pos_of_pos (abs_pos.mpr ha) _)) ha

lemma boyd_dualCoordinate_abs_rpow_q {p q a : ℝ}
    (hpq : p.HolderConjugate q) (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| ^ q = |a| ^ p := by
  rw [boyd_abs_dualCoordinate (p := p) ha]
  rw [← Real.rpow_mul (abs_nonneg a)]
  rw [hpq.sub_one_mul_conj]

lemma boyd_dualCoordinate_weight {p q a : ℝ}
    (hpq : p.HolderConjugate q) (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| ^ (q - 2) = |a| ^ (2 - p) := by
  rw [boyd_abs_dualCoordinate (p := p) ha]
  rw [← Real.rpow_mul (abs_nonneg a)]
  rw [boyd_holder_sub_one_mul_sub_two hpq]

lemma boyd_dualCoordinate_involution {p q a : ℝ}
    (hpq : p.HolderConjugate q) (ha : a ≠ 0) :
    |(|a| ^ (p - 2) * a)| ^ (q - 2) *
        (|a| ^ (p - 2) * a) = a := by
  rw [boyd_dualCoordinate_weight hpq ha]
  have hw := boyd_weight_mul_inverse_weight (p := p) ha
  calc
    |a| ^ (2 - p) * (|a| ^ (p - 2) * a) =
        (|a| ^ (p - 2) * |a| ^ (2 - p)) * a := by ring
    _ = a := by rw [hw, one_mul]

lemma boyd_scaled_dualCoordinate_weight {p q α a : ℝ}
    (hpq : p.HolderConjugate q) (hα : 0 < α) (ha : a ≠ 0) :
    |α * (|a| ^ (p - 2) * a)| ^ (q - 2) =
      α ^ (q - 2) * |a| ^ (2 - p) := by
  rw [abs_mul, abs_of_pos hα, Real.mul_rpow hα.le (abs_nonneg _)]
  rw [boyd_dualCoordinate_weight hpq ha]

lemma boyd_scaled_dualCoordinate_involution {p q α a : ℝ}
    (hpq : p.HolderConjugate q) (hα : 0 < α) (ha : a ≠ 0) :
    |α * (|a| ^ (p - 2) * a)| ^ (q - 2) *
        (α * (|a| ^ (p - 2) * a)) = α ^ (q - 1) * a := by
  rw [boyd_scaled_dualCoordinate_weight hpq hα ha]
  have hw := boyd_weight_mul_inverse_weight (p := p) ha
  calc
    (α ^ (q - 2) * |a| ^ (2 - p)) *
        (α * (|a| ^ (p - 2) * a)) =
      (α ^ (q - 2) * α) *
        (|a| ^ (2 - p) * (|a| ^ (p - 2) * a)) := by ring
    _ = α ^ (q - 1) * a := by
      rw [show |a| ^ (2 - p) * (|a| ^ (p - 2) * a) = a by
        calc
          |a| ^ (2 - p) * (|a| ^ (p - 2) * a) =
              (|a| ^ (p - 2) * |a| ^ (2 - p)) * a := by ring
          _ = a := by rw [hw, one_mul]]
      rw [show α ^ (q - 2) * α = α ^ (q - 1) by
        calc
          α ^ (q - 2) * α = α ^ (q - 2) * α ^ (1 : ℝ) := by
            rw [Real.rpow_one]
          _ = α ^ ((q - 2) + 1) := (Real.rpow_add hα (q - 2) 1).symm
          _ = α ^ (q - 1) := by congr 1 <;> ring]

lemma boyd_powerSum_scaled_dual {n : ℕ} {p q α : ℝ}
    (hpq : p.HolderConjugate q) (x : Fin n → ℝ)
    (hα : 0 < α) (hxcoord : ∀ j, x j ≠ 0) :
    realLpPowerSum q (fun j => α * (|x j| ^ (p - 2) * x j)) =
      α ^ q * realLpPowerSum p x := by
  unfold realLpPowerSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [abs_mul, abs_of_pos hα]
  rw [Real.mul_rpow hα.le (abs_nonneg _)]
  rw [boyd_dualCoordinate_abs_rpow_q hpq (hxcoord j)]

lemma boyd_weightedPair_scaled_dual_weighted {n : ℕ}
    {p q α β : ℝ} (hpq : p.HolderConjugate q)
    (x k : Fin n → ℝ) (hα : 0 < α) (hxcoord : ∀ j, x j ≠ 0) :
    boydWeightedPair q
        (fun j => α * (|x j| ^ (p - 2) * x j))
        (fun j => α * (|x j| ^ (p - 2) * x j))
        (fun j => β * |x j| ^ (p - 2) * k j) =
      α ^ (q - 1) * β * boydWeightedPair p x x k := by
  unfold boydWeightedPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  have hinv := boyd_scaled_dualCoordinate_involution hpq hα (hxcoord j)
  calc
    |α * (|x j| ^ (p - 2) * x j)| ^ (q - 2) *
          (α * (|x j| ^ (p - 2) * x j)) *
          (β * |x j| ^ (p - 2) * k j) =
        (α ^ (q - 1) * x j) *
          (β * |x j| ^ (p - 2) * k j) := by rw [hinv]
    _ = α ^ (q - 1) * (β * (|x j| ^ (p - 2) * x j * k j)) := by ring
    _ = α ^ (q - 1) * β * (|x j| ^ (p - 2) * x j * k j) := by ring

lemma boyd_outer_directional_weighted_tangent {n : ℕ}
    {p q α β : ℝ} (hpq : p.HolderConjugate q)
    (x k : Fin n → ℝ) (hα : 0 < α) (hxcoord : ∀ j, x j ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hk : boydWeightedPair p x x k = 0) :
    realLpGradientDirectional q
        (fun j => α * (|x j| ^ (p - 2) * x j))
        (fun j => β * |x j| ^ (p - 2) * k j) =
      fun j =>
        ((q - 1) * (α ^ q) ^ (q⁻¹ - 1) * β * α ^ (q - 2)) * k j := by
  have hpow := boyd_powerSum_scaled_dual hpq x hα hxcoord
  have hpair := boyd_weightedPair_scaled_dual_weighted
    (β := β) hpq x k hα hxcoord
  rw [hunit, mul_one] at hpow
  rw [hk, mul_zero] at hpair
  funext j
  unfold realLpGradientDirectional
  rw [hpow, hpair]
  simp only [mul_zero, zero_mul, zero_add]
  rw [boyd_scaled_dualCoordinate_weight hpq hα (hxcoord j)]
  have hw := boyd_weight_mul_inverse_weight (p := p) (hxcoord j)
  calc
    (q - 1) * (α ^ q) ^ (q⁻¹ - 1) *
          (α ^ (q - 2) * |x j| ^ (2 - p)) *
          (β * |x j| ^ (p - 2) * k j) =
      ((q - 1) * (α ^ q) ^ (q⁻¹ - 1) * β * α ^ (q - 2)) *
        (|x j| ^ (p - 2) * |x j| ^ (2 - p)) * k j := by ring
    _ = ((q - 1) * (α ^ q) ^ (q⁻¹ - 1) * β * α ^ (q - 2)) * k j := by
      rw [hw, mul_one]

lemma boyd_scaled_gradient_coefficient {q α : ℝ}
    (hq : q ≠ 0) (hα : 0 < α) :
    (α ^ q) ^ (q⁻¹ - 1) * α ^ (q - 1) = 1 := by
  rw [← Real.rpow_mul hα.le]
  rw [show q * (q⁻¹ - 1) = 1 - q by field_simp]
  rw [← Real.rpow_add hα]
  rw [show (1 - q) + (q - 1) = 0 by ring, Real.rpow_zero]

lemma realLpGradient_scaled_dual_eq {n : ℕ}
    {p q α : ℝ} (hpq : p.HolderConjugate q)
    (x : Fin n → ℝ) (hα : 0 < α) (hxcoord : ∀ j, x j ≠ 0)
    (hunit : realLpPowerSum p x = 1) :
    realLpGradient q (fun j => α * (|x j| ^ (p - 2) * x j)) = x := by
  have hpow := boyd_powerSum_scaled_dual hpq x hα hxcoord
  rw [hunit, mul_one] at hpow
  have hcoeff := boyd_scaled_gradient_coefficient hpq.symm.ne_zero hα
  funext j
  unfold realLpGradient
  rw [hpow]
  rw [boyd_scaled_dualCoordinate_involution hpq hα (hxcoord j)]
  calc
    (α ^ q) ^ (q⁻¹ - 1) * (α ^ (q - 1) * x j) =
        ((α ^ q) ^ (q⁻¹ - 1) * α ^ (q - 1)) * x j := by ring
    _ = x j := by rw [hcoeff, one_mul]

/-- Raw stationary scaling identifies the actual outer input of Boyd's
normalized update. -/
theorem boyd_stationarity_inner_vector {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) =
      fun j => (realLpPowerSum p (boydRectActionCLM A x)) ^ p⁻¹ *
        (|x j| ^ (p - 2) * x j) := by
  let S := realLpPowerSum p (boydRectActionCLM A x)
  have hS : S ≠ 0 := ne_of_gt hSpos
  funext j
  rw [boydRectTransposeActionCLM_apply]
  unfold realLpGradient
  change (∑ i : Fin m, A i j *
      (S ^ (p⁻¹ - 1) *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i))) = _
  calc
    (∑ i : Fin m, A i j *
      (S ^ (p⁻¹ - 1) *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i))) =
      S ^ (p⁻¹ - 1) *
        (∑ i : Fin m, A i j *
          (|boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A x i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = S ^ (p⁻¹ - 1) *
        (S * (|x j| ^ (p - 2) * x j)) := by
      rw [hstationary j]
    _ = S ^ p⁻¹ * (|x j| ^ (p - 2) * x j) := by
      rw [Real.rpow_sub_one hS]
      field_simp

/-- The outer coordinate regularity needed by Lemma 2 follows from positive
stationary scaling and nonzero coordinates of `x`; it is not an extra
assumption. -/
theorem boyd_stationarity_outer_coord_ne {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    ∀ j, boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) j ≠ 0 := by
  intro j
  rw [boyd_stationarity_inner_vector A x hSpos hstationary]
  exact mul_ne_zero
    (ne_of_gt (Real.rpow_pos_of_pos hSpos _))
    (boyd_dualCoordinate_ne_zero (p := p) (hxcoord j))

/-- Raw stationarity gives Boyd's radial eigenidentity `B x = S x`. -/
theorem boyd_stationarity_Bx {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydLemma3B p A x x = fun j =>
      realLpPowerSum p (boydRectActionCLM A x) * x j := by
  funext j
  unfold boydLemma3B
  rw [show (∑ i : Fin m, A i j *
      |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A x i) =
      ∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i) by
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  rw [hstationary j]
  have hw := boyd_weight_mul_inverse_weight (p := p) (hxcoord j)
  calc
    |x j| ^ (2 - p) *
        (realLpPowerSum p (boydRectActionCLM A x) *
          (|x j| ^ (p - 2) * x j)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * |x j| ^ (2 - p)) * x j := by ring
    _ = realLpPowerSum p (boydRectActionCLM A x) * x j := by
      rw [hw, mul_one]

lemma boyd_scale_coefficient {p q S : ℝ}
    (hpq : p.HolderConjugate q) (hS : 0 < S) :
    (q - 1) * ((S ^ p⁻¹) ^ q) ^ (q⁻¹ - 1) *
        ((p - 1) * S ^ (p⁻¹ - 1)) * (S ^ p⁻¹) ^ (q - 2) = S⁻¹ := by
  let α := S ^ p⁻¹
  have hα : 0 < α := Real.rpow_pos_of_pos hS _
  have hpow : S ^ (p⁻¹ - 1) = α / S := by
    simpa [α] using Real.rpow_sub_one (ne_of_gt hS) p⁻¹
  have hαstep : α ^ (q - 2) * α = α ^ (q - 1) := by
    calc
      α ^ (q - 2) * α = α ^ (q - 2) * α ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = α ^ ((q - 2) + 1) := (Real.rpow_add hα (q - 2) 1).symm
      _ = α ^ (q - 1) := by congr 1 <;> ring
  have hgrad := boyd_scaled_gradient_coefficient hpq.symm.ne_zero hα
  have hholder := boyd_holder_sub_one_mul_sub_one hpq
  change (q - 1) * (α ^ q) ^ (q⁻¹ - 1) *
      ((p - 1) * S ^ (p⁻¹ - 1)) * α ^ (q - 2) = S⁻¹
  calc
    (q - 1) * (α ^ q) ^ (q⁻¹ - 1) *
        ((p - 1) * S ^ (p⁻¹ - 1)) * α ^ (q - 2) =
      ((p - 1) * (q - 1)) *
        ((α ^ q) ^ (q⁻¹ - 1) * α ^ (q - 1)) * S⁻¹ := by
      rw [hpow]
      rw [div_eq_mul_inv]
      rw [← hαstep]
      ring
    _ = S⁻¹ := by rw [hholder, hgrad, one_mul, one_mul]

lemma boyd_weight_mul_B {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0) (j : Fin n) :
    |x j| ^ (p - 2) * boydLemma3B p A x h j =
      ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i := by
  unfold boydLemma3B
  have hw := boyd_weight_mul_inverse_weight (p := p) (hxcoord j)
  calc
    |x j| ^ (p - 2) *
        (|x j| ^ (2 - p) *
          ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A h i) =
      (|x j| ^ (p - 2) * |x j| ^ (2 - p)) *
        (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i) := by ring
    _ = ∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i := by rw [hw, one_mul]

lemma boyd_transpose_inner_directional_expansion {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ) (j : Fin n) :
    boydRectTransposeActionCLM A
        (realLpGradientDirectional p (boydRectActionCLM A x)
          (boydRectActionCLM A h)) j =
      (1 - p) * (realLpPowerSum p (boydRectActionCLM A x)) ^ (p⁻¹ - 2) *
          boydWeightedPair p (boydRectActionCLM A x)
            (boydRectActionCLM A x) (boydRectActionCLM A h) *
          (∑ i : Fin m, A i j *
            (|boydRectActionCLM A x i| ^ (p - 2) *
              boydRectActionCLM A x i)) +
        (p - 1) * (realLpPowerSum p (boydRectActionCLM A x)) ^ (p⁻¹ - 1) *
          (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
            boydRectActionCLM A h i) := by
  rw [boydRectTransposeActionCLM_apply]
  unfold realLpGradientDirectional
  simp only
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring

/-- Stationarity simplifies the inner part of the actual derivative to the
weighted projected `B` operator. -/
theorem boyd_inner_directional_eq_weighted_projectedLemma3B
    {m n : ℕ} {p : ℝ}
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydRectTransposeActionCLM A
        (realLpGradientDirectional p (boydRectActionCLM A x)
          (boydRectActionCLM A h)) =
      fun j =>
        (p - 1) *
          (realLpPowerSum p (boydRectActionCLM A x)) ^ (p⁻¹ - 1) *
          |x j| ^ (p - 2) * boydProjectedLemma3B p A x h j := by
  let S := realLpPowerSum p (boydRectActionCLM A x)
  let D := boydWeightedPair p (boydRectActionCLM A x)
    (boydRectActionCLM A x) (boydRectActionCLM A h)
  have hpairB : boydWeightedPair p x x (boydLemma3B p A x h) = D := by
    calc
      boydWeightedPair p x x (boydLemma3B p A x h) =
          boydWeightedPair p x (boydLemma3B p A x h) x :=
        boydWeightedPair_symm p x x (boydLemma3B p A x h)
      _ = ∑ i : Fin m, |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i * boydRectActionCLM A x i :=
        boydWeightedPair_lemma3B p A x h x hxcoord
      _ = D := by
        unfold D boydWeightedPair
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hstationaryS : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
        S * (|x j| ^ (p - 2) * x j) := by
    simpa [S] using hstationary
  have hpow : S ^ (p⁻¹ - 2) * S = S ^ (p⁻¹ - 1) := by
    calc
      S ^ (p⁻¹ - 2) * S = S ^ (p⁻¹ - 2) * S ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = S ^ ((p⁻¹ - 2) + 1) :=
        (Real.rpow_add hSpos (p⁻¹ - 2) 1).symm
      _ = S ^ (p⁻¹ - 1) := by congr 1 <;> ring
  funext j
  rw [boyd_transpose_inner_directional_expansion A x h j]
  change (1 - p) * S ^ (p⁻¹ - 2) * D *
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) +
      (p - 1) * S ^ (p⁻¹ - 1) *
        (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i) =
      (p - 1) * S ^ (p⁻¹ - 1) * |x j| ^ (p - 2) *
        boydProjectedLemma3B p A x h j
  rw [hstationaryS j]
  have hweightB := boyd_weight_mul_B (p := p) A x h hxcoord j
  have hproj : |x j| ^ (p - 2) * boydProjectedLemma3B p A x h j =
      (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
        boydRectActionCLM A h i) -
      D * (|x j| ^ (p - 2) * x j) := by
    unfold boydProjectedLemma3B
    rw [hpairB]
    calc
      |x j| ^ (p - 2) * (boydLemma3B p A x h j - D * x j) =
        |x j| ^ (p - 2) * boydLemma3B p A x h j -
          D * (|x j| ^ (p - 2) * x j) := by ring
      _ = (∑ i : Fin m, A i j * |boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A h i) -
          D * (|x j| ^ (p - 2) * x j) := by rw [hweightB]
  rw [show (p - 1) * S ^ (p⁻¹ - 1) * |x j| ^ (p - 2) *
      boydProjectedLemma3B p A x h j =
      (p - 1) * S ^ (p⁻¹ - 1) *
        (|x j| ^ (p - 2) * boydProjectedLemma3B p A x h j) by ring]
  rw [hproj]
  have hradial :
      (1 - p) * S ^ (p⁻¹ - 2) * D *
          (S * (|x j| ^ (p - 2) * x j)) =
        -(p - 1) * S ^ (p⁻¹ - 1) * D *
          (|x j| ^ (p - 2) * x j) := by
    calc
      (1 - p) * S ^ (p⁻¹ - 2) * D *
          (S * (|x j| ^ (p - 2) * x j)) =
        (1 - p) * (S ^ (p⁻¹ - 2) * S) * D *
          (|x j| ^ (p - 2) * x j) := by ring
      _ = -(p - 1) * S ^ (p⁻¹ - 1) * D *
          (|x j| ^ (p - 2) * x j) := by rw [hpow]; ring
  rw [hradial]
  ring

/-- Whole-space form of Boyd Lemma 2 at a stationary `p`-unit point.  The
actual Fréchet derivative of the normalized update is exactly `S⁻¹ P B`; no
contraction or derivative identity is assumed. -/
theorem boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B
    {m n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydSmoothRectDerivative (p := p) (q := q) A x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  let S := realLpPowerSum p (boydRectActionCLM A x)
  let α := S ^ p⁻¹
  let β := (p - 1) * S ^ (p⁻¹ - 1)
  let k := boydProjectedLemma3B p A x h
  have hα : 0 < α := Real.rpow_pos_of_pos hSpos _
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  have hchain := boydSmoothRectDerivative_apply_directional_chain
    hpq.lt hpq.symm.lt A x h hycoord hzcoord
  have hzvec := boyd_stationarity_inner_vector A x hSpos hstationary
  have hinner := boyd_inner_directional_eq_weighted_projectedLemma3B
    A x h hxcoord hSpos hstationary
  have hktangent : boydWeightedPair p x x k = 0 := by
    exact boydProjectedLemma3B_is_tangent p A x h hxcoord hunit
  have houter := boyd_outer_directional_weighted_tangent
    (α := α) (β := β) hpq x k hα hxcoord hunit hktangent
  have hcoeff := boyd_scale_coefficient hpq hSpos
  calc
    boydSmoothRectDerivative (p := p) (q := q) A x h =
        realLpGradientDirectional q
          (boydRectTransposeActionCLM A
            (realLpGradient p (boydRectActionCLM A x)))
          (boydRectTransposeActionCLM A
            (realLpGradientDirectional p (boydRectActionCLM A x)
              (boydRectActionCLM A h))) := hchain
    _ = realLpGradientDirectional q
          (fun j => α * (|x j| ^ (p - 2) * x j))
          (fun j => β * |x j| ^ (p - 2) * k j) := by
      rw [hzvec, hinner]
    _ = fun j =>
        ((q - 1) * (α ^ q) ^ (q⁻¹ - 1) * β * α ^ (q - 2)) * k j :=
      houter
    _ = fun j => S⁻¹ * k j := by
      funext j
      change ((q - 1) * ((S ^ p⁻¹) ^ q) ^ (q⁻¹ - 1) *
          ((p - 1) * S ^ (p⁻¹ - 1)) * (S ^ p⁻¹) ^ (q - 2)) * k j = _
      rw [hcoeff]
    _ = fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by rfl

/-- The same raw stationarity and unit normalization give the fixed-point
equation for the explicit smooth update; fixedness is derived, not assumed. -/
theorem boydSmoothRectUpdate_eq_of_stationarity
    {m n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    boydSmoothRectUpdate (p := p) (q := q) A x = x := by
  let S := realLpPowerSum p (boydRectActionCLM A x)
  let α := S ^ p⁻¹
  have hα : 0 < α := Real.rpow_pos_of_pos hSpos _
  rw [show boydSmoothRectUpdate (p := p) (q := q) A x =
      realLpGradient q
        (boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A x))) by rfl]
  rw [boyd_stationarity_inner_vector A x hSpos hstationary]
  exact realLpGradient_scaled_dual_eq hpq x hα hxcoord hunit

/-- Literal `RectPNormPair.general` fixedness derived on the corrected smooth
domain.  All `A x` coordinates are required here because that is the current
Lemma-2 differentiability domain; the outer nonzero condition is derived. -/
theorem rect_general_xnext_eq_of_stationarity
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    (RectPNormPair.general hn hpq A).xnext x = x := by
  let i0 : Fin m := ⟨0, hm⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    exact hycoord i0 (by simpa using congrFun hzero i0)
  have hSpos := realLpPowerSum_pos hpq.lt hy
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord j0 (by simpa using congrFun hzero j0)
  rw [rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A x hy hz]
  exact boydSmoothRectUpdate_eq_of_stationarity
    hpq A x hxcoord hunit hSpos hstationary

/-- Terminal whole-space Lemma-2 bridge for the literal source update.  It
identifies the actual Fréchet derivative with `S⁻¹ P B` pointwise on every
direction.  No tangent-only restriction and no target-bearing derivative
hypothesis remains. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
    (hycoord : ∀ i, boydRectActionCLM A x i ≠ 0)
    (hunit : realLpPowerSum p x = 1)
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv ℝ (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  let i0 : Fin m := ⟨0, hm⟩
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    exact hycoord i0 (by simpa using congrFun hzero i0)
  have hSpos := realLpPowerSum_pos hpq.lt hy
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative
    hm hn hpq A x hycoord hzcoord]
  exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B
    hpq A x h hxcoord hycoord hunit hSpos hstationary

end NumStability.Ch15
