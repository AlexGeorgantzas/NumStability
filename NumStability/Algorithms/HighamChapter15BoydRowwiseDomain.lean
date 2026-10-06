-- Algorithms/HighamChapter15BoydRowwiseDomain.lean
--
-- A zero coordinate of `A x` is harmless for Boyd's inner normalized-gradient
-- composition when the corresponding row of `A` is identically zero.  In
-- that case the coordinate remains zero under every perturbation of `x`, so
-- the nonsmooth scalar power at zero is never entered along a nonconstant
-- direction.  This file makes that rowwise source domain explicit and carries
-- it through the literal Algorithm 15.1 update.

import NumStability.Algorithms.HighamChapter15BoydSourceDomain

namespace NumStability.Ch15

open Filter Function Set
open scoped BigOperators Topology

/-- A zero coordinate of `A x` is allowed precisely when its entire row is
zero.  This is the exact composition-level weakening of Boyd's coordinatewise
nonvanishing premise in the nonsmooth range `1 < p < 2`. -/
def IsBoydRowwiseCompositionSmooth {m n : Nat}
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) : Prop :=
  forall i : Fin m,
    boydRectActionCLM A x i ≠ 0 \/ forall j : Fin n, A i j = 0

/-- Unified inner source domain: for `p >= 2` no coordinate restriction is
needed; below two, every zero coordinate must come from a zero row. -/
def IsBoydInnerRowwiseSmoothDomain {m n : Nat} (p : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) : Prop :=
  2 <= p \/ IsBoydRowwiseCompositionSmooth A x

/-- The inner normalized-gradient composition in Boyd's normal map. -/
noncomputable def boydRectInnerNormalMap {m n : Nat} (p : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) : Fin m -> Real :=
  realLpGradient p (boydRectActionCLM A x)

/-- The nonlinear rectangular normal map before the final dual
normalization. -/
noncomputable def boydRectNormalMap {m n : Nat} (p : Real)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real) : Fin n -> Real :=
  boydRectTransposeActionCLM A (boydRectInnerNormalMap p A x)

theorem boydRectActionCLM_apply_eq_zero_of_row_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) (u : Fin n -> Real) (i : Fin m)
    (hrow : forall j : Fin n, A i j = 0) :
    boydRectActionCLM A u i = 0 := by
  rw [boydRectActionCLM_apply]
  simp [hrow]

theorem boydRectInnerNormalMap_coordinateFactor_eq_zero_of_row_zero
    {m n : Nat} (p : Real) (A : Fin m -> Fin n -> Real)
    (u : Fin n -> Real) (i : Fin m)
    (hrow : forall j : Fin n, A i j = 0) :
    |boydRectActionCLM A u i| ^ (p - 2) * boydRectActionCLM A u i = 0 := by
  rw [boydRectActionCLM_apply_eq_zero_of_row_zero A u i hrow]
  simp

/-- The inner composition is genuinely Frechet differentiable on the rowwise
domain, although `realLpGradient p` need not be differentiable as a map on its
whole codomain at the intermediate vector. -/
theorem differentiableAt_boydRectInnerNormalMap_of_rowwise
    {m n : Nat} {p : Real} (hp : 1 < p)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    DifferentiableAt Real (boydRectInnerNormalMap p A) x := by
  have hA : DifferentiableAt Real (boydRectActionCLM A) x :=
    (boydRectActionCLM A).differentiableAt
  have hS : DifferentiableAt Real
      (fun u : Fin n -> Real => realLpPowerSum p (boydRectActionCLM A u)) x :=
    (differentiableAt_realLpPowerSum hp (boydRectActionCLM A x)).comp x hA
  have hSnonzero : realLpPowerSum p (boydRectActionCLM A x) ≠ 0 :=
    ne_of_gt (realLpPowerSum_pos hp hy)
  have hscale : DifferentiableAt Real
      (fun u : Fin n -> Real =>
        (realLpPowerSum p (boydRectActionCLM A u)) ^ (p⁻¹ - 1)) x :=
    hS.rpow_const (Or.inl hSnonzero)
  unfold boydRectInnerNormalMap realLpGradient
  apply differentiableAt_pi''
  intro i
  change DifferentiableAt Real
    (fun u : Fin n -> Real =>
      (realLpPowerSum p (boydRectActionCLM A u)) ^ (p⁻¹ - 1) *
        (|boydRectActionCLM A u i| ^ (p - 2) *
          boydRectActionCLM A u i)) x
  apply hscale.mul
  rcases hrowwise i with hi | hzero
  · have hcoord : DifferentiableAt Real
        (fun u : Fin n -> Real => boydRectActionCLM A u i) x :=
      ((ContinuousLinearMap.proj (R := Real)
        (φ := fun _ : Fin m => Real) i).comp
          (boydRectActionCLM A)).differentiableAt
    have hbase : DifferentiableAt Real
        (fun t : Real => |t| ^ (p - 2) * t)
        (boydRectActionCLM A x i) :=
      (hasDerivAt_abs_rpow_sub_two_mul_self p _ hi).differentiableAt
    simpa [Function.comp_def] using hbase.comp x hcoord
  · have hconst : DifferentiableAt Real
        (fun _ : Fin n -> Real => (0 : Real)) x := differentiableAt_const 0
    convert hconst using 1
    funext u
    exact boydRectInnerNormalMap_coordinateFactor_eq_zero_of_row_zero
      p A u i hzero

/-- Along a line in the source space, every exceptional zero row contributes
the constant-zero scalar factor, so the standard directional formula remains
valid. -/
theorem boydRectInnerNormalMap_line_hasDerivAt_of_rowwise
    {m n : Nat} {p : Real} (hp : 1 < p)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    HasDerivAt
      (fun t : Real => boydRectInnerNormalMap p A (fun j => x j + t * h j))
      (realLpGradientDirectional p (boydRectActionCLM A x)
        (boydRectActionCLM A h)) 0 := by
  let y := boydRectActionCLM A x
  let k := boydRectActionCLM A h
  let S : Real := realLpPowerSum p y
  let D : Real := boydWeightedPair p y y k
  have haction (t : Real) :
      boydRectActionCLM A (fun j => x j + t * h j) =
        fun i => y i + t * k i := by
    funext i
    simp only [y, k, boydRectActionCLM_apply]
    calc
      (∑ j, A i j * (x j + t * h j)) =
          ∑ j, (A i j * x j + t * (A i j * h j)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = (∑ j, A i j * x j) + ∑ j, t * (A i j * h j) :=
        Finset.sum_add_distrib
      _ = (∑ j, A i j * x j) + t * ∑ j, A i j * h j := by
        rw [Finset.mul_sum]
  have hsum : HasDerivAt
      (fun t : Real => realLpPowerSum p (fun i => y i + t * k i))
      (p * D) 0 := by
    unfold realLpPowerSum
    have hterms : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        HasDerivAt (fun t : Real => |y i + t * k i| ^ p)
          (p * |y i| ^ (p - 2) * y i * k i) 0 := by
      intro i _hi
      have hline : HasDerivAt (fun t : Real => y i + t * k i) (k i) 0 := by
        have hline' := (hasDerivAt_const (x := (0 : Real)) (y i)).add
          ((hasDerivAt_id (𝕜 := Real) 0).const_mul (k i))
        convert hline' using 1
        · funext t
          simp only [Pi.add_apply, id_eq]
          ring
        · ring
      have hbase : HasDerivAt (fun u : Real => |u| ^ p)
          (p * |y i| ^ (p - 2) * y i) (y i + 0 * k i) := by
        simpa using hasDerivAt_abs_rpow (y i) hp
      convert hbase.comp 0 hline using 1
    convert HasDerivAt.fun_sum hterms using 1
    unfold D boydWeightedPair
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  have hSpos : 0 < S := by
    simpa [S, y] using realLpPowerSum_pos hp hy
  have hscale := hsum.rpow_const
    (p := p⁻¹ - 1) (Or.inl (by simpa [S] using ne_of_gt hSpos))
  rw [show (fun t : Real => boydRectInnerNormalMap p A
      (fun j => x j + t * h j)) =
      fun t : Real => realLpGradient p (fun i => y i + t * k i) by
    funext t
    simp [boydRectInnerNormalMap, haction]]
  apply hasDerivAt_pi.2
  intro i
  have hline : HasDerivAt (fun t : Real => y i + t * k i) (k i) 0 := by
    have hline' := (hasDerivAt_const (x := (0 : Real)) (y i)).add
      ((hasDerivAt_id (𝕜 := Real) 0).const_mul (k i))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfactor : HasDerivAt
      (fun t : Real => |y i + t * k i| ^ (p - 2) * (y i + t * k i))
      ((p - 1) * |y i| ^ (p - 2) * k i) 0 := by
    rcases hrowwise i with hi | hzero
    · have hbase : HasDerivAt (fun t : Real => |t| ^ (p - 2) * t)
          ((p - 1) * |y i| ^ (p - 2)) (y i + 0 * k i) := by
        simpa using hasDerivAt_abs_rpow_sub_two_mul_self p (y i) (by
          simpa [y] using hi)
      simpa using hbase.comp 0 hline
    · have hyzero : y i = 0 := by
          exact boydRectActionCLM_apply_eq_zero_of_row_zero A x i hzero
      have hkzero : k i = 0 := by
          exact boydRectActionCLM_apply_eq_zero_of_row_zero A h i hzero
      simpa [hyzero, hkzero] using
        (hasDerivAt_const (x := (0 : Real)) (0 : Real))
  have hprod := hscale.mul hfactor
  dsimp [D, S, y, k] at hprod
  convert hprod using 1
  unfold realLpGradientDirectional
  simp only [zero_mul, add_zero]
  unfold boydWeightedPair
  field_simp [ne_of_gt (zero_lt_one.trans hp)]
  ring

/-- Actual Frechet derivative action of the inner normal-map composition on
the rowwise domain. -/
theorem fderiv_boydRectInnerNormalMap_apply_of_rowwise
    {m n : Nat} {p : Real} (hp : 1 < p)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    fderiv Real (boydRectInnerNormalMap p A) x h =
      realLpGradientDirectional p (boydRectActionCLM A x)
        (boydRectActionCLM A h) := by
  have hf :=
    (differentiableAt_boydRectInnerNormalMap_of_rowwise
      hp A x hy hrowwise).hasFDerivAt
  have hline : HasDerivAt (fun t : Real => fun j => x j + t * h j) h 0 := by
    apply hasDerivAt_pi.2
    intro j
    have hline' := (hasDerivAt_const (x := (0 : Real)) (x j)).add
      ((hasDerivAt_id (𝕜 := Real) 0).const_mul (h j))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfbase : HasFDerivAt (boydRectInnerNormalMap p A)
      (fderiv Real (boydRectInnerNormalMap p A) x)
      ((fun t : Real => fun j => x j + t * h j) 0) := by
    simpa using hf
  have hcomp := hfbase.comp_hasDerivAt 0 hline
  exact hcomp.unique
    (boydRectInnerNormalMap_line_hasDerivAt_of_rowwise
      hp A x h hy hrowwise)

/-- Holder conjugacy reverses the side of two: if `p ≤ 2`, then its conjugate
exponent satisfies `2 ≤ q`. -/
theorem holderConjugate_two_le_right_of_left_le_two {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p ≤ 2) : 2 ≤ q := by
  have hp1 : 0 < p - 1 := sub_pos.mpr hpq.lt
  have hprod : 0 ≤ (p - 1) * (q - 2) := by
    rw [boyd_holder_sub_one_mul_sub_two hpq]
    linarith
  have hprod' : 0 ≤ (q - 2) * (p - 1) := by
    simpa [mul_comm] using hprod
  have hqsub : 0 ≤ q - 2 := nonneg_of_mul_nonneg_left hprod' hp1
  linarith

/-- The transpose-composed normal map is differentiable on the rowwise
composition domain. -/
theorem differentiableAt_boydRectNormalMap_of_rowwise
    {m n : Nat} {p : Real} (hp : 1 < p)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    DifferentiableAt Real (boydRectNormalMap p A) x := by
  have hinner := differentiableAt_boydRectInnerNormalMap_of_rowwise
    hp A x hy hrowwise
  simpa [boydRectNormalMap, Function.comp_def] using
    (boydRectTransposeActionCLM A).differentiableAt.comp x hinner

/-- Directional derivative of the transpose-composed normal map on the
rowwise domain. -/
theorem boydRectNormalMap_line_hasDerivAt_of_rowwise
    {m n : Nat} {p : Real} (hp : 1 < p)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    HasDerivAt
      (fun t : Real => boydRectNormalMap p A (fun j => x j + t * h j))
      (boydRectTransposeActionCLM A
        (realLpGradientDirectional p (boydRectActionCLM A x)
          (boydRectActionCLM A h))) 0 := by
  have hinner := boydRectInnerNormalMap_line_hasDerivAt_of_rowwise
    hp A x h hy hrowwise
  have hcomp :=
    (boydRectTransposeActionCLM A).hasFDerivAt.comp_hasDerivAt 0 hinner
  simpa [boydRectNormalMap, Function.comp_def] using hcomp

/-- Actual Fréchet derivative action of the transpose-composed normal map. -/
theorem fderiv_boydRectNormalMap_apply_of_rowwise
    {m n : Nat} {p : Real} (hp : 1 < p)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    fderiv Real (boydRectNormalMap p A) x h =
      boydRectTransposeActionCLM A
        (realLpGradientDirectional p (boydRectActionCLM A x)
          (boydRectActionCLM A h)) := by
  have hf := (differentiableAt_boydRectNormalMap_of_rowwise
    hp A x hy hrowwise).hasFDerivAt
  have hline : HasDerivAt (fun t : Real => fun j => x j + t * h j) h 0 := by
    apply hasDerivAt_pi.2
    intro j
    have hline' := (hasDerivAt_const (x := (0 : Real)) (x j)).add
      ((hasDerivAt_id (𝕜 := Real) 0).const_mul (h j))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hfbase : HasFDerivAt (boydRectNormalMap p A)
      (fderiv Real (boydRectNormalMap p A) x)
      ((fun t : Real => fun j => x j + t * h j) 0) := by
    simpa using hf
  have hcomp := hfbase.comp_hasDerivAt 0 hline
  exact hcomp.unique
    (boydRectNormalMap_line_hasDerivAt_of_rowwise
      hp A x h hy hrowwise)

/-! ## The literal update when `1 < p < 2` -/

/-- Higham, 2nd ed., Chapter 15, Boyd Lemma 2 domain completion: below two,
zero coordinates of `A x` are harmless when their rows are identically zero.
The conjugate outer exponent is at least two, so only nonzeroness of the outer
vector (not of each coordinate) is required. -/
theorem boydSmoothRectUpdate_hasFDerivAt_of_rowwise_lt_two
    {m n : Nat} {p q : Real} (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    HasFDerivAt (boydSmoothRectUpdate (p := p) (q := q) A)
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  apply DifferentiableAt.hasFDerivAt
  have hnormal := differentiableAt_boydRectNormalMap_of_rowwise
    hpq.lt A x hy hrowwise
  have hq2 : 2 ≤ q :=
    holderConjugate_two_le_right_of_left_le_two hpq hp2.le
  have houter := differentiableAt_realLpGradient_of_two_le
    hpq.symm.lt hq2 (boydRectNormalMap p A x) (by
      simpa [boydRectNormalMap, boydRectInnerNormalMap] using hz)
  simpa [boydSmoothRectUpdate, boydRectNormalMap,
    boydRectInnerNormalMap, Function.comp_def] using houter.comp x hnormal

/-- The actual `RectPNormPair.general.xnext` has the rowwise-domain derivative
in the nonsmooth inner range. -/
theorem rect_general_xnext_hasFDerivAt_boyd_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  let W := boydSmoothRectUpdate (p := p) (q := q) A
  let L := boydSmoothRectDerivative (p := p) (q := q) A x
  have hW : HasFDerivAt W L x := by
    simpa [W, L] using boydSmoothRectUpdate_hasFDerivAt_of_rowwise_lt_two
      hpq hp2 A x hy hz hrowwise
  have hAcont : ContinuousAt (boydRectActionCLM A) x :=
    (boydRectActionCLM A).continuous.continuousAt
  have hzcont : ContinuousAt
      (fun u : Fin n -> Real => boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A u))) x := by
    simpa [boydRectNormalMap, boydRectInnerNormalMap] using
      (differentiableAt_boydRectNormalMap_of_rowwise
        hpq.lt A x hy hrowwise).continuousAt
  have hey : ∀ᶠ u in nhds x, boydRectActionCLM A u ≠ 0 :=
    hAcont.eventually_ne hy
  have hez : ∀ᶠ u in nhds x,
      boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A u)) ≠ 0 :=
    hzcont.eventually_ne hz
  have heq : (RectPNormPair.general hn hpq A).xnext =ᶠ[nhds x] W := by
    filter_upwards [hey, hez] with u hyu hzu
    exact rect_general_xnext_eq_boydSmoothRectUpdate hn hpq A u hyu hzu
  exact hW.congr_of_eventuallyEq heq

/-- Identification of the actual update's Fréchet derivative on the rowwise
`p < 2` branch. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x :=
  (rect_general_xnext_hasFDerivAt_boyd_of_rowwise_lt_two
    hn hpq hp2 A x hy hz hrowwise).fderiv

/-- Unified genuine Fréchet-derivative endpoint for the literal update.  The
inner map uses the whole-space `p ≥ 2` theorem or the zero-row theorem below
two; the coordinate premise on the outer input is precisely what is needed
when the conjugate exponent itself lies below two. -/
theorem rect_general_xnext_hasFDerivAt_boyd_rowwise_source_domain
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hzcoord : ∀ j, boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x) :
    HasFDerivAt (RectPNormPair.general hn hpq A).xnext
      (boydSmoothRectDerivative (p := p) (q := q) A x) x := by
  by_cases hp2 : 2 ≤ p
  · exact rect_general_xnext_hasFDerivAt_boyd_of_two_le
      hn hpq hp2 A x hy hzcoord
  · have hrowwise : IsBoydRowwiseCompositionSmooth A x :=
      Or.resolve_left hsmooth hp2
    have hplt : p < 2 := lt_of_not_ge hp2
    let j0 : Fin n := ⟨0, hn⟩
    have hz : boydRectTransposeActionCLM A
        (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
      intro hzero
      exact hzcoord j0 (by simpa using congrFun hzero j0)
    exact rect_general_xnext_hasFDerivAt_boyd_of_rowwise_lt_two
      hn hpq hplt A x hy hz hrowwise

/-- Unified identification of the actual update derivative with the explicit
smooth-composition derivative. -/
theorem rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_rowwise_source_domain
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hzcoord : ∀ j, boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x =
      boydSmoothRectDerivative (p := p) (q := q) A x :=
  (rect_general_xnext_hasFDerivAt_boyd_rowwise_source_domain
    hn hpq A x hy hzcoord hsmooth).fderiv

/-- Exact nested directional chain for the rowwise `p < 2` branch. -/
theorem boydSmoothRectDerivative_apply_directional_chain_of_rowwise_lt_two
    {m n : Nat} {p q : Real} (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hy : boydRectActionCLM A x ≠ 0)
    (hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x) :
    boydSmoothRectDerivative (p := p) (q := q) A x h =
      realLpGradientDirectional q
        (boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A x)))
        (boydRectTransposeActionCLM A
          (realLpGradientDirectional p (boydRectActionCLM A x)
            (boydRectActionCLM A h))) := by
  have hq2 : 2 ≤ q :=
    holderConjugate_two_le_right_of_left_le_two hpq hp2.le
  have hline : HasDerivAt
      (fun t : Real => fun i => x i + t * h i) h 0 := by
    apply hasDerivAt_pi.2
    intro i
    have hline' := (hasDerivAt_const (x := (0 : Real)) (x i)).add
      ((hasDerivAt_id (𝕜 := Real) 0).const_mul (h i))
    convert hline' using 1
    · funext t
      simp only [Pi.add_apply, id_eq]
      ring
    · ring
  have hnormalLine := boydRectNormalMap_line_hasDerivAt_of_rowwise
    hpq.lt A x h hy hrowwise
  have hqF := (differentiableAt_realLpGradient_of_two_le
    hpq.symm.lt hq2
    (boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x))) hz).hasFDerivAt
  have hqFbase : HasFDerivAt (realLpGradient q)
      (fderiv Real (realLpGradient q)
        (boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A x))))
      ((boydRectNormalMap p A ∘
        (fun t : Real => fun i => x i + t * h i)) 0) := by
    simpa [boydRectNormalMap, boydRectInnerNormalMap,
      Function.comp_def] using hqF
  have hqLine := hqFbase.comp_hasDerivAt 0 hnormalLine
  rw [fderiv_realLpGradient_apply_of_two_le hpq.symm.lt hq2
    (boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)))
    (boydRectTransposeActionCLM A
      (realLpGradientDirectional p (boydRectActionCLM A x)
        (boydRectActionCLM A h))) hz] at hqLine
  have hWF := boydSmoothRectUpdate_hasFDerivAt_of_rowwise_lt_two
    hpq hp2 A x hy hz hrowwise
  have hWFbase : HasFDerivAt (boydSmoothRectUpdate (p := p) (q := q) A)
      (boydSmoothRectDerivative (p := p) (q := q) A x)
      ((fun t : Real => fun i => x i + t * h i) 0) := by
    simpa using hWF
  have hactual := hWFbase.comp_hasDerivAt 0 hline
  exact hactual.unique hqLine

/-- Higham, 2nd ed., Chapter 15, Boyd Lemma 2: on the rowwise source domain
in the range `1 < p < 2`, the explicit derivative is the inverse source-power
scale times the projected Lemma-3 operator. -/
theorem boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hxcoord : ∀ j, x j ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x)
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
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    rw [hzero] at hSpos
    simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  let j0 : Fin n := ⟨0, hn⟩
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord j0 (by simpa using congrFun hzero j0)
  have hchain :=
    boydSmoothRectDerivative_apply_directional_chain_of_rowwise_lt_two
      hpq hp2 A x h hy hz hrowwise
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

/-- Terminal actual-`fderiv = S⁻¹ P B` bridge on the `p < 2` zero-row
domain. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q) (hp2 : p < 2)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hxcoord : ∀ j, x j ≠ 0)
    (hrowwise : IsBoydRowwiseCompositionSmooth A x)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  have hy : boydRectActionCLM A x ≠ 0 := by
    intro hzero
    rw [hzero] at hSpos
    simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
  have hzcoord := boyd_stationarity_outer_coord_ne
    A x hxcoord hSpos hstationary
  let j0 : Fin n := ⟨0, hn⟩
  have hz : boydRectTransposeActionCLM A
      (realLpGradient p (boydRectActionCLM A x)) ≠ 0 := by
    intro hzero
    exact hzcoord j0 (by simpa using congrFun hzero j0)
  rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_rowwise_lt_two
    hn hpq hp2 A x hy hz hrowwise]
  exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
    hn hpq hp2 A x h hxcoord hrowwise hunit hSpos hstationary

/-- Unified terminal bridge for Higham Chapter 15: zero rows are admitted in
the nonsmooth inner range, while the existing whole-space theorem supplies the
`2 ≤ p` branch. -/
theorem rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_rowwise_source_domain
    {m n : Nat} (hn : 0 < n) {p q : Real}
    (hpq : p.HolderConjugate q)
    (A : Fin m -> Fin n -> Real) (x h : Fin n -> Real)
    (hxcoord : ∀ j, x j ≠ 0)
    (hsmooth : IsBoydInnerRowwiseSmoothDomain p A x)
    (hunit : realLpPowerSum p x = 1)
    (hSpos : 0 < realLpPowerSum p (boydRectActionCLM A x))
    (hstationary : ∀ j,
      (∑ i : Fin m, A i j *
        (|boydRectActionCLM A x i| ^ (p - 2) *
          boydRectActionCLM A x i)) =
      realLpPowerSum p (boydRectActionCLM A x) *
        (|x j| ^ (p - 2) * x j)) :
    fderiv Real (RectPNormPair.general hn hpq A).xnext x h =
      fun j => (realLpPowerSum p (boydRectActionCLM A x))⁻¹ *
        boydProjectedLemma3B p A x h j := by
  by_cases hp2 : 2 ≤ p
  · have hy : boydRectActionCLM A x ≠ 0 := by
      intro hzero
      rw [hzero] at hSpos
      simp [realLpPowerSum, Real.zero_rpow (ne_of_gt hpq.pos)] at hSpos
    have hzcoord := boyd_stationarity_outer_coord_ne
      A x hxcoord hSpos hstationary
    rw [rect_general_fderiv_xnext_eq_boydSmoothRectDerivative_of_two_le
      hn hpq hp2 A x hy hzcoord]
    exact boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_two_le
      hpq hp2 A x h hxcoord hunit hSpos hstationary
  · have hrowwise : IsBoydRowwiseCompositionSmooth A x :=
      Or.resolve_left hsmooth hp2
    exact
      rect_general_fderiv_xnext_apply_eq_inv_projectedLemma3B_of_rowwise_lt_two
        hn hpq (lt_of_not_ge hp2) A x h hxcoord hrowwise
          hunit hSpos hstationary

end NumStability.Ch15
