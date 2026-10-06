import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Sequences
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Differentiation BoydLocal

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceLocal` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

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

end Ch15
end NumStability
