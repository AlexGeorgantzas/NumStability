import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Extend
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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydDomain
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Differentiation BoydDomain

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter15BoydSourceDomain` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

namespace Ch15

open Filter Function Set

open scoped BigOperators Topology

/-- For `p >= 2`, the normalized finite-dimensional `l^p` gradient is
Fréchet differentiable at every nonzero vector, even if some coordinates
vanish. -/
theorem differentiableAt_realLpGradient_of_two_le {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : 2 ≤ p) (x : Fin n → ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ (realLpGradient p) x := by
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
  have hcoord : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) i).differentiableAt
  have hfactor : DifferentiableAt ℝ
      (fun t : ℝ => |t| ^ (p - 2) * t) (x i) :=
    (hasDerivAt_abs_rpow_sub_two_mul_self_of_two_le p (x i) hp2).differentiableAt
  have hcomp := hfactor.comp x hcoord
  simpa [Function.comp_def] using hscale.mul hcomp

/-- Directional formula for the normalized gradient on the completed
`p >= 2` domain. -/
theorem realLpGradient_line_hasDerivAt_of_two_le {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : 2 ≤ p) (x h : Fin n → ℝ) (hx : x ≠ 0) :
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
    simpa using hasDerivAt_abs_rpow_sub_two_mul_self_of_two_le p (x i) hp2
  have hcoord := hbase.comp 0 hline
  have hprod := hscale.mul hcoord
  convert hprod using 1
  unfold realLpGradientDirectional
  simp only [Function.comp_apply, zero_mul, add_zero]
  unfold D
  field_simp [ne_of_gt (zero_lt_one.trans hp)]
  ring

/-- The actual Fréchet derivative action on the completed `p >= 2` domain. -/
theorem fderiv_realLpGradient_apply_of_two_le {n : ℕ} {p : ℝ}
    (hp : 1 < p) (hp2 : 2 ≤ p) (x h : Fin n → ℝ) (hx : x ≠ 0) :
    fderiv ℝ (realLpGradient p) x h =
      realLpGradientDirectional p x h := by
  have hf := (differentiableAt_realLpGradient_of_two_le hp hp2 x hx).hasFDerivAt
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
  have hexpl := realLpGradient_line_hasDerivAt_of_two_le hp hp2 x h hx
  exact hcomp.unique hexpl

/-- Boyd's explicit normalized-gradient composition is differentiable when
the inner exponent is at least two, even if `A x` has zero coordinates. -/
theorem boydSmoothRectUpdate_hasFDerivAt_of_two_le {m n : ℕ}
    {p q : ℝ} (hp : 1 < p) (hp2 : 2 ≤ p) (hq : 1 < q)
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ)
    (hy : boydRectActionCLM A x ≠ 0)
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
    (differentiableAt_realLpGradient_of_two_le hp hp2
      (boydRectActionCLM A x) hy).comp x hA
  have hAT : DifferentiableAt ℝ
      (fun u : Fin n → ℝ =>
        boydRectTransposeActionCLM A
          (realLpGradient p (boydRectActionCLM A u))) x :=
    (boydRectTransposeActionCLM A).differentiableAt.comp x hgp
  exact (differentiableAt_realLpGradient_of_all_ne hq _ hzcoord).comp x hAT

/-- Exact nested directional chain for the smooth update on the `p >= 2`
branch. -/
theorem boydSmoothRectDerivative_apply_directional_chain_of_two_le
    {m n : ℕ} {p q : ℝ} (hp : 1 < p) (hp2 : 2 ≤ p) (hq : 1 < q)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hy : boydRectActionCLM A x ≠ 0)
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
    (differentiableAt_realLpGradient_of_two_le hp hp2
      (boydRectActionCLM A x) hy).hasFDerivAt
  have hpFbase : HasFDerivAt (realLpGradient p)
      (fderiv ℝ (realLpGradient p) (boydRectActionCLM A x))
      ((boydRectActionCLM A ∘ fun t : ℝ =>
        (fun i => x i + t * h i)) 0) := by
    simpa [Function.comp_def] using hpF
  have hpLine := hpFbase.comp_hasDerivAt 0 hAline
  rw [fderiv_realLpGradient_apply_of_two_le hp hp2
    (boydRectActionCLM A x) (boydRectActionCLM A h) hy] at hpLine
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
  have hWF := boydSmoothRectUpdate_hasFDerivAt_of_two_le
    hp hp2 hq A x hy hzcoord
  have hWFbase : HasFDerivAt (boydSmoothRectUpdate (p := p) (q := q) A)
      (boydSmoothRectDerivative (p := p) (q := q) A x)
      ((fun t : ℝ => (fun i => x i + t * h i)) 0) := by
    simpa using hWF
  have hactual := hWFbase.comp_hasDerivAt 0 hline
  exact hactual.unique hqLine

/-- Whole-space Boyd-Lemma-2 formula on the completed `p >= 2` branch. -/
theorem boydSmoothRectDerivative_apply_eq_inv_projectedLemma3B_of_two_le
    {m n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : 2 ≤ p)
    (A : Fin m → Fin n → ℝ) (x h : Fin n → ℝ)
    (hxcoord : ∀ j, x j ≠ 0)
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
  have hchain := boydSmoothRectDerivative_apply_directional_chain_of_two_le
    hpq.lt hp2 hpq.symm.lt A x h hy hzcoord
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
