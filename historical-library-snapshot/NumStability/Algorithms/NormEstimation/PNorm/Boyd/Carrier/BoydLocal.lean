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
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# NumStability Algorithms NormEstimation PNorm Boyd Carrier BoydLocal

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

end Ch15
end NumStability
