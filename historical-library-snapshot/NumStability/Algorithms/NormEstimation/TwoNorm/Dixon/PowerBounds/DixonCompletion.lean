import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonProbability
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic

/-!
# NumStability Algorithms NormEstimation TwoNorm Dixon PowerBounds DixonCompletion

Canonical destination for material split out of
`NumStability.Algorithms.Ch15DixonClosure` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory Set

open scoped BigOperators Matrix MatrixOrder RealInnerProductSpace

set_option maxHeartbeats 800000

theorem ch15Closure_quadForm_power_lower_of_unit_eigenvector {n : ℕ}
    (M : Fin n → Fin n → ℝ) (hM : IsSymmetricFiniteMatrix M)
    (k : ℕ) (hPowPSD : finitePSD (matPow n M k))
    (v : Fin n → ℝ) (lam : ℝ)
    (hvnorm : ∑ i : Fin n, v i ^ 2 = 1)
    (hEig : matMulVec n M v = fun i => lam * v i)
    (x : Fin n → ℝ) :
    lam ^ k * (∑ i : Fin n, v i * x i) ^ 2 ≤
      finiteQuadraticForm (matPow n M k) x := by
  let H : Fin n → Fin n → ℝ := matPow n M k
  let α : ℝ := ∑ i : Fin n, v i * x i
  let y : Fin n → ℝ := fun i => x i - α * v i
  have hHsym : IsSymmetricFiniteMatrix H := by
    simpa [H] using ch15Closure_matPow_symmetric M hM k
  have hHeig : finiteMatVec H v = fun i => lam ^ k * v i := by
    simpa [H, finiteMatVec, matMulVec] using
      ch15Closure_matPow_mulVec_eigenvector M v lam hEig k
  have hyorth : (∑ i : Fin n, v i * y i) = 0 := by
    calc
      (∑ i : Fin n, v i * y i) =
          (∑ i : Fin n, v i * x i) - α * ∑ i : Fin n, v i ^ 2 := by
        simp only [y, Finset.mul_sum]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hvnorm]; simp [α]
  have hvHy : (∑ i : Fin n, v i * finiteMatVec H y i) = 0 := by
    rw [finiteVecInnerProduct_finiteMatVec_left_eq_right_of_symmetric H hHsym]
    simp_rw [hHeig]
    calc
      (∑ i : Fin n, (lam ^ k * v i) * y i) =
          lam ^ k * ∑ i : Fin n, v i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hyorth, mul_zero]
  have hyHv : (∑ i : Fin n, y i * finiteMatVec H v i) = 0 := by
    simp_rw [hHeig]
    calc
      (∑ i : Fin n, y i * (lam ^ k * v i)) =
          lam ^ k * ∑ i : Fin n, v i * y i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hyorth, mul_zero]
  have hqv : finiteQuadraticForm H v = lam ^ k := by
    unfold finiteQuadraticForm
    simp_rw [hHeig]
    calc
      (∑ i : Fin n, v i * (lam ^ k * v i)) =
          lam ^ k * ∑ i : Fin n, v i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = lam ^ k := by rw [hvnorm, mul_one]
  have hxdecomp : x = fun i => α * v i + y i := by
    funext i
    simp [y]
  have hscale : finiteMatVec H (fun i => α * v i) =
      fun i => α * finiteMatVec H v i := by
    funext i
    unfold finiteMatVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hqexpand :
      finiteQuadraticForm H x =
        α ^ 2 * finiteQuadraticForm H v +
          α * (∑ i : Fin n, v i * finiteMatVec H y i) +
          α * (∑ i : Fin n, y i * finiteMatVec H v i) +
          finiteQuadraticForm H y := by
    rw [hxdecomp]
    unfold finiteQuadraticForm
    rw [finiteMatVec_add, hscale]
    calc
      (∑ i : Fin n,
          (α * v i + y i) *
            (α * finiteMatVec H v i + finiteMatVec H y i)) =
          ∑ i : Fin n,
            (α ^ 2 * (v i * finiteMatVec H v i) +
              α * (v i * finiteMatVec H y i) +
              α * (y i * finiteMatVec H v i) +
              y i * finiteMatVec H y i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = α ^ 2 * (∑ i : Fin n, v i * finiteMatVec H v i) +
          α * (∑ i : Fin n, v i * finiteMatVec H y i) +
          α * (∑ i : Fin n, y i * finiteMatVec H v i) +
          ∑ i : Fin n, y i * finiteMatVec H y i := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have hqy : 0 ≤ finiteQuadraticForm H y := by
    simpa [H] using hPowPSD y
  rw [show ∑ i : Fin n, v i * x i = α from rfl]
  rw [show finiteQuadraticForm (matPow n M k) x = finiteQuadraticForm H x from rfl]
  rw [hqexpand, hqv, hvHy, hyHv]
  nlinarith

theorem ch15Closure_exists_dixon_sphere_direction_power_lower
    (d k : ℕ) (B : Fin (d + 1) → Fin (d + 1) → ℝ) :
    ∃ u : OrthogonalSphere (d + 1),
      ∀ x : OrthogonalSphere (d + 1),
        opNorm2 B ^ (2 * k) * (ch15SphereInner d u x) ^ 2 ≤
          finiteQuadraticForm
            (matPow (d + 1)
              (matMul (d + 1) (matTranspose B) B) k)
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) := by
  obtain ⟨v, hv, hEig⟩ := ch15Closure_exists_gram_opNorm2_sq_unit_eigenvector d B
  let u := ch15Closure_unitSphereOfFiniteVec d v hv
  refine ⟨u, fun x => ?_⟩
  let xv : Fin (d + 1) → ℝ :=
    WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))
  have hlower := ch15Closure_quadForm_power_lower_of_unit_eigenvector
    (matMul (d + 1) (matTranspose B) B)
    (ch15Closure_gram_symmetric B) k
    (ch15Closure_gram_pow_finitePSD B k) v (opNorm2 B ^ 2) hv hEig xv
  rw [← pow_mul] at hlower
  simpa [u, xv, ch15Closure_ch15SphereInner_unitSphereOfFiniteVec] using hlower

/-- Repeated operator-norm composition for repository-native matrix powers. -/
theorem ch15Closure_opNorm2Le_matPow {n : ℕ}
    (M : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hM : opNorm2Le M c) (k : ℕ) :
    opNorm2Le (matPow n M k) (c ^ k) := by
  induction k with
  | zero =>
      intro x
      rw [matPow_zero, matMulVec_id]
      simp
  | succ k ih =>
      simpa [matPow_succ, pow_succ'] using
        opNorm2Le_matMul n M (matPow n M k) c (c ^ k) hc hM ih

/-- The always-valid left side of Dixon's inequality for every positive
power: on the unit sphere,
`xᵀ(BᵀB)^k x ≤ ‖B‖₂^(2k)`. -/
theorem ch15Closure_dixon_left_power_inequality
    (d k : ℕ) (B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (x : OrthogonalSphere (d + 1)) :
    finiteQuadraticForm
        (matPow (d + 1) (matMul (d + 1) (matTranspose B) B) k)
        (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) ≤
      opNorm2 B ^ (2 * k) := by
  let xv : Fin (d + 1) → ℝ :=
    WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))
  let G : Fin (d + 1) → Fin (d + 1) → ℝ :=
    matMul (d + 1) (matTranspose B) B
  let H : Fin (d + 1) → Fin (d + 1) → ℝ := matPow (d + 1) G k
  have hBt : opNorm2Le (matTranspose B) (opNorm2 B) :=
    opNorm2Le_transpose B (opNorm2_nonneg B) (opNorm2Le_opNorm2 B)
  have hG : opNorm2Le G (opNorm2 B ^ 2) := by
    simpa [G, pow_two] using
      opNorm2Le_matMul (d + 1) (matTranspose B) B
        (opNorm2 B) (opNorm2 B) (opNorm2_nonneg B) hBt
        (opNorm2Le_opNorm2 B)
  have hH : opNorm2Le H ((opNorm2 B ^ 2) ^ k) := by
    exact ch15Closure_opNorm2Le_matPow G (opNorm2 B ^ 2)
      (sq_nonneg (opNorm2 B)) hG k
  have hxnorm : ‖WithLp.toLp 2 xv‖ = 1 := by
    simpa [xv, Metric.mem_sphere, dist_zero_right] using x.property
  have hxsq : vecNorm2Sq xv = 1 := by
    have hsq : ‖WithLp.toLp 2 xv‖ ^ 2 = 1 := by rw [hxnorm]; norm_num
    rw [EuclideanSpace.norm_sq_eq] at hsq
    simpa [vecNorm2Sq, Real.norm_eq_abs, sq_abs] using hsq
  have habs := abs_vecInnerProduct_matMulVec_le_of_opNorm2Le H hH xv
  have hqnonneg : 0 ≤ finiteQuadraticForm H xv := by
    simpa [H, G] using ch15Closure_gram_pow_finitePSD B k xv
  have hqle : finiteQuadraticForm H xv ≤ (opNorm2 B ^ 2) ^ k := by
    unfold finiteQuadraticForm finiteMatVec at hqnonneg ⊢
    simpa [matMulVec, hxsq, abs_of_nonneg hqnonneg] using habs
  rw [show finiteQuadraticForm
      (matPow (d + 1) (matMul (d + 1) (matTranspose B) B) k) xv =
      finiteQuadraticForm H xv from rfl]
  rw [← pow_mul] at hqle
  exact hqle

end NumStability
