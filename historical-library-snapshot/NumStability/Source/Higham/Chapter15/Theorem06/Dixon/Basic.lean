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
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.DixonCompletion
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Probability.DixonProbability
import NumStability.Analysis.TestMatrices.Orthogonal.OrthogonalCoordinates
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic

/-!
# Chapter15 Theorem06 Dixon Basic

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

theorem ch15Closure_dixon_failure_probability_le
    (d k : ℕ) (hk : 0 < k)
    (B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (θ : ℝ) (hθ : 1 < θ) :
    standardGaussianDirectionMeasure d
        {x : OrthogonalSphere (d + 1) |
          (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
            opNorm2 B ^ (2 * k)} ≤
      ENNReal.ofReal (((4 : ℝ) / 5) * Real.sqrt (d + 1) *
        θ ^ (-(k : ℝ) / 2 : ℝ)) := by
  obtain ⟨u, hlower⟩ := ch15Closure_exists_dixon_sphere_direction_power_lower d k B
  let s : ℝ := θ ^ k
  let δ : ℝ := s⁻¹
  have hsone : 1 < s := by
    exact one_lt_pow₀ hθ (Nat.ne_of_gt hk)
  have hspos : 0 < s := lt_trans zero_lt_one hsone
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hδpos : 0 < δ := inv_pos.mpr hspos
  have hδlt : δ < 1 := (inv_lt_one₀ hspos).2 hsone
  have hsδ : s * δ = 1 := by simp [δ, hsne]
  have hsδsq : s ^ 2 * δ ^ 2 = 1 := by
    rw [← mul_pow, hsδ, one_pow]
  have hsubset :
      {x : OrthogonalSphere (d + 1) |
        (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
            opNorm2 B ^ (2 * k)} ⊆
        {x | |ch15SphereInner d u x| ≤ δ} := by
    intro x hx
    change s ^ 2 *
          finiteQuadraticForm
            (matPow (d + 1)
              (matMul (d + 1) (matTranspose B) B) k)
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
        opNorm2 B ^ (2 * k) at hx
    by_cases hopzero : opNorm2 B = 0
    · have hqnonneg := ch15Closure_gram_pow_finitePSD B k
        (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))
      have hrhs : opNorm2 B ^ (2 * k) = 0 := by
        rw [hopzero, zero_pow]
        omega
      rw [hrhs] at hx
      nlinarith [sq_nonneg s]
    · by_contra hnot
      have hnot' : δ < |ch15SphereInner d u x| := lt_of_not_ge hnot
      have hrpos : 0 < opNorm2 B :=
        lt_of_le_of_ne (opNorm2_nonneg B) (Ne.symm hopzero)
      have hrpowpos : 0 < opNorm2 B ^ (2 * k) := pow_pos hrpos _
      have habssq : δ ^ 2 < (ch15SphereInner d u x) ^ 2 := by
        have h := (sq_lt_sq₀ hδpos.le (abs_nonneg _)).2 hnot'
        simpa [sq_abs] using h
      have hscaled :
          opNorm2 B ^ (2 * k) * δ ^ 2 <
            opNorm2 B ^ (2 * k) * (ch15SphereInner d u x) ^ 2 :=
        mul_lt_mul_of_pos_left habssq hrpowpos
      have hqgt :
          opNorm2 B ^ (2 * k) * δ ^ 2 <
            finiteQuadraticForm
              (matPow (d + 1)
                (matMul (d + 1) (matTranspose B) B) k)
              (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) :=
        hscaled.trans_le (hlower x)
      have hmul := mul_lt_mul_of_pos_left hqgt (sq_pos_of_pos hspos)
      have hleft :
          s ^ 2 * (opNorm2 B ^ (2 * k) * δ ^ 2) =
            opNorm2 B ^ (2 * k) := by
        calc
          s ^ 2 * (opNorm2 B ^ (2 * k) * δ ^ 2) =
              opNorm2 B ^ (2 * k) * (s ^ 2 * δ ^ 2) := by ring
          _ = opNorm2 B ^ (2 * k) := by rw [hsδsq, mul_one]
      rw [hleft] at hmul
      exact (not_lt_of_ge (le_of_lt hx)) hmul
  calc
    standardGaussianDirectionMeasure d
        {x : OrthogonalSphere (d + 1) |
          (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
            opNorm2 B ^ (2 * k)} ≤
        standardGaussianDirectionMeasure d
          {x | |ch15SphereInner d u x| ≤ δ} := measure_mono hsubset
    _ ≤ ENNReal.ofReal (((4 : ℝ) / 5) * Real.sqrt (d + 1) * Real.sqrt δ) :=
      ch15_standardGaussianDirection_inner_dixon_bound d u δ hδpos.le hδlt
    _ = ENNReal.ofReal (((4 : ℝ) / 5) * Real.sqrt (d + 1) *
        θ ^ (-(k : ℝ) / 2 : ℝ)) := by
      have hsqrt : Real.sqrt δ = θ ^ (-(k : ℝ) / 2 : ℝ) := by
        simpa [δ, s] using ch15Closure_sqrt_inv_pow_eq_rpow_neg_half θ
          (le_of_lt (lt_trans zero_lt_one hθ)) k
      rw [hsqrt]

theorem ch15Closure_dixon_success_probability_ge
    (d k : ℕ) (hk : 0 < k)
    (B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (θ : ℝ) (hθ : 1 < θ) :
    ENNReal.ofReal
        (1 - ((4 : ℝ) / 5) * Real.sqrt (d + 1) *
          θ ^ (-(k : ℝ) / 2 : ℝ)) ≤
      standardGaussianDirectionMeasure d
        {x : OrthogonalSphere (d + 1) |
          opNorm2 B ^ (2 * k) ≤
            (θ ^ k) ^ 2 *
              finiteQuadraticForm
                (matPow (d + 1)
                  (matMul (d + 1) (matTranspose B) B) k)
                (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))} := by
  let Good : Set (OrthogonalSphere (d + 1)) :=
    {x | opNorm2 B ^ (2 * k) ≤
      (θ ^ k) ^ 2 *
        finiteQuadraticForm
          (matPow (d + 1)
            (matMul (d + 1) (matTranspose B) B) k)
          (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1))))}
  let Bad : Set (OrthogonalSphere (d + 1)) :=
    {x | (θ ^ k) ^ 2 *
        finiteQuadraticForm
          (matPow (d + 1)
            (matMul (d + 1) (matTranspose B) B) k)
          (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) <
      opNorm2 B ^ (2 * k)}
  let c : ℝ := ((4 : ℝ) / 5) * Real.sqrt (d + 1) *
    θ ^ (-(k : ℝ) / 2 : ℝ)
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hBad : standardGaussianDirectionMeasure d Bad ≤ ENNReal.ofReal c := by
    simpa [Bad, c] using ch15Closure_dixon_failure_probability_le d k hk B θ hθ
  have hGoodMeas : MeasurableSet Good := by
    dsimp [Good]
    apply measurableSet_le
    · exact measurable_const
    · unfold finiteQuadraticForm finiteMatVec
      fun_prop
  have hcompl : Goodᶜ = Bad := by
    ext x
    simp [Good, Bad, not_le]
  have hBadMeas : MeasurableSet Bad := by
    rw [← hcompl]
    exact hGoodMeas.compl
  have hGoodEq : Good = Badᶜ := by
    rw [← hcompl]
    simp
  change ENNReal.ofReal (1 - c) ≤ standardGaussianDirectionMeasure d Good
  rw [ENNReal.ofReal_sub 1 hc]
  rw [hGoodEq, prob_compl_eq_one_sub hBadMeas]
  simpa using tsub_le_tsub_left hBad 1

/-- **Higham Theorem 15.6 (Dixon), closed source-shaped endpoint.**

For a certified inverse `B = A⁻¹`, a positive integer `k`, and `θ > 1`,
the actual inverse Gram matrix is `BᵀB = (AAᵀ)⁻¹`; the left powered
inequality holds for every unit vector; and the right powered inequality
holds for a uniform sphere point with probability at least
`1 - 0.8 * θ^(-k/2) * sqrt n`.  The powered event is exactly the
nonnegative `2k`-th-power form of display (15.7):
`‖B‖₂ ≤ θ * (xᵀ(BᵀB)^k x)^(1/(2k))`. -/
theorem higham15_6_dixon_closed
    (d k : ℕ) (hk : 0 < k)
    (A B : Fin (d + 1) → Fin (d + 1) → ℝ)
    (hR : IsRightInverse (d + 1) A B)
    (hL : IsLeftInverse (d + 1) A B)
    (θ : ℝ) (hθ : 1 < θ) :
    IsInverse (d + 1)
        (matMul (d + 1) A (matTranspose A))
        (matMul (d + 1) (matTranspose B) B) ∧
      (∀ x : OrthogonalSphere (d + 1),
        finiteQuadraticForm
            (matPow (d + 1)
              (matMul (d + 1) (matTranspose B) B) k)
            (WithLp.ofLp (x : EuclideanSpace ℝ (Fin (d + 1)))) ≤
          opNorm2 B ^ (2 * k)) ∧
      ENNReal.ofReal
          (1 - ((4 : ℝ) / 5) * Real.sqrt (d + 1) *
            θ ^ (-(k : ℝ) / 2 : ℝ)) ≤
        standardGaussianDirectionMeasure d
          {x : OrthogonalSphere (d + 1) |
            opNorm2 B ^ (2 * k) ≤
              (θ ^ k) ^ 2 *
                finiteQuadraticForm
                  (matPow (d + 1)
                    (matMul (d + 1) (matTranspose B) B) k)
                  (WithLp.ofLp
                    (x : EuclideanSpace ℝ (Fin (d + 1))))} := by
  refine ⟨Ch15.gram_inv_of_isInverse hR hL, ?_, ?_⟩
  · exact fun x => ch15Closure_dixon_left_power_inequality d k B x
  · exact ch15Closure_dixon_success_probability_ge d k hk B θ hθ

end NumStability
