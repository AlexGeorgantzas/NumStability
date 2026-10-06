import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Algorithms.PolynomialEvaluation.MatrixNorms
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.FunctionalCalculus.Resolvent.Analyticity
import NumStability.Analysis.FunctionalCalculus.Resolvent.DunfordResidue
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.DistanceToInstability
import NumStability.Analysis.LinearOperators.MatrixPowers.BaiDemmelGu.StabilityRadius
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.Real
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan
import NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.PlanarAlgebra
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational
import NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.ConvergenceCriterion
import NumStability.Analysis.LinearOperators.Pseudospectra.Perturbation.Definitions
import NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds.Contour
import NumStability.Analysis.LinearOperators.Pseudospectra.Resolvent.LowerBounds
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.Spijker.PlanarCrossingBounds.Polynomial

R07 canonical `reusable` leaf. Declaration-level review groups 5 source-independent declaration(s) under one mathematical dependency boundary; representative witnesses: `NumStability.RationalOrderCertificate.arcLength_le_of_planar_analyticBridge`, `NumStability.RationalOrderCertificate.projection_crossing_finset_card_le_two_mul`, `NumStability.spijkerProjectionCrossingPolynomial_natDegree_le`.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.MatrixPowersSpijkerPlanar`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


namespace NumStability

open scoped Real Topology ComplexConjugate
open Complex Polynomial Set MeasureTheory

noncomputable section

private lemma natDegree_C_mul_mul_le_two_mul
    {n : ℕ} (c : ℂ) {p q : ℂ[X]}
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n) :
    (C c * p * q).natDegree ≤ 2 * n := by
  calc
    (C c * p * q).natDegree ≤ (C c * p).natDegree + q.natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ ((C c).natDegree + p.natDegree) + q.natDegree := by
      gcongr
      exact Polynomial.natDegree_mul_le
    _ ≤ (0 + n) + n := by
      gcongr
      simp
    _ = 2 * n := by omega

lemma spijkerProjectionCrossingPolynomial_natDegree_le
    {n : ℕ} {P Q : ℂ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (ω : ℂ) (x : ℝ) :
    (spijkerProjectionCrossingPolynomial n P Q ω x).natDegree ≤ 2 * n := by
  have hPc := spijkerCircleConjugateLift_natDegree_le hP
  have hQc := spijkerCircleConjugateLift_natDegree_le hQ
  unfold spijkerProjectionCrossingPolynomial
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · exact (Polynomial.natDegree_add_le _ _).trans (max_le
      (natDegree_C_mul_mul_le_two_mul ω hP hQc)
      (natDegree_C_mul_mul_le_two_mul (conj ω) hPc hQ))
  · exact natDegree_C_mul_mul_le_two_mul (2 * (x : ℂ)) hQ hQc

/-- Algebraic crossing count in Spijker's proof.  Any finite collection of
distinct parameters in one half-open turn at which a fixed real projection
of `P/Q` takes the same value has cardinality at most `2n`, provided the
associated crossing polynomial is nonzero. -/
theorem spijker_projection_crossing_finset_card_le_two_mul
    {n : ℕ} {P Q : ℂ[X]}
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (ω : ℂ) (x : ℝ)
    (hpoly : spijkerProjectionCrossingPolynomial n P Q ω x ≠ 0)
    (s : Finset ℝ)
    (hsI : ∀ t ∈ s, t ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hQcircle : ∀ t ∈ s, Q.eval (circleMap 0 1 t) ≠ 0)
    (hcross : ∀ t ∈ s,
      spijkerRealProjection ω
        (P.eval (circleMap 0 1 t) / Q.eval (circleMap 0 1 t)) = x) :
    s.card ≤ 2 * n := by
  let c : ℝ → ℂ := circleMap 0 1
  let p := spijkerProjectionCrossingPolynomial n P Q ω x
  have hI : (↑s : Set ℝ) ⊆ Set.Ico (0 : ℝ) (2 * Real.pi) := by
    intro t ht
    exact hsI t ht
  have hinjI : Set.InjOn c (Set.Ico (0 : ℝ) (2 * Real.pi)) := by
    exact injOn_circleMap_of_abs_sub_le' (by norm_num) (by simp [mul_comm])
  have hinj : Set.InjOn c (↑s : Set ℝ) := hinjI.mono hI
  have hcard : (s.image c).card = s.card :=
    Finset.card_image_iff.mpr hinj
  have hroot : (s.image c).val ⊆ p.roots := by
    intro z hz
    change z ∈ s.image c at hz
    simp only [Finset.mem_image] at hz
    obtain ⟨t, hts, rfl⟩ := hz
    rw [Polynomial.mem_roots hpoly]
    apply spijkerProjectionCrossingPolynomial_eval_eq_zero_of_projection_eq
      hP hQ ω x
    · simp [c, circleMap]
    · exact hQcircle t hts
    · exact hcross t hts
  calc
    s.card = (s.image c).card := hcard.symm
    _ ≤ p.natDegree := Polynomial.card_le_degree_of_subset_roots hroot
    _ ≤ 2 * n := spijkerProjectionCrossingPolynomial_natDegree_le hP hQ ω x

/-- The crossing theorem expressed directly through a rational-order
certificate on an arbitrary centered circle.  This is the algebraic input to
the one-dimensional variation argument in Spijker's proof. -/
theorem RationalOrderCertificate.projection_crossing_finset_card_le_two_mul
    {n : ℕ} {f : ℂ → ℂ} (cert : RationalOrderCertificate n f)
    (R : ℝ) (ω : ℂ) (x : ℝ)
    (hden : ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      cert.denominator.eval (circleMap 0 R t) ≠ 0)
    (hvary : ∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      spijkerRealProjection ω (f (circleMap 0 R t)) ≠ x)
    (s : Finset ℝ)
    (hsI : ∀ t ∈ s, t ∈ Set.Ico (0 : ℝ) (2 * Real.pi))
    (hcross : ∀ t ∈ s,
      spijkerRealProjection ω (f (circleMap 0 R t)) = x) :
    s.card ≤ 2 * n := by
  let P := spijkerRadialScalePolynomial R cert.numerator
  let Q := spijkerRadialScalePolynomial R cert.denominator
  have hP : P.natDegree ≤ n :=
    spijkerRadialScalePolynomial_natDegree_le cert.numerator_degree R
  have hQ : Q.natDegree ≤ n :=
    spijkerRadialScalePolynomial_natDegree_le cert.denominator_degree R
  have hpoly : spijkerProjectionCrossingPolynomial n P Q ω x ≠ 0 := by
    apply spijkerProjectionCrossingPolynomial_ne_zero_of_exists_projection_ne
      hP hQ
    obtain ⟨t, ht, hne⟩ := hvary
    let z := circleMap 0 1 t
    have hden_t := hden t ht
    have hval := cert.value_eq (circleMap 0 R t) hden_t
    refine ⟨z, ?_, ?_, ?_⟩
    · simp [z, circleMap]
    · simpa [Q, z, radialScale_unitCircle_eq_circleMap] using hden_t
    · calc
        spijkerRealProjection ω (P.eval z / Q.eval z) =
            spijkerRealProjection ω
              (cert.numerator.eval (circleMap 0 R t) /
                cert.denominator.eval (circleMap 0 R t)) := by
                  simp [P, Q, z, radialScale_unitCircle_eq_circleMap]
        _ = spijkerRealProjection ω (f (circleMap 0 R t)) := by rw [hval]
        _ ≠ x := hne
  apply spijker_projection_crossing_finset_card_le_two_mul
    hP hQ ω x hpoly s hsI
  · intro t ht
    simpa [Q, radialScale_unitCircle_eq_circleMap] using hden t (hsI t ht)
  · intro t ht
    have hden_t := hden t (hsI t ht)
    have hval := cert.value_eq (circleMap 0 R t) hden_t
    calc
      spijkerRealProjection ω
          (P.eval (circleMap 0 1 t) / Q.eval (circleMap 0 1 t)) =
        spijkerRealProjection ω
          (cert.numerator.eval (circleMap 0 R t) /
            cert.denominator.eval (circleMap 0 R t)) := by
              simp [P, Q, radialScale_unitCircle_eq_circleMap]
      _ = spijkerRealProjection ω (f (circleMap 0 R t)) := by rw [hval]
      _ = x := hcross t ht

/-- Interface theorem for the sharp planar arc-length estimate after the
complete algebraic crossing argument.  The exact constant follows transparently:
`2n` crossings give projected variation `4nC`; averaging over `2π`
directions and multiplying by the factor `1/4` in equation (6) gives
`2πnC`. -/
theorem RationalOrderCertificate.arcLength_le_of_planar_analyticBridge
    {n : ℕ} {f : ℂ → ℂ} (cert : RationalOrderCertificate n f)
    (hbridge : SpijkerPlanarAnalyticBridge)
    (R C : ℝ) (hC : 0 ≤ C)
    (γ : ℝ → ℂ) (hγ : γ = fun t => f (circleMap 0 R t))
    (hγC1 : ContDiff ℝ 1 γ)
    (hden : ∀ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      cert.denominator.eval (circleMap 0 R t) ≠ 0)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi), ‖γ t‖ ≤ C) :
    (∫ t : ℝ in 0..2 * Real.pi, ‖deriv γ t‖) ≤
      2 * Real.pi * n * C := by
  obtain ⟨hprojInt, havg⟩ := hbridge.projection_average γ hγC1
  have hprojBound : ∀ θ : ℝ,
      spijkerProjectedVariation γ θ ≤ 4 * (n : ℝ) * C := by
    intro θ
    have hθC1 := spijkerProjectedCurve_contDiff hγC1 θ
    have hrange : ∀ t ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
        |spijkerProjectedCurve γ θ t| ≤ C := by
      intro t ht
      exact (abs_spijkerProjectedCurve_le_norm γ θ t).trans (hbound t ht)
    have hcrossing : ∀ x : ℝ,
        (∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
          spijkerProjectedCurve γ θ t ≠ x) →
        ∀ s : Finset ℝ,
          (∀ t ∈ s, t ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) →
          (∀ t ∈ s, spijkerProjectedCurve γ θ t = x) →
          s.card ≤ 2 * n := by
      intro x hvary s hsI hlevel
      apply cert.projection_crossing_finset_card_le_two_mul
        R (spijkerProjectionDirection θ) x hden
      · simpa [spijkerProjectedCurve, hγ] using hvary
      · exact hsI
      · simpa [spijkerProjectedCurve, hγ] using hlevel
    have hvar := hbridge.crossing_variation
      (spijkerProjectedCurve γ θ) (2 * n) C hθC1 hC hrange hcrossing
    calc
      spijkerProjectedVariation γ θ ≤ 2 * ((2 * n : ℕ) : ℝ) * C := by
        simpa [spijkerProjectedVariation] using hvar
      _ = 4 * (n : ℝ) * C := by push_cast; ring
  have hconstInt : IntervalIntegrable
      (fun _θ : ℝ => 4 * (n : ℝ) * C) volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have houter :
      (∫ θ : ℝ in 0..2 * Real.pi, spijkerProjectedVariation γ θ) ≤
        ∫ _θ : ℝ in 0..2 * Real.pi, 4 * (n : ℝ) * C := by
    apply intervalIntegral.integral_mono_on (by positivity) hprojInt hconstInt
    intro θ _hθ
    exact hprojBound θ
  rw [havg]
  calc
    (1 / 4 : ℝ) *
          (∫ θ : ℝ in 0..2 * Real.pi, spijkerProjectedVariation γ θ) ≤
        (1 / 4 : ℝ) *
          (∫ _θ : ℝ in 0..2 * Real.pi, 4 * (n : ℝ) * C) := by
            exact mul_le_mul_of_nonneg_left houter (by norm_num)
    _ = 2 * Real.pi * n * C := by
      rw [intervalIntegral.integral_const]
      push_cast
      simp only [smul_eq_mul]
      ring

end
end NumStability
