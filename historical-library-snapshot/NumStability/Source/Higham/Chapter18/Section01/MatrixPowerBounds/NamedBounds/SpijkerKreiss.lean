import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import NumStability.Analysis.LinearOperators.MatrixPowers.Kreiss.ResolventBound
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.ArcLengthPowerBounds.FiniteDimension
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Kreiss

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.SpijkerKreiss

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

/-
# The Spijker interface in the finite-dimensional Kreiss theorem

The sharp reverse Kreiss inequality

  `‖A^k‖₂ ≤ exp(1) * n * K`

does not follow from Cayley--Hamilton with uncontrolled characteristic-
polynomial coefficients.  Its standard proof uses Spijker's sharp arc-length
lemma for rational functions.  If `q` is a quotient of two polynomials of
degree at most `n`, with no pole on a circle, that lemma states

  `∫ |q'| ≤ 2π n sup |q|`.

For the Kreiss proof one takes

  `q(z) = ⟪v, (zI-A)⁻¹u⟫`.

This scalar function has rational order at most `n` by the adjugate formula.
The predicate `SpijkerArcLengthBound` below is exactly the sharp inequality in
this specialization.  Its `KreissResolventBound` and `1 < R` hypotheses imply
the source requirement that the circle be pole-free.  The continuity and
interval integrability of the derivative on
the exterior circles used by the Kreiss proof are established internally
below.  This file isolates the Spijker inequality as a reusable interface and
proves that it implies the full all-powers Kreiss endpoint.  The interface is
proved unconditionally by the planar projection and finite layer-cake
argument in `MatrixPowersSpijkerPlanarAnalysis`.
-/





namespace NumStability

open scoped Real Topology ComplexOrder

open Complex Metric Set MeasureTheory

noncomputable section






























































































































































































































































































































































































































































































































































/-- **Interface form of the literal upper endpoint in Higham's notation:**
`sup_k ‖A^k‖₂ ≤ e n φ(A)`. -/
theorem higham18_kreiss_upper_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    matrixPowerNormSup A ≤
      Real.exp 1 * n * kreissConstant A := by
  apply csSup_le
  · exact ⟨‖A ^ 0‖, 0, rfl⟩
  · intro x hx
    rcases hx with ⟨k, rfl⟩
    exact norm_pow_le_exp_mul_dim_of_spijker hS A
      (kreissResolventBound_kreissConstant A hres hbdd) k

/-- Interface form of the two-sided finite-dimensional Kreiss theorem. -/
theorem higham18_kreiss_two_sided_of_spijker
    {n : ℕ} [Nonempty (Fin n)]
    (hS : SpijkerArcLengthBound n)
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (hres : ∀ z : ℂ, 1 < ‖z‖ → z ∈ resolventSet ℂ A)
    (hbdd : BddAbove (kreissResolventValueSet A)) :
    kreissConstant A ≤ matrixPowerNormSup A ∧
      matrixPowerNormSup A ≤ Real.exp 1 * n * kreissConstant A := by
  have hK := kreissResolventBound_kreissConstant A hres hbdd
  have hpowers : BddAbove (matrixPowerNormSet A) := by
    refine ⟨Real.exp 1 * n * kreissConstant A, ?_⟩
    intro x hx
    rcases hx with ⟨k, rfl⟩
    exact norm_pow_le_exp_mul_dim_of_spijker hS A hK k
  exact ⟨higham18_kreiss_lower A hpowers,
    higham18_kreiss_upper_of_spijker hS A hres hbdd⟩

end

end NumStability
