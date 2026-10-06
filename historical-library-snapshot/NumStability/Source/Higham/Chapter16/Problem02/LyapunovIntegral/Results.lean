import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Source.Higham.Chapter16.Problem02.LyapunovIntegral.Results

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16Problem16_2.lean
--
-- Higham, 2nd ed., Problem 16.2: the exponential-integral representation
-- for Sylvester equations and the positive-definite Lyapunov corollary.











namespace NumStability

open Filter MeasureTheory Set Topology
open scoped ComplexOrder Matrix Pointwise
open NormedSpace

set_option backward.isDefEq.respectTransparency false

section SylvesterIntegral

variable {n : Nat}

abbrev Higham16CMatrix (n : Nat) := CStarMatrix (Fin n) (Fin n) Complex

/-- The integrand `exp(t A) C exp(t B)` in Higham's Problem 16.2.

The theorem is stated over complex matrices; the printed real theorem is the
real-entry special case.  Using `CStarMatrix` supplies a canonical Banach
algebra norm without choosing an arbitrary norm on Mathlib's bare `Matrix`
type. -/
noncomputable def higham16Problem16_2Kernel
    (A B C : Higham16CMatrix n) (t : Real) : Higham16CMatrix n :=
  exp (t • A) * C * exp (t • B)

/-- Higham's candidate `- integral_0^infinity exp(t A) C exp(t B) dt`. -/
noncomputable def higham16Problem16_2Integral
    (A B C : Higham16CMatrix n) : Higham16CMatrix n :=
  -∫ t in Ioi (0 : Real), higham16Problem16_2Kernel A B C t

/-- Precise form of the phrase in Problem 16.2 that the exponential integral
"exists for all C".  Bochner integrability is required for every matrix right
hand side. -/
def Higham16ExponentialProductIntegrable
    (A B : Higham16CMatrix n) : Prop :=
  ∀ C : Higham16CMatrix n,
    IntegrableOn (higham16Problem16_2Kernel A B C) (Ioi (0 : Real))

/-- Differential identity from the hint to Problem 16.2, in the form used by
the fundamental theorem of calculus. -/
theorem higham16_problem16_2_kernel_hasDerivAt
    (A B C : Higham16CMatrix n) (t : Real) :
    HasDerivAt (higham16Problem16_2Kernel A B C)
      (A * higham16Problem16_2Kernel A B C t +
        higham16Problem16_2Kernel A B C t * B) t := by
  have hA := hasDerivAt_exp_smul_const' A t
  have hB := hasDerivAt_exp_smul_const B t
  simpa only [higham16Problem16_2Kernel, mul_assoc] using
    (hA.mul_const C).mul hB

/-- The same differential identity factored through the Sylvester right-hand
side.  This is the form used for uniqueness of a homogeneous solution. -/
theorem higham16_problem16_2_kernel_hasDerivAt_factored
    (A B C : Higham16CMatrix n) (t : Real) :
    HasDerivAt (higham16Problem16_2Kernel A B C)
      (exp (t • A) * (A * C + C * B) * exp (t • B)) t := by
  have hA := hasDerivAt_exp_smul_const A t
  have hB := hasDerivAt_exp_smul_const' B t
  simpa only [higham16Problem16_2Kernel, mul_assoc, mul_add, add_mul] using
    (hA.mul_const C).mul hB






























































































































/-!
### Hurwitz spectrum bridge

The source hypothesis that every eigenvalue lies in the open left half-plane
is represented by the genuine Banach-algebra spectrum.  Compactness supplies
a uniform negative real-part margin.  After a sufficiently large positive
scalar shift, the shifted spectrum lies in a disk of radius strictly smaller
than the shift.  Gelfand's formula then bounds all powers (including the
finite prefix), and the exponential series gives quantitative decay.
-/

noncomputable section

/-- A square complex matrix is Hurwitz when every point of its genuine
Banach-algebra spectrum has strictly negative real part. -/
def Higham16Hurwitz (A : Higham16CMatrix n) : Prop :=
  ∀ z ∈ spectrum Complex A, z.re < 0

































































































































































































































































































/-- Taking adjoints preserves the Hurwitz condition: the spectrum is complex
conjugated and hence real parts are unchanged. -/
theorem Higham16Hurwitz.star {A : Higham16CMatrix n}
    (hA : Higham16Hurwitz A) : Higham16Hurwitz (star A) := by
  intro z hz
  rw [spectrum.map_star] at hz
  have hzA : starRingEnd Complex z ∈ spectrum Complex A := by
    simpa only [Set.mem_star] using hz
  have hre := hA (starRingEnd Complex z) hzA
  simpa using hre











end

/-!
### Positive-definite Lyapunov corollary

The printed corollary uses real matrices, transpose, and the spectral premise
that every eigenvalue of `A` has negative real part.  The endpoints below prove
the slightly more general complex-adjoint statement.  The preceding compact-
spectrum and Gelfand argument derives the required semigroup integrability
from that literal premise, so no target-bearing analytic assumption remains.
-/


















































































































































































































noncomputable section











































































end

end SylvesterIntegral

end NumStability
