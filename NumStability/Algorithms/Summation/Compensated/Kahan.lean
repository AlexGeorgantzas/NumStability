import NumStability.Algorithms.Summation.Compensated.Kahan.Coefficients
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.Kahan.Exactness
import NumStability.Algorithms.Summation.Compensated.Kahan.Finite
import NumStability.Algorithms.Summation.Compensated.Kahan.FiniteErrorBounds
import NumStability.Algorithms.Summation.Compensated.Kahan.FiniteFormat
import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients
import NumStability.Algorithms.Summation.Compensated.Kahan.Majorants

/-!
# Kahan compensated summation

Declaration-free reusable entry point for Kahan execution, finite-format
certificates, coefficient engines, exactness, and conditional error bounds.
Source-specific counterexamples and corrected Higham statements live under
`NumStability.Source.Higham.Chapter04`.
-/
