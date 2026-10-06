import NumStability.Algorithms.Summation.Compensated.Alternative
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula
import NumStability.Algorithms.Summation.Compensated.FastTwoSum
import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Algorithms.Summation.Compensated.Kahan
import NumStability.Algorithms.Summation.Compensated.NoGuard
import NumStability.Source.Higham.Chapter04.Algorithm02.InitializationModelLimitations
import NumStability.Source.Higham.Chapter04.Equation07.AbstractModelCounterexample
import NumStability.Source.Higham.Chapter04.Equation07.NoGuardCounterexample
import NumStability.Source.Higham.Chapter04.Equation07.SterbenzCounterexamples
import NumStability.Source.Higham.Chapter04.Equation08.FiniteRouteLimitations
import NumStability.Source.Higham.Chapter04.Equation08.ModelStrength
import NumStability.Source.Higham.Chapter04.Equation08.ReturnedSum
import NumStability.Source.Higham.Chapter04.Equation09.Correction
import NumStability.Source.Higham.Chapter04.Equation09.ModelStrength
import NumStability.Source.Higham.Chapter04.Equation10
import NumStability.Source.Higham.Chapter04.Problem10
import NumStability.Source.Higham.Chapter04.Section03.FiniteFormat
import NumStability.Source.Higham.Chapter04.Section03.NoGuardKahanCounterexample

/-!
# Compensated summation

Declaration-free complete entry point for the reusable compensated-summation
families and the source-correspondence declarations historically exported by
this module. Reusable clients should import a narrow semantic family or leaf;
the source imports here preserve the supported historical surface.
-/
