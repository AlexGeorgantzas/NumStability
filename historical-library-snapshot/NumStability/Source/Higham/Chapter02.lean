import NumStability.Source.Higham.Chapter02.Equation06.NoGuardModel.All
import NumStability.Source.Higham.Chapter02.Equation08.AdditiveError.All
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.AdditiveUnderflowModel
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.Environment
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.ExactSubtraction
import NumStability.Source.Higham.Chapter02.FloatingPointArithmetic.StandardModel
import NumStability.Source.Higham.Chapter02.Problem01.FloatingPointCounts.Basic
import NumStability.Source.Higham.Chapter02.Problem02
import NumStability.Source.Higham.Chapter02.Problem03.AdjacentPrecisionValues.Basic
import NumStability.Source.Higham.Chapter02.Problem03.AdjacentPrecisionValues.Results.Theorems
import NumStability.Source.Higham.Chapter02.Problem04
import NumStability.Source.Higham.Chapter02.Problem05.BinaryOneTenth.Basic
import NumStability.Source.Higham.Chapter02.Problem06.IntegerRepresentability.Basic
import NumStability.Source.Higham.Chapter02.Problem07
import NumStability.Source.Higham.Chapter02.Problem08.MidpointRounding.All
import NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.All
import NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.Basic
import NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.ExhaustiveBinary64.Results
import NumStability.Source.Higham.Chapter02.Problem11
import NumStability.Source.Higham.Chapter02.Problem12.ReciprocalProduct.Basic
import NumStability.Source.Higham.Chapter02.Problem12.ReciprocalProduct.Results.Theorems
import NumStability.Source.Higham.Chapter02.Problem13.ReciprocalProductThreshold.Basic
import NumStability.Source.Higham.Chapter02.Problem13.ReciprocalProductThreshold.Results.Theorems
import NumStability.Source.Higham.Chapter02.Problem14.UnitRoundoffProbe.Basic
import NumStability.Source.Higham.Chapter02.Problem14.UnitRoundoffProbe.IeeeExamples.Results
import NumStability.Source.Higham.Chapter02.Problem18.ExactSubtractionCounterexample.Basic
import NumStability.Source.Higham.Chapter02.Problem19.GradualUnderflowExactness.Basic
import NumStability.Source.Higham.Chapter02.Problem20.SquareRootIdentities.Basic
import NumStability.Source.Higham.Chapter02.Problem21.HypotenuseNormalization.Basic
import NumStability.Source.Higham.Chapter02.Problem21.HypotenuseNormalization.StandardModelCounterexample.Results
import NumStability.Source.Higham.Chapter02.Problem22
import NumStability.Source.Higham.Chapter02.Problem23
import NumStability.Source.Higham.Chapter02.Problem24.GuardDigitCancellation.Basic
import NumStability.Source.Higham.Chapter02.Problem25.NonzeroEvaluation.Basic
import NumStability.Source.Higham.Chapter02.Problem25.NonzeroEvaluation.IeeeFiniteSystems.Results
import NumStability.Source.Higham.Chapter02.Problem26.ExactProduct.All
import NumStability.Source.Higham.Chapter02.Problem27.KahanDeterminant.Basic
import NumStability.Source.Higham.Chapter02.Problem28.IterativeDivisionTermination.Basic
import NumStability.Source.Higham.Chapter02.Problem28.IterativeDivisionTermination.UnderflowAwareConvergence.Results
import NumStability.Source.Higham.Chapter02.Problems15And16.SpecialValueProbes.Basic
import NumStability.Source.Higham.Chapter02.Section03.DoubleRounding.All
import NumStability.Source.Higham.Chapter02.Section04.NoGuardModel.All
import NumStability.Source.Higham.Chapter02.Section06.Discriminant.FusedMultiplyAdd.Basic
import NumStability.Source.Higham.Chapter02.Section06.Discriminant.FusedMultiplyAdd.Counterexample.Results
import NumStability.Source.Higham.Chapter02.Section06.Discriminant.StandardModel.Basic
import NumStability.Source.Higham.Chapter02.Section06.Discriminant.StandardModel.Counterexample.Results
import NumStability.Source.Higham.Chapter02.Section06.FusedMultiplyAdd.All
import NumStability.Source.Higham.Chapter02.Section06.ReciprocalIteration.Basic
import NumStability.Source.Higham.Chapter02.Section07
import NumStability.Source.Higham.Chapter02.Section10.ArctangentRange.Basic
import NumStability.Source.Higham.Chapter02.Section10.ArctangentRange.Counterexample.Results
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Basic
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Results.Theorems
import NumStability.Source.Higham.Chapter02.Section10.Tablemaker.HermiteLindemann.Basic
import NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.Basic
import NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.CodySineResults.Theorems

/-!
# Higham Chapter 2

Canonical import-only entry point for floating-point arithmetic and the
formalized problems from Chapter 2 of Higham's *Accuracy and Stability of
Numerical Algorithms*.
-/
