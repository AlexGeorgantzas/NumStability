import NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.CancellationOfRoundingErrors
import NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.IncreasingPrecision
import NumStability.Source.Higham.Chapter01.FloatingPointArithmetic.InstabilityWithoutCancellation
import NumStability.Source.Higham.Chapter01.Problem01.RelativeError.All
import NumStability.Source.Higham.Chapter01.Problem02.NearIntegerTable.Basic
import NumStability.Source.Higham.Chapter01.Problem03.CancellationRewrites.All
import NumStability.Source.Higham.Chapter01.Problem05.CompensatedLogarithm.Basic
import NumStability.Source.Higham.Chapter01.Problem06.CalculatorWords.Basic
import NumStability.Source.Higham.Chapter01.Problem07.SampleVarianceConditioning.All
import NumStability.Source.Higham.Chapter01.Problem08.MullerRecurrence.Basic
import NumStability.Source.Higham.Chapter01.Problem09.CramersRule.All
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.All
import NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.RemainderBound.Theorem
import NumStability.Source.Higham.Chapter01.Section02.ErrorMeasures.All
import NumStability.Source.Higham.Chapter01.Section03.ErrorSources.All
import NumStability.Source.Higham.Chapter01.Section04.AccuracyAndPrecision.All
import NumStability.Source.Higham.Chapter01.Section07.Cancellation.All
import NumStability.Source.Higham.Chapter01.Section07.TrigonometricCancellation.All
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.All
import NumStability.Source.Higham.Chapter01.Section09.SampleVariance.IeeeSingleOnePassCounterexample.Results
import NumStability.Source.Higham.Chapter01.Section10.CramersRule.All
import NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic
import NumStability.Source.Higham.Chapter01.Section12.InstabilityWithoutCancellation.PivotingExample
import NumStability.Source.Higham.Chapter01.Section13.IncreasingPrecision.BinaryStorageExamples
import NumStability.Source.Higham.Chapter01.Section14.CancellationOfRoundingErrors.Algorithm02RoundedCore
import NumStability.Source.Higham.Chapter01.Section16.ProblemDependentStability.All
import NumStability.Source.Higham.Chapter01.Section17

/-!
# Higham Chapter 1

Source correspondence for introductory principles of finite-precision
computation. The current formalization covers cancellation, increasing
precision, instability without cancellation, and the nonrandom-rounding
example from Section 1.17.
-/
