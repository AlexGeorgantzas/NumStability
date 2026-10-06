import NumStability.Algorithms.Summation.Insertion.ActiveList
import NumStability.Algorithms.Summation.Insertion.Executor
import NumStability.Algorithms.Summation.Insertion.RunningError
import NumStability.Algorithms.Summation.Insertion.Schedule
import NumStability.Algorithms.Summation.Insertion.ScheduleExecution
import NumStability.Source.Higham.Chapter04.Section01.InsertionExamples

/-!
# Insertion summation family

Complete supported entry point for insertion summation. Reusable code should
import the narrow semantic leaves below `Insertion/`; the two concrete Higham
Section 4.1 examples are canonical under `Source.Higham.Chapter04.Section01`.
-/
