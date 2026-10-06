import NumStability.Source.Higham.Chapter21.Attainability.Results
import NumStability.Source.Higham.Chapter21.Corrections.CorrectedMGS.RoundedReplay
import NumStability.Source.Higham.Chapter21.Equation01.QRFoundations
import NumStability.Source.Higham.Chapter21.Equation03.QRFoundations
import NumStability.Source.Higham.Chapter21.Equation04.Pseudoinverse
import NumStability.Source.Higham.Chapter21.Equation04.QRFoundations
import NumStability.Source.Higham.Chapter21.Equation06.Perturbation
import NumStability.Source.Higham.Chapter21.Equation07.ConditionTransfer
import NumStability.Source.Higham.Chapter21.Equation08.EquationClosure
import NumStability.Source.Higham.Chapter21.Equation08.ProjectorNorm
import NumStability.Source.Higham.Chapter21.Equation08.Results.Core
import NumStability.Source.Higham.Chapter21.Equation09.EquationClosure
import NumStability.Source.Higham.Chapter21.Equation09.ProjectorNorm
import NumStability.Source.Higham.Chapter21.Equation09.Results.Core
import NumStability.Source.Higham.Chapter21.Equation10.Closure
import NumStability.Source.Higham.Chapter21.Equation10.RoundedReplay
import NumStability.Source.Higham.Chapter21.Equation11.ActualOutput
import NumStability.Source.Higham.Chapter21.Equation11.Closure
import NumStability.Source.Higham.Chapter21.Equation11.Equation
import NumStability.Source.Higham.Chapter21.Equation11.Forward
import NumStability.Source.Higham.Chapter21.Equation11.RemainderBounds
import NumStability.Source.Higham.Chapter21.Equation11.Results.Core
import NumStability.Source.Higham.Chapter21.Equation11.Scalar
import NumStability.Source.Higham.Chapter21.Equation11.ScalarCase.Core
import NumStability.Source.Higham.Chapter21.Equation11.Uniform
import NumStability.Source.Higham.Chapter21.Equation11.UniformClosure
import NumStability.Source.Higham.Chapter21.Equation11.UniformEnvelope.Core
import NumStability.Source.Higham.Chapter21.RowScalingInvariance
import NumStability.Source.Higham.Chapter21.Section03.MethodComparison.Core
import NumStability.Source.Higham.Chapter21.Theorem01.Attainability.Attainability
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.Radius
import NumStability.Source.Higham.Chapter21.Theorem01.ComponentwisePerturbation.RankStability
import NumStability.Source.Higham.Chapter21.Theorem03
import NumStability.Source.Higham.Chapter21.Theorem04
import NumStability.Source.Higham.Chapter21.Theorem04.SourceClosure.Supplement.Core

/-!
# Higham Chapter 21

Canonical import-only entry point for the currently migrated row-scaling,
Theorem 21.3, and Theorem 21.4 row-wise backward-error statements from Chapter
21 of Higham's *Accuracy and Stability of Numerical Algorithms*. The broader
historical Chapter 21 surface remains available through
`NumStability.Algorithms.Underdetermined.Higham21` while migration is in
progress.
-/
