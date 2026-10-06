import NumStability.Source.Higham.Chapter21.Theorem04.GivensQMethod.Closure
import NumStability.Source.Higham.Chapter21.Theorem04.GivensQMethod.Core
import NumStability.Source.Higham.Chapter21.Theorem04.GivensQMethod.RoundedReplay
import NumStability.Source.Higham.Chapter21.Theorem04.ModifiedGramSchmidtQMethod.Core
import NumStability.Source.Higham.Chapter21.Theorem04.ModifiedGramSchmidtQMethod.RoundedReplay
import NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.ActualOutput
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Closure
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.EnvelopeTransfer
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Forward
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.QRMajorant
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.RemainderBounds
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Signed
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.Uniform
import NumStability.Source.Higham.Chapter21.Theorem04.SourceClosure.SourceClosure
import NumStability.Source.Higham.Chapter21.Theorem04.SourceClosure.Supplement.Core

/-!
# Higham Chapter 21, Theorem 21.4

Complete canonical entry point for the currently migrated Theorem 21.4
row-wise backward-error measure and its concrete Householder Q-method bound.
The remaining Givens and source-closure developments stay on their historical
paths while the Chapter 21 migration continues.
-/
