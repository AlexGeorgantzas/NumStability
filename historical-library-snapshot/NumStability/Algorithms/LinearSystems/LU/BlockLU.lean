import NumStability.Algorithms.LinearSystems.LU.BlockLU.ArbitraryNorm
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FactorizationError
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderFamilies
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.LinearSystems.LU.BlockLU.GrowthBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.OperatorTwo
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefiniteFactorBounds
import NumStability.Algorithms.LinearSystems.LU.BlockLU.RecursiveFactorization
import NumStability.Algorithms.LinearSystems.LU.BlockLU.ResidualLifting
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SchurComplement
import NumStability.Algorithms.LinearSystems.LU.BlockLU.SolveError
import NumStability.Algorithms.LinearSystems.LU.BlockLU.VaryingBlocks

/-!
# Block LU algorithms

Declaration-free aggregate over fifteen reviewed declaration-bearing reusable
Block LU leaves and the `VaryingBlocks` subaggregate over five unequal-order
leaves, completed in Phase 12. Numbered Chapter 13 correspondence is excluded;
use `NumStability.Source.Higham.Chapter13.BlockLU`. The historical
`NumStability.Algorithms.LU.BlockLU` facade imports both aggregates.
-/
