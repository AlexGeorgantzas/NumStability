import NumStability.Source.Higham.Chapter13.Algorithm01
import NumStability.Source.Higham.Chapter13.Algorithm03
import NumStability.Source.Higham.Chapter13.Algorithm04
import NumStability.Source.Higham.Chapter13.Equation01
import NumStability.Source.Higham.Chapter13.Equation02
import NumStability.Source.Higham.Chapter13.Equation03
import NumStability.Source.Higham.Chapter13.Equation18
import NumStability.Source.Higham.Chapter13.Equation19
import NumStability.Source.Higham.Chapter13.Equation20
import NumStability.Source.Higham.Chapter13.Equation21
import NumStability.Source.Higham.Chapter13.Equation22
import NumStability.Source.Higham.Chapter13.Equation23
import NumStability.Source.Higham.Chapter13.Equation23.PointRowGrowth
import NumStability.Source.Higham.Chapter13.Equation24
import NumStability.Source.Higham.Chapter13.Equation25
import NumStability.Source.Higham.Chapter13.Equation25.Factorization
import NumStability.Source.Higham.Chapter13.Equation25.Families
import NumStability.Source.Higham.Chapter13.Equation26
import NumStability.Source.Higham.Chapter13.Lemma09
import NumStability.Source.Higham.Chapter13.Lemma10.ConditionNumber
import NumStability.Source.Higham.Chapter13.Lemma10.SchurComplement
import NumStability.Source.Higham.Chapter13.Problem01
import NumStability.Source.Higham.Chapter13.Problem02
import NumStability.Source.Higham.Chapter13.Problem03
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageBounds
import NumStability.Source.Higham.Chapter13.Problem04.ActiveStageProducts
import NumStability.Source.Higham.Chapter13.Problem04.ActiveTailProducts
import NumStability.Source.Higham.Chapter13.Problem04.BlockInverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.ComparisonChains
import NumStability.Source.Higham.Chapter13.Problem04.DeterminantChainProducts
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationExistence
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.ComparisonUpdates
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.DeterminantBounds
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.InverseBounds
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LocalComparisons
import NumStability.Source.Higham.Chapter13.Problem04.FactorizationProducts.LowerBlockBudgets
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauChain
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauGrowth
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.ActiveSuffix
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.DiagonalUpdate
import NumStability.Source.Higham.Chapter13.Problem04.GlobalTableauProducts.TailChain
import NumStability.Source.Higham.Chapter13.Problem04.HistoryEnvelope
import NumStability.Source.Higham.Chapter13.Problem04.InfNormGrowth
import NumStability.Source.Higham.Chapter13.Problem04.InverseRatioChain
import NumStability.Source.Higham.Chapter13.Problem04.LocalGrowth
import NumStability.Source.Higham.Chapter13.Problem04.LocalNormBounds
import NumStability.Source.Higham.Chapter13.Problem04.LowerComparisonChain
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStageHistory
import NumStability.Source.Higham.Chapter13.Problem04.MatrixStages
import NumStability.Source.Higham.Chapter13.Problem04.OneStepProducts
import NumStability.Source.Higham.Chapter13.Problem04.ProductBounds
import NumStability.Source.Higham.Chapter13.Problem04.RecursiveBudgetChains
import NumStability.Source.Higham.Chapter13.Problem04.ScalarGrowthBridge
import NumStability.Source.Higham.Chapter13.Problem04.StageHistory
import NumStability.Source.Higham.Chapter13.Problem05
import NumStability.Source.Higham.Chapter13.Problem06
import NumStability.Source.Higham.Chapter13.Problem07
import NumStability.Source.Higham.Chapter13.Problem08
import NumStability.Source.Higham.Chapter13.Problem09
import NumStability.Source.Higham.Chapter13.Section01.NormConventions
import NumStability.Source.Higham.Chapter13.Section01.OperationModelFamilies
import NumStability.Source.Higham.Chapter13.Section01.OperationModels
import NumStability.Source.Higham.Chapter13.Section01.StandardFactorization
import NumStability.Source.Higham.Chapter13.Section03.ArbitraryNormDominance
import NumStability.Source.Higham.Chapter13.Section03.ColumnDominanceClosure
import NumStability.Source.Higham.Chapter13.Section03.RowDominanceClosure
import NumStability.Source.Higham.Chapter13.Section03.SchurStageAnalysis
import NumStability.Source.Higham.Chapter13.Section03.SPDFactorBounds
import NumStability.Source.Higham.Chapter13.Table01
import NumStability.Source.Higham.Chapter13.Table01.Families
import NumStability.Source.Higham.Chapter13.Theorem02.Factorization
import NumStability.Source.Higham.Chapter13.Theorem02.Uniqueness
import NumStability.Source.Higham.Chapter13.Theorem02.VaryingBlocks
import NumStability.Source.Higham.Chapter13.Theorem05.ErrorAnalysis
import NumStability.Source.Higham.Chapter13.Theorem05.FamilyErrorAnalysis
import NumStability.Source.Higham.Chapter13.Theorem05.Recurrences
import NumStability.Source.Higham.Chapter13.Theorem06.AssumptionModel
import NumStability.Source.Higham.Chapter13.Theorem06.Computation
import NumStability.Source.Higham.Chapter13.Theorem06.FactorAndSolve
import NumStability.Source.Higham.Chapter13.Theorem07.OneStep
import NumStability.Source.Higham.Chapter13.Theorem07.PivotExistence
import NumStability.Source.Higham.Chapter13.Theorem08.OneStep

/-!
# Higham Chapter 13: BlockLU

Declaration-free aggregate with an exact 82-member direct-import surface:
81 declaration-bearing Chapter 13 BlockLU owners and the declaration-free
`Theorem02.VaryingBlocks` locator. The 287 declarations from the ten historical
sibling paths moved into semantic destinations, while those paths remain
available as compatibility wrappers.
-/
