import NumStability.FloatingPoint.Model
import NumStability.FloatingPoint.OperationLaws
import NumStability.Analysis.Rounding
import NumStability.Analysis.Error.Measures.All
import NumStability.Analysis.Stability
import NumStability.Analysis.VectorNorms.Basic
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.LinearOperators.Schur
import NumStability.Analysis.LinearOperators.Pseudospectra.PowerBounds
import NumStability.Analysis.LinearOperators.MatrixPowers.Semiconvergence.All
import NumStability.Analysis.SingularValues.RectangularGram
import NumStability.Analysis.TestMatrices
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.Algorithms.Summation.Recursive.Core
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.PolynomialEvaluation.RootProduct
import NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.QR.GivensSpec
import NumStability.Algorithms.LinearSystems.QR.HouseholderConstruction2
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Basic
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core
import NumStability.Algorithms.MatrixInversion.Residuals.MatrixInversion
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.NormEstimation.OneNorm.LAPACK.Basic
import NumStability.Algorithms.NormEstimation.PNorm.PowerMethod.PNormPowerMethod
import NumStability.Source.Higham.Chapter06
import NumStability.Source.Higham.Chapter12
import NumStability.Source.Higham.Chapter16
import NumStability.Source.Higham.Chapter22
import NumStability.Source.Higham.Chapter24

/-!
Executable validation companion to `docs/LIBRARY_LOOKUP.md`.

This file deliberately uses representative narrow imports. It is a package
smoke check and a set of searchable declaration checks, not an exhaustive
inventory. Run it with:

  lake env lean docs/LibraryLookupChecks.lean
-/

open NumStability

-- Floating-point foundations and reusable analysis.
#check FPModel
#check BasicOp
#check gamma
#check gammaValid
#check absError
#check relError
#check normwiseBackwardErrorBoundedVec
#check normwiseConditionNumberBoundedVec
#check complexVecLpNorm
#check complexMatrixLpNorm
#check forward_error_from_residual
#check oettli_prager
#check schur_triangulation
#check resolventPseudospectralRadius
#check matPow_tendsto_zero_of_spectralRadius_lt_one
#check RectRankFactorization
#check rectRightGram
#check rectRightGramBasisSingularValue

-- Standard matrix families.
#check hilbertMatrix
#check pascalMatrix
#check cauchyMatrix
#check companionMatrix

-- Core algorithm families.
#check fl_sum_error
#check fl_recursiveSum
#check SumTree.exactSum
#check fl_dotProduct
#check dotProduct_error_bound
#check rootProductEval
#check fl_hornerDerivativeDesc_first_derivative_error_bound
#check matVec_backward_error
#check matMul_error_bound
#check fl_forwardSub
#check forwardSub_backward_error
#check LUBackwardError
#check lu_backward_error_gamma
#check CholeskyBackwardError
#check cholesky_backward_error_perturbation
#check givensRotation
#check householderScaleAlt
#check RectLSNormalEquations
#check fl_residual
#check one_step_refinement_error_identity
#check BlockLDLTSpec
#check bunchParlettAlpha
#check inverseRightResidual
#check inversion_residual_bound
#check sylvesterOp
#check condSylvester
#check lapackNormEstimator
#check Ch15.PNormPair

-- Representative Higham source-facing results.
#check Lemma66.lemma66_a_op2_le
#check higham12_3_exact_one_step_residual_bound
#check higham16_problem16_2_lyapunov_spd_unique
#check higham22_vandermonde_det_ne_zero_iff
#check higham24Radix2FFT_eq_dftApply
