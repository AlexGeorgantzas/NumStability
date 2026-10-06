import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Carrier.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydDomain
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Differentiation.PNormGeneral
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.FixedPoints.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydInterface
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.LocalStability.BoydLocalStability
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.RowwiseDomain.Basic
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydDomain
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Scalar.BoydRowwise
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydConcrete
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.SecondVariation.BoydLocal
import NumStability.Algorithms.NormEstimation.PNorm.Boyd.Uniqueness.Basic

/-!
# Algorithms.NormEstimation.PNorm.Boyd

Reviewed W10 discovery entry point for the reusable Boyd p-norm family.
-/
