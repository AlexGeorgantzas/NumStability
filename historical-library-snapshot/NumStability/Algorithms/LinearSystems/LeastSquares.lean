import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.GQR
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.KKT
import NumStability.Algorithms.LinearSystems.LeastSquares.GramBasis
import NumStability.Algorithms.LinearSystems.LeastSquares.MGS
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.Refinement
import NumStability.Algorithms.LinearSystems.LeastSquares.RowSorting
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.LeastSquares.TraceKernel

/-!
# Least squares

Declaration-free aggregate for the canonical reusable least-squares
algorithm and specification family.
-/
