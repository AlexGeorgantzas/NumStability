import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.UnderdeterminedSolve
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve

/-!
# Source.Higham.Chapter21.Equation11.UniformClosure

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- A uniform fixed-radius form of the Q-method bound in equation (21.11).



namespace NumStability

set_option maxHeartbeats 1200000

/-- A direction-independent entrywise envelope for every normalized rowwise
    perturbation direction used in equation (21.11). -/
noncomputable def higham21Eq21_11UniformDirectionEnvelope {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun _ _ => frobNormRect A

/-- The induced Gram-perturbation envelope at the fixed radius `rho`. -/
noncomputable def higham21Eq21_11UniformGramEnvelope {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Fin m -> Fin m -> Real :=
  undetGramPerturbationComponentBudget A
    (higham21Eq21_11UniformDirectionEnvelope A) rho

/-- The fixed-radius Chapter 7 contraction controlling all perturbed Gram
    inverses arising from normalized rowwise directions. -/
noncomputable def higham21Eq21_11UniformGramContraction {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  rho * infNorm
    (ch7InverseFirstProductSensitivity m (undetGramNonsingInv A)
      (higham21Eq21_11UniformGramEnvelope A rho))

/-- One contraction condition at `rho` packages both the Q-method smallness
    condition and the uniform perturbed-Gram inverse condition. -/
noncomputable def higham21Eq21_11UniformContraction {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  max
    (rho * higham21Cond2With A (undetAplusOfGramNonsingInv A))
    (higham21Eq21_11UniformGramContraction A rho)

/-- A direction- and parameter-independent Frobenius bound for every
    perturbed Gram inverse in the fixed `rho` neighborhood. -/
noncomputable def higham21Eq21_11UniformGramInverseBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  let c := higham21Eq21_11UniformGramContraction A rho
  Real.sqrt ((m : Real) * (m : Real)) *
    (((m : Real) * (1 / (1 - c))) * infNorm (undetGramNonsingInv A))

/-- A direction-independent Frobenius bound obtained from the uniform entry
    envelope. -/
noncomputable def higham21Eq21_11UniformDirectionFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  Real.sqrt ((m : Real) * (n : Real)) * frobNormRect A

noncomputable def higham21Eq21_11UniformGramLinearFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  2 * frobNormRect A * higham21Eq21_11UniformDirectionFrobBound A

noncomputable def higham21Eq21_11UniformGramQuadraticFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  higham21Eq21_11UniformDirectionFrobBound A ^ 2

noncomputable def higham21Eq21_11UniformGramAbsFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformGramLinearFrobBound A +
    rho * higham21Eq21_11UniformGramQuadraticFrobBound A

noncomputable def higham21Eq21_11UniformFirstProductFrobBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  frobNorm (undetGramNonsingInv A) *
    higham21Eq21_11UniformGramAbsFrobBound A rho

noncomputable def higham21Eq21_11UniformInverseQuadraticBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformFirstProductFrobBound A rho ^ 2 *
    higham21Eq21_11UniformGramInverseBound A rho

noncomputable def higham21Eq21_11UniformLinearizedLinearBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  frobNorm (undetGramNonsingInv A) ^ 2 *
    higham21Eq21_11UniformGramLinearFrobBound A

noncomputable def higham21Eq21_11UniformLinearizedQuadraticBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  frobNorm (undetGramNonsingInv A) ^ 2 *
    higham21Eq21_11UniformGramQuadraticFrobBound A

noncomputable def higham21Eq21_11UniformInverseDifferenceBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformLinearizedLinearBound A +
    rho * higham21Eq21_11UniformLinearizedQuadraticBound A +
    rho * higham21Eq21_11UniformInverseQuadraticBound A rho

noncomputable def higham21Eq21_11UniformCancellationBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformLinearizedQuadraticBound A +
    higham21Eq21_11UniformInverseQuadraticBound A rho

/-- The absolute quadratic remainder coefficient.  It contains no normalized
    direction and no actual perturbation parameter. -/
noncomputable def higham21Eq21_11UniformAbsoluteCoefficient {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (rho : Real) : Real :=
  frobNormRect A * higham21Eq21_11UniformCancellationBound A rho * vecNorm2 b +
    higham21Eq21_11UniformDirectionFrobBound A *
      higham21Eq21_11UniformInverseDifferenceBound A rho * vecNorm2 b

/-- The relative fixed-radius coefficient in the uniform form of (21.11).
    It depends only on `A`, `b`, `rho`, and the matrix dimensions. -/
noncomputable def higham21Eq21_11UniformRelativeCoefficient {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real) (rho : Real) : Real :=
  higham21Eq21_11UniformAbsoluteCoefficient A b rho /
    vecNorm2 (rectMatMulVec (undetAplusOfGramNonsingInv A) b)
































































































































































































































































































































































































































































































































































































































































































































end NumStability
