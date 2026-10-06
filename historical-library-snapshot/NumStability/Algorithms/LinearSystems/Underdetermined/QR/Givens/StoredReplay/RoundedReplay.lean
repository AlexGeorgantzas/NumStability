import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Basic
import NumStability.Algorithms.LinearSystems.LU.Doolittle.Certificates
import NumStability.Algorithms.LinearSystems.LeastSquares.AugmentedSystem
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.QRSolve
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.LeastSquares.StoredQR
import NumStability.Algorithms.LinearSystems.QR.GivensQR
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication
import NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.InverseBounds
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Givens.BackwardError.Core
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Asymptotics.Bounds
import NumStability.Analysis.Conditioning.DistanceToSingularity
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.LinearOperators.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Comparisons
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.MatrixNorms.SpectralRadius
import NumStability.Analysis.MatrixNorms.UnitarilyInvariant
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.OperatorNorms.Basic
import NumStability.Analysis.Perturbation.LeastSquares.AugmentedSystem
import NumStability.Analysis.Perturbation.LeastSquares.BackwardError
import NumStability.Analysis.Perturbation.LeastSquares.Basic
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.Summation.Signs
import NumStability.Analysis.VectorNorms.Basic
import NumStability.FloatingPoint.Model

/-!
# Algorithms.LinearSystems.Underdetermined.QR.Givens.StoredReplay.RoundedReplay

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Rounded stored-Givens application endpoint for Theorem 21.4.



namespace NumStability

/-! ## Stored rotations and their rounded transpose replay -/

/-- One computed Givens rotation retained after the QR sweep.

The coefficients are stored in the orientation used while reducing `A^T`.
The final Q-method action therefore replays the transpose of each rotation. -/
structure Higham21StoredGivensRotation (n : Nat) where
  p : Fin n
  q : Fin n
  distinct : Not (p = q)
  c_hat : Real
  s_hat : Real

/-- Rounded application of the transpose of one stored Givens rotation.

For the repository convention
`G = [[c,s],[-s,c]]`, transposition replaces `s` by `-s`.  Floating-point
negation is exact, so the existing rounded two-coordinate kernel can be
reused directly. -/
noncomputable def Higham21StoredGivensRotation.applyTranspose
    {n : Nat} (fp : FPModel) (g : Higham21StoredGivensRotation n)
    (x : Fin n -> Real) : Fin n -> Real :=
  fl_givensApply fp n g.p g.q g.c_hat (-g.s_hat) x

/-- Replay stored rotations in QR order to apply their transposed product.

If `trace = [G_0,...,G_{r-1}]` is the reduction order, `foldr` computes
`G_0^T (G_1^T (... (G_{r-1}^T z)))`, which is the Q-method action. -/
noncomputable def higham21ApplyStoredGivensRotationsTranspose
    (fp : FPModel) (n : Nat)
    (trace : List (Higham21StoredGivensRotation n))
    (z : Fin n -> Real) : Fin n -> Real :=
  trace.foldr
    (fun g x => Higham21StoredGivensRotation.applyTranspose fp g x) z

/-! ## Fixed-accumulation application interface -/

/-- A per-input certificate for rounded stored-rotation replay.

`Q_hat` may depend on the input vector.  This is the right strength for a
rounded application: it records that this concrete output is an action by a
matrix within Frobenius distance `etaQ` of the fixed exact QR factor.  The
historical Householder name on `HouseholderQRPanelQhatFixedAccumError` is only
a container; its fields are method-independent. -/
structure Higham21GivensFixedAccumulationCertificate
    (fp : FPModel) (n : Nat)
    (Q_ref : Fin n -> Fin n -> Real)
    (trace : List (Higham21StoredGivensRotation n))
    (z : Fin n -> Real) (etaQ : Real) where
  Q_hat : Fin n -> Fin n -> Real
  fixed : HouseholderQRPanelQhatFixedAccumError n Q_ref Q_hat etaQ
  replay_eq :
    higham21ApplyStoredGivensRotationsTranspose fp n trace z =
      matMulVec n Q_hat z

/-- Any fixed-accumulation radius carried by the certificate is nonnegative. -/
theorem higham21_fixed_accumulation_radius_nonneg
    {n : Nat} {Q Q_hat : Fin n -> Fin n -> Real} {etaQ : Real}
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat etaQ) :
    0 <= etaQ := by
  rcases hQerr.result with ⟨DeltaQ, _hrep, hDeltaQ⟩
  exact le_trans (frobNorm_nonneg DeltaQ) hDeltaQ

/-- Global bridge expected from an implementation that retains the staged QR
rotation trace.

This is the sole missing executable bridge in the current upstream API:
`fl_givensQRStageFold` returns only the reduced panel, so it must be extended
to expose the computed coefficients in QR order and prove that reverse
transpose replay satisfies this predicate relative to the same exact factor
selected by `higham21GivensQMethodQ`. -/
def Higham21GivensStoredReplayBridge
    (fp : FPModel) (n : Nat)
    (Q_ref : Fin n -> Fin n -> Real)
    (trace : List (Higham21StoredGivensRotation n))
    (etaQ : Real) : Prop :=
  forall z : Fin n -> Real, exists Q_hat : Fin n -> Fin n -> Real,
    HouseholderQRPanelQhatFixedAccumError n Q_ref Q_hat etaQ /\
    higham21ApplyStoredGivensRotationsTranspose fp n trace z =
      matMulVec n Q_hat z

/-! ## Method-independent rounded-Q handoff -/

/-- Common rowwise coefficient obtained from a QR residual `etaQR`, the
triangular-solve residual `gamma_m`, and a fixed accumulated-Q radius `etaQ`.

The first branch controls the inverse-induced perturbation in the first
system.  The second controls the rounded product in the transpose-range
system. -/
noncomputable def Higham21FixedAccumulationRoundedRowwiseCoefficient
    (fp : FPModel) (m : Nat) (etaQR etaQ : Real) : Real :=
  let etaR := gamma fp m
  let etaBase := etaQR + etaR * (1 + etaQR)
  let qinv := 1 / (1 - etaQ)
  max
    (etaBase + (qinv * etaQ) * (1 + etaBase))
    (etaQR + etaQ * (1 + etaQR))

theorem Higham21FixedAccumulationRoundedRowwiseCoefficient_nonneg
    (fp : FPModel) (m : Nat) (etaQR etaQ : Real)
    (hetaQR : 0 <= etaQR) (hetaQ : 0 <= etaQ) :
    0 <= Higham21FixedAccumulationRoundedRowwiseCoefficient
      fp m etaQR etaQ := by
  have hsecond : 0 <= etaQR + etaQ * (1 + etaQR) :=
    add_nonneg hetaQR
      (mul_nonneg hetaQ (add_nonneg zero_le_one hetaQR))
  exact hsecond.trans (by
    unfold Higham21FixedAccumulationRoundedRowwiseCoefficient
    dsimp
    exact le_max_right _ _)

/-- An upper-triangular square block with nonzero diagonal has an exact
preimage for every vector.  This supplies the coordinate used by the second
perturbed system without referring to a particular QR implementation. -/
theorem higham21_upper_square_exists_exact_preimage
    {m : Nat} (R_hat : Fin m -> Fin m -> Real)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hdiag : forall i : Fin m, Not (R_hat i i = 0))
    (y1 : Fin m -> Real) :
    exists y : Fin m -> Real, rectMatMulVec R_hat y = y1 := by
  have hdet : Not (Matrix.det
      (R_hat : Matrix (Fin m) (Fin m) Real) = 0) :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m R_hat hupper hdiag
  have hInverse : IsInverse m R_hat (nonsingInv m R_hat) :=
    isInverse_nonsingInv_of_det_ne_zero m R_hat hdet
  refine ⟨matMulVec m (nonsingInv m R_hat) y1, ?_⟩
  change matMulVec m R_hat (matMulVec m (nonsingInv m R_hat) y1) = y1
  exact matMulVec_of_isRightInverse
    R_hat (nonsingInv m R_hat) hInverse.2 y1















































































































































































































































/-! ## Staged-Givens specialization -/

/-- Top square block of the concrete staged Givens `R_hat`. -/
noncomputable def higham21GivensRoundedRTop
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin m -> Fin m -> Real := fun i j =>
  higham21GivensQMethodRTall fp m k A (Fin.castAdd k i) j

/-- Rounded triangular coordinate used as the input to stored-rotation replay. -/
noncomputable def higham21GivensRoundedY1
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real) :
    Fin m -> Real :=
  fl_forwardSub fp m (matTranspose (higham21GivensRoundedRTop fp m k A)) b

/-- Actual rounded output obtained by replaying a supplied stored Givens trace. -/
noncomputable def higham21GivensStoredRoundedOutput
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (trace : List (Higham21StoredGivensRotation (m + k))) :
    Fin (m + k) -> Real :=
  higham21ApplyStoredGivensRotationsTranspose fp (m + k) trace
    (Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k -> Real))

/-- Per-input fixed-accumulation certificate specialized to the staged Givens
Q-method input and its exact certificate factor. -/
abbrev Higham21GivensQMethodApplicationCertificate
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hvalidGivens : gammaValid fp 8)
    (trace : List (Higham21StoredGivensRotation (m + k)))
    (etaQ : Real) :=
  Higham21GivensFixedAccumulationCertificate fp (m + k)
    (higham21GivensQMethodQ fp m k A hvalidGivens) trace
    (Fin.append (higham21GivensRoundedY1 fp m k A b)
      (0 : Fin k -> Real)) etaQ






















































































































































































































/-- Staged-Givens specialization of the global stored-replay bridge. -/
def Higham21GivensQMethodStoredReplayBridge
    (fp : FPModel) (m k : Nat)
    (A : Fin m -> Fin (m + k) -> Real)
    (hvalidGivens : gammaValid fp 8)
    (trace : List (Higham21StoredGivensRotation (m + k)))
    (etaQ : Real) : Prop :=
  Higham21GivensStoredReplayBridge fp (m + k)
    (higham21GivensQMethodQ fp m k A hvalidGivens) trace etaQ









































































end NumStability
