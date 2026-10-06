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
# Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.CorrectedRecurrence.Core

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, unnumbered MGS discussion in Section 21.3 (printed pp. 412-413).



namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## The displayed comparison bound -/

/-- The rectangular operator-2 condition-number product attached to a supplied
    pseudoinverse candidate.  When `Aplus` is the Moore--Penrose inverse this is
    the source quantity `kappa_2(A) = ||A||_2 ||Aplus||_2`. -/
noncomputable def higham21MGSRectKappa2With {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix A) *
    complexMatrixOp2 (realRectToCMatrix Aplus)




























































/-! ## Naive forward formation and its two exact error channels -/

/-- The exact real matrix-vector expression denoted by `x = Q*y` in the
    unnumbered MGS paragraph.  This definition is not a rounded matvec. -/
noncomputable def higham21MGSNaiveFormation {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) : Fin n -> Real :=
  rectMatMulVec Q y

/-- Orthonormal columns make the Chapter 19 Gram residual exactly zero. -/
theorem higham21_mgs_orthogonalityResidual_eq_zero {m n : Nat}
    {Q : Fin n -> Fin m -> Real}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    gramSchmidtOrthogonalityResidual Q = 0 := by
  ext i j
  unfold gramSchmidtOrthogonalityResidual
  rw [hQ i j]
  simp

/-- Exact algebra behind the naive formation distinction:
    `Q^T(Q*y) = y + (Q^T Q - I)y`.

    Thus loss of orthogonality and arithmetic error in forming `Q*y` are
    separate issues; this theorem makes no instability claim. -/
theorem higham21_mgs_naive_transpose_action {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) :
    rectMatMulVec (finiteTranspose Q) (higham21MGSNaiveFormation Q y) =
      fun i => y i +
        rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y i := by
  unfold higham21MGSNaiveFormation
  rw [← rectMatMulVec_rectMatMul (finiteTranspose Q) Q y]
  change rectMatMulVec (rectangularGram Q) y =
    fun i => y i +
      rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y i
  ext i
  unfold rectMatMulVec gramSchmidtOrthogonalityResidual
  calc
    (Finset.univ.sum fun j : Fin m => rectangularGram Q i j * y j) =
        Finset.univ.sum fun j : Fin m =>
          (idMatrix m i j +
            (rectangularGram Q i j - idMatrix m i j)) * y j := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (Finset.univ.sum fun j : Fin m => idMatrix m i j * y j) +
          Finset.univ.sum fun j : Fin m =>
            (rectangularGram Q i j - idMatrix m i j) * y j := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = y i + Finset.univ.sum fun j : Fin m =>
          (rectangularGram Q i j - idMatrix m i j) * y j := by
          have hid :
              (Finset.univ.sum fun j : Fin m => idMatrix m i j * y j) =
                y i := by
            simpa [rectMatMulVec] using
              congrFun (rectMatMulVec_idMatrix y) i
          rw [hid]

/-- A rounded or otherwise approximate forward formation is represented by an
    explicit additive error.  In the exact interpretation the error is zero. -/
structure Higham21MGSNaiveFormationErrorInterface {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (xhat error : Fin n -> Real) : Prop where
  output_eq : xhat = fun i => higham21MGSNaiveFormation Q y i + error i

theorem higham21_mgs_naive_formation_exact_interface {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) :
    Higham21MGSNaiveFormationErrorInterface Q y
      (higham21MGSNaiveFormation Q y) (0 : Fin n -> Real) := by
  constructor
  funext i
  simp

theorem higham21_mgs_naive_formation_forward_error_eq {m n : Nat}
    {Q : Fin n -> Fin m -> Real} {y : Fin m -> Real}
    {xhat error : Fin n -> Real}
    (h : Higham21MGSNaiveFormationErrorInterface Q y xhat error) :
    (fun i => xhat i - higham21MGSNaiveFormation Q y i) = error := by
  ext i
  have hi := congrFun h.output_eq i
  rw [hi]
  ring

theorem higham21_mgs_naive_formation_forward_error_le {m n : Nat}
    {Q : Fin n -> Fin m -> Real} {y : Fin m -> Real}
    {xhat error : Fin n -> Real} {eta : Real}
    (h : Higham21MGSNaiveFormationErrorInterface Q y xhat error)
    (herror : vecNorm2 error <=
      eta * vecNorm2 (higham21MGSNaiveFormation Q y)) :
    vecNorm2 (fun i => xhat i - higham21MGSNaiveFormation Q y i) <=
      eta * vecNorm2 (higham21MGSNaiveFormation Q y) := by
  rw [higham21_mgs_naive_formation_forward_error_eq h]
  exact herror

/-- The exact transformed action of an approximate forward formation.  The
    first added term is the MGS orthogonality defect; the second is the
    independent formation error transported by `Q^T`. -/
theorem higham21_mgs_naive_formation_error_transpose_action {m n : Nat}
    {Q : Fin n -> Fin m -> Real} {y : Fin m -> Real}
    {xhat error : Fin n -> Real}
    (h : Higham21MGSNaiveFormationErrorInterface Q y xhat error) :
    rectMatMulVec (finiteTranspose Q) xhat =
      fun i => y i +
        rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y i +
        rectMatMulVec (finiteTranspose Q) error i := by
  calc
    rectMatMulVec (finiteTranspose Q) xhat =
        rectMatMulVec (finiteTranspose Q)
          (fun j => higham21MGSNaiveFormation Q y j + error j) := by
            rw [h.output_eq]
    _ = fun i =>
        rectMatMulVec (finiteTranspose Q)
            (higham21MGSNaiveFormation Q y) i +
          rectMatMulVec (finiteTranspose Q) error i :=
      rectMatMulVec_add (finiteTranspose Q)
        (higham21MGSNaiveFormation Q y) error
    _ = fun i => y i +
        rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y i +
        rectMatMulVec (finiteTranspose Q) error i := by
          rw [higham21_mgs_naive_transpose_action]

/-- Transposing an economy factorization `A^T = Q*R` gives
    `A = R^T*Q^T`. -/
theorem higham21_mgs_transpose_economy_factor {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Q : Fin n -> Fin m -> Real)
    (R : Fin m -> Fin m -> Real)
    (hfactor : finiteTranspose A = matMulRect n m m Q R) :
    A = rectMatMul (finiteTranspose R) (finiteTranspose Q) := by
  ext i j
  have hij : A i j = matMulRect n m m Q R j i := by
    simpa [finiteTranspose] using congrFun (congrFun hfactor j) i
  calc
    A i j = matMulRect n m m Q R j i := hij
    _ = rectMatMul (finiteTranspose R) (finiteTranspose Q) i j := by
      unfold matMulRect rectMatMul finiteTranspose
      apply Finset.sum_congr rfl
      intro k _
      ring

/-- At system level the same exact split is
    `A*xhat = b + R^T(Q^T Q-I)y + A*error`, assuming `A^T=Q*R` and
    `R^T*y=b`. -/
theorem higham21_mgs_naive_formation_system_error {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Q : Fin n -> Fin m -> Real)
    (R : Fin m -> Fin m -> Real) (b y : Fin m -> Real)
    (xhat error : Fin n -> Real)
    (hfactor : finiteTranspose A = matMulRect n m m Q R)
    (hsolve : rectMatMulVec (finiteTranspose R) y = b)
    (hformation :
      Higham21MGSNaiveFormationErrorInterface Q y xhat error) :
    rectMatMulVec A xhat =
      fun i => b i +
        rectMatMulVec (finiteTranspose R)
          (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y) i +
        rectMatMulVec A error i := by
  have hA := higham21_mgs_transpose_economy_factor A Q R hfactor
  have hcore :
      rectMatMulVec A (higham21MGSNaiveFormation Q y) =
        fun i => b i +
          rectMatMulVec (finiteTranspose R)
            (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y) i := by
    calc
      rectMatMulVec A (higham21MGSNaiveFormation Q y) =
          rectMatMulVec
            (rectMatMul (finiteTranspose R) (finiteTranspose Q))
            (higham21MGSNaiveFormation Q y) := by rw [hA]
      _ = rectMatMulVec (finiteTranspose R)
          (rectMatMulVec (finiteTranspose Q)
            (higham21MGSNaiveFormation Q y)) :=
        rectMatMulVec_rectMatMul (finiteTranspose R) (finiteTranspose Q)
          (higham21MGSNaiveFormation Q y)
      _ = rectMatMulVec (finiteTranspose R)
          (fun i => y i +
            rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y i) := by
        rw [higham21_mgs_naive_transpose_action]
      _ = fun i => rectMatMulVec (finiteTranspose R) y i +
          rectMatMulVec (finiteTranspose R)
            (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y) i :=
        rectMatMulVec_add (finiteTranspose R) y
          (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y)
      _ = fun i => b i +
          rectMatMulVec (finiteTranspose R)
            (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y) i := by
        rw [hsolve]
  calc
    rectMatMulVec A xhat =
        rectMatMulVec A
          (fun j => higham21MGSNaiveFormation Q y j + error j) := by
            rw [hformation.output_eq]
    _ = fun i => rectMatMulVec A (higham21MGSNaiveFormation Q y) i +
        rectMatMulVec A error i :=
      rectMatMulVec_add A (higham21MGSNaiveFormation Q y) error
    _ = fun i => b i +
        rectMatMulVec (finiteTranspose R)
          (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y) i +
        rectMatMulVec A error i := by
      rw [hcore]

theorem higham21_mgs_naive_formation_exact_system_residual {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Q : Fin n -> Fin m -> Real)
    (R : Fin m -> Fin m -> Real) (b y : Fin m -> Real)
    (hfactor : finiteTranspose A = matMulRect n m m Q R)
    (hsolve : rectMatMulVec (finiteTranspose R) y = b) :
    rectMatMulVec A (higham21MGSNaiveFormation Q y) =
      fun i => b i +
        rectMatMulVec (finiteTranspose R)
          (rectMatMulVec (gramSchmidtOrthogonalityResidual Q) y) i := by
  have h := higham21_mgs_naive_formation_system_error
    A Q R b y (higham21MGSNaiveFormation Q y) (0 : Fin n -> Real)
    hfactor hsolve (higham21_mgs_naive_formation_exact_interface Q y)
  simpa [rectMatMulVec] using h

theorem higham21_mgs_naive_formation_solves_of_orthonormal {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Q : Fin n -> Fin m -> Real)
    (R : Fin m -> Fin m -> Real) (b y : Fin m -> Real)
    (hfactor : finiteTranspose A = matMulRect n m m Q R)
    (hsolve : rectMatMulVec (finiteTranspose R) y = b)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectMatMulVec A (higham21MGSNaiveFormation Q y) = b := by
  have h := higham21_mgs_naive_formation_exact_system_residual
    A Q R b y hfactor hsolve
  rw [higham21_mgs_orthogonalityResidual_eq_zero hQ] at h
  simpa [rectMatMulVec] using h

theorem higham21_mgs_naive_transpose_action_of_orthonormal {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectMatMulVec (finiteTranspose Q) (higham21MGSNaiveFormation Q y) = y := by
  have h := higham21_mgs_naive_transpose_action Q y
  rw [higham21_mgs_orthogonalityResidual_eq_zero hQ] at h
  simpa [rectMatMulVec] using h




































/-! ## The corrected backward recurrence -/

/-- One exact real step of the corrected formation on printed page 413. -/
noncomputable def higham21MGSCorrectedStep {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) : Fin n -> Real :=
  fun i => x i - (gsDot (gsColumn Q k) x - y k) * Q i k

/-- The displayed corrected update rewritten as
    `x + y_k*q_k - (q_k^T*x)*q_k`. -/
theorem higham21_mgs_corrected_step_rewrite {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) :
    higham21MGSCorrectedStep Q y k x =
      fun i => x i + y k * Q i k - gsDot (gsColumn Q k) x * Q i k := by
  funext i
  unfold higham21MGSCorrectedStep
  ring

/-- If the current state is orthogonal to `q_k`, the correction term is
    exactly zero and the step is ordinary accumulation. -/
theorem higham21_mgs_corrected_step_of_dot_eq_zero {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real)
    (hdot : gsDot (gsColumn Q k) x = 0) :
    higham21MGSCorrectedStep Q y k x =
      fun i => x i + y k * Q i k := by
  funext i
  unfold higham21MGSCorrectedStep
  rw [hdot]
  ring

/-- For orthonormal columns, a `Q*z` state with zero `k`th coefficient is
    orthogonal to `q_k`.  This is the exact-arithmetic premise behind the
    source's statement that the final term vanishes for later-column states. -/
theorem higham21_mgs_column_dot_naive_formation_eq_zero {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (z : Fin m -> Real) (k : Fin m)
    (hQ : GramSchmidtOrthonormalColumns Q) (hzk : z k = 0) :
    gsDot (gsColumn Q k) (higham21MGSNaiveFormation Q z) = 0 := by
  have hk := congrFun
    (higham21_mgs_naive_transpose_action_of_orthonormal Q z hQ) k
  change gsDot (gsColumn Q k) (higham21MGSNaiveFormation Q z) = z k at hk
  simpa [hzk] using hk

theorem higham21_mgs_corrected_step_on_later_column_state {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y z : Fin m -> Real) (k : Fin m)
    (hQ : GramSchmidtOrthonormalColumns Q) (hzk : z k = 0) :
    higham21MGSCorrectedStep Q y k (higham21MGSNaiveFormation Q z) =
      fun i => higham21MGSNaiveFormation Q z i + y k * Q i k :=
  higham21_mgs_corrected_step_of_dot_eq_zero Q y k
    (higham21MGSNaiveFormation Q z)
    (higham21_mgs_column_dot_naive_formation_eq_zero Q z k hQ hzk)

/-- Real-valued specification of the backward recurrence.

    The source prints an `n`-step loop although the economy `Q` has `m`
    columns.  This well-typed version has terminal state `x^(m)=0`, with
    zero-based step `k` taking state `k+1` to state `k`. -/
structure Higham21MGSCorrectedBackwardRecurrence {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (state : Fin (m + 1) -> Fin n -> Real) (xhat : Fin n -> Real) : Prop where
  terminal : state (Fin.last m) = (0 : Fin n -> Real)
  step : forall k : Fin m,
    state k.castSucc =
      higham21MGSCorrectedStep Q y k (state k.succ)
  output : xhat = state 0

/-! ## Rowwise stability handoff -/

/-- The combined certificate sufficient for Theorem-21.4-level rowwise
    backward stability of the corrected MGS formation.

    `Rrepair` may include the triangular-solve backward perturbation.  The
    `repaired_output` field is the finite-precision fact specific to the
    corrected recurrence: its output acts as `Qrepair*y`. -/
structure Higham21MGSCorrectedRowwiseCertificate {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (Rrepair : Fin m -> Fin m -> Real)
    (Qrepair DeltaAT : Fin n -> Fin m -> Real)
    (y : Fin m -> Real) (state : Fin (m + 1) -> Fin n -> Real)
    (xhat : Fin n -> Real) (eta : Real) : Prop where
  recurrence : Higham21MGSCorrectedBackwardRecurrence Qhat y state xhat
  upper : IsUpperTrapezoidal m m Rrepair
  orthonormal : GramSchmidtOrthonormalColumns Qrepair
  factor : forall i j,
    finiteTranspose A i j + DeltaAT i j =
      matMulRect n m m Qrepair Rrepair i j
  triangular_solve : rectMatMulVec (finiteTranspose Rrepair) y = b
  right_inverse : Exists fun Rinv : Fin m -> Fin m -> Real =>
    IsRightInverse m Rrepair Rinv
  repaired_output : xhat = higham21MGSNaiveFormation Qrepair y
  column_bound : forall j,
    columnFrob DeltaAT j <= eta * columnFrob (finiteTranspose A) j
  eta_nonneg : 0 <= eta












































/-- Chapter 19's MGS certificate already supplies the triangular shape,
    orthonormal repair, factor identity, and columnwise perturbation needed by
    the corrected-method handoff. -/
theorem higham21_mgs_backward_error_repair_handoff
    {m n : Nat} {A : Fin m -> Fin n -> Real}
    {Qhat : Fin n -> Fin m -> Real} {Rhat : Fin m -> Fin m -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : ModifiedGramSchmidtBackwardError n m
      (finiteTranspose A) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder) :
    IsUpperTrapezoidal m m Rhat /\
      Exists fun Qrepair : Fin n -> Fin m -> Real =>
        Exists fun DeltaAT : Fin n -> Fin m -> Real =>
          GramSchmidtOrthonormalColumns Qrepair /\
          (forall i j,
            finiteTranspose A i j + DeltaAT i j =
              matMulRect n m m Qrepair Rhat i j) /\
          (forall j,
            columnFrob DeltaAT j <=
              c3 * u * columnFrob (finiteTranspose A) j) := by
  exact ⟨hMGS.upper, hMGS.r_factor⟩

/-- The missing upgrade of Chapter 19's `r_factor` channel for the corrected
    algorithm: select one supplied orthonormal repair whose action is the
    output of the backward recurrence.  This is an explicit interface only. -/
def Higham21MGSCorrectedMGSRepairCompatibility
    {m n : Nat} {A : Fin m -> Fin n -> Real}
    {Qhat : Fin n -> Fin m -> Real} {Rhat : Fin m -> Fin m -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : ModifiedGramSchmidtBackwardError n m
      (finiteTranspose A) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (y : Fin m -> Real) (xhat : Fin n -> Real) : Prop :=
  Exists fun Qrepair : Fin n -> Fin m -> Real =>
    Exists fun DeltaAT : Fin n -> Fin m -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (forall i j,
        finiteTranspose A i j + DeltaAT i j =
          matMulRect n m m Qrepair Rhat i j) /\
      (forall j,
        columnFrob DeltaAT j <=
          c3 * u * columnFrob (finiteTranspose A) j) /\
      xhat = higham21MGSNaiveFormation Qrepair y



































end

end NumStability
