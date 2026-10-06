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
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.Perturbation.Componentwise.UnderdeterminedSolve
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
# Algorithms.LinearSystems.Underdetermined.Perturbation.FixedRadius.Radius

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- A derived fixed-radius neighborhood for Theorem 21.1 and equation (21.6).



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- The exact Euclidean operator norm of a real rectangular matrix, routed
    through the operator norm of its complexification.  The real/complex
    bridge in `Analysis/SingularValues/Realification.lean` shows that this is
    also the sharp radius for the repository predicate `rectOpNorm2Le`. -/
noncomputable def higham21RectOpNorm2 {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  complexMatrixOp2 (realRectToCMatrix A)

theorem higham21RectOpNorm2_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    0 <= higham21RectOpNorm2 A := by
  exact complexMatrixOp2_nonneg _
















/-- The exact rectangular norm is an admissible vector-action certificate. -/
theorem higham21_rectOpNorm2Le_exact {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    rectOpNorm2Le A (higham21RectOpNorm2 A) := by
  exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le A le_rfl

/-- Conversely, every nonnegative vector-action certificate bounds the exact
    rectangular operator norm. -/
theorem higham21RectOpNorm2_le_of_rectOpNorm2Le {m n : Nat}
    (A : Fin m -> Fin n -> Real) {c : Real}
    (hc : 0 <= c) (hA : rectOpNorm2Le A c) :
    higham21RectOpNorm2 A <= c := by
  exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A hc hA

/-- A fixed Gram-perturbation envelope for directions satisfying `abs D <= E`.
    The quadratic part is frozen at unit radius, so every smaller signed
    perturbation has a Gram perturbation bounded by `abs t` times this table. -/
noncomputable def higham21PerturbationGramEnvelope {m n : Nat}
    (A E : Fin m -> Fin n -> Real) : Fin m -> Fin m -> Real :=
  undetGramPerturbationComponentBudget A E 1

/-- Chapter 7 sensitivity of the fixed Gram envelope. -/
noncomputable def higham21PerturbationGramSensitivity {m n : Nat}
    (A E : Fin m -> Fin n -> Real) : Real :=
  infNorm
    (ch7InverseFirstProductSensitivity m (undetGramNonsingInv A)
      (higham21PerturbationGramEnvelope A E))

/-- A positive radius that simultaneously controls a supplied operator bound
    `q` for `A^+ D` and the fixed Gram-envelope sensitivity.  The factor two
    leaves a half-radius margin for both contractions. -/
noncomputable def higham21PerturbationRadius {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) : Real :=
  1 /
    (2 *
      (1 + max q (higham21PerturbationGramSensitivity A E)))

/-- A direction-independent inverse bound once the Gram contraction is at
    most `1/2`. -/
noncomputable def higham21PerturbationGramInverseBound {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Real :=
  Real.sqrt ((m : Real) * (m : Real)) *
    (((m : Real) * 2) * infNorm (undetGramNonsingInv A))






/-- A canonical finite operator envelope for one perturbation direction. -/
noncomputable def higham21PerturbationDirectionProductBound {m n : Nat}
    (A D : Fin m -> Fin n -> Real) : Real :=
  frobNorm
    (rectMatMul (undetAplusOfGramNonsingInv A) D)

/-- The single-direction radius obtained without any caller-supplied norm
    constant. -/
noncomputable def higham21PerturbationDirectionRadius {m n : Nat}
    (A D E : Fin m -> Fin n -> Real) : Real :=
  higham21PerturbationRadius A E
    (higham21PerturbationDirectionProductBound A D)

theorem higham21PerturbationGramSensitivity_nonneg {m n : Nat}
    (A E : Fin m -> Fin n -> Real) :
    0 <= higham21PerturbationGramSensitivity A E :=
  infNorm_nonneg _


















/-- The derived radius is strictly positive for every nonnegative operator
    envelope. -/
theorem higham21PerturbationRadius_pos {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    0 < higham21PerturbationRadius A E q := by
  let s : Real := higham21PerturbationGramSensitivity A E
  let M : Real := max q s
  have hM : 0 <= M := by
    exact hq.trans (le_max_left q s)
  have hden : 0 < 2 * (1 + M) :=
    mul_pos (by norm_num) (by linarith)
  change 0 < 1 / (2 * (1 + M))
  exact one_div_pos.mpr hden

/-- The derived radius lies inside the unit neighborhood used to freeze the
    quadratic Gram envelope. -/
theorem higham21PerturbationRadius_le_one {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (q : Real) (hq : 0 <= q) :
    higham21PerturbationRadius A E q <= 1 := by
  let s : Real := higham21PerturbationGramSensitivity A E
  let M : Real := max q s
  have hM : 0 <= M := by
    exact hq.trans (le_max_left q s)
  have hden : 0 < 2 * (1 + M) :=
    mul_pos (by norm_num) (by linarith)
  change 1 / (2 * (1 + M)) <= 1
  apply (div_le_iff₀ hden).2
  nlinarith

































theorem higham21PerturbationGramInverseBound_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    0 <= higham21PerturbationGramInverseBound A := by
  exact mul_nonneg (Real.sqrt_nonneg _)
    (mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le m) (by norm_num))
      (infNorm_nonneg _))

/-- The canonical Frobenius product bound is an operator-2 certificate. -/
theorem higham21PerturbationDirectionProduct_rectOpNorm2Le {m n : Nat}
    (A D : Fin m -> Fin n -> Real) :
    rectOpNorm2Le
      (rectMatMul (undetAplusOfGramNonsingInv A) D)
      (higham21PerturbationDirectionProductBound A D) := by
  exact
    rectOpNorm2Le_of_opNorm2Le_square _
      (opNorm2Le_of_frobNorm_self _)

theorem higham21PerturbationDirectionRadius_pos {m n : Nat}
    (A D E : Fin m -> Fin n -> Real) :
    0 < higham21PerturbationDirectionRadius A D E := by
  simpa [higham21PerturbationDirectionRadius] using
    higham21PerturbationRadius_pos A E
      (higham21PerturbationDirectionProductBound A D)
      (frobNorm_nonneg _)

















/-- Scalar multiplication scales a rectangular operator-2 certificate by the
    absolute value of the scalar. -/
theorem higham21_rectOpNorm2Le_const_mul_abs {m n : Nat}
    (M : Fin m -> Fin n -> Real) (a c : Real)
    (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (fun i j => a * M i j) (abs a * c) := by
  intro x
  have haction :
      rectMatMulVec (fun i j => a * M i j) x =
        fun i => a * rectMatMulVec M x i := by
    ext i
    unfold rectMatMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    vecNorm2 (rectMatMulVec (fun i j => a * M i j) x) =
        abs a * vecNorm2 (rectMatMulVec M x) := by
      rw [haction, vecNorm2_smul]
    _ <= abs a * (c * vecNorm2 x) :=
      mul_le_mul_of_nonneg_left (hM x) (abs_nonneg a)
    _ = (abs a * c) * vecNorm2 x := by ring

/-- Scaling a direction scales its canonical pseudoinverse product
    certificate. -/
theorem higham21_scaled_pseudoinverse_product_rectOpNorm2Le {m n : Nat}
    (A D : Fin m -> Fin n -> Real) (t q : Real)
    (hProduct :
      rectOpNorm2Le
        (rectMatMul (undetAplusOfGramNonsingInv A) D) q) :
    rectOpNorm2Le
      (rectMatMul (undetAplusOfGramNonsingInv A)
        (fun i j => t * D i j))
      (abs t * q) := by
  have hscaled :=
    higham21_rectOpNorm2Le_const_mul_abs
      (rectMatMul (undetAplusOfGramNonsingInv A) D) t q hProduct
  have hmul :
      rectMatMul (undetAplusOfGramNonsingInv A)
          (fun i j => t * D i j) =
        fun i j =>
          t * rectMatMul (undetAplusOfGramNonsingInv A) D i j := by
    ext i j
    unfold rectMatMul
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hmul]
  exact hscaled





















































































































































































































































































































































/-- A nonzero right-hand side forces a positive row dimension. -/
theorem higham21_row_dimension_pos_of_rhs_ne_zero {m : Nat}
    (b : Fin m -> Real) (hb : Not (b = 0)) : 0 < m := by
  by_contra hm
  have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
  subst m
  apply hb
  funext i
  exact Fin.elim0 i















































































































































































































































































end NumStability
