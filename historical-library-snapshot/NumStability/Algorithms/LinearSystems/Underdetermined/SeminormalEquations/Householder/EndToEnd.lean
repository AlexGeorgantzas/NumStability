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
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.ComputedOutput.Core
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.Forward
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.ForwardError.RemainderBounds
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
# Algorithms.LinearSystems.Underdetermined.SeminormalEquations.HouseholderClosure.Closure

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete Householder-QR closure for the seminormal-equations path.







namespace NumStability

open scoped BigOperators

/-!
# Concrete signed SNE closure

The analysis-only QR perturbation below is chosen from the proved
implementation-backed Householder panel theorem.  The computed objects remain
the actual panel `Q`, its actual top square `R_hat`, the two rounded triangular
solves, and the rounded final `A^T` action.
-/

/-- The exact orthogonal witness returned by the concrete Householder panel. -/
noncomputable def higham21SNEHouseholderQFull
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin (m + k) -> Real :=
  fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)

/-- The actual tall factor returned by the concrete Householder panel. -/
noncomputable def higham21SNEHouseholderRTall
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin m -> Real :=
  fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)

/-- The actual square top block used by both rounded SNE triangular solves. -/
noncomputable def higham21SNEHouseholderRHat
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) : Fin m -> Fin m -> Real :=
  fun i j => higham21SNEHouseholderRTall fp A (Fin.castAdd k i) j

/-- The first `m` columns of the exact full Householder witness. -/
noncomputable def higham21SNEHouseholderEconomyQ
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) :
    Fin (m + k) -> Fin m -> Real :=
  fun i j => higham21SNEHouseholderQFull fp A i (Fin.castAdd k j)


























/-- The nonnegative Frobenius-unit majorant used to expose the componentwise
form of the concrete Householder QR backward error. -/
noncomputable def higham21SNEHouseholderG {m k : Nat} :
    Fin (m + k) -> Fin (m + k) -> Real :=
  highamHouseholderG (m + k)













































































































































































































theorem higham21_sne_householder_G_nonneg
    {m k : Nat} (hm : 0 < m) :
    forall p s, 0 <= (higham21SNEHouseholderG :
      Fin (m + k) -> Fin (m + k) -> Real) p s := by
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  simpa [higham21SNEHouseholderG] using highamHouseholderG_nonneg hn

theorem higham21_sne_householder_G_rectOpNorm2Le_one
    {m k : Nat} (hm : 0 < m) :
    rectOpNorm2Le
      (higham21SNEHouseholderG :
        Fin (m + k) -> Fin (m + k) -> Real) 1 := by
  have hn : 0 < m + k := lt_of_lt_of_le hm (Nat.le_add_right m k)
  apply opNorm2Le_to_rectOpNorm2Le
  apply opNorm2Le_of_frobNorm_le
  rw [higham21SNEHouseholderG, highamHouseholderG_frobNorm hn]






























































































/-- A sharper leading/quadratic split for final formation: the leading
coefficient remains the actual matrix-vector coefficient `gamma`, while a
master radius `theta` dominates only the genuinely quadratic products. -/
theorem higham21_sne_formation_error_le_gamma_plus_uniform_quadratic
    {m n : Nat}
    (theta rho gamma Kd q : Real)
    (htheta : 0 <= theta)
    (hrho : 0 <= rho) (hrho_theta : rho <= theta) (hrho_lt : rho < 1)
    (hgamma : 0 <= gamma) (hgamma_theta : gamma <= theta)
    (hKd : 0 <= Kd) (hq : 0 <= q)
    (A : Fin m -> Fin n -> Real)
    (ybar yhat : Fin m -> Real) (g : Fin n -> Real)
    (hFormation :
      vecNorm2 g <= gamma *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)))
    (hbar :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
        q / (1 - rho))
    (hd : vecNorm2 (fun i => ybar i - yhat i) <= theta * Kd) :
    vecNorm2 g <=
      gamma * q +
        theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hqdiv : 0 <= q / (1 - rho) := div_nonneg hq hden.le
  have hA : 0 <= frobNorm A := frobNorm_nonneg A
  have hsource := higham21_sne_source_abs_action_change A ybar yhat
  have hhat :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |yhat i|)) <=
        q / (1 - rho) + frobNorm A * (theta * Kd) := by
    exact hsource.trans (add_le_add hbar
      (mul_le_mul_of_nonneg_left hd hA))
  have hgammaBound : vecNorm2 g <=
      gamma * (q / (1 - rho) + frobNorm A * (theta * Kd)) := by
    exact hFormation.trans
      (mul_le_mul_of_nonneg_left hhat hgamma)
  have hgammaRho : gamma * rho <= theta ^ 2 := by
    calc
      gamma * rho <= theta * rho :=
        mul_le_mul_of_nonneg_right hgamma_theta hrho
      _ <= theta * theta :=
        mul_le_mul_of_nonneg_left hrho_theta htheta
      _ = theta ^ 2 := by ring
  have hgammaTheta : gamma * theta <= theta ^ 2 := by
    calc
      gamma * theta <= theta * theta :=
        mul_le_mul_of_nonneg_right hgamma_theta htheta
      _ = theta ^ 2 := by ring
  have hidentity : q / (1 - rho) = q + rho * (q / (1 - rho)) := by
    field_simp [ne_of_gt hden]
    ring
  have hsplit : gamma * (q / (1 - rho)) <=
      gamma * q + theta ^ 2 * (q / (1 - rho)) := by
    calc
      gamma * (q / (1 - rho)) =
          gamma * (q + rho * (q / (1 - rho))) :=
        congrArg (fun z => gamma * z) hidentity
      _ =
          gamma * q + (gamma * rho) * (q / (1 - rho)) := by ring
      _ <= gamma * q + theta ^ 2 * (q / (1 - rho)) :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_right hgammaRho hqdiv)
  have hdiffFormation :
      gamma * (frobNorm A * (theta * Kd)) <=
        theta ^ 2 * (frobNorm A * Kd) := by
    calc
      gamma * (frobNorm A * (theta * Kd)) =
          (gamma * theta) * (frobNorm A * Kd) := by ring
      _ <= theta ^ 2 * (frobNorm A * Kd) :=
        mul_le_mul_of_nonneg_right hgammaTheta (mul_nonneg hA hKd)
  calc
    vecNorm2 g <=
        gamma * (q / (1 - rho) + frobNorm A * (theta * Kd)) :=
      hgammaBound
    _ = gamma * (q / (1 - rho)) +
        gamma * (frobNorm A * (theta * Kd)) := by ring
    _ <= (gamma * q + theta ^ 2 * (q / (1 - rho))) +
        theta ^ 2 * (frobNorm A * Kd) :=
      add_le_add hsplit hdiffFormation
    _ = gamma * q +
        theta ^ 2 * (q / (1 - rho) + frobNorm A * Kd) := by ring

/-- A direct Frobenius bound for the Gram displacement generated by a
rectangular perturbation. -/
theorem higham21_sne_rectGram_difference_frobNorm_le
    {m n : Nat} (A F : Fin m -> Fin n -> Real) :
    frobNorm (fun i j =>
        rectGram (fun r s => A r s + F r s) i j - rectGram A i j) <=
      2 * frobNorm A * frobNorm F + frobNorm F ^ 2 := by
  let AFt : Fin m -> Fin m -> Real := rectMatMul A (finiteTranspose F)
  let FAt : Fin m -> Fin m -> Real := rectMatMul F (finiteTranspose A)
  let FFt : Fin m -> Fin m -> Real := rectMatMul F (finiteTranspose F)
  have hdecomp :
      (fun i j =>
        rectGram (fun r s => A r s + F r s) i j - rectGram A i j) =
      fun i j => AFt i j + FAt i j + FFt i j := by
    ext i j
    dsimp [AFt, FAt, FFt, rectGram, rectMatMul, finiteTranspose]
    rw [<- Finset.sum_sub_distrib]
    rw [<- Finset.sum_add_distrib]
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hAFt : frobNorm AFt <= frobNorm A * frobNorm F := by
    rw [<- frobNormRect_eq_frobNormFn]
    calc
      frobNormRect AFt <=
          frobNormRect A * frobNormRect (finiteTranspose F) := by
        simpa [AFt] using
          frobNormRect_rectMatMul_le A (finiteTranspose F)
      _ = frobNorm A * frobNorm F := by
        rw [frobNormRect_finiteTranspose]
        rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  have hFAt : frobNorm FAt <= frobNorm F * frobNorm A := by
    rw [<- frobNormRect_eq_frobNormFn]
    calc
      frobNormRect FAt <=
          frobNormRect F * frobNormRect (finiteTranspose A) := by
        simpa [FAt] using
          frobNormRect_rectMatMul_le F (finiteTranspose A)
      _ = frobNorm F * frobNorm A := by
        rw [frobNormRect_finiteTranspose]
        rw [frobNormRect_eq_frobNormFn, frobNormRect_eq_frobNormFn]
  have hFFt : frobNorm FFt <= frobNorm F * frobNorm F := by
    rw [<- frobNormRect_eq_frobNormFn]
    calc
      frobNormRect FFt <=
          frobNormRect F * frobNormRect (finiteTranspose F) := by
        simpa [FFt] using
          frobNormRect_rectMatMul_le F (finiteTranspose F)
      _ = frobNorm F * frobNorm F := by
        rw [frobNormRect_finiteTranspose]
        rw [frobNormRect_eq_frobNormFn]
  rw [hdecomp]
  calc
    frobNorm (fun i j => AFt i j + FAt i j + FFt i j) <=
        frobNorm (fun i j => AFt i j + FAt i j) + frobNorm FFt :=
      frobNorm_add_le _ _
    _ <= (frobNorm AFt + frobNorm FAt) + frobNorm FFt :=
      add_le_add (frobNorm_add_le AFt FAt) le_rfl
    _ <= (frobNorm A * frobNorm F + frobNorm F * frobNorm A) +
        frobNorm F * frobNorm F :=
      add_le_add (add_le_add hAFt hFAt) hFFt
    _ = 2 * frobNorm A * frobNorm F + frobNorm F ^ 2 := by ring

/-- Resolvent identity in Frobenius norm, stated only with two-sided inverse
certificates. -/
theorem higham21_sne_inverse_difference_frobNorm_le
    {m : Nat}
    (S T G H : Fin m -> Fin m -> Real)
    (hS : IsInverse m S G) (hT : IsInverse m T H) :
    frobNorm (fun i j => H i j - G i j) <=
      frobNorm G * frobNorm (fun i j => S i j - T i j) * frobNorm H := by
  let E : Fin m -> Fin m -> Real := fun i j => S i j - T i j
  have hGS : rectMatMul G S = idMatrix m := by
    ext i j
    exact hS.1 i j
  have hTH : rectMatMul T H = idMatrix m := by
    ext i j
    exact hT.2 i j
  have hresolvent :
      (fun i j => H i j - G i j) = rectMatMul (rectMatMul G E) H := by
    calc
      (fun i j => H i j - G i j) =
          fun i j =>
            rectMatMul (rectMatMul G S) H i j -
              rectMatMul G (rectMatMul T H) i j := by
        rw [hGS, hTH]
        rw [rectMatMul_id_left, rectMatMul_id_right]
      _ = fun i j =>
          rectMatMul G (rectMatMul S H) i j -
            rectMatMul G (rectMatMul T H) i j := by
        rw [rectMatMul_assoc G S H]
      _ = rectMatMul G
          (fun i j => rectMatMul S H i j - rectMatMul T H i j) := by
        symm
        exact rectMatMul_sub_right G (rectMatMul S H) (rectMatMul T H)
      _ = rectMatMul G (rectMatMul E H) := by
        rw [show rectMatMul E H =
            (fun i j => rectMatMul S H i j - rectMatMul T H i j) by
          simpa [E] using rectMatMul_sub_left S T H]
      _ = rectMatMul (rectMatMul G E) H := by
        exact (rectMatMul_assoc G E H).symm
  rw [hresolvent]
  calc
    frobNorm (rectMatMul (rectMatMul G E) H) <=
        frobNorm (rectMatMul G E) * frobNorm H :=
      frobNorm_matMul_le (rectMatMul G E) H
    _ <= (frobNorm G * frobNorm E) * frobNorm H :=
      mul_le_mul_of_nonneg_right
        (frobNorm_matMul_le G E) (frobNorm_nonneg H)
    _ = frobNorm G * frobNorm (fun i j => S i j - T i j) *
        frobNorm H := by rfl



















































































































/-- The exact inverse of the actual top factor, used only in the analysis. -/
noncomputable def higham21SNEHouseholderRInv
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) : Fin m -> Fin m -> Real :=
  nonsingInv m (higham21SNEHouseholderRHat fp A)

/-- Exact reference normal-equation vector for the QR-perturbed matrix. -/
noncomputable def higham21SNEHouseholderReferenceY
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real) :
    Fin m -> Real :=
  rectMatMulVec (higham21SNEHouseholderRInv fp A)
    (rectMatMulVec (finiteTranspose (higham21SNEHouseholderRInv fp A)) b)













/-- The actual rounding error committed by the final `fl(A^T y_hat)` call. -/
noncomputable def higham21SNEHouseholderFormationError
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real) :
    Fin (m + k) -> Real :=
  let R_hat := higham21SNEHouseholderRHat fp A
  let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
  fun j =>
    higham21SNEActualOutput fp m (m + k) A R_hat b j -
      rectTransposeMulVec A y_hat j















































































































































































































































































































































































































































































































































































































































































/-- Componentwise error of the actual final rounded transpose action. -/
theorem higham21_sne_householder_formation_error_pointwise
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hmGamma : gammaValid fp m) :
    let R_hat := higham21SNEHouseholderRHat fp A
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    forall j,
      |higham21SNEHouseholderFormationError fp A b j| <=
        gamma fp m *
          rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|) j := by
  dsimp only
  intro j
  simpa [higham21SNEHouseholderFormationError,
    higham21SNEActualOutput, rectTransposeMulVec, finiteTranspose,
    absMatrixRect] using
      (matVec_error_bound fp (m + k) m (finiteTranspose A)
        (higham21SNEComputedNormalSolution fp m
          (higham21SNEHouseholderRHat fp A) b) hmGamma j)

/-- Normwise consequence of the preceding componentwise final-formation
bound. -/
theorem higham21_sne_householder_formation_error_norm
    (fp : FPModel) {m k : Nat}
    (A : Fin m -> Fin (m + k) -> Real) (b : Fin m -> Real)
    (hmGamma : gammaValid fp m) :
    let R_hat := higham21SNEHouseholderRHat fp A
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    vecNorm2 (higham21SNEHouseholderFormationError fp A b) <=
      gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y_hat i|)) := by
  dsimp only
  let w : Fin (m + k) -> Real :=
    rectTransposeMulVec (absMatrixRect A)
      (fun i =>
        |higham21SNEComputedNormalSolution fp m
          (higham21SNEHouseholderRHat fp A) b i|)
  have hpoint : forall j,
      |higham21SNEHouseholderFormationError fp A b j| <=
        gamma fp m * w j := by
    simpa [w] using
      higham21_sne_householder_formation_error_pointwise
        fp A b hmGamma
  calc
    vecNorm2 (higham21SNEHouseholderFormationError fp A b) <=
        vecNorm2 (fun j => gamma fp m * w j) :=
      vecNorm2_le_of_abs_le _ _ hpoint
    _ = gamma fp m * vecNorm2 w := by
      rw [vecNorm2_smul, abs_of_nonneg (gamma_nonneg fp hmGamma)]
    _ = gamma fp m *
        vecNorm2
          (rectTransposeMulVec (absMatrixRect A)
            (fun i =>
              |higham21SNEComputedNormalSolution fp m
                (higham21SNEHouseholderRHat fp A) b i|)) := by rfl

































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































end NumStability
