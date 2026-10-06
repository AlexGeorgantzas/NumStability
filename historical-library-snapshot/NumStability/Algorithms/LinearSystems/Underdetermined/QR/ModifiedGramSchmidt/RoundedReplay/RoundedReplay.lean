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
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.CorrectedRecurrence.Core
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.RankOneUpdate
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
# Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.RoundedReplay.RoundedReplay

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, corrected MGS formation on printed page 413.





namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## A rounded corrected-MGS step -/

/-- Rounded corrected MGS update in the printed operation order:
rounded dot product, rounded subtraction of `y_k`, rounded multiplication by
`q_k`, and rounded componentwise subtraction from `x`. -/
noncomputable def higham21FlMGSCorrectedStep (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) : Fin n -> Real :=
  let q := gsColumn Q k
  let t := fl_dotProduct fp n q x
  let s := fp.fl_sub t (y k)
  fun i => fp.fl_sub (x i) (fp.fl_mul s (q i))

/-- The exact corrected step is a rank-one update followed by `y_k q_k`. -/
theorem higham21_mgs_corrected_step_eq_rankOneUpdate_add {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) :
    higham21MGSCorrectedStep Q y k x =
      fun i =>
        rankOneUpdateExact n (gsColumn Q k) (gsColumn Q k) x i +
          y k * gsColumn Q k i := by
  funext i
  unfold higham21MGSCorrectedStep rankOneUpdateExact gsDot gsColumn
  ring

/-- Error budget for subtracting `y` from an approximation `t` to `d`. -/
noncomputable def higham21FlSubAfterApproxBudget
    (fp : FPModel) (E T : Real) : Real :=
  E + T * fp.u

/-- Reusable certificate for rounded subtraction after an approximate input. -/
theorem higham21_fl_sub_after_approx_error_bound
    (fp : FPModel) (t d y E T : Real)
    (hT : 0 <= T) (htd : |t - d| <= E) (hty : |t - y| <= T) :
    |fp.fl_sub t y - (d - y)| <=
      higham21FlSubAfterApproxBudget fp E T := by
  obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub t y
  have hrewrite :
      fp.fl_sub t y - (d - y) = (t - d) + (t - y) * delta := by
    rw [hsub]
    ring
  rw [hrewrite]
  calc
    |(t - d) + (t - y) * delta| <=
        |t - d| + |(t - y) * delta| := abs_add_le _ _
    _ = |t - d| + |t - y| * |delta| := by rw [abs_mul]
    _ <= E + T * fp.u :=
      add_le_add htd (mul_le_mul hty hdelta (abs_nonneg delta) hT)
    _ = higham21FlSubAfterApproxBudget fp E T := rfl

/-- Error budget for multiplying an approximate scalar `shat` by `q`. -/
noncomputable def higham21FlMulAfterApproxBudget
    (fp : FPModel) (q E S : Real) : Real :=
  |q| * E * (1 + fp.u) + |q| * S * fp.u

/-- Reusable certificate for rounded multiplication after an approximate
scalar input. -/
theorem higham21_fl_mul_after_approx_error_bound
    (fp : FPModel) (shat s q E S : Real)
    (hE : 0 <= E) (hS : 0 <= S)
    (hshat : |shat - s| <= E) (hs : |s| <= S) :
    |fp.fl_mul shat q - s * q| <=
      higham21FlMulAfterApproxBudget fp q E S := by
  obtain ⟨delta, hdelta, hmul⟩ := fp.model_mul shat q
  have hone : |1 + delta| <= 1 + fp.u := by
    calc
      |1 + delta| <= |(1 : Real)| + |delta| := abs_add_le _ _
      _ <= 1 + fp.u := by simpa using add_le_add_left hdelta 1
  have hrewrite :
      fp.fl_mul shat q - s * q =
        q * (shat - s) * (1 + delta) + s * q * delta := by
    rw [hmul]
    ring
  rw [hrewrite]
  calc
    |q * (shat - s) * (1 + delta) + s * q * delta| <=
        |q * (shat - s) * (1 + delta)| + |s * q * delta| :=
      abs_add_le _ _
    _ = |q| * |shat - s| * |1 + delta| + |s| * |q| * |delta| := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul]
    _ <= |q| * E * (1 + fp.u) + S * |q| * fp.u := by
      exact add_le_add
        (mul_le_mul
          (mul_le_mul_of_nonneg_left hshat (abs_nonneg q)) hone
          (abs_nonneg (1 + delta))
          (mul_nonneg (abs_nonneg q) hE))
        (mul_le_mul
          (mul_le_mul_of_nonneg_right hs (abs_nonneg q)) hdelta
          (abs_nonneg delta)
          (mul_nonneg hS (abs_nonneg q)))
    _ = higham21FlMulAfterApproxBudget fp q E S := by
      unfold higham21FlMulAfterApproxBudget
      ring

/-- Error budget for the final rounded subtraction `fl(x-what)`. -/
noncomputable def higham21FlFinalSubBudget
    (fp : FPModel) (x W E : Real) : Real :=
  E + (|x| + W + E) * fp.u

/-- Reusable certificate for the final subtraction with an approximate
subtrahend. -/
theorem higham21_fl_final_sub_error_bound
    (fp : FPModel) (x what w W E : Real)
    (hW : 0 <= W) (hE : 0 <= E)
    (hwhat : |what - w| <= E) (hw : |w| <= W) :
    |fp.fl_sub x what - (x - w)| <=
      higham21FlFinalSubBudget fp x W E := by
  obtain ⟨delta, hdelta, hsub⟩ := fp.model_sub x what
  have hwhatAbs : |what| <= W + E := by
    calc
      |what| = |w + (what - w)| := by ring_nf
      _ <= |w| + |what - w| := abs_add_le _ _
      _ <= W + E := add_le_add hw hwhat
  have hdiffAbs : |x - what| <= |x| + W + E := by
    calc
      |x - what| <= |x| + |what| := abs_sub _ _
      _ <= |x| + (W + E) := add_le_add_right hwhatAbs _
      _ = |x| + W + E := by ring
  have hdiffNonneg : 0 <= |x| + W + E :=
    add_nonneg (add_nonneg (abs_nonneg x) hW) hE
  have hrewrite :
      fp.fl_sub x what - (x - w) =
        -(what - w) + (x - what) * delta := by
    rw [hsub]
    ring
  rw [hrewrite]
  calc
    |-(what - w) + (x - what) * delta| <=
        |-(what - w)| + |(x - what) * delta| :=
      abs_add_le _ _
    _ = |what - w| + |x - what| * |delta| := by
      rw [abs_mul, abs_neg]
    _ <= E + (|x| + W + E) * fp.u :=
      add_le_add hwhat
        (mul_le_mul hdiffAbs hdelta (abs_nonneg delta) hdiffNonneg)
    _ = higham21FlFinalSubBudget fp x W E := rfl

/-- Per-component local budget for the printed rounded corrected-MGS step. -/
noncomputable def higham21FlMGSCorrectedLocalBudget
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) : Fin n -> Real :=
  let q := gsColumn Q k
  let S := Finset.univ.sum fun j : Fin n => |q j| * |x j|
  let Edot := gamma fp n * S
  let T := S + Edot + |y k|
  let Es := higham21FlSubAfterApproxBudget fp Edot T
  let Sscalar := S + |y k|
  fun i =>
    let Ew := higham21FlMulAfterApproxBudget fp (q i) Es Sscalar
    let W := |q i| * Sscalar
    higham21FlFinalSubBudget fp (x i) W Ew

/-- The concrete printed-order rounded step satisfies its local componentwise
budget. -/
theorem higham21_fl_mgs_corrected_step_componentwise_error_bound
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x : Fin n -> Real) (hvalid : gammaValid fp (n + 3)) :
    forall i : Fin n,
      |higham21FlMGSCorrectedStep fp Q y k x i -
          higham21MGSCorrectedStep Q y k x i| <=
        higham21FlMGSCorrectedLocalBudget fp Q y k x i := by
  intro i
  let q : Fin n -> Real := gsColumn Q k
  let d : Real := gsDot q x
  let t : Real := fl_dotProduct fp n q x
  let S : Real := Finset.univ.sum fun j : Fin n => |q j| * |x j|
  let Edot : Real := gamma fp n * S
  let T : Real := S + Edot + |y k|
  let s : Real := d - y k
  let shat : Real := fp.fl_sub t (y k)
  let Es : Real := higham21FlSubAfterApproxBudget fp Edot T
  let Sscalar : Real := S + |y k|
  let Ew : Real := higham21FlMulAfterApproxBudget fp (q i) Es Sscalar
  let W : Real := |q i| * Sscalar
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hvalid
  have hgamma : 0 <= gamma fp n := gamma_nonneg fp hn
  have hS : 0 <= S :=
    Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hEdot : 0 <= Edot := mul_nonneg hgamma hS
  have hdotError : |t - d| <= Edot := by
    simpa [q, d, t, S, Edot, gsDot] using
      dotProduct_error_bound fp n q x hn
  have hdotAbs : |d| <= S := by
    calc
      |d| = |Finset.univ.sum fun j : Fin n => q j * x j| := by
        rfl
      _ <= Finset.univ.sum fun j : Fin n => |q j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = S := by simp [S, abs_mul]
  have htAbs : |t| <= S + Edot := by
    calc
      |t| = |d + (t - d)| := by ring_nf
      _ <= |d| + |t - d| := abs_add_le _ _
      _ <= S + Edot := add_le_add hdotAbs hdotError
  have hT : 0 <= T :=
    add_nonneg (add_nonneg hS hEdot) (abs_nonneg (y k))
  have hty : |t - y k| <= T := by
    calc
      |t - y k| <= |t| + |y k| := abs_sub _ _
      _ <= (S + Edot) + |y k| := add_le_add_left htAbs _
      _ = T := rfl
  have hsError : |shat - s| <= Es := by
    simpa [shat, s, Es] using
      higham21_fl_sub_after_approx_error_bound
        fp t d (y k) Edot T hT hdotError hty
  have hSscalar : 0 <= Sscalar := add_nonneg hS (abs_nonneg (y k))
  have hsAbs : |s| <= Sscalar := by
    calc
      |s| = |d - y k| := rfl
      _ <= |d| + |y k| := abs_sub _ _
      _ <= S + |y k| := add_le_add_left hdotAbs _
      _ = Sscalar := rfl
  have hEs : 0 <= Es := by
    simp only [Es, higham21FlSubAfterApproxBudget]
    exact add_nonneg hEdot (mul_nonneg hT fp.u_nonneg)
  have hmulError :
      |fp.fl_mul shat (q i) - s * q i| <= Ew := by
    simpa [Ew] using higham21_fl_mul_after_approx_error_bound
      fp shat s (q i) Es Sscalar hEs hSscalar hsError hsAbs
  have hW : 0 <= W := mul_nonneg (abs_nonneg (q i)) hSscalar
  have hw : |s * q i| <= W := by
    simpa [W, abs_mul, mul_comm] using
      mul_le_mul_of_nonneg_right hsAbs (abs_nonneg (q i))
  have hEw : 0 <= Ew := by
    simp only [Ew, higham21FlMulAfterApproxBudget]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (abs_nonneg (q i)) hEs)
        (add_nonneg zero_le_one fp.u_nonneg))
      (mul_nonneg (mul_nonneg (abs_nonneg (q i)) hSscalar) fp.u_nonneg)
  have hfinal := higham21_fl_final_sub_error_bound
    fp (x i) (fp.fl_mul shat (q i)) (s * q i) W Ew
      hW hEw hmulError hw
  simpa [higham21FlMGSCorrectedStep, higham21MGSCorrectedStep,
    higham21FlMGSCorrectedLocalBudget, q, d, t, S, Edot, T, s, shat,
    Es, Sscalar, Ew, W] using hfinal

/-! ## The backward loop and its repaired-action majorant -/

/-- At distance `d+1` from the terminal state, the next column is
`m-(d+1)`. -/
def higham21MGSBackwardIndex {m : Nat} (d : Nat) (hd : d + 1 <= m) : Fin m :=
  ⟨m - (d + 1), by omega⟩

/-- State after `d` rounded steps, starting from zero and visiting columns
`m-1,m-2,...`. -/
noncomputable def higham21FlMGSCorrectedStateAtDistance
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) :
    (d : Nat) -> d <= m -> Fin n -> Real
  | 0, _ => 0
  | d + 1, hd =>
      higham21FlMGSCorrectedStep fp Q y
        (higham21MGSBackwardIndex d hd)
        (higham21FlMGSCorrectedStateAtDistance fp Q y d (by omega))

/-- Terminal equation of the concrete rounded backward recurrence. -/
theorem higham21_fl_mgs_corrected_state_terminal
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (h0 : 0 <= m) :
    higham21FlMGSCorrectedStateAtDistance fp Q y 0 h0 =
      (0 : Fin n -> Real) := by
  rfl

/-- Successor equation: distance `d+1` applies column `m-(d+1)` to the
state after `d` later-column updates. -/
theorem higham21_fl_mgs_corrected_state_succ
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (d : Nat) (hd : d + 1 <= m) :
    higham21FlMGSCorrectedStateAtDistance fp Q y (d + 1) hd =
      higham21FlMGSCorrectedStep fp Q y
        (higham21MGSBackwardIndex d hd)
        (higham21FlMGSCorrectedStateAtDistance fp Q y d (by omega)) := by
  rfl

/-- Actual output of the rounded corrected-MGS backward recurrence. -/
noncomputable def higham21FlMGSCorrectedOutput
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) : Fin n -> Real :=
  higham21FlMGSCorrectedStateAtDistance fp Q y m le_rfl

/-- Absolute majorant for applying `I-q*q^T` to a vector already bounded by
`B`. -/
noncomputable def higham21MGSRankOneMajorant {n : Nat}
    (q B : Fin n -> Real) : Fin n -> Real :=
  fun i => B i + |q i| * (Finset.univ.sum fun j : Fin n => |q j| * B j)

/-- A rank-one update transports a componentwise majorant as expected. -/
theorem higham21_rankOneUpdateExact_abs_le_majorant {n : Nat}
    (q e B : Fin n -> Real)
    (he : forall j, |e j| <= B j) :
    forall i,
      |rankOneUpdateExact n q q e i| <=
        higham21MGSRankOneMajorant q B i := by
  intro i
  have hsum :
      |Finset.univ.sum fun j : Fin n => q j * e j| <=
        Finset.univ.sum fun j : Fin n => |q j| * B j := by
    calc
      |Finset.univ.sum fun j : Fin n => q j * e j| <=
          Finset.univ.sum fun j : Fin n => |q j * e j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= Finset.univ.sum fun j : Fin n => |q j| * B j := by
        exact Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (he j) (abs_nonneg (q j))
  calc
    |rankOneUpdateExact n q q e i| <=
        |e i| + |q i| *
          |Finset.univ.sum fun j : Fin n => q j * e j| := by
      unfold rankOneUpdateExact
      calc
        |e i - q i * (Finset.univ.sum fun j : Fin n => q j * e j)| <=
            |e i| + |q i * (Finset.univ.sum fun j : Fin n => q j * e j)| :=
          abs_sub _ _
        _ = |e i| + |q i| *
            |Finset.univ.sum fun j : Fin n => q j * e j| := by
          rw [abs_mul]
    _ <= B i + |q i| *
        (Finset.univ.sum fun j : Fin n => |q j| * B j) :=
      add_le_add (he i) (mul_le_mul_of_nonneg_left hsum (abs_nonneg (q i)))
    _ = higham21MGSRankOneMajorant q B i := rfl

/-- The affine corrected step has rank-one linear part. -/
theorem higham21_mgs_corrected_step_sub {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real) (k : Fin m)
    (x t : Fin n -> Real) :
    (fun i =>
      higham21MGSCorrectedStep Q y k x i -
        higham21MGSCorrectedStep Q y k t i) =
      rankOneUpdateExact n (gsColumn Q k) (gsColumn Q k)
        (fun j => x j - t j) := by
  funext i
  have hsum :
      (Finset.univ.sum fun j : Fin n =>
          gsColumn Q k j * (x j - t j)) =
        (Finset.univ.sum fun j : Fin n => gsColumn Q k j * x j) -
          (Finset.univ.sum fun j : Fin n => gsColumn Q k j * t j) := by
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold higham21MGSCorrectedStep rankOneUpdateExact gsDot
  rw [hsum]
  unfold gsColumn
  ring_nf

/-- Propagated componentwise budget against a fixed reference vector.  The
middle term measures the exact corrected-step defect of that reference; for a
Chapter 19 repair the reference is `Qrepair*y`. -/
noncomputable def higham21FlMGSComparisonBudgetAtDistance
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (target : Fin n -> Real) :
    (d : Nat) -> d <= m -> Fin n -> Real
  | 0, _ => fun i => |target i|
  | d + 1, hd =>
      let hd' : d <= m := by omega
      let k := higham21MGSBackwardIndex d hd
      let x := higham21FlMGSCorrectedStateAtDistance fp Q y d hd'
      let B := higham21FlMGSComparisonBudgetAtDistance fp Q y target d hd'
      fun i =>
        higham21MGSRankOneMajorant (gsColumn Q k) B i +
          |higham21MGSCorrectedStep Q y k target i - target i| +
          higham21FlMGSCorrectedLocalBudget fp Q y k x i

/-- The propagated budget bounds every intermediate rounded state. -/
theorem higham21_fl_mgs_state_componentwise_reference_error
    (fp : FPModel) {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (target : Fin n -> Real) (hvalid : gammaValid fp (n + 3)) :
    forall (d : Nat) (hd : d <= m) (i : Fin n),
      |higham21FlMGSCorrectedStateAtDistance fp Q y d hd i - target i| <=
        higham21FlMGSComparisonBudgetAtDistance fp Q y target d hd i := by
  intro d
  induction d with
  | zero =>
      intro hd i
      simp [higham21FlMGSCorrectedStateAtDistance,
        higham21FlMGSComparisonBudgetAtDistance]
  | succ d ih =>
      intro hd i
      let hd' : d <= m := by omega
      let k : Fin m := higham21MGSBackwardIndex d hd
      let x := higham21FlMGSCorrectedStateAtDistance fp Q y d hd'
      let B := higham21FlMGSComparisonBudgetAtDistance fp Q y target d hd'
      have hprev : forall j : Fin n, |x j - target j| <= B j := by
        intro j
        simpa [x, B] using ih hd' j
      have hmiddle :
          |higham21MGSCorrectedStep Q y k x i -
              higham21MGSCorrectedStep Q y k target i| <=
            higham21MGSRankOneMajorant (gsColumn Q k) B i := by
        rw [congrFun (higham21_mgs_corrected_step_sub Q y k x target) i]
        exact higham21_rankOneUpdateExact_abs_le_majorant
          (gsColumn Q k) (fun j => x j - target j) B hprev i
      have hlocal :=
        higham21_fl_mgs_corrected_step_componentwise_error_bound
          fp Q y k x hvalid i
      have hsplit :
          higham21FlMGSCorrectedStep fp Q y k x i - target i =
            (higham21FlMGSCorrectedStep fp Q y k x i -
              higham21MGSCorrectedStep Q y k x i) +
            (higham21MGSCorrectedStep Q y k x i -
              higham21MGSCorrectedStep Q y k target i) +
            (higham21MGSCorrectedStep Q y k target i - target i) := by
        ring
      change
        |higham21FlMGSCorrectedStep fp Q y k x i - target i| <= _
      rw [hsplit]
      calc
        |(higham21FlMGSCorrectedStep fp Q y k x i -
              higham21MGSCorrectedStep Q y k x i) +
            (higham21MGSCorrectedStep Q y k x i -
              higham21MGSCorrectedStep Q y k target i) +
            (higham21MGSCorrectedStep Q y k target i - target i)| <=
            |higham21FlMGSCorrectedStep fp Q y k x i -
                higham21MGSCorrectedStep Q y k x i| +
              |higham21MGSCorrectedStep Q y k x i -
                higham21MGSCorrectedStep Q y k target i| +
              |higham21MGSCorrectedStep Q y k target i - target i| := by
          exact le_trans (abs_add_le _ _)
            (add_le_add (abs_add_le _ _) le_rfl)
        _ <= higham21FlMGSCorrectedLocalBudget fp Q y k x i +
              higham21MGSRankOneMajorant (gsColumn Q k) B i +
              |higham21MGSCorrectedStep Q y k target i - target i| :=
          add_le_add (add_le_add hlocal hmiddle) le_rfl
        _ = higham21MGSRankOneMajorant (gsColumn Q k) B i +
              |higham21MGSCorrectedStep Q y k target i - target i| +
              higham21FlMGSCorrectedLocalBudget fp Q y k x i := by ring
        _ = higham21FlMGSComparisonBudgetAtDistance
              fp Q y target (d + 1) hd i := by
          simp [higham21FlMGSComparisonBudgetAtDistance, k, x, B]

/-- Final propagated budget against the repaired action. -/
noncomputable def higham21FlMGSRepairedActionBudget
    (fp : FPModel) {m n : Nat}
    (Qhat Qrepair : Fin n -> Fin m -> Real) (y : Fin m -> Real) :
    Fin n -> Real :=
  higham21FlMGSComparisonBudgetAtDistance fp Qhat y
    (higham21MGSNaiveFormation Qrepair y) m le_rfl

/-- Componentwise relation between the actual rounded recurrence and the
selected orthonormal Chapter 19 repair action. -/
theorem higham21_fl_mgs_corrected_output_repaired_action_componentwise
    (fp : FPModel) {m n : Nat}
    (Qhat Qrepair : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (hvalid : gammaValid fp (n + 3)) :
    forall i : Fin n,
      |higham21FlMGSCorrectedOutput fp Qhat y i -
          higham21MGSNaiveFormation Qrepair y i| <=
        higham21FlMGSRepairedActionBudget fp Qhat Qrepair y i := by
  intro i
  exact higham21_fl_mgs_state_componentwise_reference_error
    fp Qhat y (higham21MGSNaiveFormation Qrepair y) hvalid m le_rfl i

/-! ## A rowwise action certificate for a fixed triangular-solve vector -/

/-- Least-Frobenius rank-one correction whose action on `y` is `e`. -/
noncomputable def higham21MGSFixedVectorActionCorrection {m n : Nat}
    (y : Fin m -> Real) (e : Fin n -> Real) : Fin n -> Fin m -> Real :=
  fun i j => (1 / vecNorm2Sq y) * (e i * y j)






























































































/-! ## Explicit rank-one system corrections -/

/-- Rowwise rank-one correction that makes `x` feasible for `B*x=b` when
`x` is nonzero. -/
noncomputable def higham21MGSFeasibilityCorrection {m n : Nat}
    (B : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (x : Fin n -> Real) : Fin m -> Fin n -> Real :=
  higham21MGSFixedVectorActionCorrection x
    (fun i => b i - rectMatMulVec B x i)


































/-- Transposed rank-one correction that puts `x` in the transpose range of
`B` through a fixed nonzero dual vector `z`. -/
noncomputable def higham21MGSRangeCorrection {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) : Fin m -> Fin n -> Real :=
  finiteTranspose
    (higham21MGSFixedVectorActionCorrection z
      (fun j => x j - rectTransposeMulVec B z j))
































/-- Exact row norm of the explicit transpose-range correction. -/
theorem higham21_mgs_rangeCorrection_rowNorm {m n : Nat}
    (B : Fin m -> Fin n -> Real) (x : Fin n -> Real)
    (z : Fin m -> Real) (i : Fin m) :
    rectRowNorm2 (higham21MGSRangeCorrection B x z) i =
      |(1 / vecNorm2Sq z) * z i| *
        vecNorm2 (fun j => x j - rectTransposeMulVec B z j) := by
  let e : Fin n -> Real := fun j => x j - rectTransposeMulVec B z j
  change vecNorm2 (fun j : Fin n =>
      higham21MGSRangeCorrection B x z i j) =
    |(1 / vecNorm2Sq z) * z i| * vecNorm2 e
  have hfun :
      (fun j : Fin n => higham21MGSRangeCorrection B x z i j) =
        fun j => ((1 / vecNorm2Sq z) * z i) * e j := by
    funext j
    simp [higham21MGSRangeCorrection,
      higham21MGSFixedVectorActionCorrection, finiteTranspose, e]
    ring
  rw [hfun, vecNorm2_smul]

/-! ## The Problem 19.12 repair and the triangular-solve perturbation -/




















































































































































































/-! ## Actual-output Theorem 21.4 handoff -/

/-- The remaining action-to-system transfer needed by Lemma 21.2.

The concrete output is fixed in this structure.  `DeltaA1` makes that output
solve a nearby system, while `DeltaA2` puts it in the transpose range of a
nearby system.  The rounded recurrence and its repaired-action row certificate
above do not, by themselves, imply these two row-scaled matrix bounds. -/
structure Higham21MGSRoundedSystemTransfer
    (fp : FPModel) {m n : Nat}
    (A : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (Qhat : Fin n -> Fin m -> Real) (y : Fin m -> Real)
    (DeltaBase : Fin m -> Fin n -> Real) (etaAction : Real) : Type where
  DeltaA1 : Fin m -> Fin n -> Real
  DeltaA2 : Fin m -> Fin n -> Real
  dual : Fin m -> Real
  first_system :
    rectMatMulVec
      (fun i j => A i j + DeltaBase i j + DeltaA1 i j)
      (higham21FlMGSCorrectedOutput fp Qhat y) = b
  second_system :
    higham21FlMGSCorrectedOutput fp Qhat y =
      rectTransposeMulVec
        (fun i j => A i j + DeltaBase i j + DeltaA2 i j) dual
  row_bound1 : forall i,
    rectRowNorm2 DeltaA1 i <= etaAction * rectRowNorm2 A i
  row_bound2 : forall i,
    rectRowNorm2 DeltaA2 i <= etaAction * rectRowNorm2 A i
  eta_nonneg : 0 <= etaAction



















































































































































































































































































end

end NumStability
