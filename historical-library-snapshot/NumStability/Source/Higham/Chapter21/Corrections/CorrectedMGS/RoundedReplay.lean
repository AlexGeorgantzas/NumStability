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
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.ModifiedGramSchmidt.CorrectedRecurrence.Core
import NumStability.Algorithms.RankOneUpdate
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Theorem04.HouseholderQMethod.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Theorem04.RowwiseBackwardError

/-!
# Source.Higham.Chapter21.Corrections.Problem19_12.RoundedReplay

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 21, corrected MGS formation on printed page 413.





namespace NumStability

open scoped BigOperators

noncomputable section

/-! ## A rounded corrected-MGS step -/













































































































































































































































/-! ## The backward loop and its repaired-action majorant -/




























































































































































































































/-! ## A rowwise action certificate for a fixed triangular-solve vector -/



































































































/-! ## Explicit rank-one system corrections -/






































































































/-! ## The Problem 19.12 repair and the triangular-solve perturbation -/

/-- The pure Problem 19.12 correction map gives the exact action split
`Qrepair*y = P21*y + F*(P11*y)`. -/
theorem higham21_mgs_problem1912_repaired_action_eq {m n : Nat}
    (P11 : Fin n -> Fin n -> Real)
    (P21 Qrepair F : Fin m -> Fin n -> Real)
    (hrepair : MGSProblem1912CorrectionMapData m n P11 P21 Qrepair F)
    (y : Fin n -> Real) :
    higham21MGSNaiveFormation Qrepair y =
      fun i => higham21MGSNaiveFormation P21 y i +
        rectMatMulVec F (rectMatMulVec P11 y) i := by
  rw [hrepair.add_factor_eq]
  unfold higham21MGSNaiveFormation
  calc
    rectMatMulVec
        (fun i j => P21 i j + matMulRect m n n F P11 i j) y =
        fun i => rectMatMulVec P21 y i +
          rectMatMulVec (matMulRect m n n F P11) y i :=
      rectMatMulVec_mat_add P21 (matMulRect m n n F P11) y
    _ = fun i => rectMatMulVec P21 y i +
        rectMatMulVec F (rectMatMulVec P11 y) i := by
      rw [matMulRect_eq_rectMatMul, rectMatMulVec_rectMatMul]

/-- Fold the computed triangular-solve perturbation into the repaired economy
factor perturbation. -/
noncomputable def higham21MGSFoldedDeltaAT {m n : Nat}
    (Qrepair : Fin n -> Fin m -> Real)
    (DeltaAT : Fin n -> Fin m -> Real)
    (DeltaR : Fin m -> Fin m -> Real) : Fin n -> Fin m -> Real :=
  fun i j => DeltaAT i j + matMulRect n m m Qrepair DeltaR i j

/-- Exact economy-factor identity after folding `DeltaR` into `Rhat`. -/
theorem higham21_mgs_folded_deltaAT_factor {m n : Nat}
    (AT DeltaAT : Fin n -> Fin m -> Real)
    (Qrepair : Fin n -> Fin m -> Real)
    (Rhat DeltaR : Fin m -> Fin m -> Real)
    (hfactor : forall i j,
      AT i j + DeltaAT i j = matMulRect n m m Qrepair Rhat i j) :
    forall i j,
      AT i j + higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR i j =
        matMulRect n m m Qrepair
          (fun a b => Rhat a b + DeltaR a b) i j := by
  intro i j
  have hadd := congrFun (congrFun
    (matMulRect_add_right n m m Qrepair Rhat DeltaR) i) j
  unfold higham21MGSFoldedDeltaAT
  calc
    AT i j +
        (DeltaAT i j + matMulRect n m m Qrepair DeltaR i j) =
        (AT i j + DeltaAT i j) +
          matMulRect n m m Qrepair DeltaR i j := by ring
    _ = matMulRect n m m Qrepair Rhat i j +
          matMulRect n m m Qrepair DeltaR i j := by rw [hfactor i j]
    _ = matMulRect n m m Qrepair
          (fun a b => Rhat a b + DeltaR a b) i j := hadd.symm

/-- Economy matrices with orthonormal columns preserve Euclidean norm. -/
theorem higham21_mgs_orthonormal_columns_action_norm_eq {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (hQ : GramSchmidtOrthonormalColumns Q)
    (x : Fin m -> Real) :
    vecNorm2 (rectMatMulVec Q x) = vecNorm2 x := by
  have hforward := hQ.rectOpNorm2Le_one x
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num)
      hQ.rectOpNorm2Le_one
  have hback := hQT (rectMatMulVec Q x)
  have hid := higham21_mgs_naive_transpose_action_of_orthonormal Q x hQ
  unfold higham21MGSNaiveFormation at hid
  rw [hid] at hback
  apply le_antisymm
  . simpa using hforward
  . simpa using hback

/-- Column form of the economy isometry. -/
theorem higham21_mgs_orthonormal_columns_matMulRect_columnFrob {m n : Nat}
    (Q : Fin n -> Fin m -> Real) (R : Fin m -> Fin m -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) (j : Fin m) :
    columnFrob (matMulRect n m m Q R) j = columnFrob R j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  change
    vecNorm2 (rectMatMulVec Q (fun i : Fin m => R i j)) =
      vecNorm2 (fun i : Fin m => R i j)
  exact higham21_mgs_orthonormal_columns_action_norm_eq
    Q hQ (fun i : Fin m => R i j)

set_option maxHeartbeats 800000 in
/-- Economy analogue of the Theorem 21.4 lifted-`DeltaR` estimate. -/
theorem higham21_mgs_folded_deltaAT_column_bound {m n : Nat}
    (AT DeltaAT : Fin n -> Fin m -> Real)
    (Qrepair : Fin n -> Fin m -> Real)
    (Rhat DeltaR : Fin m -> Fin m -> Real)
    {etaQR etaR : Real}
    (hQ : GramSchmidtOrthonormalColumns Qrepair)
    (hfactor : forall i j,
      AT i j + DeltaAT i j = matMulRect n m m Qrepair Rhat i j)
    (_hetaQR : 0 <= etaQR)
    (hDeltaAT : forall j,
      columnFrob DeltaAT j <= etaQR * columnFrob AT j)
    (hetaR : 0 <= etaR)
    (hDeltaR : forall i j, |DeltaR i j| <= etaR * |Rhat i j|) :
    forall j,
      columnFrob (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR) j <=
        (etaQR + etaR * (1 + etaQR)) * columnFrob AT j := by
  intro j
  have hmat :
      matMulRect n m m Qrepair Rhat =
        fun i j => AT i j + DeltaAT i j := by
    ext i r
    exact (hfactor i r).symm
  have hRhat :
      columnFrob Rhat j <= (1 + etaQR) * columnFrob AT j := by
    calc
      columnFrob Rhat j =
          columnFrob (matMulRect n m m Qrepair Rhat) j :=
        (higham21_mgs_orthonormal_columns_matMulRect_columnFrob
          Qrepair Rhat hQ j).symm
      _ = columnFrob (fun i r => AT i r + DeltaAT i r) j := by rw [hmat]
      _ <= columnFrob AT j + columnFrob DeltaAT j :=
        columnFrob_add_le AT DeltaAT j
      _ <= columnFrob AT j + etaQR * columnFrob AT j :=
        add_le_add_right (hDeltaAT j) _
      _ = (1 + etaQR) * columnFrob AT j := by ring
  have hDeltaRCol :
      columnFrob DeltaR j <= etaR * columnFrob Rhat j :=
    higham21_columnFrob_le_of_entrywise_relative_bound
      Rhat DeltaR hetaR hDeltaR j
  have hQDeltaR :
      columnFrob (matMulRect n m m Qrepair DeltaR) j <=
        columnFrob DeltaR j := by
    have h := columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
      Qrepair DeltaR hQ.rectOpNorm2Le_one j
    simpa using h
  calc
    columnFrob (higham21MGSFoldedDeltaAT Qrepair DeltaAT DeltaR) j <=
        columnFrob DeltaAT j +
          columnFrob (matMulRect n m m Qrepair DeltaR) j :=
      columnFrob_add_le DeltaAT (matMulRect n m m Qrepair DeltaR) j
    _ <= etaQR * columnFrob AT j + columnFrob DeltaR j :=
      add_le_add (hDeltaAT j) hQDeltaR
    _ <= etaQR * columnFrob AT j + etaR * columnFrob Rhat j :=
      add_le_add_right hDeltaRCol _
    _ <= etaQR * columnFrob AT j +
        etaR * ((1 + etaQR) * columnFrob AT j) :=
      add_le_add_right (mul_le_mul_of_nonneg_left hRhat hetaR) _
    _ = (etaQR + etaR * (1 + etaQR)) * columnFrob AT j := by ring

/-- A selected witness from the Chapter 19 MGS `r_factor` channel. -/
structure Higham21MGSSelectedRepair {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Rhat : Fin m -> Fin m -> Real)
    (Qrepair DeltaAT : Fin n -> Fin m -> Real) (etaQR : Real) : Prop where
  upper : IsUpperTrapezoidal m m Rhat
  orthonormal : GramSchmidtOrthonormalColumns Qrepair
  factor : forall i j,
    finiteTranspose A i j + DeltaAT i j =
      matMulRect n m m Qrepair Rhat i j
  column_bound : forall j,
    columnFrob DeltaAT j <= etaQR * columnFrob (finiteTranspose A) j
  eta_nonneg : 0 <= etaQR

/-- Chapter 19's MGS theorem supplies a selected repair witness. -/
theorem higham21_mgs_selected_repair_exists_of_mgs
    {m n : Nat} {A : Fin m -> Fin n -> Real}
    {Qhat : Fin n -> Fin m -> Real} {Rhat : Fin m -> Fin m -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hMGS : ModifiedGramSchmidtBackwardError n m
      (finiteTranspose A) Qhat Rhat
      c1 c2 c3 u normA kappaA higherOrder)
    (heta : 0 <= c3 * u) :
    exists Qrepair : Fin n -> Fin m -> Real,
      exists DeltaAT : Fin n -> Fin m -> Real,
        Higham21MGSSelectedRepair A Rhat Qrepair DeltaAT (c3 * u) := by
  rcases hMGS.r_factor with
    ⟨Qrepair, DeltaAT, hQ, hfactor, hcolumn⟩
  exact ⟨Qrepair, DeltaAT,
    { upper := hMGS.upper
      orthonormal := hQ
      factor := hfactor
      column_bound := hcolumn
      eta_nonneg := heta }⟩

/-! ## Actual-output Theorem 21.4 handoff -/















































































































































































































































































































end

end NumStability
