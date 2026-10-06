import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.Execution.GJEOperationalBridge
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Closure
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.Concrete
import NumStability.Source.Higham.Chapter14.Corollary06.SPD.GaussJordanSPDCorollary
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Closure
import NumStability.Source.Higham.Chapter14.Problem15

/-!
# Chapter14 Algorithm04 Execution GJEFinalDivisionClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GJEFinalDivisionClosure` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open Finset BigOperators
open scoped Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The state produced by the structurally finalized second-stage elimination,
immediately before Algorithm 14.4's final componentwise divisions. -/
noncomputable def ch14ext_gjeBeforeFinalDivision {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Ch14GJEState n :=
  ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)

/-- The literal returned vector in the last line of Algorithm 14.4:
`x_i = fl(b_i / a_ii)`.  No unit-diagonal convention is made here. -/
noncomputable def ch14ext_gjeFinalizedDivOutput {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Fin n -> Real :=
  fun i => fp.fl_div
    ((ch14ext_gjeBeforeFinalDivision fp s).rhs i)
    ((ch14ext_gjeBeforeFinalDivision fp s).matrix i i)

/-- The observable postcondition of Algorithm 14.4 after the final divisions:
the diagonal work array is discharged and the returned RHS storage is the
computed solution.  Setting the dead matrix storage to the identity is
structural and performs no floating-point arithmetic. -/
noncomputable def ch14ext_gjeAfterFinalDivision {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) : Ch14GJEState n where
  matrix := idMatrix n
  rhs := ch14ext_gjeFinalizedDivOutput fp s

@[simp] theorem ch14ext_gjeAfterFinalDivision_matrix {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) :
    (ch14ext_gjeAfterFinalDivision fp s).matrix = idMatrix n := by
  rfl

@[simp] theorem ch14ext_gjeAfterFinalDivision_rhs {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n) :
    (ch14ext_gjeAfterFinalDivision fp s).rhs =
      ch14ext_gjeFinalizedDivOutput fp s := by
  rfl

/-- Successful nonzero diagonal data for the general finalized trace is
inherited from the initial upper factor, because every second-stage operation
preserves the diagonal exactly. -/
theorem ch14ext_gjeBeforeFinalDivision_diag_ne_zero {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0) :
    forall i : Fin n,
      (ch14ext_gjeBeforeFinalDivision fp s).matrix i i ≠ 0 := by
  intro i
  simpa [ch14ext_gjeBeforeFinalDivision] using
    (show (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix i i ≠ 0 by
      rw [ch14ext_gjeFinalizedSourceTrace_diag]
      exact hdiag i)

/-- Scalar final-division backward error, proved locally from the primitive
division model.  This is the one-dimensional operation performed in every row
of Algorithm 14.4's final line. -/
theorem ch14ext_gjeFinalDivision_scalar_backward_error
    (fp : FPModel) (b d : Real) (hd : d ≠ 0)
    (h1 : gammaValid fp 1) :
    exists DeltaD : Real,
      |DeltaD| <= gamma fp 1 * |d| /\
      (d + DeltaD) * fp.fl_div b d = b := by
  obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div b d hd
  have hu1 : fp.u < 1 := by
    simpa [gammaValid] using h1
  have hdelta1 : |delta| < 1 := lt_of_le_of_lt hdelta hu1
  have hpos : 0 < 1 + delta := by
    have hlo : -1 < delta := (abs_lt.mp hdelta1).1
    linarith
  have hgamma0 : 0 <= gamma fp 1 := gamma_nonneg fp h1
  have hden : (1 : Real) - fp.u ≠ 0 := by linarith
  have hgamma : gamma fp 1 * (1 - fp.u) = fp.u := by
    unfold gamma
    rw [Nat.cast_one, one_mul]
    field_simp
  refine ⟨-d * delta / (1 + delta), ?_, ?_⟩
  . rw [abs_div, abs_mul, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
    have hkey : |delta| <= gamma fp 1 * (1 + delta) := by
      have hmono : gamma fp 1 * (1 - fp.u) <=
          gamma fp 1 * (1 + delta) :=
        mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hdelta).1]) hgamma0
      calc
        |delta| <= fp.u := hdelta
        _ = gamma fp 1 * (1 - fp.u) := hgamma.symm
        _ <= gamma fp 1 * (1 + delta) := hmono
    calc
      |d| * |delta| <= |d| * (gamma fp 1 * (1 + delta)) :=
        mul_le_mul_of_nonneg_left hkey (abs_nonneg d)
      _ = gamma fp 1 * |d| * (1 + delta) := by ring
  . rw [hdiv]
    field_simp
    ring

/-- Division-aware version of the accumulated second-stage backward error.

The existing accumulator assumes that the computed last matrix is `I` and
identifies the last RHS with the returned vector.  Algorithm 14.4 actually
finishes its eliminations at a diagonal `D` and then returns componentwise
rounded quotients.  Here `DeltaD` is the operation-derived backward error of
those quotients.  The theorem composes it with the accumulated GJE errors.

The additional term in the `DeltaY` bound is explicit and first order; it is
precisely the contribution hidden by the book's "without loss of generality,
assume D = I" sentence. -/
theorem ch14ext_gje_stage2_backward_error_of_accumulation_final_diagonal
    (n : Nat) (fp : FPModel) (xhat : Fin n -> Real)
    (Nhat : Fin n -> Fin n -> Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real)
    (Q DeltaD : Fin n -> Fin n -> Real) (start : Nat)
    (hn : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hQP : matMul n Q
      (gje_cumulative_product n Nhat start (start + (n - 1))) = idMatrix n)
    (hfinal : forall i : Fin n,
      Finset.univ.sum (fun j : Fin n =>
        (V (start + (n - 1)) i j + DeltaD i j) * xhat j) =
        xseq (start + (n - 1)) i)
    (hDeltaD : forall i j : Fin n,
      |DeltaD i j| <= gamma fp 1 * |V (start + (n - 1)) i j|)
    (hrecM : forall t : Nat, (ht : t < n - 1) -> forall i j : Fin n,
      |V (start + (t + 1)) i j -
          Finset.univ.sum (fun l : Fin n =>
            Nhat ⟨start + t, hidx t ht⟩ i l * V (start + t) l j)| <=
        gamma fp 3 * Finset.univ.sum (fun l : Fin n =>
          |Nhat ⟨start + t, hidx t ht⟩ i l| * |V (start + t) l j|))
    (hrecX : forall t : Nat, (ht : t < n - 1) -> forall i : Fin n,
      |xseq (start + (t + 1)) i -
          Finset.univ.sum (fun l : Fin n =>
            Nhat ⟨start + t, hidx t ht⟩ i l * xseq (start + t) l)| <=
        gamma fp 3 * Finset.univ.sum (fun l : Fin n =>
          |Nhat ⟨start + t, hidx t ht⟩ i l| * |xseq (start + t) l|)) :
    exists DeltaU : Fin n -> Fin n -> Real,
      exists DeltaY : Fin n -> Real,
        (forall i : Fin n,
          Finset.univ.sum (fun j : Fin n =>
            (V start i j + DeltaU i j) * xhat j) =
            xseq start i + DeltaY i) /\
        (forall i j : Fin n,
          V start i j + DeltaU i j =
            matMul n Q (V (start + (n - 1))) i j) /\
        (forall i j : Fin n,
          |DeltaU i j| <= gje_c₃ fp n *
            Finset.univ.sum (fun k : Fin n =>
              |ch14ext_gjeXabs n Nhat Q start (n - 1) i k| *
                |V start k j|)) /\
        (forall i : Fin n,
          |DeltaY i| <=
            gje_c₃ fp n * Finset.univ.sum (fun j : Fin n =>
              |ch14ext_gjeXabs n Nhat Q start (n - 1) i j| *
                |xseq start j|) +
            gamma fp 1 * Finset.univ.sum (fun k : Fin n =>
              |Q i k| * Finset.univ.sum (fun j : Fin n =>
                |V (start + (n - 1)) k j| * |xhat j|))) := by
  let P := gje_cumulative_product n Nhat start (start + (n - 1))
  let E : Fin n -> Fin n -> Real := fun i j =>
    V (start + (n - 1)) i j - matMul n P (V start) i j
  let g : Fin n -> Real := fun i =>
    xseq (start + (n - 1)) i - matMulVec n P (xseq start) i
  let dvec : Fin n -> Real := matMulVec n DeltaD xhat
  let DeltaU := matMul n Q E
  let DeltaY : Fin n -> Real := fun i =>
    matMulVec n Q g i - matMulVec n Q dvec i
  have hEbnd : forall k j : Fin n,
      |E k j| <= gje_c₃ fp n *
        ch14ext_boundObj n Nhat (V start) start (n - 1) k j :=
    ch14ext_matrixAccumulation_c3 n fp Nhat V start hn h3 hidx hrecM
  have hgbnd : forall k : Fin n,
      |g k| <= gje_c₃ fp n *
        ch14ext_boundVec n Nhat (xseq start) start (n - 1) k :=
    ch14ext_rhsAccumulation_c3 n fp Nhat xseq start hn h3 hidx hrecX
  have hQPV : matMul n Q (matMul n P (V start)) = V start := by
    rw [← matMul_assoc]
    change matMul n (matMul n Q P) (V start) = V start
    rw [show matMul n Q P = idMatrix n by simpa [P] using hQP,
      matMul_id_left]
  have hDeltaUeq : forall i j : Fin n,
      V start i j + DeltaU i j =
        matMul n Q (V (start + (n - 1))) i j := by
    intro i j
    have hexp : matMul n Q E i j =
        matMul n Q (V (start + (n - 1))) i j -
          matMul n Q (matMul n P (V start)) i j := by
      change (Finset.univ.sum fun k : Fin n => Q i k * E k j) =
        (Finset.univ.sum fun k : Fin n =>
          Q i k * V (start + (n - 1)) k j) -
        (Finset.univ.sum fun k : Fin n =>
          Q i k * matMul n P (V start) k j)
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by
        show Q i k *
            (V (start + (n - 1)) k j - matMul n P (V start) k j) = _
        ring)
    change V start i j + matMul n Q E i j = _
    rw [hexp, congrFun (congrFun hQPV i) j]
    ring
  have hQg : forall i : Fin n,
      matMulVec n Q g i =
        matMulVec n Q (xseq (start + (n - 1))) i - xseq start i := by
    intro i
    have hQPy : matMulVec n Q (matMulVec n P (xseq start)) = xseq start := by
      funext a
      rw [← matMulVec_matMul]
      rw [show matMul n Q P = idMatrix n by simpa [P] using hQP,
        matMulVec_id]
    change (Finset.univ.sum fun k : Fin n => Q i k * g k) = _
    rw [show (Finset.univ.sum fun k : Fin n => Q i k * g k) =
        (Finset.univ.sum fun k : Fin n =>
          Q i k * xseq (start + (n - 1)) k) -
        (Finset.univ.sum fun k : Fin n =>
          Q i k * matMulVec n P (xseq start) k) by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by
        change Q i k *
          (xseq (start + (n - 1)) k - matMulVec n P (xseq start) k) = _
        ring)]
    change matMulVec n Q (xseq (start + (n - 1))) i -
      matMulVec n Q (matMulVec n P (xseq start)) i = _
    rw [congrFun hQPy i]
  have hVx : forall i : Fin n,
      matMulVec n (V (start + (n - 1))) xhat i =
        xseq (start + (n - 1)) i - dvec i := by
    intro i
    have hf := hfinal i
    change (Finset.univ.sum fun j : Fin n =>
      (V (start + (n - 1)) i j + DeltaD i j) * xhat j) = _ at hf
    have hsplit :
        (Finset.univ.sum fun j : Fin n =>
          (V (start + (n - 1)) i j + DeltaD i j) * xhat j) =
        matMulVec n (V (start + (n - 1))) xhat i + dvec i := by
      change _ =
        (Finset.univ.sum fun j : Fin n =>
          V (start + (n - 1)) i j * xhat j) +
        (Finset.univ.sum fun j : Fin n => DeltaD i j * xhat j)
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hsplit] at hf
    linarith
  have hEq : forall i : Fin n,
      Finset.univ.sum (fun j : Fin n =>
        (V start i j + DeltaU i j) * xhat j) =
        xseq start i + DeltaY i := by
    intro i
    have hleft :
        (Finset.univ.sum fun j : Fin n =>
          (V start i j + DeltaU i j) * xhat j) =
        matMulVec n Q
          (matMulVec n (V (start + (n - 1))) xhat) i := by
      calc
        (Finset.univ.sum fun j : Fin n =>
          (V start i j + DeltaU i j) * xhat j) =
            matMulVec n (matMul n Q (V (start + (n - 1)))) xhat i := by
              unfold matMulVec
              exact Finset.sum_congr rfl (fun j _ => by rw [hDeltaUeq i j])
        _ = matMulVec n Q
              (matMulVec n (V (start + (n - 1))) xhat) i := by
              rw [matMulVec_matMul]
    rw [hleft]
    have hlin : matMulVec n Q
        (matMulVec n (V (start + (n - 1))) xhat) i =
        matMulVec n Q (xseq (start + (n - 1))) i -
          matMulVec n Q dvec i := by
      unfold matMulVec
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by
        have hv := hVx k
        change (Finset.univ.sum fun j : Fin n =>
          V (start + (n - 1)) k j * xhat j) = _ at hv
        rw [hv]
        ring)
    rw [hlin]
    change matMulVec n Q (xseq (start + (n - 1))) i -
        matMulVec n Q dvec i =
      xseq start i +
        (matMulVec n Q g i - matMulVec n Q dvec i)
    linarith [hQg i]
  have hDeltaUbound : forall i j : Fin n,
      |DeltaU i j| <= gje_c₃ fp n *
        Finset.univ.sum (fun k : Fin n =>
          |ch14ext_gjeXabs n Nhat Q start (n - 1) i k| * |V start k j|) := by
    intro i j
    have hb := ch14ext_matMul_abs_bound n Q E
      (ch14ext_boundObj n Nhat (V start) start (n - 1))
      (gje_c₃ fp n) hEbnd i j
    have hrw : matMul n (absMatrix n Q)
          (ch14ext_boundObj n Nhat (V start) start (n - 1)) i j =
        Finset.univ.sum (fun k : Fin n =>
          |ch14ext_gjeXabs n Nhat Q start (n - 1) i k| * |V start k j|) := by
      have hassoc : matMul n (absMatrix n Q)
            (ch14ext_boundObj n Nhat (V start) start (n - 1)) =
          matMul n (ch14ext_gjeXabs n Nhat Q start (n - 1))
            (absMatrix n (V start)) := by
        show matMul n (absMatrix n Q)
            (matMul n (ch14ext_absCumProd n Nhat start (n - 1))
              (absMatrix n (V start))) = _
        rw [← matMul_assoc]
        rfl
      rw [hassoc]
      exact Finset.sum_congr rfl (fun k _ => by
        rw [abs_of_nonneg
          (ch14ext_gjeXabs_nonneg n Nhat Q start (n - 1) i k)]
        simp [absMatrix])
    change |matMul n Q E i j| <= _
    rw [hrw] at hb
    exact hb
  have hQgBound : forall i : Fin n,
      |matMulVec n Q g i| <= gje_c₃ fp n *
        Finset.univ.sum (fun j : Fin n =>
          |ch14ext_gjeXabs n Nhat Q start (n - 1) i j| * |xseq start j|) := by
    intro i
    have hb := ch14ext_matMulVec_abs_bound n Q g
      (ch14ext_boundVec n Nhat (xseq start) start (n - 1))
      (gje_c₃ fp n) hgbnd i
    have hrw : matMulVec n (absMatrix n Q)
          (ch14ext_boundVec n Nhat (xseq start) start (n - 1)) i =
        Finset.univ.sum (fun j : Fin n =>
          |ch14ext_gjeXabs n Nhat Q start (n - 1) i j| * |xseq start j|) := by
      have hassoc : matMulVec n (absMatrix n Q)
            (ch14ext_boundVec n Nhat (xseq start) start (n - 1)) =
          matMulVec n (ch14ext_gjeXabs n Nhat Q start (n - 1))
            (absVec n (xseq start)) := by
        funext a
        show matMulVec n (absMatrix n Q)
            (matMulVec n (ch14ext_absCumProd n Nhat start (n - 1))
              (absVec n (xseq start))) a = _
        rw [← matMulVec_matMul]
        rfl
      rw [hassoc]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [abs_of_nonneg
          (ch14ext_gjeXabs_nonneg n Nhat Q start (n - 1) i j)]
        simp [absVec])
    rw [hrw] at hb
    exact hb
  have hdvecBound : forall k : Fin n,
      |dvec k| <= gamma fp 1 * Finset.univ.sum (fun j : Fin n =>
        |V (start + (n - 1)) k j| * |xhat j|) := by
    intro k
    change |Finset.univ.sum (fun j : Fin n => DeltaD k j * xhat j)| <= _
    calc
      |Finset.univ.sum (fun j : Fin n => DeltaD k j * xhat j)| <=
          Finset.univ.sum (fun j : Fin n => |DeltaD k j * xhat j|) :=
        Finset.abs_sum_le_sum_abs _ _
      _ = Finset.univ.sum (fun j : Fin n => |DeltaD k j| * |xhat j|) := by
        exact Finset.sum_congr rfl (fun j _ => abs_mul _ _)
      _ <= Finset.univ.sum (fun j : Fin n =>
          (gamma fp 1 * |V (start + (n - 1)) k j|) * |xhat j|) := by
        exact Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_right (hDeltaD k j) (abs_nonneg _))
      _ = gamma fp 1 * Finset.univ.sum (fun j : Fin n =>
          |V (start + (n - 1)) k j| * |xhat j|) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring)
  have hQdBound : forall i : Fin n,
      |matMulVec n Q dvec i| <= gamma fp 1 *
        Finset.univ.sum (fun k : Fin n => |Q i k| *
          Finset.univ.sum (fun j : Fin n =>
            |V (start + (n - 1)) k j| * |xhat j|)) := by
    intro i
    calc
      |matMulVec n Q dvec i| <=
          Finset.univ.sum (fun k : Fin n => |Q i k * dvec k|) := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ = Finset.univ.sum (fun k : Fin n => |Q i k| * |dvec k|) := by
        exact Finset.sum_congr rfl (fun k _ => abs_mul _ _)
      _ <= Finset.univ.sum (fun k : Fin n => |Q i k| *
          (gamma fp 1 * Finset.univ.sum (fun j : Fin n =>
            |V (start + (n - 1)) k j| * |xhat j|))) := by
        exact Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hdvecBound k) (abs_nonneg _))
      _ = gamma fp 1 * Finset.univ.sum (fun k : Fin n => |Q i k| *
          Finset.univ.sum (fun j : Fin n =>
            |V (start + (n - 1)) k j| * |xhat j|)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
  refine ⟨DeltaU, DeltaY, hEq, hDeltaUeq, hDeltaUbound, ?_⟩
  intro i
  change |matMulVec n Q g i - matMulVec n Q dvec i| <= _
  calc
    |matMulVec n Q g i - matMulVec n Q dvec i| <=
        |matMulVec n Q g i| + |matMulVec n Q dvec i| := by
      simpa [sub_eq_add_neg] using abs_add_le (matMulVec n Q g i)
        (-(matMulVec n Q dvec i))
    _ <= _ := add_le_add (hQgBound i) (hQdBound i)

/-- Source-facing form of the preceding result.  The only structural premise
is the upper-triangular output of GE; the finalized executor itself supplies
the diagonal shape used by the final divisions. -/
theorem ch14ext_gjeFinalizedDivOutput_diagonal_backward_error_of_upper
    {n : Nat} (fp : FPModel) (s : Ch14GJEState n) (hn : 1 <= n)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0)
    (h1 : gammaValid fp 1) :
    exists DeltaD : Fin n -> Fin n -> Real,
      (forall i j : Fin n,
        |DeltaD i j| <= gamma fp 1 *
          |(ch14ext_gjeBeforeFinalDivision fp s).matrix i j|) /\
      (forall i j : Fin n, i ≠ j -> DeltaD i j = 0) /\
      (forall i : Fin n,
        Finset.univ.sum (fun j : Fin n =>
          ((ch14ext_gjeBeforeFinalDivision fp s).matrix i j + DeltaD i j) *
            ch14ext_gjeFinalizedDivOutput fp s j) =
          (ch14ext_gjeBeforeFinalDivision fp s).rhs i) := by
  let pre := ch14ext_gjeBeforeFinalDivision fp s
  have hpreDiag : forall i : Fin n, pre.matrix i i ≠ 0 := by
    intro i
    exact ch14ext_gjeBeforeFinalDivision_diag_ne_zero fp s hdiag i
  have hpreOff : forall i j : Fin n, i ≠ j -> pre.matrix i j = 0 := by
    intro i j hij
    have hfinal := ch14ext_gjeFinalizedSourceTrace_final_diagonal fp s hn hUpper
    change (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix i j = 0
    rw [hfinal]
    simp [ch14ext_gjeFinalDiagonal, hij]
  have hscalar : forall i : Fin n, exists e : Real,
      |e| <= gamma fp 1 * |pre.matrix i i| /\
      (pre.matrix i i + e) *
          fp.fl_div (pre.rhs i) (pre.matrix i i) = pre.rhs i := by
    intro i
    exact ch14ext_gjeFinalDivision_scalar_backward_error
      fp (pre.rhs i) (pre.matrix i i) (hpreDiag i) h1
  choose e heBound heEq using hscalar
  let DeltaD : Fin n -> Fin n -> Real :=
    fun i j => if i = j then e i else 0
  refine ⟨DeltaD, ?_, ?_, ?_⟩
  . intro i j
    by_cases hij : i = j
    . subst j
      simpa [DeltaD] using heBound i
    . simp only [DeltaD, if_neg hij, abs_zero]
      exact mul_nonneg (gamma_nonneg fp h1) (abs_nonneg _)
  . intro i j hij
    simp [DeltaD, hij]
  . intro i
    rw [Finset.sum_eq_single i]
    . simpa [DeltaD, ch14ext_gjeFinalizedDivOutput, pre,
        ch14ext_gjeBeforeFinalDivision] using heEq i
    . intro j _ hji
      have hoff : pre.matrix i j = 0 := hpreOff i j (Ne.symm hji)
      have hoff' :
          (ch14ext_gjeBeforeFinalDivision fp s).matrix i j = 0 := by
        simpa [pre] using hoff
      have hij : i ≠ j := Ne.symm hji
      simp [DeltaD, hij, hoff']
    . intro hi
      exact False.elim (hi (Finset.mem_univ i))

/-- **Higham (14.30a-c), now for the literal general Algorithm 14.4 output.**

The elimination phase is the recursively executed finalized trace and the
returned vector is the actual componentwise `fl_div` output.  Consequently no
`final_matrix = I` or `final_vector` premise occurs.  The last summand in the
`DeltaY` bound is the explicit final-division contribution that the PDF hides
behind its `D = I` normalization. -/
theorem ch14ext_gjeFinalizedSourceTrace_stage2_backward_error_14_30abc_with_final_division
    {n : Nat} (fp : FPModel) (s : Ch14GJEState n)
    (hn : 1 <= n) (h3 : gammaValid fp 3) (h1 : gammaValid fp 1)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    exists DeltaU : Fin n -> Fin n -> Real,
      exists DeltaY : Fin n -> Real,
        (forall i : Fin n,
          Finset.univ.sum (fun j : Fin n =>
            (s.matrix i j + DeltaU i j) *
              ch14ext_gjeFinalizedDivOutput fp s j) =
            s.rhs i + DeltaY i) /\
        (forall i j : Fin n,
          s.matrix i j + DeltaU i j =
            matMul n (ch14ext_gjeFinalizedSourceQ fp s)
              (ch14ext_gjeBeforeFinalDivision fp s).matrix i j) /\
        (forall i j : Fin n,
          |DeltaU i j| <= gje_c₃ fp n *
            Finset.univ.sum (fun k : Fin n =>
              |ch14ext_gjeFinalizedSourceXabs fp s i k| * |s.matrix k j|)) /\
        (forall i : Fin n,
          |DeltaY i| <=
            gje_c₃ fp n * Finset.univ.sum (fun j : Fin n =>
              |ch14ext_gjeFinalizedSourceXabs fp s i j| * |s.rhs j|) +
            gamma fp 1 * Finset.univ.sum (fun k : Fin n =>
              |ch14ext_gjeFinalizedSourceQ fp s i k| *
                Finset.univ.sum (fun j : Fin n =>
                  |(ch14ext_gjeBeforeFinalDivision fp s).matrix k j| *
                    |ch14ext_gjeFinalizedDivOutput fp s j|))) := by
  let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
  let xseq := ch14ext_gjeFinalizedSourceTraceRhs fp 1 s
  let Nhat := ch14ext_gjeFinalizedSourceStages fp s
  let Q := ch14ext_gjeFinalizedSourceQ fp s
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hrec :=
    ch14ext_gjeFinalizedSourceTrace_recurrence_bounds_14_25b_14_26
      fp s hidx hUpper hpiv' h3
  have hsum : 1 + (n - 1) = n := by omega
  have hQP : matMul n Q
      (gje_cumulative_product n Nhat 1 (1 + (n - 1))) = idMatrix n := by
    simpa [Q, Nhat, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeFinalizedSourceStages] using
      ch14ext_gjeConstructedQ_isLeftInverse n V 1 hidx
  obtain ⟨DeltaD, hDeltaD, _hDeltaDoff, hFinalDiv⟩ :=
    ch14ext_gjeFinalizedDivOutput_diagonal_backward_error_of_upper
      fp s hn hUpper hdiag h1
  have hFinalDiv' : forall i : Fin n,
      Finset.univ.sum (fun j : Fin n =>
        (V (1 + (n - 1)) i j + DeltaD i j) * xhat j) =
        xseq (1 + (n - 1)) i := by
    intro i
    rw [hsum]
    simpa [V, xseq, xhat, ch14ext_gjeBeforeFinalDivision,
      ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTraceRhs] using hFinalDiv i
  have hDeltaD' : forall i j : Fin n,
      |DeltaD i j| <= gamma fp 1 * |V (1 + (n - 1)) i j| := by
    intro i j
    rw [hsum]
    simpa [V, ch14ext_gjeBeforeFinalDivision,
      ch14ext_gjeFinalizedSourceTraceMatrix] using hDeltaD i j
  obtain ⟨DeltaU, DeltaY, hEq, hQD, hDeltaU, hDeltaY⟩ :=
    ch14ext_gje_stage2_backward_error_of_accumulation_final_diagonal
      n fp xhat Nhat V xseq Q DeltaD 1 hn h3 hidx hQP
      hFinalDiv' hDeltaD' hrec.1 hrec.2
  refine ⟨DeltaU, DeltaY, ?_, ?_, ?_, ?_⟩
  . intro i
    simpa [V, xseq, xhat, ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTraceRhs,
      ch14ext_gjeFinalizedSourceTrace] using hEq i
  . intro i j
    simpa [V, Q, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeBeforeFinalDivision,
      ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTrace] using hQD i j
  . intro i j
    simpa [V, Nhat, Q, ch14ext_gjeFinalizedSourceXabs,
      ch14ext_gjeFinalizedSourceStages, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTrace] using hDeltaU i j
  . intro i
    simpa [V, xseq, Nhat, Q, xhat,
      ch14ext_gjeFinalizedSourceXabs,
      ch14ext_gjeFinalizedSourceStages, ch14ext_gjeFinalizedSourceQ,
      ch14ext_gjeFinalizedSourceTraceMatrix,
      ch14ext_gjeFinalizedSourceTraceRhs,
      ch14ext_gjeBeforeFinalDivision,
      ch14ext_gjeFinalizedSourceTrace] using hDeltaY i

/-- The absolute action generated by the final diagonal divisions. -/
noncomputable def ch14ext_gjeFinalDivisionEnvelope (n : Nat)
    (Q D : Fin n -> Fin n -> Real) (xhat : Fin n -> Real) : Fin n -> Real :=
  fun i => Finset.univ.sum (fun k : Fin n =>
    |Q i k| * Finset.univ.sum (fun j : Fin n => |D k j| * |xhat j|))

/-- Action of `|L|` on the final-division envelope. -/
noncomputable def ch14ext_gjeFinalDivisionLAction (n : Nat)
    (L Q D : Fin n -> Fin n -> Real) (xhat : Fin n -> Real)
    (i : Fin n) : Real :=
  matMulVec n (absMatrix n L)
    (ch14ext_gjeFinalDivisionEnvelope n Q D xhat) i

/-- Action of `|L||X|` on the final-division envelope. -/
noncomputable def ch14ext_gjeFinalDivisionLXAction (n : Nat)
    (L X Q D : Fin n -> Fin n -> Real) (xhat : Fin n -> Real)
    (i : Fin n) : Real :=
  matMulVec n (absMatrix n L)
    (matMulVec n (absMatrix n X)
      (ch14ext_gjeFinalDivisionEnvelope n Q D xhat)) i

theorem ch14ext_gjeFinalDivisionEnvelope_nonneg (n : Nat)
    (Q D : Fin n -> Fin n -> Real) (xhat : Fin n -> Real) (i : Fin n) :
    0 <= ch14ext_gjeFinalDivisionEnvelope n Q D xhat i := by
  unfold ch14ext_gjeFinalDivisionEnvelope
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _)
    (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))))

/-- Since the executed last matrix `D` is diagonal, the apparently new
`|Q||D||xhat|` object is bounded by
`|U||xhat| + c |X||U||xhat|` using `QD = U + DeltaU`. -/
theorem ch14ext_gjeFinalDivisionEnvelope_le_stage_objects (n : Nat)
    (U X Q D DeltaU : Fin n -> Fin n -> Real)
    (xhat : Fin n -> Real) (c : Real) (hc : 0 <= c)
    (hDoff : forall i j : Fin n, i ≠ j -> D i j = 0)
    (hQD : forall i j : Fin n,
      U i j + DeltaU i j = matMul n Q D i j)
    (hDeltaU : forall i j : Fin n,
      |DeltaU i j| <= c * Finset.univ.sum (fun k : Fin n =>
        |X i k| * |U k j|)) :
    forall i : Fin n,
      ch14ext_gjeFinalDivisionEnvelope n Q D xhat i <=
        matMulVec n (absMatrix n U) (absVec n xhat) i +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n U) (absVec n xhat)) i := by
  intro i
  have hQDentry : forall k : Fin n,
      matMul n Q D i k = Q i k * D k k := by
    intro k
    unfold matMul
    rw [Finset.sum_eq_single k]
    . intro j _ hjk
      rw [hDoff j k hjk, mul_zero]
    . simp
  have hcollapse : ch14ext_gjeFinalDivisionEnvelope n Q D xhat i =
      Finset.univ.sum (fun k : Fin n => |matMul n Q D i k| * |xhat k|) := by
    unfold ch14ext_gjeFinalDivisionEnvelope
    apply Finset.sum_congr rfl
    intro k _
    have hinner : Finset.univ.sum (fun j : Fin n => |D k j| * |xhat j|) =
        |D k k| * |xhat k| := by
      rw [Finset.sum_eq_single k]
      . intro j _ hjk
        rw [hDoff k j (Ne.symm hjk), abs_zero, zero_mul]
      . simp
    rw [hinner, hQDentry, abs_mul]
    ring
  rw [hcollapse]
  calc
    Finset.univ.sum (fun k : Fin n => |matMul n Q D i k| * |xhat k|) =
        Finset.univ.sum (fun k : Fin n =>
          |U i k + DeltaU i k| * |xhat k|) := by
      exact Finset.sum_congr rfl (fun k _ => by rw [hQD i k])
    _ <= Finset.univ.sum (fun k : Fin n =>
        (|U i k| + |DeltaU i k|) * |xhat k|) := by
      exact Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _))
    _ <= Finset.univ.sum (fun k : Fin n =>
        (|U i k| + c * Finset.univ.sum (fun a : Fin n =>
          |X i a| * |U a k|)) * |xhat k|) := by
      exact Finset.sum_le_sum (fun k _ =>
        mul_le_mul_of_nonneg_right
          (add_le_add_right (hDeltaU i k) |U i k|) (abs_nonneg _))
    _ = matMulVec n (absMatrix n U) (absVec n xhat) i +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n U) (absVec n xhat)) i := by
      unfold matMulVec absMatrix absVec
      simp only [add_mul, Finset.sum_add_distrib]
      congr 1
      calc
        Finset.univ.sum (fun k : Fin n =>
            (c * Finset.univ.sum (fun a : Fin n => |X i a| * |U a k|)) *
              |xhat k|) =
            c * Finset.univ.sum (fun k : Fin n =>
              Finset.univ.sum (fun a : Fin n => |X i a| * |U a k|) *
                |xhat k|) := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = c * Finset.univ.sum (fun a : Fin n =>
              |X i a| * Finset.univ.sum (fun k : Fin n => |U a k| * |xhat k|)) := by
              congr 1
              calc
                Finset.univ.sum (fun k : Fin n =>
                    Finset.univ.sum (fun a : Fin n => |X i a| * |U a k|) *
                      |xhat k|) =
                    Finset.univ.sum (fun k : Fin n =>
                      Finset.univ.sum (fun a : Fin n =>
                        |X i a| * (|U a k| * |xhat k|))) := by
                          exact Finset.sum_congr rfl (fun k _ => by
                            rw [Finset.sum_mul]
                            exact Finset.sum_congr rfl (fun a _ => by ring))
                _ = Finset.univ.sum (fun a : Fin n =>
                      Finset.univ.sum (fun k : Fin n =>
                        |X i a| * (|U a k| * |xhat k|))) := Finset.sum_comm
                _ = Finset.univ.sum (fun a : Fin n =>
                      |X i a| * Finset.univ.sum (fun k : Fin n =>
                        |U a k| * |xhat k|)) := by
                          exact Finset.sum_congr rfl (fun a _ => by
                            rw [Finset.mul_sum])

/-- Four-term matrix-vector linearity used by the division-aware residual
bookkeeping. -/
theorem ch14ext_matMulVec_add_three_scales (n : Nat)
    (M : Fin n -> Fin n -> Real) (w x y z : Fin n -> Real)
    (a b c : Real) (i : Fin n) :
    matMulVec n M (fun j => w j + a * x j + b * y j + c * z j) i =
      matMulVec n M w i + a * matMulVec n M x i +
        b * matMulVec n M y i + c * matMulVec n M z i := by
  unfold matMulVec
  simp only [mul_add, Finset.sum_add_distrib]
  have hx : Finset.univ.sum (fun j : Fin n => M i j * (a * x j)) =
      a * Finset.univ.sum (fun j : Fin n => M i j * x j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hy : Finset.univ.sum (fun j : Fin n => M i j * (b * y j)) =
      b * Finset.univ.sum (fun j : Fin n => M i j * y j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hz : Finset.univ.sum (fun j : Fin n => M i j * (c * z j)) =
      c * Finset.univ.sum (fun j : Fin n => M i j * z j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hx, hy, hz]

theorem ch14ext_matMulVec_two_scales (n : Nat)
    (M : Fin n -> Fin n -> Real) (x y : Fin n -> Real)
    (a b : Real) (i : Fin n) :
    matMulVec n M (fun j => a * x j + b * y j) i =
      a * matMulVec n M x i + b * matMulVec n M y i := by
  unfold matMulVec
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (.+.)
  . exact Finset.sum_congr rfl (fun j _ => by ring)
  . exact Finset.sum_congr rfl (fun j _ => by ring)

/-- Residual bound with one additional RHS-error envelope.  This is the exact
extension of `ch14ext_gjeResidual1433_bound_corrected` needed for the literal
final divisions. -/
theorem ch14ext_gjeResidual1433_bound_with_extra_rhs (n : Nat)
    (L U X DeltaA DeltaL DeltaU : Fin n -> Fin n -> Real)
    (y xhat DeltaY r : Fin n -> Real) (g c d : Real)
    (hg : 0 <= g) (hc : 0 <= c) (hd : 0 <= d)
    (hr : forall i : Fin n, 0 <= r i)
    (hDeltaA : forall i j : Fin n, |DeltaA i j| <= g *
      Finset.univ.sum (fun k : Fin n => |L i k| * |U k j|))
    (hDeltaL : forall i j : Fin n, |DeltaL i j| <= g * |L i j|)
    (hDeltaU : forall i j : Fin n, |DeltaU i j| <= c *
      Finset.univ.sum (fun k : Fin n => |X i k| * |U k j|))
    (hDeltaY : forall i : Fin n, |DeltaY i| <=
      c * Finset.univ.sum (fun j : Fin n => |X i j| * |y j|) + d * r i)
    (hStage : forall i : Fin n,
      matMulVec n U xhat i + matMulVec n DeltaU xhat i = y i + DeltaY i)
    (i : Fin n) :
    |ch14ext_gjeResidual1433 n L U DeltaA DeltaL DeltaU xhat DeltaY i| <=
      2 * g * ch14ext_gjeResidualS1 n L U xhat i +
      2 * c * ch14ext_gjeResidualS2 n L X U xhat i +
      2 * g * c * ch14ext_gjeResidualS2 n L X U xhat i +
      c * c * (1 + g) *
        (ch14ext_gjeResidualS22 n L X U xhat i +
          ch14ext_gjeResidualS23 n L X y i) +
      d * (1 + g) * matMulVec n (absMatrix n L) r i +
      c * d * (1 + g) *
        matMulVec n (absMatrix n L) (matMulVec n (absMatrix n X) r) i := by
  let AL := absMatrix n L
  let AU := absMatrix n U
  let AX := absMatrix n X
  let ux := matMulVec n AU (absVec n xhat)
  let xu := matMulVec n AX ux
  let xy := matMulVec n AX (absVec n y)
  have hDeltaA' : forall a b : Fin n, |DeltaA a b| <=
      g * matMul n AL AU a b := by
    intro a b
    simpa [AL, AU, matMul, absMatrix] using hDeltaA a b
  have hA0 := ch14ext_abs_matMulVec_le_scaled n DeltaA
    (matMul n AL AU) xhat g hDeltaA' i
  rw [matMulVec_matMul] at hA0
  have hA : |matMulVec n DeltaA xhat i| <=
      g * ch14ext_gjeResidualS1 n L U xhat i := by
    simpa [ch14ext_gjeResidualS1, AL, AU] using hA0
  have hDeltaL' : forall a b : Fin n, |DeltaL a b| <= g * AL a b := by
    intro a b
    simpa [AL, absMatrix] using hDeltaL a b
  have hDeltaU' : forall a b : Fin n, |DeltaU a b| <=
      c * matMul n AX AU a b := by
    intro a b
    simpa [AX, AU, matMul, absMatrix] using hDeltaU a b
  have hDeltaUact : forall a : Fin n,
      |matMulVec n DeltaU xhat a| <= c * xu a := by
    intro a
    have h := ch14ext_abs_matMulVec_le_scaled n DeltaU
      (matMul n AX AU) xhat c hDeltaU' a
    rw [matMulVec_matMul] at h
    simpa [xu, ux, AX, AU] using h
  have hUx : forall a : Fin n, |matMulVec n U xhat a| <= ux a := by
    intro a
    simpa [ux, AU, matMulVec, absMatrix, absVec] using
      abs_matMulVec_le n U xhat a
  have hDeltaYact : forall a : Fin n, |DeltaY a| <= c * xy a + d * r a := by
    intro a
    simpa [xy, AX, matMulVec, absMatrix, absVec] using hDeltaY a
  have hLDeltaU0 := ch14ext_abs_matMulVec_le_of_vec_bound n L
    (matMulVec n DeltaU xhat) (fun a => c * xu a) hDeltaUact i
  have hLDeltaU : |matMulVec n L (matMulVec n DeltaU xhat) i| <=
      c * ch14ext_gjeResidualS2 n L X U xhat i := by
    calc
      |matMulVec n L (matMulVec n DeltaU xhat) i| <=
          matMulVec n AL (fun a => c * xu a) i := by simpa [AL] using hLDeltaU0
      _ = c * ch14ext_gjeResidualS2 n L X U xhat i := by
        rw [ch14ext_matMulVec_scale]
        rfl
  have hDeltaLU0 := ch14ext_abs_matMulVec_le_scaled n DeltaL AL
    (matMulVec n U xhat) g hDeltaL' i
  have hALU := ch14ext_matMulVec_mono_nonneg n AL
    (absVec n (matMulVec n U xhat)) ux
    (fun a b => by simp [AL, absMatrix])
    (fun a => by simpa [absVec] using hUx a) i
  have hDeltaLU : |matMulVec n DeltaL (matMulVec n U xhat) i| <=
      g * ch14ext_gjeResidualS1 n L U xhat i := by
    calc
      |matMulVec n DeltaL (matMulVec n U xhat) i| <=
          g * matMulVec n AL (absVec n (matMulVec n U xhat)) i := hDeltaLU0
      _ <= g * matMulVec n AL ux i := mul_le_mul_of_nonneg_left hALU hg
      _ = g * ch14ext_gjeResidualS1 n L U xhat i := rfl
  have hDeltaLDeltaU0 := ch14ext_abs_matMulVec_le_scaled n DeltaL AL
    (matMulVec n DeltaU xhat) g hDeltaL' i
  have hALDeltaU := ch14ext_matMulVec_mono_nonneg n AL
    (absVec n (matMulVec n DeltaU xhat)) (fun a => c * xu a)
    (fun a b => by simp [AL, absMatrix])
    (fun a => by simpa [absVec] using hDeltaUact a) i
  have hDeltaLDeltaU :
      |matMulVec n DeltaL (matMulVec n DeltaU xhat) i| <=
        g * c * ch14ext_gjeResidualS2 n L X U xhat i := by
    calc
      |matMulVec n DeltaL (matMulVec n DeltaU xhat) i| <=
          g * matMulVec n AL (absVec n (matMulVec n DeltaU xhat)) i :=
        hDeltaLDeltaU0
      _ <= g * matMulVec n AL (fun a => c * xu a) i :=
        mul_le_mul_of_nonneg_left hALDeltaU hg
      _ = g * c * ch14ext_gjeResidualS2 n L X U xhat i := by
        rw [ch14ext_matMulVec_scale]
        simp [ch14ext_gjeResidualS2, xu, ux, AL, AX, AU]
        ring
  have hLDeltaY0 := ch14ext_abs_matMulVec_le_of_vec_bound n L DeltaY
    (fun a => c * xy a + d * r a) hDeltaYact i
  have hLDeltaY : |matMulVec n L DeltaY i| <=
      c * matMulVec n AL xy i + d * matMulVec n AL r i := by
    calc
      |matMulVec n L DeltaY i| <=
          matMulVec n AL (fun a => c * xy a + d * r a) i := by
        simpa [AL] using hLDeltaY0
      _ = _ := by
        exact ch14ext_matMulVec_two_scales n AL xy r c d i
  have hDeltaLDeltaY0 := ch14ext_abs_matMulVec_le_scaled n DeltaL AL
    DeltaY g hDeltaL' i
  have hALDeltaY := ch14ext_matMulVec_mono_nonneg n AL (absVec n DeltaY)
    (fun a => c * xy a + d * r a) (fun a b => by simp [AL, absMatrix])
    (fun a => by simpa [absVec] using hDeltaYact a) i
  have hDeltaLDeltaY : |matMulVec n DeltaL DeltaY i| <=
      g * (c * matMulVec n AL xy i + d * matMulVec n AL r i) := by
    calc
      |matMulVec n DeltaL DeltaY i| <=
          g * matMulVec n AL (absVec n DeltaY) i := hDeltaLDeltaY0
      _ <= g * matMulVec n AL (fun a => c * xy a + d * r a) i :=
        mul_le_mul_of_nonneg_left hALDeltaY hg
      _ = _ := by
        rw [ch14ext_matMulVec_two_scales]
  have hyBound : forall a : Fin n, |y a| <=
      ux a + c * xu a + c * xy a + d * r a := by
    intro a
    have hyEq : y a = matMulVec n U xhat a +
        matMulVec n DeltaU xhat a - DeltaY a := by linarith [hStage a]
    rw [hyEq]
    calc
      |matMulVec n U xhat a + matMulVec n DeltaU xhat a - DeltaY a| <=
          |matMulVec n U xhat a| + |matMulVec n DeltaU xhat a| + |DeltaY a| := by
        have hsum := abs_add_le (matMulVec n U xhat a) (matMulVec n DeltaU xhat a)
        have hsub : |matMulVec n U xhat a + matMulVec n DeltaU xhat a - DeltaY a| <=
            |matMulVec n U xhat a + matMulVec n DeltaU xhat a| + |DeltaY a| := by
          simpa [sub_eq_add_neg, abs_neg] using
            abs_add_le (matMulVec n U xhat a + matMulVec n DeltaU xhat a) (-DeltaY a)
        linarith
      _ <= _ := by linarith [hUx a, hDeltaUact a, hDeltaYact a]
  have hXy : forall a : Fin n,
      matMulVec n AX (absVec n y) a <=
        matMulVec n AX ux a + c * matMulVec n AX xu a +
          c * matMulVec n AX xy a + d * matMulVec n AX r a := by
    intro a
    calc
      matMulVec n AX (absVec n y) a <=
          matMulVec n AX (fun j => ux j + c * xu j + c * xy j + d * r j) a :=
        ch14ext_matMulVec_mono_nonneg n AX (absVec n y)
          (fun j => ux j + c * xu j + c * xy j + d * r j)
          (fun p q => by simp [AX, absMatrix])
          (fun j => by simpa [absVec] using hyBound j) a
      _ = _ := by
        exact ch14ext_matMulVec_add_three_scales n AX ux xu xy r c c d a
  have hS3 : matMulVec n AL xy i <=
      ch14ext_gjeResidualS2 n L X U xhat i +
        c * ch14ext_gjeResidualS22 n L X U xhat i +
        c * ch14ext_gjeResidualS23 n L X y i +
        d * matMulVec n AL (matMulVec n AX r) i := by
    calc
      matMulVec n AL xy i <= matMulVec n AL
          (fun a => matMulVec n AX ux a + c * matMulVec n AX xu a +
            c * matMulVec n AX xy a + d * matMulVec n AX r a) i :=
        ch14ext_matMulVec_mono_nonneg n AL xy _
          (fun p q => by simp [AL, absMatrix]) hXy i
      _ = _ := by
        rw [ch14ext_matMulVec_add_three_scales]
        rfl
  let a := matMulVec n DeltaA xhat i
  let b := matMulVec n L (matMulVec n DeltaU xhat) i
  let p := matMulVec n DeltaL (matMulVec n U xhat) i
  let e := matMulVec n DeltaL (matMulVec n DeltaU xhat) i
  let f := matMulVec n L DeltaY i
  let q := matMulVec n DeltaL DeltaY i
  have htri : |a + b + p + e - (f + q)| <=
      |a| + |b| + |p| + |e| + |f| + |q| := by
    have h1 := abs_add_le a b
    have h2 := abs_add_le (a + b) p
    have h3' := abs_add_le (a + b + p) e
    have h4 := abs_add_le f q
    have h5 : |a + b + p + e - (f + q)| <=
        |a + b + p + e| + |f + q| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (a + b + p + e) (-(f + q))
    linarith
  unfold ch14ext_gjeResidual1433
  change |a + b + p + e - (f + q)| <= _
  have hraw : |a + b + p + e - (f + q)| <=
      2 * g * ch14ext_gjeResidualS1 n L U xhat i +
        c * (1 + g) * ch14ext_gjeResidualS2 n L X U xhat i +
        c * (1 + g) * matMulVec n AL xy i +
        d * (1 + g) * matMulVec n AL r i := by
    dsimp [a, b, p, e, f, q] at htri
    nlinarith [htri, hA, hLDeltaU, hDeltaLU, hDeltaLDeltaU,
      hLDeltaY, hDeltaLDeltaY]
  have hcoef : 0 <= c * (1 + g) := mul_nonneg hc (by linarith)
  have hS3mul := mul_le_mul_of_nonneg_left hS3 hcoef
  calc
    |a + b + p + e - (f + q)| <= _ := hraw
    _ <= 2 * g * ch14ext_gjeResidualS1 n L U xhat i +
        c * (1 + g) * ch14ext_gjeResidualS2 n L X U xhat i +
        c * (1 + g) *
          (ch14ext_gjeResidualS2 n L X U xhat i +
            c * ch14ext_gjeResidualS22 n L X U xhat i +
            c * ch14ext_gjeResidualS23 n L X y i +
            d * matMulVec n AL (matMulVec n AX r) i) +
        d * (1 + g) * matMulVec n AL r i := by linarith
    _ = _ := by ring

/-- The scalar remainder left after the final division is absorbed into the
printed `8*n*u` coefficient in (14.31).  Every summand has at least two
roundoff factors. -/
noncomputable def ch14ext_gjeResidualFinalDivisionHigherOrder (n : Nat)
    (fp : FPModel) (L X U : Fin n -> Fin n -> Real)
    (y xhat : Fin n -> Real) (i : Fin n) : Real :=
  ch14ext_gjeResidualHigherOrder n fp L X U y xhat i +
    (ch14ext_gammaRem fp 1 + gamma fp 1 * gamma fp n +
      2 * gje_c₃ fp n * gamma fp 1 * (1 + gamma fp n)) *
      ch14ext_gjeResidualS2 n L X U xhat i +
    gje_c₃ fp n * gje_c₃ fp n * gamma fp 1 * (1 + gamma fp n) *
      ch14ext_gjeResidualS22 n L X U xhat i

/-- The extra rounded divisions consume only the five units of slack between
the exact linear coefficient `8*n-5` and Higham's printed `8*n` cap. -/
theorem ch14ext_gje_residual_coeff_budget_with_final_division
    (fp : FPModel) (n : Nat) (hn : gammaValid fp n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3) :
    2 * gamma fp n + 2 * gje_c₃ fp n + gamma fp 1 <=
      8 * (n : Real) * fp.u +
        2 * ch14ext_gammaRem fp n +
        2 * gje_c3_quadratic_remainder fp n +
        ch14ext_gammaRem fp 1 := by
  rw [ch14ext_gamma_split fp n hn, ch14ext_gamma_split fp 1 h1,
    gje_c3_eq_linear_plus_quadratic_remainder_term fp n h3]
  norm_num
  nlinarith [fp.u_nonneg]

theorem ch14ext_gjeResidualFinalDivisionHigherOrder_nonneg (n : Nat)
    (fp : FPModel) (L X U : Fin n -> Fin n -> Real)
    (y xhat : Fin n -> Real) (i : Fin n)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3) :
    0 <= ch14ext_gjeResidualFinalDivisionHigherOrder
      n fp L X U y xhat i := by
  have hg : 0 <= gamma fp n := gamma_nonneg fp hn
  have hd : 0 <= gamma fp 1 := gamma_nonneg fp h1
  have hc : 0 <= gje_c₃ fp n := gje_c3_nonneg fp n hnpos h3
  have hgr : 0 <= ch14ext_gammaRem fp n :=
    ch14ext_gammaRem_nonneg fp n hn
  have hdgr : 0 <= ch14ext_gammaRem fp 1 :=
    ch14ext_gammaRem_nonneg fp 1 h1
  have hcr : 0 <= gje_c3_quadratic_remainder fp n :=
    ch14ext_gjeC3Rem_nonneg fp n hnpos h3
  have hs2 := ch14ext_gjeResidualS2_nonneg n L X U xhat i
  have hs22 := ch14ext_gjeResidualS22_nonneg n L X U xhat i
  have hs23 := ch14ext_gjeResidualS23_nonneg n L X y i
  have hbase := ch14ext_gjeResidualHigherOrder_nonneg n fp L X U y xhat i
    hn hnpos h3
  unfold ch14ext_gjeResidualFinalDivisionHigherOrder
  apply add_nonneg
  . apply add_nonneg
    . exact hbase
    . positivity
  . positivity

/-- **Higham (14.31) for the literal executor, including its final
componentwise divisions.**  The returned vector is
`ch14ext_gjeFinalizedDivOutput`; neither a unit final matrix nor an externally
supplied final vector is assumed. -/
theorem ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31
    {n : Nat} (fp : FPModel)
    (A L_hat : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i| <=
        8 * (n : Real) * fp.u *
          ch14ext_gjeResidualS2 n L_hat
            (ch14ext_gjeFinalizedSourceXabs fp s) s.matrix
            (ch14ext_gjeFinalizedDivOutput fp s) i +
        ch14ext_gjeResidualFinalDivisionHigherOrder n fp L_hat
          (ch14ext_gjeFinalizedSourceXabs fp s) s.matrix s.rhs
          (ch14ext_gjeFinalizedDivOutput fp s) i := by
  intro i
  let X := ch14ext_gjeFinalizedSourceXabs fp s
  let Q := ch14ext_gjeFinalizedSourceQ fp s
  let D := (ch14ext_gjeBeforeFinalDivision fp s).matrix
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let r := ch14ext_gjeFinalDivisionEnvelope n Q D xhat
  let g := gamma fp n
  let c := gje_c₃ fp n
  let d := gamma fp 1
  let DeltaA1 : Fin n -> Fin n -> Real := fun a j =>
    matMul n L_hat s.matrix a j - A a j
  have hDeltaA1 : forall a j : Fin n, |DeltaA1 a j| <= g *
      Finset.univ.sum (fun k : Fin n => |L_hat a k| * |s.matrix k j|) := by
    intro a j
    simpa [g] using hLU.backward_bound a j
  have hFactor : forall a j : Fin n,
      A a j + DeltaA1 a j = matMul n L_hat s.matrix a j := by
    intro a j
    unfold DeltaA1
    ring
  obtain ⟨DeltaL, hDeltaL, hForwardRaw⟩ :=
    forwardSub_backward_error fp n L_hat b
      (fun a => by rw [hLU.L_diag a]; norm_num) hLU.L_upper_zero hn
  have hForward : forall a : Fin n,
      matMulVec n L_hat s.rhs a + matMulVec n DeltaL s.rhs a = b a := by
    intro a
    have h := hForwardRaw a
    rw [← hyStart] at h
    simpa [matMulVec, Finset.sum_add_distrib, add_mul] using h
  obtain ⟨DeltaU, DeltaY, hStageRaw, hQD, hDeltaUraw, hDeltaYraw⟩ :=
    ch14ext_gjeFinalizedSourceTrace_stage2_backward_error_14_30abc_with_final_division
      fp s hnpos h3 h1 hLU.U_lower_zero hdiagU hpiv
  have hStage : forall a : Fin n,
      matMulVec n s.matrix xhat a + matMulVec n DeltaU xhat a =
        s.rhs a + DeltaY a := by
    intro a
    have h := hStageRaw a
    simpa [xhat, matMulVec, Finset.sum_add_distrib, add_mul] using h
  have hDeltaU : forall a j : Fin n, |DeltaU a j| <= c *
      Finset.univ.sum (fun k : Fin n => |X a k| * |s.matrix k j|) := by
    intro a j
    simpa [c, X] using hDeltaUraw a j
  have hDeltaY : forall a : Fin n, |DeltaY a| <= c *
      Finset.univ.sum (fun j : Fin n => |X a j| * |s.rhs j|) + d * r a := by
    intro a
    simpa [c, d, r, X, Q, D, xhat,
      ch14ext_gjeFinalDivisionEnvelope] using hDeltaYraw a
  have hResidual := ch14ext_gje_residual_decomposition_14_33 n A L_hat
    s.matrix DeltaA1 DeltaL DeltaU b s.rhs xhat DeltaY
    hFactor hForward hStage
  have hg : 0 <= g := by simpa [g] using gamma_nonneg fp hn
  have hc : 0 <= c := by simpa [c] using gje_c3_nonneg fp n hnpos h3
  have hd : 0 <= d := by simpa [d] using gamma_nonneg fp h1
  have hr : forall a : Fin n, 0 <= r a := by
    intro a
    exact ch14ext_gjeFinalDivisionEnvelope_nonneg n Q D xhat a
  have hR := ch14ext_gjeResidual1433_bound_with_extra_rhs n L_hat
    s.matrix X DeltaA1 DeltaL DeltaU s.rhs xhat DeltaY r g c d
    hg hc hd hr hDeltaA1 hDeltaL hDeltaU hDeltaY hStage i
  have hDoff : forall a j : Fin n, a ≠ j -> D a j = 0 := by
    intro a j haj
    have hfinal := ch14ext_gjeFinalizedSourceTrace_final_diagonal
      fp s hnpos hLU.U_lower_zero
    change (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix a j = 0
    rw [hfinal]
    simp [ch14ext_gjeFinalDiagonal, haj]
  have hrBound : forall a : Fin n,
      r a <= matMulVec n (absMatrix n s.matrix) (absVec n xhat) a +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n s.matrix) (absVec n xhat)) a := by
    exact ch14ext_gjeFinalDivisionEnvelope_le_stage_objects n
      s.matrix X Q D DeltaU xhat c hc hDoff
      (by
        intro a j
        simpa [Q, D] using hQD a j)
      hDeltaU
  have hLr0 := ch14ext_matMulVec_mono_nonneg n (absMatrix n L_hat) r
    (fun a =>
      matMulVec n (absMatrix n s.matrix) (absVec n xhat) a +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n s.matrix) (absVec n xhat)) a)
    (fun a j => by simp [absMatrix]) hrBound i
  have hLr : matMulVec n (absMatrix n L_hat) r i <=
      ch14ext_gjeResidualS1 n L_hat s.matrix xhat i +
        c * ch14ext_gjeResidualS2 n L_hat X s.matrix xhat i := by
    calc
      matMulVec n (absMatrix n L_hat) r i <= _ := hLr0
      _ = _ := by
        simpa [ch14ext_gjeResidualS1, ch14ext_gjeResidualS2] using
          ch14ext_matMulVec_two_scales n (absMatrix n L_hat)
            (matMulVec n (absMatrix n s.matrix) (absVec n xhat))
            (matMulVec n (absMatrix n X)
              (matMulVec n (absMatrix n s.matrix) (absVec n xhat))) 1 c i
  have hXr0 : forall a : Fin n,
      matMulVec n (absMatrix n X) r a <=
        matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n s.matrix) (absVec n xhat)) a +
        c * matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n X)
            (matMulVec n (absMatrix n s.matrix) (absVec n xhat))) a := by
    intro a
    calc
      matMulVec n (absMatrix n X) r a <=
          matMulVec n (absMatrix n X)
            (fun j =>
              matMulVec n (absMatrix n s.matrix) (absVec n xhat) j +
                c * matMulVec n (absMatrix n X)
                  (matMulVec n (absMatrix n s.matrix) (absVec n xhat)) j) a :=
        ch14ext_matMulVec_mono_nonneg n (absMatrix n X) r _
          (fun p q => by simp [absMatrix]) hrBound a
      _ = _ := by
        simpa using ch14ext_matMulVec_two_scales n (absMatrix n X)
          (matMulVec n (absMatrix n s.matrix) (absVec n xhat))
          (matMulVec n (absMatrix n X)
            (matMulVec n (absMatrix n s.matrix) (absVec n xhat))) 1 c a
  have hLXr0 := ch14ext_matMulVec_mono_nonneg n (absMatrix n L_hat)
    (matMulVec n (absMatrix n X) r)
    (fun a =>
      matMulVec n (absMatrix n X)
        (matMulVec n (absMatrix n s.matrix) (absVec n xhat)) a +
      c * matMulVec n (absMatrix n X)
        (matMulVec n (absMatrix n X)
          (matMulVec n (absMatrix n s.matrix) (absVec n xhat))) a)
    (fun a j => by simp [absMatrix]) hXr0 i
  have hLXr : matMulVec n (absMatrix n L_hat)
      (matMulVec n (absMatrix n X) r) i <=
      ch14ext_gjeResidualS2 n L_hat X s.matrix xhat i +
        c * ch14ext_gjeResidualS22 n L_hat X s.matrix xhat i := by
    calc
      matMulVec n (absMatrix n L_hat)
          (matMulVec n (absMatrix n X) r) i <= _ := hLXr0
      _ = _ := by
        simpa [ch14ext_gjeResidualS2, ch14ext_gjeResidualS22] using
          ch14ext_matMulVec_two_scales n (absMatrix n L_hat)
            (matMulVec n (absMatrix n X)
              (matMulVec n (absMatrix n s.matrix) (absVec n xhat)))
            (matMulVec n (absMatrix n X)
              (matMulVec n (absMatrix n X)
                (matMulVec n (absMatrix n s.matrix) (absVec n xhat)))) 1 c i
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hXdiag : forall k : Fin n, 1 <= X k k := by
    intro k
    simpa [X, ch14ext_gjeFinalizedSourceXabs,
      ch14ext_gjeFinalizedSourceStages, ch14ext_gjeFinalizedSourceQ] using
      ch14ext_gjeXabs_diag_ge_one n (ch14ext_gjeFinalizedSourceStages fp s)
        (ch14ext_gjeFinalizedSourceQ fp s) 1 (n - 1) hidx
        (by
          simpa [ch14ext_gjeFinalizedSourceQ,
            ch14ext_gjeFinalizedSourceStages] using
            ch14ext_gjeConstructedQ_isLeftInverse n
              (ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s) 1 hidx)
        k
  have hS12 := ch14ext_gjeResidualS1_le_S2 n L_hat X s.matrix xhat i hXdiag
  have hS2nn := ch14ext_gjeResidualS2_nonneg n L_hat X s.matrix xhat i
  have hCoeff := ch14ext_gje_residual_coeff_budget_with_final_division
    fp n hn h1 h3
  have hCoeffS2 := mul_le_mul_of_nonneg_right hCoeff hS2nn
  have hCoeffS2' :
      (2 * g + 2 * c + d) *
          ch14ext_gjeResidualS2 n L_hat X s.matrix xhat i <=
        (8 * (n : Real) * fp.u +
          2 * ch14ext_gammaRem fp n +
          2 * gje_c3_quadratic_remainder fp n +
          ch14ext_gammaRem fp 1) *
            ch14ext_gjeResidualS2 n L_hat X s.matrix xhat i := by
    simpa [g, c, d] using hCoeffS2
  have hOnePlusG : 0 <= 1 + g := by linarith [hg]
  have hLrScaled := mul_le_mul_of_nonneg_left hLr
    (mul_nonneg hd hOnePlusG)
  have hLXrScaled := mul_le_mul_of_nonneg_left hLXr
    (mul_nonneg (mul_nonneg hc hd) hOnePlusG)
  have hS1Scaled := mul_le_mul_of_nonneg_left hS12
    (by nlinarith [hg, hd] : 0 <= 2 * g + d * (1 + g))
  have hresEq : b i - matMulVec n A xhat i =
      ch14ext_gjeResidual1433 n L_hat s.matrix DeltaA1 DeltaL DeltaU
        xhat DeltaY i := by
    linarith [hResidual i]
  rw [hresEq]
  have hFinal :
      |ch14ext_gjeResidual1433 n L_hat s.matrix DeltaA1 DeltaL DeltaU
          xhat DeltaY i| <=
        8 * (n : Real) * fp.u *
            ch14ext_gjeResidualS2 n L_hat X s.matrix xhat i +
          ch14ext_gjeResidualFinalDivisionHigherOrder n fp L_hat X
            s.matrix s.rhs xhat i := by
    unfold ch14ext_gjeResidualFinalDivisionHigherOrder
      ch14ext_gjeResidualHigherOrder
    nlinarith [hR, hLrScaled, hLXrScaled, hS1Scaled, hCoeffS2']
  simpa [X, xhat] using hFinal

/-- Exact inverse of a nonzero diagonal work matrix. -/
noncomputable def ch14ext_gjeDiagonalInv (n : Nat)
    (D : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => if i = j then (D i i)⁻¹ else 0

/-- The normalized absolute stage product `|D⁻¹| |P|`.  This is the
general-diagonal replacement for the unit-diagonal stage envelope in (14.29). -/
noncomputable def ch14ext_gjeNormalizedPabs (n : Nat)
    (D Pabs : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  matMul n (absMatrix n (ch14ext_gjeDiagonalInv n D)) Pabs

theorem ch14ext_gjeDiagonalInv_mul_diagonal (n : Nat)
    (D : Fin n -> Fin n -> Real)
    (hdiag : forall i : Fin n, D i i ≠ 0)
    (hoff : forall i j : Fin n, i ≠ j -> D i j = 0) :
    matMul n (ch14ext_gjeDiagonalInv n D) D = idMatrix n := by
  funext i j
  unfold matMul ch14ext_gjeDiagonalInv idMatrix
  rw [Finset.sum_eq_single i]
  . by_cases hij : i = j
    . subst j
      simp [hdiag i]
    . simp [hij, hoff i j hij]
  . intro k _ hki
    rw [if_neg (Ne.symm hki), zero_mul]
  . simp

theorem ch14ext_gjeDiagonalInv_delta_action (n : Nat)
    (D DeltaD : Fin n -> Fin n -> Real) (x : Fin n -> Real) (d : Real)
    (hd : 0 <= d) (hdiag : forall i : Fin n, D i i ≠ 0)
    (hDoff : forall i j : Fin n, i ≠ j -> D i j = 0)
    (hDeltaOff : forall i j : Fin n, i ≠ j -> DeltaD i j = 0)
    (hDelta : forall i j : Fin n, |DeltaD i j| <= d * |D i j|) :
    forall i : Fin n,
      |matMulVec n (ch14ext_gjeDiagonalInv n D)
          (matMulVec n DeltaD x) i| <= d * |x i| := by
  intro i
  have hDeltaCollapse : matMulVec n DeltaD x i = DeltaD i i * x i := by
    unfold matMulVec
    rw [Finset.sum_eq_single i]
    . intro j _ hji
      rw [hDeltaOff i j (Ne.symm hji), zero_mul]
    . simp
  have hInvCollapse : matMulVec n (ch14ext_gjeDiagonalInv n D)
      (matMulVec n DeltaD x) i =
      (D i i)⁻¹ * (DeltaD i i * x i) := by
    change (Finset.univ.sum (fun j : Fin n =>
      (if i = j then (D i i)⁻¹ else 0) * matMulVec n DeltaD x j)) = _
    rw [Finset.sum_eq_single i]
    . rw [if_pos rfl, hDeltaCollapse]
    . intro j _ hji
      rw [if_neg (Ne.symm hji), zero_mul]
    . simp
  rw [hInvCollapse, abs_mul, abs_mul]
  have hDabs : 0 < |D i i| := abs_pos.mpr (hdiag i)
  have hInvAbs : |(D i i)⁻¹| = (|D i i|)⁻¹ := abs_inv _
  rw [hInvAbs]
  calc
    (|D i i|)⁻¹ * (|DeltaD i i| * |x i|) <=
        (|D i i|)⁻¹ * ((d * |D i i|) * |x i|) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hDelta i i) (abs_nonneg _))
        (inv_nonneg.mpr (le_of_lt hDabs))
    _ = d * |x i| := by
      field_simp

theorem ch14ext_gjeNormalizedPabs_nonneg (n : Nat)
    (D Pabs : Fin n -> Fin n -> Real)
    (hP : forall i j : Fin n, 0 <= Pabs i j) :
    forall i j : Fin n, 0 <= ch14ext_gjeNormalizedPabs n D Pabs i j := by
  intro i j
  unfold ch14ext_gjeNormalizedPabs matMul absMatrix
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (hP k j))

/-- Self-substitution form of the general-diagonal (14.29).  The final
division contributes `d*|xhat|` and the interaction `2*c*d*T2`; both are kept
explicit. -/
theorem ch14ext_gje_stage2_forward_split_with_final_division (n : Nat)
    (U X : Fin n -> Fin n -> Real) (z y xhat : Fin n -> Real)
    (c d : Real) (hc : 0 <= c) (hd : 0 <= d)
    (hX : forall i j : Fin n, 0 <= X i j)
    (hUz : forall i : Fin n, matMulVec n U z i = y i)
    (hErr : forall i : Fin n, |z i - xhat i| <=
      c * ch14ext_gjeForwardRaw n X U z y i + d * |xhat i|) :
    forall i : Fin n, |z i - xhat i| <=
      2 * c * ch14ext_gjeForwardT2 n X U xhat i +
      2 * c * c * ch14ext_gjeForwardQ2 n X U z y i +
      2 * c * d * ch14ext_gjeForwardT2 n X U xhat i +
      d * |xhat i| := by
  intro i
  let AU := absMatrix n U
  let ev : Fin n -> Real := fun j => |z j - xhat j|
  let uz := matMulVec n AU (absVec n z)
  let ux := matMulVec n AU (absVec n xhat)
  let ue := matMulVec n AU ev
  let F : Fin n -> Real := fun j => ch14ext_gjeForwardRaw n X U z y j
  have hy : forall j : Fin n, |y j| <= uz j := by
    intro j
    rw [← hUz j]
    simpa [uz, AU, matMulVec, absMatrix, absVec] using abs_matMulVec_le n U z j
  have hXy : matMulVec n X (absVec n y) i <= matMulVec n X uz i :=
    ch14ext_matMulVec_mono_nonneg n X (absVec n y) uz hX
      (fun j => by simpa [absVec] using hy j) i
  have hF : F i <= 2 * matMulVec n X uz i := by
    unfold F ch14ext_gjeForwardRaw
    nlinarith
  have hz : forall j : Fin n, |z j| <= |xhat j| + ev j := by
    intro j
    have h := abs_add_le (xhat j) (z j - xhat j)
    have heq : z j = xhat j + (z j - xhat j) := by ring
    rw [heq]
    simpa [ev] using h
  have hUzX : forall j : Fin n, uz j <= ux j + ue j := by
    intro j
    have h := ch14ext_matMulVec_mono_nonneg n AU (absVec n z)
      (fun k => |xhat k| + ev k) (fun a b => by simp [AU, absMatrix])
      (fun k => by simpa [absVec] using hz k) j
    have hadd : matMulVec n AU (fun k => |xhat k| + ev k) j =
        ux j + ue j := by
      simpa [ux, ue, absVec] using
        congrFun (matMulVec_add_right n AU (absVec n xhat) ev) j
    rw [hadd] at h
    exact h
  have hXUz : matMulVec n X uz i <=
      ch14ext_gjeForwardT2 n X U xhat i + matMulVec n X ue i := by
    have h := ch14ext_matMulVec_mono_nonneg n X uz (fun j => ux j + ue j)
      hX hUzX i
    have hadd : matMulVec n X (fun j => ux j + ue j) i =
        matMulVec n X ux i + matMulVec n X ue i := by
      simpa using congrFun (matMulVec_add_right n X ux ue) i
    rw [hadd] at h
    simpa [ch14ext_gjeForwardT2, ux, AU] using h
  have heF : forall j : Fin n, ev j <= c * F j + d * |xhat j| := by
    intro j
    simpa [ev, F] using hErr j
  have hUe : forall j : Fin n, ue j <=
      c * matMulVec n AU F j + d * ux j := by
    intro j
    have h := ch14ext_matMulVec_mono_nonneg n AU ev
      (fun k => c * F k + d * |xhat k|)
      (fun a b => by simp [AU, absMatrix]) heF j
    calc
      ue j <= matMulVec n AU (fun k => c * F k + d * |xhat k|) j := by
        simpa [ue] using h
      _ = c * matMulVec n AU F j + d * ux j := by
        simpa [ux, absVec] using
          ch14ext_matMulVec_two_scales n AU F (absVec n xhat) c d j
  have hXUe0 := ch14ext_matMulVec_mono_nonneg n X ue
    (fun j => c * matMulVec n AU F j + d * ux j) hX hUe i
  have hXUe : matMulVec n X ue i <=
      c * ch14ext_gjeForwardQ2 n X U z y i +
        d * ch14ext_gjeForwardT2 n X U xhat i := by
    calc
      matMulVec n X ue i <=
          matMulVec n X (fun j =>
            c * matMulVec n AU F j + d * ux j) i := hXUe0
      _ = _ := by
        simpa [ch14ext_gjeForwardQ2, ch14ext_gjeForwardT2,
          F, ux, AU] using
          ch14ext_matMulVec_two_scales n X (matMulVec n AU F) ux c d i
  have hFi := mul_le_mul_of_nonneg_left hF hc
  have hXUzi : 2 * c * matMulVec n X uz i <=
      2 * c * (ch14ext_gjeForwardT2 n X U xhat i + matMulVec n X ue i) :=
    mul_le_mul_of_nonneg_left hXUz (mul_nonneg (by norm_num) hc)
  have hXUei : 2 * c * matMulVec n X ue i <=
      2 * c * (c * ch14ext_gjeForwardQ2 n X U z y i +
        d * ch14ext_gjeForwardT2 n X U xhat i) :=
    mul_le_mul_of_nonneg_left hXUe (mul_nonneg (by norm_num) hc)
  have hEi := hErr i
  change ev i <= _
  change ev i <= c * F i + d * |xhat i| at hEi
  nlinarith

/-- The row-normalized stage envelope is the general-diagonal analogue of
the unit-final `Pabs`: it differs from `|U⁻¹|` only by the same accumulated
`c₃` correction used in the printed (14.32) endpoint. -/
theorem ch14ext_gjeFinalizedNormalizedPabs_le_abs_Uinv_add {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (U_inv : Fin n -> Fin n -> Real)
    (hn : 1 <= n) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0)
    (hUinv : IsRightInverse n s.matrix U_inv) :
    forall i j : Fin n,
      ch14ext_gjeNormalizedPabs n
          (ch14ext_gjeBeforeFinalDivision fp s).matrix
          (ch14ext_gjeFinalizedSourcePabs fp s) i j <=
        |U_inv i j| + gje_c₃ fp n *
          matMul n
            (matMul n
              (ch14ext_gjeNormalizedPabs n
                (ch14ext_gjeBeforeFinalDivision fp s).matrix
                (ch14ext_gjeFinalizedSourcePabs fp s))
              (absMatrix n s.matrix))
            (absMatrix n U_inv) i j := by
  let V := ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s
  let Nhat := ch14ext_gjeFinalizedSourceStages fp s
  let P := gje_cumulative_product n Nhat 1 (1 + (n - 1))
  let Pabs := ch14ext_gjeFinalizedSourcePabs fp s
  let D := (ch14ext_gjeBeforeFinalDivision fp s).matrix
  let R := ch14ext_gjeDiagonalInv n D
  let S := matMul n R P
  let X := ch14ext_gjeNormalizedPabs n D Pabs
  let E : Fin n -> Fin n -> Real := fun a j =>
    D a j - matMul n P s.matrix a j
  have hidx : forall t : Nat, t < n - 1 -> 1 + t < n := by omega
  have hpiv' : forall t : Nat, (ht : t < n - 1) ->
      V (1 + t) ⟨1 + t, hidx t ht⟩ ⟨1 + t, hidx t ht⟩ ≠ 0 := by
    intro t ht
    simpa [V] using hpiv t ht
  have hrec :=
    ch14ext_gjeFinalizedSourceTrace_recurrence_bounds_14_25b_14_26
      fp s hidx hUpper hpiv' h3
  have hsum : 1 + (n - 1) = n := by omega
  have hE : forall a j : Fin n, |E a j| <= gje_c₃ fp n *
      matMul n Pabs (absMatrix n s.matrix) a j := by
    intro a j
    have h := ch14ext_matrixAccumulation_c3 n fp Nhat V 1 hn h3 hidx hrec.1 a j
    simpa [E, D, P, Pabs, Nhat, V, ch14ext_gjeBeforeFinalDivision,
      ch14ext_boundObj, ch14ext_gjeFinalizedSourcePabs,
      ch14ext_gjeFinalizedSourceStages, hsum] using h
  have hDdiag : forall a : Fin n, D a a ≠ 0 := by
    intro a
    exact ch14ext_gjeBeforeFinalDivision_diag_ne_zero fp s hdiag a
  have hDoff : forall a j : Fin n, a ≠ j -> D a j = 0 := by
    intro a j haj
    have hf := ch14ext_gjeFinalizedSourceTrace_final_diagonal fp s hn hUpper
    change (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix a j = 0
    rw [hf]
    simp [ch14ext_gjeFinalDiagonal, haj]
  have hRD : matMul n R D = idMatrix n :=
    ch14ext_gjeDiagonalInv_mul_diagonal n D hDdiag hDoff
  have hUpperSeq : forall t : Nat, t <= n - 1 ->
      forall a j : Fin n, j.val < a.val -> V (1 + t) a j = 0 := by
    intro t _ht a j hja
    simpa [V, ch14ext_gjeFinalizedSourceTraceMatrix] using
      ch14ext_gjeFinalizedSourceTrace_upper fp 1 s hUpper t a j hja
  have hPabsEq : forall a j : Fin n, Pabs a j = |P a j| := by
    intro a j
    simpa [Pabs, P, Nhat, ch14ext_gjeFinalizedSourcePabs,
      ch14ext_gjeFinalizedSourceStages] using
      ch14ext_gje_absCumProd_eq_abs_signed n V 1 (n - 1)
        hidx hUpperSeq a j
  have hRrow : forall a k : Fin n, k ≠ a -> R a k = 0 := by
    intro a k hka
    simp [R, ch14ext_gjeDiagonalInv, Ne.symm hka]
  have hAbsRrow : forall a k : Fin n, k ≠ a -> absMatrix n R a k = 0 := by
    intro a k hka
    simp [absMatrix, hRrow a k hka]
  have hRP : forall a j : Fin n, S a j = R a a * P a j := by
    intro a j
    unfold S matMul
    rw [Finset.sum_eq_single a]
    . intro k _ hka
      rw [hRrow a k hka, zero_mul]
    . simp
  have hXP : forall a j : Fin n, X a j = |R a a| * Pabs a j := by
    intro a j
    unfold X ch14ext_gjeNormalizedPabs matMul
    rw [Finset.sum_eq_single a]
    . simp [absMatrix, R]
    . intro k _ hka
      rw [hAbsRrow a k hka, zero_mul]
    . simp
  have hXabs : forall a j : Fin n, X a j = |S a j| := by
    intro a j
    rw [hXP, hRP, hPabsEq, abs_mul]
  have hSE : matMul n R E = fun a j =>
      idMatrix n a j - matMul n S s.matrix a j := by
    funext a j
    have hExpand : matMul n R E a j =
        matMul n R D a j - matMul n R (matMul n P s.matrix) a j := by
      unfold matMul E
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun k _ => by
        simp only [matMul]
        ring)
    rw [hExpand, hRD]
    unfold S
    rw [← matMul_assoc]
  have hResidual : forall a j : Fin n,
      |idMatrix n a j - matMul n S s.matrix a j| <=
        gje_c₃ fp n * matMul n X (absMatrix n s.matrix) a j := by
    intro a j
    have hse := congrFun (congrFun hSE a) j
    rw [← hse]
    have hRE : matMul n R E a j = R a a * E a j := by
      unfold matMul
      rw [Finset.sum_eq_single a]
      . intro k _ hka
        rw [hRrow a k hka, zero_mul]
      . simp
    have hXU : matMul n X (absMatrix n s.matrix) a j =
        |R a a| * matMul n Pabs (absMatrix n s.matrix) a j := by
      unfold matMul
      simp_rw [hXP]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [hRE, abs_mul, hXU]
    calc
      |R a a| * |E a j| <=
          |R a a| * (gje_c₃ fp n *
            matMul n Pabs (absMatrix n s.matrix) a j) :=
        mul_le_mul_of_nonneg_left (hE a j) (abs_nonneg _)
      _ = gje_c₃ fp n *
          (|R a a| * matMul n Pabs (absMatrix n s.matrix) a j) := by ring
  intro i j
  simpa [X, S, D, Pabs] using
    ch14ext_abs_signed_le_abs_rightInverse_add n S X s.matrix U_inv
      (gje_c₃ fp n) hXabs hUinv hResidual i j

/-- First-stage action of the already first-order stage-two error. -/
noncomputable def ch14ext_gjeForwardFirstStageErrorAction (n : Nat)
    (A_inv L U : Fin n -> Fin n -> Real)
    (z xhat : Fin n -> Real) (i : Fin n) : Real :=
  matMulVec n (absMatrix n A_inv)
    (matMulVec n (absMatrix n L)
      (matMulVec n (absMatrix n U)
        (fun j => |z j - xhat j|))) i

/-- The first-stage portion of (14.32), leaving its product with the
stage-two error explicit.  In a vanishing-roundoff family that product is
quadratic, while the pointwise leading object stays exactly Higham's `T1`. -/
theorem ch14ext_gje_first_stage_forward_split_with_error (n : Nat)
    (A A_inv L U DeltaA DeltaL : Fin n -> Fin n -> Real)
    (b x z y xhat : Fin n -> Real) (g : Real) (hg : 0 <= g)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hFactor : forall i j : Fin n,
      A i j + DeltaA i j = matMul n L U i j)
    (hForward : forall i : Fin n,
      matMulVec n L y i + matMulVec n DeltaL y i = b i)
    (hUz : forall i : Fin n, matMulVec n U z i = y i)
    (hDeltaA : forall i j : Fin n, |DeltaA i j| <= g *
      Finset.univ.sum (fun k : Fin n => |L i k| * |U k j|))
    (hDeltaL : forall i j : Fin n, |DeltaL i j| <= g * |L i j|) :
    forall i : Fin n, |x i - z i| <=
      2 * g * ch14ext_gjeForwardT1 n A_inv L U xhat i +
        2 * g * ch14ext_gjeForwardFirstStageErrorAction
          n A_inv L U z xhat i := by
  intro i
  let AA := absMatrix n A_inv
  let AL := absMatrix n L
  let AU := absMatrix n U
  let ev : Fin n -> Real := fun j => |z j - xhat j|
  let uz := matMulVec n AU (absVec n z)
  let ux := matMulVec n AU (absVec n xhat)
  let ue := matMulVec n AU ev
  let luz := matMulVec n AL uz
  let r : Fin n -> Real := fun j =>
    matMulVec n DeltaA z j + matMulVec n DeltaL y j
  have hFactorZ : forall a : Fin n,
      matMulVec n A z a + matMulVec n DeltaA z a =
        matMulVec n L (matMulVec n U z) a := by
    intro a
    calc
      matMulVec n A z a + matMulVec n DeltaA z a =
          Finset.univ.sum (fun j : Fin n => (A a j + DeltaA a j) * z j) := by
        unfold matMulVec
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = matMulVec n (matMul n L U) z a := by
        unfold matMulVec
        exact Finset.sum_congr rfl (fun j _ => by rw [hFactor a j])
      _ = matMulVec n L (matMulVec n U z) a := by rw [matMulVec_matMul]
  have hAdiff : forall a : Fin n,
      matMulVec n A (fun j => x j - z j) a = r a := by
    intro a
    have hlin : matMulVec n A (fun j => x j - z j) a =
        matMulVec n A x a - matMulVec n A z a := by
      unfold matMulVec
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    have hUzFn : matMulVec n U z = y := by
      funext j
      exact hUz j
    unfold r
    rw [hlin]
    have hLUzy : matMulVec n L (matMulVec n U z) a = matMulVec n L y a := by
      rw [hUzFn]
    linarith [hExact a, hFactorZ a, hLUzy, hForward a]
  have hAinvMat : matMul n A_inv A = idMatrix n := by
    funext a j
    exact hAinv a j
  have hAdiffFn : matMulVec n A (fun j => x j - z j) = r := by
    funext a
    exact hAdiff a
  have hDiff : x i - z i = matMulVec n A_inv r i := by
    have hleft : matMulVec n A_inv
        (matMulVec n A (fun j => x j - z j)) i = x i - z i := by
      rw [← matMulVec_matMul, hAinvMat, matMulVec_id]
    calc
      x i - z i = matMulVec n A_inv
          (matMulVec n A (fun j => x j - z j)) i := hleft.symm
      _ = matMulVec n A_inv r i := by rw [hAdiffFn]
  have hDeltaA' : forall a j : Fin n, |DeltaA a j| <=
      g * matMul n AL AU a j := by
    intro a j
    simpa [AL, AU, matMul, absMatrix] using hDeltaA a j
  have hDeltaAz : forall a : Fin n,
      |matMulVec n DeltaA z a| <= g * luz a := by
    intro a
    have h := ch14ext_abs_matMulVec_le_scaled n DeltaA (matMul n AL AU)
      z g hDeltaA' a
    rw [matMulVec_matMul] at h
    simpa [luz, uz, AL, AU] using h
  have hy : forall a : Fin n, |y a| <= uz a := by
    intro a
    rw [← hUz a]
    simpa [uz, AU, matMulVec, absMatrix, absVec] using abs_matMulVec_le n U z a
  have hDeltaL' : forall a j : Fin n, |DeltaL a j| <= g * AL a j := by
    intro a j
    simpa [AL, absMatrix] using hDeltaL a j
  have hDeltaLy0 : forall a : Fin n,
      |matMulVec n DeltaL y a| <= g * matMulVec n AL (absVec n y) a := by
    intro a
    exact ch14ext_abs_matMulVec_le_scaled n DeltaL AL y g hDeltaL' a
  have hLy : forall a : Fin n, matMulVec n AL (absVec n y) a <= luz a := by
    intro a
    exact ch14ext_matMulVec_mono_nonneg n AL (absVec n y) uz
      (fun p q => by simp [AL, absMatrix])
      (fun j => by simpa [absVec] using hy j) a
  have hDeltaLy : forall a : Fin n, |matMulVec n DeltaL y a| <= g * luz a := by
    intro a
    exact le_trans (hDeltaLy0 a) (mul_le_mul_of_nonneg_left (hLy a) hg)
  have hr : forall a : Fin n, |r a| <= 2 * g * luz a := by
    intro a
    unfold r
    have ht := abs_add_le (matMulVec n DeltaA z a) (matMulVec n DeltaL y a)
    nlinarith [hDeltaAz a, hDeltaLy a]
  have hOuter := ch14ext_abs_matMulVec_le_of_vec_bound n A_inv r
    (fun a => 2 * g * luz a) hr i
  have hBase : |x i - z i| <= 2 * g * matMulVec n AA luz i := by
    rw [hDiff]
    calc
      |matMulVec n A_inv r i| <=
          matMulVec n AA (fun a => 2 * g * luz a) i := by
        simpa [AA] using hOuter
      _ = 2 * g * matMulVec n AA luz i := by rw [ch14ext_matMulVec_scale]
  have hz : forall j : Fin n, |z j| <= |xhat j| + ev j := by
    intro j
    have h := abs_add_le (xhat j) (z j - xhat j)
    have heq : z j = xhat j + (z j - xhat j) := by ring
    rw [heq]
    simpa [ev] using h
  have hU : forall a : Fin n, uz a <= ux a + ue a := by
    intro a
    have h := ch14ext_matMulVec_mono_nonneg n AU (absVec n z)
      (fun j => |xhat j| + ev j) (fun p q => by simp [AU, absMatrix])
      (fun j => by simpa [absVec] using hz j) a
    have hadd : matMulVec n AU (fun j => |xhat j| + ev j) a = ux a + ue a := by
      simpa [ux, ue, absVec] using
        congrFun (matMulVec_add_right n AU (absVec n xhat) ev) a
    rw [hadd] at h
    exact h
  let lux := matMulVec n AL ux
  let lue := matMulVec n AL ue
  have hL : forall a : Fin n, luz a <= lux a + lue a := by
    intro a
    have h := ch14ext_matMulVec_mono_nonneg n AL uz (fun j => ux j + ue j)
      (fun p q => by simp [AL, absMatrix]) hU a
    have hadd : matMulVec n AL (fun j => ux j + ue j) a = lux a + lue a := by
      simpa [lux, lue] using congrFun (matMulVec_add_right n AL ux ue) a
    rw [hadd] at h
    exact h
  have hA : matMulVec n AA luz i <=
      matMulVec n AA lux i + matMulVec n AA lue i := by
    have h := ch14ext_matMulVec_mono_nonneg n AA luz (fun j => lux j + lue j)
      (fun p q => by simp [AA, absMatrix]) hL i
    have hadd : matMulVec n AA (fun j => lux j + lue j) i =
        matMulVec n AA lux i + matMulVec n AA lue i := by
      simpa using congrFun (matMulVec_add_right n AA lux lue) i
    rw [hadd] at h
    exact h
  have hScaled : 2 * g * matMulVec n AA luz i <=
      2 * g * (matMulVec n AA lux i + matMulVec n AA lue i) :=
    mul_le_mul_of_nonneg_left hA (mul_nonneg (by norm_num) hg)
  have hT1 : matMulVec n AA lux i =
      ch14ext_gjeForwardT1 n A_inv L U xhat i := rfl
  have hErrAction : matMulVec n AA lue i =
      ch14ext_gjeForwardFirstStageErrorAction n A_inv L U z xhat i := rfl
  rw [hT1, hErrAction] at hScaled
  linarith

theorem ch14ext_absVec_le_inverse_product (n : Nat)
    (U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hUinv : IsRightInverse n U U_inv) :
    forall i : Fin n, |x i| <=
      ch14ext_gjeForwardT2 n (absMatrix n U_inv) U x i := by
  have hLeft : IsLeftInverse n U U_inv :=
    isLeftInverse_of_isRightInverse U U_inv hUinv
  have hMat : matMul n U_inv U = idMatrix n := by
    funext a j
    exact hLeft a j
  have hAct : matMulVec n U_inv (matMulVec n U x) = x := by
    funext a
    rw [← matMulVec_matMul, hMat, matMulVec_id]
  intro i
  have hOuter := abs_matMulVec_le n U_inv (matMulVec n U x) i
  have hInner : forall a : Fin n, |matMulVec n U x a| <=
      matMulVec n (absMatrix n U) (absVec n x) a := by
    intro a
    simpa [matMulVec, absMatrix, absVec] using abs_matMulVec_le n U x a
  have hMono := ch14ext_matMulVec_mono_nonneg n (absMatrix n U_inv)
    (absVec n (matMulVec n U x))
    (matMulVec n (absMatrix n U) (absVec n x))
    (fun a j => by simp [absMatrix])
    (fun a => by simpa [absVec] using hInner a) i
  rw [congrFun hAct i] at hOuter
  exact le_trans hOuter (by
    simpa [ch14ext_gjeForwardT2] using hMono)

theorem ch14ext_gje_forward_second_coeff_with_final_division
    (fp : FPModel) (n : Nat) (h1 : gammaValid fp 1)
    (h3 : gammaValid fp 3) :
    2 * gje_c₃ fp n + gamma fp 1 <=
      6 * (n : Real) * fp.u +
        2 * gje_c3_quadratic_remainder fp n +
        ch14ext_gammaRem fp 1 := by
  rw [gje_c3_eq_linear_plus_quadratic_remainder_term fp n h3,
    ch14ext_gamma_split fp 1 h1]
  norm_num
  nlinarith [fp.u_nonneg]

/-- Explicit higher-order remainder for the literal final-division version
of (14.32). -/
noncomputable def ch14ext_gjeForwardFinalDivisionHigherOrder (n : Nat)
    (fp : FPModel)
    (A_inv L U X U_inv : Fin n -> Fin n -> Real)
    (z y xhat : Fin n -> Real) (i : Fin n) : Real :=
  2 * ch14ext_gammaRem fp n *
      ch14ext_gjeForwardT1 n A_inv L U xhat i +
    (2 * gje_c3_quadratic_remainder fp n + ch14ext_gammaRem fp 1) *
      ch14ext_gjeForwardT2 n (absMatrix n U_inv) U xhat i +
    2 * gamma fp n *
      ch14ext_gjeForwardFirstStageErrorAction n A_inv L U z xhat i +
    2 * gje_c₃ fp n * gje_c₃ fp n *
      ch14ext_gjeForwardQ2 n X U z y i +
    2 * gje_c₃ fp n * gamma fp 1 *
      ch14ext_gjeForwardT2 n X U xhat i +
    2 * gje_c₃ fp n * gje_c₃ fp n *
      ch14ext_gjeForwardUinvCorrection n X U U_inv xhat i

/-- Explicit correction that identifies the literal general-diagonal
`Xabs` in (14.31) with Higham's printed `|U||U⁻¹|` envelope. -/
noncomputable def ch14ext_gjeFinalizedResidualEnvelopeCorrection (n : Nat)
    (U X Z U_inv : Fin n -> Fin n -> Real) (c : Real) :
    Fin n -> Fin n -> Real :=
  fun i j =>
    matMul n (matMul n (matMul n (absMatrix n U) Z)
      (absMatrix n U)) (absMatrix n U_inv) i j +
    matMul n (matMul n X (absMatrix n U)) (absMatrix n U_inv) i j +
    c * matMul n
      (matMul n (matMul n (matMul n X (absMatrix n U)) Z)
        (absMatrix n U)) (absMatrix n U_inv) i j

/-- General-diagonal residual-envelope bridge required by Theorem 14.5 and
Corollaries 14.6--14.7. -/
theorem ch14ext_gjeFinalizedSourceXabs_le_printed_add_correction {n : Nat}
    (fp : FPModel) (s : Ch14GJEState n)
    (U_inv : Fin n -> Fin n -> Real)
    (hn : 1 <= n) (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0)
    (hUinv : IsRightInverse n s.matrix U_inv) :
    forall i j : Fin n,
      ch14ext_gjeFinalizedSourceXabs fp s i j <=
        matMul n (absMatrix n s.matrix) (absMatrix n U_inv) i j +
        gje_c₃ fp n * ch14ext_gjeFinalizedResidualEnvelopeCorrection n
          s.matrix (ch14ext_gjeFinalizedSourceXabs fp s)
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          U_inv (gje_c₃ fp n) i j := by
  let U := s.matrix
  let X := ch14ext_gjeFinalizedSourceXabs fp s
  let Q := ch14ext_gjeFinalizedSourceQ fp s
  let D := (ch14ext_gjeBeforeFinalDivision fp s).matrix
  let Pabs := ch14ext_gjeFinalizedSourcePabs fp s
  let Z := ch14ext_gjeNormalizedPabs n D Pabs
  let Aabs := absMatrix n U
  let B := absMatrix n U_inv
  let c := gje_c₃ fp n
  obtain ⟨DeltaU, _DeltaY, _hStage, hQD, hDeltaU0, _hDeltaY⟩ :=
    ch14ext_gjeFinalizedSourceTrace_stage2_backward_error_14_30abc_with_final_division
      fp s hn h3 h1 hUpper hdiag hpiv
  have hc : 0 <= c := by simpa [c] using gje_c3_nonneg fp n hn h3
  have hDdiag : forall k : Fin n, D k k ≠ 0 := by
    intro k
    exact ch14ext_gjeBeforeFinalDivision_diag_ne_zero fp s hdiag k
  have hDoff : forall k l : Fin n, k ≠ l -> D k l = 0 := by
    intro k l hkl
    have hf := ch14ext_gjeFinalizedSourceTrace_final_diagonal fp s hn hUpper
    change (ch14ext_gjeFinalizedSourceTrace fp 1 s (n - 1)).matrix k l = 0
    rw [hf]
    simp [ch14ext_gjeFinalDiagonal, hkl]
  have hPnonneg : forall k l : Fin n, 0 <= Pabs k l := by
    intro k l
    exact gje_cumulative_product_abs_nonneg n
      (ch14ext_gjeFinalizedSourceStages fp s) 1 (1 + (n - 1)) k l
  have hZnonneg : forall k l : Fin n, 0 <= Z k l :=
    ch14ext_gjeNormalizedPabs_nonneg n D Pabs hPnonneg
  have hXnonneg : forall k l : Fin n, 0 <= X k l := by
    intro k l
    exact ch14ext_gjeXabs_nonneg n (ch14ext_gjeFinalizedSourceStages fp s)
      Q 1 (n - 1) k l
  have hZA : forall k l : Fin n,
      0 <= matMul n Z Aabs k l := by
    intro k l
    exact Finset.sum_nonneg (fun q _ =>
      mul_nonneg (hZnonneg k q) (abs_nonneg _))
  have hXA : forall k l : Fin n,
      0 <= matMul n X Aabs k l := by
    intro k l
    exact Finset.sum_nonneg (fun q _ =>
      mul_nonneg (hXnonneg k q) (abs_nonneg _))
  have hQDentry : forall i k : Fin n,
      matMul n Q D i k = Q i k * D k k := by
    intro i k
    unfold matMul
    rw [Finset.sum_eq_single k]
    . intro l _ hlk
      rw [hDoff l k hlk, mul_zero]
    . simp
  have hZentry : forall k j : Fin n,
      Z k j = |(D k k)⁻¹| * Pabs k j := by
    intro k j
    unfold Z ch14ext_gjeNormalizedPabs matMul
    rw [Finset.sum_eq_single k]
    . simp [absMatrix, ch14ext_gjeDiagonalInv]
    . intro l _ hlk
      have hkl : k ≠ l := Ne.symm hlk
      simp [absMatrix, ch14ext_gjeDiagonalInv, hkl]
    . simp
  have hXfactor : forall i j : Fin n,
      X i j = Finset.univ.sum (fun k : Fin n =>
        |matMul n Q D i k| * Z k j) := by
    intro i j
    unfold X ch14ext_gjeFinalizedSourceXabs ch14ext_gjeXabs matMul
    apply Finset.sum_congr rfl
    intro k _
    change |Q i k| * Pabs k j = |matMul n Q D i k| * Z k j
    rw [hQDentry, hZentry, abs_mul]
    have hk : |D k k| ≠ 0 := abs_ne_zero.mpr (hDdiag k)
    rw [abs_inv]
    field_simp
  have hDeltaU : forall i j : Fin n, |DeltaU i j| <=
      c * matMul n X Aabs i j := by
    intro i j
    calc
      |DeltaU i j| <= c * Finset.univ.sum (fun k : Fin n =>
          |X i k| * |U k j|) := by
        simpa [c, X, U] using hDeltaU0 i j
      _ = c * matMul n X Aabs i j := by
        congr 1
        unfold matMul Aabs absMatrix
        apply Finset.sum_congr rfl
        intro k _
        rw [abs_of_nonneg (hXnonneg i k)]
  have hQDabs : forall i k : Fin n,
      |matMul n Q D i k| <= Aabs i k + c * matMul n X Aabs i k := by
    intro i k
    rw [← hQD i k]
    calc
      |U i k + DeltaU i k| <= |U i k| + |DeltaU i k| := abs_add_le _ _
      _ <= |U i k| + c * matMul n X Aabs i k :=
        by nlinarith [hDeltaU i k]
      _ = _ := by rfl
  have hFirst : forall i j : Fin n,
      X i j <= matMul n Aabs Z i j +
        c * matMul n (matMul n X Aabs) Z i j := by
    intro i j
    rw [hXfactor]
    calc
      Finset.univ.sum (fun k : Fin n => |matMul n Q D i k| * Z k j) <=
          Finset.univ.sum (fun k : Fin n =>
            (Aabs i k + c * matMul n X Aabs i k) * Z k j) := by
        exact Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_right (hQDabs i k) (hZnonneg k j))
      _ = matMul n Aabs Z i j +
          c * matMul n (matMul n X Aabs) Z i j := by
        unfold matMul
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
  have hZcompare : forall k j : Fin n, Z k j <= B k j +
      c * matMul n (matMul n Z Aabs) B k j := by
    intro k j
    simpa [Z, D, Pabs, B, Aabs, c, U] using
      ch14ext_gjeFinalizedNormalizedPabs_le_abs_Uinv_add
        fp s U_inv hn h3 hUpper hdiag hpiv hUinv k j
  have hAZ : forall i j : Fin n,
      matMul n Aabs Z i j <= matMul n Aabs B i j +
        c * matMul n (matMul n (matMul n Aabs Z) Aabs) B i j := by
    intro i j
    let E := matMul n (matMul n Z Aabs) B
    have hAssoc : matMul n Aabs E i j =
        matMul n (matMul n (matMul n Aabs Z) Aabs) B i j := by
      simp only [E, matMul_assoc]
    calc
      matMul n Aabs Z i j <= Finset.univ.sum (fun k : Fin n =>
          Aabs i k * (B k j + c * E k j)) := by
        unfold matMul
        exact Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hZcompare k j) (abs_nonneg _))
      _ = matMul n Aabs B i j + c * matMul n Aabs E i j := by
        change (Finset.univ.sum (fun k : Fin n =>
            Aabs i k * (B k j + c * E k j))) =
          (Finset.univ.sum (fun k : Fin n => Aabs i k * B k j)) +
            c * Finset.univ.sum (fun k : Fin n => Aabs i k * E k j)
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by rw [hAssoc]
  have hXAZ : forall i j : Fin n,
      matMul n (matMul n X Aabs) Z i j <=
        matMul n (matMul n X Aabs) B i j +
        c * matMul n
          (matMul n (matMul n (matMul n X Aabs) Z) Aabs) B i j := by
    intro i j
    let XA := matMul n X Aabs
    let E := matMul n (matMul n Z Aabs) B
    have hAssoc : matMul n XA E i j =
        matMul n (matMul n (matMul n XA Z) Aabs) B i j := by
      simp only [E, matMul_assoc]
    calc
      matMul n XA Z i j <=
          Finset.univ.sum (fun k : Fin n =>
            XA i k * (B k j + c * E k j)) := by
        unfold matMul
        exact Finset.sum_le_sum (fun k _ =>
          mul_le_mul_of_nonneg_left (hZcompare k j) (hXA i k))
      _ = matMul n XA B i j + c * matMul n XA E i j := by
        change (Finset.univ.sum (fun k : Fin n =>
            XA i k * (B k j + c * E k j))) =
          (Finset.univ.sum (fun k : Fin n => XA i k * B k j)) +
            c * Finset.univ.sum (fun k : Fin n => XA i k * E k j)
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      _ = _ := by
        dsimp [XA]
        rw [hAssoc]
  intro i j
  have h1 := hFirst i j
  have h2 := hAZ i j
  have h3' := hXAZ i j
  unfold ch14ext_gjeFinalizedResidualEnvelopeCorrection
  dsimp [U, X, Z, Aabs, B, c] at h1 h2 h3' ⊢
  nlinarith

/-- Action of the retained general-diagonal envelope correction on the
residual leading vector. -/
noncomputable def ch14ext_gjeFinalizedResidualPrintedCorrection {n : Nat}
    (fp : FPModel) (L_hat U U_inv : Fin n -> Fin n -> Real)
    (X Z : Fin n -> Fin n -> Real) (xhat : Fin n -> Real)
    (i : Fin n) : Real :=
  matMulVec n (absMatrix n L_hat)
    (matMulVec n
      (ch14ext_gjeFinalizedResidualEnvelopeCorrection n U X Z U_inv
        (gje_c₃ fp n))
      (matMulVec n (absMatrix n U) (absVec n xhat))) i

/-- The source residual object with the literal accumulated stage matrix is
bounded by Higham's printed `|L| |U| |U⁻¹| |U| |xhat|` object plus the
explicit general-diagonal correction. -/
theorem ch14ext_gjeFinalizedSource_residualS2_le_printed_add_correction
    {n : Nat} (fp : FPModel) (L_hat U_inv : Fin n -> Fin n -> Real)
    (s : Ch14GJEState n)
    (hn : 1 <= n) (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hUpper : forall i j : Fin n, j.val < i.val -> s.matrix i j = 0)
    (hdiag : forall i : Fin n, s.matrix i i ≠ 0)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0)
    (hUinv : IsRightInverse n s.matrix U_inv) (i : Fin n) :
    ch14ext_gjeResidualS2 n L_hat
        (ch14ext_gjeFinalizedSourceXabs fp s) s.matrix
        (ch14ext_gjeFinalizedDivOutput fp s) i <=
      ch14ext_gjeResidualS2 n L_hat
        (matMul n (absMatrix n s.matrix) (absMatrix n U_inv)) s.matrix
        (ch14ext_gjeFinalizedDivOutput fp s) i +
      gje_c₃ fp n * ch14ext_gjeFinalizedResidualPrintedCorrection fp
        L_hat s.matrix U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
        (ch14ext_gjeNormalizedPabs n
          (ch14ext_gjeBeforeFinalDivision fp s).matrix
          (ch14ext_gjeFinalizedSourcePabs fp s))
        (ch14ext_gjeFinalizedDivOutput fp s) i := by
  let X := ch14ext_gjeFinalizedSourceXabs fp s
  let P := matMul n (absMatrix n s.matrix) (absMatrix n U_inv)
  let Z := ch14ext_gjeNormalizedPabs n
    (ch14ext_gjeBeforeFinalDivision fp s).matrix
    (ch14ext_gjeFinalizedSourcePabs fp s)
  let C := ch14ext_gjeFinalizedResidualEnvelopeCorrection n
    s.matrix X Z U_inv (gje_c₃ fp n)
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let w := matMulVec n (absMatrix n s.matrix) (absVec n xhat)
  let c := gje_c₃ fp n
  have hw : forall j : Fin n, 0 <= w j := by
    intro j
    unfold w matMulVec absMatrix absVec
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hmid : forall a : Fin n,
      matMulVec n X w a <= matMulVec n P w a + c * matMulVec n C w a := by
    intro a
    unfold matMulVec
    calc
      Finset.univ.sum (fun k : Fin n => X a k * w k) <=
          Finset.univ.sum (fun k : Fin n =>
            (P a k + c * C a k) * w k) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right
          (by
            simpa [X, P, C, Z, c] using
              ch14ext_gjeFinalizedSourceXabs_le_printed_add_correction
                fp s U_inv hn h1 h3 hUpper hdiag hpiv hUinv a k)
          (hw k)
      _ = Finset.univ.sum (fun k : Fin n => P a k * w k) +
          c * Finset.univ.sum (fun k : Fin n => C a k * w k) := by
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun k _ => by ring)
  have houter := ch14ext_matMulVec_mono_nonneg n
    (absMatrix n L_hat) (matMulVec n X w)
    (fun a => matMulVec n P w a + c * matMulVec n C w a)
    (fun a k => abs_nonneg _) hmid i
  have hXabs : absMatrix n X = X := by
    funext a k
    exact abs_of_nonneg (ch14ext_gjeXabs_nonneg n
      (ch14ext_gjeFinalizedSourceStages fp s)
      (ch14ext_gjeFinalizedSourceQ fp s) 1 (n - 1) a k)
  have hPnonneg : forall a k : Fin n, 0 <= P a k := by
    intro a k
    unfold P matMul absMatrix
    exact Finset.sum_nonneg fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hPabs : absMatrix n P = P := by
    funext a k
    exact abs_of_nonneg (hPnonneg a k)
  change matMulVec n (absMatrix n L_hat)
      (matMulVec n (absMatrix n X) w) i <=
    matMulVec n (absMatrix n L_hat)
        (matMulVec n (absMatrix n P) w) i +
      c * ch14ext_gjeFinalizedResidualPrintedCorrection fp
        L_hat s.matrix U_inv X Z xhat i
  rw [hXabs, hPabs]
  calc
    matMulVec n (absMatrix n L_hat) (matMulVec n X w) i <=
        matMulVec n (absMatrix n L_hat)
          (fun a => matMulVec n P w a + c * matMulVec n C w a) i := houter
    _ = matMulVec n (absMatrix n L_hat) (matMulVec n P w) i +
        c * ch14ext_gjeFinalizedResidualPrintedCorrection fp
          L_hat s.matrix U_inv X Z xhat i := by
      unfold matMulVec ch14ext_gjeFinalizedResidualPrintedCorrection
      change (Finset.univ.sum (fun k : Fin n =>
          absMatrix n L_hat i k *
            ((Finset.univ.sum (fun q : Fin n => P k q * w q)) +
              c * (Finset.univ.sum (fun q : Fin n => C k q * w q))))) =
        (Finset.univ.sum (fun k : Fin n => absMatrix n L_hat i k *
          (Finset.univ.sum (fun q : Fin n => P k q * w q)))) +
        c * Finset.univ.sum (fun k : Fin n => absMatrix n L_hat i k *
          (Finset.univ.sum (fun q : Fin n => C k q * w q)))
      calc
        _ = Finset.univ.sum (fun k : Fin n =>
            absMatrix n L_hat i k *
                (Finset.univ.sum (fun q : Fin n => P k q * w q)) +
              c * (absMatrix n L_hat i k *
                (Finset.univ.sum (fun q : Fin n => C k q * w q)))) := by
          exact Finset.sum_congr rfl (fun k _ => by ring)
        _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Explicit higher-order term in the literal printed version of (14.31).
The second summand is the `8*n*u` leading coefficient applied to the retained
general-diagonal envelope correction. -/
noncomputable def ch14ext_gjeResidualFinalizedPrintedHigherOrder {n : Nat}
    (fp : FPModel) (L_hat U U_inv : Fin n -> Fin n -> Real)
    (X Z : Fin n -> Fin n -> Real) (y xhat : Fin n -> Real)
    (i : Fin n) : Real :=
  ch14ext_gjeResidualFinalDivisionHigherOrder n fp L_hat X U y xhat i +
    8 * (n : Real) * fp.u * gje_c₃ fp n *
      ch14ext_gjeFinalizedResidualPrintedCorrection fp
        L_hat U U_inv X Z xhat i

/-- **Higham (14.31), literal executor and literal printed inverse
envelope.**  The leading term is exactly
`8*n*u*|L|*|U|*|U⁻¹|*|U|*|xhat|`; all general-diagonal and final-division
effects are retained in the named higher-order expression. -/
theorem ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31_printed
    {n : Nat} (fp : FPModel)
    (A L_hat U_inv : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (s : Ch14GJEState n)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hUinv : IsRightInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i| <=
        8 * (n : Real) * fp.u *
          ch14ext_gjeResidualS2 n L_hat
            (matMul n (absMatrix n s.matrix) (absMatrix n U_inv))
            s.matrix (ch14ext_gjeFinalizedDivOutput fp s) i +
        ch14ext_gjeResidualFinalizedPrintedHigherOrder fp L_hat s.matrix
          U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i := by
  intro i
  have hbase := ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31
    fp A L_hat b s hLU hn hnpos h1 h3 hdiagU hyStart hpiv i
  have hreplace :=
    ch14ext_gjeFinalizedSource_residualS2_le_printed_add_correction
      fp L_hat U_inv s hnpos h1 h3 hLU.U_lower_zero hdiagU hpiv hUinv i
  have hcoef : 0 <= 8 * (n : Real) * fp.u :=
    mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hreplace hcoef
  unfold ch14ext_gjeResidualFinalizedPrintedHigherOrder
  nlinarith

/-- The first-stage action of the stage-two error is `O(u)` whenever the
componentwise stage-two error itself is `O(u)`. -/
theorem ch14ext_gjeForwardFirstStageErrorAction_family_isBigO_unit
    {ι : Type*} {l : Filter ι} (n : Nat) (fp : ι -> FPModel)
    (A_inv L U : ι -> Fin n -> Fin n -> Real)
    (z xhat : ι -> Fin n -> Real)
    (hA : MatrixFamilyIsBigOOne l A_inv)
    (hL : MatrixFamilyIsBigOOne l L) (hU : MatrixFamilyIsBigOOne l U)
    (he : forall j : Fin n,
      (fun t => |z t j - xhat t j|) =O[l] (fun t => (fp t).u))
    (i : Fin n) :
    (fun t => ch14ext_gjeForwardFirstStageErrorAction n
      (A_inv t) (L t) (U t) (z t) (xhat t) i)
      =O[l] (fun t => (fp t).u) := by
  have hAA := matrixFamily_abs_isBigOOne hA
  have hAL := matrixFamily_abs_isBigOOne hL
  have hAU := matrixFamily_abs_isBigOOne hU
  have hUe : forall a : Fin n,
      (fun t => matMulVec n (absMatrix n (U t))
        (fun j => |z t j - xhat t j|) a)
        =O[l] (fun t => (fp t).u) := by
    intro a
    simpa only [matMulVec, absMatrix, one_mul] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun j _ =>
        (hAU a j).mul (he j)))
  have hLUe : forall a : Fin n,
      (fun t => matMulVec n (absMatrix n (L t))
        (matMulVec n (absMatrix n (U t))
          (fun j => |z t j - xhat t j|)) a)
        =O[l] (fun t => (fp t).u) := by
    intro a
    simpa only [matMulVec, absMatrix, one_mul] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun j _ =>
        (hAL a j).mul (hUe j)))
  have hALUe :
      (fun t => matMulVec n (absMatrix n (A_inv t))
        (matMulVec n (absMatrix n (L t))
          (matMulVec n (absMatrix n (U t))
            (fun j => |z t j - xhat t j|))) i)
        =O[l] (fun t => (fp t).u) := by
    simpa only [matMulVec, absMatrix, one_mul] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun j _ =>
        (hAA i j).mul (hLUe j)))
  simpa only [ch14ext_gjeForwardFirstStageErrorAction] using hALUe

/-- A vanishing-roundoff family of successful literal Algorithm 14.4 runs.
Unlike the legacy source-family contract, this structure has no
`final_matrix = I` or separately supplied final-vector field: the output is
definitionally the componentwise `fl_div` result. -/
structure Ch14GJEFinalizedFamily
    (ι : Type*) (l : Filter ι) (n : Nat)
    (A : Fin n -> Fin n -> Real) (b : Fin n -> Real) where
  model : ι -> FPModel
  L_hat : ι -> Fin n -> Fin n -> Real
  initial : ι -> Ch14GJEState n
  U_inv : ι -> Fin n -> Fin n -> Real
  z : ι -> Fin n -> Real
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (nhds 0)
  lu_certificate : forall t,
    LUBackwardError n A (L_hat t) (initial t).matrix (gamma (model t) n)
  valid_n : forall t, gammaValid (model t) n
  valid_one : forall t, gammaValid (model t) 1
  valid_three : forall t, gammaValid (model t) 3
  dimension_pos : 1 <= n
  diagonal_nonzero : forall t i, (initial t).matrix i i ≠ 0
  forward_start : forall t,
    (initial t).rhs = fl_forwardSub (model t) n (L_hat t) b
  pivots_nonzero : forall t q, (hq : q < n - 1) ->
    ch14ext_gjeFinalizedSourceTraceMatrix (model t) 1 (initial t) (1 + q)
      ⟨1 + q, by omega⟩ ⟨1 + q, by omega⟩ ≠ 0
  computed_upper_inverse : forall t,
    IsInverse n (initial t).matrix (U_inv t)
  upper_solve : forall t i,
    matMulVec n (initial t).matrix (z t) i = (initial t).rhs i
  L_hat_isBigO_one : MatrixFamilyIsBigOOne l L_hat
  U_hat_isBigO_one : MatrixFamilyIsBigOOne l (fun t => (initial t).matrix)
  source_Xabs_isBigO_one : MatrixFamilyIsBigOOne l (fun t =>
    ch14ext_gjeFinalizedSourceXabs (model t) (initial t))
  normalized_Pabs_isBigO_one : MatrixFamilyIsBigOOne l (fun t =>
    ch14ext_gjeNormalizedPabs n
      (ch14ext_gjeBeforeFinalDivision (model t) (initial t)).matrix
      (ch14ext_gjeFinalizedSourcePabs (model t) (initial t)))
  y_isBigO_one : VectorFamilyIsBigOOne l (fun t => (initial t).rhs)
  output_isBigO_one : VectorFamilyIsBigOOne l (fun t =>
    ch14ext_gjeFinalizedDivOutput (model t) (initial t))
  U_inv_isBigO_one : MatrixFamilyIsBigOOne l U_inv
  z_isBigO_one : VectorFamilyIsBigOOne l z

noncomputable def ch14ext_gjeFinalizedFamilyOutput
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14GJEFinalizedFamily ι l n A b) (τ : ι) : Fin n -> Real :=
  ch14ext_gjeFinalizedDivOutput (F.model τ) (F.initial τ)

noncomputable def ch14ext_gjeFinalizedFamilyXabs
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14GJEFinalizedFamily ι l n A b) (τ : ι) :
    Fin n -> Fin n -> Real :=
  ch14ext_gjeFinalizedSourceXabs (F.model τ) (F.initial τ)

noncomputable def ch14ext_gjeFinalizedFamilyNormalizedPabs
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14GJEFinalizedFamily ι l n A b) (τ : ι) :
    Fin n -> Fin n -> Real :=
  ch14ext_gjeNormalizedPabs n
    (ch14ext_gjeBeforeFinalDivision (F.model τ) (F.initial τ)).matrix
    (ch14ext_gjeFinalizedSourcePabs (F.model τ) (F.initial τ))

theorem ch14ext_gjePrintedResidualS2_eq_matrix_action (n : Nat)
    (L U U_inv : Fin n -> Fin n -> Real) (xhat : Fin n -> Real)
    (i : Fin n) :
    ch14ext_gjeResidualS2 n L
        (matMul n (absMatrix n U) (absMatrix n U_inv)) U xhat i =
      matMulVec n
        (matMul n
          (matMul n (absMatrix n L) (absMatrix n U))
          (matMul n (absMatrix n U_inv) (absMatrix n U)))
        (absVec n xhat) i := by
  let P := matMul n (absMatrix n U) (absMatrix n U_inv)
  have hPnonneg : forall a b : Fin n, 0 <= P a b := by
    intro a b
    unfold P matMul absMatrix
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hPabs : absMatrix n P = P := by
    funext a b
    exact abs_of_nonneg (hPnonneg a b)
  unfold ch14ext_gjeResidualS2
  change matMulVec n (absMatrix n L)
      (matMulVec n (absMatrix n P)
        (matMulVec n (absMatrix n U) (absVec n xhat))) i = _
  rw [hPabs]
  rw [matMulVec_matMul n
    (matMul n (absMatrix n L) (absMatrix n U))
    (matMul n (absMatrix n U_inv) (absMatrix n U))]
  rw [matMulVec_matMul n (absMatrix n L) (absMatrix n U)]
  apply congrArg (fun v => matMulVec n (absMatrix n L) v i)
  funext a
  dsimp only [P]
  rw [matMulVec_matMul n (absMatrix n U) (absMatrix n U_inv)]
  apply congrArg (fun v => matMulVec n (absMatrix n U) v a)
  funext q
  exact (matMulVec_matMul n (absMatrix n U_inv) (absMatrix n U)
    (absVec n xhat) q).symm

theorem ch14ext_gjePrintedForwardT1_eq_matrix_action (n : Nat)
    (A_inv L U : Fin n -> Fin n -> Real) (xhat : Fin n -> Real)
    (i : Fin n) :
    ch14ext_gjeForwardT1 n A_inv L U xhat i =
      matMulVec n
        (matMul n (absMatrix n A_inv)
          (matMul n (absMatrix n L) (absMatrix n U)))
        (absVec n xhat) i := by
  unfold ch14ext_gjeForwardT1
  rw [matMulVec_matMul n (absMatrix n A_inv)
    (matMul n (absMatrix n L) (absMatrix n U))]
  apply congrArg (fun v => matMulVec n (absMatrix n A_inv) v i)
  funext a
  exact (matMulVec_matMul n (absMatrix n L) (absMatrix n U)
    (absVec n xhat) a).symm

theorem ch14ext_gjePrintedForwardT2_eq_matrix_action (n : Nat)
    (U U_inv : Fin n -> Fin n -> Real) (xhat : Fin n -> Real)
    (i : Fin n) :
    ch14ext_gjeForwardT2 n (absMatrix n U_inv) U xhat i =
      matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U))
        (absVec n xhat) i := by
  unfold ch14ext_gjeForwardT2
  simp only [matMulVec_matMul]

/-- **Corollary 14.7 residual adapter for the literal final-division
executor.**  The computed vector is definitionally
`ch14ext_gjeFinalizedDivOutput`; the named extra term is the actual (14.31)
`O(u²)` remainder, not a supplied endpoint certificate. -/
theorem ch14ext_cor147Finalized_rowwise_residual_printed
    {n : Nat} (fp : FPModel)
    (A L_hat U_inv : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (s : Ch14GJEState n)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLUexact : LUFactSpec n A L_hat s.matrix)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hUinv : IsInverse n s.matrix U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    forall i : Fin n,
      |b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i| <=
        32 * (n : Real) ^ 2 * fp.u *
          (Finset.univ.sum (fun j : Fin n => |A i j|)) *
          (Finset.univ.sum (fun j : Fin n =>
            |ch14ext_gjeFinalizedDivOutput fp s j|)) +
        ch14ext_gjeResidualFinalizedPrintedHigherOrder fp L_hat s.matrix
          U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i := by
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let rho : Fin n -> Real := fun i =>
    ch14ext_gjeResidualFinalizedPrintedHigherOrder fp L_hat s.matrix
      U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
      (ch14ext_gjeNormalizedPabs n
        (ch14ext_gjeBeforeFinalDivision fp s).matrix
        (ch14ext_gjeFinalizedSourcePabs fp s)) s.rhs xhat i
  let lead : Fin n -> Real := fun i =>
    8 * (n : Real) * fp.u *
      ch14ext_gjeResidualS2 n L_hat
        (matMul n (absMatrix n s.matrix) (absMatrix n U_inv))
        s.matrix xhat i
  let bLead : Fin n -> Real := fun i => matMulVec n A xhat i + lead i
  have hleadNonneg : forall i : Fin n, 0 <= lead i := by
    intro i
    unfold lead
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (ch14ext_gjeResidualS2_nonneg n L_hat
        (matMul n (absMatrix n s.matrix) (absMatrix n U_inv))
        s.matrix xhat i)
  have hLeadRes : forall i : Fin n,
      |bLead i - Finset.univ.sum (fun j : Fin n => A i j * xhat j)| <=
        8 * (n : Real) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n s.matrix))
              (matMul n (absMatrix n U_inv) (absMatrix n s.matrix)))
            (absVec n xhat) i := by
    intro i
    rw [show bLead i - Finset.univ.sum (fun j : Fin n => A i j * xhat j) =
      lead i by simp [bLead, matMulVec]]
    rw [abs_of_nonneg (hleadNonneg i)]
    exact le_of_eq (congrArg
      (fun q => 8 * (n : Real) * fp.u * q)
      (ch14ext_gjePrintedResidualS2_eq_matrix_action
        n L_hat s.matrix U_inv xhat i))
  have hLeadPrinted :=
    ch14ext_cor147_rowwise_residual_printed_of_exactGE_and_theorem14_5
      n fp A L_hat s.matrix U_inv bLead xhat hRow hdet hLUexact hUinv hLeadRes
  have hActual := ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31_printed
    fp A L_hat U_inv b s hLU hUinv.2 hn hnpos h1 h3 hdiagU hyStart hpiv
  intro i
  have hLeadEq : |bLead i - matMulVec n A xhat i| = lead i := by
    simp [bLead, abs_of_nonneg (hleadNonneg i)]
  have hLeadBound : lead i <=
      32 * (n : Real) ^ 2 * fp.u *
        (Finset.univ.sum (fun j : Fin n => |A i j|)) *
        (Finset.univ.sum (fun j : Fin n => |xhat j|)) := by
    rw [← hLeadEq]
    simpa only [matMulVec] using hLeadPrinted i
  calc
    |b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i| <=
        lead i + rho i := by
      simpa only [lead, rho, xhat] using hActual i
    _ <= 32 * (n : Real) ^ 2 * fp.u *
          (Finset.univ.sum (fun j : Fin n => |A i j|)) *
          (Finset.univ.sum (fun j : Fin n => |xhat j|)) + rho i :=
      by linarith [hLeadBound]
    _ = _ := by rfl

/-- **Corollary 14.6 residual adapter for the literal final-division
executor.**  This is the exact pre-asymptotic SPD reduction; the remaining
vector is the actual terminal (14.31) remainder and is `O(u²)` by
`ch14ext_gjeResidualFinalizedPrintedHigherOrder_family_isBigO`. -/
theorem ch14ext_cor146Finalized_residual_norm2
    {n : Nat} (fp : FPModel)
    (A L_hat U_inv R_inv : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (s : Ch14GJEState n)
    (hSPD : IsSymPosDef n A)
    (hLU : LUBackwardError n A L_hat s.matrix (gamma fp n))
    (hpivPos : forall i : Fin n, 0 < s.matrix i i)
    (hsym : forall i j : Fin n,
      s.matrix i j = s.matrix i i * L_hat j i)
    (hUinv : IsInverse n s.matrix U_inv)
    (hRinv : IsInverse n (ch14ext_cor146_scaledUpper n s.matrix) R_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n)
    (h1 : gammaValid fp 1) (h3 : gammaValid fp 3)
    (hsmall : (n : Real) * gamma fp n < 1)
    (hdiagU : forall i : Fin n, s.matrix i i ≠ 0)
    (hyStart : s.rhs = fl_forwardSub fp n L_hat b)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      ch14ext_gjeFinalizedSourceTraceMatrix fp 1 s (1 + t)
        ⟨1 + t, by omega⟩ ⟨1 + t, by omega⟩ ≠ 0) :
    vecNorm2 (fun i : Fin n =>
      b i - matMulVec n A (ch14ext_gjeFinalizedDivOutput fp s) i) <=
      8 * (n : Real) ^ 3 * fp.u *
        (1 - (n : Real) * gamma fp n)⁻¹ *
        Real.sqrt
          (kappa2
            (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
            (nonsingInv n (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) *
        opNorm2 A * vecNorm2 (ch14ext_gjeFinalizedDivOutput fp s) +
      vecNorm2 (fun i =>
        ch14ext_gjeResidualFinalizedPrintedHigherOrder fp L_hat s.matrix
          U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
          (ch14ext_gjeNormalizedPabs n
            (ch14ext_gjeBeforeFinalDivision fp s).matrix
            (ch14ext_gjeFinalizedSourcePabs fp s))
          s.rhs (ch14ext_gjeFinalizedDivOutput fp s) i) := by
  let xhat := ch14ext_gjeFinalizedDivOutput fp s
  let rho : Fin n -> Real := fun i =>
    ch14ext_gjeResidualFinalizedPrintedHigherOrder fp L_hat s.matrix
      U_inv (ch14ext_gjeFinalizedSourceXabs fp s)
      (ch14ext_gjeNormalizedPabs n
        (ch14ext_gjeBeforeFinalDivision fp s).matrix
        (ch14ext_gjeFinalizedSourcePabs fp s)) s.rhs xhat i
  let lead : Fin n -> Real := fun i =>
    8 * (n : Real) * fp.u *
      ch14ext_gjeResidualS2 n L_hat
        (matMul n (absMatrix n s.matrix) (absMatrix n U_inv))
        s.matrix xhat i
  let bLead : Fin n -> Real := fun i => matMulVec n A xhat i + lead i
  let factor := (1 - (n : Real) * gamma fp n)⁻¹
  have hden : 0 < 1 - (n : Real) * gamma fp n := by linarith
  have hfactor : 0 <= factor := le_of_lt (inv_pos.mpr hden)
  have hAbsLU : opNorm2Le
      (matMul n (absMatrix n L_hat) (absMatrix n s.matrix))
      ((n : Real) * factor * opNorm2 A) := by
    simpa [factor] using ch14ext_cor146_absLU_budget
      n fp A L_hat s.matrix hLU hpivPos hsym hn hsmall
  have hleadNonneg : forall i : Fin n, 0 <= lead i := by
    intro i
    unfold lead
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (ch14ext_gjeResidualS2_nonneg n L_hat
        (matMul n (absMatrix n s.matrix) (absMatrix n U_inv))
        s.matrix xhat i)
  have hLeadRes : forall i : Fin n,
      |bLead i - Finset.univ.sum (fun j : Fin n => A i j * xhat j)| <=
        8 * (n : Real) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n s.matrix))
              (matMul n (absMatrix n U_inv) (absMatrix n s.matrix)))
            (absVec n xhat) i := by
    intro i
    rw [show bLead i - Finset.univ.sum (fun j : Fin n => A i j * xhat j) =
      lead i by simp [bLead, matMulVec]]
    rw [abs_of_nonneg (hleadNonneg i)]
    exact le_of_eq (congrArg
      (fun q => 8 * (n : Real) * fp.u * q)
      (ch14ext_gjePrintedResidualS2_eq_matrix_action
        n L_hat s.matrix U_inv xhat i))
  have hLeadNormRaw :=
    ch14ext_cor146_residual_positivePivot_exactGram_of_theorem14_5
      n fp A L_hat s.matrix U_inv R_inv bLead xhat factor hSPD hLU
      hpivPos hsym hUinv hRinv hfactor hAbsLU hLeadRes
  have hLeadVector : (fun i : Fin n =>
      bLead i - Finset.univ.sum (fun j : Fin n => A i j * xhat j)) = lead := by
    funext i
    simp [bLead, matMulVec]
  have hLeadNorm : vecNorm2 lead <=
      8 * (n : Real) ^ 3 * fp.u * factor *
        Real.sqrt
          (kappa2
            (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
            (nonsingInv n (fun i j => A i j +
              ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) *
        opNorm2 A * vecNorm2 xhat := by
    rw [← hLeadVector]
    exact hLeadNormRaw
  have hActual := ch14ext_gjeFinalizedSourceTrace_overall_residual_14_31_printed
    fp A L_hat U_inv b s hLU hUinv.2 hn hnpos h1 h3 hdiagU hyStart hpiv
  have hEntry : forall i : Fin n,
      |b i - matMulVec n A xhat i| <= lead i + rho i := by
    intro i
    simpa only [lead, rho, xhat] using hActual i
  have hNorm := vecNorm2_le_of_abs_le
    (fun i : Fin n => b i - matMulVec n A xhat i)
    (fun i => lead i + rho i) hEntry
  calc
    vecNorm2 (fun i : Fin n => b i - matMulVec n A xhat i) <=
        vecNorm2 (fun i => lead i + rho i) := hNorm
    _ <= vecNorm2 lead + vecNorm2 rho := vecNorm2_add_le lead rho
    _ <= 8 * (n : Real) ^ 3 * fp.u * factor *
          Real.sqrt
            (kappa2
              (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j)
              (nonsingInv n (fun i j => A i j +
                ch14ext_cor146_symmetricGEDelta n A L_hat s.matrix i j))) *
          opNorm2 A * vecNorm2 xhat + vecNorm2 rho :=
      by linarith [hLeadNorm]
    _ = _ := by rfl

/-- Successful vanishing-roundoff SPD runs whose returned vector is the
literal componentwise `fl_div` output.  The extra fields are structural and
spectral regularity data; no residual or forward-error conclusion is assumed.
-/
structure Ch14Cor146FinalizedRunFamily
    (I : Type*) (l : Filter I) (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) where
  gje : Ch14GJEFinalizedFamily I l n A b
  R_inv : I -> Fin n -> Fin n -> Real
  spd : IsSymPosDef n A
  exact_solution_nonzero : 0 < vecNorm2 x
  computed_pivots_pos : forall t i, 0 < (gje.initial t).matrix i i
  symmetric_factor_relation : forall t i j,
    (gje.initial t).matrix i j =
      (gje.initial t).matrix i i * gje.L_hat t j i
  scaled_upper_inverse : forall t,
    IsInverse n (ch14ext_cor146_scaledUpper n (gje.initial t).matrix)
      (R_inv t)
  gamma_small : forall t, (n : Real) * gamma (gje.model t) n < 1
  exact_solution : forall i, matMulVec n A x i = b i
  uniform_inverse : Ch14Cor146UniformInverseRegularity l n A A_inv
    gje.model gje.L_hat (fun t => (gje.initial t).matrix)

/-- The norm of the literal terminal remainder in (14.31). -/
noncomputable def ch14ext_cor146FinalizedResidualTerminal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  vecNorm2 (fun i =>
    ch14ext_gjeResidualFinalizedPrintedHigherOrder (F.gje.model t)
      (F.gje.L_hat t) (F.gje.initial t).matrix (F.gje.U_inv t)
      (ch14ext_gjeFinalizedFamilyXabs F.gje t)
      (ch14ext_gjeFinalizedFamilyNormalizedPabs F.gje t)
      (F.gje.initial t).rhs (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)

/-- The norm of the literal terminal remainder in (14.32). -/
noncomputable def ch14ext_cor146FinalizedForwardTerminal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  vecNorm2 (fun i =>
    ch14ext_gjeForwardFinalDivisionHigherOrder n (F.gje.model t) A_inv
      (F.gje.L_hat t) (F.gje.initial t).matrix
      (ch14ext_gjeFinalizedFamilyNormalizedPabs F.gje t)
      (F.gje.U_inv t) (F.gje.z t) (F.gje.initial t).rhs
      (ch14ext_gjeFinalizedFamilyOutput F.gje t) i)

/-- Explicit residual remainder after replacing the perturbed SPD condition
factor by the source-matrix factor printed in Corollary 14.6. -/
noncomputable def ch14ext_cor146FinalizedResidualRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  ch14ext_cor146FinalizedResidualTerminal F t +
    8 * (n : Real) ^ 3 * (F.gje.model t).u *
      ch14ext_cor146ResidualSpectralCorrection n F.gje.model A A_inv
        F.gje.L_hat (fun s => (F.gje.initial s).matrix) t *
      opNorm2 A * vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t)

/-- The literal printed Corollary 14.6 residual remainder.  In addition to
the spectral and terminal corrections above, it records the replacement
`||xhat||_2 <= ||x||_2 + ||xhat-x||_2` required by the PDF statement. -/
noncomputable def ch14ext_cor146FinalizedResidualPrintedRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  ch14ext_cor146FinalizedResidualRemainder F t +
    8 * (n : Real) ^ 3 * (F.gje.model t).u *
      Real.sqrt (kappa2 A A_inv) * opNorm2 A *
      vecNorm2 (fun i => ch14ext_gjeFinalizedFamilyOutput F.gje t i - x i)

/-- Explicit absolute forward remainder after replacing both varying SPD
coefficients by `8*n^2*sqrt(n)*kappa2(A)`. -/
noncomputable def ch14ext_cor146FinalizedForwardAbsoluteRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  ch14ext_cor146FinalizedForwardTerminal F t +
    (F.gje.model t).u *
      ch14ext_cor146ForwardCoefficientCorrection n F.gje.model A A_inv
        F.gje.L_hat (fun s => (F.gje.initial s).matrix) t *
      vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t)

/-- Explicit relative-error remainder after the standard successful-run
bootstrap removes `||xhat||_2/||x||_2`. -/
noncomputable def ch14ext_cor146FinalizedForwardRelativeRemainder
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x)
    (t : I) : Real :=
  let c := ch14ext_cor146ForwardPrintedCoefficient n A A_inv
  let q := c * (F.gje.model t).u
  q ^ 2 * (1 - q)⁻¹ +
    ch14ext_cor146FinalizedForwardAbsoluteRemainder F t *
      (1 - q)⁻¹ * (vecNorm2 x)⁻¹

/-- Corollary 14.6 residual bound with the literal printed source-matrix
coefficient, for the actual final-division output. -/
theorem ch14ext_cor146Finalized_residual_source_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) (t : I) :
    vecNorm2 (fun i : Fin n =>
      b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) <=
      8 * (n : Real) ^ 3 * (F.gje.model t).u *
          Real.sqrt (kappa2 A A_inv) * opNorm2 A *
          vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t) +
        ch14ext_cor146FinalizedResidualRemainder F t := by
  let factor := (1 - (n : Real) * gamma (F.gje.model t) n)⁻¹
  let khat := ch14ext_cor146ClosureSqrtKappa n A F.gje.L_hat
    (fun s => (F.gje.initial s).matrix) t
  let ksrc := Real.sqrt (kappa2 A A_inv)
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  let C := 8 * (n : Real) ^ 3 * (F.gje.model t).u *
    opNorm2 A * vecNorm2 xhat
  let rho := ch14ext_cor146FinalizedResidualTerminal F t
  have hbase := ch14ext_cor146Finalized_residual_norm2
    (F.gje.model t) A (F.gje.L_hat t) (F.gje.U_inv t) (F.R_inv t) b
      (F.gje.initial t) F.spd (F.gje.lu_certificate t)
      (F.computed_pivots_pos t) (F.symmetric_factor_relation t)
      (F.gje.computed_upper_inverse t) (F.scaled_upper_inverse t)
      (F.gje.valid_n t) F.gje.dimension_pos (F.gje.valid_one t)
      (F.gje.valid_three t) (F.gamma_small t)
      (F.gje.diagonal_nonzero t) (F.gje.forward_start t)
      (F.gje.pivots_nonzero t)
  have hAhat : ch14ext_cor146ClosureAhat n A F.gje.L_hat
      (fun s => (F.gje.initial s).matrix) t =
      (fun i j => A i j + ch14ext_cor146_symmetricGEDelta n A
        (F.gje.L_hat t) (F.gje.initial t).matrix i j) := rfl
  have hspectral : factor * khat <=
      ksrc + |factor * khat - ksrc| := by
    linarith [le_abs_self (factor * khat - ksrc)]
  have hC0 : 0 <= C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (F.gje.model t).u_nonneg)
        (opNorm2_nonneg A))
      (vecNorm2_nonneg xhat)
  have hbase' :
      vecNorm2 (fun i : Fin n => b i - matMulVec n A xhat i) <=
        C * (factor * khat) + rho := by
    convert hbase using 1 <;>
      simp [C, factor, khat, rho, xhat,
        ch14ext_cor146FinalizedResidualTerminal,
        ch14ext_gjeFinalizedFamilyOutput,
        ch14ext_gjeFinalizedFamilyXabs,
        ch14ext_gjeFinalizedFamilyNormalizedPabs,
        ch14ext_cor146ClosureSqrtKappa, hAhat] <;> ring
  calc
    vecNorm2 (fun i : Fin n =>
        b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) <=
        C * (factor * khat) + rho := hbase'
    _ <= C * (ksrc + |factor * khat - ksrc|) + rho :=
      add_le_add (mul_le_mul_of_nonneg_left hspectral hC0) (le_refl rho)
    _ = 8 * (n : Real) ^ 3 * (F.gje.model t).u *
          Real.sqrt (kappa2 A A_inv) * opNorm2 A *
          vecNorm2 (ch14ext_gjeFinalizedFamilyOutput F.gje t) +
        ch14ext_cor146FinalizedResidualRemainder F t := by
      simp only [ch14ext_cor146FinalizedResidualRemainder,
        ch14ext_cor146ResidualSpectralCorrection, C, factor, khat, ksrc,
        rho, xhat]
      ring

/-- The exact PDF form of the Corollary 14.6 residual bound.  Its leading
term contains the exact-solution norm `||x||_2`; the actual-output
`||xhat-x||_2` replacement is exposed in a named higher-order remainder. -/
theorem ch14ext_cor146Finalized_residual_exact_solution_literal
    {I : Type*} {l : Filter I} {n : Nat}
    {A A_inv : Fin n -> Fin n -> Real} {b x : Fin n -> Real}
    (F : Ch14Cor146FinalizedRunFamily I l n A A_inv b x) (t : I) :
    vecNorm2 (fun i : Fin n =>
      b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) <=
      8 * (n : Real) ^ 3 * (F.gje.model t).u *
          Real.sqrt (kappa2 A A_inv) * opNorm2 A * vecNorm2 x +
        ch14ext_cor146FinalizedResidualPrintedRemainder F t := by
  let xhat := ch14ext_gjeFinalizedFamilyOutput F.gje t
  let C := 8 * (n : Real) ^ 3 * (F.gje.model t).u *
    Real.sqrt (kappa2 A A_inv) * opNorm2 A
  let e := vecNorm2 (fun i : Fin n => xhat i - x i)
  have hraw := ch14ext_cor146Finalized_residual_source_literal F t
  have hxhat : vecNorm2 xhat <= vecNorm2 x + e := by
    calc
      vecNorm2 xhat = vecNorm2 (fun i : Fin n => x i + (xhat i - x i)) := by
        apply congrArg vecNorm2
        funext i
        ring
      _ <= vecNorm2 x + vecNorm2 (fun i : Fin n => xhat i - x i) :=
        vecNorm2_add_le x (fun i : Fin n => xhat i - x i)
      _ = vecNorm2 x + e := rfl
  have hC0 : 0 <= C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (F.gje.model t).u_nonneg)
        (Real.sqrt_nonneg (kappa2 A A_inv)))
      (opNorm2_nonneg A)
  calc
    vecNorm2 (fun i : Fin n =>
        b i - matMulVec n A (ch14ext_gjeFinalizedFamilyOutput F.gje t) i) <=
        C * vecNorm2 xhat +
          ch14ext_cor146FinalizedResidualRemainder F t := by
      simpa only [C, xhat, mul_assoc] using hraw
    _ <= C * (vecNorm2 x + e) +
          ch14ext_cor146FinalizedResidualRemainder F t :=
      add_le_add (mul_le_mul_of_nonneg_left hxhat hC0) (le_refl _)
    _ = 8 * (n : Real) ^ 3 * (F.gje.model t).u *
          Real.sqrt (kappa2 A A_inv) * opNorm2 A * vecNorm2 x +
        ch14ext_cor146FinalizedResidualPrintedRemainder F t := by
      simp only [ch14ext_cor146FinalizedResidualPrintedRemainder, C, e,
        xhat]
      ring

end Ch14Ext
end NumStability
