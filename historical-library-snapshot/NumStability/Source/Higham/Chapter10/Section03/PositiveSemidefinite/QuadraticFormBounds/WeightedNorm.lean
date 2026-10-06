import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# WeightedNorm

Canonical destination for 2 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.CholeskyPSD` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **PSD quadratic form is trace-bounded**:
    `xᵀAx ≤ (∑ᵢ a_ii)(∑ᵢ xᵢ²)` — entrywise domination by
    `√(a_ii a_jj)` plus Cauchy–Schwarz. This turns the trace into a
    computable operator certificate for PSD matrices. -/
lemma psd_quadForm_le_trace {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 := by
  have hstep : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      ∑ i : Fin n, ∑ j : Fin n,
        (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have habs : x i * A i j * x j ≤ |x i| * |A i j| * |x j| := by
      calc x i * A i j * x j ≤ |x i * A i j * x j| := le_abs_self _
        _ = |x i| * |A i j| * |x j| := by rw [abs_mul, abs_mul]
    calc x i * A i j * x j ≤ |x i| * |A i j| * |x j| := habs
      _ ≤ |x i| * (Real.sqrt (A i i) * Real.sqrt (A j j)) * |x j| := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left
              (psd_abs_entry_le_sqrt_diag A hPSD i j)
              (abs_nonneg _)) (abs_nonneg _)
      _ = (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) :=
          by ring
  have hsq : ∑ i : Fin n, ∑ j : Fin n,
      (|x i| * Real.sqrt (A i i)) * (|x j| * Real.sqrt (A j j)) =
      (∑ i : Fin n, |x i| * Real.sqrt (A i i)) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |x i|) (fun i => Real.sqrt (A i i))
  have hL : ∑ i : Fin n, |x i| ^ 2 = ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  have hR : ∑ i : Fin n, Real.sqrt (A i i) ^ 2 = ∑ i : Fin n, A i i :=
    Finset.sum_congr rfl fun i _ =>
      Real.sq_sqrt (isPosSemiDef_diag_nonneg A hPSD i)
  rw [hL, hR] at hcs
  calc ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      ≤ (∑ i : Fin n, |x i| * Real.sqrt (A i i)) ^ 2 :=
        hstep.trans_eq hsq
    _ ≤ (∑ i : Fin n, x i ^ 2) * ∑ i : Fin n, A i i := hcs
    _ = (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 := mul_comm _ _

/-- **PSD quadratic form bounded by dimension times the largest
    diagonal** (the normwise reading of the same engine):
    `xᵀAx ≤ n·d·‖x‖₂²` when every `a_ii ≤ d`. -/
lemma psd_quadForm_le_card_maxdiag {n : ℕ} (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (d : ℝ)
    (hd : ∀ i : Fin n, A i i ≤ d) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j ≤
      (n : ℝ) * d * ∑ i : Fin n, x i ^ 2 := by
  have htr : (∑ i : Fin n, A i i) ≤ (n : ℝ) * d := by
    calc ∑ i : Fin n, A i i ≤ ∑ _i : Fin n, d :=
          Finset.sum_le_sum fun i _ => hd i
      _ = (n : ℝ) * d := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
  have hx : 0 ≤ ∑ i : Fin n, x i ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  calc ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      ≤ (∑ i : Fin n, A i i) * ∑ i : Fin n, x i ^ 2 :=
        psd_quadForm_le_trace A hPSD x
    _ ≤ (n : ℝ) * d * ∑ i : Fin n, x i ^ 2 :=
        mul_le_mul_of_nonneg_right htr hx

end NumStability
