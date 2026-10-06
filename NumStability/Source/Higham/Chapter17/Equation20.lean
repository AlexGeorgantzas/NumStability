import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Order.Monotone
import NumStability.Algorithms.StationaryIteration

/-!
# Higham Chapter 17, Equation 17.20

Canonical source-correspondence owner for the literal residual-sigma matrix series, its equality with the finite-partial supremum envelope, and the diagonalizable maximum-bound bridge.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    paragraph before eq (17.20): the literal `(i,j)` entry of the infinite
    sigma series `Σ_{k=0}^∞ |H^k (I - H)|`.  Scope: like every real `tsum`
    this evaluates to `0` when not summable; `summable_residualSigmaEntry`
    certifies summability under `‖H‖∞ ≤ q < 1`. -/
noncomputable def residualSigmaEntry (n : ℕ) (H : Fin n → Fin n → ℝ)
    (i j : Fin n) : ℝ :=
  ∑' k : ℕ, |matMul n (matPow n H k) (matSub_id n H) i j|

/-- The literal (17.20) sigma entries are nonnegative. -/
theorem residualSigmaEntry_nonneg (n : ℕ) (H : Fin n → Fin n → ℝ)
    (i j : Fin n) :
    0 ≤ residualSigmaEntry n H i j :=
  tsum_nonneg fun _ => abs_nonneg _

/-- Geometric majorant for the terms of the sigma series in Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    eq (17.20): each entry satisfies
    `||H^k (I - H)|_{ij}| ≤ q^k · ‖I - H‖∞` (single entry ≤ row sum ≤
    matrix norm, then submultiplicativity and the power bound). -/
theorem residual_entry_abs_le_geometric (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ) (q : ℝ) (hH : infNorm H ≤ q)
    (i j : Fin n) (k : ℕ) :
    |matMul n (matPow n H k) (matSub_id n H) i j| ≤
      q ^ k * infNorm (matSub_id n H) :=
  calc |matMul n (matPow n H k) (matSub_id n H) i j|
      ≤ ∑ l : Fin n, |matMul n (matPow n H k) (matSub_id n H) i l| :=
        Finset.single_le_sum
          (f := fun l => |matMul n (matPow n H k) (matSub_id n H) i l|)
          (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ infNorm (matMul n (matPow n H k) (matSub_id n H)) :=
        row_sum_le_infNorm _ i
    _ ≤ infNorm (matPow n H k) * infNorm (matSub_id n H) :=
        infNorm_matMul_le hn _ _
    _ ≤ q ^ k * infNorm (matSub_id n H) :=
        mul_le_mul_of_nonneg_right
          ((infNorm_matPow_le hn H k).trans
            (pow_le_pow_left₀ (infNorm_nonneg H) hH k))
          (infNorm_nonneg _)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    eq (17.20): entrywise summability of the sigma series
    `Σ_k ||H^k (I - H)|_{ij}|` under the norm certificate `‖H‖∞ ≤ q < 1`,
    by comparison with the geometric majorant `q^k · ‖I - H‖∞`. -/
theorem summable_residualSigmaEntry (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) (i j : Fin n) :
    Summable (fun k => |matMul n (matPow n H k) (matSub_id n H) i j|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun k => residual_entry_abs_le_geometric n hn H q hH i j k)
    ((summable_geometric_of_lt_one hq0 hq1).mul_right (infNorm (matSub_id n H)))

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.3,
    paragraph before eq (17.20): the literal entrywise `tsum` sigma matrix
    `Σ_{k=0}^∞ |H^k (I - H)|`. -/
noncomputable def residualSigmaMatrix (n : ℕ) (H : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => residualSigmaEntry n H i j

/-- The finite partial sigma matrices are entrywise nonnegative. -/
theorem finiteResidualSigmaMatrix_nonneg (n : ℕ) (H : Fin n → Fin n → ℝ)
    (m : ℕ) (i j : Fin n) :
    0 ≤ finiteResidualSigmaMatrix n H m i j :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Each finite partial sigma matrix is entrywise dominated by the literal
    `tsum` sigma matrix (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.3, eq (17.20)): partial sums of a summable
    nonnegative series are below its `tsum`. -/
theorem finiteResidualSigmaMatrix_le_residualSigmaMatrix (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q)
    (m : ℕ) (i j : Fin n) :
    finiteResidualSigmaMatrix n H m i j ≤ residualSigmaMatrix n H i j :=
  Summable.sum_le_tsum (Finset.range (m + 1)) (fun _ _ => abs_nonneg _)
    (summable_residualSigmaEntry n hn H q hq0 hq1 hH i j)

/-- Every finite partial sigma norm is dominated by the norm of the literal
    `tsum` sigma matrix (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §17.3, eq (17.20)): row sums are monotone under
    the entrywise domination of nonnegative matrices. -/
theorem finiteResidualSigma_le_infNorm_residualSigmaMatrix (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) (m : ℕ) :
    finiteResidualSigma n H m ≤ infNorm (residualSigmaMatrix n H) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j|
        = ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j :=
          Finset.sum_congr rfl fun j _ =>
            abs_of_nonneg (finiteResidualSigmaMatrix_nonneg n H m i j)
      _ ≤ ∑ j : Fin n, residualSigmaMatrix n H i j :=
          Finset.sum_le_sum fun j _ =>
            finiteResidualSigmaMatrix_le_residualSigmaMatrix
              n hn H q hq0 hq1 hH m i j
      _ = ∑ j : Fin n, |residualSigmaMatrix n H i j| :=
          Finset.sum_congr rfl fun j _ =>
            (abs_of_nonneg (residualSigmaEntry_nonneg n H i j)).symm
      _ ≤ infNorm (residualSigmaMatrix n H) :=
          row_sum_le_infNorm _ i
  · exact infNorm_nonneg _

/-- The candidate finite partial sigma norms are bounded above under the
    norm certificate `‖H‖∞ ≤ q < 1` — the `bddAbove` input that makes the
    supremum envelope `residualSigmaSup` meaningful. -/
theorem bddAbove_residualSigmaValues (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    BddAbove (ResidualSigmaValues n H) := by
  refine ⟨infNorm (residualSigmaMatrix n H), fun y hy => ?_⟩
  rcases hy with ⟨m, rfl⟩
  exact finiteResidualSigma_le_infNorm_residualSigmaMatrix n hn H q hq0 hq1 hH m

/-- One half of the (17.20) equality: the supremum envelope is dominated by
    the norm of the literal `tsum` sigma matrix (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.3, eq (17.20)). -/
theorem residualSigmaSup_le_infNorm_residualSigmaMatrix (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    residualSigmaSup n H ≤ infNorm (residualSigmaMatrix n H) :=
  residualSigmaSup_le_of_finiteResidualSigma_le n H _
    (fun m => finiteResidualSigma_le_infNorm_residualSigmaMatrix
      n hn H q hq0 hq1 hH m)

/-- Other half of the (17.20) equality: the norm of the literal `tsum` sigma
    matrix is dominated by the supremum envelope (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.3, eq (17.20)).  Route:
    each row sum of the `tsum` matrix is a `tsum` of finite row sums (the
    finite-sum/`tsum` exchange), whose partial sums are row sums of the
    finite partial sigma matrices, hence below the supremum envelope. -/
theorem infNorm_residualSigmaMatrix_le_residualSigmaSup (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    infNorm (residualSigmaMatrix n H) ≤ residualSigmaSup n H := by
  have hbdd : BddAbove (ResidualSigmaValues n H) :=
    bddAbove_residualSigmaValues n hn H q hq0 hq1 hH
  have hsup0 : 0 ≤ residualSigmaSup n H :=
    le_trans (infNorm_nonneg (finiteResidualSigmaMatrix n H 0))
      (le_csSup hbdd ⟨0, rfl⟩)
  apply infNorm_le_of_row_sum_le
  · intro i
    have habs : ∑ j : Fin n, |residualSigmaMatrix n H i j| =
        ∑ j : Fin n, residualSigmaEntry n H i j :=
      Finset.sum_congr rfl fun j _ =>
        abs_of_nonneg (residualSigmaEntry_nonneg n H i j)
    rw [habs]
    have hexch : ∑ j : Fin n, residualSigmaEntry n H i j =
        ∑' k : ℕ, ∑ j : Fin n,
          |matMul n (matPow n H k) (matSub_id n H) i j| := by
      unfold residualSigmaEntry
      exact (Summable.tsum_finsetSum
        (fun j _ => summable_residualSigmaEntry n hn H q hq0 hq1 hH i j)).symm
    rw [hexch]
    apply Real.tsum_le_of_sum_range_le
    · intro k
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · intro mtot
      cases mtot with
      | zero => simpa using hsup0
      | succ m =>
        have hcomm : ∑ k ∈ Finset.range (m + 1), ∑ j : Fin n,
            |matMul n (matPow n H k) (matSub_id n H) i j| =
            ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j := by
          unfold finiteResidualSigmaMatrix
          exact Finset.sum_comm
        rw [hcomm]
        calc ∑ j : Fin n, finiteResidualSigmaMatrix n H m i j
            = ∑ j : Fin n, |finiteResidualSigmaMatrix n H m i j| :=
              Finset.sum_congr rfl fun j _ =>
                (abs_of_nonneg (finiteResidualSigmaMatrix_nonneg n H m i j)).symm
          _ ≤ finiteResidualSigma n H m :=
              row_sum_le_infNorm (finiteResidualSigmaMatrix n H m) i
          _ ≤ residualSigmaSup n H := le_csSup hbdd ⟨m, rfl⟩
  · exact hsup0

/-- **The literal (17.20) sigma equality** (Higham, Accuracy and Stability
    of Numerical Algorithms, 2nd ed., §17.3, eq (17.20)): the infinity norm
    of the literal entrywise `tsum` matrix series `Σ_{k=0}^∞ |H^k (I - H)|`
    EQUALS the supremum envelope `residualSigmaSup` of the finite partial
    sigma norms, under the norm certificate `‖H‖∞ ≤ q < 1`.  This closes
    the gap between the `tsum` sigma model and the `sSup`-based finite
    model used by the residual bounds of §17.3. -/
theorem infNorm_residualSigmaMatrix_eq_residualSigmaSup (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    infNorm (residualSigmaMatrix n H) = residualSigmaSup n H :=
  le_antisymm
    (infNorm_residualSigmaMatrix_le_residualSigmaSup n hn H q hq0 hq1 hH)
    (residualSigmaSup_le_infNorm_residualSigmaMatrix n hn H q hq0 hq1 hH)

-- ============================================================
-- Bridges to the `residualSigmaTsum` surface of StationaryIteration.lean
-- ============================================================

/-- The two independently developed literal sigma objects coincide: this
    module's `residualSigmaMatrix` and `StationaryIteration.lean`'s
    `residualSigmaTsumMatrix` are the same entrywise `tsum`, so the scalar
    `residualSigmaTsum` is definitionally the ∞-norm of
    `residualSigmaMatrix`. -/
theorem residualSigmaTsum_eq_infNorm_residualSigmaMatrix (n : ℕ)
    (H : Fin n → Fin n → ℝ) :
    residualSigmaTsum n H = infNorm (residualSigmaMatrix n H) := rfl

/-- **Eq (17.20), literal `tsum` sigma equals the supremum envelope**
    (Higham 2nd ed., §17.3): under a norm certificate `‖H‖∞ ≤ q < 1`, the
    scalar `residualSigmaTsum` coincides with the supremum of the finite
    partial norms `residualSigmaSup`. -/
theorem residualSigmaTsum_eq_residualSigmaSup (n : ℕ) (hn : 0 < n)
    (H : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    residualSigmaTsum n H = residualSigmaSup n H := by
  rw [residualSigmaTsum_eq_infNorm_residualSigmaMatrix]
  exact infNorm_residualSigmaMatrix_eq_residualSigmaSup n hn H q hq0 hq1 hH

/-- **Eq (17.20), q-certificate bridge for the literal diagonalizable sigma
    bound on the `tsum` object**
    (Higham 2nd ed., §17.3): with real diagonalization data `X⁻¹HX = J`
    (`|J i i| < 1`) and a norm certificate `‖H‖∞ ≤ q < 1`, the literal
    series sigma satisfies
    `residualSigmaTsum ≤ κ∞(X) · diagonalResidualRatioMax`.  Composes the
    envelope equality with the finite-partial diagonalization bound from
    `StationaryIteration.lean`. -/
theorem residualSigmaTsum_le_diagonalizable_max_bound_of_infNorm_bound
    (n : ℕ) (hn : 0 < n)
    (H X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n H X) = J)
    (hdiag : ∀ i j, i ≠ j → J i j = 0)
    (hLam : ∀ i : Fin n, |J i i| < 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hH : infNorm H ≤ q) :
    residualSigmaTsum n H ≤
      (infNorm X * infNorm X_inv) * diagonalResidualRatioMax n J hn := by
  rw [residualSigmaTsum_eq_residualSigmaSup n hn H q hq0 hq1 hH]
  exact residualSigmaSup_le_diagonalizable_max_bound n hn H X X_inv J
    hXr hXl hsim hdiag hLam

end NumStability
