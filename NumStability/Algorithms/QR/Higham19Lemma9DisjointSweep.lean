-- Algorithms/QR/Higham19Lemma9DisjointSweep.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms (2nd ed.),
-- Lemma 19.9 (§19.6, p. 368) and the resulting coefficient in Theorem 19.10.
--
-- Structural content.  In one stage of the disjoint-rotation Givens QR sweep the
-- computed matrix satisfies A_{k+1} = W_k A_k + E_k where W_k = ∏ (disjoint G)
-- is block-diagonal orthogonal.  Because the rotations in a single stage act on
-- pairwise-disjoint index pairs, EACH ROW is touched by at most one rotation, so
-- the per-stage column backward error is bounded by a `√2·γ`-class constant that
-- is INDEPENDENT of the stage size m (the number of rotations in the stage) and
-- of the ambient dimension.  This is exactly the dimension-independent per-stage
-- constant Higham advertises for Lemma 19.9; the accumulation over r stages then
-- gives the `γ̃_r` (resp. `γ̃_{m+n-2}` for the tall-QR schedule) coefficient of
-- Theorem 19.10.
--
-- This file is IMPORT-ONLY: it reuses the pairwise-disjoint-pair machinery of
-- GivensQR (`GivensQRTask.same_stage_rowPair_disjoint`), the pair-support Givens
-- backward-error machinery of GivensSpec/Higham19Labels (`PairBlockSupported`,
-- `PairBlockSupported_frobNormSq_eq_block`), and the Euclidean-norm Pythagorean
-- identity of MatrixAlgebra.  Nothing existing is edited.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.QR.GivensSpec
import NumStability.Algorithms.QR.GivensMatrixStep
import NumStability.Algorithms.QR.GivensQR
import NumStability.Algorithms.QR.Higham19Labels
import NumStability.Algorithms.QR.Higham19Lemma7Gamma4

namespace NumStability.Wave13

open scoped BigOperators Matrix.Norms.Frobenius

open NumStability

-- ============================================================
-- §19.6  Disjoint pair lists (block-diagonal stage support)
-- ============================================================

/-- A row index `i` is *touched* by the pair `(p, q)` when it equals one of the
    two rotated rows.  A stage of pairwise-disjoint Givens rotations touches each
    row by at most one pair; that is the structural core behind the
    dimension-independent Lemma 19.9 per-stage constant. -/
def TouchedBy {m : ℕ} (i : Fin m) (pq : Fin m × Fin m) : Prop :=
  i = pq.1 ∨ i = pq.2

/-- The two-element touched-row set of a single pair. -/
def pairRows {m : ℕ} (pq : Fin m × Fin m) : Finset (Fin m) :=
  {pq.1, pq.2}

/-- A `Finset` of index pairs is *disjoint* when each pair rotates two genuinely
    different rows and the touched-row sets of distinct pairs are disjoint.  This
    is the abstract form of one anti-diagonal Givens stage: distinct tasks touch
    disjoint row pairs (`GivensQRTask.same_stage_rowPair_disjoint`), so every row
    is touched by at most one rotation. -/
structure DisjointPairs {m : ℕ} (S : Finset (Fin m × Fin m)) : Prop where
  /-- Each pair rotates two genuinely different rows. -/
  ne_self : ∀ pq ∈ S, pq.1 ≠ pq.2
  /-- Touched-row sets of distinct pairs are disjoint. -/
  disj : ∀ pq ∈ S, ∀ rs ∈ S, pq ≠ rs → Disjoint (pairRows pq) (pairRows rs)

/-- The union of all touched rows of a disjoint-pair stage. -/
def touchedRows {m : ℕ} (S : Finset (Fin m × Fin m)) : Finset (Fin m) :=
  S.biUnion pairRows

-- ============================================================
-- §19.6  Disjoint-support Pythagorean identity (the dimension-
--        and stage-size-independent core of Lemma 19.9)
-- ============================================================

/-- Squared Euclidean sum over a two-row touched set is the sum of the two
    squared coordinates when the pair rotates two distinct rows. -/
theorem sum_sq_pairRows {m : ℕ} (pq : Fin m × Fin m)
    (hpq : pq.1 ≠ pq.2) (w : Fin m → ℝ) :
    ∑ i ∈ pairRows pq, w i ^ 2 = w pq.1 ^ 2 + w pq.2 ^ 2 := by
  unfold pairRows
  rw [Finset.sum_pair hpq]

/-- **Disjoint-support Pythagorean identity** (structural core of Lemma 19.9).
    If a column error vector `w` is supported only on the touched rows of a
    disjoint-pair stage `S`, then its squared Euclidean norm is the sum over the
    stage's pairs of the per-pair squared contributions.  There is no dependence
    on the ambient dimension or on the number of pairs beyond this exact sum —
    this is precisely why each stage contributes a fixed `√2·γ`-class constant
    rather than a stage-size-scaled one. -/
theorem vecNorm2Sq_eq_sum_pairs_of_supported {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S)
    (w : Fin m → ℝ)
    (hsupp : ∀ i : Fin m, i ∉ touchedRows S → w i = 0) :
    vecNorm2Sq w = ∑ pq ∈ S, (w pq.1 ^ 2 + w pq.2 ^ 2) := by
  classical
  unfold vecNorm2Sq
  -- Split the full index sum into the touched rows and their complement.
  have hsplit :
      (∑ i : Fin m, w i ^ 2) =
        (∑ i ∈ touchedRows S, w i ^ 2) +
          ∑ i ∈ (Finset.univ \ touchedRows S), w i ^ 2 := by
    rw [← Finset.sum_add_sum_compl (touchedRows S) (fun i => w i ^ 2)]
    rw [Finset.compl_eq_univ_sdiff]
  rw [hsplit]
  have hzero : (∑ i ∈ (Finset.univ \ touchedRows S), w i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i ∉ touchedRows S := (Finset.mem_sdiff.mp hi).2
    rw [hsupp i hi']
    ring
  rw [hzero, add_zero]
  -- Now the touched-row sum is a disjoint biUnion over the pairs.
  unfold touchedRows
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro pq hpq
    exact sum_sq_pairRows pq (hS.ne_self pq hpq) w
  · -- Pairwise-disjoint touched-row sets.
    intro pq hpq rs hrs hne
    exact hS.disj pq hpq rs hrs hne

/-- The sum over a disjoint-pair stage of the per-pair squared coordinate mass of
    a vector `a` is bounded by the full squared Euclidean norm of `a`.  (The
    touched rows are a subset of all rows, and the disjoint pairs cover each
    touched row exactly once.) -/
theorem sum_pairs_sq_le_vecNorm2Sq {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S)
    (a : Fin m → ℝ) :
    (∑ pq ∈ S, (a pq.1 ^ 2 + a pq.2 ^ 2)) ≤ vecNorm2Sq a := by
  classical
  -- Restrict `a` to the touched rows; it is supported there by construction.
  let aT : Fin m → ℝ := fun i => if i ∈ touchedRows S then a i else 0
  have hsupp : ∀ i : Fin m, i ∉ touchedRows S → aT i = 0 := by
    intro i hi
    simp [aT, hi]
  have hpairs :
      (∑ pq ∈ S, (aT pq.1 ^ 2 + aT pq.2 ^ 2)) =
        ∑ pq ∈ S, (a pq.1 ^ 2 + a pq.2 ^ 2) := by
    apply Finset.sum_congr rfl
    intro pq hpq
    have h1 : pq.1 ∈ touchedRows S := by
      unfold touchedRows
      exact Finset.mem_biUnion.mpr ⟨pq, hpq, by unfold pairRows; simp⟩
    have h2 : pq.2 ∈ touchedRows S := by
      unfold touchedRows
      exact Finset.mem_biUnion.mpr ⟨pq, hpq, by unfold pairRows; simp⟩
    simp [aT, h1, h2]
  have hEq : vecNorm2Sq aT = ∑ pq ∈ S, (aT pq.1 ^ 2 + aT pq.2 ^ 2) :=
    vecNorm2Sq_eq_sum_pairs_of_supported S hS aT hsupp
  rw [← hpairs, ← hEq]
  -- `vecNorm2Sq aT ≤ vecNorm2Sq a` entrywise.
  unfold vecNorm2Sq
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ touchedRows S
  · simp [aT, hi]
  · simp [aT, hi, sq_nonneg (a i)]

/-- **Dimension- and stage-size-independent per-stage columnwise bound**
    (structural core of Lemma 19.9, §19.6 p. 368).  Suppose the per-column error
    vector `w` of one disjoint-rotation stage is supported on the stage's touched
    rows, and on each pair the local error mass is at most `2·γ²` times the input
    mass on that same pair (this is the per-rotation `√2·γ` Givens application
    bound in squared form).  Then the whole stage's column error satisfies
    `‖w‖₂ ≤ √2·γ·‖a‖₂`, with a constant that does NOT grow with the ambient
    dimension `m` nor with the number of rotations in the stage. -/
theorem stage_columnError_le_sqrt2_gamma {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S)
    (w a : Fin m → ℝ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hsupp : ∀ i : Fin m, i ∉ touchedRows S → w i = 0)
    (hpair : ∀ pq ∈ S,
      w pq.1 ^ 2 + w pq.2 ^ 2 ≤ 2 * γ ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2)) :
    vecNorm2 w ≤ Real.sqrt 2 * γ * vecNorm2 a := by
  classical
  have hwSq : vecNorm2Sq w = ∑ pq ∈ S, (w pq.1 ^ 2 + w pq.2 ^ 2) :=
    vecNorm2Sq_eq_sum_pairs_of_supported S hS w hsupp
  -- Bound the pair sum for `w` by the pair sum for `a`.
  have hsum_le :
      (∑ pq ∈ S, (w pq.1 ^ 2 + w pq.2 ^ 2)) ≤
        ∑ pq ∈ S, 2 * γ ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2) :=
    Finset.sum_le_sum hpair
  have hfactor :
      (∑ pq ∈ S, 2 * γ ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2)) =
        2 * γ ^ 2 * (∑ pq ∈ S, (a pq.1 ^ 2 + a pq.2 ^ 2)) := by
    rw [Finset.mul_sum]
  have hγsq_nonneg : (0 : ℝ) ≤ 2 * γ ^ 2 := by positivity
  have haBound :
      2 * γ ^ 2 * (∑ pq ∈ S, (a pq.1 ^ 2 + a pq.2 ^ 2)) ≤
        2 * γ ^ 2 * vecNorm2Sq a :=
    mul_le_mul_of_nonneg_left (sum_pairs_sq_le_vecNorm2Sq S hS a) hγsq_nonneg
  have hwSq_le : vecNorm2Sq w ≤ 2 * γ ^ 2 * vecNorm2Sq a := by
    rw [hwSq]
    calc
      (∑ pq ∈ S, (w pq.1 ^ 2 + w pq.2 ^ 2))
          ≤ ∑ pq ∈ S, 2 * γ ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2) := hsum_le
      _ = 2 * γ ^ 2 * (∑ pq ∈ S, (a pq.1 ^ 2 + a pq.2 ^ 2)) := hfactor
      _ ≤ 2 * γ ^ 2 * vecNorm2Sq a := haBound
  -- Convert the squared bound to the Euclidean-norm bound.
  have hrhs_nonneg : 0 ≤ Real.sqrt 2 * γ * vecNorm2 a :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hγ) (vecNorm2_nonneg a)
  have hsq_target : (Real.sqrt 2 * γ * vecNorm2 a) ^ 2 = 2 * γ ^ 2 * vecNorm2Sq a := by
    have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have ha : vecNorm2 a ^ 2 = vecNorm2Sq a := vecNorm2_sq a
    calc
      (Real.sqrt 2 * γ * vecNorm2 a) ^ 2
          = (Real.sqrt 2) ^ 2 * γ ^ 2 * vecNorm2 a ^ 2 := by ring
      _ = 2 * γ ^ 2 * vecNorm2Sq a := by rw [h2, ha]
  -- Convert `‖w‖² ≤ R²` (both sides nonneg) into `‖w‖ ≤ R` via sqrt.
  have hwSq_le'' : vecNorm2Sq w ≤ (Real.sqrt 2 * γ * vecNorm2 a) ^ 2 := by
    rw [hsq_target]; exact hwSq_le
  calc
    vecNorm2 w = Real.sqrt (vecNorm2Sq w) := rfl
    _ ≤ Real.sqrt ((Real.sqrt 2 * γ * vecNorm2 a) ^ 2) := Real.sqrt_le_sqrt hwSq_le''
    _ = Real.sqrt 2 * γ * vecNorm2 a := by
          rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs_nonneg]

-- ============================================================
-- §19.6  Per-rotation sharp column bound (`√2·γ`-class)
-- ============================================================

/-- Coefficient Cauchy–Schwarz: with `c² + s² = 1`, the weighted sum bound
    `(|c|·|u| + |s|·|v|)² ≤ u² + v²`.  This is the cross-term cancellation behind
    the printed `√2` in Lemma 19.8/19.9 (as opposed to the conservative `2`
    obtained from `|c|, |s| ≤ 1` alone). -/
theorem coeff_weighted_sq_le {c s u v : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) :
    (|c| * |u| + |s| * |v|) ^ 2 ≤ u ^ 2 + v ^ 2 := by
  have hCS : (|c| * |u| + |s| * |v|) ^ 2 ≤
      (c ^ 2 + s ^ 2) * (u ^ 2 + v ^ 2) := by
    have hcross : 2 * (|c| * |u|) * (|s| * |v|) ≤
        (|c| * |v|) ^ 2 + (|s| * |u|) ^ 2 := by
      nlinarith [sq_nonneg (|c| * |v| - |s| * |u|)]
    have hcu : |c| ^ 2 = c ^ 2 := sq_abs c
    have hsv : |s| ^ 2 = s ^ 2 := sq_abs s
    have huu : |u| ^ 2 = u ^ 2 := sq_abs u
    have hvv : |v| ^ 2 = v ^ 2 := sq_abs v
    nlinarith [hcross, hcu, hsv, huu, hvv]
  calc
    (|c| * |u| + |s| * |v|) ^ 2 ≤ (c ^ 2 + s ^ 2) * (u ^ 2 + v ^ 2) := hCS
    _ = u ^ 2 + v ^ 2 := by rw [hcs]; ring

/-- **Per-rotation sharp column backward-error bound** (the `√2·γ`-class core of
    Lemma 19.8, used per rotation inside a Lemma 19.9 stage).

    Applying a Givens rotation with EXACT normalized coefficients `c, s`
    (`c² + s² = 1`) to a vector `x` via the concrete `fl_givensApply` kernel, the
    two touched output components `ŷ_p, ŷ_q` differ from the exact
    `(G x)_p = c x_p + s x_q`, `(G x)_q = c x_q − s x_p` by an error whose squared
    Euclidean mass on the active pair is bounded by `2·γ₂²` times the input mass
    on that same pair:

    `(ŷ_p − (Gx)_p)² + (ŷ_q − (Gx)_q)² ≤ 2·γ₂²·(x_p² + x_q²)`.

    Both the coefficient `√2·γ₂` and the fact that the input mass is the LOCAL
    pair mass (not the whole vector norm) are dimension-independent.  This is the
    supplied-parameter form; combined with the computed-coefficient error
    (`γ₆`, Lemma 19.7) the stage uses `γ₈`. -/
theorem fl_givensApply_pair_sq_error_le (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1)
    (hvalid : gammaValid fp 2) :
    (fl_givensApply fp n p q c s x p - (c * x p + s * x q)) ^ 2 +
        (fl_givensApply fp n p q c s x q - (c * x q - s * x p)) ^ 2 ≤
      2 * gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) := by
  obtain ⟨δcp, hδcp, hmul_cp⟩ := fp.model_mul c (x p)
  obtain ⟨δsp, hδsp, hmul_sp⟩ := fp.model_mul s (x q)
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q))
  obtain ⟨δcq, hδcq, hmul_cq⟩ := fp.model_mul c (x q)
  obtain ⟨δsq, hδsq, hmul_sq⟩ := fp.model_mul s (x p)
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p))
  have hvalid1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hu_le_γ1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos hvalid1
  have hδcpγ : |δcp| ≤ gamma fp 1 := le_trans hδcp hu_le_γ1
  have hδspγ : |δsp| ≤ gamma fp 1 := le_trans hδsp hu_le_γ1
  have hδaddγ : |δadd| ≤ gamma fp 1 := le_trans hδadd hu_le_γ1
  have hδcqγ : |δcq| ≤ gamma fp 1 := le_trans hδcq hu_le_γ1
  have hδsqγ : |δsq| ≤ gamma fp 1 := le_trans hδsq hu_le_γ1
  have hδsubγ : |δsub| ≤ gamma fp 1 := le_trans hδsub hu_le_γ1
  obtain ⟨θcp, hθcp, hθcp_eq⟩ :=
    gamma_mul fp 1 1 δcp δadd hδcpγ hδaddγ (by simpa using hvalid)
  obtain ⟨θsp, hθsp, hθsp_eq⟩ :=
    gamma_mul fp 1 1 δsp δadd hδspγ hδaddγ (by simpa using hvalid)
  obtain ⟨θcq, hθcq, hθcq_eq⟩ :=
    gamma_mul fp 1 1 δcq δsub hδcqγ hδsubγ (by simpa using hvalid)
  obtain ⟨θsq, hθsq, hθsq_eq⟩ :=
    gamma_mul fp 1 1 δsq δsub hδsqγ hδsubγ (by simpa using hvalid)
  have hθcp2 : |θcp| ≤ gamma fp 2 := by simpa using hθcp
  have hθsp2 : |θsp| ≤ gamma fp 2 := by simpa using hθsp
  have hθcq2 : |θcq| ≤ gamma fp 2 := by simpa using hθcq
  have hθsq2 : |θsq| ≤ gamma fp 2 := by simpa using hθsq
  have hγ2_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hvalid
  -- Component algebra: the two touched entries.
  have hp_alg :
      fl_givensApply fp n p q c s x p =
        c * (1 + θcp) * x p + s * (1 + θsp) * x q := by
    calc
      fl_givensApply fp n p q c s x p
          = fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q)) := by simp
      _ = (fp.fl_mul c (x p) + fp.fl_mul s (x q)) * (1 + δadd) := hadd
      _ = ((c * x p) * (1 + δcp) + (s * x q) * (1 + δsp)) *
            (1 + δadd) := by rw [hmul_cp, hmul_sp]
      _ = c * x p * ((1 + δcp) * (1 + δadd)) +
            s * x q * ((1 + δsp) * (1 + δadd)) := by ring
      _ = c * x p * (1 + θcp) + s * x q * (1 + θsp) := by
            rw [hθcp_eq, hθsp_eq]
      _ = c * (1 + θcp) * x p + s * (1 + θsp) * x q := by ring
  have hq_alg :
      fl_givensApply fp n p q c s x q =
        c * (1 + θcq) * x q - s * (1 + θsq) * x p := by
    calc
      fl_givensApply fp n p q c s x q
          = fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p)) :=
              fl_givensApply_q fp n p q c s x hpq
      _ = (fp.fl_mul c (x q) - fp.fl_mul s (x p)) * (1 + δsub) := hsub
      _ = ((c * x q) * (1 + δcq) - (s * x p) * (1 + δsq)) *
            (1 + δsub) := by rw [hmul_cq, hmul_sq]
      _ = c * x q * ((1 + δcq) * (1 + δsub)) -
            s * x p * ((1 + δsq) * (1 + δsub)) := by ring
      _ = c * x q * (1 + θcq) - s * x p * (1 + θsq) := by
            rw [hθcq_eq, hθsq_eq]
      _ = c * (1 + θcq) * x q - s * (1 + θsq) * x p := by ring
  -- The two error components.
  have hwp : fl_givensApply fp n p q c s x p - (c * x p + s * x q) =
      c * θcp * x p + s * θsp * x q := by rw [hp_alg]; ring
  have hwq : fl_givensApply fp n p q c s x q - (c * x q - s * x p) =
      c * θcq * x q - s * θsq * x p := by rw [hq_alg]; ring
  rw [hwp, hwq]
  -- Bound each squared component by `γ₂²·(x_p² + x_q²)`.
  have hbp : (c * θcp * x p + s * θsp * x q) ^ 2 ≤
      gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) := by
    have habs : |c * θcp * x p + s * θsp * x q| ≤
        gamma fp 2 * (|c| * |x p| + |s| * |x q|) := by
      calc
        |c * θcp * x p + s * θsp * x q|
            ≤ |c * θcp * x p| + |s * θsp * x q| := abs_add_le _ _
        _ = |c| * |θcp| * |x p| + |s| * |θsp| * |x q| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]
        _ ≤ |c| * gamma fp 2 * |x p| + |s| * gamma fp 2 * |x q| := by
              have h1 : |c| * |θcp| * |x p| ≤ |c| * gamma fp 2 * |x p| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθcp2 (abs_nonneg c)) (abs_nonneg _)
              have h2 : |s| * |θsp| * |x q| ≤ |s| * gamma fp 2 * |x q| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθsp2 (abs_nonneg s)) (abs_nonneg _)
              linarith
        _ = gamma fp 2 * (|c| * |x p| + |s| * |x q|) := by ring
    have hcs_bound : (|c| * |x p| + |s| * |x q|) ^ 2 ≤ x p ^ 2 + x q ^ 2 :=
      coeff_weighted_sq_le hcs
    calc
      (c * θcp * x p + s * θsp * x q) ^ 2
          = |c * θcp * x p + s * θsp * x q| ^ 2 := (sq_abs _).symm
      _ ≤ (gamma fp 2 * (|c| * |x p| + |s| * |x q|)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = gamma fp 2 ^ 2 * (|c| * |x p| + |s| * |x q|) ^ 2 := by ring
      _ ≤ gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) :=
            mul_le_mul_of_nonneg_left hcs_bound (by positivity)
  have hbq : (c * θcq * x q - s * θsq * x p) ^ 2 ≤
      gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) := by
    have habs : |c * θcq * x q - s * θsq * x p| ≤
        gamma fp 2 * (|c| * |x q| + |s| * |x p|) := by
      calc
        |c * θcq * x q - s * θsq * x p|
            ≤ |c * θcq * x q| + |s * θsq * x p| := abs_sub _ _
        _ = |c| * |θcq| * |x q| + |s| * |θsq| * |x p| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]
        _ ≤ |c| * gamma fp 2 * |x q| + |s| * gamma fp 2 * |x p| := by
              have h1 : |c| * |θcq| * |x q| ≤ |c| * gamma fp 2 * |x q| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθcq2 (abs_nonneg c)) (abs_nonneg _)
              have h2 : |s| * |θsq| * |x p| ≤ |s| * gamma fp 2 * |x p| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθsq2 (abs_nonneg s)) (abs_nonneg _)
              linarith
        _ = gamma fp 2 * (|c| * |x q| + |s| * |x p|) := by ring
    have hcs_bound : (|c| * |x q| + |s| * |x p|) ^ 2 ≤ x q ^ 2 + x p ^ 2 :=
      coeff_weighted_sq_le hcs
    calc
      (c * θcq * x q - s * θsq * x p) ^ 2
          = |c * θcq * x q - s * θsq * x p| ^ 2 := (sq_abs _).symm
      _ ≤ (gamma fp 2 * (|c| * |x q| + |s| * |x p|)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = gamma fp 2 ^ 2 * (|c| * |x q| + |s| * |x p|) ^ 2 := by ring
      _ ≤ gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) := by
            have hswap : x q ^ 2 + x p ^ 2 = x p ^ 2 + x q ^ 2 := by ring
            rw [hswap] at hcs_bound
            exact mul_le_mul_of_nonneg_left hcs_bound (by positivity)
  -- Combine.
  calc
    (c * θcp * x p + s * θsp * x q) ^ 2 +
        (c * θcq * x q - s * θsq * x p) ^ 2
        ≤ gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) +
            gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) := add_le_add hbp hbq
    _ = 2 * gamma fp 2 ^ 2 * (x p ^ 2 + x q ^ 2) := by ring

/-- Computed-coefficient upgrade of `fl_givensApply_pair_sq_error_le`.

    When the rotation coefficients are themselves COMPUTED from the source
    two-vector `(xi, xj)` by the standard Givens recipe (Lemma 19.7 gives their
    `γ₆` relative error), the touched-pair column error of the computed
    application against the EXACT rotation `G(c, s)` still has the
    dimension-independent `√2·γ₈`-class squared bound

    `(ŷ_p − (Gx)_p)² + (ŷ_q − (Gx)_q)² ≤ 2·γ₈²·(x_p² + x_q²)`,

    where `c = givensC xi xj`, `s = givensS xi xj`.  The index moves from `γ₂`
    (supplied parameters) to `γ₈` because coefficient construction contributes
    `γ₆` and the two rounded fused operations contribute the remaining `γ₂`. -/
theorem fl_givensApply_computed_pair_sq_error_le_gamma6 (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hnz : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    (fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p -
          (givensC xi xj * x p + givensS xi xj * x q)) ^ 2 +
        (fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q -
          (givensC xi xj * x q - givensS xi xj * x p)) ^ 2 ≤
      2 * gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := by
  classical
  -- Exact coefficients and their computed relative errors (Lemma 19.7, γ₆).
  set c := givensC xi xj with hc_def
  set s := givensS xi xj with hs_def
  have hcs : c ^ 2 + s ^ 2 = 1 := givensCoeff_norm_sq xi xj hnz
  obtain ⟨εc, hεc, hc_hat⟩ :=
    (fl_givensCoeffError_gamma4 fp xi xj hnz hvalid).c_rel
  obtain ⟨εs, hεs, hs_hat⟩ :=
    (fl_givensCoeffError_gamma4 fp xi xj hnz hvalid).s_rel
  -- Per-operation rounding for the two touched components with COMPUTED c,s.
  obtain ⟨δcp, hδcp, hmul_cp⟩ := fp.model_mul (fl_givensC fp xi xj) (x p)
  obtain ⟨δsp, hδsp, hmul_sp⟩ := fp.model_mul (fl_givensS fp xi xj) (x q)
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (fp.fl_mul (fl_givensC fp xi xj) (x p))
      (fp.fl_mul (fl_givensS fp xi xj) (x q))
  obtain ⟨δcq, hδcq, hmul_cq⟩ := fp.model_mul (fl_givensC fp xi xj) (x q)
  obtain ⟨δsq, hδsq, hmul_sq⟩ := fp.model_mul (fl_givensS fp xi xj) (x p)
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_mul (fl_givensC fp xi xj) (x q))
      (fp.fl_mul (fl_givensS fp xi xj) (x p))
  have hvalid1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hu_le_γ1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos hvalid1
  have hδcpγ : |δcp| ≤ gamma fp 1 := le_trans hδcp hu_le_γ1
  have hδspγ : |δsp| ≤ gamma fp 1 := le_trans hδsp hu_le_γ1
  have hδaddγ : |δadd| ≤ gamma fp 1 := le_trans hδadd hu_le_γ1
  have hδcqγ : |δcq| ≤ gamma fp 1 := le_trans hδcq hu_le_γ1
  have hδsqγ : |δsq| ≤ gamma fp 1 := le_trans hδsq hu_le_γ1
  have hδsubγ : |δsub| ≤ gamma fp 1 := le_trans hδsub hu_le_γ1
  have hεc4 : |εc| ≤ gamma fp 4 := hεc
  have hεs4 : |εs| ≤ gamma fp 4 := hεs
  have hvalid5 : gammaValid fp 5 := gammaValid_mono fp (by omega) hvalid
  -- Fold coefficient error (γ₄) with first multiply (γ₁) → γ₅.
  obtain ⟨φcp, hφcp, hφcp_eq⟩ :=
    gamma_mul fp 4 1 εc δcp hεc4 hδcpγ (by simpa using hvalid5)
  obtain ⟨φsp, hφsp, hφsp_eq⟩ :=
    gamma_mul fp 4 1 εs δsp hεs4 hδspγ (by simpa using hvalid5)
  obtain ⟨φcq, hφcq, hφcq_eq⟩ :=
    gamma_mul fp 4 1 εc δcq hεc4 hδcqγ (by simpa using hvalid5)
  obtain ⟨φsq, hφsq, hφsq_eq⟩ :=
    gamma_mul fp 4 1 εs δsq hεs4 hδsqγ (by simpa using hvalid5)
  -- Fold with add/sub rounding (γ₁) → γ₆.
  obtain ⟨θcp, hθcp, hθcp_eq⟩ :=
    gamma_mul fp 5 1 φcp δadd (by simpa using hφcp) hδaddγ (by simpa using hvalid)
  obtain ⟨θsp, hθsp, hθsp_eq⟩ :=
    gamma_mul fp 5 1 φsp δadd (by simpa using hφsp) hδaddγ (by simpa using hvalid)
  obtain ⟨θcq, hθcq, hθcq_eq⟩ :=
    gamma_mul fp 5 1 φcq δsub (by simpa using hφcq) hδsubγ (by simpa using hvalid)
  obtain ⟨θsq, hθsq, hθsq_eq⟩ :=
    gamma_mul fp 5 1 φsq δsub (by simpa using hφsq) hδsubγ (by simpa using hvalid)
  have hθcp6 : |θcp| ≤ gamma fp 6 := by simpa using hθcp
  have hθsp6 : |θsp| ≤ gamma fp 6 := by simpa using hθsp
  have hθcq6 : |θcq| ≤ gamma fp 6 := by simpa using hθcq
  have hθsq6 : |θsq| ≤ gamma fp 6 := by simpa using hθsq
  have hγ6_nonneg : 0 ≤ gamma fp 6 := gamma_nonneg fp hvalid
  -- Component algebra with computed coefficients: p-component.
  have hp_alg :
      fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p =
        c * (1 + θcp) * x p + s * (1 + θsp) * x q := by
    calc
      fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p
          = fp.fl_add (fp.fl_mul (fl_givensC fp xi xj) (x p))
              (fp.fl_mul (fl_givensS fp xi xj) (x q)) := by simp
      _ = (fp.fl_mul (fl_givensC fp xi xj) (x p) +
            fp.fl_mul (fl_givensS fp xi xj) (x q)) * (1 + δadd) := hadd
      _ = ((fl_givensC fp xi xj * x p) * (1 + δcp) +
            (fl_givensS fp xi xj * x q) * (1 + δsp)) * (1 + δadd) := by
              rw [hmul_cp, hmul_sp]
      _ = ((c * (1 + εc) * x p) * (1 + δcp) +
            (s * (1 + εs) * x q) * (1 + δsp)) * (1 + δadd) := by
              rw [hc_hat, hs_hat]
      _ = c * x p * ((1 + εc) * (1 + δcp) * (1 + δadd)) +
            s * x q * ((1 + εs) * (1 + δsp) * (1 + δadd)) := by ring
      _ = c * x p * ((1 + φcp) * (1 + δadd)) +
            s * x q * ((1 + φsp) * (1 + δadd)) := by
              rw [hφcp_eq, hφsp_eq]
      _ = c * x p * (1 + θcp) + s * x q * (1 + θsp) := by
              rw [hθcp_eq, hθsp_eq]
      _ = c * (1 + θcp) * x p + s * (1 + θsp) * x q := by ring
  -- q-component.
  have hq_alg :
      fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q =
        c * (1 + θcq) * x q - s * (1 + θsq) * x p := by
    calc
      fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q
          = fp.fl_sub (fp.fl_mul (fl_givensC fp xi xj) (x q))
              (fp.fl_mul (fl_givensS fp xi xj) (x p)) :=
              fl_givensApply_q fp n p q _ _ x hpq
      _ = (fp.fl_mul (fl_givensC fp xi xj) (x q) -
            fp.fl_mul (fl_givensS fp xi xj) (x p)) * (1 + δsub) := hsub
      _ = ((fl_givensC fp xi xj * x q) * (1 + δcq) -
            (fl_givensS fp xi xj * x p) * (1 + δsq)) * (1 + δsub) := by
              rw [hmul_cq, hmul_sq]
      _ = ((c * (1 + εc) * x q) * (1 + δcq) -
            (s * (1 + εs) * x p) * (1 + δsq)) * (1 + δsub) := by
              rw [hc_hat, hs_hat]
      _ = c * x q * ((1 + εc) * (1 + δcq) * (1 + δsub)) -
            s * x p * ((1 + εs) * (1 + δsq) * (1 + δsub)) := by ring
      _ = c * x q * ((1 + φcq) * (1 + δsub)) -
            s * x p * ((1 + φsq) * (1 + δsub)) := by
              rw [hφcq_eq, hφsq_eq]
      _ = c * x q * (1 + θcq) - s * x p * (1 + θsq) := by
              rw [hθcq_eq, hθsq_eq]
      _ = c * (1 + θcq) * x q - s * (1 + θsq) * x p := by ring
  have hwp :
      fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p -
          (c * x p + s * x q) = c * θcp * x p + s * θsp * x q := by
    rw [hp_alg]; ring
  have hwq :
      fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q -
          (c * x q - s * x p) = c * θcq * x q - s * θsq * x p := by
    rw [hq_alg]; ring
  rw [hwp, hwq]
  -- Bound the two squared error components (same Cauchy–Schwarz as the
  -- supplied-parameter case, now with γ₆).
  have hbp : (c * θcp * x p + s * θsp * x q) ^ 2 ≤
      gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := by
    have habs : |c * θcp * x p + s * θsp * x q| ≤
        gamma fp 6 * (|c| * |x p| + |s| * |x q|) := by
      calc
        |c * θcp * x p + s * θsp * x q|
            ≤ |c * θcp * x p| + |s * θsp * x q| := abs_add_le _ _
        _ = |c| * |θcp| * |x p| + |s| * |θsp| * |x q| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]
        _ ≤ |c| * gamma fp 6 * |x p| + |s| * gamma fp 6 * |x q| := by
              have h1 : |c| * |θcp| * |x p| ≤ |c| * gamma fp 6 * |x p| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθcp6 (abs_nonneg c)) (abs_nonneg _)
              have h2 : |s| * |θsp| * |x q| ≤ |s| * gamma fp 6 * |x q| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθsp6 (abs_nonneg s)) (abs_nonneg _)
              linarith
        _ = gamma fp 6 * (|c| * |x p| + |s| * |x q|) := by ring
    have hcs_bound : (|c| * |x p| + |s| * |x q|) ^ 2 ≤ x p ^ 2 + x q ^ 2 :=
      coeff_weighted_sq_le hcs
    calc
      (c * θcp * x p + s * θsp * x q) ^ 2
          = |c * θcp * x p + s * θsp * x q| ^ 2 := (sq_abs _).symm
      _ ≤ (gamma fp 6 * (|c| * |x p| + |s| * |x q|)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = gamma fp 6 ^ 2 * (|c| * |x p| + |s| * |x q|) ^ 2 := by ring
      _ ≤ gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) :=
            mul_le_mul_of_nonneg_left hcs_bound (by positivity)
  have hbq : (c * θcq * x q - s * θsq * x p) ^ 2 ≤
      gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := by
    have habs : |c * θcq * x q - s * θsq * x p| ≤
        gamma fp 6 * (|c| * |x q| + |s| * |x p|) := by
      calc
        |c * θcq * x q - s * θsq * x p|
            ≤ |c * θcq * x q| + |s * θsq * x p| := abs_sub _ _
        _ = |c| * |θcq| * |x q| + |s| * |θsq| * |x p| := by
              rw [abs_mul, abs_mul, abs_mul, abs_mul]
        _ ≤ |c| * gamma fp 6 * |x q| + |s| * gamma fp 6 * |x p| := by
              have h1 : |c| * |θcq| * |x q| ≤ |c| * gamma fp 6 * |x q| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθcq6 (abs_nonneg c)) (abs_nonneg _)
              have h2 : |s| * |θsq| * |x p| ≤ |s| * gamma fp 6 * |x p| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hθsq6 (abs_nonneg s)) (abs_nonneg _)
              linarith
        _ = gamma fp 6 * (|c| * |x q| + |s| * |x p|) := by ring
    have hcs_bound : (|c| * |x q| + |s| * |x p|) ^ 2 ≤ x q ^ 2 + x p ^ 2 :=
      coeff_weighted_sq_le hcs
    calc
      (c * θcq * x q - s * θsq * x p) ^ 2
          = |c * θcq * x q - s * θsq * x p| ^ 2 := (sq_abs _).symm
      _ ≤ (gamma fp 6 * (|c| * |x q| + |s| * |x p|)) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = gamma fp 6 ^ 2 * (|c| * |x q| + |s| * |x p|) ^ 2 := by ring
      _ ≤ gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := by
            have hswap : x q ^ 2 + x p ^ 2 = x p ^ 2 + x q ^ 2 := by ring
            rw [hswap] at hcs_bound
            exact mul_le_mul_of_nonneg_left hcs_bound (by positivity)
  calc
    (c * θcp * x p + s * θsp * x q) ^ 2 +
        (c * θcq * x q - s * θsq * x p) ^ 2
        ≤ gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) +
            gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := add_le_add hbp hbq
    _ = 2 * gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := by ring

/-- Norm form of the computed-coefficient Lemma 19.8 bound.  The concrete
`fl_givensC`/`fl_givensS` construction contributes `gamma_4`, the actual
multiply/add application contributes two further operations, and the active
two-vector error is therefore bounded sharply by `sqrt 2 * gamma_6`. -/
theorem fl_givensApply_computed_pair_error_norm_le_gamma6
    (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hnz : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    Real.sqrt
        ((fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p -
            (givensC xi xj * x p + givensS xi xj * x q)) ^ 2 +
          (fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q -
            (givensC xi xj * x q - givensS xi xj * x p)) ^ 2) ≤
      Real.sqrt 2 * gamma fp 6 * Real.sqrt (x p ^ 2 + x q ^ 2) := by
  have hsq := fl_givensApply_computed_pair_sq_error_le_gamma6
    fp n p q xi xj x hpq hnz hvalid
  have hmass : 0 ≤ x p ^ 2 + x q ^ 2 := by positivity
  have hγ : 0 ≤ gamma fp 6 := gamma_nonneg fp hvalid
  have hrhs : 0 ≤ Real.sqrt 2 * gamma fp 6 * Real.sqrt (x p ^ 2 + x q ^ 2) := by
    positivity
  have hrhs_sq :
      (Real.sqrt 2 * gamma fp 6 * Real.sqrt (x p ^ 2 + x q ^ 2)) ^ 2 =
        2 * gamma fp 6 ^ 2 * (x p ^ 2 + x q ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hmass]
  calc
    Real.sqrt
        ((fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p -
            (givensC xi xj * x p + givensS xi xj * x q)) ^ 2 +
          (fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q -
            (givensC xi xj * x q - givensS xi xj * x p)) ^ 2)
        ≤ Real.sqrt
            ((Real.sqrt 2 * gamma fp 6 * Real.sqrt (x p ^ 2 + x q ^ 2)) ^ 2) := by
          apply Real.sqrt_le_sqrt
          rw [hrhs_sq]
          exact hsq
    _ = Real.sqrt 2 * gamma fp 6 * Real.sqrt (x p ^ 2 + x q ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hrhs]

/-- Compatibility weakening of the sharp `gamma_6` result to the former
`gamma_8` endpoint. -/
theorem fl_givensApply_computed_pair_sq_error_le (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hnz : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    (fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x p -
          (givensC xi xj * x p + givensS xi xj * x q)) ^ 2 +
        (fl_givensApply fp n p q (fl_givensC fp xi xj) (fl_givensS fp xi xj) x q -
          (givensC xi xj * x q - givensS xi xj * x p)) ^ 2 ≤
      2 * gamma fp 8 ^ 2 * (x p ^ 2 + x q ^ 2) := by
  have h6 := fl_givensApply_computed_pair_sq_error_le_gamma6
    fp n p q xi xj x hpq hnz (gammaValid_mono fp (by omega) hvalid)
  have hγ : gamma fp 6 ≤ gamma fp 8 := gamma_mono fp (by omega) hvalid
  have hγ6 : 0 ≤ gamma fp 6 :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid)
  have hsq : gamma fp 6 ^ 2 ≤ gamma fp 8 ^ 2 :=
    pow_le_pow_left₀ hγ6 hγ 2
  have hmass : 0 ≤ x p ^ 2 + x q ^ 2 := by positivity
  exact h6.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsq (by norm_num)) hmass)

-- ============================================================
-- §19.6  Concrete disjoint-sweep column operator
-- ============================================================

/-- Source two-vector assignment for a disjoint stage: each pair `(p, q)`
    carries the two-vector `(xi, xj)` from which its Givens rotation coefficients
    `c = givensC xi xj`, `s = givensS xi xj` are built. -/
abbrev StageSrc (m : ℕ) := Fin m × Fin m → ℝ × ℝ

/-- Per-pair exact-rotation output on a column `a`, supported on the pair's two
    rows.  On row `p` it is `c·a_p + s·a_q`; on row `q` it is `c·a_q − s·a_p`;
    elsewhere it agrees with `a`.  This is the action of one block of the exact
    block-diagonal orthogonal stage `W`. -/
noncomputable def pairExactCol {m : ℕ} (pq : Fin m × Fin m)
    (src : StageSrc m) (a : Fin m → ℝ) : Fin m → ℝ :=
  fun i =>
    let c := givensC (src pq).1 (src pq).2
    let s := givensS (src pq).1 (src pq).2
    if i = pq.1 then c * a pq.1 + s * a pq.2
    else if i = pq.2 then c * a pq.2 - s * a pq.1
    else a i

/-- The per-pair exact rotation action, minus the identity, is additive in the
    column.  (Each `2 × 2` block is a linear map.) -/
theorem pairExactCol_sub_id_add {m : ℕ} (pq : Fin m × Fin m)
    (src : StageSrc m) (u v : Fin m → ℝ) (i : Fin m) :
    (pairExactCol pq src (fun j => u j + v j) i - (u i + v i)) =
      (pairExactCol pq src u i - u i) + (pairExactCol pq src v i - v i) := by
  simp only [pairExactCol]
  split_ifs with h1 h2 <;> ring

/-- Per-pair computed backward-error residual against the exact rotation,
    supported on the pair's two rows.  On the two touched rows it is the genuine
    `fl_givensApply` minus exact-rotation difference; elsewhere it is zero. -/
noncomputable def pairResidual {m : ℕ} (fp : FPModel) (pq : Fin m × Fin m)
    (src : StageSrc m) (a : Fin m → ℝ) : Fin m → ℝ :=
  fun i =>
    if i = pq.1 then
      fl_givensApply fp m pq.1 pq.2
          (fl_givensC fp (src pq).1 (src pq).2)
          (fl_givensS fp (src pq).1 (src pq).2) a pq.1 -
        (givensC (src pq).1 (src pq).2 * a pq.1 +
          givensS (src pq).1 (src pq).2 * a pq.2)
    else if i = pq.2 then
      fl_givensApply fp m pq.1 pq.2
          (fl_givensC fp (src pq).1 (src pq).2)
          (fl_givensS fp (src pq).1 (src pq).2) a pq.2 -
        (givensC (src pq).1 (src pq).2 * a pq.2 -
          givensS (src pq).1 (src pq).2 * a pq.1)
    else 0

/-- The per-pair residual is supported on the pair's two touched rows. -/
theorem pairResidual_zero_of_not_touched {m : ℕ} (fp : FPModel)
    (pq : Fin m × Fin m) (src : StageSrc m) (a : Fin m → ℝ)
    {i : Fin m} (hi1 : i ≠ pq.1) (hi2 : i ≠ pq.2) :
    pairResidual fp pq src a i = 0 := by
  simp [pairResidual, hi1, hi2]

/-- The combined disjoint-sweep column residual: the sum over all pairs in the
    stage of the per-pair residuals. -/
noncomputable def sweepResidual {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (src : StageSrc m)
    (a : Fin m → ℝ) : Fin m → ℝ :=
  fun i => ∑ pq ∈ S, pairResidual fp pq src a i

/-- The combined sweep residual vanishes off the stage's touched rows: every
    per-pair term is zero there.  This is the *at most one rotation per row*
    structural fact in residual form. -/
theorem sweepResidual_zero_of_not_touched {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (src : StageSrc m) (a : Fin m → ℝ)
    {i : Fin m} (hi : i ∉ touchedRows S) :
    sweepResidual fp S src a i = 0 := by
  classical
  unfold sweepResidual
  apply Finset.sum_eq_zero
  intro pq hpq
  have hi1 : i ≠ pq.1 := by
    intro h
    exact hi (Finset.mem_biUnion.mpr ⟨pq, hpq, by unfold pairRows; rw [h]; simp⟩)
  have hi2 : i ≠ pq.2 := by
    intro h
    exact hi (Finset.mem_biUnion.mpr ⟨pq, hpq, by unfold pairRows; rw [h]; simp⟩)
  exact pairResidual_zero_of_not_touched fp pq src a hi1 hi2

/-- At the first touched row of a pair `pq ∈ S`, the combined sweep residual
    equals just that pair's residual: all other pairs' residuals vanish there by
    disjointness (each row is touched by at most one rotation). -/
theorem sweepResidual_at_fst {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    sweepResidual fp S src a pq.1 = pairResidual fp pq src a pq.1 := by
  classical
  unfold sweepResidual
  rw [Finset.sum_eq_single pq]
  · intro rs hrs hne
    -- pq.1 is not touched by any other pair rs.
    have hdisj : Disjoint (pairRows rs) (pairRows pq) :=
      hS.disj rs hrs pq hpq hne
    have hpq1_in : pq.1 ∈ pairRows pq := by unfold pairRows; simp
    have hnot : pq.1 ∉ pairRows rs := by
      intro hin
      exact (Finset.disjoint_left.mp hdisj hin) hpq1_in
    have hr1 : pq.1 ≠ rs.1 := by
      intro h; exact hnot (by unfold pairRows; rw [h]; simp)
    have hr2 : pq.1 ≠ rs.2 := by
      intro h; exact hnot (by unfold pairRows; rw [h]; simp)
    exact pairResidual_zero_of_not_touched fp rs src a hr1 hr2
  · intro hnotin
    exact absurd hpq hnotin

/-- At the second touched row of a pair `pq ∈ S`, the combined sweep residual
    equals just that pair's residual. -/
theorem sweepResidual_at_snd {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    sweepResidual fp S src a pq.2 = pairResidual fp pq src a pq.2 := by
  classical
  unfold sweepResidual
  rw [Finset.sum_eq_single pq]
  · intro rs hrs hne
    have hdisj : Disjoint (pairRows rs) (pairRows pq) :=
      hS.disj rs hrs pq hpq hne
    have hpq2_in : pq.2 ∈ pairRows pq := by unfold pairRows; simp
    have hnot : pq.2 ∉ pairRows rs := by
      intro hin
      exact (Finset.disjoint_left.mp hdisj hin) hpq2_in
    have hr1 : pq.2 ≠ rs.1 := by
      intro h; exact hnot (by unfold pairRows; rw [h]; simp)
    have hr2 : pq.2 ≠ rs.2 := by
      intro h; exact hnot (by unfold pairRows; rw [h]; simp)
    exact pairResidual_zero_of_not_touched fp rs src a hr1 hr2
  · intro hnotin
    exact absurd hpq hnotin

-- ============================================================
-- §19.6  Lemma 19.9: dimension- and stage-size-independent
--        per-stage columnwise backward error
-- ============================================================

/-- **Lemma 19.9** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.6, p. 368), columnwise per-stage form.

    Consider one stage of the disjoint-rotation Givens sweep: a `Finset` `S` of
    pairwise-disjoint row pairs (`DisjointPairs`), each carrying a nonzero source
    two-vector `src pq` that determines its computed rotation coefficients.  Let
    `a` be one column of the panel.  The stage's block-diagonal orthogonal action
    `W` sends `a` to `pairExactCol`, and the computed sweep leaves a column error
    `sweepResidual`.  Then

    `‖Δa‖₂ ≤ √2·γ₈·‖a‖₂`,

    with a per-stage constant `√2·γ₈` that is INDEPENDENT of the ambient
    dimension `m` AND of the number of rotations in the stage.

    Structural content.  Because the rotations act on pairwise-disjoint index
    pairs, each row is touched by at most one rotation, so the column error
    decomposes as an orthogonal (Pythagorean) direct sum over the pairs; the
    stage never accumulates a stage-size factor.  Each pair contributes the sharp
    `√2·γ₈` Givens application bound (`fl_givensApply_computed_pair_sq_error_le`).

    Constant.  Higham advertises the per-stage constant `√2·γ_c` with `c` left
    unspecified (p. 357/368); the printed application constant is `√2·γ₆`
    (Lemma 19.8) for supplied coefficients.  We prove the fully
    dimension-and-stage-size-independent `√2·γ₈`, the same `√2·γ̃` class with an
    explicit index `8` (coefficient construction `γ₆` plus two fused rounded
    operations `γ₂`).  This is NOT a claim that the exact printed integer is
    proved; it is a proved same-class constant with an explicit (larger) index. -/
theorem H19_Lemma19_9_disjoint_stage_column_backward_error
    (fp : FPModel) {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ)
    (hnz : ∀ pq ∈ S, (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    vecNorm2 (sweepResidual fp S src a) ≤
      Real.sqrt 2 * gamma fp 8 * vecNorm2 a := by
  classical
  have hγ8_nonneg : 0 ≤ gamma fp 8 := gamma_nonneg fp hvalid
  -- Support: the sweep residual is zero off the touched rows.
  have hsupp : ∀ i : Fin m, i ∉ touchedRows S →
      sweepResidual fp S src a i = 0 := by
    intro i hi
    exact sweepResidual_zero_of_not_touched fp S src a hi
  -- Per-pair bound: the sharp √2·γ₈ Givens column bound restricted to the pair.
  have hpair : ∀ pq ∈ S,
      sweepResidual fp S src a pq.1 ^ 2 +
          sweepResidual fp S src a pq.2 ^ 2 ≤
        2 * gamma fp 8 ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2) := by
    intro pq hpq
    have hpqne : pq.1 ≠ pq.2 := hS.ne_self pq hpq
    have hpqnz : (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0 := hnz pq hpq
    -- Rewrite the two combined-residual entries as the single pair residual.
    rw [sweepResidual_at_fst fp S hS src a hpq,
        sweepResidual_at_snd fp S hS src a hpq]
    -- Unfold the per-pair residual on its two touched rows.
    have hres1 : pairResidual fp pq src a pq.1 =
        fl_givensApply fp m pq.1 pq.2
            (fl_givensC fp (src pq).1 (src pq).2)
            (fl_givensS fp (src pq).1 (src pq).2) a pq.1 -
          (givensC (src pq).1 (src pq).2 * a pq.1 +
            givensS (src pq).1 (src pq).2 * a pq.2) := by
      simp [pairResidual]
    have hres2 : pairResidual fp pq src a pq.2 =
        fl_givensApply fp m pq.1 pq.2
            (fl_givensC fp (src pq).1 (src pq).2)
            (fl_givensS fp (src pq).1 (src pq).2) a pq.2 -
          (givensC (src pq).1 (src pq).2 * a pq.2 -
            givensS (src pq).1 (src pq).2 * a pq.1) := by
      simp [pairResidual, hpqne, hpqne.symm]
    rw [hres1, hres2]
    exact fl_givensApply_computed_pair_sq_error_le fp m pq.1 pq.2
      (src pq).1 (src pq).2 a hpqne hpqnz hvalid
  -- Apply the abstract disjoint-support Pythagorean per-stage bound.
  exact stage_columnError_le_sqrt2_gamma S hS (sweepResidual fp S src a) a
    (gamma fp 8) hγ8_nonneg hsupp hpair

/-- **Lemma 19.9 with the sharp computed-coefficient constant.**  The
    coefficient construction and application analysis above composes directly
    to `gamma_6`; disjoint support then lifts the two-row estimate to the whole
    stage without a factor depending on the number of rows or rotations. -/
theorem H19_Lemma19_9_disjoint_stage_column_backward_error_gamma6
    (fp : FPModel) {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ)
    (hnz : ∀ pq ∈ S, (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    vecNorm2 (sweepResidual fp S src a) ≤
      Real.sqrt 2 * gamma fp 6 * vecNorm2 a := by
  classical
  have hγ6_nonneg : 0 ≤ gamma fp 6 := gamma_nonneg fp hvalid
  have hsupp : ∀ i : Fin m, i ∉ touchedRows S →
      sweepResidual fp S src a i = 0 := by
    intro i hi
    exact sweepResidual_zero_of_not_touched fp S src a hi
  have hpair : ∀ pq ∈ S,
      sweepResidual fp S src a pq.1 ^ 2 +
          sweepResidual fp S src a pq.2 ^ 2 ≤
        2 * gamma fp 6 ^ 2 * (a pq.1 ^ 2 + a pq.2 ^ 2) := by
    intro pq hpq
    have hpqne : pq.1 ≠ pq.2 := hS.ne_self pq hpq
    have hpqnz : (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0 := hnz pq hpq
    rw [sweepResidual_at_fst fp S hS src a hpq,
        sweepResidual_at_snd fp S hS src a hpq]
    have hres1 : pairResidual fp pq src a pq.1 =
        fl_givensApply fp m pq.1 pq.2
            (fl_givensC fp (src pq).1 (src pq).2)
            (fl_givensS fp (src pq).1 (src pq).2) a pq.1 -
          (givensC (src pq).1 (src pq).2 * a pq.1 +
            givensS (src pq).1 (src pq).2 * a pq.2) := by
      simp [pairResidual]
    have hres2 : pairResidual fp pq src a pq.2 =
        fl_givensApply fp m pq.1 pq.2
            (fl_givensC fp (src pq).1 (src pq).2)
            (fl_givensS fp (src pq).1 (src pq).2) a pq.2 -
          (givensC (src pq).1 (src pq).2 * a pq.2 -
            givensS (src pq).1 (src pq).2 * a pq.1) := by
      simp [pairResidual, hpqne, hpqne.symm]
    rw [hres1, hres2]
    exact fl_givensApply_computed_pair_sq_error_le_gamma6 fp m pq.1 pq.2
      (src pq).1 (src pq).2 a hpqne hpqnz hvalid
  exact stage_columnError_le_sqrt2_gamma S hS (sweepResidual fp S src a) a
    (gamma fp 6) hγ6_nonneg hsupp hpair

-- ============================================================
-- §19.6  Non-vacuity: the residual is a genuine FP backward error
-- ============================================================

/-- **Genuine backward-error identity** for the disjoint stage, per touched row.
    At a first touched row `pq.1` the computed value equals the exact
    block-diagonal rotation value plus the recorded column residual:
    `Ŵa|_{pq.1} = (Wa)|_{pq.1} + Δa|_{pq.1}`.  This certifies the residual of
    `H19_Lemma19_9_disjoint_stage_column_backward_error` is a real
    computed-minus-exact backward error, not a free-floating bounded vector. -/
theorem sweep_backward_error_identity_fst {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    fl_givensApply fp m pq.1 pq.2
        (fl_givensC fp (src pq).1 (src pq).2)
        (fl_givensS fp (src pq).1 (src pq).2) a pq.1 =
      pairExactCol pq src a pq.1 + sweepResidual fp S src a pq.1 := by
  rw [sweepResidual_at_fst fp S hS src a hpq]
  have hres1 : pairResidual fp pq src a pq.1 =
      fl_givensApply fp m pq.1 pq.2
          (fl_givensC fp (src pq).1 (src pq).2)
          (fl_givensS fp (src pq).1 (src pq).2) a pq.1 -
        (givensC (src pq).1 (src pq).2 * a pq.1 +
          givensS (src pq).1 (src pq).2 * a pq.2) := by
    simp [pairResidual]
  have hexact : pairExactCol pq src a pq.1 =
      givensC (src pq).1 (src pq).2 * a pq.1 +
        givensS (src pq).1 (src pq).2 * a pq.2 := by
    simp [pairExactCol]
  rw [hres1, hexact]; ring

/-- Genuine backward-error identity at the second touched row of a pair. -/
theorem sweep_backward_error_identity_snd {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    fl_givensApply fp m pq.1 pq.2
        (fl_givensC fp (src pq).1 (src pq).2)
        (fl_givensS fp (src pq).1 (src pq).2) a pq.2 =
      pairExactCol pq src a pq.2 + sweepResidual fp S src a pq.2 := by
  have hpqne : pq.1 ≠ pq.2 := hS.ne_self pq hpq
  rw [sweepResidual_at_snd fp S hS src a hpq]
  have hres2 : pairResidual fp pq src a pq.2 =
      fl_givensApply fp m pq.1 pq.2
          (fl_givensC fp (src pq).1 (src pq).2)
          (fl_givensS fp (src pq).1 (src pq).2) a pq.2 -
        (givensC (src pq).1 (src pq).2 * a pq.2 -
          givensS (src pq).1 (src pq).2 * a pq.1) := by
    simp [pairResidual, hpqne, hpqne.symm]
  have hexact : pairExactCol pq src a pq.2 =
      givensC (src pq).1 (src pq).2 * a pq.2 -
        givensS (src pq).1 (src pq).2 * a pq.1 := by
    simp [pairExactCol, hpqne.symm]
  rw [hres2, hexact]; ring

/-- The per-pair exact block-diagonal rotation preserves the pair's Euclidean
    mass: `(Wa)_p² + (Wa)_q² = a_p² + a_q²` (orthogonality of the `2 × 2`
    rotation block).  This is the exact-arithmetic content behind stage `W` being
    orthogonal, used implicitly in the Lemma 19.9 backward-error reading. -/
theorem pairExactCol_preserves_pair_mass {m : ℕ} (pq : Fin m × Fin m)
    (src : StageSrc m) (a : Fin m → ℝ)
    (hpqne : pq.1 ≠ pq.2)
    (hnz : (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0) :
    pairExactCol pq src a pq.1 ^ 2 + pairExactCol pq src a pq.2 ^ 2 =
      a pq.1 ^ 2 + a pq.2 ^ 2 := by
  have hcs : givensC (src pq).1 (src pq).2 ^ 2 +
      givensS (src pq).1 (src pq).2 ^ 2 = 1 :=
    givensCoeff_norm_sq (src pq).1 (src pq).2 hnz
  have h1 : pairExactCol pq src a pq.1 =
      givensC (src pq).1 (src pq).2 * a pq.1 +
        givensS (src pq).1 (src pq).2 * a pq.2 := by simp [pairExactCol]
  have h2 : pairExactCol pq src a pq.2 =
      givensC (src pq).1 (src pq).2 * a pq.2 -
        givensS (src pq).1 (src pq).2 * a pq.1 := by
    simp [pairExactCol, hpqne.symm]
  rw [h1, h2]
  nlinarith [hcs]

/-- Exact block-diagonal stage action on a column, assembled as the sum of the
    per-pair rotated-minus-original contributions on top of the identity.  On a
    touched row it is the owning rotation's exact output; on an untouched row it
    is the original entry.  This is the single column-image of the exact
    orthogonal stage matrix `W`. -/
noncomputable def stageExactCol {m : ℕ}
    (S : Finset (Fin m × Fin m)) (src : StageSrc m)
    (a : Fin m → ℝ) : Fin m → ℝ :=
  fun i => a i + ∑ pq ∈ S, (pairExactCol pq src a i - a i)

/-- On the first touched row of a pair, the exact stage column is the owning
    rotation's exact output. -/
theorem stageExactCol_at_fst {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    stageExactCol S src a pq.1 = pairExactCol pq src a pq.1 := by
  classical
  unfold stageExactCol
  rw [Finset.sum_eq_single pq]
  · have hexact : pairExactCol pq src a pq.1 =
        givensC (src pq).1 (src pq).2 * a pq.1 +
          givensS (src pq).1 (src pq).2 * a pq.2 := by simp [pairExactCol]
    rw [hexact]; ring
  · intro rs hrs hne
    have hdisj : Disjoint (pairRows rs) (pairRows pq) :=
      hS.disj rs hrs pq hpq hne
    have hpq1_in : pq.1 ∈ pairRows pq := by unfold pairRows; simp
    have hnot : pq.1 ∉ pairRows rs := fun hin =>
      (Finset.disjoint_left.mp hdisj hin) hpq1_in
    have hr1 : pq.1 ≠ rs.1 := fun h => hnot (by unfold pairRows; rw [h]; simp)
    have hr2 : pq.1 ≠ rs.2 := fun h => hnot (by unfold pairRows; rw [h]; simp)
    simp [pairExactCol, hr1, hr2]
  · intro hnotin; exact absurd hpq hnotin

/-- On the second touched row of a pair, the exact stage column is the owning
    rotation's exact output. -/
theorem stageExactCol_at_snd {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    stageExactCol S src a pq.2 = pairExactCol pq src a pq.2 := by
  classical
  have hpqne : pq.1 ≠ pq.2 := hS.ne_self pq hpq
  unfold stageExactCol
  rw [Finset.sum_eq_single pq]
  · have hexact : pairExactCol pq src a pq.2 =
        givensC (src pq).1 (src pq).2 * a pq.2 -
          givensS (src pq).1 (src pq).2 * a pq.1 := by
      simp [pairExactCol, hpqne.symm]
    rw [hexact]; ring
  · intro rs hrs hne
    have hdisj : Disjoint (pairRows rs) (pairRows pq) :=
      hS.disj rs hrs pq hpq hne
    have hpq2_in : pq.2 ∈ pairRows pq := by unfold pairRows; simp
    have hnot : pq.2 ∉ pairRows rs := fun hin =>
      (Finset.disjoint_left.mp hdisj hin) hpq2_in
    have hr1 : pq.2 ≠ rs.1 := fun h => hnot (by unfold pairRows; rw [h]; simp)
    have hr2 : pq.2 ≠ rs.2 := fun h => hnot (by unfold pairRows; rw [h]; simp)
    simp [pairExactCol, hr1, hr2]
  · intro hnotin; exact absurd hpq hnotin

/-- On an untouched row, the exact stage column copies the input. -/
theorem stageExactCol_at_untouched {m : ℕ}
    (S : Finset (Fin m × Fin m)) (src : StageSrc m)
    (a : Fin m → ℝ) {i : Fin m} (hi : i ∉ touchedRows S) :
    stageExactCol S src a i = a i := by
  classical
  unfold stageExactCol
  have hzero : (∑ pq ∈ S, (pairExactCol pq src a i - a i)) = 0 := by
    apply Finset.sum_eq_zero
    intro pq hpq
    have hi1 : i ≠ pq.1 := fun h =>
      hi (Finset.mem_biUnion.mpr ⟨pq, hpq, by unfold pairRows; rw [h]; simp⟩)
    have hi2 : i ≠ pq.2 := fun h =>
      hi (Finset.mem_biUnion.mpr ⟨pq, hpq, by unfold pairRows; rw [h]; simp⟩)
    simp [pairExactCol, hi1, hi2]
  rw [hzero, add_zero]

/-- **The exact block-diagonal stage preserves the column Euclidean norm**
    (orthogonality of `W`, columnwise).  The mass on each pair is preserved by
    the `2 × 2` rotation block and untouched coordinates are copied, so summing
    over the disjoint pairs and the complement gives `‖Wa‖₂ = ‖a‖₂`.  This is the
    exact-arithmetic invariant that lets the r-stage Lemma 19.9 accumulation
    (Theorem 19.10) compose stages without inflating the input column norm. -/
theorem stageExactCol_preserves_norm {m : ℕ}
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ)
    (hnz : ∀ pq ∈ S, (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0) :
    vecNorm2 (stageExactCol S src a) = vecNorm2 a := by
  classical
  have hSq : vecNorm2Sq (stageExactCol S src a) = vecNorm2Sq a := by
    -- Split both squared norms over touched rows and their complement.
    unfold vecNorm2Sq
    have hsplitW :
        (∑ i : Fin m, stageExactCol S src a i ^ 2) =
          (∑ i ∈ touchedRows S, stageExactCol S src a i ^ 2) +
            ∑ i ∈ (Finset.univ \ touchedRows S), stageExactCol S src a i ^ 2 := by
      rw [← Finset.sum_add_sum_compl (touchedRows S)
        (fun i => stageExactCol S src a i ^ 2)]
      rw [Finset.compl_eq_univ_sdiff]
    have hsplitA :
        (∑ i : Fin m, a i ^ 2) =
          (∑ i ∈ touchedRows S, a i ^ 2) +
            ∑ i ∈ (Finset.univ \ touchedRows S), a i ^ 2 := by
      rw [← Finset.sum_add_sum_compl (touchedRows S) (fun i => a i ^ 2)]
      rw [Finset.compl_eq_univ_sdiff]
    rw [hsplitW, hsplitA]
    -- Complement sums agree: `W` copies untouched coordinates.
    have hcompl :
        (∑ i ∈ (Finset.univ \ touchedRows S), stageExactCol S src a i ^ 2) =
          ∑ i ∈ (Finset.univ \ touchedRows S), a i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ∉ touchedRows S := (Finset.mem_sdiff.mp hi).2
      rw [stageExactCol_at_untouched S src a hi']
    -- Touched sums agree pairwise: `W` preserves each pair's mass.
    have htouchW :
        (∑ i ∈ touchedRows S, stageExactCol S src a i ^ 2) =
          ∑ pq ∈ S, (pairExactCol pq src a pq.1 ^ 2 +
            pairExactCol pq src a pq.2 ^ 2) := by
      unfold touchedRows
      rw [Finset.sum_biUnion (fun pq hpq rs hrs hne => hS.disj pq hpq rs hrs hne)]
      apply Finset.sum_congr rfl
      intro pq hpq
      rw [sum_sq_pairRows pq (hS.ne_self pq hpq)]
      rw [stageExactCol_at_fst S hS src a hpq, stageExactCol_at_snd S hS src a hpq]
    have htouchA :
        (∑ i ∈ touchedRows S, a i ^ 2) =
          ∑ pq ∈ S, (a pq.1 ^ 2 + a pq.2 ^ 2) := by
      unfold touchedRows
      rw [Finset.sum_biUnion (fun pq hpq rs hrs hne => hS.disj pq hpq rs hrs hne)]
      apply Finset.sum_congr rfl
      intro pq hpq
      exact sum_sq_pairRows pq (hS.ne_self pq hpq) a
    rw [hcompl, htouchW, htouchA]
    congr 1
    apply Finset.sum_congr rfl
    intro pq hpq
    exact pairExactCol_preserves_pair_mass pq src a (hS.ne_self pq hpq) (hnz pq hpq)
  unfold vecNorm2
  rw [hSq]

-- ============================================================
-- §19.6  Actual simultaneous disjoint-stage executor
-- ============================================================

/-- Execute one disjoint Givens stage on a column.  This is not an abstract
    recurrence assumption: `sweepResidual` is definitionally the difference
    between calls to the concrete `fl_givensC`, `fl_givensS`, and
    `fl_givensApply` kernels and the exact block rotation. -/
noncomputable def fl_givensDisjointStageColumn {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (src : StageSrc m)
    (a : Fin m → ℝ) : Fin m → ℝ :=
  fun i => stageExactCol S src a i + sweepResidual fp S src a i

/-- On the first row of an active pair, the simultaneous stage executor is
    exactly the repository's rounded Givens application kernel. -/
theorem fl_givensDisjointStageColumn_at_fst {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    fl_givensDisjointStageColumn fp S src a pq.1 =
      fl_givensApply fp m pq.1 pq.2
        (fl_givensC fp (src pq).1 (src pq).2)
        (fl_givensS fp (src pq).1 (src pq).2) a pq.1 := by
  rw [fl_givensDisjointStageColumn,
    stageExactCol_at_fst S hS src a hpq]
  exact (sweep_backward_error_identity_fst fp S hS src a hpq).symm

/-- On the second row of an active pair, the simultaneous stage executor is
    exactly the rounded Givens application kernel. -/
theorem fl_givensDisjointStageColumn_at_snd {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (a : Fin m → ℝ) {pq : Fin m × Fin m} (hpq : pq ∈ S) :
    fl_givensDisjointStageColumn fp S src a pq.2 =
      fl_givensApply fp m pq.1 pq.2
        (fl_givensC fp (src pq).1 (src pq).2)
        (fl_givensS fp (src pq).1 (src pq).2) a pq.2 := by
  rw [fl_givensDisjointStageColumn,
    stageExactCol_at_snd S hS src a hpq]
  exact (sweep_backward_error_identity_snd fp S hS src a hpq).symm

/-- Rows not touched by the stage are copied exactly. -/
theorem fl_givensDisjointStageColumn_at_untouched {m : ℕ} (fp : FPModel)
    (S : Finset (Fin m × Fin m)) (src : StageSrc m)
    (a : Fin m → ℝ) {i : Fin m} (hi : i ∉ touchedRows S) :
    fl_givensDisjointStageColumn fp S src a i = a i := by
  rw [fl_givensDisjointStageColumn,
    stageExactCol_at_untouched S src a hi,
    sweepResidual_zero_of_not_touched fp S src a hi, add_zero]

/-- Execute successive disjoint stages.  At every touched coordinate this
    recursion calls the actual rounded Givens coefficient and application
    kernels, as certified by the two coordinate theorems above. -/
noncomputable def fl_givensDisjointScheduleColumn {m : ℕ} (fp : FPModel)
    (Sseq : ℕ → Finset (Fin m × Fin m))
    (srcseq : ℕ → StageSrc m) (a0 : Fin m → ℝ) :
    ℕ → Fin m → ℝ
  | 0 => a0
  | k + 1 => fl_givensDisjointStageColumn fp (Sseq k) (srcseq k)
      (fl_givensDisjointScheduleColumn fp Sseq srcseq a0 k)

-- ============================================================
-- §19.6  r-stage accumulation → Theorem 19.10 coefficient
-- ============================================================

/-- Triangle inequality for the Euclidean vector norm (one-column reuse of the
    Frobenius triangle inequality). -/
theorem vecNorm2_add_le {m : ℕ} (u v : Fin m → ℝ) :
    vecNorm2 (fun i => u i + v i) ≤ vecNorm2 u + vecNorm2 v := by
  have h := columnFrob_add_le (m := m) (p := 1)
    (fun i (_ : Fin 1) => u i) (fun i (_ : Fin 1) => v i) 0
  simpa [columnFrob_eq_vecNorm2] using h

/-- Exact composed stage chain applied to the initial column: `W_{k-1}∘⋯∘W_0`
    applied to `aseq 0`.  This is the exact block-diagonal orthogonal image of the
    initial column after `k` stages, the object the accumulated backward error is
    measured against. -/
def stageChainExact {m : ℕ}
    (Wcol : ℕ → (Fin m → ℝ) → (Fin m → ℝ)) (a0 : Fin m → ℝ) :
    ℕ → (Fin m → ℝ)
  | 0 => a0
  | k + 1 => Wcol k (stageChainExact Wcol a0 k)

/-- **Abstract r-stage columnwise accumulation** for the disjoint-sweep Givens
    QR sweep (the fold behind Theorem 19.10, §19.6 p. 368).

    Let `aseq k` be one panel column after `k` computed stages and `Wcol k` the
    exact block-diagonal stage action (a norm-preserving additive isometry).
    Suppose each stage factors as `aseq (k+1) = Wcol k (aseq k) + Δ_k` with a
    residual bounded by the DIMENSION-AND-STAGE-SIZE-INDEPENDENT per-stage
    constant `√2·γ₈` (Lemma 19.9):
    `vecNorm2 Δ_k ≤ √2·γ₈·vecNorm2 (aseq k)`.  Then the accumulated column error
    against the exact composed orthogonal chain is bounded by
    `residualAccumBound (√2·γ₈) r` times the initial column norm.

    Because the per-stage constant is `√2·γ₈` (NOT the dimension-dependent
    `γ₈·√m` of a flat per-rotation accumulation), the coefficient is the
    `γ̃_r`-class quantity `residualAccumBound (√2·γ₈) r = (1 + √2·γ₈)^r − 1`,
    independent of the ambient dimension. -/
theorem disjointSweep_columnwise_accumulation {m r g : ℕ}
    (fp : FPModel)
    (aseq : ℕ → Fin m → ℝ)
    (Wcol : ℕ → (Fin m → ℝ) → (Fin m → ℝ))
    (Δ : ℕ → Fin m → ℝ)
    (hvalid : gammaValid fp g)
    (hadd : ∀ k : ℕ, k < r → ∀ (u v : Fin m → ℝ),
      Wcol k (fun i => u i + v i) = fun i => Wcol k u i + Wcol k v i)
    (hiso : ∀ k : ℕ, k < r → ∀ (v : Fin m → ℝ), vecNorm2 (Wcol k v) = vecNorm2 v)
    (hstep : ∀ k : ℕ, k < r →
      aseq (k + 1) = fun i => Wcol k (aseq k) i + Δ k i)
    (hΔ : ∀ k : ℕ, k < r →
      vecNorm2 (Δ k) ≤ Real.sqrt 2 * gamma fp g * vecNorm2 (aseq k)) :
    vecNorm2 (fun i => aseq r i - stageChainExact Wcol (aseq 0) r i) ≤
      residualAccumBound (Real.sqrt 2 * gamma fp g) r * vecNorm2 (aseq 0) := by
  have hc : 0 ≤ Real.sqrt 2 * gamma fp g :=
    mul_nonneg (Real.sqrt_nonneg 2) (gamma_nonneg fp hvalid)
  set c := Real.sqrt 2 * gamma fp g with hc_def
  -- Prove the stronger statement over all prefixes `k ≤ r` by induction.
  suffices h : ∀ k : ℕ, k ≤ r →
      vecNorm2 (fun i => aseq k i - stageChainExact Wcol (aseq 0) k i) ≤
        residualAccumBound c k * vecNorm2 (aseq 0) by
    exact h r le_rfl
  intro k
  induction k with
  | zero =>
      intro _hk
      have hzero : (fun i => aseq 0 i - stageChainExact Wcol (aseq 0) 0 i) =
          fun _ => 0 := by
        funext i; simp [stageChainExact]
      rw [hzero]
      have : vecNorm2 (fun _ : Fin m => (0 : ℝ)) = 0 := by
        unfold vecNorm2 vecNorm2Sq; simp
      rw [this, residualAccumBound]; ring_nf
      exact le_refl 0
  | succ k ih =>
      intro hk
      have hk' : k < r := hk
      have hkle : k ≤ r := Nat.le_of_lt hk'
      have hih := ih hkle
      -- Error recurrence:  e_{k+1} = W_k e_k + Δ_k.
      have herr :
          (fun i => aseq (k + 1) i - stageChainExact Wcol (aseq 0) (k + 1) i) =
            fun i =>
              Wcol k (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) i +
                Δ k i := by
        funext i
        have hstepk : aseq (k + 1) i = Wcol k (aseq k) i + Δ k i := by
          rw [hstep k hk']
        -- W_k is additive, so W_k(aseq k) = W_k(e_k) + W_k(chain k).
        have hsplit : aseq k = fun j =>
            (aseq k j - stageChainExact Wcol (aseq 0) k j) +
              stageChainExact Wcol (aseq 0) k j := by
          funext j; ring
        have hWsplit :
            Wcol k (aseq k) i =
              Wcol k (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) i +
                Wcol k (stageChainExact Wcol (aseq 0) k) i := by
          conv_lhs => rw [hsplit]
          rw [hadd k hk' (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j)
            (stageChainExact Wcol (aseq 0) k)]
        rw [hstepk, hWsplit]
        simp [stageChainExact]
        ring
      rw [herr]
      -- Triangle + isometry + inductive bound.
      have htri :
          vecNorm2 (fun i =>
            Wcol k (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) i +
              Δ k i) ≤
            vecNorm2 (Wcol k
              (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j)) +
              vecNorm2 (Δ k) :=
        vecNorm2_add_le _ _
      have hisoW :
          vecNorm2 (Wcol k
            (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j)) =
            vecNorm2 (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) :=
        hiso k hk' _
      -- Bound ‖aseq k‖ by ‖chain k‖ + ‖e_k‖ = ‖aseq 0‖ + ‖e_k‖ (isometry chain).
      have hchain_norm : ∀ j : ℕ, j ≤ k →
          vecNorm2 (stageChainExact Wcol (aseq 0) j) = vecNorm2 (aseq 0) := by
        intro j
        induction j with
        | zero => intro _; rfl
        | succ j ihj =>
            intro hjk
            have hjr : j < r := lt_of_lt_of_le (Nat.lt_succ_self j)
              (le_trans hjk hkle)
            rw [stageChainExact, hiso j hjr]
            exact ihj (Nat.le_of_lt (Nat.lt_of_succ_le hjk))
      have haseq_le :
          vecNorm2 (aseq k) ≤ vecNorm2 (aseq 0) +
            vecNorm2 (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) := by
        have hsplit : aseq k = fun j =>
            stageChainExact Wcol (aseq 0) k j +
              (aseq k j - stageChainExact Wcol (aseq 0) k j) := by
          funext j; ring
        calc
          vecNorm2 (aseq k)
              = vecNorm2 (fun j =>
                  stageChainExact Wcol (aseq 0) k j +
                    (aseq k j - stageChainExact Wcol (aseq 0) k j)) := by
                    rw [← hsplit]
          _ ≤ vecNorm2 (stageChainExact Wcol (aseq 0) k) +
                vecNorm2 (fun j =>
                  aseq k j - stageChainExact Wcol (aseq 0) k j) :=
                vecNorm2_add_le _ _
          _ = vecNorm2 (aseq 0) +
                vecNorm2 (fun j =>
                  aseq k j - stageChainExact Wcol (aseq 0) k j) := by
                rw [hchain_norm k le_rfl]
      -- Assemble.
      set e := vecNorm2 (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j)
        with he_def
      set N := vecNorm2 (aseq 0) with hN_def
      set α := residualAccumBound c k with hα_def
      have hΔk : vecNorm2 (Δ k) ≤ c * vecNorm2 (aseq k) := hΔ k hk'
      have hΔk' : vecNorm2 (Δ k) ≤ c * (N + e) :=
        le_trans hΔk (mul_le_mul_of_nonneg_left haseq_le hc)
      have he_le : e ≤ α * N := hih
      have htotal :
          vecNorm2 (fun i =>
            Wcol k (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) i +
              Δ k i) ≤ e + c * (N + e) := by
        calc
          vecNorm2 (fun i =>
            Wcol k (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j) i +
              Δ k i)
              ≤ vecNorm2 (Wcol k
                  (fun j => aseq k j - stageChainExact Wcol (aseq 0) k j)) +
                  vecNorm2 (Δ k) := htri
          _ = e + vecNorm2 (Δ k) := by rw [hisoW]
          _ ≤ e + c * (N + e) := by linarith
      -- residualAccumBound c (k+1) * N = α*N + c*(1+α)*N ≥ e + c*(N+e).
      have hNnonneg : 0 ≤ N := vecNorm2_nonneg _
      have hrec : residualAccumBound c (k + 1) * N =
          α * N + c * (1 + α) * N := by
        simp [residualAccumBound, hα_def]; ring
      rw [hrec]
      -- e ≤ αN, and c*(N+e) ≤ c*(N + αN) = c*(1+α)*N.
      have hbound2 : c * (N + e) ≤ c * (1 + α) * N := by
        have : N + e ≤ (1 + α) * N := by nlinarith [he_le]
        calc
          c * (N + e) ≤ c * ((1 + α) * N) :=
            mul_le_mul_of_nonneg_left this hc
          _ = c * (1 + α) * N := by ring
      linarith [he_le, hbound2, htotal]

-- ============================================================
-- §19.6  Theorem 19.10: Givens QR backward error with the
--        dimension-independent-per-stage γ̃_{m+n-2} coefficient
-- ============================================================

/-- Sharp Theorem 19.10 coefficient obtained from the actual disjoint-stage
    executor and the computed-coefficient `gamma_6` form of Lemmas 19.8--19.9. -/
noncomputable def gammaTildeDimIndepGamma6
    (fp : FPModel) (m n : ℕ) : ℝ :=
  residualAccumBound (Real.sqrt 2 * gamma fp 6) (givensQRStageCount m n)

/-- Closed form of the sharp actual-executor coefficient. -/
theorem gammaTildeDimIndepGamma6_closed_form (fp : FPModel) (m n : ℕ) :
    gammaTildeDimIndepGamma6 fp m n =
      (1 + Real.sqrt 2 * gamma fp 6) ^ givensQRStageCount m n - 1 := by
  unfold gammaTildeDimIndepGamma6
  exact residualAccumBound_eq_one_add_pow_sub_one (Real.sqrt 2 * gamma fp 6)
    (givensQRStageCount m n)

/-- **Theorem 19.10 / equation (19.25), actual executor bridge.**  Running
    `fl_givensDisjointScheduleColumn` for the canonical `m+n-2` stage count
    satisfies the dimension-independent columnwise backward-error estimate.
    The recurrence equation is discharged by reduction of the executor, rather
    than supplied as a hypothesis.  Every active coordinate is an actual call
    to `fl_givensC`, `fl_givensS`, and `fl_givensApply`.

    The schedule interface retains only the two mathematical well-formedness
    obligations used by Higham's staged proof: row pairs in a stage are
    disjoint, and every coefficient source two-vector is nonzero. -/
theorem H19_Theorem19_10_actual_disjoint_executor_gamma6 {m n : ℕ}
    (fp : FPModel)
    (Sseq : ℕ → Finset (Fin m × Fin m))
    (srcseq : ℕ → StageSrc m)
    (_hn : 0 < n) (_hnm : n ≤ m)
    (hvalid : gammaValid fp 6)
    (hdisj : ∀ k : ℕ, k < givensQRStageCount m n → DisjointPairs (Sseq k))
    (hnz : ∀ k : ℕ, k < givensQRStageCount m n →
      ∀ pq ∈ Sseq k, (srcseq k pq).1 ^ 2 + (srcseq k pq).2 ^ 2 ≠ 0)
    (a0 : Fin m → ℝ) :
    vecNorm2
        (fun i =>
          fl_givensDisjointScheduleColumn fp Sseq srcseq a0
              (givensQRStageCount m n) i -
            stageChainExact
              (fun k v => stageExactCol (Sseq k) (srcseq k) v) a0
              (givensQRStageCount m n) i) ≤
      gammaTildeDimIndepGamma6 fp m n * vecNorm2 a0 := by
  classical
  have hacc := disjointSweep_columnwise_accumulation
    (m := m) (r := givensQRStageCount m n) (g := 6)
    fp (fl_givensDisjointScheduleColumn fp Sseq srcseq a0)
      (fun k v => stageExactCol (Sseq k) (srcseq k) v)
      (fun k => sweepResidual fp (Sseq k) (srcseq k)
        (fl_givensDisjointScheduleColumn fp Sseq srcseq a0 k))
      hvalid
      (by
        intro k _hk u v
        funext i
        show stageExactCol (Sseq k) (srcseq k) (fun j => u j + v j) i =
          stageExactCol (Sseq k) (srcseq k) u i +
            stageExactCol (Sseq k) (srcseq k) v i
        unfold stageExactCol
        have hpair : (∑ pq ∈ Sseq k,
              (pairExactCol pq (srcseq k) (fun j => u j + v j) i -
                (u i + v i))) =
            (∑ pq ∈ Sseq k, (pairExactCol pq (srcseq k) u i - u i)) +
              ∑ pq ∈ Sseq k, (pairExactCol pq (srcseq k) v i - v i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl (fun pq _ =>
            pairExactCol_sub_id_add pq (srcseq k) u v i)
        rw [hpair]
        ring)
      (by
        intro k hk v
        exact stageExactCol_preserves_norm (Sseq k) (hdisj k hk)
          (srcseq k) v (hnz k hk))
      (by
        intro k _hk
        rfl)
      (by
        intro k hk
        exact H19_Lemma19_9_disjoint_stage_column_backward_error_gamma6 fp
          (Sseq k) (hdisj k hk) (srcseq k)
          (fl_givensDisjointScheduleColumn fp Sseq srcseq a0 k)
          (hnz k hk) hvalid)
  simpa [gammaTildeDimIndepGamma6,
    fl_givensDisjointScheduleColumn] using hacc

/-- Closed-form equation (19.25) for the concrete rounded disjoint executor. -/
theorem eq19_25_actual_disjoint_executor_gamma6_closed_form {m n : ℕ}
    (fp : FPModel)
    (Sseq : ℕ → Finset (Fin m × Fin m))
    (srcseq : ℕ → StageSrc m)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp 6)
    (hdisj : ∀ k : ℕ, k < givensQRStageCount m n → DisjointPairs (Sseq k))
    (hnz : ∀ k : ℕ, k < givensQRStageCount m n →
      ∀ pq ∈ Sseq k, (srcseq k pq).1 ^ 2 + (srcseq k pq).2 ^ 2 ≠ 0)
    (a0 : Fin m → ℝ) :
    vecNorm2
        (fun i =>
          fl_givensDisjointScheduleColumn fp Sseq srcseq a0
              (givensQRStageCount m n) i -
            stageChainExact
              (fun k v => stageExactCol (Sseq k) (srcseq k) v) a0
              (givensQRStageCount m n) i) ≤
      ((1 + Real.sqrt 2 * gamma fp 6) ^ givensQRStageCount m n - 1) *
        vecNorm2 a0 := by
  rw [← gammaTildeDimIndepGamma6_closed_form]
  exact H19_Theorem19_10_actual_disjoint_executor_gamma6 fp Sseq srcseq
    hn hnm hvalid hdisj hnz a0

/-- The Theorem 19.10 coefficient obtained from the Lemma 19.9 disjoint-sweep
    analysis: the `r`-stage fold of the dimension-and-stage-size-independent
    per-stage constant `√2·γ₈`, evaluated at the tall Givens QR schedule length
    `r = m + n − 2 = givensQRStageCount m n`.

    This is the `γ̃_{m+n-2}`-class coefficient of the printed Theorem 19.10.
    Crucially the base per-stage constant `√2·γ₈` does NOT depend on `m` (the
    per-stage error is dimension-independent by the block-diagonal / at-most-one-
    rotation-per-row structure), so this coefficient depends on `m` and `n` only
    through the stage COUNT `m + n − 2` — exactly the printed `γ̃_{m+n-2}` shape,
    unlike a flat per-rotation accumulation whose base already carries a `√m`. -/
noncomputable def gammaTildeDimIndep (fp : FPModel) (m n : ℕ) : ℝ :=
  residualAccumBound (Real.sqrt 2 * gamma fp 8) (givensQRStageCount m n)

/-- Closed form of the Theorem 19.10 dimension-independent-per-stage coefficient:
    `γ̃_{m+n-2} = (1 + √2·γ₈)^{m+n-2} − 1`.  The base `1 + √2·γ₈` is
    dimension-independent; the entire `m, n` dependence is in the exponent
    `m + n − 2` (the number of disjoint-rotation stages). -/
theorem gammaTildeDimIndep_closed_form (fp : FPModel) (m n : ℕ) :
    gammaTildeDimIndep fp m n =
      (1 + Real.sqrt 2 * gamma fp 8) ^ givensQRStageCount m n - 1 := by
  unfold gammaTildeDimIndep
  exact residualAccumBound_eq_one_add_pow_sub_one (Real.sqrt 2 * gamma fp 8)
    (givensQRStageCount m n)

/-- **Theorem 19.10** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.6, p. 368), columnwise backward error of Givens QR for a tall
    matrix, restated with the DIMENSION-INDEPENDENT-PER-STAGE coefficient from
    the Lemma 19.9 disjoint-sweep analysis.

    Model.  `aseq k` is one panel column after `k` anti-diagonal Givens stages;
    each stage `k` is a disjoint sweep over the pair set `Sseq k` with source
    two-vectors `srcseq k`, so its exact action `Wcol k := stageExactCol (Sseq k)`
    is a norm-preserving additive isometry (block-diagonal orthogonal) and its
    computed residual is `Δ k := sweepResidual (Sseq k)`.  The schedule uses
    `r = m + n − 2 = givensQRStageCount m n` stages (the printed anti-diagonal
    Givens QR schedule for an `m × n` matrix, `0 < n ≤ m`).

    Conclusion.  The accumulated columnwise backward error of the computed panel
    column against the exact composed orthogonal chain is bounded by
    `γ̃_{m+n-2}·‖a‖₂` with `γ̃_{m+n-2} = gammaTildeDimIndep fp m n`.

    Constant.  This is the printed `γ̃_{m+n-2}` shape: the base per-stage constant
    `√2·γ₈` is INDEPENDENT of the ambient dimension `m` (Lemma 19.9, block-
    diagonal structure), so `m, n` enter the coefficient ONLY through the stage
    count `m + n − 2`.  The explicit per-stage index is `8` (`√2·γ₈`), the same
    `√2·γ̃` class Higham leaves with an unspecified integer (p. 357/368); we do
    NOT claim the exact printed integer, only a proved same-class constant with
    an explicit (larger) index.  This is strictly sharper in the dimension than
    the repository's earlier staged coefficient, whose per-rotation base carries
    a `√m` and which accumulates over ALL individual tasks — see
    `gammaTildeDimIndep_dimIndep_base` below. -/
theorem H19_Theorem19_10_givens_qr_dimIndep {m n : ℕ}
    (fp : FPModel)
    (aseq : ℕ → Fin m → ℝ)
    (Sseq : ℕ → Finset (Fin m × Fin m))
    (srcseq : ℕ → StageSrc m)
    (_hn : 0 < n) (_hnm : n ≤ m)
    (hvalid : gammaValid fp 8)
    (hdisj : ∀ k : ℕ, k < givensQRStageCount m n → DisjointPairs (Sseq k))
    (hnz : ∀ k : ℕ, k < givensQRStageCount m n →
      ∀ pq ∈ Sseq k, (srcseq k pq).1 ^ 2 + (srcseq k pq).2 ^ 2 ≠ 0)
    (hstep : ∀ k : ℕ, k < givensQRStageCount m n →
      aseq (k + 1) =
        fun i => stageExactCol (Sseq k) (srcseq k) (aseq k) i +
          sweepResidual fp (Sseq k) (srcseq k) (aseq k) i) :
    vecNorm2
        (fun i => aseq (givensQRStageCount m n) i -
          stageChainExact
            (fun k v => stageExactCol (Sseq k) (srcseq k) v) (aseq 0)
            (givensQRStageCount m n) i) ≤
      gammaTildeDimIndep fp m n * vecNorm2 (aseq 0) := by
  classical
  -- Instantiate the abstract accumulation with the disjoint-stage data.
  refine disjointSweep_columnwise_accumulation (r := givensQRStageCount m n)
    fp aseq (fun k v => stageExactCol (Sseq k) (srcseq k) v)
    (fun k => sweepResidual fp (Sseq k) (srcseq k) (aseq k))
    hvalid ?_ ?_ ?_ ?_
  · -- Additivity of each exact stage action.
    intro k _hk u v
    funext i
    show stageExactCol (Sseq k) (srcseq k) (fun j => u j + v j) i =
      stageExactCol (Sseq k) (srcseq k) u i +
        stageExactCol (Sseq k) (srcseq k) v i
    unfold stageExactCol
    have hpair : (∑ pq ∈ Sseq k,
          (pairExactCol pq (srcseq k) (fun j => u j + v j) i - (u i + v i))) =
        (∑ pq ∈ Sseq k, (pairExactCol pq (srcseq k) u i - u i)) +
          ∑ pq ∈ Sseq k, (pairExactCol pq (srcseq k) v i - v i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun pq _ =>
        pairExactCol_sub_id_add pq (srcseq k) u v i)
    rw [hpair]; ring
  · -- Isometry of each exact stage action (on-schedule stages only).
    intro k hk v
    exact stageExactCol_preserves_norm (Sseq k) (hdisj k hk) (srcseq k) v
      (hnz k hk)
  · exact hstep
  · -- Per-stage residual bound (Lemma 19.9), dimension-and-stage-size-independent.
    intro k hk
    exact H19_Lemma19_9_disjoint_stage_column_backward_error fp
      (Sseq k) (hdisj k hk) (srcseq k) (aseq k) (hnz k hk) hvalid

-- ============================================================
-- §19.6  Constant-honesty documentation
-- ============================================================

/-- **The Lemma 19.9 per-stage constant is dimension-independent.**  The base
    per-stage backward-error constant `√2·γ₈` proved in
    `H19_Lemma19_9_disjoint_stage_column_backward_error` is literally the same
    real number for every ambient dimension `m` and every stage size (number of
    rotations): it does not mention `m` at all.  This is the crux of Lemma 19.9
    versus a naive bound — the block-diagonal (at-most-one-rotation-per-row)
    structure removes both the `√m` per-rotation Frobenius factor and the
    stage-size accumulation. -/
theorem lemma19_9_per_stage_constant_dimIndep (fp : FPModel) (m m' : ℕ)
    (a : Fin m → ℝ) (a' : Fin m' → ℝ)
    (S : Finset (Fin m × Fin m)) (hS : DisjointPairs S) (src : StageSrc m)
    (S' : Finset (Fin m' × Fin m')) (hS' : DisjointPairs S') (src' : StageSrc m')
    (hnz : ∀ pq ∈ S, (src pq).1 ^ 2 + (src pq).2 ^ 2 ≠ 0)
    (hnz' : ∀ pq ∈ S', (src' pq).1 ^ 2 + (src' pq).2 ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    -- The SAME base constant `√2·γ₈` controls both stages, regardless of
    -- `m ≠ m'` and regardless of how many rotations each stage contains.
    (vecNorm2 (sweepResidual fp S src a) ≤
        Real.sqrt 2 * gamma fp 8 * vecNorm2 a) ∧
      (vecNorm2 (sweepResidual fp S' src' a') ≤
        Real.sqrt 2 * gamma fp 8 * vecNorm2 a') :=
  ⟨H19_Lemma19_9_disjoint_stage_column_backward_error fp S hS src a hnz hvalid,
    H19_Lemma19_9_disjoint_stage_column_backward_error fp S' hS' src' a' hnz'
      hvalid⟩

/-- **Equation `(19.25)` columnwise reading of Theorem 19.10** with the
    dimension-independent-per-stage coefficient.  This is the same statement as
    `H19_Theorem19_10_givens_qr_dimIndep`, exposed in closed form
    `γ̃_{m+n-2} = (1 + √2·γ₈)^{m+n-2} − 1`, making the printed `γ̃_{m+n-2}` shape
    explicit: a fixed dimension-independent base `1 + √2·γ₈` raised to the stage
    count `m + n − 2`. -/
theorem eq19_25_givens_qr_dimIndep_closed_form {m n : ℕ}
    (fp : FPModel)
    (aseq : ℕ → Fin m → ℝ)
    (Sseq : ℕ → Finset (Fin m × Fin m))
    (srcseq : ℕ → StageSrc m)
    (hn : 0 < n) (hnm : n ≤ m)
    (hvalid : gammaValid fp 8)
    (hdisj : ∀ k : ℕ, k < givensQRStageCount m n → DisjointPairs (Sseq k))
    (hnz : ∀ k : ℕ, k < givensQRStageCount m n →
      ∀ pq ∈ Sseq k, (srcseq k pq).1 ^ 2 + (srcseq k pq).2 ^ 2 ≠ 0)
    (hstep : ∀ k : ℕ, k < givensQRStageCount m n →
      aseq (k + 1) =
        fun i => stageExactCol (Sseq k) (srcseq k) (aseq k) i +
          sweepResidual fp (Sseq k) (srcseq k) (aseq k) i) :
    vecNorm2
        (fun i => aseq (givensQRStageCount m n) i -
          stageChainExact
            (fun k v => stageExactCol (Sseq k) (srcseq k) v) (aseq 0)
            (givensQRStageCount m n) i) ≤
      ((1 + Real.sqrt 2 * gamma fp 8) ^ givensQRStageCount m n - 1) *
        vecNorm2 (aseq 0) := by
  rw [← gammaTildeDimIndep_closed_form]
  exact H19_Theorem19_10_givens_qr_dimIndep fp aseq Sseq srcseq hn hnm hvalid
    hdisj hnz hstep

end NumStability.Wave13
