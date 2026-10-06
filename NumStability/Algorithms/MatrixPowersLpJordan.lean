-- Algorithms/MatrixPowersLpJordan.lean
--
-- Higham Chapter 18: exact-arithmetic power bound of §18.1, eq (18.5)
-- alternative form (p. 344, unnumbered display), at every finite real
-- p-norm exponent over ℂ for Jordan (possibly defective) data:
--
--   ‖A^k‖_p ≤ κ_p(X) · κ_p(D) · (ρ + β)^k     (A = X J X⁻¹, J bidiagonal)
--
-- for `A : CMatrix n n` with complex bidiagonal Jordan-form-like similarity
-- data, where `‖·‖_p` is the repo's subordinate complex matrix `L^p` norm
-- `complexMatrixLpNormOfReal` at a real exponent `1 ≤ p < ∞`,
-- `κ_p(X) = ‖X‖_p·‖X⁻¹‖_p`, and `κ_p(D) ≤ (β^s)⁻¹` for the diagonal
-- δ-scaling `D = diag(q)` with `β^s ≤ q ≤ 1`.
--
-- Honest scope: the printed display reads "for any p-norm"; this file closes
-- every finite real exponent `1 ≤ p < ∞` for complex Jordan data.  The
-- `p = ∞` real-spectrum subcase is closed separately in
-- `MatrixPowersJordan.lean` (`higham_eq_18_5_alt_real_jordan`), and the
-- diagonalizable all-p case (eq 18.4) in `MatrixPowersLp.lean`.
--
-- Infrastructure REUSED (source traceability):
--   `CVec`, `CMatrix`, `complexVecLpNorm`,
--   `complexVecLpNorm_isComplexVectorNorm`,
--   `complexVecLpNorm_ofReal_eq_sum_rpow`     — Analysis/Norms.lean (~47–530)
--   `complexMatrixVecMul`, `complexMatrixMul`, `complexMatrixMul_assoc`,
--   `complexMatrixVecMul_mul`, `IsComplexMatrixRightInverse`
--                                             — Norms.lean ~3022–3177
--   `HasComplexMatrixLpBound`, `hasComplexMatrixLpBound_apply`,
--   `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`,
--   `complexMatrixLpNormOfReal` (+ value/bound/mul_le lemmas)
--                                             — Norms.lean ~4209–8560
--   `cDiagMatrix`, `cDiagMatrix_vecMul`, `cDiagMatrix_conj_entry`
--                                             — Algorithms/MatrixPowersComplex.lean ~366
--   `cIdMatrix`, `cMatPow` (+_zero/_succ), `cMatPow_similarity`,
--   `complexVecLpNorm_le_mul_of_forall_norm_le`,
--   `complexMatrixLpNormOfReal_diagonal_le`   — Algorithms/MatrixPowersLp.lean
-- The proof skeletons mirrored here are `higham_eq_18_5_alt_real_jordan`
-- (Algorithms/MatrixPowersJordan.lean, the p = ∞ real case), the entry
-- computation of `cJordan_conj_row_sum_le`
-- (Algorithms/MatrixPowersComplex.lean ~418), and
-- `higham_eq_18_4_upper_lp_diagonalizable` (Algorithms/MatrixPowersLp.lean).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import NumStability.Analysis.Norms
import NumStability.Algorithms.MatrixPowersLp

namespace NumStability

open scoped BigOperators

-- ============================================================
-- The shift bound: ‖shift(x)‖_p ≤ ‖x‖_p
-- ============================================================

/-- Dropping the first term of a nonnegative sequence that vanishes at `n`:
    `∑_{m<n} F(m+1) ≤ ∑_{m<n} F(m)`.  Scalar reindexing workhorse for the
    superdiagonal shift estimate below; proved by comparing the two
    one-step-extended range sums (`Finset.sum_range_succ'` /
    `Finset.sum_range_succ`). -/
theorem sum_range_shift_le (n : ℕ) (F : ℕ → ℝ) (hF : ∀ m, 0 ≤ F m)
    (hFn : F n = 0) :
    ∑ m ∈ Finset.range n, F (m + 1) ≤ ∑ m ∈ Finset.range n, F m := by
  have h1 := Finset.sum_range_succ' F n
  have h2 := Finset.sum_range_succ F n
  have h0 := hF 0
  rw [hFn, add_zero] at h2
  linarith

/-- One-step downward shift of a finite complex vector: coordinate `i` holds
    `x_{i+1}` when `i + 1 < n`, and `0` in the last coordinate.  This is the
    vector acted on by the superdiagonal part of a bidiagonal Jordan matrix
    (Higham 2nd ed., §18.1, p. 344). -/
noncomputable def cShiftVec {n : ℕ} (x : CVec n) : CVec n :=
  fun i => if h : (i : ℕ) + 1 < n then x ⟨(i : ℕ) + 1, h⟩ else 0

/-- **The shift bound for the finite complex `L^p` norm** (the crux of the
    superdiagonal estimate in eq (18.5)'s alternative form, Higham 2nd ed.,
    §18.1, p. 344): `‖shift(x)‖_p ≤ ‖x‖_p` for every real exponent
    `1 ≤ p < ∞`.  The shifted coordinate norms are a reindexed subfamily of
    the original ones, so the `p`-th power sums compare termwise after the
    range reindexing `sum_range_shift_le`; entrywise domination at a fixed
    index does NOT hold, so this cannot be obtained from
    `complexVecLpNorm_le_mul_of_forall_norm_le`. -/
theorem complexVecLpNorm_shift_le {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (x : CVec n) :
    complexVecLpNorm (ENNReal.ofReal p) (cShiftVec x) ≤
      complexVecLpNorm (ENNReal.ofReal p) x := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le zero_lt_one hp
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp0,
    complexVecLpNorm_ofReal_eq_sum_rpow hp0]
  have hFnonneg : ∀ m : ℕ,
      0 ≤ (if h : m < n then ‖x ⟨m, h⟩‖ ^ p else 0) := by
    intro m
    by_cases h : m < n
    · rw [dif_pos h]
      exact Real.rpow_nonneg (norm_nonneg _) p
    · rw [dif_neg h]
  have hFn : (if h : n < n then ‖x ⟨n, h⟩‖ ^ p else 0) = 0 :=
    dif_neg (lt_irrefl n)
  have hleft : ∑ i : Fin n, ‖cShiftVec x i‖ ^ p
      = ∑ m ∈ Finset.range n,
          (if h : m + 1 < n then ‖x ⟨m + 1, h⟩‖ ^ p else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun m => if h : m + 1 < n then ‖x ⟨m + 1, h⟩‖ ^ p else 0) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (i : ℕ) + 1 < n
    · have h2 : cShiftVec x i = x ⟨(i : ℕ) + 1, h⟩ := by
        unfold cShiftVec
        exact dif_pos h
      rw [h2, dif_pos h]
    · have h2 : cShiftVec x i = 0 := by
        unfold cShiftVec
        exact dif_neg h
      rw [h2, dif_neg h, norm_zero]
      exact Real.zero_rpow hp0.ne'
  have hright : ∑ i : Fin n, ‖x i‖ ^ p
      = ∑ m ∈ Finset.range n,
          (if h : m < n then ‖x ⟨m, h⟩‖ ^ p else 0) := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun m => if h : m < n then ‖x ⟨m, h⟩‖ ^ p else 0) n]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dif_pos i.isLt]
  refine Real.rpow_le_rpow ?_ ?_ (inv_nonneg.mpr hp0.le)
  · exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) p)
  · rw [hleft, hright]
    exact sum_range_shift_le n
      (fun m => if h : m < n then ‖x ⟨m, h⟩‖ ^ p else 0) hFnonneg hFn

-- ============================================================
-- The bidiagonal L^p bound ‖J'‖_p ≤ ρ + β
-- ============================================================

/-- **Bidiagonal `p`-norm bound, predicate form** (the `‖D⁻¹JD‖_p ≤ ρ + β`
    step of eq (18.5)'s alternative form, Higham 2nd ed., §18.1, p. 344): an
    upper bidiagonal complex matrix with diagonal moduli ≤ `ρ` and
    superdiagonal moduli ≤ `β` satisfies the subordinate upper-bound
    predicate `HasComplexMatrixLpBound` with constant `ρ + β` at every real
    exponent `1 ≤ p < ∞`.

    Proof by the direct vector estimate: pointwise,
    `(Mx)_i = M_{ii}·x_i + M_{i,i+1}·x_{i+1}`, so `Mx` splits into a
    diagonal part dominated by `ρ‖x‖_p` and a shifted superdiagonal part
    dominated by `β‖shift(x)‖_p ≤ β‖x‖_p` (via `complexVecLpNorm_shift_le`);
    the vector triangle inequality (`complexVecLpNorm` is a genuine norm)
    combines the two.  No matrix-level triangle inequality is needed. -/
theorem hasComplexMatrixLpBound_bidiagonal {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    (M : CMatrix n n) (ρ β : ℝ) (hρ0 : 0 ≤ ρ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      M i j = 0)
    (hdiagbd : ∀ i, ‖M i i‖ ≤ ρ)
    (hsupbd : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖M i j‖ ≤ β) :
    HasComplexMatrixLpBound (ENNReal.ofReal p) M (ρ + β) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hν : IsComplexVectorNorm (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  refine ⟨add_nonneg hρ0 hβ0, ?_⟩
  intro x
  -- Pointwise split of the matrix action into diagonal and shifted parts.
  have hdecomp : complexMatrixVecMul M x =
      complexVecAdd (fun i => M i i * x i)
        (fun i => if h : (i : ℕ) + 1 < n then
          M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ else 0) := by
    funext i
    show (∑ j : Fin n, M i j * x j) =
      M i i * x i + (if h : (i : ℕ) + 1 < n then
        M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ else 0)
    by_cases hi : (i : ℕ) + 1 < n
    · rw [dif_pos hi]
      have hii' : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
        intro h
        have h1 : (i : ℕ) = (i : ℕ) + 1 := congrArg Fin.val h
        omega
      have hzero : ∀ j : Fin n, j ≠ i → j ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) →
          M i j = 0 := by
        intro j hj1 hj2
        apply hshape i j
        · exact fun h => hj1 (Fin.eq_of_val_eq h)
        · exact fun h => hj2 (Fin.eq_of_val_eq h)
      have hsub : ∑ j ∈ ({i, ⟨(i : ℕ) + 1, hi⟩} : Finset (Fin n)), M i j * x j
          = ∑ j : Fin n, M i j * x j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
        rw [hzero j hj.1 hj.2, zero_mul]
      rw [← hsub, Finset.sum_pair hii']
    · rw [dif_neg hi, add_zero]
      have hzero : ∀ j : Fin n, j ≠ i → M i j = 0 := by
        intro j hj
        apply hshape i j
        · exact fun h => hj (Fin.eq_of_val_eq h)
        · intro h
          have hlt := j.isLt
          omega
      exact Finset.sum_eq_single i
        (fun j _ hj => by rw [hzero j hj, zero_mul])
        (fun h => absurd (Finset.mem_univ i) h)
  -- Diagonal part: entrywise domination at the same index.
  have hd : complexVecLpNorm (ENNReal.ofReal p) (fun i => M i i * x i) ≤
      ρ * complexVecLpNorm (ENNReal.ofReal p) x := by
    refine complexVecLpNorm_le_mul_of_forall_norm_le hp (fun i => ?_) hρ0
    show ‖M i i * x i‖ ≤ ρ * ‖x i‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hdiagbd i) (norm_nonneg _)
  -- Superdiagonal part: entrywise domination against the shifted vector.
  have hs : complexVecLpNorm (ENNReal.ofReal p)
      (fun i => if h : (i : ℕ) + 1 < n then
        M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ else 0) ≤
      β * complexVecLpNorm (ENNReal.ofReal p) (cShiftVec x) := by
    refine complexVecLpNorm_le_mul_of_forall_norm_le hp (fun i => ?_) hβ0
    show ‖(if h : (i : ℕ) + 1 < n then
        M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ else 0)‖ ≤
      β * ‖cShiftVec x i‖
    by_cases h : (i : ℕ) + 1 < n
    · have h1 : (if h' : (i : ℕ) + 1 < n then
          M i ⟨(i : ℕ) + 1, h'⟩ * x ⟨(i : ℕ) + 1, h'⟩ else 0)
          = M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ := dif_pos h
      have h2 : cShiftVec x i = x ⟨(i : ℕ) + 1, h⟩ := by
        unfold cShiftVec
        exact dif_pos h
      rw [h1, h2, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (hsupbd i ⟨(i : ℕ) + 1, h⟩ rfl) (norm_nonneg _)
    · have h1 : (if h' : (i : ℕ) + 1 < n then
          M i ⟨(i : ℕ) + 1, h'⟩ * x ⟨(i : ℕ) + 1, h'⟩ else 0) = (0 : ℂ) :=
        dif_neg h
      rw [h1, norm_zero]
      exact mul_nonneg hβ0 (norm_nonneg _)
  calc complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul M x)
      = complexVecLpNorm (ENNReal.ofReal p)
          (complexVecAdd (fun i => M i i * x i)
            (fun i => if h : (i : ℕ) + 1 < n then
              M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ else 0)) := by
        rw [hdecomp]
    _ ≤ complexVecLpNorm (ENNReal.ofReal p) (fun i => M i i * x i) +
        complexVecLpNorm (ENNReal.ofReal p)
          (fun i => if h : (i : ℕ) + 1 < n then
            M i ⟨(i : ℕ) + 1, h⟩ * x ⟨(i : ℕ) + 1, h⟩ else 0) :=
        hν.add_le _ _
    _ ≤ ρ * complexVecLpNorm (ENNReal.ofReal p) x +
        β * complexVecLpNorm (ENNReal.ofReal p) (cShiftVec x) :=
        add_le_add hd hs
    _ ≤ ρ * complexVecLpNorm (ENNReal.ofReal p) x +
        β * complexVecLpNorm (ENNReal.ofReal p) x :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (complexVecLpNorm_shift_le hp x) hβ0)
    _ = (ρ + β) * complexVecLpNorm (ENNReal.ofReal p) x := by ring

/-- **Bidiagonal `p`-norm bound, norm-function form** (Higham 2nd ed., §18.1,
    p. 344): `‖M‖_p ≤ ρ + β` for an upper bidiagonal complex matrix with
    diagonal moduli ≤ `ρ` and superdiagonal moduli ≤ `β`, at every real
    exponent `1 ≤ p < ∞`. -/
theorem complexMatrixLpNormOfReal_bidiagonal_le {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (M : CMatrix n n) (ρ β : ℝ)
    (hρ0 : 0 ≤ ρ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      M i j = 0)
    (hdiagbd : ∀ i, ‖M i i‖ ≤ ρ)
    (hsupbd : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖M i j‖ ≤ β) :
    complexMatrixLpNormOfReal hn p hp M ≤ ρ + β :=
  isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp M)
    (hasComplexMatrixLpBound_bidiagonal hp M ρ β hρ0 hβ0 hshape hdiagbd hsupbd)

-- ============================================================
-- Identity and power norm bounds at every real exponent 1 ≤ p < ∞
-- ============================================================

/-- The complex identity matrix has subordinate `p`-norm at most `1` at every
    real exponent `1 ≤ p < ∞` (it is `cDiagMatrix` of the all-ones vector). -/
theorem complexMatrixLpNormOfReal_cIdMatrix_le {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) :
    complexMatrixLpNormOfReal hn p hp (cIdMatrix n) ≤ 1 := by
  have hid : cIdMatrix n = cDiagMatrix (fun _ : Fin n => (1 : ℂ)) := by
    funext i j
    rfl
  rw [hid]
  exact complexMatrixLpNormOfReal_diagonal_le hn p hp _ zero_le_one
    (fun _ => le_of_eq norm_one)

/-- Submultiplicative power bound: `‖M‖_p ≤ c` gives `‖M^k‖_p ≤ c^k` at every
    real exponent `1 ≤ p < ∞`, by induction via
    `complexMatrixLpNormOfReal_mul_le` (Norms.lean ~8517). -/
theorem complexMatrixLpNormOfReal_cMatPow_le {n : ℕ} (hn : 0 < n)
    (p : ℝ) (hp : 1 ≤ p) (M : CMatrix n n) {c : ℝ} (hc : 0 ≤ c)
    (hM : complexMatrixLpNormOfReal hn p hp M ≤ c) (k : ℕ) :
    complexMatrixLpNormOfReal hn p hp (cMatPow n M k) ≤ c ^ k := by
  have hnonneg : ∀ N : CMatrix n n, 0 ≤ complexMatrixLpNormOfReal hn p hp N :=
    fun N => (hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal hn hp
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp N)).1
  induction k with
  | zero =>
    rw [cMatPow_zero, pow_zero]
    exact complexMatrixLpNormOfReal_cIdMatrix_le hn p hp
  | succ k ih =>
    rw [cMatPow_succ]
    calc complexMatrixLpNormOfReal hn p hp
          (complexMatrixMul M (cMatPow n M k))
        ≤ complexMatrixLpNormOfReal hn p hp M *
            complexMatrixLpNormOfReal hn p hp (cMatPow n M k) :=
          complexMatrixLpNormOfReal_mul_le hn hn hp M _
      _ ≤ c * c ^ k := mul_le_mul hM ih (hnonneg _) hc
      _ = c ^ (k + 1) := by ring

-- ============================================================
-- §18.1  Eq (18.5) alternative form, complex Jordan case, all 1 ≤ p < ∞
-- ============================================================

/-- **Higham 2nd ed., §18.1, eq (18.5) alternative form (p. 344, unnumbered
    display) at every real exponent `1 ≤ p < ∞` for complex Jordan data**:
    for complex bidiagonal Jordan-form-like data `X⁻¹AX = J` with
    `‖J_{ii}‖ ≤ ρ`, superdiagonal moduli ≤ 1, and a `β`-scaling vector `q`
    with `β^s ≤ q ≤ 1` obeying the run-step law across nonzero superdiagonal
    entries, the exact powers satisfy

      `‖A^k‖_p ≤ κ_p(X) · (β^s)⁻¹ · (ρ + β)^k`

    where `(β^s)⁻¹` bounds `κ_p(D)` for `D = diag(q)` (in the Jordan
    application `s = t − 1` with `t` the maximal block size, and `β` plays
    the role of the printed δ-margin, cf. `jordanBeta`).

    Honest scope: the printed display covers all p-norms; this closes every
    finite real exponent `1 ≤ p < ∞` for complex Jordan (defective) data;
    the `p = ∞` real-spectrum case is closed separately
    (`higham_eq_18_5_alt_real_jordan`, Algorithms/MatrixPowersJordan.lean).

    Structure: transport powers along `S = X·D`, `S⁻¹ = D⁻¹·X⁻¹`
    (`cMatPow_similarity`), bound the scaled bidiagonal `J' = D⁻¹JD` by
    `‖J'‖_p ≤ ρ + β` (`complexMatrixLpNormOfReal_bidiagonal_le` with the
    shift estimate `complexVecLpNorm_shift_le`), then chain
    submultiplicativity. -/
theorem higham_eq_18_5_alt_lp_jordan (n : ℕ) (hn : 0 < n)
    (A X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hXl : IsComplexMatrixRightInverse X_inv X)
    (hsim : complexMatrixMul X_inv (complexMatrixMul A X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (β : ℝ) (hβ0 : 0 < β) (s : ℕ)
    (q : Fin n → ℝ)
    (hq1 : ∀ i, β ^ s ≤ q i) (hq2 : ∀ i, q i ≤ 1)
    (hqstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      q j = β * q i)
    (p : ℝ) (hp : 1 ≤ p) (k : ℕ) :
    complexMatrixLpNormOfReal hn p hp (cMatPow n A k) ≤
      (complexMatrixLpNormOfReal hn p hp X *
        complexMatrixLpNormOfReal hn p hp X_inv) * (β ^ s)⁻¹ * (ρ + β) ^ k := by
  have hβs : (0 : ℝ) < β ^ s := pow_pos hβ0 s
  have hq0 : ∀ i, 0 < q i := fun i => lt_of_lt_of_le hβs (hq1 i)
  have hnonneg : ∀ M : CMatrix n n, 0 ≤ complexMatrixLpNormOfReal hn p hp M :=
    fun M => (hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal hn hp
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp M)).1
  set D := cDiagMatrix (fun a => ((q a : ℝ) : ℂ)) with hD
  set Dinv := cDiagMatrix (fun a => (((q a)⁻¹ : ℝ) : ℂ)) with hDinv
  set S := complexMatrixMul X D with hS
  set Sinv := complexMatrixMul Dinv X_inv with hSinv
  set J' := complexMatrixMul Dinv (complexMatrixMul J D) with hJ'
  -- D and D⁻¹ are a two-sided inverse pair through the vector action.
  have hDr : IsComplexMatrixRightInverse D Dinv := by
    intro x
    rw [hD, hDinv, cDiagMatrix_vecMul, cDiagMatrix_vecMul]
    funext i
    show ((q i : ℝ) : ℂ) * ((((q i)⁻¹ : ℝ) : ℂ) * x i) = x i
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hq0 i).ne',
      Complex.ofReal_one, one_mul]
  have hDl : IsComplexMatrixRightInverse Dinv D := by
    intro x
    rw [hD, hDinv, cDiagMatrix_vecMul, cDiagMatrix_vecMul]
    funext i
    show (((q i)⁻¹ : ℝ) : ℂ) * (((q i : ℝ) : ℂ) * x i) = x i
    rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ (hq0 i).ne',
      Complex.ofReal_one, one_mul]
  -- S = X·D and S⁻¹ = D⁻¹·X⁻¹ are a two-sided inverse pair.
  have hSr : IsComplexMatrixRightInverse S Sinv := by
    intro x
    rw [hS, hSinv, complexMatrixVecMul_mul, complexMatrixVecMul_mul]
    rw [hDr (complexMatrixVecMul X_inv x)]
    exact hXr x
  have hSl : IsComplexMatrixRightInverse Sinv S := by
    intro x
    rw [hS, hSinv, complexMatrixVecMul_mul, complexMatrixVecMul_mul]
    rw [hXl (complexMatrixVecMul D x)]
    exact hDl x
  -- The scaled similarity: S⁻¹·A·S = D⁻¹·J·D = J'.
  have hsim' : complexMatrixMul Sinv (complexMatrixMul A S) = J' := by
    rw [hS, hSinv, hJ']
    have h1 : complexMatrixMul X_inv
        (complexMatrixMul A (complexMatrixMul X D))
        = complexMatrixMul (complexMatrixMul X_inv (complexMatrixMul A X)) D := by
      simp only [complexMatrixMul_assoc]
    rw [complexMatrixMul_assoc Dinv X_inv
      (complexMatrixMul A (complexMatrixMul X D)), h1, hsim]
  have htrans := cMatPow_similarity n A S Sinv J' hSr hSl hsim' k
  -- The scaled bidiagonal bound ‖J'‖_p ≤ ρ + β.
  have hJ'norm : complexMatrixLpNormOfReal hn p hp J' ≤ ρ + β := by
    refine complexMatrixLpNormOfReal_bidiagonal_le hn p hp J' ρ β hρ0 hβ0.le
      ?_ ?_ ?_
    · -- shape: J' inherits the bidiagonal zero pattern from J
      intro i j hji1 hji2
      rw [hJ', hDinv, hD]
      have he : complexMatrixMul (cDiagMatrix fun a => (((q a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((q a : ℝ) : ℂ))) i j
          = (((q i)⁻¹ : ℝ) : ℂ) * J i j * ((q j : ℝ) : ℂ) :=
        cDiagMatrix_conj_entry J _ _ i j
      rw [he, hshape i j hji1 hji2, mul_zero, zero_mul]
    · -- diagonal: the conjugation fixes diagonal entries
      intro i
      rw [hJ', hDinv, hD]
      have he : complexMatrixMul (cDiagMatrix fun a => (((q a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((q a : ℝ) : ℂ))) i i
          = (((q i)⁻¹ : ℝ) : ℂ) * J i i * ((q i : ℝ) : ℂ) :=
        cDiagMatrix_conj_entry J _ _ i i
      have hpc : (((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hq0 i).ne',
          Complex.ofReal_one]
      have hdiagentry : (((q i)⁻¹ : ℝ) : ℂ) * J i i * ((q i : ℝ) : ℂ)
          = J i i := by
        calc (((q i)⁻¹ : ℝ) : ℂ) * J i i * ((q i : ℝ) : ℂ)
            = J i i * ((((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ)) := by ring
          _ = J i i := by rw [hpc, mul_one]
      rw [he, hdiagentry]
      exact hdiagbd i
    · -- superdiagonal: the run-step law compresses each entry to modulus ≤ β
      intro i j hji
      rw [hJ', hDinv, hD]
      have he : complexMatrixMul (cDiagMatrix fun a => (((q a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((q a : ℝ) : ℂ))) i j
          = (((q i)⁻¹ : ℝ) : ℂ) * J i j * ((q j : ℝ) : ℂ) :=
        cDiagMatrix_conj_entry J _ _ i j
      rw [he]
      by_cases hJz : J i j = 0
      · rw [hJz, mul_zero, zero_mul, norm_zero]
        exact hβ0.le
      · have hstep := hqstep i j hji hJz
        have hpc : (((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ) = 1 := by
          rw [← Complex.ofReal_mul, inv_mul_cancel₀ (hq0 i).ne',
            Complex.ofReal_one]
        have hentry : (((q i)⁻¹ : ℝ) : ℂ) * J i j * ((q j : ℝ) : ℂ)
            = ((β : ℝ) : ℂ) * J i j := by
          rw [hstep, Complex.ofReal_mul]
          calc (((q i)⁻¹ : ℝ) : ℂ) * J i j * (((β : ℝ) : ℂ) * ((q i : ℝ) : ℂ))
              = ((β : ℝ) : ℂ) * J i j *
                ((((q i)⁻¹ : ℝ) : ℂ) * ((q i : ℝ) : ℂ)) := by ring
            _ = ((β : ℝ) : ℂ) * J i j := by rw [hpc, mul_one]
        rw [hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hβ0.le]
        calc β * ‖J i j‖ ≤ β * 1 :=
              mul_le_mul_of_nonneg_left (hsup i j hji) hβ0.le
          _ = β := mul_one β
  have hJ'k : complexMatrixLpNormOfReal hn p hp (cMatPow n J' k) ≤
      (ρ + β) ^ k :=
    complexMatrixLpNormOfReal_cMatPow_le hn p hp J'
      (add_nonneg hρ0 hβ0.le) hJ'norm k
  -- Diagonal factor norms: ‖D‖_p ≤ 1 and ‖D⁻¹‖_p ≤ (β^s)⁻¹.
  have hDnorm : complexMatrixLpNormOfReal hn p hp D ≤ 1 := by
    rw [hD]
    refine complexMatrixLpNormOfReal_diagonal_le hn p hp _ zero_le_one
      (fun i => ?_)
    show ‖((q i : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0 i)]
    exact hq2 i
  have hDinvnorm : complexMatrixLpNormOfReal hn p hp Dinv ≤ (β ^ s)⁻¹ := by
    rw [hDinv]
    refine complexMatrixLpNormOfReal_diagonal_le hn p hp _
      (inv_nonneg.mpr hβs.le) (fun i => ?_)
    show ‖(((q i)⁻¹ : ℝ) : ℂ)‖ ≤ (β ^ s)⁻¹
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hq0 i))]
    exact inv_anti₀ hβs (hq1 i)
  have hSnorm : complexMatrixLpNormOfReal hn p hp S ≤
      complexMatrixLpNormOfReal hn p hp X := by
    calc complexMatrixLpNormOfReal hn p hp S
        ≤ complexMatrixLpNormOfReal hn p hp X *
            complexMatrixLpNormOfReal hn p hp D := by
          rw [hS]
          exact complexMatrixLpNormOfReal_mul_le hn hn hp X D
      _ ≤ complexMatrixLpNormOfReal hn p hp X * 1 :=
          mul_le_mul_of_nonneg_left hDnorm (hnonneg X)
      _ = complexMatrixLpNormOfReal hn p hp X := mul_one _
  have hSinvnorm : complexMatrixLpNormOfReal hn p hp Sinv ≤
      (β ^ s)⁻¹ * complexMatrixLpNormOfReal hn p hp X_inv := by
    calc complexMatrixLpNormOfReal hn p hp Sinv
        ≤ complexMatrixLpNormOfReal hn p hp Dinv *
            complexMatrixLpNormOfReal hn p hp X_inv := by
          rw [hSinv]
          exact complexMatrixLpNormOfReal_mul_le hn hn hp Dinv X_inv
      _ ≤ (β ^ s)⁻¹ * complexMatrixLpNormOfReal hn p hp X_inv :=
          mul_le_mul_of_nonneg_right hDinvnorm (hnonneg X_inv)
  rw [htrans]
  calc complexMatrixLpNormOfReal hn p hp
        (complexMatrixMul S (complexMatrixMul (cMatPow n J' k) Sinv))
      ≤ complexMatrixLpNormOfReal hn p hp S *
          complexMatrixLpNormOfReal hn p hp
            (complexMatrixMul (cMatPow n J' k) Sinv) :=
        complexMatrixLpNormOfReal_mul_le hn hn hp S _
    _ ≤ complexMatrixLpNormOfReal hn p hp S *
          (complexMatrixLpNormOfReal hn p hp (cMatPow n J' k) *
            complexMatrixLpNormOfReal hn p hp Sinv) :=
        mul_le_mul_of_nonneg_left
          (complexMatrixLpNormOfReal_mul_le hn hn hp _ Sinv) (hnonneg S)
    _ ≤ complexMatrixLpNormOfReal hn p hp X *
          ((ρ + β) ^ k *
            ((β ^ s)⁻¹ * complexMatrixLpNormOfReal hn p hp X_inv)) := by
        apply mul_le_mul hSnorm _
          (mul_nonneg (hnonneg _) (hnonneg _)) (hnonneg X)
        exact mul_le_mul hJ'k hSinvnorm (hnonneg Sinv)
          (pow_nonneg (add_nonneg hρ0 hβ0.le) k)
    _ = (complexMatrixLpNormOfReal hn p hp X *
          complexMatrixLpNormOfReal hn p hp X_inv) * (β ^ s)⁻¹ *
          (ρ + β) ^ k := by ring

end NumStability
