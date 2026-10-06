import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexDiagonal
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.VectorNorms.Basic

/-!
# Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexJordan

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

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
--   `complexVecLpNorm_ofReal_eq_sum_rpow`     — Analysis/VectorNorms/Basic.lean
--   `complexMatrixVecMul`, `complexMatrixMul`, `complexMatrixMul_assoc`,
--   `complexMatrixVecMul_mul`, `IsComplexMatrixRightInverse`
--                                             — Analysis/MatrixNorms/Basic.lean
--   `HasComplexMatrixLpBound`, `hasComplexMatrixLpBound_apply`,
--   `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`,
--   `complexMatrixLpNormOfReal` (+ value/bound/mul_le lemmas)
--                                             — Analysis/MatrixNorms/Lp.lean
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
    `complexMatrixLpNormOfReal_mul_le` (`Analysis/MatrixNorms/Lp.lean`). -/
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














































































































































































































end NumStability
