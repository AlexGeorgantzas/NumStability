-- Algorithms/LU/Ch15Problem4.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Problem 15.4 (Problems for Chapter 15).
--
--   "Let PA = LU be an LU factorization with partial pivoting of A ∈ ℝⁿˣⁿ.
--    Show that  ‖A⁻¹‖∞ / 2^{n-1}  ≤  ‖U⁻¹‖∞  ≤  n · ‖A⁻¹‖∞."
--
-- Intended Appendix A / textbook solution: from PA = LU one has
-- A⁻¹ = U⁻¹ L⁻¹ P, hence
--   (upper)  ‖U⁻¹‖∞ = ‖A⁻¹ P⁻¹ L‖∞ ≤ ‖A⁻¹‖∞ · ‖L‖∞  and, since L is unit
--            lower triangular with |Lᵢⱼ| ≤ 1 (partial pivoting), ‖L‖∞ ≤ n;
--   (lower)  ‖A⁻¹‖∞ ≤ ‖U⁻¹‖∞ · ‖L⁻¹‖∞  and, for unit lower triangular L
--            with |Lᵢⱼ| ≤ 1, the classic bound ‖L⁻¹‖∞ ≤ 2^{n-1} holds,
--            giving ‖A⁻¹‖∞ / 2^{n-1} ≤ ‖U⁻¹‖∞.
-- Permutation matrices preserve ‖·‖∞ (they only reorder rows / columns).
--
-- HONEST STATEMENT STRENGTH.  The printed constants `2^{n-1}` and `n` appear
-- in the CONCLUSION, derived, never assumed.  The partial-pivoting fact
-- `|Lᵢⱼ| ≤ 1` is taken as an explicit hypothesis (`hL_bound`) — it is the
-- DEFINITION of partial pivoting, not the conclusion.  The unit-lower-
-- triangular structure and the PA = LU relation are supplied through the
-- repository's `PermutedLUFactSpec` (Higham §9.1), and the inverses are
-- supplied as `IsInverse` witnesses.  No conclusion is smuggled into a
-- hypothesis.
--
-- IMPORT-ONLY module.  Reuses:
--   * `matMul`, `idMatrix`, `IsInverse`, `IsLeftInverse`, `IsRightInverse`,
--     `infNorm`, `infNorm_le_of_row_sum_le`, `row_sum_le_infNorm`,
--     `infNorm_matMul_le`, `matMul_assoc`, `matMul_id_left/right`
--     from `Analysis.MatrixAlgebra`;
--   * `PermutedLUFactSpec`, `IsPermutation` from `LU.GaussianElimination`.
-- The unit-lower-triangular inverse row-sum bound `‖L⁻¹‖∞ ≤ 2^{n-1}` is
-- proved here from scratch (the "double-S" trick on the forward-substitution
-- recurrence); the analogous UPPER-triangular bound is in
-- `TriangularForwardBound`, but the LOWER-triangular / row-oriented form used
-- here is not present, so it is established directly.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.LU.GaussianElimination

namespace NumStability.Ch15

open scoped BigOperators
open NumStability

-- ============================================================
-- Uniqueness of inverse (local re-proof of the standard fact)
-- ============================================================

/-- A left inverse and a right inverse of the same matrix coincide:
    `A = A(TB) = (AT)B = B`.  Re-proved locally from the `matMul`
    identity / associativity lemmas to avoid importing large chapters. -/
theorem ch15p4_leftInv_eq_rightInv {n : ℕ}
    (T A B : Fin n → Fin n → ℝ)
    (hA : IsLeftInverse n T A) (hB : IsRightInverse n T B) : A = B := by
  have hAT : matMul n A T = idMatrix n := by funext i j; exact hA i j
  have hTB : matMul n T B = idMatrix n := by funext i j; exact hB i j
  calc A = matMul n A (idMatrix n) := (matMul_id_right n A).symm
    _ = matMul n A (matMul n T B) := by rw [hTB]
    _ = matMul n (matMul n A T) B := (matMul_assoc n A T B).symm
    _ = matMul n (idMatrix n) B := by rw [hAT]
    _ = B := matMul_id_left n B

-- ============================================================
-- ‖L‖∞ ≤ n for unit lower triangular L with |Lᵢⱼ| ≤ 1
-- ============================================================

/-- Every entry of a unit lower triangular matrix with sub-diagonal entries
    bounded by 1 satisfies `|L i j| ≤ 1`. -/
theorem ch15p4_L_entry_le_one {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1) :
    ∀ i j : Fin n, |L i j| ≤ 1 := by
  intro i j
  rcases lt_trichotomy j.val i.val with h | h | h
  · exact hL_bound i j h
  · have : i = j := Fin.ext h.symm
    subst this; rw [hL_diag, abs_one]
  · rw [hL_upper i j h, abs_zero]; norm_num

/-- Row sums of a unit lower triangular matrix with `|Lᵢⱼ| ≤ 1` are `≤ n`. -/
theorem ch15p4_L_row_sum_le {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1) (i : Fin n) :
    ∑ j : Fin n, |L i j| ≤ (n : ℝ) := by
  have hentry := ch15p4_L_entry_le_one L hL_diag hL_upper hL_bound i
  calc ∑ j : Fin n, |L i j| ≤ ∑ _j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun j _ => hentry j)
    _ = (n : ℝ) := by simp

-- ============================================================
-- ‖L⁻¹‖∞ ≤ 2^{n-1} for unit lower triangular L with |Lᵢⱼ| ≤ 1
-- ============================================================

/-- The inverse of a unit lower triangular matrix is lower triangular:
    `L_inv i j = 0` for `i < j`.  (Left-inverse form.) -/
theorem ch15p4_Linv_upper_zero {n : ℕ} (L L_inv : Fin n → Fin n → ℝ)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hLInv : IsLeftInverse n L L_inv) :
    ∀ i j : Fin n, i.val < j.val → L_inv i j = 0 := by
  -- Downward induction on the target column: prove for large j first,
  -- via strong induction on (n - j.val).
  suffices H : ∀ (d : ℕ), ∀ (jv : ℕ) (hjv : jv < n), n - jv ≤ d →
      ∀ i : Fin n, i.val < jv → L_inv i ⟨jv, hjv⟩ = 0 by
    intro i j hij; exact H (n - j.val) j.val j.isLt (le_refl _) i hij
  intro d
  induction d with
  | zero => intro jv hjv hd i hi; omega
  | succ d' ih =>
    intro jv hjv hd i hi
    let j : Fin n := ⟨jv, hjv⟩
    have hij : i ≠ j := Fin.ne_of_val_ne (by simp [j]; omega)
    have hLd : L j j = 1 := hL_diag j
    have h := hLInv i j
    simp [hij] at h
    -- Isolate the k = j term of ∑_k L_inv i k * L k j.
    have hsum : ∑ k : Fin n, L_inv i k * L k j = L_inv i j * L j j := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
      have hrest : ∑ k ∈ Finset.univ.erase j, L_inv i k * L k j = 0 := by
        apply Finset.sum_eq_zero; intro k hk
        have hk_ne := Finset.ne_of_mem_erase hk
        by_cases hklt : k.val < jv
        · -- k < j ⟹ L_inv i k lies at column k with i < j; but here L k j = 0
          rw [hL_upper k j (by simp [j]; exact hklt), mul_zero]
        · push_neg at hklt
          have hkgt : jv < k.val := by
            rcases lt_or_eq_of_le hklt with h' | h'
            · exact h'
            · exact absurd (Fin.ext (by simp [j]; omega)) hk_ne
          rw [ih k.val k.isLt (by omega) i (by omega), zero_mul]
      -- ∑ = (k=j term) + rest, rest = 0
      have : L_inv i j * L j j +
          ∑ k ∈ Finset.univ.erase j, L_inv i k * L k j = L_inv i j * L j j := by
        rw [hrest]; ring
      linarith [this]
    have hval : L_inv i j * L j j = 0 := by rw [← hsum]; exact h
    rw [hLd, mul_one] at hval
    exact hval

/-- Diagonal entries of the inverse of a unit lower triangular matrix are 1. -/
theorem ch15p4_Linv_diag {n : ℕ} (L L_inv : Fin n → Fin n → ℝ)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hLInv : IsLeftInverse n L L_inv)
    (hInv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0) :
    ∀ i : Fin n, L_inv i i = 1 := by
  intro i
  have h := hLInv i i
  simp at h
  have honly : ∑ k : Fin n, L_inv i k * L k i = L_inv i i * L i i := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    have hrest : ∑ k ∈ Finset.univ.erase i, L_inv i k * L k i = 0 := by
      apply Finset.sum_eq_zero; intro k hk
      have hki := Finset.ne_of_mem_erase hk
      by_cases hlt : i.val < k.val
      · rw [hInv_lt i k hlt, zero_mul]
      · push_neg at hlt
        have : k.val < i.val := by
          rcases lt_or_eq_of_le hlt with h' | h'
          · exact h'
          · exact absurd (Fin.ext h') hki
        rw [hL_upper k i this, mul_zero]
    have : L_inv i i * L i i +
        ∑ k ∈ Finset.univ.erase i, L_inv i k * L k i = L_inv i i * L i i := by
      rw [hrest]; ring
    linarith [this]
  rw [honly, hL_diag i, mul_one] at h
  exact h

/-- Left-inverse recurrence for unit lower triangular `L`, fixed row `i`,
    target column `j < i`:
      `L_inv i j · L j j + ∑_{k: j<k≤i} L_inv i k · L k j = 0`.
    (This is the row-oriented mirror of `inv_left_recurrence`.) -/
theorem ch15p4_Linv_left_recurrence {n : ℕ} (L L_inv : Fin n → Fin n → ℝ)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hLInv : IsLeftInverse n L L_inv)
    (hInv_lt : ∀ i j : Fin n, i.val < j.val → L_inv i j = 0) :
    ∀ i j : Fin n, j.val < i.val →
      L_inv i j * L j j +
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val < k.val ∧ k.val ≤ i.val),
        L_inv i k * L k j = 0 := by
  intro i j hij
  have hL := hLInv i j
  simp [show i ≠ j from Fin.ne_of_val_ne (by omega)] at hL
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at hL
  have hrest : ∑ k ∈ Finset.univ.erase j, L_inv i k * L k j =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => j.val < k.val ∧ k.val ≤ i.val),
        L_inv i k * L k j := by
    symm; apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
      exact Finset.mem_erase.mpr ⟨Fin.ne_of_val_ne (by omega), Finset.mem_univ _⟩
    · intro k hk hknot
      rw [Finset.mem_erase] at hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hknot
      push_neg at hknot
      by_cases hlt : i.val < k.val
      · rw [hInv_lt i k hlt, zero_mul]
      · push_neg at hlt
        -- k ≤ i and not (j < k ∧ k ≤ i) with k ≠ j ⟹ k < j ⟹ L k j = 0
        by_cases hkj : j.val < k.val
        · exact absurd (hknot hkj) (by omega)
        · push_neg at hkj
          have : k.val < j.val := by
            rcases lt_or_eq_of_le hkj with h' | h'
            · exact h'
            · exact absurd (Fin.ext h') hk.1
          rw [hL_upper k j this, mul_zero]
  rw [hrest] at hL; linarith

/-- **Row-sum bound for the inverse of a unit lower triangular matrix.**
    For unit lower triangular `L` with `|Lᵢⱼ| ≤ 1`, and fixed row `i`,
    the partial row sum of `|L_inv|` over columns `jv ≤ k ≤ i` is `≤ 2^{i-jv}`.
    The full row sum (jv = 0) is therefore `≤ 2^{i.val} ≤ 2^{n-1}`.

    Proof: "double-S" trick.  Within a fixed row, downward induction on the
    starting column `jv`.  The recurrence bounds `|L_inv i j|` by the tail sum
    `∑_{j<k≤i}|L_inv i k|`, and the diagonal term is 1. -/
theorem ch15p4_Linv_row_partial_sum {n : ℕ} (L L_inv : Fin n → Fin n → ℝ)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1)
    (hLInv : IsLeftInverse n L L_inv) :
    ∀ (i : Fin n) (d : ℕ) (jv : ℕ) (hjv : jv < n),
      i.val - jv = d → jv ≤ i.val →
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => jv ≤ k.val ∧ k.val ≤ i.val),
        |L_inv i k| ≤ 2 ^ d := by
  have hInv_lt := ch15p4_Linv_upper_zero L L_inv hL_upper hL_diag hLInv
  have hInv_diag := ch15p4_Linv_diag L L_inv hL_upper hL_diag hLInv hInv_lt
  have hrec := ch15p4_Linv_left_recurrence L L_inv hL_upper hLInv hInv_lt
  intro i d
  induction d with
  | zero =>
    intro jv hjv hdiff hle
    -- jv = i.val, filter is {i}.
    have hji : jv = i.val := by omega
    have hfilt :
        Finset.univ.filter (fun k : Fin n => jv ≤ k.val ∧ k.val ≤ i.val)
          = {i} := by
      ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · intro ⟨h1, h2⟩; exact Fin.ext (by omega)
      · intro h; subst h; exact ⟨by omega, le_refl _⟩
    rw [hfilt, Finset.sum_singleton, hInv_diag, abs_one]; norm_num
  | succ d' ih =>
    intro jv hjv hdiff hle
    by_cases heq : jv = i.val
    · omega
    · have hjv' : jv < i.val := by omega
      let j : Fin n := ⟨jv, hjv⟩
      -- Split off k = j from the filter.
      have hj_mem : j ∈ Finset.univ.filter
          (fun k : Fin n => jv ≤ k.val ∧ k.val ≤ i.val) := by
        simp [Finset.mem_filter, j]; omega
      rw [← Finset.add_sum_erase _ _ hj_mem]
      -- The remaining sum ranges over j < k ≤ i.
      have hfilt_eq : (Finset.univ.filter
            (fun k : Fin n => jv ≤ k.val ∧ k.val ≤ i.val)).erase j =
          Finset.univ.filter (fun k : Fin n => jv + 1 ≤ k.val ∧ k.val ≤ i.val) := by
        ext k; simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · intro ⟨hne, h1, h2⟩
          refine ⟨?_, h2⟩
          rcases lt_or_eq_of_le h1 with h' | h'
          · omega
          · exact absurd (Fin.ext (by simp [j]; omega)) hne
        · intro ⟨h1, h2⟩
          exact ⟨Fin.ne_of_val_ne (by simp [j]; omega), by omega, h2⟩
      -- recurrence: |L_inv i j| ≤ ∑_{j<k≤i} |L_inv i k|.
      have hr := hrec i j hjv'
      rw [hL_diag j, mul_one] at hr
      have hvinv_eq : L_inv i j = -(∑ k ∈ Finset.univ.filter (fun k : Fin n =>
          j.val < k.val ∧ k.val ≤ i.val), L_inv i k * L k j) := by linarith
      have hvinv_bound : |L_inv i j| ≤
          ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            j.val < k.val ∧ k.val ≤ i.val), |L_inv i k| := by
        rw [hvinv_eq, abs_neg]
        calc |∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              j.val < k.val ∧ k.val ≤ i.val), L_inv i k * L k j|
            ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              j.val < k.val ∧ k.val ≤ i.val), |L_inv i k * L k j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              j.val < k.val ∧ k.val ≤ i.val), |L_inv i k| * |L k j| := by
              apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
          _ ≤ ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
              j.val < k.val ∧ k.val ≤ i.val), |L_inv i k| := by
              apply Finset.sum_le_sum; intro k hk
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
              -- k > j = column index, need |L k j| ≤ 1; here j < k so j.val<k.val
              have hLkj : |L k j| ≤ 1 := hL_bound k j hk.1
              calc |L_inv i k| * |L k j|
                  ≤ |L_inv i k| * 1 :=
                    mul_le_mul_of_nonneg_left hLkj (abs_nonneg _)
                _ = |L_inv i k| := mul_one _
      -- Rewrite the tail filter to `jv+1 ≤ k ≤ i` matching the IH.
      have hj_col : j.val = jv := rfl
      have hfilt_eq2 : Finset.univ.filter (fun k : Fin n =>
            j.val < k.val ∧ k.val ≤ i.val) =
          Finset.univ.filter (fun k : Fin n =>
            jv + 1 ≤ k.val ∧ k.val ≤ i.val) := by
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, hj_col]
        omega
      rw [hfilt_eq2] at hvinv_bound
      rw [hfilt_eq]
      -- IH on the tail: ∑_{jv+1≤k≤i} |L_inv i k| ≤ 2^{d'}.
      have hR : ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            jv + 1 ≤ k.val ∧ k.val ≤ i.val), |L_inv i k| ≤ 2 ^ d' := by
        exact ih (jv + 1) (by omega) (by omega) (by omega)
      have hsum : |L_inv i j| + ∑ k ∈ Finset.univ.filter (fun k : Fin n =>
            jv + 1 ≤ k.val ∧ k.val ≤ i.val), |L_inv i k|
          ≤ 2 ^ d' + 2 ^ d' := add_le_add (le_trans hvinv_bound hR) hR
      linarith [show (2 : ℝ) ^ d' + 2 ^ d' = 2 ^ (d' + 1) by ring]

/-- The full row sum of `|L_inv|` in row `i` is `≤ 2^{i.val} ≤ 2^{n-1}`,
    for unit lower triangular `L` with `|Lᵢⱼ| ≤ 1`. -/
theorem ch15p4_Linv_row_sum_le {n : ℕ} (L L_inv : Fin n → Fin n → ℝ)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1)
    (hLInv : IsLeftInverse n L L_inv) (i : Fin n) :
    ∑ j : Fin n, |L_inv i j| ≤ 2 ^ (n - 1) := by
  have hpartial :=
    ch15p4_Linv_row_partial_sum L L_inv hL_upper hL_diag hL_bound hLInv
      i i.val 0 (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt) (by omega) (by omega)
  -- The filter with jv = 0 is the whole universe.
  have hfilt : Finset.univ.filter (fun k : Fin n => 0 ≤ k.val ∧ k.val ≤ i.val)
      = Finset.univ.filter (fun k : Fin n => k.val ≤ i.val) := by
    ext k; simp [Finset.mem_filter]
  rw [hfilt] at hpartial
  -- Off the filter, L_inv i k = 0 (upper zero), so the sum over the filter
  -- equals the full row sum.
  have hInv_lt := ch15p4_Linv_upper_zero L L_inv hL_upper hL_diag hLInv
  have hfull : ∑ j : Fin n, |L_inv i j| =
      ∑ k ∈ Finset.univ.filter (fun k : Fin n => k.val ≤ i.val), |L_inv i k| := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro k _ hknot
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hknot
    rw [hInv_lt i k hknot, abs_zero]
  rw [hfull]
  refine le_trans hpartial ?_
  -- 2^{i.val} ≤ 2^{n-1}
  have : i.val ≤ n - 1 := by omega
  exact pow_le_pow_right₀ (by norm_num) this

/-- **‖L⁻¹‖∞ ≤ 2^{n-1}** for unit lower triangular `L` with `|Lᵢⱼ| ≤ 1`.
    The classic Higham §8.3 bound, in the ∞-operator-norm (`infNorm`) form. -/
theorem ch15p4_infNorm_Linv_le {n : ℕ} (L L_inv : Fin n → Fin n → ℝ)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1)
    (hLInv : IsLeftInverse n L L_inv) :
    infNorm L_inv ≤ 2 ^ (n - 1) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    exact ch15p4_Linv_row_sum_le L L_inv hL_upper hL_diag hL_bound hLInv i
  · positivity

/-- **‖L‖∞ ≤ n** for unit lower triangular `L` with `|Lᵢⱼ| ≤ 1`. -/
theorem ch15p4_infNorm_L_le {n : ℕ} (L : Fin n → Fin n → ℝ)
    (hL_diag : ∀ i : Fin n, L i i = 1)
    (hL_upper : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1) :
    infNorm L ≤ (n : ℝ) := by
  apply infNorm_le_of_row_sum_le
  · intro i; exact ch15p4_L_row_sum_le L hL_diag hL_upper hL_bound i
  · positivity

-- ============================================================
-- Factorization identities from PA = LU
-- ============================================================

/-- From `PermutedLUFactSpec`, the row-permuted `L` times `U` reproduces `A`:
    with `e := Equiv.ofBijective σ`, `matMul n (fun i j => L (e.symm i) j) U = A`.
    (This is `P⁻¹ L · U = A`, i.e. `A = P⁻¹ (LU) = P⁻¹ (PA)`.) -/
theorem ch15p4_permL_mul_U_eq_A {n : ℕ} (A L U : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (spec : PermutedLUFactSpec n A L U σ) :
    let e := Equiv.ofBijective σ spec.perm
    matMul n (fun i j => L (e.symm i) j) U = A := by
  intro e
  funext i j
  show ∑ k : Fin n, L (e.symm i) k * U k j = A i j
  have h := spec.product_eq (e.symm i) j
  have he : σ (e.symm i) = i := Equiv.apply_symm_apply e i
  rw [h, he]

/-- **Upper-bound identity**: `U⁻¹ = A⁻¹ · (P⁻¹ L)`.
    With `e := Equiv.ofBijective σ`, `Uinv = matMul n Ainv (fun i j => L (e.symm i) j)`.
    Proved by uniqueness of inverse: the right side is a LEFT inverse of `U`,
    and `Uinv` is a RIGHT inverse of `U`. -/
theorem ch15p4_Uinv_eq {n : ℕ} (A L U Ainv Uinv : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (spec : PermutedLUFactSpec n A L U σ)
    (hAinv : IsInverse n A Ainv) (hUinv : IsInverse n U Uinv) :
    let e := Equiv.ofBijective σ spec.perm
    matMul n Ainv (fun i j => L (e.symm i) j) = Uinv := by
  intro e
  set Q : Fin n → Fin n → ℝ := fun i j => L (e.symm i) j with hQ
  have hQU : matMul n Q U = A := ch15p4_permL_mul_U_eq_A A L U σ spec
  -- (Ainv Q) U = Ainv (Q U) = Ainv A = I ⟹ Ainv Q is a left inverse of U.
  have hleft : IsLeftInverse n U (matMul n Ainv Q) := by
    intro i j
    have : matMul n (matMul n Ainv Q) U = idMatrix n := by
      rw [matMul_assoc, hQU]
      funext a b; exact hAinv.1 a b
    exact congrFun (congrFun this i) j
  exact ch15p4_leftInv_eq_rightInv U (matMul n Ainv Q) Uinv hleft hUinv.2

/-- **Lower-bound identity**: `A⁻¹ = (U⁻¹ L⁻¹) · P`.
    With `e := Equiv.ofBijective σ`,
    `Ainv = fun i j => (matMul n Uinv Linv) i (e.symm j)`.
    Proved by uniqueness of inverse: the right side is a LEFT inverse of `A`,
    and `Ainv` is a RIGHT inverse of `A`. -/
theorem ch15p4_Ainv_eq {n : ℕ} (A L U Ainv Uinv Linv : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (spec : PermutedLUFactSpec n A L U σ)
    (hAinv : IsInverse n A Ainv) (hUinv : IsInverse n U Uinv)
    (hLinv : IsInverse n L Linv) :
    let e := Equiv.ofBijective σ spec.perm
    (fun i j => matMul n Uinv Linv i (e.symm j)) = Ainv := by
  intro e
  set R : Fin n → Fin n → ℝ := matMul n Uinv Linv with hR
  set RP : Fin n → Fin n → ℝ := fun i j => R i (e.symm j) with hRP
  -- R · (LU) = Uinv (Linv (L U)) = Uinv (I U) = Uinv U = I.
  have hR_LU : matMul n R (matMul n L U) = idMatrix n := by
    rw [hR, matMul_assoc]
    have hLinvLU : matMul n Linv (matMul n L U) = U := by
      rw [← matMul_assoc]
      have : matMul n Linv L = idMatrix n := by funext a b; exact hLinv.1 a b
      rw [this, matMul_id_left]
    rw [hLinvLU]
    funext a b; exact hUinv.1 a b
  -- RP · A = I via the reindexing ∑_k R i (e.symm k) A k j = ∑_m R i m (LU) m j.
  have hleft : IsLeftInverse n A RP := by
    intro i j
    have hreindex :
        (∑ k : Fin n, RP i k * A k j) = matMul n R (matMul n L U) i j := by
      show (∑ k : Fin n, R i (e.symm k) * A k j) =
        ∑ m : Fin n, R i m * (∑ l : Fin n, L m l * U l j)
      -- reindex k = e m
      rw [← Equiv.sum_comp e (fun k => R i (e.symm k) * A k j)]
      apply Finset.sum_congr rfl
      intro m _
      have hsym : e.symm (e m) = m := Equiv.symm_apply_apply e m
      have hAe : A (e m) j = ∑ l : Fin n, L m l * U l j :=
        (spec.product_eq m j).symm
      rw [hsym, hAe]
    rw [hreindex, hR_LU]; rfl
  have := ch15p4_leftInv_eq_rightInv A RP Ainv hleft hAinv.2
  rw [← this]

-- ============================================================
-- Problem 15.4: the two-sided inequality
-- ============================================================

/-- **Higham, 2nd ed., Problem 15.4.**

    Let `PA = LU` be an LU factorization with partial pivoting of `A ∈ ℝⁿˣⁿ`
    (modelled by `PermutedLUFactSpec`, with `L` unit lower triangular and the
    partial-pivoting bound `|Lᵢⱼ| ≤ 1` supplied explicitly as `hL_bound`).
    Given two-sided inverses `Ainv, Uinv, Linv` of `A, U, L`, then

      ‖A⁻¹‖∞ / 2^{n-1}  ≤  ‖U⁻¹‖∞  ≤  n · ‖A⁻¹‖∞.

    The printed constants `2^{n-1}` and `n` appear in the conclusion, derived
    from `A⁻¹ = U⁻¹L⁻¹P` via ∞-norm submultiplicativity, the row-sum bound
    `‖L‖∞ ≤ n`, and the classic `‖L⁻¹‖∞ ≤ 2^{n-1}`. -/
theorem ch15p4_infNorm_Uinv_two_sided {n : ℕ}
    (A L U Ainv Uinv Linv : Fin n → Fin n → ℝ)
    (σ : Fin n → Fin n) (spec : PermutedLUFactSpec n A L U σ)
    (hL_bound : ∀ i j : Fin n, j.val < i.val → |L i j| ≤ 1)
    (hAinv : IsInverse n A Ainv) (hUinv : IsInverse n U Uinv)
    (hLinv : IsInverse n L Linv) :
    infNorm Ainv / 2 ^ (n - 1) ≤ infNorm Uinv ∧
      infNorm Uinv ≤ (n : ℝ) * infNorm Ainv := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · -- n = 0: every ∞-norm is 0.
    subst hn0
    have hz : ∀ M : Fin 0 → Fin 0 → ℝ, infNorm M = 0 := by
      intro M
      refine le_antisymm ?_ (infNorm_nonneg M)
      exact infNorm_le_of_row_sum_le M (fun i => i.elim0) (le_refl 0)
    rw [hz Ainv, hz Uinv]
    constructor
    · simp
    · simp
  · set e := Equiv.ofBijective σ spec.perm with he
    have hLdiag := spec.L_diag
    have hLupper := spec.L_upper_zero
    -- ‖L‖∞ ≤ n and ‖L⁻¹‖∞ ≤ 2^{n-1}
    have hLnorm : infNorm L ≤ (n : ℝ) :=
      ch15p4_infNorm_L_le L hLdiag hLupper hL_bound
    have hLinv_norm : infNorm Linv ≤ 2 ^ (n - 1) :=
      ch15p4_infNorm_Linv_le L Linv hLupper hLdiag hL_bound hLinv.1
    constructor
    · -- Lower bound: ‖A⁻¹‖∞ ≤ ‖U⁻¹‖∞ · 2^{n-1}, then divide.
      have hAinv_eq := ch15p4_Ainv_eq A L U Ainv Uinv Linv σ spec hAinv hUinv hLinv
      set R : Fin n → Fin n → ℝ := matMul n Uinv Linv with hRdef
      -- ‖A⁻¹‖∞ ≤ ‖R‖∞ (columns of R permuted by e.symm ⟹ same row sums).
      have hAinv_le_R : infNorm Ainv ≤ infNorm R := by
        apply infNorm_le_of_row_sum_le
        · intro i
          have hrow : (∑ j : Fin n, |Ainv i j|) = ∑ j : Fin n, |R i (e.symm j)| := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← hAinv_eq]
          rw [hrow]
          -- ∑_j |R i (e.symm j)| = ∑_k |R i k| ≤ ‖R‖∞
          rw [← Equiv.sum_comp e (fun j => |R i (e.symm j)|)]
          have : (∑ m : Fin n, |R i (e.symm (e m))|) = ∑ m : Fin n, |R i m| := by
            apply Finset.sum_congr rfl
            intro m _; rw [Equiv.symm_apply_apply e m]
          rw [this]
          exact row_sum_le_infNorm R i
        · exact infNorm_nonneg R
      -- ‖R‖∞ ≤ ‖U⁻¹‖∞ · 2^{n-1}
      have hR_le : infNorm R ≤ infNorm Uinv * 2 ^ (n - 1) := by
        calc infNorm R = infNorm (matMul n Uinv Linv) := by rw [hRdef]
          _ ≤ infNorm Uinv * infNorm Linv := infNorm_matMul_le hn Uinv Linv
          _ ≤ infNorm Uinv * 2 ^ (n - 1) :=
              mul_le_mul_of_nonneg_left hLinv_norm (infNorm_nonneg Uinv)
      have hAinv_le : infNorm Ainv ≤ infNorm Uinv * 2 ^ (n - 1) :=
        le_trans hAinv_le_R hR_le
      -- Divide by 2^{n-1} > 0.
      rw [div_le_iff₀ (by positivity)]
      linarith
    · -- Upper bound: ‖U⁻¹‖∞ = ‖A⁻¹ · (P⁻¹ L)‖∞ ≤ ‖A⁻¹‖∞ · ‖P⁻¹L‖∞ ≤ ‖A⁻¹‖∞ · n.
      have hUinv_eq := ch15p4_Uinv_eq A L U Ainv Uinv σ spec hAinv hUinv
      set Q : Fin n → Fin n → ℝ := fun i j => L (e.symm i) j with hQdef
      -- ‖Q‖∞ ≤ n (rows of Q are rows of L, permuted).
      have hQ_le : infNorm Q ≤ (n : ℝ) := by
        apply infNorm_le_of_row_sum_le
        · intro i
          show (∑ j : Fin n, |L (e.symm i) j|) ≤ (n : ℝ)
          exact ch15p4_L_row_sum_le L hLdiag hLupper hL_bound (e.symm i)
        · positivity
      have hUinv_le : infNorm Uinv ≤ infNorm Ainv * (n : ℝ) := by
        calc infNorm Uinv = infNorm (matMul n Ainv Q) := by rw [← hUinv_eq]
          _ ≤ infNorm Ainv * infNorm Q := infNorm_matMul_le hn Ainv Q
          _ ≤ infNorm Ainv * (n : ℝ) :=
              mul_le_mul_of_nonneg_left hQ_le (infNorm_nonneg Ainv)
      rw [mul_comm]; exact hUinv_le

end NumStability.Ch15
