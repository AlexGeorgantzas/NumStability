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
# Existence

Canonical destination for 7 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.CholeskyPSD` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- Diagonal entry of a PSD matrix is nonnegative. -/
private lemma psd_diag_nonneg {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (i : Fin (m + 1)) : 0 ≤ A i i := by
  have h := hPSD.2 (fun k => if k = i then 1 else 0)
  suffices hs : ∑ k₁ : Fin (m + 1), ∑ k₂ : Fin (m + 1),
      (if k₁ = i then 1 else 0) * A k₁ k₂ * (if k₂ = i then 1 else 0) = A i i by linarith
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
      Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp)]
  simp

/-- If a PSD matrix has A_{00} = 0, then the entire first row is zero.

    Proof: the quadratic form x^T A x evaluated at x = e_0 + t·e_{j+1}
    gives 2t·A_{0,j+1} + t²·A_{j+1,j+1} ≥ 0 for all t, forcing A_{0,j+1} = 0. -/
private lemma psd_zero_diag_row_zero {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hPSD : IsPosSemiDef (m + 1) A) (h00 : A 0 0 = 0) (j : Fin m) :
    A 0 j.succ = 0 := by
  set a := A 0 j.succ
  set d := A j.succ j.succ
  have hd_nn : 0 ≤ d := psd_diag_nonneg hPSD j.succ
  -- Key: for all t, 0 ≤ 2ta + t²d (= x^T A x for x = e_0 + t·e_{j+1})
  suffices key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * d by
    by_cases hd : d = 0
    · have h1 := key 1; have h2 := key (-1); nlinarith
    · have hd_pos : 0 < d := lt_of_le_of_ne hd_nn (Ne.symm hd)
      have h := key (-a / d)
      have hcalc : 2 * (-a / d) * a + (-a / d) ^ 2 * d = -(a ^ 2 / d) := by
        field_simp; ring
      rw [hcalc] at h
      have h_pos : 0 ≤ a ^ 2 / d := div_nonneg (sq_nonneg a) (le_of_lt hd_pos)
      have h_zero : a ^ 2 / d = 0 := le_antisymm (by linarith) h_pos
      have ha_sq : a ^ 2 = 0 := by
        by_contra h_ne
        exact absurd h_zero (ne_of_gt (div_pos (lt_of_le_of_ne (sq_nonneg a)
          (Ne.symm h_ne)) hd_pos))
      exact sq_eq_zero_iff.mp ha_sq
  -- Prove: x^T A x = 2ta + t²d for suitable x
  intro t
  have hpsd := hPSD.2 (fun k => if k = (0 : Fin (m + 1)) then 1
    else if k = j.succ then t else 0)
  suffices heval : ∑ i : Fin (m + 1), ∑ k : Fin (m + 1),
      (if i = (0 : Fin (m + 1)) then 1 else if i = j.succ then t else 0) * A i k *
      (if k = (0 : Fin (m + 1)) then 1 else if k = j.succ then t else 0) =
      2 * t * a + t ^ 2 * d by linarith
  -- Inner sum: ∑_k A_{ik} · x_k = A_{i,0} + t · A_{i,j+1}
  have inner : ∀ i : Fin (m + 1), ∑ k : Fin (m + 1), A i k *
      (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0) =
      A i 0 + t * A i j.succ := by
    intro i; rw [Fin.sum_univ_succ]; simp only [ite_true, mul_one]
    congr 1
    rw [Finset.sum_eq_single j]
    · simp only [show j.succ ≠ (0 : Fin (m + 1)) from Fin.succ_ne_zero _,
                  ite_false, ite_true]; ring
    · intro b _ hb
      have : b.succ ≠ j.succ := fun h => hb (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- Factor x_i out and apply inner sum
  simp_rw [show ∀ (i k : Fin (m + 1)),
      (if i = (0 : Fin (m + 1)) then (1 : ℝ) else if i = j.succ then t else 0) * A i k *
      (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0) =
      (if i = (0 : Fin (m + 1)) then (1 : ℝ) else if i = j.succ then t else 0) *
      (A i k * (if k = (0 : Fin (m + 1)) then (1 : ℝ) else if k = j.succ then t else 0))
    from fun i k => by ring]
  simp_rw [← Finset.mul_sum, inner]
  -- Outer sum: ∑_i x_i · (A_{i,0} + t·A_{i,j+1})
  rw [Fin.sum_univ_succ]
  simp only [ite_true, one_mul]
  rw [Finset.sum_eq_single j]
  · simp only [show j.succ ≠ (0 : Fin (m + 1)) from Fin.succ_ne_zero _,
                ite_false, ite_true]
    rw [h00, hPSD.1 j.succ 0]; ring
  · intro b _ hb
    have : b.succ ≠ j.succ := fun h => hb (Fin.succ_injective _ h)
    simp [Fin.succ_ne_zero, this]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **PSD Cholesky existence** (Higham §10.3, Theorem 10.9, part a).

    Every positive semidefinite matrix has a factorization A = R^T R
    with R upper triangular and nonnegative diagonal.

    Proof by induction on n using the Schur complement:
    - If A_{00} = 0: first row/column is zero, recurse on submatrix.
    - If A_{00} > 0: form Schur complement S (PSD), recurse,
      assemble R = [[√a₁₁, a^T/√a₁₁], [0, R₁]]. -/
theorem psd_cholesky_existence (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ R : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → R i j = 0) ∧
      (∀ i : Fin n, 0 ≤ R i i) ∧
      (∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j) := by
  induction n with
  | zero =>
    exact ⟨fun i => Fin.elim0 i,
           fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    have ha₁₁_nn : 0 ≤ A 0 0 := psd_diag_nonneg hPSD 0
    by_cases ha₁₁ : A 0 0 = 0
    · -- Case A₀₀ = 0: first row/column is zero
      have hrow : ∀ j : Fin m, A 0 j.succ = 0 := psd_zero_diag_row_zero hPSD ha₁₁
      have hcol : ∀ i : Fin m, A i.succ 0 = 0 := fun i => by rw [hPSD.1]; exact hrow i
      -- Lower-right submatrix is PSD
      set B : Fin m → Fin m → ℝ := fun i j => A i.succ j.succ
      have hB_psd : IsPosSemiDef m B := by
        constructor
        · intro i j; exact hPSD.1 i.succ j.succ
        · intro y
          set x : Fin (m + 1) → ℝ := Fin.cons 0 y
          have h := hPSD.2 x
          suffices heq : ∑ i : Fin m, ∑ j : Fin m, y i * B i j * y j =
              ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
          rw [Fin.sum_univ_succ]
          simp only [x, Fin.cons_zero, zero_mul, Finset.sum_const_zero, zero_add]
          simp_rw [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add, B]
      obtain ⟨R₁, hR₁_upper, hR₁_diag, hR₁_prod⟩ := ih B hB_psd
      -- R: first row all zero, rest = R₁
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
        if hi : i = 0 then 0
        else if hj : j = 0 then 0
        else R₁ (i.pred hi) (j.pred hj)
      have hR0 : ∀ p : Fin (m + 1), R 0 p = 0 := fun p => by simp [R]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
      · -- R_upper
        simp only [R]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hR₁_upper _ _ (by
              have := Fin.val_pred j hj
              have := Fin.val_pred i hi
              have : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have : j.val ≠ 0 := fun h => hj (Fin.ext h)
              omega)
      · -- R_diag nonneg
        simp only [R]
        by_cases hi : i = 0
        · simp [hi]
        · simp [hi]; exact hR₁_diag _
      · -- product_eq
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj; simp [ha₁₁]
        · subst hi; simp only [dite_true]; simp [hj]
          have := hrow (j.pred hj)
          rw [Fin.succ_pred] at this; exact this.symm
        · subst hj; simp only [dite_true]; simp [hi]
          have := hcol (i.pred hi)
          rw [Fin.succ_pred] at this; exact this.symm
        · simp [hi, hj]
          have hih := hR₁_prod (i.pred hi) (j.pred hj)
          simp only [B, Fin.succ_pred] at hih
          linarith
    · -- Case A₀₀ > 0: Schur complement induction
      have ha₁₁_pos : 0 < A 0 0 := lt_of_le_of_ne ha₁₁_nn (Ne.symm ha₁₁)
      set S : Fin m → Fin m → ℝ := fun i j =>
        A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
      have hS_psd := schur_psd hPSD ha₁₁_pos
      obtain ⟨R₁, hR₁_upper, hR₁_diag, hR₁_prod⟩ := ih S hS_psd
      set sa := Real.sqrt (A 0 0)
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos ha₁₁_pos
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = A 0 0 := Real.mul_self_sqrt (le_of_lt ha₁₁_pos)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
        if hi : i = 0 then
          if hj : j = 0 then sa else A 0 j / sa
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj)
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else A 0 p / sa := by
        intro p; simp [R]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
      · -- R_upper
        simp only [R]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hR₁_upper _ _ (by
              have := Fin.val_pred j hj
              have := Fin.val_pred i hi
              have : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have : j.val ≠ 0 := fun h => hj (Fin.ext h)
              omega)
      · -- R_diag nonneg
        simp only [R]
        by_cases hi : i = 0
        · subst hi; simp; exact le_of_lt hsa_pos
        · simp [hi]; exact hR₁_diag _
      · -- product_eq (same structure as cholesky_existence)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj; simp [hsa_sq]
        · subst hi; simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj; simp [hi, hPSD.1 i 0, hsa_ne]
        · simp [hi, hj]
          have hih := hR₁_prod (i.pred hi) (j.pred hj)
          simp only [S, Fin.succ_pred] at hih
          have h1 : A 0 i / sa * (A 0 j / sa) = A 0 i * A 0 j / A 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          linarith

/-- **Theorem 10.9(b), constructive core** (Higham §10.3, equation
    (10.11)): every real PSD matrix admits a pivoted Cholesky
    factorization `Πᵀ A Π = RᵀR` in the displayed rank-truncated form,
    with the permutation produced by greedy complete pivoting and `r`
    the number of positive pivots encountered.  Identification of `r`
    with the matrix rank is left as a separate row over Mathlib's rank. -/
theorem psd_pivoted_cholesky_exists (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
      fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0, Function.bijective_id,
        fun i j _ => rfl, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i j _ => rfl, fun i j => ?_⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, _⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
        fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
        fun i j => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · show ∑ k : Fin (m + 1), R k i * R k j =
          B (extendPerm σ' i) (extendPerm σ' j)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring

/-- **Theorem 10.9(b) with the complete-pivoting invariant**: the greedy
    construction additionally yields nonincreasing factor diagonal —
    `R l l ≤ R k k` for `k ≤ l` — the per-stage maximality that together
    with `pivoted_spec_column_split` gives the display (10.13). -/
theorem psd_pivoted_cholesky_exists_cp (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r ∧
      ∀ k l : Fin n, k.val ≤ l.val → R l l ≤ R k k := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      ⟨Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
       fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun k => Fin.elim0 k⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0,
        ⟨Function.bijective_id, fun i j _ => rfl,
         fun i hi => absurd hi (Nat.not_lt_zero _),
         fun i j _ => rfl, fun i j => ?_⟩,
        fun k l _ => le_rfl⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, hτ_max⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec, hmono⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      -- the tail's leading diagonal is bounded by the pivot root
      have hR₁_le_sa : ∀ i : Fin m, R₁ i i ≤ sa := by
        intro i
        rcases Nat.eq_zero_or_pos m with hm | hm
        · exact absurd i.isLt (by omega)
        · have h0m : (0 : ℕ) < m := hm
          have hhead : R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ * R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ =
              S (σ' ⟨0, h0m⟩) (σ' ⟨0, h0m⟩) := by
            have h := hspec.product_eq ⟨0, h0m⟩ ⟨0, h0m⟩
            rw [show ∑ k : Fin m, R₁ k ⟨0, h0m⟩ * R₁ k ⟨0, h0m⟩ =
                R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ * R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ from ?_] at h
            · exact h
            · rw [Finset.sum_eq_single ⟨0, h0m⟩]
              · intro b _ hb
                rw [hspec.R_upper b ⟨0, h0m⟩ (by
                  have hb0 : b.val ≠ 0 := fun h0 => hb (Fin.ext h0)
                  show 0 < b.val
                  omega), zero_mul]
              · intro habs
                exact absurd (Finset.mem_univ _) habs
          have hSmax : S (σ' ⟨0, h0m⟩) (σ' ⟨0, h0m⟩) ≤ B 0 0 :=
            schur_diag_le_pivot B hB00 (fun i => hτ_max i) _
          have hi_le : R₁ i i ≤ R₁ ⟨0, h0m⟩ ⟨0, h0m⟩ :=
            hmono ⟨0, h0m⟩ i (by simp)
          have hnn := pivoted_spec_diag_nonneg hspec ⟨0, h0m⟩
          nlinarith [pivoted_spec_diag_nonneg hspec i, hsa_sq, hsa_pos]
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        ⟨hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
         fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
         fun i j => ?_⟩, fun k l hkl => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · show ∑ k : Fin (m + 1), R k i * R k j =
          B (extendPerm σ' i) (extendPerm σ' j)
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring
      · -- diagonal monotonicity
        simp only [hRdef]
        by_cases hk : k = 0
        · subst hk
          by_cases hl : l = 0
          · subst hl; simp
          · simp only [dif_neg hl]
            exact hR₁_le_sa _
        · have hlk : l ≠ 0 := by
            intro h0
            apply hk
            apply Fin.ext
            have hl0 : l.val = 0 := by simp [h0]
            omega
          simp only [dif_neg hk, dif_neg hlk]
          exact hmono _ _ (by
            have := Fin.val_pred k hk
            have := Fin.val_pred l hlk
            omega)

/-- Reindex a succ-tail filter sum over `Fin (m+1)` to a tail filter sum
    over `Fin m`. -/
private lemma sum_filter_succ_tail {m : ℕ} (k₀ : ℕ)
    (f : Fin (m + 1) → ℝ) :
    (∑ i ∈ Finset.univ.filter
      (fun i : Fin (m + 1) => k₀ + 1 ≤ i.val), f i) =
    ∑ i₀ ∈ Finset.univ.filter (fun i₀ : Fin m => k₀ ≤ i₀.val),
      f i₀.succ := by
  have himg : (Finset.univ.filter
      (fun i₀ : Fin m => k₀ ≤ i₀.val)).image Fin.succ =
      Finset.univ.filter (fun i : Fin (m + 1) => k₀ + 1 ≤ i.val) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨i₀, hi₀, rfl⟩
      simp only [Fin.val_succ]
      omega
    · intro hi
      have hne : i ≠ 0 := by
        intro h0
        rw [h0] at hi
        simp at hi
      refine ⟨i.pred hne, ?_, Fin.succ_pred i hne⟩
      have := Fin.val_pred i hne
      omega
  rw [← himg, Finset.sum_image
    (fun a _ b _ h => Fin.succ_injective m h)]

/-- **Theorem 10.9(b) with the (10.13) column-tail invariant**: the greedy
    complete-pivoting construction yields, beyond the pivoted certificate,
    the stage-wise column-tail domination
    `∑_{i ≥ k} r_ij² ≤ r_kk²` for `k ≤ j` — precisely the content of the
    display (10.13). -/
theorem psd_pivoted_cholesky_exists_tail (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A) :
    ∃ (r : ℕ) (σ : Fin n → Fin n) (R : Fin n → Fin n → ℝ),
      PivotedCholeskySpec n A R σ r ∧
      ∀ k j : Fin n, k.val ≤ j.val →
        (∑ i ∈ Finset.univ.filter (fun i : Fin n => k.val ≤ i.val),
          R i j ^ 2) ≤ R k k ^ 2 := by
  induction n with
  | zero =>
    exact ⟨0, id, fun i => Fin.elim0 i,
      ⟨Function.bijective_id, fun i => Fin.elim0 i, fun i => Fin.elim0 i,
       fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩,
      fun k => Fin.elim0 k⟩
  | succ m ih =>
    by_cases hall : ∀ i, A i i = 0
    · have hzero := psd_all_diag_zero A hPSD hall
      refine ⟨0, id, fun _ _ => 0,
        ⟨Function.bijective_id, fun i j _ => rfl,
         fun i hi => absurd hi (Nat.not_lt_zero _),
         fun i j _ => rfl, fun i j => ?_⟩,
        fun k j _ => by simp⟩
      show ∑ k : Fin (m + 1), (0:ℝ) * 0 = A i j
      rw [hzero i j]
      simp
    · push_neg at hall
      obtain ⟨w, hw⟩ := hall
      have hw_pos : 0 < A w w :=
        lt_of_le_of_ne (psd_diag_nonneg hPSD w) (Ne.symm hw)
      obtain ⟨τ, hτ_perm, hτ_pos, hτ_max⟩ :=
        psd_pivot_selection A ⟨w, hw_pos⟩
      set B : Fin (m + 1) → Fin (m + 1) → ℝ :=
        fun i j => A (τ i) (τ j) with hBdef
      have hB_psd : IsPosSemiDef (m + 1) B :=
        isPosSemiDef_perm (m + 1) A τ hτ_perm hPSD
      have hB00 : 0 < B 0 0 := hτ_pos
      set S : Fin m → Fin m → ℝ := fun i j =>
        B i.succ j.succ - B 0 i.succ * B 0 j.succ / B 0 0 with hSdef
      have hS_psd := schur_psd hB_psd hB00
      obtain ⟨r', σ', R₁, hspec, htail⟩ := ih S hS_psd
      set sa := Real.sqrt (B 0 0) with hsadef
      have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos hB00
      have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
      have hsa_sq : sa * sa = B 0 0 :=
        Real.mul_self_sqrt (le_of_lt hB00)
      set R : Fin (m + 1) → Fin (m + 1) → ℝ := (fun i j =>
        if hi : i = 0 then
          (if j = 0 then sa else B 0 (extendPerm σ' j) / sa)
        else
          if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj))
        with hRdef
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else B 0 (extendPerm σ' p) / sa := by
        intro p; simp [hRdef]
      have hRs : ∀ (k : Fin m) (p : Fin (m + 1)), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [hRdef, Fin.succ_ne_zero, Fin.pred_succ]
      have hext : ∀ (p : Fin (m + 1)) (hp : p ≠ 0),
          extendPerm σ' p = (σ' (p.pred hp)).succ := by
        intro p hp
        conv_lhs => rw [← Fin.succ_pred p hp]
        rw [extendPerm_succ]
      have hproduct : ∀ i j : Fin (m + 1),
          ∑ p : Fin (m + 1), R p i * R p j =
          B (extendPerm σ' i) (extendPerm σ' j) := by
        intro i j
        rw [Fin.sum_univ_succ]
        simp only [hR0, hRs]
        by_cases hi : i = 0 <;> by_cases hj : j = 0
        · subst hi; subst hj
          simp [hsa_sq]
        · subst hi
          simp [hj, mul_div_cancel₀, hsa_ne]
        · subst hj
          simp [hi, hsa_ne, hB_psd.1 (extendPerm σ' i) 0]
        · simp only [if_neg hi, if_neg hj, dif_neg hi, dif_neg hj]
          have hih := hspec.product_eq (i.pred hi) (j.pred hj)
          rw [hext i hi, hext j hj, hih]
          have h1 : B 0 (σ' (i.pred hi)).succ / sa *
              (B 0 (σ' (j.pred hj)).succ / sa) =
              B 0 (σ' (i.pred hi)).succ *
                B 0 (σ' (j.pred hj)).succ / B 0 0 := by
            rw [div_mul_div_comm, hsa_sq]
          rw [h1]
          simp only [hSdef]
          ring
      refine ⟨r' + 1, fun i => τ (extendPerm σ' i), R,
        ⟨hτ_perm.comp (extendPerm_isPermutation σ' hspec.perm),
         fun i j hij => ?_, fun i hir => ?_, fun i j hri => ?_,
         fun i j => hproduct i j⟩, fun k j hkj => ?_⟩
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; exact absurd hij (Nat.not_lt_zero _)
        · by_cases hj : j = 0
          · simp [hi, hj]
          · simp only [dif_neg hi, dif_neg hj]
            exact hspec.R_upper _ _ (by
              have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
              have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
              have := Fin.val_pred i hi
              have := Fin.val_pred j hj
              omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi; simp [hsa_pos]
        · simp only [dif_neg hi]
          exact hspec.R_diag_pos _ (by
            have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have := Fin.val_pred i hi
            omega)
      · simp only [hRdef]
        by_cases hi : i = 0
        · subst hi
          exact absurd hri (by simp)
        · simp only [dif_neg hi]
          by_cases hj : j = 0
          · simp [hj]
          · simp only [dif_neg hj]
            exact hspec.R_rank_zero _ _ (by
              have := Fin.val_pred i hi
              omega)
      · -- column-tail domination (the (10.13) invariant)
        by_cases hk : k = 0
        · subst hk
          have hfilter : Finset.univ.filter
              (fun i : Fin (m + 1) => (0 : Fin (m + 1)).val ≤ i.val) =
              Finset.univ := by
            ext i; simp
          rw [hfilter]
          have hsum : ∑ i : Fin (m + 1), R i j ^ 2 =
              B (extendPerm σ' j) (extendPerm σ' j) := by
            rw [← hproduct j j]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hsum]
          have hR00 : R 0 0 = sa := by rw [hR0 0]; simp
          rw [hR00]
          calc B (extendPerm σ' j) (extendPerm σ' j) ≤ B 0 0 :=
              hτ_max (extendPerm σ' j)
            _ = sa ^ 2 := by rw [← hsa_sq]; ring
        · have hj0 : j ≠ 0 := by
            intro h0
            apply hk
            apply Fin.ext
            have hjv : j.val = 0 := by simp [h0]
            omega
          have hkval : k.val = (k.pred hk).val + 1 := by
            have := Fin.val_pred k hk
            have hkv : k.val ≠ 0 := fun h => hk (Fin.ext h)
            omega
          have hfeq : Finset.univ.filter
              (fun i : Fin (m + 1) => k.val ≤ i.val) =
              Finset.univ.filter
              (fun i : Fin (m + 1) => (k.pred hk).val + 1 ≤ i.val) := by
            apply Finset.filter_congr
            intro i _
            constructor <;> intro h <;> omega
          rw [hfeq, sum_filter_succ_tail (k.pred hk).val
            (fun i => R i j ^ 2)]
          have hterm : ∀ i₀ : Fin m, R i₀.succ j ^ 2 =
              R₁ i₀ (j.pred hj0) ^ 2 := by
            intro i₀
            rw [hRs i₀ j, dif_neg hj0]
          rw [Finset.sum_congr rfl fun i₀ _ => hterm i₀]
          have hkk : R k k = R₁ (k.pred hk) (k.pred hk) := by
            conv_lhs => rw [← Fin.succ_pred k hk]
            rw [hRs (k.pred hk) (k.pred hk).succ,
              dif_neg (Fin.succ_ne_zero _), Fin.pred_succ]
          rw [hkk]
          exact htail (k.pred hk) (j.pred hj0) (by
            have := Fin.val_pred j hj0
            have := Fin.val_pred k hk
            omega)

end NumStability
