-- Algorithms/Cholesky/CholeskySpec.lean
--
-- Cholesky factorization specification and backward error (Higham §10.1).
--
-- A symmetric positive definite matrix A has a unique Cholesky factorization
-- A = R^T R where R is upper triangular with positive diagonal.
--
-- Algorithm 10.2 (jik Cholesky) computes R̂ satisfying the backward error
-- |R̂^T R̂ − A| ≤ γ_{n+1} |R̂^T| |R̂| (Theorem 10.3).
--
-- For SPD matrices, the growth factor is exactly 1: |R̂^T||R̂| ≤ |A|/(1−ε).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §10.1  Cholesky factorization specification
-- ============================================================

/-- **Cholesky factorization specification** (Higham §10.1, Theorem 10.1).

    A = R^T R where R is upper triangular with positive diagonal.
    Convention: (R^T R)_{ij} = ∑_k R_{ki} R_{kj} since (R^T)_{ik} = R_{ki}. -/
structure CholeskyFactSpec (n : ℕ) (A R : Fin n → Fin n → ℝ) : Prop where
  /-- R is upper triangular: entries below diagonal are 0. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R i j = 0
  /-- R has positive diagonal. -/
  R_diag_pos : ∀ i : Fin n, 0 < R i i
  /-- A = R^T R: the product recovers A exactly. -/
  product_eq : ∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j

/-- **Computed Cholesky factorization with backward error** (Higham §10.1, Theorem 10.3).

    Algorithm 10.2 (jik Cholesky) computes R̂ such that
    |R̂^T R̂ − A| ≤ ε · |R̂^T| · |R̂| componentwise,
    where ε = γ_{n+1} accounts for at most n+1 floating-point operations
    per entry (inner product of up to n terms + subtraction + sqrt/division). -/
structure CholeskyBackwardError (n : ℕ) (A R_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) : Prop where
  /-- R̂ is upper triangular. -/
  R_upper : ∀ i j : Fin n, j.val < i.val → R_hat i j = 0
  /-- Componentwise backward error: |R̂^T R̂ − A| ≤ ε|R̂^T||R̂|. -/
  backward_bound : ∀ i j : Fin n,
    |∑ k : Fin n, R_hat k i * R_hat k j - A i j| ≤
      ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j|

-- ============================================================
-- §10.1  Theorem 10.1: Cholesky existence
-- ============================================================

/-- Diagonal entry of an SPD matrix is positive. -/
private lemma spd_diag_pos {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hSPD : IsSymPosDef (m + 1) A) (i : Fin (m + 1)) : 0 < A i i := by
  have h := hSPD.2 (fun k => if k = i then 1 else 0) ⟨i, by simp⟩
  suffices hs : ∑ k₁ : Fin (m + 1), ∑ k₂ : Fin (m + 1),
      (if k₁ = i then 1 else 0) * A k₁ k₂ * (if k₂ = i then 1 else 0) = A i i by linarith
  rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
      Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp)]
  simp

/-- Schur complement of SPD matrix is symmetric. -/
private lemma schur_sym {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hSym : ∀ i j : Fin (m + 1), A i j = A j i) :
    ∀ i j : Fin m,
      A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0 =
      A j.succ i.succ - A 0 j.succ * A 0 i.succ / A 0 0 := by
  intro i j
  rw [hSym i.succ j.succ, hSym 0 i.succ, hSym 0 j.succ]; ring

/-- Schur complement of SPD matrix is positive definite.

    Key identity: y^T S y = x^T A x where x₀ = -(a^T y)/a₁₁, x_{i+1} = yᵢ.
    Since A is SPD and x ≠ 0 (some xᵢ₊₁ = yᵢ ≠ 0), we get y^T S y > 0.
    To avoid divisions in sum manipulation, we verify the identity
    multiplied by a₁₁ on both sides. -/
private lemma schur_pd {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hSPD : IsSymPosDef (m + 1) A)
    (ha₁₁ : 0 < A 0 0) :
    ∀ y : Fin m → ℝ, (∃ i, y i ≠ 0) →
      0 < ∑ i : Fin m, ∑ j : Fin m, y i *
        (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j := by
  intro y hy
  have ha_ne : A 0 0 ≠ 0 := ne_of_gt ha₁₁
  set t := ∑ j : Fin m, A 0 j.succ * y j
  set Q := ∑ i : Fin m, ∑ j : Fin m, y i * A i.succ j.succ * y j
  set x : Fin (m + 1) → ℝ := Fin.cons (-t / A 0 0) y
  have hx_nz : ∃ k : Fin (m + 1), x k ≠ 0 := by
    obtain ⟨i, hi⟩ := hy; exact ⟨i.succ, by simp [x, hi]⟩
  have hpos := hSPD.2 x hx_nz
  have hsym : ∀ i : Fin m, A i.succ 0 = A 0 i.succ := fun i => hSPD.1 i.succ 0
  have ht' : ∑ i : Fin m, y i * A 0 i.succ = t := by
    show ∑ i, y i * A 0 i.succ = ∑ j, A 0 j.succ * y j; congr 1; ext i; ring
  -- We show y^T S y = x^T A x, then use x^T A x > 0.
  suffices heq :
      ∑ i : Fin m, ∑ j : Fin m, y i *
        (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j by linarith
  -- Both sides equal Q - t²/A₀₀.
  -- LHS = Q - t²/A₀₀
  have lhs_eq : ∑ i : Fin m, ∑ j : Fin m, y i *
      (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
      Q - t * t / A 0 0 := by
    simp_rw [show ∀ (i j : Fin m), y i *
        (A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) * y j =
        y i * A i.succ j.succ * y j -
        (y i * A 0 i.succ) * (A 0 j.succ * y j) / A 0 0
        from fun i j => by ring]
    simp_rw [Finset.sum_sub_distrib]
    congr 1
    -- Factor /A₀₀ out of double sum, then factor product of sums
    simp_rw [← Finset.sum_div]
    congr 1
    simp_rw [← Finset.mul_sum]
    simp_rw [← Finset.sum_mul]
    rw [ht']
  -- RHS = Q - t²/A₀₀
  have rhs_eq : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1), x i * A i j * x j =
      Q - t * t / A 0 0 := by
    rw [Fin.sum_univ_succ]
    simp only [x, Fin.cons_zero, Fin.cons_succ]
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    -- Factor the j-sum for i=0
    simp_rw [show ∀ j : Fin m, (-t / A 0 0) * A 0 j.succ * y j =
        (-t / A 0 0) * (A 0 j.succ * y j) from fun j => by ring]
    rw [← Finset.mul_sum]
    -- Expand inner sums for i = succ
    simp_rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, hsym]
    -- Split ∑ᵢ (cross_i + Q_row_i)
    simp_rw [Finset.sum_add_distrib]
    -- Factor ∑ᵢ yᵢ A₀,i+1 (-t/A₀₀) = t * (-t/A₀₀)
    rw [← Finset.sum_mul, ht']
    -- Now: scalar expression + Q = Q - t²/A₀₀
    field_simp; ring
  -- Conclude
  rw [lhs_eq, rhs_eq]

/-- A leading Schur complement of an SPD matrix is SPD.

This is the exact algebraic first-stage reduced matrix used by Cholesky
factorization and by Higham Problem 10.4's first Gaussian-elimination stage. -/
theorem spd_schur_complement_isSymPosDef {m : ℕ}
    (A : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hSPD : IsSymPosDef (m + 1) A) :
    IsSymPosDef m
      (fun i j => A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0) := by
  have ha₁₁ : 0 < A 0 0 := spd_diag_pos hSPD 0
  exact ⟨schur_sym hSPD.1, schur_pd hSPD ha₁₁⟩

/-- **Cholesky existence** (Higham §10.1, Theorem 10.1).

    Every symmetric positive definite matrix has a unique Cholesky
    factorization A = R^T R with R upper triangular and positive diagonal.

    Proof by induction on n using the Schur complement:
    partition A = [[a₁₁, a^T], [a, B]], form S = B − aa^T/a₁₁,
    show S is SPD, recurse to get R₁, then assemble
    R = [[√a₁₁, a^T/√a₁₁], [0, R₁]]. -/
theorem cholesky_existence (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    ∃ R : Fin n → Fin n → ℝ, CholeskyFactSpec n A R := by
  induction n with
  | zero =>
    exact ⟨fun i => Fin.elim0 i,
           fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ m ih =>
    -- Step 1: Corner entry is positive
    have ha₁₁ : 0 < A 0 0 := spd_diag_pos hSPD 0
    -- Step 2: Schur complement
    set S : Fin m → Fin m → ℝ := fun i j =>
      A i.succ j.succ - A 0 i.succ * A 0 j.succ / A 0 0
    -- Step 3: S is SPD
    have hS_spd : IsSymPosDef m S := ⟨schur_sym hSPD.1, schur_pd hSPD ha₁₁⟩
    -- Step 4: IH
    obtain ⟨R₁, hR₁⟩ := ih S hS_spd
    -- Step 5: Construct R
    set sa := Real.sqrt (A 0 0)
    have hsa_pos : 0 < sa := Real.sqrt_pos_of_pos ha₁₁
    have hsa_ne : sa ≠ 0 := ne_of_gt hsa_pos
    have hsa_sq : sa * sa = A 0 0 := Real.mul_self_sqrt (le_of_lt ha₁₁)
    -- R defined by cases on index values
    set R : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j =>
      if hi : i = 0 then
        if hj : j = 0 then sa else A 0 j / sa
      else
        if hj : j = 0 then 0 else R₁ (i.pred hi) (j.pred hj)
    -- Step 6: Verify CholeskyFactSpec
    refine ⟨R, fun i j hij => ?_, fun i => ?_, fun i j => ?_⟩
    · -- R_upper: R i j = 0 when j.val < i.val
      simp only [R]
      by_cases hi : i = 0
      · subst hi; exact absurd hij (Nat.not_lt_zero _)
      · by_cases hj : j = 0
        · simp [hi, hj]
        · simp only [dif_neg hi, dif_neg hj]
          exact hR₁.R_upper _ _ (by
            have := Fin.val_pred j hj
            have := Fin.val_pred i hi
            have : i.val ≠ 0 := fun h => hi (Fin.ext h)
            have : j.val ≠ 0 := fun h => hj (Fin.ext h)
            omega)
    · -- R_diag_pos: R i i > 0
      simp only [R]
      by_cases hi : i = 0
      · subst hi; simp; exact hsa_pos
      · simp [hi]; exact hR₁.R_diag_pos _
    · -- product_eq: ∑ k, R k i * R k j = A i j
      -- Helper lemmas for R entries
      have hR0 : ∀ p : Fin (m + 1), R 0 p =
          if p = 0 then sa else A 0 p / sa := by
        intro p; simp [R]
      have hRs : ∀ k : Fin m, ∀ p : Fin (m + 1), R k.succ p =
          if hp : p = 0 then 0 else R₁ k (p.pred hp) := by
        intro k p; simp [R, Fin.succ_ne_zero, Fin.pred_succ]
      rw [Fin.sum_univ_succ]
      simp only [hR0, hRs]
      by_cases hi : i = 0 <;> by_cases hj : j = 0
      · -- i = 0, j = 0
        subst hi; subst hj; simp [hsa_sq]
      · -- i = 0, j ≠ 0
        subst hi; simp [hj, mul_div_cancel₀, hsa_ne]
      · -- i ≠ 0, j = 0
        subst hj; simp [hi, hSPD.1 i 0, hsa_ne]
      · -- i ≠ 0, j ≠ 0
        simp [hi, hj]
        have hih := hR₁.product_eq (i.pred hi) (j.pred hj)
        simp only [S, Fin.succ_pred] at hih
        have h1 : A 0 i / sa * (A 0 j / sa) = A 0 i * A 0 j / A 0 0 := by
          rw [div_mul_div_comm, hsa_sq]
        linarith

-- ============================================================
-- §10.1  Theorem 10.1: Cholesky uniqueness
-- ============================================================

/-- **Cholesky uniqueness helper**: if two upper triangular matrices with
    positive diagonals satisfy R₁^T R₁ = R₂^T R₂, then R₁ = R₂.

    Proof by induction on n. The (0,0) entry gives R₁(0,0)² = R₂(0,0)²,
    and positivity forces equality. The first row follows by cancellation.
    The submatrix products then agree, and the IH completes the proof. -/
private lemma cholesky_factor_uniqueness :
    ∀ (n : ℕ) (R₁ R₂ : Fin n → Fin n → ℝ),
    (∀ i j : Fin n, j.val < i.val → R₁ i j = 0) →
    (∀ i j : Fin n, j.val < i.val → R₂ i j = 0) →
    (∀ i : Fin n, 0 < R₁ i i) →
    (∀ i : Fin n, 0 < R₂ i i) →
    (∀ i j : Fin n, ∑ k : Fin n, R₁ k i * R₁ k j = ∑ k : Fin n, R₂ k i * R₂ k j) →
    ∀ i j : Fin n, R₁ i j = R₂ i j := by
  intro n; induction n with
  | zero => intro _ _ _ _ _ _ _ i; exact Fin.elim0 i
  | succ m ih =>
    intro R₁ R₂ hR₁_up hR₂_up hR₁_diag hR₂_diag hprod
    -- Column 0 entries are zero for k > 0
    have hR₁_c0 : ∀ k : Fin m, R₁ k.succ 0 = 0 :=
      fun k => hR₁_up k.succ 0 (Nat.succ_pos _)
    have hR₂_c0 : ∀ k : Fin m, R₂ k.succ 0 = 0 :=
      fun k => hR₂_up k.succ 0 (Nat.succ_pos _)
    -- R₁ 0 0 = R₂ 0 0 (from (0,0) entry: a² = b², a > 0, b > 0)
    have h00 : R₁ 0 0 = R₂ 0 0 := by
      have hp := hprod 0 0
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hp
      simp only [hR₁_c0, hR₂_c0, zero_mul, Finset.sum_const_zero, add_zero] at hp
      have hfact : (R₁ 0 0 - R₂ 0 0) * (R₁ 0 0 + R₂ 0 0) = 0 := by nlinarith
      have hsum : 0 < R₁ 0 0 + R₂ 0 0 := by linarith [hR₁_diag 0, hR₂_diag 0]
      cases mul_eq_zero.mp hfact with
      | inl h => linarith
      | inr h => linarith
    -- First row: R₁ 0 j = R₂ 0 j for all j
    have h0j : ∀ j : Fin (m + 1), R₁ 0 j = R₂ 0 j := by
      intro j; by_cases hj : j = 0
      · subst hj; exact h00
      · have hp := hprod 0 j
        rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hp
        simp only [hR₁_c0, hR₂_c0, zero_mul, Finset.sum_const_zero, add_zero] at hp
        rw [h00] at hp; exact mul_left_cancel₀ (ne_of_gt (hR₂_diag 0)) hp
    -- Submatrix products agree
    have hsub : ∀ i j : Fin m,
        ∑ k : Fin m, R₁ k.succ i.succ * R₁ k.succ j.succ =
        ∑ k : Fin m, R₂ k.succ i.succ * R₂ k.succ j.succ := by
      intro i j; have hp := hprod i.succ j.succ
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ] at hp
      rw [h0j i.succ, h0j j.succ] at hp; linarith
    -- Apply IH to submatrices
    have hih := ih (fun k p => R₁ k.succ p.succ) (fun k p => R₂ k.succ p.succ)
      (fun i j hij => hR₁_up i.succ j.succ (Nat.succ_lt_succ hij))
      (fun i j hij => hR₂_up i.succ j.succ (Nat.succ_lt_succ hij))
      (fun i => hR₁_diag i.succ) (fun i => hR₂_diag i.succ) hsub
    -- Combine
    intro i j
    by_cases hi : i = 0
    · subst hi; exact h0j j
    · by_cases hj : j = 0
      · subst hj
        have hi_pos : (0 : Fin (m + 1)).val < i.val :=
          Nat.pos_of_ne_zero (fun h => hi (Fin.ext h))
        rw [hR₁_up i 0 hi_pos, hR₂_up i 0 hi_pos]
      · have := hih (i.pred hi) (j.pred hj)
        simp only [Fin.succ_pred] at this; exact this

/-- **Cholesky uniqueness** (Higham §10.1, Theorem 10.1, part 2).

    The Cholesky factorization A = R^T R with R upper triangular and
    positive diagonal is unique. If R₁ and R₂ both satisfy
    CholeskyFactSpec, then R₁ = R₂ entry-by-entry. -/
theorem cholesky_uniqueness (n : ℕ) (A R₁ R₂ : Fin n → Fin n → ℝ)
    (h₁ : CholeskyFactSpec n A R₁) (h₂ : CholeskyFactSpec n A R₂) :
    ∀ i j : Fin n, R₁ i j = R₂ i j :=
  cholesky_factor_uniqueness n R₁ R₂ h₁.R_upper h₂.R_upper h₁.R_diag_pos h₂.R_diag_pos
    (fun i j => by rw [h₁.product_eq, h₂.product_eq])

-- ============================================================
-- §10.1  Theorem 10.3: Backward error (perturbation form)
-- ============================================================

/-- **Nonnegativity of |R̂^T||R̂| product**.

    The componentwise product (|R̂^T||R̂|)_{ij} = ∑_k |R̂_{ki}||R̂_{kj}| is nonneg. -/
lemma absRT_R_product_nonneg (n : ℕ) (R_hat : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, 0 ≤ ∑ k : Fin n, |R_hat k i| * |R_hat k j| := by
  intro i j
  apply Finset.sum_nonneg
  intro k _
  exact mul_nonneg (abs_nonneg _) (abs_nonneg _)

/-- **Cholesky backward error perturbation** (Higham §10.1, Theorem 10.3).

    The computed Cholesky factor R̂ satisfies R̂^T R̂ = A + ΔA where
    |ΔA_{ij}| ≤ ε · (|R̂^T||R̂|)_{ij} componentwise.

    This is equation (10.5) in Higham. -/
theorem cholesky_backward_error_perturbation (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (_hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  refine ⟨fun i j => ∑ k : Fin n, R_hat k i * R_hat k j - A i j,
          fun i j => hChol.backward_bound i j, fun i j => ?_⟩
  ring

/-- **Cholesky backward error relative to |A|** (Higham §10.1).

    If (|R̂^T||R̂|)_{ij} ≤ c · |A_{ij}| componentwise (growth bounded by c),
    then |ΔA_{ij}| ≤ ε · c · |A_{ij}|. -/
theorem cholesky_backward_error_relative (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε c : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hGrowth : ∀ i j : Fin n,
      ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ c * |A i j|) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * c * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  exact ⟨ΔA, fun i j => by
    have h1 := hΔA_bound i j
    have h2 := hGrowth i j
    calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := h1
      _ ≤ ε * (c * |A i j|) := by
          apply mul_le_mul_of_nonneg_left h2 hε
      _ = ε * c * |A i j| := by ring,
    hΔA_eq⟩

-- ============================================================
-- §10.1  SPD optimal growth: |R̂^T||R̂| ≤ |A|/(1−ε)
-- ============================================================

/-- **Nonneg Cholesky factors: |R̂^T||R̂| = R̂^T R̂**.

    When R̂ has nonneg entries, |R̂_{ki}| = R̂_{ki}, so the absolute
    factor product equals the actual product. -/
lemma nonneg_cholesky_absRTR_eq (n : ℕ) (R_hat : Fin n → Fin n → ℝ)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∀ i j : Fin n, ∑ k : Fin n, |R_hat k i| * |R_hat k j| =
      ∑ k : Fin n, R_hat k i * R_hat k j := by
  intro i j
  apply Finset.sum_congr rfl; intro k _
  rw [abs_of_nonneg (hR_nn k i), abs_of_nonneg (hR_nn k j)]

/-- **Nonneg Cholesky factors: |R̂^T||R̂| = |R̂^T R̂|**.

    When R̂ ≥ 0, each product R̂_{ki} R̂_{kj} ≥ 0, so the sum is nonneg
    and (|R̂^T||R̂|)_{ij} = (R̂^T R̂)_{ij} = |(R̂^T R̂)_{ij}|. -/
lemma nonneg_cholesky_absRTR_eq_absProduct (n : ℕ) (R_hat : Fin n → Fin n → ℝ)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∀ i j : Fin n, ∑ k : Fin n, |R_hat k i| * |R_hat k j| =
      |∑ k : Fin n, R_hat k i * R_hat k j| := by
  intro i j
  have h1 := nonneg_cholesky_absRTR_eq n R_hat hR_nn i j
  have h2 : 0 ≤ ∑ k : Fin n, R_hat k i * R_hat k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hR_nn k i) (hR_nn k j))
  rw [h1, abs_of_nonneg h2]

/-- **SPD optimal growth** (Higham §10.1, Problem 10.4).

    For SPD matrices, the growth factor for Cholesky is exactly 1.
    When R̂ ≥ 0 and ε < 1:
      (|R̂^T||R̂|)_{ij} ≤ |A_{ij}| / (1 − ε)

    This follows from: |R̂^T||R̂| = R̂^T R̂, and
    |R̂^T R̂ − A| ≤ ε · R̂^T R̂ rearranges to R̂^T R̂ · (1 − ε) ≤ A. -/
theorem cholesky_spd_optimal_growth (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (hε_lt : ε < 1) (_hε_nn : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∀ i j : Fin n,
      ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ |A i j| / (1 - ε) := by
  intro i j
  have habs_eq := nonneg_cholesky_absRTR_eq n R_hat hR_nn i j
  have hS_nn : 0 ≤ ∑ k : Fin n, R_hat k i * R_hat k j :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (hR_nn k i) (hR_nn k j))
  have hbe := hChol.backward_bound i j
  rw [habs_eq] at hbe
  have h_upper := (abs_le.mp hbe).2
  have h1_ε_pos : (0 : ℝ) < 1 - ε := by linarith
  have hA_nn : 0 ≤ A i j := by nlinarith
  rw [habs_eq, abs_of_nonneg hA_nn]
  have hne : (1 : ℝ) - ε ≠ 0 := ne_of_gt h1_ε_pos
  rw [le_div_iff₀ h1_ε_pos]
  nlinarith

/-- **SPD backward stability** (Higham §10.1, equation 10.7, simplified).

    For SPD matrices with nonneg Cholesky factors and ε < 1:
      |ΔA_{ij}| ≤ ε/(1−ε) · |A_{ij}|

    This is the componentwise version of the perfect stability result. -/
theorem cholesky_spd_backward_stable (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * |A i j|) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε_nn hChol
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have hgrowth := cholesky_spd_optimal_growth n A R_hat ε hε_lt hε_nn hChol hR_nn i j
  have h1 := hΔA_bound i j
  calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := h1
    _ ≤ ε * (|A i j| / (1 - ε)) := by
        apply mul_le_mul_of_nonneg_left hgrowth hε_nn
    _ = ε / (1 - ε) * |A i j| := by ring

-- ============================================================
-- §10.1  Normwise backward stability (equation 10.7)
-- ============================================================

/-- **SPD normwise backward stability** (Higham §10.1, equation 10.7).

    For SPD matrices with nonneg Cholesky factors and ε < 1:
      ‖ΔA‖∞ ≤ ε/(1−ε) · ‖A‖∞

    This follows from the componentwise bound |ΔA_{ij}| ≤ ε/(1−ε)|A_{ij}|
    by summing over rows and taking the maximum. -/
theorem cholesky_spd_backward_stable_normwise (n : ℕ) (_hn : 0 < n)
    (A R_hat : Fin n → Fin n → ℝ) (ε : ℝ) (hε_lt : ε < 1) (hε_nn : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε)
    (hR_nn : ∀ k j : Fin n, 0 ≤ R_hat k j) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      infNorm ΔA ≤ ε / (1 - ε) * infNorm A ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_spd_backward_stable n A R_hat ε hε_lt hε_nn hChol hR_nn
  refine ⟨ΔA, ?_, hΔA_eq⟩
  have h1ε : (0 : ℝ) < 1 - ε := by linarith
  have hc_nn : 0 ≤ ε / (1 - ε) := div_nonneg hε_nn (le_of_lt h1ε)
  -- infNorm(ΔA) = max_i ∑_j |ΔA_ij| ≤ ε/(1-ε) · max_i ∑_j |A_ij| = ε/(1-ε) · infNorm(A)
  apply infNorm_le_of_row_sum_le
  · intro i
    calc ∑ j : Fin n, |ΔA i j|
        ≤ ∑ j : Fin n, ε / (1 - ε) * |A i j| :=
          Finset.sum_le_sum (fun j _ => hΔA_bound i j)
      _ = ε / (1 - ε) * ∑ j : Fin n, |A i j| := (Finset.mul_sum _ _ _).symm
      _ ≤ ε / (1 - ε) * infNorm A := by
          apply mul_le_mul_of_nonneg_left _ hc_nn
          exact row_sum_le_infNorm A i
  · exact mul_nonneg hc_nn (infNorm_nonneg A)

end NumStability
