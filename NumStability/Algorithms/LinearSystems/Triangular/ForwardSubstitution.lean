import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold

/-!
# Forward substitution

Reusable forward-substitution algorithm and backward-error analysis for lower
triangular systems.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §8.1  Algorithm definition (Algorithm 8.2)
-- ============================================================

/-- Auxiliary for forward substitution: solve rows `n-k, n-k+1, …, n-1` given
    that rows `0, 1, …, n-k-1` are already in `x`.

    The recursion counts down from `k = n` (nothing solved) to `k = 0`
    (everything solved), processing row `n-k` at each step. -/
noncomputable def fl_forwardSub_steps (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0,     _,  x => x
  | k + 1, hk, x =>
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let m := n - k - 1  -- number of off-diagonal terms for this row
      let s := Fin.foldl m (fun acc (t : Fin m) =>
                  fp.fl_sub acc
                    (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                               (x   ⟨t.val, by omega⟩)))
                (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      fl_forwardSub_steps fp n L b k (Nat.le_of_succ_le hk) x'

/-- Floating-point forward substitution: solve Lx = b for lower triangular L.

    Implements Algorithm 8.2 (Higham §8.1), processing rows from 0 up
    to n-1.  For row i with m = i off-diagonal terms:
      s = b i;  for j < i: s = fl_sub(s, fl_mul(L i j, x̂ j));  x̂ i = fl_div(s, L i i) -/
noncomputable def fl_forwardSub (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_forwardSub_steps fp n L b n (le_refl n) (fun _ => 0)

-- ============================================================
-- §8.1  Structural lemmas for fl_forwardSub_steps
-- ============================================================

/-- `fl_forwardSub_steps` preserves entries at indices < n-k (already solved). -/
private lemma fl_forwardSub_steps_stable (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (j : Fin n),
      j.val < n - k → fl_forwardSub_steps fp n L b k hk x j = x j := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro hk x j hjk
    unfold fl_forwardSub_steps
    simp only
    have hjk' : j.val < n - k := by omega
    rw [ih (Nat.le_of_succ_le hk) _ j hjk']
    rw [Function.update_of_ne]
    intro heq
    have : j.val = n - k - 1 := congr_arg Fin.val heq
    omega

/-- At row n-k-1, `fl_forwardSub_steps` sets x[n-k-1] = fl_div(s, L_{n-k-1,n-k-1})
    where s is the inner fold using the final values at indices < n-k-1. -/
private lemma fl_forwardSub_steps_at_row (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (k : ℕ) (hk : k + 1 ≤ n) (x : Fin n → ℝ) :
    let ik : Fin n := ⟨n - k - 1, by omega⟩
    let m := n - k - 1
    let x_final := fl_forwardSub_steps fp n L b (k + 1) hk x
    x_final ik = fp.fl_div
      (Fin.foldl m (fun acc (t : Fin m) =>
        fp.fl_sub acc
          (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                     (x_final ⟨t.val, by omega⟩)))
        (b ik))
      (L ik ik) := by
  simp only [fl_forwardSub_steps]
  rw [fl_forwardSub_steps_stable fp n L b k (Nat.le_of_succ_le hk) _
      ⟨n - k - 1, by omega⟩ (by omega : n - k - 1 < n - k)]
  rw [Function.update_self]
  congr 1
  congr 1
  funext acc t
  congr 1; congr 1
  symm
  rw [fl_forwardSub_steps_stable fp n L b k (Nat.le_of_succ_le hk) _
      ⟨t.val, by omega⟩ (by omega : t.val < n - k)]
  rw [Function.update_of_ne]
  intro heq; have := congr_arg Fin.val heq; simp at this; omega

-- ============================================================
-- §8.1  Per-row computation specification
-- ============================================================

/-- **Reindexing**: a sum over `Fin m` with identity index map equals the sum over
    the filtered finset `{j : Fin n | j < k}` where m = k.  This connects the
    fold-based algorithm (which uses `Fin m` with `m = i`) to the specification
    (which uses `Finset.filter`). -/
private lemma sum_fin_eq_sum_filter_lt {n k : ℕ} (hk : k ≤ n) (f : Fin n → ℝ) :
    (∑ t : Fin k, f ⟨t.val, by omega⟩) =
    Finset.sum (Finset.filter (fun j : Fin n => j.val < k) Finset.univ) f := by
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  rw [← himg, Finset.sum_image hinj]

/-- `fl_forwardSub_steps` decomposes: applying p steps from x can be split as
    q steps from some intermediate state x'. -/
private lemma fl_forwardSub_steps_decompose (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (p q : ℕ) (hp : p ≤ n) (hq : q ≤ p) (x : Fin n → ℝ) :
    ∃ x', fl_forwardSub_steps fp n L b p hp x =
          fl_forwardSub_steps fp n L b q (le_trans hq hp) x' := by
  induction p generalizing x with
  | zero =>
    have : q = 0 := by omega
    subst this; exact ⟨x, rfl⟩
  | succ p ih =>
    rcases Nat.eq_or_lt_of_le hq with rfl | hlt
    · exact ⟨x, rfl⟩
    · simp only [fl_forwardSub_steps]
      exact ih (Nat.le_of_succ_le hp) (by omega : q ≤ p) _

/-- For each row i, `fl_forwardSub i` equals `fl_div(fold, L_ii)` where the fold
    uses `fl_forwardSub` values at indices < i. -/
private lemma fl_forwardSub_at_row (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    fl_forwardSub fp n L b i = fp.fl_div
      (Fin.foldl i.val (fun acc (t : Fin i.val) =>
        fp.fl_sub acc
          (fp.fl_mul (L i ⟨t.val, by omega⟩)
                     (fl_forwardSub fp n L b ⟨t.val, by omega⟩)))
        (b i))
      (L i i) := by
  -- i corresponds to row n - (n - i.val - 1) - 1 = i in the step counting
  set k := n - i.val - 1 with hk_def
  have hk1 : k + 1 ≤ n := by omega
  have hrow : n - k - 1 = i.val := by omega
  obtain ⟨x_mid, hdecomp⟩ :=
    fl_forwardSub_steps_decompose fp n L b n (k + 1) (le_refl n) hk1 (fun _ => 0)
  have h_pw : ∀ j : Fin n, fl_forwardSub fp n L b j =
      fl_forwardSub_steps fp n L b (k + 1) hk1 x_mid j :=
    fun j => congr_fun hdecomp j
  have hat := fl_forwardSub_steps_at_row fp n L b k hk1 x_mid
  -- ⟨n-k-1, _⟩ = i since n-k-1 = i.val
  have hik : (⟨n - k - 1, by omega⟩ : Fin n) = i := Fin.ext (by omega)
  -- Rewrite hat to use i and i.val
  simp only [show n - k - 1 = i.val from hrow] at hat
  rw [h_pw i]
  have h_fn : fl_forwardSub fp n L b = fl_forwardSub_steps fp n L b (k + 1) hk1 x_mid :=
    funext h_pw
  rw [h_fn]
  exact hat

/-- Per-row computation specification for forward substitution.

    Row `i` of forward substitution computes x̂_i such that there exist
    rounding errors Θ_i, θ_ij (combined mul+sub fold) and ρ_i (from division)
    satisfying:

      L_ii * x̂_i = (b_i * (1 + Θ_i) - ∑_{j<i} L_ij * x̂_j * (1 + θ_ij)) * (1 + ρ_i)

    with |Θ_i| ≤ γ(i), |θ_ij| ≤ γ(i + 1), |ρ_i| ≤ u, where i
    is the number of off-diagonal terms in row i. -/
def ForwardSubRowSpec (fp : FPModel) (n : ℕ) (L : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n), ∃ (Θ : ℝ) (ρ : ℝ) (θ : Fin n → ℝ),
    |Θ| ≤ gamma fp i.val ∧
    |ρ| ≤ fp.u ∧
    (∀ j, |θ j| ≤ gamma fp (i.val + 1)) ∧
    L i i * x_hat i =
      (b i * (1 + Θ) -
       Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
         (fun j => L i j * x_hat j * (1 + θ j))) * (1 + ρ)

/-- **Per-row backward error**: for row `i`, the algorithm produces an equation
    matching ForwardSubRowSpec using the final solution vector. -/
private lemma fl_forwardSub_row_spec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (Θ : ℝ) (ρ : ℝ) (θ : Fin n → ℝ),
      |Θ| ≤ gamma fp i.val ∧
      |ρ| ≤ fp.u ∧
      (∀ j, |θ j| ≤ gamma fp (i.val + 1)) ∧
      L i i * fl_forwardSub fp n L b i =
        (b i * (1 + Θ) -
         Finset.sum (Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ)
           (fun j => L i j * fl_forwardSub fp n L b j * (1 + θ j))) * (1 + ρ) := by
  set m := i.val with hm_def
  -- Step 1: x̂_i = fl_div(s, L_ii) where s is the subtraction fold
  have hat := fl_forwardSub_at_row fp n L b i
  set s := Fin.foldl m (fun acc (t : Fin m) =>
    fp.fl_sub acc
      (fp.fl_mul (L i ⟨t.val, by omega⟩)
                 (fl_forwardSub fp n L b ⟨t.val, by omega⟩)))
    (b i)
  -- Step 2: Extract division error ρ
  obtain ⟨ρ, hρ, hfl_div⟩ := fp.model_div s (L i i) (hL i)
  have hLx : L i i * fl_forwardSub fp n L b i = s * (1 + ρ) := by
    rw [hat, hfl_div]
    have h := hL i; field_simp
  -- Step 3: Apply fl_sub_sum_error_init to expand s
  let t_vals : Fin m → ℝ := fun t =>
    fp.fl_mul (L i ⟨t.val, by omega⟩)
              (fl_forwardSub fp n L b ⟨t.val, by omega⟩)
  have hs_fold : s = Fin.foldl m (fun acc j => fp.fl_sub acc (t_vals j)) (b i) := rfl
  have hm_le : m ≤ n := by omega
  have hm_valid : gammaValid fp m := gammaValid_mono fp hm_le hn
  obtain ⟨Θ_sub, θ_sub, hΘ_sub, hθ_sub, hfold_eq⟩ :=
    fl_sub_sum_error_init fp m t_vals (b i) hm_valid
  rw [← hs_fold] at hfold_eq
  -- Step 4: Expand each fl_mul via model_mul
  have hmul_expand : ∀ t : Fin m,
      ∃ δ : ℝ, |δ| ≤ fp.u ∧
        t_vals t = L i ⟨t.val, by omega⟩ *
                   fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1 + δ) := by
    intro t
    obtain ⟨δ, hδ, hfl_mul⟩ := fp.model_mul
      (L i ⟨t.val, by omega⟩) (fl_forwardSub fp n L b ⟨t.val, by omega⟩)
    exact ⟨δ, hδ, hfl_mul⟩
  let δ_vals : Fin m → ℝ := fun t => Classical.choose (hmul_expand t)
  have hδ_bound : ∀ t, |δ_vals t| ≤ fp.u := fun t =>
    (Classical.choose_spec (hmul_expand t)).1
  have hδ_eq : ∀ t, t_vals t =
      L i ⟨t.val, by omega⟩ * fl_forwardSub fp n L b ⟨t.val, by omega⟩ *
      (1 + δ_vals t) := fun t =>
    (Classical.choose_spec (hmul_expand t)).2
  -- Step 5: Combine (1 + δ_t) * (1 + θ_sub t) via gamma_mul
  have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
  have h1m_le : 1 + m ≤ n := by omega
  have h1m_valid : gammaValid fp (1 + m) := gammaValid_mono fp h1m_le hn
  have hcombine : ∀ t : Fin m,
      ∃ η : ℝ, |η| ≤ gamma fp (1 + m) ∧
        (1 + δ_vals t) * (1 + θ_sub t) = 1 + η := by
    intro t
    have hδ_γ1 : |δ_vals t| ≤ gamma fp 1 :=
      le_trans (hδ_bound t) (u_le_gamma fp one_pos h1valid)
    exact gamma_mul fp 1 m (δ_vals t) (θ_sub t) hδ_γ1 (hθ_sub t) h1m_valid
  let η_vals : Fin m → ℝ := fun t => Classical.choose (hcombine t)
  have hη_bound : ∀ t, |η_vals t| ≤ gamma fp (1 + m) := fun t =>
    (Classical.choose_spec (hcombine t)).1
  have hη_eq : ∀ t, (1 + δ_vals t) * (1 + θ_sub t) = 1 + η_vals t := fun t =>
    (Classical.choose_spec (hcombine t)).2
  -- Step 6: Rewrite the sum
  have hsum_rw : ∑ t : Fin m, t_vals t * (1 + θ_sub t) =
      ∑ t : Fin m, L i ⟨t.val, by omega⟩ *
        fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1 + η_vals t) := by
    apply Finset.sum_congr rfl; intro t _
    rw [hδ_eq t]
    have hassoc : L i ⟨t.val, by omega⟩ *
        fl_forwardSub fp n L b ⟨t.val, by omega⟩ *
        (1 + δ_vals t) * (1 + θ_sub t) =
      L i ⟨t.val, by omega⟩ *
        fl_forwardSub fp n L b ⟨t.val, by omega⟩ *
        ((1 + δ_vals t) * (1 + θ_sub t)) := by ring
    rw [hassoc, hη_eq t]
  -- Step 7: Build witnesses
  have h1m_eq : 1 + m = i.val + 1 := by omega
  let θ_full : Fin n → ℝ := fun j =>
    if h : j.val < i.val then η_vals ⟨j.val, by omega⟩
    else 0
  refine ⟨Θ_sub, ρ, θ_full, ?_, ?_, ?_, ?_⟩
  · exact hΘ_sub
  · exact hρ
  · intro j; simp only [θ_full]
    by_cases hij : j.val < i.val
    · simp only [hij, dite_true]
      have := hη_bound ⟨j.val, by omega⟩
      rwa [h1m_eq] at this
    · simp only [hij, dite_false, abs_zero]
      exact gamma_nonneg fp (gammaValid_mono fp (by omega) hn)
  · -- The equation
    rw [hLx, hfold_eq, hsum_rw]
    congr 1; congr 1
    -- Reindex: ∑ over Fin m → ∑ over {j | j < i.val}
    let g : Fin n → ℝ := fun j => L i j * fl_forwardSub fp n L b j * (1 + θ_full j)
    have hsummand_eq : ∀ t : Fin m,
        L i ⟨t.val, by omega⟩ *
          fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1 + η_vals t) =
        g ⟨t.val, by omega⟩ := by
      intro t
      simp only [g, θ_full]
      have hlt : (⟨t.val, by omega⟩ : Fin n).val < i.val := by simp; omega
      simp only [hlt, dite_true]
    conv_lhs => rw [show ∑ t : Fin m,
        L i ⟨t.val, by omega⟩ *
          fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1 + η_vals t) =
        ∑ t : Fin m, g ⟨t.val, by omega⟩
      from Finset.sum_congr rfl (fun t _ => hsummand_eq t)]
    exact sum_fin_eq_sum_filter_lt (by omega) g

/-- The computed solution `fl_forwardSub` satisfies the per-row specification. -/
lemma fl_forwardSub_satisfies_spec (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hn : gammaValid fp n) :
    ForwardSubRowSpec fp n L b (fl_forwardSub fp n L b) := by
  intro i
  exact fl_forwardSub_row_spec fp n L b hL hn i

-- ============================================================
-- §8.1  Per-row tight backward error
-- ============================================================

set_option maxHeartbeats 800000

/-- **Per-row tight backward error** (Higham §8.1, Theorem 8.5 analog for forward sub).

    For row i of forward substitution, the computed solution satisfies
      b_i = ∑_{j ≤ i} L_ij * (1 + φ_j) * x̂_j
    where each |φ_j| ≤ γ(n).

    Unlike `ForwardSubRowSpec` (which perturbs b via Θ and ρ), this form
    leaves b_i unperturbed by tracking individual (1+δ) factors through
    the fold and dividing through by their accumulated product. -/
private lemma forwardSub_row_tight (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (φ : Fin n → ℝ),
      (∀ j, j.val ≤ i.val → |φ j| ≤ gamma fp n) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
              (fun j => L i j * (1 + φ j) * fl_forwardSub fp n L b j) := by
  set m := i.val with hm_def
  have hi : i.val < n := i.isLt
  -- Validity facts
  have hu : fp.u < 1 := by
    have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    unfold gammaValid at h1; simp at h1; linarith [fp.u_nonneg]
  have hm1_eq : m + 1 ≤ n := by omega
  have hm1_valid : gammaValid fp (m + 1) := gammaValid_mono fp hm1_eq hn
  -- Step 1: fl_forwardSub_at_row
  have hat := fl_forwardSub_at_row fp n L b i
  -- Step 2: fl_sub_fold_unroll
  let a_vals : Fin m → ℝ := fun t =>
    fp.fl_mul (L i ⟨t.val, by omega⟩)
              (fl_forwardSub fp n L b ⟨t.val, by omega⟩)
  obtain ⟨σ, hσ, hfold_eq⟩ := fl_sub_fold_unroll fp m a_vals (b i)
  -- Step 3: model_mul for each off-diagonal term
  have hmul : ∀ t : Fin m, ∃ ε, |ε| ≤ fp.u ∧
      a_vals t = L i ⟨t.val, by omega⟩ *
                 fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1+ε) :=
    fun t => fp.model_mul _ _
  let ε : Fin m → ℝ := fun t => Classical.choose (hmul t)
  have hε_bd : ∀ t, |ε t| ≤ fp.u := fun t => (Classical.choose_spec (hmul t)).1
  have hε_eq : ∀ t, a_vals t =
      L i ⟨t.val, by omega⟩ *
      fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1+ε t) :=
    fun t => (Classical.choose_spec (hmul t)).2
  -- Step 4: model_div
  set fold := Fin.foldl m (fun acc t => fp.fl_sub acc (a_vals t)) (b i)
  obtain ⟨δd, hδd, hfl_div⟩ := fp.model_div fold (L i i) (hL i)
  have hx_eq : fl_forwardSub fp n L b i = (fold / L i i) * (1 + δd) := by
    rw [hat]; exact hfl_div
  have hLx : L i i * fl_forwardSub fp n L b i = fold * (1 + δd) := by
    rw [hx_eq]; field_simp [hL i]
  -- Step 5: Product definitions and positivity
  set P := ∏ k : Fin m, (1 + σ k)
  have hP_pos : (0:ℝ) < P := prod_pos_of_u_bound fp m σ hσ hu
  have hd_pos : (0:ℝ) < 1 + δd := by linarith [neg_abs_le δd, hδd]
  set Q := P * (1 + δd)
  have hQ_pos : (0:ℝ) < Q := mul_pos hP_pos hd_pos
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
  have hP_ne : P ≠ 0 := ne_of_gt hP_pos
  -- Step 6: Key algebraic identity: b_i * Q = L_ii*x̂_i + Σ a_t * TP(t) * (1+δd)
  have hkey : b i * Q = L i i * fl_forwardSub fp n L b i +
      ∑ t : Fin m, a_vals t *
        (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) := by
    rw [hLx, ← Finset.sum_mul, ← add_mul, hfold_eq, sub_add_cancel, mul_assoc]
  -- Step 7: Diagonal — inv_prod_error_bound gives 1/Q = 1+β
  let ρ : Fin (m + 1) → ℝ := Fin.snoc σ δd
  have hρ_bd : ∀ k, |ρ k| ≤ fp.u := by
    intro k
    rcases Fin.eq_castSucc_or_eq_last k with ⟨j, rfl⟩ | rfl
    · simp only [ρ, Fin.snoc_castSucc]; exact hσ j
    · simp only [ρ, Fin.snoc_last]; exact hδd
  have hQ_prod : Q = ∏ k : Fin (m + 1), (1 + ρ k) := by
    rw [Fin.prod_univ_castSucc]
    show P * (1 + δd) = (∏ k : Fin m, (1 + ρ k.castSucc)) * (1 + ρ (Fin.last m))
    congr 1
    · apply Finset.prod_congr rfl; intro k _
      simp only [ρ, Fin.snoc_castSucc]
    · simp only [ρ, Fin.snoc_last]
  obtain ⟨β, hβ, hβ_eq⟩ := inv_prod_error_bound fp (m + 1) ρ hρ_bd hu hm1_valid
  have hβQ : (1 + β) * Q = 1 := by
    rw [hQ_prod, ← hβ_eq, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one; intro k _
    have hk_pos : (0:ℝ) < 1 + ρ k := by linarith [neg_abs_le (ρ k), hρ_bd k]
    field_simp [hk_pos.ne']
  -- Step 8: Off-diagonal — for each t, bound (1+ε_t) * TP(t) / P
  have hP_split : ∀ t : Fin m,
      P = (∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1) *
          (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) := by
    intro t; show (∏ k : Fin m, (1 + σ k)) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _
    by_cases h : k.val < t.val
    · simp [h, show ¬(t.val ≤ k.val) from by omega]
    · simp [h, show t.val ≤ k.val from by omega]
  have hHP_pos : ∀ t : Fin m,
      (0:ℝ) < ∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1 := by
    intro t
    apply Finset.prod_pos; intro k _
    by_cases h : k.val < t.val
    · simp [h]; linarith [neg_abs_le (σ k), hσ k]
    · simp [h]
  have hoff : ∀ t : Fin m,
      ∃ η : ℝ, |η| ≤ gamma fp (m + 1) ∧
        a_vals t * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) =
        L i ⟨t.val, by omega⟩ *
          fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1+η) * Q := by
    intro t
    let σ_head : Fin t.val → ℝ := fun j => σ ⟨j.val, by omega⟩
    have hσ_head : ∀ k, |σ_head k| ≤ fp.u := fun k => hσ ⟨k.val, by omega⟩
    have ht_valid : gammaValid fp t.val := gammaValid_mono fp (by omega) hn
    obtain ⟨α, hα, hα_eq⟩ := inv_prod_error_bound fp t.val σ_head hσ_head hu ht_valid
    have hHP_eq : (∏ k : Fin m, if k.val < t.val then (1+σ k) else 1) =
        ∏ j : Fin t.val, (1 + σ_head j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin m => k.val < t.val)]
      have hrest : ∏ k ∈ Finset.filter (fun k : Fin m => ¬(k.val < t.val)) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) = 1 := by
        apply Finset.prod_eq_one; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hrest, mul_one]
      have hS_eq : ∏ k ∈ Finset.filter (fun k : Fin m => k.val < t.val) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) =
        ∏ k ∈ Finset.filter (fun k : Fin m => k.val < t.val) Finset.univ,
          (1 + σ k) := by
        apply Finset.prod_congr rfl; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk; simp [hk]
      rw [hS_eq]
      symm
      apply Finset.prod_nbij (fun j => ⟨j.val, by omega⟩)
      · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · intro j₁ _ j₂ _ h; exact Fin.ext (Fin.mk.inj h)
      · intro k hk; simp at hk
        exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _; simp only [σ_head]
    have hα_cancel : (1 + α) * (∏ k : Fin m, if k.val < t.val then (1+σ k) else 1) = 1 := by
      rw [hHP_eq, ← hα_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one; intro k _
      have hk_pos : (0:ℝ) < 1 + σ_head k := by linarith [neg_abs_le (σ_head k), hσ_head k]
      field_simp [hk_pos.ne']
    have hε_γ1 : |ε t| ≤ gamma fp 1 :=
      le_trans (hε_bd t) (u_le_gamma fp one_pos (gammaValid_mono fp (by omega) hn))
    have hα_mono : |α| ≤ gamma fp t.val := hα
    obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp 1 t.val (ε t) α hε_γ1 hα_mono
      (gammaValid_mono fp (by omega) hn)
    have hη_le : |η| ≤ gamma fp (m + 1) := by
      have : 1 + t.val ≤ m + 1 := by omega
      exact le_trans hη (gamma_mono fp this hm1_valid)
    refine ⟨η, hη_le, ?_⟩
    have hTP_eq : (1 + α) * P = ∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1 := by
      calc (1 + α) * P
          = (1 + α) * ((∏ k : Fin m, if k.val < t.val then (1+σ k) else 1) *
                        (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1)) := by
              rw [hP_split t]
        _ = ((1 + α) * (∏ k : Fin m, if k.val < t.val then (1+σ k) else 1)) *
              (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) := by ring
        _ = 1 * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) := by rw [hα_cancel]
        _ = ∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1 := one_mul _
    rw [hε_eq t, ← hTP_eq, ← hη_eq]; ring
  -- Step 9: Extract all η witnesses
  let η_vals : Fin m → ℝ := fun t => Classical.choose (hoff t)
  have hη_bd : ∀ t, |η_vals t| ≤ gamma fp (m+1) := fun t =>
    (Classical.choose_spec (hoff t)).1
  have hη_eq : ∀ t,
      a_vals t * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) =
      L i ⟨t.val, by omega⟩ *
        fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1+η_vals t) * Q := fun t =>
    (Classical.choose_spec (hoff t)).2
  -- Step 10: Define φ
  let φ : Fin n → ℝ := fun j =>
    if h : j.val = i.val then β
    else if h2 : j.val < i.val then η_vals ⟨j.val, by omega⟩
    else 0
  refine ⟨φ, ?_, ?_⟩
  -- Bounds
  · intro j hij
    simp only [φ]
    by_cases heq : j.val = i.val
    · simp only [heq, dite_true]
      exact le_trans hβ (gamma_mono fp hm1_eq hn)
    · have hlt : j.val < i.val := by omega
      simp only [show ¬(j.val = i.val) from heq, dite_false,
                  show j.val < i.val from hlt, dite_true]
      have := hη_bd ⟨j.val, by omega⟩
      exact le_trans this (gamma_mono fp hm1_eq hn)
  -- Equation: b_i = Σ_{j≤i} L_ij * (1+φ_j) * x̂_j
  · have hQ_ne' : Q ≠ 0 := hQ_ne
    suffices h : b i * Q =
        Finset.sum (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
          (fun j => L i j * (1 + φ j) * fl_forwardSub fp n L b j) * Q by
      have := mul_right_cancel₀ hQ_ne' h
      linarith
    rw [hkey]
    rw [Finset.sum_mul]
    -- Split the filtered sum into j=i and j<i parts
    rw [← Finset.add_sum_erase _ _ (by simp : i ∈ Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)]
    -- The i-th term
    have hdiag : L i i * (1 + φ i) * fl_forwardSub fp n L b i * Q = L i i * fl_forwardSub fp n L b i := by
      simp only [φ, dite_true]
      have h1 : L i i * (1 + β) * fl_forwardSub fp n L b i * Q =
                L i i * fl_forwardSub fp n L b i * ((1 + β) * Q) := by ring
      rw [h1, hβQ, mul_one]
    rw [hdiag]
    congr 1
    -- Reindex erased filter → Fin m
    conv_lhs => rw [show ∑ t : Fin m,
        a_vals t * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) =
      ∑ t : Fin m, L i ⟨t.val, by omega⟩ *
        fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1+η_vals t) * Q from
      Finset.sum_congr rfl (fun t _ => hη_eq t)]
    have hbound : ∀ t : Fin m, t.val < n := fun t => by omega
    apply Finset.sum_nbij (fun (t : Fin m) => (⟨t.val, hbound t⟩ : Fin n))
    · intro t _
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by intro h; exact absurd (Fin.mk.inj h) (by omega), by omega⟩
    · intro t₁ _ t₂ _ h
      exact Fin.ext (by simp only [Fin.mk.injEq] at h; exact h)
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
                  Finset.mem_univ, true_and] at hj
      have hjlt : j.val < i.val := by
        by_cases heq : j.val = i.val
        · exfalso; exact hj.1 (Fin.ext heq)
        · omega
      exact ⟨⟨j.val, by omega⟩, Finset.mem_univ _,
             Fin.ext (by simp)⟩
    · intro t _
      show L i ⟨t.val, by omega⟩ *
          fl_forwardSub fp n L b ⟨t.val, by omega⟩ * (1+η_vals t) * Q =
        L i ⟨t.val, hbound t⟩ *
          (1 + φ ⟨t.val, hbound t⟩) *
          fl_forwardSub fp n L b ⟨t.val, hbound t⟩ * Q
      have hφ_eq : φ ⟨t.val, hbound t⟩ = η_vals t := by
        simp only [φ]
        rw [dif_neg (by omega : ¬(t.val = i.val)),
            dif_pos (by omega : t.val < i.val)]
      rw [hφ_eq]; ring

-- ============================================================
-- §8.1  Backward error (Theorem 8.5, forward sub analog)
-- ============================================================

/-- **Forward substitution backward error** (Higham §8.1, Theorem 8.5 analog).

    Let x̂ = fl_forwardSub fp n L b.  Then there exists ΔL such that:
      (1) |ΔL i j| ≤ γ(n) * |L i j|  for all i j   (componentwise bound)
      (2) ∑ j, (L i j + ΔL i j) * x̂ j = b i        (exact perturbed system)

    In other words, x̂ is the exact solution of (L + ΔL)x = b. -/
theorem forwardSub_backward_error (fp : FPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ gamma fp n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * fl_forwardSub fp n L b j = b i := by
  have h_tight : ∀ i : Fin n, ∃ (φ : Fin n → ℝ),
      (∀ j, j.val ≤ i.val → |φ j| ≤ gamma fp n) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
              (fun j => L i j * (1 + φ j) * fl_forwardSub fp n L b j) :=
    fun i => forwardSub_row_tight fp n L b hL hn i
  let φ_data : Fin n → Fin n → ℝ := fun i =>
    Classical.choose (h_tight i)
  have hφ_bound : ∀ i j, j.val ≤ i.val → |φ_data i j| ≤ gamma fp n := fun i j hij =>
    (Classical.choose_spec (h_tight i)).1 j hij
  have hφ_eq : ∀ i,
      b i = Finset.sum (Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)
              (fun j => L i j * (1 + φ_data i j) * fl_forwardSub fp n L b j) := fun i =>
    (Classical.choose_spec (h_tight i)).2
  let ΔL : Fin n → Fin n → ℝ := fun i j =>
    if j.val ≤ i.val then L i j * φ_data i j else 0
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    show |ΔL i j| ≤ gamma fp n * |L i j|
    simp only [ΔL]
    by_cases hij : j.val ≤ i.val
    · simp only [hij, ite_true, abs_mul]
      rw [mul_comm (gamma fp n)]
      exact mul_le_mul_of_nonneg_left (hφ_bound i j hij) (abs_nonneg _)
    · simp only [hij, ite_false, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _)
  · intro i
    rw [hφ_eq i]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val ≤ i.val)]
    have habove_zero : Finset.sum (Finset.filter (fun j : Fin n => ¬(j.val ≤ i.val)) Finset.univ)
        (fun j => (L i j + ΔL i j) * fl_forwardSub fp n L b j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hL_zero : L i j = 0 := hLT i j hj
      have hΔL_zero : ΔL i j = 0 := by
        simp only [ΔL, show ¬(j.val ≤ i.val) by omega, ite_false]
      rw [hL_zero, hΔL_zero, add_zero, zero_mul]
    rw [habove_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show (L i j + ΔL i j) * fl_forwardSub fp n L b j =
      L i j * (1 + φ_data i j) * fl_forwardSub fp n L b j
    simp only [ΔL, show j.val ≤ i.val from hj, ite_true]
    ring

end NumStability
