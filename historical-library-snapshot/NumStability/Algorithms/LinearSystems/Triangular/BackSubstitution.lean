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
# Back substitution

Reusable back-substitution algorithm and backward-error analysis for upper
triangular systems.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §8.1  Algorithm definition (Algorithm 8.1)
-- ============================================================

/-- Auxiliary for back substitution: solve rows `k-1, k-2, …, 0` given
    that rows `k, k+1, …, n-1` are already in `x`.

    The recursion counts down from `k = n` (nothing solved) to `k = 0`
    (everything solved). -/
noncomputable def fl_backSub_steps (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0,     _,  x => x
  | k + 1, hk, x =>
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let m := n - k - 1
      let s := Fin.foldl m (fun acc (t : Fin m) =>
                  fp.fl_sub acc
                    (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
                               (x   ⟨k + 1 + t.val, by omega⟩)))
                (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      fl_backSub_steps fp n U b k (Nat.le_of_succ_le hk) x'

/-- Floating-point back substitution: solve Ux = b for upper triangular U.

    Implements Algorithm 8.1 (Higham §8.1), processing rows from n-1 down
    to 0.  For row i with m = n-1-i off-diagonal terms:
      s = b i;  for j > i: s = fl_sub(s, fl_mul(U i j, x̂ j));  x̂ i = fl_div(s, U i i) -/
noncomputable def fl_backSub (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) : Fin n → ℝ :=
  fl_backSub_steps fp n U b n (le_refl n) (fun _ => 0)

-- ============================================================
-- §8.1  Structural lemmas for fl_backSub_steps
-- ============================================================

/-- `fl_backSub_steps` preserves entries at indices ≥ k. -/
private lemma fl_backSub_steps_stable (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (j : Fin n),
      k ≤ j.val → fl_backSub_steps fp n U b k hk x j = x j := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro hk x j hkj
    unfold fl_backSub_steps
    simp only
    -- The recursive call is fl_backSub_steps ... k ... x' j where
    -- x' = Function.update x ⟨k, _⟩ (fl_div s ...)
    -- By IH, this equals x' j since k ≤ j.val (from k+1 ≤ j.val)
    have hkj' : k ≤ j.val := by omega
    rw [ih (Nat.le_of_succ_le hk) _ j hkj']
    -- Now show Function.update x ⟨k, _⟩ val j = x j since j ≠ ⟨k, _⟩
    rw [Function.update_of_ne]
    intro heq
    have : j.val = k := congr_arg Fin.val heq
    omega

/-- At row k, `fl_backSub_steps` sets x[k] = fl_div(s, U_kk) where s is the
    inner fold using the final values at indices > k. -/
private lemma fl_backSub_steps_at_row (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (k : ℕ) (hk : k + 1 ≤ n) (x : Fin n → ℝ) :
    let ik : Fin n := ⟨k, hk⟩
    let m := n - k - 1
    let x_final := fl_backSub_steps fp n U b (k + 1) hk x
    x_final ik = fp.fl_div
      (Fin.foldl m (fun acc (t : Fin m) =>
        fp.fl_sub acc
          (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
                     (x_final ⟨k + 1 + t.val, by omega⟩)))
        (b ik))
      (U ik ik) := by
  -- Unfold one step of fl_backSub_steps
  simp only [fl_backSub_steps]
  -- After unfolding: x_final = fl_backSub_steps k _ x'
  -- where x' = Function.update x ⟨k,_⟩ (fl_div s_old (U kk))
  -- and s_old uses x (not x_final) at indices > k.
  -- By fl_backSub_steps_stable, fl_backSub_steps k _ x' ⟨k,_⟩ = x' ⟨k,_⟩
  -- = Function.update x ⟨k,_⟩ (fl_div s_old (U kk)) ⟨k,_⟩ = fl_div s_old (U kk)
  rw [fl_backSub_steps_stable fp n U b k (Nat.le_of_succ_le hk) _ ⟨k, hk⟩ (le_refl k)]
  rw [Function.update_self]
  -- Now show: the fold with x equals the fold with x_final at indices > k.
  -- Both folds use the same function at each step because
  -- x_final j = x j for j > k (by stable + update_of_ne).
  congr 1
  congr 1
  funext acc t
  congr 1; congr 1
  -- Show: x ⟨k+1+t.val, _⟩ = x_final ⟨k+1+t.val, _⟩
  symm
  have ht_lt : k + 1 + t.val < n := by omega
  rw [fl_backSub_steps_stable fp n U b k (Nat.le_of_succ_le hk) _
      ⟨k + 1 + t.val, ht_lt⟩ (by omega : k ≤ k + 1 + t.val)]
  rw [Function.update_of_ne]
  intro heq; have := congr_arg Fin.val heq; simp at this; omega

-- ============================================================
-- §8.1  Per-row computation specification
-- ============================================================

/-- Per-row computation specification for back substitution.

    Row `i` of back substitution computes x̂_i such that there exist
    rounding errors Θ_i, θ_ij (combined mul+sub fold) and ρ_i (from division)
    satisfying:

      U_ii * x̂_i = (b_i * (1 + Θ_i) - ∑_{j>i} U_ij * x̂_j * (1 + θ_ij)) * (1 + ρ_i)

    with |Θ_i| ≤ γ(m_i), |θ_ij| ≤ γ(m_i + 1), |ρ_i| ≤ u, where m_i = n - 1 - i
    is the number of off-diagonal terms in row i.

    The θ bound is γ(m_i + 1) = γ(n - i) rather than γ(m_i) because each
    off-diagonal term accumulates one fl_mul error (bounded by u ≤ γ(1))
    composed with the subtraction fold error (bounded by γ(m_i)), yielding
    γ(m_i + 1) via gamma_mul. -/
def BackSubRowSpec (fp : FPModel) (n : ℕ) (U : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (x_hat : Fin n → ℝ) : Prop :=
  ∀ (i : Fin n), ∃ (Θ : ℝ) (ρ : ℝ) (θ : Fin n → ℝ),
    |Θ| ≤ gamma fp (n - 1 - i.val) ∧
    |ρ| ≤ fp.u ∧
    (∀ j, |θ j| ≤ gamma fp (n - i.val)) ∧
    U i i * x_hat i =
      (b i * (1 + Θ) -
       Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ)
         (fun j => U i j * x_hat j * (1 + θ j))) * (1 + ρ)

/-- **Reindexing**: a sum over `Fin m` with index map `k+1+t` equals the sum over
    the filtered finset `{j : Fin n | k < j}`.  This connects the fold-based
    algorithm (which uses `Fin m` with `m = n-k-1`) to the specification
    (which uses `Finset.filter`). -/
private lemma sum_fin_eq_sum_filter {n k : ℕ} (hk : k < n) (f : Fin n → ℝ) :
    (∑ t : Fin (n - k - 1), f ⟨k + 1 + t.val, by omega⟩) =
    Finset.sum (Finset.filter (fun j : Fin n => k < j.val) Finset.univ) f := by
  -- The forward map is injective
  have hinj : ∀ a : Fin (n - k - 1), a ∈ Finset.univ →
      ∀ b : Fin (n - k - 1), b ∈ Finset.univ →
      (⟨k + 1 + a.val, by omega⟩ : Fin n) = ⟨k + 1 + b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; omega)
  -- The image of the forward map equals the filtered finset
  have himg : Finset.image (fun (t : Fin (n - k - 1)) => (⟨k + 1 + t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => k < j.val) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; simp; omega
    · intro hj
      exact ⟨⟨j.val - (k + 1), by omega⟩, Fin.ext (by simp; omega)⟩
  rw [← himg, Finset.sum_image hinj]

/-- `fl_backSub_steps` decomposes: applying p steps from x can be split as
    q steps from some intermediate state x'. -/
private lemma fl_backSub_steps_decompose (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (p q : ℕ) (hp : p ≤ n) (hq : q ≤ p) (x : Fin n → ℝ) :
    ∃ x', fl_backSub_steps fp n U b p hp x =
          fl_backSub_steps fp n U b q (le_trans hq hp) x' := by
  induction p generalizing x with
  | zero =>
    have : q = 0 := by omega
    subst this; exact ⟨x, rfl⟩
  | succ p ih =>
    rcases Nat.eq_or_lt_of_le hq with rfl | hlt
    · exact ⟨x, rfl⟩
    · simp only [fl_backSub_steps]
      exact ih (Nat.le_of_succ_le hp) (by omega : q ≤ p) _

/-- For each row i, `fl_backSub i` equals `fl_div(fold, U_ii)` where the fold
    uses `fl_backSub` values at indices > i. -/
private lemma fl_backSub_at_row (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    fl_backSub fp n U b i = fp.fl_div
      (Fin.foldl (n - i.val - 1) (fun acc (t : Fin (n - i.val - 1)) =>
        fp.fl_sub acc
          (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                     (fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩)))
        (b i))
      (U i i) := by
  have hi : i.val + 1 ≤ n := by omega
  obtain ⟨x_mid, hdecomp⟩ :=
    fl_backSub_steps_decompose fp n U b n (i.val + 1) (le_refl n) hi (fun _ => 0)
  -- Pointwise: fl_backSub j = fl_backSub_steps (i.val+1) _ x_mid j
  have h_pw : ∀ j : Fin n, fl_backSub fp n U b j =
      fl_backSub_steps fp n U b (i.val + 1) hi x_mid j :=
    fun j => congr_fun hdecomp j
  -- fl_backSub_steps_at_row gives the fold-div equation at row i
  have hat := fl_backSub_steps_at_row fp n U b i.val hi x_mid
  -- hat's let bindings: ik = ⟨i.val, hi⟩, m = n - i.val - 1,
  --   x_final = fl_backSub_steps ... (i.val+1) hi x_mid
  -- hat: x_final ik = fl_div (fold using x_final) (U ik ik)
  -- Step 1: LHS = fl_backSub i = x_final i (by h_pw)
  rw [h_pw i]
  -- Lift pointwise equality to function equality
  have h_fn : fl_backSub fp n U b = fl_backSub_steps fp n U b (i.val + 1) hi x_mid :=
    funext h_pw
  -- Rewrite ALL occurrences of fl_backSub (LHS + inside fold on RHS)
  rw [h_fn]
  -- Now goal exactly matches hat (i vs ⟨i.val, hi⟩ is def-eq by proof irrel)
  exact hat

/-- **Per-row backward error**: for row `i`, the algorithm produces an equation
    matching BackSubRowSpec using the final solution vector.

    Proof: use `fl_backSub_at_row` to get x̂_i = fl_div(s, U_ii),
    apply `model_div` and `fl_sub_sum_error_init` to expand s, then
    `model_mul` and `gamma_mul` for each off-diagonal term. -/
private lemma fl_backSub_row_spec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (Θ : ℝ) (ρ : ℝ) (θ : Fin n → ℝ),
      |Θ| ≤ gamma fp (n - 1 - i.val) ∧
      |ρ| ≤ fp.u ∧
      (∀ j, |θ j| ≤ gamma fp (n - i.val)) ∧
      U i i * fl_backSub fp n U b i =
        (b i * (1 + Θ) -
         Finset.sum (Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ)
           (fun j => U i j * fl_backSub fp n U b j * (1 + θ j))) * (1 + ρ) := by
  -- m = number of off-diagonal terms in row i
  set m := n - i.val - 1 with hm_def
  -- Step 1: x̂_i = fl_div(s, U_ii) where s is the subtraction fold
  have hat := fl_backSub_at_row fp n U b i
  set s := Fin.foldl m (fun acc (t : Fin m) =>
    fp.fl_sub acc
      (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                 (fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩)))
    (b i)
  -- Step 2: Extract division error ρ
  obtain ⟨ρ, hρ, hfl_div⟩ := fp.model_div s (U i i) (hU i)
  have hUx : U i i * fl_backSub fp n U b i = s * (1 + ρ) := by
    rw [hat, hfl_div]
    have h := hU i; field_simp
  -- Step 3: Apply fl_sub_sum_error_init to expand s
  let t_vals : Fin m → ℝ := fun t =>
    fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
              (fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩)
  have hs_fold : s = Fin.foldl m (fun acc j => fp.fl_sub acc (t_vals j)) (b i) := rfl
  have hm_le : m ≤ n := by omega
  have hm_valid : gammaValid fp m := gammaValid_mono fp hm_le hn
  obtain ⟨Θ_sub, θ_sub, hΘ_sub, hθ_sub, hfold_eq⟩ :=
    fl_sub_sum_error_init fp m t_vals (b i) hm_valid
  rw [← hs_fold] at hfold_eq
  -- Step 4: Expand each fl_mul via model_mul
  have hmul_expand : ∀ t : Fin m,
      ∃ δ : ℝ, |δ| ≤ fp.u ∧
        t_vals t = U i ⟨i.val + 1 + t.val, by omega⟩ *
                   fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ * (1 + δ) := by
    intro t
    obtain ⟨δ, hδ, hfl_mul⟩ := fp.model_mul
      (U i ⟨i.val + 1 + t.val, by omega⟩) (fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩)
    exact ⟨δ, hδ, hfl_mul⟩
  let δ_vals : Fin m → ℝ := fun t => Classical.choose (hmul_expand t)
  have hδ_bound : ∀ t, |δ_vals t| ≤ fp.u := fun t =>
    (Classical.choose_spec (hmul_expand t)).1
  have hδ_eq : ∀ t, t_vals t =
      U i ⟨i.val + 1 + t.val, by omega⟩ * fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ *
      (1 + δ_vals t) := fun t =>
    (Classical.choose_spec (hmul_expand t)).2
  -- Step 5: Combine (1 + δ_t) * (1 + θ_sub t) via gamma_mul
  have h1valid : gammaValid fp 1 := gammaValid_mono fp (by have := i.isLt; omega) hn
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
      ∑ t : Fin m, U i ⟨i.val + 1 + t.val, by omega⟩ *
        fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ * (1 + η_vals t) := by
    apply Finset.sum_congr rfl; intro t _
    rw [hδ_eq t]
    -- a*b*(1+δ)*(1+θ) = a*b*((1+δ)*(1+θ)) = a*b*(1+η)
    have hassoc : U i ⟨i.val + 1 + t.val, by omega⟩ *
        fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ *
        (1 + δ_vals t) * (1 + θ_sub t) =
      U i ⟨i.val + 1 + t.val, by omega⟩ *
        fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ *
        ((1 + δ_vals t) * (1 + θ_sub t)) := by ring
    rw [hassoc, hη_eq t]
  -- Step 7: Build witnesses
  have hm_eq : m = n - 1 - i.val := by omega
  have h1m_eq : 1 + m = n - i.val := by omega
  let θ_full : Fin n → ℝ := fun j =>
    if h : i.val < j.val then η_vals ⟨j.val - (i.val + 1), by omega⟩
    else 0
  refine ⟨Θ_sub, ρ, θ_full, ?_, ?_, ?_, ?_⟩
  · rw [← hm_eq]; exact hΘ_sub
  · exact hρ
  · intro j; simp only [θ_full]
    by_cases hij : i.val < j.val
    · simp only [hij, dite_true]
      have := hη_bound ⟨j.val - (i.val + 1), by omega⟩
      rwa [h1m_eq] at this
    · simp only [hij, dite_false, abs_zero]
      exact gamma_nonneg fp (gammaValid_mono fp (by omega) hn)
  · -- The equation
    rw [hUx, hfold_eq, hsum_rw]
    congr 1; congr 1
    -- Reindex: ∑ over Fin m → ∑ over {j | i.val < j}
    -- First show each summand equals g ⟨i.val+1+t, _⟩ where g j = U i j * x̂ j * (1+θ_full j)
    let g : Fin n → ℝ := fun j => U i j * fl_backSub fp n U b j * (1 + θ_full j)
    have hsummand_eq : ∀ t : Fin m,
        U i ⟨i.val + 1 + t.val, by omega⟩ *
          fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ * (1 + η_vals t) =
        g ⟨i.val + 1 + t.val, by omega⟩ := by
      intro t
      simp only [g, θ_full]
      have hlt : i.val < i.val + 1 + t.val := by omega
      simp only [show i.val < (⟨i.val + 1 + t.val, by omega⟩ : Fin n).val from hlt, dite_true]
      congr 1; congr 1; congr 1; exact Fin.ext (by simp)
    conv_lhs => rw [show ∑ t : Fin m,
        U i ⟨i.val + 1 + t.val, by omega⟩ *
          fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩ * (1 + η_vals t) =
        ∑ t : Fin m, g ⟨i.val + 1 + t.val, by omega⟩
      from Finset.sum_congr rfl (fun t _ => hsummand_eq t)]
    exact sum_fin_eq_sum_filter (by omega) g

/-- The computed solution `fl_backSub` satisfies the per-row specification. -/
lemma fl_backSub_satisfies_spec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n) :
    BackSubRowSpec fp n U b (fl_backSub fp n U b) := by
  intro i
  exact fl_backSub_row_spec fp n U b hU hn i

-- ============================================================
-- §8.1  Perturbed system backward error (proved from spec)
-- ============================================================

set_option maxHeartbeats 800000

/-- **Back substitution perturbed system** (Higham §8.1, Lemma 8.4 intermediate form).

    Given that x̂ satisfies the per-row computation specification, there exist
    perturbations ΔU and Δb with componentwise bounds such that
    (U + ΔU)x̂ = b + Δb.

    This is the "perturbed system" form of backward error, where both U and b
    may be perturbed.  The bound γ(n) is uniform over all rows.

    Proof: For each row i with m_i = n-1-i off-diagonal terms:
    - The subtraction fold gives errors Θ_i (for b_i) and θ_j (for each U_ij*x̂_j),
      all bounded by γ(m_i).
    - Each fl_mul gives δ_j bounded by u ≤ γ(1).
    - The division gives ρ_i bounded by u ≤ γ(1).
    - Combining: each U_ij factor gets (1+θ_j)(1+ρ) = 1+η_j with |η_j| ≤ γ(m_i+1) ≤ γ(n).
    - The b_i factor gets (1+Θ)(1+ρ) = 1+ψ with |ψ| ≤ γ(m_i+1) ≤ γ(n).
    - For j < i (U upper triangular): ΔU_ij = 0.
    - For j = i (diagonal): ΔU_ii = 0 (the diagonal is unperturbed).
    - For j > i: ΔU_ij = U_ij * ((1+θ_j)*(1+ρ)-1).
    - Δb_i = b_i * ((1+Θ)*(1+ρ) - 1). -/
theorem backSub_backward_error_perturbed (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (x_hat : Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp (n + 1))
    (hspec : BackSubRowSpec fp n U b x_hat) :
    ∃ (ΔU : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔU i j| ≤ gamma fp (n + 1) * |U i j|) ∧
      (∀ i, |Δb i| ≤ gamma fp n * |b i|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = b i + Δb i := by
  -- For each row i, extract witnesses from the spec
  unfold BackSubRowSpec at hspec

  -- Abbreviation for the filtered finset {j | i < j}
  let above (i : Fin n) := Finset.filter (fun j : Fin n => i.val < j.val) Finset.univ

  -- Extract per-row data using Classical.choose
  let Θ_data : Fin n → ℝ := fun i =>
    Classical.choose (hspec i)
  let ρ_data : Fin n → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (hspec i))
  let θ_data : Fin n → Fin n → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (Classical.choose_spec (hspec i)))
  have hΘ_bound : ∀ i, |Θ_data i| ≤ gamma fp (n - 1 - i.val) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).1
  have hρ_bound : ∀ i, |ρ_data i| ≤ fp.u := fun i =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).2.1
  have hθ_bound : ∀ i j, |θ_data i j| ≤ gamma fp (n - i.val) := fun i j =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).2.2.1 j
  have hrow_eq : ∀ i, U i i * x_hat i =
      (b i * (1 + Θ_data i) -
       Finset.sum (above i)
         (fun j => U i j * x_hat j * (1 + θ_data i j))) * (1 + ρ_data i) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hspec i)))).2.2.2

  -- Build ΔU and Δb
  let ΔU : Fin n → Fin n → ℝ := fun i j =>
    if i.val < j.val then
      U i j * ((1 + θ_data i j) * (1 + ρ_data i) - 1)
    else
      0
  let Δb : Fin n → ℝ := fun i =>
    b i * ((1 + Θ_data i) * (1 + ρ_data i) - 1)

  refine ⟨ΔU, Δb, ?_, ?_, ?_⟩

  -- ============================================================
  -- Bound 1: |ΔU i j| ≤ γ(n+1) * |U i j|
  -- ============================================================
  · intro i j
    show |ΔU i j| ≤ gamma fp (n + 1) * |U i j|
    simp only [ΔU]
    have hn' : gammaValid fp n := gammaValid_mono fp (by omega) hn
    by_cases hij : i.val < j.val
    · -- j > i: ΔU_ij = U_ij * ((1+θ_j)*(1+ρ)-1)
      simp only [hij, ite_true]
      -- Combine (1+θ)(1+ρ) via gamma_mul: θ ≤ γ(n-i), ρ ≤ γ(1) → η ≤ γ(n-i+1)
      have hmi : n - i.val + 1 ≤ n + 1 := by omega
      have hmi_valid : gammaValid fp (n - i.val + 1) :=
        gammaValid_mono fp hmi hn
      have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
      have hρ_1 : |ρ_data i| ≤ gamma fp 1 :=
        le_trans (hρ_bound i) (u_le_gamma fp one_pos h1valid)
      obtain ⟨η, hη, heq_η⟩ := gamma_mul fp (n - i.val) 1 (θ_data i j)
        (ρ_data i) (hθ_bound i j) hρ_1 hmi_valid
      have hη_eq : η = (1 + θ_data i j) * (1 + ρ_data i) - 1 := by linarith
      rw [← hη_eq]
      have hη_n : |η| ≤ gamma fp (n + 1) :=
        le_trans hη (gamma_mono fp hmi hn)
      rw [abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hη_n (abs_nonneg _)
    · -- j ≤ i: ΔU_ij = 0
      simp only [hij, ite_false, abs_zero]
      exact mul_nonneg (gamma_nonneg fp (gammaValid_mono fp (by omega) hn)) (abs_nonneg _)

  -- ============================================================
  -- Bound 2: |Δb i| ≤ γ(n) * |b i|
  -- ============================================================
  · intro i
    show |Δb i| ≤ gamma fp n * |b i|
    simp only [Δb]
    have hn' : gammaValid fp n := gammaValid_mono fp (by omega) hn
    have hmi : n - 1 - i.val + 1 ≤ n := by omega
    have hmi_valid : gammaValid fp (n - 1 - i.val + 1) :=
      gammaValid_mono fp hmi hn'
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    have hρ_1 : |ρ_data i| ≤ gamma fp 1 :=
      le_trans (hρ_bound i) (u_le_gamma fp one_pos h1valid)
    obtain ⟨ψ, hψ, heq_ψ⟩ := gamma_mul fp (n - 1 - i.val) 1 (Θ_data i)
      (ρ_data i) (hΘ_bound i) hρ_1 hmi_valid
    have hψ_eq : ψ = (1 + Θ_data i) * (1 + ρ_data i) - 1 := by linarith
    rw [← hψ_eq]
    have hψ_n : |ψ| ≤ gamma fp n :=
      le_trans hψ (gamma_mono fp hmi hn')
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hψ_n (abs_nonneg _)

  -- ============================================================
  -- Equality: ∑ j, (U i j + ΔU i j) * x̂ j = b i + Δb i
  -- ============================================================
  · intro i
    show ∑ j : Fin n, (U i j + ΔU i j) * x_hat j = b i + Δb i

    -- Abbreviations for filtered finsets
    let below := Finset.filter (fun j : Fin n => j.val < i.val) Finset.univ
    let diag  := Finset.filter (fun j : Fin n => j.val = i.val) Finset.univ

    -- Simplify ΔU terms by case
    have hΔU_below : ∀ j : Fin n, j.val < i.val → ΔU i j = 0 := by
      intro j hj; simp only [ΔU, show ¬(i.val < j.val) by omega, ite_false]
    have hΔU_diag : ΔU i i = 0 := by
      simp only [ΔU, show ¬(i.val < i.val) by omega, ite_false]
    have hΔU_above : ∀ j : Fin n, i.val < j.val →
        ΔU i j = U i j * ((1 + θ_data i j) * (1 + ρ_data i) - 1) := by
      intro j hj; simp only [ΔU, show i.val < j.val from hj, ite_true]

    -- For j < i: the full term vanishes (upper triangularity)
    have hterm_below : ∀ j : Fin n, j.val < i.val →
        (U i j + ΔU i j) * x_hat j = 0 := by
      intro j hj
      rw [hUT i j hj, hΔU_below j hj, add_zero, zero_mul]

    -- For j = i: the diagonal term
    have hterm_diag : (U i i + ΔU i i) * x_hat i = U i i * x_hat i := by
      rw [hΔU_diag, add_zero]

    -- For j > i: the off-diagonal term
    have hterm_above : ∀ j : Fin n, i.val < j.val →
        (U i j + ΔU i j) * x_hat j =
          U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i)) := by
      intro j hj
      rw [hΔU_above j hj]; ring

    -- Expand Δb
    have hΔb_expand : b i + Δb i = b i * ((1 + Θ_data i) * (1 + ρ_data i)) := by
      simp only [Δb]; ring

    -- From hrow_eq, derive the key identity:
    -- U_ii*x̂_i + Σ_{j>i} U_ij*x̂_j*(1+θ_j)*(1+ρ) = b_i*(1+Θ)*(1+ρ)
    have hexpand : U i i * x_hat i +
        Finset.sum (above i)
          (fun j => U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i))) =
        b i * ((1 + Θ_data i) * (1 + ρ_data i)) := by
      have heq := hrow_eq i
      have hrhs : (b i * (1 + Θ_data i) -
         Finset.sum (above i)
           (fun j => U i j * x_hat j * (1 + θ_data i j))) * (1 + ρ_data i) =
         b i * (1 + Θ_data i) * (1 + ρ_data i) -
         Finset.sum (above i)
           (fun j => U i j * x_hat j * (1 + θ_data i j) * (1 + ρ_data i)) := by
        rw [sub_mul]; congr 1; rw [Finset.sum_mul]
      rw [heq, hrhs]
      have hmul_assoc :
          Finset.sum (above i)
            (fun j => U i j * x_hat j * (1 + θ_data i j) * (1 + ρ_data i)) =
          Finset.sum (above i)
            (fun j => U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i))) := by
        apply Finset.sum_congr rfl; intro j _; ring
      rw [hmul_assoc]
      have := mul_comm (b i * (1 + Θ_data i)) (1 + ρ_data i)
      linarith

    -- Each term of the full sum equals the corresponding term in the rearranged form
    -- For j < i: term = 0 (upper triangularity + ΔU = 0)
    -- For j = i: term = U_ii * x̂_i (ΔU_ii = 0)
    -- For j > i: term = U_ij * x̂_j * (1+θ)(1+ρ)
    -- Total = U_ii*x̂_i + Σ_{j>i} U_ij*x̂_j*(1+θ)(1+ρ) = b_i*(1+Θ)*(1+ρ)

    -- Step 1: Peel off the i-th term from the full sum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    rw [hterm_diag]
    -- Goal: U_ii*x̂_i + ∑_{j ∈ univ\{i}} (U_ij+ΔU_ij)*x̂_j = b_i + Δb_i

    -- Step 2: Show the sum over univ\{i} equals the sum over above i
    -- Terms with j < i vanish; terms with j > i give the target
    have herase_eq : Finset.sum (Finset.univ.erase i)
        (fun j => (U i j + ΔU i j) * x_hat j) =
      Finset.sum (above i)
        (fun j => U i j * x_hat j * ((1 + θ_data i j) * (1 + ρ_data i))) := by
      -- Show: every term in erase that is NOT in above i is zero
      -- and every term that IS in above i matches
      have h_above_sub : above i ⊆ Finset.univ.erase i := by
        intro j hj
        simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
        intro heq; subst heq; exact absurd hj (lt_irrefl _)
      rw [← Finset.sum_sdiff h_above_sub]
      -- The sdiff part is zero: these are j ≠ i with j ≤ i, i.e. j < i
      have hsdiff_zero : Finset.sum (Finset.univ.erase i \ above i)
          (fun j => (U i j + ΔU i j) * x_hat j) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        simp only [above, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true,
          ne_eq, Finset.mem_filter, true_and, not_lt] at hj
        have : j.val < i.val := by
          rcases Nat.lt_or_ge j.val i.val with h | h
          · exact h
          · exfalso; apply hj.1; exact Fin.ext (Nat.le_antisymm hj.2 h)
        exact hterm_below j this
      rw [hsdiff_zero, zero_add]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [above, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hterm_above j hj

    rw [herase_eq, hΔb_expand]
    exact hexpand

-- ============================================================
-- §8.1  Full perturbed system theorem (from fl_backSub)
-- ============================================================

/-- **Back substitution perturbed backward error** (Higham §8.1).

    The computed solution x̂ = fl_backSub fp n U b satisfies
    (U + ΔU)x̂ = b + Δb with componentwise bounds:
      |ΔU i j| ≤ γ(n+1) * |U i j|
      |Δb i|   ≤ γ(n) * |b i|

    This combines `fl_backSub_satisfies_spec` with the fully proved
    `backSub_backward_error_perturbed` theorem.

    The γ(n+1) bound on ΔU arises because each off-diagonal term
    accumulates one fl_mul error (γ(1)) composed with the subtraction
    fold error (γ(n-1-i)) and the division error (γ(1)), totalling
    γ(n-i+1) ≤ γ(n+1) via gamma_mul.  The Δb bound is tighter (γ(n))
    because b has no multiplication error. -/
theorem backSub_backward_error_dual (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp (n + 1)) :
    ∃ (ΔU : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔU i j| ≤ gamma fp (n + 1) * |U i j|) ∧
      (∀ i, |Δb i| ≤ gamma fp n * |b i|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i + Δb i :=
  backSub_backward_error_perturbed fp n U b (fl_backSub fp n U b) hUT hn
    (fl_backSub_satisfies_spec fp n U b hU (gammaValid_mono fp (by omega) hn))

-- ============================================================
-- §8.1  Per-row tight backward error (Lemma 8.2/8.4)
-- ============================================================

/-- **Per-row tight backward error** (Higham §8.1, Lemma 8.2).

    For row i of back substitution, the computed solution satisfies
      b_i = ∑_{j ≥ i} U_ij * (1 + φ_j) * x̂_j
    with the source-sharp constants: the diagonal factor is bounded by
    `γ(n-i)` in zero-based indexing, and the off-diagonal factor in column
    `j > i` is bounded by `γ(j-i)`.

    Unlike `BackSubRowSpec` (which perturbs b via Θ and ρ), this form
    leaves b_i unperturbed by tracking individual (1+δ) factors through
    the fold and dividing through by their accumulated product.

    Proof sketch:
    1. From `fl_backSub_at_row`: x̂_i = fl_div(fold, U_ii)
    2. Extract div error δ^d, mul errors δ^m_t, sub errors δ^s_t (each ≤ u)
    3. Unroll fold: fold = b_i * ∏(1+δ^s_k) - ∑_t q_t * tailProd(δ^s, t)
       where q_t = U_ij_t * x̂_j_t * (1+δ^m_t)
    4. Multiply by (1+δ^d) and divide through by (1+δ^d)*∏(1+δ^s_k)
    5. Diagonal: 1/((1+δ^d)*∏(1+δ^s_k)) = 1+θ_ii, |θ_ii| ≤ γ(m+1) by `inv_prod_error_bound`
    6. Off-diag t: (1+δ^m_t)/∏_{k<t}(1+δ^s_k) = (1+δ^m_t)*(1+α_t)
       where |α_t| ≤ γ(t) by `inv_prod_error_bound` and then = 1+η_t
       with |η_t| ≤ γ(t+1) by `gamma_mul`
    7. All bounds ≤ γ(n-i) ≤ γ(n) -/
lemma backSub_row_tight (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hn : gammaValid fp n)
    (i : Fin n) :
    ∃ (φ : Fin n → ℝ),
      |φ i| ≤ gamma fp (n - i.val) ∧
      (∀ j, i.val < j.val → |φ j| ≤ gamma fp (j.val - i.val)) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) := by
  set m := n - i.val - 1 with hm_def
  have hi : i.val < n := i.isLt
  -- Validity facts
  have hu : fp.u < 1 := by
    have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hn
    unfold gammaValid at h1; simp at h1; linarith [fp.u_nonneg]
  have hm1_eq : m + 1 = n - i.val := by omega
  have hm1_le : m + 1 ≤ n := by omega
  have hm1_valid : gammaValid fp (m + 1) := gammaValid_mono fp hm1_le hn
  -- Step 1: fl_backSub_at_row
  have hat := fl_backSub_at_row fp n U b i
  -- Step 2: fl_sub_fold_unroll
  let a_vals : Fin m → ℝ := fun t =>
    fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
              (fl_backSub fp n U b ⟨i.val + 1 + t.val, by omega⟩)
  obtain ⟨σ, hσ, hfold_eq⟩ := fl_sub_fold_unroll fp m a_vals (b i)
  -- Step 3: model_mul for each off-diagonal term
  have hmul : ∀ t : Fin m, ∃ ε, |ε| ≤ fp.u ∧
      a_vals t = U i ⟨i.val+1+t.val, by omega⟩ *
                 fl_backSub fp n U b ⟨i.val+1+t.val, by omega⟩ * (1+ε) :=
    fun t => fp.model_mul _ _
  let ε : Fin m → ℝ := fun t => Classical.choose (hmul t)
  have hε_bd : ∀ t, |ε t| ≤ fp.u := fun t => (Classical.choose_spec (hmul t)).1
  have hε_eq : ∀ t, a_vals t =
      U i ⟨i.val+1+t.val, by omega⟩ *
      fl_backSub fp n U b ⟨i.val+1+t.val, by omega⟩ * (1+ε t) :=
    fun t => (Classical.choose_spec (hmul t)).2
  -- Step 4: model_div
  set fold := Fin.foldl m (fun acc t => fp.fl_sub acc (a_vals t)) (b i)
  obtain ⟨δd, hδd, hfl_div⟩ := fp.model_div fold (U i i) (hU i)
  have hx_eq : fl_backSub fp n U b i = (fold / U i i) * (1 + δd) := by
    rw [hat]; exact hfl_div
  have hUx : U i i * fl_backSub fp n U b i = fold * (1 + δd) := by
    rw [hx_eq]; field_simp [hU i]
  -- Step 5: Product definitions and positivity
  set P := ∏ k : Fin m, (1 + σ k)
  have hP_pos : (0:ℝ) < P := prod_pos_of_u_bound fp m σ hσ hu
  have hd_pos : (0:ℝ) < 1 + δd := by linarith [neg_abs_le δd, hδd]
  set Q := P * (1 + δd)
  have hQ_pos : (0:ℝ) < Q := mul_pos hP_pos hd_pos
  have hQ_ne : Q ≠ 0 := ne_of_gt hQ_pos
  have hP_ne : P ≠ 0 := ne_of_gt hP_pos
  -- Step 6: Key algebraic identity: b_i * Q = U_ii*x̂_i + Σ a_t * TP(t) * (1+δd)
  have hkey : b i * Q = U i i * fl_backSub fp n U b i +
      ∑ t : Fin m, a_vals t *
        (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) := by
    rw [hUx, ← Finset.sum_mul, ← add_mul, hfold_eq, sub_add_cancel, mul_assoc]
  -- Step 7: Diagonal — inv_prod_error_bound gives 1/Q = 1+β
  -- Combine σ and δd into ρ : Fin(m+1)
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
  -- (1+β) = ∏ 1/(1+ρ_k) = 1/Q
  have hβQ : (1 + β) * Q = 1 := by
    rw [hQ_prod, ← hβ_eq, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one; intro k _
    have hk_pos : (0:ℝ) < 1 + ρ k := by linarith [neg_abs_le (ρ k), hρ_bd k]
    field_simp [hk_pos.ne']
  -- Step 8: Off-diagonal — for each t, bound (1+ε_t) * TP(t) / P
  -- Product split: P = headProd(t) * TP(t)
  have hP_split : ∀ t : Fin m,
      P = (∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1) *
          (∏ k : Fin m, if t.val ≤ k.val then (1 + σ k) else 1) := by
    intro t; show (∏ k : Fin m, (1 + σ k)) = _
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl; intro k _
    by_cases h : k.val < t.val
    · simp [h, show ¬(t.val ≤ k.val) from by omega]
    · simp [h, show t.val ≤ k.val from by omega]
  -- headProd positivity
  have hHP_pos : ∀ t : Fin m,
      (0:ℝ) < ∏ k : Fin m, if k.val < t.val then (1 + σ k) else 1 := by
    intro t
    apply Finset.prod_pos; intro k _
    by_cases h : k.val < t.val
    · simp [h]; linarith [neg_abs_le (σ k), hσ k]
    · simp [h]
  -- For each t < m, inv_prod_error_bound on first t factors of σ
  have hoff : ∀ t : Fin m,
      ∃ η : ℝ, |η| ≤ gamma fp (t.val + 1) ∧
        a_vals t * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) =
        U i ⟨i.val+1+t.val, by omega⟩ *
          fl_backSub fp n U b ⟨i.val+1+t.val, by omega⟩ * (1+η) * Q := by
    intro t
    -- 1/headProd(t) = 1+α_t
    -- We need inv_prod_error_bound on the first t.val factors of σ
    let σ_head : Fin t.val → ℝ := fun j => σ ⟨j.val, by omega⟩
    have hσ_head : ∀ k, |σ_head k| ≤ fp.u := fun k => hσ ⟨k.val, by omega⟩
    have ht_valid : gammaValid fp t.val := gammaValid_mono fp (by omega) hn
    obtain ⟨α, hα, hα_eq⟩ := inv_prod_error_bound fp t.val σ_head hσ_head hu ht_valid
    -- headProd(t) = ∏ j : Fin t.val, (1+σ_head j) [reindex]
    have hHP_eq : (∏ k : Fin m, if k.val < t.val then (1+σ k) else 1) =
        ∏ j : Fin t.val, (1 + σ_head j) := by
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k : Fin m => k.val < t.val)]
      have hrest : ∏ k ∈ Finset.filter (fun k : Fin m => ¬(k.val < t.val)) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) = 1 := by
        apply Finset.prod_eq_one; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        simp [hk]
      rw [hrest, mul_one]
      -- Reindex the filter product
      have hS_eq : ∏ k ∈ Finset.filter (fun k : Fin m => k.val < t.val) Finset.univ,
          (if k.val < t.val then (1 + σ k) else 1) =
        ∏ k ∈ Finset.filter (fun k : Fin m => k.val < t.val) Finset.univ,
          (1 + σ k) := by
        apply Finset.prod_congr rfl; intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk; simp [hk]
      rw [hS_eq]
      -- Bijection between {k : Fin m | k.val < t.val} and Fin t.val
      symm
      apply Finset.prod_nbij (fun j => ⟨j.val, by omega⟩)
      · intro j _; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
      · intro j₁ _ j₂ _ h; exact Fin.ext (Fin.mk.inj h)
      · intro k hk; simp at hk
        exact ⟨⟨k.val, hk⟩, Finset.mem_univ _, Fin.ext rfl⟩
      · intro j _; simp only [σ_head]
    -- (1+α)*headProd = 1
    have hα_cancel : (1 + α) * (∏ k : Fin m, if k.val < t.val then (1+σ k) else 1) = 1 := by
      rw [hHP_eq, ← hα_eq, ← Finset.prod_mul_distrib]
      apply Finset.prod_eq_one; intro k _
      have hk_pos : (0:ℝ) < 1 + σ_head k := by linarith [neg_abs_le (σ_head k), hσ_head k]
      field_simp [hk_pos.ne']
    -- Combine (1+ε_t)*(1+α) via gamma_mul
    have hε_γ1 : |ε t| ≤ gamma fp 1 :=
      le_trans (hε_bd t) (u_le_gamma fp one_pos (gammaValid_mono fp (by omega) hn))
    have hα_mono : |α| ≤ gamma fp t.val := hα
    obtain ⟨η, hη, hη_eq⟩ := gamma_mul fp 1 t.val (ε t) α hε_γ1 hα_mono
      (gammaValid_mono fp (by omega) hn)
    have hη_exact : |η| ≤ gamma fp (t.val + 1) := by
      simpa [Nat.add_comm] using hη
    refine ⟨η, hη_exact, ?_⟩
    -- Algebraic identity: a_t * TP(t) * (1+δd) = U*x̂*(1+η) * Q
    -- TP = (1+α)*P, (1+ε)*(1+α) = 1+η, Q = P*(1+δd)
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
  have hη_bd : ∀ t, |η_vals t| ≤ gamma fp (t.val + 1) := fun t =>
    (Classical.choose_spec (hoff t)).1
  have hη_eq : ∀ t,
      a_vals t * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) =
      U i ⟨i.val+1+t.val, by omega⟩ *
        fl_backSub fp n U b ⟨i.val+1+t.val, by omega⟩ * (1+η_vals t) * Q := fun t =>
    (Classical.choose_spec (hoff t)).2
  -- Step 10: Define φ
  let φ : Fin n → ℝ := fun j =>
    if h : j.val = i.val then β
    else if h2 : i.val < j.val then η_vals ⟨j.val - (i.val + 1), by omega⟩
    else 0
  refine ⟨φ, ?_, ?_, ?_⟩
  -- Bounds
  · simp only [φ]
    exact (by
      simp only [dite_true]
      simpa [hm1_eq] using hβ)
  · intro j hij
    simp only [φ]
    have hne : ¬ j.val = i.val := by omega
    simp only [hne, dite_false, hij, dite_true]
    have ht : j.val - (i.val + 1) + 1 = j.val - i.val := by
      omega
    simpa [ht] using hη_bd ⟨j.val - (i.val + 1), by omega⟩
  -- Equation: b_i = Σ_{j≥i} U_ij * (1+φ_j) * x̂_j
  · -- Multiply both sides by Q (nonzero), then use hkey and hη_eq
    have hQ_ne' : Q ≠ 0 := hQ_ne
    suffices h : b i * Q =
        Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
          (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) * Q by
      have := mul_right_cancel₀ hQ_ne' h
      linarith
    -- LHS = b_i * Q = U_ii*x̂_i + Σ a_t*TP(t)*(1+δd) [from hkey]
    rw [hkey]
    -- RHS: expand the sum * Q
    rw [Finset.sum_mul]
    -- Split the filtered sum into j=i and j>i parts
    rw [← Finset.add_sum_erase _ _ (by simp : i ∈ Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)]
    -- The i-th term: U_ii * (1+φ_i) * x̂_i * Q = U_ii * x̂_i [since (1+φ_i)*Q = (1+β)*Q = 1]
    have hdiag : U i i * (1 + φ i) * fl_backSub fp n U b i * Q = U i i * fl_backSub fp n U b i := by
      simp only [φ, dite_true]
      have h1 : U i i * (1 + β) * fl_backSub fp n U b i * Q =
                U i i * fl_backSub fp n U b i * ((1 + β) * Q) := by ring
      rw [h1, hβQ, mul_one]
    rw [hdiag]
    -- The remaining sum over {j ≥ i} \ {i} = {j > i}
    -- This equals Σ_t a_vals_t * TP(t) * (1+δd) via reindexing and hη_eq
    congr 1
    -- Reindex: filter erase → Fin m
    -- Show: Σ_{j ∈ filter(≤i) \ {i}} (U_ij*(1+φ_j)*x̂_j*Q) = Σ_t a_t*TP(t)*(1+δd)
    -- Each term j in the erased set has i < j, and maps to t = j.val - (i.val+1)
    conv_lhs => rw [show ∑ t : Fin m,
        a_vals t * (∏ k : Fin m, if t.val ≤ k.val then (1+σ k) else 1) * (1+δd) =
      ∑ t : Fin m, U i ⟨i.val+1+t.val, by omega⟩ *
        fl_backSub fp n U b ⟨i.val+1+t.val, by omega⟩ * (1+η_vals t) * Q from
      Finset.sum_congr rfl (fun t _ => hη_eq t)]
    -- Now both sides sum U*x̂*(1+φ_j)*Q over j > i
    -- Reindex from erased filter to Fin m
    have hbound : ∀ t : Fin m, i.val + 1 + t.val < n := fun t => by omega
    apply Finset.sum_nbij (fun (t : Fin m) => (⟨i.val + 1 + t.val, hbound t⟩ : Fin n))
    · -- Maps into the erased filter
      intro t _
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by intro h; exact absurd (Fin.mk.inj h) (by omega), by omega⟩
    · -- Injective (Set.InjOn)
      intro t₁ _ t₂ _ h
      exact Fin.ext (by simp only [Fin.mk.injEq] at h; omega)
    · -- Surjective (Set.SurjOn)
      intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
                  Finset.mem_univ, true_and] at hj
      have hij : i.val < j.val := by
        by_cases heq : j.val = i.val
        · exfalso; exact hj.1 (Fin.ext heq)
        · omega
      exact ⟨⟨j.val - (i.val + 1), by omega⟩, Finset.mem_univ _,
             Fin.ext (by simp; omega)⟩
    · -- Values match: f t = g (e t)
      intro t _
      show U i ⟨i.val+1+t.val, hbound t⟩ *
          fl_backSub fp n U b ⟨i.val+1+t.val, hbound t⟩ * (1+η_vals t) * Q =
        U i ⟨i.val+1+t.val, hbound t⟩ *
          (1 + φ ⟨i.val+1+t.val, hbound t⟩) *
          fl_backSub fp n U b ⟨i.val+1+t.val, hbound t⟩ * Q
      have hφ_eq : φ ⟨i.val+1+t.val, hbound t⟩ = η_vals t := by
        simp only [φ]
        rw [dif_neg (by omega : ¬(i.val + 1 + t.val = i.val)),
            dif_pos (by omega : i.val < i.val + 1 + t.val)]
        congr 1; ext; simp
      rw [hφ_eq]; ring

-- ============================================================
-- §8.1  Source-sharp backward error (Theorem 8.3)
-- ============================================================

/-- **Higham Theorem 8.3** (Algorithm 8.1, source-sharp constants).

    For the back-substitution algorithm applied to a nonsingular upper
    triangular system `Ux = b`, the computed solution `x̂` satisfies
    `(U + ΔU)x̂ = b`, with row-wise perturbation constants matching the
    source statement in zero-based indexing:

    * diagonal entry in row `i`: `γ(n - i)`, corresponding to
      `γ_{n-i+1}` in the book's one-based indexing;
    * off-diagonal entry `(i,j)`, `i < j`: `γ(j - i)`, corresponding to
      `γ_{|i-j|}`. -/
theorem backSub_backward_error_algorithm_8_1 (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i, |ΔU i i| ≤ gamma fp (n - i.val) * |U i i|) ∧
      (∀ i j, i.val < j.val →
        |ΔU i j| ≤ gamma fp (j.val - i.val) * |U i j|) ∧
      (∀ i j, j.val < i.val → ΔU i j = 0) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i := by
  have h_tight : ∀ i : Fin n, ∃ (φ : Fin n → ℝ),
      |φ i| ≤ gamma fp (n - i.val) ∧
      (∀ j, i.val < j.val → |φ j| ≤ gamma fp (j.val - i.val)) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) :=
    fun i => backSub_row_tight fp n U b hU hn i
  let φ_data : Fin n → Fin n → ℝ := fun i =>
    Classical.choose (h_tight i)
  have hφ_diag : ∀ i, |φ_data i i| ≤ gamma fp (n - i.val) := fun i =>
    (Classical.choose_spec (h_tight i)).1
  have hφ_off : ∀ i j, i.val < j.val →
      |φ_data i j| ≤ gamma fp (j.val - i.val) := fun i j hij =>
    (Classical.choose_spec (h_tight i)).2.1 j hij
  have hφ_eq : ∀ i,
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ_data i j) * fl_backSub fp n U b j) := fun i =>
    (Classical.choose_spec (h_tight i)).2.2
  let ΔU : Fin n → Fin n → ℝ := fun i j =>
    if i.val ≤ j.val then U i j * φ_data i j else 0
  refine ⟨ΔU, ?_, ?_, ?_, ?_⟩
  · intro i
    show |ΔU i i| ≤ gamma fp (n - i.val) * |U i i|
    simp only [ΔU, le_rfl, ite_true, abs_mul]
    rw [mul_comm (gamma fp (n - i.val))]
    exact mul_le_mul_of_nonneg_left (hφ_diag i) (abs_nonneg _)
  · intro i j hij
    show |ΔU i j| ≤ gamma fp (j.val - i.val) * |U i j|
    simp only [ΔU, le_of_lt hij, ite_true, abs_mul]
    rw [mul_comm (gamma fp (j.val - i.val))]
    exact mul_le_mul_of_nonneg_left (hφ_off i j hij) (abs_nonneg _)
  · intro i j hij
    show ΔU i j = 0
    simp only [ΔU, show ¬ i.val ≤ j.val by omega, ite_false]
  · intro i
    rw [hφ_eq i]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => i.val ≤ j.val)]
    have hbelow_zero : Finset.sum (Finset.filter (fun j : Fin n => ¬(i.val ≤ j.val)) Finset.univ)
        (fun j => (U i j + ΔU i j) * fl_backSub fp n U b j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hU_zero : U i j = 0 := hUT i j hj
      have hΔU_zero : ΔU i j = 0 := by
        simp only [ΔU, show ¬(i.val ≤ j.val) by omega, ite_false]
      rw [hU_zero, hΔU_zero, add_zero, zero_mul]
    rw [hbelow_zero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show (U i j + ΔU i j) * fl_backSub fp n U b j =
      U i j * (1 + φ_data i j) * fl_backSub fp n U b j
    simp only [ΔU, show i.val ≤ j.val from hj, ite_true]
    ring

-- ============================================================
-- §8.1  Backward error (Theorem 8.5)
-- ============================================================

/-- **Back substitution backward error** (Higham §8.1, Theorem 8.5).

    Let x̂ = fl_backSub fp n U b.  Then there exists ΔU such that:
      (1) |ΔU i j| ≤ γ(n) * |U i j|  for all i j   (componentwise bound)
      (2) ∑ j, (U i j + ΔU i j) * x̂ j = b i        (exact perturbed system)

    In other words, x̂ is the exact solution of (U + ΔU)x = b.

    Proof: For each row i, `backSub_row_tight` gives
      b_i = ∑_{j≥i} U_ij (1+φ_j) x̂_j, with the source-sharp
      row constants.  Monotonicity of `γ` gives the displayed uniform
      `γ(n)` envelope.
    Define ΔU_ij = U_ij · φ_j for j ≥ i, and ΔU_ij = 0 for j < i.
    By upper triangularity, U_ij = 0 for j < i, so the j < i terms vanish
    and the sum reduces to the tight backward error equation. -/
theorem backSub_backward_error (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : gammaValid fp n) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ gamma fp n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * fl_backSub fp n U b j = b i := by
  -- For each row, extract tight backward error witnesses
  have h_tight : ∀ i : Fin n, ∃ (φ : Fin n → ℝ),
      |φ i| ≤ gamma fp (n - i.val) ∧
      (∀ j, i.val < j.val → |φ j| ≤ gamma fp (j.val - i.val)) ∧
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ j) * fl_backSub fp n U b j) :=
    fun i => backSub_row_tight fp n U b hU hn i
  -- Extract per-row witnesses
  let φ_data : Fin n → Fin n → ℝ := fun i =>
    Classical.choose (h_tight i)
  have hφ_bound : ∀ i j, i.val ≤ j.val → |φ_data i j| ≤ gamma fp n := by
    intro i j hij
    by_cases heq : i = j
    · subst j
      exact le_trans (Classical.choose_spec (h_tight i)).1
        (gamma_mono fp (Nat.sub_le n i.val) hn)
    · have hij_lt : i.val < j.val := by
        exact Nat.lt_of_le_of_ne hij (fun h => heq (Fin.ext h))
      exact le_trans ((Classical.choose_spec (h_tight i)).2.1 j hij_lt)
        (gamma_mono fp (by omega : j.val - i.val ≤ n) hn)
  have hφ_eq : ∀ i,
      b i = Finset.sum (Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)
              (fun j => U i j * (1 + φ_data i j) * fl_backSub fp n U b j) := fun i =>
    (Classical.choose_spec (h_tight i)).2.2
  -- Define ΔU
  let ΔU : Fin n → Fin n → ℝ := fun i j =>
    if i.val ≤ j.val then U i j * φ_data i j else 0
  refine ⟨ΔU, ?_, ?_⟩
  -- Bound: |ΔU i j| ≤ γ(n) * |U i j|
  · intro i j
    show |ΔU i j| ≤ gamma fp n * |U i j|
    simp only [ΔU]
    by_cases hij : i.val ≤ j.val
    · simp only [hij, ite_true, abs_mul]
      rw [mul_comm (gamma fp n)]
      exact mul_le_mul_of_nonneg_left (hφ_bound i j hij) (abs_nonneg _)
    · simp only [hij, ite_false, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hn) (abs_nonneg _)
  -- Equation: ∑ j, (U i j + ΔU i j) * x̂ j = b i
  · intro i
    rw [hφ_eq i]
    -- Split the full sum into j < i and j ≥ i parts
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => i.val ≤ j.val)]
    -- The j < i part: (U i j + ΔU i j) * x̂ j = 0 by upper triangularity
    have hbelow_zero : Finset.sum (Finset.filter (fun j : Fin n => ¬(i.val ≤ j.val)) Finset.univ)
        (fun j => (U i j + ΔU i j) * fl_backSub fp n U b j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hU_zero : U i j = 0 := hUT i j hj
      have hΔU_zero : ΔU i j = 0 := by
        simp only [ΔU, show ¬(i.val ≤ j.val) by omega, ite_false]
      rw [hU_zero, hΔU_zero, add_zero, zero_mul]
    rw [hbelow_zero, add_zero]
    -- The j ≥ i part: (U i j + ΔU i j) * x̂ j = U i j * (1 + φ j) * x̂ j
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    show (U i j + ΔU i j) * fl_backSub fp n U b j =
      U i j * (1 + φ_data i j) * fl_backSub fp n U b j
    simp only [ΔU, show i.val ≤ j.val from hj, ite_true]
    ring

end NumStability
