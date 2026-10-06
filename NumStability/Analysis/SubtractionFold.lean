-- Analysis/SubtractionFold.lean
--
-- Subtraction fold error lemmas, mirroring Summation.lean for fl_sub.
-- Shared infrastructure for back substitution and forward substitution.

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

/-!
# Rounded subtraction folds

Reusable error lemmas for repeated rounded subtraction, shared by forward and
back substitution.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Subtraction fold error (mirrors fl_sum_error_init)
-- ============================================================

/-- **Subtraction fold error with initial accumulator** (fl_sub analog of fl_sum_error_init).

    For a sequence t : Fin m → ℝ and initial accumulator s, sequential
    fl_sub accumulation satisfies:
      foldl m (fl_sub · (t ·)) s = s * (1 + Θ) - ∑ i, t i * (1 + θ i)
    where |Θ| ≤ γ(m) and ∀ i, |θ i| ≤ γ(m).

    Proof: identical to fl_sum_error_init, substituting model_sub for model_add. -/
lemma fl_sub_sum_error_init (fp : FPModel) (m : ℕ) (t : Fin m → ℝ) (s : ℝ)
    (hm : gammaValid fp m) :
    ∃ (Θ : ℝ) (θ : Fin m → ℝ),
      |Θ| ≤ gamma fp m ∧ (∀ i, |θ i| ≤ gamma fp m) ∧
      Fin.foldl m (fun acc i => fp.fl_sub acc (t i)) s =
        s * (1 + Θ) - ∑ i : Fin m, t i * (1 + θ i) := by
  induction m with
  | zero =>
    exact ⟨0, fun i => i.elim0, by simp [gamma], fun i => i.elim0, by simp⟩
  | succ m ih =>
    have hm_pred : gammaValid fp m := gammaValid_mono fp (Nat.le_succ m) hm
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hm
    obtain ⟨Θ', θ', hΘ', hθ', hfold_m⟩ := ih (fun i => t i.castSucc) hm_pred
    have hfold_last : Fin.foldl (m + 1) (fun acc i => fp.fl_sub acc (t i)) s =
        fp.fl_sub (Fin.foldl m (fun acc i => fp.fl_sub acc (t i.castSucc)) s)
          (t (Fin.last m)) :=
      Fin.foldl_succ_last _ _
    obtain ⟨δ, hδ, hfl⟩ := fp.model_sub
        (Fin.foldl m (fun acc i => fp.fl_sub acc (t i.castSucc)) s) (t (Fin.last m))
    rw [hfold_last, hfl, hfold_m]
    refine ⟨Θ' + δ + Θ' * δ, Fin.lastCases δ (fun i => θ' i + δ + θ' i * δ), ?_, ?_, ?_⟩
    · have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
      obtain ⟨η, hη, heq⟩ := gamma_mul fp m 1 Θ' δ hΘ' hδ_1 hm
      have hval : η = Θ' + δ + Θ' * δ := by
        have hring : (1 + Θ') * (1 + δ) = 1 + (Θ' + δ + Θ' * δ) := by ring
        linarith [hring, heq]
      rw [← hval]; exact hη
    · intro i
      refine Fin.lastCases ?_ ?_ i
      · simp only [Fin.lastCases_last]
        have h1m : gamma fp 1 ≤ gamma fp (m + 1) := gamma_mono fp (by omega) hm
        linarith [u_le_gamma fp one_pos h1valid]
      · intro j
        simp only [Fin.lastCases_castSucc]
        have hδ_1 : |δ| ≤ gamma fp 1 := le_trans hδ (u_le_gamma fp one_pos h1valid)
        obtain ⟨θ_j, hθ_j, heq⟩ := gamma_mul fp m 1 (θ' j) δ (hθ' j) hδ_1 hm
        have hval : θ_j = θ' j + δ + θ' j * δ := by
          have hring : (1 + θ' j) * (1 + δ) = 1 + (θ' j + δ + θ' j * δ) := by ring
          linarith [hring, heq]
        rw [← hval]; exact hθ_j
    · rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_last, Fin.lastCases_castSucc]
      have hsum_rw : ∑ i : Fin m, t i.castSucc * (1 + (θ' i + δ + θ' i * δ)) =
                     (∑ i : Fin m, t i.castSucc * (1 + θ' i)) * (1 + δ) := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [hsum_rw]
      ring

/-- Absolute residual form of `fl_sub_sum_error_init`.

The rounded subtraction fold differs from the exact subtraction of the same
rounded terms by at most `gamma fp m` times the absolute initial accumulator
plus the absolute rounded terms. -/
lemma fl_sub_sum_error_init_abs_residual_le (fp : FPModel) (m : ℕ)
    (t : Fin m → ℝ) (s : ℝ) (hm : gammaValid fp m) :
    |(s - ∑ i : Fin m, t i) -
        Fin.foldl m (fun acc i => fp.fl_sub acc (t i)) s| ≤
      gamma fp m * (|s| + ∑ i : Fin m, |t i|) := by
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    fl_sub_sum_error_init fp m t s hm
  have hγ : 0 ≤ gamma fp m := gamma_nonneg fp hm
  have hres :
      (s - ∑ i : Fin m, t i) -
          Fin.foldl m (fun acc i => fp.fl_sub acc (t i)) s =
        -(s * Θ) + ∑ i : Fin m, t i * θ i := by
    have hsum_expand :
        (∑ i : Fin m, t i * (1 + θ i)) =
          (∑ i : Fin m, t i) + ∑ i : Fin m, t i * θ i := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfold]
    rw [hsum_expand]
    ring
  calc
    |(s - ∑ i : Fin m, t i) -
        Fin.foldl m (fun acc i => fp.fl_sub acc (t i)) s|
        = |-(s * Θ) + ∑ i : Fin m, t i * θ i| := by rw [hres]
    _ ≤ |-(s * Θ)| + |∑ i : Fin m, t i * θ i| := abs_add_le _ _
    _ ≤ |s| * |Θ| + ∑ i : Fin m, |t i| * |θ i| := by
      refine add_le_add ?_ ?_
      · rw [abs_neg, abs_mul]
      · calc
          |∑ i : Fin m, t i * θ i|
              ≤ ∑ i : Fin m, |t i * θ i| :=
                Finset.abs_sum_le_sum_abs _ _
          _ = ∑ i : Fin m, |t i| * |θ i| := by
                apply Finset.sum_congr rfl
                intro i _
                rw [abs_mul]
    _ ≤ |s| * gamma fp m + ∑ i : Fin m, |t i| * gamma fp m := by
      refine add_le_add ?_ ?_
      · exact mul_le_mul_of_nonneg_left hΘ (abs_nonneg _)
      · exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hθ i) (abs_nonneg _))
    _ = gamma fp m * (|s| + ∑ i : Fin m, |t i|) := by
      rw [← Finset.sum_mul]
      ring

-- ============================================================
-- Inverse product error bound
-- ============================================================

/-- **Inverse product error bound**: ∏(1/(1+δ_k)) = 1+θ with |θ| ≤ γ(p).

    Given p rounding errors δ_k with |δ_k| ≤ u, the product of their
    reciprocals satisfies ∏(1/(1+δ_k)) = 1+θ for some |θ| ≤ γ(p).

    This is the signed variant of `prod_error_bound` (Higham eq. 3.11)
    for all-negative exponents.  The key identity used at each step is
    (γ(p) + u) / (1 − u) = γ(p + 1), proved algebraically. -/
lemma inv_prod_error_bound (fp : FPModel) (p : ℕ) (δ : Fin p → ℝ)
    (hδ : ∀ i, |δ i| ≤ fp.u)
    (hu : fp.u < 1)
    (hp : gammaValid fp p) :
    ∃ θ : ℝ, |θ| ≤ gamma fp p ∧
      ∏ i : Fin p, (1 / (1 + δ i)) = 1 + θ := by
  induction p with
  | zero => exact ⟨0, by simp [gamma], by simp⟩
  | succ p ih =>
    have hp_pred : gammaValid fp p := gammaValid_mono fp (Nat.le_succ p) hp
    have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hp
    obtain ⟨θ', hθ', hprod⟩ := ih (fun i => δ i.castSucc) (fun i => hδ i.castSucc) hp_pred
    set δ_last := δ (Fin.last p) with hδ_last_def
    have hδ_last : |δ_last| ≤ fp.u := hδ (Fin.last p)
    have hpos : (0 : ℝ) < 1 + δ_last := by linarith [neg_abs_le δ_last]
    -- Write 1/(1+δ_last) = 1+α where α = -δ_last/(1+δ_last)
    set α := -δ_last / (1 + δ_last)
    have hα_eq : 1 / (1 + δ_last) = 1 + α := by
      simp only [α]; field_simp [hpos.ne']; ring
    -- Bound |α| ≤ γ(1): |α| = |δ_last|/(1+δ_last) ≤ u/(1-u) = γ(1)
    have hα_bound : |α| ≤ gamma fp 1 := by
      simp only [α, abs_div, abs_neg, abs_of_pos hpos]
      have h1u : (0 : ℝ) < 1 - fp.u := by linarith
      have hγ1 : gamma fp 1 = fp.u / (1 - fp.u) := by unfold gamma; simp
      rw [hγ1, ← sub_nonneg]
      have key : fp.u / (1 - fp.u) - |δ_last| / (1 + δ_last) =
                 (fp.u * (1 + δ_last) - |δ_last| * (1 - fp.u)) /
                 ((1 - fp.u) * (1 + δ_last)) := by
        field_simp [h1u.ne', hpos.ne']
      rw [key]
      apply div_nonneg
      · nlinarith [neg_abs_le δ_last, fp.u_nonneg]
      · exact le_of_lt (mul_pos h1u hpos)
    -- Combine: (1+θ')*(1+α) = 1+η with |η| ≤ γ(p+1) via gamma_mul
    obtain ⟨η, hη, heq_η⟩ := gamma_mul fp p 1 θ' α hθ' hα_bound hp
    exact ⟨η, hη, by
      rw [Fin.prod_univ_castSucc, hprod]
      show (1 + θ') * (1 / (1 + δ_last)) = 1 + η
      rw [hα_eq]; exact heq_η⟩

-- ============================================================
-- Fold unrolling with individual error factors
-- ============================================================

/-- Positivity of product of (1+δ_k) factors when each |δ_k| ≤ u < 1. -/
lemma prod_pos_of_u_bound (fp : FPModel) (m : ℕ) (δ : Fin m → ℝ)
    (hδ : ∀ k, |δ k| ≤ fp.u) (hu : fp.u < 1) :
    (0 : ℝ) < ∏ k : Fin m, (1 + δ k) := by
  apply Finset.prod_pos (s := Finset.univ)
  intro k _
  linarith [neg_abs_le (δ k), hδ k]

/-- **Subtraction fold with individual error tracking** (Higham §3.1 eq. 3.3 analog).

    For a fold s₀ = c, s_{t+1} = fl_sub(s_t, a_t), each step introduces
    a rounding error δ_t with |δ_t| ≤ u.  The unrolled result is:

      s_m = c * ∏_{k<m}(1+δ_k) - ∑_{t<m} a_t * tailProd(δ, t)

    where tailProd(δ, t) = ∏_{k : Fin m} (if t ≤ k then (1+δ_k) else 1),
    i.e., the product of (1+δ_k) for indices k ≥ t.

    This tracks each individual δ factor (unlike `fl_sub_sum_error_init`
    which collapses them into a single Θ), enabling the tight Theorem 8.5
    backward error where b is unperturbed. -/
lemma fl_sub_fold_unroll (fp : FPModel) (m : ℕ) (a : Fin m → ℝ) (c : ℝ) :
    ∃ (δ : Fin m → ℝ),
      (∀ k, |δ k| ≤ fp.u) ∧
      Fin.foldl m (fun acc t => fp.fl_sub acc (a t)) c =
        c * ∏ k : Fin m, (1 + δ k) -
        ∑ t : Fin m, a t *
          ∏ k : Fin m, if t.val ≤ k.val then (1 + δ k) else 1 := by
  induction m generalizing c with
  | zero =>
    exact ⟨fun i => i.elim0, fun i => i.elim0, by simp⟩
  | succ m ih =>
    obtain ⟨δ', hδ', hfold_m⟩ := ih (fun i => a i.castSucc) c
    -- Peel the last step
    have hfold_last : Fin.foldl (m + 1) (fun acc t => fp.fl_sub acc (a t)) c =
        fp.fl_sub (Fin.foldl m (fun acc t => fp.fl_sub acc (a t.castSucc)) c)
          (a (Fin.last m)) :=
      Fin.foldl_succ_last _ _
    -- Extract the rounding error from the last subtraction
    obtain ⟨δ_new, hδ_new, hfl_sub⟩ := fp.model_sub
        (Fin.foldl m (fun acc t => fp.fl_sub acc (a t.castSucc)) c) (a (Fin.last m))
    -- Define the combined δ
    let δ : Fin (m + 1) → ℝ := Fin.lastCases δ_new δ'
    refine ⟨δ, ?_, ?_⟩
    -- Bound: each |δ k| ≤ u
    · intro k
      refine Fin.lastCases ?_ ?_ k
      · simp only [δ, Fin.lastCases_last]; exact hδ_new
      · intro j; simp only [δ, Fin.lastCases_castSucc]; exact hδ' j
    -- Equation
    · rw [hfold_last, hfl_sub, hfold_m]
      -- LHS: (c * P_m - S_m - a_last) * (1 + δ_new)
      -- RHS: c * P_{m+1} - S_{m+1}
      -- Step 1: Decompose the full product via Fin.prod_univ_castSucc
      have hP : ∏ k : Fin (m + 1), (1 + δ k) =
          (∏ k : Fin m, (1 + δ' k)) * (1 + δ_new) := by
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl; intro k _
          show 1 + δ k.castSucc = 1 + δ' k
          simp only [δ, Fin.lastCases_castSucc]
        · show 1 + δ (Fin.last m) = 1 + δ_new
          simp only [δ, Fin.lastCases_last]
      -- Step 2: Decompose each tail product for castSucc terms
      have hTP_cast : ∀ t : Fin m,
          ∏ k : Fin (m + 1), (if t.val ≤ k.val then (1 + δ k) else 1) =
          (∏ k : Fin m, (if t.val ≤ k.val then (1 + δ' k) else 1)) * (1 + δ_new) := by
        intro t
        rw [Fin.prod_univ_castSucc]
        congr 1
        · apply Finset.prod_congr rfl; intro k _
          simp only [Fin.val_castSucc, δ, Fin.lastCases_castSucc]
        · simp only [Fin.val_last, δ, Fin.lastCases_last]
          rw [if_pos (by omega : t.val ≤ m)]
      -- Step 3: Decompose tail product for the last term
      have hTP_last :
          ∏ k : Fin (m + 1), (if (Fin.last m).val ≤ k.val then (1 + δ k) else 1) =
          1 + δ_new := by
        rw [Fin.prod_univ_castSucc]
        have hprod_one : (∏ k : Fin m,
            (if (Fin.last m).val ≤ k.castSucc.val then (1 + δ k.castSucc) else 1)) = 1 := by
          apply Finset.prod_eq_one; intro k _
          simp only [Fin.val_last, Fin.val_castSucc]
          rw [if_neg (by omega : ¬(m ≤ k.val))]
        rw [hprod_one, one_mul]
        simp only [Fin.val_last, le_refl, ite_true, δ, Fin.lastCases_last]
      -- Step 4: Decompose the sum via Fin.sum_univ_castSucc
      have hS : ∑ t : Fin (m + 1), a t *
            ∏ k : Fin (m + 1), (if t.val ≤ k.val then (1 + δ k) else 1) =
          (∑ t : Fin m, a t.castSucc *
            (∏ k : Fin m, (if t.val ≤ k.val then (1 + δ' k) else 1))) * (1 + δ_new) +
          a (Fin.last m) * (1 + δ_new) := by
        rw [Fin.sum_univ_castSucc, hTP_last]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl; intro t _
        have htv : t.castSucc.val = t.val := Fin.val_castSucc t
        simp only [htv]
        rw [hTP_cast t, mul_assoc]
      -- Step 5: Put it all together
      rw [hP, hS]; ring

end NumStability
