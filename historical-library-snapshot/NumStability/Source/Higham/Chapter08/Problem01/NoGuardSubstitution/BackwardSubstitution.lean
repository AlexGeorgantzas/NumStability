import NumStability.Algorithms.LinearSystems.Triangular.ErrorAnalysis.NoGuardBackward
import NumStability.Analysis.FloatingPointArithmetic.ErrorModels.NoGuardModel
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold

-- Algorithms/TriangularNoGuard.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 8, Problem 8.1.  No-guard-digit triangular-substitution support.





namespace NumStability

open scoped BigOperators

namespace NoGuardFPModel







end NoGuardFPModel









/-! ## Problem 8.1 support: no-guard subtraction folds -/



































































































































































































































































































































































































/-! ## Problem 8.1: no-guard triangular substitution -/


















































set_option maxHeartbeats 800000

/-- **Problem 8.1**, upper-triangular matrix form.

For an ordered no-guard back-substitution computation, the computed vector is
the exact solution of a componentwise perturbed triangular system with the
Problem 8.1 envelope `|ΔU| ≤ γ_(n+1)|U|`. -/
theorem noGuard_backSub_backward_error (fp : NoGuardFPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (hU : ∀ i, U i i ≠ 0)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hn : noGuardGammaValid fp (n + 1))
    (hrow : NoGuardBackSubSpec fp n U b xhat) :
    ∃ ΔU : Fin n → Fin n → ℝ,
      (∀ i j, |ΔU i j| ≤ noGuardGamma fp (n + 1) * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + ΔU i j) * xhat j = b i := by
  classical
  have h_rows : ∀ i : Fin n,
      ∃ (θdiag : ℝ) (η : Fin (n - i.val - 1) → ℝ),
        |θdiag| ≤ noGuardGamma fp (n + 1) ∧
        (∀ q, |η q| ≤ noGuardGamma fp (n + 1)) ∧
        U i i * xhat i * (1 + θdiag) =
          b i - ∑ q : Fin (n - i.val - 1),
            U i ⟨i.val + 1 + q.val, by omega⟩ *
              xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η q) :=
    fun i => noGuard_backSub_row_error fp n U b xhat hU hn hrow i
  let θdiag : Fin n → ℝ := fun i => Classical.choose (h_rows i)
  let η_data : (i : Fin n) → Fin (n - i.val - 1) → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (h_rows i))
  have hθdiag_bound : ∀ i, |θdiag i| ≤ noGuardGamma fp (n + 1) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).1
  have hη_bound : ∀ i q, |η_data i q| ≤ noGuardGamma fp (n + 1) := fun i q =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.1 q
  have hrow_eq : ∀ i,
      U i i * xhat i * (1 + θdiag i) =
        b i - ∑ q : Fin (n - i.val - 1),
          U i ⟨i.val + 1 + q.val, by omega⟩ *
            xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η_data i q) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.2
  let ΔU : Fin n → Fin n → ℝ := fun i j =>
    if hdiag : j.val = i.val then U i j * θdiag i
    else if hupper : i.val < j.val then
      U i j * η_data i ⟨j.val - (i.val + 1), by omega⟩
    else 0
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    show |ΔU i j| ≤ noGuardGamma fp (n + 1) * |U i j|
    simp only [ΔU]
    by_cases hdiag : j.val = i.val
    · simp only [hdiag, dite_true, abs_mul]
      rw [mul_comm (noGuardGamma fp (n + 1))]
      exact mul_le_mul_of_nonneg_left (hθdiag_bound i) (abs_nonneg _)
    · simp only [hdiag, dite_false]
      by_cases hupper : i.val < j.val
      · simp only [hupper, dite_true, abs_mul]
        rw [mul_comm (noGuardGamma fp (n + 1))]
        exact mul_le_mul_of_nonneg_left
          (hη_bound i ⟨j.val - (i.val + 1), by omega⟩) (abs_nonneg _)
      · simp only [hupper, dite_false, abs_zero]
        exact mul_nonneg (gamma_nonneg fp.gammaProxy hn) (abs_nonneg _)
  · intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => i.val ≤ j.val)]
    have hbelow_zero : Finset.sum
        (Finset.filter (fun j : Fin n => ¬(i.val ≤ j.val)) Finset.univ)
        (fun j => (U i j + ΔU i j) * xhat j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hU_zero : U i j = 0 := hUT i j hj
      have hΔ_zero : ΔU i j = 0 := by
        simp only [ΔU]
        have hdiag : ¬ j.val = i.val := by omega
        have hupper : ¬ i.val < j.val := by omega
        simp [hdiag, hupper]
      rw [hU_zero, hΔ_zero, add_zero, zero_mul]
    rw [hbelow_zero, add_zero]
    have hrow_sum : U i i * xhat i * (1 + θdiag i) +
        (∑ q : Fin (n - i.val - 1),
          U i ⟨i.val + 1 + q.val, by omega⟩ *
            xhat ⟨i.val + 1 + q.val, by omega⟩ * (1 + η_data i q)) = b i := by
      linarith [hrow_eq i]
    rw [← hrow_sum]
    rw [← Finset.add_sum_erase _ _
      (by simp : i ∈ Finset.filter (fun j : Fin n => i.val ≤ j.val) Finset.univ)]
    have hdiag_term :
        (U i i + ΔU i i) * xhat i =
          U i i * xhat i * (1 + θdiag i) := by
      simp only [ΔU, dite_true]
      ring
    rw [hdiag_term]
    congr 1
    have hbound : ∀ q : Fin (n - i.val - 1), i.val + 1 + q.val < n := fun q => by
      have hi := i.isLt
      omega
    symm
    apply Finset.sum_nbij
      (fun (q : Fin (n - i.val - 1)) =>
        (⟨i.val + 1 + q.val, hbound q⟩ : Fin n))
    · intro q _
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by intro h; exact absurd (Fin.mk.inj h) (by omega), by omega⟩
    · intro q₁ _ q₂ _ h
      exact Fin.ext (by simp only [Fin.mk.injEq] at h; omega)
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      have hij : i.val < j.val := by
        by_cases heq : j.val = i.val
        · exfalso
          exact hj.1 (Fin.ext heq)
        · omega
      exact ⟨⟨j.val - (i.val + 1), by omega⟩, Finset.mem_univ _,
        Fin.ext (by simp; omega)⟩
    · intro q _
      show
        U i ⟨i.val + 1 + q.val, hbound q⟩ *
            xhat ⟨i.val + 1 + q.val, hbound q⟩ * (1 + η_data i q) =
          (U i ⟨i.val + 1 + q.val, hbound q⟩ +
              ΔU i ⟨i.val + 1 + q.val, hbound q⟩) *
            xhat ⟨i.val + 1 + q.val, hbound q⟩
      have hΔ :
          ΔU i ⟨i.val + 1 + q.val, hbound q⟩ =
            U i ⟨i.val + 1 + q.val, hbound q⟩ * η_data i q := by
        simp only [ΔU]
        rw [dif_neg (by omega : ¬(i.val + 1 + q.val = i.val)),
          dif_pos (by omega : i.val < i.val + 1 + q.val)]
        have hidx :
            (⟨(⟨i.val + 1 + q.val, hbound q⟩ : Fin n).val - (i.val + 1), by
                change i.val + 1 + q.val - (i.val + 1) < n - i.val - 1
                omega⟩ :
              Fin (n - i.val - 1)) = q := by
          apply Fin.ext
          change i.val + 1 + q.val - (i.val + 1) = q.val
          omega
        rw [hidx]
      rw [hΔ]
      ring








































































































































































end NumStability
