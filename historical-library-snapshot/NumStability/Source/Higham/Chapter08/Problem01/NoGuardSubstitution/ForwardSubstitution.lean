import NumStability.Algorithms.LinearSystems.Triangular.ErrorAnalysis.NoGuardBackward
import NumStability.Algorithms.LinearSystems.Triangular.ErrorAnalysis.NoGuardForward
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
























































































































































































/-- **Problem 8.1**, lower-triangular matrix form.

For an ordered no-guard forward-substitution computation, the computed vector is
the exact solution of a componentwise perturbed triangular system with the
Problem 8.1 envelope `|ΔL| ≤ γ_(n+1)|L|`. -/
theorem noGuard_forwardSub_backward_error (fp : NoGuardFPModel) (n : ℕ)
    (L : Fin n → Fin n → ℝ) (b xhat : Fin n → ℝ)
    (hL : ∀ i, L i i ≠ 0)
    (hLT : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hn : noGuardGammaValid fp (n + 1))
    (hrow : NoGuardForwardSubSpec fp n L b xhat) :
    ∃ ΔL : Fin n → Fin n → ℝ,
      (∀ i j, |ΔL i j| ≤ noGuardGamma fp (n + 1) * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * xhat j = b i := by
  classical
  have h_rows : ∀ i : Fin n,
      ∃ (θdiag : ℝ) (η : Fin i.val → ℝ),
        |θdiag| ≤ noGuardGamma fp (n + 1) ∧
        (∀ q, |η q| ≤ noGuardGamma fp (n + 1)) ∧
        L i i * xhat i * (1 + θdiag) =
          b i - ∑ q : Fin i.val,
            L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η q) :=
    fun i => noGuard_forwardSub_row_error fp n L b xhat hL hn hrow i
  let θdiag : Fin n → ℝ := fun i => Classical.choose (h_rows i)
  let η_data : (i : Fin n) → Fin i.val → ℝ := fun i =>
    Classical.choose (Classical.choose_spec (h_rows i))
  have hθdiag_bound : ∀ i, |θdiag i| ≤ noGuardGamma fp (n + 1) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).1
  have hη_bound : ∀ i q, |η_data i q| ≤ noGuardGamma fp (n + 1) := fun i q =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.1 q
  have hrow_eq : ∀ i,
      L i i * xhat i * (1 + θdiag i) =
        b i - ∑ q : Fin i.val,
          L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η_data i q) := fun i =>
    (Classical.choose_spec (Classical.choose_spec (h_rows i))).2.2
  let ΔL : Fin n → Fin n → ℝ := fun i j =>
    if hdiag : j.val = i.val then L i j * θdiag i
    else if hlower : j.val < i.val then
      L i j * η_data i ⟨j.val, by omega⟩
    else 0
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    show |ΔL i j| ≤ noGuardGamma fp (n + 1) * |L i j|
    simp only [ΔL]
    by_cases hdiag : j.val = i.val
    · simp only [hdiag, dite_true, abs_mul]
      rw [mul_comm (noGuardGamma fp (n + 1))]
      exact mul_le_mul_of_nonneg_left (hθdiag_bound i) (abs_nonneg _)
    · simp only [hdiag, dite_false]
      by_cases hlower : j.val < i.val
      · simp only [hlower, dite_true, abs_mul]
        rw [mul_comm (noGuardGamma fp (n + 1))]
        exact mul_le_mul_of_nonneg_left
          (hη_bound i ⟨j.val, by omega⟩) (abs_nonneg _)
      · simp only [hlower, dite_false, abs_zero]
        exact mul_nonneg (gamma_nonneg fp.gammaProxy hn) (abs_nonneg _)
  · intro i
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin n => j.val ≤ i.val)]
    have habove_zero : Finset.sum
        (Finset.filter (fun j : Fin n => ¬(j.val ≤ i.val)) Finset.univ)
        (fun j => (L i j + ΔL i j) * xhat j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hj
      have hL_zero : L i j = 0 := hLT i j hj
      have hΔ_zero : ΔL i j = 0 := by
        simp only [ΔL]
        have hdiag : ¬ j.val = i.val := by omega
        have hlower : ¬ j.val < i.val := by omega
        simp [hdiag, hlower]
      rw [hL_zero, hΔ_zero, add_zero, zero_mul]
    rw [habove_zero, add_zero]
    have hrow_sum : L i i * xhat i * (1 + θdiag i) +
        (∑ q : Fin i.val,
          L i ⟨q.val, by omega⟩ * xhat ⟨q.val, by omega⟩ * (1 + η_data i q)) = b i := by
      linarith [hrow_eq i]
    rw [← hrow_sum]
    rw [← Finset.add_sum_erase _ _
      (by simp : i ∈ Finset.filter (fun j : Fin n => j.val ≤ i.val) Finset.univ)]
    have hdiag_term :
        (L i i + ΔL i i) * xhat i =
          L i i * xhat i * (1 + θdiag i) := by
      simp only [ΔL, dite_true]
      ring
    rw [hdiag_term]
    congr 1
    have hbound : ∀ q : Fin i.val, q.val < n := fun q => by
      have hi := i.isLt
      omega
    symm
    apply Finset.sum_nbij (fun (q : Fin i.val) => (⟨q.val, hbound q⟩ : Fin n))
    · intro q _
      simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by intro h; exact absurd (Fin.mk.inj h) (by omega), by omega⟩
    · intro q₁ _ q₂ _ h
      exact Fin.ext (by simp only [Fin.mk.injEq] at h; omega)
    · intro j hj
      simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
        Finset.mem_univ, true_and] at hj
      have hjlt : j.val < i.val := by
        by_cases heq : j.val = i.val
        · exfalso
          exact hj.1 (Fin.ext heq)
        · omega
      exact ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext (by simp)⟩
    · intro q _
      show
        L i ⟨q.val, hbound q⟩ * xhat ⟨q.val, hbound q⟩ *
            (1 + η_data i q) =
          (L i ⟨q.val, hbound q⟩ + ΔL i ⟨q.val, hbound q⟩) *
            xhat ⟨q.val, hbound q⟩
      have hΔ :
          ΔL i ⟨q.val, hbound q⟩ =
            L i ⟨q.val, hbound q⟩ * η_data i q := by
        simp only [ΔL]
        rw [dif_neg (by omega : ¬(q.val = i.val)),
          dif_pos (by omega : q.val < i.val)]
      rw [hΔ]
      ring

end NumStability
