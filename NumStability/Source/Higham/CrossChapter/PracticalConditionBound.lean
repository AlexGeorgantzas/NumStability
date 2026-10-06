import NumStability.Analysis.HighamChapter7
import NumStability.Algorithms.CondEstimation

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapters 7 -> 15: practical-bound norm-estimation bridge

Chapter 15 begins with the observation that the right-hand side of the
practical forward-error bound (7.31) has the form `|A⁻¹| d`, with `d ≥ 0`.
Equation (15.1) then rewrites its infinity norm as the matrix norm of
`A⁻¹ diag(d)`.  This file composes the actual Chapter 7 computed-residual
quantity with that identity, so the cross-chapter handoff is explicit.
-/

/-- The computed-residual safety vector occurring in (7.31) is componentwise
nonnegative. -/
theorem higham15_1_ch7ComputedResidualSafetyTerm_nonneg
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (y b : Fin n → ℝ) (hn1 : gammaValid fp (n + 1)) :
    ∀ i, 0 ≤ ch7ComputedResidualSafetyTerm fp n A y b i := by
  intro i
  unfold ch7ComputedResidualSafetyTerm
  exact add_nonneg (abs_nonneg _)
    (mul_nonneg (gamma_nonneg fp hn1)
      (add_nonneg (abs_nonneg _)
        (Finset.sum_nonneg fun j _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))

/-- Equation (15.1), specialized to the concrete `d` produced by (7.31):
`‖|A⁻¹|d‖∞ = ‖A⁻¹ diag(d)‖∞`. -/
theorem higham15_1_ch7_31_cond_norm_identity
    (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (hn1 : gammaValid fp (n + 1)) :
    infNormVec (ch7ComputedResidualImage fp n A A_inv y b) =
      infNorm (fun i j =>
        A_inv i j * ch7ComputedResidualSafetyTerm fp n A y b j) := by
  simpa [ch7ComputedResidualImage] using
    cond_norm_identity n hn A_inv
      (ch7ComputedResidualSafetyTerm fp n A y b)
      (higham15_1_ch7ComputedResidualSafetyTerm_nonneg fp n A y b hn1)

/-- The actual practical bound (7.31), with its numerator rewritten by the
Chapter 15 equation (15.1).  This is the implementation-facing Chapter
7-to-15 bridge used by norm estimation. -/
theorem higham15_1_eq_7_31_practical_bound_bridge
    (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hγn : gammaValid fp n) (hγn1 : gammaValid fp (n + 1))
    (hy : 0 < infNormVec y) :
    infNormVec (fun i => x i - y i) / infNormVec y ≤
      infNorm (fun i j =>
        A_inv i j * ch7ComputedResidualSafetyTerm fp n A y b j) /
        infNormVec y := by
  rw [← higham15_1_ch7_31_cond_norm_identity fp n hn A A_inv y b hγn1]
  exact eq_7_31_relative_infNorm_bound fp n A A_inv x y b
    hInv hAx hγn hγn1 hy

end NumStability
