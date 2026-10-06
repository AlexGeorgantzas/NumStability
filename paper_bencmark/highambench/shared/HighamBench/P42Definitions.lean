import Mathlib

open scoped BigOperators

namespace HighamBench

/-- One-based prefix product: `p42PrefixProduct f k = f 1 * ... * f k`. -/
noncomputable def p42PrefixProduct (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range k, f (i + 1)

@[simp] theorem p42PrefixProduct_zero (f : ℕ → ℝ) :
    p42PrefixProduct f 0 = 1 := by
  simp [p42PrefixProduct]

theorem p42PrefixProduct_succ (f : ℕ → ℝ) (k : ℕ) :
    p42PrefixProduct f (k + 1) = p42PrefixProduct f k * f (k + 1) := by
  simp [p42PrefixProduct, Finset.prod_range_succ, mul_comm]

/-- The scalar recurrences used in Lemma 3.1 and Appendix A.

Indices are one-based, matching the paper. The fields record the three exact
plane-rotation constructions, the transformed right-hand-side recurrence, and
the forward-substitution recurrence; the equality asserted by Lemma 3.1 is not
a field of this structure. -/
structure P42Lemma31Run where
  alpha : ℕ → ℝ
  beta : ℕ → ℝ
  alphaBar : ℕ → ℝ
  rho : ℕ → ℝ
  c : ℕ → ℝ
  s : ℕ → ℝ
  theta : ℕ → ℝ
  rhoBar : ℕ → ℝ
  cBar : ℕ → ℝ
  sBar : ℕ → ℝ
  thetaBar : ℕ → ℝ
  rhoDot : ℕ → ℝ
  rhoTilde : ℕ → ℝ
  cTilde : ℕ → ℝ
  sTilde : ℕ → ℝ
  thetaTilde : ℕ → ℝ
  betaOne : ℝ
  betaBarOne : ℝ
  betaDot : ℕ → ℝ
  betaTilde : ℕ → ℝ
  tauTilde : ℕ → ℝ
  alphaBar_one : alphaBar 1 = alpha 1
  betaBarOne_eq : betaBarOne = alpha 1 * betaOne
  cBar_zero : cBar 0 = 1
  sBar_zero : sBar 0 = 0
  rho_ne : ∀ k, 1 ≤ k → rho k ≠ 0
  rho_sq : ∀ k, 1 ≤ k →
    rho k ^ 2 = alphaBar k ^ 2 + beta (k + 1) ^ 2
  c_eq : ∀ k, 1 ≤ k → c k = alphaBar k / rho k
  s_eq : ∀ k, 1 ≤ k → s k = beta (k + 1) / rho k
  theta_succ : ∀ k, 1 ≤ k → theta (k + 1) = s k * alpha (k + 1)
  alphaBar_succ : ∀ k, 1 ≤ k →
    alphaBar (k + 1) = c k * alpha (k + 1)
  thetaBar_eq : ∀ k, 1 ≤ k → thetaBar k = sBar (k - 1) * rho k
  rhoBar_ne : ∀ k, 1 ≤ k → rhoBar k ≠ 0
  rhoBar_sq : ∀ k, 1 ≤ k →
    rhoBar k ^ 2 =
      (cBar (k - 1) * rho k) ^ 2 + theta (k + 1) ^ 2
  cBar_eq : ∀ k, 1 ≤ k →
    cBar k = cBar (k - 1) * rho k / rhoBar k
  sBar_eq : ∀ k, 1 ≤ k → sBar k = theta (k + 1) / rhoBar k
  rhoDot_one : rhoDot 1 = rhoBar 1
  rhoTilde_ne : ∀ k, 1 ≤ k → rhoTilde k ≠ 0
  rhoTilde_sq : ∀ k, 1 ≤ k →
    rhoTilde k ^ 2 = rhoDot k ^ 2 + thetaBar (k + 1) ^ 2
  cTilde_eq : ∀ k, 1 ≤ k → cTilde k = rhoDot k / rhoTilde k
  sTilde_eq : ∀ k, 1 ≤ k →
    sTilde k = thetaBar (k + 1) / rhoTilde k
  thetaTilde_succ : ∀ k, 1 ≤ k →
    thetaTilde (k + 1) = sTilde k * rhoBar (k + 1)
  rhoDot_succ : ∀ k, 1 ≤ k →
    rhoDot (k + 1) = cTilde k * rhoBar (k + 1)
  betaDot_one : betaDot 1 = c 1 * betaOne
  betaDot_succ : ∀ k, 1 ≤ k →
    betaDot (k + 1) =
      -sTilde k * betaDot k +
        cTilde k * (-1 : ℝ) ^ k *
          p42PrefixProduct s k * c (k + 1) * betaOne
  betaTilde_eq : ∀ k, 1 ≤ k →
    betaTilde k =
      cTilde k * betaDot k +
        sTilde k * (-1 : ℝ) ^ k *
          p42PrefixProduct s k * c (k + 1) * betaOne
  tauTilde_one :
    tauTilde 1 = cBar 1 * betaBarOne / rhoTilde 1
  tauTilde_succ : ∀ k, 1 ≤ k →
    tauTilde (k + 1) =
      ((-1 : ℝ) ^ (k + 2) *
          p42PrefixProduct sBar k * cBar (k + 1) * betaBarOne -
        thetaTilde (k + 1) * tauTilde k) /
      rhoTilde (k + 1)

end HighamBench
