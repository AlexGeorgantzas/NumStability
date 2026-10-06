/-
SPDX-License-Identifier: MIT
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import NumStability.Analysis.LeadingDigits.Decimal
import NumStability.Analysis.LeadingDigits.Empirical
import NumStability.Analysis.LeadingDigits.LogarithmicDistribution

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problem 2.11

Problem 2.11 is an empirical leading-significant-digit investigation. It asks
the reader to examine powers, factorials, random symmetric-matrix eigenvalues,
physical constants, and newspaper numbers.

This canonical source locator owns the exact sample-family declarations and
re-exports the reusable decimal predicate, finite empirical distribution, and
logarithmic comparison law used to formalize the problem. Externally gathered
data remain empirical inputs.
-/

/-- The five source families named by Problem 2.11. -/
inductive problem2_11EmpiricalSource where
  | powersOfTwo
  | powersOfThree
  | factorials
  | randomSymmetricEigenvalues
  | physicalConstants
  | newspaperNumbers
  deriving DecidableEq, Repr

theorem problem2_11EmpiricalSource_exhaustive
    (s : problem2_11EmpiricalSource) :
    s = problem2_11EmpiricalSource.powersOfTwo ∨
      s = problem2_11EmpiricalSource.powersOfThree ∨
      s = problem2_11EmpiricalSource.factorials ∨
      s = problem2_11EmpiricalSource.randomSymmetricEigenvalues ∨
      s = problem2_11EmpiricalSource.physicalConstants ∨
      s = problem2_11EmpiricalSource.newspaperNumbers := by
  cases s <;> simp

/-- Source item 1: powers `k^n`, `n = 0:1000`, represented by `Fin 1001`. -/
def problem2_11_powerSample (k : ℕ) : Fin 1001 → ℝ :=
  fun n => (k ^ n.val : ℕ)

theorem problem2_11_powerSample_card :
    Fintype.card (Fin 1001) = 1001 := by
  simp

theorem problem2_11_powerSample_index_le_1000 (n : Fin 1001) :
    n.val ≤ 1000 :=
  Nat.le_of_lt_succ n.isLt

theorem problem2_11_powerSample_first (k : ℕ) :
    problem2_11_powerSample k ⟨0, by norm_num⟩ = 1 := by
  simp [problem2_11_powerSample]

theorem problem2_11_powerSample_last (k : ℕ) :
    problem2_11_powerSample k ⟨1000, by norm_num⟩ =
      ((k ^ 1000 : ℕ) : ℝ) := by
  simp [problem2_11_powerSample]

theorem problem2_11_powerSample_two_last :
    problem2_11_powerSample 2 ⟨1000, by norm_num⟩ =
      ((2 ^ 1000 : ℕ) : ℝ) :=
  problem2_11_powerSample_last 2

theorem problem2_11_powerSample_three_last :
    problem2_11_powerSample 3 ⟨1000, by norm_num⟩ =
      ((3 ^ 1000 : ℕ) : ℝ) :=
  problem2_11_powerSample_last 3

theorem problem2_11_powerSample_pos {k : ℕ} (hk : 0 < k)
    (n : Fin 1001) :
    0 < problem2_11_powerSample k n := by
  dsimp [problem2_11_powerSample]
  have hnat : 0 < k ^ n.val := Nat.pow_pos hk
  exact_mod_cast hnat

theorem problem2_11_powerSample_two_pos (n : Fin 1001) :
    0 < problem2_11_powerSample 2 n :=
  problem2_11_powerSample_pos (by norm_num) n

theorem problem2_11_powerSample_three_pos (n : Fin 1001) :
    0 < problem2_11_powerSample 3 n :=
  problem2_11_powerSample_pos (by norm_num) n

/-- Source item 2: factorials `n!`, `n = 1:1000`, represented by `Fin 1000`
with value `(i+1)!`. -/
def problem2_11_factorialSample : Fin 1000 → ℝ :=
  fun n => (Nat.factorial (n.val + 1) : ℕ)

theorem problem2_11_factorialSample_card :
    Fintype.card (Fin 1000) = 1000 := by
  simp

theorem problem2_11_factorialSample_index_between (n : Fin 1000) :
    1 ≤ n.val + 1 ∧ n.val + 1 ≤ 1000 :=
  ⟨Nat.succ_pos n.val, Nat.succ_le_of_lt n.isLt⟩

theorem problem2_11_factorialSample_first :
    problem2_11_factorialSample ⟨0, by norm_num⟩ = 1 := by
  simp [problem2_11_factorialSample]

theorem problem2_11_factorialSample_last :
    problem2_11_factorialSample ⟨999, by norm_num⟩ =
      ((Nat.factorial 1000 : ℕ) : ℝ) := by
  change ((Nat.factorial (999 + 1) : ℕ) : ℝ) =
    ((Nat.factorial 1000 : ℕ) : ℝ)
  rw [show 999 + 1 = 1000 by norm_num]

theorem problem2_11_factorialSample_pos (n : Fin 1000) :
    0 < problem2_11_factorialSample n := by
  dsimp [problem2_11_factorialSample]
  have hnat : 0 < Nat.factorial (n.val + 1) := Nat.factorial_pos _
  exact_mod_cast hnat

end

end NumStability
