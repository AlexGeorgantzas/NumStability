/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace NumStability

open scoped BigOperators

/-!
# Unsupported legacy fast-multiplication bounds

This internal module preserves declarations historically exported by
`NumStability.Algorithms.FastMatMul`. They are stale first-edition source
stand-ins or weak placeholder propositions and are not used by the formalized
Chapter 23 results. They remain reachable through the historical family
umbrella solely for compatibility and are not a supported new import surface.
-/

/-- Legacy placeholder for a normwise Strassen error bound. -/
structure StrassenErrorBound (n : ℕ)
    (A B C_hat : Fin n → Fin n → ℝ)
    (c_bound u : ℝ) : Prop where
  /-- Positive unit roundoff. -/
  u_pos : 0 < u
  /-- Nonnegative coefficient. -/
  bound_nonneg : 0 ≤ c_bound
  /-- Entrywise consequence of the placeholder bound. -/
  error_bound : ∀ maxA maxB : ℝ,
    (∀ a b : Fin n, |A a b| ≤ maxA) →
    (∀ a b : Fin n, |B a b| ≤ maxB) →
    ∀ i j : Fin n,
      |∑ k : Fin n, A i k * B k j - C_hat i j| ≤ c_bound * u * maxA * maxB

/-- Historical Winograd--Strassen alias of `StrassenErrorBound`. -/
abbrev WinogradStrassenErrorBound := StrassenErrorBound

/-- The legacy scalar comparison used to contrast conventional and fast
coefficient growth. -/
theorem conventional_componentwise_implies_cubic
    (n : ℕ) (c_conv c_fast : ℝ)
    (hConv : c_conv = (n : ℝ) ^ 2)
    (hFast_gt : c_fast > (n : ℝ) ^ 2)
    (hn : 1 < (n : ℝ)) :
    c_conv < c_fast := by
  linarith

/-- Legacy placeholder for the Winograd inner-product error statement. -/
structure WinogradInnerProductError (n : ℕ)
    (x y : Fin n → ℝ) (result : ℝ) (eps : ℝ) : Prop where
  n_even : 2 ∣ n
  bound : |∑ k : Fin n, x k * y k - result| ≤ eps

/-- Legacy placeholder for a general bilinear-algorithm error statement. -/
structure BilinearAlgorithmError (n : ℕ)
    (c_bound u : ℝ) : Prop where
  u_pos : 0 < u
  bound_nonneg : 0 ≤ c_bound

/-- Legacy placeholder for a componentwise 3M error statement. -/
structure ThreeMMethodError (n : ℕ)
    (A1 A2 B1 B2 : Fin n → Fin n → ℝ)
    (C1_hat C2_hat : Fin n → Fin n → ℝ)
    (eps_real eps_imag : ℝ) : Prop where
  eps_nonneg : 0 ≤ eps_real ∧ 0 ≤ eps_imag
  /-- Real-part componentwise error placeholder. -/
  real_bound : ∀ i j : Fin n,
    |∑ k, (A1 i k * B1 k j - A2 i k * B2 k j) - C1_hat i j| ≤ eps_real
  /-- Imaginary-part componentwise error placeholder. -/
  imag_bound : ∀ i j : Fin n,
    |∑ k, (A1 i k * B2 k j + A2 i k * B1 k j) - C2_hat i j| ≤ eps_imag

end NumStability
