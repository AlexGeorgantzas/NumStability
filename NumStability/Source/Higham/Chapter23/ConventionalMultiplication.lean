/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.GammaAsymptotics

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23: Conventional multiplication

Componentwise and normwise error bounds for conventional matrix multiplication from Higham, Chapter 23.
-/

section ConventionalMatrixMultiplication

/-- Actual conventional rounded matrix multiplication, entrywise as the
repository's left-to-right rounded dot product. -/
noncomputable def higham23FlMatrixMul (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ fl_dotProduct fp n (fun k ↦ A i k) (fun k ↦ B k j)

/-- A source-facing presentation of the max-entry norm inequality. -/
def Higham23MaxEntryNormLe {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (bound : ℝ) : Prop :=
  ∀ i j, |A i j| ≤ bound

/-- Equation (23.10), exact-gamma componentwise form for the actual computed
matrix product. -/
theorem higham23_eq23_10_conventional_componentwise (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hvalid : gammaValid fp n)
    (i j : Fin n) :
    |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
      gamma fp n * ∑ k : Fin n, |A i k| * |B k j| := by
  simpa [higham23FlMatrixMul, Matrix.mul_apply, abs_sub_comm] using
    dotProduct_error_bound fp n (fun k ↦ A i k) (fun k ↦ B k j) hvalid

/-- Equation (23.10) with the printed `nu` term and explicit `O(u²)`
remainder. -/
theorem higham23_eq23_10_conventional_firstOrder (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (hvalid : gammaValid fp n)
    (i j : Fin n) :
    |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
      (n : ℝ) * fp.u * (∑ k : Fin n, |A i k| * |B k j|) +
        higham23GammaRemainder n fp.u *
          (∑ k : Fin n, |A i k| * |B k j|) :=
  higham23_error_bound_gamma_split fp n _ _ hvalid
    (higham23_eq23_10_conventional_componentwise fp A B hvalid i j)

/-- Equation (23.17), as the exact max-entry envelope produced from (23.10).
The first summand is the printed `n²u` coefficient; the second is a genuine
quadratic remainder by `higham23_gammaRemainder_isBigO_u_sq`. -/
theorem higham23_eq23_17_conventional_normwise (fp : FPModel) {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ) (Amax Bmax : ℝ)
    (hAmax : 0 ≤ Amax) (_hBmax : 0 ≤ Bmax)
    (hA : Higham23MaxEntryNormLe A Amax)
    (hB : Higham23MaxEntryNormLe B Bmax)
    (hvalid : gammaValid fp n) :
    Higham23MaxEntryNormLe (A * B - higham23FlMatrixMul fp A B)
      ((n : ℝ) ^ 2 * fp.u * Amax * Bmax +
        higham23GammaRemainder n fp.u * (n : ℝ) * Amax * Bmax) := by
  intro i j
  have hcomp := higham23_eq23_10_conventional_componentwise fp A B hvalid i j
  have hbudget :
      (∑ k : Fin n, |A i k| * |B k j|) ≤ (n : ℝ) * Amax * Bmax := by
    calc
      (∑ k : Fin n, |A i k| * |B k j|) ≤
          ∑ _k : Fin n, Amax * Bmax := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hAmax
      _ = (n : ℝ) * Amax * Bmax := by simp; ring
  have hgamma : 0 ≤ gamma fp n := gamma_nonneg fp hvalid
  have hgammaBound :
      |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
        gamma fp n * ((n : ℝ) * Amax * Bmax) :=
    le_trans hcomp (mul_le_mul_of_nonneg_left hbudget hgamma)
  have hsplit := higham23_error_bound_gamma_split fp n
    |(A * B) i j - higham23FlMatrixMul fp A B i j|
    ((n : ℝ) * Amax * Bmax) hvalid hgammaBound
  simpa [Higham23MaxEntryNormLe, Matrix.sub_apply] using (show
    |(A * B) i j - higham23FlMatrixMul fp A B i j| ≤
      (n : ℝ) ^ 2 * fp.u * Amax * Bmax +
        higham23GammaRemainder n fp.u * (n : ℝ) * Amax * Bmax by
      nlinarith)

end ConventionalMatrixMultiplication

end NumStability
