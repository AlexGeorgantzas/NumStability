/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# The Higham (1997) exact/computed Bunch--Kaufman product interface

Higham's 1997 analysis proves the `36 n rho_n` max-entry estimate for the
exact factors `|L||D||L^T|`.  Section 4.3 of that paper then observes that
replacing the exact factors by computed factors changes this product by a
first-order amount.  The book prints the computed factors under the unchanged
exact coefficient.  This file records the distinction formally.

The first result is a one-dimensional counterexample to exact transport of the
coefficient.  The remaining results give the finite-precision replacement:
entrywise factor inflation by `1 + epsL` and `1 + epsD` inflates the product by
`(1 + epsL)^2 (1 + epsD)`.  A final polynomial identity isolates the extra
term as second order after multiplication by a first-order backward-error
coefficient.
-/

import NumStability.Algorithms.HighamChapter11

open scoped BigOperators

namespace NumStability

/-! ## A concrete obstruction to exact transport -/

private def higham11_4_sourceCorrectionOneMatrix :
    Fin 1 -> Fin 1 -> Real :=
  fun _ _ => 1

private def higham11_4_sourceCorrectionTwoMatrix :
    Fin 1 -> Fin 1 -> Real :=
  fun _ _ => 2

/-- An exact-factor product bound does not, by itself, imply the same bound for
nontrivially perturbed computed factors.  Here `L = D = Dhat = [1]` and
`Lhat = [2]`: the exact product has max entry `1`, while the computed product
has its sole entry equal to `4`.

This is the finite-dimensional discrepancy witness for transporting Higham
(1997), eq. (4.14), to the hatted factors with the coefficient unchanged. -/
theorem higham11_4_exact_product_bound_does_not_imply_same_computed_bound :
    let L := higham11_4_sourceCorrectionOneMatrix
    let D := higham11_4_sourceCorrectionOneMatrix
    let L_hat := higham11_4_sourceCorrectionTwoMatrix
    let D_hat := higham11_4_sourceCorrectionOneMatrix
    higham11_4_bunchKaufmanProductMax 1 (by omega) L D ≤ 1 ∧
      ¬ (higham11_4_bunchKaufmanProductMax 1 (by omega) L_hat D_hat ≤ 1) ∧
      L_hat ≠ L := by
  dsimp only
  constructor
  · rw [higham11_4_bunchKaufmanProductMax_le_iff]
    intro i j
    simp [higham11_4_bunchKaufmanProductEntry,
      higham11_4_sourceCorrectionOneMatrix]
  constructor
  · intro h
    have hentry :=
      (higham11_4_bunchKaufmanProductEntry_le_productMax 1 (by omega)
        higham11_4_sourceCorrectionTwoMatrix higham11_4_sourceCorrectionOneMatrix
        (0 : Fin 1) (0 : Fin 1)).trans h
    norm_num [higham11_4_bunchKaufmanProductEntry,
      higham11_4_sourceCorrectionOneMatrix,
      higham11_4_sourceCorrectionTwoMatrix] at hentry
  · intro hEq
    have h00 := congrFun (congrFun hEq (0 : Fin 1)) (0 : Fin 1)
    norm_num [higham11_4_sourceCorrectionOneMatrix,
      higham11_4_sourceCorrectionTwoMatrix] at h00

/-! ## Finite-u factor-to-product transfer -/

/-- The exact multiplicative inflation of `|L||D||L^T|` produced by relative
factor inflations `epsL` and `epsD`. -/
def higham11_4_relativeProductInflation (epsL epsD : Real) : Real :=
  (1 + epsL) ^ 2 * (1 + epsD)

/-- Entrywise finite-precision transfer from factor bounds to the Bunch--Kaufman
product.  Unlike an assumed bound on the final hatted product, the hypotheses
refer separately to the two computed factors and can be discharged by a
rounding analysis of their construction. -/
theorem higham11_4_computed_productEntry_le_of_relative_factor_bounds
    (n : Nat) (L D L_hat D_hat : Fin n -> Fin n -> Real)
    (epsL epsD : Real) (hepsL : 0 <= epsL) (hepsD : 0 <= epsD)
    (hL : forall i k : Fin n,
      |L_hat i k| <= (1 + epsL) * |L i k|)
    (hD : forall k l : Fin n,
      |D_hat k l| <= (1 + epsD) * |D k l|)
    (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry n L_hat D_hat i j <=
      higham11_4_relativeProductInflation epsL epsD *
        higham11_4_bunchKaufmanProductEntry n L D i j := by
  have hscaleL : 0 <= 1 + epsL := by linarith
  have hscaleD : 0 <= 1 + epsD := by linarith
  unfold higham11_4_bunchKaufmanProductEntry
  calc
    (∑ k1 : Fin n, ∑ k2 : Fin n,
        |L_hat i k1| * |D_hat k1 k2| * |L_hat j k2|) <=
        ∑ k1 : Fin n, ∑ k2 : Fin n,
          ((1 + epsL) * |L i k1|) *
            ((1 + epsD) * |D k1 k2|) *
            ((1 + epsL) * |L j k2|) := by
      apply Finset.sum_le_sum
      intro k1 _
      apply Finset.sum_le_sum
      intro k2 _
      have hLD :
          |L_hat i k1| * |D_hat k1 k2| <=
            ((1 + epsL) * |L i k1|) * ((1 + epsD) * |D k1 k2|) := by
        exact mul_le_mul (hL i k1) (hD k1 k2) (abs_nonneg _)
          (mul_nonneg hscaleL (abs_nonneg _))
      exact mul_le_mul hLD (hL j k2) (abs_nonneg _)
        (mul_nonneg
          (mul_nonneg hscaleL (abs_nonneg _))
          (mul_nonneg hscaleD (abs_nonneg _)))
    _ = ∑ k1 : Fin n, ∑ k2 : Fin n,
          higham11_4_relativeProductInflation epsL epsD *
            (|L i k1| * |D k1 k2| * |L j k2|) := by
      apply Finset.sum_congr rfl
      intro k1 _
      apply Finset.sum_congr rfl
      intro k2 _
      unfold higham11_4_relativeProductInflation
      ring
    _ = higham11_4_relativeProductInflation epsL epsD *
          (∑ k1 : Fin n, ∑ k2 : Fin n,
            |L i k1| * |D k1 k2| * |L j k2|) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k1 _
      rw [Finset.mul_sum]

/-- Relative entrywise perturbation bounds on `Lhat-L` and `Dhat-D` imply the
factor-magnitude hypotheses used by the finite-u product transfer theorem. -/
theorem higham11_4_computed_productEntry_le_of_relative_factor_perturbations
    (n : Nat) (L D L_hat D_hat : Fin n -> Fin n -> Real)
    (epsL epsD : Real) (hepsL : 0 <= epsL) (hepsD : 0 <= epsD)
    (hDeltaL : forall i k : Fin n,
      |L_hat i k - L i k| <= epsL * |L i k|)
    (hDeltaD : forall k l : Fin n,
      |D_hat k l - D k l| <= epsD * |D k l|)
    (i j : Fin n) :
    higham11_4_bunchKaufmanProductEntry n L_hat D_hat i j <=
      higham11_4_relativeProductInflation epsL epsD *
        higham11_4_bunchKaufmanProductEntry n L D i j := by
  apply higham11_4_computed_productEntry_le_of_relative_factor_bounds
    n L D L_hat D_hat epsL epsD hepsL hepsD
  · intro r k
    calc
      |L_hat r k| = |L r k + (L_hat r k - L r k)| := by ring_nf
      _ <= |L r k| + |L_hat r k - L r k| := abs_add_le _ _
      _ <= |L r k| + epsL * |L r k| :=
        add_le_add (le_refl _) (hDeltaL r k)
      _ = (1 + epsL) * |L r k| := by ring
  · intro k l
    calc
      |D_hat k l| = |D k l + (D_hat k l - D k l)| := by ring_nf
      _ <= |D k l| + |D_hat k l - D k l| := abs_add_le _ _
      _ <= |D k l| + epsD * |D k l| :=
        add_le_add (le_refl _) (hDeltaD k l)
      _ = (1 + epsD) * |D k l| := by ring

/-- Max-entry-norm transfer corresponding to
`higham11_4_computed_productEntry_le_of_relative_factor_bounds`. -/
theorem higham11_4_computed_productMax_le_of_relative_factor_bounds
    (n : Nat) (hn : 0 < n)
    (L D L_hat D_hat : Fin n -> Fin n -> Real)
    (epsL epsD : Real) (hepsL : 0 <= epsL) (hepsD : 0 <= epsD)
    (hL : forall i k : Fin n,
      |L_hat i k| <= (1 + epsL) * |L i k|)
    (hD : forall k l : Fin n,
      |D_hat k l| <= (1 + epsD) * |D k l|) :
    higham11_4_bunchKaufmanProductMax n hn L_hat D_hat <=
      higham11_4_relativeProductInflation epsL epsD *
        higham11_4_bunchKaufmanProductMax n hn L D := by
  rw [higham11_4_bunchKaufmanProductMax_le_iff]
  intro i j
  exact (higham11_4_computed_productEntry_le_of_relative_factor_bounds
    n L D L_hat D_hat epsL epsD hepsL hepsD hL hD i j).trans
      (mul_le_mul_of_nonneg_left
        (higham11_4_bunchKaufmanProductEntry_le_productMax n hn L D i j)
        (mul_nonneg (sq_nonneg (1 + epsL)) (by linarith)))

/-- Repository `maxEntryNorm` form of the finite-u product transfer. -/
theorem higham11_4_computed_absLDLT_maxEntryNorm_le_of_relative_factor_bounds
    (n : Nat) (hn : 0 < n)
    (L D L_hat D_hat : Fin n -> Fin n -> Real)
    (epsL epsD : Real) (hepsL : 0 <= epsL) (hepsD : 0 <= epsD)
    (hL : forall i k : Fin n,
      |L_hat i k| <= (1 + epsL) * |L i k|)
    (hD : forall k l : Fin n,
      |D_hat k l| <= (1 + epsD) * |D k l|) :
    maxEntryNorm hn (higham11_4_absLDLTProduct n L_hat D_hat) <=
      higham11_4_relativeProductInflation epsL epsD *
        maxEntryNorm hn (higham11_4_absLDLTProduct n L D) := by
  rw [← higham11_4_bunchKaufmanProductMax_eq_maxEntryNorm_absLDLTProduct
    n hn L_hat D_hat]
  rw [← higham11_4_bunchKaufmanProductMax_eq_maxEntryNorm_absLDLTProduct
    n hn L D]
  exact higham11_4_computed_productMax_le_of_relative_factor_bounds
    n hn L D L_hat D_hat epsL epsD hepsL hepsD hL hD

/-! ## Corrected Higham-source interface -/

/-- Correct finite-u transfer of Higham (1997), eq. (4.14), from exact factors
to computed factors.  The exact `36 n rho_n` source bound is preserved as a
premise about the exact factors; the hatted product acquires the explicit
factor-inflation multiplier. -/
theorem higham11_4_computed_productMax_le_higham1997_exact_bound_finite_u
    (n : Nat) (hn : 0 < n)
    (L D L_hat D_hat : Fin n -> Fin n -> Real)
    (epsL epsD rho_n Amax : Real)
    (hepsL : 0 <= epsL) (hepsD : 0 <= epsD)
    (hL : forall i k : Fin n,
      |L_hat i k| <= (1 + epsL) * |L i k|)
    (hD : forall k l : Fin n,
      |D_hat k l| <= (1 + epsD) * |D k l|)
    (hExact : higham11_4_bunchKaufmanMaxEntryProductBound n
      (higham11_4_bunchKaufmanProductMax n hn L D) rho_n Amax) :
    higham11_4_bunchKaufmanProductMax n hn L_hat D_hat <=
      higham11_4_relativeProductInflation epsL epsD *
        (36 * (n : Real) * rho_n * Amax) := by
  exact (higham11_4_computed_productMax_le_of_relative_factor_bounds
    n hn L D L_hat D_hat epsL epsD hepsL hepsD hL hD).trans
      (mul_le_mul_of_nonneg_left hExact
        (mul_nonneg (sq_nonneg (1 + epsL)) (by linarith)))

/-- The polynomial coefficient left after factoring one additional `u` from
the computed-factor inflation. -/
def higham11_4_relativeProductSecondOrderCoefficient
    (cL cD u : Real) : Real :=
  2 * cL + cD + (cL ^ 2 + 2 * cL * cD) * u + cL ^ 2 * cD * u ^ 2

/-- Precise first-order/second-order split for composition with Theorem 11.3.
If the factor perturbations are bounded by `cL*u` and `cD*u`, then multiplying
the computed product by the first-order solve coefficient `p*u` yields the
exact-factor source term plus an explicit multiple of `u^2`.

This is the formal finite-u content of the `O(u)` replacement observation in
Higham (1997), section 4.3; no unchanged exact hatted-factor bound is assumed. -/
theorem higham11_4_first_order_times_computed_productMax_le_exact_plus_second_order
    (n : Nat) (hn : 0 < n)
    (L D L_hat D_hat : Fin n -> Fin n -> Real)
    (p cL cD u B : Real)
    (hp : 0 <= p) (hcL : 0 <= cL) (hcD : 0 <= cD) (hu : 0 <= u)
    (hL : forall i k : Fin n,
      |L_hat i k| <= (1 + cL * u) * |L i k|)
    (hD : forall k l : Fin n,
      |D_hat k l| <= (1 + cD * u) * |D k l|)
    (hExact : higham11_4_bunchKaufmanProductMax n hn L D <= B) :
    (p * u) * higham11_4_bunchKaufmanProductMax n hn L_hat D_hat <=
      (p * u) * B +
        p * u ^ 2 * higham11_4_relativeProductSecondOrderCoefficient cL cD u * B := by
  have hepsL : 0 <= cL * u := mul_nonneg hcL hu
  have hepsD : 0 <= cD * u := mul_nonneg hcD hu
  have hcomputed :
      higham11_4_bunchKaufmanProductMax n hn L_hat D_hat <=
        higham11_4_relativeProductInflation (cL * u) (cD * u) * B :=
    (higham11_4_computed_productMax_le_of_relative_factor_bounds
      n hn L D L_hat D_hat (cL * u) (cD * u)
        hepsL hepsD hL hD).trans
      (mul_le_mul_of_nonneg_left hExact
        (mul_nonneg (sq_nonneg (1 + cL * u)) (by linarith)))
  calc
    (p * u) * higham11_4_bunchKaufmanProductMax n hn L_hat D_hat <=
        (p * u) *
          (higham11_4_relativeProductInflation (cL * u) (cD * u) * B) :=
      mul_le_mul_of_nonneg_left hcomputed (mul_nonneg hp hu)
    _ = (p * u) * B +
        p * u ^ 2 * higham11_4_relativeProductSecondOrderCoefficient cL cD u * B := by
      unfold higham11_4_relativeProductInflation
        higham11_4_relativeProductSecondOrderCoefficient
      ring

#print axioms higham11_4_exact_product_bound_does_not_imply_same_computed_bound
#print axioms higham11_4_computed_productEntry_le_of_relative_factor_perturbations
#print axioms higham11_4_computed_absLDLT_maxEntryNorm_le_of_relative_factor_bounds
#print axioms higham11_4_computed_productMax_le_higham1997_exact_bound_finite_u
#print axioms higham11_4_first_order_times_computed_productMax_le_exact_plus_second_order

end NumStability
