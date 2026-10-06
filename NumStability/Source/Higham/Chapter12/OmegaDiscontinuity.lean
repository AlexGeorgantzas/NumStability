/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/

import NumStability.Source.Higham.Chapter12.IterativeRefinement

namespace NumStability

noncomputable section

/-!
# Higham Chapter 12: the zero-denominator backward-error discontinuity

Printed page 241 observes that componentwise relative backward error is
ill-posed at an exact solution when a component of `|A||x|` vanishes.  This
file uses `ENNReal` for the Oettli--Prager ratio, so the source convention
`xi / 0 = 0` for `xi = 0` and `infinity` otherwise is represented literally.
-/

/-- Residual component `b_i - (Ay)_i`. -/
def higham12ResidualComponent {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (y : Fin n → Real) (i : Fin m) : Real :=
  b i - ∑ j : Fin n, A i j * y j

/-- Componentwise relative tolerance `( |A| |y| + |b| )_i`. -/
def higham12ComponentwiseTolerance {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (y : Fin n → Real) (i : Fin m) : Real :=
  (∑ j : Fin n, |A i j| * |y j|) + |b i|

/-- One Oettli--Prager row ratio.  Extended nonnegative reals encode the
printed zero-denominator convention without an auxiliary case split. -/
noncomputable def higham12ComponentwiseBackwardRowRatio {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (y : Fin n → Real) (i : Fin m) : ENNReal :=
  ENNReal.ofReal |higham12ResidualComponent A b y i| /
    ENNReal.ofReal (higham12ComponentwiseTolerance A b y i)

/-- Higham's componentwise relative backward error
`omega_{|A|,|b|}(y)`, as the maximum of the row ratios. -/
noncomputable def higham12ComponentwiseBackwardOmega {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (y : Fin n → Real) : ENNReal :=
  (Finset.univ : Finset (Fin m)).sup
    (higham12ComponentwiseBackwardRowRatio A b y)

/-- An exact solution has zero componentwise relative backward error, including
rows with the source's `0/0 = 0` convention. -/
theorem higham12_componentwiseBackwardOmega_eq_zero_of_exact {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (x : Fin n → Real)
    (hsolve : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    higham12ComponentwiseBackwardOmega A b x = 0 := by
  unfold higham12ComponentwiseBackwardOmega
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    simp [higham12ComponentwiseBackwardRowRatio,
      higham12ResidualComponent, hsolve i]
  · exact bot_le

/-- If one component of `|A||x|` vanishes, every product in that row vanishes. -/
theorem higham12_abs_row_term_eq_zero_of_sum_eq_zero {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (x : Fin n → Real)
    (i : Fin m)
    (hrow : (∑ j : Fin n, |A i j| * |x j|) = 0) :
    ∀ j : Fin n, |A i j| * |x j| = 0 := by
  intro j
  have hnonneg : ∀ k : Fin n, 0 ≤ |A i k| * |x k| :=
    fun k => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hle : |A i j| * |x j| ≤
      ∑ k : Fin n, |A i k| * |x k| := by
    exact Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_univ j)
  rw [hrow] at hle
  exact le_antisymm hle (hnonneg j)

/-- Change only coordinate `j` by `delta`. -/
def higham12SingleComponentPerturb {n : Nat}
    (x : Fin n → Real) (j : Fin n) (delta : Real) : Fin n → Real :=
  Function.update x j (x j + delta)

/-- The precise page-241 phenomenon: at an exact solution with
`(|A||x|)_i = 0`, every nonzero change to a coordinate coupled to row `i`
raises the componentwise relative backward error to at least one. -/
theorem higham12_componentwiseBackwardOmega_ge_one_of_zero_row_component_perturb
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (x : Fin n → Real) (i : Fin m) (j : Fin n)
    (hsolve : ∀ r, ∑ k : Fin n, A r k * x k = b r)
    (hrow : (∑ k : Fin n, |A i k| * |x k|) = 0)
    (haij : A i j ≠ 0) {delta : Real} (hdelta : delta ≠ 0) :
    (1 : ENNReal) ≤
      higham12ComponentwiseBackwardOmega A b
        (higham12SingleComponentPerturb x j delta) := by
  have hterm := higham12_abs_row_term_eq_zero_of_sum_eq_zero A x i hrow
  have hAxzero : ∀ k : Fin n, A i k * x k = 0 := by
    intro k
    apply abs_eq_zero.mp
    rw [abs_mul]
    exact hterm k
  have hbi : b i = 0 := by
    rw [← hsolve i]
    exact Finset.sum_eq_zero (fun k _ => hAxzero k)
  have hxj : x j = 0 := by
    have hprod := hterm j
    rcases mul_eq_zero.mp hprod with hA | hx
    · exact False.elim (haij (abs_eq_zero.mp hA))
    · exact abs_eq_zero.mp hx
  have hsum :
      (∑ k : Fin n,
          A i k * higham12SingleComponentPerturb x j delta k) =
        A i j * delta := by
    rw [Finset.sum_eq_single j]
    · simp [higham12SingleComponentPerturb, hxj]
    · intro k hk hkj
      rw [higham12SingleComponentPerturb, Function.update_of_ne hkj]
      exact hAxzero k
    · simp
  have habssum :
      (∑ k : Fin n,
          |A i k| * |higham12SingleComponentPerturb x j delta k|) =
        |A i j| * |delta| := by
    rw [Finset.sum_eq_single j]
    · simp [higham12SingleComponentPerturb, hxj]
    · intro k hk hkj
      rw [higham12SingleComponentPerturb, Function.update_of_ne hkj]
      exact hterm k
    · simp
  have hqpos : 0 < |A i j| * |delta| :=
    mul_pos (abs_pos.mpr haij) (abs_pos.mpr hdelta)
  have hrowratio :
      higham12ComponentwiseBackwardRowRatio A b
          (higham12SingleComponentPerturb x j delta) i = 1 := by
    simp only [higham12ComponentwiseBackwardRowRatio,
      higham12ResidualComponent, higham12ComponentwiseTolerance,
      hsum, habssum, hbi, abs_zero, add_zero, zero_sub, abs_neg, abs_mul]
    have hne : ENNReal.ofReal (|A i j| * |delta|) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr hqpos
    exact ENNReal.div_self hne ENNReal.ofReal_ne_top
  have hle := Finset.le_sup
    (s := (Finset.univ : Finset (Fin m)))
    (f := higham12ComponentwiseBackwardRowRatio A b
      (higham12SingleComponentPerturb x j delta))
    (Finset.mem_univ i)
  rw [hrowratio] at hle
  exact hle

/-- Literal "arbitrarily small change" corollary from printed page 241. -/
theorem higham12_exists_arbitrarily_small_component_perturb_with_omega_ge_one
    {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) (b : Fin m → Real)
    (x : Fin n → Real) (i : Fin m) (j : Fin n)
    (hsolve : ∀ r, ∑ k : Fin n, A r k * x k = b r)
    (hrow : (∑ k : Fin n, |A i k| * |x k|) = 0)
    (haij : A i j ≠ 0) :
    ∀ epsilon > 0, ∃ delta : Real,
      0 < |delta| ∧ |delta| < epsilon ∧
      (1 : ENNReal) ≤
        higham12ComponentwiseBackwardOmega A b
          (higham12SingleComponentPerturb x j delta) := by
  intro epsilon hepsilon
  refine ⟨epsilon / 2, ?_, ?_, ?_⟩
  · rw [abs_of_pos (half_pos hepsilon)]
    exact half_pos hepsilon
  · rw [abs_of_pos (half_pos hepsilon)]
    linarith
  · exact
      higham12_componentwiseBackwardOmega_ge_one_of_zero_row_component_perturb
        A b x i j hsolve hrow haij (ne_of_gt (half_pos hepsilon))

end

end NumStability
