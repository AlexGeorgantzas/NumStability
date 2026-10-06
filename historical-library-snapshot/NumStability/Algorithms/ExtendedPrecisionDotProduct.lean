-- Algorithms/ExtendedPrecisionDotProduct.lean

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct

namespace NumStability

open scoped BigOperators

/-!
# Extended-precision inner products

Higham Chapter 3, pp. 70--71, describes computing an inner product in a
higher-precision arithmetic with unit roundoff `u_e`, then rounding the final
accumulated value back to the working precision with unit roundoff `u`.

The repository's abstract `FPModel` has binary rounded operations, but no
generic unary "round this exact real into a target format" operation.  This
file therefore exposes the final rounding as an explicit unary model
`FinalRoundingModel u round`.
-/

/-- Unary relative-error model for the final rounding from extended precision
back to the working precision. -/
def FinalRoundingModel (u : ℝ) (round : ℝ → ℝ) : Prop :=
  ∀ z : ℝ, ∃ δ : ℝ, |δ| ≤ u ∧ round z = z * (1 + δ)

/-- Final rounding preserves the extended value up to a working-precision
relative error, so the rounded result differs from `exact * (1 + δ)` only by
the extended-precision error multiplied by the final factor. -/
theorem finalRound_error_from_rounded_exact {u : ℝ} {round : ℝ → ℝ}
    (hround : FinalRoundingModel u round) {s exact B : ℝ}
    (hs : |s - exact| ≤ B) (hB : 0 ≤ B) :
    ∃ δ : ℝ,
      |δ| ≤ u ∧ |round s - exact * (1 + δ)| ≤ (1 + u) * B := by
  obtain ⟨δ, hδ, hround_s⟩ := hround s
  refine ⟨δ, hδ, ?_⟩
  have hone : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ ≤ 1 + u := by
        simpa using add_le_add_left hδ (1 : ℝ)
  have hdecomp : round s - exact * (1 + δ) = (s - exact) * (1 + δ) := by
    rw [hround_s]
    ring
  rw [hdecomp, abs_mul]
  calc
    |s - exact| * |1 + δ| ≤ B * (1 + u) :=
      mul_le_mul hs hone (abs_nonneg _) hB
    _ = (1 + u) * B := by ring

/-- Absolute-error form after final rounding.

This is the algebraic source of the displayed extended-precision bound:
one term is the final working-precision rounding of the exact inner product,
and one term is the extended-precision accumulation error, amplified by at
most `1 + u`. -/
theorem finalRound_error_bound {u : ℝ} {round : ℝ → ℝ}
    (hround : FinalRoundingModel u round) {s exact B : ℝ}
    (hs : |s - exact| ≤ B) (hB : 0 ≤ B) :
    |round s - exact| ≤ u * |exact| + (1 + u) * B := by
  obtain ⟨δ, hδ, hround_s⟩ := hround s
  have hone : |1 + δ| ≤ 1 + u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ ≤ 1 + u := by
        simpa using add_le_add_left hδ (1 : ℝ)
  have hdecomp : round s - exact = exact * δ + (s - exact) * (1 + δ) := by
    rw [hround_s]
    ring
  rw [hdecomp]
  calc
    |exact * δ + (s - exact) * (1 + δ)|
        ≤ |exact * δ| + |(s - exact) * (1 + δ)| := abs_add_le _ _
    _ = |exact| * |δ| + |s - exact| * |1 + δ| := by
          rw [abs_mul, abs_mul]
    _ ≤ |exact| * u + B * (1 + u) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hδ (abs_nonneg _))
            (mul_le_mul hs hone (abs_nonneg _) hB)
    _ = u * |exact| + (1 + u) * B := by ring

/-- Standard extended-precision dot product: compute the whole inner product
with the inner `FPModel`, then apply a unary final rounding. -/
noncomputable def fl_extendedDotProduct (inner : FPModel)
    (finalRound : ℝ → ℝ) (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  finalRound (fl_dotProduct inner n x y)

/-- Extended-precision dot product compared with the same final rounding
factor applied to the exact inner product. -/
theorem extendedDotProduct_error_from_rounded_exact (inner : FPModel)
    {u : ℝ} {finalRound : ℝ → ℝ} (n : ℕ) (x y : Fin n → ℝ)
    (hround : FinalRoundingModel u finalRound)
    (hγ : gammaValid inner n) :
    ∃ δ : ℝ,
      |δ| ≤ u ∧
      |fl_extendedDotProduct inner finalRound n x y -
          (∑ i : Fin n, x i * y i) * (1 + δ)| ≤
        (1 + u) * (gamma inner n *
          ∑ i : Fin n, |x i| * |y i|) := by
  let exact := ∑ i : Fin n, x i * y i
  let B := gamma inner n * ∑ i : Fin n, |x i| * |y i|
  have hinner :
      |fl_dotProduct inner n x y - exact| ≤ B := by
    simpa [exact, B] using dotProduct_error_bound inner n x y hγ
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| * |y i| := by
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hB : 0 ≤ B :=
    mul_nonneg (gamma_nonneg inner hγ) hsum_nonneg
  simpa [fl_extendedDotProduct, exact, B] using
    finalRound_error_from_rounded_exact hround hinner hB

/-- Extended-precision dot product absolute-error bound.

This is the formal version of Higham's displayed estimate
`u*|x^T y| + (1+u)*gamma_n^(e)*|x|^T|y|`, with
`gamma inner n` representing the inner precision's `gamma_n^(e)`. -/
theorem extendedDotProduct_error_bound (inner : FPModel)
    {u : ℝ} {finalRound : ℝ → ℝ} (n : ℕ) (x y : Fin n → ℝ)
    (hround : FinalRoundingModel u finalRound)
    (hγ : gammaValid inner n) :
    |fl_extendedDotProduct inner finalRound n x y -
        ∑ i : Fin n, x i * y i| ≤
      u * |∑ i : Fin n, x i * y i| +
        (1 + u) * (gamma inner n *
          ∑ i : Fin n, |x i| * |y i|) := by
  let exact := ∑ i : Fin n, x i * y i
  let B := gamma inner n * ∑ i : Fin n, |x i| * |y i|
  have hinner :
      |fl_dotProduct inner n x y - exact| ≤ B := by
    simpa [exact, B] using dotProduct_error_bound inner n x y hγ
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| * |y i| := by
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hB : 0 ≤ B :=
    mul_nonneg (gamma_nonneg inner hγ) hsum_nonneg
  simpa [fl_extendedDotProduct, exact, B] using
    finalRound_error_bound hround hinner hB

/-- Inner product with exact products and rounded extended-precision additions.

This models the parenthetical source case in which products are formed exactly
in the extended format before accumulation. -/
noncomputable def fl_exactMulDotProduct (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n' (fun acc i => fp.fl_add acc (x i.succ * y i.succ))
        (x 0 * y 0)

/-- Exact-product dot product backward error: only the `n-1` additions are
charged, matching the source's "subscripts reduced by 1" parenthetical. -/
theorem exactMulDotProduct_backward_error (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hγ : gammaValid fp (n - 1)) :
    ∃ η : Fin n → ℝ,
      (∀ i, |η i| ≤ gamma fp (n - 1)) ∧
      fl_exactMulDotProduct fp n x y =
        ∑ i : Fin n, x i * y i * (1 + η i) := by
  cases n with
  | zero =>
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp [fl_exactMulDotProduct]⟩
  | succ n' =>
      simp only [Nat.succ_sub_one] at hγ
      obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
        fl_sum_error_init fp n'
          (fun i => x i.succ * y i.succ) (x 0 * y 0) hγ
      refine ⟨Fin.cons Θ θ, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hΘ
        · intro j
          simpa using hθ j
      · rw [fl_exactMulDotProduct, hfold, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]

/-- Exact-product dot product forward error with radius `gamma (n-1)`. -/
theorem exactMulDotProduct_error_bound (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) (hγ : gammaValid fp (n - 1)) :
    |fl_exactMulDotProduct fp n x y - ∑ i : Fin n, x i * y i| ≤
      gamma fp (n - 1) * ∑ i : Fin n, |x i| * |y i| := by
  obtain ⟨η, hη, hfl⟩ := exactMulDotProduct_backward_error fp n x y hγ
  have herr :
      fl_exactMulDotProduct fp n x y - ∑ i : Fin n, x i * y i =
        ∑ i : Fin n, x i * y i * η i := by
    rw [hfl, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [herr]
  calc
    |∑ i : Fin n, x i * y i * η i|
        ≤ ∑ i : Fin n, |x i * y i * η i| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin n, |x i| * |y i| * |η i| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_mul]
    _ ≤ ∑ i : Fin n, |x i| * |y i| * gamma fp (n - 1) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hη i)
            (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp (n - 1) * ∑ i : Fin n, |x i| * |y i| := by
          rw [← Finset.sum_mul, mul_comm]

/-- Extended-precision dot product with exact products in the inner precision. -/
noncomputable def fl_extendedExactMulDotProduct (inner : FPModel)
    (finalRound : ℝ → ℝ) (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  finalRound (fl_exactMulDotProduct inner n x y)

/-- Exact-product extended-precision dot product compared with the same final
rounding factor applied to the exact inner product. -/
theorem extendedExactMulDotProduct_error_from_rounded_exact (inner : FPModel)
    {u : ℝ} {finalRound : ℝ → ℝ} (n : ℕ) (x y : Fin n → ℝ)
    (hround : FinalRoundingModel u finalRound)
    (hγ : gammaValid inner (n - 1)) :
    ∃ δ : ℝ,
      |δ| ≤ u ∧
      |fl_extendedExactMulDotProduct inner finalRound n x y -
          (∑ i : Fin n, x i * y i) * (1 + δ)| ≤
        (1 + u) * (gamma inner (n - 1) *
          ∑ i : Fin n, |x i| * |y i|) := by
  let exact := ∑ i : Fin n, x i * y i
  let B := gamma inner (n - 1) * ∑ i : Fin n, |x i| * |y i|
  have hinner :
      |fl_exactMulDotProduct inner n x y - exact| ≤ B := by
    simpa [exact, B] using exactMulDotProduct_error_bound inner n x y hγ
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| * |y i| := by
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hB : 0 ≤ B :=
    mul_nonneg (gamma_nonneg inner hγ) hsum_nonneg
  simpa [fl_extendedExactMulDotProduct, exact, B] using
    finalRound_error_from_rounded_exact hround hinner hB

/-- Absolute-error bound for the exact-product extended-precision route.

Compared with `extendedDotProduct_error_bound`, the inner term uses
`gamma inner (n - 1)` because the products themselves are exact and only the
`n - 1` extended additions are rounded. -/
theorem extendedExactMulDotProduct_error_bound (inner : FPModel)
    {u : ℝ} {finalRound : ℝ → ℝ} (n : ℕ) (x y : Fin n → ℝ)
    (hround : FinalRoundingModel u finalRound)
    (hγ : gammaValid inner (n - 1)) :
    |fl_extendedExactMulDotProduct inner finalRound n x y -
        ∑ i : Fin n, x i * y i| ≤
      u * |∑ i : Fin n, x i * y i| +
        (1 + u) * (gamma inner (n - 1) *
          ∑ i : Fin n, |x i| * |y i|) := by
  let exact := ∑ i : Fin n, x i * y i
  let B := gamma inner (n - 1) * ∑ i : Fin n, |x i| * |y i|
  have hinner :
      |fl_exactMulDotProduct inner n x y - exact| ≤ B := by
    simpa [exact, B] using exactMulDotProduct_error_bound inner n x y hγ
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |x i| * |y i| := by
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hB : 0 ≤ B :=
    mul_nonneg (gamma_nonneg inner hγ) hsum_nonneg
  simpa [fl_extendedExactMulDotProduct, exact, B] using
    finalRound_error_bound hround hinner hB

end NumStability
