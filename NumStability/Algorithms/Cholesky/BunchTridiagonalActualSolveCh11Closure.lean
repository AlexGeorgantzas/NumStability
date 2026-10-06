/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Theorem 11.7: actual Algorithm 11.6 block solves

This module removes the abstract equation-(11.5) middle-solve input from the
tridiagonal Bunch path.  At an accepted `2 × 2` pivot, Algorithm 11.6 makes the
off-diagonal entry the largest entry in the first pivot column.  Swapping the
two equations therefore gives the actual two-step GEPP order.  The printed
pivot inequality and the fixed-scale stage bound control the only elimination
fill term, so the rounded `2 × 2` kernel has a componentwise perturbation bounded
by `36 u |E|` under `9u ≤ 1/2`.

The stage result is then folded over a `PivotSchedule`, producing the concrete
`MixedMiddleSolveHigham115Blocks` witness for every right-hand side.  The only
run condition left is that each computed second GEPP pivot is nonzero, exactly
the usual no-breakdown domain condition for a floating-point solve.
-/
import NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthInvariantCh11Closure
import NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure
import NumStability.Algorithms.Sylvester.Higham16QuasiRoundedSolve

open scoped BigOperators

namespace NumStability.Ch11Closure.BunchTriActual

open NumStability
open NumStability.Wave15
open NumStability.Ch11Closure
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.Solve
open NumStability.Ch11Closure.TriGrowthInv

/-- The actual rounded GEPP solve for an accepted symmetric `2 × 2` Bunch
pivot.  The equations are swapped before calling the two-step rounded kernel,
so the off-diagonal pivot `A₁₀` is used first. -/
noncomputable def flBunchTwoByTwoSolve (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (z : Fin (m + 2) → ℝ) : Fin 2 → ℝ :=
  let xy := fl_solve2x2 fp
    (A (oneIdx m) 0) (A (oneIdx m) (oneIdx m))
    (A 0 0) (A 0 (oneIdx m)) (z (oneIdx m)) (z 0)
  fun p => Fin.cases xy.1 (fun _ => xy.2) p

@[simp] theorem flBunchTwoByTwoSolve_zero (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (z : Fin (m + 2) → ℝ) :
    flBunchTwoByTwoSolve fp A z 0 =
      (fl_solve2x2 fp
        (A (oneIdx m) 0) (A (oneIdx m) (oneIdx m))
        (A 0 0) (A 0 (oneIdx m)) (z (oneIdx m)) (z 0)).1 := rfl

@[simp] theorem flBunchTwoByTwoSolve_one (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) (z : Fin (m + 2) → ℝ) :
    flBunchTwoByTwoSolve fp A z 1 =
      (fl_solve2x2 fp
        (A (oneIdx m) 0) (A (oneIdx m) (oneIdx m))
        (A 0 0) (A 0 (oneIdx m)) (z (oneIdx m)) (z 0)).2 := rfl

/-- The computed second pivot of the swapped, hence partially pivoted, `2 × 2`
solve used by `flBunchTwoByTwoSolve`. -/
noncomputable def flBunchTwoByTwoSecondPivot (fp : FPModel) {m : ℕ}
    (A : Fin (m + 2) → Fin (m + 2) → ℝ) : ℝ :=
  flSolve2x2SecondPivot fp
    (A (oneIdx m) 0) (A (oneIdx m) (oneIdx m))
    (A 0 0) (A 0 (oneIdx m))

/-- Higham (11.5), produced by an actual rounded GEPP solve of an Algorithm
11.6 `2 × 2` pivot.  The accepted-pivot inequality and `α τ < M0` imply
`|A₀₀| |A₁₁| ≤ |A₁₀|²`, the growth certificate needed by the two-step kernel.
The returned vector is `flBunchTwoByTwoSolve`, not an existentially postulated
solution. -/
theorem flBunchTwoByTwoSolve_higham115 (fp : FPModel)
    (hval9 : gammaValid fp 9) (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    {m : ℕ} (A : Fin (m + 2) → Fin (m + 2) → ℝ)
    (z : Fin (m + 2) → ℝ) (M0 tau : ℝ)
    (hM0 : 0 < M0)
    (hslack : bunchTridiagonalAlpha * tau < M0)
    (hA : IsSymTridiagonal (m + 2) A)
    (hchoice : BunchTridiagonalPivotChoice M0 (A 0 0)
      (A (oneIdx m) 0) PivotSize.two)
    (hdiag : |A (oneIdx m) (oneIdx m)| ≤ tau)
    (hsecond : flBunchTwoByTwoSecondPivot fp A ≠ 0) :
    ∃ ΔE : Fin 2 → Fin 2 → ℝ,
      higham11_5_twoByTwoPivotSolveStable fp.u 36 (leadingTwoBlock m A) ΔE ∧
      ∀ p : Fin 2,
        ∑ q : Fin 2, (leadingTwoBlock m A p q + ΔE p q) *
          flBunchTwoByTwoSolve fp A z q = z (embedTwo m p) := by
  have hsym : A 0 (oneIdx m) = A (oneIdx m) 0 := hA.1 _ _
  have hpivot : A (oneIdx m) 0 ≠ 0 :=
    bunch_tridiagonal_pivot_choice_two_a21_ne_zero_of_sigma_nonneg
      M0 (A 0 0) (A (oneIdx m) 0) hchoice hM0.le
  have htest : M0 * |A 0 0| <
      bunchTridiagonalAlpha * (A (oneIdx m) 0) ^ 2 :=
    bunch_tridiagonal_pivot_choice_two_threshold M0 (A 0 0)
      (A (oneIdx m) 0) hchoice
  have hfill : |A 0 0| * |A (oneIdx m) (oneIdx m)| ≤
      |A (oneIdx m) 0| * |A 0 (oneIdx m)| := by
    have hα : 0 < bunchTridiagonalAlpha := bunch_tridiagonal_alpha_pos
    have h1 : bunchTridiagonalAlpha * |A 0 0| *
        |A (oneIdx m) (oneIdx m)| ≤
        bunchTridiagonalAlpha * |A 0 0| * tau :=
      mul_le_mul_of_nonneg_left hdiag
        (mul_nonneg hα.le (abs_nonneg _))
    have h2 : bunchTridiagonalAlpha * |A 0 0| * tau ≤
        M0 * |A 0 0| := by
      calc
        bunchTridiagonalAlpha * |A 0 0| * tau =
            (bunchTridiagonalAlpha * tau) * |A 0 0| := by ring
        _ ≤ M0 * |A 0 0| :=
          mul_le_mul_of_nonneg_right (le_of_lt hslack) (abs_nonneg _)
    have h3 : bunchTridiagonalAlpha *
        (|A 0 0| * |A (oneIdx m) (oneIdx m)|) ≤
        bunchTridiagonalAlpha * (|A (oneIdx m) 0| ^ 2) := by
      calc
        bunchTridiagonalAlpha *
            (|A 0 0| * |A (oneIdx m) (oneIdx m)|) =
            bunchTridiagonalAlpha * |A 0 0| *
              |A (oneIdx m) (oneIdx m)| := by ring
        _ ≤ bunchTridiagonalAlpha * |A 0 0| * tau := h1
        _ ≤ M0 * |A 0 0| := h2
        _ ≤ bunchTridiagonalAlpha * (A (oneIdx m) 0) ^ 2 := le_of_lt htest
        _ = bunchTridiagonalAlpha * (|A (oneIdx m) 0| ^ 2) := by rw [sq_abs]
    have hcancel := le_of_mul_le_mul_left h3 hα
    rw [hsym]
    simpa [pow_two] using hcancel
  obtain ⟨Δ10, Δ11, Δ00, Δ01, hΔ10, hΔ11, hΔ00, hΔ01, hrow1, hrow0⟩ :=
    fl_solve2x2_backward_error_componentwise fp
      (A (oneIdx m) 0) (A (oneIdx m) (oneIdx m))
      (A 0 0) (A 0 (oneIdx m)) (z (oneIdx m)) (z 0) 1
      hpivot hsecond (by norm_num) (by simpa using hfill) hval9
  let ΔE : Fin 2 → Fin 2 → ℝ := fun i j =>
    Fin.cases (Fin.cases Δ00 (fun _ => Δ01) j)
      (fun _ => Fin.cases Δ10 (fun _ => Δ11) j) i
  have hgamma : (1 + (1 : ℝ)) * gamma fp 9 ≤ 36 * fp.u := by
    have hg := gamma_le_two_mul_n_u_of_nu_le_half fp 9 hsmall9
    norm_num at hg ⊢
    linarith
  refine ⟨ΔE, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact le_trans hΔ00
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
    · exact le_trans hΔ01
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
    · exact le_trans hΔ10
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
    · exact le_trans hΔ11
        (mul_le_mul_of_nonneg_right hgamma (abs_nonneg _))
  · intro p
    fin_cases p
    · rw [Fin.sum_univ_two]
      simpa [ΔE, leadingTwoBlock, flBunchTwoByTwoSolve] using hrow0
    · rw [Fin.sum_univ_two]
      simpa [ΔE, leadingTwoBlock, flBunchTwoByTwoSolve] using hrow1

/-- No-breakdown condition for the actual schedule-local middle solve.  Only
accepted `2 × 2` stages have a clause, requiring the computed second GEPP pivot
to be nonzero. -/
def BunchMiddleSolveNoBreakdown (fp : FPModel) :
    {n : ℕ} → PivotSchedule n → (Fin n → Fin n → ℝ) → Prop
  | 0, .nil, _ => True
  | n + 1, .consOne s, A =>
      BunchMiddleSolveNoBreakdown fp s (flSchurCompl n fp A)
  | n + 2, .consTwo s, A =>
      flBunchTwoByTwoSecondPivot fp A ≠ 0 ∧
        BunchMiddleSolveNoBreakdown fp s (flSchurCompl2 n fp A)

/-- Fold the actual scalar/GEPP block solves over an Algorithm 11.6 run.  This
constructs the schedule-local Higham-(11.5) data for every right-hand side;
there is no residual or solution hypothesis. -/
theorem mixedMiddleSolveHigham115Blocks_of_bunch_actual
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    (M0 tau : ℝ) (hM0 : 0 < M0) (htau : 0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0) :
    ∀ {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ)
      (z : Fin n → ℝ),
      TriGrowthBounded fp M0 tau s A →
      BunchMiddleSolveNoBreakdown fp s A →
      MixedMiddleSolveHigham115Blocks fp 36 s A z
  | 0, .nil, A, z, _, _ => True.intro
  | n + 1, .consOne s, A, z, hdata, hnb => by
      rw [TriGrowthBounded_consOne] at hdata
      refine ⟨hdata.2.1, ?_⟩
      exact mixedMiddleSolveHigham115Blocks_of_bunch_actual fp hval9 hsmall9
        M0 tau hM0 htau hslack s (flSchurCompl n fp A) (fun i => z i.succ)
        hdata.2.2.2.2 hnb
  | m + 2, .consTwo s, A, z, hdata, hnb => by
      rw [TriGrowthBounded_consTwo] at hdata
      rcases hdata with ⟨hA, hchoice, hoff, htail⟩
      rcases hnb with ⟨hsecond, hnbTail⟩
      constructor
      · refine ⟨flBunchTwoByTwoSolve fp A z, ?_⟩
        exact flBunchTwoByTwoSolve_higham115 fp hval9 hsmall9 A z M0 tau
          hM0 hslack hA hchoice
          (hoff (oneIdx m) (oneIdx m) (Or.inl (by simp [oneIdx]))) hsecond
      · exact mixedMiddleSolveHigham115Blocks_of_bunch_actual fp hval9 hsmall9
          M0 tau hM0 htau hslack s (flSchurCompl2 m fp A)
          (fun i => z i.succ.succ) htail hnbTail

/-- The actual schedule-local block solver produces the global named middle
solve with `|ΔD| ≤ 36u |D̂|`. -/
theorem flMixedD_solve_of_bunch_actual
    (fp : FPModel) (hval9 : gammaValid fp 9)
    (hsmall9 : (9 : ℝ) * fp.u ≤ 1 / 2)
    (M0 tau : ℝ) (hM0 : 0 < M0) (htau : 0 ≤ tau)
    (hslack : bunchTridiagonalAlpha * tau < M0)
    {n : ℕ} (s : PivotSchedule n) (A : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hdata : TriGrowthBounded fp M0 tau s A)
    (hnb : BunchMiddleSolveNoBreakdown fp s A) :
    ∃ (w : Fin n → ℝ) (ΔD : Fin n → Fin n → ℝ),
      (∀ i j : Fin n, |ΔD i j| ≤ (36 * fp.u) * |flMixedD fp s A i j|) ∧
      (∀ p : Fin n, ∑ q : Fin n,
        (flMixedD fp s A p q + ΔD p q) * w q = z p) := by
  have hval1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hval9
  have huHalf : (1 : ℝ) * fp.u ≤ 1 / 2 := by
    have hu := fp.u_nonneg
    nlinarith [hsmall9]
  have hgamma1 : gamma fp 1 ≤ 36 * fp.u := by
    have h := gamma_le_two_mul_n_u_of_nu_le_half fp 1 (by simpa using huHalf)
    calc
      gamma fp 1 ≤ 2 * ((1 : ℝ) * fp.u) := by simpa using h
      _ ≤ 36 * fp.u := by nlinarith [fp.u_nonneg]
  exact flMixedD_solve_of_higham115_blocks fp 36 (36 * fp.u) hval1
    hgamma1 (le_refl _) s A z
    (mixedMiddleSolveHigham115Blocks_of_bunch_actual fp hval9 hsmall9
      M0 tau hM0 htau hslack s A z hdata hnb)

end NumStability.Ch11Closure.BunchTriActual
