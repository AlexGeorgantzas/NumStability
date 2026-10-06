import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.ErrorAnalysis.BlockLDLT
import NumStability.Algorithms.LinearSystems.SymmetricIndefinite.Pivoting.Tridiagonal
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter11 Theorem07 TridiagonalTwoByTwoResidual Basic

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.CholeskyIndefinite` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Printed-budget handoff for the single trailing block in an accepted
tridiagonal `2 × 2` pivot step.  Once the local scalar budget is bounded by
`c_bound * u * Amax`, the perturbation has the componentwise shape used in
Theorem 11.7. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔS : Fin 1 → Fin 1 → ℝ,
      (∀ i j : Fin 1, |ΔS i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin 1,
        fp.fl_sub b
            (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
          = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) + ΔS i j) := by
  obtain ⟨ΔS, hΔS, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_bound fp
      σ a11 a21 a22 b c Amax κ hchoice hσa11 hσa22 hAmax hκ hb hc
      hratio hval
  refine ⟨ΔS, ?_, hstep⟩
  intro i j
  exact le_trans (hΔS i j) hbudget

/-- First-stage embedding of the printed `2 × 2` tridiagonal trailing scalar
backward error into the ambient `3 × 3` tridiagonal block-LDLᵀ step.  The
perturbation is zero outside the single trailing entry, so this is the local
handoff needed before iterating the tridiagonal recursion. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_three
    (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin 3 → Fin 3 → ℝ,
      (∀ i j : Fin 3, |ΔA i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin 3,
        i ≠ (⟨2, by decide⟩ : Fin 3) ∨
          j ≠ (⟨2, by decide⟩ : Fin 3) →
        ΔA i j = 0) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (⟨2, by decide⟩ : Fin 3) (⟨2, by decide⟩ : Fin 3) := by
  obtain ⟨ΔS, hΔS, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  let tail : Fin 3 := ⟨2, by decide⟩
  let zero : Fin 1 := ⟨0, by decide⟩
  let ΔA : Fin 3 → Fin 3 → ℝ :=
    fun i j => if i = tail ∧ j = tail then ΔS zero zero else 0
  refine ⟨ΔA, ?_, ?_, ?_⟩
  · intro i j
    have hzero_bound : |(0 : ℝ)| ≤ c_bound * u * Amax := by
      simpa using (abs_nonneg (ΔS zero zero)).trans (hΔS zero zero)
    by_cases htail : i = tail ∧ j = tail
    · simpa [ΔA, htail] using hΔS zero zero
    · simpa [ΔA, htail] using hzero_bound
  · intro i j houtside
    have htail : ¬(i = tail ∧ j = tail) := by
      intro htail
      rcases houtside with hi | hj
      · exact hi htail.1
      · exact hj htail.2
    simp [ΔA, htail]
  · simpa [ΔA, tail, zero] using hstep zero zero

/-- Printed-coefficient version of the zero perturbation package. -/
theorem tridiagonalLeadingBlockSupport_zero_printed_bound
    (m offset : ℕ) (c u Amax : ℝ) (hβ : 0 ≤ c * u * Amax) :
    ∃ Z : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |Z i j| ≤ c * u * Amax) ∧
      TridiagonalLeadingBlockSupport m offset Z ∧
      (∀ i j : Fin m, Z i j = 0) :=
  tridiagonalLeadingBlockSupport_zero_bound m offset (c * u * Amax) hβ

/-- Printed-coefficient version of the zero-prefix support add/bound combiner:
two perturbations bounded by `cE * u * Amax` and `cF * u * Amax` combine with
coefficient `cE + cF`. -/
theorem tridiagonalLeadingBlockSupport_add_bound_printed
    (m offset : ℕ) (E F : Fin m → Fin m → ℝ) (cE cF u Amax : ℝ)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ cE * u * Amax)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ cF * u * Amax)
    (hEsupp : TridiagonalLeadingBlockSupport m offset E)
    (hFsupp : TridiagonalLeadingBlockSupport m offset F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ (cE + cF) * u * Amax) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) := by
  obtain ⟨G, hG, hGsupp, hsum⟩ :=
    tridiagonalLeadingBlockSupport_add_bound m offset E F
      (cE * u * Amax) (cF * u * Amax) hEbound hFbound hEsupp hFsupp
  refine ⟨G, ?_, hGsupp, hsum⟩
  intro i j
  calc
    |G i j| ≤ cE * u * Amax + cF * u * Amax := hG i j
    _ = (cE + cF) * u * Amax := by ring

/-- Printed-coefficient mixed-depth version of the zero-prefix support
add/bound combiner. -/
theorem tridiagonalLeadingBlockSupport_add_bound_printed_of_le_offset
    (m offset offsetE offsetF : ℕ) (E F : Fin m → Fin m → ℝ)
    (cE cF u Amax : ℝ)
    (hoffE : offset ≤ offsetE) (hoffF : offset ≤ offsetF)
    (hEbound : ∀ i j : Fin m, |E i j| ≤ cE * u * Amax)
    (hFbound : ∀ i j : Fin m, |F i j| ≤ cF * u * Amax)
    (hEsupp : TridiagonalLeadingBlockSupport m offsetE E)
    (hFsupp : TridiagonalLeadingBlockSupport m offsetF F) :
    ∃ G : Fin m → Fin m → ℝ,
      (∀ i j : Fin m, |G i j| ≤ (cE + cF) * u * Amax) ∧
      TridiagonalLeadingBlockSupport m offset G ∧
      (∀ i j : Fin m, G i j = E i j + F i j) :=
  tridiagonalLeadingBlockSupport_add_bound_printed m offset E F cE cF u Amax
    hEbound hFbound
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetE E
      hoffE hEsupp)
    (tridiagonalLeadingBlockSupport_of_le_offset m offset offsetF F
      hoffF hFsupp)

/-- Dimension-generic first-stage embedding of the printed `2 × 2`
tridiagonal trailing scalar backward error.  In a local block of size `n+3`,
the first accepted `2 × 2` pivot only touches the first trailing scalar of a
tridiagonal matrix; the ambient perturbation is therefore zero at every entry
except `tridiagonalTwoByTwoFirstTrailingIndex n`. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax) ∧
      (∀ i j : Fin (n + 3),
        i ≠ tridiagonalTwoByTwoFirstTrailingIndex n ∨
          j ≠ tridiagonalTwoByTwoFirstTrailingIndex n →
        ΔA i j = 0) ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔS, hΔS, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  let tail : Fin (n + 3) := tridiagonalTwoByTwoFirstTrailingIndex n
  let zero : Fin 1 := ⟨0, by decide⟩
  let ΔA : Fin (n + 3) → Fin (n + 3) → ℝ :=
    fun i j => if i = tail ∧ j = tail then ΔS zero zero else 0
  refine ⟨ΔA, ?_, ?_, ?_⟩
  · intro i j
    have hzero_bound : |(0 : ℝ)| ≤ c_bound * u * Amax := by
      simpa using (abs_nonneg (ΔS zero zero)).trans (hΔS zero zero)
    by_cases htail : i = tail ∧ j = tail
    · simpa [ΔA, htail] using hΔS zero zero
    · simpa [ΔA, htail] using hzero_bound
  · intro i j houtside
    have htail : ¬(i = tail ∧ j = tail) := by
      intro htail
      rcases houtside with hi | hj
      · exact hi htail.1
      · exact hj htail.2
    simp [ΔA, htail]
  · simpa [ΔA, tail, zero] using hstep zero zero

/-- Dimension-generic first-stage embedding of the printed `2 × 2`
tridiagonal trailing scalar backward error, with the support property needed to
compose with a recursive trailing-subproblem hypothesis. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hzero, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed n fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  refine ⟨ΔA, hΔA, ?_, hstep⟩
  intro i j hlead
  apply hzero
  rcases hlead with hi | hj
  · exact Or.inl (ne_tridiagonalTwoByTwoFirstTrailingIndex_of_val_lt_two hi)
  · exact Or.inr (ne_tridiagonalTwoByTwoFirstTrailingIndex_of_val_lt_two hj)

/-- Accumulate the local printed-budget residual from a leading `2 × 2`
tridiagonal pivot with an already-supported recursive trailing perturbation.
This is the local algebraic handoff used when iterating the tridiagonal
block-LDLᵀ recursion. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound u βR : ℝ)
    (ΔR : Fin (n + 3) → Fin (n + 3) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRbound : ∀ i j : Fin (n + 3), |ΔR i j| ≤ βR)
    (hRsupp : TridiagonalTwoByTwoTrailingBlockSupport n ΔR) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ c_bound * u * Amax + βR) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔR (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔS, hΔS, hSsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_embed_support n fp
      σ a11 a21 a22 b c Amax κ c_bound u hchoice hσa11 hσa22 hAmax hκ
      hb hc hratio hbudget hval
  obtain ⟨ΔA, hΔA, hAsupp, hsum⟩ :=
    tridiagonalTwoByTwoTrailingBlockSupport_add_bound n ΔS ΔR
      (c_bound * u * Amax) βR hΔS hRbound hSsupp hRsupp
  refine ⟨ΔA, hΔA, hAsupp, ?_⟩
  rw [hstep, hsum (tridiagonalTwoByTwoFirstTrailingIndex n)
    (tridiagonalTwoByTwoFirstTrailingIndex n)]
  ring

/-- Printed-coefficient form of the local recursive accumulation step: if the
recursive trailing perturbation is already bounded by `c_rec * u * Amax`, then
the accumulated perturbation is bounded by `(c_bound + c_rec) * u * Amax`. -/
theorem fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound c_rec u : ℝ)
    (ΔR : Fin (n + 3) → Fin (n + 3) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRbound : ∀ i j : Fin (n + 3), |ΔR i j| ≤ c_rec * u * Amax)
    (hRsupp : TridiagonalTwoByTwoTrailingBlockSupport n ΔR) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔR (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n)
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate n fp
      σ a11 a21 a22 b c Amax κ c_bound u (c_rec * u * Amax) ΔR
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval hRbound hRsupp
  refine ⟨ΔA, ?_, hAsupp, hstep⟩
  intro i j
  calc
    |ΔA i j| ≤ c_bound * u * Amax + c_rec * u * Amax := hΔA i j
    _ = (c_bound + c_rec) * u * Amax := by ring

/-- Recursive-subproblem form of the printed accumulation step.  A perturbation
proved on the trailing subproblem `Fin (n+1)` is first lifted into the ambient
`Fin (n+3)` block, then accumulated with the local `2 × 2` tridiagonal rounded
Schur residual. -/
theorem fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound c_rec u : ℝ)
    (ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRtail_bound : ∀ i j : Fin (n + 1),
      |ΔRtail i j| ≤ c_rec * u * Amax) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔRtail 0 0
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔR, hRbound, hRsupp, hRembed⟩ :=
    tridiagonalTwoByTwoLiftTrailingPerturbation_bound_support n ΔRtail
      (c_rec * u * Amax) hRtail_bound
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_one_stage_printed_bound_accumulate_printed
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u ΔR hchoice
      hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval hRbound hRsupp
  refine ⟨ΔA, hΔA, hAsupp, ?_⟩
  have htail :
      ΔR (tridiagonalTwoByTwoFirstTrailingIndex n)
          (tridiagonalTwoByTwoFirstTrailingIndex n) = ΔRtail 0 0 := by
    simpa [tridiagonalTwoByTwoTrailingSubproblemIndex_zero] using
      hRembed 0 0
  simpa [htail] using hstep

/-- Recursive-residual form of the printed accumulation step.  If the recursive
trailing subproblem already has a scalar backward-error certificate
`tail_fl = tail_exact + ΔRtail 0 0`, the leading `2 × 2` tridiagonal step
absorbs that certificate into one ambient perturbation with coefficient
`c_bound + c_rec`. -/
theorem fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate
    (n : ℕ) (fp : FPModel)
    (σ a11 a21 a22 b c Amax κ c_bound c_rec u tail_fl tail_exact : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hrec : ∃ ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i j : Fin (n + 1), |ΔRtail i j| ≤ c_rec * u * Amax) ∧
      tail_fl = tail_exact + ΔRtail 0 0) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalTwoByTwoTrailingBlockSupport n ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          tail_fl
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          tail_exact +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔRtail, hRtail_bound, htail⟩ := hrec
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u ΔRtail
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval
      hRtail_bound
  refine ⟨ΔA, hΔA, hAsupp, ?_⟩
  rw [htail]
  calc
    fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          (tail_exact + ΔRtail 0 0)
        =
          (fp.fl_sub b
              (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
            ΔRtail 0 0) + tail_exact := by
      ring
    _ =
          ((b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
            ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
              (tridiagonalTwoByTwoFirstTrailingIndex n)) + tail_exact := by
      rw [hstep]
    _ =
          (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          tail_exact +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
      ring

/-- Recursive-subproblem printed accumulation with the generic zero-prefix
support predicate.  This is the same algebraic handoff as
`fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate`, but
with support stated as `TridiagonalLeadingBlockSupport ... 2` for recursive
assembly. -/
theorem fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate_leadingBlockSupport
    (n : ℕ) (fp : FPModel) (σ a11 a21 a22 b c Amax κ c_bound c_rec u : ℝ)
    (ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hRtail_bound : ∀ i j : Fin (n + 1),
      |ΔRtail i j| ≤ c_rec * u * Amax) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalLeadingBlockSupport (n + 3) 2 ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          ΔRtail 0 0
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_subproblem_printed_bound_accumulate
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u ΔRtail
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval
      hRtail_bound
  refine ⟨ΔA, hΔA, ?_, hstep⟩
  exact (tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport
    n ΔA).1 hAsupp

/-- Recursive-residual printed accumulation with the generic zero-prefix
support predicate. -/
theorem fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate_leadingBlockSupport
    (n : ℕ) (fp : FPModel)
    (σ a11 a21 a22 b c Amax κ c_bound c_rec u tail_fl tail_exact : ℝ)
    (hchoice : BunchTridiagonalPivotChoice σ a11 a21 PivotSize.two)
    (hσa11 : |a11| ≤ σ) (hσa22 : |a22| ≤ σ)
    (hAmax : 0 ≤ Amax) (hκ : 0 ≤ κ)
    (hb : |b| ≤ Amax) (hc : |c| ≤ Amax)
    (hratio : σ / ((1 - bunchTridiagonalAlpha) * a21 ^ 2) ≤ κ)
    (hbudget :
      gamma fp 3 * (Amax + Amax * κ * Amax) ≤ c_bound * u * Amax)
    (hval : gammaValid fp 3)
    (hrec : ∃ ΔRtail : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i j : Fin (n + 1), |ΔRtail i j| ≤ c_rec * u * Amax) ∧
      tail_fl = tail_exact + ΔRtail 0 0) :
    ∃ ΔA : Fin (n + 3) → Fin (n + 3) → ℝ,
      (∀ i j : Fin (n + 3), |ΔA i j| ≤ (c_bound + c_rec) * u * Amax) ∧
      TridiagonalLeadingBlockSupport (n + 3) 2 ΔA ∧
      fp.fl_sub b
          (fp.fl_mul (fp.fl_mul c (a11 / (a11 * a22 - a21 ^ 2))) c) +
          tail_fl
        = (b - c * (a11 / (a11 * a22 - a21 ^ 2)) * c) +
          tail_exact +
          ΔA (tridiagonalTwoByTwoFirstTrailingIndex n)
            (tridiagonalTwoByTwoFirstTrailingIndex n) := by
  obtain ⟨ΔA, hΔA, hAsupp, hstep⟩ :=
    fl_tridiagonal_twoByTwo_trailing_recursive_residual_printed_bound_accumulate
      n fp σ a11 a21 a22 b c Amax κ c_bound c_rec u tail_fl tail_exact
      hchoice hσa11 hσa22 hAmax hκ hb hc hratio hbudget hval hrec
  refine ⟨ΔA, hΔA, ?_, hstep⟩
  exact (tridiagonalTwoByTwoTrailingBlockSupport_iff_leadingBlockSupport
    n ΔA).1 hAsupp

end NumStability
