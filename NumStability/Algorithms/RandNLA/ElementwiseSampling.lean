-- Algorithms/RandNLA/ElementwiseSampling.lean
--
-- Floating-point stability infrastructure for the element-wise sampling
-- meta-algorithm in Drineas--Mahoney's CACM RandNLA survey, Algorithm 1.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.Analysis.Summation.ErrorBounds

namespace NumStability

open scoped BigOperators

/-!
## Algorithm 1: element-wise sampling

Algorithm 1 repeatedly samples an entry `(i, j)` of a matrix `A` with
probability `pᵢⱼ` and updates the sketch entry by

`Atildeᵢⱼ := Atildeᵢⱼ + Aᵢⱼ / (s * pᵢⱼ)`.

This file formalizes the deterministic floating-point stability of one such
sampled-entry update. It also specializes the scaling to the squared-magnitude
probabilities used in Algorithm 1 of Drineas and Mahoney's CACM RandNLA
survey:

Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
https://dl.acm.org/doi/10.1145/2842602

`pᵢⱼ = Aᵢⱼ² / ∑ₖ∑ₗ Aₖₗ²`.

At the end of the file, the deterministic theorem is lifted to a probability
space: any high-probability concentration bound for the hit counter
`qᵢⱼ = hitCount samples i j` gives the corresponding high-probability
floating-point stability bound.
-/

-- ============================================================
-- Squared-magnitude probabilities
-- ============================================================

/-- Denominator for squared-magnitude sampling probabilities:
    `∑ₖ∑ₗ Aₖₗ² = ‖A‖²_F`. -/
noncomputable def sqMagProbDen {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNormSqRect A

/-- Squared-magnitude sampling probability:
    `pᵢⱼ = Aᵢⱼ² / ∑ₖ∑ₗ Aₖₗ²`. -/
noncomputable def sqMagProb {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  A i j ^ 2 / sqMagProbDen A

/-- Squared-magnitude probabilities are nonnegative when the Frobenius
    denominator is positive. -/
theorem sqMagProb_nonneg {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n) :
    0 ≤ sqMagProb A i j := by
  unfold sqMagProb
  exact div_nonneg (sq_nonneg _) (le_of_lt hden)

/-- A nonzero sampled entry has strictly positive squared-magnitude
    probability, provided the Frobenius denominator is positive. -/
theorem sqMagProb_pos_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hAij : A i j ≠ 0) :
    0 < sqMagProb A i j := by
  unfold sqMagProb
  exact div_pos (sq_pos_of_ne_zero hAij) hden

/-- A positive squared-magnitude sampling probability can only occur at a
    nonzero entry. -/
theorem entry_ne_zero_of_sqMagProb_pos {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hpos : 0 < sqMagProb A i j) :
    A i j ≠ 0 := by
  intro hzero
  unfold sqMagProb at hpos
  simp [hzero] at hpos

/-- Squared-magnitude probabilities sum to one for a nonzero matrix. -/
theorem sqMagProb_sum_eq_one {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : sqMagProbDen A ≠ 0) :
    ∑ i : Fin m, ∑ j : Fin n, sqMagProb A i j = 1 := by
  unfold sqMagProb sqMagProbDen
  simp_rw [div_eq_mul_inv]
  simp_rw [← Finset.sum_mul]
  change frobNormSqRect A * (frobNormSqRect A)⁻¹ = 1
  exact mul_inv_cancel₀ hden

/-- For a nonzero entry, its squared-magnitude probability is nonzero. -/
theorem sqMagProb_ne_zero_of_entry_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hAij : A i j ≠ 0) :
    sqMagProb A i j ≠ 0 := by
  unfold sqMagProb sqMagProbDen
  exact div_ne_zero (pow_ne_zero 2 hAij)
    (frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij)

/-- A sampled entry of an `m × n` matrix. -/
abbrev ElementwiseSample (m n : ℕ) := Fin m × Fin n

/-- A deterministic trace of `steps` sampled entries. Probability enters by
    choosing a finite probability law over such traces. -/
abbrev ElementwiseTrace (m n steps : ℕ) := Fin steps → ElementwiseSample m n

-- ============================================================
-- Exact and floating-point sampled-entry updates
-- ============================================================

/-- Exact Algorithm 1 increment using a supplied exact probability table:
    `Aᵢⱼ / (s * pᵢⱼ)`. -/
noncomputable def elementwiseIncrementWithProb {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  A i j / ((s : ℝ) * p i j)

/-- Exact scalar update using a supplied probability table. -/
noncomputable def elementwiseUpdateEntryWithProb {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  x + elementwiseIncrementWithProb s A p i j

/-- Floating-point increment using a supplied exact probability table. The
    denominator uses `p`, not necessarily `sqMagProb A`. -/
noncomputable def fl_elementwiseIncrementWithProb (fp : FPModel) {m n : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ℝ :=
  fp.fl_div (A i j) ((s : ℝ) * p i j)

/-- Floating-point scalar update using a supplied exact probability table. -/
noncomputable def fl_elementwiseUpdateEntryWithProb (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  fp.fl_add x (fl_elementwiseIncrementWithProb fp s A p i j)

/-- Exact one-sample matrix update using a supplied probability table. -/
noncomputable def elementwiseSampleUpdateWithProb {m n : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) : Fin m → Fin n → ℝ :=
  fun r c =>
    if r = i ∧ c = j then
      elementwiseUpdateEntryWithProb s A p i j (Atilde r c)
    else
      Atilde r c

/-- Floating-point one-sample matrix update using a supplied probability
    table. -/
noncomputable def fl_elementwiseSampleUpdateWithProb (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    Fin m → Fin n → ℝ :=
  fun r c =>
    if r = i ∧ c = j then
      fl_elementwiseUpdateEntryWithProb fp s A p i j (Atilde r c)
    else
      Atilde r c

/-- Exact Algorithm 1 increment for a sampled entry `(i, j)`:
    `Aᵢⱼ / (s * pᵢⱼ)`. -/
noncomputable def elementwiseIncrement {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  elementwiseIncrementWithProb s A (sqMagProb A) i j

/-- Exact scalar update of the sampled sketch entry. -/
noncomputable def elementwiseUpdateEntry {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  elementwiseUpdateEntryWithProb s A (sqMagProb A) i j x

/-- Floating-point Algorithm 1 increment: compute the rescaling division in
    floating point. -/
noncomputable def fl_elementwiseIncrement (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  fl_elementwiseIncrementWithProb fp s A (sqMagProb A) i j

/-- Floating-point scalar update of the sampled sketch entry. -/
noncomputable def fl_elementwiseUpdateEntry (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  fl_elementwiseUpdateEntryWithProb fp s A (sqMagProb A) i j x

/-- Exact one-sample matrix update for Algorithm 1. Only the sampled entry is
    changed. -/
noncomputable def elementwiseSampleUpdate {m n : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    Fin m → Fin n → ℝ :=
  elementwiseSampleUpdateWithProb s A Atilde (sqMagProb A) i j

/-- Floating-point one-sample matrix update for Algorithm 1. Only the sampled
    entry is changed. -/
noncomputable def fl_elementwiseSampleUpdate (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    Fin m → Fin n → ℝ :=
  fl_elementwiseSampleUpdateWithProb fp s A Atilde (sqMagProb A) i j

-- ============================================================
-- Exact simplification for pᵢⱼ = Aᵢⱼ² / ‖A‖²_F
-- ============================================================

/-- The sampled-entry denominator `s * pᵢⱼ` is nonzero whenever `s > 0` and
    the sampled entry is nonzero. Under squared-magnitude sampling, zero
    entries have probability zero, so a sampled entry should satisfy this
    hypothesis. -/
theorem elementwiseSampleDenom_ne_zero {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) :
    (s : ℝ) * sqMagProb A i j ≠ 0 :=
  mul_ne_zero hs (sqMagProb_ne_zero_of_entry_ne_zero A i j hAij)

/-- With squared-magnitude probabilities, the exact Algorithm 1 increment
    simplifies to `‖A‖²_F / (s * Aᵢⱼ)` for a nonzero sampled entry. -/
theorem elementwiseIncrement_sqMag_eq {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) :
    elementwiseIncrement s A i j =
      frobNormSqRect A / ((s : ℝ) * A i j) := by
  have hF : frobNormSqRect A ≠ 0 :=
    frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij
  unfold elementwiseIncrement elementwiseIncrementWithProb sqMagProb sqMagProbDen
  field_simp [hs, hAij, hF]

-- ============================================================
-- Stability of the sampled-entry update
-- ============================================================

/-- Generic forward-error bound for the floating-point update
    `fl_add x (fl_div a denom)`.

    If `t = a / denom`, then the computed update differs from the exact
    update `x + t` by at most

    `u |x+t| + u (1+u) |t|`.

    This is the local arithmetic kernel used by Algorithm 1. -/
theorem fl_add_div_update_error_bound (fp : FPModel)
    (x a denom : ℝ) (hdenom : denom ≠ 0) :
    |fp.fl_add x (fp.fl_div a denom) - (x + a / denom)| ≤
      |x + a / denom| * fp.u + |a / denom| * fp.u * (1 + fp.u) := by
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div a denom hdenom
  obtain ⟨δa, hδa, hadd⟩ := fp.model_add x (fp.fl_div a denom)
  let t : ℝ := a / denom
  have hdiv' : fp.fl_div a denom = t * (1 + δd) := by
    simpa [t] using hdiv
  have herr :
      fp.fl_add x (fp.fl_div a denom) - (x + t) =
        (x + t) * δa + t * δd * (1 + δa) := by
    rw [hadd, hdiv']
    ring
  have hδa_abs : |1 + δa| ≤ 1 + fp.u := by
    calc |1 + δa|
        ≤ |(1 : ℝ)| + |δa| := abs_add_le _ _
      _ ≤ 1 + fp.u := by
          norm_num
          exact hδa
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have h1u : 0 ≤ 1 + fp.u := by linarith
  calc |fp.fl_add x (fp.fl_div a denom) - (x + a / denom)|
      = |(x + t) * δa + t * δd * (1 + δa)| := by
          rw [herr]
      _ ≤ |(x + t) * δa| + |t * δd * (1 + δa)| := abs_add_le _ _
      _ = |x + t| * |δa| + |t| * |δd| * |1 + δa| := by
          simp only [abs_mul]
      _ ≤ |x + t| * fp.u + |t| * fp.u * (1 + fp.u) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left hδa (abs_nonneg _)
          · have hfirst : |t| * |δd| ≤ |t| * fp.u :=
              mul_le_mul_of_nonneg_left hδd (abs_nonneg _)
            calc |t| * |δd| * |1 + δa|
                ≤ |t| * fp.u * |1 + δa| :=
                    mul_le_mul_of_nonneg_right hfirst (abs_nonneg _)
              _ ≤ |t| * fp.u * (1 + fp.u) :=
                    mul_le_mul_of_nonneg_left hδa_abs
                      (mul_nonneg (abs_nonneg _) hu)
      _ = |x + a / denom| * fp.u +
          |a / denom| * fp.u * (1 + fp.u) := by
          simp [t]

/-- A supplied positive probability and a nonzero sample count give a nonzero
    rescaling denominator. -/
theorem elementwiseSampleDenomWithProb_ne_zero {m n : ℕ} (s : ℕ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hpij : p i j ≠ 0) :
    (s : ℝ) * p i j ≠ 0 :=
  mul_ne_zero hs hpij

/-- A positive supplied probability gives a nonzero rescaling denominator. -/
theorem elementwiseSampleDenomWithProb_ne_zero_of_pos {m n : ℕ} (s : ℕ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hpij : 0 < p i j) :
    (s : ℝ) * p i j ≠ 0 :=
  elementwiseSampleDenomWithProb_ne_zero s p i j hs hpij.ne'

/-- Decomposition form of the sampled-entry floating-point update when the
    algorithm uses a supplied exact probability table. -/
theorem fl_elementwiseUpdateEntryWithProb_decomp (fp : FPModel) {m n : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ)
    (hdenom : (s : ℝ) * p i j ≠ 0) :
    ∃ δdiv δadd : ℝ,
      |δdiv| ≤ fp.u ∧
      |δadd| ≤ fp.u ∧
      fl_elementwiseUpdateEntryWithProb fp s A p i j x =
        (x + elementwiseIncrementWithProb s A p i j * (1 + δdiv)) *
          (1 + δadd) := by
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div (A i j) ((s : ℝ) * p i j) hdenom
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add x (fl_elementwiseIncrementWithProb fp s A p i j)
  refine ⟨δdiv, δadd, hδdiv, hδadd, ?_⟩
  unfold fl_elementwiseUpdateEntryWithProb
  rw [hadd]
  unfold fl_elementwiseIncrementWithProb elementwiseIncrementWithProb
  rw [hdiv]

/-- Forward-error bound for the floating-point sampled-entry update when the
    algorithm uses a supplied exact probability table. -/
theorem fl_elementwiseUpdateEntryWithProb_error_bound (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ)
    (hdenom : (s : ℝ) * p i j ≠ 0) :
    |fl_elementwiseUpdateEntryWithProb fp s A p i j x -
      elementwiseUpdateEntryWithProb s A p i j x| ≤
      |elementwiseUpdateEntryWithProb s A p i j x| * fp.u +
        |elementwiseIncrementWithProb s A p i j| * fp.u * (1 + fp.u) := by
  unfold fl_elementwiseUpdateEntryWithProb fl_elementwiseIncrementWithProb
    elementwiseUpdateEntryWithProb elementwiseIncrementWithProb
  exact fl_add_div_update_error_bound fp x (A i j) ((s : ℝ) * p i j) hdenom

/-- Entrywise forward-error bound for the one-sample matrix update with a
    supplied exact probability table. Entries other than the sampled entry
    are unchanged. -/
theorem fl_elementwiseSampleUpdateWithProb_error_bound (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hdenom : (s : ℝ) * p i j ≠ 0) (r : Fin m) (c : Fin n) :
    |fl_elementwiseSampleUpdateWithProb fp s A Atilde p i j r c -
      elementwiseSampleUpdateWithProb s A Atilde p i j r c| ≤
      if r = i ∧ c = j then
        |elementwiseUpdateEntryWithProb s A p i j (Atilde i j)| * fp.u +
          |elementwiseIncrementWithProb s A p i j| * fp.u * (1 + fp.u)
      else
        0 := by
  by_cases h : r = i ∧ c = j
  · rcases h with ⟨hr, hc⟩
    subst r
    subst c
    simp [fl_elementwiseSampleUpdateWithProb, elementwiseSampleUpdateWithProb]
    exact fl_elementwiseUpdateEntryWithProb_error_bound fp s A p i j
      (Atilde i j) hdenom
  · simp [fl_elementwiseSampleUpdateWithProb, elementwiseSampleUpdateWithProb, h]

/-- Decomposition form of the sampled-entry floating-point update. The division
    and addition each introduce one model error bounded by unit roundoff. -/
theorem fl_elementwiseUpdateEntry_decomp (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ)
    (hdenom : (s : ℝ) * sqMagProb A i j ≠ 0) :
    ∃ δdiv δadd : ℝ,
      |δdiv| ≤ fp.u ∧
      |δadd| ≤ fp.u ∧
      fl_elementwiseUpdateEntry fp s A i j x =
        (x + elementwiseIncrement s A i j * (1 + δdiv)) * (1 + δadd) := by
  simpa [fl_elementwiseUpdateEntry, fl_elementwiseIncrement,
    elementwiseIncrement] using
    fl_elementwiseUpdateEntryWithProb_decomp fp s A (sqMagProb A) i j x hdenom

/-- Forward-error bound for the floating-point sampled-entry update in
    Algorithm 1. -/
theorem fl_elementwiseUpdateEntry_error_bound (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ)
    (hdenom : (s : ℝ) * sqMagProb A i j ≠ 0) :
    |fl_elementwiseUpdateEntry fp s A i j x -
      elementwiseUpdateEntry s A i j x| ≤
      |elementwiseUpdateEntry s A i j x| * fp.u +
        |elementwiseIncrement s A i j| * fp.u * (1 + fp.u) := by
  simpa [fl_elementwiseUpdateEntry, fl_elementwiseIncrement,
    elementwiseUpdateEntry, elementwiseIncrement] using
    fl_elementwiseUpdateEntryWithProb_error_bound fp s A (sqMagProb A) i j x
      hdenom

/-- Entrywise forward-error bound for the one-sample matrix update. Entries
    other than the sampled entry are unchanged, hence have zero error. -/
theorem fl_elementwiseSampleUpdate_error_bound (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hdenom : (s : ℝ) * sqMagProb A i j ≠ 0) (r : Fin m) (c : Fin n) :
    |fl_elementwiseSampleUpdate fp s A Atilde i j r c -
      elementwiseSampleUpdate s A Atilde i j r c| ≤
      if r = i ∧ c = j then
        |elementwiseUpdateEntry s A i j (Atilde i j)| * fp.u +
          |elementwiseIncrement s A i j| * fp.u * (1 + fp.u)
      else
        0 := by
  simpa [fl_elementwiseSampleUpdate, elementwiseSampleUpdate,
    fl_elementwiseUpdateEntry, elementwiseUpdateEntry, fl_elementwiseIncrement,
    elementwiseIncrement] using
    fl_elementwiseSampleUpdateWithProb_error_bound fp s A Atilde
      (sqMagProb A) i j hdenom r c

/-- Squared-magnitude specialization of the sampled-entry update bound:
    for `pᵢⱼ = Aᵢⱼ² / ‖A‖²_F`, the exact increment is
    `‖A‖²_F / (s Aᵢⱼ)`. -/
theorem fl_elementwiseUpdateEntry_sqMag_error_bound (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) :
    |fl_elementwiseUpdateEntry fp s A i j x -
      (x + frobNormSqRect A / ((s : ℝ) * A i j))| ≤
      |x + frobNormSqRect A / ((s : ℝ) * A i j)| * fp.u +
        |frobNormSqRect A / ((s : ℝ) * A i j)| * fp.u * (1 + fp.u) := by
  have hdenom := elementwiseSampleDenom_ne_zero s A i j hs hAij
  have hinc := elementwiseIncrement_sqMag_eq s A i j hs hAij
  have hbound := fl_elementwiseUpdateEntry_error_bound fp s A i j x hdenom
  have hinc' :
      elementwiseIncrementWithProb s A (sqMagProb A) i j =
        frobNormSqRect A / ((s : ℝ) * A i j) := by
    simpa [elementwiseIncrement] using hinc
  have hupdate :
      elementwiseUpdateEntryWithProb s A (sqMagProb A) i j x =
        x + frobNormSqRect A / ((s : ℝ) * A i j) := by
    simp [elementwiseUpdateEntryWithProb, hinc']
  have hupdate_old :
      elementwiseUpdateEntry s A i j x =
        x + frobNormSqRect A / ((s : ℝ) * A i j) := by
    simpa [elementwiseUpdateEntry] using hupdate
  simpa [hupdate_old, hinc] using hbound

-- ============================================================
-- Deterministic traces and accumulated repeated-hit bounds
-- ============================================================

/-- Predicate that a trace step samples the entry `(r, c)`. -/
def sampleHits {m n steps : ℕ} (samples : ElementwiseTrace m n steps)
    (t : Fin steps) (r : Fin m) (c : Fin n) : Prop :=
  (samples t).1 = r ∧ (samples t).2 = c

/-- The exact contribution of one sampled pair to a fixed entry `(r, c)`,
    using a supplied exact probability table. -/
noncomputable def elementwiseSampleContributionWithProb {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (r : Fin m) (c : Fin n) : ℝ :=
  by
    classical
    exact
      if sample.1 = r ∧ sample.2 = c then
        elementwiseIncrementWithProb s A p r c
      else
        0

/-- The exact contribution of one trace step to a fixed entry `(r, c)`, using
    a supplied exact probability table. -/
noncomputable def elementwiseTraceContributionWithProb {m n steps : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (t : Fin steps)
    (r : Fin m) (c : Fin n) : ℝ :=
  by
    classical
    exact
      if sampleHits samples t r c then
        elementwiseIncrementWithProb s A p r c
      else
        0

/-- A supplied-probability trace contribution is the one-sample contribution
    of that trace step. -/
theorem elementwiseTraceContributionWithProb_eq_sampleContributionWithProb
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (t : Fin steps) (r : Fin m) (c : Fin n) :
    elementwiseTraceContributionWithProb s A p samples t r c =
      elementwiseSampleContributionWithProb s A p (samples t) r c := by
  simp [elementwiseTraceContributionWithProb,
    elementwiseSampleContributionWithProb, sampleHits]

/-- Exact deterministic Algorithm 1 trace using a supplied exact
    probability table. -/
noncomputable def elementwiseTraceSketchWithProb {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun r c =>
    Atilde r c +
      ∑ t : Fin steps, elementwiseTraceContributionWithProb s A p samples t r c

/-- Floating-point deterministic Algorithm 1 trace using a supplied exact
    probability table. -/
noncomputable def fl_elementwiseTraceSketchWithProb (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun r c =>
    by
      classical
      exact
        Fin.foldl steps
          (fun acc t =>
            if sampleHits samples t r c then
              fl_elementwiseUpdateEntryWithProb fp s A p r c acc
            else
              acc)
          (Atilde r c)

/-- Repeated exact updates to a fixed entry, using a supplied exact
    probability table. -/
noncomputable def repeatElementwiseUpdateEntryWithProb {m n : ℕ} (q s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  x + (q : ℝ) * elementwiseIncrementWithProb s A p i j

/-- Repeated floating-point updates to a fixed entry, using a supplied exact
    probability table. -/
noncomputable def fl_repeatElementwiseUpdateEntryWithProb (fp : FPModel)
    {m n : ℕ} (q s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  Fin.foldl q
    (fun acc _ => fp.fl_add acc (fl_elementwiseIncrementWithProb fp s A p i j))
    x

/-- The exact contribution of one sampled pair to a fixed entry `(r, c)`.
    This is the one-step version of `elementwiseTraceContribution`. -/
noncomputable def elementwiseSampleContribution {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (r : Fin m) (c : Fin n) : ℝ :=
  by
    classical
    exact
      if sample.1 = r ∧ sample.2 = c then
        elementwiseIncrement s A r c
      else
        0

/-- The exact contribution of one trace step to the fixed entry `(r, c)`.
    Non-hitting steps contribute zero to this entry. -/
noncomputable def elementwiseTraceContribution {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (t : Fin steps) (r : Fin m) (c : Fin n) : ℝ :=
  by
    classical
    exact
      if sampleHits samples t r c then
        elementwiseIncrement s A r c
      else
        0

/-- A trace contribution is the one-sample contribution of that trace step. -/
theorem elementwiseTraceContribution_eq_sampleContribution {m n steps : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (t : Fin steps)
    (r : Fin m) (c : Fin n) :
    elementwiseTraceContribution s A samples t r c =
      elementwiseSampleContribution s A (samples t) r c := by
  simp [elementwiseTraceContribution, elementwiseSampleContribution, sampleHits]

/-- Exact deterministic Algorithm 1 trace, written entrywise as the initial
    sketch plus the contributions from every sampled step that hits the entry. -/
noncomputable def elementwiseTraceSketch {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun r c =>
    Atilde r c +
      ∑ t : Fin steps, elementwiseTraceContribution s A samples t r c

/-- Floating-point deterministic Algorithm 1 trace, restricted entrywise. A
    step that does not sample `(r, c)` is a no-op for this entry. -/
noncomputable def fl_elementwiseTraceSketch (fp : FPModel) {m n steps : ℕ}
    (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun r c =>
    by
      classical
      exact
        Fin.foldl steps
          (fun acc t =>
            if sampleHits samples t r c then
              fl_elementwiseUpdateEntry fp s A r c acc
            else
              acc)
          (Atilde r c)

/-- Number of trace steps that sample the entry `(r, c)`. -/
noncomputable def hitCount {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (r : Fin m) (c : Fin n) : ℕ :=
  by
    classical
    exact
      Fin.foldl steps
        (fun q t => if sampleHits samples t r c then q + 1 else q)
        0

/-- Repeated exact updates to a fixed entry. This is the scalar form obtained
    from a trace after retaining only the steps that hit that entry. -/
noncomputable def repeatElementwiseUpdateEntry {m n : ℕ} (q s : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ) : ℝ :=
  x + (q : ℝ) * elementwiseIncrement s A i j

/-- Repeated floating-point updates to a fixed entry. -/
noncomputable def fl_repeatElementwiseUpdateEntry (fp : FPModel) {m n : ℕ}
    (q s : ℕ) (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (x : ℝ) : ℝ :=
  Fin.foldl q
    (fun acc _ => fp.fl_add acc (fl_elementwiseIncrement fp s A i j))
    x

/-- Hit-count recurrence when the last trace step hits the entry. -/
theorem hitCount_succ_last_of_hit {m n steps : ℕ}
    (samples : ElementwiseTrace m n (steps + 1)) (i : Fin m) (j : Fin n)
    (hlast : sampleHits samples (Fin.last steps) i j) :
    hitCount samples i j =
      hitCount (fun t : Fin steps => samples t.castSucc) i j + 1 := by
  classical
  unfold hitCount
  rw [Fin.foldl_succ_last]
  have hlast' :
      (samples (Fin.last steps)).1 = i ∧ (samples (Fin.last steps)).2 = j := by
    simpa [sampleHits] using hlast
  simp [sampleHits, hlast']
  rfl

/-- Hit-count recurrence when the last trace step does not hit the entry. -/
theorem hitCount_succ_last_of_not_hit {m n steps : ℕ}
    (samples : ElementwiseTrace m n (steps + 1)) (i : Fin m) (j : Fin n)
    (hlast : ¬ sampleHits samples (Fin.last steps) i j) :
    hitCount samples i j =
      hitCount (fun t : Fin steps => samples t.castSucc) i j := by
  classical
  unfold hitCount
  rw [Fin.foldl_succ_last]
  have hlast' :
      ¬ ((samples (Fin.last steps)).1 = i ∧
          (samples (Fin.last steps)).2 = j) := by
    simpa [sampleHits] using hlast
  simp [sampleHits, hlast']
  rfl

/-- A fixed entry can be hit at most once per trace step. -/
theorem hitCount_le_steps {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    hitCount samples i j ≤ steps := by
  classical
  induction steps with
  | zero =>
      simp [hitCount]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps := fun t => samples t.castSucc
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        rw [hcount]
        exact Nat.succ_le_succ (ih samplePrefix)
      · have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        rw [hcount]
        exact Nat.le_succ_of_le (ih samplePrefix)

/-- If no trace step hits a fixed entry, then its hit count is zero. -/
theorem hitCount_eq_zero_of_forall_not_hit {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hnohit : ∀ t : Fin steps, ¬ sampleHits samples t i j) :
    hitCount samples i j = 0 := by
  classical
  induction steps with
  | zero =>
      simp [hitCount]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps := fun t => samples t.castSucc
      have hlast : ¬ sampleHits samples (Fin.last steps) i j := hnohit (Fin.last steps)
      have hprefix : ∀ t : Fin steps, ¬ sampleHits samplePrefix t i j := by
        intro t
        exact hnohit t.castSucc
      have hcount := hitCount_succ_last_of_not_hit samples i j hlast
      change hitCount samples i j = hitCount samplePrefix i j at hcount
      rw [hcount]
      exact ih samplePrefix hprefix

/-- Peeling one supplied-probability repeated floating-point update from the
    end. -/
theorem fl_repeatElementwiseUpdateEntryWithProb_succ (fp : FPModel)
    {m n : ℕ} (q s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ) :
    fl_repeatElementwiseUpdateEntryWithProb fp (q + 1) s A p i j x =
      fl_elementwiseUpdateEntryWithProb fp s A p i j
        (fl_repeatElementwiseUpdateEntryWithProb fp q s A p i j x) := by
  unfold fl_repeatElementwiseUpdateEntryWithProb
    fl_elementwiseUpdateEntryWithProb
  rw [Fin.foldl_succ_last]

/-- The exact supplied-probability trace at a fixed entry reduces to repeated
    scalar updates, with repetition count equal to the number of hits. -/
theorem elementwiseTraceSketchWithProb_eq_repeat_of_hitCount
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n) :
    elementwiseTraceSketchWithProb s A Atilde p samples i j =
      repeatElementwiseUpdateEntryWithProb (hitCount samples i j) s A p i j
        (Atilde i j) := by
  classical
  induction steps with
  | zero =>
      simp [elementwiseTraceSketchWithProb, elementwiseTraceContributionWithProb,
        hitCount, repeatElementwiseUpdateEntryWithProb]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps := fun t => samples t.castSucc
      have ih_prefix := ih samplePrefix
      have hprefix_sum :
          (∑ t : Fin steps,
              elementwiseTraceContributionWithProb s A p samples t.castSucc i j) =
            ∑ t : Fin steps,
              elementwiseTraceContributionWithProb s A p samplePrefix t i j := by
        apply Finset.sum_congr rfl
        intro t _
        simp [elementwiseTraceContributionWithProb, sampleHits, samplePrefix]
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · unfold elementwiseTraceSketchWithProb
        rw [Fin.sum_univ_castSucc, hprefix_sum]
        rw [← add_assoc]
        rw [show Atilde i j +
              (∑ t : Fin steps,
                elementwiseTraceContributionWithProb s A p samplePrefix t i j) =
              elementwiseTraceSketchWithProb s A Atilde p samplePrefix i j by
                rfl]
        rw [ih_prefix]
        have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        rw [hcount]
        simp [hlast, elementwiseTraceContributionWithProb,
          repeatElementwiseUpdateEntryWithProb]
        ring
      · unfold elementwiseTraceSketchWithProb
        rw [Fin.sum_univ_castSucc, hprefix_sum]
        rw [← add_assoc]
        rw [show Atilde i j +
              (∑ t : Fin steps,
                elementwiseTraceContributionWithProb s A p samplePrefix t i j) =
              elementwiseTraceSketchWithProb s A Atilde p samplePrefix i j by
                rfl]
        rw [ih_prefix]
        have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        rw [hcount]
        simp [hlast, elementwiseTraceContributionWithProb]

/-- The floating-point supplied-probability trace at a fixed entry reduces to
    repeated scalar floating-point updates, with repetition count equal to the
    number of hits. -/
theorem fl_elementwiseTraceSketchWithProb_eq_repeat_of_hitCount
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    fl_elementwiseTraceSketchWithProb fp s A Atilde p samples i j =
      fl_repeatElementwiseUpdateEntryWithProb fp (hitCount samples i j)
        s A p i j (Atilde i j) := by
  classical
  induction steps with
  | zero =>
      simp [fl_elementwiseTraceSketchWithProb,
        fl_repeatElementwiseUpdateEntryWithProb, hitCount]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps := fun t => samples t.castSucc
      have ih_prefix := ih samplePrefix
      have hstep :
          (fun acc t =>
            if sampleHits samples t.castSucc i j then
              fl_elementwiseUpdateEntryWithProb fp s A p i j acc
            else
              acc) =
            (fun acc t =>
              if sampleHits samplePrefix t i j then
                fl_elementwiseUpdateEntryWithProb fp s A p i j acc
              else
                acc) := by
        funext acc t
        rfl
      have hfold :
          fl_elementwiseTraceSketchWithProb fp s A Atilde p samples i j =
            (if sampleHits samples (Fin.last steps) i j then
              fl_elementwiseUpdateEntryWithProb fp s A p i j
                (fl_elementwiseTraceSketchWithProb fp s A Atilde p
                  samplePrefix i j)
            else
              fl_elementwiseTraceSketchWithProb fp s A Atilde p
                samplePrefix i j) := by
        unfold fl_elementwiseTraceSketchWithProb
        rw [Fin.foldl_succ_last]
        rw [hstep]
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        rw [hfold, if_pos hlast, ih_prefix, hcount]
        rw [fl_repeatElementwiseUpdateEntryWithProb_succ]
      · have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        rw [hfold, if_neg hlast, ih_prefix, hcount]

/-- Accumulated forward-error bound for `q` floating-point updates to one fixed
    sampled entry when the rescaling probability is the supplied exact value
    `pᵢⱼ`. -/
theorem fl_repeatElementwiseUpdateEntryWithProb_error_bound (fp : FPModel)
    {m n : ℕ} (q s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (x : ℝ)
    (hdenom : (s : ℝ) * p i j ≠ 0)
    (hq : gammaValid fp q) (hq1 : gammaValid fp (q + 1)) :
    |fl_repeatElementwiseUpdateEntryWithProb fp q s A p i j x -
      repeatElementwiseUpdateEntryWithProb q s A p i j x| ≤
      |x| * gamma fp q +
        (q : ℝ) * |elementwiseIncrementWithProb s A p i j| *
          gamma fp (q + 1) := by
  let inc : ℝ := elementwiseIncrementWithProb s A p i j
  let y : ℝ := fl_elementwiseIncrementWithProb fp s A p i j
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div (A i j) ((s : ℝ) * p i j) hdenom
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    fl_sum_error_init fp q (fun _ : Fin q => y) x hq
  have hy : y = inc * (1 + δdiv) := by
    unfold y inc fl_elementwiseIncrementWithProb elementwiseIncrementWithProb
    exact hdiv
  have hsum_rw :
      ∑ k : Fin q, inc * (1 + δdiv) * (1 + θ k) =
        ∑ k : Fin q, (inc + inc * ((1 + δdiv) * (1 + θ k) - 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have herr :
      fl_repeatElementwiseUpdateEntryWithProb fp q s A p i j x -
        repeatElementwiseUpdateEntryWithProb q s A p i j x =
        x * Θ + ∑ k : Fin q, inc * ((1 + δdiv) * (1 + θ k) - 1) := by
    unfold fl_repeatElementwiseUpdateEntryWithProb
      repeatElementwiseUpdateEntryWithProb
    rw [hfold]
    simp_rw [hy]
    rw [hsum_rw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hq1
  have hδγ : |δdiv| ≤ gamma fp 1 :=
    le_trans hδdiv (u_le_gamma fp one_pos h1valid)
  have hfactor :
      ∀ k : Fin q, |(1 + δdiv) * (1 + θ k) - 1| ≤ gamma fp (q + 1) := by
    intro k
    obtain ⟨η, hη, heq⟩ := gamma_mul fp q 1 (θ k) δdiv (hθ k) hδγ hq1
    have heq' : (1 + δdiv) * (1 + θ k) - 1 = η := by
      have hcomm : (1 + δdiv) * (1 + θ k) = 1 + η := by
        rw [mul_comm]
        exact heq
      linarith
    rw [heq']
    exact hη
  have hsum_bound :
      ∑ k : Fin q, |inc * ((1 + δdiv) * (1 + θ k) - 1)| ≤
        (q : ℝ) * |inc| * gamma fp (q + 1) := by
    calc
      ∑ k : Fin q, |inc * ((1 + δdiv) * (1 + θ k) - 1)|
          = ∑ k : Fin q, |inc| * |(1 + δdiv) * (1 + θ k) - 1| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
      _ ≤ ∑ _k : Fin q, |inc| * gamma fp (q + 1) := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_left (hfactor k) (abs_nonneg inc)
      _ = (q : ℝ) * |inc| * gamma fp (q + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
              ring
  calc
    |fl_repeatElementwiseUpdateEntryWithProb fp q s A p i j x -
      repeatElementwiseUpdateEntryWithProb q s A p i j x|
        = |x * Θ + ∑ k : Fin q,
            inc * ((1 + δdiv) * (1 + θ k) - 1)| := by
            rw [herr]
    _ ≤ |x * Θ| + |∑ k : Fin q,
          inc * ((1 + δdiv) * (1 + θ k) - 1)| := abs_add_le _ _
    _ ≤ |x| * gamma fp q +
          ∑ k : Fin q, |inc * ((1 + δdiv) * (1 + θ k) - 1)| := by
            apply add_le_add
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_left hΘ (abs_nonneg x)
            · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |x| * gamma fp q +
          (q : ℝ) * |inc| * gamma fp (q + 1) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hsum_bound (|x| * gamma fp q)

/-- General accumulated deterministic trace bound for a fixed entry using a
    supplied exact probability table. -/
theorem fl_elementwiseTraceSketchWithProb_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n)
    (hdenom : (s : ℝ) * p i j ≠ 0)
    (hsteps : gammaValid fp (hitCount samples i j))
    (hsteps1 : gammaValid fp (hitCount samples i j + 1)) :
    |fl_elementwiseTraceSketchWithProb fp s A Atilde p samples i j -
      elementwiseTraceSketchWithProb s A Atilde p samples i j| ≤
      |Atilde i j| * gamma fp (hitCount samples i j) +
        (hitCount samples i j : ℝ) *
          |elementwiseIncrementWithProb s A p i j| *
          gamma fp (hitCount samples i j + 1) := by
  rw [fl_elementwiseTraceSketchWithProb_eq_repeat_of_hitCount,
    elementwiseTraceSketchWithProb_eq_repeat_of_hitCount]
  exact fl_repeatElementwiseUpdateEntryWithProb_error_bound fp
    (hitCount samples i j) s A p i j (Atilde i j)
    hdenom hsteps hsteps1

/-- Peeling one repeated floating-point update from the end. -/
theorem fl_repeatElementwiseUpdateEntry_succ (fp : FPModel)
    {m n : ℕ} (q s : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ) :
    fl_repeatElementwiseUpdateEntry fp (q + 1) s A i j x =
      fl_elementwiseUpdateEntry fp s A i j
        (fl_repeatElementwiseUpdateEntry fp q s A i j x) := by
  unfold fl_repeatElementwiseUpdateEntry fl_elementwiseUpdateEntry
  rw [Fin.foldl_succ_last]
  simp [fl_elementwiseUpdateEntryWithProb, fl_elementwiseIncrement]

/-- The exact trace at a fixed entry reduces to repeated scalar updates, with
    repetition count equal to the number of hits of that entry. -/
theorem elementwiseTraceSketch_eq_repeat_of_hitCount {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n) :
    elementwiseTraceSketch s A Atilde samples i j =
      repeatElementwiseUpdateEntry (hitCount samples i j) s A i j (Atilde i j) := by
  classical
  induction steps with
  | zero =>
      simp [elementwiseTraceSketch, elementwiseTraceContribution, hitCount,
        repeatElementwiseUpdateEntry]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps := fun t => samples t.castSucc
      have ih_prefix := ih samplePrefix
      have hprefix_sum :
          (∑ t : Fin steps,
              elementwiseTraceContribution s A samples t.castSucc i j) =
            ∑ t : Fin steps, elementwiseTraceContribution s A samplePrefix t i j := by
        apply Finset.sum_congr rfl
        intro t _
        simp [elementwiseTraceContribution, sampleHits, samplePrefix]
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · unfold elementwiseTraceSketch
        rw [Fin.sum_univ_castSucc, hprefix_sum]
        rw [← add_assoc]
        rw [show Atilde i j +
              (∑ t : Fin steps, elementwiseTraceContribution s A samplePrefix t i j) =
              elementwiseTraceSketch s A Atilde samplePrefix i j by
                rfl]
        rw [ih_prefix]
        have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        rw [hcount]
        simp [hlast, elementwiseTraceContribution, repeatElementwiseUpdateEntry]
        ring
      · unfold elementwiseTraceSketch
        rw [Fin.sum_univ_castSucc, hprefix_sum]
        rw [← add_assoc]
        rw [show Atilde i j +
              (∑ t : Fin steps, elementwiseTraceContribution s A samplePrefix t i j) =
              elementwiseTraceSketch s A Atilde samplePrefix i j by
                rfl]
        rw [ih_prefix]
        have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        rw [hcount]
        simp [hlast, elementwiseTraceContribution]

/-- The floating-point trace at a fixed entry reduces to repeated scalar
    floating-point updates, with repetition count equal to the number of hits
    of that entry. -/
theorem fl_elementwiseTraceSketch_eq_repeat_of_hitCount (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    fl_elementwiseTraceSketch fp s A Atilde samples i j =
      fl_repeatElementwiseUpdateEntry fp (hitCount samples i j) s A i j
        (Atilde i j) := by
  classical
  induction steps with
  | zero =>
      simp [fl_elementwiseTraceSketch, fl_repeatElementwiseUpdateEntry, hitCount]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps := fun t => samples t.castSucc
      have ih_prefix := ih samplePrefix
      have hstep :
          (fun acc t =>
            if sampleHits samples t.castSucc i j then
              fl_elementwiseUpdateEntry fp s A i j acc
            else
              acc) =
            (fun acc t =>
              if sampleHits samplePrefix t i j then
                fl_elementwiseUpdateEntry fp s A i j acc
              else
                acc) := by
        funext acc t
        rfl
      have hfold :
          fl_elementwiseTraceSketch fp s A Atilde samples i j =
            (if sampleHits samples (Fin.last steps) i j then
              fl_elementwiseUpdateEntry fp s A i j
                (fl_elementwiseTraceSketch fp s A Atilde samplePrefix i j)
            else
              fl_elementwiseTraceSketch fp s A Atilde samplePrefix i j) := by
        unfold fl_elementwiseTraceSketch
        rw [Fin.foldl_succ_last]
        rw [hstep]
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        rw [hfold, if_pos hlast, ih_prefix, hcount]
        rw [fl_repeatElementwiseUpdateEntry_succ]
      · have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        rw [hfold, if_neg hlast, ih_prefix, hcount]

/-- If a zero-initialized trace never hits an entry, the floating-point value
    of that entry remains exactly zero because all non-hit steps are no-ops. -/
theorem fl_elementwiseTraceSketch_zero_init_eq_zero_of_forall_not_hit
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n)
    (hnohit : ∀ t : Fin steps, ¬ sampleHits samples t i j) :
    fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j = 0 := by
  have hcount := hitCount_eq_zero_of_forall_not_hit samples i j hnohit
  rw [fl_elementwiseTraceSketch_eq_repeat_of_hitCount, hcount]
  simp [fl_repeatElementwiseUpdateEntry]

/-- Accumulated forward-error bound for `q` floating-point updates to one
    fixed sampled entry. The bound separates the accumulated summation error
    `γ_q |x|` from the `q` repeated rounded increments, each carrying the
    division error and the summation error combined into `γ_{q+1}`. -/
theorem fl_repeatElementwiseUpdateEntry_error_bound (fp : FPModel)
    {m n : ℕ} (q s : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ)
    (hdenom : (s : ℝ) * sqMagProb A i j ≠ 0)
    (hq : gammaValid fp q) (hq1 : gammaValid fp (q + 1)) :
    |fl_repeatElementwiseUpdateEntry fp q s A i j x -
      repeatElementwiseUpdateEntry q s A i j x| ≤
      |x| * gamma fp q +
        (q : ℝ) * |elementwiseIncrement s A i j| * gamma fp (q + 1) := by
  let inc : ℝ := elementwiseIncrement s A i j
  let y : ℝ := fl_elementwiseIncrement fp s A i j
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div (A i j) ((s : ℝ) * sqMagProb A i j) hdenom
  obtain ⟨Θ, θ, hΘ, hθ, hfold⟩ :=
    fl_sum_error_init fp q (fun _ : Fin q => y) x hq
  have hy : y = inc * (1 + δdiv) := by
    unfold y inc fl_elementwiseIncrement elementwiseIncrement
    exact hdiv
  have hsum_rw :
      ∑ k : Fin q, inc * (1 + δdiv) * (1 + θ k) =
        ∑ k : Fin q, (inc + inc * ((1 + δdiv) * (1 + θ k) - 1)) := by
    apply Finset.sum_congr rfl
    intro k _
    ring
  have herr :
      fl_repeatElementwiseUpdateEntry fp q s A i j x -
        repeatElementwiseUpdateEntry q s A i j x =
        x * Θ + ∑ k : Fin q, inc * ((1 + δdiv) * (1 + θ k) - 1) := by
    unfold fl_repeatElementwiseUpdateEntry repeatElementwiseUpdateEntry
    rw [hfold]
    simp_rw [hy]
    rw [hsum_rw, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have h1valid : gammaValid fp 1 := gammaValid_mono fp (by omega) hq1
  have hδγ : |δdiv| ≤ gamma fp 1 :=
    le_trans hδdiv (u_le_gamma fp one_pos h1valid)
  have hfactor :
      ∀ k : Fin q, |(1 + δdiv) * (1 + θ k) - 1| ≤ gamma fp (q + 1) := by
    intro k
    obtain ⟨η, hη, heq⟩ := gamma_mul fp q 1 (θ k) δdiv (hθ k) hδγ hq1
    have heq' : (1 + δdiv) * (1 + θ k) - 1 = η := by
      have hcomm : (1 + δdiv) * (1 + θ k) = 1 + η := by
        rw [mul_comm]
        exact heq
      linarith
    rw [heq']
    exact hη
  have hsum_bound :
      ∑ k : Fin q, |inc * ((1 + δdiv) * (1 + θ k) - 1)| ≤
        (q : ℝ) * |inc| * gamma fp (q + 1) := by
    calc
      ∑ k : Fin q, |inc * ((1 + δdiv) * (1 + θ k) - 1)|
          = ∑ k : Fin q, |inc| * |(1 + δdiv) * (1 + θ k) - 1| := by
              apply Finset.sum_congr rfl
              intro k _
              rw [abs_mul]
      _ ≤ ∑ _k : Fin q, |inc| * gamma fp (q + 1) := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul_of_nonneg_left (hfactor k) (abs_nonneg inc)
      _ = (q : ℝ) * |inc| * gamma fp (q + 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              ring
  calc
    |fl_repeatElementwiseUpdateEntry fp q s A i j x -
      repeatElementwiseUpdateEntry q s A i j x|
        = |x * Θ + ∑ k : Fin q, inc * ((1 + δdiv) * (1 + θ k) - 1)| := by
            rw [herr]
    _ ≤ |x * Θ| + |∑ k : Fin q, inc * ((1 + δdiv) * (1 + θ k) - 1)| :=
            abs_add_le _ _
    _ ≤ |x| * gamma fp q +
          ∑ k : Fin q, |inc * ((1 + δdiv) * (1 + θ k) - 1)| := by
            apply add_le_add
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_left hΘ (abs_nonneg x)
            · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ |x| * gamma fp q +
          (q : ℝ) * |inc| * gamma fp (q + 1) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right hsum_bound (|x| * gamma fp q)

/-- General accumulated deterministic trace bound for a fixed entry. This is
    the trace-level version of the repeated-hit theorem: non-hit steps are
    no-ops, and hit steps form a scalar repeated-update computation. -/
theorem fl_elementwiseTraceSketch_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hdenom : (s : ℝ) * sqMagProb A i j ≠ 0)
    (hsteps : gammaValid fp (hitCount samples i j))
    (hsteps1 : gammaValid fp (hitCount samples i j + 1)) :
    |fl_elementwiseTraceSketch fp s A Atilde samples i j -
      elementwiseTraceSketch s A Atilde samples i j| ≤
      |Atilde i j| * gamma fp (hitCount samples i j) +
        (hitCount samples i j : ℝ) * |elementwiseIncrement s A i j| *
          gamma fp (hitCount samples i j + 1) := by
  rw [fl_elementwiseTraceSketch_eq_repeat_of_hitCount,
    elementwiseTraceSketch_eq_repeat_of_hitCount]
  exact fl_repeatElementwiseUpdateEntry_error_bound fp (hitCount samples i j)
    s A i j (Atilde i j) hdenom hsteps hsteps1

/-- Squared-magnitude specialization of the accumulated repeated-hit bound. -/
theorem fl_repeatElementwiseUpdateEntry_sqMag_error_bound (fp : FPModel)
    {m n : ℕ} (q s : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (x : ℝ)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hq : gammaValid fp q) (hq1 : gammaValid fp (q + 1)) :
    |fl_repeatElementwiseUpdateEntry fp q s A i j x -
      (x + (q : ℝ) * (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
      |x| * gamma fp q +
        (q : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| *
          gamma fp (q + 1) := by
  have hdenom := elementwiseSampleDenom_ne_zero s A i j hs hAij
  have hinc := elementwiseIncrement_sqMag_eq s A i j hs hAij
  have hbound :=
    fl_repeatElementwiseUpdateEntry_error_bound fp q s A i j x hdenom hq hq1
  unfold repeatElementwiseUpdateEntry at hbound
  rw [hinc] at hbound
  exact hbound

/-- Exact deterministic trace formula for squared-magnitude probabilities. -/
theorem elementwiseTraceSketch_sqMag_eq {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) :
    elementwiseTraceSketch s A Atilde samples i j =
      Atilde i j + (hitCount samples i j : ℝ) *
        (frobNormSqRect A / ((s : ℝ) * A i j)) := by
  rw [elementwiseTraceSketch_eq_repeat_of_hitCount]
  unfold repeatElementwiseUpdateEntry
  rw [elementwiseIncrement_sqMag_eq s A i j hs hAij]

/-- Complete deterministic entrywise stability bound for Algorithm 1 with
    squared-magnitude probabilities. This compares the floating-point trace to
    the exact trace formula obtained by counting how many times `(i, j)` is
    sampled. -/
theorem fl_elementwiseTraceSketch_sqMag_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hsteps : gammaValid fp (hitCount samples i j))
    (hsteps1 : gammaValid fp (hitCount samples i j + 1)) :
    |fl_elementwiseTraceSketch fp s A Atilde samples i j -
      (Atilde i j + (hitCount samples i j : ℝ) *
        (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
      |Atilde i j| * gamma fp (hitCount samples i j) +
        (hitCount samples i j : ℝ) *
          |frobNormSqRect A / ((s : ℝ) * A i j)| *
          gamma fp (hitCount samples i j + 1) := by
  rw [fl_elementwiseTraceSketch_eq_repeat_of_hitCount]
  exact fl_repeatElementwiseUpdateEntry_sqMag_error_bound fp
    (hitCount samples i j) s A i j (Atilde i j) hs hAij hsteps hsteps1

/-- Complete deterministic entrywise stability bound against the exact trace,
    specialized to squared-magnitude probabilities. -/
theorem fl_elementwiseTraceSketch_sqMag_error_bound_exact (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hsteps : gammaValid fp (hitCount samples i j))
    (hsteps1 : gammaValid fp (hitCount samples i j + 1)) :
    |fl_elementwiseTraceSketch fp s A Atilde samples i j -
      elementwiseTraceSketch s A Atilde samples i j| ≤
      |Atilde i j| * gamma fp (hitCount samples i j) +
        (hitCount samples i j : ℝ) *
          |frobNormSqRect A / ((s : ℝ) * A i j)| *
          gamma fp (hitCount samples i j + 1) := by
  rw [elementwiseTraceSketch_sqMag_eq s A Atilde samples i j hs hAij]
  exact fl_elementwiseTraceSketch_sqMag_error_bound fp s A Atilde samples i j
    hs hAij hsteps hsteps1

/-- Algorithm 1 starts from the zero sketch. In that case the accumulated
    initial-accumulator term disappears. -/
theorem fl_elementwiseSketch_zero_init_sqMag_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hsteps : gammaValid fp (hitCount samples i j))
    (hsteps1 : gammaValid fp (hitCount samples i j + 1)) :
    |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
      ((hitCount samples i j : ℝ) *
        (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
        (hitCount samples i j : ℝ) *
          |frobNormSqRect A / ((s : ℝ) * A i j)| *
          gamma fp (hitCount samples i j + 1) := by
  have hbound :=
    fl_elementwiseTraceSketch_sqMag_error_bound fp s A (fun _ _ => 0)
      samples i j hs hAij hsteps hsteps1
  simpa using hbound

/-- Entrywise packaged form of the squared-magnitude deterministic stability
    theorem. -/
theorem fl_elementwiseTraceSketch_entrywise_sqMag_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps)
    (hs : (s : ℝ) ≠ 0)
    (hA : ∀ i j, A i j ≠ 0)
    (hsteps : ∀ i j, gammaValid fp (hitCount samples i j))
    (hsteps1 : ∀ i j, gammaValid fp (hitCount samples i j + 1)) :
    ∀ i j,
      |fl_elementwiseTraceSketch fp s A Atilde samples i j -
        (Atilde i j + (hitCount samples i j : ℝ) *
          (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
        |Atilde i j| * gamma fp (hitCount samples i j) +
          (hitCount samples i j : ℝ) *
            |frobNormSqRect A / ((s : ℝ) * A i j)| *
            gamma fp (hitCount samples i j + 1) := by
  intro i j
  exact fl_elementwiseTraceSketch_sqMag_error_bound fp s A Atilde samples i j
    hs (hA i j) (hsteps i j) (hsteps1 i j)

-- ============================================================
-- Random-trace stability transfer through the hit counter
-- ============================================================

/-- Deterministic stability budget after replacing the actual hit count by
    an upper bound `Q`. This is the quantity that a concentration theorem for
    `qᵢⱼ = hitCount samples i j` can plug into the stability result. -/
noncomputable def sqMagTraceErrorBudget (fp : FPModel) {m n : ℕ} (Q s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) : ℝ :=
  |Atilde i j| * gamma fp Q +
    (Q : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| * gamma fp (Q + 1)

/-- The squared-magnitude trace error budget is nonnegative under its usual
    `gammaValid` guards. -/
theorem sqMagTraceErrorBudget_nonneg (fp : FPModel) {m n : ℕ} (Q s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1)) :
    0 ≤ sqMagTraceErrorBudget fp Q s A Atilde i j := by
  unfold sqMagTraceErrorBudget
  apply add_nonneg
  · exact mul_nonneg (abs_nonneg _) (gamma_nonneg fp hQ)
  · exact mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le Q) (abs_nonneg _))
      (gamma_nonneg fp hQ1)

/-- The squared-magnitude stability budget is monotone in the hit-count
    parameter, under the usual validity guard for the larger count. -/
theorem sqMagTraceErrorBudget_mono (fp : FPModel) {m n : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    {q Q : ℕ} (hqQ : q ≤ Q) (hQ : gammaValid fp Q)
    (hQ1 : gammaValid fp (Q + 1)) :
    sqMagTraceErrorBudget fp q s A Atilde i j ≤
      sqMagTraceErrorBudget fp Q s A Atilde i j := by
  let c : ℝ := frobNormSqRect A / ((s : ℝ) * A i j)
  have hγqQ : gamma fp q ≤ gamma fp Q :=
    gamma_mono fp hqQ hQ
  have hq1Q1 : q + 1 ≤ Q + 1 := Nat.succ_le_succ hqQ
  have hγq1Q1 : gamma fp (q + 1) ≤ gamma fp (Q + 1) :=
    gamma_mono fp hq1Q1 hQ1
  have hγq1_nonneg : 0 ≤ gamma fp (q + 1) :=
    gamma_nonneg fp (gammaValid_mono fp hq1Q1 hQ1)
  have hQ_nonneg : 0 ≤ (Q : ℝ) := by exact_mod_cast Nat.zero_le Q
  have hqQ_real : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hterm1 :
      |Atilde i j| * gamma fp q ≤ |Atilde i j| * gamma fp Q :=
    mul_le_mul_of_nonneg_left hγqQ (abs_nonneg _)
  have hcount :
      (q : ℝ) * |c| ≤ (Q : ℝ) * |c| :=
    mul_le_mul_of_nonneg_right hqQ_real (abs_nonneg c)
  have hterm2_count :
      (q : ℝ) * |c| * gamma fp (q + 1) ≤
        (Q : ℝ) * |c| * gamma fp (q + 1) :=
    mul_le_mul_of_nonneg_right hcount hγq1_nonneg
  have hterm2_gamma :
      (Q : ℝ) * |c| * gamma fp (q + 1) ≤
        (Q : ℝ) * |c| * gamma fp (Q + 1) :=
    mul_le_mul_of_nonneg_left hγq1Q1
      (mul_nonneg hQ_nonneg (abs_nonneg c))
  have hterm2 :
      (q : ℝ) * |c| * gamma fp (q + 1) ≤
        (Q : ℝ) * |c| * gamma fp (Q + 1) :=
    le_trans hterm2_count hterm2_gamma
  unfold sqMagTraceErrorBudget
  simpa [c] using add_le_add hterm1 hterm2

/-- Deterministic corollary with the actual hit count bounded by any larger
    deterministic count `Q`. This is the Lean form of replacing the random
    counter in the *error budget* by a concentration upper bound. The exact
    trace formula remains centered at the actual counter `qᵢⱼ`, as it should. -/
theorem fl_elementwiseTraceSketch_sqMag_error_bound_of_hitCount_le
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hcount : hitCount samples i j ≤ Q) (hQ : gammaValid fp Q)
    (hQ1 : gammaValid fp (Q + 1)) :
    |fl_elementwiseTraceSketch fp s A Atilde samples i j -
      (Atilde i j + (hitCount samples i j : ℝ) *
        (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
      sqMagTraceErrorBudget fp Q s A Atilde i j := by
  have hdet :=
    fl_elementwiseTraceSketch_sqMag_error_bound fp s A Atilde samples i j
      hs hAij (gammaValid_mono fp hcount hQ)
      (gammaValid_mono fp (Nat.succ_le_succ hcount) hQ1)
  exact le_trans hdet
    (sqMagTraceErrorBudget_mono fp s A Atilde i j hcount hQ hQ1)

/-- Event that the random trace hits entry `(i, j)` at most `Q` times. A
    concentration theorem for the sampling model can prove this event has high
    probability for an appropriate `Q`. -/
def hitCountAtMostEvent {Ω : Type*} {m n steps : ℕ}
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) : Set Ω :=
  {ω | hitCount (X ω) i j ≤ Q}

/-- Event that the entrywise floating-point stability bound holds with the
    deterministic budget `Q`. -/
noncomputable def sqMagTraceStabilityEvent {Ω : Type*} (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) : Set Ω :=
  {ω |
    |fl_elementwiseTraceSketch fp s A Atilde (X ω) i j -
      (Atilde i j + (hitCount (X ω) i j : ℝ) *
        (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
      sqMagTraceErrorBudget fp Q s A Atilde i j}

/-- Pointwise probabilistic-transfer statement: on every outcome where the
    random hit counter is at most `Q`, the stability event with budget `Q`
    holds. -/
theorem hitCountAtMostEvent_subset_sqMagTraceStabilityEvent
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1)) :
    hitCountAtMostEvent X i j Q ⊆
      sqMagTraceStabilityEvent fp s A Atilde X i j Q := by
  intro ω hω
  exact fl_elementwiseTraceSketch_sqMag_error_bound_of_hitCount_le fp
    s A Atilde (X ω) i j Q hs hAij hω hQ hQ1

/-- High-probability stability corollary for any monotone real-valued
    probability functional on events. If the random counter concentrates below
    `Q` with probability at least `ρ`, then the floating-point stability bound
    with deterministic budget `Q` also holds with probability at least `ρ`. -/
theorem probability_sqMagTraceStability_of_hitCount_concentration
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ}
    (Pr : Set Ω → ℝ) (ρ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1))
    (hPr_mono : ∀ {E F : Set Ω}, E ⊆ F → Pr E ≤ Pr F)
    (hprob : ρ ≤ Pr (hitCountAtMostEvent X i j Q)) :
    ρ ≤ Pr (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  exact le_trans hprob
    (hPr_mono
      (hitCountAtMostEvent_subset_sqMagTraceStabilityEvent fp s A Atilde
        X i j Q hs hAij hQ hQ1))

/-- The same transfer theorem in the common `1 - δ` high-probability form. -/
theorem highProbability_sqMagTraceStability_of_hitCount_concentration
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ}
    (Pr : Set Ω → ℝ) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1))
    (hPr_mono : ∀ {E F : Set Ω}, E ⊆ F → Pr E ≤ Pr F)
    (hprob : 1 - δ ≤ Pr (hitCountAtMostEvent X i j Q)) :
    1 - δ ≤ Pr (sqMagTraceStabilityEvent fp s A Atilde X i j Q) :=
  probability_sqMagTraceStability_of_hitCount_concentration fp Pr (1 - δ)
    s A Atilde X i j Q hs hAij hQ hQ1 hPr_mono hprob

/-- A trace is compatible with squared-magnitude sampling when every sampled
    entry has nonzero matrix value. Under the squared-magnitude law, zero
    entries have probability zero and should not appear in an actual sample. -/
def TraceValidForSqMag {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Prop :=
  ∀ t, A (samples t).1 (samples t).2 ≠ 0

/-- A valid squared-magnitude trace only hits nonzero entries. -/
theorem TraceValidForSqMag.entry_ne_zero_of_hit {m n steps : ℕ}
    {A : Fin m → Fin n → ℝ} {samples : ElementwiseTrace m n steps}
    (hvalid : TraceValidForSqMag A samples) {t : Fin steps}
    {i : Fin m} {j : Fin n} (hhit : sampleHits samples t i j) :
    A i j ≠ 0 := by
  rcases hhit with ⟨hi, hj⟩
  rw [← hi, ← hj]
  exact hvalid t

/-- If every step in a trace samples the same entry `(i, j)`, the exact trace
    at that entry is the repeated scalar update. -/
theorem elementwiseTraceSketch_all_hit_eq_repeat {m n steps : ℕ} (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n) (hhit : ∀ t, sampleHits samples t i j) :
    elementwiseTraceSketch s A Atilde samples i j =
      repeatElementwiseUpdateEntry steps s A i j (Atilde i j) := by
  classical
  unfold elementwiseTraceSketch repeatElementwiseUpdateEntry
  simp [elementwiseTraceContribution, hhit, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- If every step in a trace samples the same entry `(i, j)`, the floating-point
    trace at that entry is the repeated scalar floating-point update. -/
theorem fl_elementwiseTraceSketch_all_hit_eq_repeat (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hhit : ∀ t, sampleHits samples t i j) :
    fl_elementwiseTraceSketch fp s A Atilde samples i j =
      fl_repeatElementwiseUpdateEntry fp steps s A i j (Atilde i j) := by
  classical
  unfold fl_elementwiseTraceSketch fl_repeatElementwiseUpdateEntry
  simp [hhit, fl_elementwiseUpdateEntry, fl_elementwiseIncrement,
    fl_elementwiseUpdateEntryWithProb]

/-- Trace-level squared-magnitude accumulated bound for the case where all
    trace steps hit one fixed entry. The general trace case reduces to this
    theorem after filtering a trace by the hits of each output entry. -/
theorem fl_elementwiseTraceSketch_all_hit_sqMag_error_bound (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A Atilde : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hhit : ∀ t, sampleHits samples t i j)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hsteps : gammaValid fp steps) (hsteps1 : gammaValid fp (steps + 1)) :
    |fl_elementwiseTraceSketch fp s A Atilde samples i j -
      (Atilde i j + (steps : ℝ) *
        (frobNormSqRect A / ((s : ℝ) * A i j)))| ≤
      |Atilde i j| * gamma fp steps +
        (steps : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| *
          gamma fp (steps + 1) := by
  rw [fl_elementwiseTraceSketch_all_hit_eq_repeat fp s A Atilde samples i j hhit]
  exact fl_repeatElementwiseUpdateEntry_sqMag_error_bound fp steps s A i j
    (Atilde i j) hs hAij hsteps hsteps1

end NumStability
