-- Algorithms/RandNLA/RowSamplingGram.lean
--
-- Gram-matrix expectation and stability consequences for Algorithm 2 of
-- Drineas--Mahoney's CACM RandNLA survey.
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
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.RandNLA.RowSampling

namespace NumStability

open scoped BigOperators

/-!
## Algorithm 2 Gram analysis

Algorithm 2 returns an `s × n` sampled row sketch `Ã`; the paper measures its
quality through the square Gram matrices `AᵀA` and `ÃᵀÃ`. This file contains
the modular Gram-matrix layer for row sampling:

* exact and floating-point sampled Gram matrices;
* the product-law marginal facts needed for independent row traces;
* elementwise unbiasedness of `ÃᵀÃ` under norm-squared row probabilities;
* the squared-Frobenius second moment and high-probability Markov form of
  equation (5);
* expected and high-probability consequences of an entrywise floating-point
  stability bound on the sampled sketch.

The final floating-point equation (5) corollaries keep the exact sampling
failure probability when the Gram perturbation budget is deterministic; the
generic `δτ` theorem is only a reusable union-bound transfer lemma.
-/

-- ============================================================
-- Gram matrices for exact and sampled row sketches
-- ============================================================

/-- Exact rectangular Gram matrix: `(AᵀA)_{jk} = ∑ᵢ Aᵢⱼ Aᵢₖ`. -/
noncomputable def rowGram {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ i : Fin m, A i j * A i k

/-- Gram matrix of an arbitrary row sketch. -/
noncomputable def rowSketchGram {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps, B t j * B t k

/-- Quadratic form of a row-sketch Gram matrix as a squared sketch norm. -/
theorem vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram
    {steps n : ℕ} (B : Fin steps → Fin n → ℝ) (y : Fin n → ℝ) :
    vecNorm2Sq (fun t : Fin steps => ∑ j : Fin n, B t j * y j) =
      ∑ j : Fin n, y j * matMulVec n (rowSketchGram B) y j := by
  classical
  unfold vecNorm2Sq matMulVec rowSketchGram
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Exact sampled Gram matrix `(ÃᵀÃ)` for an Algorithm 2 trace. -/
noncomputable def rowSampleGram {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps,
    rowSampleSketch s A samples t j * rowSampleSketch s A samples t k

/-- Quadratic form of an exact Algorithm 2 sampled Gram matrix. -/
theorem vecNorm2Sq_rowSampleSketch_linearCombination_eq_quadratic_rowSampleGram
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps)
    (y : Fin n → ℝ) :
    vecNorm2Sq
        (fun t : Fin steps => ∑ j : Fin n, rowSampleSketch s A samples t j * y j) =
      ∑ j : Fin n, y j * matMulVec n (rowSampleGram s A samples) y j := by
  simpa [rowSampleGram] using
    vecNorm2Sq_rowSketch_linearCombination_eq_quadratic_rowSketchGram
      (B := rowSampleSketch s A samples) y

/-- Floating-point sampled Gram matrix formed from the rounded sampled sketch. -/
noncomputable def fl_rowSampleGram (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k => ∑ t : Fin steps,
    fl_rowSampleSketch fp s A samples t j *
      fl_rowSampleSketch fp s A samples t k

/-- Fully floating-point sampled Gram matrix: form the rounded sampled sketch,
    then compute each Gram entry with the library's floating-point dot-product
    algorithm. -/
noncomputable def fl_rowSampleGramDot (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_rowSampleSketch fp s A samples t j)
      (fun t => fl_rowSampleSketch fp s A samples t k)

/-- Floating-point sampled Gram matrix formed from a sketch whose row-scale
    denominators were first computed approximately. -/
noncomputable def fl_rowSampleGramWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (den : Fin m → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  rowSketchGram (fl_rowSampleSketchWithComputedDen fp A den samples)

/-- Fully floating-point sampled Gram matrix for the computed-denominator
    Algorithm 2 path: compute denominators, round row scaling, then compute
    Gram entries with floating-point dot products. -/
noncomputable def fl_rowSampleGramDotWithComputedDen (fp : FPModel)
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (den : Fin m → ℝ) (samples : RowTrace m steps) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps
      (fun t => fl_rowSampleSketchWithComputedDen fp A den samples t j)
      (fun t => fl_rowSampleSketchWithComputedDen fp A den samples t k)

-- ============================================================
-- Marginals of the independent row trace product law
-- ============================================================

/-- Under the independent product row-trace law, a function of one sampled row
    has expectation equal to its one-step row expectation. -/
theorem rowSqNormTraceProbMass_marginal_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0)
    (t0 : Fin steps) (f : Fin m → ℝ) :
    (∑ samples : RowTrace m steps,
      rowSqNormTraceProbMass A samples * f (samples t0)) =
      ∑ i : Fin m, rowSqNormProb A i * f i := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun t x =>
        if t = t0 then rowSqNormProb A x * f x else rowSqNormProb A x)
  have hleft :
      (∏ t : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          (if t = t0 then rowSqNormProb A x * f x else rowSqNormProb A x)) =
        ∑ i : Fin m, rowSqNormProb A i * f i := by
    simp [rowSqNormProb_sum_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ i, (if i = t0 then rowSqNormProb A (x i) * f (x i)
          else rowSqNormProb A (x i)))
        = ∑ samples : RowTrace m steps,
          rowSqNormTraceProbMass A samples * f (samples t0) := by
    simp [rowSqNormTraceProbMass, RowTrace]
    apply Finset.sum_congr rfl
    intro x _
    have h1 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps =>
        if i = t0 then rowSqNormProb A (x i) * f (x i)
        else rowSqNormProb A (x i))
      (by intro h; simp at h)
    have h2 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps => rowSqNormProb A (x i))
      (by intro h; simp at h)
    simp at h1 h2
    rw [h1, h2]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t0},
          (if x_1 = t0 then rowSqNormProb A (x x_1) * f (x x_1)
          else rowSqNormProb A (x x_1))) =
        ∏ x_1 ∈ Finset.univ \ {t0}, rowSqNormProb A (x x_1) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hi_ne : i ≠ t0 := by
        simp at hi
        exact hi
      simp [hi_ne]
    rw [herase]
    ring
  rw [← hright, ← hprod]
  exact hleft

/-- Product-law pointwise factorization for two distinct trace coordinates. -/
private theorem rowSqNormTraceProbMass_two_point_factor
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (t u : Fin steps) (htu : t ≠ u) (f g : Fin m → ℝ)
    (x : RowTrace m steps) :
    (∏ r : Fin steps,
      if r = t then rowSqNormProb A (x r) * f (x r)
      else if r = u then rowSqNormProb A (x r) * g (x r)
      else rowSqNormProb A (x r)) =
    (∏ r : Fin steps, rowSqNormProb A (x r)) * f (x t) * g (x u) := by
  classical
  have hfactor : ∀ r : Fin steps,
      (if r = t then rowSqNormProb A (x r) * f (x r)
      else if r = u then rowSqNormProb A (x r) * g (x r)
      else rowSqNormProb A (x r)) =
      rowSqNormProb A (x r) *
        (if r = t then f (x r) else if r = u then g (x r) else 1) := by
    intro r
    by_cases hrt : r = t
    · simp [hrt]
    · by_cases hru : r = u
      · simp [hru]
      · simp [hru]
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib]
  have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
    (s := (Finset.univ : Finset (Fin steps))) t
    (fun r : Fin steps =>
      if r = t then f (x r) else if r = u then g (x r) else 1)
    (by intro h; simp at h)
  simp at hprod_t
  have hfac :
      (∏ x_1 : Fin steps,
        if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1) else 1)
      = f (x t) * g (x u) := by
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1)
          else 1) = g (x u) := by
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then f (x r) else if r = u then g (x r) else 1)
        (by
          intro hu_notin
          have : u ∈ (Finset.univ : Finset (Fin steps)).erase t := by
            simp [htu.symm]
          exact False.elim (hu_notin this))
      simp [htu.symm] at hprod_u
      rw [Finset.sdiff_singleton_eq_erase]
      rw [hprod_u]
      have hrest :
          (∏ x_1 ∈ (Finset.univ : Finset (Fin steps)).erase t \ {u},
            if x_1 = t then f (x x_1) else if x_1 = u then g (x x_1)
            else 1) = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        have hrt : r ≠ t := by
          simp at hr
          exact hr.1
        have hru : r ≠ u := by
          simp at hr
          exact hr.2
        simp [hrt, hru]
      rw [hrest]
      ring
    rw [herase]
  rw [hfac]
  ring

/-- Two distinct coordinates of the independent trace have product
    expectation equal to the product of their one-step expectations. -/
theorem rowSqNormTraceProbMass_marginal_two_ne {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : rowSqNormProbDen A ≠ 0)
    (t u : Fin steps) (htu : t ≠ u) (f g : Fin m → ℝ) :
    (∑ samples : RowTrace m steps,
      rowSqNormTraceProbMass A samples *
        (f (samples t) * g (samples u))) =
      (∑ i : Fin m, rowSqNormProb A i * f i) *
      (∑ i : Fin m, rowSqNormProb A i * g i) := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (RowSample m)))
      (f := fun r x =>
        if r = t then rowSqNormProb A x * f x
        else if r = u then rowSqNormProb A x * g x
        else rowSqNormProb A x)
  have hleft :
      (∏ r : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (RowSample m)),
          (if r = t then rowSqNormProb A x * f x
          else if r = u then rowSqNormProb A x * g x
          else rowSqNormProb A x)) =
      (∑ i : Fin m, rowSqNormProb A i * f i) *
      (∑ i : Fin m, rowSqNormProb A i * g i) := by
    simp [rowSqNormProb_sum_eq_one A hden]
    have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t
      (fun r : Fin steps =>
        if r = t then ∑ x : RowSample m, rowSqNormProb A x * f x
        else if r = u then ∑ x : RowSample m, rowSqNormProb A x * g x
        else 1)
      (by intro h; simp at h)
    simp at hprod_t
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then ∑ x : RowSample m, rowSqNormProb A x * f x
          else if x_1 = u then ∑ x : RowSample m, rowSqNormProb A x * g x
          else 1) = ∑ x : RowSample m, rowSqNormProb A x * g x := by
      rw [Finset.sdiff_singleton_eq_erase]
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then ∑ x : RowSample m, rowSqNormProb A x * f x
          else if r = u then ∑ x : RowSample m, rowSqNormProb A x * g x
          else 1)
        (by
          intro hu_notin
          have : u ∈ (Finset.univ : Finset (Fin steps)).erase t := by
            simp [htu.symm]
          exact False.elim (hu_notin this))
      simp [htu.symm] at hprod_u
      rw [hprod_u]
      have hrest :
          (∏ x_1 ∈ (Finset.univ : Finset (Fin steps)).erase t \ {u},
            if x_1 = t then ∑ x : RowSample m, rowSqNormProb A x * f x
            else if x_1 = u then ∑ x : RowSample m, rowSqNormProb A x * g x
            else 1) = 1 := by
        apply Finset.prod_eq_one
        intro r hr
        have hrt : r ≠ t := by
          simp at hr
          exact hr.1
        have hru : r ≠ u := by
          simp at hr
          exact hr.2
        simp [hrt, hru]
      rw [hrest]
      ring
    rw [herase]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (RowSample m))),
        ∏ r, (if r = t then rowSqNormProb A (x r) * f (x r)
          else if r = u then rowSqNormProb A (x r) * g (x r)
          else rowSqNormProb A (x r)))
        = ∑ samples : RowTrace m steps,
          rowSqNormTraceProbMass A samples *
            (f (samples t) * g (samples u)) := by
    simp [rowSqNormTraceProbMass, RowTrace]
    apply Finset.sum_congr rfl
    intro x _
    simpa [mul_assoc] using
      rowSqNormTraceProbMass_two_point_factor A t u htu f g x
  rw [← hright, ← hprod]
  exact hleft

-- ============================================================
-- Unbiasedness of the sampled Gram matrix
-- ============================================================

/-- One-step cancellation for a row-sampled Gram entry. Rows with zero sampling
    probability are zero rows, so the identity also covers the zero-probability
    case without an extra support predicate. -/
theorem rowSqNormProb_mul_rowSampleIncrement_mul_eq {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (i : Fin m) (j k : Fin n) :
    rowSqNormProb A i *
      (rowSampleIncrement s A i j * rowSampleIncrement s A i k) =
      (A i j * A i k) / (s : ℝ) := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [hpzero, hij, hik]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hp_ne : rowSqNormProb A i ≠ 0 := ne_of_gt hp_pos
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hmul_nonneg : 0 ≤ (s : ℝ) * rowSqNormProb A i :=
      mul_nonneg (le_of_lt hs) hp_nonneg
    have hscale_sq : rowSampleScaleDen s A i * rowSampleScaleDen s A i =
        (s : ℝ) * rowSqNormProb A i := by
      unfold rowSampleScaleDen
      exact Real.mul_self_sqrt hmul_nonneg
    unfold rowSampleIncrement
    field_simp [rowSampleScaleDen_ne_zero s A i hs hp_pos, hp_ne, hs_ne]
    rw [sq, hscale_sq]
    ring

/-- Elementwise unbiasedness of Algorithm 2's Gram estimator with the
    norm-squared row distribution of equation (4):
    `E[(ÃᵀÃ)_{jk}] = (AᵀA)_{jk}`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_entry
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (j k : Fin n) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => rowSampleGram s A samples j k) =
      rowGram A j k := by
  classical
  unfold rowSampleGram rowGram
  rw [FiniteProbability.expectationReal_sum]
  calc
    (∑ t : Fin s,
      (rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun ω => rowSampleSketch s A ω t j * rowSampleSketch s A ω t k))
        = ∑ t : Fin s,
            ∑ i : Fin m, rowSqNormProb A i *
              (rowSampleIncrement s A i j * rowSampleIncrement s A i k) := by
          apply Finset.sum_congr rfl
          intro t _
          unfold FiniteProbability.expectationReal rowSqNormTraceProbability
            rowSampleSketch
          exact rowSqNormTraceProbMass_marginal_one A hden.ne' t
            (fun i => rowSampleIncrement s A i j * rowSampleIncrement s A i k)
    _ = ∑ t : Fin s, ∑ i : Fin m, (A i j * A i k) / (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro t _
          apply Finset.sum_congr rfl
          intro i _
          exact rowSqNormProb_mul_rowSampleIncrement_mul_eq s A hden hs i j k
    _ = ∑ i : Fin m, A i j * A i k := by
          rw [Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          field_simp [ne_of_gt hs]

-- ============================================================
-- Scalar second-moment kernel for independent row traces
-- ============================================================

/-- For any scalar quantity attached to a sampled row, the centered sum over an
    independent row trace has second moment `s` times the one-step centered
    second moment. This is the finite iid variance calculation used in the
    proof of the Algorithm 2 Frobenius estimate. -/
theorem rowSqNormTraceProbability_expectationReal_centered_sum_sq
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (f : Fin m → ℝ) :
    let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2) =
      (s : ℝ) * ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
  classical
  let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
  have hcenter : ∑ i : Fin m, rowSqNormProb A i * (f i - μ) = 0 := by
    unfold μ
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [rowSqNormProb_sum_eq_one A hden.ne']
    ring
  have hsame : ∀ t : Fin s,
      (rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => (f (samples t) - μ) * (f (samples t) - μ)) =
        ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
    intro t
    unfold FiniteProbability.expectationReal rowSqNormTraceProbability
    calc
      ∑ samples : RowTrace m s,
          rowSqNormTraceProbMass A samples *
            ((f (samples t) - μ) * (f (samples t) - μ))
          = ∑ i : Fin m, rowSqNormProb A i *
              ((f i - μ) * (f i - μ)) :=
            rowSqNormTraceProbMass_marginal_one A hden.ne' t
              (fun i => (f i - μ) * (f i - μ))
      _ = ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
  have hdiff : ∀ t u : Fin s, t ≠ u →
      (rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => (f (samples t) - μ) * (f (samples u) - μ)) = 0 := by
    intro t u htu
    unfold FiniteProbability.expectationReal rowSqNormTraceProbability
    calc
      ∑ samples : RowTrace m s,
          rowSqNormTraceProbMass A samples *
            ((f (samples t) - μ) * (f (samples u) - μ))
          = (∑ i : Fin m, rowSqNormProb A i * (f i - μ)) *
            (∑ i : Fin m, rowSqNormProb A i * (f i - μ)) :=
            rowSqNormTraceProbMass_marginal_two_ne A hden.ne' t u htu
              (fun i => f i - μ) (fun i => f i - μ)
      _ = 0 := by rw [hcenter]; ring
  have hsquare : ∀ samples : RowTrace m s,
      (∑ t : Fin s, (f (samples t) - μ)) ^ 2 =
        ∑ t : Fin s, ∑ u : Fin s,
          (f (samples t) - μ) * (f (samples u) - μ) := by
    intro samples
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
  calc
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2)
        = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
            (fun samples => ∑ t : Fin s, ∑ u : Fin s,
              (f (samples t) - μ) * (f (samples u) - μ)) := by
            congr 1
            ext samples
            exact hsquare samples
    _ = ∑ t : Fin s, ∑ u : Fin s,
          (rowSqNormTraceProbability (steps := s) A hden).expectationReal
            (fun samples => (f (samples t) - μ) * (f (samples u) - μ)) := by
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ t : Fin s, ∑ i : Fin m,
          rowSqNormProb A i * (f i - μ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro t _
            calc
              (∑ u : Fin s,
                (rowSqNormTraceProbability (steps := s) A hden).expectationReal
                  (fun samples =>
                    (f (samples t) - μ) * (f (samples u) - μ)))
                  = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
                      (fun samples =>
                        (f (samples t) - μ) * (f (samples t) - μ)) := by
                    apply Finset.sum_eq_single t
                    · intro u _ hut
                      exact hdiff t u hut.symm
                    · intro ht_not
                      exact False.elim (ht_not (Finset.mem_univ t))
              _ = ∑ i : Fin m,
                    rowSqNormProb A i * (f i - μ) ^ 2 := hsame t
    _ = (s : ℝ) * ∑ i : Fin m,
          rowSqNormProb A i * (f i - μ) ^ 2 := by
            rw [Finset.sum_const]
            simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Sample-average form of the finite iid variance calculation. -/
theorem rowSqNormTraceProbability_expectationReal_sampleAverage_sub_mean_sq
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (f : Fin m → ℝ) :
    let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => ((∑ t : Fin s, f (samples t)) / (s : ℝ) - μ) ^ 2) =
      (1 / (s : ℝ)) *
        ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
  classical
  let μ : ℝ := ∑ i : Fin m, rowSqNormProb A i * f i
  have hcentered :=
    rowSqNormTraceProbability_expectationReal_centered_sum_sq (s := s) A hden f
  have hpoint : ∀ samples : RowTrace m s,
      (∑ t : Fin s, f (samples t)) / (s : ℝ) - μ =
        (∑ t : Fin s, (f (samples t) - μ)) / (s : ℝ) := by
    intro samples
    rw [Finset.sum_sub_distrib, Finset.sum_const]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [ne_of_gt hs]
  calc
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => ((∑ t : Fin s, f (samples t)) / (s : ℝ) - μ) ^ 2)
        = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              ((∑ t : Fin s, (f (samples t) - μ)) / (s : ℝ)) ^ 2) := by
            congr 1
            ext samples
            rw [hpoint samples]
    _ = (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples => (∑ t : Fin s, (f (samples t) - μ)) ^ 2) /
            (s : ℝ) ^ 2 := by
          unfold FiniteProbability.expectationReal
          simp_rw [div_eq_mul_inv]
          calc
            ∑ samples : RowTrace m s,
                (rowSqNormTraceProbability (steps := s) A hden).prob samples *
                  ((∑ t : Fin s, (f (samples t) - μ)) * (s : ℝ)⁻¹) ^ 2
                = ∑ samples : RowTrace m s,
                    ((rowSqNormTraceProbability (steps := s) A hden).prob samples *
                      (∑ t : Fin s, (f (samples t) - μ)) ^ 2) *
                      ((s : ℝ) ^ 2)⁻¹ := by
                    apply Finset.sum_congr rfl
                    intro samples _
                    ring
            _ = (∑ samples : RowTrace m s,
                    (rowSqNormTraceProbability (steps := s) A hden).prob samples *
                      (∑ t : Fin s, (f (samples t) - μ)) ^ 2) *
                    ((s : ℝ) ^ 2)⁻¹ := by
                    rw [Finset.sum_mul]
    _ = ((s : ℝ) * ∑ i : Fin m,
          rowSqNormProb A i * (f i - μ) ^ 2) / (s : ℝ) ^ 2 := by
          rw [hcentered]
    _ = (1 / (s : ℝ)) *
        ∑ i : Fin m, rowSqNormProb A i * (f i - μ) ^ 2 := by
          field_simp [ne_of_gt hs]

/-- Weighted centered second moments are bounded by raw second moments. -/
theorem weighted_centered_sq_le_sq {ι : Type*} [Fintype ι]
    (p f : ι → ℝ) (μ : ℝ) (hsum : ∑ i, p i = 1)
    (hμ : μ = ∑ i, p i * f i) :
    ∑ i, p i * (f i - μ) ^ 2 ≤ ∑ i, p i * f i ^ 2 := by
  classical
  have hidentity : ∑ i, p i * (f i - μ) ^ 2 =
      ∑ i, p i * f i ^ 2 - μ ^ 2 := by
    calc
      ∑ i, p i * (f i - μ) ^ 2
          = ∑ i, (p i * f i ^ 2 - 2 * μ * (p i * f i) + p i * μ ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = ∑ i, p i * f i ^ 2 - 2 * μ * (∑ i, p i * f i) +
            μ ^ 2 * (∑ i, p i) := by
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              rw [← Finset.mul_sum]
              have hsum_mu : (∑ x : ι, p x * μ ^ 2) =
                  (∑ x : ι, p x) * μ ^ 2 := by
                rw [Finset.sum_mul]
              rw [hsum_mu]
              ring
      _ = ∑ i, p i * f i ^ 2 - μ ^ 2 := by
              rw [← hμ, hsum]
              ring
  rw [hidentity]
  nlinarith [sq_nonneg μ]

-- ============================================================
-- Row-outer-product specialization of the variance kernel
-- ============================================================

/-- One unscaled row outer-product estimator for a Gram entry:
    `Aᵢⱼ Aᵢₖ / pᵢ`. Its one-step expectation is `(AᵀA)ⱼₖ`. -/
noncomputable def rowOuterGramSample {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j k : Fin n) : ℝ :=
  (A i j * A i k) / rowSqNormProb A i

/-- If a row has zero sampling probability, then its row outer-product
    estimator is the zero matrix. -/
theorem rowOuterGramSample_eq_zero_of_prob_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (hpzero : rowSqNormProb A i = 0) :
    rowOuterGramSample A i = fun _j _k : Fin n => 0 := by
  ext j k
  have hrowzero : rowNormSq A i = 0 := by
    unfold rowSqNormProb at hpzero
    rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
    · exact hrow
    · exact False.elim (hden.ne' hdenzero)
  have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
  have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
  simp [rowOuterGramSample, hpzero, hij, hik]

/-- Quadratic form of one row outer-product estimator.  On positive-probability
    rows it is the squared row/vector inner product divided by the sampling
    probability. -/
theorem finiteQuadraticForm_rowOuterGramSample_eq_sq_div {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m)
    (hprob : 0 < rowSqNormProb A i) (x : Fin n → ℝ) :
    finiteQuadraticForm (fun j k : Fin n => rowOuterGramSample A i j k) x =
      (∑ j : Fin n, A i j * x j) ^ 2 / rowSqNormProb A i := by
  classical
  have hp_ne : rowSqNormProb A i ≠ 0 := ne_of_gt hprob
  unfold finiteQuadraticForm finiteMatVec rowOuterGramSample
  simp_rw [div_eq_mul_inv]
  calc
    ∑ j : Fin n,
        x j *
          (∑ k : Fin n, (A i j * A i k) * (rowSqNormProb A i)⁻¹ * x k)
        =
      ∑ j : Fin n,
        x j * (A i j * (rowSqNormProb A i)⁻¹ *
          ∑ k : Fin n, A i k * x k) := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ =
      (∑ j : Fin n, A i j * x j) *
        ((rowSqNormProb A i)⁻¹ * ∑ k : Fin n, A i k * x k) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = (∑ j : Fin n, A i j * x j) ^ 2 *
        (rowSqNormProb A i)⁻¹ := by ring
    _ = (∑ j : Fin n, A i j * x j) ^ 2 / rowSqNormProb A i := by
          rw [div_eq_mul_inv]

/-- A one-step row outer-product estimator is positive semidefinite. -/
theorem finitePSD_rowOuterGramSample {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) :
    finitePSD (fun j k : Fin n => rowOuterGramSample A i j k) := by
  classical
  intro x
  by_cases hpzero : rowSqNormProb A i = 0
  · have hzero := rowOuterGramSample_eq_zero_of_prob_zero A hden i hpzero
    simp [finiteQuadraticForm, finiteMatVec, hzero]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hprob : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    rw [finiteQuadraticForm_rowOuterGramSample_eq_sq_div A i hprob x]
    exact div_nonneg (sq_nonneg _) hp_nonneg

/-- The probability weight cancels the `1 / pᵢ` in a row outer-product
    estimator. The zero-probability case is covered because `pᵢ = 0` implies
    row `i` is zero. -/
theorem rowSqNormProb_mul_rowOuterGramSample_eq {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (j k : Fin n) :
    rowSqNormProb A i * rowOuterGramSample A i j k = A i j * A i k := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [rowOuterGramSample, hpzero, hij, hik]
  · unfold rowOuterGramSample
    field_simp [hpzero]

/-- One-step unbiasedness of the row outer-product estimator for a Gram entry. -/
theorem rowOuterGramSample_mean_eq_rowGram {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (j k : Fin n) :
    ∑ i : Fin m, rowSqNormProb A i * rowOuterGramSample A i j k =
      rowGram A j k := by
  unfold rowGram
  apply Finset.sum_congr rfl
  intro i _
  exact rowSqNormProb_mul_rowOuterGramSample_eq A hden i j k

/-- The scaled sketch-row product is the sample-average contribution of the
    unscaled row outer-product estimator. -/
theorem rowSampleIncrement_mul_eq_rowOuterGramSample_div {m n : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (i : Fin m) (j k : Fin n) :
    rowSampleIncrement s A i j * rowSampleIncrement s A i k =
      rowOuterGramSample A i j k / (s : ℝ) := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [rowSampleIncrement, rowOuterGramSample, hpzero, hij, hik]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hp_ne : rowSqNormProb A i ≠ 0 := ne_of_gt hp_pos
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hmul_nonneg : 0 ≤ (s : ℝ) * rowSqNormProb A i :=
      mul_nonneg (le_of_lt hs) hp_nonneg
    have hscale_sq : rowSampleScaleDen s A i * rowSampleScaleDen s A i =
        (s : ℝ) * rowSqNormProb A i := by
      unfold rowSampleScaleDen
      exact Real.mul_self_sqrt hmul_nonneg
    unfold rowSampleIncrement rowOuterGramSample
    field_simp [rowSampleScaleDen_ne_zero s A i hs hp_pos, hp_ne, hs_ne]
    rw [sq, hscale_sq]
    ring

/-- Each sampled Gram entry is the average of iid row outer-product
    estimators. -/
theorem rowSampleGram_eq_rowOuterGramSample_average {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s) (j k : Fin n) :
    rowSampleGram s A samples j k =
      (∑ t : Fin s, rowOuterGramSample A (samples t) j k) / (s : ℝ) := by
  unfold rowSampleGram rowSampleSketch
  calc
    ∑ t : Fin s,
        rowSampleIncrement s A (samples t) j *
          rowSampleIncrement s A (samples t) k
        = ∑ t : Fin s,
            rowOuterGramSample A (samples t) j k / (s : ℝ) := by
          apply Finset.sum_congr rfl
          intro t _
          exact rowSampleIncrement_mul_eq_rowOuterGramSample_div
            s A hden hs (samples t) j k
    _ = (∑ t : Fin s, rowOuterGramSample A (samples t) j k) / (s : ℝ) := by
          simp_rw [div_eq_mul_inv]
          rw [Finset.sum_mul]

/-- The sampled Gram error against the identity is the average of the centered
row outer-product estimators. -/
theorem rowSampleGram_sub_finiteIdMatrix_eq_centered_rowOuterGramSample_average
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (samples : RowTrace m s) (j k : Fin n) :
    rowSampleGram s A samples j k - finiteIdMatrix j k =
      (∑ t : Fin s,
        (rowOuterGramSample A (samples t) j k - finiteIdMatrix j k)) /
          (s : ℝ) := by
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  rw [rowSampleGram_eq_rowOuterGramSample_average A hden hs samples j k]
  calc
    (∑ t : Fin s, rowOuterGramSample A (samples t) j k) / (s : ℝ) -
        finiteIdMatrix j k =
      ((∑ t : Fin s, rowOuterGramSample A (samples t) j k) -
          (s : ℝ) * finiteIdMatrix j k) / (s : ℝ) := by
        field_simp [hs_ne]
    _ =
      ((∑ t : Fin s, rowOuterGramSample A (samples t) j k) -
          (∑ _t : Fin s, finiteIdMatrix j k)) / (s : ℝ) := by
        simp
    _ =
      (∑ t : Fin s,
        (rowOuterGramSample A (samples t) j k - finiteIdMatrix j k)) /
          (s : ℝ) := by
        rw [Finset.sum_sub_distrib]

/-- Coordinate second-moment formula for the Algorithm 2 Gram estimator. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_entry_error_sq
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (j k : Fin n) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples => (rowSampleGram s A samples j k - rowGram A j k) ^ 2) =
      (1 / (s : ℝ)) *
        ∑ i : Fin m, rowSqNormProb A i *
          (rowOuterGramSample A i j k - rowGram A j k) ^ 2 := by
  classical
  have hvar :=
    rowSqNormTraceProbability_expectationReal_sampleAverage_sub_mean_sq
      (s := s) A hden hs (fun i => rowOuterGramSample A i j k)
  have hmean := rowOuterGramSample_mean_eq_rowGram A hden j k
  simpa [rowSampleGram_eq_rowOuterGramSample_average A hden hs,
    hmean] using hvar

/-- Pair-expansion of the squared row norm. -/
theorem rowNormSq_sq_eq_sum_pair {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) :
    rowNormSq A i ^ 2 =
      ∑ j : Fin n, ∑ k : Fin n, A i j ^ 2 * A i k ^ 2 := by
  unfold rowNormSq
  rw [sq, Finset.sum_mul]
  simp_rw [Finset.mul_sum]

/-- Raw second moment of one row outer-product estimator. -/
theorem rowOuterGramSample_row_second_moment {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) :
    ∑ j : Fin n, ∑ k : Fin n,
      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 =
      rowSqNormProbDen A * rowNormSq A i := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    simp [hpzero, hrowzero]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq A i := by
      unfold rowSqNormProb at hp_pos
      exact (div_pos_iff_of_pos_right hden).mp hp_pos
    have hrow_ne : rowNormSq A i ≠ 0 := ne_of_gt hrow_pos
    have hp_eq : rowSqNormProb A i =
        rowNormSq A i / rowSqNormProbDen A := rfl
    have hpair := rowNormSq_sq_eq_sum_pair A i
    calc
      ∑ j : Fin n, ∑ k : Fin n,
        rowSqNormProb A i * rowOuterGramSample A i j k ^ 2
          = ∑ j : Fin n, ∑ k : Fin n,
              (A i j ^ 2 * A i k ^ 2) / rowSqNormProb A i := by
              apply Finset.sum_congr rfl
              intro j _
              apply Finset.sum_congr rfl
              intro k _
              unfold rowOuterGramSample
              field_simp [hpzero]
      _ = (∑ j : Fin n, ∑ k : Fin n, A i j ^ 2 * A i k ^ 2) /
            rowSqNormProb A i := by
              simp_rw [div_eq_mul_inv]
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.sum_mul]
      _ = rowNormSq A i ^ 2 / rowSqNormProb A i := by rw [← hpair]
      _ = rowSqNormProbDen A * rowNormSq A i := by
              rw [hp_eq]
              field_simp [hrow_ne, hden.ne']

/-- Total raw second moment of the row outer-product estimator. -/
theorem rowOuterGramSample_total_second_moment {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A) :
    ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 =
      rowSqNormProbDen A ^ 2 := by
  classical
  calc
    ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2
        = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
            rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
            calc
              ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
                rowSqNormProb A i * rowOuterGramSample A i j k ^ 2
                  = ∑ j : Fin n, ∑ i : Fin m, ∑ k : Fin n,
                      rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
                      apply Finset.sum_congr rfl
                      intro j _
                      rw [Finset.sum_comm]
              _ = ∑ i : Fin m, ∑ j : Fin n, ∑ k : Fin n,
                    rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
                    rw [Finset.sum_comm]
    _ = ∑ i : Fin m, rowSqNormProbDen A * rowNormSq A i := by
            apply Finset.sum_congr rfl
            intro i _
            exact rowOuterGramSample_row_second_moment A hden i
    _ = rowSqNormProbDen A * ∑ i : Fin m, rowNormSq A i := by
            rw [Finset.mul_sum]
    _ = rowSqNormProbDen A ^ 2 := by
            rw [rowNormSq_sum_eq_frobNormSqRect A]
            unfold rowSqNormProbDen
            ring

/-- Squared-Frobenius second-moment form of equation (5):
    `E ||ÃᵀÃ - AᵀA||_F² ≤ ||A||_F⁴ / s`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ)) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNormSq (fun j k => rowSampleGram s A samples j k - rowGram A j k)) ≤
      rowSqNormProbDen A ^ 2 / (s : ℝ) := by
  classical
  have hcoord := fun j k =>
    rowSqNormTraceProbability_expectationReal_rowSampleGram_entry_error_sq
      A hden hs j k
  have hcenter_le : ∀ j k : Fin n,
      ∑ i : Fin m, rowSqNormProb A i *
          (rowOuterGramSample A i j k - rowGram A j k) ^ 2 ≤
        ∑ i : Fin m, rowSqNormProb A i *
          rowOuterGramSample A i j k ^ 2 := by
    intro j k
    exact weighted_centered_sq_le_sq
      (fun i : Fin m => rowSqNormProb A i)
      (fun i : Fin m => rowOuterGramSample A i j k)
      (rowGram A j k)
      (rowSqNormProb_sum_eq_one A hden.ne')
      (rowOuterGramSample_mean_eq_rowGram A hden j k).symm
  calc
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNormSq (fun j k => rowSampleGram s A samples j k - rowGram A j k))
        = ∑ j : Fin n, ∑ k : Fin n,
            (rowSqNormTraceProbability (steps := s) A hden).expectationReal
              (fun samples =>
                (rowSampleGram s A samples j k - rowGram A j k) ^ 2) := by
            unfold frobNormSq
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ j : Fin n, ∑ k : Fin n,
          (1 / (s : ℝ)) *
            ∑ i : Fin m, rowSqNormProb A i *
              (rowOuterGramSample A i j k - rowGram A j k) ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            exact hcoord j k
    _ ≤ ∑ j : Fin n, ∑ k : Fin n,
          (1 / (s : ℝ)) *
            ∑ i : Fin m, rowSqNormProb A i *
              rowOuterGramSample A i j k ^ 2 := by
            apply Finset.sum_le_sum
            intro j _
            apply Finset.sum_le_sum
            intro k _
            exact mul_le_mul_of_nonneg_left (hcenter_le j k)
              (by positivity)
    _ = (1 / (s : ℝ)) *
          ∑ j : Fin n, ∑ k : Fin n, ∑ i : Fin m,
            rowSqNormProb A i * rowOuterGramSample A i j k ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
    _ = rowSqNormProbDen A ^ 2 / (s : ℝ) := by
            rw [rowOuterGramSample_total_second_moment A hden]
            ring

/-- Equation (5) in expectation for norm-squared row sampling:
    `E ||ÃᵀÃ - AᵀA||_F ≤ ||A||_F² / sqrt(s)`.  In this development
    `rowSqNormProbDen A` is `||A||_F²`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ)) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k)) ≤
      (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Z : RowTrace m s → ℝ := fun samples =>
    frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k)
  have hZ_nonneg : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact frobNorm_nonneg _
  have hjensen := FiniteProbability.expectationReal_le_sqrt_expectationReal_sq
    P Z hZ_nonneg
  have hZsq :
      P.expectationReal (fun samples => Z samples ^ 2) =
        P.expectationReal
          (fun samples =>
            frobNormSq
              (fun j k => rowSampleGram s A samples j k - rowGram A j k)) := by
    unfold Z
    congr 1
    ext samples
    exact frobNorm_sq _
  have hsecond :=
    rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
      A hden hs
  have hsqrt_bound :
      Real.sqrt (P.expectationReal (fun samples => Z samples ^ 2)) ≤
        Real.sqrt (rowSqNormProbDen A ^ 2 / (s : ℝ)) := by
    apply Real.sqrt_le_sqrt
    rw [hZsq]
    exact hsecond
  have hden_nonneg : 0 ≤ rowSqNormProbDen A := frobNormSqRect_nonneg A
  have hsqrt_eq :
      Real.sqrt (rowSqNormProbDen A ^ 2 / (s : ℝ)) =
        (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A := by
    rw [Real.sqrt_div (sq_nonneg (rowSqNormProbDen A)) (s : ℝ)]
    rw [Real.sqrt_sq hden_nonneg]
    ring
  calc
    P.expectationReal Z
        ≤ Real.sqrt (P.expectationReal (fun samples => Z samples ^ 2)) := hjensen
    _ ≤ Real.sqrt (rowSqNormProbDen A ^ 2 / (s : ℝ)) := hsqrt_bound
    _ = (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A := hsqrt_eq

-- ============================================================
-- Floating-point perturbation of the sampled Gram matrix
-- ============================================================

/-- Deterministic entrywise Gram perturbation from relative entrywise sampled
    sketch errors. If each sampled sketch entry has relative error at most
    `u`, then each Gram entry changes by at most
    `(2u + u²) ∑ₜ |B_{tj}| |B_{tk}|`. -/
theorem rowSampleGram_entry_error_bound_of_entrywise
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j,
      |Bhat t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * u)
    (j k : Fin n) :
    |(∑ t : Fin steps, Bhat t j * Bhat t k) -
      rowSampleGram s A samples j k| ≤
      (2 * u + u ^ 2) *
        ∑ t : Fin steps,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
  classical
  unfold rowSampleGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps,
        (Bhat t j * Bhat t k -
          rowSampleSketch s A samples t j *
            rowSampleSketch s A samples t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k -
              rowSampleSketch s A samples t j *
                rowSampleSketch s A samples t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (2 * u + u ^ 2) *
            (|rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) := by
          apply Finset.sum_le_sum
          intro t _
          let bj := rowSampleSketch s A samples t j
          let bk := rowSampleSketch s A samples t k
          let ej := Bhat t j - bj
          let ek := Bhat t k - bk
          have hj : |ej| ≤ |bj| * u := hentry t j
          have hk : |ek| ≤ |bk| * u := hentry t k
          have hBj : Bhat t j = bj + ej := by
            simp [ej, bj]
          have hBk : Bhat t k = bk + ek := by
            simp [ek, bk]
          have hdecomp :
              Bhat t j * Bhat t k - bj * bk =
                ej * bk + bj * ek + ej * ek := by
            rw [hBj, hBk]
            ring
          have hnonneg_bj : 0 ≤ |bj| := abs_nonneg bj
          have hnonneg_bk : 0 ≤ |bk| := abs_nonneg bk
          have hnonneg_u2 : 0 ≤ u ^ 2 := sq_nonneg u
          calc
            |Bhat t j * Bhat t k - bj * bk|
                = |ej * bk + bj * ek + ej * ek| := by rw [hdecomp]
            _ ≤ |ej * bk| + |bj * ek| + |ej * ek| := by
                exact abs_add_three _ _ _
            _ = |ej| * |bk| + |bj| * |ek| + |ej| * |ek| := by
                rw [abs_mul, abs_mul, abs_mul]
            _ ≤ (|bj| * u) * |bk| + |bj| * (|bk| * u) +
                  (|bj| * u) * (|bk| * u) := by
                gcongr
            _ = (2 * u + u ^ 2) * (|bj| * |bk|) := by ring
    _ = (2 * u + u ^ 2) *
          ∑ t : Fin steps,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k| := by
          rw [Finset.mul_sum]

/-- Frobenius-norm Gram perturbation bound induced by entrywise sampled-sketch
    stability. -/
theorem rowSampleGram_frob_error_bound_of_entrywise
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : RowTrace m steps) (Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j,
      |Bhat t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * u) :
    frobNorm
      (fun j k =>
        rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
      frobNorm
        (fun j k =>
          (2 * u + u ^ 2) *
            ∑ t : Fin steps,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg
    · nlinarith [hu, sq_nonneg u]
    · apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j k
    unfold rowSketchGram
    exact rowSampleGram_entry_error_bound_of_entrywise
      s A samples Bhat u hu hentry j k

/-- Generic deterministic entrywise Gram perturbation from relative row-sketch
    entry errors. If `Bhat` is componentwise within relative error `u` of an
    exact sketch `B`, then each Gram entry changes by at most
    `(2u + u²) ∑ₜ |B_{tj}| |B_{tk}|`. -/
theorem rowSketchGram_entry_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (j k : Fin n) :
    |rowSketchGram Bhat j k - rowSketchGram B j k| ≤
      (2 * u + u ^ 2) *
        ∑ t : Fin steps, |B t j| * |B t k| := by
  classical
  unfold rowSketchGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps, (Bhat t j * Bhat t k - B t j * B t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k - B t j * B t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (2 * u + u ^ 2) * (|B t j| * |B t k|) := by
          apply Finset.sum_le_sum
          intro t _
          let bj := B t j
          let bk := B t k
          let ej := Bhat t j - bj
          let ek := Bhat t k - bk
          have hj : |ej| ≤ |bj| * u := hentry t j
          have hk : |ek| ≤ |bk| * u := hentry t k
          have hBj : Bhat t j = bj + ej := by
            simp [ej, bj]
          have hBk : Bhat t k = bk + ek := by
            simp [ek, bk]
          have hdecomp :
              Bhat t j * Bhat t k - bj * bk =
                ej * bk + bj * ek + ej * ek := by
            rw [hBj, hBk]
            ring
          calc
            |Bhat t j * Bhat t k - bj * bk|
                = |ej * bk + bj * ek + ej * ek| := by rw [hdecomp]
            _ ≤ |ej * bk| + |bj * ek| + |ej * ek| := by
                exact abs_add_three _ _ _
            _ = |ej| * |bk| + |bj| * |ek| + |ej| * |ek| := by
                rw [abs_mul, abs_mul, abs_mul]
            _ ≤ (|bj| * u) * |bk| + |bj| * (|bk| * u) +
                  (|bj| * u) * (|bk| * u) := by
                gcongr
            _ = (2 * u + u ^ 2) * (|bj| * |bk|) := by ring
    _ = (2 * u + u ^ 2) *
          ∑ t : Fin steps, |B t j| * |B t k| := by
          rw [Finset.mul_sum]

/-- Generic Frobenius-norm Gram perturbation bound induced by componentwise
    relative stability of an arbitrary row sketch. -/
theorem rowSketchGram_frob_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u) :
    frobNorm
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      frobNorm
        (fun j k =>
          (2 * u + u ^ 2) *
            ∑ t : Fin steps, |B t j| * |B t k|) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg
    · nlinarith [hu, sq_nonneg u]
    · apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j k
    exact rowSketchGram_entry_error_bound_of_entrywise
      B Bhat u hu hentry j k

/-- Generic deterministic entrywise Gram perturbation from absolute row-sketch
    entry errors.  If `Bhat` is within an absolute error matrix `E` of `B`,
    then the Gram perturbation is bounded by the visible mixed exact/computed
    row products. -/
theorem rowSketchGram_entry_abs_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (_hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (j k : Fin n) :
    |rowSketchGram Bhat j k - rowSketchGram B j k| ≤
      ∑ t : Fin steps,
        (E t j * |Bhat t k| + |B t j| * E t k) := by
  classical
  unfold rowSketchGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps, (Bhat t j * Bhat t k - B t j * B t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k - B t j * B t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (E t j * |Bhat t k| + |B t j| * E t k) := by
          apply Finset.sum_le_sum
          intro t _
          let ej := Bhat t j - B t j
          let ek := Bhat t k - B t k
          have hj : |ej| ≤ E t j := hentry t j
          have hk : |ek| ≤ E t k := hentry t k
          have hBj : Bhat t j = B t j + ej := by
            simp [ej]
          have hBk : Bhat t k = B t k + ek := by
            simp [ek]
          have hdecomp :
              Bhat t j * Bhat t k - B t j * B t k =
                ej * Bhat t k + B t j * ek := by
            rw [hBj, hBk]
            ring
          calc
            |Bhat t j * Bhat t k - B t j * B t k|
                = |ej * Bhat t k + B t j * ek| := by rw [hdecomp]
            _ ≤ |ej * Bhat t k| + |B t j * ek| := abs_add_le _ _
            _ = |ej| * |Bhat t k| + |B t j| * |ek| := by
                rw [abs_mul, abs_mul]
            _ ≤ E t j * |Bhat t k| + |B t j| * E t k := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hj (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left hk (abs_nonneg _))

/-- Frobenius-norm Gram perturbation bound induced by absolute entrywise
    row-sketch errors. -/
theorem rowSketchGram_frob_abs_error_bound_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      frobNorm
        (fun j k =>
          ∑ t : Fin steps,
            (E t j * |Bhat t k| + |B t j| * E t k)) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply Finset.sum_nonneg
    intro t _
    exact add_nonneg
      (mul_nonneg (hE_nonneg t j) (abs_nonneg _))
      (mul_nonneg (abs_nonneg _) (hE_nonneg t k))
  · intro j k
    exact rowSketchGram_entry_abs_error_bound_of_entrywise
      B Bhat E hE_nonneg hentry j k

/-- A componentwise relative perturbation bounds the absolute value of each
    perturbed sketch entry. -/
theorem rowSketch_abs_perturbed_le
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (_hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (t : Fin steps) (j : Fin n) :
    |Bhat t j| ≤ (1 + u) * |B t j| := by
  calc
    |Bhat t j|
        = |(Bhat t j - B t j) + B t j| := by
            congr 1
            ring
    _ ≤ |Bhat t j - B t j| + |B t j| := abs_add_le _ _
    _ ≤ |B t j| * u + |B t j| := by
            exact add_le_add (hentry t j) le_rfl
    _ = (1 + u) * |B t j| := by ring

/-- Product form of `rowSketch_abs_perturbed_le`. -/
theorem rowSketch_abs_perturbed_mul_le
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (t : Fin steps) (j k : Fin n) :
    |Bhat t j| * |Bhat t k| ≤
      (1 + u) ^ 2 * (|B t j| * |B t k|) := by
  have hj := rowSketch_abs_perturbed_le B Bhat u hu hentry t j
  have hk := rowSketch_abs_perturbed_le B Bhat u hu hentry t k
  have hfac_nonneg : 0 ≤ 1 + u := by linarith
  have hbj_nonneg : 0 ≤ (1 + u) * |B t j| :=
    mul_nonneg hfac_nonneg (abs_nonneg _)
  calc
    |Bhat t j| * |Bhat t k|
        ≤ ((1 + u) * |B t j|) * ((1 + u) * |B t k|) := by
            exact mul_le_mul hj hk (abs_nonneg _) hbj_nonneg
    _ = (1 + u) ^ 2 * (|B t j| * |B t k|) := by ring

/-- Sum form of `rowSketch_abs_perturbed_mul_le`. -/
theorem rowSketch_abs_perturbed_mul_sum_le
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u)
    (j k : Fin n) :
    (∑ t : Fin steps, |Bhat t j| * |Bhat t k|) ≤
      (1 + u) ^ 2 * ∑ t : Fin steps, |B t j| * |B t k| := by
  calc
    (∑ t : Fin steps, |Bhat t j| * |Bhat t k|)
        ≤ ∑ t : Fin steps,
            (1 + u) ^ 2 * (|B t j| * |B t k|) := by
            apply Finset.sum_le_sum
            intro t _
            exact rowSketch_abs_perturbed_mul_le B Bhat u hu hentry t j k
    _ = (1 + u) ^ 2 * ∑ t : Fin steps, |B t j| * |B t k| := by
            rw [Finset.mul_sum]

/-- An absolute entrywise perturbation bounds the absolute value of each
    perturbed sketch entry. -/
theorem rowSketch_abs_perturbed_le_of_abs_error
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (_hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (t : Fin steps) (j : Fin n) :
    |Bhat t j| ≤ |B t j| + E t j := by
  calc
    |Bhat t j|
        = |(Bhat t j - B t j) + B t j| := by
            congr 1
            ring
    _ ≤ |Bhat t j - B t j| + |B t j| := abs_add_le _ _
    _ ≤ E t j + |B t j| := by
            exact add_le_add (hentry t j) le_rfl
    _ = |B t j| + E t j := by ring

/-- Product form of `rowSketch_abs_perturbed_le_of_abs_error`. -/
theorem rowSketch_abs_perturbed_mul_le_of_abs_error
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (t : Fin steps) (j k : Fin n) :
    |Bhat t j| * |Bhat t k| ≤
      (|B t j| + E t j) * (|B t k| + E t k) := by
  have hj :=
    rowSketch_abs_perturbed_le_of_abs_error
      B Bhat E hE_nonneg hentry t j
  have hk :=
    rowSketch_abs_perturbed_le_of_abs_error
      B Bhat E hE_nonneg hentry t k
  have hright_nonneg : 0 ≤ |B t j| + E t j :=
    add_nonneg (abs_nonneg _) (hE_nonneg t j)
  exact mul_le_mul hj hk (abs_nonneg _) hright_nonneg

/-- Sum form of `rowSketch_abs_perturbed_mul_le_of_abs_error`. -/
theorem rowSketch_abs_perturbed_mul_sum_le_of_abs_error
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (j k : Fin n) :
    (∑ t : Fin steps, |Bhat t j| * |Bhat t k|) ≤
      ∑ t : Fin steps,
        (|B t j| + E t j) * (|B t k| + E t k) := by
  apply Finset.sum_le_sum
  intro t _
  exact rowSketch_abs_perturbed_mul_le_of_abs_error
    B Bhat E hE_nonneg hentry t j k

/-- Absolute-entry Gram perturbation bound with no computed-entry term left in
    the right-hand side. -/
theorem rowSketchGram_entry_abs_error_bound_exact_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j)
    (j k : Fin n) :
    |rowSketchGram Bhat j k - rowSketchGram B j k| ≤
      ∑ t : Fin steps,
        (E t j * |B t k| + |B t j| * E t k + E t j * E t k) := by
  classical
  unfold rowSketchGram
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ t : Fin steps, (Bhat t j * Bhat t k - B t j * B t k)|
        ≤ ∑ t : Fin steps,
            |Bhat t j * Bhat t k - B t j * B t k| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : Fin steps,
          (E t j * |B t k| + |B t j| * E t k +
            E t j * E t k) := by
          apply Finset.sum_le_sum
          intro t _
          let ej := Bhat t j - B t j
          let ek := Bhat t k - B t k
          have hj : |ej| ≤ E t j := hentry t j
          have hk : |ek| ≤ E t k := hentry t k
          have hBj : Bhat t j = B t j + ej := by
            simp [ej]
          have hBk : Bhat t k = B t k + ek := by
            simp [ek]
          have hdecomp :
              Bhat t j * Bhat t k - B t j * B t k =
                ej * B t k + B t j * ek + ej * ek := by
            rw [hBj, hBk]
            ring
          have h1 : |ej| * |B t k| ≤ E t j * |B t k| :=
            mul_le_mul_of_nonneg_right hj (abs_nonneg _)
          have h2 : |B t j| * |ek| ≤ |B t j| * E t k :=
            mul_le_mul_of_nonneg_left hk (abs_nonneg _)
          have h3 : |ej| * |ek| ≤ E t j * E t k :=
            mul_le_mul hj hk (abs_nonneg _) (hE_nonneg t j)
          calc
            |Bhat t j * Bhat t k - B t j * B t k|
                = |ej * B t k + B t j * ek + ej * ek| := by
                    rw [hdecomp]
            _ ≤ |ej * B t k| + |B t j * ek| + |ej * ek| := by
                    exact abs_add_three _ _ _
            _ = |ej| * |B t k| + |B t j| * |ek| +
                  |ej| * |ek| := by
                    rw [abs_mul, abs_mul, abs_mul]
            _ ≤ E t j * |B t k| + |B t j| * E t k +
                  E t j * E t k := by
                    linarith

/-- Frobenius-norm Gram perturbation bound from absolute entrywise sketch
    errors, with a right-hand side depending only on the exact sketch and the
    explicit absolute error matrix. -/
theorem rowSketchGram_frob_abs_error_bound_exact_of_entrywise
    {steps n : ℕ} (B Bhat : Fin steps → Fin n → ℝ)
    (E : Fin steps → Fin n → ℝ)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) ≤
      frobNorm
        (fun j k =>
          ∑ t : Fin steps,
            (E t j * |B t k| + |B t j| * E t k +
              E t j * E t k)) := by
  classical
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply Finset.sum_nonneg
    intro t _
    exact add_nonneg
      (add_nonneg
        (mul_nonneg (hE_nonneg t j) (abs_nonneg _))
        (mul_nonneg (abs_nonneg _) (hE_nonneg t k)))
      (mul_nonneg (hE_nonneg t j) (hE_nonneg t k))
  · intro j k
    exact rowSketchGram_entry_abs_error_bound_exact_of_entrywise
      B Bhat E hE_nonneg hentry j k

/-- Fully floating-point Gram of an already-computed row sketch: each entry is
    evaluated with the repository floating-point dot-product algorithm. -/
noncomputable def fl_rowSketchGramDot (fp : FPModel)
    {steps n : ℕ} (Bhat : Fin steps → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun j k =>
    fl_dotProduct fp steps (fun t => Bhat t j) (fun t => Bhat t k)

/-- Exact-only dot-product roundoff budget for a computed row sketch whose
    entries are within the explicit absolute error matrix `E` of `B`. -/
noncomputable def rowSketchGramDotRoundoffExactBudget
    (fp : FPModel) {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      gamma fp steps *
        ∑ t : Fin steps,
          (|B t j| + E t j) * (|B t k| + E t k))

/-- Exact-only sketch-formation perturbation budget for a Gram matrix built
    from a computed row sketch. -/
noncomputable def rowSketchGramAbsPerturbExactBudget
    {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun j k : Fin n =>
      ∑ t : Fin steps,
        (E t j * |B t k| + |B t j| * E t k + E t j * E t k))

/-- Total exact-only floating-point perturbation budget for the Gram of an
    already-computed row sketch.  The first term charges rounded dot products;
    the second charges the perturbation from exact sketch `B` to computed
    sketch `Bhat` through its explicit entrywise radius `E`. -/
noncomputable def rowSketchGramFullAbsFpExactBudget
    (fp : FPModel) {steps n : ℕ}
    (B : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ) : ℝ :=
  rowSketchGramDotRoundoffExactBudget fp B E +
    rowSketchGramAbsPerturbExactBudget B E

/-- Dot-product roundoff bound for an already-computed row sketch, stated with
    a right-hand side that depends only on the exact sketch and the explicit
    absolute entrywise error matrix. -/
theorem fl_rowSketchGramDot_roundoff_bound_of_abs_error
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ)
    (hγ : gammaValid fp steps)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) ≤
      rowSketchGramDotRoundoffExactBudget fp B E := by
  classical
  have hγ_nonneg : 0 ≤ gamma fp steps := gamma_nonneg fp hγ
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg hγ_nonneg
    apply Finset.sum_nonneg
    intro t _
    exact mul_nonneg
      (add_nonneg (abs_nonneg _) (hE_nonneg t j))
      (add_nonneg (abs_nonneg _) (hE_nonneg t k))
  · intro j k
    have hdot :=
      dotProduct_error_bound fp steps
        (fun t => Bhat t j) (fun t => Bhat t k) hγ
    have hsum :=
      rowSketch_abs_perturbed_mul_sum_le_of_abs_error
        B Bhat E hE_nonneg hentry j k
    calc
      |fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k|
          ≤ gamma fp steps *
              ∑ t : Fin steps, |Bhat t j| * |Bhat t k| := by
              simpa [fl_rowSketchGramDot, rowSketchGram] using hdot
      _ ≤ gamma fp steps *
            ∑ t : Fin steps,
              (|B t j| + E t j) * (|B t k| + E t k) := by
              exact mul_le_mul_of_nonneg_left hsum hγ_nonneg

/-- Fully floating-point Gram perturbation for an already-computed row sketch,
    with every non-probability computation charged by an explicit exact-only
    budget. -/
theorem fl_rowSketchGramDot_abs_perturb_bound_exact
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ) (E : Fin steps → Fin n → ℝ)
    (hγ : gammaValid fp steps)
    (hE_nonneg : ∀ (t : Fin steps) (j : Fin n), 0 ≤ E t j)
    (hentry : ∀ (t : Fin steps) (j : Fin n),
      |Bhat t j - B t j| ≤ E t j) :
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k) ≤
      rowSketchGramFullAbsFpExactBudget fp B E := by
  classical
  have hdot :=
    fl_rowSketchGramDot_roundoff_bound_of_abs_error
      fp B Bhat E hγ hE_nonneg hentry
  have hsketch :=
    rowSketchGram_frob_abs_error_bound_exact_of_entrywise
      B Bhat E hE_nonneg hentry
  have hsplit :
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k) =
      (fun j k =>
        (fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) +
          (rowSketchGram Bhat j k - rowSketchGram B j k)) := by
    funext j k
    ring
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k)
  calc
    frobNorm
      (fun j k =>
        fl_rowSketchGramDot fp Bhat j k - rowSketchGram B j k)
        =
      frobNorm
        (fun j k =>
          (fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) +
            (rowSketchGram Bhat j k - rowSketchGram B j k)) := by
          rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_rowSketchGramDot fp Bhat j k - rowSketchGram Bhat j k) +
        frobNorm
          (fun j k => rowSketchGram Bhat j k - rowSketchGram B j k) :=
          htri
    _ ≤ rowSketchGramDotRoundoffExactBudget fp B E +
        rowSketchGramAbsPerturbExactBudget B E :=
          add_le_add hdot hsketch
    _ = rowSketchGramFullAbsFpExactBudget fp B E := by
          rfl

/-- Dot-product computation error for the Gram matrix, reusing the library's
    `dotProduct_error_bound`. The only local work here is translating the
    entrywise sketch perturbation into a bound on the dot-product inputs. -/
theorem rowSketchGram_dot_frob_error_bound_of_entrywise
    (fp : FPModel) {steps n : ℕ}
    (B Bhat : Fin steps → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hγ : gammaValid fp steps)
    (hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * u) :
    frobNorm
      (fun j k =>
        fl_dotProduct fp steps (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) ≤
      frobNorm
        (fun j k =>
          gamma fp steps * (1 + u) ^ 2 *
            ∑ t : Fin steps, |B t j| * |B t k|) := by
  classical
  have hγ_nonneg : 0 ≤ gamma fp steps := gamma_nonneg fp hγ
  have hfac_nonneg : 0 ≤ (1 + u) ^ 2 := sq_nonneg (1 + u)
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    apply mul_nonneg
    · exact mul_nonneg hγ_nonneg hfac_nonneg
    · apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · intro j k
    have hdot :=
      dotProduct_error_bound fp steps
        (fun t => Bhat t j) (fun t => Bhat t k) hγ
    have hsum :=
      rowSketch_abs_perturbed_mul_sum_le B Bhat u hu hentry j k
    calc
      |fl_dotProduct fp steps (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k|
          ≤ gamma fp steps *
              ∑ t : Fin steps, |Bhat t j| * |Bhat t k| := by
              simpa [rowSketchGram] using hdot
      _ ≤ gamma fp steps *
            ((1 + u) ^ 2 * ∑ t : Fin steps, |B t j| * |B t k|) := by
              exact mul_le_mul_of_nonneg_left hsum hγ_nonneg
      _ = gamma fp steps * (1 + u) ^ 2 *
            ∑ t : Fin steps, |B t j| * |B t k| := by ring

/-- The row outer-product estimator has magnitude at most `||A||_F²` in each
    entry. -/
theorem abs_rowOuterGramSample_le_den {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (i : Fin m) (j k : Fin n) :
    |rowOuterGramSample A i j k| ≤ rowSqNormProbDen A := by
  classical
  by_cases hpzero : rowSqNormProb A i = 0
  · have hrowzero : rowNormSq A i = 0 := by
      unfold rowSqNormProb at hpzero
      rcases (div_eq_zero_iff.mp hpzero) with hrow | hdenzero
      · exact hrow
      · exact False.elim (hden.ne' hdenzero)
    have hij : A i j = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero j
    have hik : A i k = 0 := (rowNormSq_eq_zero_iff A i).mp hrowzero k
    simp [rowOuterGramSample, hpzero, hij, hik, le_of_lt hden]
  · have hp_nonneg : 0 ≤ rowSqNormProb A i := rowSqNormProb_nonneg A hden i
    have hp_pos : 0 < rowSqNormProb A i :=
      lt_of_le_of_ne hp_nonneg (Ne.symm hpzero)
    have hrow_pos : 0 < rowNormSq A i := by
      unfold rowSqNormProb at hp_pos
      exact (div_pos_iff_of_pos_right hden).mp hp_pos
    have hrow_ne : rowNormSq A i ≠ 0 := ne_of_gt hrow_pos
    have hj_le : A i j ^ 2 ≤ rowNormSq A i := by
      unfold rowNormSq
      exact Finset.single_le_sum
        (fun x _ => sq_nonneg (A i x)) (Finset.mem_univ j)
    have hk_le : A i k ^ 2 ≤ rowNormSq A i := by
      unfold rowNormSq
      exact Finset.single_le_sum
        (fun x _ => sq_nonneg (A i x)) (Finset.mem_univ k)
    have htwo :
        2 * (|A i j| * |A i k|) ≤ A i j ^ 2 + A i k ^ 2 := by
      have hsq : 0 ≤ (|A i j| - |A i k|) ^ 2 := sq_nonneg _
      nlinarith [sq_abs (A i j), sq_abs (A i k)]
    have hsum : A i j ^ 2 + A i k ^ 2 ≤ 2 * rowNormSq A i := by
      nlinarith
    have hprod : |A i j * A i k| ≤ rowNormSq A i := by
      rw [abs_mul]
      nlinarith
    have hp_eq : rowSqNormProb A i =
        rowNormSq A i / rowSqNormProbDen A := rfl
    calc
      |rowOuterGramSample A i j k|
          = |A i j * A i k| / rowSqNormProb A i := by
              unfold rowOuterGramSample
              rw [abs_div, abs_of_nonneg hp_nonneg]
      _ ≤ rowNormSq A i / rowSqNormProb A i := by
              exact div_le_div_of_nonneg_right hprod hp_nonneg
      _ = rowSqNormProbDen A := by
              rw [hp_eq]
              field_simp [hrow_ne, hden.ne']

/-- A single exact sampled-row contribution to `ÃᵀÃ` has absolute product at
    most `||A||_F² / s`. -/
theorem rowSampleSketch_abs_mul_le_den_div_steps {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s)
    (t : Fin s) (j k : Fin n) :
    |rowSampleSketch s A samples t j| *
        |rowSampleSketch s A samples t k| ≤
      rowSqNormProbDen A / (s : ℝ) := by
  classical
  have hprod :=
    rowSampleIncrement_mul_eq_rowOuterGramSample_div
      s A hden hs (samples t) j k
  have habs :
      |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k| =
        |rowOuterGramSample A (samples t) j k| / (s : ℝ) := by
    unfold rowSampleSketch
    rw [← abs_mul, hprod, abs_div, abs_of_nonneg (le_of_lt hs)]
  rw [habs]
  exact div_le_div_of_nonneg_right
    (abs_rowOuterGramSample_le_den A hden (samples t) j k) (le_of_lt hs)

/-- The entrywise absolute-product budget in the sampled Gram perturbation is
    bounded uniformly by `||A||_F²`. -/
theorem rowSampleSketch_abs_mul_sum_le_den {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (hs : 0 < (s : ℝ)) (samples : RowTrace m s)
    (j k : Fin n) :
    (∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|) ≤
      rowSqNormProbDen A := by
  classical
  calc
    (∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|)
        ≤ ∑ _t : Fin s, rowSqNormProbDen A / (s : ℝ) := by
            apply Finset.sum_le_sum
            intro t _
            exact rowSampleSketch_abs_mul_le_den_div_steps
              A hden hs samples t j k
    _ = rowSqNormProbDen A := by
            rw [Finset.sum_const]
            simp
            field_simp [ne_of_gt hs]

/-- Explicit deterministic floating-point Gram perturbation budget for
    Algorithm 2. This is a worst-case bound over the support of the row sampler:
    every Gram entry can change by at most
    `(2u + u²) ||A||_F²`, and the Frobenius norm packages those entrywise
    bounds. -/
noncomputable def rowSampleGramFpPerturbBudget (fp : FPModel)
    {m n : ℕ} (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm (fun _j _k : Fin n => (2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A)

/-- Explicit deterministic budget for computing each already-rounded sampled
    Gram entry with the library dot-product algorithm. -/
noncomputable def rowSampleGramDotProductBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun _j _k : Fin n =>
      gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A)

/-- Closed form of the row-scaling perturbation budget, exposing the implicit
    dependence on the number `n` of columns/Gram rows. -/
theorem rowSampleGramFpPerturbBudget_eq_nat_mul (fp : FPModel)
    {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    rowSampleGramFpPerturbBudget fp A =
      (n : ℝ) * ((2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A) := by
  have hC : 0 ≤ (2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A := by
    have hu : 0 ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hu hden
  unfold rowSampleGramFpPerturbBudget
  exact frobNorm_const hC

/-- Closed form of the dot-product perturbation budget, exposing the implicit
    dependence on the number `n` of columns/Gram rows. -/
theorem rowSampleGramDotProductBudget_eq_nat_mul (fp : FPModel)
    {m n : ℕ} {s : ℕ} (A : Fin m → Fin n → ℝ)
    (hγ : gammaValid fp s) :
    rowSampleGramDotProductBudget fp s A =
      (n : ℝ) *
        (gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A) := by
  have hC :
      0 ≤ gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A := by
    have hleft : 0 ≤ gamma fp s * (1 + fp.u) ^ 2 :=
      mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hleft hden
  unfold rowSampleGramDotProductBudget
  exact frobNorm_const hC

/-- The deterministic Gram perturbation matrix obtained from entrywise sampled
    sketch stability is bounded by the explicit worst-case budget. -/
theorem rowSampleGram_perturb_budget_le_explicit (fp : FPModel)
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        (2 * fp.u + fp.u ^ 2) *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramFpPerturbBudget fp A := by
  classical
  let C : ℝ := 2 * fp.u + fp.u ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [fp.u_nonneg, sq_nonneg fp.u]
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramFpPerturbBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |(2 * fp.u + fp.u ^ 2) * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = (2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A := by
              simp [C]

/-- The dot-product computation budget is uniformly bounded by the explicit
    `rowSampleGramDotProductBudget`. -/
theorem rowSampleGram_dot_product_budget_le_explicit (fp : FPModel)
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) (samples : RowTrace m s) :
    frobNorm
      (fun j k =>
        gamma fp s * (1 + fp.u) ^ 2 *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramDotProductBudget fp s A := by
  classical
  let C : ℝ := gamma fp s * (1 + fp.u) ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + fp.u))
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramDotProductBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |gamma fp s * (1 + fp.u) ^ 2 * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = gamma fp s * (1 + fp.u) ^ 2 * rowSqNormProbDen A := by
              simp [C]

/-- Total deterministic perturbation budget for the fully floating-point Gram:
    rounded row scaling plus rounded dot products for each Gram entry. -/
noncomputable def rowSampleGramFullFpPerturbBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ) : ℝ :=
  rowSampleGramFpPerturbBudget fp A + rowSampleGramDotProductBudget fp s A

/-- Row-scaling Gram perturbation budget for an arbitrary proved relative
    sampled-sketch entry error `uEff`. -/
noncomputable def rowSampleGramRelPerturbBudget {m n : ℕ}
    (uEff : ℝ) (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm (fun _j _k : Fin n => (2 * uEff + uEff ^ 2) * rowSqNormProbDen A)

/-- Dot-product perturbation budget when the already rounded sampled sketch is
    within relative error `uEff` of the exact sampled sketch. -/
noncomputable def rowSampleGramDotProductRelBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (uEff : ℝ) (A : Fin m → Fin n → ℝ) : ℝ :=
  frobNorm
    (fun _j _k : Fin n =>
      gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A)

/-- Fully computed-denominator Algorithm 2 Gram perturbation budget.  The
    effective row error charges denominator computation and final rounded
    division; the dot-product term additionally charges the computed Gram
    entries. -/
noncomputable def rowSampleGramComputedDenFullFpPerturbBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A)) : ℝ :=
  let uEff := rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat
  rowSampleGramRelPerturbBudget uEff A +
    rowSampleGramDotProductRelBudget fp s uEff A

/-- Scaling-only computed-denominator budget, used when the Gram matrix is an
    exact mathematical object formed from the already rounded sketch. -/
noncomputable def rowSampleGramComputedDenScalePerturbBudget (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A)) : ℝ :=
  rowSampleGramRelPerturbBudget
    (rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat) A

/-- The fully floating-point sampled-Gram perturbation budget is nonnegative. -/
theorem rowSampleGramFullFpPerturbBudget_nonneg (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ) :
    0 ≤ rowSampleGramFullFpPerturbBudget fp s A := by
  unfold rowSampleGramFullFpPerturbBudget rowSampleGramFpPerturbBudget
    rowSampleGramDotProductBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

theorem rowSampleGramRelPerturbBudget_nonneg {m n : ℕ}
    (uEff : ℝ) (A : Fin m → Fin n → ℝ) :
    0 ≤ rowSampleGramRelPerturbBudget (m := m) (n := n) uEff A := by
  unfold rowSampleGramRelPerturbBudget
  exact frobNorm_nonneg _

theorem rowSampleGramDotProductRelBudget_nonneg (fp : FPModel)
    {m n : ℕ} (s : ℕ) (uEff : ℝ) (A : Fin m → Fin n → ℝ) :
    0 ≤ rowSampleGramDotProductRelBudget fp s uEff A := by
  unfold rowSampleGramDotProductRelBudget
  exact frobNorm_nonneg _

theorem rowSampleGramComputedDenFullFpPerturbBudget_nonneg (fp : FPModel)
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A)) :
    0 ≤ rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat := by
  unfold rowSampleGramComputedDenFullFpPerturbBudget
  exact add_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- Closed form of the arbitrary-relative-error row-scaling budget. -/
theorem rowSampleGramRelPerturbBudget_eq_nat_mul {m n : ℕ}
    (uEff : ℝ) (A : Fin m → Fin n → ℝ)
    (huEff : 0 ≤ uEff) :
    rowSampleGramRelPerturbBudget (m := m) (n := n) uEff A =
      (n : ℝ) * ((2 * uEff + uEff ^ 2) * rowSqNormProbDen A) := by
  have hC : 0 ≤ (2 * uEff + uEff ^ 2) * rowSqNormProbDen A := by
    have hu : 0 ≤ 2 * uEff + uEff ^ 2 := by
      nlinarith [huEff, sq_nonneg uEff]
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hu hden
  unfold rowSampleGramRelPerturbBudget
  exact frobNorm_const hC

/-- Closed form of the arbitrary-relative-error dot-product budget. -/
theorem rowSampleGramDotProductRelBudget_eq_nat_mul (fp : FPModel)
    {m n : ℕ} {s : ℕ} (uEff : ℝ) (A : Fin m → Fin n → ℝ)
    (hγ : gammaValid fp s) :
    rowSampleGramDotProductRelBudget fp s uEff A =
      (n : ℝ) *
        (gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A) := by
  have hC :
      0 ≤ gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A := by
    have hleft : 0 ≤ gamma fp s * (1 + uEff) ^ 2 :=
      mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + uEff))
    have hden : 0 ≤ rowSqNormProbDen A := by
      unfold rowSqNormProbDen
      exact frobNormSqRect_nonneg A
    exact mul_nonneg hleft hden
  unfold rowSampleGramDotProductRelBudget
  exact frobNorm_const hC

/-- The deterministic Gram perturbation matrix from a relative sampled-sketch
    error `uEff` is bounded by the explicit arbitrary-relative-error budget. -/
theorem rowSampleGram_rel_perturb_budget_le_explicit
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (samples : RowTrace m s) (uEff : ℝ) (huEff : 0 ≤ uEff) :
    frobNorm
      (fun j k =>
        (2 * uEff + uEff ^ 2) *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramRelPerturbBudget uEff A := by
  classical
  let C : ℝ := 2 * uEff + uEff ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    nlinarith [huEff, sq_nonneg uEff]
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramRelPerturbBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |(2 * uEff + uEff ^ 2) * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = (2 * uEff + uEff ^ 2) * rowSqNormProbDen A := by
              simp [C]

/-- The dot-product computation budget under entrywise relative row error
    `uEff` is bounded by the explicit arbitrary-relative-error budget. -/
theorem rowSampleGram_dot_product_rel_budget_le_explicit
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) (samples : RowTrace m s)
    (uEff : ℝ) :
    frobNorm
      (fun j k =>
        gamma fp s * (1 + uEff) ^ 2 *
          ∑ t : Fin s,
            |rowSampleSketch s A samples t j| *
              |rowSampleSketch s A samples t k|) ≤
      rowSampleGramDotProductRelBudget fp s uEff A := by
  classical
  let C : ℝ := gamma fp s * (1 + uEff) ^ 2
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (gamma_nonneg fp hγ) (sq_nonneg (1 + uEff))
  have hD_nonneg : 0 ≤ rowSqNormProbDen A := le_of_lt hden
  unfold rowSampleGramDotProductRelBudget
  apply frobNorm_le_of_entry_abs_le
  · intro j k
    exact mul_nonneg hC_nonneg hD_nonneg
  · intro j k
    have hsum_nonneg :
        0 ≤ ∑ t : Fin s,
          |rowSampleSketch s A samples t j| *
            |rowSampleSketch s A samples t k| := by
      apply Finset.sum_nonneg
      intro t _
      exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsum_le :=
      rowSampleSketch_abs_mul_sum_le_den A hden hs samples j k
    let S : ℝ :=
      ∑ t : Fin s,
        |rowSampleSketch s A samples t j| *
          |rowSampleSketch s A samples t k|
    calc
      |gamma fp s * (1 + uEff) ^ 2 * S|
          = C * S := by
              simp [C, S, abs_of_nonneg (mul_nonneg hC_nonneg hsum_nonneg)]
      _ ≤ C * rowSqNormProbDen A := by
              exact mul_le_mul_of_nonneg_left (by simpa [S] using hsum_le) hC_nonneg
      _ = gamma fp s * (1 + uEff) ^ 2 * rowSqNormProbDen A := by
              simp [C]

/-- Deterministic fully-floating-point Gram perturbation from entrywise sketch
    stability and the library dot-product bound. -/
theorem fl_rowSampleGramDot_perturb_bound_of_entrywise
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s) (samples : RowTrace m s)
    (hentry : ∀ t j,
      |fl_rowSampleSketch fp s A samples t j -
        rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * fp.u) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDot fp s A samples j k -
          rowSampleGram s A samples j k) ≤
      rowSampleGramFullFpPerturbBudget fp s A := by
  classical
  let B : Fin s → Fin n → ℝ := rowSampleSketch s A samples
  let Bhat : Fin s → Fin n → ℝ := fl_rowSampleSketch fp s A samples
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
        rowSampleGramDotProductBudget fp s A := by
    have hlocal :=
      rowSketchGram_dot_frob_error_bound_of_entrywise
        fp B Bhat fp.u fp.u_nonneg hγ (by simpa [B, Bhat] using hentry)
    have hbudget :=
      rowSampleGram_dot_product_budget_le_explicit fp A hden hs hγ samples
    have hlocal' :
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) ≤
          frobNorm
            (fun j k =>
              gamma fp s * (1 + fp.u) ^ 2 *
                ∑ t : Fin s,
                  |rowSampleSketch s A samples t j| *
                    |rowSampleSketch s A samples t k|) := by
      simpa [B, Bhat] using hlocal
    exact hlocal'.trans hbudget
  have hscale :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
        rowSampleGramFpPerturbBudget fp A := by
    have hpoint :=
      rowSampleGram_frob_error_bound_of_entrywise
        s A samples Bhat fp.u fp.u_nonneg
        (by simpa [B, Bhat] using hentry)
    have hbudget :=
      rowSampleGram_perturb_budget_le_explicit fp A hden hs samples
    have hpoint' :
        frobNorm
          (fun j k =>
            rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
          frobNorm
            (fun j k =>
              (2 * fp.u + fp.u ^ 2) *
                ∑ t : Fin s,
                  |rowSampleSketch s A samples t j| *
                    |rowSampleSketch s A samples t k|) := by
      simpa [Bhat] using hpoint
    exact hpoint'.trans hbudget
  have hsplit :
      (fun j k =>
        fl_rowSampleGramDot fp s A samples j k -
          rowSampleGram s A samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
    funext j k
    simp [fl_rowSampleGramDot, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_rowSampleGramDot fp s A samples j k -
          rowSampleGram s A samples j k)
        = frobNorm
          (fun j k =>
            (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
            (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
            rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k) :=
          htri
    _ ≤ rowSampleGramDotProductBudget fp s A +
        rowSampleGramFpPerturbBudget fp A :=
          add_le_add hdot hscale
    _ = rowSampleGramFullFpPerturbBudget fp s A := by
          unfold rowSampleGramFullFpPerturbBudget
          ring

/-- Deterministic Gram perturbation for the computed-denominator Algorithm 2
    path when the Gram matrix is formed exactly from the rounded sampled
    sketch. -/
theorem fl_rowSampleGramWithComputedDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb A samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k) ≤
      rowSampleGramComputedDenScalePerturbBudget fp s A dhat := by
  classical
  let uEff : ℝ :=
    rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat
  have huEff : 0 ≤ uEff :=
    rowScaleComputedDenEffectiveRelError_nonneg fp (rowSqNormProb A) dhat
  let Bhat : Fin s → Fin n → ℝ :=
    fl_rowSampleSketchWithComputedDen fp A dhat.den samples
  have hentry : ∀ t j,
      |Bhat t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * uEff := by
    intro t j
    have hprob : 0 < rowSqNormProb A (samples t) := hgood t
    have h :=
      fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
        fp A (rowSqNormProb A) dhat samples t j hs hprob
    simpa [Bhat, rowSampleSketchWithProb, rowSampleSketch,
      rowSampleIncrementWithProb, rowSampleIncrement,
      rowSampleScaleDenWithProb, rowSampleScaleDen, uEff] using h
  have hpoint :=
    rowSampleGram_frob_error_bound_of_entrywise
      s A samples Bhat uEff huEff hentry
  have hbudget :=
    rowSampleGram_rel_perturb_budget_le_explicit
      A hden hs samples uEff huEff
  have hpoint' :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
        rowSampleGramRelPerturbBudget uEff A :=
    hpoint.trans hbudget
  simpa [fl_rowSampleGramWithComputedDen, Bhat,
    rowSampleGramComputedDenScalePerturbBudget, uEff] using hpoint'

/-- Deterministic fully floating-point Gram perturbation for the
    computed-denominator Algorithm 2 path. -/
theorem fl_rowSampleGramDotWithComputedDen_perturb_bound
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (samples : RowTrace m s) (hgood : rowTracePositiveProb A samples) :
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k) ≤
      rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat := by
  classical
  let uEff : ℝ :=
    rowScaleComputedDenEffectiveRelError fp (rowSqNormProb A) dhat
  have huEff : 0 ≤ uEff :=
    rowScaleComputedDenEffectiveRelError_nonneg fp (rowSqNormProb A) dhat
  let B : Fin s → Fin n → ℝ := rowSampleSketch s A samples
  let Bhat : Fin s → Fin n → ℝ :=
    fl_rowSampleSketchWithComputedDen fp A dhat.den samples
  have hentry : ∀ t j, |Bhat t j - B t j| ≤ |B t j| * uEff := by
    intro t j
    have hprob : 0 < rowSqNormProb A (samples t) := hgood t
    have h :=
      fl_rowSampleSketchWithComputedDen_total_error_bound_le_budget
        fp A (rowSqNormProb A) dhat samples t j hs hprob
    simpa [B, Bhat, rowSampleSketchWithProb, rowSampleSketch,
      rowSampleIncrementWithProb, rowSampleIncrement,
      rowSampleScaleDenWithProb, rowSampleScaleDen, uEff] using h
  have hdot :
      frobNorm
        (fun j k =>
          fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
            rowSketchGram Bhat j k) ≤
        rowSampleGramDotProductRelBudget fp s uEff A := by
    have hlocal :=
      rowSketchGram_dot_frob_error_bound_of_entrywise
        fp B Bhat uEff huEff hγ hentry
    have hbudget :=
      rowSampleGram_dot_product_rel_budget_le_explicit
        fp A hden hs hγ samples uEff
    exact hlocal.trans hbudget
  have hscale :
      frobNorm
        (fun j k =>
          rowSketchGram Bhat j k - rowSampleGram s A samples j k) ≤
        rowSampleGramRelPerturbBudget uEff A := by
    have hpoint :=
      rowSampleGram_frob_error_bound_of_entrywise
        s A samples Bhat uEff huEff (by simpa [B] using hentry)
    have hbudget :=
      rowSampleGram_rel_perturb_budget_le_explicit
        A hden hs samples uEff huEff
    exact hpoint.trans hbudget
  have hsplit :
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k) =
      (fun j k =>
        (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k) +
        (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
    funext j k
    simp [fl_rowSampleGramDotWithComputedDen, Bhat]
  have htri :=
    frobNorm_add_le
      (fun j k =>
        fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
          rowSketchGram Bhat j k)
      (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k)
  calc
    frobNorm
      (fun j k =>
        fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
          rowSampleGram s A samples j k)
        = frobNorm
          (fun j k =>
            (fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
            (rowSketchGram Bhat j k - rowSampleGram s A samples j k)) := by
            rw [hsplit]
    _ ≤
        frobNorm
          (fun j k =>
            fl_dotProduct fp s (fun t => Bhat t j) (fun t => Bhat t k) -
              rowSketchGram Bhat j k) +
        frobNorm
          (fun j k => rowSketchGram Bhat j k - rowSampleGram s A samples j k) :=
          htri
    _ ≤ rowSampleGramDotProductRelBudget fp s uEff A +
        rowSampleGramRelPerturbBudget uEff A :=
          add_le_add hdot hscale
    _ = rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat := by
          unfold rowSampleGramComputedDenFullFpPerturbBudget
          dsimp [uEff]
          ring

-- ============================================================
-- Expected Gram perturbation from sampled-sketch stability
-- ============================================================

/-- Expected entrywise bias of a perturbed sampled Gram matrix. If every entry
    of a row sketch `Bhat` is within relative error `u` of the exact Algorithm 2
    sampled sketch, then the expected bias of the Gram entry is bounded by the
    expected deterministic Gram perturbation. -/
theorem rowSqNormTraceProbability_expectationReal_rowSketchGram_entry_bias_bound_of_entrywise
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (Bhat : RowTrace m s → Fin s → Fin n → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hentry : ∀ samples t j,
      |Bhat samples t j - rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * u)
    (j k : Fin n) :
    |(rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => rowSketchGram (Bhat samples) j k) -
      rowGram A j k| ≤
      (2 * u + u ^ 2) *
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let diff : RowTrace m s → ℝ := fun samples =>
    rowSketchGram (Bhat samples) j k - rowSampleGram s A samples j k
  have hunbiased :=
    rowSqNormTraceProbability_expectationReal_rowSampleGram_entry
      A hden hs j k
  have hsplit :
      P.expectationReal (fun samples => rowSketchGram (Bhat samples) j k) -
        rowGram A j k =
      P.expectationReal diff := by
    unfold diff P
    rw [FiniteProbability.expectationReal_sub]
    rw [hunbiased]
  calc
    |P.expectationReal (fun samples => rowSketchGram (Bhat samples) j k) -
        rowGram A j k|
        = |P.expectationReal diff| := by rw [hsplit]
    _ ≤ P.expectationReal (fun samples => |diff samples|) :=
        FiniteProbability.abs_expectationReal_le_expectationReal_abs P diff
    _ ≤ P.expectationReal
          (fun samples =>
            (2 * u + u ^ 2) *
              ∑ t : Fin s,
                |rowSampleSketch s A samples t j| *
                  |rowSampleSketch s A samples t k|) := by
        apply FiniteProbability.expectationReal_mono
        intro samples
        unfold diff rowSketchGram
        exact rowSampleGram_entry_error_bound_of_entrywise
          s A samples (Bhat samples) u hu (hentry samples) j k
    _ = (2 * u + u ^ 2) *
        P.expectationReal
          (fun samples =>
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
        rw [FiniteProbability.expectationReal_const_mul]

/-- Floating-point sampled-Gram bias bound, stated directly for the rounded
    Algorithm 2 sketch. The entrywise sampled-sketch stability assumption is
    explicit; `fl_rowSampleSketch_error_bound` supplies it whenever the sampled
    row-scale denominators are nonzero. -/
theorem rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_entry_bias_bound_of_entrywise
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hentry : ∀ (samples : RowTrace m s) (t : Fin s) (j : Fin n),
      |fl_rowSampleSketch fp s A samples t j -
        rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * fp.u)
    (j k : Fin n) :
    |(rowSqNormTraceProbability (steps := s) A hden).expectationReal
        (fun samples => fl_rowSampleGram fp s A samples j k) -
      rowGram A j k| ≤
      (2 * fp.u + fp.u ^ 2) *
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) := by
  simpa [fl_rowSampleGram, rowSketchGram] using
    rowSqNormTraceProbability_expectationReal_rowSketchGram_entry_bias_bound_of_entrywise
      A hden hs (fun samples => fl_rowSampleSketch fp s A samples)
      fp.u fp.u_nonneg hentry j k

/-- Stability decomposition for equation (5): for any perturbed sampled sketch,
    the expected Gram error is bounded by the exact row-sampling equation (5)
    term plus the expected perturbation from replacing `rowSampleSketch` by
    `Bhat`. -/
theorem rowSqNormTraceProbability_expectationReal_rowSketchGram_frob_error_le_add_perturb
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (Bhat : RowTrace m s → Fin s → Fin n → ℝ) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNorm (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k)) ≤
      (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A +
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k)) := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  have hpoint : ∀ samples : RowTrace m s,
      frobNorm (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
        frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
          frobNorm
            (fun j k =>
              rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
    intro samples
    have h :=
      frobNorm_add_le
        (fun j k => rowSampleGram s A samples j k - rowGram A j k)
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k)
    have hsame :
        (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) =
          fun j k =>
            (rowSampleGram s A samples j k - rowGram A j k) +
              (rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
      funext j k
      ring
    simpa [hsame] using h
  calc
    P.expectationReal
      (fun samples =>
        frobNorm (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k))
        ≤ P.expectationReal
            (fun samples =>
              frobNorm
                (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
              frobNorm
                (fun j k =>
                  rowSketchGram (Bhat samples) j k -
                    rowSampleGram s A samples j k)) := by
            exact FiniteProbability.expectationReal_mono P hpoint
    _ = P.expectationReal
          (fun samples =>
            frobNorm
              (fun j k => rowSampleGram s A samples j k - rowGram A j k)) +
        P.expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k)) := by
            rw [FiniteProbability.expectationReal_add]
    _ ≤ (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A +
        P.expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k)) := by
            have h :=
              add_le_add_right
              (rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_le
                A hden hs)
              (P.expectationReal
                (fun samples =>
                  frobNorm
                    (fun j k =>
                      rowSketchGram (Bhat samples) j k -
                        rowSampleGram s A samples j k)))
            simpa [P, add_comm, add_left_comm, add_assoc] using h

/-- Floating-point version of the equation (5) stability decomposition. -/
theorem rowSqNormTraceProbability_expectationReal_fl_rowSampleGram_frob_error_le_add_perturb
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ)) :
    (rowSqNormTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        frobNorm (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k)) ≤
      (1 / Real.sqrt (s : ℝ)) * rowSqNormProbDen A +
        (rowSqNormTraceProbability (steps := s) A hden).expectationReal
          (fun samples =>
            frobNorm
              (fun j k =>
                fl_rowSampleGram fp s A samples j k -
                  rowSampleGram s A samples j k)) := by
  simpa [fl_rowSampleGram, rowSketchGram] using
    rowSqNormTraceProbability_expectationReal_rowSketchGram_frob_error_le_add_perturb
      A hden hs (fun samples => fl_rowSampleSketch fp s A samples)

-- ============================================================
-- High-probability equation (5) and floating-point perturbation
-- ============================================================

/-- High-probability squared-moment form of equation (5): for any threshold
    `η > 0`, the exact sampled Gram error is at most `η` with probability at
    least `1 - (||A||_F⁴ / s) / η²`. -/
theorem rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_ge_one_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) :
    1 - (rowSqNormProbDen A ^ 2 / (s : ℝ)) / η ^ 2 ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤ η} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Z : RowTrace m s → ℝ := fun samples =>
    frobNorm (fun j k => rowSampleGram s A samples j k - rowGram A j k)
  have hZ : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact frobNorm_nonneg _
  have hprob :=
    FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
      P Z η hZ hη
  have hsecond :
      P.expectationReal (fun samples => Z samples ^ 2) ≤
        rowSqNormProbDen A ^ 2 / (s : ℝ) := by
    have h :=
      rowSqNormTraceProbability_expectationReal_rowSampleGram_frob_error_sq_le
        A hden hs
    have hZsq :
        P.expectationReal (fun samples => Z samples ^ 2) =
          P.expectationReal
            (fun samples =>
              frobNormSq
                (fun j k => rowSampleGram s A samples j k - rowGram A j k)) := by
      unfold Z
      congr 1
      ext samples
      exact frobNorm_sq _
    simpa [P, hZsq] using h
  have hdiv :
      P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 ≤
        (rowSqNormProbDen A ^ 2 / (s : ℝ)) / η ^ 2 := by
    exact div_le_div_of_nonneg_right hsecond (sq_nonneg η)
  calc
    1 - (rowSqNormProbDen A ^ 2 / (s : ℝ)) / η ^ 2
        ≤ 1 - P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 := by
            linarith
    _ ≤ P.eventProb {samples | Z samples ≤ η} := hprob

/-- Equation (5) as a high-probability statement with explicit failure
    probability `1 / (s ε²)`. -/
theorem rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A} := by
  classical
  have hη : 0 < ε * rowSqNormProbDen A := mul_pos hε hden
  have hbase :=
    rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_ge_one_sub
      A hden hs (ε * rowSqNormProbDen A) hη
  have hfail :
      (rowSqNormProbDen A ^ 2 / (s : ℝ)) /
          (ε * rowSqNormProbDen A) ^ 2 =
        1 / ((s : ℝ) * ε ^ 2) := by
    have hD : rowSqNormProbDen A ≠ 0 := hden.ne'
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hε_ne : ε ≠ 0 := hε.ne'
    field_simp [hD, hs_ne, hε_ne]
  simpa [hfail] using hbase

/-- `1 - δ` form of high-probability equation (5). It is enough to choose the
    sample size so that `1 / (s ε²) ≤ δ`. -/
theorem rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon_of_budget
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε δ : ℝ) (hε : 0 < ε)
    (hbudget : 1 / ((s : ℝ) * ε ^ 2) ≤ δ) :
    1 - δ ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A} := by
  have h :=
    rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
      A hden hs ε hε
  linarith

/-- Generic high-probability transfer from exact sampled-Gram error to any
    computed Gram matrix whose perturbation from the exact sampled Gram is
    bounded with high probability. -/
theorem rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (G : RowTrace m s → Fin n → Fin n → ℝ)
    (ε τ δτ : ℝ) (hε : 0 < ε)
    (hpertProb :
      1 - δτ ≤
        (rowSqNormTraceProbability (steps := s) A hden).eventProb
          {samples |
            frobNorm
              (fun j k =>
                G samples j k - rowSampleGram s A samples j k) ≤ τ}) :
    1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => G samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          G samples j k - rowSampleGram s A samples j k) ≤ τ}
  let H : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => G samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A + τ}
  have hE : 1 - 1 / ((s : ℝ) * ε ^ 2) ≤ P.eventProb E := by
    simpa [P, E] using
      rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
        A hden hs ε hε
  have hF : 1 - δτ ≤ P.eventProb F := by
    simpa [P, F] using hpertProb
  have hinter :
      1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F (1 / ((s : ℝ) * ε ^ 2)) δτ hE hF
  have hsubset : E ∩ F ⊆ H := by
    intro samples hsamples
    have hExact : frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A := hsamples.1
    have hPert : frobNorm
        (fun j k =>
          G samples j k - rowSampleGram s A samples j k) ≤ τ := hsamples.2
    have htri :=
      frobNorm_add_le
        (fun j k => rowSampleGram s A samples j k - rowGram A j k)
        (fun j k => G samples j k - rowSampleGram s A samples j k)
    have hsame :
        (fun j k => G samples j k - rowGram A j k) =
          fun j k =>
            (rowSampleGram s A samples j k - rowGram A j k) +
              (G samples j k - rowSampleGram s A samples j k) := by
      funext j k
      ring
    have htotal :
        frobNorm
          (fun j k => G samples j k - rowGram A j k) ≤
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
          frobNorm
            (fun j k =>
              G samples j k - rowSampleGram s A samples j k) := by
      simpa [hsame] using htri
    exact htotal.trans (add_le_add hExact hPert)
  exact hinter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- High-probability floating-point equation (5) for an arbitrary perturbed row
    sketch. If the perturbation `BᵀB - ÃᵀÃ` is at most `τ` with probability at
    least `1 - δτ`, then the total Gram error is at most
    `ε ||A||_F² + τ` with probability at least
    `1 - (1 / (s ε²) + δτ)`. -/
theorem rowSqNormTraceProbability_eventProb_rowSketchGram_frob_error_le_epsilon_add_tau
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (Bhat : RowTrace m s → Fin s → Fin n → ℝ)
    (ε τ δτ : ℝ) (hε : 0 < ε)
    (hpertProb :
      1 - δτ ≤
        (rowSqNormTraceProbability (steps := s) A hden).eventProb
          {samples |
            frobNorm
              (fun j k =>
                rowSketchGram (Bhat samples) j k -
                  rowSampleGram s A samples j k) ≤ τ}) :
    1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let E : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k) ≤ τ}
  let G : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A + τ}
  have hE : 1 - 1 / ((s : ℝ) * ε ^ 2) ≤ P.eventProb E := by
    simpa [P, E] using
      rowSqNormTraceProbability_eventProb_rowSampleGram_frob_error_le_epsilon
        A hden hs ε hε
  have hF : 1 - δτ ≤ P.eventProb F := by
    simpa [P, F] using hpertProb
  have hinter :
      1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add
      P E F (1 / ((s : ℝ) * ε ^ 2)) δτ hE hF
  have hsubset : E ∩ F ⊆ G := by
    intro samples hsamples
    have hExact : frobNorm
        (fun j k => rowSampleGram s A samples j k - rowGram A j k) ≤
          ε * rowSqNormProbDen A := hsamples.1
    have hPert : frobNorm
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k) ≤ τ := hsamples.2
    have htri :=
      frobNorm_add_le
        (fun j k => rowSampleGram s A samples j k - rowGram A j k)
        (fun j k =>
          rowSketchGram (Bhat samples) j k -
            rowSampleGram s A samples j k)
    have hsame :
        (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) =
          fun j k =>
            (rowSampleGram s A samples j k - rowGram A j k) +
              (rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
      funext j k
      ring
    have htotal :
        frobNorm
          (fun j k => rowSketchGram (Bhat samples) j k - rowGram A j k) ≤
          frobNorm
            (fun j k => rowSampleGram s A samples j k - rowGram A j k) +
          frobNorm
            (fun j k =>
              rowSketchGram (Bhat samples) j k -
                rowSampleGram s A samples j k) := by
      simpa [hsame] using htri
    exact htotal.trans (add_le_add hExact hPert)
  exact hinter.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Floating-point high-probability equation (5): the exact sampling term is
    unchanged, and floating-point arithmetic contributes the perturbation event
    for `fl(Ã)ᵀ fl(Ã) - ÃᵀÃ`. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε τ δτ : ℝ) (hε : 0 < ε)
    (hpertProb :
      1 - δτ ≤
        (rowSqNormTraceProbability (steps := s) A hden).eventProb
          {samples |
            frobNorm
              (fun j k =>
                fl_rowSampleGram fp s A samples j k -
                  rowSampleGram s A samples j k) ≤ τ}) :
    1 - (1 / ((s : ℝ) * ε ^ 2) + δτ) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  simpa [fl_rowSampleGram, rowSketchGram] using
    rowSqNormTraceProbability_eventProb_rowSketchGram_frob_error_le_epsilon_add_tau
      A hden hs (fun samples => fl_rowSampleSketch fp s A samples)
      ε τ δτ hε hpertProb

/-- Deterministic-perturbation version of the floating-point high-probability
    equation (5). If the floating-point Gram perturbation is always at most
    `τ`, the failure probability remains the exact sampling failure
    `1 / (s ε²)`. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε τ : ℝ) (hε : 0 < ε)
    (hpert : ∀ samples : RowTrace m s,
      frobNorm
        (fun j k =>
          fl_rowSampleGram fp s A samples j k -
            rowSampleGram s A samples j k) ≤ τ) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGram fp s A samples j k -
            rowSampleGram s A samples j k) ≤ τ}
  have hF_eq : F = Set.univ := by
    ext samples
    simp [F, hpert samples]
  have hpertProb : 1 - (0 : ℝ) ≤ P.eventProb F := by
    rw [hF_eq, FiniteProbability.eventProb_univ]
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
      fp A hden hs ε τ 0 hε (by simpa [P, F] using hpertProb)
  simpa using h

/-- High-probability floating-point equation (5) from entrywise sampled-sketch
    stability plus an explicit deterministic Gram-perturbation budget. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_entrywise_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε τ : ℝ) (hε : 0 < ε)
    (hentry : ∀ (samples : RowTrace m s) (t : Fin s) (j : Fin n),
      |fl_rowSampleSketch fp s A samples t j -
        rowSampleSketch s A samples t j| ≤
        |rowSampleSketch s A samples t j| * fp.u)
    (hbudget : ∀ samples : RowTrace m s,
      frobNorm
        (fun j k =>
          (2 * fp.u + fp.u ^ 2) *
            ∑ t : Fin s,
              |rowSampleSketch s A samples t j| *
                |rowSampleSketch s A samples t k|) ≤ τ) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + τ} := by
  apply
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_of_forall
      fp A hden hs ε τ hε
  intro samples
  have hpoint :=
    rowSampleGram_frob_error_bound_of_entrywise
      s A samples (fl_rowSampleSketch fp s A samples)
      fp.u fp.u_nonneg (hentry samples)
  simpa [fl_rowSampleGram, rowSketchGram] using hpoint.trans (hbudget samples)

/-- High-probability floating-point equation (5) with no user-supplied
    perturbation event or budget. The exact sampling failure probability is
    unchanged; floating point adds the explicit deterministic budget
    `rowSampleGramFpPerturbBudget fp A`.

    The proof uses the product-law support theorem to apply the floating-point
    division model only on positive-probability sampled rows. Zero-probability
    traces contribute no probability mass. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A + rowSampleGramFpPerturbBudget fp A} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGram fp s A samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramFpPerturbBudget fp A}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    have hentry : ∀ t : Fin s, ∀ j : Fin n,
        |fl_rowSampleSketch fp s A samples t j -
          rowSampleSketch s A samples t j| ≤
          |rowSampleSketch s A samples t j| * fp.u := by
      intro t j
      have hprob : 0 < rowSqNormProb A (samples t) := hgood_pos t
      exact fl_rowSampleSketch_error_bound fp s A samples t j
        (rowSampleScaleDen_ne_zero s A (samples t) hs hprob)
    have hpoint :=
      rowSampleGram_frob_error_bound_of_entrywise
        s A samples (fl_rowSampleSketch fp s A samples)
        fp.u fp.u_nonneg hentry
    have hbudget :=
      rowSampleGram_perturb_budget_le_explicit fp A hden hs samples
    simpa [F, fl_rowSampleGram, rowSketchGram] using hpoint.trans hbudget
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau
      fp A hden hs ε (rowSampleGramFpPerturbBudget fp A) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

/-- Scaling-only floating-point high-probability equation (5).  This is the
    model where Algorithm 2 forms the sampled-and-scaled rows in floating point,
    but the Gram matrix is a mathematical object formed exactly from those
    rounded rows.  Thus the dot-product budget is zero, and the only FP term is
    the row-rescaling division budget. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                (n : ℝ) * ((2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A)} := by
  have h :=
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_explicit_budget
      fp A hden hs ε hε
  simpa [rowSampleGramFpPerturbBudget_eq_nat_mul fp A] using h

/-- Scaling-only floating-point high-probability equation (5), written as the
    `tau_dot = 0` specialization.  This is the practical model where Algorithm
    2 computes the sampled-and-scaled rows in floating point, while the Gram
    matrix is used only as an exact mathematical object in the analysis of that
    rounded sketch. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_tau_dot_zero
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGram fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                ((n : ℝ) * ((2 * fp.u + fp.u ^ 2) * rowSqNormProbDen A) + 0)} := by
  simpa using
    rowSqNormTraceProbability_eventProb_fl_rowSampleGram_frob_error_le_epsilon_add_scaling_budget
      fp A hden hs ε hε

/-- Fully floating-point high-probability equation (5), reusing the library dot
    product theorem for the Gram computation. The deterministic FP budget has
    two modular pieces: row-rescaling division error and dot-product evaluation
    error for the Gram entries. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGramDot_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k => fl_rowSampleGramDot fp s A samples j k - rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                rowSampleGramFullFpPerturbBudget fp s A} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGramDot fp s A samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramFullFpPerturbBudget fp s A}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    have hentry : ∀ t : Fin s, ∀ j : Fin n,
        |fl_rowSampleSketch fp s A samples t j -
          rowSampleSketch s A samples t j| ≤
          |rowSampleSketch s A samples t j| * fp.u := by
      intro t j
      have hprob : 0 < rowSqNormProb A (samples t) := hgood_pos t
      exact fl_rowSampleSketch_error_bound fp s A samples t j
        (rowSampleScaleDen_ne_zero s A (samples t) hs hprob)
    simpa [F] using
      fl_rowSampleGramDot_perturb_bound_of_entrywise
        fp A hden hs hγ samples hentry
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
      A hden hs (fun samples => fl_rowSampleGramDot fp s A samples)
      ε (rowSampleGramFullFpPerturbBudget fp s A) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

/-- High-probability equation (5) for the computed-denominator Algorithm 2
    path, with exact Gram arithmetic after the rounded sketch.  The sampling
    law is unchanged; the additive FP radius is the proved deterministic
    computed-denominator row-scaling budget. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGramWithComputedDen_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k =>
              fl_rowSampleGramWithComputedDen fp A dhat.den samples j k -
                rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                rowSampleGramComputedDenScalePerturbBudget fp s A dhat} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGramWithComputedDen fp A dhat.den samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramComputedDenScalePerturbBudget fp s A dhat}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    simpa [F] using
      fl_rowSampleGramWithComputedDen_perturb_bound
        fp A hden hs dhat samples hgood_pos
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
      A hden hs
      (fun samples => fl_rowSampleGramWithComputedDen fp A dhat.den samples)
      ε (rowSampleGramComputedDenScalePerturbBudget fp s A dhat) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

/-- Fully floating-point high-probability equation (5) for the
    computed-denominator Algorithm 2 path.  This charges denominator
    computation, rounded row scaling, and floating-point dot products for the
    Gram entries. -/
theorem rowSqNormTraceProbability_eventProb_fl_rowSampleGramDotWithComputedDen_frob_error_le_epsilon_add_explicit_budget
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < rowSqNormProbDen A) (hs : 0 < (s : ℝ))
    (hγ : gammaValid fp s)
    (dhat : ComputedRowScaleDen fp s (rowSqNormProb A))
    (ε : ℝ) (hε : 0 < ε) :
    1 - 1 / ((s : ℝ) * ε ^ 2) ≤
      (rowSqNormTraceProbability (steps := s) A hden).eventProb
        {samples |
          frobNorm
            (fun j k =>
              fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
                rowGram A j k) ≤
              ε * rowSqNormProbDen A +
                rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat} := by
  classical
  let P := rowSqNormTraceProbability (steps := s) A hden
  let Good : Set (RowTrace m s) := {samples | rowTracePositiveProb A samples}
  let F : Set (RowTrace m s) :=
    {samples |
      frobNorm
        (fun j k =>
          fl_rowSampleGramDotWithComputedDen fp A dhat.den samples j k -
            rowSampleGram s A samples j k) ≤
        rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat}
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      rowSqNormTraceProbability_eventProb_rowTracePositiveProb
        (steps := s) A hden
  have hGood_subset_F : Good ⊆ F := by
    intro samples hgood
    have hgood_pos : rowTracePositiveProb A samples := by
      simpa [Good] using hgood
    simpa [F] using
      fl_rowSampleGramDotWithComputedDen_perturb_bound
        fp A hden hs hγ dhat samples hgood_pos
  have hpertProb :
      1 - (0 : ℝ) ≤ P.eventProb F := by
    have hmono : P.eventProb Good ≤ P.eventProb F :=
      FiniteProbability.eventProb_mono P hGood_subset_F
    linarith
  have h :=
    rowSqNormTraceProbability_eventProb_computedGram_frob_error_le_epsilon_add_tau
      A hden hs
      (fun samples => fl_rowSampleGramDotWithComputedDen fp A dhat.den samples)
      ε (rowSampleGramComputedDenFullFpPerturbBudget fp s A dhat) 0 hε
      (by simpa [P, F] using hpertProb)
  simpa using h

end NumStability
