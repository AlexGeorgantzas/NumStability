-- Algorithms/RandNLA/ElementwiseSpectral.lean
--
-- Deterministic spectral-norm transfer infrastructure for Algorithm 1.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602
--
-- The hard-thresholded source-alignment layer follows:
-- Petros Drineas and Anastasios Zouzias, "A Note on Element-wise Matrix
-- Sparsification via a Matrix-valued Bernstein Inequality," arXiv:1006.0407.
-- https://arxiv.org/pdf/1006.0407

import NumStability.Algorithms.RandNLA.ElementwiseSampling
import NumStability.Algorithms.RandNLA.HitCountConcentration
import NumStability.Algorithms.RandNLA.ElementwiseTraceMGF
import NumStability.Algorithms.RandNLA.Preconditioning
import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixConcentration
import NumStability.Analysis.MatrixSpectral

namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Algorithm 1 spectral transfer layer

The CACM RandNLA survey states a high-probability spectral-norm concentration
bound for Algorithm 1, equation (2).  This file proves deterministic spectral
and floating-point transfer infrastructure and several exact concentration
layers for the truncated self-adjoint dilation route, including parameterized
trace-MGF-to-eigenvalue tails.  The remaining open piece is the final
theta-optimization/source-constant conversion from the scaled dilation
eigenvalue statement to the exact CACM equation (2) spectral-norm theorem:

* if the exact sampled residual satisfies a rectangular vector-action
  operator-2 bound, and
* if the floating-point sampled sketch is entrywise close to the exact sampled
  sketch,

then the floating-point sampled residual satisfies the same operator-2 bound
with the rectangular Frobenius norm of the entrywise perturbation budget added.

This keeps the equation (2) backlog explicit: the missing piece is the final
source-constant concentration conversion, not the lower-level trace-MGF or
floating-point transfer infrastructure.
-/

-- ============================================================
-- Residuals and spectral events
-- ============================================================

/-- Exact Algorithm 1 residual `A - Atilde` for a deterministic trace, starting
    the sketch from zero. -/
noncomputable def elementwiseTraceResidual {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j - elementwiseTraceSketch s A (fun _ _ => 0) samples i j

/-- Floating-point Algorithm 1 residual `A - fl(Atilde)` for a deterministic
    trace, starting the sketch from zero. -/
noncomputable def fl_elementwiseTraceResidual (fp : FPModel) {m n steps : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j => A i j - fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j

/-- Exact Algorithm 1 residual when the sampler rescales with a supplied exact
    probability table `p`. -/
noncomputable def elementwiseTraceResidualWithProb {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j =>
    A i j - elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j

/-- Floating-point Algorithm 1 residual when the sampler rescales with a
    supplied exact probability table `p`. -/
noncomputable def fl_elementwiseTraceResidualWithProb (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      fl_elementwiseTraceSketchWithProb fp s A (fun _ _ => 0) p samples i j

/-- Entrywise hard-thresholding used by the primary Drineas--Zouzias
    matrix-Bernstein source for elementwise sparsification.  Entries with
    magnitude below `tau` are zeroed; all other entries are left unchanged. -/
noncomputable def elementwiseTruncate {m n : ℕ} (tau : ℝ)
    (A : Fin m → Fin n → ℝ) : Fin m → Fin n → ℝ :=
  fun i j => if |A i j| < tau then 0 else A i j

/-- Exact residual of the truncated Algorithm 1 sketch against the original
    input matrix.  The sketch is built from `elementwiseTruncate tau A`, while
    the final error is measured against `A`. -/
noncomputable def elementwiseTruncatedTraceResidual {m n steps : ℕ}
    (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      elementwiseTraceSketch s (elementwiseTruncate tau A) (fun _ _ => 0)
        samples i j

/-- Floating-point residual of the truncated Algorithm 1 sketch against the
    original input matrix. -/
noncomputable def fl_elementwiseTruncatedTraceResidual (fp : FPModel)
    {m n steps : ℕ} (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
        (fun _ _ => 0) samples i j

/-- Exact residual of the truncated Algorithm 1 sketch when the sampler uses a
    supplied exact probability table for the truncated matrix. -/
noncomputable def elementwiseTruncatedTraceResidualWithProb {m n steps : ℕ}
    (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      elementwiseTraceSketchWithProb s (elementwiseTruncate tau A)
        (fun _ _ => 0) p samples i j

/-- Floating-point residual of the truncated Algorithm 1 sketch when the
    sampler uses a supplied exact probability table for the
    truncated matrix. -/
noncomputable def fl_elementwiseTruncatedTraceResidualWithProb (fp : FPModel)
    {m n steps : ℕ} (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) :
    Fin m → Fin n → ℝ :=
  fun i j =>
    A i j -
      fl_elementwiseTraceSketchWithProb fp s (elementwiseTruncate tau A)
        (fun _ _ => 0) p samples i j

/-- The deterministic truncation error is entrywise bounded by the threshold. -/
theorem elementwiseTruncate_error_entry_abs_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (htau : 0 ≤ tau)
    (i : Fin m) (j : Fin n) :
    |A i j - elementwiseTruncate tau A i j| ≤ tau := by
  unfold elementwiseTruncate
  by_cases hsmall : |A i j| < tau
  · simp [hsmall]
    exact le_of_lt hsmall
  · simp [hsmall, htau]

/-- Hard-thresholding cannot increase the magnitude of any entry. -/
theorem elementwiseTruncate_abs_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) :
    |elementwiseTruncate tau A i j| ≤ |A i j| := by
  unfold elementwiseTruncate
  by_cases hsmall : |A i j| < tau
  · simp [hsmall]
  · simp [hsmall]

/-- If every nonzero entry already has magnitude at least the threshold, then
hard-thresholding does not change the matrix.

This is used only as an adapter from the source-aligned truncated
matrix-Bernstein theorem back to the literal Algorithm 1 law on inputs for
which the source truncation is the identity. -/
theorem elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
    {m n : ℕ} {tau : ℝ} (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → tau ≤ |A i j|) :
    elementwiseTruncate tau A = A := by
  funext i j
  unfold elementwiseTruncate
  by_cases hsmall : |A i j| < tau
  · have hzero : A i j = 0 := by
      by_contra hne
      exact (not_lt_of_ge (hentry i j hne)) hsmall
    simp [hzero]
  · simp [hsmall]

/-- Hard-thresholding cannot increase the squared rectangular Frobenius norm. -/
theorem frobNormSqRect_elementwiseTruncate_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) :
    frobNormSqRect (elementwiseTruncate tau A) ≤ frobNormSqRect A := by
  unfold frobNormSqRect
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  exact (sq_le_sq).mpr (elementwiseTruncate_abs_le tau A i j)

/-- Hard-thresholding cannot increase the rectangular Frobenius norm. -/
theorem frobNormRect_elementwiseTruncate_le {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) :
    frobNormRect (elementwiseTruncate tau A) ≤ frobNormRect A := by
  unfold frobNormRect
  exact Real.sqrt_le_sqrt (frobNormSqRect_elementwiseTruncate_le tau A)

/-- A nonzero retained entry of the hard-thresholded matrix has magnitude at
    least the threshold. -/
theorem elementwiseTruncate_nonzero_abs_ge {m n : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (hij : elementwiseTruncate tau A i j ≠ 0) :
    tau ≤ |elementwiseTruncate tau A i j| := by
  unfold elementwiseTruncate at hij ⊢
  by_cases hsmall : |A i j| < tau
  · simp [hsmall] at hij
  · simp [hsmall]
    exact le_of_not_gt hsmall

/-- If the truncated matrix has nonzero squared-magnitude denominator, then
its Frobenius norm is at least the truncation threshold.  This is the local
source-sample-complexity fact used to control the linear `eps * ||Ahat||_F`
term in the Bernstein denominator. -/
theorem elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
    {m n : ℕ} {tau : ℝ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    tau ≤ frobNormRect (elementwiseTruncate tau A) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hnot_all_zero : ¬ ∀ i j, Ahat i j = 0 := by
    intro hall
    have hzero : frobNormSqRect Ahat = 0 :=
      (frobNormSqRect_eq_zero_iff Ahat).mpr hall
    have hpos : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    linarith
  push_neg at hnot_all_zero
  rcases hnot_all_zero with ⟨i, j, hij⟩
  have htaule : tau ≤ |Ahat i j| := by
    simpa [Ahat] using
      elementwiseTruncate_nonzero_abs_ge (tau := tau) A i j hij
  have hentry_sq_le :
      Ahat i j ^ 2 ≤ frobNormSqRect Ahat := by
    unfold frobNormSqRect
    have hrow :
        Ahat i j ^ 2 ≤ ∑ b : Fin n, Ahat i b ^ 2 :=
      Finset.single_le_sum (fun b _ => sq_nonneg (Ahat i b))
        (Finset.mem_univ j)
    have hrow_nonneg :
        ∀ a : Fin m, 0 ≤ ∑ b : Fin n, Ahat a b ^ 2 :=
      fun a => Finset.sum_nonneg (fun b _ => sq_nonneg (Ahat a b))
    exact hrow.trans
      (Finset.single_le_sum (fun a _ => hrow_nonneg a) (Finset.mem_univ i))
  have habs_le_frob : |Ahat i j| ≤ frobNormRect Ahat := by
    have hsq :
        |Ahat i j| ^ 2 ≤ frobNormRect Ahat ^ 2 := by
      rw [sq_abs, frobNormRect_sq]
      exact hentry_sq_le
    have hsq_abs := (sq_le_sq).mp hsq
    simpa [abs_of_nonneg (frobNormRect_nonneg Ahat)] using hsq_abs
  exact htaule.trans habs_le_frob

/-- For the hard-thresholded matrix, a one-sample contribution from a retained
    entry is entrywise bounded by `||Ahat||_F^2 / (s*tau)`.  This is the
    bounded-increment side condition needed before a Bernstein proof can be
    instantiated for the truncated source route. -/
theorem elementwiseSampleContribution_truncated_entry_abs_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0)
    (i : Fin m) (j : Fin n) :
    |elementwiseSampleContribution s (elementwiseTruncate tau A) sample i j| ≤
      frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hF_nonneg : 0 ≤ frobNormSqRect Ahat := frobNormSqRect_nonneg Ahat
  have hden_tau_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
  have hbound_nonneg :
      0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
    div_nonneg hF_nonneg (le_of_lt hden_tau_pos)
  by_cases hhit : sample.1 = i ∧ sample.2 = j
  · have hi : sample.1 = i := hhit.1
    have hj : sample.2 = j := hhit.2
    have hAij_ne : Ahat i j ≠ 0 := by
      simpa [Ahat, ← hi, ← hj] using hsample
    have htaule : tau ≤ |Ahat i j| := by
      simpa [Ahat] using
        elementwiseTruncate_nonzero_abs_ge tau A i j (by simpa [Ahat] using hAij_ne)
    have hAij_abs_pos : 0 < |Ahat i j| := lt_of_lt_of_le htau htaule
    have hden_abs_pos : 0 < (s : ℝ) * |Ahat i j| :=
      mul_pos hs hAij_abs_pos
    have hden_le : (s : ℝ) * tau ≤ (s : ℝ) * |Ahat i j| :=
      mul_le_mul_of_nonneg_left htaule (le_of_lt hs)
    have hdiv_le :
        frobNormSqRect Ahat / ((s : ℝ) * |Ahat i j|) ≤
          frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_le_div_of_nonneg_left hF_nonneg hden_tau_pos hden_le
    have hinc :
        elementwiseIncrement s Ahat i j =
          frobNormSqRect Ahat / ((s : ℝ) * Ahat i j) := by
      simpa [Ahat] using
        elementwiseIncrement_sqMag_eq s Ahat i j hs_ne hAij_ne
    calc
      |elementwiseSampleContribution s Ahat sample i j|
          = |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| := by
              simp [elementwiseSampleContribution, hhit, hinc]
      _ = frobNormSqRect Ahat / ((s : ℝ) * |Ahat i j|) := by
              rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt hs),
                abs_of_nonneg hF_nonneg]
      _ ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) := hdiv_le
  · simp [elementwiseSampleContribution, hhit]
    exact hbound_nonneg

/-- Frobenius form of
    `elementwiseSampleContribution_truncated_entry_abs_le`: for a retained
    sampled entry of the hard-thresholded matrix, the one-sample contribution
    has Frobenius norm at most `||Ahat||_F^2 / (s*tau)`. -/
theorem frobNormRect_elementwiseSampleContribution_truncated_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    frobNormRect
      (elementwiseSampleContribution s (elementwiseTruncate tau A) sample) ≤
      frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hshape :
      elementwiseSampleContribution s Ahat sample =
        fun r c =>
          if sample.1 = r ∧ sample.2 = c then
            elementwiseIncrement s Ahat sample.1 sample.2
          else
            0 := by
    ext r c
    by_cases hhit : sample.1 = r ∧ sample.2 = c
    · simp [elementwiseSampleContribution, hhit]
    · simp [elementwiseSampleContribution, hhit]
  have hentry :=
    elementwiseSampleContribution_truncated_entry_abs_le
      htau hs A sample hsample sample.1 sample.2
  have hentry' :
      |elementwiseIncrement s Ahat sample.1 sample.2| ≤
        frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    simpa [Ahat, elementwiseSampleContribution] using hentry
  calc
    frobNormRect (elementwiseSampleContribution s Ahat sample)
        = |elementwiseIncrement s Ahat sample.1 sample.2| := by
            rw [hshape]
            exact frobNormRect_single_left sample.1 sample.2
              (elementwiseIncrement s Ahat sample.1 sample.2)
    _ ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) := hentry'

/-- Exact input-dependent contribution radius for the literal, untruncated
Algorithm 1 squared-magnitude sampler.

This is deliberately not a uniform source constant: it is the finite sum of the
reciprocal nonzero entry magnitudes that controls the one-sample rescaled
contribution under the exact literal law.  Tiny nonzero entries therefore make
the displayed radius large, which is the behavior exposed by the route
obstruction above. -/
noncomputable def elementwiseLiteralContributionRadius {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n,
    if A i j = 0 then 0
    else frobNormSqRect A / ((s : ℝ) * |A i j|)

/-- Exact input-dependent one-sample residual radius for the literal,
untruncated Algorithm 1 sampler. -/
noncomputable def elementwiseLiteralResidualSupportRadius {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) : ℝ :=
  (1 / (s : ℝ)) * frobNormRect A +
    elementwiseLiteralContributionRadius s A

/-- Every summand in the literal contribution radius is nonnegative when the
sample count is positive. -/
theorem elementwiseLiteralContributionRadius_term_nonneg
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    0 ≤
      (if A i j = 0 then 0
       else frobNormSqRect A / ((s : ℝ) * |A i j|)) := by
  by_cases hzero : A i j = 0
  · simp [hzero]
  · have habs_pos : 0 < |A i j| := abs_pos.mpr hzero
    have hden_pos : 0 < (s : ℝ) * |A i j| := mul_pos hs habs_pos
    simp [hzero, div_nonneg (frobNormSqRect_nonneg A) (le_of_lt hden_pos)]

/-- The literal contribution radius is nonnegative when the sample count is
positive. -/
theorem elementwiseLiteralContributionRadius_nonneg
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ) :
    0 ≤ elementwiseLiteralContributionRadius s A := by
  unfold elementwiseLiteralContributionRadius
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact elementwiseLiteralContributionRadius_term_nonneg hs A i j

/-- If every nonzero entry is bounded below by `alpha`, then the literal
reciprocal-entry contribution radius is bounded by a simple floor-dependent
quantity.

This is a deterministic exact-arithmetic simplification of
`elementwiseLiteralContributionRadius`; it is not a probability statement. -/
theorem elementwiseLiteralContributionRadius_le_of_entry_abs_ge
    {m n s : ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|) :
    elementwiseLiteralContributionRadius s A ≤
      ((m : ℝ) * (n : ℝ)) *
        (frobNormSqRect A / ((s : ℝ) * alpha)) := by
  classical
  let C : ℝ := frobNormSqRect A / ((s : ℝ) * alpha)
  have hC_nonneg : 0 ≤ C :=
    div_nonneg (frobNormSqRect_nonneg A)
      (mul_nonneg (le_of_lt hs) (le_of_lt halpha))
  have hterm_le :
      ∀ i j,
        (if A i j = 0 then 0
         else frobNormSqRect A / ((s : ℝ) * |A i j|)) ≤ C := by
    intro i j
    by_cases hzero : A i j = 0
    · simpa [hzero, C] using hC_nonneg
    · have habs_pos : 0 < |A i j| := abs_pos.mpr hzero
      have halpha_le : alpha ≤ |A i j| := hentry i j hzero
      have hden_alpha_pos : 0 < (s : ℝ) * alpha := mul_pos hs halpha
      have hden_le : (s : ℝ) * alpha ≤ (s : ℝ) * |A i j| :=
        mul_le_mul_of_nonneg_left halpha_le (le_of_lt hs)
      have hle :
          frobNormSqRect A / ((s : ℝ) * |A i j|) ≤
            frobNormSqRect A / ((s : ℝ) * alpha) :=
        div_le_div_of_nonneg_left (frobNormSqRect_nonneg A)
          hden_alpha_pos hden_le
      simpa [hzero, C] using hle
  calc
    elementwiseLiteralContributionRadius s A
        = ∑ i : Fin m, ∑ j : Fin n,
            (if A i j = 0 then 0
             else frobNormSqRect A / ((s : ℝ) * |A i j|)) := by
              rfl
    _ ≤ ∑ i : Fin m, ∑ _j : Fin n, C := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro j _
          exact hterm_le i j
    _ = ((m : ℝ) * (n : ℝ)) * C := by
          simp [C, Finset.sum_const, nsmul_eq_mul]
          ring
    _ = ((m : ℝ) * (n : ℝ)) *
        (frobNormSqRect A / ((s : ℝ) * alpha)) := by
          simp [C]

/-- Entry-floor simplification for the literal one-sample residual support
radius. -/
theorem elementwiseLiteralResidualSupportRadius_le_of_entry_abs_ge
    {m n s : ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|) :
    elementwiseLiteralResidualSupportRadius s A ≤
      (1 / (s : ℝ)) * frobNormRect A +
        ((m : ℝ) * (n : ℝ)) *
          (frobNormSqRect A / ((s : ℝ) * alpha)) := by
  have hR :=
    elementwiseLiteralContributionRadius_le_of_entry_abs_ge
      halpha hs A hentry
  simpa [elementwiseLiteralResidualSupportRadius] using
    add_le_add_left hR ((1 / (s : ℝ)) * frobNormRect A)

/-- Scaled version of the entry-floor contribution-radius bound, in the form
used by the literal floating-point scalar radius. -/
theorem smul_elementwiseLiteralContributionRadius_le_of_entry_abs_ge
    {m n s : ℕ} {alpha : ℝ} (halpha : 0 < alpha)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|) :
    (s : ℝ) * elementwiseLiteralContributionRadius s A ≤
      ((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha) := by
  have hR :=
    elementwiseLiteralContributionRadius_le_of_entry_abs_ge
      halpha hs A hentry
  have hmul :=
    mul_le_mul_of_nonneg_left hR (le_of_lt hs)
  have hcancel_core :
      (s : ℝ) * (frobNormSqRect A / (alpha * (s : ℝ))) =
        frobNormSqRect A / alpha := by
    field_simp [hs.ne', halpha.ne']
  simpa [hcancel_core, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Any nonzero entry's reciprocal contribution is bounded by the finite
literal contribution radius. -/
theorem literal_entry_contribution_le_elementwiseLiteralContributionRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) :
    (if A i j = 0 then 0
     else frobNormSqRect A / ((s : ℝ) * |A i j|)) ≤
      elementwiseLiteralContributionRadius s A := by
  classical
  unfold elementwiseLiteralContributionRadius
  let term : Fin m → Fin n → ℝ :=
    fun a b =>
      if A a b = 0 then 0
      else frobNormSqRect A / ((s : ℝ) * |A a b|)
  have hterm_nonneg : ∀ a b, 0 ≤ term a b := by
    intro a b
    exact elementwiseLiteralContributionRadius_term_nonneg hs A a b
  have hrow :
      term i j ≤ ∑ b : Fin n, term i b :=
    Finset.single_le_sum (fun b _ => hterm_nonneg i b) (Finset.mem_univ j)
  have hrow_nonneg : ∀ a : Fin m, 0 ≤ ∑ b : Fin n, term a b := by
    intro a
    exact Finset.sum_nonneg (fun b _ => hterm_nonneg a b)
  exact hrow.trans
    (Finset.single_le_sum (fun a _ => hrow_nonneg a) (Finset.mem_univ i))

/-- For the literal untruncated matrix, a one-sample contribution from a
positive-probability entry is bounded by the explicit input-dependent
contribution radius. -/
theorem elementwiseSampleContribution_literal_entry_abs_le
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0)
    (i : Fin m) (j : Fin n) :
    |elementwiseSampleContribution s A sample i j| ≤
      elementwiseLiteralContributionRadius s A := by
  classical
  have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have hRadius_nonneg :
      0 ≤ elementwiseLiteralContributionRadius s A :=
    elementwiseLiteralContributionRadius_nonneg hs A
  by_cases hhit : sample.1 = i ∧ sample.2 = j
  · have hi : sample.1 = i := hhit.1
    have hj : sample.2 = j := hhit.2
    have hAij_ne : A i j ≠ 0 := by
      simpa [← hi, ← hj] using hsample
    have hF_nonneg : 0 ≤ frobNormSqRect A := frobNormSqRect_nonneg A
    have hinc :
        elementwiseIncrement s A i j =
          frobNormSqRect A / ((s : ℝ) * A i j) := by
      simpa using elementwiseIncrement_sqMag_eq s A i j hs_ne hAij_ne
    calc
      |elementwiseSampleContribution s A sample i j|
          = |frobNormSqRect A / ((s : ℝ) * A i j)| := by
              simp [elementwiseSampleContribution, hhit, hinc]
      _ = frobNormSqRect A / ((s : ℝ) * |A i j|) := by
              rw [abs_div, abs_mul, abs_of_nonneg (le_of_lt hs),
                abs_of_nonneg hF_nonneg]
      _ =
          (if A i j = 0 then 0
           else frobNormSqRect A / ((s : ℝ) * |A i j|)) := by
              simp [hAij_ne]
      _ ≤ elementwiseLiteralContributionRadius s A :=
          literal_entry_contribution_le_elementwiseLiteralContributionRadius
            hs A i j
  · simp [elementwiseSampleContribution, hhit]
    exact hRadius_nonneg

/-- Frobenius form of
`elementwiseSampleContribution_literal_entry_abs_le`: for a sampled nonzero
entry of the literal matrix, the one-sample contribution has Frobenius norm at
most the finite input-dependent contribution radius. -/
theorem frobNormRect_elementwiseSampleContribution_literal_le
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    frobNormRect (elementwiseSampleContribution s A sample) ≤
      elementwiseLiteralContributionRadius s A := by
  classical
  have hshape :
      elementwiseSampleContribution s A sample =
        fun r c =>
          if sample.1 = r ∧ sample.2 = c then
            elementwiseIncrement s A sample.1 sample.2
          else
            0 := by
    ext r c
    by_cases hhit : sample.1 = r ∧ sample.2 = c
    · simp [elementwiseSampleContribution, hhit]
    · simp [elementwiseSampleContribution, hhit]
  have hentry :=
    elementwiseSampleContribution_literal_entry_abs_le
      hs A sample hsample sample.1 sample.2
  have hentry' :
      |elementwiseIncrement s A sample.1 sample.2| ≤
        elementwiseLiteralContributionRadius s A := by
    simpa [elementwiseSampleContribution] using hentry
  calc
    frobNormRect (elementwiseSampleContribution s A sample)
        = |elementwiseIncrement s A sample.1 sample.2| := by
            rw [hshape]
            exact frobNormRect_single_left sample.1 sample.2
              (elementwiseIncrement s A sample.1 sample.2)
    _ ≤ elementwiseLiteralContributionRadius s A := hentry'

/-- Frobenius norm of a constant square matrix. -/
theorem frobNormRect_const_square {n : ℕ} (c : ℝ) (hc : 0 ≤ c) :
    frobNormRect (fun _i : Fin n => fun _j : Fin n => c) =
      (n : ℝ) * c := by
  unfold frobNormRect frobNormSqRect
  have hsum :
      (∑ i : Fin n, ∑ j : Fin n, c ^ 2) =
        (n : ℝ) * (n : ℝ) * c ^ 2 := by
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hsum]
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hprod : 0 ≤ (n : ℝ) * c := mul_nonneg hn hc
  have hsquare : (n : ℝ) * (n : ℝ) * c ^ 2 = ((n : ℝ) * c) ^ 2 := by
    ring
  rw [hsquare, Real.sqrt_sq_eq_abs, abs_of_nonneg hprod]

/-- Square-matrix truncation at `eps / (2n)` costs at most `eps / 2` in
    rectangular Frobenius norm. -/
theorem elementwiseTruncate_square_error_frobNormRect_le_half
    {n : ℕ} (A : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n) :
    frobNormRect
      (fun i j =>
        A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
      eps / 2 := by
  let tau : ℝ := eps / (2 * (n : ℝ))
  have hden_nonneg : 0 ≤ 2 * (n : ℝ) := by positivity
  have htau : 0 ≤ tau := div_nonneg heps hden_nonneg
  calc
    frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j)
        ≤ frobNormRect (fun _i : Fin n => fun _j : Fin n => tau) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact htau
          · intro i j
            exact elementwiseTruncate_error_entry_abs_le tau A htau i j
    _ = (n : ℝ) * tau := frobNormRect_const_square tau htau
    _ = eps / 2 := by
          have hn_ne : (n : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt hn)
          unfold tau
          field_simp [hn_ne]

/-- Square-matrix truncation at `eps / (2n)` costs at most `eps / 2` in the
    repository's rectangular operator-2 predicate.  This is the deterministic
    first half of the Drineas--Zouzias truncated elementwise-sampling proof. -/
theorem elementwiseTruncate_square_error_rectOpNorm2Le_half
    {n : ℕ} (A : Fin n → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n) :
    rectOpNorm2Le
      (fun i j =>
        A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j)
      (eps / 2) := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact elementwiseTruncate_square_error_frobNormRect_le_half A heps hn

/-- Rectangular truncation at `eps / (2*sqrt(mn))` costs at most `eps / 2`
    in rectangular Frobenius norm. -/
theorem elementwiseTruncate_rect_error_frobNormRect_le_half
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ)) :
    frobNormRect
      (fun i j =>
        A i j -
          elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
      eps / 2 := by
  let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
  let tau : ℝ := eps / (2 * R)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr hmn
  have htau : 0 ≤ tau := by
    dsimp [tau]
    positivity
  have hentry :
      ∀ i j,
        |(fun i j => A i j - elementwiseTruncate tau A i j) i j| ≤ tau := by
    intro i j
    exact elementwiseTruncate_error_entry_abs_le tau A htau i j
  have hnorm :
      frobNormRect
          (fun i j => A i j - elementwiseTruncate tau A i j) ≤
        Real.sqrt ((m : ℝ) * (n : ℝ)) * tau :=
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun i j => A i j - elementwiseTruncate tau A i j) htau hentry
  have hmul : Real.sqrt ((m : ℝ) * (n : ℝ)) * tau = eps / 2 := by
    dsimp [tau, R]
    field_simp [ne_of_gt hR_pos]
  calc
    frobNormRect
        (fun i j =>
          A i j -
            elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j)
        ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) * tau := by
          simpa [tau, R] using hnorm
    _ = eps / 2 := hmul

/-- Rectangular truncation at `eps / (2*sqrt(mn))` costs at most `eps / 2`
    in the repository's rectangular operator-2 predicate. -/
theorem elementwiseTruncate_rect_error_rectOpNorm2Le_half
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ)) :
    rectOpNorm2Le
      (fun i j =>
        A i j -
          elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j)
      (eps / 2) := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact elementwiseTruncate_rect_error_frobNormRect_le_half A heps hmn

/-- If the sampled residual of the truncated matrix is operator-bounded and
    the deterministic truncation error has Frobenius budget `alpha`, then the
    truncated sketch is operator-bounded against the original matrix. -/
theorem elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
    {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {beta alpha : ℝ}
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s (elementwiseTruncate tau A) samples)
        beta)
    (hTrunc :
      frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j) ≤ alpha) :
    rectOpNorm2Le (elementwiseTruncatedTraceResidual tau s A samples)
      (beta + alpha) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let M : Fin m → Fin n → ℝ := elementwiseTraceResidual s Ahat samples
  let E : Fin m → Fin n → ℝ := fun i j => A i j - Ahat i j
  have hsum : rectOpNorm2Le (fun i j => M i j + E i j) (beta + alpha) :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le M E hSample hTrunc
  convert hsum using 1
  ext i j
  simp [elementwiseTruncatedTraceResidual, elementwiseTraceResidual, Ahat, M, E]

/-- Square-matrix specialization of the truncated transfer: if the sampled
    residual for the truncated matrix is at most `eps / 2`, then the exact
    truncated sketch is within `eps` of the original matrix. -/
theorem elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half
    {n steps : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (samples : ElementwiseTrace n n steps) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s
          (elementwiseTruncate (eps / (2 * (n : ℝ))) A) samples)
        (eps / 2)) :
    rectOpNorm2Le
      (elementwiseTruncatedTraceResidual (eps / (2 * (n : ℝ))) s A samples)
      eps := by
  have hTruncFrob :
      frobNormRect
        (fun i j =>
          A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_square_error_frobNormRect_le_half A heps hn
  have h :=
    elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      (eps / (2 * (n : ℝ))) s A samples hSample hTruncFrob
  convert h using 1
  ring

/-- One-sample exact residual increment for Algorithm 1.  When the trace has
    exactly `s` samples, the exact residual `A - Atilde` is the sum of these
    increments over the trace. -/
noncomputable def elementwiseSampleResidualIncrement {m n : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n) :
    Fin m → Fin n → ℝ :=
  fun i j => A i j / (s : ℝ) -
    elementwiseSampleContribution s A sample i j

/-- Literal untruncated one-sample residual increments are bounded in
rectangular operator norm by the exact input-dependent support radius. -/
theorem rectOpNorm2Le_elementwiseSampleResidualIncrement_literal_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    rectOpNorm2Le (elementwiseSampleResidualIncrement s A sample)
      (elementwiseLiteralResidualSupportRadius s A) := by
  classical
  apply rectOpNorm2Le_of_frobNormRect_le
  let C : Fin m → Fin n → ℝ := elementwiseSampleContribution s A sample
  have htri :
      frobNormRect (fun i j => (1 / (s : ℝ)) * A i j + (-1) * C i j) ≤
        frobNormRect (fun i j => (1 / (s : ℝ)) * A i j) +
          frobNormRect (fun i j => (-1) * C i j) :=
    frobNormRect_add_le
      (fun i j => (1 / (s : ℝ)) * A i j)
      (fun i j => (-1) * C i j)
  have hscaleA :
      frobNormRect (fun i j => (1 / (s : ℝ)) * A i j) =
        (1 / (s : ℝ)) * frobNormRect A := by
    rw [frobNormRect_smul]
    simp
  have hscaleC :
      frobNormRect (fun i j => (-1) * C i j) = frobNormRect C := by
    rw [frobNormRect_smul]
    norm_num
  have hcontrib :
      frobNormRect C ≤ elementwiseLiteralContributionRadius s A :=
    frobNormRect_elementwiseSampleContribution_literal_le hs A sample hsample
  have hres_shape :
      elementwiseSampleResidualIncrement s A sample =
        fun i j => (1 / (s : ℝ)) * A i j + (-1) * C i j := by
    ext i j
    simp [elementwiseSampleResidualIncrement, C]
    ring_nf
  calc
    frobNormRect (elementwiseSampleResidualIncrement s A sample)
        = frobNormRect
            (fun i j => (1 / (s : ℝ)) * A i j + (-1) * C i j) := by
            rw [hres_shape]
    _ ≤ frobNormRect (fun i j => (1 / (s : ℝ)) * A i j) +
          frobNormRect (fun i j => (-1) * C i j) := htri
    _ = (1 / (s : ℝ)) * frobNormRect A + frobNormRect C := by
          rw [hscaleA, hscaleC]
    _ ≤ (1 / (s : ℝ)) * frobNormRect A +
          elementwiseLiteralContributionRadius s A := by
          exact add_le_add (le_refl _) hcontrib
    _ = elementwiseLiteralResidualSupportRadius s A := by
          rfl

/-- The literal support radius is nonnegative when the sample count is
positive. -/
theorem elementwiseLiteralResidualSupportRadius_nonneg
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ) :
    0 ≤ elementwiseLiteralResidualSupportRadius s A := by
  unfold elementwiseLiteralResidualSupportRadius
  exact add_nonneg
    (mul_nonneg (by positivity) (frobNormRect_nonneg A))
    (elementwiseLiteralContributionRadius_nonneg hs A)

/-- The literal support radius is strictly positive for a nonzero matrix and a
positive sample count. -/
theorem elementwiseLiteralResidualSupportRadius_pos
    {m n s : ℕ} (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    0 < elementwiseLiteralResidualSupportRadius s A := by
  have hF_sq_pos : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hF_pos : 0 < frobNormRect A := by
    unfold frobNormRect
    exact Real.sqrt_pos.mpr hF_sq_pos
  unfold elementwiseLiteralResidualSupportRadius
  exact add_pos_of_pos_of_nonneg
    (mul_pos (by positivity) hF_pos)
    (elementwiseLiteralContributionRadius_nonneg hs A)

/-- Literal self-adjoint dilation increments are bounded above by the explicit
input-dependent support radius. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample))
      (fun a b =>
        elementwiseLiteralResidualSupportRadius s A * finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s A sample)
      (elementwiseLiteralResidualSupportRadius_nonneg hs A)
      (rectOpNorm2Le_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample)

/-- Literal self-adjoint dilation increments are bounded below by the negative
of the same explicit input-dependent support radius. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample : A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b)
      (fun a b =>
        elementwiseLiteralResidualSupportRadius s A * finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_neg_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s A sample)
      (elementwiseLiteralResidualSupportRadius_nonneg hs A)
      (rectOpNorm2Le_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample)

/-- Positive-probability support under the literal squared-magnitude law gives
the spectral upper-bound hypothesis needed by the support-aware C⋆ Bernstein
log-CGF theorem, with an explicit input-dependent radius. -/
theorem sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (sample : ElementwiseSample m n)
    (hsampleProb : 0 < (sqMagSampleProbability A hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)))) :
    x ≤ elementwiseLiteralResidualSupportRadius s A := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  have hsampleSq : 0 < sqMagProb A sample.1 sample.2 := by
    simpa [sqMagSampleProbability] using hsampleProb
  have hsample_ne : A sample.1 sample.2 ≠ 0 :=
    entry_ne_zero_of_sqMagProb_pos A sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [L] using
      finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample)) :=
    rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s A sample)
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hx

/-- Negative-increment companion of the literal support-radius spectral bound. -/
theorem sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
    {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (sample : ElementwiseSample m n)
    (hsampleProb : 0 < (sqMagSampleProbability A hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) :
    x ≤ elementwiseLiteralResidualSupportRadius s A := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  have hsampleSq : 0 < sqMagProb A sample.1 sample.2 := by
    simpa [sqMagSampleProbability] using hsampleProb
  have hsample_ne : A sample.1 sample.2 ≠ 0 :=
    entry_ne_zero_of_sqMagProb_pos A sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [L] using
      finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_literal_supportRadius
        hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
    intro a b
    change
      -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b =
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) b a
    rw [rectSelfAdjointDilation_symmetric]
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      -finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_neg, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  exact cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hx

/-- A one-row, two-column family with one unit entry and one arbitrarily small
positive entry.  It is used to show that literal squared-magnitude sampling
does not supply a uniform bounded-increment radius for untruncated Algorithm 1:
the small entry is sampled with positive probability, but its rescaled
contribution is proportional to the reciprocal of that entry. -/
noncomputable def algorithm1SmallEntrySupportMatrix (L : ℝ) :
    Fin 1 → Fin 2 → ℝ :=
  fun _ j => if j = (0 : Fin 2) then 1 else (|L| + 2)⁻¹

/-- The counterexample family has positive squared-magnitude denominator. -/
theorem sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (L : ℝ) :
    0 < sqMagProbDen (algorithm1SmallEntrySupportMatrix L) := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  simp [sqMagProbDen, frobNormSqRect, algorithm1SmallEntrySupportMatrix,
    add_pos_of_pos_of_nonneg zero_lt_one
      (le_of_lt (inv_pos.mpr (sq_pos_of_pos hbase)))]

/-- The small entry in the counterexample family has positive
squared-magnitude sampling probability. -/
theorem sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos (L : ℝ) :
    0 <
      sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2) := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  exact
    sqMagProb_pos_of_entry_ne_zero
      (algorithm1SmallEntrySupportMatrix L)
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
      (0 : Fin 1) (1 : Fin 2)
      (by
        simp [algorithm1SmallEntrySupportMatrix,
          inv_ne_zero (ne_of_gt hbase)])

/-- The small-entry sampling probability in the counterexample family is
strictly less than one. -/
theorem sqMagProb_algorithm1SmallEntrySupportMatrix_small_lt_one (L : ℝ) :
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2) < 1 := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hβ : 0 < ((|L| + 2) ^ 2)⁻¹ :=
    inv_pos.mpr (sq_pos_of_pos hbase)
  simp [sqMagProb, sqMagProbDen, frobNormSqRect,
    algorithm1SmallEntrySupportMatrix]
  change
    ((|L| + 2) ^ 2)⁻¹ /
        (1 + ((|L| + 2) ^ 2)⁻¹) < 1
  have hden : 0 < 1 + ((|L| + 2) ^ 2)⁻¹ := by
    nlinarith
  have hnum_lt_den :
      ((|L| + 2) ^ 2)⁻¹ < 1 + ((|L| + 2) ^ 2)⁻¹ := by
    nlinarith
  exact (div_lt_iff₀ hden).mpr (by simp [hnum_lt_den])

/-- On the positive-probability small-entry sample, the one-step literal
residual increment has arbitrarily large entry magnitude.

This is a formal obstruction to instantiating the repository's current
bounded-increment matrix-Bernstein route for the untruncated squared-magnitude
sampler by a radius depending only on dimensions, sample count, and the
Frobenius scale. -/
theorem algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq (L : ℝ) :
    |elementwiseSampleResidualIncrement 1
        (algorithm1SmallEntrySupportMatrix L)
        ((0 : Fin 1), (1 : Fin 2)) (0 : Fin 1) (1 : Fin 2)| =
      |L| + 2 := by
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hbase_ne : |L| + 2 ≠ 0 := ne_of_gt hbase
  have hden_ne : (1 + ((|L| + 2)⁻¹) ^ 2) ≠ 0 := by
    positivity
  have hres :
      elementwiseSampleResidualIncrement 1
          (algorithm1SmallEntrySupportMatrix L)
          ((0 : Fin 1), (1 : Fin 2)) (0 : Fin 1) (1 : Fin 2) =
        -(|L| + 2) := by
    simp [elementwiseSampleResidualIncrement, elementwiseSampleContribution,
      elementwiseIncrement, elementwiseIncrementWithProb, sqMagProb,
      sqMagProbDen, frobNormSqRect, algorithm1SmallEntrySupportMatrix]
    field_simp [hbase_ne]
    ring
  rw [hres, abs_neg, abs_of_pos hbase]

/-- The positive-probability small-entry sample in the counterexample family
violates the rectangular operator-2 support predicate at radius `L`. -/
theorem algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le
    (L : ℝ) :
    ¬ rectOpNorm2Le
      (elementwiseSampleResidualIncrement 1
        (algorithm1SmallEntrySupportMatrix L)
        ((0 : Fin 1), (1 : Fin 2))) L := by
  intro hnorm
  let M : Fin 1 → Fin 2 → ℝ :=
    elementwiseSampleResidualIncrement 1
      (algorithm1SmallEntrySupportMatrix L)
      ((0 : Fin 1), (1 : Fin 2))
  let x : Fin 2 → ℝ := finiteBasisVec (1 : Fin 2)
  have hxnorm : vecNorm2 x = 1 := by
    simp [x, finiteBasisVec, vecNorm2, vecNorm2Sq]
  have hleft :
      vecNorm2 (rectMatMulVec M x) =
        |elementwiseSampleResidualIncrement 1
          (algorithm1SmallEntrySupportMatrix L)
          ((0 : Fin 1), (1 : Fin 2)) (0 : Fin 1) (1 : Fin 2)| := by
    simp [M, x, rectMatMulVec, finiteBasisVec, vecNorm2, vecNorm2Sq]
    rw [Real.sqrt_sq_eq_abs]
  have hbound := hnorm x
  rw [hleft, hxnorm, mul_one,
    algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq] at hbound
  nlinarith [le_abs_self L]

/-- For every proposed entrywise support radius `L`, literal untruncated
squared-magnitude sampling admits a positive-probability sample whose exact
one-step residual increment exceeds that radius. -/
theorem exists_sqMagPositive_sampleResidualIncrement_entry_abs_gt (L : ℝ) :
    ∃ (A : Fin 1 → Fin 2 → ℝ) (sample : ElementwiseSample 1 2),
      0 < sqMagProbDen A ∧
      0 < sqMagProb A sample.1 sample.2 ∧
      L < |elementwiseSampleResidualIncrement 1 A sample
        (0 : Fin 1) (1 : Fin 2)| := by
  refine
    ⟨algorithm1SmallEntrySupportMatrix L,
      ((0 : Fin 1), (1 : Fin 2)),
      sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L,
      sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L, ?_⟩
  rw [algorithm1SmallEntrySupportMatrix_residual_increment_abs_eq]
  nlinarith [le_abs_self L]

/-- Therefore no proposed scalar radius `L` can bound all positive-probability
literal squared-magnitude one-step residual increments in the rectangular
operator-2 predicate used by the spectral concentration layer. -/
theorem exists_sqMagPositive_sampleResidualIncrement_not_rectOpNorm2Le
    (L : ℝ) :
    ∃ (A : Fin 1 → Fin 2 → ℝ) (sample : ElementwiseSample 1 2),
      0 < sqMagProbDen A ∧
      0 < sqMagProb A sample.1 sample.2 ∧
      ¬ rectOpNorm2Le (elementwiseSampleResidualIncrement 1 A sample) L := by
  refine
    ⟨algorithm1SmallEntrySupportMatrix L,
      ((0 : Fin 1), (1 : Fin 2)),
      sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L,
      sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L, ?_⟩
  exact algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le L

/-- For the one-step exact squared-magnitude trace law, the counterexample
family violates the radius-`L` exact Algorithm 1 spectral event with strictly
positive probability.  Thus the obstruction is not merely existential: it
occurs on an event of positive mass under the exact product law. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_smallEntry_pos
    (L : ℝ) :
    0 <
      (sqMagTraceProbability (steps := 1)
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 1 |
          ¬ rectOpNorm2Le
            (elementwiseTraceResidual 1
              (algorithm1SmallEntrySupportMatrix L) samples) L} := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let P := sqMagTraceProbability (steps := 1) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let Hit : Set (ElementwiseTrace 1 2 1) :=
    {samples | sampleHits samples (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)}
  let Bad : Set (ElementwiseTrace 1 2 1) :=
    {samples |
      ¬ rectOpNorm2Le (elementwiseTraceResidual 1 A samples) L}
  have hHitProb :
      P.eventProb Hit =
        sqMagProb A (0 : Fin 1) (1 : Fin 2) := by
    simpa [P, Hit, A] using
      sqMagTraceProbability_eventProb_sampleHits
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
        (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)
  have hHitProb_pos : 0 < P.eventProb Hit := by
    rw [hHitProb]
    exact sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hsubset : Hit ⊆ Bad := by
    intro samples hhit
    have hsamp :
        samples (0 : Fin 1) = ((0 : Fin 1), (1 : Fin 2)) :=
      Prod.ext hhit.1 hhit.2
    have htrace :
        elementwiseTraceResidual 1 A samples =
          elementwiseSampleResidualIncrement 1 A
            ((0 : Fin 1), (1 : Fin 2)) := by
      ext i j
      simp [elementwiseTraceResidual, elementwiseTraceSketch,
        elementwiseTraceContribution, elementwiseSampleResidualIncrement,
        elementwiseSampleContribution, sampleHits, hsamp]
    intro hnorm
    exact
      algorithm1SmallEntrySupportMatrix_residual_increment_not_rectOpNorm2Le L
        (by simpa [A, htrace] using hnorm)
  exact hHitProb_pos.trans_le (P.eventProb_mono hsubset)

/-- The same small-entry family also breaks an exact one-step copy-difference
operator bound: compare the trace that samples the tiny entry with the trace
that samples the unit entry. -/
theorem algorithm1SmallEntrySupportMatrix_trace_residual_small_unit_diff_not_rectOpNorm2Le
    (L : ℝ) :
    ¬ rectOpNorm2Le
      (fun i j =>
        elementwiseTraceResidual 1 (algorithm1SmallEntrySupportMatrix L)
          (fun _ : Fin 1 => ((0 : Fin 1), (1 : Fin 2))) i j -
        elementwiseTraceResidual 1 (algorithm1SmallEntrySupportMatrix L)
          (fun _ : Fin 1 => ((0 : Fin 1), (0 : Fin 2))) i j)
      L := by
  classical
  intro hnorm
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let samplesSmall : ElementwiseTrace 1 2 1 :=
    fun _ : Fin 1 => ((0 : Fin 1), (1 : Fin 2))
  let samplesUnit : ElementwiseTrace 1 2 1 :=
    fun _ : Fin 1 => ((0 : Fin 1), (0 : Fin 2))
  let M : Fin 1 → Fin 2 → ℝ :=
    fun i j =>
      elementwiseTraceResidual 1 A samplesSmall i j -
        elementwiseTraceResidual 1 A samplesUnit i j
  let x : Fin 2 → ℝ := finiteBasisVec (1 : Fin 2)
  have hxnorm : vecNorm2 x = 1 := by
    simp [x, finiteBasisVec, vecNorm2, vecNorm2Sq]
  have hleft :
      vecNorm2 (rectMatMulVec M x) = |M (0 : Fin 1) (1 : Fin 2)| := by
    simp [M, x, rectMatMulVec, finiteBasisVec, vecNorm2, vecNorm2Sq]
    rw [Real.sqrt_sq_eq_abs]
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hbase_ne : |L| + 2 ≠ 0 := ne_of_gt hbase
  have hentry :
      M (0 : Fin 1) (1 : Fin 2) =
        -((|L| + 2) + (|L| + 2)⁻¹) := by
    simp [M, A, samplesSmall, samplesUnit, elementwiseTraceResidual,
      elementwiseTraceSketch, elementwiseTraceContribution,
      sampleHits, elementwiseIncrement, elementwiseIncrementWithProb, sqMagProb,
      sqMagProbDen, frobNormSqRect, algorithm1SmallEntrySupportMatrix]
    field_simp [hbase_ne]
    ring_nf
  have hentry_gt : L < |M (0 : Fin 1) (1 : Fin 2)| := by
    rw [hentry, abs_neg]
    have hinv_pos : 0 < (|L| + 2)⁻¹ := inv_pos.mpr hbase
    rw [abs_of_pos (add_pos hbase hinv_pos)]
    nlinarith [le_abs_self L, hinv_pos]
  have hbound := hnorm x
  rw [hleft, hxnorm, mul_one] at hbound
  exact not_le_of_gt hentry_gt hbound

/-- A retained hard-thresholded one-sample residual increment has Frobenius
    norm bounded by the input share plus the contribution bound.  This is the
    scalar bounded-increment prerequisite for the matrix-Bernstein route. -/
theorem frobNormRect_elementwiseSampleResidualIncrement_truncated_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    frobNormRect
      (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample) ≤
      (1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let C : Fin m → Fin n → ℝ :=
    elementwiseSampleContribution s Ahat sample
  have htri :
      frobNormRect
        (fun i j => (1 / (s : ℝ)) * Ahat i j + (-1) * C i j) ≤
        frobNormRect (fun i j => (1 / (s : ℝ)) * Ahat i j) +
          frobNormRect (fun i j => (-1) * C i j) :=
    frobNormRect_add_le
      (fun i j => (1 / (s : ℝ)) * Ahat i j)
      (fun i j => (-1) * C i j)
  have hscaleA :
      frobNormRect (fun i j => (1 / (s : ℝ)) * Ahat i j) =
        (1 / (s : ℝ)) * frobNormRect Ahat := by
    rw [frobNormRect_smul]
    have hnonneg : 0 ≤ (1 / (s : ℝ)) := by positivity
    rw [abs_of_nonneg hnonneg]
  have hscaleC :
      frobNormRect (fun i j => (-1) * C i j) = frobNormRect C := by
    rw [frobNormRect_smul]
    norm_num
  have hcontrib :
      frobNormRect C ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    simpa [Ahat, C] using
      frobNormRect_elementwiseSampleContribution_truncated_le
        htau hs A sample hsample
  have hres_shape :
      elementwiseSampleResidualIncrement s Ahat sample =
        fun i j => (1 / (s : ℝ)) * Ahat i j + (-1) * C i j := by
    ext i j
    simp [elementwiseSampleResidualIncrement, C]
    ring_nf
  calc
    frobNormRect (elementwiseSampleResidualIncrement s Ahat sample)
        = frobNormRect
            (fun i j => (1 / (s : ℝ)) * Ahat i j + (-1) * C i j) := by
            rw [hres_shape]
    _ ≤ frobNormRect (fun i j => (1 / (s : ℝ)) * Ahat i j) +
          frobNormRect (fun i j => (-1) * C i j) := htri
    _ = (1 / (s : ℝ)) * frobNormRect Ahat + frobNormRect C := by
          rw [hscaleA, hscaleC]
    _ ≤ (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau) := by
          exact add_le_add (le_refl _) hcontrib

/-- Operator-norm predicate version of the retained truncated one-sample
    residual-increment Frobenius bound. -/
theorem rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    rectOpNorm2Le
      (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample)
      ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact frobNormRect_elementwiseSampleResidualIncrement_truncated_le
    htau hs A sample hsample

/-- Event that every one-sample residual increment in a trace of the truncated
    matrix is bounded by `L` in the rectangular operator-2 predicate. -/
def truncatedResidualIncrementsBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      rectOpNorm2Le
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) (samples t)) L}

/-- Under the canonical squared-magnitude product law for the truncated
    matrix, the retained-sample bounded-increment side condition holds with
    probability one.  This discharges the support issue for later
    Bernstein-style concentration theorems; it is not itself a tail bound. -/
theorem sqMagTraceProbability_eventProb_truncatedResidualIncrementsBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedResidualIncrementsBoundedEvent tau A
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedResidualIncrementsBoundedEvent tau A
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    exact
      rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
        htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat] using hbound_prob

/-- Self-adjoint-dilation version of the retained truncated one-sample
    residual-increment bound.  The `sqrt 2` factor is the elementary
    Frobenius bound for the dilation. -/
theorem finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample))
      (Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_nonneg : 0 ≤ L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    unfold L
    exact add_nonneg hfirst hsecond
  have hF :
      frobNormRect (elementwiseSampleResidualIncrement s Ahat sample) ≤ L := by
    simpa [Ahat, L] using
      frobNormRect_elementwiseSampleResidualIncrement_truncated_le
        htau hs A sample hsample
  simpa [Ahat, L] using
    finiteOpNorm2Le_rectSelfAdjointDilation_of_frobNormRect_le
      (elementwiseSampleResidualIncrement s Ahat sample) hL_nonneg hF

/-- Quadratic-form version of the retained truncated one-sample
    self-adjoint-dilation increment bound.

This is the scalar form consumed by support-aware finite-family MGF bounds.
The retained-entry hypothesis is later discharged from positive sampling
probability. -/
theorem finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0)
    (z : Fin m ⊕ Fin n → ℝ) :
    finiteQuadraticForm
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample)) z ≤
      (Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
        finiteVecNorm2Sq z := by
  exact
    finiteQuadraticForm_le_of_finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s (elementwiseTruncate tau A) sample))
      (finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample) z

/-- One-sided Loewner upper bound for each retained truncated self-adjoint
    dilation increment.  This is the `X_t <= L I` side condition used by
    largest-eigenvalue matrix Bernstein routes. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (fun a b =>
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_smul_id_of_finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample)

/-- Lower Loewner side for each retained truncated self-adjoint dilation
    increment, written as `-X_t <= L I`. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample) a b)
      (fun a b =>
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  exact
    finiteLoewnerLe_neg_smul_id_of_finiteOpNorm2Le
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample)

/-- Sharper one-sided Loewner upper bound for each retained truncated
    self-adjoint dilation increment.

Unlike `finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated`,
this uses the rectangular operator bound directly and therefore avoids the
auxiliary `sqrt 2` Frobenius-to-dilation loss.  This is the source-aligned
bounded-increment radius needed for the Drineas--Zouzias matrix Bernstein
constants. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s
          (elementwiseTruncate tau A) sample))
      (fun a b =>
        (((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_nonneg : 0 ≤ L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    unfold L
    exact add_nonneg hfirst hsecond
  have hrect :
      rectOpNorm2Le
        (elementwiseSampleResidualIncrement s Ahat sample) L := by
    simpa [Ahat, L] using
      rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample
  simpa [Ahat, L] using
    finiteLoewnerLe_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s Ahat sample) hL_nonneg hrect

/-- Sharper lower-tail companion for retained truncated dilation increments,
    also avoiding the `sqrt 2` Frobenius-to-dilation loss. -/
theorem finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample) a b)
      (fun a b =>
        (((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) *
          finiteIdMatrix a b) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_nonneg : 0 ≤ L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    unfold L
    exact add_nonneg hfirst hsecond
  have hrect :
      rectOpNorm2Le
        (elementwiseSampleResidualIncrement s Ahat sample) L := by
    simpa [Ahat, L] using
      rectOpNorm2Le_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample
  simpa [Ahat, L] using
    finiteLoewnerLe_neg_rectSelfAdjointDilation_of_rectOpNorm2Le
      (elementwiseSampleResidualIncrement s Ahat sample) hL_nonneg hrect

/-- Event that every self-adjoint dilation of a truncated residual increment is
    bounded by `L` in the finite square operator predicate. -/
def truncatedDilationIncrementsBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      finiteOpNorm2Le
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) (samples t))) L}

/-- Event that every retained truncated self-adjoint dilation increment is
    bounded above and below in Loewner order by `L I`. -/
def truncatedDilationIncrementLoewnerBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) (samples t)))
        (fun a b => L * finiteIdMatrix a b) ∧
      finiteLoewnerLe
        (fun a b =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t)) a b)
        (fun a b => L * finiteIdMatrix a b)}

/-- Under the canonical squared-magnitude product law for the truncated
    matrix, the self-adjoint dilation bounded-increment condition holds with
    probability one.  This is a Bernstein prerequisite, not the Bernstein tail
    theorem itself. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationIncrementsBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementsBoundedEvent tau A
      (Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)))
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    exact
      finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat] using hbound_prob

/-- Under the truncated squared-magnitude product law, the two-sided Loewner
    bounded-increment side condition for the self-adjoint dilation increments
    holds with probability one.  This is still a Bernstein prerequisite, not a
    trace-MGF or spectral tail theorem. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationIncrementLoewnerBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementLoewnerBoundedEvent tau A L
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    constructor
    · simpa [Ahat, L, Bound, truncatedDilationIncrementLoewnerBoundedEvent] using
        finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
          htau hs A (samples t) hsample_ne
    · simpa [Ahat, L, Bound, truncatedDilationIncrementLoewnerBoundedEvent] using
        finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
          htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat, L] using hbound_prob

/-- Squared-Loewner form of the retained truncated self-adjoint dilation
    increment bound.  This is the deterministic bounded-square hypothesis used
    by Bernstein-style matrix concentration. -/
theorem finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated
    {m n : ℕ} {tau : ℝ} (htau : 0 < tau) {s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (sample : ElementwiseSample m n)
    (hsample :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0) :
    finiteLoewnerLe
      (finiteMatMul
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample))
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s
            (elementwiseTruncate tau A) sample)))
      (fun a b =>
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) ^ 2 *
          finiteIdMatrix a b) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hinner_nonneg :
      0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    exact add_nonneg hfirst hsecond
  have hL_nonneg : 0 ≤ L := by
    unfold L
    exact mul_nonneg (Real.sqrt_nonneg 2) hinner_nonneg
  have hD :
      finiteOpNorm2Le
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample)) L := by
    simpa [Ahat, L] using
      finiteOpNorm2Le_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample
  simpa [Ahat, L] using
    rectSelfAdjointDilation_square_loewnerLe_scalar_id_of_finiteOpNorm2Le
      (elementwiseSampleResidualIncrement s Ahat sample) hD hL_nonneg

/-- Event that every squared self-adjoint dilation increment is bounded in
    Loewner order by `L^2 I`. -/
def truncatedDilationIncrementSquaresBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ t : Fin s,
      finiteLoewnerLe
        (finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t)))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t))))
        (fun a b => L ^ 2 * finiteIdMatrix a b)}

/-- The squared-Loewner bounded-increment event for truncated self-adjoint
    dilation increments has probability one under the truncated product law. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationIncrementSquaresBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementSquaresBoundedEvent tau A L
  have hgood_prob : P.eventProb Good = 1 := by
    simpa [P, Good, Ahat] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hsubset : Good ⊆ Bound := by
    intro samples hgood t
    have hsample_pos : 0 < sqMagProb Ahat (samples t).1 (samples t).2 :=
      hgood t
    have hsample_ne :
        elementwiseTruncate tau A (samples t).1 (samples t).2 ≠ 0 := by
      simpa [Ahat] using
        entry_ne_zero_of_sqMagProb_pos Ahat (samples t).1 (samples t).2
          hsample_pos
    simpa [Ahat, L, Bound, truncatedDilationIncrementSquaresBoundedEvent] using
      finiteLoewnerLe_rectSelfAdjointDilation_square_elementwiseSampleResidualIncrement_truncated
        htau hs A (samples t) hsample_ne
  have hmono : P.eventProb Good ≤ P.eventProb Bound :=
    FiniteProbability.eventProb_mono P hsubset
  have hge : 1 ≤ P.eventProb Bound := by
    linarith
  have hle : P.eventProb Bound ≤ 1 :=
    FiniteProbability.eventProb_le_one P Bound
  have hbound_prob : P.eventProb Bound = 1 := le_antisymm hle hge
  simpa [P, Bound, Ahat, L] using hbound_prob

/-- Simultaneous bounded-operator and bounded-square event for the
    self-adjoint dilation increments in the truncated Algorithm 1 route.  The
    two-sided Loewner component is included because Tropp-style Bernstein
    hypotheses are usually stated as `-L I <= X_t <= L I` or `lambda_max X_t
    <= L`, while the squared component is useful for variance proxies. -/
def truncatedDilationBernsteinBoundedEvent {m n s : ℕ}
    (tau : ℝ) (A : Fin m → Fin n → ℝ) (L : ℝ) :
    Set (ElementwiseTrace m n s) :=
  (truncatedDilationIncrementsBoundedEvent tau A L ∩
    truncatedDilationIncrementLoewnerBoundedEvent tau A L) ∩
    truncatedDilationIncrementSquaresBoundedEvent tau A L

/-- Under the truncated squared-magnitude product law, the simultaneous
    bounded-operator, two-sided Loewner, and bounded-square side conditions for
    the self-adjoint dilation increments have probability one. -/
theorem sqMagTraceProbability_eventProb_truncatedDilationBernsteinBoundedEvent_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (truncatedDilationBernsteinBoundedEvent tau A
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hOp :
      P.eventProb (truncatedDilationIncrementsBoundedEvent tau A L) = 1 := by
    simpa [P, Ahat, L] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementsBoundedEvent_eq_one
        htau hs A hden
  have hLoewner :
      P.eventProb (truncatedDilationIncrementLoewnerBoundedEvent tau A L) = 1 := by
    simpa [P, Ahat, L] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
        htau hs A hden
  have hSq :
      P.eventProb (truncatedDilationIncrementSquaresBoundedEvent tau A L) = 1 := by
    simpa [P, Ahat, L] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementSquaresBoundedEvent_eq_one
        htau hs A hden
  have hOpLoewner :
      P.eventProb
        (truncatedDilationIncrementsBoundedEvent tau A L ∩
          truncatedDilationIncrementLoewnerBoundedEvent tau A L) = 1 :=
    FiniteProbability.eventProb_inter_eq_one_of_eq_one P
      (truncatedDilationIncrementsBoundedEvent tau A L)
      (truncatedDilationIncrementLoewnerBoundedEvent tau A L)
      hOp hLoewner
  simpa [P, Ahat, L, truncatedDilationBernsteinBoundedEvent] using
    FiniteProbability.eventProb_inter_eq_one_of_eq_one P
      (truncatedDilationIncrementsBoundedEvent tau A L ∩
        truncatedDilationIncrementLoewnerBoundedEvent tau A L)
      (truncatedDilationIncrementSquaresBoundedEvent tau A L)
      hOpLoewner hSq

/-- The exact residual of an `s`-step Algorithm 1 trace is a sum of one-sample
    residual increments.  This is the algebraic shape needed by matrix
    concentration arguments. -/
theorem elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    elementwiseTraceResidual s A samples i j =
      ∑ t : Fin s, elementwiseSampleResidualIncrement s A (samples t) i j := by
  classical
  have hconst :
      (∑ _t : Fin s, A i j / (s : ℝ)) = A i j := by
    calc
      (∑ _t : Fin s, A i j / (s : ℝ))
          = (s : ℝ) * (A i j / (s : ℝ)) := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
      _ = A i j := by
              field_simp [hs]
  have hcontrib :
      (∑ t : Fin s, elementwiseSampleContribution s A (samples t) i j) =
        ∑ t : Fin s, elementwiseTraceContribution s A samples t i j := by
    apply Finset.sum_congr rfl
    intro t _
    rw [elementwiseTraceContribution_eq_sampleContribution]
  calc
    elementwiseTraceResidual s A samples i j
        = A i j -
            ∑ t : Fin s, elementwiseTraceContribution s A samples t i j := by
            simp [elementwiseTraceResidual, elementwiseTraceSketch]
    _ = (∑ t : Fin s, A i j / (s : ℝ)) -
            ∑ t : Fin s, elementwiseSampleContribution s A (samples t) i j := by
            rw [hconst, hcontrib]
    _ = ∑ t : Fin s, elementwiseSampleResidualIncrement s A (samples t) i j := by
            rw [← Finset.sum_sub_distrib]
            rfl

/-- One-step expectation of the exact Algorithm 1 contribution at a fixed
    entry under squared-magnitude probabilities. -/
theorem sqMagProb_sum_elementwiseSampleContribution_entry
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleContribution s A sample i j) =
      A i j / (s : ℝ) := by
  classical
  by_cases hAij_zero : A i j = 0
  · have hcontrib : ∀ sample : ElementwiseSample m n,
        elementwiseSampleContribution s A sample i j = 0 := by
      intro sample
      simp [elementwiseSampleContribution, elementwiseIncrement,
        elementwiseIncrementWithProb, hAij_zero]
    simp [hcontrib, hAij_zero]
  · have hp_ne : sqMagProb A i j ≠ 0 :=
      sqMagProb_ne_zero_of_entry_ne_zero A i j hAij_zero
    rw [Finset.sum_eq_single (i, j)]
    · simp [elementwiseSampleContribution]
      unfold elementwiseIncrement elementwiseIncrementWithProb
      field_simp [hs, hp_ne]
    · intro sample _ hsample
      have hnot : ¬ (sample.1 = i ∧ sample.2 = j) := by
        intro h
        apply hsample
        ext <;> simp [h.1, h.2]
      simp [elementwiseSampleContribution, hnot]
    · intro hnot
      simp at hnot

/-- The one-sample residual increment has zero mean under the squared-magnitude
    one-step law. -/
theorem sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j) = 0 := by
  classical
  have hprob :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2) = 1 :=
    sqMagProb_sum_samples_eq_one A hden.ne'
  have hcontrib :=
    sqMagProb_sum_elementwiseSampleContribution_entry s A hs i j
  have hconst :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * (A i j / (s : ℝ))) =
        A i j / (s : ℝ) := by
    rw [← Finset.sum_mul, hprob, one_mul]
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j)
        = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * (A i j / (s : ℝ))) -
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              elementwiseSampleContribution s A sample i j) := by
            simp [elementwiseSampleResidualIncrement, mul_sub,
              Finset.sum_sub_distrib]
    _ = A i j / (s : ℝ) - A i j / (s : ℝ) := by
            rw [hconst, hcontrib]
    _ = 0 := by ring

/-- The one-step contribution at a fixed entry has squared expectation at
    most `||A||_F^2 / s^2` under the squared-magnitude one-step law. -/
theorem sqMagProb_sum_elementwiseSampleContribution_entry_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleContribution s A sample i j ^ 2) ≤
      frobNormSqRect A / (s : ℝ) ^ 2 := by
  classical
  by_cases hAij_zero : A i j = 0
  · have hcontrib : ∀ sample : ElementwiseSample m n,
        elementwiseSampleContribution s A sample i j = 0 := by
      intro sample
      simp [elementwiseSampleContribution, elementwiseIncrement,
        elementwiseIncrementWithProb, hAij_zero]
    have hden_nonneg : 0 ≤ (s : ℝ) ^ 2 := sq_nonneg (s : ℝ)
    simp [hcontrib]
    exact div_nonneg (frobNormSqRect_nonneg A) hden_nonneg
  · have hp_ne : sqMagProb A i j ≠ 0 :=
      sqMagProb_ne_zero_of_entry_ne_zero A i j hAij_zero
    have hF_ne : frobNormSqRect A ≠ 0 :=
      frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij_zero
    have hsingle :
        sqMagProb A i j *
          elementwiseSampleContribution s A (i, j) i j ^ 2 =
          frobNormSqRect A / (s : ℝ) ^ 2 := by
      simp [elementwiseSampleContribution]
      unfold elementwiseIncrement elementwiseIncrementWithProb sqMagProb
        sqMagProbDen
      field_simp [hs, hAij_zero, hF_ne]
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          elementwiseSampleContribution s A sample i j ^ 2)
          = sqMagProb A i j *
              elementwiseSampleContribution s A (i, j) i j ^ 2 := by
            rw [Finset.sum_eq_single (i, j)]
            · intro sample _ hsample
              have hnot : ¬ (sample.1 = i ∧ sample.2 = j) := by
                intro h
                apply hsample
                ext <;> simp [h.1, h.2]
              simp [elementwiseSampleContribution, hnot]
            · intro hnot
              simp at hnot
      _ = frobNormSqRect A / (s : ℝ) ^ 2 := hsingle
      _ ≤ frobNormSqRect A / (s : ℝ) ^ 2 := le_rfl

/-- Applying a one-sample contribution matrix to a vector leaves only the
    sampled row active. -/
theorem vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (x : Fin n → ℝ) :
    vecNorm2Sq
      (rectMatMulVec (elementwiseSampleContribution s A sample) x) =
      (elementwiseIncrement s A sample.1 sample.2 * x sample.2) ^ 2 := by
  classical
  unfold vecNorm2Sq rectMatMulVec
  rw [Finset.sum_eq_single sample.1]
  · have hinner :
        (∑ j : Fin n,
          elementwiseSampleContribution s A sample sample.1 j * x j) =
          elementwiseIncrement s A sample.1 sample.2 * x sample.2 := by
      rw [Finset.sum_eq_single sample.2]
      · simp [elementwiseSampleContribution]
      · intro j _ hj
        have hneq : sample.2 ≠ j := by
          intro h
          exact hj h.symm
        simp [elementwiseSampleContribution, hneq]
      · intro hnot
        simp at hnot
    change
      (∑ j : Fin n,
        elementwiseSampleContribution s A sample sample.1 j * x j) ^ 2 =
        (elementwiseIncrement s A sample.1 sample.2 * x sample.2) ^ 2
    rw [hinner]
  · intro i _ hi
    have hinner :
        (∑ j : Fin n,
          elementwiseSampleContribution s A sample i j * x j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      have hneq : sample.1 ≠ i := by
        intro h
        exact hi h.symm
      simp [elementwiseSampleContribution, hneq]
    rw [hinner]
    ring
  · intro hnot
    simp at hnot

/-- Under squared-magnitude sampling, the weighted square of one contribution
    scalar cancels the sampling probability. -/
theorem sqMagProb_mul_elementwiseIncrement_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (i : Fin m) (j : Fin n) (x : ℝ) :
    sqMagProb A i j * (elementwiseIncrement s A i j * x) ^ 2 ≤
      (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
  classical
  by_cases hAij_zero : A i j = 0
  · have hrhs_nonneg :
        0 ≤ (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
      exact mul_nonneg
        (div_nonneg (frobNormSqRect_nonneg A) (sq_nonneg (s : ℝ)))
        (sq_nonneg x)
    simp [sqMagProb, elementwiseIncrement, elementwiseIncrementWithProb,
      hAij_zero, hrhs_nonneg]
  · have hp_ne : sqMagProb A i j ≠ 0 :=
      sqMagProb_ne_zero_of_entry_ne_zero A i j hAij_zero
    have hF_ne : frobNormSqRect A ≠ 0 :=
      frobNormSqRect_ne_zero_of_entry_ne_zero A i j hAij_zero
    have heq :
        sqMagProb A i j * (elementwiseIncrement s A i j * x) ^ 2 =
          (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
      let p : ℝ := sqMagProb A i j
      have hp_ne' : p ≠ 0 := by
        simpa [p] using hp_ne
      calc
        sqMagProb A i j * (elementwiseIncrement s A i j * x) ^ 2
            = p * ((A i j / ((s : ℝ) * p) * x) ^ 2) := by
                simp [p, elementwiseIncrement, elementwiseIncrementWithProb]
        _ = (A i j ^ 2 / ((s : ℝ) ^ 2 * p)) * x ^ 2 := by
                field_simp [hs, hp_ne']
        _ = (frobNormSqRect A / (s : ℝ) ^ 2) * x ^ 2 := by
                unfold p sqMagProb sqMagProbDen
                field_simp [hs, hAij_zero, hF_ne]
    rw [heq]

/-- Source-aligned one-step vector-action second-moment bound for the sampled
    contribution itself.  The dimension factor is the number of rows because a
    contribution has only one active row. -/
theorem sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (x : Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleContribution s A sample) x)) ≤
      ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq x := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleContribution s A sample) x))
        = ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (elementwiseIncrement s A sample.1 sample.2 * x sample.2) ^ 2 := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_eq]
    _ ≤ ∑ sample : ElementwiseSample m n,
          (frobNormSqRect A / (s : ℝ) ^ 2) * x sample.2 ^ 2 := by
          apply Finset.sum_le_sum
          intro sample _
          exact sqMagProb_mul_elementwiseIncrement_sq_le
            s A hs sample.1 sample.2 (x sample.2)
    _ = ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq x := by
          change
            (∑ sample : Fin m × Fin n,
              (frobNormSqRect A / (s : ℝ) ^ 2) * x sample.2 ^ 2) =
            ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
              vecNorm2Sq x
          rw [Fintype.sum_prod_type]
          unfold vecNorm2Sq
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          ring

/-- One-step vector-action mean identity for the sampled contribution. -/
theorem sqMagProb_sum_rectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (x : Fin n → ℝ) (i : Fin m) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleContribution s A sample) x i) =
      (1 / (s : ℝ)) * rectMatMulVec A x i := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleContribution s A sample) x i)
        = ∑ j : Fin n,
            (∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                elementwiseSampleContribution s A sample i j) * x j := by
            unfold rectMatMulVec
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ = ∑ j : Fin n, (A i j / (s : ℝ)) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sqMagProb_sum_elementwiseSampleContribution_entry
              s A hs i j]
    _ = (1 / (s : ℝ)) * rectMatMulVec A x i := by
            unfold rectMatMulVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring

/-- Source-aligned one-step vector-action second-moment bound for the centered
    residual increment.  This avoids the Frobenius detour used by the older
    `m*n` bound. -/
theorem sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x)) ≤
      ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq x := by
  classical
  let p : ElementwiseSample m n → ℝ := fun sample =>
    sqMagProb A sample.1 sample.2
  let a : Fin m → ℝ := fun i => (1 / (s : ℝ)) * rectMatMulVec A x i
  let C : ElementwiseSample m n → Fin m → ℝ := fun sample i =>
    rectMatMulVec (elementwiseSampleContribution s A sample) x i
  have hprob : (∑ sample : ElementwiseSample m n, p sample) = 1 := by
    simpa [p] using sqMagProb_sum_samples_eq_one A hden.ne'
  have hCmean : ∀ i : Fin m,
      (∑ sample : ElementwiseSample m n, p sample * C sample i) = a i := by
    intro i
    simpa [p, C, a] using
      sqMagProb_sum_rectMatMulVec_elementwiseSampleContribution_eq
        s A hs x i
  have hres : ∀ sample : ElementwiseSample m n,
      rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x =
        fun i => a i - C sample i := by
    intro sample
    ext i
    unfold rectMatMulVec elementwiseSampleResidualIncrement a C
    calc
      (∑ j : Fin n,
        (A i j / (s : ℝ) -
            elementwiseSampleContribution s A sample i j) * x j)
          = (∑ j : Fin n, (A i j / (s : ℝ)) * x j) -
              ∑ j : Fin n,
                elementwiseSampleContribution s A sample i j * x j := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (1 / (s : ℝ)) * (∑ j : Fin n, A i j * x j) -
              ∑ j : Fin n,
                elementwiseSampleContribution s A sample i j * x j := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  have hrow : ∀ i : Fin m,
      (∑ sample : ElementwiseSample m n,
        p sample * (a i - C sample i) ^ 2) ≤
        ∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2 := by
    intro i
    have hcross :
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a i * C sample i)) = 2 * a i ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a i * C sample i))
            = 2 * a i *
                (∑ sample : ElementwiseSample m n, p sample * C sample i) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = 2 * a i ^ 2 := by
                rw [hCmean i]
                ring
    have hconst :
        (∑ sample : ElementwiseSample m n, p sample * a i ^ 2) =
          a i ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n, p sample * a i ^ 2)
            = a i ^ 2 * (∑ sample : ElementwiseSample m n, p sample) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = a i ^ 2 := by
                rw [hprob]
                ring
    have hvariance :
        (∑ sample : ElementwiseSample m n,
          p sample * (a i - C sample i) ^ 2) =
          (∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2) -
            a i ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (a i - C sample i) ^ 2)
            = ∑ sample : ElementwiseSample m n,
                p sample * (C sample i ^ 2 -
                  2 * a i * C sample i + a i ^ 2) := by
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = (∑ sample : ElementwiseSample m n,
              p sample * C sample i ^ 2) -
            (∑ sample : ElementwiseSample m n,
              p sample * (2 * a i * C sample i)) +
            (∑ sample : ElementwiseSample m n, p sample * a i ^ 2) := by
                simp [mul_sub, mul_add, Finset.sum_sub_distrib,
                  Finset.sum_add_distrib]
        _ = (∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2) -
              a i ^ 2 := by
                rw [hcross, hconst]
                ring
    calc
      (∑ sample : ElementwiseSample m n,
        p sample * (a i - C sample i) ^ 2)
          = (∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2) -
              a i ^ 2 := hvariance
      _ ≤ ∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2 := by
          nlinarith [sq_nonneg (a i)]
  have hcontrib :=
    sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleContribution_le
      s A hs x
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x))
        = ∑ i : Fin m,
            ∑ sample : ElementwiseSample m n,
              p sample * (a i - C sample i) ^ 2 := by
            unfold vecNorm2Sq
            simp_rw [p, hres]
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin m,
          ∑ sample : ElementwiseSample m n, p sample * C sample i ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          exact hrow i
    _ = ∑ sample : ElementwiseSample m n,
          p sample * vecNorm2Sq (C sample) := by
          unfold vecNorm2Sq
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro sample _
          rw [Finset.mul_sum]
    _ = ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            vecNorm2Sq
              (rectMatMulVec (elementwiseSampleContribution s A sample) x) := by
          apply Finset.sum_congr rfl
          intro sample _
          simp [p, C]
    _ ≤ ((m : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq x := hcontrib

/-- Applying the transpose-action of a one-sample contribution matrix to a
    vector leaves only the sampled column active. -/
theorem vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (y : Fin m → ℝ) :
    vecNorm2Sq
      (fun j : Fin n =>
        ∑ i : Fin m, elementwiseSampleContribution s A sample i j * y i) =
      (elementwiseIncrement s A sample.1 sample.2 * y sample.1) ^ 2 := by
  classical
  unfold vecNorm2Sq
  rw [Finset.sum_eq_single sample.2]
  · have hinner :
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i sample.2 * y i) =
          elementwiseIncrement s A sample.1 sample.2 * y sample.1 := by
      rw [Finset.sum_eq_single sample.1]
      · simp [elementwiseSampleContribution]
      · intro i _ hi
        have hneq : sample.1 ≠ i := by
          intro h
          exact hi h.symm
        simp [elementwiseSampleContribution, hneq]
      · intro hnot
        simp at hnot
    change
      (∑ i : Fin m,
        elementwiseSampleContribution s A sample i sample.2 * y i) ^ 2 =
        (elementwiseIncrement s A sample.1 sample.2 * y sample.1) ^ 2
    rw [hinner]
  · intro j _ hj
    have hinner :
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i j * y i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hneq : sample.2 ≠ j := by
        intro h
        exact hj h.symm
      simp [elementwiseSampleContribution, hneq]
    change
      (∑ i : Fin m,
        elementwiseSampleContribution s A sample i j * y i) ^ 2 = 0
    rw [hinner]
    ring
  · intro hnot
    simp at hnot

/-- Source-aligned one-step transpose-vector second-moment bound for sampled
    contributions.  The dimension factor is the number of columns. -/
theorem sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (y : Fin m → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleContribution s A sample i j * y i)) ≤
      ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq y := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleContribution s A sample i j * y i))
        = ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (elementwiseIncrement s A sample.1 sample.2 * y sample.1) ^ 2 := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_eq]
    _ ≤ ∑ sample : ElementwiseSample m n,
          (frobNormSqRect A / (s : ℝ) ^ 2) * y sample.1 ^ 2 := by
          apply Finset.sum_le_sum
          intro sample _
          exact sqMagProb_mul_elementwiseIncrement_sq_le
            s A hs sample.1 sample.2 (y sample.1)
    _ = ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq y := by
          change
            (∑ sample : Fin m × Fin n,
              (frobNormSqRect A / (s : ℝ) ^ 2) * y sample.1 ^ 2) =
            ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
              vecNorm2Sq y
          rw [Fintype.sum_prod_type]
          unfold vecNorm2Sq
          simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
          calc
            (∑ x : Fin m,
              (n : ℝ) * ((frobNormSqRect A / (s : ℝ) ^ 2) * y x ^ 2))
                = ∑ x : Fin m,
                    ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
                      y x ^ 2 := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
            _ = ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
                  ∑ i : Fin m, y i ^ 2 := by
                    rw [Finset.mul_sum]

/-- One-step transpose-vector mean identity for the sampled contribution. -/
theorem sqMagProb_sum_transposeRectMatMulVec_elementwiseSampleContribution_eq
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hs : (s : ℝ) ≠ 0) (y : Fin m → ℝ) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i j * y i)) =
      (1 / (s : ℝ)) * ∑ i : Fin m, A i j * y i := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        (∑ i : Fin m,
          elementwiseSampleContribution s A sample i j * y i))
        = ∑ i : Fin m,
            (∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                elementwiseSampleContribution s A sample i j) * y i := by
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ = ∑ i : Fin m, (A i j / (s : ℝ)) * y i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [sqMagProb_sum_elementwiseSampleContribution_entry
              s A hs i j]
    _ = (1 / (s : ℝ)) * ∑ i : Fin m, A i j * y i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring

/-- Source-aligned one-step transpose-vector second-moment bound for the
    centered residual increment. -/
theorem sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (y : Fin m → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleResidualIncrement s A sample i j * y i)) ≤
      ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq y := by
  classical
  let p : ElementwiseSample m n → ℝ := fun sample =>
    sqMagProb A sample.1 sample.2
  let a : Fin n → ℝ := fun j => (1 / (s : ℝ)) * ∑ i : Fin m, A i j * y i
  let C : ElementwiseSample m n → Fin n → ℝ := fun sample j =>
    ∑ i : Fin m, elementwiseSampleContribution s A sample i j * y i
  have hprob : (∑ sample : ElementwiseSample m n, p sample) = 1 := by
    simpa [p] using sqMagProb_sum_samples_eq_one A hden.ne'
  have hCmean : ∀ j : Fin n,
      (∑ sample : ElementwiseSample m n, p sample * C sample j) = a j := by
    intro j
    simpa [p, C, a] using
      sqMagProb_sum_transposeRectMatMulVec_elementwiseSampleContribution_eq
        s A hs y j
  have hres : ∀ sample : ElementwiseSample m n,
      (fun j : Fin n =>
        ∑ i : Fin m,
          elementwiseSampleResidualIncrement s A sample i j * y i) =
        fun j => a j - C sample j := by
    intro sample
    ext j
    unfold elementwiseSampleResidualIncrement a C
    calc
      (∑ i : Fin m,
        (A i j / (s : ℝ) -
            elementwiseSampleContribution s A sample i j) * y i)
          = (∑ i : Fin m, (A i j / (s : ℝ)) * y i) -
              ∑ i : Fin m,
                elementwiseSampleContribution s A sample i j * y i := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (1 / (s : ℝ)) * (∑ i : Fin m, A i j * y i) -
              ∑ i : Fin m,
                elementwiseSampleContribution s A sample i j * y i := by
              congr 1
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
  have hrow : ∀ j : Fin n,
      (∑ sample : ElementwiseSample m n,
        p sample * (a j - C sample j) ^ 2) ≤
        ∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2 := by
    intro j
    have hcross :
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a j * C sample j)) = 2 * a j ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (2 * a j * C sample j))
            = 2 * a j *
                (∑ sample : ElementwiseSample m n, p sample * C sample j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = 2 * a j ^ 2 := by
                rw [hCmean j]
                ring
    have hconst :
        (∑ sample : ElementwiseSample m n, p sample * a j ^ 2) =
          a j ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n, p sample * a j ^ 2)
            = a j ^ 2 * (∑ sample : ElementwiseSample m n, p sample) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = a j ^ 2 := by
                rw [hprob]
                ring
    have hvariance :
        (∑ sample : ElementwiseSample m n,
          p sample * (a j - C sample j) ^ 2) =
          (∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2) -
            a j ^ 2 := by
      calc
        (∑ sample : ElementwiseSample m n,
          p sample * (a j - C sample j) ^ 2)
            = ∑ sample : ElementwiseSample m n,
                p sample * (C sample j ^ 2 -
                  2 * a j * C sample j + a j ^ 2) := by
                apply Finset.sum_congr rfl
                intro sample _
                ring
        _ = (∑ sample : ElementwiseSample m n,
              p sample * C sample j ^ 2) -
            (∑ sample : ElementwiseSample m n,
              p sample * (2 * a j * C sample j)) +
            (∑ sample : ElementwiseSample m n, p sample * a j ^ 2) := by
                simp [mul_sub, mul_add, Finset.sum_sub_distrib,
                  Finset.sum_add_distrib]
        _ = (∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2) -
              a j ^ 2 := by
                rw [hcross, hconst]
                ring
    calc
      (∑ sample : ElementwiseSample m n,
        p sample * (a j - C sample j) ^ 2)
          = (∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2) -
              a j ^ 2 := hvariance
      _ ≤ ∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2 := by
          nlinarith [sq_nonneg (a j)]
  have hcontrib :=
    sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleContribution_le
      s A hs y
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleResidualIncrement s A sample i j * y i))
        = ∑ sample : ElementwiseSample m n,
            p sample * vecNorm2Sq (fun j : Fin n => a j - C sample j) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [hres sample]
    _ = ∑ j : Fin n,
            ∑ sample : ElementwiseSample m n,
              p sample * (a j - C sample j) ^ 2 := by
            unfold vecNorm2Sq
            simp_rw [Finset.mul_sum]
            rw [Finset.sum_comm]
    _ ≤ ∑ j : Fin n,
          ∑ sample : ElementwiseSample m n, p sample * C sample j ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          exact hrow j
    _ = ∑ sample : ElementwiseSample m n,
          p sample * vecNorm2Sq (C sample) := by
          unfold vecNorm2Sq
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro sample _
          rw [Finset.mul_sum]
    _ = ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            vecNorm2Sq
              (fun j : Fin n =>
                ∑ i : Fin m,
                  elementwiseSampleContribution s A sample i j * y i) := by
          apply Finset.sum_congr rfl
          intro sample _
          simp [p, C]
    _ ≤ ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq y := hcontrib

/-- The one-step residual increment at a fixed entry has squared expectation
    at most `||A||_F^2 / s^2` under the squared-magnitude one-step law.  This
    is the scalar variance proxy needed before a matrix concentration theorem
    can be formalized for CACM equation (2). -/
theorem sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j ^ 2) ≤
      frobNormSqRect A / (s : ℝ) ^ 2 := by
  classical
  let a : ℝ := A i j / (s : ℝ)
  let C : ElementwiseSample m n → ℝ := fun sample =>
    elementwiseSampleContribution s A sample i j
  have hprob :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2) = 1 :=
    sqMagProb_sum_samples_eq_one A hden.ne'
  have hCmean :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * C sample) = a := by
    simpa [C, a] using
      sqMagProb_sum_elementwiseSampleContribution_entry s A hs i j
  have hCsq :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * C sample ^ 2) ≤
        frobNormSqRect A / (s : ℝ) ^ 2 := by
    simpa [C] using
      sqMagProb_sum_elementwiseSampleContribution_entry_sq_le s A hs i j
  have hcross :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * (2 * a * C sample)) = 2 * a ^ 2 := by
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * (2 * a * C sample))
          = 2 * a *
              (∑ sample : ElementwiseSample m n,
                sqMagProb A sample.1 sample.2 * C sample) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro sample _
              ring
      _ = 2 * a ^ 2 := by
              rw [hCmean]
              ring
  have hconst_sq :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * a ^ 2) = a ^ 2 := by
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 * a ^ 2)
          = a ^ 2 *
              (∑ sample : ElementwiseSample m n,
                sqMagProb A sample.1 sample.2) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro sample _
              ring
      _ = a ^ 2 := by
              rw [hprob]
              ring
  have hres :
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          elementwiseSampleResidualIncrement s A sample i j ^ 2) =
        (∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 * C sample ^ 2) - a ^ 2 := by
    calc
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          elementwiseSampleResidualIncrement s A sample i j ^ 2)
          = ∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                (a - C sample) ^ 2 := by
              apply Finset.sum_congr rfl
              intro sample _
              simp [elementwiseSampleResidualIncrement, C, a]
      _ = ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (C sample ^ 2 - 2 * a * C sample + a ^ 2) := by
              apply Finset.sum_congr rfl
              intro sample _
              ring
      _ = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * C sample ^ 2) -
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * (2 * a * C sample)) +
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * a ^ 2) := by
              simp [mul_sub, mul_add, Finset.sum_sub_distrib,
                Finset.sum_add_distrib]
      _ = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * C sample ^ 2) - a ^ 2 := by
              rw [hcross, hconst_sq]
              ring
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        elementwiseSampleResidualIncrement s A sample i j ^ 2)
        = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 * C sample ^ 2) - a ^ 2 := hres
    _ ≤ ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 * C sample ^ 2 := by
          nlinarith [sq_nonneg a]
    _ ≤ frobNormSqRect A / (s : ℝ) ^ 2 := hCsq

/-- The one-step residual increment has a squared-Frobenius second-moment
    bound obtained by summing the entrywise variance proxy. -/
theorem sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        frobNormSqRect (elementwiseSampleResidualIncrement s A sample)) ≤
      (m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2) := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        frobNormSqRect (elementwiseSampleResidualIncrement s A sample))
        = ∑ sample : ElementwiseSample m n, ∑ i : Fin m, ∑ j : Fin n,
            sqMagProb A sample.1 sample.2 *
              elementwiseSampleResidualIncrement s A sample i j ^ 2 := by
            unfold frobNormSqRect
            apply Finset.sum_congr rfl
            intro sample _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    _ = ∑ i : Fin m, ∑ j : Fin n, ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            elementwiseSampleResidualIncrement s A sample i j ^ 2 := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_comm]
    _ ≤ ∑ i : Fin m, ∑ j : Fin n,
          frobNormSqRect A / (s : ℝ) ^ 2 := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact
              sqMagProb_sum_elementwiseSampleResidualIncrement_entry_sq_le
                s A hden hs i j
    _ = (m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            ring

/-- The self-adjoint dilation of the one-step residual increment has a
    squared-Frobenius second-moment bound.  The factor `2` comes from the two
    off-diagonal blocks in the dilation. -/
theorem sqMagProb_sum_finiteFrobNormSq_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteFrobNormSq
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))) ≤
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) := by
  classical
  have hFrob :=
    sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
      s A hden hs
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteFrobNormSq
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)))
        = 2 *
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              frobNormSqRect
                (elementwiseSampleResidualIncrement s A sample)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro sample _
            rw [finiteFrobNormSq_rectSelfAdjointDilation]
            ring
    _ ≤ 2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hFrob (by linarith)

/-- Quadratic-form variance proxy for the one-step self-adjoint dilation
    residual increment.

This is the matrix-concentration object behind a Bernstein-style proof: for
every deterministic test vector, the expected quadratic form of the squared
dilation increment is controlled by the same explicit Frobenius proxy. -/
theorem sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) *
        finiteVecNorm2Sq x := by
  classical
  have hFrob :=
    sqMagProb_sum_finiteFrobNormSq_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_le
      s A hden hs
  have hx_nonneg : 0 ≤ finiteVecNorm2Sq x := finiteVecNorm2Sq_nonneg x
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
        ≤ ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (finiteFrobNormSq
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) *
                finiteVecNorm2Sq x) := by
            apply Finset.sum_le_sum
            intro sample _
            exact mul_le_mul_of_nonneg_left
              (finiteQuadraticForm_finiteMatMul_self_le_finiteFrobNormSq_mul_of_symmetric
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation_symmetric
                  (elementwiseSampleResidualIncrement s A sample)) x)
              (sqMagProb_nonneg A hden sample.1 sample.2)
    _ = (∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteFrobNormSq
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) *
          finiteVecNorm2Sq x := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ ≤ (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2))) *
          finiteVecNorm2Sq x :=
            mul_le_mul_of_nonneg_right hFrob hx_nonneg

/-- Source-sharp square-matrix quadratic-form variance proxy for the one-step
    self-adjoint dilation residual increment.

This is the Drineas--Zouzias variance scale: for an `n × n` matrix, the
one-step dilation variance is controlled by
`n * ||A||_F^2 / s^2`, not by the older Frobenius-detour
`2 * n^2 * ||A||_F^2 / s^2` proxy. -/
theorem sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square
    {n : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n ⊕ Fin n → ℝ) :
    (∑ sample : ElementwiseSample n n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x) ≤
      ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        finiteVecNorm2Sq x := by
  classical
  let y : Fin n → ℝ := fun i => x (Sum.inl i)
  let z : Fin n → ℝ := fun j => x (Sum.inr j)
  let C : ℝ := (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)
  have hx_decomp : sumBothVec y z = x := by
    ext a
    cases a <;> rfl
  have hqform : ∀ sample : ElementwiseSample n n,
      finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x =
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) z) +
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin n,
              elementwiseSampleResidualIncrement s A sample i j * y i) := by
    intro sample
    let M : Fin n → Fin n → ℝ :=
      elementwiseSampleResidualIncrement s A sample
    calc
      finiteQuadraticForm
          (finiteMatMul (rectSelfAdjointDilation M)
            (rectSelfAdjointDilation M)) x
          = finiteQuadraticForm
              (finiteMatMul (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation M)) (sumBothVec y z) := by
              rw [hx_decomp]
      _ = finiteVecNorm2Sq
            (finiteMatVec (rectSelfAdjointDilation M) (sumBothVec y z)) := by
              rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric
                (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation_symmetric M)]
      _ = finiteVecNorm2Sq
            (sumBothVec (rectMatMulVec M z)
              (fun j : Fin n => ∑ i : Fin n, M i j * y i)) := by
              rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
      _ = vecNorm2Sq (rectMatMulVec M z) +
            vecNorm2Sq
              (fun j : Fin n => ∑ i : Fin n, M i j * y i) := by
              rw [finiteVecNorm2Sq_sumBothVec]
              simp [finiteVecNorm2Sq_fin]
  have hright :=
    sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs z
  have hleft :=
    sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs y
  have hnorm :
      finiteVecNorm2Sq x = vecNorm2Sq y + vecNorm2Sq z := by
    rw [← hx_decomp, finiteVecNorm2Sq_sumBothVec]
    simp [finiteVecNorm2Sq_fin]
  calc
    (∑ sample : ElementwiseSample n n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
        = (∑ sample : ElementwiseSample n n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (rectMatMulVec
                  (elementwiseSampleResidualIncrement s A sample) z)) +
          (∑ sample : ElementwiseSample n n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (fun j : Fin n =>
                  ∑ i : Fin n,
                    elementwiseSampleResidualIncrement s A sample i j * y i)) := by
            simp_rw [hqform]
            simp [mul_add, Finset.sum_add_distrib]
    _ ≤ C * vecNorm2Sq z + C * vecNorm2Sq y := by
          exact add_le_add (by simpa [C] using hright) (by simpa [C] using hleft)
    _ = C * finiteVecNorm2Sq x := by
          rw [hnorm]
          ring
    _ = ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteVecNorm2Sq x := by
          rfl

/-- Source-aligned rectangular quadratic-form variance proxy for the one-step
    self-adjoint dilation residual increment.

For an `m × n` matrix, the vector-action decomposition gives the variance
scale `max m n * ||A||_F^2 / s^2`, improving the older Frobenius-detour
`2mn * ||A||_F^2 / s^2` proxy without imposing truncation or a small-entry
floor. -/
theorem sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) *
        finiteVecNorm2Sq x := by
  classical
  let y : Fin m → ℝ := fun i => x (Sum.inl i)
  let z : Fin n → ℝ := fun j => x (Sum.inr j)
  let F : ℝ := frobNormSqRect A / (s : ℝ) ^ 2
  let C : ℝ := max (m : ℝ) (n : ℝ) * F
  have hF_nonneg : 0 ≤ F := by
    exact div_nonneg (frobNormSqRect_nonneg A) (sq_nonneg (s : ℝ))
  have hx_decomp : sumBothVec y z = x := by
    ext a
    cases a <;> rfl
  have hqform : ∀ sample : ElementwiseSample m n,
      finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x =
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) z) +
        vecNorm2Sq
          (fun j : Fin n =>
            ∑ i : Fin m,
              elementwiseSampleResidualIncrement s A sample i j * y i) := by
    intro sample
    let M : Fin m → Fin n → ℝ :=
      elementwiseSampleResidualIncrement s A sample
    calc
      finiteQuadraticForm
          (finiteMatMul (rectSelfAdjointDilation M)
            (rectSelfAdjointDilation M)) x
          = finiteQuadraticForm
              (finiteMatMul (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation M)) (sumBothVec y z) := by
              rw [hx_decomp]
      _ = finiteVecNorm2Sq
            (finiteMatVec (rectSelfAdjointDilation M) (sumBothVec y z)) := by
              rw [finiteQuadraticForm_finiteMatMul_self_of_symmetric
                (rectSelfAdjointDilation M)
                (rectSelfAdjointDilation_symmetric M)]
      _ = finiteVecNorm2Sq
            (sumBothVec (rectMatMulVec M z)
              (fun j : Fin n => ∑ i : Fin m, M i j * y i)) := by
              rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
      _ = vecNorm2Sq (rectMatMulVec M z) +
            vecNorm2Sq
              (fun j : Fin n => ∑ i : Fin m, M i j * y i) := by
              rw [finiteVecNorm2Sq_sumBothVec]
              simp [finiteVecNorm2Sq_fin]
  have hright :=
    sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs z
  have hleft :=
    sqMagProb_sum_vecNorm2Sq_transposeRectMatMulVec_elementwiseSampleResidualIncrement_le_sharp
      s A hden hs y
  have hrightC :
      ((m : ℝ) * F) * vecNorm2Sq z ≤ C * vecNorm2Sq z := by
    have hmC : (m : ℝ) * F ≤ C := by
      exact mul_le_mul_of_nonneg_right
        (le_max_left (m : ℝ) (n : ℝ)) hF_nonneg
    exact mul_le_mul_of_nonneg_right hmC (vecNorm2Sq_nonneg z)
  have hleftC :
      ((n : ℝ) * F) * vecNorm2Sq y ≤ C * vecNorm2Sq y := by
    have hnC : (n : ℝ) * F ≤ C := by
      exact mul_le_mul_of_nonneg_right
        (le_max_right (m : ℝ) (n : ℝ)) hF_nonneg
    exact mul_le_mul_of_nonneg_right hnC (vecNorm2Sq_nonneg y)
  have hnorm :
      finiteVecNorm2Sq x = vecNorm2Sq y + vecNorm2Sq z := by
    rw [← hx_decomp, finiteVecNorm2Sq_sumBothVec]
    simp [finiteVecNorm2Sq_fin]
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
        = (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (rectMatMulVec
                  (elementwiseSampleResidualIncrement s A sample) z)) +
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              vecNorm2Sq
                (fun j : Fin n =>
                  ∑ i : Fin m,
                    elementwiseSampleResidualIncrement s A sample i j * y i)) := by
            simp_rw [hqform]
            simp [mul_add, Finset.sum_add_distrib]
    _ ≤ ((m : ℝ) * F) * vecNorm2Sq z +
          ((n : ℝ) * F) * vecNorm2Sq y := by
          exact add_le_add
            (by simpa [F] using hright)
            (by simpa [F] using hleft)
    _ ≤ C * vecNorm2Sq z + C * vecNorm2Sq y := by
          exact add_le_add hrightC hleftC
    _ = C * finiteVecNorm2Sq x := by
          rw [hnorm]
          ring
    _ = (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteVecNorm2Sq x := by
          rfl

/-- Loewner-form one-step variance proxy for the squared self-adjoint dilation
    residual increment.

This is the same mathematical content as
`sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le`, packaged
as a matrix-order statement.  It is a matrix-concentration prerequisite, not a
tail theorem. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2))) *
          finiteIdMatrix a b) := by
  classical
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    s A hden hs x

/-- Source-sharp square-matrix Loewner variance proxy for the squared
    self-adjoint dilation residual increment. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square
    {n : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        ∑ sample : ElementwiseSample n n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        ((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteIdMatrix a b) := by
  classical
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_square
      s A hden hs x

/-- Source-aligned rectangular Loewner variance proxy for the squared
    self-adjoint dilation residual increment. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteLoewnerLe
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) *
          finiteIdMatrix a b) := by
  classical
  intro x
  rw [finiteQuadraticForm_fintype_sum_smul,
    finiteQuadraticForm_smul_finiteIdMatrix]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      s A hden hs x

/-- The one-step self-adjoint dilation variance matrix is positive
    semidefinite. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_square_psd
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    finitePSD
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b) := by
  classical
  apply finitePSD_fintype_sum_smul_of_nonneg
  · intro sample
    exact sqMagProb_nonneg A hden sample.1 sample.2
  · intro sample
    exact finitePSD_rectSelfAdjointDilation_square
      (elementwiseSampleResidualIncrement s A sample)

/-- Summed quadratic-form variance proxy over the `s` independent one-step
    dilation increments.  This is the deterministic variance-parameter shape
    used by a future matrix Bernstein theorem: the per-step proxy above sums
    to an order `||A||_F^2 / s` quantity. -/
theorem sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ)))) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
      s A hden (ne_of_gt hs) x
  calc
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x)
        ≤ ∑ _t : Fin s,
            (2 * ((m : ℝ) * (n : ℝ) *
              (frobNormSqRect A / (s : ℝ) ^ 2))) *
              finiteVecNorm2Sq x := by
            apply Finset.sum_le_sum
            intro t _
            exact hstep
    _ = (s : ℝ) *
          ((2 * ((m : ℝ) * (n : ℝ) *
            (frobNormSqRect A / (s : ℝ) ^ 2))) *
            finiteVecNorm2Sq x) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ = (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ)))) *
          finiteVecNorm2Sq x := by
            field_simp [ne_of_gt hs]

/-- Source-aligned rectangular summed quadratic-form variance proxy over the
    `s` independent one-step dilation increments. -/
theorem sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ))) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      s A hden (ne_of_gt hs) x
  calc
    (∑ _t : Fin s,
      ∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))) x)
        ≤ ∑ _t : Fin s,
            (max (m : ℝ) (n : ℝ) *
              (frobNormSqRect A / (s : ℝ) ^ 2)) *
              finiteVecNorm2Sq x := by
            apply Finset.sum_le_sum
            intro t _
            exact hstep
    _ = (s : ℝ) *
          ((max (m : ℝ) (n : ℝ) *
            (frobNormSqRect A / (s : ℝ) ^ 2)) *
            finiteVecNorm2Sq x) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
    _ = (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ))) *
          finiteVecNorm2Sq x := by
            field_simp [ne_of_gt hs]

/-- Summed Loewner-form variance proxy over the `s` independent one-step
    self-adjoint dilation residual increments.  This is the variance matrix
    shape expected by a future matrix Bernstein theorem. -/
theorem sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ)))) *
          finiteIdMatrix a b) := by
  classical
  intro x
  have hrewrite :
      finiteQuadraticForm
        (fun a b =>
          ∑ _t : Fin s,
            ∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample)) a b) x =
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [finiteQuadraticForm_fintype_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [finiteQuadraticForm_fintype_sum_smul]
  rw [hrewrite, finiteQuadraticForm_smul_finiteIdMatrix]
  exact sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    A hden hs x

/-- Source-aligned rectangular summed Loewner variance proxy over the `s`
    independent one-step self-adjoint dilation residual increments. -/
theorem sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b)
      (fun a b =>
        (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ))) *
          finiteIdMatrix a b) := by
  classical
  intro x
  have hrewrite :
      finiteQuadraticForm
        (fun a b =>
          ∑ _t : Fin s,
            ∑ sample : ElementwiseSample m n,
              sqMagProb A sample.1 sample.2 *
                finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample)) a b) x =
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [finiteQuadraticForm_fintype_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [finiteQuadraticForm_fintype_sum_smul]
  rw [hrewrite, finiteQuadraticForm_smul_finiteIdMatrix]
  exact
    sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      A hden hs x

/-- The summed self-adjoint dilation variance matrix is positive
    semidefinite. -/
theorem sqMagProb_sum_steps_rectSelfAdjointDilation_square_psd
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    finitePSD
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
  classical
  apply finitePSD_fintype_sum_of_finitePSD
  intro _t
  exact sqMagProb_sum_rectSelfAdjointDilation_square_psd s A hden

/-- Product-law expectation form of the one-step self-adjoint dilation square
    variance proxy at a fixed trace coordinate.

This is the bridge from the one-step `sqMagProb` variance calculation to the
canonical independent trace probability space. -/
theorem sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (t : Fin s) (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hstep]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le
      s A hden hs x

/-- Product-law expectation form of the source-aligned rectangular one-step
    self-adjoint dilation square variance proxy. -/
theorem sqMagTraceProbability_expectationReal_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (t : Fin s) (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) *
        finiteVecNorm2Sq x := by
  classical
  have hstep :=
    sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hstep]
  exact
    sqMagProb_sum_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      s A hden hs x

/-- Product-law expectation form of the summed self-adjoint dilation variance
    proxy.  The left side is the trace-law expectation of the sum of the
    quadratic forms of the squared one-step dilation increments. -/
theorem sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        ∑ t : Fin s,
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ)))) *
        finiteVecNorm2Sq x := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hrewrite :
      P.expectationReal
        (fun samples : ElementwiseTrace m n s =>
          ∑ t : Fin s,
            finiteQuadraticForm
              (finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))) x) =
        ∑ t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [FiniteProbability.expectationReal_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hrewrite]
  exact sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le
    A hden hs x

/-- Product-law expectation form of the source-aligned rectangular summed
    self-adjoint dilation variance proxy. -/
theorem sqMagTraceProbability_expectationReal_sum_finiteQuadraticForm_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin m ⊕ Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        ∑ t : Fin s,
          finiteQuadraticForm
            (finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)))) x) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ))) *
        finiteVecNorm2Sq x := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hrewrite :
      P.expectationReal
        (fun samples : ElementwiseTrace m n s =>
          ∑ t : Fin s,
            finiteQuadraticForm
              (finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))) x) =
        ∑ t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteQuadraticForm
                (finiteMatMul
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample))) x := by
    rw [FiniteProbability.expectationReal_sum]
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteQuadraticForm
          (finiteMatMul
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample))) x)
  rw [hrewrite]
  exact
    sqMagProb_sum_steps_finiteQuadraticForm_rectSelfAdjointDilation_square_le_sharp_rect
      A hden hs x

/-- Loewner-form trace-law expectation of the summed squared dilation
    increments.  This packages the product-law expectation adapter in the
    exact matrix order shape needed by a future Bernstein theorem. -/
theorem sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b))
      (fun a b =>
        (2 * ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ)))) *
          finiteIdMatrix a b) := by
  classical
  have hmatrix :
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) =
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
    ext a b
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) a b)
  rw [hmatrix]
  exact
    sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id
      A hden hs

/-- Source-aligned rectangular Loewner-form trace-law expectation of the summed
    squared dilation increments. -/
theorem sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteLoewnerLe
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b))
      (fun a b =>
        (max (m : ℝ) (n : ℝ) *
          (frobNormSqRect A / (s : ℝ))) *
          finiteIdMatrix a b) := by
  classical
  have hmatrix :
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) =
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
    ext a b
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) a b)
  rw [hmatrix]
  exact
    sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
      A hden hs

/-- The trace-law expectation of the summed squared dilation increments is
    positive semidefinite. -/
theorem sqMagTraceProbability_sum_expectationReal_rectSelfAdjointDilation_square_psd
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    finitePSD
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) := by
  classical
  have hmatrix :
      (fun a b =>
        ∑ t : Fin s,
          (sqMagTraceProbability (steps := s) A hden).expectationReal
            (fun samples =>
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t))) a b)) =
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) := by
    ext a b
    apply Finset.sum_congr rfl
    intro t _
    exact sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        finiteMatMul
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) a b)
  rw [hmatrix]
  exact sqMagProb_sum_steps_rectSelfAdjointDilation_square_psd A hden

/-- Trace form of the one-step self-adjoint dilation variance proxy.  This is
    obtained from the Loewner proxy by trace monotonicity, and is one of the
    scalar quantities used by trace-moment and matrix-Bernstein routes. -/
theorem sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteTrace
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id
        s A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Trace form of the source-aligned rectangular one-step self-adjoint dilation
    variance proxy. -/
theorem sqMagProb_sum_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    finiteTrace
      (fun a b =>
        ∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            finiteMatMul
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample))
              (rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
        s A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Trace form of the summed self-adjoint dilation variance proxy.  After `s`
    independent samples the scalar variance trace is order
    `||A||_F^2 / s`, with the explicit dilation dimension `m + n`. -/
theorem sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteTrace
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ)))) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id
        A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Trace form of the source-aligned rectangular summed self-adjoint dilation
    variance proxy. -/
theorem sqMagProb_sum_steps_finiteTrace_rectSelfAdjointDilation_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    finiteTrace
      (fun a b =>
        ∑ _t : Fin s,
          ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              finiteMatMul
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample))
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) a b) ≤
      (max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ))) *
        ((m : ℝ) + (n : ℝ)) := by
  classical
  have hmono :=
    finiteTrace_mono_of_finiteLoewnerLe
      (sqMagProb_sum_steps_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
        A hden hs)
  rw [finiteTrace_smul_finiteIdMatrix] at hmono
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hmono

/-- Applying a one-step residual increment to a fixed vector has squared
    second moment controlled by the Frobenius variance proxy. -/
theorem sqMagProb_sum_vecNorm2Sq_rectMatMulVec_elementwiseSampleResidualIncrement_le
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x)) ≤
      ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) *
        vecNorm2Sq x := by
  classical
  have hFrob :=
    sqMagProb_sum_elementwiseSampleResidualIncrement_frob_sq_le
      s A hden hs
  have hx_nonneg : 0 ≤ vecNorm2Sq x := vecNorm2Sq_nonneg x
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        vecNorm2Sq
          (rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x))
        ≤ ∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              (frobNormSqRect (elementwiseSampleResidualIncrement s A sample) *
                vecNorm2Sq x) := by
            apply Finset.sum_le_sum
            intro sample _
            exact mul_le_mul_of_nonneg_left
              (vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul
                (elementwiseSampleResidualIncrement s A sample) x)
              (sqMagProb_nonneg A hden sample.1 sample.2)
    _ = (∑ sample : ElementwiseSample m n,
          sqMagProb A sample.1 sample.2 *
            frobNormSqRect (elementwiseSampleResidualIncrement s A sample)) *
          vecNorm2Sq x := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ ≤ ((m : ℝ) * (n : ℝ) *
          (frobNormSqRect A / (s : ℝ) ^ 2)) *
          vecNorm2Sq x :=
            mul_le_mul_of_nonneg_right hFrob hx_nonneg

/-- The exact Algorithm 1 residual is entrywise mean-zero under the canonical
    independent squared-magnitude trace law. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples => elementwiseTraceResidual s A samples i j) = 0 := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hsketch :
      P.expectationReal
        (fun samples : ElementwiseTrace m n s =>
          elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
        A i j :=
    sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
      (steps := s) s A hden i j rfl hs
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        elementwiseTraceResidual s A samples i j)
        = P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              A i j -
                elementwiseTraceSketch s A (fun _ _ => 0) samples i j) := by
            rfl
    _ = P.expectationReal (fun _samples : ElementwiseTrace m n s => A i j) -
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceSketch s A (fun _ _ => 0) samples i j) := by
            rw [FiniteProbability.expectationReal_sub]
    _ = A i j - A i j := by
            rw [FiniteProbability.expectationReal_const, hsketch]
    _ = 0 := by ring

/-- Applying the exact residual to a fixed vector preserves the sum of
    one-sample residual increments. -/
theorem rectMatMulVec_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) (i : Fin m) :
    rectMatMulVec (elementwiseTraceResidual s A samples) x i =
      ∑ t : Fin s,
        rectMatMulVec (elementwiseSampleResidualIncrement s A (samples t)) x i := by
  classical
  have hentry :
      elementwiseTraceResidual s A samples =
        fun i j =>
          ∑ t : Fin s,
            elementwiseSampleResidualIncrement s A (samples t) i j := by
    ext i j
    exact elementwiseTraceResidual_eq_sum_sampleResidualIncrement
      A samples hs i j
  rw [hentry]
  unfold rectMatMulVec
  calc
    (∑ j : Fin n,
      (∑ t : Fin s,
        elementwiseSampleResidualIncrement s A (samples t) i j) * x j)
        = ∑ j : Fin n, ∑ t : Fin s,
            elementwiseSampleResidualIncrement s A (samples t) i j * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ t : Fin s, ∑ j : Fin n,
            elementwiseSampleResidualIncrement s A (samples t) i j * x j := by
            rw [Finset.sum_comm]

/-- The self-adjoint dilation of the exact residual is the sum of the
    self-adjoint dilations of the one-sample residual increments.  This is the
    square-matrix random object needed by a future Bernstein/Khintchine proof. -/
theorem rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b =
      ∑ t : Fin s,
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A (samples t)) a b := by
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          simp [rectSelfAdjointDilation]
      | inr j =>
          simpa [rectSelfAdjointDilation] using
            elementwiseTraceResidual_eq_sum_sampleResidualIncrement
              A samples hs i j
  | inr j =>
      cases b with
      | inl i =>
          simpa [rectSelfAdjointDilation] using
            elementwiseTraceResidual_eq_sum_sampleResidualIncrement
              A samples hs i j
      | inr k =>
          simp [rectSelfAdjointDilation]

/-- Quadratic forms of the residual dilation decompose as sums of the
    corresponding one-step quadratic forms.

This is the scalar-projection bridge between the exact residual decomposition
and finite-family MGF or finite-cover concentration arguments. -/
theorem finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n s) (hs : (s : ℝ) ≠ 0)
    (x : Fin m ⊕ Fin n → ℝ) :
    finiteQuadraticForm
        (rectSelfAdjointDilation (elementwiseTraceResidual s A samples)) x =
      ∑ t : Fin s,
        finiteQuadraticForm
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A (samples t))) x := by
  classical
  have hmat :
      rectSelfAdjointDilation (elementwiseTraceResidual s A samples) =
        fun a b =>
          ∑ t : Fin s,
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t)) a b := by
    ext a b
    exact rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
      A samples hs a b
  calc
    finiteQuadraticForm
        (rectSelfAdjointDilation (elementwiseTraceResidual s A samples)) x
        = finiteQuadraticForm
            (fun a b =>
              ∑ t : Fin s,
                rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)) a b) x := by
            rw [hmat]
    _ = ∑ t : Fin s,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t))) x := by
            rw [finiteQuadraticForm_fintype_sum]

/-- The one-step self-adjoint dilation residual increment, scaled by a scalar
    parameter, is symmetric.  This is the domain side condition for feeding the
    Algorithm 1 dilation increments into the finite-real trace-MGF theorem. -/
theorem rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (sample : ElementwiseSample m n) (theta : ℝ) :
    IsSymmetricFiniteMatrix
      (fun a b : Fin m ⊕ Fin n =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
  intro a b
  exact congrArg (fun x => theta * x)
    (rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s A sample) a b)

/-- Algorithm 1 trace-MGF domination instantiated with the self-adjoint
    dilation residual increments.

This is the source-aligned trace-MGF target that the scalar
matrix-CGF/log-MGF Bernstein step must bound next.  It does not assume a CGF
bound; it is the no-hidden-Lieb iid trace-MGF theorem specialized to
\(\theta D(Z_t)\), where \(D(\cdot)\) is the self-adjoint dilation. -/
theorem sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (theta : ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun a b : Fin m ⊕ Fin n =>
              ∑ t : Fin s,
                theta *
                  rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A (samples t)) a b))) ≤
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
  classical
  let zeroMat : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun _ _ => 0
  let X : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample a b =>
      theta *
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b
  have hzero : IsSymmetricFiniteMatrix zeroMat := by
    intro a b
    rfl
  have hX : ∀ sample, IsSymmetricFiniteMatrix (X sample) := by
    intro sample
    exact
      rectSelfAdjointDilation_elementwiseSampleResidualIncrement_smul_symmetric
        A sample theta
  have h :=
    sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
      (steps := s) A hden (H := zeroMat) hzero (X := X) hX
  simpa [zeroMat, X, sqMagTraceProbabilityFiniteRealTraceMGFLogBound] using h

/-- Algorithm 1 trace-MGF domination for the actual self-adjoint dilation of
    the full exact residual.

The left side is now the finite-real trace exponential of
\(\theta D(A-\widetilde A)\).  The right side is the same logarithmic
one-sample mean increment produced by the no-hidden-Lieb trace-MGF iteration.
The remaining red-bottleneck theorem is to bound this logarithmic increment by
a scalar/variance proxy and then apply the eigenvalue Markov interface. -/
theorem sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) (theta : ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun a b : Fin m ⊕ Fin n =>
              theta *
                rectSelfAdjointDilation
                  (elementwiseTraceResidual s A samples) a b))) ≤
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hleft :
      P.expectationReal
        (fun samples =>
          finiteTrace
            (finiteMatrixExp
              (fun a b : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) a b))) =
      P.expectationReal
        (fun samples =>
          finiteTrace
            (finiteMatrixExp
              (fun a b : Fin m ⊕ Fin n =>
                ∑ t : Fin s,
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseSampleResidualIncrement s A (samples t)) a b))) := by
    unfold P FiniteProbability.expectationReal
    apply Finset.sum_congr rfl
    intro samples _
    apply congrArg (fun z : ℝ => (sqMagTraceProbability A hden).prob samples * z)
    apply congrArg
      (fun M : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ =>
        finiteTrace (finiteMatrixExp M))
    funext a b
    rw [rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
      A samples hs a b]
    rw [Finset.mul_sum]
  rw [hleft]
  exact
    sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_sum_rectSelfAdjointDilation_sampleResidualIncrement_le
      A hden theta

/-- Algorithm 1 upper-tail eigenvalue Markov step after the no-hidden-Lieb
    trace-MGF iteration has been specialized to the actual self-adjoint
    dilation residual.

This is the final trace-exponential-to-largest-eigenvalue interface for the
scaled residual `theta * D(A - Atilde)`.  It does not prove the scalar
matrix-CGF/Bernstein estimate for the logarithmic one-step mean increment; that
quantity remains exposed on the right-hand side. -/
theorem sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (theta T : ℝ) :
    (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∃ a : Fin m ⊕ Fin n,
            T ≤ finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a} ≤
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let M : ElementwiseTrace m n s → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun samples b c =>
      theta *
        rectSelfAdjointDilation
          (elementwiseTraceResidual s A samples) b c
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples b c
    exact congrArg (fun x => theta * x)
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A samples) b c)
  have hTrace :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
    simpa [P, M] using
      sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
        A hden hs theta
  simpa [P, M] using
    FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound
      (P := P) (M := M) hM T
      (sqMagTraceProbabilityFiniteRealTraceMGFLogBound
        (steps := s) A hden
        (fun _a _b : Fin m ⊕ Fin n => 0)
        (fun sample a b =>
          theta *
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b))
      hTrace

/-- Two-sided eigenvalue Markov step for the scaled Algorithm 1 dilation
    residual.

The positive trace-MGF bound is supplied by the trace-MGF instantiation with
`theta`; the negative trace-MGF bound is the same theorem with `-theta`.
The remaining open source obligation is still the scalar
matrix-CGF/Bernstein--Khintchine bound that turns the two logarithmic
trace-MGF quantities into explicit CACM equation (2) constants. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
    {m n s : ℕ} [Fintype (Fin m ⊕ Fin n)] [DecidableEq (Fin m ⊕ Fin n)]
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (theta T : ℝ) :
    1 -
        (Real.exp (-T) *
            sqMagTraceProbabilityFiniteRealTraceMGFLogBound
              (steps := s) A hden
              (fun _a _b : Fin m ⊕ Fin n => 0)
              (fun sample a b =>
                (-theta) *
                  rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b) +
          Real.exp (-T) *
            sqMagTraceProbabilityFiniteRealTraceMGFLogBound
              (steps := s) A hden
              (fun _a _b : Fin m ⊕ Fin n => 0)
              (fun sample a b =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a| < T} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let M : ElementwiseTrace m n s → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun samples b c =>
      theta *
        rectSelfAdjointDilation
          (elementwiseTraceResidual s A samples) b c
  have hM : ∀ samples, IsSymmetricFiniteMatrix (M samples) := by
    intro samples b c
    exact congrArg (fun x => theta * x)
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A samples) b c)
  have hTracePos :
      P.expectationReal
          (fun samples => finiteTrace (finiteMatrixExp (M samples))) ≤
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
    simpa [P, M] using
      sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
        A hden hs theta
  have hTraceNeg :
      P.expectationReal
          (fun samples => finiteTrace
            (finiteMatrixExp (fun b c : Fin m ⊕ Fin n => -M samples b c))) ≤
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) *
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) := by
    simpa [P, M, neg_mul] using
      sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_rectSelfAdjointDilation_elementwiseTraceResidual_le
        A hden hs (-theta)
  simpa [P, M] using
    FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add
      (P := P) (M := M) hM T
      (sqMagTraceProbabilityFiniteRealTraceMGFLogBound
        (steps := s) A hden
        (fun _a _b : Fin m ⊕ Fin n => 0)
        (fun sample a b =>
          (-theta) *
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b))
      (sqMagTraceProbabilityFiniteRealTraceMGFLogBound
        (steps := s) A hden
        (fun _a _b : Fin m ⊕ Fin n => 0)
        (fun sample a b =>
          theta *
            rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b))
      hTraceNeg hTracePos

/-- Finite-family scalar MGF tail for quadratic forms of the Algorithm 1
    self-adjoint dilation residual.

The theorem consumes one-step scalar MGF bounds for a supplied finite family of
test vectors and proves simultaneous control of the corresponding residual
quadratic forms under the canonical product trace law.  It is a concentration
foundation for cover or trace-exponential routes; it is not yet the CACM
equation (2) matrix Bernstein/Khintchine theorem. -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hs : (s : ℝ) ≠ 0)
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T psi lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hmgf : ∀ a,
      (∑ sample : ElementwiseSample m n,
        sqMagProb A sample.1 sample.2 *
          Real.exp
            (lam a *
              finiteQuadraticForm
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) (z a))) ≤
        Real.exp (psi a)) :
    1 - ∑ a : ι, Real.exp ((s : ℝ) * psi a - lam a * T a) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
  classical
  let f : ι → ElementwiseSample m n → ℝ := fun a sample =>
    finiteQuadraticForm
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)) (z a)
  have htail :=
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      (steps := s) A hden f T psi lam hlam
      (by
        intro a
        simpa [f] using hmgf a)
  have hset :
      {samples : ElementwiseTrace m n s |
        ∀ a : ι, ∑ t : Fin s, f a (samples t) ≤ T a} =
      {samples : ElementwiseTrace m n s |
        ∀ a : ι,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
    ext samples
    constructor
    · intro h a
      rw [
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      simpa [f] using h a
    · intro h a
      change
        (∑ t : Fin s,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t))) (z a)) ≤
          T a
      rw [←
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      exact h a
  simpa [hset] using htail

/-- Finite-family quadratic-form tail from pointwise one-step bounds.

This removes the explicit one-step MGF hypothesis from the previous theorem
when each supplied test-vector quadratic form has a proved pointwise upper
bound.  The resulting estimate is generally too weak to be the CACM equation
(2) matrix Bernstein theorem, but it is a fully proved finite-test support
layer. -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_pointwise_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hs : (s : ℝ) ≠ 0)
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a sample,
      finiteQuadraticForm
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample)) (z a) ≤ B a) :
    1 - ∑ a : ι, Real.exp ((s : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
  classical
  exact
    sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      A hden hs z T (fun a => lam a * B a) lam hlam
      (by
        intro a
        simpa using
          sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
            A hden
            (fun sample : ElementwiseSample m n =>
              finiteQuadraticForm
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) (z a))
            (le_of_lt (hlam a)) (hbound a))

/-- Finite-family quadratic-form tail from support-aware pointwise one-step
    bounds.

This is the same finite-test theorem as
`..._of_pointwise_bound`, but the one-step bound is only required on samples
with positive squared-magnitude probability.  It is designed for truncated
sampling laws where zero-mass samples need not satisfy retained-entry side
conditions. -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hs : (s : ℝ) ≠ 0)
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a sample,
      0 < sqMagProb A sample.1 sample.2 →
        finiteQuadraticForm
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample)) (z a) ≤ B a) :
    1 - ∑ a : ι, Real.exp ((s : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
  classical
  let f : ι → ElementwiseSample m n → ℝ := fun a sample =>
    finiteQuadraticForm
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)) (z a)
  have htail :=
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound
      (steps := s) A hden f T B lam hlam
      (by
        intro a sample hsample
        simpa [f] using hbound a sample hsample)
  have hset :
      {samples : ElementwiseTrace m n s |
        ∀ a : ι, ∑ t : Fin s, f a (samples t) ≤ T a} =
      {samples : ElementwiseTrace m n s |
        ∀ a : ι,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseTraceResidual s A samples)) (z a) ≤ T a} := by
    ext samples
    constructor
    · intro h a
      rw [
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      simpa [f] using h a
    · intro h a
      change
        (∑ t : Fin s,
          finiteQuadraticForm
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A (samples t))) (z a)) ≤
          T a
      rw [←
        finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
          A samples hs (z a)]
      exact h a
  simpa [hset] using htail

/-- Truncated Algorithm 1 finite-family quadratic-form tail from the retained
    one-step dilation bound.

Positive probability under the truncated squared-magnitude law implies the
sampled entry is retained, so the one-step operator bound applies without any
extra support hypothesis.  This is still a finite-test scalar support theorem,
not the trace-exponential or matrix Bernstein proof of CACM equation (2). -/
theorem sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_truncatedTraceResidual_le_ge_one_sub_sum_exp_of_support_bound
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (z : ι → Fin m ⊕ Fin n → ℝ)
    (T lam : ι → ℝ) (hlam : ∀ a, 0 < lam a) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
    1 -
        ∑ a : ι,
          Real.exp ((s : ℝ) * (lam a * (L * finiteVecNorm2Sq (z a))) -
            lam a * T a) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : ι,
            finiteQuadraticForm
              (rectSelfAdjointDilation
                (elementwiseTraceResidual s Ahat samples)) (z a) ≤ T a} := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hsne : (s : ℝ) ≠ 0 := ne_of_gt hs
  have htail :=
    sqMagTraceProbability_eventProb_forall_finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_le_ge_one_sub_sum_exp_of_support_pointwise_bound
      (A := Ahat) hden hsne z T (fun a => L * finiteVecNorm2Sq (z a))
      lam hlam
      (by
        intro a sample hprob
        have hsample_ne :
            elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
          simpa [Ahat] using
            entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hprob
        simpa [Ahat, L] using
          finiteQuadraticForm_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_le
            htau hs A sample hsample_ne (z a))
  simpa [Ahat, L] using htail

/-- The one-sample residual increment has zero mean after applying it to a
    fixed vector. -/
theorem sqMagProb_sum_rectMatMulVec_elementwiseSampleResidualIncrement_eq_zero
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) (i : Fin m) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x i) = 0 := by
  classical
  calc
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectMatMulVec (elementwiseSampleResidualIncrement s A sample) x i)
        = ∑ sample : ElementwiseSample m n, ∑ j : Fin n,
            sqMagProb A sample.1 sample.2 *
              (elementwiseSampleResidualIncrement s A sample i j * x j) := by
            apply Finset.sum_congr rfl
            intro sample _
            rw [rectMatMulVec, Finset.mul_sum]
    _ = ∑ j : Fin n, ∑ sample : ElementwiseSample m n,
            (sqMagProb A sample.1 sample.2 *
              elementwiseSampleResidualIncrement s A sample i j) * x j := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro sample _
            ring
    _ = ∑ j : Fin n,
          (∑ sample : ElementwiseSample m n,
            sqMagProb A sample.1 sample.2 *
              elementwiseSampleResidualIncrement s A sample i j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = 0 := by
            simp [sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
              s A hden hs]

/-- The one-step self-adjoint dilation residual increment has zero mean in
    every square-matrix entry. -/
theorem sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero
    {m n : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    (∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 *
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b) = 0 := by
  cases a with
  | inl i =>
      cases b with
      | inl k =>
          simp [rectSelfAdjointDilation]
      | inr j =>
          simpa [rectSelfAdjointDilation] using
            sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
              s A hden hs i j
  | inr j =>
      cases b with
      | inl i =>
          simpa [rectSelfAdjointDilation] using
            sqMagProb_sum_elementwiseSampleResidualIncrement_entry_eq_zero
              s A hden hs i j
      | inr k =>
          simp [rectSelfAdjointDilation]

/-- One-sample C⋆-matrix zero mean for the self-adjoint dilation residual
increment under the squared-magnitude sampling law. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample m n =>
        finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample))) = 0 := by
  classical
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  ext a b
  change
    ((sqMagSampleProbability A hden).expectationReal
      (fun sample : ElementwiseSample m n =>
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b) : ℂ) = 0
  have hsum :=
    sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero
      s A hden hs a b
  simpa [FiniteProbability.expectationReal, sqMagSampleProbability] using
    congrArg (fun x : ℝ => (x : ℂ)) hsum

/-- C⋆-matrix Loewner variance proxy for the one-sample self-adjoint dilation
residual increment under the squared-magnitude sampling law.

This is the complex C⋆ form consumed by the one-sample log-CGF theorem.  It is
obtained from the repository's finite-real Loewner variance proxy and the
finite-real-to-C⋆ embedding. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) *
          finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) :
        CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
      ((2 * ((m : ℝ) * (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2))) : ℂ) •
        (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
  classical
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let V : ℝ := 2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2))
  have hprod :
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
      (fun sample : ElementwiseSample m n =>
        finiteComplexCStarMatrix (finiteMatMul (D sample) (D sample))) := by
    funext sample
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  let M : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun a b =>
    ∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 * finiteMatMul (D sample) (D sample) a b
  have hM_eq :
      (fun a b : Fin m ⊕ Fin n =>
          (sqMagSampleProbability A hden).expectationReal
            (fun sample : ElementwiseSample m n =>
              finiteMatMul (D sample) (D sample) a b)) = M := by
    ext a b
    simp [M, FiniteProbability.expectationReal, sqMagSampleProbability]
  rw [hM_eq]
  have hMsym : IsSymmetricFiniteMatrix M := by
    dsimp [M]
    exact IsSymmetricFiniteMatrix.sum_smul
      (fun sample : ElementwiseSample m n => sqMagProb A sample.1 sample.2)
      (fun sample : ElementwiseSample m n => finiteMatMul (D sample) (D sample))
      (fun sample =>
        finiteMatMul_self_symmetric_of_symmetric (D sample)
          (rectSelfAdjointDilation_symmetric
            (elementwiseSampleResidualIncrement s A sample)))
  have hNsym :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric V
  have hLe :
      finiteLoewnerLe M
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) := by
    dsimp [M, V, D]
    exact sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id
      s A hden hs
  have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M
    (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) hMsym hNsym hLe
  simpa [V, D, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC

/-- Source-sharp square-matrix C⋆ variance proxy for the one-sample
    self-adjoint dilation residual increment. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
    {n s : ℕ} (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample n n =>
        (finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) *
          finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) :
        CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) ≤
      (((n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)) : ℂ) •
        (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
  classical
  let D : ElementwiseSample n n → Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let V : ℝ := (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)
  have hprod :
      (fun sample : ElementwiseSample n n =>
        (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) =
      (fun sample : ElementwiseSample n n =>
        finiteComplexCStarMatrix (finiteMatMul (D sample) (D sample))) := by
    funext sample
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  let M : Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ := fun a b =>
    ∑ sample : ElementwiseSample n n,
      sqMagProb A sample.1 sample.2 * finiteMatMul (D sample) (D sample) a b
  have hM_eq :
      (fun a b : Fin n ⊕ Fin n =>
          (sqMagSampleProbability A hden).expectationReal
            (fun sample : ElementwiseSample n n =>
              finiteMatMul (D sample) (D sample) a b)) = M := by
    ext a b
    simp [M, FiniteProbability.expectationReal, sqMagSampleProbability]
  rw [hM_eq]
  have hMsym : IsSymmetricFiniteMatrix M := by
    dsimp [M]
    exact IsSymmetricFiniteMatrix.sum_smul
      (fun sample : ElementwiseSample n n => sqMagProb A sample.1 sample.2)
      (fun sample : ElementwiseSample n n => finiteMatMul (D sample) (D sample))
      (fun sample =>
        finiteMatMul_self_symmetric_of_symmetric (D sample)
          (rectSelfAdjointDilation_symmetric
            (elementwiseSampleResidualIncrement s A sample)))
  have hNsym :
      IsSymmetricFiniteMatrix
        (fun a b : Fin n ⊕ Fin n => V * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric V
  have hLe :
      finiteLoewnerLe M
        (fun a b : Fin n ⊕ Fin n => V * finiteIdMatrix a b) := by
    dsimp [M, V, D]
    exact
      sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_square
        s A hden hs
  have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M
    (fun a b : Fin n ⊕ Fin n => V * finiteIdMatrix a b) hMsym hNsym hLe
  simpa [V, D, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC

/-- Source-aligned rectangular C⋆ variance proxy for the one-sample
    self-adjoint dilation residual increment. -/
theorem sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) :
    (sqMagSampleProbability A hden).expectationCStarMatrix
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) *
          finiteComplexCStarMatrix
            (rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample)) :
        CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
      ((max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)) : ℂ) •
        (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
  classical
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let V : ℝ := max (m : ℝ) (n : ℝ) * (frobNormSqRect A / (s : ℝ) ^ 2)
  have hprod :
      (fun sample : ElementwiseSample m n =>
        (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
      (fun sample : ElementwiseSample m n =>
        finiteComplexCStarMatrix (finiteMatMul (D sample) (D sample))) := by
    funext sample
    rw [finiteComplexCStarMatrix_mul]
  rw [hprod]
  rw [FiniteProbability.expectationCStarMatrix_finiteComplexCStarMatrix]
  let M : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ := fun a b =>
    ∑ sample : ElementwiseSample m n,
      sqMagProb A sample.1 sample.2 * finiteMatMul (D sample) (D sample) a b
  have hM_eq :
      (fun a b : Fin m ⊕ Fin n =>
          (sqMagSampleProbability A hden).expectationReal
            (fun sample : ElementwiseSample m n =>
              finiteMatMul (D sample) (D sample) a b)) = M := by
    ext a b
    simp [M, FiniteProbability.expectationReal, sqMagSampleProbability]
  rw [hM_eq]
  have hMsym : IsSymmetricFiniteMatrix M := by
    dsimp [M]
    exact IsSymmetricFiniteMatrix.sum_smul
      (fun sample : ElementwiseSample m n => sqMagProb A sample.1 sample.2)
      (fun sample : ElementwiseSample m n => finiteMatMul (D sample) (D sample))
      (fun sample =>
        finiteMatMul_self_symmetric_of_symmetric (D sample)
          (rectSelfAdjointDilation_symmetric
            (elementwiseSampleResidualIncrement s A sample)))
  have hNsym :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric V
  have hLe :
      finiteLoewnerLe M
        (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) := by
    dsimp [M, V, D]
    exact
      sqMagProb_sum_rectSelfAdjointDilation_square_loewnerLe_scalar_id_sharp_rect
        s A hden hs
  have hC := finiteComplexCStarMatrix_le_of_finiteLoewnerLe M
    (fun a b : Fin m ⊕ Fin n => V * finiteIdMatrix a b) hMsym hNsym hLe
  simpa [V, D, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC

/-- Positive support for the truncated squared-magnitude law gives the spectral
upper-bound hypothesis needed by the support-aware C⋆ Bernstein log-CGF
theorem. -/
theorem sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)))) :
    x ≤
      Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n =>
          L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample)) :=
    rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s Ahat sample)
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample))) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Negative-increment companion of
`sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le`.

Positive support under the truncated law also gives the upper spectral bound
for `-D(Z_t)`, needed for the lower-tail Bernstein route. -/
theorem sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) :
    x ≤
      Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) := by
    intro a b
    change
      -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) a b =
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) b a
    rw [rectSelfAdjointDilation_symmetric]
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      -finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_neg, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Sharper positive-support spectral upper bound for the truncated
squared-magnitude law.

This version uses the direct rectangular-operator-to-dilation Loewner adapter,
so the radius is
`(1/s) * ||Ahat||_F + ||Ahat||_F^2/(s*tau)` without the auxiliary `sqrt 2`
factor. -/
theorem sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)))) :
    x ≤
      (1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample)) :=
    rectSelfAdjointDilation_symmetric
      (elementwiseSampleResidualIncrement s Ahat sample)
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample))) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Sharper negative-increment spectral upper bound for the truncated
squared-magnitude law, again without the auxiliary `sqrt 2` factor. -/
theorem sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (sample : ElementwiseSample m n)
    (hsampleProb :
      0 < (sqMagSampleProbability (elementwiseTruncate tau A) hden).prob sample)
    {x : ℝ}
    (hx :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) :
    x ≤
      (1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
        frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hsampleSq : 0 < sqMagProb Ahat sample.1 sample.2 := by
    simpa [Ahat, sqMagSampleProbability] using hsampleProb
  have hsample_ne :
      elementwiseTruncate tau A sample.1 sample.2 ≠ 0 := by
    simpa [Ahat] using
      entry_ne_zero_of_sqMagProb_pos Ahat sample.1 sample.2 hsampleSq
  have hLeFinite :
      finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) := by
    simpa [Ahat, L] using
      finiteLoewnerLe_neg_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_truncated_sharp
        htau hs A sample hsample_ne
  have hM :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) := by
    intro a b
    change
      -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) a b =
        -rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample) b a
    rw [rectSelfAdjointDilation_symmetric]
  have hN :
      IsSymmetricFiniteMatrix
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) :=
    smulFiniteIdMatrix_symmetric L
  have hCLe :
      -finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) ≤
        (L : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hC :=
      finiteComplexCStarMatrix_le_of_finiteLoewnerLe
        (fun a b : Fin m ⊕ Fin n =>
          -rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b)
        (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b)
        hM hN hLeFinite
    simpa [finiteComplexCStarMatrix_neg, finiteComplexCStarMatrix_smul_finiteIdMatrix] using hC
  have hxAhat :
      x ∈ spectrum ℝ
        (-finiteComplexCStarMatrix
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample)) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat] using hx
  have hxle : x ≤ L :=
    cstarMatrix_spectrum_le_of_le_real_smul_one hCLe hxAhat
  simpa [Ahat, L] using hxle

/-- Algorithm 1 literal one-sample Bernstein log-CGF for the self-adjoint
dilation residual increment with the exact input-dependent support radius.

Unlike the source-aligned truncated theorem, this statement keeps the literal
law `p_ij = A_ij^2 / ||A||_F^2` and uses the finite reciprocal-entry radius
`elementwiseLiteralResidualSupportRadius s A`.  The result is therefore
nonconditional for the literal sampler, but the displayed radius necessarily
depends on the small nonzero entries of `A`. -/
theorem sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
    {m n s : ℕ} {theta : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    CFC.log
        ((sqMagSampleProbability A hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample)) :
                CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
      ((Real.exp (theta * L) - theta * L - 1) / L ^ 2) •
        (sqMagSampleProbability A hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            (finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) *
              finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A sample)) :
            CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
  classical
  intro L
  let P := sqMagSampleProbability A hden
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample =>
      finiteComplexCStarMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample))
  have hL_pos : 0 < L := by
    simpa [L] using
      elementwiseLiteralResidualSupportRadius_pos hs A hden
  have hX : ∀ sample, IsSelfAdjoint (X sample) := by
    intro sample
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample))
      (rectSelfAdjointDilation_symmetric
        (elementwiseSampleResidualIncrement s A sample))
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        A hden (ne_of_gt hs)
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (X sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, L] using
      sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
        hs A hden sample (by simpa [P] using hsample) hx
  simpa [P, X, L] using
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hL_pos hspec

/-- Algorithm 1 truncated one-sample Bernstein log-CGF for the self-adjoint
dilation residual increment.

This instantiates the generic support-aware one-sample C⋆ Bernstein theorem
with the squared-magnitude row-entry law, the zero-mean dilation residual
increment, and the retained-entry truncated spectral bound.  It is still a
one-sample log-CGF theorem; the iid trace-MGF iteration and final optimized
matrix-Bernstein tail remain separate ledger items. -/
theorem sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    CFC.log
        ((sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s
                      (elementwiseTruncate tau A) sample)) :
                CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
      ((Real.exp
          (theta *
            (Real.sqrt 2 *
              ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
                frobNormSqRect (elementwiseTruncate tau A) /
                  ((s : ℝ) * tau)))) -
          theta *
            (Real.sqrt 2 *
              ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
                frobNormSqRect (elementwiseTruncate tau A) /
                  ((s : ℝ) * tau))) - 1) /
        (Real.sqrt 2 *
          ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
            frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))) ^ 2) •
        (sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            (finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) *
              finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) :
            CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagSampleProbability Ahat hden
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample =>
      finiteComplexCStarMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hX : ∀ sample, IsSelfAdjoint (X sample) := by
    intro sample
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample))
      (rectSelfAdjointDilation_symmetric
        (elementwiseSampleResidualIncrement s Ahat sample))
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (X sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Ahat, L] using
      sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  simpa [P, X, Ahat, L] using
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hL_pos hspec

/-- Source-sharpened version of the Algorithm 1 truncated one-sample
Bernstein log-CGF bound.

The only change from
`sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`
is the spectral radius: this theorem uses the direct rectangular
operator-to-dilation bridge, so the bounded-increment parameter is
`(1/s)||Ahat||_F + ||Ahat||_F^2/(s*tau)` rather than that quantity multiplied
by `sqrt 2`. -/
theorem sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    CFC.log
        ((sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            NormedSpace.exp
              (theta •
                finiteComplexCStarMatrix
                  (rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s
                      (elementwiseTruncate tau A) sample)) :
                CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
      ((Real.exp
          (theta *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) /
                ((s : ℝ) * tau))) -
          theta *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) /
                ((s : ℝ) * tau)) - 1) /
        ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
          frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau)) ^ 2) •
        (sqMagSampleProbability (elementwiseTruncate tau A) hden).expectationCStarMatrix
          (fun sample : ElementwiseSample m n =>
            (finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) *
              finiteComplexCStarMatrix
                (rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s
                    (elementwiseTruncate tau A) sample)) :
            CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagSampleProbability Ahat hden
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample =>
      finiteComplexCStarMatrix
        (rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s Ahat sample))
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    exact add_pos_of_nonneg_of_pos hfirst hsecond
  have hX : ∀ sample, IsSelfAdjoint (X sample) := by
    intro sample
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
      (rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample))
      (rectSelfAdjointDilation_symmetric
        (elementwiseSampleResidualIncrement s Ahat sample))
  have hmean : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (X sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Ahat, L] using
      sqMagSampleProbability_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  simpa [P, X, Ahat, L] using
    P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
      hX hmean htheta hL_pos hspec

/-- Algorithm 1 literal scalar trace-MGF bound after combining the
input-dependent support-radius log-CGF theorem with the sharp rectangular
variance proxy.

This is a nonconditional trace-MGF bound for the literal squared-magnitude
sampler.  Its bounded-increment parameter is the exact finite quantity
`elementwiseLiteralResidualSupportRadius s A`, not a uniform source constant. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
    {m n s : ℕ} {theta : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro L beta V
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability A hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
    simpa [D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
        (m := m) (n := n) (s := s) (theta := theta)
        hs A hden htheta
  have hvar :
      (sqMagSampleProbability A hden).expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        A hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability A hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun x : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) A hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, D, L, beta, V]
    using hbound

/-- Negative-increment literal scalar trace-MGF bound with the same exact
input-dependent support radius. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
    {m n s : ℕ} {theta : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) A hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s A sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro L beta V
  let P := sqMagSampleProbability A hden
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s A sample)
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    simpa [L] using
      elementwiseLiteralResidualSupportRadius_pos hs A hden
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s A sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        A hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_literal_spectrum_le_supportRadius
        hs A hden sample (by simpa [P] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample m n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        A hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) A hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, D, L, beta, V]
    using hbound

/-- Algorithm 1 truncated scalar trace-MGF bound after combining the
support-aware one-sample log-CGF theorem with the proved C⋆ variance proxy.

This is the matrix-Bernstein trace-MGF scalarization layer for the
self-adjoint dilation increments.  It still leaves the final optimization of
`theta` and the conversion to the exact CACM equation (2) constants as the next
tail step. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
    simpa [Ahat, D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        htau hs A hden htheta
  have hvar :
      (sqMagSampleProbability Ahat hden).expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun x : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Rectangular source-sharp Algorithm 1 truncated scalar trace-MGF bound.

This is the rectangular companion to the square source-sharp theorem below,
but it keeps the generic truncated support radius with the `sqrt 2` factor.
The improvement is in the variance proxy:
`V = max(m,n) * ||Ahat||_F^2 / s^2`, using the already formalized
self-adjoint-dilation rectangular variance theorem. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
    simpa [Ahat, D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        htau hs A hden htheta
  have hvar :
      (sqMagSampleProbability Ahat hden).expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    simpa [Ahat, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun x : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Source-sharp square-matrix Algorithm 1 truncated scalar trace-MGF bound.

This combines the no-`sqrt 2` one-sample log-CGF support radius with the
Drineas--Zouzias square variance proxy
`V = n * ||Ahat||_F^2 / s^2`. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
    {n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin n ⊕ Fin n => 0)
      (fun sample a b =>
        theta *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let D : ElementwiseSample n n → Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  have hlog :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              NormedSpace.exp
                (theta • finiteComplexCStarMatrix (D sample) :
                  CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))) ≤
        beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
    simpa [Ahat, D, L, beta] using
      sqMagSampleProbability_cstarMatrix_log_expectationCStarMatrix_normed_exp_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp
        (m := n) (n := n) (s := s) (tau := tau) (theta := theta)
        htau hs A hden htheta
  have hvar :
      (sqMagSampleProbability Ahat hden).expectationCStarMatrix
        (fun sample : ElementwiseSample n n =>
          (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
          CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    simpa [Ahat, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          (sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              (finiteComplexCStarMatrix (D sample) * finiteComplexCStarMatrix (D sample) :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          ((sqMagSampleProbability Ahat hden).expectationCStarMatrix
            (fun x : ElementwiseSample n n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin n ⊕ Fin n => theta * D x a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have hexp :
        (fun x : ElementwiseSample n n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin n ⊕ Fin n => theta * D x a b))) =
        (fun x : ElementwiseSample n n =>
          NormedSpace.exp
            (theta • finiteComplexCStarMatrix (D x) :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      funext x
      rw [finiteComplexCStarMatrix_smul]
      rfl
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample n n) (a b : Fin n ⊕ Fin n) =>
        theta * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Algorithm 1 truncated upper-tail eigenvalue bound obtained from the
proved one-sample log-CGF, the C⋆ variance proxy, the iid trace-MGF iteration,
and the finite-dimensional trace-exponential Markov interface.

The theorem is still parameterized by `theta` and `T`; optimizing these
parameters and adding the lower-tail/spectral-norm conversion is the remaining
Bernstein tail step. -/
theorem sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_ge_le_exp
    {m n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∃ a : Fin m ⊕ Fin n,
            T ≤ finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a} ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
  classical
  intro Ahat L beta V
  have hmarkov :=
    sqMagTraceProbability_eventProb_exists_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_ge_le
      (A := Ahat) hden (ne_of_gt hs) theta T
  have htrace :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hmul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using htrace)
      (le_of_lt (Real.exp_pos _))
  exact hmarkov.trans hmul

/-- Negative-increment companion of
`sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le`.

This proves the scalar trace-MGF bound needed for the lower-tail half of the
two-sided matrix-Bernstein route.  The proof applies the same one-sample
log-CGF theorem to `-D(Z_t)`, using the negative support bound and the fact
that `(-X)^2 = X^2`. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let P := sqMagSampleProbability Ahat hden
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s Ahat sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, Ahat, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample m n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Negative-increment companion of the rectangular source-sharp truncated
trace-MGF bound.

The support radius is the same generic truncated radius as in the positive
bound, while the variance proxy is the rectangular
`max(m,n) * ||Ahat||_F^2 / s^2` proxy. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
    {m n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin m ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let P := sqMagSampleProbability Ahat hden
  let D : ElementwiseSample m n → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  let X : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample m n →
      CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s Ahat sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, Ahat, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample m n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample m n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_rect
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample m n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin m ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample m n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample m n) (a b : Fin m ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Source-sharp square-matrix negative-increment trace-MGF bound for
    Algorithm 1. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
    {n s : ℕ} {tau theta : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := s) Ahat hden
      (fun _a _b : Fin n ⊕ Fin n => 0)
      (fun sample a b =>
        (-theta) *
          rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)) := by
  classical
  intro Ahat L beta V
  let P := sqMagSampleProbability Ahat hden
  let D : ElementwiseSample n n → Fin n ⊕ Fin n → Fin n ⊕ Fin n → ℝ :=
    fun sample =>
      rectSelfAdjointDilation
        (elementwiseSampleResidualIncrement s Ahat sample)
  let X : ElementwiseSample n n →
      CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun sample => finiteComplexCStarMatrix (D sample)
  let Xneg : ElementwiseSample n n →
      CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ :=
    fun sample => -X sample
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hdenA : 0 < frobNormSqRect Ahat := by
      simpa [Ahat, sqMagProbDen] using hden
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    exact add_pos_of_nonneg_of_pos hfirst hsecond
  have hX : ∀ sample, IsSelfAdjoint (Xneg sample) := by
    intro sample
    have hD : IsSelfAdjoint (X sample) :=
      finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric
        (D sample)
        (rectSelfAdjointDilation_symmetric
          (elementwiseSampleResidualIncrement s Ahat sample))
    simpa [Xneg] using hD.neg
  have hmeanX : P.expectationCStarMatrix X = 0 := by
    simpa [P, X, D, Ahat] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
        Ahat hden (ne_of_gt hs)
  have hmean : P.expectationCStarMatrix Xneg = 0 := by
    calc
      P.expectationCStarMatrix Xneg
          = -P.expectationCStarMatrix X := by
              simpa [Xneg] using
                (FiniteProbability.expectationCStarMatrix_neg P X)
      _ = 0 := by simp [hmeanX]
  have hspec :
      ∀ sample, 0 < P.prob sample →
        ∀ x, x ∈ spectrum ℝ (Xneg sample) → x ≤ L := by
    intro sample hsample x hx
    simpa [P, X, Xneg, D, Ahat, L] using
      sqMagSampleProbability_neg_finiteComplex_rectSelfAdjointDilation_sampleResidualIncrement_truncated_spectrum_le_sharp
        htau hs A hden sample (by simpa [P, Ahat] using hsample) hx
  have hlog :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              NormedSpace.exp
                (theta • Xneg sample :
                  CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ))) ≤
        beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              Xneg sample * Xneg sample) := by
    simpa [P, Xneg, X, D, L, beta] using
      P.cstarMatrix_log_expectationCStarMatrix_normed_exp_real_smul_le_bernstein_variance_proxy_of_prob_pos
        hX hmean htheta hL_pos hspec
  have hsq :
      (fun sample : ElementwiseSample n n =>
          Xneg sample * Xneg sample) =
        (fun sample : ElementwiseSample n n =>
          X sample * X sample) := by
    funext sample
    ext a b
    simp [Xneg, X, CStarMatrix.mul_apply]
  have hvar :
      P.expectationCStarMatrix
        (fun sample : ElementwiseSample n n =>
          Xneg sample * Xneg sample) ≤
        (V : ℂ) • (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    rw [hsq]
    simpa [P, X, D, V] using
      sqMagSampleProbability_expectationCStarMatrix_rectSelfAdjointDilation_sampleResidualIncrement_square_le_sharp_square
        Ahat hden (ne_of_gt hs)
  have hbeta_nonneg : 0 ≤ beta := by
    dsimp [beta]
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    exact div_nonneg hnum (sq_nonneg L)
  have hscaled :
      beta •
          P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              Xneg sample * Xneg sample) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have h1 := smul_le_smul_of_nonneg_left hvar hbeta_nonneg
    have hEq :
        beta • ((V : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) =
          (((beta * V : ℝ) : ℂ) •
            (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    simpa [hEq] using h1
  have hK :
      CFC.log
          (P.expectationCStarMatrix
            (fun sample : ElementwiseSample n n =>
              NormedSpace.exp
                (finiteComplexCStarMatrix
                  (fun a b : Fin n ⊕ Fin n => (-theta) * D sample a b)))) ≤
        ((beta * V : ℝ) : ℂ) •
          (1 : CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ) := by
    have hexp :
        (fun sample : ElementwiseSample n n =>
          NormedSpace.exp
            (finiteComplexCStarMatrix
              (fun a b : Fin n ⊕ Fin n => (-theta) * D sample a b))) =
        (fun sample : ElementwiseSample n n =>
          NormedSpace.exp
            (theta • Xneg sample :
              CStarMatrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ)) := by
      funext sample
      congr 1
      ext a b
      simp [Xneg, X, D]
    rw [hexp]
    exact hlog.trans hscaled
  have hbound :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
      (steps := s) Ahat hden
      (fun (sample : ElementwiseSample n n) (a b : Fin n ⊕ Fin n) =>
        (-theta) * D sample a b)
      hK
  simpa [Fintype.card_sum, Fintype.card_fin, Nat.cast_add, Ahat, D, L, beta, V]
    using hbound

/-- Source-sharp square-matrix two-sided truncated eigenvalue tail skeleton
    before optimizing `theta`. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square
    {n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    1 -
        (Real.exp (-T) *
            (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin n ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin n ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < T} := by
  classical
  intro Ahat L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := Ahat) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
      (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_square
      (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin n ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin n ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin n ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin n ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
          (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin n ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin n ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Two-sided literal Algorithm 1 eigenvalue tail bound before optimizing
`theta`, using the exact input-dependent support radius.

This is the literal-law counterpart of the truncated Bernstein skeleton.  It
is fully nonconditional for exact squared-magnitude sampling, but the rate is
controlled by the irreducible finite radius
`elementwiseLiteralResidualSupportRadius s A`, which expands to
`(1/s)||A||_F + sum_{A_ij != 0} ||A||_F^2/(s |A_ij|)`. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_exp_supportRadius
    {m n s : ℕ} {theta T : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    1 -
        (Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a| < T} := by
  classical
  intro L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := A) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
      (m := m) (n := n) (s := s) (theta := theta)
      hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_literal_sampleResidualIncrement_le_supportRadius
      (m := m) (n := n) (s := s) (theta := theta)
      hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) A hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s A sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) A hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) A hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A sample) a b) ≤
      Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) A hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) A hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s A sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Two-sided Algorithm 1 truncated eigenvalue tail bound before optimizing
`theta`.

This combines the positive and negative scalar trace-MGF bounds with the
repository's two-sided trace-exponential Markov interface.  It is the
two-sided Bernstein tail skeleton for the truncated self-adjoint dilation; the
remaining CACM equation (2) work is the parameter optimization and conversion
from this eigenvalue event to the final stated spectral-norm constants. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp
    {m n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    1 -
        (Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < T} := by
  classical
  intro Ahat L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := Ahat) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Rectangular source-sharp two-sided truncated eigenvalue tail skeleton.

This is the same scaled-eigenvalue statement as the generic rectangular
truncated theorem, but it uses the sharpened rectangular variance proxy
`max(m,n) * ||Ahat||_F^2 / s^2`.  The support radius remains the generic
truncated radius with the `sqrt 2` factor. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_rect
    {m n s : ℕ} {tau theta T : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    1 -
        (Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
          Real.exp (-T) *
            (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < T} := by
  classical
  intro Ahat L beta V
  have htwo :=
    sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_elementwiseTraceResidual_lt_ge
      (A := Ahat) hden (ne_of_gt hs) theta T
  have hpos :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hneg :=
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound_neg_rectSelfAdjointDilation_truncated_sampleResidualIncrement_le_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
      htau hs A hden htheta
  have hposMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            theta * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hpos)
      (le_of_lt (Real.exp_pos _))
  have hnegMul :
      Real.exp (-T) *
        sqMagTraceProbabilityFiniteRealTraceMGFLogBound
          (steps := s) Ahat hden
          (fun _a _b : Fin m ⊕ Fin n => 0)
          (fun sample a b =>
            (-theta) * rectSelfAdjointDilation
              (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
        (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) := by
    exact mul_le_mul_of_nonneg_left
      (by simpa [Ahat, L, beta, V] using hneg)
      (le_of_lt (Real.exp_pos _))
  have hsum :
      Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              (-theta) * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) +
        Real.exp (-T) *
          sqMagTraceProbabilityFiniteRealTraceMGFLogBound
            (steps := s) Ahat hden
            (fun _a _b : Fin m ⊕ Fin n => 0)
            (fun sample a b =>
              theta * rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s Ahat sample) a b) ≤
      Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
        Real.exp (-T) *
          (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) :=
    add_le_add hnegMul hposMul
  have hsub :
      1 -
          (Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))) +
            Real.exp (-T) *
              (((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V)))) ≤
        1 -
          (Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  (-theta) * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b) +
            Real.exp (-T) *
              sqMagTraceProbabilityFiniteRealTraceMGFLogBound
                (steps := s) Ahat hden
                (fun _a _b : Fin m ⊕ Fin n => 0)
                (fun sample a b =>
                  theta * rectSelfAdjointDilation
                    (elementwiseSampleResidualIncrement s Ahat sample) a b)) := by
    linarith
  exact hsub.trans htwo

/-- Explicit high-probability form of the two-sided Algorithm 1 truncated
eigenvalue tail skeleton.

This corollary chooses
`T = log (2 B / δ)`, where
`B = (m + n) * exp (s * beta * V)` is the scalar trace-MGF bound from the
parameterized theorem above.  The choice makes the two equal
trace-exponential failure terms sum to `δ`.  The result is still a scaled
eigenvalue statement; optimizing `theta` and converting to the exact CACM
equation (2) constants remain the next red-bottleneck dependency. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro Ahat L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) Ahat hden).eventProb
          {samples |
            ∀ a : Fin m ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin m ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s Ahat samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s Ahat samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [Ahat, L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        (T := Real.log ((2 * B) / δ)) htau hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Explicit high-probability form of the rectangular source-sharp two-sided
truncated eigenvalue tail skeleton. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_rect
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro Ahat L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) Ahat hden).eventProb
          {samples |
            ∀ a : Fin m ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin m ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s Ahat samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s Ahat samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [Ahat, L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_rect
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta)
        (T := Real.log ((2 * B) / δ)) htau hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Explicit high-probability scaled-eigenvalue form for the literal
Algorithm 1 trace-MGF bound with input-dependent support radius. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_one_sub_delta_supportRadius
    {m n s : ℕ} {theta δ : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 ≤ theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples |
          ∀ a : Fin m ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin m ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s A samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s A samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) A hden).eventProb
          {samples |
            ∀ a : Fin m ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin m ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s A samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s A samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_exp_supportRadius
        (m := m) (n := n) (s := s) (theta := theta)
        (T := Real.log ((2 * B) / δ)) hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Explicit high-probability form of the source-sharp square-matrix
    two-sided truncated eigenvalue tail skeleton. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square
    {n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 ≤ theta)
    (hdim : 0 < (n : ℝ) + (n : ℝ)) (hδ : 0 < δ) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples |
          ∀ a : Fin n ⊕ Fin n,
            |finiteHermitianEigenvalues
              (fun b c : Fin n ⊕ Fin n =>
                theta *
                  rectSelfAdjointDilation
                    (elementwiseTraceResidual s Ahat samples) b c)
              (by
                intro b c
                exact congrArg (fun x => theta * x)
                  (rectSelfAdjointDilation_symmetric
                    (elementwiseTraceResidual s Ahat samples) b c))
              a| < Real.log ((2 * B) / δ)} := by
  classical
  intro Ahat L beta V B
  have hB_pos : 0 < B := by
    dsimp [B]
    exact mul_pos hdim (Real.exp_pos _)
  have htail :
      1 -
          (Real.exp (-Real.log ((2 * B) / δ)) * B +
            Real.exp (-Real.log ((2 * B) / δ)) * B) ≤
        (sqMagTraceProbability (steps := s) Ahat hden).eventProb
          {samples |
            ∀ a : Fin n ⊕ Fin n,
              |finiteHermitianEigenvalues
                (fun b c : Fin n ⊕ Fin n =>
                  theta *
                    rectSelfAdjointDilation
                      (elementwiseTraceResidual s Ahat samples) b c)
                (by
                  intro b c
                  exact congrArg (fun x => theta * x)
                    (rectSelfAdjointDilation_symmetric
                      (elementwiseTraceResidual s Ahat samples) b c))
                a| < Real.log ((2 * B) / δ)} := by
    simpa [Ahat, L, beta, V, B] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_exp_sharp_square
        (n := n) (s := s) (tau := tau) (theta := theta)
        (T := Real.log ((2 * B) / δ)) htau hs A hden htheta
  have hfailure :
      Real.exp (-Real.log ((2 * B) / δ)) * B +
          Real.exp (-Real.log ((2 * B) / δ)) * B = δ :=
    real_exp_neg_log_two_mul_div_mul_self_add (B := B) (δ := δ) hB_pos hδ
  simpa [hfailure] using htail

/-- Product-law expectation form of one-step zero mean for the self-adjoint
    dilation residual increment at a fixed trace coordinate. -/
theorem sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (t : Fin s) (a b : Fin m ⊕ Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A (samples t)) a b) = 0 := by
  classical
  have hstep :=
    sqMagTraceProbability_expectationReal_step_eq A hden t
      (fun sample : ElementwiseSample m n =>
        rectSelfAdjointDilation
          (elementwiseSampleResidualIncrement s A sample) a b)
  rw [hstep]
  exact sqMagProb_sum_rectSelfAdjointDilation_elementwiseSampleResidualIncrement_eq_zero
    s A hden hs a b

/-- The full self-adjoint dilation residual is entrywise mean-zero under the
    canonical independent squared-magnitude trace law. -/
theorem sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b) =
      0 := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b)
        = P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              ∑ t : Fin s,
                rectSelfAdjointDilation
                  (elementwiseSampleResidualIncrement s A (samples t)) a b) := by
            congr 1
            ext samples
            exact rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
              A samples hs a b
    _ = ∑ t : Fin s,
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              rectSelfAdjointDilation
                (elementwiseSampleResidualIncrement s A (samples t)) a b) := by
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ _t : Fin s, 0 := by
            apply Finset.sum_congr rfl
            intro t _
            exact
              sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_sampleResidualIncrement_eq_zero
                A hden hs t a b
    _ = 0 := by simp

/-- Scalar symmetrization for a fixed coordinate of the Algorithm 1
self-adjoint dilation residual.

This is a source-uniform-route foundation: the exact residual coordinate is
centered under the literal squared-magnitude product law, so its expected
absolute value is bounded by the expected absolute difference between two
independent copies of the same exact sketch. -/
theorem sqMagTraceProbability_expectationReal_abs_rectSelfAdjointDilation_elementwiseTraceResidual_le_prod_abs_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (a b : Fin m ⊕ Fin n) :
    let P := sqMagTraceProbability (steps := s) A hden
    P.expectationReal
        (fun samples =>
          |rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b|) ≤
      (P.prod P).expectationReal
        (fun x : ElementwiseTrace m n s × ElementwiseTrace m n s =>
          |rectSelfAdjointDilation (elementwiseTraceResidual s A x.1) a b -
            rectSelfAdjointDilation (elementwiseTraceResidual s A x.2) a b|) := by
  classical
  intro P
  exact
    FiniteProbability.expectationReal_abs_le_prod_expectationReal_abs_sub_of_expectation_eq_zero
      P
      (fun samples : ElementwiseTrace m n s =>
        rectSelfAdjointDilation (elementwiseTraceResidual s A samples) a b)
      (sqMagTraceProbability_expectationReal_rectSelfAdjointDilation_elementwiseTraceResidual_eq_zero
        A hden hs a b)

namespace FiniteProbability

/-- Jensen/duality bound for the Euclidean norm of a finite-probability vector
mean.

This avoids adding a matrix-algebra dependency to `FiniteProbability.lean`
itself, but gives the Khintchine route the standard finite-dimensional
ingredient `||E Y||_2 <= E ||Y||_2`. -/
theorem expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {n : ℕ}
    (Y : Ω → Fin n → ℝ) :
    vecNorm2 (fun i : Fin n => P.expectationReal (fun ω => Y ω i)) ≤
      P.expectationReal (fun ω => vecNorm2 (Y ω)) := by
  classical
  let z : Fin n → ℝ := fun i => P.expectationReal (fun ω => Y ω i)
  by_cases hz : vecNorm2 z = 0
  · have hright_nonneg :
        0 ≤ P.expectationReal (fun ω => vecNorm2 (Y ω)) := by
      unfold FiniteProbability.expectationReal
      exact Finset.sum_nonneg fun ω _ =>
        mul_nonneg (P.prob_nonneg ω) (vecNorm2_nonneg (Y ω))
    have hleft : vecNorm2 (fun i : Fin n => P.expectationReal (fun ω => Y ω i)) = 0 := by
      simpa [z] using hz
    rw [hleft]
    exact hright_nonneg
  · have hzpos : 0 < vecNorm2 z :=
      lt_of_le_of_ne (vecNorm2_nonneg z) (Ne.symm hz)
    let u : Fin n → ℝ := fun i => (vecNorm2 z)⁻¹ * z i
    have hinner_z :
        (∑ i : Fin n, u i * z i) = vecNorm2 z := by
      simpa [u] using vecInnerProduct_inv_smul_self_eq_norm z hzpos
    have hu_norm : vecNorm2 u = 1 := by
      simpa [u] using vecNorm2_inv_smul_self_of_pos z hzpos
    have hmean_inner :
        vecNorm2 z =
          P.expectationReal (fun ω => ∑ i : Fin n, u i * Y ω i) := by
      calc
        vecNorm2 z = ∑ i : Fin n, u i * z i := hinner_z.symm
        _ = ∑ i : Fin n, P.expectationReal (fun ω => u i * Y ω i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [FiniteProbability.expectationReal_const_mul]
        _ = P.expectationReal (fun ω => ∑ i : Fin n, u i * Y ω i) := by
              rw [FiniteProbability.expectationReal_sum]
    have hinner_abs :
        P.expectationReal (fun ω => ∑ i : Fin n, u i * Y ω i) ≤
          P.expectationReal (fun ω => |∑ i : Fin n, u i * Y ω i|) :=
      FiniteProbability.expectationReal_mono P fun ω => le_abs_self _
    have habs_norm :
        P.expectationReal (fun ω => |∑ i : Fin n, u i * Y ω i|) ≤
          P.expectationReal (fun ω => vecNorm2 (Y ω)) := by
      apply FiniteProbability.expectationReal_mono
      intro ω
      have hcs := abs_vecInnerProduct_le_vecNorm2_mul u (Y ω)
      simpa [hu_norm] using hcs
    have hmain :
        vecNorm2 z ≤ P.expectationReal (fun ω => vecNorm2 (Y ω)) :=
      hmean_inner.trans_le (hinner_abs.trans habs_norm)
    simpa [z] using hmain

/-- Finite vector-valued symmetrization around the mean. -/
theorem expectationReal_vecNorm2_sub_mean_le_prod_expectationReal_vecNorm2_sub
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {n : ℕ}
    (X : Ω → Fin n → ℝ) :
    P.expectationReal
        (fun ω => vecNorm2
          (fun i : Fin n => X ω i - P.expectationReal (fun η => X η i))) ≤
      (P.prod P).expectationReal
        (fun x : Ω × Ω => vecNorm2 (fun i : Fin n => X x.1 i - X x.2 i)) := by
  classical
  have hpoint :
      ∀ ω,
        vecNorm2
            (fun i : Fin n => X ω i - P.expectationReal (fun η => X η i)) ≤
          P.expectationReal
            (fun η => vecNorm2 (fun i : Fin n => X ω i - X η i)) := by
    intro ω
    have h :=
      expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2 P
        (fun η : Ω => fun i : Fin n => X ω i - X η i)
    have hmean :
        (fun i : Fin n =>
            P.expectationReal (fun η : Ω => X ω i - X η i)) =
          fun i : Fin n => X ω i - P.expectationReal (fun η : Ω => X η i) := by
      ext i
      calc
        P.expectationReal (fun η : Ω => X ω i - X η i)
            = P.expectationReal (fun _η : Ω => X ω i) -
                P.expectationReal (fun η : Ω => X η i) := by
                simpa using
                  (FiniteProbability.expectationReal_sub P
                    (fun _η : Ω => X ω i) (fun η : Ω => X η i))
        _ = X ω i - P.expectationReal (fun η : Ω => X η i) := by
                rw [FiniteProbability.expectationReal_const]
    simpa [hmean] using h
  calc
    P.expectationReal
        (fun ω => vecNorm2
          (fun i : Fin n => X ω i - P.expectationReal (fun η => X η i)))
        ≤ P.expectationReal
            (fun ω =>
              P.expectationReal
                (fun η => vecNorm2 (fun i : Fin n => X ω i - X η i))) :=
          FiniteProbability.expectationReal_mono P hpoint
    _ = (P.prod P).expectationReal
        (fun x : Ω × Ω => vecNorm2 (fun i : Fin n => X x.1 i - X x.2 i)) := by
          rw [FiniteProbability.prod_expectationReal_eq]

/-- Centered finite vector-valued symmetrization. -/
theorem expectationReal_vecNorm2_le_prod_expectationReal_vecNorm2_sub_of_expectation_eq_zero
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {n : ℕ}
    (X : Ω → Fin n → ℝ)
    (hmean : ∀ i : Fin n, P.expectationReal (fun ω => X ω i) = 0) :
    P.expectationReal (fun ω => vecNorm2 (X ω)) ≤
      (P.prod P).expectationReal
        (fun x : Ω × Ω => vecNorm2 (fun i : Fin n => X x.1 i - X x.2 i)) := by
  simpa [hmean] using
    expectationReal_vecNorm2_sub_mean_le_prod_expectationReal_vecNorm2_sub P X

end FiniteProbability

/-- The exact Algorithm 1 residual is mean-zero after applying it to any fixed
    vector. -/
theorem sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) (i : Fin m) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x i) = 0 := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x i)
        = P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              ∑ j : Fin n,
                elementwiseTraceResidual s A samples i j * x j) := by
            rfl
    _ = ∑ j : Fin n,
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceResidual s A samples i j * x j) := by
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ j : Fin n,
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceResidual s A samples i j) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [FiniteProbability.expectationReal_mul_const]
    _ = ∑ _j : Fin n, 0 := by
            apply Finset.sum_congr rfl
            intro j _
            rw [sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
              A hden hs]
            ring
    _ = 0 := by
            simp

/-- Fixed-vector Algorithm 1 symmetrization.

For any fixed vector `x`, the expected Euclidean norm of the exact residual
action is bounded by the expected Euclidean norm of the difference of two
independent exact residual actions.  This is a matrix-action version of the
scalar symmetrization checkpoint and is a reusable dependency for a future
matrix Khintchine route. -/
theorem sqMagTraceProbability_expectationReal_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_prod_vecNorm2_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (x : Fin n → ℝ) :
    let P := sqMagTraceProbability (steps := s) A hden
    P.expectationReal
        (fun samples =>
          vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x)) ≤
      (P.prod P).expectationReal
        (fun y : ElementwiseTrace m n s × ElementwiseTrace m n s =>
          vecNorm2
            (fun i : Fin m =>
              rectMatMulVec (elementwiseTraceResidual s A y.1) x i -
                rectMatMulVec (elementwiseTraceResidual s A y.2) x i)) := by
  classical
  intro P
  exact
    FiniteProbability.expectationReal_vecNorm2_le_prod_expectationReal_vecNorm2_sub_of_expectation_eq_zero
      P
      (fun samples : ElementwiseTrace m n s =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x)
      (fun i =>
        sqMagTraceProbability_expectationReal_rectMatMulVec_elementwiseTraceResidual_eq_zero
          A hden hs x i)

namespace FiniteProbability

/-- Operator-predicate independent-copy symmetrization for rectangular
matrix-valued random variables.

For a fixed outcome `ω`, if every independent-copy difference `X ω - X η` is
bounded by `L` in the rectangular operator predicate, and if the matrix entries
of `X` are centered under `P`, then `X ω` itself is bounded by `L`.

This is a deterministic Jensen/convexity adapter.  It does not prove a tail
bound for the copy-difference event; that is the future Khintchine/matrix-tail
step. -/
theorem rectOpNorm2Le_of_entrywise_mean_zero_of_copy_diff_rectOpNorm2Le
    {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) {m n : ℕ}
    (X : Ω → Fin m → Fin n → ℝ)
    (hmean : ∀ i j, P.expectationReal (fun η => X η i j) = 0)
    (ω : Ω) {L : ℝ}
    (hdiff : ∀ η : Ω,
      rectOpNorm2Le (fun i j => X ω i j - X η i j) L) :
    rectOpNorm2Le (X ω) L := by
  classical
  intro x
  let Y : Ω → Fin m → ℝ :=
    fun η => rectMatMulVec (fun i j => X ω i j - X η i j) x
  have hmean_vec :
      (fun i : Fin m => P.expectationReal (fun η => Y η i)) =
        rectMatMulVec (X ω) x := by
    ext i
    calc
      P.expectationReal (fun η : Ω => Y η i)
          =
            P.expectationReal
              (fun η : Ω =>
                ∑ j : Fin n, (X ω i j - X η i j) * x j) := by
              rfl
      _ = ∑ j : Fin n,
            P.expectationReal
              (fun η : Ω => (X ω i j - X η i j) * x j) := by
              rw [FiniteProbability.expectationReal_sum]
      _ = ∑ j : Fin n,
            (X ω i j - P.expectationReal (fun η : Ω => X η i j)) * x j := by
              apply Finset.sum_congr rfl
              intro j _
              calc
                P.expectationReal
                    (fun η : Ω => (X ω i j - X η i j) * x j)
                    =
                  P.expectationReal
                    (fun η : Ω => X ω i j - X η i j) * x j := by
                    rw [FiniteProbability.expectationReal_mul_const]
                _ =
                  (P.expectationReal (fun _η : Ω => X ω i j) -
                    P.expectationReal (fun η : Ω => X η i j)) * x j := by
                    rw [FiniteProbability.expectationReal_sub]
                _ =
                  (X ω i j - P.expectationReal (fun η : Ω => X η i j)) *
                    x j := by
                    rw [FiniteProbability.expectationReal_const]
      _ = ∑ j : Fin n, X ω i j * x j := by
              apply Finset.sum_congr rfl
              intro j _
              rw [hmean i j]
              ring
      _ = rectMatMulVec (X ω) x i := by
              rfl
  have hleft :
      vecNorm2 (rectMatMulVec (X ω) x) ≤
        P.expectationReal (fun η => vecNorm2 (Y η)) := by
    calc
      vecNorm2 (rectMatMulVec (X ω) x)
          = vecNorm2 (fun i : Fin m => P.expectationReal (fun η => Y η i)) := by
              rw [hmean_vec]
      _ ≤ P.expectationReal (fun η => vecNorm2 (Y η)) :=
              expectationReal_vecNorm2_mean_le_expectationReal_vecNorm2 P Y
  have hright :
      P.expectationReal (fun η => vecNorm2 (Y η)) ≤ L * vecNorm2 x := by
    calc
      P.expectationReal (fun η => vecNorm2 (Y η))
          ≤ P.expectationReal (fun _η : Ω => L * vecNorm2 x) := by
              apply FiniteProbability.expectationReal_mono
              intro η
              exact hdiff η x
      _ = L * vecNorm2 x := by
              rw [FiniteProbability.expectationReal_const]
  exact hleft.trans hright

end FiniteProbability

/-- Operator-predicate independent-copy symmetrization specialized to
Algorithm 1.

For a fixed realized trace, if every independent exact copy of the Algorithm 1
trace residual differs from it by an operator-`L` matrix, then the realized
residual itself is operator-`L`.  The only probability input is the exact
squared-magnitude law used to know that the residual entries are mean-zero. -/
theorem sqMagTraceProbability_rectOpNorm2Le_elementwiseTraceResidual_of_all_copy_diffs
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (samples : ElementwiseTrace m n s) {L : ℝ}
    (hdiff : ∀ samples' : ElementwiseTrace m n s,
      rectOpNorm2Le
        (fun i j =>
          elementwiseTraceResidual s A samples i j -
            elementwiseTraceResidual s A samples' i j)
        L) :
    rectOpNorm2Le (elementwiseTraceResidual s A samples) L := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  exact
    FiniteProbability.rectOpNorm2Le_of_entrywise_mean_zero_of_copy_diff_rectOpNorm2Le
      P
      (fun samples : ElementwiseTrace m n s =>
        elementwiseTraceResidual s A samples)
      (fun i j =>
        sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_eq_zero
          A hden hs i j)
      samples hdiff

/-- Event that the exact Algorithm 1 residual satisfies a rectangular
    vector-action operator-2 bound.  This is the repository's formal target
    shape for the exact spectral-norm statement in CACM equation (2). -/
def algorithm1ExactSpectralEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω | rectOpNorm2Le (elementwiseTraceResidual s A (X ω)) ε}

/-- Event that all exact independent-copy differences from a realized
Algorithm 1 trace are rectangular operator-bounded by `L`.  This is a
symmetrization support event; it is not itself a probability tail theorem. -/
def algorithm1ExactAllCopyDiffSpectralEvent {m n s : ℕ}
    (A : Fin m → Fin n → ℝ) (L : ℝ) : Set (ElementwiseTrace m n s) :=
  {samples |
    ∀ samples' : ElementwiseTrace m n s,
      rectOpNorm2Le
        (fun i j =>
          elementwiseTraceResidual s A samples i j -
            elementwiseTraceResidual s A samples' i j)
        L}

/-- Independent-copy difference event implies the exact Algorithm 1 spectral
event at the same radius. -/
theorem algorithm1ExactAllCopyDiffSpectralEvent_subset_exactSpectralEvent
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0) (L : ℝ) :
    algorithm1ExactAllCopyDiffSpectralEvent (m := m) (n := n) (s := s) A L ⊆
      algorithm1ExactSpectralEvent s A
        (fun samples : ElementwiseTrace m n s => samples) L := by
  intro samples hdiff
  exact
    sqMagTraceProbability_rectOpNorm2Le_elementwiseTraceResidual_of_all_copy_diffs
      A hden hs samples hdiff

/-- Probability transfer from the all-independent-copy-differences event to
the exact Algorithm 1 spectral event.  This is exact-law infrastructure for a
future Khintchine tail on copy differences. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_of_all_copy_diff
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : (s : ℝ) ≠ 0)
    (ρ L : ℝ)
    (hCopy :
      ρ ≤
        (sqMagTraceProbability (steps := s) A hden).eventProb
          (algorithm1ExactAllCopyDiffSpectralEvent
            (m := m) (n := n) (s := s) A L)) :
    ρ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) L) := by
  exact le_trans hCopy
    ((sqMagTraceProbability (steps := s) A hden).eventProb_mono
      (algorithm1ExactAllCopyDiffSpectralEvent_subset_exactSpectralEvent
        A hden hs L))

/-- For the small-entry counterexample, the exact all-copy-difference support
event fails with probability at least the probability of sampling the tiny
entry in the first trace.  Thus this copy-difference event cannot be silently
treated as probability-one for the literal untruncated squared-magnitude law. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge
    (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    sqMagProb A (0 : Fin 1) (1 : Fin 2) ≤
      (sqMagTraceProbability (steps := 1) A
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 1 |
          samples ∉
            algorithm1ExactAllCopyDiffSpectralEvent
              (m := 1) (n := 2) (s := 1) A L} := by
  classical
  intro A
  let P := sqMagTraceProbability (steps := 1) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let Hit : Set (ElementwiseTrace 1 2 1) :=
    {samples | sampleHits samples (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)}
  let Bad : Set (ElementwiseTrace 1 2 1) :=
    {samples |
      samples ∉
        algorithm1ExactAllCopyDiffSpectralEvent
          (m := 1) (n := 2) (s := 1) A L}
  have hHitProb :
      P.eventProb Hit =
        sqMagProb A (0 : Fin 1) (1 : Fin 2) := by
    simpa [P, Hit, A] using
      sqMagTraceProbability_eventProb_sampleHits
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
        (0 : Fin 1) (0 : Fin 1) (1 : Fin 2)
  have hsubset : Hit ⊆ Bad := by
    intro samples hhit hall
    let samplesUnit : ElementwiseTrace 1 2 1 :=
      fun _ : Fin 1 => ((0 : Fin 1), (0 : Fin 2))
    have hsamp0 :
        samples (0 : Fin 1) = ((0 : Fin 1), (1 : Fin 2)) :=
      Prod.ext hhit.1 hhit.2
    have hsamples :
        samples = (fun _ : Fin 1 => ((0 : Fin 1), (1 : Fin 2))) := by
      funext t
      fin_cases t
      exact hsamp0
    have hdiff := hall samplesUnit
    exact
      algorithm1SmallEntrySupportMatrix_trace_residual_small_unit_diff_not_rectOpNorm2Le
        L
        (by
          simpa [A, samplesUnit, hsamples] using hdiff)
  calc
    sqMagProb A (0 : Fin 1) (1 : Fin 2) = P.eventProb Hit := hHitProb.symm
    _ ≤ P.eventProb Bad := P.eventProb_mono hsubset

/-- Positive-probability form of
`sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge`. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_pos
    (L : ℝ) :
    0 <
      (sqMagTraceProbability (steps := 1)
        (algorithm1SmallEntrySupportMatrix L)
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 1 |
          samples ∉
            algorithm1ExactAllCopyDiffSpectralEvent
              (m := 1) (n := 2) (s := 1)
              (algorithm1SmallEntrySupportMatrix L) L} := by
  have hpos :=
    sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hle :=
    sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge
      L
  exact hpos.trans_le hle

/-- Quantitative necessary condition for any high-probability all-copy support
claim on the small-entry family.

If the literal all-copy-differences event for `[1,(|L|+2)^{-1}]` is claimed to
hold with probability at least `1 - delta`, then `delta` must be at least the
exact probability of sampling the tiny entry. -/
theorem sqMagTraceProbability_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_delta_ge
    (L δ : ℝ)
    (hAll :
      1 - δ ≤
        (sqMagTraceProbability (steps := 1)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactAllCopyDiffSpectralEvent
            (m := 1) (n := 2) (s := 1)
            (algorithm1SmallEntrySupportMatrix L) L)) :
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2) ≤ δ := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let P := sqMagTraceProbability (steps := 1) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let E : Set (ElementwiseTrace 1 2 1) :=
    algorithm1ExactAllCopyDiffSpectralEvent
      (m := 1) (n := 2) (s := 1) A L
  have hbad :
      sqMagProb A (0 : Fin 1) (1 : Fin 2) ≤ P.eventProb Eᶜ := by
    simpa [A, P, E, Set.mem_compl_iff] using
      sqMagTraceProbability_eventProb_not_algorithm1ExactAllCopyDiffSpectralEvent_smallEntry_ge
        L
  have hsplit := P.eventProb_add_eventProb_compl E
  have hAll' : 1 - δ ≤ P.eventProb E := by
    simpa [A, P, E] using hAll
  have hcompl_le : P.eventProb Eᶜ ≤ δ := by
    linarith
  simpa [A] using hbad.trans hcompl_le

/-- Product-law mass of the trace that samples the tiny entry at every step in
the small-entry obstruction family. -/
theorem sqMagTraceProbMass_algorithm1SmallEntrySupportMatrix_all_tiny
    (s : ℕ) (L : ℝ) :
    sqMagTraceProbMass (algorithm1SmallEntrySupportMatrix L)
      (fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2))) =
      (sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)) ^ s := by
  classical
  simp [sqMagTraceProbMass]

/-- For any positive sample count, the trace that samples the tiny entry at
every step violates the exact spectral event at radius `L`.  This strengthens
the one-step obstruction from a support-radius failure to a failure of the
Algorithm 1 exact residual event itself. -/
theorem algorithm1SmallEntrySupportMatrix_all_tiny_trace_residual_not_rectOpNorm2Le
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    ¬ rectOpNorm2Le
      (elementwiseTraceResidual s (algorithm1SmallEntrySupportMatrix L)
        (fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2)))) L := by
  classical
  intro hnorm
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let samplesTiny : ElementwiseTrace 1 2 s :=
    fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2))
  let M : Fin 1 → Fin 2 → ℝ :=
    elementwiseTraceResidual s A samplesTiny
  let x : Fin 2 → ℝ := finiteBasisVec (1 : Fin 2)
  have hxnorm : vecNorm2 x = 1 := by
    simp [x, finiteBasisVec, vecNorm2, vecNorm2Sq]
  have hleft :
      vecNorm2 (rectMatMulVec M x) = |M (0 : Fin 1) (1 : Fin 2)| := by
    simp [M, x, rectMatMulVec, finiteBasisVec, vecNorm2, vecNorm2Sq]
    rw [Real.sqrt_sq_eq_abs]
  have hbase : 0 < |L| + 2 := by
    nlinarith [abs_nonneg L]
  have hbase_ne : |L| + 2 ≠ 0 := ne_of_gt hbase
  have hs_ne : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have hentry :
      M (0 : Fin 1) (1 : Fin 2) = -(|L| + 2) := by
    simp [M, A, samplesTiny, elementwiseTraceResidual, elementwiseTraceSketch,
      elementwiseTraceContribution, sampleHits, elementwiseIncrement,
      elementwiseIncrementWithProb, sqMagProb, sqMagProbDen, frobNormSqRect,
      algorithm1SmallEntrySupportMatrix, Finset.sum_const, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [hbase_ne, hs_ne]
    ring_nf
  have hentry_gt : L < |M (0 : Fin 1) (1 : Fin 2)| := by
    rw [hentry, abs_neg, abs_of_pos hbase]
    nlinarith [le_abs_self L]
  have hbound := hnorm x
  rw [hleft, hxnorm, mul_one] at hbound
  exact not_le_of_gt hentry_gt hbound

/-- Quantitative lower bound on exact spectral-event failure for the
small-entry family at any positive sample count: the all-tiny trace alone has
mass `p_tiny ^ s` and is outside the radius-`L` event. -/
theorem sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    (sqMagProb A (0 : Fin 1) (1 : Fin 2)) ^ s ≤
      (sqMagTraceProbability (steps := s) A
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        {samples : ElementwiseTrace 1 2 s |
          samples ∉
            algorithm1ExactSpectralEvent s A
              (fun samples : ElementwiseTrace 1 2 s => samples) L} := by
  classical
  intro A
  let P := sqMagTraceProbability (steps := s) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let tinyTrace : ElementwiseTrace 1 2 s :=
    fun _ : Fin s => ((0 : Fin 1), (1 : Fin 2))
  let Bad : Set (ElementwiseTrace 1 2 s) :=
    {samples |
      samples ∉
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace 1 2 s => samples) L}
  have htiny_bad : tinyTrace ∈ Bad := by
    intro htiny_good
    exact
      algorithm1SmallEntrySupportMatrix_all_tiny_trace_residual_not_rectOpNorm2Le
        hs L
        (by
          simpa [A, tinyTrace, algorithm1ExactSpectralEvent] using htiny_good)
  have hmass :
      P.prob tinyTrace =
        (sqMagProb A (0 : Fin 1) (1 : Fin 2)) ^ s := by
    simp [P, tinyTrace, A, sqMagTraceProbability,
      sqMagTraceProbMass_algorithm1SmallEntrySupportMatrix_all_tiny]
  rw [← hmass]
  exact FiniteProbability.prob_le_eventProb_of_mem P htiny_bad

/-- Necessary condition for any `1 - delta` lower bound on the exact spectral
event for the small-entry family at a positive sample count.  Even the exact
Algorithm 1 spectral event must pay at least the all-tiny trace mass. -/
theorem sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
    {s : ℕ} (hs : 0 < s) (L δ : ℝ)
    (hEvent :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) :
    (sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)) ^ s ≤ δ := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let P := sqMagTraceProbability (steps := s) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let E : Set (ElementwiseTrace 1 2 s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace 1 2 s => samples) L
  have hbad :
      (sqMagProb A (0 : Fin 1) (1 : Fin 2)) ^ s ≤ P.eventProb Eᶜ := by
    simpa [A, P, E, Set.mem_compl_iff] using
      sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge
        hs L
  have hsplit := P.eventProb_add_eventProb_compl E
  have hEvent' : 1 - δ ≤ P.eventProb E := by
    simpa [A, P, E] using hEvent
  have hcompl_le : P.eventProb Eᶜ ≤ δ := by
    linarith
  simpa [A] using hbad.trans hcompl_le

/-- Logarithmic form of a power-mass obstruction.  If a bad trace of one-step
mass `p` occurs with product mass `p^s`, then any failure budget `δ` that
dominates that trace mass must satisfy the corresponding logarithmic
sample-count lower bound. -/
theorem log_inv_delta_le_nat_mul_log_inv_of_pow_le
    {s : ℕ} {p δ : ℝ} (hp : 0 < p) (hδ : 0 < δ)
    (hpow : p ^ s ≤ δ) :
    Real.log (1 / δ) ≤ (s : ℝ) * Real.log (1 / p) := by
  have hpows : 0 < p ^ s := pow_pos hp s
  have hrecip : 1 / δ ≤ 1 / (p ^ s) :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) hpows hpow
  have hlog :=
    Real.log_le_log (one_div_pos.mpr hδ) hrecip
  have hrewrite :
      Real.log (1 / (p ^ s)) = (s : ℝ) * Real.log (1 / p) := by
    rw [one_div, Real.log_inv, Real.log_pow, one_div, Real.log_inv]
    ring
  simpa [hrewrite] using hlog

/-- Divided logarithmic form of a power-mass obstruction.  If `0 < p < 1`,
then the logarithmic denominator is positive, so the logarithmic obstruction
can be stated as a direct lower bound on the sample count. -/
theorem log_inv_delta_div_log_inv_le_nat_of_pow_le
    {s : ℕ} {p δ : ℝ} (hp : 0 < p) (hp_lt_one : p < 1)
    (hδ : 0 < δ) (hpow : p ^ s ≤ δ) :
    Real.log (1 / δ) / Real.log (1 / p) ≤ (s : ℝ) := by
  have hlog :
      Real.log (1 / δ) ≤ (s : ℝ) * Real.log (1 / p) :=
    log_inv_delta_le_nat_mul_log_inv_of_pow_le hp hδ hpow
  have hden_pos : 0 < Real.log (1 / p) :=
    Real.log_pos (one_lt_one_div hp hp_lt_one)
  exact (div_le_iff₀ hden_pos).mpr hlog

/-- Logarithmic necessary condition for a `1 - delta` exact spectral-event
claim on the Algorithm 1 small-entry obstruction family.  The displayed
inequality is the order form of the all-tiny mass condition
`p_tiny^s <= delta`. -/
theorem sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_log_delta_le
    {s : ℕ} (hs : 0 < s) (L δ : ℝ) (hδ : 0 < δ)
    (hEvent :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) :
    let pTiny : ℝ :=
      sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)
    Real.log (1 / δ) ≤ (s : ℝ) * Real.log (1 / pTiny) := by
  classical
  intro pTiny
  have hp : 0 < pTiny := by
    simpa [pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hpow : pTiny ^ s ≤ δ := by
    simpa [pTiny] using
      sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
        hs L δ hEvent
  exact log_inv_delta_le_nat_mul_log_inv_of_pow_le hp hδ hpow

/-- Sample-count lower-bound form of the Algorithm 1 all-tiny obstruction.
The small-entry probability is strictly between zero and one, so any `1 -
delta` exact spectral-event claim on this family forces the displayed divided
logarithmic lower bound on `s`. -/
theorem sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge
    {s : ℕ} (hs : 0 < s) (L δ : ℝ) (hδ : 0 < δ)
    (hEvent :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) :
    let pTiny : ℝ :=
      sqMagProb (algorithm1SmallEntrySupportMatrix L)
        (0 : Fin 1) (1 : Fin 2)
    Real.log (1 / δ) / Real.log (1 / pTiny) ≤ (s : ℝ) := by
  classical
  intro pTiny
  have hp : 0 < pTiny := by
    simpa [pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hp_lt_one : pTiny < 1 := by
    simpa [pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_lt_one L
  have hpow : pTiny ^ s ≤ δ := by
    simpa [pTiny] using
        sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
        hs L δ hEvent
  exact log_inv_delta_div_log_inv_le_nat_of_pow_le hp hp_lt_one hδ hpow

/-- Direct incompatibility form of the all-tiny obstruction.

If the claimed failure budget `delta` is smaller than the exact all-tiny trace
mass `p_tiny ^ s`, then the radius-`L` exact Algorithm 1 spectral event cannot
hold with probability at least `1 - delta` on the small-entry family. -/
theorem sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
    {s : ℕ} (hs : 0 < s) (L δ : ℝ)
    (hδ_small :
      let pTiny : ℝ :=
        sqMagProb (algorithm1SmallEntrySupportMatrix L)
          (0 : Fin 1) (1 : Fin 2)
      δ < pTiny ^ s) :
    ¬
      (1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) := by
  classical
  intro hEvent
  let pTiny : ℝ :=
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
      (0 : Fin 1) (1 : Fin 2)
  have hpow_le : pTiny ^ s ≤ δ := by
    simpa [pTiny] using
      sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_delta_ge
        hs L δ hEvent
  have hδ_small' : δ < pTiny ^ s := by
    simpa [pTiny] using hδ_small
  exact (not_lt_of_ge hpow_le) hδ_small'

/-- Divided-log incompatibility form of the all-tiny obstruction.

For positive `delta`, if the sample count is strictly below the exact
lower-bound threshold
`log (1 / delta) / log (1 / p_tiny)`, then the radius-`L` exact Algorithm 1
spectral event cannot have probability at least `1 - delta` on the
small-entry family. -/
theorem sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_sample_count_lt
    {s : ℕ} (hs : 0 < s) (L δ : ℝ) (hδ : 0 < δ)
    (hs_lt :
      let pTiny : ℝ :=
        sqMagProb (algorithm1SmallEntrySupportMatrix L)
          (0 : Fin 1) (1 : Fin 2)
      (s : ℝ) < Real.log (1 / δ) / Real.log (1 / pTiny)) :
    ¬
      (1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (algorithm1SmallEntrySupportMatrix L)
          (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
          (algorithm1ExactSpectralEvent s
            (algorithm1SmallEntrySupportMatrix L)
            (fun samples : ElementwiseTrace 1 2 s => samples) L)) := by
  classical
  intro hEvent
  let pTiny : ℝ :=
    sqMagProb (algorithm1SmallEntrySupportMatrix L)
      (0 : Fin 1) (1 : Fin 2)
  have hlower :
      Real.log (1 / δ) / Real.log (1 / pTiny) ≤ (s : ℝ) := by
    simpa [pTiny] using
      sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry_sample_count_ge
        hs L δ hδ hEvent
  have hs_lt' :
      (s : ℝ) < Real.log (1 / δ) / Real.log (1 / pTiny) := by
    simpa [pTiny] using hs_lt
  exact (not_lt_of_ge hlower) hs_lt'

/-- Success-probability upper bound from the all-tiny obstruction.

For the literal small-entry family, the exact radius-`L` spectral event has
success probability at most `1 - p_tiny ^ s`, because the all-tiny trace alone
has exact product-law mass `p_tiny ^ s` and lies outside the event. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
    (sqMagTraceProbability (steps := s) A
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
      (algorithm1ExactSpectralEvent s A
        (fun samples : ElementwiseTrace 1 2 s => samples) L) ≤
      1 - pTiny ^ s := by
  classical
  intro A pTiny
  let P := sqMagTraceProbability (steps := s) A
    (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)
  let E : Set (ElementwiseTrace 1 2 s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace 1 2 s => samples) L
  have hbad :
      pTiny ^ s ≤ P.eventProb Eᶜ := by
    simpa [A, pTiny, P, E, Set.mem_compl_iff] using
      sqMagTraceProbability_eventProb_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_ge
        hs L
  have hsplit := P.eventProb_add_eventProb_compl E
  nlinarith

/-- Strict form of the all-tiny success-probability obstruction.

For every positive sample count, the exact radius-`L` spectral event for the
literal small-entry family has probability strictly below one. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_lt_one
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
    (sqMagTraceProbability (steps := s) A
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
      (algorithm1ExactSpectralEvent s A
        (fun samples : ElementwiseTrace 1 2 s => samples) L) < 1 := by
  classical
  intro A
  let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
  have hp : 0 < pTiny := by
    simpa [A, pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hpow_pos : 0 < pTiny ^ s := pow_pos hp s
  have hle :
      (sqMagTraceProbability (steps := s) A
        (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace 1 2 s => samples) L) ≤
        1 - pTiny ^ s := by
    simpa [A, pTiny] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_all_tiny_smallEntry_le_one_sub_pow
        hs L
  nlinarith

/-- Fixed-sample impossibility form.

For any fixed positive sample count and radius `L`, there is a positive
failure budget `delta` for which the literal small-entry exact spectral event
cannot have probability at least `1 - delta`. -/
theorem exists_delta_not_sqMagTraceProbability_algorithm1ExactSpectralEvent_all_tiny_smallEntry
    {s : ℕ} (hs : 0 < s) (L : ℝ) :
    ∃ δ : ℝ,
      0 < δ ∧
      ¬
        (1 - δ ≤
          (sqMagTraceProbability (steps := s)
            (algorithm1SmallEntrySupportMatrix L)
            (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos L)).eventProb
            (algorithm1ExactSpectralEvent s
              (algorithm1SmallEntrySupportMatrix L)
              (fun samples : ElementwiseTrace 1 2 s => samples) L)) := by
  classical
  let A : Fin 1 → Fin 2 → ℝ := algorithm1SmallEntrySupportMatrix L
  let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
  have hp : 0 < pTiny := by
    simpa [A, pTiny] using sqMagProb_algorithm1SmallEntrySupportMatrix_small_pos L
  have hpow_pos : 0 < pTiny ^ s := pow_pos hp s
  refine ⟨pTiny ^ s / 2, ?_, ?_⟩
  · nlinarith
  · have hsmall : pTiny ^ s / 2 < pTiny ^ s := by
      nlinarith
    exact
      sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
        (s := s) hs L (pTiny ^ s / 2)
        (by simpa [A, pTiny] using hsmall)

/-- A small numerical logarithm certificate used by the concrete Algorithm 1
source-budget obstruction below.  The proof uses only `2 ≤ exp 1`, so it is a
coarse exact certificate rather than an external decimal approximation. -/
theorem real_log_180000_le_18 : Real.log (180000 : ℝ) ≤ 18 := by
  have hpos : (0 : ℝ) < 180000 := by norm_num
  rw [Real.log_le_iff_le_exp hpos]
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h
    exact h
  have hpow : (2 : ℝ) ^ 18 ≤ (Real.exp 1) ^ 18 :=
    pow_le_pow_left₀ (by norm_num) h2e 18
  have hexp : (Real.exp 1) ^ 18 = Real.exp 18 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h180 : (180000 : ℝ) ≤ (2 : ℝ) ^ 18 := by norm_num
  exact h180.trans (by simpa [hexp] using hpow)

/-- The concrete rectangular source-style budget at `m = 1`, `n = 2`,
`s = 1`, radius `100`, and failure budget `1/30000`.

This predicate is exact arithmetic only.  It records the budget surface whose
source-uniform use is refuted by the concrete small-entry witness below. -/
def algorithm1RectSourceBudget_1_2_100_one_div_30000
    (A : Fin 1 → Fin 2 → ℝ) : Prop :=
  4 *
      (let M : ℝ := max (1 : ℝ) (2 : ℝ)
       let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
       let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
       C) *
      frobNormSqRect A *
      Real.log ((2 * ((1 : ℝ) + (2 : ℝ))) / ((1 : ℝ) / 30000)) ≤
    (1 : ℝ) * (100 : ℝ) ^ 2

/-- In the concrete small-entry witness with radius `100` and
`δ = 1/30000`, the tiny entry has one-step sampling probability larger than
`δ`. -/
theorem algorithm1SmallEntrySupportMatrix_100_small_prob_gt_one_div_30000 :
    (1 / 30000 : ℝ) <
      sqMagProb (algorithm1SmallEntrySupportMatrix (100 : ℝ))
        (0 : Fin 1) (1 : Fin 2) := by
  norm_num [sqMagProb, sqMagProbDen, frobNormSqRect,
    algorithm1SmallEntrySupportMatrix]

/-- The concrete small-entry witness satisfies the rectangular source-style
sample-budget inequality with `m = 1`, `n = 2`, `s = 1`, radius `eps = 100`,
and `δ = 1/30000`.

This theorem is exact arithmetic/probability only.  It says the displayed
source-budget premise can be true for the literal untruncated law even though
the spectral event lower bound is refuted by the next theorem. -/
theorem algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000 :
    algorithm1RectSourceBudget_1_2_100_one_div_30000
      (algorithm1SmallEntrySupportMatrix (100 : ℝ)) := by
  have hlog : Real.log (180000 : ℝ) ≤ 18 := real_log_180000_le_18
  have hC :
      (let M : ℝ := max (1 : ℝ) (2 : ℝ)
       let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
       let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
       C) ≤ 7 := by
    have hsqrt : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
      rw [← sq, Real.sq_sqrt]
      norm_num
    calc
      (let M : ℝ := max (1 : ℝ) (2 : ℝ)
       let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
       let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
       C)
          = 4 + ((4 * Real.sqrt 2) / 3) * Real.sqrt 2 := by
              norm_num [max_eq_right]
      _ = 4 + 8 / 3 := by
              rw [div_mul_eq_mul_div, mul_assoc, hsqrt]
              norm_num
      _ ≤ 7 := by norm_num
  have hF :
      frobNormSqRect (algorithm1SmallEntrySupportMatrix (100 : ℝ)) ≤ 2 := by
    norm_num [frobNormSqRect, algorithm1SmallEntrySupportMatrix]
  have hnonnegC :
      0 ≤
        (let M : ℝ := max (1 : ℝ) (2 : ℝ)
         let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
         let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
         C) := by positivity
  have hnonnegF :
      0 ≤ frobNormSqRect (algorithm1SmallEntrySupportMatrix (100 : ℝ)) :=
    frobNormSqRect_nonneg _
  have hlog_nonneg : 0 ≤ Real.log (180000 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hmain :
      4 *
          (let M : ℝ := max (1 : ℝ) (2 : ℝ)
           let R : ℝ := Real.sqrt ((1 : ℝ) * (2 : ℝ))
           let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
           C) *
          frobNormSqRect (algorithm1SmallEntrySupportMatrix (100 : ℝ)) *
          Real.log (180000 : ℝ) ≤
        4 * 7 * 2 * 18 := by
    gcongr
  have htarget : 4 * 7 * 2 * 18 ≤ (1 : ℝ) * (100 : ℝ) ^ 2 := by
    norm_num
  have harg :
      (2 * ((1 : ℝ) + (2 : ℝ))) / ((1 : ℝ) / 30000) =
        (180000 : ℝ) := by
    norm_num
  unfold algorithm1RectSourceBudget_1_2_100_one_div_30000
  rw [harg]
  exact hmain.trans htarget

/-- Concrete source-budget incompatibility witness for the literal
untruncated Algorithm 1 law.

For `m = 1`, `n = 2`, `s = 1`, radius `100`, and `δ = 1/30000`, the usual
rectangular source-style sample budget is true, but the exact squared-magnitude
law cannot satisfy the advertised spectral-event lower bound.  Thus a literal
source-uniform equation-(2) theorem cannot be justified by this source budget
alone on inputs with arbitrarily small nonzero entries. -/
theorem sqMagTraceProbability_not_algorithm1ExactSpectralEvent_rect_source_budget_witness :
    let A : Fin 1 → Fin 2 → ℝ :=
      algorithm1SmallEntrySupportMatrix (100 : ℝ)
    algorithm1RectSourceBudget_1_2_100_one_div_30000 A ∧
      ¬
        (1 - (1 / 30000 : ℝ) ≤
          (sqMagTraceProbability (steps := 1) A
            (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (100 : ℝ))).eventProb
            (algorithm1ExactSpectralEvent 1 A
              (fun samples : ElementwiseTrace 1 2 1 => samples) (100 : ℝ))) := by
  classical
  intro A
  refine ⟨?_, ?_⟩
  · simpa [A] using
      algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000
  · have hδ_small :
        let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
        (1 / 30000 : ℝ) < pTiny ^ 1 := by
      norm_num [A, sqMagProb, sqMagProbDen, frobNormSqRect,
        algorithm1SmallEntrySupportMatrix]
    exact
      sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
        (s := 1) (by norm_num) (100 : ℝ) (1 / 30000 : ℝ) hδ_small

/-- No theorem with only the concrete rectangular source-style budget as
premise can imply the advertised literal exact Algorithm 1 success probability
for all inputs at these parameters.

This is a schema-refutation wrapper around the concrete small-entry witness:
the probability law is exact, no floating-point quantity is computed, and the
failure is caused by the literal untruncated squared-magnitude law assigning
positive mass to the tiny entry. -/
theorem not_forall_algorithm1ExactSpectralEvent_of_rect_source_budget_one_div_30000 :
    ¬
      (∀ (A : Fin 1 → Fin 2 → ℝ) (hden : 0 < sqMagProbDen A),
        algorithm1RectSourceBudget_1_2_100_one_div_30000 A →
        1 - (1 / 30000 : ℝ) ≤
          (sqMagTraceProbability (steps := 1) A hden).eventProb
            (algorithm1ExactSpectralEvent 1 A
              (fun samples : ElementwiseTrace 1 2 1 => samples) (100 : ℝ))) := by
  classical
  intro hschema
  let A : Fin 1 → Fin 2 → ℝ :=
    algorithm1SmallEntrySupportMatrix (100 : ℝ)
  have hbudget :
      algorithm1RectSourceBudget_1_2_100_one_div_30000 A := by
    simpa [A] using
      algorithm1SmallEntrySupportMatrix_100_rect_source_budget_one_div_30000
  have hδ_small :
      let pTiny : ℝ := sqMagProb A (0 : Fin 1) (1 : Fin 2)
      (1 / 30000 : ℝ) < pTiny ^ 1 := by
    norm_num [A, sqMagProb, sqMagProbDen, frobNormSqRect,
      algorithm1SmallEntrySupportMatrix]
  have hnot :
      ¬
        (1 - (1 / 30000 : ℝ) ≤
          (sqMagTraceProbability (steps := 1) A
            (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (100 : ℝ))).eventProb
            (algorithm1ExactSpectralEvent 1 A
              (fun samples : ElementwiseTrace 1 2 1 => samples) (100 : ℝ))) := by
    simpa [A] using
      sqMagTraceProbability_not_algorithm1ExactSpectralEvent_all_tiny_smallEntry_of_delta_lt_pow
        (s := 1) (by norm_num) (100 : ℝ) (1 / 30000 : ℝ) hδ_small
  exact hnot
    (hschema A
      (sqMagProbDen_algorithm1SmallEntrySupportMatrix_pos (100 : ℝ))
      hbudget)

/-- Rademacher finite-test tail for fixed Algorithm 1 stepwise copy
differences.

Fix two exact Algorithm 1 traces.  If the quadratic-form coefficients of the
stepwise self-adjoint dilation differences have variance proxy `σ a ^ 2` for
each finite test vector `z a`, then exact Rademacher signs over the step index
satisfy the simultaneous two-sided Hoeffding event.  This is the first
Algorithm-1-specific adapter from copy differences to the generic finite-test
matrix-Khintchine primitive; it is exact-probability and exact-arithmetic only. -/
theorem sqMagTraceProbability_eventProb_forall_abs_finiteQuadraticForm_rademacher_signed_rectSelfAdjointDilation_sampleResidualIncrement_diff_le_ge_one_sub_sum_two_mul_exp_neg_sq_div
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ)
    (samples samples' : ElementwiseTrace m n s)
    (z : ι → Fin m ⊕ Fin n → ℝ) (T σ : ι → ℝ)
    (hT : ∀ a : ι, 0 < T a) (hσ : ∀ a : ι, 0 < σ a)
    (hvar :
      ∀ a : ι,
        (∑ t : Fin s,
          finiteQuadraticForm
            (fun b c : Fin m ⊕ Fin n =>
              rectSelfAdjointDilation
                (fun i j =>
                  elementwiseSampleResidualIncrement s A (samples t) i j -
                    elementwiseSampleResidualIncrement s A (samples' t) i j)
                b c)
            (z a) ^ 2) ≤ σ a ^ 2) :
    1 - (∑ a : ι, 2 * Real.exp (-(T a ^ 2 / (2 * σ a ^ 2)))) ≤
      (rademacherTraceProbability s).eventProb
        {ω | ∀ a : ι,
          |finiteQuadraticForm
            (fun b c : Fin m ⊕ Fin n =>
              ∑ t : Fin s,
                rademacherSignVector ω t *
                  rectSelfAdjointDilation
                    (fun i j =>
                      elementwiseSampleResidualIncrement s A (samples t) i j -
                        elementwiseSampleResidualIncrement s A (samples' t) i j)
                    b c)
            (z a)| ≤ T a} := by
  classical
  simpa using
    rademacherTraceProbability_eventProb_forall_abs_finiteQuadraticForm_signed_matrix_sum_fintype_le_ge_one_sub_sum_two_mul_exp_neg_sq_div
      (m := s) (κ := Fin m ⊕ Fin n) (ι := ι)
      (M := fun t b c =>
        rectSelfAdjointDilation
          (fun i j =>
            elementwiseSampleResidualIncrement s A (samples t) i j -
              elementwiseSampleResidualIncrement s A (samples' t) i j)
          b c)
      (z := z) (T := T) (σ := σ) hT hσ hvar

/-- Cover-to-operator Rademacher tail for fixed Algorithm 1 copy-difference
increments.

This theorem composes the finite-test Rademacher quadratic-form tail with a
supplied finite unit-ball cover of the self-adjoint-dilation space and a coarse
operator radius for each signed dilation sum.  It is exact-law/exact-arithmetic
infrastructure: no sampling probabilities are approximated and no
floating-point computation appears.  The coarse radius is an explicit remaining
deterministic input, so this is not a final source-uniform CACM equation-(2)
spectral theorem. -/
theorem rademacherTraceProbability_eventProb_rectOpNorm2Le_signed_sampleResidualIncrement_diff_ge_one_sub_sum_two_mul_exp_neg_sq_div_of_finiteUnitBallCover
    {m n s : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ)
    (samples samples' : ElementwiseTrace m n s)
    (net : ι → Fin m ⊕ Fin n → ℝ)
    (ρ η L : ℝ) (σ : ι → ℝ)
    (hcover : finiteUnitBallCover net ρ)
    (hη : 0 < η) (hσ : ∀ a : ι, 0 < σ a)
    (hL : 0 ≤ L) (hρ : 0 ≤ ρ)
    (hcoarse :
      ∀ ω : RademacherTrace s,
        finiteOpNorm2Le
          (fun b c : Fin m ⊕ Fin n =>
            ∑ t : Fin s,
              rademacherSignVector ω t *
                rectSelfAdjointDilation
                  (fun i j =>
                    elementwiseSampleResidualIncrement s A (samples t) i j -
                      elementwiseSampleResidualIncrement s A (samples' t) i j)
                  b c)
          L)
    (hvar :
      ∀ a : ι,
        (∑ t : Fin s,
          finiteQuadraticForm
            (fun b c : Fin m ⊕ Fin n =>
              rectSelfAdjointDilation
                (fun i j =>
                  elementwiseSampleResidualIncrement s A (samples t) i j -
                    elementwiseSampleResidualIncrement s A (samples' t) i j)
                b c)
            (net a) ^ 2) ≤ σ a ^ 2) :
    1 - (∑ a : ι, 2 * Real.exp (-(η ^ 2 / (2 * σ a ^ 2)))) ≤
      (rademacherTraceProbability s).eventProb
        {ω | rectOpNorm2Le
          (fun i j =>
            ∑ t : Fin s,
              rademacherSignVector ω t *
                (elementwiseSampleResidualIncrement s A (samples t) i j -
                  elementwiseSampleResidualIncrement s A (samples' t) i j))
          (η + L * (2 * ρ + ρ ^ 2))} := by
  classical
  let P := rademacherTraceProbability s
  let D : RademacherTrace s → Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun ω b c =>
      ∑ t : Fin s,
        rademacherSignVector ω t *
          rectSelfAdjointDilation
            (fun i j =>
              elementwiseSampleResidualIncrement s A (samples t) i j -
                elementwiseSampleResidualIncrement s A (samples' t) i j)
            b c
  let R : RademacherTrace s → Fin m → Fin n → ℝ :=
    fun ω i j =>
      ∑ t : Fin s,
        rademacherSignVector ω t *
          (elementwiseSampleResidualIncrement s A (samples t) i j -
            elementwiseSampleResidualIncrement s A (samples' t) i j)
  let Etest : Set (RademacherTrace s) :=
    {ω | ∀ a : ι, |finiteQuadraticForm (D ω) (net a)| ≤ η}
  let Eop : Set (RademacherTrace s) :=
    {ω | rectOpNorm2Le (R ω) (η + L * (2 * ρ + ρ ^ 2))}
  have htest :
      1 - (∑ a : ι, 2 * Real.exp (-(η ^ 2 / (2 * σ a ^ 2)))) ≤
        P.eventProb Etest := by
    simpa [P, Etest, D] using
      sqMagTraceProbability_eventProb_forall_abs_finiteQuadraticForm_rademacher_signed_rectSelfAdjointDilation_sampleResidualIncrement_diff_le_ge_one_sub_sum_two_mul_exp_neg_sq_div
        (A := A) samples samples' (z := net) (T := fun _a : ι => η)
        (σ := σ) (by intro _; exact hη) hσ hvar
  have hsubset : Etest ⊆ Eop := by
    intro ω hω
    have hnet :
        ∀ a : ι, finiteQuadraticForm (D ω) (net a) ≤ η := by
      intro a
      exact (le_abs_self (finiteQuadraticForm (D ω) (net a))).trans (hω a)
    have hloewner :
        finiteLoewnerLe (D ω)
          (fun b c : Fin m ⊕ Fin n =>
            (η + L * (2 * ρ + ρ ^ 2)) * finiteIdMatrix b c) := by
      exact
        finiteLoewnerLe_of_finite_unit_ball_cover_quadraticForm
          (D ω) net hcover hnet (hcoarse ω) hL hρ
    have hD_eq :
        D ω = rectSelfAdjointDilation (R ω) := by
      ext b c
      cases b <;> cases c <;> simp [D, R, rectSelfAdjointDilation]
    have hC_nonneg : 0 ≤ η + L * (2 * ρ + ρ ^ 2) := by
      have hshape : 0 ≤ 2 * ρ + ρ ^ 2 := by nlinarith [hρ, sq_nonneg ρ]
      exact add_nonneg (le_of_lt hη) (mul_nonneg hL hshape)
    have hloewnerR :
        finiteLoewnerLe (rectSelfAdjointDilation (R ω))
          (fun b c : Fin m ⊕ Fin n =>
            (η + L * (2 * ρ + ρ ^ 2)) * finiteIdMatrix b c) := by
      simpa [hD_eq] using hloewner
    exact
      rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
        (R ω) hC_nonneg hloewnerR
  exact htest.trans (FiniteProbability.eventProb_mono P hsubset)

/-- Event that the exact truncated Algorithm 1 sketch is close to the
    original matrix.  This is the event shape used by the
    Drineas--Zouzias-style source-aligned variant: the sketch is built from
    `elementwiseTruncate tau A`, but the residual is measured against `A`. -/
def algorithm1ExactTruncatedSpectralEvent {Ω : Type*} {m n steps : ℕ}
    (tau : ℝ) (s : ℕ) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (elementwiseTruncatedTraceResidual tau s A (X ω)) ε}

/-- Event that the self-adjoint dilation of the exact Algorithm 1 residual
    satisfies a square vector-action operator bound.  This is the natural
    interface for future matrix Bernstein/Khintchine theorems, which are often
    stated for self-adjoint matrices. -/
def algorithm1ExactDilationEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω | finiteOpNorm2Le
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω))) ε}

/-- Event that the self-adjoint dilation of the exact Algorithm 1 residual is
    one-sided Loewner-bounded by `ε I`.  This is the natural output shape of
    largest-eigenvalue matrix concentration; for self-adjoint dilations it is
    already enough to imply the rectangular residual operator bound. -/
def algorithm1ExactDilationUpperEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω |
    finiteLoewnerLe
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
      (fun a b => ε * finiteIdMatrix a b)}

/-- Scaled eigenvalue event produced by the current trace-MGF tail layer:
    every Hermitian eigenvalue of `theta * D(A - Atilde)` has absolute value
    below `T`.  The deterministic theorem below converts this event into the
    rectangular spectral event at radius `T / theta` when `theta > 0`. -/
noncomputable def algorithm1ScaledDilationAbsEigenvalueEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (theta T : ℝ) : Set Ω :=
  {ω |
    ∀ a : Fin m ⊕ Fin n,
      |finiteHermitianEigenvalues
        (fun b c : Fin m ⊕ Fin n =>
          theta *
            rectSelfAdjointDilation
              (elementwiseTraceResidual s A (X ω)) b c)
        (by
          intro b c
          exact congrArg (fun x => theta * x)
            (rectSelfAdjointDilation_symmetric
              (elementwiseTraceResidual s A (X ω)) b c))
        a| < T}

/-- Eigenvalue form of the one-sided self-adjoint-dilation upper event:
    every Hermitian eigenvalue of `ε I - D(A - Atilde)` is nonnegative.  This
    is only a deterministic restatement of the Loewner event; it is useful as a
    target shape for future largest-eigenvalue concentration work. -/
noncomputable def algorithm1ExactDilationEigenUpperEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω |
    ∀ a : Fin m ⊕ Fin n,
      0 ≤ finiteScalarUpperDiffEigenvalues
        (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
        (rectSelfAdjointDilation_symmetric
          (elementwiseTraceResidual s A (X ω)))
        ε a}

/-- Single-eigenvalue component of the dilation eigenvalue upper event.  A
    union-bound argument over these events gives the full eigenvalue event. -/
noncomputable def algorithm1ExactDilationEigenUpperIndexEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (a : Fin m ⊕ Fin n) : Set Ω :=
  {ω |
    0 ≤ finiteScalarUpperDiffEigenvalues
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A (X ω)))
      ε a}

/-- Event that the square of the self-adjoint dilation of the exact residual
    is Loewner-bounded by `ε^2 I`.  This is a convenient target shape for
    future matrix-concentration/moment arguments; the theorem below converts it
    to the dilation operator event. -/
def algorithm1ExactDilationSquareEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω |
    finiteLoewnerLe
      (finiteMatMul
        (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
        (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω))))
      (fun a b => ε ^ 2 * finiteIdMatrix a b)}

/-- Event that the exact Algorithm 1 residual satisfies a rectangular
    Frobenius-norm bound. This is weaker than the CACM equation (2) spectral
    target as a theorem shape, but it gives a fully deterministic bridge to the
    repository's rectangular vector-action operator event. -/
noncomputable def algorithm1ExactFrobEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (ε : ℝ) :
    Set Ω :=
  {ω | frobNormRect (elementwiseTraceResidual s A (X ω)) ≤ ε}

/-- Event that every entry of the exact Algorithm 1 residual is bounded by
    `τ` in absolute value.  This is a scalar-entry layer used by union-bound
    arguments; it is weaker than a matrix Bernstein/Khintchine spectral event. -/
def algorithm1ExactEntrywiseEvent {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps) (τ : ℝ) :
    Set Ω :=
  {ω | ∀ i j, |elementwiseTraceResidual s A (X ω) i j| ≤ τ}

/-- Event that the floating-point Algorithm 1 residual satisfies the exact
    spectral budget plus the Frobenius norm of an entrywise perturbation
    budget. -/
noncomputable def algorithm1FlSpectralEvent {Ω : Type*} (fp : FPModel)
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (fl_elementwiseTraceResidual fp s A (X ω))
      (ε + frobNormRect B)}

/-- Event that the exact residual using a supplied exact probability table
    satisfies a rectangular operator bound. -/
noncomputable def algorithm1ExactSpectralEventWithProb {Ω : Type*}
    {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (p : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (elementwiseTraceResidualWithProb s A p (X ω)) ε}

/-- Floating-point event for Algorithm 1 when the sampler uses a supplied exact
    probability table. The displayed radius has separate additive budgets for
    changing from the canonical squared-magnitude law to `p` and for
    floating-point arithmetic while using `p` exactly. -/
noncomputable def algorithm1FlSpectralEventWithProb {Ω : Type*}
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (C B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (fl_elementwiseTraceResidualWithProb fp s A p (X ω))
      (ε + frobNormRect C + frobNormRect B)}

/-- Floating-point event for the truncated Algorithm 1 sketch against the
    original matrix. -/
noncomputable def algorithm1FlTruncatedSpectralEvent {Ω : Type*}
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω | rectOpNorm2Le (fl_elementwiseTruncatedTraceResidual fp tau s A (X ω))
      (ε + frobNormRect B)}

/-- Floating-point event for the truncated Algorithm 1 sketch when the sampler
    uses a supplied exact probability table for the
    truncated matrix. -/
noncomputable def algorithm1FlTruncatedSpectralEventWithProb {Ω : Type*}
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (ε : ℝ)
    (C B : Fin m → Fin n → ℝ) : Set Ω :=
  {ω |
    rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidualWithProb fp tau s A p (X ω))
      (ε + frobNormRect C + frobNormRect B)}

-- ============================================================
-- Deterministic floating-point transfer
-- ============================================================

/-- Deterministic transfer for Algorithm 1 spectral residuals.

If the exact residual has rectangular operator-2 bound `ε`, and the computed
sketch differs entrywise from the exact sketch by a nonnegative budget `B`,
then the floating-point residual has rectangular operator-2 bound
`ε + ||B||_F`.

This theorem is intentionally deterministic: the exact high-probability
concentration theorem for CACM equation (2) remains a separate obligation. -/
theorem fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {ε : ℝ} (B : Fin m → Fin n → ℝ)
    (hExact : rectOpNorm2Le (elementwiseTraceResidual s A samples) ε)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
      (ε + frobNormRect B) := by
  let E : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j -
      fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j
  have hE : frobNormRect E ≤ frobNormRect B := by
    apply frobNormRect_le_of_entry_abs_le E B hB_nonneg
    intro i j
    have h := hEntry i j
    simpa [E, abs_sub_comm] using h
  have hsum :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
      (elementwiseTraceResidual s A samples) E hExact hE
  have hres :
      fl_elementwiseTraceResidual fp s A samples =
        fun i j => elementwiseTraceResidual s A samples i j + E i j := by
    ext i j
    unfold fl_elementwiseTraceResidual elementwiseTraceResidual E
    ring
  simpa [hres] using hsum

/-- Deterministic floating-point transfer for Algorithm 1 when the sampler uses
    a supplied exact probability table.

The hypothesis `hProbEntry` is the exact-sketch perturbation caused by using
`p` in the rescaling denominator instead of the ideal squared-magnitude
probability.  The hypothesis `hFlEntry` is the usual floating-point perturbation
while using the supplied exact table `p`. -/
theorem fl_elementwiseTraceResidualWithProb_rectOpNorm2Le_of_ideal
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps)
    {ε : ℝ} (C B : Fin m → Fin n → ℝ)
    (hExact : rectOpNorm2Le (elementwiseTraceResidual s A samples) ε)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hProbEntry : ∀ i j,
      |elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ C i j)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hFlEntry : ∀ i j,
      |fl_elementwiseTraceSketchWithProb fp s A (fun _ _ => 0) p samples i j -
        elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j| ≤
          B i j) :
    rectOpNorm2Le (fl_elementwiseTraceResidualWithProb fp s A p samples)
      (ε + frobNormRect C + frobNormRect B) := by
  let Eprob : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j -
      elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j
  have hEprob : frobNormRect Eprob ≤ frobNormRect C := by
    apply frobNormRect_le_of_entry_abs_le Eprob C hC_nonneg
    intro i j
    have h := hProbEntry i j
    simpa [Eprob, abs_sub_comm] using h
  have hExactComputed :
      rectOpNorm2Le (elementwiseTraceResidualWithProb s A p samples)
        (ε + frobNormRect C) := by
    have hsum :=
      rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
        (elementwiseTraceResidual s A samples) Eprob hExact hEprob
    have hres :
        elementwiseTraceResidualWithProb s A p samples =
          fun i j => elementwiseTraceResidual s A samples i j + Eprob i j := by
      ext i j
      unfold elementwiseTraceResidualWithProb elementwiseTraceResidual Eprob
      ring
    simpa [hres] using hsum
  let Efp : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketchWithProb s A (fun _ _ => 0) p samples i j -
      fl_elementwiseTraceSketchWithProb fp s A (fun _ _ => 0) p samples i j
  have hEfp : frobNormRect Efp ≤ frobNormRect B := by
    apply frobNormRect_le_of_entry_abs_le Efp B hB_nonneg
    intro i j
    have h := hFlEntry i j
    simpa [Efp, abs_sub_comm] using h
  have hsum :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le
      (elementwiseTraceResidualWithProb s A p samples) Efp
      hExactComputed hEfp
  have hres :
      fl_elementwiseTraceResidualWithProb fp s A p samples =
        fun i j => elementwiseTraceResidualWithProb s A p samples i j + Efp i j := by
    ext i j
    unfold fl_elementwiseTraceResidualWithProb elementwiseTraceResidualWithProb Efp
    ring
  simpa [hres, add_assoc] using hsum

/-- Floating-point version of the truncated transfer.  The sampled residual
    for the truncated matrix is first transferred through the existing
    Algorithm 1 floating-point perturbation theorem, and then the deterministic
    truncation error is added back. -/
theorem fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {beta alpha : ℝ} (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s (elementwiseTruncate tau A) samples)
        beta)
    (hPoint :
      ∀ i j,
        |fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
            (fun _ _ => 0) samples i j -
          elementwiseTraceSketch s (elementwiseTruncate tau A)
            (fun _ _ => 0) samples i j| ≤ B i j)
    (hTrunc :
      frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j) ≤ alpha) :
    rectOpNorm2Le (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
      (beta + frobNormRect B + alpha) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hFl :
      rectOpNorm2Le (fl_elementwiseTraceResidual fp s Ahat samples)
        (beta + frobNormRect B) :=
    fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
      fp s Ahat samples B hSample hB_nonneg hPoint
  let M : Fin m → Fin n → ℝ := fl_elementwiseTraceResidual fp s Ahat samples
  let E : Fin m → Fin n → ℝ := fun i j => A i j - Ahat i j
  have hsum :
      rectOpNorm2Le (fun i j => M i j + E i j)
        ((beta + frobNormRect B) + alpha) :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le M E hFl hTrunc
  have hmain :
      rectOpNorm2Le (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
        ((beta + frobNormRect B) + alpha) := by
    convert hsum using 1
    ext i j
    simp [fl_elementwiseTruncatedTraceResidual, fl_elementwiseTraceResidual,
      Ahat, M, E]
  exact hmain

/-- Truncated floating-point transfer for Algorithm 1 when the sampler uses a
    supplied exact probability table for the truncated matrix. The radius
    separates truncation error, exact-sketch perturbation from changing the
    exact law, and floating-point arithmetic while using that law. -/
theorem fl_elementwiseTruncatedTraceResidualWithProb_rectOpNorm2Le_of_ideal
    (fp : FPModel) {m n steps : ℕ} (tau : ℝ) (s : ℕ)
    (A : Fin m → Fin n → ℝ) (p : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps)
    {beta alpha : ℝ} (C B : Fin m → Fin n → ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hSample :
      rectOpNorm2Le
        (elementwiseTraceResidual s (elementwiseTruncate tau A) samples)
        beta)
    (hProbEntry :
      ∀ i j,
        |elementwiseTraceSketchWithProb s (elementwiseTruncate tau A)
            (fun _ _ => 0) p samples i j -
          elementwiseTraceSketch s (elementwiseTruncate tau A)
            (fun _ _ => 0) samples i j| ≤ C i j)
    (hFlEntry :
      ∀ i j,
        |fl_elementwiseTraceSketchWithProb fp s (elementwiseTruncate tau A)
            (fun _ _ => 0) p samples i j -
          elementwiseTraceSketchWithProb s (elementwiseTruncate tau A)
            (fun _ _ => 0) p samples i j| ≤ B i j)
    (hTrunc :
      frobNormRect
        (fun i j => A i j - elementwiseTruncate tau A i j) ≤ alpha) :
    rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidualWithProb fp tau s A p samples)
      (beta + frobNormRect C + frobNormRect B + alpha) := by
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  have hFl :
      rectOpNorm2Le (fl_elementwiseTraceResidualWithProb fp s Ahat p samples)
        (beta + frobNormRect C + frobNormRect B) :=
    fl_elementwiseTraceResidualWithProb_rectOpNorm2Le_of_ideal
      fp s Ahat p samples C B hSample hC_nonneg
      (by simpa [Ahat] using hProbEntry) hB_nonneg
      (by simpa [Ahat] using hFlEntry)
  let M : Fin m → Fin n → ℝ :=
    fl_elementwiseTraceResidualWithProb fp s Ahat p samples
  let E : Fin m → Fin n → ℝ := fun i j => A i j - Ahat i j
  have hsum :
      rectOpNorm2Le (fun i j => M i j + E i j)
        ((beta + frobNormRect C + frobNormRect B) + alpha) :=
    rectOpNorm2Le_add_of_rectOpNorm2Le_of_frobNormRect_le M E hFl hTrunc
  have hmain :
      rectOpNorm2Le
        (fl_elementwiseTruncatedTraceResidualWithProb fp tau s A p samples)
        ((beta + frobNormRect C + frobNormRect B) + alpha) := by
    convert hsum using 1
    ext i j
    simp [fl_elementwiseTruncatedTraceResidualWithProb,
      fl_elementwiseTraceResidualWithProb, Ahat, M, E]
  simpa [add_assoc] using hmain

/-- For the source-aligned square truncated variant, a half-budget spectral
    residual event for the truncated matrix implies an `eps`-budget residual
    event against the original matrix. -/
theorem algorithm1ExactSpectralEvent_truncated_half_subset_original
    {Ω : Type*} {n steps : ℕ} (s : ℕ) (A : Fin n → Fin n → ℝ)
    (X : Ω → ElementwiseTrace n n steps) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2) ⊆
      algorithm1ExactTruncatedSpectralEvent (eps / (2 * (n : ℝ))) s A X eps := by
  intro ω h
  exact elementwiseTruncatedTraceResidual_square_rectOpNorm2Le_of_half
    s A (X ω) heps hn h

/-- Probability transfer for the source-aligned square truncated variant.  This
    does not prove the matrix-Bernstein residual event for the truncated matrix;
    it records the deterministic truncation step needed once that event is
    proved. -/
theorem probability_algorithm1_exact_truncated_spectral_of_sampled_half
    {Ω : Type*} [Fintype Ω] {n steps : ℕ} (s : ℕ)
    (A : Fin n → Fin n → ℝ) (X : Ω → ElementwiseTrace n n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1ExactTruncatedSpectralEvent
        (eps / (2 * (n : ℝ))) s A X eps) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_half_subset_original
        s A X heps hn))

/-- Floating-point event transfer for the source-aligned square truncated
    variant.  A half-budget exact event for the truncated matrix transfers to
    an `eps + ||B||_F` floating-point event against the original matrix, provided
    the rounded truncated sketch has the advertised entrywise perturbation
    budget. -/
theorem algorithm1ExactSpectralEvent_truncated_half_subset_fl_original
    (fp : FPModel) {Ω : Type*} {n steps : ℕ} (s : ℕ)
    (A : Fin n → Fin n → ℝ) (X : Ω → ElementwiseTrace n n steps)
    {eps : ℝ} (B : Fin n → Fin n → ℝ)
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2) ⊆
      algorithm1FlTruncatedSpectralEvent fp (eps / (2 * (n : ℝ))) s A X eps B := by
  intro ω h
  have hTruncFrob :
      frobNormRect
        (fun i j =>
          A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_square_error_frobNormRect_le_half A heps hn
  have hfl :=
    fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      fp (eps / (2 * (n : ℝ))) s A (X ω) B hB_nonneg h (hPoint ω) hTruncFrob
  change rectOpNorm2Le
    (fl_elementwiseTruncatedTraceResidual fp (eps / (2 * (n : ℝ))) s A (X ω))
    (eps + frobNormRect B)
  convert hfl using 1
  ring

/-- Probability transfer to the floating-point source-aligned truncated event. -/
theorem probability_algorithm1_fl_truncated_spectral_of_sampled_half
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {n steps : ℕ} (s : ℕ)
    (A : Fin n → Fin n → ℝ) (X : Ω → ElementwiseTrace n n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (B : Fin n → Fin n → ℝ)
    (heps : 0 ≤ eps) (hn : 0 < n)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate (eps / (2 * (n : ℝ))) A) X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1FlTruncatedSpectralEvent fp
        (eps / (2 * (n : ℝ))) s A X eps B) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_half_subset_fl_original
        fp s A X B heps hn hB_nonneg hPoint))

/-- Rectangular half-budget truncation transfer for Algorithm 1.

If the sampled residual of `elementwiseTruncate (eps/(2*sqrt(mn))) A` is
bounded by `eps/2`, then the exact truncated residual against `A` is bounded
by `eps`. -/
theorem algorithm1ExactSpectralEvent_truncated_rect_half_subset_original
    {Ω : Type*} {m n steps : ℕ} (s : ℕ) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ)) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
        X (eps / 2) ⊆
      algorithm1ExactTruncatedSpectralEvent
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps := by
  intro ω h
  have hTrunc :
      frobNormRect
        (fun i j =>
          A i j -
            elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_rect_error_frobNormRect_le_half A heps hmn
  have hmain :=
    elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω)
      (beta := eps / 2) (alpha := eps / 2) h hTrunc
  change rectOpNorm2Le
    (elementwiseTruncatedTraceResidual
      (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω)) eps
  convert hmain using 1
  ring

/-- Probability transfer for the rectangular source-aligned truncated variant. -/
theorem probability_algorithm1_exact_truncated_rect_spectral_of_sampled_half
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
          X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1ExactTruncatedSpectralEvent
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_rect_half_subset_original
        s A X heps hmn))

/-- Rectangular floating-point half-budget truncation transfer for Algorithm 1.

The exact sampled residual event at radius `eps/2` transfers to the rounded
truncated residual event at radius `eps + ||B||_F`, provided the rounded sketch
has the advertised entrywise perturbation budget. -/
theorem algorithm1ExactSpectralEvent_truncated_rect_half_subset_fl_original
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    {eps : ℝ} (B : Fin m → Fin n → ℝ)
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j) :
    algorithm1ExactSpectralEvent s
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
        X (eps / 2) ⊆
      algorithm1FlTruncatedSpectralEvent fp
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps B := by
  intro ω h
  have hTrunc :
      frobNormRect
        (fun i j =>
          A i j -
            elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
        eps / 2 :=
    elementwiseTruncate_rect_error_frobNormRect_le_half A heps hmn
  have hfl :=
    fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
      fp (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω)
      (beta := eps / 2) (alpha := eps / 2)
      B hB_nonneg h (hPoint ω) hTrunc
  change rectOpNorm2Le
    (fl_elementwiseTruncatedTraceResidual fp
      (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A (X ω))
    (eps + frobNormRect B)
  convert hfl using 1
  ring

/-- Probability transfer to the rectangular floating-point source-aligned
truncated event. -/
theorem probability_algorithm1_fl_truncated_rect_spectral_of_sampled_half
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ : ℝ) {eps : ℝ}
    (B : Fin m → Fin n → ℝ)
    (heps : 0 ≤ eps) (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ ω i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j -
          elementwiseTraceSketch s
            (elementwiseTruncate
              (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
            (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hProb :
      ρ ≤ Pr.eventProb
        (algorithm1ExactSpectralEvent s
          (elementwiseTruncate
            (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A)
          X (eps / 2))) :
    ρ ≤ Pr.eventProb
      (algorithm1FlTruncatedSpectralEvent fp
        (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) s A X eps B) := by
  exact hProb.trans
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_truncated_rect_half_subset_fl_original
        fp s A X B heps hmn hB_nonneg hPoint))

/-- Fixed-vector deterministic floating-point transfer for Algorithm 1
residuals.  This is the vector version of the spectral transfer above: an
exact bound for one vector `x` transfers to the rounded residual with the
Frobenius norm of the entrywise perturbation budget multiplied by `||x||₂`. -/
theorem fl_elementwiseTraceResidual_vecNorm2_le_of_exact_fixed_vector
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (x : Fin n → ℝ) {η : ℝ} (B : Fin m → Fin n → ℝ)
    (hExact :
      vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤ η)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    vecNorm2 (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x) ≤
      η + frobNormRect B * vecNorm2 x := by
  let E : Fin m → Fin n → ℝ := fun i j =>
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j -
      fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j
  have hE : frobNormRect E ≤ frobNormRect B := by
    apply frobNormRect_le_of_entry_abs_le E B hB_nonneg
    intro i j
    have h := hEntry i j
    simpa [E, abs_sub_comm] using h
  have hres :
      fl_elementwiseTraceResidual fp s A samples =
        fun i j => elementwiseTraceResidual s A samples i j + E i j := by
    ext i j
    unfold fl_elementwiseTraceResidual elementwiseTraceResidual E
    ring
  have hsplit :
      rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x =
        fun i =>
          rectMatMulVec (elementwiseTraceResidual s A samples) x i +
            rectMatMulVec E x i := by
    rw [hres]
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  calc
    vecNorm2
      (fun i =>
        rectMatMulVec (elementwiseTraceResidual s A samples) x i +
          rectMatMulVec E x i)
        ≤ vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x) +
            vecNorm2 (rectMatMulVec E x) :=
          vecNorm2_add_le _ _
    _ ≤ η + frobNormRect E * vecNorm2 x := by
          exact add_le_add hExact (vecNorm2_rectMatMulVec_le_frobNormRect_mul E x)
    _ ≤ η + frobNormRect B * vecNorm2 x := by
          exact add_le_add (le_refl η)
            (mul_le_mul_of_nonneg_right hE (vecNorm2_nonneg x))

/-- Algorithm 1 spectral FP transfer with the existing squared-magnitude
    hit-count stability budget.  This is useful only after an exact spectral
    theorem has supplied `hExact`; it does not prove CACM equation (2) by
    itself. -/
theorem fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact_and_hitCount_le
    (fp : FPModel) {m n steps : ℕ} (s Q : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    {ε : ℝ}
    (hExact : rectOpNorm2Le (elementwiseTraceResidual s A samples) ε)
    (hs : (s : ℝ) ≠ 0)
    (hA_ne : ∀ i j, A i j ≠ 0)
    (hcount : ∀ i j, hitCount samples i j ≤ Q)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1)) :
    rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
      (ε + frobNormRect
        (fun i j => sqMagTraceErrorBudget fp Q s A (fun _ _ => 0) i j)) := by
  apply fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
      fp s A samples (fun i j =>
        sqMagTraceErrorBudget fp Q s A (fun _ _ => 0) i j)
      hExact
  · intro i j
    unfold sqMagTraceErrorBudget
    have hQnonneg : 0 ≤ (Q : ℝ) := by exact_mod_cast Nat.zero_le Q
    have hgammaQ : 0 ≤ gamma fp Q := gamma_nonneg fp hQ
    have hgamma : 0 ≤ gamma fp (Q + 1) := gamma_nonneg fp hQ1
    exact add_nonneg
      (mul_nonneg
        (abs_nonneg ((fun _ _ => 0 : Fin m → Fin n → ℝ) i j))
        hgammaQ)
      (mul_nonneg
        (mul_nonneg hQnonneg
          (abs_nonneg (frobNormSqRect A / ((s : ℝ) * A i j))))
        hgamma)
  · intro i j
    have h :=
      fl_elementwiseTraceSketch_sqMag_error_bound_of_hitCount_le fp
        s A (fun _ _ => 0) samples i j Q hs (hA_ne i j)
        (hcount i j) hQ hQ1
    rw [← elementwiseTraceSketch_sqMag_eq
      s A (fun _ _ => 0) samples i j hs (hA_ne i j)] at h
    simpa using h

-- ============================================================
-- Exact Frobenius residual concentration under the product trace law
-- ============================================================

/-- Under the canonical independent squared-magnitude trace law, each exact
    Algorithm 1 residual entry has second moment at most
    `||A||_F^2 / s`.

This is a Frobenius-level scalar consequence of the product trace law; it is
not the matrix Bernstein/Khintchine spectral theorem from CACM equation (2). -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_sq_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples => elementwiseTraceResidual s A samples i j ^ 2) ≤
      frobNormSqRect A / (s : ℝ) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  by_cases hAij_zero : A i j = 0
  · have hpoint : ∀ samples : ElementwiseTrace m n s,
        elementwiseTraceResidual s A samples i j = 0 := by
      intro samples
      unfold elementwiseTraceResidual
      rw [elementwiseTraceSketch_zero_init_of_entry_eq_zero
        s A samples i j hAij_zero]
      rw [hAij_zero]
      ring
    have hzero :
        P.expectationReal
          (fun samples : ElementwiseTrace m n s =>
            elementwiseTraceResidual s A samples i j ^ 2) = 0 := by
      unfold FiniteProbability.expectationReal
      simp [hpoint]
    rw [hzero]
    exact div_nonneg (frobNormSqRect_nonneg A) (le_of_lt hs)
  · let p : ℝ := sqMagProb A i j
    let c : ℝ := frobNormSqRect A / ((s : ℝ) * A i j)
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs
    have hF_ne : frobNormSqRect A ≠ 0 := by
      simpa [sqMagProbDen] using hden.ne'
    have hAeq : A i j = ((s : ℝ) * p) * c := by
      unfold p c sqMagProb sqMagProbDen
      field_simp [hs_ne, hAij_zero, hF_ne]
    have hres : ∀ samples : ElementwiseTrace m n s,
        elementwiseTraceResidual s A samples i j =
          ((s : ℝ) * p - (hitCount samples i j : ℝ)) * c := by
      intro samples
      unfold elementwiseTraceResidual
      rw [elementwiseTraceSketch_sqMag_eq
        s A (fun _ _ => 0) samples i j hs_ne hAij_zero]
      simp only [zero_add]
      change A i j - (hitCount samples i j : ℝ) * c =
        ((s : ℝ) * p - (hitCount samples i j : ℝ)) * c
      rw [hAeq]
      ring
    have hsq : ∀ samples : ElementwiseTrace m n s,
        elementwiseTraceResidual s A samples i j ^ 2 =
          ((hitCount samples i j : ℝ) - (s : ℝ) * p) ^ 2 * c ^ 2 := by
      intro samples
      rw [hres samples]
      ring
    have hE :
        P.expectationReal
          (fun samples : ElementwiseTrace m n s =>
            elementwiseTraceResidual s A samples i j ^ 2) =
          hitCountPairwiseCenteredMoment s p * c ^ 2 := by
      calc
        P.expectationReal
          (fun samples : ElementwiseTrace m n s =>
            elementwiseTraceResidual s A samples i j ^ 2)
            = P.expectationReal
                (fun samples : ElementwiseTrace m n s =>
                  ((hitCount samples i j : ℝ) - (s : ℝ) * p) ^ 2 * c ^ 2) := by
                unfold FiniteProbability.expectationReal
                apply Finset.sum_congr rfl
                intro samples _
                simp [hsq samples]
        _ = P.expectationReal
              (fun samples : ElementwiseTrace m n s =>
                ((hitCount samples i j : ℝ) - (s : ℝ) * p) ^ 2) *
              c ^ 2 := by
                rw [FiniteProbability.expectationReal_mul_const]
        _ = hitCountPairwiseCenteredMoment s p * c ^ 2 := by
                have hmarginal : ∀ t : Fin s,
                    P.eventProb {samples | sampleHits samples t i j} = p := by
                  intro t
                  simpa [P, p] using
                    sqMagTraceProbability_eventProb_sampleHits A hden t i j
                have hpairwise : ∀ t u : Fin s, t ≠ u →
                    P.eventProb
                      {samples | sampleHits samples t i j ∧
                        sampleHits samples u i j} = p * p := by
                  intro t u htu
                  simpa [P, p] using
                    sqMagTraceProbability_eventProb_sampleHits_pair_ne
                      A hden t u htu i j
                rw [expectationReal_hitCount_centered_sq_eq_pairwise
                  P (fun samples : ElementwiseTrace m n s => samples)
                  i j p hmarginal hpairwise]
    rw [hE]
    have hp_nonneg : 0 ≤ p := by
      simpa [p] using sqMagProb_nonneg A hden i j
    have hmoment :=
      hitCountPairwiseCenteredMoment_le_steps_mul s p hp_nonneg
    have hmul :
        hitCountPairwiseCenteredMoment s p * c ^ 2 ≤
          ((s : ℝ) * p) * c ^ 2 :=
      mul_le_mul_of_nonneg_right hmoment (sq_nonneg c)
    have hscale : ((s : ℝ) * p) * c ^ 2 =
        frobNormSqRect A / (s : ℝ) := by
      unfold p c sqMagProb sqMagProbDen
      field_simp [hs_ne, hAij_zero, hF_ne]
    exact hmul.trans_eq hscale

/-- Entrywise high-probability residual bound for Algorithm 1, obtained by
    applying Markov to the scalar second moment of one residual entry. -/
theorem sqMagTraceProbability_eventProb_elementwiseTraceResidual_entry_abs_le_ge_one_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (τ : ℝ) (hτ : 0 < τ) (i : Fin m) (j : Fin n) :
    1 - (frobNormSqRect A / (s : ℝ)) / τ ^ 2 ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          |elementwiseTraceResidual s A samples i j| ≤ τ} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let Z : ElementwiseTrace m n s → ℝ := fun samples =>
    |elementwiseTraceResidual s A samples i j|
  have hprob :=
    FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
      P Z τ (fun samples => abs_nonneg _) hτ
  have hsecond :
      P.expectationReal (fun samples => Z samples ^ 2) ≤
        frobNormSqRect A / (s : ℝ) := by
    have h :=
      sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_sq_le
        A hden hs i j
    have hZsq :
        P.expectationReal (fun samples => Z samples ^ 2) =
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              elementwiseTraceResidual s A samples i j ^ 2) := by
      unfold Z
      congr 1
      ext samples
      exact sq_abs (elementwiseTraceResidual s A samples i j)
    simpa [P, hZsq] using h
  have hdiv :
      P.expectationReal (fun samples => Z samples ^ 2) / τ ^ 2 ≤
        (frobNormSqRect A / (s : ℝ)) / τ ^ 2 :=
    div_le_div_of_nonneg_right hsecond (sq_nonneg τ)
  calc
    1 - (frobNormSqRect A / (s : ℝ)) / τ ^ 2
        ≤ 1 - P.expectationReal (fun samples => Z samples ^ 2) / τ ^ 2 := by
            linarith
    _ ≤ P.eventProb {samples : ElementwiseTrace m n s | Z samples ≤ τ} := hprob
    _ = P.eventProb
        {samples : ElementwiseTrace m n s |
          |elementwiseTraceResidual s A samples i j| ≤ τ} := by
            rfl

/-- Simultaneous entrywise Algorithm 1 residual bound from the scalar Markov
    entry bound and the finite union bound.

This is a genuine high-probability theorem under the canonical product trace
law, but it is an entrywise/union-bound route and is much weaker than the CACM
equation (2) matrix Bernstein/Khintchine spectral concentration result. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactEntrywiseEvent_ge_one_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (τ : ℝ) (hτ : 0 < τ) :
    1 - (((m * n : ℕ) : ℝ) *
        ((frobNormSqRect A / (s : ℝ)) / τ ^ 2)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactEntrywiseEvent s A
          (fun samples : ElementwiseTrace m n s => samples) τ) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let δ : ℝ := (frobNormSqRect A / (s : ℝ)) / τ ^ 2
  let E : Fin m × Fin n → Set (ElementwiseTrace m n s) := fun ij =>
    {samples : ElementwiseTrace m n s |
      |elementwiseTraceResidual s A samples ij.1 ij.2| ≤ τ}
  have hEach : ∀ ij : Fin m × Fin n, 1 - δ ≤ P.eventProb (E ij) := by
    intro ij
    simpa [P, E, δ] using
      sqMagTraceProbability_eventProb_elementwiseTraceResidual_entry_abs_le_ge_one_sub
        A hden hs τ hτ ij.1 ij.2
  have hAll :=
    FiniteProbability.eventProb_forall_ge_one_sub_sum
      P E (fun _ : Fin m × Fin n => δ) hEach
  have hset :
      {samples : ElementwiseTrace m n s |
        ∀ ij : Fin m × Fin n, samples ∈ E ij} =
        algorithm1ExactEntrywiseEvent s A
          (fun samples : ElementwiseTrace m n s => samples) τ := by
    ext samples
    constructor
    · intro h i j
      exact h (i, j)
    · intro h ij
      exact h ij.1 ij.2
  have hsum :
      (∑ _ij : Fin m × Fin n, δ) =
        (((m * n : ℕ) : ℝ) * δ) := by
    simp [δ, Finset.sum_const, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_mul]
  simpa [hset, hsum, δ] using hAll

/-- Squared-Frobenius second-moment bound for the exact Algorithm 1 residual
    under the canonical independent squared-magnitude trace law. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ)) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples => frobNormSqRect (elementwiseTraceResidual s A samples)) ≤
      (m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ)) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        frobNormSqRect (elementwiseTraceResidual s A samples))
        = ∑ i : Fin m, ∑ j : Fin n,
            P.expectationReal
              (fun samples : ElementwiseTrace m n s =>
                elementwiseTraceResidual s A samples i j ^ 2) := by
            unfold frobNormSqRect
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [FiniteProbability.expectationReal_sum]
    _ ≤ ∑ i : Fin m, ∑ j : Fin n, frobNormSqRect A / (s : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            apply Finset.sum_le_sum
            intro j _
            exact
              sqMagTraceProbability_expectationReal_elementwiseTraceResidual_entry_sq_le
                A hden hs i j
    _ = (m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ)) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            ring

/-- Squared vector-action second-moment bound for the exact Algorithm 1
    residual under the canonical independent squared-magnitude trace law. -/
theorem sqMagTraceProbability_expectationReal_vecNorm2Sq_rectMatMulVec_elementwiseTraceResidual_le
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin n → ℝ) :
    (sqMagTraceProbability (steps := s) A hden).expectationReal
      (fun samples =>
        vecNorm2Sq (rectMatMulVec (elementwiseTraceResidual s A samples) x)) ≤
      ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
        vecNorm2Sq x := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hpoint : ∀ samples : ElementwiseTrace m n s,
      vecNorm2Sq (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤
        frobNormSqRect (elementwiseTraceResidual s A samples) *
          vecNorm2Sq x := by
    intro samples
    exact vecNorm2Sq_rectMatMulVec_le_frobNormSqRect_mul
      (elementwiseTraceResidual s A samples) x
  have hmono := FiniteProbability.expectationReal_mono P hpoint
  have hfrob :=
    sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le
      A hden hs
  have hx_nonneg : 0 ≤ vecNorm2Sq x := vecNorm2Sq_nonneg x
  calc
    P.expectationReal
      (fun samples : ElementwiseTrace m n s =>
        vecNorm2Sq (rectMatMulVec (elementwiseTraceResidual s A samples) x))
        ≤ P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              frobNormSqRect (elementwiseTraceResidual s A samples) *
                vecNorm2Sq x) := hmono
    _ = P.expectationReal
          (fun samples : ElementwiseTrace m n s =>
            frobNormSqRect (elementwiseTraceResidual s A samples)) *
          vecNorm2Sq x := by
            rw [FiniteProbability.expectationReal_mul_const]
    _ ≤ ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq x :=
            mul_le_mul_of_nonneg_right hfrob hx_nonneg

/-- Fixed-vector high-probability residual bound for exact Algorithm 1,
    obtained by applying Markov to the vector-action second moment.  This is a
    one-vector support theorem; it is not the uniform spectral-norm
    concentration theorem in CACM equation (2). -/
theorem sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin n → ℝ) (η : ℝ) (hη : 0 < η) :
    1 -
      (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
        vecNorm2Sq x) / η ^ 2 ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          vecNorm2
            (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤ η} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let Z : ElementwiseTrace m n s → ℝ := fun samples =>
    vecNorm2 (rectMatMulVec (elementwiseTraceResidual s A samples) x)
  have hZ : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact vecNorm2_nonneg _
  have hprob :=
    FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
      P Z η hZ hη
  have hsecond :
      P.expectationReal (fun samples => Z samples ^ 2) ≤
        ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq x := by
    have h :=
      sqMagTraceProbability_expectationReal_vecNorm2Sq_rectMatMulVec_elementwiseTraceResidual_le
        A hden hs x
    have hZsq :
        P.expectationReal (fun samples => Z samples ^ 2) =
          P.expectationReal
            (fun samples : ElementwiseTrace m n s =>
              vecNorm2Sq
                (rectMatMulVec (elementwiseTraceResidual s A samples) x)) := by
      unfold Z
      congr 1
      ext samples
      exact vecNorm2_sq _
    simpa [P, hZsq] using h
  have hdiv :
      P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 ≤
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq x) / η ^ 2 :=
    div_le_div_of_nonneg_right hsecond (sq_nonneg η)
  calc
    1 -
      (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
        vecNorm2Sq x) / η ^ 2
        ≤ 1 - P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 := by
            linarith
    _ ≤ P.eventProb {samples | Z samples ≤ η} := hprob
    _ = P.eventProb
        {samples : ElementwiseTrace m n s |
          vecNorm2
            (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤ η} := by
            rfl

/-- Fixed-vector high-probability residual bound for floating-point Algorithm
    1, obtained by composing the exact fixed-vector Markov theorem with the
    entrywise floating-point perturbation budget.  This remains a fixed-vector
    theorem, not the uniform spectral-norm concentration theorem. -/
theorem sqMagTraceProbability_eventProb_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : Fin n → ℝ) (η : ℝ) (hη : 0 < η)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ samples : ElementwiseTrace m n s, ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    1 -
      (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
        vecNorm2Sq x) / η ^ 2 ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          vecNorm2
            (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x) ≤
              η + frobNormRect B * vecNorm2 x} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  have hExactProb :=
    sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
      A hden hs x η hη
  have hsubset :
      {samples : ElementwiseTrace m n s |
        vecNorm2
          (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤ η} ⊆
      {samples : ElementwiseTrace m n s |
        vecNorm2
          (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x) ≤
            η + frobNormRect B * vecNorm2 x} := by
    intro samples hsamples
    exact
      fl_elementwiseTraceResidual_vecNorm2_le_of_exact_fixed_vector
        fp s A samples x B hsamples hB_nonneg (hEntry samples)
  have hmono : P.eventProb
      {samples : ElementwiseTrace m n s |
        vecNorm2
          (rectMatMulVec (elementwiseTraceResidual s A samples) x) ≤ η} ≤
      P.eventProb
      {samples : ElementwiseTrace m n s |
        vecNorm2
          (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) x) ≤
            η + frobNormRect B * vecNorm2 x} :=
    FiniteProbability.eventProb_mono P hsubset
  exact hExactProb.trans hmono

/-- Finite-test-set version of the exact fixed-vector residual Markov bound.
    This is useful for future net arguments, but it does not by itself provide
    a covering net or a uniform spectral-norm theorem. -/
theorem sqMagTraceProbability_eventProb_forall_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : ι → Fin n → ℝ) (η : ι → ℝ) (hη : ∀ a, 0 < η a) :
    1 -
      (∑ a : ι,
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq (x a)) / (η a) ^ 2) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          ∀ a : ι,
            vecNorm2
              (rectMatMulVec (elementwiseTraceResidual s A samples) (x a)) ≤
                η a} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let δ : ι → ℝ := fun a =>
    (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
      vecNorm2Sq (x a)) / (η a) ^ 2
  let E : ι → Set (ElementwiseTrace m n s) := fun a =>
    {samples : ElementwiseTrace m n s |
      vecNorm2
        (rectMatMulVec (elementwiseTraceResidual s A samples) (x a)) ≤
          η a}
  have hEach : ∀ a : ι, 1 - δ a ≤ P.eventProb (E a) := by
    intro a
    simpa [P, E, δ] using
      sqMagTraceProbability_eventProb_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
        A hden hs (x a) (η a) (hη a)
  have hAll := FiniteProbability.eventProb_forall_ge_one_sub_sum
    P E δ hEach
  have hset :
      {samples : ElementwiseTrace m n s | ∀ a : ι, samples ∈ E a} =
        {samples : ElementwiseTrace m n s |
          ∀ a : ι,
            vecNorm2
              (rectMatMulVec (elementwiseTraceResidual s A samples) (x a)) ≤
                η a} := by
    rfl
  simpa [P, E, δ, hset] using hAll

/-- Finite-test-set version of the floating-point fixed-vector residual
    Markov bound.  It composes the exact finite-vector probability argument
    with the entrywise floating-point perturbation budget for every outcome. -/
theorem sqMagTraceProbability_eventProb_forall_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum
    (fp : FPModel) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (x : ι → Fin n → ℝ) (η : ι → ℝ) (hη : ∀ a, 0 < η a)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ samples : ElementwiseTrace m n s, ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    1 -
      (∑ a : ι,
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq (x a)) / (η a) ^ 2) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          ∀ a : ι,
            vecNorm2
              (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) (x a)) ≤
                η a + frobNormRect B * vecNorm2 (x a)} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let δ : ι → ℝ := fun a =>
    (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
      vecNorm2Sq (x a)) / (η a) ^ 2
  let E : ι → Set (ElementwiseTrace m n s) := fun a =>
    {samples : ElementwiseTrace m n s |
      vecNorm2
        (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) (x a)) ≤
          η a + frobNormRect B * vecNorm2 (x a)}
  have hEach : ∀ a : ι, 1 - δ a ≤ P.eventProb (E a) := by
    intro a
    simpa [P, E, δ] using
      sqMagTraceProbability_eventProb_fl_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub
        fp A hden hs (x a) (η a) (hη a) B hB_nonneg hEntry
  have hAll := FiniteProbability.eventProb_forall_ge_one_sub_sum
    P E δ hEach
  have hset :
      {samples : ElementwiseTrace m n s | ∀ a : ι, samples ∈ E a} =
        {samples : ElementwiseTrace m n s |
          ∀ a : ι,
            vecNorm2
              (rectMatMulVec (fl_elementwiseTraceResidual fp s A samples) (x a)) ≤
                η a + frobNormRect B * vecNorm2 (x a)} := by
    rfl
  simpa [P, E, δ, hset] using hAll

/-- High-probability Frobenius residual bound for exact Algorithm 1 under the
    canonical squared-magnitude product trace law.

The bound is a Markov consequence of the Frobenius second moment. It is weaker
than the CACM equation (2) spectral concentration theorem, but it is
nonconditional and can feed the Frobenius-to-operator bridge below. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactFrobEvent_ge_one_sub
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) :
    1 -
      ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2 ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactFrobEvent s A
          (fun samples : ElementwiseTrace m n s => samples) η) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let Z : ElementwiseTrace m n s → ℝ := fun samples =>
    frobNormRect (elementwiseTraceResidual s A samples)
  have hZ : ∀ samples, 0 ≤ Z samples := by
    intro samples
    exact frobNormRect_nonneg _
  have hprob :=
    FiniteProbability.eventProb_le_ge_one_sub_expectationReal_sq_div
      P Z η hZ hη
  have hsecond :
      P.expectationReal (fun samples => Z samples ^ 2) ≤
        (m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ)) := by
    have h :=
      sqMagTraceProbability_expectationReal_elementwiseTraceResidual_frob_sq_le
        A hden hs
    have hZsq :
        P.expectationReal (fun samples => Z samples ^ 2) =
          P.expectationReal
            (fun samples =>
              frobNormSqRect (elementwiseTraceResidual s A samples)) := by
      unfold Z
      congr 1
      ext samples
      exact frobNormRect_sq _
    simpa [P, hZsq] using h
  have hdiv :
      P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 ≤
        ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2 :=
    div_le_div_of_nonneg_right hsecond (sq_nonneg η)
  calc
    1 - ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2
        ≤ 1 - P.expectationReal (fun samples => Z samples ^ 2) / η ^ 2 := by
            linarith
    _ ≤ P.eventProb {samples | Z samples ≤ η} := hprob
    _ = P.eventProb
        (algorithm1ExactFrobEvent s A
          (fun samples : ElementwiseTrace m n s => samples) η) := by
            rfl

-- ============================================================
-- Probabilistic transfer
-- ============================================================

/-- A Frobenius residual event implies the corresponding rectangular
    vector-action operator-2 residual event. This deterministic bridge is useful
    for weaker exact concentration theorems and as a sanity layer before a true
    matrix Bernstein/Khintchine proof. -/
theorem algorithm1ExactFrobEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) :
    algorithm1ExactFrobEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hFrob
  exact rectOpNorm2Le_of_frobNormRect_le
    (elementwiseTraceResidual s A (X ω)) hFrob

/-- A simultaneous entrywise residual bound implies an exact rectangular
    operator-2 event with the Frobenius norm of the constant entry budget.

This is a deterministic union-bound support bridge, not a spectral
concentration theorem. -/
theorem algorithm1ExactEntrywiseEvent_subset_exactSpectralEvent_const
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    algorithm1ExactEntrywiseEvent s A X τ ⊆
      algorithm1ExactSpectralEvent s A X
        (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ)) := by
  intro ω hEntry
  apply rectOpNorm2Le_of_frobNormRect_le
  apply frobNormRect_le_of_entry_abs_le
  · intro i j
    exact hτ
  · intro i j
    exact hEntry i j

/-- Probability transfer from an exact Frobenius residual event to the
    repository's exact rectangular operator event. This is not the CACM
    equation (2) matrix-concentration theorem; it is a deterministic
    Frobenius-to-operator consequence for whatever exact Frobenius event has
    already been proved. -/
theorem probability_algorithm1_exact_spectral_of_frob
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ)
    (hFrobProb : ρ ≤ Pr.eventProb (algorithm1ExactFrobEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hFrobProb
    (Pr.eventProb_mono
      (algorithm1ExactFrobEvent_subset_exactSpectralEvent s A X ε))

/-- Probability transfer from a simultaneous entrywise residual event to the
    exact rectangular operator event with constant-entry Frobenius budget. -/
theorem probability_algorithm1_exact_spectral_of_entrywise_const
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ τ : ℝ) (hτ : 0 ≤ τ)
    (hEntryProb :
      ρ ≤ Pr.eventProb (algorithm1ExactEntrywiseEvent s A X τ)) :
    ρ ≤ Pr.eventProb
      (algorithm1ExactSpectralEvent s A X
        (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ))) := by
  exact le_trans hEntryProb
    (Pr.eventProb_mono
      (algorithm1ExactEntrywiseEvent_subset_exactSpectralEvent_const
        s A X τ hτ))

/-- A self-adjoint dilation residual event implies the rectangular
    vector-action residual event. This is the deterministic bridge needed to
    use future square matrix concentration theorems for CACM equation (2). -/
theorem algorithm1ExactDilationEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) :
    algorithm1ExactDilationEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hDilation
  exact rectOpNorm2Le_of_selfAdjointDilation
    (elementwiseTraceResidual s A (X ω)) hDilation

/-- A one-sided dilation Loewner event implies the rectangular spectral event.
    This is the event-level adapter for a future largest-eigenvalue matrix
    concentration theorem stated as `D(M) <= ε I`. -/
theorem algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationUpperEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hUpper
  exact rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hε hUpper

/-- Monotonicity of the exact Algorithm 1 spectral event in the radius. -/
theorem algorithm1ExactSpectralEvent_mono
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    {ε η : ℝ} (hεη : ε ≤ η) :
    algorithm1ExactSpectralEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X η := by
  intro ω hω
  exact rectOpNorm2Le_mono hεη hω

/-- Deterministic bridge from the scaled Hermitian-eigenvalue tail event to
    the rectangular Algorithm 1 spectral event.  It is the first conversion
    step after the trace-MGF corollary: `|lambda(theta D(R))| < T` implies
    `D(R) <= (T / theta) I`, and self-adjoint dilation Loewner control gives
    the rectangular operator bound. -/
theorem algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    {theta T : ℝ} (htheta : 0 < theta) (hTtheta : 0 ≤ T / theta) :
    algorithm1ScaledDilationAbsEigenvalueEvent s A X theta T ⊆
      algorithm1ExactSpectralEvent s A X (T / theta) := by
  intro ω hScaled
  let D : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω))
  let Mscaled : Fin m ⊕ Fin n → Fin m ⊕ Fin n → ℝ :=
    fun b c => theta * D b c
  have hsymScaled : IsSymmetricFiniteMatrix Mscaled := by
    intro b c
    exact congrArg (fun x => theta * x)
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A (X ω)) b c)
  have hEigUpper :
      ∀ a : Fin m ⊕ Fin n,
        finiteHermitianEigenvalues Mscaled hsymScaled a ≤ T := by
    intro a
    have hlt := hScaled a
    have hle_abs :
        finiteHermitianEigenvalues Mscaled hsymScaled a ≤
          |finiteHermitianEigenvalues Mscaled hsymScaled a| :=
      le_abs_self _
    exact le_of_lt (lt_of_le_of_lt hle_abs hlt)
  have hUpperScaled :
      finiteLoewnerLe Mscaled (fun a b => T * finiteIdMatrix a b) :=
    finiteLoewnerLe_smul_id_of_finiteHermitianEigenvalues_le
      Mscaled hsymScaled hEigUpper
  have hUpper :
      finiteLoewnerLe D (fun a b => (T / theta) * finiteIdMatrix a b) := by
    exact finiteLoewnerLe_of_smul_left_le_smul_id D htheta
      (by simpa [Mscaled, D] using hUpperScaled)
  exact rectOpNorm2Le_of_selfAdjointDilation_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hTtheta (by simpa [D] using hUpper)

/-- Explicit high-probability spectral-event form obtained from the scaled
eigenvalue tail.

The radius is still the unoptimized matrix-Bernstein parameter expression
`log (2 B / δ) / theta`.  This theorem closes the deterministic conversion
from the trace-MGF eigenvalue event to the repository's rectangular
`algorithm1ExactSpectralEvent`; the remaining CACM equation (2) work is the
source-constant `theta` optimization. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius
    {m n s : ℕ} {theta δ : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro L beta V B
  let P := sqMagTraceProbability (steps := s) A hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hmn_pos_nat : 0 < m + n := by
      exact_mod_cast hdim
    have hmn_ge_one_nat : 1 ≤ m + n := Nat.succ_le_of_lt hmn_pos_nat
    have hmn_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (m + n : ℕ) := by
        exact_mod_cast hmn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      have hmax_nonneg : 0 ≤ max (m : ℝ) (n : ℝ) :=
        le_trans (Nat.cast_nonneg m) (le_max_left (m : ℝ) (n : ℝ))
      have hfrac_nonneg :
          0 ≤ frobNormSqRect A / (s : ℝ) ^ 2 :=
        div_nonneg (frobNormSqRect_nonneg A) (sq_nonneg (s : ℝ))
      exact mul_nonneg hmax_nonneg hfrac_nonneg
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hmn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s A
          (fun samples : ElementwiseTrace m n s => samples) theta T) := by
    simpa [P, T, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_literalTraceResidual_lt_ge_one_sub_delta_supportRadius
        (m := m) (n := n) (s := s) (theta := theta) (δ := δ)
        hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s A
          (fun samples : ElementwiseTrace m n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s A (fun samples : ElementwiseTrace m n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Bennett-optimized literal Algorithm 1 support-radius theorem.

This is the nontruncated, literal-law analogue of the truncated Bennett
wrapper.  It removes the free trace-MGF parameter by choosing
`theta = log (1 + L*r/W) / L`, where `L` is the exact reciprocal-entry support
radius and `W = s*V` is the summed variance proxy.  The theorem is
nonconditional, but its budget visibly depends on the literal support radius;
it is therefore not the source-uniform CACM equation-(2) rate when tiny
nonzero entries are present. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bennett_radius_supportRadius
    {m n s : ℕ} {δ r : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect A / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) A hden
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hFrob_pos : 0 < frobNormRect A := by
    have hne : frobNormRect A ≠ 0 := by
      intro hzero
      have hsq := frobNormRect_sq A
      have hzero_sq : frobNormRect A ^ 2 = 0 := by simp [hzero]
      have hzero_frob : frobNormSqRect A = 0 := by
        rw [← hsq, hzero_sq]
      exact (ne_of_gt hdenA) hzero_frob
    exact lt_of_le_of_ne (frobNormRect_nonneg A) (Ne.symm hne)
  have hL_pos : 0 < L := by
    have hfirst :
        0 < (1 / (s : ℝ)) * frobNormRect A :=
      mul_pos (one_div_pos.mpr hs) hFrob_pos
    have hsecond :
        0 ≤ elementwiseLiteralContributionRadius s A :=
      elementwiseLiteralContributionRadius_nonneg hs A
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect A +
            elementwiseLiteralContributionRadius s A :=
      add_pos_of_pos_of_nonneg hfirst hsecond
    simpa [L, elementwiseLiteralResidualSupportRadius] using hsum
  have hmax_pos : 0 < max (m : ℝ) (n : ℝ) := by
    by_contra hnot
    have hmax_le : max (m : ℝ) (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm_le : (m : ℝ) ≤ 0 :=
      le_trans (le_max_left (m : ℝ) (n : ℝ)) hmax_le
    have hn_le : (n : ℝ) ≤ 0 :=
      le_trans (le_max_right (m : ℝ) (n : ℝ)) hmax_le
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect A / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hmax_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((m : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((m : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((m : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s A
            (fun samples : ElementwiseTrace m n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius
        (m := m) (n := n) (s := s) (theta := theta) (δ := δ)
        hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s A
      (fun samples : ElementwiseTrace m n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Literal Algorithm 1 support-radius theorem in Bernstein-denominator form.

This corollary replaces the exact Bennett-transform budget by the fully proved
scalar denominator `2W + (2/3)Lr`.  The support scale `L` is still the exact
literal reciprocal-entry radius, so the result is nonconditional and
nonvacuous without hiding the tiny-entry dependence. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius
    {m n s : ℕ} {δ r : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect A / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    simpa [L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hFrob_pos : 0 < frobNormRect A := by
    have hne : frobNormRect A ≠ 0 := by
      intro hzero
      have hsq := frobNormRect_sq A
      have hzero_sq : frobNormRect A ^ 2 = 0 := by simp [hzero]
      have hzero_frob : frobNormSqRect A = 0 := by
        rw [← hsq, hzero_sq]
      exact (ne_of_gt hdenA) hzero_frob
    exact lt_of_le_of_ne (frobNormRect_nonneg A) (Ne.symm hne)
  have hL_pos : 0 < L := by
    have hfirst :
        0 < (1 / (s : ℝ)) * frobNormRect A :=
      mul_pos (one_div_pos.mpr hs) hFrob_pos
    have hsecond :
        0 ≤ elementwiseLiteralContributionRadius s A :=
      elementwiseLiteralContributionRadius_nonneg hs A
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect A +
            elementwiseLiteralContributionRadius s A :=
      add_pos_of_pos_of_nonneg hfirst hsecond
    simpa [L, elementwiseLiteralResidualSupportRadius] using hsum
  have hmax_pos : 0 < max (m : ℝ) (n : ℝ) := by
    by_contra hnot
    have hmax_le : max (m : ℝ) (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm_le : (m : ℝ) ≤ 0 :=
      le_trans (le_max_left (m : ℝ) (n : ℝ)) hmax_le
    have hn_le : (n : ℝ) ≤ 0 :=
      le_trans (le_max_right (m : ℝ) (n : ℝ)) hmax_le
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect A / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hmax_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL_pos hW_pos hr hbudget'
  exact
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bennett_radius_supportRadius
      (m := m) (n := n) (s := s) (δ := δ) (r := r)
      hs A hden hdim hδ hδ_le_one hr
      (by simpa [L, V, W] using hbennett)

/-- Budget adapter from a simple nonzero-entry floor to the exact literal
reciprocal-entry support radius used by the Bernstein-denominator theorem.

The floor budget is stronger but easier to read: it replaces
`elementwiseLiteralResidualSupportRadius s A` by the upper bound
`s^{-1}||A||_F + mn ||A||_F^2/(s alpha)`. -/
theorem algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor
    {m n s : ℕ} {δ r alpha : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hr : 0 < r)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hbudget :
      let Lfloor : ℝ :=
        (1 / (s : ℝ)) * frobNormRect A +
          ((m : ℝ) * (n : ℝ)) *
            (frobNormSqRect A / ((s : ℝ) * alpha))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r)) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let W : ℝ := (s : ℝ) * V
    Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
      r ^ 2 / (2 * W + (2 / 3) * L * r) := by
  classical
  let L : ℝ := elementwiseLiteralResidualSupportRadius s A
  let Lfloor : ℝ :=
    (1 / (s : ℝ)) * frobNormRect A +
      ((m : ℝ) * (n : ℝ)) *
        (frobNormSqRect A / ((s : ℝ) * alpha))
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect A / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget_floor :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r) := by
    simpa [Lfloor, V, W] using hbudget
  have hL_le : L ≤ Lfloor := by
    simpa [L, Lfloor] using
      elementwiseLiteralResidualSupportRadius_le_of_entry_abs_ge
        halpha hs A hentry
  have hL_nonneg : 0 ≤ L := by
    simpa [L] using elementwiseLiteralResidualSupportRadius_nonneg hs A
  have hdenA : 0 < frobNormSqRect A := by
    simpa [sqMagProbDen] using hden
  have hmax_pos : 0 < max (m : ℝ) (n : ℝ) := by
    by_contra hnot
    have hmax_le : max (m : ℝ) (n : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm_le : (m : ℝ) ≤ 0 :=
      le_trans (le_max_left (m : ℝ) (n : ℝ)) hmax_le
    have hn_le : (n : ℝ) ≤ 0 :=
      le_trans (le_max_right (m : ℝ) (n : ℝ)) hmax_le
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect A / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hmax_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hden_actual_pos : 0 < 2 * W + (2 / 3) * L * r := by
    nlinarith [hW_pos, hL_nonneg, hr]
  have hden_le :
      2 * W + (2 / 3) * L * r ≤
        2 * W + (2 / 3) * Lfloor * r := by
    have hcoef_nonneg : 0 ≤ (2 / 3 : ℝ) * r := by positivity
    have hmul := mul_le_mul_of_nonneg_right hL_le hcoef_nonneg
    nlinarith [hmul]
  have hdiv :
      r ^ 2 / (2 * W + (2 / 3) * Lfloor * r) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) :=
    div_le_div_of_nonneg_left (sq_nonneg r) hden_actual_pos hden_le
  exact hbudget_floor.trans
    (by simpa [L, Lfloor, V, W] using hdiv)

/-- Literal Algorithm 1 exact spectral theorem with the reciprocal-entry
support radius replaced by a readable nonzero-entry floor.

This is still a literal-law theorem.  It is nonconditional and exact, but it is
not source-uniform: the displayed budget depends on the entry floor `alpha`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_entry_floor
    {m n s : ℕ} {δ r alpha : ℝ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hbudget :
      let Lfloor : ℝ :=
        (1 / (s : ℝ)) * frobNormRect A +
          ((m : ℝ) * (n : ℝ)) *
            (frobNormSqRect A / ((s : ℝ) * alpha))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  have hbudget_actual :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) :=
    algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor
      hs A hden hdim hr halpha hentry hbudget
  exact
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius
      (m := m) (n := n) (s := s) (δ := δ) (r := r)
      hs A hden hdim hδ hδ_le_one hr hbudget_actual

theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ :=
      2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro Ahat L beta V B
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hmn_pos_nat : 0 < m + n := by
      exact_mod_cast hdim
    have hmn_ge_one_nat : 1 ≤ m + n := Nat.succ_le_of_lt hmn_pos_nat
    have hmn_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (m + n : ℕ) := by
        exact_mod_cast hmn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hmn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T) := by
    simpa [P, T, Ahat, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s Ahat (fun samples : ElementwiseTrace m n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Bennett-optimized high-probability spectral-event form for the truncated
Algorithm 1 route.

This corollary chooses
`theta = log (1 + L * r / W) / L`, where `W = s * V`, and uses the exact
scalar Bennett transform to replace the unoptimized radius
`log (2B/delta) / theta` by a requested radius `r`.  It is still a truncated
exact-arithmetic theorem; the CACM equation (2) row also needs the source
sample-complexity simplification, truncation transfer back to the original
matrix at the final constants, and the downstream floating-point spectral
transfer. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius
    {m n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ := Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
      let V : ℝ :=
        2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ :=
    2 * ((m : ℝ) * (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2))
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hparen :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hparen
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos (by norm_num) (mul_pos hmn hfrac)
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((m : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((m : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((m : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s Ahat
            (fun samples : ElementwiseTrace m n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, Ahat, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s Ahat
      (fun samples : ElementwiseTrace m n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Rectangular source-sharp high-probability spectral-event form obtained
from the scaled eigenvalue tail.

This is the rectangular companion of the square source-sharp wrapper.  It uses
the variance scale `max(m,n) * ||Ahat||_F^2 / s^2` from the rectangular
trace-MGF skeleton and keeps the generic retained-entry support radius with
the `sqrt 2` dilation factor. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_rect
    {m n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ := Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro Ahat L beta V B
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hmn_pos_nat : 0 < m + n := by
      exact_mod_cast hdim
    have hmn_ge_one_nat : 1 ≤ m + n := Nat.succ_le_of_lt hmn_pos_nat
    have hmn_ge_one : (1 : ℝ) ≤ (m : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (m + n : ℕ) := by
        exact_mod_cast hmn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hmn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T) := by
    simpa [P, T, Ahat, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_rect
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s Ahat (fun samples : ElementwiseTrace m n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Rectangular source-sharp Bennett-optimized high-probability spectral-event
form for the truncated Algorithm 1 route. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_rect
    {m n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ := Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((m : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hsum
  have hM_pos : 0 < max (m : ℝ) (n : ℝ) := by
    have hm_le : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
    have hn_le : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hM_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((m : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((m : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((m : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s Ahat
            (fun samples : ElementwiseTrace m n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, Ahat, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_rect
        (m := m) (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s Ahat
      (fun samples : ElementwiseTrace m n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Rectangular source-sharp Bernstein-denominator corollary for the truncated
Algorithm 1 route.

This removes the raw Bennett-transform hypothesis using the proved scalar
bound `(1+x) log(1+x)-x >= x^2/(2+(2/3)x)`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_rect
    {m n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ := Real.sqrt 2 *
        ((1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ := max (m : ℝ) (n : ℝ) *
    (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    exact mul_pos hsqrt hsum
  have hM_pos : 0 < max (m : ℝ) (n : ℝ) := by
    have hm_le : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
    have hn_le : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
    nlinarith [hdim, hm_le, hn_le]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hM_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL_pos hW_pos hr hbudget'
  simpa [Ahat] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau hs A hden hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W] using hbennett)

set_option maxHeartbeats 800000

/-- Rectangular source-sample-budget corollary for the truncated Algorithm 1
route.

With `tau = eps/(2*sqrt(mn))`, the explicit budget
`4*(2M+(4 sqrt(2)/3)R)*||A||_F^2*log(2(m+n)/delta) <= s*eps^2`, where
`M=max(m,n)` and `R=sqrt(mn)`, implies the source-sharp rectangular
Bernstein-denominator event at radius `eps/2`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_rect
    {m n s : ℕ} {eps δ : ℝ} (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (eps / 2)) := by
  classical
  let M : ℝ := max (m : ℝ) (n : ℝ)
  let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
  let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let r : ℝ := eps / 2
  let L : ℝ := Real.sqrt 2 *
    ((1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau))
  let V : ℝ := M * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let q : ℝ := Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ)
  intro tau' Ahat'
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr hmn
  have htau_pos : 0 < tau := by
    dsimp [tau, R]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdim : 0 < (m : ℝ) + (n : ℝ) := by
    have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hmn, hm_nonneg, hn_nonneg]
  have hM_pos : 0 < M := by
    have hm_le : (m : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_left _ _
    have hn_le : (n : ℝ) ≤ max (m : ℝ) (n : ℝ) := le_max_right _ _
    dsimp [M]
    nlinarith [hdim, hm_le, hn_le]
  have hC_pos : 0 < C := by
    dsimp [C]
    have hterm_nonneg :
        0 ≤ ((4 * Real.sqrt 2) / 3) * R := by
      positivity
    nlinarith
  have hFhatSq_pos : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, tau, sqMagProbDen] using hden
  have hFhat_pos : 0 < frobNormRect Ahat := by
    have hne : frobNormRect Ahat ≠ 0 := by
      intro hzero
      have hsq_zero : frobNormSqRect Ahat = 0 := by
        rw [← frobNormRect_sq Ahat, hzero]
        norm_num
      linarith
    exact lt_of_le_of_ne (frobNormRect_nonneg Ahat) (Ne.symm hne)
  have hFsq_pos : 0 < frobNormSqRect A := by
    exact lt_of_lt_of_le hFhatSq_pos
      (by simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A)
  have hFhatSq_le_Fsq : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have htau_le_Fhat : tau ≤ frobNormRect Ahat := by
    simpa [Ahat, tau] using
      elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
        (tau := tau) A (by simpa [Ahat, tau] using hden)
  have heps_le_two_R_Fhat :
      eps ≤ 2 * R * frobNormRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_left htau_le_Fhat
        (by positivity : 0 ≤ 2 * R)
    dsimp [tau] at hmul
    field_simp [hR_pos.ne'] at hmul
    nlinarith
  have heps_mul_Fhat_le :
      eps * frobNormRect Ahat ≤
        2 * R * frobNormSqRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_right heps_le_two_R_Fhat
        (le_of_lt hFhat_pos)
    calc
      eps * frobNormRect Ahat
          ≤ 2 * R * frobNormRect Ahat * frobNormRect Ahat := hmul
      _ = 2 * R * frobNormSqRect Ahat := by
          rw [← frobNormRect_sq Ahat]
          ring
  have hD_bound :
      2 * W + (2 / 3 : ℝ) * L * r ≤
        C * frobNormSqRect A / (s : ℝ) := by
    have hcoef_le :
        (6 * M + 4 * Real.sqrt 2 * R) * frobNormSqRect Ahat ≤
          (6 * M + 4 * Real.sqrt 2 * R) * frobNormSqRect A := by
      have hcoef_nonneg : 0 ≤ 6 * M + 4 * Real.sqrt 2 * R := by
        positivity
      exact mul_le_mul_of_nonneg_left hFhatSq_le_Fsq hcoef_nonneg
    dsimp [W, V, L, r, tau, C, M, R]
    field_simp [hs.ne', hR_pos.ne']
    nlinarith [heps_mul_Fhat_le, hcoef_le, Real.sqrt_nonneg 2]
  have hD_pos : 0 < 2 * W + (2 / 3 : ℝ) * L * r := by
    have hL_pos : 0 < L := by
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
        mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
      have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
        div_pos hFhatSq_pos (mul_pos hs htau_pos)
      have hsum :
          0 <
            (1 / (s : ℝ)) * frobNormRect Ahat +
              frobNormSqRect Ahat / ((s : ℝ) * tau) :=
        add_pos_of_nonneg_of_pos hfirst hsecond
      exact mul_pos hsqrt hsum
    have hV_pos : 0 < V := by
      have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
      have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
        div_pos hFhatSq_pos hs_sq
      dsimp [V]
      exact mul_pos hM_pos hfrac
    have hW_pos : 0 < W := by
      dsimp [W]
      exact mul_pos hs hV_pos
    positivity
  have hq_le_sample :
      q ≤ ((s : ℝ) * eps ^ 2) /
          (4 * C * frobNormSqRect A) := by
    have hden_sample : 0 < 4 * C * frobNormSqRect A := by
      positivity
    exact (le_div_iff₀ hden_sample).mpr (by
      have hsample_comm :
          q * (4 * C * frobNormSqRect A) ≤ (s : ℝ) * eps ^ 2 := by
        simpa [q, M, R, C, mul_assoc, mul_left_comm, mul_comm] using hsample
      simpa [mul_assoc, mul_left_comm, mul_comm] using hsample_comm)
  have hsample_factor_nonneg :
      0 ≤ ((s : ℝ) * eps ^ 2) /
          (4 * C * frobNormSqRect A) := by
    positivity
  have hqD_le : q * (2 * W + (2 / 3 : ℝ) * L * r) ≤ r ^ 2 := by
    have h1 :
        q * (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) :=
      mul_le_mul_of_nonneg_right hq_le_sample (le_of_lt hD_pos)
    have h2 :
        (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (C * frobNormSqRect A / (s : ℝ)) :=
      mul_le_mul_of_nonneg_left hD_bound hsample_factor_nonneg
    have h3 :
        (((s : ℝ) * eps ^ 2) /
            (4 * C * frobNormSqRect A)) *
            (C * frobNormSqRect A / (s : ℝ)) =
          r ^ 2 := by
      dsimp [r]
      field_simp [hs.ne', hC_pos.ne', (ne_of_gt hFsq_pos)]
      ring
    exact h1.trans (h2.trans_eq h3)
  have hbudget :
      q ≤ r ^ 2 / (2 * W + (2 / 3 : ℝ) * L * r) :=
    (le_div_iff₀ hD_pos).mpr hqD_le
  simpa [tau, Ahat, tau', Ahat', r, L, V, W, q, M, R, C] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_rect
      (m := m) (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau_pos hs A (by simpa [Ahat, tau] using hden) hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W, q, M] using hbudget)

/-- Exact rectangular source-budget Algorithm 1 theorem after deterministic
truncation transfer.

This theorem controls the exact truncated sketch against the original
rectangular input `A` at radius `eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_rect
    {m n s : ℕ} {eps δ : ℝ} (hmn : 0 < (m : ℝ) * (n : ℝ))
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  intro tau' Ahat'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hProb :
      1 - δ ≤ P.eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace m n s => samples) (eps / 2)) := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_rect
        (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample
  have hmain :=
    probability_algorithm1_exact_truncated_rect_spectral_of_sampled_half
      (s := s) (A := A)
      (X := fun samples : ElementwiseTrace m n s => samples)
      (Pr := P) (ρ := 1 - δ) (eps := eps)
      (le_of_lt heps) hmn hProb
  simpa [P, tau, Ahat, tau', Ahat'] using hmain

/-- Source-sharp square-matrix high-probability spectral-event form obtained
from the scaled eigenvalue tail.

This is the square-matrix companion to
`sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius`.
It uses the Drineas--Zouzias variance scale
`V = n * ||Ahat||_F^2 / s^2` and the no-`sqrt 2` support radius supplied by
the source-sharp trace-MGF skeleton. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square
    {n s : ℕ} {tau theta δ : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (htheta : 0 < theta)
    (hdim : 0 < (n : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let L : ℝ :=
      (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau)
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
    let B : ℝ := ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples)
          (Real.log ((2 * B) / δ) / theta)) := by
  classical
  intro Ahat L beta V B
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let T : ℝ := Real.log ((2 * B) / δ)
  have hTtheta : 0 ≤ T / theta := by
    have hnn_pos_nat : 0 < n + n := by
      exact_mod_cast hdim
    have hnn_ge_one_nat : 1 ≤ n + n := Nat.succ_le_of_lt hnn_pos_nat
    have hnn_ge_one : (1 : ℝ) ≤ (n : ℝ) + (n : ℝ) := by
      have hcast : (1 : ℝ) ≤ (n + n : ℕ) := by
        exact_mod_cast hnn_ge_one_nat
      simpa [Nat.cast_add] using hcast
    have hnum : 0 ≤ Real.exp (theta * L) - theta * L - 1 :=
      real_exp_sub_self_sub_one_nonneg (theta * L)
    have hbeta_nonneg : 0 ≤ beta := by
      dsimp [beta]
      exact div_nonneg hnum (sq_nonneg L)
    have hV_nonneg : 0 ≤ V := by
      dsimp [V]
      positivity
    have hexponent_nonneg : 0 ≤ (s : ℝ) * (beta * V) := by
      positivity
    have hexp_ge_one : 1 ≤ Real.exp ((s : ℝ) * (beta * V)) :=
      Real.one_le_exp_iff.mpr hexponent_nonneg
    have hB_ge_one : 1 ≤ B := by
      dsimp [B]
      nlinarith [hnn_ge_one, hexp_ge_one]
    have harg_ge_one : 1 ≤ (2 * B) / δ := by
      have hδ_le_2B : δ ≤ 2 * B := by
        nlinarith [hδ_le_one, hB_ge_one]
      exact (le_div_iff₀ hδ).mpr
        (by simpa using hδ_le_2B : (1 : ℝ) * δ ≤ 2 * B)
    have hlog_nonneg : 0 ≤ Real.log ((2 * B) / δ) :=
      Real.log_nonneg harg_ge_one
    exact div_nonneg hlog_nonneg (le_of_lt htheta)
  have hscaled :
      1 - δ ≤ P.eventProb
        (algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) theta T) := by
    simpa [P, T, Ahat, L, beta, V, B,
      algorithm1ScaledDilationAbsEigenvalueEvent] using
      sqMagTraceProbability_eventProb_forall_abs_finiteHermitianEigenvalue_scaled_rectSelfAdjointDilation_truncatedTraceResidual_lt_ge_one_sub_delta_sharp_square
        (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden (le_of_lt htheta) hdim hδ
  have hsubset :
      algorithm1ScaledDilationAbsEigenvalueEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) theta T ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (T / theta) :=
    algorithm1ScaledDilationAbsEigenvalueEvent_subset_exactSpectralEvent
      s Ahat (fun samples : ElementwiseTrace n n s => samples)
      htheta hTtheta
  exact hscaled.trans (P.eventProb_mono hsubset)

/-- Source-sharp Bennett-optimized high-probability spectral-event form for the
square truncated Algorithm 1 route.

This theorem closes the next source-sharp dependency after the two-sided
eigenvalue skeleton: under the explicit scalar Bennett budget with
`L = s^{-1} ||Ahat||_F + ||Ahat||_F^2/(s tau)` and
`W = s * n * ||Ahat||_F^2 / s^2`, the exact truncated sketch is within any
requested spectral radius `r` with probability at least `1 - delta`.  The
remaining Algorithm 1 equation (2) work is to simplify this budget to the
Drineas--Zouzias/CACM sample-complexity constants and then transfer the result
through truncation and floating-point perturbation. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
    {n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (n : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ :=
        (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)
      let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W))) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let theta : ℝ := Real.log (1 + L * r / W) / L
  let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
  let B : ℝ := ((n : ℝ) + (n : ℝ)) * Real.exp ((s : ℝ) * (beta * V))
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hbudget' :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    simpa [L] using hsum
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hdim, hn_nonneg]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hn_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL_pos
  have hradius_core :
      (Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) + W * beta) /
          theta ≤ r := by
    simpa [theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL_pos hW_pos hr hbudget'
  have hlog_radius :
      Real.log ((2 * B) / δ) / theta ≤ r := by
    have hq_pos : 0 < (2 * ((n : ℝ) + (n : ℝ))) / δ :=
      div_pos (mul_pos (by norm_num) hdim) hδ
    have hexp_ne : Real.exp ((s : ℝ) * (beta * V)) ≠ 0 :=
      ne_of_gt (Real.exp_pos _)
    have hrewrite :
        (2 * B) / δ =
          ((2 * ((n : ℝ) + (n : ℝ))) / δ) *
            Real.exp ((s : ℝ) * (beta * V)) := by
      dsimp [B]
      field_simp [hδ.ne']
    have hlog :
        Real.log ((2 * B) / δ) =
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) +
            W * beta := by
      calc
        Real.log ((2 * B) / δ)
            = Real.log
                (((2 * ((n : ℝ) + (n : ℝ))) / δ) *
                  Real.exp ((s : ℝ) * (beta * V))) := by
                rw [hrewrite]
        _ = Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) +
              Real.log (Real.exp ((s : ℝ) * (beta * V))) := by
                rw [Real.log_mul (ne_of_gt hq_pos) hexp_ne]
        _ = Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) + W * beta := by
                rw [Real.log_exp]
                dsimp [W]
                ring
    simpa [hlog] using hradius_core
  have hbase :
      1 - δ ≤
        P.eventProb
          (algorithm1ExactSpectralEvent s Ahat
            (fun samples : ElementwiseTrace n n s => samples)
            (Real.log ((2 * B) / δ) / theta)) := by
    simpa [P, Ahat, L, V, B, beta, theta] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_scaled_radius_sharp_square
        (n := n) (s := s) (tau := tau) (theta := theta) (δ := δ)
        htau hs A hden htheta_pos hdim hδ hδ_le_one
  have hsubset :
      algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples)
          (Real.log ((2 * B) / δ) / theta) ⊆
        algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r :=
    algorithm1ExactSpectralEvent_mono s Ahat
      (fun samples : ElementwiseTrace n n s => samples) hlog_radius
  exact hbase.trans (P.eventProb_mono hsubset)

/-- Conservative Bernstein-denominator corollary for the source-sharp square
Algorithm 1 route.

This theorem composes the source-sharp Bennett-radius theorem with the fully
proved scalar inequality
`(1+x) log(1+x) - x >= x^2/(2+x)`.  Its denominator
`2W + Lr` is weaker than the source-sharp Bernstein denominator
`2W + (2/3)Lr`; the latter is kept as the active final-constant bottleneck.
Nevertheless this corollary removes the raw Bennett-transform hypothesis for
a completely formalized fallback high-probability statement. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_sharp_square
    {n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (n : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ :=
        (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)
      let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + L * r)) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + L * r) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    simpa [L] using hsum
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hdim, hn_nonneg]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hn_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add
      hL_pos hW_pos hr hbudget'
  simpa [Ahat] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
      (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau hs A hden hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W] using hbennett)

/-- Source-sharp Bernstein-denominator corollary for the square Algorithm 1
route.

This theorem uses the fully proved scalar Bennett lower bound
`(1+x) log(1+x)-x >= x^2/(2+(2/3)x)`.  Thus the paper-style denominator
condition `q <= r^2/(2W+(2/3)Lr)` is enough to obtain the source-sharp
truncated spectral event at radius `r`.  The remaining CACM equation (2)
work is now the final sample-size algebra for the Drineas--Zouzias constants,
followed by truncation and floating-point transfer. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_square
    {n s : ℕ} {tau δ r : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A))
    (hdim : 0 < (n : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hbudget :
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
      let L : ℝ :=
        (1 / (s : ℝ)) * frobNormRect Ahat +
          frobNormSqRect Ahat / ((s : ℝ) * tau)
      let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) r) := by
  classical
  intro Ahat
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  have hbudget' :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    simpa [Ahat, L, V, W] using hbudget
  have hdenA : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, sqMagProbDen] using hden
  have hL_pos : 0 < L := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_pos hdenA (mul_pos hs htau)
    have hsum :
        0 <
          (1 / (s : ℝ)) * frobNormRect Ahat +
            frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      add_pos_of_nonneg_of_pos hfirst hsecond
    simpa [L] using hsum
  have hn_pos : 0 < (n : ℝ) := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    nlinarith [hdim, hn_nonneg]
  have hV_pos : 0 < V := by
    have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
    have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
      div_pos hdenA hs_sq
    dsimp [V]
    exact mul_pos hn_pos hfrac
  have hW_pos : 0 < W := by
    dsimp [W]
    exact mul_pos hs hV_pos
  have hbennett :
      Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL_pos hW_pos hr hbudget'
  simpa [Ahat] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bennett_radius_sharp_square
      (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau hs A hden hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W] using hbennett)

/-- Source sample-budget corollary for the square truncated Algorithm 1 route.

With the Drineas--Zouzias truncation threshold `tau = eps/(2n)`, the explicit
sample-budget condition
`14*n*||A||_F^2*log(2(2n)/delta) <= s*eps^2` implies the source-sharp
Bernstein-denominator budget at radius `eps/2`.  The conclusion is still the
truncated exact spectral event; the final paper row additionally needs the
deterministic truncation transfer back to `A` and then the FP perturbation
transfer. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
    {n s : ℕ} {eps δ : ℝ} (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (eps / 2)) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let r : ℝ := eps / 2
  let L : ℝ :=
    (1 / (s : ℝ)) * frobNormRect Ahat +
      frobNormSqRect Ahat / ((s : ℝ) * tau)
  let V : ℝ := (n : ℝ) * (frobNormSqRect Ahat / (s : ℝ) ^ 2)
  let W : ℝ := (s : ℝ) * V
  let q : ℝ := Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ)
  intro tau' Ahat'
  have htau_pos : 0 < tau := by
    dsimp [tau]
    positivity
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hdim : 0 < (n : ℝ) + (n : ℝ) := by nlinarith
  have hFhatSq_pos : 0 < frobNormSqRect Ahat := by
    simpa [Ahat, tau, sqMagProbDen] using hden
  have hFhat_pos : 0 < frobNormRect Ahat := by
    have hne : frobNormRect Ahat ≠ 0 := by
      intro hzero
      have hsq_zero : frobNormSqRect Ahat = 0 := by
        rw [← frobNormRect_sq Ahat, hzero]
        norm_num
      linarith
    exact lt_of_le_of_ne (frobNormRect_nonneg Ahat) (Ne.symm hne)
  have hFsq_pos : 0 < frobNormSqRect A := by
    exact lt_of_lt_of_le hFhatSq_pos
      (by simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A)
  have hFhatSq_le_Fsq : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have htau_le_Fhat : tau ≤ frobNormRect Ahat := by
    simpa [Ahat, tau] using
      elementwiseTruncate_tau_le_frobNormRect_of_sqMagProbDen_pos
        (tau := tau) A (by simpa [Ahat, tau] using hden)
  have heps_le_two_n_Fhat :
      eps ≤ 2 * (n : ℝ) * frobNormRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_left htau_le_Fhat
        (by positivity : 0 ≤ 2 * (n : ℝ))
    dsimp [tau] at hmul
    field_simp [hn.ne'] at hmul
    nlinarith
  have heps_mul_Fhat_le :
      eps * frobNormRect Ahat ≤
        2 * (n : ℝ) * frobNormSqRect Ahat := by
    have hmul :=
      mul_le_mul_of_nonneg_right heps_le_two_n_Fhat
        (le_of_lt hFhat_pos)
    calc
      eps * frobNormRect Ahat
          ≤ 2 * (n : ℝ) * frobNormRect Ahat * frobNormRect Ahat := hmul
      _ = 2 * (n : ℝ) * frobNormSqRect Ahat := by
          rw [← frobNormRect_sq Ahat]
          ring
  have hD_bound :
      2 * W + (2 / 3 : ℝ) * L * r ≤
        ((7 / 2 : ℝ) * (n : ℝ) * frobNormSqRect A) / (s : ℝ) := by
    dsimp [W, V, L, r, tau]
    field_simp [hs.ne', hn.ne', htau_pos.ne']
    nlinarith [heps_mul_Fhat_le, hFhatSq_le_Fsq]
  have hD_pos : 0 < 2 * W + (2 / 3 : ℝ) * L * r := by
    have hL_pos : 0 < L := by
      have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
        mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
      have hsecond : 0 < frobNormSqRect Ahat / ((s : ℝ) * tau) :=
        div_pos hFhatSq_pos (mul_pos hs htau_pos)
      exact add_pos_of_nonneg_of_pos hfirst hsecond
    have hV_pos : 0 < V := by
      have hs_sq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hs
      have hfrac : 0 < frobNormSqRect Ahat / (s : ℝ) ^ 2 :=
        div_pos hFhatSq_pos hs_sq
      dsimp [V]
      exact mul_pos hn hfrac
    have hW_pos : 0 < W := by
      dsimp [W]
      exact mul_pos hs hV_pos
    positivity
  have hq_le_sample :
      q ≤ ((s : ℝ) * eps ^ 2) /
          (14 * (n : ℝ) * frobNormSqRect A) := by
    have hden_sample : 0 < 14 * (n : ℝ) * frobNormSqRect A := by
      positivity
    exact (le_div_iff₀ hden_sample).mpr (by
      dsimp [q]
      nlinarith [hsample])
  have hsample_factor_nonneg :
      0 ≤ ((s : ℝ) * eps ^ 2) /
          (14 * (n : ℝ) * frobNormSqRect A) := by
    positivity
  have hqD_le : q * (2 * W + (2 / 3 : ℝ) * L * r) ≤ r ^ 2 := by
    have h1 :
        q * (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) :=
      mul_le_mul_of_nonneg_right hq_le_sample (le_of_lt hD_pos)
    have h2 :
        (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (2 * W + (2 / 3 : ℝ) * L * r) ≤
          (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (((7 / 2 : ℝ) * (n : ℝ) * frobNormSqRect A) / (s : ℝ)) :=
      mul_le_mul_of_nonneg_left hD_bound hsample_factor_nonneg
    have h3 :
        (((s : ℝ) * eps ^ 2) /
            (14 * (n : ℝ) * frobNormSqRect A)) *
            (((7 / 2 : ℝ) * (n : ℝ) * frobNormSqRect A) / (s : ℝ)) =
          r ^ 2 := by
      dsimp [r]
      field_simp [hs.ne', hn.ne', (ne_of_gt hFsq_pos)]
      ring
    exact h1.trans (h2.trans_eq h3)
  have hbudget :
      q ≤ r ^ 2 / (2 * W + (2 / 3 : ℝ) * L * r) :=
    (le_div_iff₀ hD_pos).mpr hqD_le
  simpa [tau, Ahat, r, L, V, W, q] using
    sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_sharp_square
      (n := n) (s := s) (tau := tau) (δ := δ) (r := r)
      htau_pos hs A (by simpa [Ahat, tau] using hden) hdim hδ hδ_le_one hr
      (by simpa [Ahat, L, V, W, q] using hbudget)

/-- Exact source-budget Algorithm 1 theorem after the deterministic truncation
transfer.

The previous theorem controls the sampled residual of the truncated matrix at
radius `eps/2`.  This corollary adds the already-formalized deterministic
truncation error, giving an exact-arithmetic event against the original matrix
at radius `eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
    {n s : ℕ} {eps δ : ℝ} (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  intro tau' Ahat'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hn_nat : 0 < n := by exact_mod_cast hn
  have hProb :
      1 - δ ≤ P.eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (eps / 2)) := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
        (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample
  exact
    probability_algorithm1_exact_truncated_spectral_of_sampled_half
      (s := s) (A := A)
      (X := fun samples : ElementwiseTrace n n s => samples)
      (Pr := P) (ρ := 1 - δ) (eps := eps)
      (le_of_lt heps) hn_nat hProb

/-- On the positive-probability support of the squared-magnitude trace law, the
zero-initialized floating-point trace admits the repository's deterministic
gamma budget with `Q = steps`.

This support-aware statement is needed for truncated sampling: traces that hit
zero-probability entries have probability zero, and the floating-point model
does not constrain division by a zero denominator on those impossible traces. -/
theorem fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
    (fp : FPModel) {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (hs : (s : ℝ) ≠ 0)
    (hsteps : gammaValid fp steps) (hsteps1 : gammaValid fp (steps + 1))
    (hpos : elementwiseTracePositiveProb A samples) :
    ∀ i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤
        sqMagTraceErrorBudget fp steps s A (fun _ _ => 0) i j := by
  intro i j
  by_cases hzero : A i j = 0
  · have hnohit : ∀ t : Fin steps, ¬ sampleHits samples t i j := by
      intro t hhit
      have hp : 0 < sqMagProb A i j := by
        rcases hhit with ⟨hi, hj⟩
        simpa [hi, hj] using hpos t
      exact (entry_ne_zero_of_sqMagProb_pos A i j hp) hzero
    have hfl :
        fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j = 0 :=
      fl_elementwiseTraceSketch_zero_init_eq_zero_of_forall_not_hit
        fp s A samples i j hnohit
    have hexact :
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j = 0 :=
      elementwiseTraceSketch_zero_init_of_entry_eq_zero s A samples i j hzero
    have hbudget :
        0 ≤ sqMagTraceErrorBudget fp steps s A (fun _ _ => 0) i j :=
      sqMagTraceErrorBudget_nonneg fp steps s A (fun _ _ => 0) i j
        hsteps hsteps1
    simpa [hfl, hexact] using hbudget
  · have hcount : hitCount samples i j ≤ steps :=
      hitCount_le_steps samples i j
    have hdet :=
      fl_elementwiseTraceSketch_sqMag_error_bound_exact fp s A (fun _ _ => 0)
        samples i j hs hzero
        (gammaValid_mono fp hcount hsteps)
        (gammaValid_mono fp (Nat.succ_le_succ hcount) hsteps1)
    exact le_trans hdet
      (sqMagTraceErrorBudget_mono fp s A (fun _ _ => 0) i j
        hcount hsteps hsteps1)

/-- Floating-point literal Algorithm 1 spectral event with the exact
input-dependent support-radius concentration bound and the local gamma sketch
budget.

This theorem contains no generic perturbation-budget hypothesis.  The exact
probability law is the literal squared-magnitude trace law for `A`; the
floating-point budget is the concrete matrix
`sqMagTraceErrorBudget fp s s A 0`, obtained on the probability-one support
where all sampled denominators are nonzero. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_literal_scaled_radius_gamma_supportRadius
    (fp : FPModel) {m n s : ℕ} {theta δ : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let TraceB : ℝ := ((m : ℝ) + (n : ℝ)) *
      Real.exp ((s : ℝ) * (beta * V))
    let eps : ℝ := Real.log ((2 * TraceB) / δ) / theta
    let Bmat : Fin m → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples) eps Bmat) := by
  classical
  intro L beta V TraceB eps Bmat
  let P := sqMagTraceProbability (steps := s) A hden
  let Exact : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace m n s => samples) eps
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb A samples}
  let Fl : Set (ElementwiseTrace m n s) :=
    algorithm1FlSpectralEvent fp s A
      (fun samples : ElementwiseTrace m n s => samples) eps Bmat
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, L, beta, V, TraceB, eps] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_scaled_radius_supportRadius
        (m := m) (n := n) (s := s) (theta := theta) (δ := δ)
        hs A hden htheta hdim hδ hδ_le_one
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb A hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ Bmat i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s A (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s A
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s A
              (fun _ _ => 0) samples i j| ≤ Bmat i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb A samples := by
        simpa [Good] using hGood
      simpa [Bmat] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s A samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hfl :=
      fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
        fp s A samples Bmat hExact hB_nonneg hPoint
    simpa [Fl, algorithm1FlSpectralEvent] using hfl
  exact hInter'.trans (P.eventProb_mono hsubset)

/-- Floating-point source-budget Algorithm 1 theorem after deterministic
truncation and a stated entrywise FP perturbation budget.

The probability part is fully inherited from the exact source-budget theorem.
The only extra hypothesis is the explicit entrywise bound comparing the rounded
truncated sketch to the exact truncated sketch; this is the standard local FP
stability interface used elsewhere in the Algorithm 1 development. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (B : Fin n → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hPoint :
      ∀ (samples : ElementwiseTrace n n s) i j,
        |fl_elementwiseTraceSketch fp s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) samples i j -
          elementwiseTraceSketch s
            (elementwiseTruncate (eps / (2 * (n : ℝ))) A)
            (fun _ _ => 0) samples i j| ≤ B i j) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps B) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  intro tau' Ahat'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  have hn_nat : 0 < n := by exact_mod_cast hn
  have hProb :
      1 - δ ≤ P.eventProb
        (algorithm1ExactSpectralEvent s Ahat
          (fun samples : ElementwiseTrace n n s => samples) (eps / 2)) := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
        (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample
  exact
    probability_algorithm1_fl_truncated_spectral_of_sampled_half
      (fp := fp) (s := s) (A := A)
      (X := fun samples : ElementwiseTrace n n s => samples)
      (Pr := P) (ρ := 1 - δ) (eps := eps) (B := B)
      (le_of_lt heps) hn_nat hB_nonneg hPoint hProb

/-- Floating-point source-budget Algorithm 1 theorem with the entrywise
perturbation budget derived from the local gamma/hit-count stability library.

The exact event is intersected with the sampler's probability-one positive
support event.  On that support, every actually sampled denominator is nonzero,
so the deterministic local FP theorem supplies the budget
`sqMagTraceErrorBudget fp s s Ahat 0` with no separate `hPoint` hypothesis. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    let B : Fin n → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps B) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin n → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  intro tau' Ahat' B'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Exact : Set (ElementwiseTrace n n s) :=
    algorithm1ExactSpectralEvent s Ahat
      (fun samples : ElementwiseTrace n n s => samples) (eps / 2)
  let Good : Set (ElementwiseTrace n n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Fl : Set (ElementwiseTrace n n s) :=
    algorithm1FlTruncatedSpectralEvent fp tau s A
      (fun samples : ElementwiseTrace n n s => samples) eps B
  have hn_nat : 0 < n := by exact_mod_cast hn
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_square
        (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s Ahat (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j| ≤ B i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb Ahat samples := by
        simpa [Good] using hGood
      simpa [Ahat, B] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s Ahat samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hTruncFrob :
        frobNormRect
          (fun i j =>
            A i j - elementwiseTruncate (eps / (2 * (n : ℝ))) A i j) ≤
          eps / 2 :=
      elementwiseTruncate_square_error_frobNormRect_le_half A (le_of_lt heps) hn_nat
    have hfl :=
      fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
        fp tau s A samples (beta := eps / 2) (alpha := eps / 2)
        B hB_nonneg
        (by simpa [Ahat] using hExact)
        hPoint
        (by simpa [tau] using hTruncFrob)
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
      (eps + frobNormRect B)
    convert hfl using 1
    ring
  exact hInter'.trans
    (by
      simpa [P, Exact, Good, Fl, tau, Ahat, B] using
        P.eventProb_mono hsubset)

/-- Rectangular floating-point source-budget Algorithm 1 theorem with the
entrywise perturbation budget derived from the local gamma/hit-count stability
library.

The sampling law is exact by convention.  The non-probability computation
charged here is the rounded zero-initialized truncated sketch update, packaged
as `sqMagTraceErrorBudget fp s s Ahat 0` on the sampler's probability-one
positive support. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    let B : Fin m → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        (algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps B) := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  intro tau' Ahat' B'
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let Exact : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) (eps / 2)
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb Ahat samples}
  let Fl : Set (ElementwiseTrace m n s) :=
    algorithm1FlTruncatedSpectralEvent fp tau s A
      (fun samples : ElementwiseTrace m n s => samples) eps B
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncatedTraceResidual_ge_one_sub_delta_source_sample_budget_sharp_rect
        (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb Ahat hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s Ahat (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s (elementwiseTruncate tau A)
              (fun _ _ => 0) samples i j| ≤ B i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb Ahat samples := by
        simpa [Good] using hGood
      simpa [Ahat, B] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s Ahat samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hTruncFrob :
        frobNormRect
          (fun i j =>
            A i j -
              elementwiseTruncate
                (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A i j) ≤
          eps / 2 :=
      elementwiseTruncate_rect_error_frobNormRect_le_half A (le_of_lt heps) hmn
    have hfl :=
      fl_elementwiseTruncatedTraceResidual_rectOpNorm2Le_of_truncated
        fp tau s A samples (beta := eps / 2) (alpha := eps / 2)
        B hB_nonneg
        (by simpa [Ahat] using hExact)
        hPoint
        (by simpa [tau] using hTruncFrob)
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
      (eps + frobNormRect B)
    convert hfl using 1
    ring
  exact hInter'.trans
    (by
      simpa [P, Exact, Good, Fl, tau, Ahat, B, tau', Ahat', B'] using
        P.eventProb_mono hsubset)

/-- The zero-initialized literal Algorithm 1 FP perturbation budget is bounded
by a scalar constant when all nonzero entries of `A` are bounded below in
absolute value by `alpha`.

This is the nontruncated analogue of the explicit budget expansion used for the
hard-thresholded route.  Zero entries cause no difficulty on the sampler's
positive-probability support: they are never hit, and Lean's total division
convention makes the displayed budget term zero at those entries. -/
theorem sqMagTraceErrorBudget_zero_init_le_const_of_entry_abs_ge
    (fp : FPModel) {m n s : ℕ} {alpha : ℝ}
    (halpha : 0 < alpha) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma1 : gammaValid fp (s + 1)) :
    ∀ i j,
      sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j ≤
        (frobNormSqRect A / alpha) * gamma fp (s + 1) := by
  classical
  intro i j
  by_cases hAij : A i j = 0
  · have hC_nonneg :
        0 ≤ (frobNormSqRect A / alpha) * gamma fp (s + 1) :=
      mul_nonneg
        (div_nonneg (frobNormSqRect_nonneg A) (le_of_lt halpha))
        (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, hAij] using hC_nonneg
  · have habs_pos : 0 < |A i j| := abs_pos.mpr hAij
    have halpha_le : alpha ≤ |A i j| := hentry i j hAij
    have hinv :
        |frobNormSqRect A / ((s : ℝ) * A i j)| ≤
          frobNormSqRect A / ((s : ℝ) * alpha) := by
      have hnum_nonneg : 0 ≤ frobNormSqRect A := frobNormSqRect_nonneg A
      have hden_abs :
          |(s : ℝ) * A i j| = (s : ℝ) * |A i j| := by
        rw [abs_mul, abs_of_pos hs]
      have hden_pos : 0 < (s : ℝ) * |A i j| :=
        mul_pos hs habs_pos
      have hden_alpha_pos : 0 < (s : ℝ) * alpha :=
        mul_pos hs halpha
      have hden_le : (s : ℝ) * alpha ≤ (s : ℝ) * |A i j| :=
        mul_le_mul_of_nonneg_left halpha_le (le_of_lt hs)
      calc
        |frobNormSqRect A / ((s : ℝ) * A i j)|
            = frobNormSqRect A / ((s : ℝ) * |A i j|) := by
                rw [abs_div, abs_of_nonneg hnum_nonneg, hden_abs]
        _ ≤ frobNormSqRect A / ((s : ℝ) * alpha) :=
              div_le_div_of_nonneg_left hnum_nonneg hden_alpha_pos hden_le
    have hbase :
        (s : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| ≤
          frobNormSqRect A / alpha := by
      have hmul :=
        mul_le_mul_of_nonneg_left hinv (le_of_lt hs)
      have hcancel :
          (s : ℝ) * (frobNormSqRect A / ((s : ℝ) * alpha)) =
            frobNormSqRect A / alpha := by
        field_simp [hs.ne', halpha.ne']
      simpa [hcancel] using hmul
    have hterm :
        (s : ℝ) *
            |frobNormSqRect A / ((s : ℝ) * A i j)| *
            gamma fp (s + 1) ≤
          (frobNormSqRect A / alpha) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hbase (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, hAij] using hterm

/-- Square-matrix Frobenius expansion of the literal Algorithm 1 gamma budget
under an explicit nonzero-entry lower bound `alpha`.

The conclusion contains no hidden budget matrix:
`||B||_F <= n * (||A||_F^2 / alpha) * gamma_{s+1}`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_le_const_square_of_entry_abs_ge
    (fp : FPModel) {n s : ℕ} {alpha : ℝ}
    (halpha : 0 < alpha) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j) ≤
      (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1)) := by
  classical
  let C : ℝ := (frobNormSqRect A / alpha) * gamma fp (s + 1)
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg
      (div_nonneg (frobNormSqRect_nonneg A) (le_of_lt halpha))
      (gamma_nonneg fp hgamma1)
  calc
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j)
        ≤ frobNormRect (fun _i : Fin n => fun _j : Fin n => C) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact hC_nonneg
          · intro i j
            have hnonneg :
                0 ≤ sqMagTraceErrorBudget fp s s A
                    (fun _ _ => 0) i j :=
              sqMagTraceErrorBudget_nonneg fp s s A
                (fun _ _ => 0) i j hgamma hgamma1
            have hle :
                sqMagTraceErrorBudget fp s s A
                    (fun _ _ => 0) i j ≤ C := by
              simpa [C] using
                sqMagTraceErrorBudget_zero_init_le_const_of_entry_abs_ge
                  fp halpha hs A hentry hgamma1 i j
            simpa [abs_of_nonneg hnonneg] using hle
    _ = (n : ℝ) * C := frobNormRect_const_square C hC_nonneg
    _ = (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1)) := by
          simp [C]

/-- The zero-initialized literal Algorithm 1 FP perturbation budget is bounded
entrywise by the input-dependent reciprocal-entry contribution radius.

The right hand side is completely determined by the exact input matrix, the
sample count, and the local floating-point `gamma` factor.  No lower bound on
the nonzero entries is assumed; very small nonzero entries are charged through
`elementwiseLiteralContributionRadius`. -/
theorem sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
    (fp : FPModel) {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    ∀ i j,
      sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j ≤
        ((s : ℝ) * elementwiseLiteralContributionRadius s A) *
          gamma fp (s + 1) := by
  classical
  intro i j
  let Rlit : ℝ := elementwiseLiteralContributionRadius s A
  have hRlit_nonneg : 0 ≤ Rlit := by
    simpa [Rlit] using elementwiseLiteralContributionRadius_nonneg hs A
  have hgamma_nonneg : 0 ≤ gamma fp (s + 1) :=
    gamma_nonneg fp hgamma1
  have hC_nonneg :
      0 ≤ ((s : ℝ) * Rlit) * gamma fp (s + 1) :=
    mul_nonneg
      (mul_nonneg (le_of_lt hs) hRlit_nonneg)
      hgamma_nonneg
  by_cases hAij : A i j = 0
  · simpa [sqMagTraceErrorBudget, hAij, Rlit] using hC_nonneg
  · have hsingle :
        frobNormSqRect A / ((s : ℝ) * |A i j|) ≤ Rlit := by
      have h :=
        literal_entry_contribution_le_elementwiseLiteralContributionRadius
          hs A i j
      simpa [hAij, Rlit] using h
    have hF_nonneg : 0 ≤ frobNormSqRect A := frobNormSqRect_nonneg A
    have habs :
        |frobNormSqRect A / ((s : ℝ) * A i j)| =
          frobNormSqRect A / ((s : ℝ) * |A i j|) := by
      rw [abs_div, abs_mul, abs_of_nonneg hF_nonneg,
        abs_of_pos hs]
    have hbase :
        (s : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| ≤
          (s : ℝ) * Rlit := by
      rw [habs]
      exact mul_le_mul_of_nonneg_left hsingle (le_of_lt hs)
    have hterm :
        (s : ℝ) * |frobNormSqRect A / ((s : ℝ) * A i j)| *
            gamma fp (s + 1) ≤
          ((s : ℝ) * Rlit) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hbase hgamma_nonneg
    simpa [sqMagTraceErrorBudget, hAij, Rlit] using hterm

/-- Rectangular Frobenius expansion of the literal Algorithm 1 gamma budget
using the input-dependent reciprocal-entry contribution radius.

The conclusion contains no hidden budget matrix:
`||B||_F <= sqrt(m*n) * (s * R_lit(A,s)) * gamma_{s+1}`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
    (fp : FPModel) {m n s : ℕ} (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j) ≤
      Real.sqrt ((m : ℝ) * (n : ℝ)) *
        (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
          gamma fp (s + 1)) := by
  classical
  let C : ℝ :=
    ((s : ℝ) * elementwiseLiteralContributionRadius s A) *
      gamma fp (s + 1)
  have hRlit_nonneg :
      0 ≤ elementwiseLiteralContributionRadius s A :=
    elementwiseLiteralContributionRadius_nonneg hs A
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg
      (mul_nonneg (le_of_lt hs) hRlit_nonneg)
      (gamma_nonneg fp hgamma1)
  have hentry :
      ∀ i j,
        |sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j| ≤ C := by
    intro i j
    have hnonneg :
        0 ≤ sqMagTraceErrorBudget fp s s A
            (fun _ _ => 0) i j :=
      sqMagTraceErrorBudget_nonneg fp s s A
        (fun _ _ => 0) i j hgamma hgamma1
    have hle :
        sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j ≤ C := by
      simpa [C] using
        sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
          fp hs A hgamma1 i j
    simpa [abs_of_nonneg hnonneg] using hle
  simpa [C] using
    frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
      (fun i j =>
        sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j)
      hC_nonneg hentry

/-- Literal Algorithm 1 floating-point spectral event with a scalar radius
expanded from the concrete local gamma budget.

The exact probability law is the squared-magnitude trace law for the exact
input.  The only floating-point term is the deterministic contribution of the
rounded sketch computation:
`sqrt(m*n) * (s * elementwiseLiteralContributionRadius s A) * gamma fp (s+1)`.
This is the implementation-facing scalar version of the literal support-radius
theorem above. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_scaled_radius_gamma_supportRadius
    (fp : FPModel) {m n s : ℕ} {theta δ : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (htheta : 0 < theta)
    (hdim : 0 < (m : ℝ) + (n : ℝ)) (hδ : 0 < δ) (hδ_le_one : δ ≤ 1)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let L : ℝ := elementwiseLiteralResidualSupportRadius s A
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    let V : ℝ := max (m : ℝ) (n : ℝ) *
      (frobNormSqRect A / (s : ℝ) ^ 2)
    let TraceB : ℝ := ((m : ℝ) + (n : ℝ)) *
      Real.exp ((s : ℝ) * (beta * V))
    let eps : ℝ := Real.log ((2 * TraceB) / δ) / theta
    let fpRad : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
      (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
        gamma fp (s + 1))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps + fpRad)} := by
  classical
  intro L beta V TraceB eps fpRad
  let P := sqMagTraceProbability (steps := s) A hden
  let Bmat : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
  have hProb :
      1 - δ ≤
        P.eventProb
          (algorithm1FlSpectralEvent fp s A
            (fun samples : ElementwiseTrace m n s => samples) eps Bmat) := by
    simpa [P, Bmat, L, beta, V, TraceB, eps] using
      sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_literal_scaled_radius_gamma_supportRadius
        (fp := fp) (m := m) (n := n) (s := s)
        (theta := theta) (δ := δ)
        hs A hden htheta hdim hδ hδ_le_one hgamma hgamma1
  have hB :
      frobNormRect Bmat ≤ fpRad := by
    simpa [Bmat, fpRad] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
        fp hs A hgamma hgamma1
  have hsubset :
      algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples) eps Bmat ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps + fpRad)} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Final literal Algorithm 1 FP support-radius theorem with no free
trace-MGF parameter.

The exact probability law is the literal squared-magnitude product law.  The
sample-size/radius hypothesis is the visible Bernstein denominator involving
the exact reciprocal-entry support radius `L` and summed variance proxy `W`.
All floating-point arithmetic in the rounded sketch is charged by the
displayed scalar `fpRad`; probability construction remains exact by project
convention. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_supportRadius
    (fp : FPModel) {m n s : ℕ} {δ r : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1))
    (hbudget :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    let fpRad : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
      (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
        gamma fp (s + 1))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (r + fpRad)} := by
  classical
  intro fpRad
  let P := sqMagTraceProbability (steps := s) A hden
  let Exact : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace m n s => samples) r
  let Good : Set (ElementwiseTrace m n s) :=
    {samples | elementwiseTracePositiveProb A samples}
  let Bmat : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    simpa [P, Exact] using
      sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_literalTraceResidual_ge_one_sub_delta_bernstein_denominator_two_thirds_supportRadius
        (m := m) (n := n) (s := s) (δ := δ) (r := r)
        hs A hden hdim hδ hδ_le_one hr hbudget
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb A hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hBnorm : frobNormRect Bmat ≤ fpRad := by
    simpa [Bmat, fpRad] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_le_literalContributionRadius
        fp hs A hgamma hgamma1
  have hsubset :
      Exact ∩ Good ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (r + fpRad)} := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    have hB_nonneg : ∀ i j, 0 ≤ Bmat i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s A (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s A
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s A
              (fun _ _ => 0) samples i j| ≤ Bmat i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb A samples := by
        simpa [Good] using hGood
      simpa [Bmat] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s A samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hfl :=
      fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
        fp s A samples Bmat hExact hB_nonneg hPoint
    exact rectOpNorm2Le_mono (by linarith) hfl
  exact hInter'.trans (P.eventProb_mono hsubset)

/-- Literal Algorithm 1 FP support-radius theorem with an explicit
nonzero-entry floor.

The exact sampling law is still the literal squared-magnitude law.  The
probability budget uses the readable support radius
`s^{-1}||A||_F + mn||A||_F^2/(s alpha)`, and the rounded-sketch arithmetic is
charged by
`sqrt(mn) * mn * (||A||_F^2/alpha) * gamma_{s+1}`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_entry_floor
    (fp : FPModel) {m n s : ℕ} {δ r alpha : ℝ}
    (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hdim : 0 < (m : ℝ) + (n : ℝ))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (hr : 0 < r)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1))
    (hbudget :
      let Lfloor : ℝ :=
        (1 / (s : ℝ)) * frobNormRect A +
          ((m : ℝ) * (n : ℝ)) *
            (frobNormSqRect A / ((s : ℝ) * alpha))
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * Lfloor * r)) :
    let fpRad : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
      ((((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha)) *
        gamma fp (s + 1))
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (r + fpRad)} := by
  classical
  intro fpRad
  let P := sqMagTraceProbability (steps := s) A hden
  let fpRadActual : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ)) *
    (((s : ℝ) * elementwiseLiteralContributionRadius s A) *
      gamma fp (s + 1))
  have hbudget_actual :
      let L : ℝ := elementwiseLiteralResidualSupportRadius s A
      let V : ℝ := max (m : ℝ) (n : ℝ) *
        (frobNormSqRect A / (s : ℝ) ^ 2)
      let W : ℝ := (s : ℝ) * V
      Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        r ^ 2 / (2 * W + (2 / 3) * L * r) :=
    algorithm1LiteralBernsteinDenominatorBudget_of_entry_floor
      hs A hden hdim hr halpha hentry hbudget
  have hProb :
      1 - δ ≤
        P.eventProb
          {samples : ElementwiseTrace m n s |
            rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
              (r + fpRadActual)} := by
    simpa [P, fpRadActual] using
      sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_literal_ge_one_sub_delta_bernstein_denominator_gamma_supportRadius
        (fp := fp) (m := m) (n := n) (s := s) (δ := δ) (r := r)
        hs A hden hdim hδ hδ_le_one hr hgamma hgamma1 hbudget_actual
  have hscaled :
      (s : ℝ) * elementwiseLiteralContributionRadius s A ≤
        ((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha) :=
    smul_elementwiseLiteralContributionRadius_le_of_entry_abs_ge
      halpha hs A hentry
  have hinner :
      ((s : ℝ) * elementwiseLiteralContributionRadius s A) *
          gamma fp (s + 1) ≤
        (((m : ℝ) * (n : ℝ)) * (frobNormSqRect A / alpha)) *
          gamma fp (s + 1) :=
    mul_le_mul_of_nonneg_right hscaled (gamma_nonneg fp hgamma1)
  have hfpRad : fpRadActual ≤ fpRad := by
    have hsqrt_nonneg :
        0 ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) := Real.sqrt_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hinner hsqrt_nonneg
    simpa [fpRadActual, fpRad, mul_assoc] using hmul
  have hsubset :
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
          (r + fpRadActual)} ⊆
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
          (r + fpRad)} := by
    intro samples hsamp
    exact rectOpNorm2Le_mono (by linarith) hsamp
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Faithful, nontruncated Algorithm 1 floating-point high-probability
operator event under the literal squared-magnitude distribution
`p_ij = A_ij^2 / ||A||_F^2`.

This corollary deliberately does not use hard-thresholding.  The exact
probability input is the repository's nonconditional Frobenius/Markov route,
so the sample condition is weaker than CACM equation (2)'s matrix Bernstein
bound.  The floating-point term is explicit: if every nonzero entry has
absolute value at least `alpha`, then the rounded residual radius is
`eps + n * (||A||_F^2 / alpha) * gamma_{s+1}`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_frob_explicit_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ alpha : ℝ}
    (hs : 0 < (s : ℝ)) (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (heps : 0 < eps)
    (hsample :
      (((n : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / eps ^ 2) ≤ δ)
    (halpha : 0 < alpha)
    (hentry : ∀ i j, A i j ≠ 0 → alpha ≤ |A i j|)
    (hgamma1 : gammaValid fp (s + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps + (n : ℝ) *
              ((frobNormSqRect A / alpha) * gamma fp (s + 1)))} := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let Exact : Set (ElementwiseTrace n n s) :=
    algorithm1ExactSpectralEvent s A
      (fun samples : ElementwiseTrace n n s => samples) eps
  let Good : Set (ElementwiseTrace n n s) :=
    {samples | elementwiseTracePositiveProb A samples}
  let Radius : ℝ :=
    eps + (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1))
  let Fl : Set (ElementwiseTrace n n s) :=
    {samples : ElementwiseTrace n n s |
      rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples) Radius}
  have hExactBase :
      1 -
        (((n : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / eps ^ 2) ≤
        P.eventProb Exact := by
    exact
      probability_algorithm1_exact_spectral_of_frob
        s A (fun samples : ElementwiseTrace n n s => samples) P
        (1 - (((n : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / eps ^ 2))
        eps
        (by
          simpa [P] using
            sqMagTraceProbability_eventProb_algorithm1ExactFrobEvent_ge_one_sub
              A hden hs eps heps)
  have hExactProb : 1 - δ ≤ P.eventProb Exact := by
    linarith
  have hGoodProb : P.eventProb Good = 1 := by
    simpa [P, Good] using
      sqMagTraceProbability_eventProb_elementwiseTracePositiveProb A hden
  have hInter :
      1 - (δ + 0) ≤ P.eventProb (Exact ∩ Good) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P Exact Good δ 0
      hExactProb (by simp [hGoodProb])
  have hInter' : 1 - δ ≤ P.eventProb (Exact ∩ Good) := by
    simpa using hInter
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hsubset : Exact ∩ Good ⊆ Fl := by
    intro samples hsamp
    rcases hsamp with ⟨hExact, hGood⟩
    let B : Fin n → Fin n → ℝ :=
      fun i j => sqMagTraceErrorBudget fp s s A (fun _ _ => 0) i j
    have hB_nonneg : ∀ i j, 0 ≤ B i j := by
      intro i j
      exact sqMagTraceErrorBudget_nonneg fp s s A (fun _ _ => 0) i j
        hgamma hgamma1
    have hPoint :
        ∀ i j,
          |fl_elementwiseTraceSketch fp s A
              (fun _ _ => 0) samples i j -
            elementwiseTraceSketch s A
              (fun _ _ => 0) samples i j| ≤ B i j := by
      intro i j
      have hgood_pos : elementwiseTracePositiveProb A samples := by
        simpa [Good] using hGood
      simpa [B] using
        fl_elementwiseTraceSketch_zero_init_sqMag_error_bound_of_positiveProb
          fp s A samples hs.ne' hgamma hgamma1 hgood_pos i j
    have hflBudget :
        rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
          (eps + frobNormRect B) :=
      fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
        fp s A samples B (by simpa [Exact] using hExact) hB_nonneg hPoint
    have hB_radius :
        frobNormRect B ≤
          (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1)) := by
      simpa [B] using
        frobNormRect_sqMagTraceErrorBudget_zero_init_le_const_square_of_entry_abs_ge
          fp halpha hs A hentry hgamma1
    have hRadius :
        eps + frobNormRect B ≤ Radius := by
      change eps + frobNormRect B ≤
        eps + (n : ℝ) * ((frobNormSqRect A / alpha) * gamma fp (s + 1))
      linarith
    exact rectOpNorm2Le_mono hRadius hflBudget
  exact hInter'.trans
    (by
      simpa [P, Exact, Good, Fl, Radius] using P.eventProb_mono hsubset)

/-- Literal Algorithm 1 exact spectral event at the source `n log n` sample
budget, for inputs where the Drineas--Zouzias threshold would not remove any
nonzero entry.

The probability law in the conclusion is the literal squared-magnitude law
`p_ij = A_ij^2 / ||A||_F^2`; no truncated matrix appears in the statement.
The explicit no-small-entry hypothesis is what allows the already-formalized
source-sharp truncated matrix-Bernstein theorem to specialize back to the
literal Algorithm 1 sampler. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_square
    {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 → eps / (2 * (n : ℝ)) ≤ |A i j|)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace n n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  have hprob :
      let tau' : ℝ := eps / (2 * (n : ℝ))
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau' A
      1 - δ ≤
        (sqMagTraceProbability (steps := s) Ahat hden_trunc).eventProb
          (algorithm1ExactTruncatedSpectralEvent tau' s A
            (fun samples : ElementwiseTrace n n s => samples) eps) :=
    sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_square
      (n := n) (s := s) (eps := eps) (δ := δ)
      hn hs A hden_trunc hδ hδ_le_one heps hsample
  let P := sqMagTraceProbability (steps := s) A hden
  have hprob' :
      1 - δ ≤ P.eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps) := by
    simpa [P, tau, htrunc, sqMagTraceProbability, sqMagSampleProbability]
      using hprob
  have hsubset :
      algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace n n s => samples) eps := by
    intro samples hsamp
    change rectOpNorm2Le (elementwiseTraceResidual s A samples) eps
    change rectOpNorm2Le
      (elementwiseTruncatedTraceResidual tau s A samples) eps at hsamp
    convert hsamp using 1
    ext i j
    simp [elementwiseTraceResidual, elementwiseTruncatedTraceResidual, htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- The zero-initialized truncated Algorithm 1 FP perturbation budget is
bounded by a scalar constant on each entry.  This is the local expansion of the
internal budget matrix used by the gamma-square corollary. -/
theorem sqMagTraceErrorBudget_zero_init_truncated_le_const
    (fp : FPModel) {m n s : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    ∀ i j,
      sqMagTraceErrorBudget fp s s (elementwiseTruncate tau A)
          (fun _ _ => 0) i j ≤
        (frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  intro i j
  by_cases hAij : Ahat i j = 0
  · have hC_nonneg :
        0 ≤ (frobNormSqRect Ahat / tau) * gamma fp (s + 1) :=
      mul_nonneg
        (div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt htau))
        (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, Ahat, hAij] using hC_nonneg
  · have hsample : elementwiseTruncate tau A i j ≠ 0 := by
      simpa [Ahat] using hAij
    have hcontrib :=
      elementwiseSampleContribution_truncated_entry_abs_le
        (m := m) (n := n) (tau := tau) htau (s := s) hs
        A (i, j) hsample i j
    have hinc :
        |elementwiseIncrement s Ahat i j| ≤
          frobNormSqRect Ahat / ((s : ℝ) * tau) := by
      simpa [Ahat, elementwiseSampleContribution] using hcontrib
    have hinc_eq :
        elementwiseIncrement s Ahat i j =
          frobNormSqRect Ahat / ((s : ℝ) * Ahat i j) :=
      elementwiseIncrement_sqMag_eq s Ahat i j hs.ne' hAij
    have habs :
        |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| ≤
          frobNormSqRect Ahat / ((s : ℝ) * tau) := by
      simpa [hinc_eq] using hinc
    have hbase :
        (s : ℝ) * |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| ≤
          frobNormSqRect Ahat / tau := by
      have hmul :=
        mul_le_mul_of_nonneg_left habs (le_of_lt hs)
      have hcancel :
          (s : ℝ) * (frobNormSqRect Ahat / ((s : ℝ) * tau)) =
            frobNormSqRect Ahat / tau := by
        field_simp [hs.ne', htau.ne']
      simpa [hcancel] using hmul
    have hterm :
        (s : ℝ) *
            |frobNormSqRect Ahat / ((s : ℝ) * Ahat i j)| *
            gamma fp (s + 1) ≤
          (frobNormSqRect Ahat / tau) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hbase (gamma_nonneg fp hgamma1)
    simpa [sqMagTraceErrorBudget, Ahat] using hterm

/-- Frobenius expansion of the internal Algorithm 1 gamma budget in the square
truncated route.  The budget matrix is bounded by the Frobenius norm of the
constant matrix with entry
`(||Ahat||_F^2 / tau) * gamma fp (s+1)`, hence by
`n * (||Ahat||_F^2 / tau) * gamma fp (s+1)`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square
    (fp : FPModel) {n s : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hs : 0 < (s : ℝ)) (A : Fin n → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s (elementwiseTruncate tau A)
            (fun _ _ => 0) i j) ≤
      (n : ℝ) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
  classical
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let C : ℝ := (frobNormSqRect Ahat / tau) * gamma fp (s + 1)
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg
      (div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt htau))
      (gamma_nonneg fp hgamma1)
  calc
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j)
        ≤ frobNormRect (fun _i : Fin n => fun _j : Fin n => C) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact hC_nonneg
          · intro i j
            have hnonneg :
                0 ≤ sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j :=
              sqMagTraceErrorBudget_nonneg fp s s Ahat
                (fun _ _ => 0) i j hgamma hgamma1
            have hle :
                sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j ≤ C := by
              simpa [Ahat, C] using
                sqMagTraceErrorBudget_zero_init_truncated_le_const
                  fp htau hs A hgamma1 i j
            simpa [abs_of_nonneg hnonneg] using hle
    _ = (n : ℝ) * C := frobNormRect_const_square C hC_nonneg
    _ = (n : ℝ) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
          simp [Ahat, C]

/-- Floating-point Algorithm 1 equation (2) corollary with the internal budget
matrix expanded to an explicit scalar radius depending on the truncated input.

The probability and sample-size hypotheses are exactly those of the
source-budget gamma-square theorem.  The conclusion no longer contains a
budget matrix: the FP additive term is
`n * (||Ahat||_F^2 / tau) * gamma fp (s+1)`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (n : ℝ) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin n → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          (algorithm1FlTruncatedSpectralEvent fp tau s A
            (fun samples : ElementwiseTrace n n s => samples) eps B) := by
    simpa [P, tau, Ahat, B] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_square
        (fp := fp) (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hB :
      frobNormRect B ≤
        (n : ℝ) * ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) := by
    simpa [B, Ahat] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_square
        fp htau hs A hgamma1
  have hsubset :
      algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace n n s => samples) eps B ⊆
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (n : ℝ) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Source-only floating-point Algorithm 1 equation (2) corollary.

This is the PDF-facing version of the previous theorem.  For the Drineas--
Zouzias threshold `tau = eps/(2n)`, hard-thresholding gives
`||Ahat||_F <= ||A||_F`, so the additive FP term is bounded explicitly by
`2*n^2*||A||_F^2*gamma fp (s+1)/eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate (eps / (2 * (n : ℝ))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * (n : ℝ))
    let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          {samples : ElementwiseTrace n n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
              (eps +
                (n : ℝ) *
                  ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    simpa [P, tau, Ahat] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_square
        (fp := fp) (n := n) (s := s) (eps := eps) (δ := δ)
        hn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hFhat_le : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have hgamma_nonneg : 0 ≤ gamma fp (s + 1) :=
    gamma_nonneg fp hgamma1
  have hterm_le :
      (n : ℝ) * ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
        (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
          gamma fp (s + 1) := by
    have hdiv :
        frobNormSqRect Ahat / tau ≤ frobNormSqRect A / tau :=
      div_le_div_of_nonneg_right hFhat_le (le_of_lt htau)
    have hmul_gamma :
        (frobNormSqRect Ahat / tau) * gamma fp (s + 1) ≤
          (frobNormSqRect A / tau) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hdiv hgamma_nonneg
    have hmul_n :
        (n : ℝ) * ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
          (n : ℝ) * ((frobNormSqRect A / tau) * gamma fp (s + 1)) :=
      mul_le_mul_of_nonneg_left hmul_gamma (by positivity)
    have hrewrite :
        (n : ℝ) * ((frobNormSqRect A / tau) * gamma fp (s + 1)) =
          (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
            gamma fp (s + 1) := by
      dsimp [tau]
      field_simp [hn.ne', heps.ne']
    exact hmul_n.trans_eq hrewrite
  have hsubset :
      {samples : ElementwiseTrace n n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          (eps +
            (n : ℝ) *
              ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} ⊆
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Frobenius expansion of the internal Algorithm 1 gamma budget in the
rectangular truncated route.

The budget matrix is bounded by the rectangular Frobenius norm of the constant
matrix with entry `(||Ahat||_F^2/tau) * gamma fp (s+1)`, hence by
`sqrt(mn) * (||Ahat||_F^2/tau) * gamma fp (s+1)`. -/
theorem frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_rect
    (fp : FPModel) {m n s : ℕ} {tau : ℝ} (htau : 0 < tau)
    (hs : 0 < (s : ℝ)) (A : Fin m → Fin n → ℝ)
    (hgamma1 : gammaValid fp (s + 1)) :
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s (elementwiseTruncate tau A)
            (fun _ _ => 0) i j) ≤
      Real.sqrt ((m : ℝ) * (n : ℝ)) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let C : ℝ := (frobNormSqRect Ahat / tau) * gamma fp (s + 1)
  have hgamma : gammaValid fp s :=
    gammaValid_mono fp (Nat.le_succ s) hgamma1
  have hC_nonneg : 0 ≤ C := by
    exact mul_nonneg
      (div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt htau))
      (gamma_nonneg fp hgamma1)
  calc
    frobNormRect
        (fun i j =>
          sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j)
        ≤ frobNormRect (fun _i : Fin m => fun _j : Fin n => C) := by
          apply frobNormRect_le_of_entry_abs_le
          · intro _ _
            exact hC_nonneg
          · intro i j
            have hnonneg :
                0 ≤ sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j :=
              sqMagTraceErrorBudget_nonneg fp s s Ahat
                (fun _ _ => 0) i j hgamma hgamma1
            have hle :
                sqMagTraceErrorBudget fp s s Ahat
                    (fun _ _ => 0) i j ≤ C := by
              simpa [Ahat, C] using
                sqMagTraceErrorBudget_zero_init_truncated_le_const
                  fp htau hs A hgamma1 i j
            simpa [abs_of_nonneg hnonneg] using hle
    _ ≤ Real.sqrt ((m : ℝ) * (n : ℝ)) * C :=
          frobNormRect_le_sqrt_mul_nat_of_entry_abs_le
            (fun _i : Fin m => fun _j : Fin n => C) hC_nonneg
            (by
              intro _ _
              simp [abs_of_nonneg hC_nonneg])
    _ = Real.sqrt ((m : ℝ) * (n : ℝ)) *
        ((frobNormSqRect (elementwiseTruncate tau A) / tau) *
          gamma fp (s + 1)) := by
          simp [Ahat, C]

/-- Rectangular floating-point Algorithm 1 corollary with the internal budget
matrix expanded to a scalar radius depending on the truncated input. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              Real.sqrt ((m : ℝ) * (n : ℝ)) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let B : Fin m → Fin n → ℝ :=
    fun i j => sqMagTraceErrorBudget fp s s Ahat (fun _ _ => 0) i j
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          (algorithm1FlTruncatedSpectralEvent fp tau s A
            (fun samples : ElementwiseTrace m n s => samples) eps B) := by
    simpa [P, tau, Ahat, B] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_gamma_rect
        (fp := fp) (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hB :
      frobNormRect B ≤
        Real.sqrt ((m : ℝ) * (n : ℝ)) *
          ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) := by
    simpa [B, Ahat] using
      frobNormRect_sqMagTraceErrorBudget_zero_init_truncated_le_const_rect
        fp htau hs A hgamma1
  have hsubset :
      algorithm1FlTruncatedSpectralEvent fp tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps B ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              Real.sqrt ((m : ℝ) * (n : ℝ)) *
                ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Source-only rectangular floating-point Algorithm 1 corollary.

For `tau = eps/(2*sqrt(mn))`, hard-thresholding gives
`||Ahat||_F <= ||A||_F`, so the additive FP term is bounded explicitly by
`2*m*n*||A||_F^2*gamma fp (s+1)/eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden :
      0 < sqMagProbDen
        (elementwiseTruncate
          (eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))) A))
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
    let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
    1 - δ ≤
      (sqMagTraceProbability (steps := s) Ahat hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
  let tau : ℝ := eps / (2 * R)
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  intro tau' Ahat'
  have hR_pos : 0 < R := by
    dsimp [R]
    exact Real.sqrt_pos.mpr hmn
  have htau : 0 < tau := by
    dsimp [tau]
    positivity
  have hProb :
      1 - δ ≤
        P.eventProb
          {samples : ElementwiseTrace m n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
              (eps +
                Real.sqrt ((m : ℝ) * (n : ℝ)) *
                  ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} := by
    simpa [P, tau, Ahat, R] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_gamma_rect
        (fp := fp) (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden hδ hδ_le_one heps hsample hgamma hgamma1
  have hFhat_le : frobNormSqRect Ahat ≤ frobNormSqRect A := by
    simpa [Ahat, tau] using frobNormSqRect_elementwiseTruncate_le tau A
  have hgamma_nonneg : 0 ≤ gamma fp (s + 1) :=
    gamma_nonneg fp hgamma1
  have hterm_le :
      Real.sqrt ((m : ℝ) * (n : ℝ)) *
          ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
        (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
          gamma fp (s + 1) := by
    have hdiv :
        frobNormSqRect Ahat / tau ≤ frobNormSqRect A / tau :=
      div_le_div_of_nonneg_right hFhat_le (le_of_lt htau)
    have hmul_gamma :
        (frobNormSqRect Ahat / tau) * gamma fp (s + 1) ≤
          (frobNormSqRect A / tau) * gamma fp (s + 1) :=
      mul_le_mul_of_nonneg_right hdiv hgamma_nonneg
    have hmul_R :
        Real.sqrt ((m : ℝ) * (n : ℝ)) *
            ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)) ≤
          Real.sqrt ((m : ℝ) * (n : ℝ)) *
            ((frobNormSqRect A / tau) * gamma fp (s + 1)) :=
      mul_le_mul_of_nonneg_left hmul_gamma (le_of_lt hR_pos)
    have hrewrite :
        Real.sqrt ((m : ℝ) * (n : ℝ)) *
            ((frobNormSqRect A / tau) * gamma fp (s + 1)) =
          (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
            gamma fp (s + 1) := by
      have hR_sq :
          (Real.sqrt ((m : ℝ) * (n : ℝ))) ^ 2 = (m : ℝ) * (n : ℝ) :=
        Real.sq_sqrt (le_of_lt hmn)
      dsimp [tau, R]
      field_simp [hR_pos.ne', heps.ne']
      rw [hR_sq]
    exact hmul_R.trans_eq hrewrite
  have hsubset :
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          (eps +
            Real.sqrt ((m : ℝ) * (n : ℝ)) *
              ((frobNormSqRect Ahat / tau) * gamma fp (s + 1)))} ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            (eps +
              (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
    intro samples h
    exact rectOpNorm2Le_mono (by linarith) h
  exact hProb.trans (P.eventProb_mono hsubset)

/-- Literal rectangular Algorithm 1 exact spectral event at the rectangular
source sample budget, for inputs where the rectangular source threshold would
not remove any nonzero entry.

The probability law in the conclusion is the literal squared-magnitude law
`p_ij = A_ij^2 / ||A||_F^2`; no truncated matrix appears in the statement.
The explicit no-small-entry hypothesis proves that the rectangular
hard-thresholding parameter `eps/(2*sqrt(m*n))` acts as the identity on `A`. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_delta_source_sample_budget_no_small_entries_rect
    {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 →
        eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ))) ≤ |A i j|)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) eps) := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  let P := sqMagTraceProbability (steps := s) A hden
  have hprob :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (elementwiseTruncate tau A) hden_trunc).eventProb
          (algorithm1ExactTruncatedSpectralEvent tau s A
            (fun samples : ElementwiseTrace m n s => samples) eps) := by
    simpa [tau] using
      sqMagTraceProbability_eventProb_algorithm1ExactTruncatedSpectralEvent_ge_one_sub_delta_source_sample_budget_sharp_rect
        (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden_trunc hδ hδ_le_one heps hsample
  have hP_eq :
      sqMagTraceProbability (steps := s)
        (elementwiseTruncate tau A) hden_trunc = P := by
    ext samples
    simp [P, sqMagTraceProbability, htrunc]
  have hprob' :
      1 - δ ≤ P.eventProb
        (algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps) := by
    simpa [hP_eq] using hprob
  have hsubset :
      algorithm1ExactTruncatedSpectralEvent tau s A
          (fun samples : ElementwiseTrace m n s => samples) eps ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) eps := by
    intro samples hsamp
    change rectOpNorm2Le (elementwiseTraceResidual s A samples) eps
    change rectOpNorm2Le
      (elementwiseTruncatedTraceResidual tau s A samples) eps at hsamp
    convert hsamp using 1
    ext i j
    simp [elementwiseTraceResidual, elementwiseTruncatedTraceResidual, htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- Literal rectangular Algorithm 1 floating-point spectral event at the
rectangular source sample budget, for inputs where the rectangular source
threshold would not remove any nonzero entry.

The exact law is the literal squared-magnitude product law for `A`.  The
non-probability computation charged here is the rounded sampled-entry
rescaling, sketch accumulation, and residual formation; the FP additive radius
is the rectangular source-only gamma term
`2*m*n*||A||_F^2*gamma fp (s+1)/eps`. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_rect
    (fp : FPModel) {m n s : ℕ} {eps δ : ℝ}
    (hmn : 0 < (m : ℝ) * (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 →
        eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ))) ≤ |A i j|)
    (hsample :
      let M : ℝ := max (m : ℝ) (n : ℝ)
      let R : ℝ := Real.sqrt ((m : ℝ) * (n : ℝ))
      let C : ℝ := 2 * M + ((4 * Real.sqrt 2) / 3) * R
      4 * C * frobNormSqRect A *
          Real.log ((2 * ((m : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps +
              (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let tau : ℝ := eps / (2 * Real.sqrt ((m : ℝ) * (n : ℝ)))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  let P := sqMagTraceProbability (steps := s) A hden
  let Radius : ℝ :=
    eps + (2 * ((m : ℝ) * (n : ℝ)) * frobNormSqRect A / eps) *
      gamma fp (s + 1)
  have hprob :
      1 - δ ≤
        (sqMagTraceProbability (steps := s)
          (elementwiseTruncate tau A) hden_trunc).eventProb
          {samples : ElementwiseTrace m n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
              Radius} := by
    simpa [tau, Radius] using
      sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_rect
        (fp := fp) (m := m) (n := n) (s := s) (eps := eps) (δ := δ)
        hmn hs A hden_trunc hδ hδ_le_one heps hsample hgamma hgamma1
  have hP_eq :
      sqMagTraceProbability (steps := s)
        (elementwiseTruncate tau A) hden_trunc = P := by
    ext samples
    simp [P, sqMagTraceProbability, htrunc]
  have hprob' :
      1 - δ ≤ P.eventProb
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            Radius} := by
    simpa [hP_eq] using hprob
  have hsubset :
      {samples : ElementwiseTrace m n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          Radius} ⊆
        {samples : ElementwiseTrace m n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            Radius} := by
    intro samples hsamp
    change rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples) Radius
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples) Radius at hsamp
    convert hsamp using 1
    ext i j
    simp [fl_elementwiseTraceResidual, fl_elementwiseTruncatedTraceResidual,
      htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- Literal Algorithm 1 floating-point spectral event at the source `n log n`
sample budget, for inputs where the source threshold would not remove any
nonzero entry.

This is the source-rate counterpart to the Frobenius/Markov literal corollary.
The probability law in the statement is the literal squared-magnitude law
`p_ij = A_ij^2 / ||A||_F^2`.  The extra no-small-entry condition makes the
Drineas--Zouzias threshold `eps/(2n)` an identity operation on `A`; it also
exposes the necessary denominator control for the floating-point update. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralRadius_ge_one_sub_delta_source_sample_budget_no_small_entries_square
    (fp : FPModel) {n s : ℕ} {eps δ : ℝ}
    (hn : 0 < (n : ℝ)) (hs : 0 < (s : ℝ))
    (A : Fin n → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (hδ : 0 < δ) (hδ_le_one : δ ≤ 1) (heps : 0 < eps)
    (hentry :
      ∀ i j, A i j ≠ 0 → eps / (2 * (n : ℝ)) ≤ |A i j|)
    (hsample :
      14 * (n : ℝ) * frobNormSqRect A *
          Real.log ((2 * ((n : ℝ) + (n : ℝ))) / δ) ≤
        (s : ℝ) * eps ^ 2)
    (hgamma : gammaValid fp s) (hgamma1 : gammaValid fp (s + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            (eps +
              (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
                gamma fp (s + 1))} := by
  classical
  let tau : ℝ := eps / (2 * (n : ℝ))
  have htrunc : elementwiseTruncate tau A = A :=
    elementwiseTruncate_eq_self_of_forall_nonzero_entry_abs_ge
      (tau := tau) A (by simpa [tau] using hentry)
  have hden_trunc : 0 < sqMagProbDen (elementwiseTruncate tau A) := by
    simpa [htrunc] using hden
  let P := sqMagTraceProbability (steps := s) A hden
  let Radius : ℝ :=
    eps + (2 * (n : ℝ) ^ 2 * frobNormSqRect A / eps) *
      gamma fp (s + 1)
  have hprob :
      let tau' : ℝ := eps / (2 * (n : ℝ))
      let Ahat : Fin n → Fin n → ℝ := elementwiseTruncate tau' A
      1 - δ ≤
        (sqMagTraceProbability (steps := s) Ahat hden_trunc).eventProb
          {samples : ElementwiseTrace n n s |
            rectOpNorm2Le
              (fl_elementwiseTruncatedTraceResidual fp tau' s A samples)
              Radius} :=
    sqMagTraceProbability_eventProb_algorithm1FlTruncatedSpectralRadius_ge_one_sub_delta_source_sample_budget_explicit_gamma_square
      (fp := fp) (n := n) (s := s) (eps := eps) (δ := δ)
      hn hs A hden_trunc hδ hδ_le_one heps hsample hgamma hgamma1
  have hprob' :
      1 - δ ≤ P.eventProb
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le
            (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
            Radius} := by
    simpa [P, tau, htrunc, Radius, sqMagTraceProbability, sqMagSampleProbability]
      using hprob
  have hsubset :
      {samples : ElementwiseTrace n n s |
        rectOpNorm2Le
          (fl_elementwiseTruncatedTraceResidual fp tau s A samples)
          Radius} ⊆
        {samples : ElementwiseTrace n n s |
          rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples)
            Radius} := by
    intro samples hsamp
    change rectOpNorm2Le (fl_elementwiseTraceResidual fp s A samples) Radius
    change rectOpNorm2Le
      (fl_elementwiseTruncatedTraceResidual fp tau s A samples) Radius at hsamp
    convert hsamp using 1
    ext i j
    simp [fl_elementwiseTraceResidual, fl_elementwiseTruncatedTraceResidual,
      htrunc]
  exact hprob'.trans (P.eventProb_mono hsubset)

/-- If every self-adjoint dilation increment of the truncated residual is
    Loewner-bounded above by `L I`, then the full truncated residual dilation is
    Loewner-bounded above by `(s * L) I`.

This is a deterministic accumulation lemma for bounded-increment hypotheses.
It is intentionally weaker than a matrix Bernstein theorem: it proves a
probability-one bound at the accumulated worst-case scale, not a concentration
bound at the variance scale. -/
theorem truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound
    {m n s : ℕ} (tau : ℝ) (A : Fin m → Fin n → ℝ)
    (L : ℝ) (hs : (s : ℝ) ≠ 0) :
    truncatedDilationIncrementLoewnerBoundedEvent tau A L ⊆
      algorithm1ExactDilationUpperEvent s (elementwiseTruncate tau A)
        (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L) := by
  intro samples hBound z
  rw [finiteQuadraticForm_rectSelfAdjointDilation_elementwiseTraceResidual_eq_sum_sampleResidualIncrement
    (elementwiseTruncate tau A) samples hs z]
  calc
    (∑ t : Fin s,
        finiteQuadraticForm
          (rectSelfAdjointDilation
            (elementwiseSampleResidualIncrement s
              (elementwiseTruncate tau A) (samples t))) z)
        ≤ ∑ _t : Fin s,
            finiteQuadraticForm
              (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) z := by
          apply Finset.sum_le_sum
          intro t _
          exact (hBound t).1 z
    _ = finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => ((s : ℝ) * L) * finiteIdMatrix a b) z := by
          simp_rw [finiteQuadraticForm_smul_finiteIdMatrix]
          simp [mul_assoc]

/-- Under the truncated squared-magnitude product law, the exact truncated
    residual satisfies the accumulated one-sided dilation bound with
    probability one.

This theorem consumes the already-proved probability-one bounded-increment
side condition.  It is a weak deterministic consequence and is not advertised
as the CACM equation (2) matrix-concentration theorem. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (algorithm1ExactDilationUpperEvent s (elementwiseTruncate tau A)
        (fun samples : ElementwiseTrace m n s => samples)
        ((s : ℝ) *
          (Real.sqrt 2 *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Bound : Set (ElementwiseTrace m n s) :=
    truncatedDilationIncrementLoewnerBoundedEvent tau A L
  let Upper : Set (ElementwiseTrace m n s) :=
    algorithm1ExactDilationUpperEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L)
  have hBoundProb : P.eventProb Bound = 1 := by
    simpa [P, Ahat, L, Bound] using
      sqMagTraceProbability_eventProb_truncatedDilationIncrementLoewnerBoundedEvent_eq_one
        htau hs A hden
  have hsubset : Bound ⊆ Upper := by
    simpa [Ahat, L, Bound, Upper] using
      truncatedDilationIncrementLoewnerBoundedEvent_subset_exactDilationUpperEvent_sum_bound
        tau A L (ne_of_gt hs)
  have hmono : P.eventProb Bound ≤ P.eventProb Upper :=
    P.eventProb_mono hsubset
  have hge : 1 ≤ P.eventProb Upper := by
    linarith
  have hle : P.eventProb Upper ≤ 1 := P.eventProb_le_one Upper
  have hUpper : P.eventProb Upper = 1 := le_antisymm hle hge
  simpa [P, Ahat, L, Upper] using hUpper

/-- Probability-one rectangular spectral consequence of the accumulated
    truncated bounded-increment dilation bound.

This is still only a worst-case accumulated bound.  It helps audit the
bounded-increment layer, but it does not replace the missing
matrix-Bernstein/trace-MGF proof for CACM equation (2). -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_truncated_sum_bound_eq_one
    {m n s : ℕ} {tau : ℝ} (htau : 0 < tau) (hs : 0 < (s : ℝ))
    (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen (elementwiseTruncate tau A)) :
    (sqMagTraceProbability (steps := s) (elementwiseTruncate tau A) hden).eventProb
      (algorithm1ExactSpectralEvent s (elementwiseTruncate tau A)
        (fun samples : ElementwiseTrace m n s => samples)
        ((s : ℝ) *
          (Real.sqrt 2 *
            ((1 / (s : ℝ)) * frobNormRect (elementwiseTruncate tau A) +
              frobNormSqRect (elementwiseTruncate tau A) / ((s : ℝ) * tau))))) = 1 := by
  classical
  let Ahat : Fin m → Fin n → ℝ := elementwiseTruncate tau A
  let P := sqMagTraceProbability (steps := s) Ahat hden
  let L : ℝ :=
    Real.sqrt 2 *
      ((1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau))
  let Upper : Set (ElementwiseTrace m n s) :=
    algorithm1ExactDilationUpperEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L)
  let Spectral : Set (ElementwiseTrace m n s) :=
    algorithm1ExactSpectralEvent s Ahat
      (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L)
  have hinner_nonneg :
      0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat +
        frobNormSqRect Ahat / ((s : ℝ) * tau) := by
    have hfirst : 0 ≤ (1 / (s : ℝ)) * frobNormRect Ahat :=
      mul_nonneg (by positivity) (frobNormRect_nonneg Ahat)
    have hden_pos : 0 < (s : ℝ) * tau := mul_pos hs htau
    have hsecond : 0 ≤ frobNormSqRect Ahat / ((s : ℝ) * tau) :=
      div_nonneg (frobNormSqRect_nonneg Ahat) (le_of_lt hden_pos)
    exact add_nonneg hfirst hsecond
  have hL_nonneg : 0 ≤ L := by
    unfold L
    exact mul_nonneg (Real.sqrt_nonneg 2) hinner_nonneg
  have hε : 0 ≤ (s : ℝ) * L := mul_nonneg (le_of_lt hs) hL_nonneg
  have hUpperProb : P.eventProb Upper = 1 := by
    simpa [P, Ahat, L, Upper] using
      sqMagTraceProbability_eventProb_algorithm1ExactDilationUpperEvent_truncated_sum_bound_eq_one
        htau hs A hden
  have hsubset : Upper ⊆ Spectral := by
    simpa [Ahat, L, Upper, Spectral] using
      algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
        s Ahat (fun samples : ElementwiseTrace m n s => samples) ((s : ℝ) * L) hε
  have hmono : P.eventProb Upper ≤ P.eventProb Spectral :=
    P.eventProb_mono hsubset
  have hge : 1 ≤ P.eventProb Spectral := by
    linarith
  have hle : P.eventProb Spectral ≤ 1 := P.eventProb_le_one Spectral
  have hSpectral : P.eventProb Spectral = 1 := le_antisymm hle hge
  simpa [P, Ahat, L, Spectral] using hSpectral

/-- The eigenvalue upper event is exactly strong enough to produce the
    one-sided dilation Loewner event.  This is a deterministic vocabulary
    adapter, not a probability or concentration theorem. -/
theorem algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) :
    algorithm1ExactDilationEigenUpperEvent s A X ε ⊆
      algorithm1ExactDilationUpperEvent s A X ε := by
  intro ω hEigen
  exact
    (finiteLoewnerLe_smul_id_iff_finiteScalarUpperDiffEigenvalues_nonneg
      (rectSelfAdjointDilation (elementwiseTraceResidual s A (X ω)))
      (rectSelfAdjointDilation_symmetric
        (elementwiseTraceResidual s A (X ω)))
      ε).mpr hEigen

/-- An eigenvalue form of the one-sided dilation event implies the rectangular
    spectral event.  The probability of this eigenvalue event remains the
    missing matrix-concentration step. -/
theorem algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationEigenUpperEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  exact Set.Subset.trans
    (algorithm1ExactDilationEigenUpperEvent_subset_exactDilationUpperEvent
      s A X ε)
    (algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
      s A X ε hε)

/-- A squared dilation Loewner event implies the dilation operator event.
    This is a deterministic spectral-event adapter, not a concentration
    theorem. -/
theorem algorithm1ExactDilationSquareEvent_subset_exactDilationEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationSquareEvent s A X ε ⊆
      algorithm1ExactDilationEvent s A X ε := by
  intro ω hSq
  exact rectSelfAdjointDilation_opNorm2Le_of_square_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hε hSq

/-- A squared dilation Loewner event implies the rectangular spectral event.
    This is the event-level bridge for any future theorem proving the squared
    Loewner event with high probability. -/
theorem algorithm1ExactDilationSquareEvent_subset_exactSpectralEvent
    {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (hε : 0 ≤ ε) :
    algorithm1ExactDilationSquareEvent s A X ε ⊆
      algorithm1ExactSpectralEvent s A X ε := by
  intro ω hSq
  exact rectOpNorm2Le_of_selfAdjointDilation_square_loewnerLe_scalar_id
    (elementwiseTraceResidual s A (X ω)) hε hSq

/-- Probability transfer from a self-adjoint dilation residual event to the
    exact rectangular operator event. It does not prove the dilation
    concentration theorem; it only connects a future matrix-concentration
    theorem to the repository's rectangular Algorithm 1 target. -/
theorem probability_algorithm1_exact_spectral_of_dilation
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ)
    (hDilationProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationEvent_subset_exactSpectralEvent s A X ε))

/-- Probability transfer from a one-sided self-adjoint-dilation Loewner event to
    the exact rectangular operator event.  It does not prove the
    largest-eigenvalue concentration theorem; it records the deterministic
    adapter needed once that probability bound is available. -/
theorem probability_algorithm1_exact_spectral_of_dilation_upper
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hDilationUpperProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationUpperProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationUpperEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Probability transfer from the eigenvalue form of the one-sided
    self-adjoint-dilation event to the exact rectangular operator event.  The
    theorem deliberately assumes only the probability of the eigenvalue event;
    proving that probability from matrix concentration remains separate. -/
theorem probability_algorithm1_exact_spectral_of_dilation_eigen_upper
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hDilationEigenProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEigenUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationEigenProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Union-bound transfer from single-eigenvalue scalar events to the full
    dilation eigenvalue upper event.  This does not prove the scalar
    eigenvalue probabilities; it only combines them once supplied. -/
theorem probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ε : ℝ)
    (δ : (Fin m ⊕ Fin n) → ℝ)
    (hIndex :
      ∀ a : Fin m ⊕ Fin n,
        1 - δ a ≤
          Pr.eventProb
            (algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)) :
    1 - ∑ a : Fin m ⊕ Fin n, δ a ≤
      Pr.eventProb (algorithm1ExactDilationEigenUpperEvent s A X ε) := by
  classical
  simpa [algorithm1ExactDilationEigenUpperEvent,
    algorithm1ExactDilationEigenUpperIndexEvent] using
    (Pr.eventProb_forall_ge_one_sub_sum
      (fun a : Fin m ⊕ Fin n =>
        algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)
      δ hIndex)

/-- Union-bound transfer from single-eigenvalue scalar events all the way to
    the exact rectangular spectral event.  The scalar eigenvalue probability
    estimates remain separate concentration obligations. -/
theorem probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ε : ℝ) (hε : 0 ≤ ε)
    (δ : (Fin m ⊕ Fin n) → ℝ)
    (hIndex :
      ∀ a : Fin m ⊕ Fin n,
        1 - δ a ≤
          Pr.eventProb
            (algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)) :
    1 - ∑ a : Fin m ⊕ Fin n, δ a ≤
      Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans
    (probability_algorithm1_exact_dilation_eigen_upper_of_index_bounds
      s A X Pr ε δ hIndex)
    (Pr.eventProb_mono
      (algorithm1ExactDilationEigenUpperEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Probability transfer from a squared dilation Loewner event to the exact
    rectangular operator event.  It keeps the future concentration theorem's
    target explicit: the probability of the squared Loewner event must still be
    proved separately. -/
theorem probability_algorithm1_exact_spectral_of_dilation_square
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (hDilationSqProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationSquareEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε) := by
  exact le_trans hDilationSqProb
    (Pr.eventProb_mono
      (algorithm1ExactDilationSquareEvent_subset_exactSpectralEvent
        s A X ε hε))

/-- Covering-net support theorem for Algorithm 1 exact residuals.

For a supplied finite unit-ball cover `net` at radius `ρ`, the fixed-vector
Markov theorem on the net plus the Frobenius residual Markov theorem imply an
operator-2 event with budget `η + L * ρ`.  This is still weaker than CACM
equation (2): the theorem assumes a concrete cover and uses Markov/Frobenius
control rather than proving a Bernstein/Khintchine spectral tail. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_cover
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (net : ι → Fin n → ℝ) (ρ η L : ℝ)
    (hcover : rectUnitBallCover net ρ) (hη : 0 < η) (hL : 0 < L) :
    1 -
      ((∑ a : ι,
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq (net a)) / η ^ 2) +
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / L ^ 2)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (η + L * ρ)) := by
  classical
  let P := sqMagTraceProbability (steps := s) A hden
  let δNet : ℝ :=
    ∑ a : ι,
      (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
        vecNorm2Sq (net a)) / η ^ 2
  let δFrob : ℝ :=
    ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / L ^ 2
  let E : Set (ElementwiseTrace m n s) :=
    {samples : ElementwiseTrace m n s |
      ∀ a : ι,
        vecNorm2
          (rectMatMulVec (elementwiseTraceResidual s A samples) (net a)) ≤ η}
  let F : Set (ElementwiseTrace m n s) :=
    algorithm1ExactFrobEvent s A
      (fun samples : ElementwiseTrace m n s => samples) L
  have hE : 1 - δNet ≤ P.eventProb E := by
    simpa [P, E, δNet] using
      sqMagTraceProbability_eventProb_forall_vecNorm2_rectMatMulVec_elementwiseTraceResidual_le_ge_one_sub_sum
        A hden hs net (fun _a : ι => η) (fun _a => hη)
  have hF : 1 - δFrob ≤ P.eventProb F := by
    simpa [P, F, δFrob] using
      sqMagTraceProbability_eventProb_algorithm1ExactFrobEvent_ge_one_sub
        A hden hs L hL
  have hinter :
      1 - (δNet + δFrob) ≤ P.eventProb (E ∩ F) :=
    FiniteProbability.eventProb_inter_ge_one_sub_add P E F δNet δFrob hE hF
  have hsubset :
      E ∩ F ⊆
        algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (η + L * ρ) := by
    intro samples hsamples
    rcases hsamples with ⟨hnet, hFrob⟩
    exact rectOpNorm2Le_of_unit_ball_cover
      (elementwiseTraceResidual s A samples) net hcover hnet hFrob
  exact le_trans hinter (FiniteProbability.eventProb_mono P hsubset)

/-- Event inclusion form of the deterministic spectral transfer. -/
theorem algorithm1ExactSpectralEvent_subset_flSpectralEvent
    (fp : FPModel) {Ω : Type*} {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j) :
    algorithm1ExactSpectralEvent s A X ε ⊆
      algorithm1FlSpectralEvent fp s A X ε B := by
  intro ω hExact
  exact fl_elementwiseTraceResidual_rectOpNorm2Le_of_exact
    fp s A (X ω) B hExact hB_nonneg (hEntry ω)

/-- Probability transfer for Algorithm 1 spectral residuals.

If an exact spectral event has probability at least `ρ`, then the corresponding
floating-point spectral event has probability at least `ρ`, provided the
entrywise perturbation budget holds for every outcome.  The theorem transfers
probability mass; it does not prove the exact spectral concentration event. -/
theorem probability_algorithm1_fl_spectral_of_exact_spectral
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hExactProb :
      ρ ≤ Pr.eventProb (algorithm1ExactSpectralEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact le_trans hExactProb
    (Pr.eventProb_mono
      (algorithm1ExactSpectralEvent_subset_flSpectralEvent
        fp s A X ε B hB_nonneg hEntry))

/-- Probability transfer from a self-adjoint dilation residual event all the
    way to the floating-point rectangular operator event.  This is the
    composition point for a future matrix Bernstein/Khintchine theorem stated
    on the dilation. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation
      s A X Pr ρ ε hDilationProb)

/-- Probability transfer from a one-sided self-adjoint-dilation Loewner event
    all the way to the floating-point rectangular operator event.  This is a
    deterministic FP transfer from a future largest-eigenvalue tail theorem, not
    the tail theorem itself. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_upper
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationUpperProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_upper
      s A X Pr ρ ε hε hDilationUpperProb)

/-- Floating-point probability transfer from an eigenvalue form of the
    one-sided self-adjoint-dilation event.  This theorem is an adapter from a
    future largest-eigenvalue tail bound to the existing FP residual event; it
    does not prove the tail bound itself. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationEigenProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationEigenUpperEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_eigen_upper
      s A X Pr ρ ε hε hDilationEigenProb)

/-- Floating-point probability transfer from supplied single-eigenvalue scalar
    probability bounds.  This combines the finite union-bound adapter, the
    eigenvalue-to-spectral event adapter, and the existing FP perturbation
    transfer; it does not prove the scalar eigenvalue concentration bounds. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_eigen_upper_index_bounds
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (δ : (Fin m ⊕ Fin n) → ℝ)
    (hIndex :
      ∀ a : Fin m ⊕ Fin n,
        1 - δ a ≤
          Pr.eventProb
            (algorithm1ExactDilationEigenUpperIndexEvent s A X ε a)) :
    1 - ∑ a : Fin m ⊕ Fin n, δ a ≤
      Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr (1 - ∑ a : Fin m ⊕ Fin n, δ a) ε B
    hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_eigen_upper_index_bounds
      s A X Pr ε hε δ hIndex)

/-- Probability transfer from a squared dilation Loewner event all the way to
    the floating-point rectangular operator event.  The concentration theorem
    for the squared Loewner event remains a separate obligation. -/
theorem probability_algorithm1_fl_spectral_of_exact_dilation_square
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (hε : 0 ≤ ε)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hDilationSqProb :
      ρ ≤ Pr.eventProb (algorithm1ExactDilationSquareEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_dilation_square
      s A X Pr ρ ε hε hDilationSqProb)

/-- Probability transfer from an exact Frobenius residual event all the way to
    the floating-point rectangular operator event.

This is a bridge theorem: it closes no concentration claim by itself. It says
that a proved exact Frobenius residual event, combined with an entrywise
floating-point perturbation budget, gives the corresponding floating-point
operator-2 event. -/
theorem probability_algorithm1_fl_spectral_of_exact_frob
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (X : Ω → ElementwiseTrace m n steps)
    (Pr : FiniteProbability Ω) (ρ ε : ℝ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ ω i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) (X ω) i j -
        elementwiseTraceSketch s A (fun _ _ => 0) (X ω) i j| ≤ B i j)
    (hFrobProb :
      ρ ≤ Pr.eventProb (algorithm1ExactFrobEvent s A X ε)) :
    ρ ≤ Pr.eventProb (algorithm1FlSpectralEvent fp s A X ε B) := by
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A X Pr ρ ε B hB_nonneg hEntry
    (probability_algorithm1_exact_spectral_of_frob s A X Pr ρ ε hFrobProb)

/-- Floating-point covering-net support theorem for Algorithm 1 residuals.

This composes the exact finite-cover theorem with the deterministic
floating-point spectral transfer.  It is explicit about the entrywise FP budget
`B`, and it remains a cover/Markov support result rather than the survey's
Bernstein/Khintchine equation (2). -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_cover
    (fp : FPModel) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (net : ι → Fin n → ℝ) (ρ η L : ℝ)
    (hcover : rectUnitBallCover net ρ) (hη : 0 < η) (hL : 0 < L)
    (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ (samples : ElementwiseTrace m n s) i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    1 -
      ((∑ a : ι,
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq (net a)) / η ^ 2) +
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / L ^ 2)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples)
          (η + L * ρ) B) := by
  let P := sqMagTraceProbability (steps := s) A hden
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A (fun samples : ElementwiseTrace m n s => samples) P
    (1 -
      ((∑ a : ι,
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) *
          vecNorm2Sq (net a)) / η ^ 2) +
        (((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / L ^ 2)))
    (η + L * ρ) B hB_nonneg hEntry
    (sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_cover
      A hden hs net ρ η L hcover hη hL)

/-- Nonconditional high-probability exact operator event obtained from the
    proved Frobenius residual second moment under the canonical Algorithm 1
    product trace law.

This is weaker than CACM equation (2), because it goes through a Frobenius
bound with an `(m * n)` factor instead of matrix Bernstein/Khintchine. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_frob
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) :
    1 -
      ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2 ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples) η) := by
  let P := sqMagTraceProbability (steps := s) A hden
  exact probability_algorithm1_exact_spectral_of_frob
    s A (fun samples : ElementwiseTrace m n s => samples) P
    (1 - ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2)
    η
    (sqMagTraceProbability_eventProb_algorithm1ExactFrobEvent_ge_one_sub
      A hden hs η hη)

/-- Nonconditional exact operator event obtained from simultaneous entrywise
    Markov bounds and a finite union bound.

The exact budget is `||τ * 1||_F`, the Frobenius norm of the constant matrix
with every entry equal to `τ`.  This theorem is useful as a scalar-entry
concentration bridge, but it is weaker than the CACM equation (2) spectral
matrix-concentration theorem. -/
theorem sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_entrywise
    {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (τ : ℝ) (hτ : 0 < τ) :
    1 - (((m * n : ℕ) : ℝ) *
        ((frobNormSqRect A / (s : ℝ)) / τ ^ 2)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1ExactSpectralEvent s A
          (fun samples : ElementwiseTrace m n s => samples)
          (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ))) := by
  let P := sqMagTraceProbability (steps := s) A hden
  exact probability_algorithm1_exact_spectral_of_entrywise_const
    s A (fun samples : ElementwiseTrace m n s => samples) P
    (1 - (((m * n : ℕ) : ℝ) *
        ((frobNormSqRect A / (s : ℝ)) / τ ^ 2)))
    τ (le_of_lt hτ)
    (sqMagTraceProbability_eventProb_algorithm1ExactEntrywiseEvent_ge_one_sub
      A hden hs τ hτ)

/-- Floating-point operator event obtained by composing the nonconditional
    exact Frobenius residual bound with the deterministic Algorithm 1
    floating-point perturbation transfer.

The only additional hypotheses are the usual nonnegative entrywise perturbation
budget and the proof that the rounded trace sketch is entrywise within that
budget for every trace. -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_frob
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (η : ℝ) (hη : 0 < η) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ (samples : ElementwiseTrace m n s) i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    1 -
      ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2 ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples) η B) := by
  let P := sqMagTraceProbability (steps := s) A hden
  exact probability_algorithm1_fl_spectral_of_exact_frob
    fp s A (fun samples : ElementwiseTrace m n s => samples) P
    (1 - ((m : ℝ) * (n : ℝ) * (frobNormSqRect A / (s : ℝ))) / η ^ 2)
    η B hB_nonneg hEntry
    (sqMagTraceProbability_eventProb_algorithm1ExactFrobEvent_ge_one_sub
      A hden hs η hη)

/-- Floating-point operator event obtained by composing the simultaneous
    entrywise/union-bound exact theorem with the deterministic Algorithm 1
    floating-point perturbation transfer.

Like the exact entrywise theorem, this is a scalar-entry route and remains
weaker than CACM equation (2). -/
theorem sqMagTraceProbability_eventProb_algorithm1FlSpectralEvent_ge_one_sub_entrywise
    (fp : FPModel) {m n s : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (hs : 0 < (s : ℝ))
    (τ : ℝ) (hτ : 0 < τ) (B : Fin m → Fin n → ℝ)
    (hB_nonneg : ∀ i j, 0 ≤ B i j)
    (hEntry : ∀ (samples : ElementwiseTrace m n s) i j,
      |fl_elementwiseTraceSketch fp s A (fun _ _ => 0) samples i j -
        elementwiseTraceSketch s A (fun _ _ => 0) samples i j| ≤ B i j) :
    1 - (((m * n : ℕ) : ℝ) *
        ((frobNormSqRect A / (s : ℝ)) / τ ^ 2)) ≤
      (sqMagTraceProbability (steps := s) A hden).eventProb
        (algorithm1FlSpectralEvent fp s A
          (fun samples : ElementwiseTrace m n s => samples)
          (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ)) B) := by
  let P := sqMagTraceProbability (steps := s) A hden
  exact probability_algorithm1_fl_spectral_of_exact_spectral
    fp s A (fun samples : ElementwiseTrace m n s => samples) P
    (1 - (((m * n : ℕ) : ℝ) *
        ((frobNormSqRect A / (s : ℝ)) / τ ^ 2)))
    (frobNormRect (fun _i : Fin m => fun _j : Fin n => τ))
    B hB_nonneg hEntry
    (sqMagTraceProbability_eventProb_algorithm1ExactSpectralEvent_ge_one_sub_entrywise
      A hden hs τ hτ)

end NumStability
