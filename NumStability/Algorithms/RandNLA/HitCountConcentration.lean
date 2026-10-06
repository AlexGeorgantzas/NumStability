-- Algorithms/RandNLA/HitCountConcentration.lean
--
-- Elementary finite-probability concentration for the Algorithm 1 hit counter.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FiniteProbability
import NumStability.Algorithms.RandNLA.ElementwiseSampling

namespace NumStability

open scoped BigOperators

/-!
## Concentration for the element-wise sampling hit counter

This file adds a small finite-probability layer around the deterministic
Algorithm 1 trace formalization from Drineas and Mahoney's CACM RandNLA
survey (https://dl.acm.org/doi/10.1145/2842602). It proves a marginal-only
Markov upper-tail
bound, a pairwise-independence Chebyshev bound around the mean, and Chernoff
upper-tail bounds for

`qᵢⱼ = hitCount samples i j`.

If every sample step hits `(i, j)` with marginal probability `pᵢⱼ`, then
`E qᵢⱼ = steps * pᵢⱼ`, so Markov gives

`Pr(qᵢⱼ ≤ Q) ≥ 1 - steps * pᵢⱼ / (Q + 1)`.

With pairwise independence of distinct hit indicators, Chebyshev also gives an
around-mean bound for `|qᵢⱼ - steps * pᵢⱼ|`. For the canonical independent
Algorithm 1 sampler with squared-magnitude probabilities, Lean constructs the
finite product trace law and proves the Chernoff MGF bound from that law. This
gives both a tunable fixed-parameter budget and the optimized exponent obtained
from `lam = log((Q+1)/(steps*pᵢⱼ))`. Specializing `pᵢⱼ` to `sqMagProb A i j`
then gives high-probability stability theorems by composing these counter
bounds with the deterministic stability transfer.
-/

-- ============================================================
-- Hit-count expectation and concentration
-- ============================================================

/-- Real-valued indicator of a trace step hitting `(i, j)`. -/
noncomputable def hitIndicator {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (t : Fin steps)
    (i : Fin m) (j : Fin n) : ℝ :=
  by
    classical
    exact if sampleHits samples t i j then 1 else 0

/-- The hit count is the sum of the stepwise hit indicators. -/
theorem hitCount_eq_sum_indicator {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    (hitCount samples i j : ℝ) =
      ∑ t : Fin steps, hitIndicator samples t i j := by
  classical
  induction steps with
  | zero =>
      simp [hitCount]
  | succ steps ih =>
      let samplePrefix : ElementwiseTrace m n steps :=
        fun t => samples t.castSucc
      by_cases hlast : sampleHits samples (Fin.last steps) i j
      · have hcount := hitCount_succ_last_of_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j + 1 at hcount
        calc
          (hitCount samples i j : ℝ)
              = (hitCount samplePrefix i j : ℝ) + 1 := by
                  exact_mod_cast hcount
          _ = (∑ t : Fin steps, hitIndicator samplePrefix t i j) + 1 := by
                  rw [ih samplePrefix]
          _ = ∑ t : Fin (steps + 1), hitIndicator samples t i j := by
                  have hlast_ind :
                      hitIndicator samples (Fin.last steps) i j = 1 := by
                    simp [hitIndicator, hlast]
                  have hprefix :
                      (∑ t : Fin steps, hitIndicator samplePrefix t i j) =
                        ∑ t : Fin steps, hitIndicator samples t.castSucc i j := by
                    apply Finset.sum_congr rfl
                    intro t _
                    rfl
                  rw [Fin.sum_univ_castSucc]
                  rw [← hprefix, hlast_ind]
      · have hcount := hitCount_succ_last_of_not_hit samples i j hlast
        change hitCount samples i j = hitCount samplePrefix i j at hcount
        calc
          (hitCount samples i j : ℝ)
              = (hitCount samplePrefix i j : ℝ) := by
                  exact_mod_cast hcount
          _ = ∑ t : Fin steps, hitIndicator samplePrefix t i j := by
                  rw [ih samplePrefix]
          _ = ∑ t : Fin (steps + 1), hitIndicator samples t i j := by
                  have hlast_ind :
                      hitIndicator samples (Fin.last steps) i j = 0 := by
                    simp [hitIndicator, hlast]
                  have hprefix :
                      (∑ t : Fin steps, hitIndicator samplePrefix t i j) =
                        ∑ t : Fin steps, hitIndicator samples t.castSucc i j := by
                    apply Finset.sum_congr rfl
                    intro t _
                    rfl
                  rw [Fin.sum_univ_castSucc]
                  rw [← hprefix, hlast_ind]
                  ring

/-- Expectation of the hit counter as the sum of marginal hit probabilities. -/
theorem expectationNat_hitCount_eq_sum_step_hit_probs {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) :
    P.expectationNat (fun ω => hitCount (X ω) i j) =
      ∑ t : Fin steps,
        P.eventProb {ω | sampleHits (X ω) t i j} := by
  classical
  unfold FiniteProbability.expectationNat FiniteProbability.eventProb
  calc
    ∑ ω, P.prob ω * (hitCount (X ω) i j : ℝ)
        = ∑ ω, P.prob ω *
            (∑ t : Fin steps, hitIndicator (X ω) t i j) := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [hitCount_eq_sum_indicator]
    _ = ∑ ω, ∑ t : Fin steps,
            P.prob ω * hitIndicator (X ω) t i j := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [Finset.mul_sum]
    _ = ∑ t : Fin steps, ∑ ω,
            P.prob ω * hitIndicator (X ω) t i j := by
            rw [Finset.sum_comm]
    _ = ∑ t : Fin steps, ∑ ω,
            if sampleHits (X ω) t i j then P.prob ω else 0 := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro ω _
            by_cases hhit : sampleHits (X ω) t i j <;>
              simp [hitIndicator, hhit]

/-- If every step has marginal hit probability `p`, the expected hit count is
    `steps * p`. No independence is needed for this expectation identity. -/
theorem expectationNat_hitCount_eq_steps_mul_hitProb {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p) :
    P.expectationNat (fun ω => hitCount (X ω) i j) = (steps : ℝ) * p := by
  rw [expectationNat_hitCount_eq_sum_step_hit_probs P X i j]
  simp [hmarginal, Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]

/-- Real-expectation version of `expectationNat_hitCount_eq_steps_mul_hitProb`. -/
theorem expectationReal_hitCount_eq_steps_mul_hitProb {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p) :
    P.expectationReal (fun ω => (hitCount (X ω) i j : ℝ)) =
      (steps : ℝ) * p := by
  simpa [FiniteProbability.expectationReal, FiniteProbability.expectationNat]
    using expectationNat_hitCount_eq_steps_mul_hitProb P X i j p hmarginal

/-- The expectation of a hit indicator is the hit probability of that step. -/
theorem expectationReal_hitIndicator_eq_eventProb {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (t : Fin steps)
    (i : Fin m) (j : Fin n) :
    P.expectationReal (fun ω => hitIndicator (X ω) t i j) =
      P.eventProb {ω | sampleHits (X ω) t i j} := by
  classical
  unfold FiniteProbability.expectationReal FiniteProbability.eventProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hhit : sampleHits (X ω) t i j <;>
    simp [hitIndicator, hhit]

/-- The expectation of a product of two hit indicators is the probability that
    both corresponding steps hit the entry. -/
theorem expectationReal_hitIndicator_mul_eq_eventProb_inter {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (t u : Fin steps)
    (i : Fin m) (j : Fin n) :
    P.expectationReal
      (fun ω => hitIndicator (X ω) t i j * hitIndicator (X ω) u i j) =
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} := by
  classical
  unfold FiniteProbability.expectationReal FiniteProbability.eventProb
  apply Finset.sum_congr rfl
  intro ω _
  by_cases ht : sampleHits (X ω) t i j
  · by_cases hu : sampleHits (X ω) u i j <;>
      simp [hitIndicator, ht, hu]
  · simp [hitIndicator, ht]

/-- Sum of a diagonal/off-diagonal constant kernel over `Fin steps × Fin steps`.
    This is the ordered-pair count used in the hit-count second-moment proof. -/
theorem sum_pairwise_diag_offdiag (steps : ℕ) (p : ℝ) :
    (∑ t : Fin steps, ∑ u : Fin steps, if u = t then p else p * p)
      = (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
  classical
  have hinner : ∀ t : Fin steps,
      (∑ u : Fin steps, if u = t then p else p * p)
        = p + ((steps - 1 : ℕ) : ℝ) * (p * p) := by
    intro t
    have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin steps))
      (fun u : Fin steps => if u = t then p else p * p) (Finset.mem_univ t)
    have herase :
        (∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t,
          (if x = t then p else p * p))
          = ∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t, p * p := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxt : x ≠ t := by
        simpa using (Finset.mem_erase.mp hx).1
      simp [hxt]
    have hcard : ((Finset.univ : Finset (Fin steps)).erase t).card =
        steps - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ t), Finset.card_univ,
        Fintype.card_fin]
    calc
      (∑ u : Fin steps, if u = t then p else p * p)
          = ∑ u ∈ (Finset.univ : Finset (Fin steps)),
              if u = t then p else p * p := by
              simp
      _ = (∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t,
              (if x = t then p else p * p)) +
            (if t = t then p else p * p) := by
              rw [← hsum]
      _ = (∑ x ∈ (Finset.univ : Finset (Fin steps)).erase t, p * p) + p := by
              rw [herase]
              simp
      _ = ((steps - 1 : ℕ) : ℝ) * (p * p) + p := by
              rw [Finset.sum_const, hcard]
              simp [nsmul_eq_mul]
      _ = p + ((steps - 1 : ℕ) : ℝ) * (p * p) := by ring
  calc
    (∑ t : Fin steps, ∑ u : Fin steps, if u = t then p else p * p)
        = ∑ t : Fin steps, (p + ((steps - 1 : ℕ) : ℝ) * (p * p)) := by
            apply Finset.sum_congr rfl
            intro t _
            exact hinner t
    _ = (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
            simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
            ring

/-- Under marginal probability `p` and pairwise independence of distinct hit
    indicators, the second moment of the hit counter is the usual ordered-pair
    count for Bernoulli sums. -/
theorem expectationReal_hitCount_sq_eq_pairwise {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} = p * p) :
    P.expectationReal (fun ω => ((hitCount (X ω) i j : ℝ) ^ 2)) =
      (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
  classical
  let I : Fin steps → Ω → ℝ := fun t ω => hitIndicator (X ω) t i j
  have hcount : ∀ ω, (hitCount (X ω) i j : ℝ) = ∑ t, I t ω := by
    intro ω
    exact hitCount_eq_sum_indicator (X ω) i j
  calc
    P.expectationReal (fun ω => ((hitCount (X ω) i j : ℝ) ^ 2))
        = P.expectationReal (fun ω => (∑ t, I t ω) ^ 2) := by
            unfold FiniteProbability.expectationReal
            apply Finset.sum_congr rfl
            intro ω _
            simp [hcount ω]
    _ = P.expectationReal
          (fun ω => ∑ t : Fin steps, ∑ u : Fin steps, I t ω * I u ω) := by
            unfold FiniteProbability.expectationReal
            apply Finset.sum_congr rfl
            intro ω _
            congr 1
            calc
              (∑ t : Fin steps, I t ω) ^ 2
                  = (∑ t : Fin steps, I t ω) *
                    (∑ u : Fin steps, I u ω) := by ring
              _ = ∑ t : Fin steps, ∑ u : Fin steps, I t ω * I u ω := by
                    rw [Finset.sum_mul]
                    simp_rw [Finset.mul_sum]
    _ = ∑ t : Fin steps, ∑ u : Fin steps,
          P.expectationReal (fun ω => I t ω * I u ω) := by
            rw [FiniteProbability.expectationReal_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [FiniteProbability.expectationReal_sum]
    _ = ∑ t : Fin steps, ∑ u : Fin steps, if u = t then p else p * p := by
            apply Finset.sum_congr rfl
            intro t _
            apply Finset.sum_congr rfl
            intro u _
            by_cases hut : u = t
            · subst u
              have hset :
                  {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) t i j} =
                    {ω | sampleHits (X ω) t i j} := by
                ext ω
                simp
              rw [expectationReal_hitIndicator_mul_eq_eventProb_inter]
              rw [hset, hmarginal t]
              simp
            · have htu : t ≠ u := by
                intro h
                exact hut h.symm
              rw [expectationReal_hitIndicator_mul_eq_eventProb_inter]
              simp [hut, hpairwise t u htu]
    _ = (steps : ℝ) * p +
        (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) :=
            sum_pairwise_diag_offdiag steps p

/-- Closed-form centered second moment for a pairwise-independent hit counter
    with `steps` trials and marginal hit probability `p`. -/
noncomputable def hitCountPairwiseCenteredMoment (steps : ℕ) (p : ℝ) : ℝ :=
  ((steps : ℝ) * p +
    (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p)) -
    ((steps : ℝ) * p) ^ 2

/-- The pairwise-independent hit-count centered second-moment expression is at
    most its mean when the marginal probability is nonnegative. -/
theorem hitCountPairwiseCenteredMoment_le_steps_mul
    (steps : ℕ) (p : ℝ) (hp : 0 ≤ p) :
    hitCountPairwiseCenteredMoment steps p ≤ (steps : ℝ) * p := by
  have hsteps : 0 ≤ (steps : ℝ) := by exact_mod_cast Nat.zero_le steps
  have hpred : ((steps - 1 : ℕ) : ℝ) ≤ (steps : ℝ) := by
    exact_mod_cast Nat.sub_le steps 1
  have hp2 : 0 ≤ p * p := mul_nonneg hp hp
  have hmul1 :
      (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) ≤
        (steps : ℝ) * (steps : ℝ) :=
    mul_le_mul_of_nonneg_left hpred hsteps
  have hmul :
      (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) ≤
        (steps : ℝ) * (steps : ℝ) * (p * p) :=
    mul_le_mul_of_nonneg_right hmul1 hp2
  unfold hitCountPairwiseCenteredMoment
  nlinarith [hmul]

/-- Centered second moment of the hit counter around its mean `steps * p`, under
    pairwise independence of distinct hit indicators.  The expression is kept in
    a form that is valid without splitting off the `steps = 0` case. -/
theorem expectationReal_hitCount_centered_sq_eq_pairwise {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} = p * p) :
    P.expectationReal
        (fun ω => ((hitCount (X ω) i j : ℝ) - (steps : ℝ) * p) ^ 2) =
      hitCountPairwiseCenteredMoment steps p := by
  classical
  let μ : ℝ := (steps : ℝ) * p
  let Q : Ω → ℝ := fun ω => (hitCount (X ω) i j : ℝ)
  have hmean : P.expectationReal Q = μ := by
    simpa [Q, μ] using
      expectationReal_hitCount_eq_steps_mul_hitProb P X i j p hmarginal
  have hsecond :
      P.expectationReal (fun ω => Q ω ^ 2) =
        (steps : ℝ) * p +
          (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p) := by
    simpa [Q] using
      expectationReal_hitCount_sq_eq_pairwise P X i j p hmarginal hpairwise
  calc
    P.expectationReal (fun ω => (Q ω - μ) ^ 2)
        = P.expectationReal
            (fun ω => Q ω ^ 2 - (2 * μ) * Q ω + μ ^ 2) := by
            unfold FiniteProbability.expectationReal
            apply Finset.sum_congr rfl
            intro ω _
            ring
    _ = P.expectationReal (fun ω => Q ω ^ 2) -
          P.expectationReal (fun ω => (2 * μ) * Q ω) +
          P.expectationReal (fun _ => μ ^ 2) := by
            rw [FiniteProbability.expectationReal_add,
              FiniteProbability.expectationReal_sub]
    _ = P.expectationReal (fun ω => Q ω ^ 2) - (2 * μ) * P.expectationReal Q +
          μ ^ 2 := by
            rw [FiniteProbability.expectationReal_const_mul,
              FiniteProbability.expectationReal_const]
    _ = ((steps : ℝ) * p +
          (steps : ℝ) * ((steps - 1 : ℕ) : ℝ) * (p * p)) -
          ((steps : ℝ) * p) ^ 2 := by
            rw [hmean, hsecond]
            simp [μ]
            ring
    _ = hitCountPairwiseCenteredMoment steps p := by
            rfl

/-- Markov concentration for the hit counter from a marginal hit probability
    `p`: with probability at least `1 - steps * p / (Q+1)`, the hit count is
    at most `Q`. -/
theorem hitCount_concentration_markov_of_marginal_hitProb {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p) :
    1 - (steps : ℝ) * p / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  have hmarkov :=
    FiniteProbability.eventProb_nat_le_ge_one_sub_expectationNat_div_succ
      P (fun ω => hitCount (X ω) i j) Q
  have hexpect :=
    expectationNat_hitCount_eq_steps_mul_hitProb P X i j p hmarginal
  simpa [hitCountAtMostEvent, hexpect] using hmarkov

/-- `1 - δ` form of the Markov concentration theorem. -/
theorem hitCount_concentrates_of_marginal_hitProb {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p δ : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hQ : (steps : ℝ) * p / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤ P.eventProb (hitCountAtMostEvent X i j Q) := by
  have hconc :=
    hitCount_concentration_markov_of_marginal_hitProb P X i j p Q hmarginal
  linarith

/-- Squared-magnitude specialization of the Markov concentration theorem for
    Algorithm 1: if each step hits `(i, j)` with marginal probability
    `pᵢⱼ = sqMagProb A i j`, then `qᵢⱼ ≤ Q` with probability at least
    `1 - steps * pᵢⱼ / (Q+1)`. -/
theorem hitCount_concentration_sqMag_markov {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j) :
    1 - (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb (hitCountAtMostEvent X i j Q) :=
  hitCount_concentration_markov_of_marginal_hitProb P X i j
    (sqMagProb A i j) Q hmarginal

/-- `1 - δ` squared-magnitude concentration theorem for the hit counter. -/
theorem hitCount_concentrates_sqMag {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (δ : ℝ) (Q : ℕ)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤ P.eventProb (hitCountAtMostEvent X i j Q) :=
  hitCount_concentrates_of_marginal_hitProb P X i j
    (sqMagProb A i j) δ Q hmarginal hQ

/-- Markov-selected natural budget:
    `Q = ceil(steps * p / δ)`.

With `δ > 0`, this choice ensures
`steps * p / (Q+1) ≤ δ`, hence a `1 - δ` Markov bound. -/
noncomputable def markovHitCountBudget (steps : ℕ) (p δ : ℝ) : ℕ :=
  Nat.ceil ((steps : ℝ) * p / δ)

/-- Squared-magnitude specialization of the Markov-selected hit-count budget. -/
noncomputable def sqMagMarkovHitCountBudget {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (δ : ℝ) : ℕ :=
  markovHitCountBudget steps (sqMagProb A i j) δ

theorem markovHitCountBudget_tail {steps : ℕ} {p δ : ℝ} (hδ : 0 < δ) :
    (steps : ℝ) * p /
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) ≤ δ := by
  have hceil :
      (steps : ℝ) * p / δ ≤ (markovHitCountBudget steps p δ : ℝ) := by
    unfold markovHitCountBudget
    exact Nat.le_ceil ((steps : ℝ) * p / δ)
  have hQle :
      (markovHitCountBudget steps p δ : ℝ) ≤
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ (markovHitCountBudget steps p δ)
  have hdiv_le :
      (steps : ℝ) * p / δ ≤
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) :=
    le_trans hceil hQle
  have hnum_le :
      (steps : ℝ) * p ≤
        (((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ) * δ := by
    rwa [div_le_iff₀ hδ] at hdiv_le
  have hden :
      0 < ((((markovHitCountBudget steps p δ) + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos (markovHitCountBudget steps p δ)
  rw [div_le_iff₀ hden]
  nlinarith

theorem sqMagMarkovHitCountBudget_tail {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    {δ : ℝ} (hδ : 0 < δ) :
    (steps : ℝ) * sqMagProb A i j /
        (((sqMagMarkovHitCountBudget steps A i j δ) + 1 : ℕ) : ℝ) ≤ δ := by
  simpa [sqMagMarkovHitCountBudget] using
    markovHitCountBudget_tail (steps := steps) (p := sqMagProb A i j) hδ

-- ============================================================
-- The canonical independent squared-magnitude trace distribution
-- ============================================================

/-- One-step real indicator for the sampled pair being `(i, j)`. -/
noncomputable def sampleHitIndicator {m n : ℕ}
    (x : ElementwiseSample m n) (i : Fin m) (j : Fin n) : ℝ :=
  if x.1 = i ∧ x.2 = j then 1 else 0

/-- Product probability mass of an Algorithm 1 trace when each step samples
    independently from the squared-magnitude probabilities. -/
noncomputable def sqMagTraceProbMass {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps) : ℝ :=
  ∏ t : Fin steps, sqMagProb A (samples t).1 (samples t).2

/-- The squared-magnitude probabilities sum to one over sampled pairs. -/
theorem sqMagProb_sum_samples_eq_one {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0) :
    (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2) = 1 := by
  change (∑ x : Fin m × Fin n, sqMagProb A x.1 x.2) = 1
  rw [← sqMagProb_sum_eq_one A hden]
  have h := Finset.sum_product
    (s := (Finset.univ : Finset (Fin m)))
    (t := (Finset.univ : Finset (Fin n)))
    (f := fun x : Fin m × Fin n => sqMagProb A x.1 x.2)
  simpa using h

theorem sqMagTraceProbMass_nonneg {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (samples : ElementwiseTrace m n steps) :
    0 ≤ sqMagTraceProbMass A samples := by
  unfold sqMagTraceProbMass
  exact Finset.prod_nonneg fun t _ =>
    sqMagProb_nonneg A hden (samples t).1 (samples t).2

theorem sqMagTraceProbMass_sum_eq_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples) = 1 := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n)))
      (f := fun _ x => sqMagProb A x.1 x.2)
  have hleft :
      (∏ _ : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (ElementwiseSample m n)),
          sqMagProb A x.1 x.2) = 1 := by
    simp [sqMagProb_sum_samples_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n))),
        ∏ i, sqMagProb A (x i).1 (x i).2)
        = ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples := by
    simp [sqMagTraceProbMass, ElementwiseTrace]
  rw [← hright, ← hprod]
  exact hleft

/-- Under the independent product trace law, a function of one sampled entry
    has expectation equal to its one-step entry expectation. -/
theorem sqMagTraceProbMass_marginal_one {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (t0 : Fin steps) (f : ElementwiseSample m n → ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples * f (samples t0)) =
      ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n)))
      (f := fun t x =>
        if t = t0 then sqMagProb A x.1 x.2 * f x
        else sqMagProb A x.1 x.2)
  have hleft :
      (∏ t : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (ElementwiseSample m n)),
          (if t = t0 then sqMagProb A x.1 x.2 * f x
          else sqMagProb A x.1 x.2)) =
        ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x := by
    simp [sqMagProb_sum_samples_eq_one A hden]
  have hright :
      (∑ x ∈ Fintype.piFinset
        (fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n))),
        ∏ i, (if i = t0 then sqMagProb A (x i).1 (x i).2 * f (x i)
          else sqMagProb A (x i).1 (x i).2))
        = ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples * f (samples t0) := by
    simp [sqMagTraceProbMass, ElementwiseTrace]
    apply Finset.sum_congr rfl
    intro x _
    have h1 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps =>
        if i = t0 then sqMagProb A (x i).1 (x i).2 * f (x i)
        else sqMagProb A (x i).1 (x i).2)
      (by intro h; simp at h)
    have h2 := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t0
      (fun i : Fin steps => sqMagProb A (x i).1 (x i).2)
      (by intro h; simp at h)
    simp at h1 h2
    rw [h1, h2]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t0},
          (if x_1 = t0 then sqMagProb A (x x_1).1 (x x_1).2 * f (x x_1)
          else sqMagProb A (x x_1).1 (x x_1).2)) =
        ∏ x_1 ∈ Finset.univ \ {t0}, sqMagProb A (x x_1).1 (x x_1).2 := by
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

/-- Product-law pointwise factorization for two distinct elementwise trace
    coordinates. -/
private theorem sqMagTraceProbMass_two_point_factor
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (t u : Fin steps) (htu : t ≠ u)
    (f g : ElementwiseSample m n → ℝ)
    (x : ElementwiseTrace m n steps) :
    (∏ r : Fin steps,
      if r = t then sqMagProb A (x r).1 (x r).2 * f (x r)
      else if r = u then sqMagProb A (x r).1 (x r).2 * g (x r)
      else sqMagProb A (x r).1 (x r).2) =
    (∏ r : Fin steps, sqMagProb A (x r).1 (x r).2) *
      f (x t) * g (x u) := by
  classical
  have hfactor : ∀ r : Fin steps,
      (if r = t then sqMagProb A (x r).1 (x r).2 * f (x r)
      else if r = u then sqMagProb A (x r).1 (x r).2 * g (x r)
      else sqMagProb A (x r).1 (x r).2) =
      sqMagProb A (x r).1 (x r).2 *
        (if r = t then f (x r) else if r = u then g (x r) else 1) := by
    intro r
    by_cases hrt : r = t
    · simp [hrt]
    · by_cases hru : r = u
      · simp [hru]
      · simp [hrt, hru]
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

/-- Two distinct coordinates of the independent elementwise trace have product
    expectation equal to the product of their one-step expectations. -/
theorem sqMagTraceProbMass_marginal_two_ne {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (t u : Fin steps) (htu : t ≠ u)
    (f g : ElementwiseSample m n → ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        (f (samples t) * g (samples u))) =
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) *
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x) := by
  classical
  have hprod :=
    Finset.prod_univ_sum
      (t := fun _ : Fin steps =>
        (Finset.univ : Finset (ElementwiseSample m n)))
      (f := fun r x =>
        if r = t then sqMagProb A x.1 x.2 * f x
        else if r = u then sqMagProb A x.1 x.2 * g x
        else sqMagProb A x.1 x.2)
  have hleft :
      (∏ r : Fin steps,
        ∑ x ∈ (Finset.univ : Finset (ElementwiseSample m n)),
          (if r = t then sqMagProb A x.1 x.2 * f x
          else if r = u then sqMagProb A x.1 x.2 * g x
          else sqMagProb A x.1 x.2)) =
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) *
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x) := by
    simp [sqMagProb_sum_samples_eq_one A hden]
    have hprod_t := Finset.prod_eq_mul_prod_diff_singleton
      (s := (Finset.univ : Finset (Fin steps))) t
      (fun r : Fin steps =>
        if r = t then
          ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
        else if r = u then
          ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
        else 1)
      (by intro h; simp at h)
    simp at hprod_t
    rw [hprod_t]
    have herase :
        (∏ x_1 ∈ Finset.univ \ {t},
          if x_1 = t then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
          else if x_1 = u then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
          else 1) =
          ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x := by
      rw [Finset.sdiff_singleton_eq_erase]
      have hprod_u := Finset.prod_eq_mul_prod_diff_singleton
        (s := ((Finset.univ : Finset (Fin steps)).erase t)) u
        (fun r : Fin steps =>
          if r = t then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
          else if r = u then
            ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
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
            if x_1 = t then
              ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x
            else if x_1 = u then
              ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * g x
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
        (fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n))),
        ∏ r, (if r = t then sqMagProb A (x r).1 (x r).2 * f (x r)
          else if r = u then sqMagProb A (x r).1 (x r).2 * g (x r)
          else sqMagProb A (x r).1 (x r).2))
        = ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples *
            (f (samples t) * g (samples u)) := by
    simp [sqMagTraceProbMass, ElementwiseTrace]
    apply Finset.sum_congr rfl
    intro x _
    simpa [mul_assoc] using
      sqMagTraceProbMass_two_point_factor A t u htu f g x
  rw [← hright, ← hprod]
  exact hleft

/-- The canonical finite probability space for Algorithm 1 traces with
    independent squared-magnitude samples at every step. -/
noncomputable def sqMagTraceProbability {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A) :
    FiniteProbability (ElementwiseTrace m n steps) where
  prob := sqMagTraceProbMass A
  prob_nonneg := sqMagTraceProbMass_nonneg A hden
  prob_sum := sqMagTraceProbMass_sum_eq_one A hden.ne'

/-- Expectation form of `sqMagTraceProbMass_marginal_one` for the canonical
    finite probability space.  This is the reusable product-law adapter for
    lifting one-step calculations to any fixed trace coordinate. -/
theorem sqMagTraceProbability_expectationReal_step_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t0 : Fin steps) (f : ElementwiseSample m n → ℝ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => f (samples t0)) =
      ∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x := by
  simpa [FiniteProbability.expectationReal, sqMagTraceProbability] using
    sqMagTraceProbMass_marginal_one A hden.ne' t0 f

/-- Trace-support predicate for Algorithm 1: every sampled entry has positive
    squared-magnitude probability.  Entries with zero probability carry zero
    mass under the canonical product law, so this is the event on which all
    sampled-entry divisions have nonzero denominators. -/
def elementwiseTracePositiveProb {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) : Prop :=
  ∀ t : Fin steps, 0 < sqMagProb A (samples t).1 (samples t).2

theorem sqMagTraceProbMass_eq_zero_of_exists_prob_zero {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (samples : ElementwiseTrace m n steps)
    (hzero :
      ∃ t : Fin steps, sqMagProb A (samples t).1 (samples t).2 = 0) :
    sqMagTraceProbMass A samples = 0 := by
  classical
  rcases hzero with ⟨t, ht⟩
  unfold sqMagTraceProbMass
  exact Finset.prod_eq_zero (Finset.mem_univ t) ht

/-- The independent Algorithm 1 elementwise sampler assigns probability one to
    traces whose sampled entries all have positive squared-magnitude
    probability. -/
theorem sqMagTraceProbability_eventProb_elementwiseTracePositiveProb
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples | elementwiseTracePositiveProb A samples} = 1 := by
  classical
  let P := sqMagTraceProbability (steps := steps) A hden
  let Good : Set (ElementwiseTrace m n steps) :=
    {samples | elementwiseTracePositiveProb A samples}
  have hcompl_zero : P.eventProb Goodᶜ = 0 := by
    unfold FiniteProbability.eventProb
    apply Finset.sum_eq_zero
    intro samples _
    by_cases hbad : samples ∈ Goodᶜ
    · have hnot_good : samples ∉ Good := by simpa using hbad
      have hexists :
          ∃ t : Fin steps,
            sqMagProb A (samples t).1 (samples t).2 = 0 := by
        by_contra hno
        have hgood : samples ∈ Good := by
          intro t
          have hne : sqMagProb A (samples t).1 (samples t).2 ≠ 0 := by
            intro hzero
            exact hno ⟨t, hzero⟩
          exact lt_of_le_of_ne
            (sqMagProb_nonneg A hden (samples t).1 (samples t).2)
            (Ne.symm hne)
        exact hnot_good hgood
      have hmass :=
        sqMagTraceProbMass_eq_zero_of_exists_prob_zero A samples hexists
      simp [P, Good, sqMagTraceProbability, hbad, hmass]
    · simp [hbad]
  have hsplit := P.eventProb_add_eventProb_compl Good
  rw [hcompl_zero] at hsplit
  linarith

/-- In the canonical independent trace law, each step hits entry `(i, j)` with
    probability `pᵢⱼ = sqMagProb A i j`. -/
theorem sqMagTraceProbability_eventProb_sampleHits {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t : Fin steps) (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples | sampleHits samples t i j} =
      sqMagProb A i j := by
  classical
  let f : ElementwiseSample m n → ℝ :=
    fun x => if x.1 = i ∧ x.2 = j then 1 else 0
  have hmarg :=
    sqMagTraceProbMass_marginal_one A hden.ne' t f
  have hleft :
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples | sampleHits samples t i j} =
        ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples * f (samples t) := by
    unfold FiniteProbability.eventProb sqMagTraceProbability f sampleHits
    apply Finset.sum_congr rfl
    intro samples _
    by_cases h : (samples t).1 = i ∧ (samples t).2 = j <;> simp [h]
  have hright :
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) =
        sqMagProb A i j := by
    rw [Finset.sum_eq_single (i, j)]
    · simp [f]
    · intro x _ hx
      have hnot : ¬ (x.1 = i ∧ x.2 = j) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [f, hnot]
    · intro hnot
      simp at hnot
  rw [hleft, hmarg, hright]

/-- In the canonical independent trace law, two distinct steps hit the same
    entry with product probability `pᵢⱼ^2`. -/
theorem sqMagTraceProbability_eventProb_sampleHits_pair_ne {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t u : Fin steps) (htu : t ≠ u) (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples | sampleHits samples t i j ∧ sampleHits samples u i j} =
      sqMagProb A i j * sqMagProb A i j := by
  classical
  let f : ElementwiseSample m n → ℝ :=
    fun x => if x.1 = i ∧ x.2 = j then 1 else 0
  have hsingle :
      (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) =
        sqMagProb A i j := by
    rw [Finset.sum_eq_single (i, j)]
    · simp [f]
    · intro x _ hx
      have hnot : ¬ (x.1 = i ∧ x.2 = j) := by
        intro h
        apply hx
        ext <;> simp [h.1, h.2]
      simp [f, hnot]
    · intro hnot
      simp at hnot
  have hE :
      (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples =>
          hitIndicator samples t i j * hitIndicator samples u i j) =
        sqMagProb A i j * sqMagProb A i j := by
    unfold FiniteProbability.expectationReal sqMagTraceProbability
    calc
      ∑ samples : ElementwiseTrace m n steps,
          sqMagTraceProbMass A samples *
            (hitIndicator samples t i j * hitIndicator samples u i j)
          = ∑ samples : ElementwiseTrace m n steps,
              sqMagTraceProbMass A samples *
                (f (samples t) * f (samples u)) := by
              apply Finset.sum_congr rfl
              intro samples _
              unfold f hitIndicator sampleHits
              by_cases ht : (samples t).1 = i ∧ (samples t).2 = j <;>
                by_cases hu : (samples u).1 = i ∧ (samples u).2 = j <;>
                  simp [ht, hu]
      _ = (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) *
            (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2 * f x) :=
              sqMagTraceProbMass_marginal_two_ne A hden.ne' t u htu f f
      _ = sqMagProb A i j * sqMagProb A i j := by
              rw [hsingle]
  rw [expectationReal_hitIndicator_mul_eq_eventProb_inter
    (sqMagTraceProbability (steps := steps) A hden)
    (fun samples : ElementwiseTrace m n steps => samples) t u i j] at hE
  exact hE

/-- Expected hit count under the canonical independent Algorithm 1 trace law. -/
theorem sqMagTraceProbability_expectationReal_hitCount_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => (hitCount samples i j : ℝ)) =
      (steps : ℝ) * sqMagProb A i j := by
  exact expectationReal_hitCount_eq_steps_mul_hitProb
    (sqMagTraceProbability (steps := steps) A hden)
    (fun samples => samples) i j (sqMagProb A i j)
    (fun t => sqMagTraceProbability_eventProb_sampleHits A hden t i j)

/-- Nonzero-entry unbiasedness for the exact Algorithm 1 trace estimator under
    the canonical independent squared-magnitude trace law.  The trace length
    `steps` and the update denominator `s` are linked by `steps = s`. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hsteps : steps = s)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
      A i j := by
  let P := sqMagTraceProbability (steps := steps) A hden
  let c : ℝ := frobNormSqRect A / ((s : ℝ) * A i j)
  have hpoint : ∀ samples : ElementwiseTrace m n steps,
      elementwiseTraceSketch s A (fun _ _ => 0) samples i j =
        (hitCount samples i j : ℝ) * c := by
    intro samples
    have h :=
      elementwiseTraceSketch_sqMag_eq s A (fun _ _ => 0) samples i j hs hAij
    simpa [c] using h
  have hE :
      P.expectationReal
        (fun samples : ElementwiseTrace m n steps =>
          elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
        P.expectationReal
          (fun samples : ElementwiseTrace m n steps =>
            (hitCount samples i j : ℝ) * c) := by
    apply Finset.sum_congr rfl
    intro samples _
    simp [hpoint samples]
  have hhit :
      P.expectationReal
        (fun samples : ElementwiseTrace m n steps => (hitCount samples i j : ℝ)) =
        (steps : ℝ) * sqMagProb A i j :=
    sqMagTraceProbability_expectationReal_hitCount_eq A hden i j
  have hconst :
      P.expectationReal
        (fun samples : ElementwiseTrace m n steps =>
          (hitCount samples i j : ℝ) * c) =
        ((steps : ℝ) * sqMagProb A i j) * c := by
    rw [FiniteProbability.expectationReal_mul_const, hhit]
  rw [hE, hconst]
  have hF : frobNormSqRect A ≠ 0 := by
    simpa [sqMagProbDen] using hden.ne'
  unfold c sqMagProb sqMagProbDen
  rw [hsteps]
  field_simp [hs, hAij]

/-- If the target entry is zero, the exact Algorithm 1 trace contribution at
    that entry is identically zero, independently of the sampled trace. -/
theorem elementwiseTraceSketch_zero_init_of_entry_eq_zero {m n steps : ℕ}
    (s : ℕ) (A : Fin m → Fin n → ℝ)
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hAij : A i j = 0) :
    elementwiseTraceSketch s A (fun _ _ => 0) samples i j = 0 := by
  classical
  have hinc : elementwiseIncrement s A i j = 0 := by
    simp [elementwiseIncrement, elementwiseIncrementWithProb, hAij]
  simp [elementwiseTraceSketch, elementwiseTraceContribution, hinc]

/-- Zero-entry unbiasedness for the exact Algorithm 1 trace estimator. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_zero_entry
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hAij : A i j = 0) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
      A i j := by
  classical
  unfold FiniteProbability.expectationReal
  simp [elementwiseTraceSketch_zero_init_of_entry_eq_zero s A, hAij]

/-- Entrywise unbiasedness for the exact Algorithm 1 trace estimator under the
    canonical independent squared-magnitude trace law.  The trace length
    `steps` and the algorithm parameter `s` are linked by `steps = s`. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (hsteps : steps = s)
    (hs : (s : ℝ) ≠ 0) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j) =
      A i j := by
  by_cases hAij_zero : A i j = 0
  · exact sqMagTraceProbability_expectationReal_elementwiseTraceSketch_zero_entry
      s A hden i j hAij_zero
  · exact sqMagTraceProbability_expectationReal_elementwiseTraceSketch_nonzero_entry
      s A hden i j hsteps hs hAij_zero

/-- Matrix form of Algorithm 1 unbiasedness for the exact trace estimator,
    stated entrywise as an equality of matrices. -/
theorem sqMagTraceProbability_expectationReal_elementwiseTraceSketch_matrix
    {m n steps : ℕ} (s : ℕ)
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (hsteps : steps = s) (hs : (s : ℝ) ≠ 0) :
    (fun i j =>
      (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples => elementwiseTraceSketch s A (fun _ _ => 0) samples i j)) =
      A := by
  funext i j
  exact sqMagTraceProbability_expectationReal_elementwiseTraceSketch_entry
    s A hden i j hsteps hs

/-- The one-step exponential moment for a single squared-magnitude sample. -/
theorem sqMag_sampleHitIndicator_exp_sum {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (i : Fin m) (j : Fin n) (lam : ℝ) :
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j)) =
      1 + sqMagProb A i j * (Real.exp lam - 1) := by
  classical
  let p : ElementwiseSample m n → ℝ := fun x => sqMagProb A x.1 x.2
  have hsum : (∑ x : ElementwiseSample m n, p x) = 1 := by
    simpa [p] using sqMagProb_sum_samples_eq_one A hden
  have hrewrite : ∀ x : ElementwiseSample m n,
      p x * Real.exp (lam * sampleHitIndicator x i j) =
        p x + (if x.1 = i ∧ x.2 = j then p x * (Real.exp lam - 1) else 0) := by
    intro x
    by_cases h : x.1 = i ∧ x.2 = j
    · simp [p, sampleHitIndicator, h]
      ring
    · simp [p, sampleHitIndicator, h]
  calc
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j))
        = ∑ x : ElementwiseSample m n,
            (p x + (if x.1 = i ∧ x.2 = j then p x * (Real.exp lam - 1) else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            simpa [p] using hrewrite x
    _ = (∑ x : ElementwiseSample m n, p x) +
          ∑ x : ElementwiseSample m n,
            (if x.1 = i ∧ x.2 = j then p x * (Real.exp lam - 1) else 0) := by
            rw [Finset.sum_add_distrib]
    _ = 1 + p (i, j) * (Real.exp lam - 1) := by
            rw [hsum]
            congr 1
            rw [Finset.sum_eq_single (i, j)]
            · simp [p]
            · intro b _ hb
              have hnot : ¬ (b.1 = i ∧ b.2 = j) := by
                intro hh
                apply hb
                ext <;> simp [hh.1, hh.2]
              simp [hnot]
            · intro hnot
              simp at hnot
    _ = 1 + sqMagProb A i j * (Real.exp lam - 1) := by
            simp [p]

/-- Exponential of a trace-sum of an arbitrary one-step scalar function
    factors into the product of one-step exponentials. -/
theorem exp_sum_stepFunction_eq_prod {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps)
    (f : ElementwiseSample m n → ℝ) (lam : ℝ) :
    Real.exp (lam * (∑ t : Fin steps, f (samples t))) =
      ∏ t : Fin steps, Real.exp (lam * f (samples t)) := by
  classical
  calc
    Real.exp (lam * (∑ t : Fin steps, f (samples t)))
        = Real.exp (∑ t : Fin steps, lam * f (samples t)) := by
            rw [Finset.mul_sum]
    _ = ∏ t : Fin steps, Real.exp (lam * f (samples t)) := by
            simpa using
              (Real.exp_sum (Finset.univ : Finset (Fin steps))
                (fun t => lam * f (samples t)))

/-- Product-law MGF factorization for an arbitrary one-step scalar statistic
    under the canonical independent squared-magnitude trace distribution. -/
theorem sqMagTraceProbMass_exp_sum_stepFunction_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ)
    (f : ElementwiseSample m n → ℝ) (lam : ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (∑ t : Fin steps, f (samples t)))) =
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
  classical
  calc
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (∑ t : Fin steps, f (samples t))))
        = ∑ samples : ElementwiseTrace m n steps,
            ∏ t : Fin steps,
              sqMagProb A (samples t).1 (samples t).2 *
                Real.exp (lam * f (samples t)) := by
            apply Finset.sum_congr rfl
            intro samples _
            rw [exp_sum_stepFunction_eq_prod samples f lam]
            simp [sqMagTraceProbMass, Finset.prod_mul_distrib]
    _ = ∏ t : Fin steps,
          ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * f x) := by
            have hprod :=
              Finset.prod_univ_sum
                (t := fun _ : Fin steps =>
                  (Finset.univ : Finset (ElementwiseSample m n)))
                (f := fun _ x =>
                  sqMagProb A x.1 x.2 * Real.exp (lam * f x))
            symm
            simpa [ElementwiseTrace] using hprod
    _ = (∑ x : ElementwiseSample m n,
          sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
            simp [Fintype.card_fin]

/-- Expectation form of the product-law MGF factorization for an arbitrary
    one-step scalar statistic. -/
theorem sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) (lam : ℝ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        Real.exp (lam * (∑ t : Fin steps, f (samples t)))) =
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
  simpa [sqMagTraceProbability, FiniteProbability.expectationReal,
    sqMagTraceProbMass] using
    sqMagTraceProbMass_exp_sum_stepFunction_eq
      (steps := steps) A f lam

/-- Exponential-Markov upper tail for a trace-sum of an arbitrary one-step
    scalar statistic, with the product-law MGF evaluated exactly. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples |
        T ≤ ∑ t : Fin steps, f (samples t)} ≤
      Real.exp (-(lam * T)) *
        (∑ x : ElementwiseSample m n,
          sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps := by
  let P := sqMagTraceProbability (steps := steps) A hden
  have hmarkov :=
    FiniteProbability.eventProb_real_ge_le_exp_mul_mgf
      P (fun samples => ∑ t : Fin steps, f (samples t)) (T := T)
      (lam := lam) hlam
  rw [sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
    A hden f lam] at hmarkov
  simpa [P] using hmarkov

/-- Lower-probability complement form of
    `sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf`. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    1 - Real.exp (-(lam * T)) *
        (∑ x : ElementwiseSample m n,
          sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ^ steps ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∑ t : Fin steps, f (samples t) ≤ T} := by
  let P := sqMagTraceProbability (steps := steps) A hden
  have htail :=
    FiniteProbability.eventProb_real_le_ge_one_sub_exp_mul_mgf
      P (fun samples => ∑ t : Fin steps, f (samples t)) (T := T)
      (lam := lam) hlam
  rw [sqMagTraceProbability_expectationReal_exp_sum_stepFunction_eq
    A hden f lam] at htail
  simpa [P] using htail

/-- Exponential-Markov upper tail for a trace-sum from a one-step scalar MGF
    bound.  If `E exp(lam f(X)) <= exp(psi)` for one sampled entry, then the
    independent trace sum has the expected `exp(s*psi - lam*T)` tail. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_of_one_step_mgf_bound
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam psi : ℝ} (hlam : 0 < lam)
    (hmgf :
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤ Real.exp psi) :
    (sqMagTraceProbability (steps := steps) A hden).eventProb
      {samples |
        T ≤ ∑ t : Fin steps, f (samples t)} ≤
      Real.exp ((steps : ℝ) * psi - lam * T) := by
  classical
  let M : ℝ :=
    ∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)
  have hM_nonneg : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (sqMagProb_nonneg A hden x.1 x.2)
        (le_of_lt (Real.exp_pos _))
  have htail :=
    sqMagTraceProbability_eventProb_sum_stepFunction_ge_le_exp_mul_mgf
      (steps := steps) A hden f (T := T) (lam := lam) hlam
  have hpow : M ^ steps ≤ (Real.exp psi) ^ steps :=
    pow_le_pow_left₀ hM_nonneg hmgf steps
  have hmul :
      Real.exp (-(lam * T)) * M ^ steps ≤
        Real.exp (-(lam * T)) * (Real.exp psi) ^ steps :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hexp :
      Real.exp (-(lam * T)) * (Real.exp psi) ^ steps =
        Real.exp ((steps : ℝ) * psi - lam * T) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  exact htail.trans (hmul.trans_eq hexp)

/-- Complement form of the scalar trace-sum tail obtained from a one-step MGF
    bound. -/
theorem sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {T lam psi : ℝ} (hlam : 0 < lam)
    (hmgf :
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤ Real.exp psi) :
    1 - Real.exp ((steps : ℝ) * psi - lam * T) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∑ t : Fin steps, f (samples t) ≤ T} := by
  classical
  let M : ℝ :=
    ∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)
  have hM_nonneg : 0 ≤ M := by
    unfold M
    exact Finset.sum_nonneg fun x _ =>
      mul_nonneg (sqMagProb_nonneg A hden x.1 x.2)
        (le_of_lt (Real.exp_pos _))
  have htail :=
    sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_mul_mgf
      (steps := steps) A hden f (T := T) (lam := lam) hlam
  have hpow : M ^ steps ≤ (Real.exp psi) ^ steps :=
    pow_le_pow_left₀ hM_nonneg hmgf steps
  have hmul :
      Real.exp (-(lam * T)) * M ^ steps ≤
        Real.exp (-(lam * T)) * (Real.exp psi) ^ steps :=
    mul_le_mul_of_nonneg_left hpow (le_of_lt (Real.exp_pos _))
  have hexp :
      Real.exp (-(lam * T)) * (Real.exp psi) ^ steps =
        Real.exp ((steps : ℝ) * psi - lam * T) := by
    rw [← Real.exp_nat_mul]
    rw [← Real.exp_add]
    congr 1
    ring
  linarith

/-- Finite-family complement form of the product-law scalar MGF tail.

This is the union-bound layer needed by finite-cover arguments: if each
one-step statistic `f a` has a scalar MGF bound at parameter `lam a`, then all
corresponding trace sums are below their thresholds simultaneously with the
displayed probability.  This is still scalar MGF infrastructure, not a matrix
Bernstein theorem. -/
theorem sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
    {m n steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (f : ι → ElementwiseSample m n → ℝ)
    (T psi lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hmgf : ∀ a,
      (∑ x : ElementwiseSample m n,
        sqMagProb A x.1 x.2 * Real.exp (lam a * f a x)) ≤
        Real.exp (psi a)) :
    1 - ∑ a : ι, Real.exp ((steps : ℝ) * psi a - lam a * T a) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
  classical
  let P := sqMagTraceProbability (steps := steps) A hden
  let E : ι → Set (ElementwiseTrace m n steps) := fun a =>
    {samples | ∑ t : Fin steps, f a (samples t) ≤ T a}
  let δ : ι → ℝ := fun a =>
    Real.exp ((steps : ℝ) * psi a - lam a * T a)
  have hEach : ∀ a : ι, 1 - δ a ≤ P.eventProb (E a) := by
    intro a
    simpa [P, E, δ] using
      sqMagTraceProbability_eventProb_sum_stepFunction_le_ge_one_sub_exp_of_one_step_mgf_bound
        (steps := steps) A hden (f a) (T := T a) (lam := lam a)
        (psi := psi a) (hlam a) (hmgf a)
  have hAll :=
    FiniteProbability.eventProb_forall_ge_one_sub_sum
      P E δ hEach
  have hset :
      {samples : ElementwiseTrace m n steps |
        ∀ a : ι, samples ∈ E a} =
      {samples : ElementwiseTrace m n steps |
        ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
    ext samples
    simp [E]
  simpa [P, E, δ, hset] using hAll

/-- A pointwise upper bound on a one-step statistic gives a one-step scalar MGF
    bound under the squared-magnitude sampling law. -/
theorem sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {lam B : ℝ} (hlam : 0 ≤ lam)
    (hf : ∀ x : ElementwiseSample m n, f x ≤ B) :
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤
      Real.exp (lam * B) := by
  classical
  calc
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x))
        ≤ ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * B) := by
            apply Finset.sum_le_sum
            intro x _
            have harg : lam * f x ≤ lam * B :=
              mul_le_mul_of_nonneg_left (hf x) hlam
            exact mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr harg)
              (sqMagProb_nonneg A hden x.1 x.2)
    _ = (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2) *
          Real.exp (lam * B) := by
            rw [Finset.sum_mul]
    _ = Real.exp (lam * B) := by
            rw [sqMagProb_sum_samples_eq_one A hden.ne']
            ring

/-- A support-aware pointwise upper bound on a one-step statistic gives a
    one-step scalar MGF bound under the squared-magnitude sampling law.

This variant is important for truncated sampling: samples with zero probability
do not need to satisfy the pointwise bound, because their mass is zero in the
one-step law. -/
theorem sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A)
    (f : ElementwiseSample m n → ℝ) {lam B : ℝ} (hlam : 0 ≤ lam)
    (hf : ∀ x : ElementwiseSample m n,
      0 < sqMagProb A x.1 x.2 → f x ≤ B) :
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x)) ≤
      Real.exp (lam * B) := by
  classical
  calc
    (∑ x : ElementwiseSample m n,
      sqMagProb A x.1 x.2 * Real.exp (lam * f x))
        ≤ ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * B) := by
            apply Finset.sum_le_sum
            intro x _
            by_cases hpos : 0 < sqMagProb A x.1 x.2
            · have harg : lam * f x ≤ lam * B :=
                mul_le_mul_of_nonneg_left (hf x hpos) hlam
              exact mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr harg)
                (sqMagProb_nonneg A hden x.1 x.2)
            · have hzero : sqMagProb A x.1 x.2 = 0 :=
                le_antisymm (le_of_not_gt hpos)
                  (sqMagProb_nonneg A hden x.1 x.2)
              simp [hzero]
    _ = (∑ x : ElementwiseSample m n, sqMagProb A x.1 x.2) *
          Real.exp (lam * B) := by
            rw [Finset.sum_mul]
    _ = Real.exp (lam * B) := by
            rw [sqMagProb_sum_samples_eq_one A hden.ne']
            ring

/-- Finite-family scalar trace-sum tail from pointwise one-step bounds.

This is weaker than a Bernstein/Hoeffding-type MGF estimate, but it is fully
proved from the local squared-magnitude product law and is useful as a
bookkeeping-free finite-test support theorem. -/
theorem sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_pointwise_bound
    {m n steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (f : ι → ElementwiseSample m n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a x, f a x ≤ B a) :
    1 - ∑ a : ι, Real.exp ((steps : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
  classical
  exact
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      (steps := steps) A hden f T (fun a => lam a * B a) lam hlam
      (by
        intro a
        exact sqMagProb_sum_exp_stepFunction_le_exp_of_forall_le
          A hden (f a) (le_of_lt (hlam a)) (hbound a))

/-- Finite-family scalar trace-sum tail from support-aware pointwise one-step
    bounds.

The pointwise hypothesis only needs to hold on one-step samples with positive
squared-magnitude probability.  This avoids adding artificial hypotheses for
zero-mass truncated samples. -/
theorem sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_support_pointwise_bound
    {m n steps : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (f : ι → ElementwiseSample m n → ℝ)
    (T B lam : ι → ℝ) (hlam : ∀ a, 0 < lam a)
    (hbound : ∀ a x, 0 < sqMagProb A x.1 x.2 → f a x ≤ B a) :
    1 - ∑ a : ι, Real.exp ((steps : ℝ) * (lam a * B a) - lam a * T a) ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        {samples |
          ∀ a : ι, ∑ t : Fin steps, f a (samples t) ≤ T a} := by
  classical
  exact
    sqMagTraceProbability_eventProb_forall_sum_stepFunction_le_ge_one_sub_sum_exp_of_one_step_mgf_bound
      (steps := steps) A hden f T (fun a => lam a * B a) lam hlam
      (by
        intro a
        exact sqMagProb_sum_exp_stepFunction_le_exp_of_support_forall_le
          A hden (f a) (le_of_lt (hlam a)) (hbound a))

/-- The trace hit-count exponential is the product of the one-step
    exponential indicators. -/
theorem exp_hitCount_eq_prod_sampleHitIndicator {m n steps : ℕ}
    (samples : ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (lam : ℝ) :
    Real.exp (lam * (hitCount samples i j : ℝ)) =
      ∏ t : Fin steps, Real.exp (lam * sampleHitIndicator (samples t) i j) := by
  classical
  have hcount := hitCount_eq_sum_indicator samples i j
  calc
    Real.exp (lam * (hitCount samples i j : ℝ))
        = Real.exp (∑ t : Fin steps, lam * hitIndicator samples t i j) := by
            rw [hcount]
            rw [Finset.mul_sum]
    _ = ∏ t : Fin steps, Real.exp (lam * hitIndicator samples t i j) := by
            simpa using (Real.exp_sum (Finset.univ : Finset (Fin steps))
              (fun t => lam * hitIndicator samples t i j))
    _ = ∏ t : Fin steps, Real.exp (lam * sampleHitIndicator (samples t) i j) := by
            apply Finset.prod_congr rfl
            intro t _
            simp [hitIndicator, sampleHitIndicator, sampleHits]

/-- Exact moment-generating identity for the hit counter under the canonical
    independent squared-magnitude trace distribution. -/
theorem sqMagTraceProbMass_exp_hitCount_sum_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : sqMagProbDen A ≠ 0)
    (i : Fin m) (j : Fin n) (lam : ℝ) :
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (hitCount samples i j : ℝ))) =
      (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
  classical
  calc
    (∑ samples : ElementwiseTrace m n steps,
      sqMagTraceProbMass A samples *
        Real.exp (lam * (hitCount samples i j : ℝ)))
        = ∑ samples : ElementwiseTrace m n steps,
            ∏ t : Fin steps,
              sqMagProb A (samples t).1 (samples t).2 *
                Real.exp (lam * sampleHitIndicator (samples t) i j) := by
            apply Finset.sum_congr rfl
            intro samples _
            rw [exp_hitCount_eq_prod_sampleHitIndicator]
            simp [sqMagTraceProbMass, Finset.prod_mul_distrib]
    _ = ∏ t : Fin steps,
          ∑ x : ElementwiseSample m n,
            sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j) := by
            have hprod :=
              Finset.prod_univ_sum
                (t := fun _ : Fin steps => (Finset.univ : Finset (ElementwiseSample m n)))
                (f := fun _ x =>
                  sqMagProb A x.1 x.2 * Real.exp (lam * sampleHitIndicator x i j))
            symm
            simpa [ElementwiseTrace] using hprod
    _ = ∏ _ : Fin steps, (1 + sqMagProb A i j * (Real.exp lam - 1)) := by
            apply Finset.prod_congr rfl
            intro t _
            exact sqMag_sampleHitIndicator_exp_sum A hden i j lam
    _ = (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
            simp [Fintype.card_fin]

/-- Exact expectation form of the hit-count MGF identity for the canonical
    independent squared-magnitude trace distribution. -/
theorem sqMagTraceProbability_expectationReal_exp_hitCount_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (lam : ℝ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples => Real.exp (lam * (hitCount samples i j : ℝ))) =
      (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
  simpa [sqMagTraceProbability, FiniteProbability.expectationReal,
    sqMagTraceProbMass] using
    sqMagTraceProbMass_exp_hitCount_sum_eq
      (steps := steps) A hden.ne' i j lam

-- ============================================================
-- Chernoff concentration from an exponential-moment bound
-- ============================================================

/-- The standard Bernoulli-sum exponential-moment upper bound used by the
    Chernoff argument:

`E exp(lam qᵢⱼ) ≤ exp(steps * pᵢⱼ * (exp lam - 1))`.

For Algorithm 1 this is the condition supplied by fully independent sampling
of the step-hit indicators. It is stronger than the marginal law used by
Markov and stronger than the pairwise law used by Chebyshev. -/
def hitCountChernoffMGFBound {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ) : Prop :=
  ∀ lam : ℝ, 0 < lam →
    P.expectationReal
        (fun ω => Real.exp (lam * (hitCount (X ω) i j : ℝ))) ≤
      Real.exp ((steps : ℝ) * p * (Real.exp lam - 1))

/-- Squared-magnitude specialization of the Chernoff MGF condition. -/
def sqMagHitCountChernoffMGFBound {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n) : Prop :=
  hitCountChernoffMGFBound P X i j (sqMagProb A i j)

/-- The Chernoff MGF condition is a theorem for the canonical independent
    Algorithm 1 trace distribution with squared-magnitude sampling. -/
theorem sqMagTraceProbability_chernoff_mgf_bound {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) :
    sqMagHitCountChernoffMGFBound
      (sqMagTraceProbability (steps := steps) A hden)
      A (fun samples => samples) i j := by
  intro lam hlam
  let x : ℝ := sqMagProb A i j * (Real.exp lam - 1)
  have hexact :=
    sqMagTraceProbability_expectationReal_exp_hitCount_eq
      (steps := steps) A hden i j lam
  have hp : 0 ≤ sqMagProb A i j :=
    sqMagProb_nonneg A hden i j
  have hexp_ge_one : 1 ≤ Real.exp lam := by
    have hadd := Real.add_one_le_exp lam
    linarith
  have hx_nonneg : 0 ≤ x := by
    unfold x
    exact mul_nonneg hp (by linarith)
  have hbase_nonneg : 0 ≤ 1 + x := by
    linarith
  have hbase_le_exp : 1 + x ≤ Real.exp x := by
    simpa [add_comm] using Real.add_one_le_exp x
  have hpow : (1 + x) ^ steps ≤ (Real.exp x) ^ steps :=
    pow_le_pow_left₀ hbase_nonneg hbase_le_exp steps
  have hexp_pow : (Real.exp x) ^ steps = Real.exp ((steps : ℝ) * x) :=
    (Real.exp_nat_mul x steps).symm
  calc
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
        (fun samples => Real.exp (lam * (hitCount ((fun samples => samples) samples) i j : ℝ)))
        = (1 + sqMagProb A i j * (Real.exp lam - 1)) ^ steps := by
            simpa using hexact
    _ = (1 + x) ^ steps := by
            simp [x]
    _ ≤ (Real.exp x) ^ steps := hpow
    _ = Real.exp ((steps : ℝ) * x) := hexp_pow
    _ = Real.exp ((steps : ℝ) * sqMagProb A i j * (Real.exp lam - 1)) := by
            congr 1
            simp [x]
            ring

/-- Chernoff upper-tail expression for `qᵢⱼ > Q`, written as
    `Pr(Q+1 ≤ qᵢⱼ)`. -/
noncomputable def chernoffHitCountTail (steps : ℕ) (p lam : ℝ) (Q : ℕ) : ℝ :=
  Real.exp ((steps : ℝ) * p * (Real.exp lam - 1) -
    lam * (((Q + 1 : ℕ) : ℝ)))

/-- Squared-magnitude specialization of the Chernoff tail expression. -/
noncomputable def sqMagChernoffHitCountTail {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (lam : ℝ) (Q : ℕ) : ℝ :=
  chernoffHitCountTail steps (sqMagProb A i j) lam Q

/-- Chernoff concentration for the Algorithm 1 hit counter from the MGF bound. -/
theorem hitCount_concentrates_chernoff_of_mgf_bound {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p lam : ℝ) (Q : ℕ) (hlam : 0 < lam)
    (hmgf : hitCountChernoffMGFBound P X i j p) :
    1 - chernoffHitCountTail steps p lam Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  simpa [hitCountAtMostEvent, chernoffHitCountTail] using
    FiniteProbability.eventProb_nat_le_ge_one_sub_chernoff_of_mgf_bound
      P (fun ω => hitCount (X ω) i j) Q (lam := lam)
      (μ := (steps : ℝ) * p) hlam (hmgf lam hlam)

/-- Squared-magnitude Chernoff concentration for the Algorithm 1 hit counter. -/
theorem hitCount_concentrates_sqMag_chernoff_of_mgf_bound {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (lam : ℝ) (Q : ℕ) (hlam : 0 < lam)
    (hmgf : sqMagHitCountChernoffMGFBound P A X i j) :
    1 - sqMagChernoffHitCountTail steps A i j lam Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  simpa [sqMagChernoffHitCountTail, sqMagHitCountChernoffMGFBound] using
    hitCount_concentrates_chernoff_of_mgf_bound P X i j
      (sqMagProb A i j) lam Q hlam hmgf

/-- Chernoff concentration for the canonical independent squared-magnitude
    Algorithm 1 sampler, with no abstract MGF hypothesis. -/
theorem hitCount_concentrates_sqMag_chernoff_independent {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n) (lam : ℝ) (Q : ℕ) (hlam : 0 < lam) :
    1 - sqMagChernoffHitCountTail steps A i j lam Q ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j Q) := by
  exact hitCount_concentrates_sqMag_chernoff_of_mgf_bound
    (sqMagTraceProbability (steps := steps) A hden) A
    (fun samples => samples) i j lam Q hlam
    (sqMagTraceProbability_chernoff_mgf_bound A hden i j)

/-- Chernoff-selected natural budget for a fixed exponential parameter `lam`:

`Q = ceil((steps * p * (exp lam - 1) - log δ) / lam)`.

With `lam > 0` and `δ > 0`, this makes the Chernoff tail at most `δ`. -/
noncomputable def chernoffHitCountBudget (steps : ℕ)
    (p lam δ : ℝ) : ℕ :=
  Nat.ceil (((steps : ℝ) * p * (Real.exp lam - 1) - Real.log δ) / lam)

/-- Squared-magnitude specialization of the Chernoff-selected budget. -/
noncomputable def sqMagChernoffHitCountBudget {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    (lam δ : ℝ) : ℕ :=
  chernoffHitCountBudget steps (sqMagProb A i j) lam δ

theorem chernoffHitCountBudget_tail {steps : ℕ} {p lam δ : ℝ}
    (hlam : 0 < lam) (hδ : 0 < δ) :
    chernoffHitCountTail steps p lam
        (chernoffHitCountBudget steps p lam δ) ≤ δ := by
  let a : ℝ := (steps : ℝ) * p * (Real.exp lam - 1)
  let Q : ℕ := chernoffHitCountBudget steps p lam δ
  have hceil :
      (a - Real.log δ) / lam ≤ (Q : ℝ) := by
    unfold Q chernoffHitCountBudget
    exact Nat.le_ceil ((a - Real.log δ) / lam)
  have hQle :
      (Q : ℝ) ≤ (((Q + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.le_succ Q
  have htarget :
      a - Real.log δ ≤ lam * (((Q + 1 : ℕ) : ℝ)) := by
    have hdiv :
        (a - Real.log δ) / lam ≤ (((Q + 1 : ℕ) : ℝ)) :=
      le_trans hceil hQle
    have hdiv' : a - Real.log δ ≤ (((Q + 1 : ℕ) : ℝ)) * lam := by
      rwa [div_le_iff₀ hlam] at hdiv
    linarith
  have hexponent :
      a - lam * (((Q + 1 : ℕ) : ℝ)) ≤ Real.log δ := by
    linarith
  have hexp :
      Real.exp (a - lam * (((Q + 1 : ℕ) : ℝ))) ≤
        Real.exp (Real.log δ) :=
    Real.exp_le_exp.mpr hexponent
  have hlog : Real.exp (Real.log δ) = δ := Real.exp_log hδ
  simpa [chernoffHitCountTail, a, Q, hlog] using hexp

theorem sqMagChernoffHitCountBudget_tail {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n)
    {lam δ : ℝ} (hlam : 0 < lam) (hδ : 0 < δ) :
    sqMagChernoffHitCountTail steps A i j lam
        (sqMagChernoffHitCountBudget steps A i j lam δ) ≤ δ := by
  simpa [sqMagChernoffHitCountTail, sqMagChernoffHitCountBudget] using
    chernoffHitCountBudget_tail
      (steps := steps) (p := sqMagProb A i j) hlam hδ

/-- `1 - δ` Chernoff concentration for the canonical independent
    squared-magnitude sampler with the fixed-`lam` budget already selected. -/
theorem hitCount_concentrates_sqMag_chernoff_independent_budget
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n)
    (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j
          (sqMagChernoffHitCountBudget steps A i j lam δ)) := by
  have htail :=
    sqMagChernoffHitCountBudget_tail
      (steps := steps) A i j hlam hδ
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_independent
      (steps := steps) A hden i j lam
      (sqMagChernoffHitCountBudget steps A i j lam δ) hlam
  linarith

/-- Optimized Chernoff upper-tail expression, obtained from
    `chernoffHitCountTail` by choosing
    `lam = log((Q+1)/(steps*p))`.

This is the sharp Chernoff exponent for a Bernoulli-sum upper tail at the
threshold `Q+1`, under the side conditions `0 < steps*p` and
`steps*p < Q+1`. -/
noncomputable def chernoffOptimizedHitCountTail
    (steps : ℕ) (p : ℝ) (Q : ℕ) : ℝ :=
  chernoffHitCountTail steps p
    (Real.log ((((Q + 1 : ℕ) : ℝ)) / ((steps : ℝ) * p))) Q

/-- Squared-magnitude specialization of the optimized Chernoff tail. -/
noncomputable def sqMagChernoffOptimizedHitCountTail {m n : ℕ}
    (steps : ℕ) (A : Fin m → Fin n → ℝ)
    (i : Fin m) (j : Fin n) (Q : ℕ) : ℝ :=
  chernoffOptimizedHitCountTail steps (sqMagProb A i j) Q

/-- Optimized Chernoff concentration for the hit counter. The exponential
    parameter is chosen as `log((Q+1)/(steps*p))`, which minimizes the
    Chernoff upper-tail expression for this threshold. -/
theorem hitCount_concentrates_chernoff_optimized_of_mgf_bound {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p : ℝ) (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * p)
    (hQ : (steps : ℝ) * p < (((Q + 1 : ℕ) : ℝ)))
    (hmgf : hitCountChernoffMGFBound P X i j p) :
    1 - chernoffOptimizedHitCountTail steps p Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  let T : ℝ := (((Q + 1 : ℕ) : ℝ))
  let μ : ℝ := (steps : ℝ) * p
  have hTpos : 0 < T := by
    unfold T
    exact_mod_cast Nat.succ_pos Q
  have hratio_pos : 0 < T / μ := div_pos hTpos hμ
  have hratio_gt_one : 1 < T / μ := by
    rw [one_lt_div hμ]
    simpa [T, μ] using hQ
  have hlam : 0 < Real.log (T / μ) :=
    (Real.log_pos_iff (le_of_lt hratio_pos)).mpr hratio_gt_one
  simpa [chernoffOptimizedHitCountTail, T, μ] using
    hitCount_concentrates_chernoff_of_mgf_bound P X i j p
      (Real.log (T / μ)) Q hlam hmgf

/-- Squared-magnitude optimized Chernoff concentration for the hit counter. -/
theorem hitCount_concentrates_sqMag_chernoff_optimized_of_mgf_bound
    {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j <
      (((Q + 1 : ℕ) : ℝ)))
    (hmgf : sqMagHitCountChernoffMGFBound P A X i j) :
    1 - sqMagChernoffOptimizedHitCountTail steps A i j Q ≤
      P.eventProb (hitCountAtMostEvent X i j Q) := by
  simpa [sqMagChernoffOptimizedHitCountTail,
    sqMagHitCountChernoffMGFBound] using
    hitCount_concentrates_chernoff_optimized_of_mgf_bound
      P X i j (sqMagProb A i j) Q hμ hQ hmgf

/-- Optimized Chernoff concentration for the canonical independent
    squared-magnitude Algorithm 1 sampler. -/
theorem hitCount_concentrates_sqMag_chernoff_optimized_independent
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n)
    (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j <
      (((Q + 1 : ℕ) : ℝ))) :
    1 - sqMagChernoffOptimizedHitCountTail steps A i j Q ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j Q) := by
  exact hitCount_concentrates_sqMag_chernoff_optimized_of_mgf_bound
    (sqMagTraceProbability (steps := steps) A hden) A
    (fun samples => samples) i j Q hμ hQ
    (sqMagTraceProbability_chernoff_mgf_bound A hden i j)

/-- `1 - δ` optimized Chernoff concentration for the canonical independent
    squared-magnitude sampler from a supplied optimized-tail budget. -/
theorem hitCount_concentrates_sqMag_chernoff_optimized_independent_of_tail_budget
    {m n steps : ℕ} (A : Fin m → Fin n → ℝ)
    (hden : 0 < sqMagProbDen A) (i : Fin m) (j : Fin n)
    (δ : ℝ) (Q : ℕ)
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQ : (steps : ℝ) * sqMagProb A i j <
      (((Q + 1 : ℕ) : ℝ)))
    (htail : sqMagChernoffOptimizedHitCountTail steps A i j Q ≤ δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (hitCountAtMostEvent (fun samples => samples) i j Q) := by
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_optimized_independent
      A hden i j Q hμ hQ
  linarith

/-- Event that the hit counter lies within real radius `ε` of a center `μ`. -/
def hitCountDeviationEvent {Ω : Type*} {m n steps : ℕ}
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (μ ε : ℝ) : Set Ω :=
  {ω | |(hitCount (X ω) i j : ℝ) - μ| ≤ ε}

/-- Chebyshev concentration of the hit counter around `steps * p`, assuming
    marginal hit probability `p` and pairwise independence of distinct hit
    indicators. -/
theorem hitCount_concentrates_around_mean_pairwise {Ω : Type*} [Fintype Ω]
    {m n steps : ℕ} (P : FiniteProbability Ω)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (p ε δ : ℝ) (hε : 0 < ε)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = p)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} = p * p)
    (htail :
      hitCountPairwiseCenteredMoment steps p / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb
        (hitCountDeviationEvent X i j ((steps : ℝ) * p) ε) := by
  have hmoment :=
    expectationReal_hitCount_centered_sq_eq_pairwise P X i j p hmarginal hpairwise
  exact FiniteProbability.eventProb_abs_sub_le_ge_one_sub_of_second_moment
    P (fun ω => (hitCount (X ω) i j : ℝ)) ((steps : ℝ) * p) ε δ hε
    (by simpa [hmoment])

/-- Squared-magnitude specialization of the pairwise Chebyshev concentration:
    `qᵢⱼ` concentrates around `steps * pᵢⱼ`, where
    `pᵢⱼ = sqMagProb A i j`. -/
theorem hitCount_concentrates_sqMag_around_mean_pairwise {Ω : Type*}
    [Fintype Ω] {m n steps : ℕ} (P : FiniteProbability Ω)
    (A : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (ε δ : ℝ) (hε : 0 < ε)
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j)
    (htail :
      hitCountPairwiseCenteredMoment steps (sqMagProb A i j) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb
        (hitCountDeviationEvent X i j
          ((steps : ℝ) * sqMagProb A i j) ε) :=
  hitCount_concentrates_around_mean_pairwise P X i j
    (sqMagProb A i j) ε δ hε hmarginal hpairwise htail

/-- Chebyshev radius selected from the pairwise second moment:
    `ε = M / δ + 1`, where `M` is the centered second moment.

The extra `+1` keeps the radius strictly positive and avoids a square-root
dependency while still giving `M / ε² ≤ δ` for `δ > 0`. -/
noncomputable def chebyshevHitCountRadius (steps : ℕ) (p δ : ℝ) : ℝ :=
  hitCountPairwiseCenteredMoment steps p / δ + 1

/-- Chebyshev-selected natural budget:
    `Q = ceil(steps * p + ε)`, with
    `ε = hitCountPairwiseCenteredMoment steps p / δ + 1`. -/
noncomputable def chebyshevHitCountBudget (steps : ℕ) (p δ : ℝ) : ℕ :=
  Nat.ceil ((steps : ℝ) * p + chebyshevHitCountRadius steps p δ)

/-- Squared-magnitude specialization of the Chebyshev-selected budget. -/
noncomputable def sqMagChebyshevHitCountBudget {m n : ℕ} (steps : ℕ)
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (δ : ℝ) : ℕ :=
  chebyshevHitCountBudget steps (sqMagProb A i j) δ

theorem chebyshevHitCountRadius_pos {steps : ℕ} {p δ : ℝ}
    (hδ : 0 < δ) (hM : 0 ≤ hitCountPairwiseCenteredMoment steps p) :
    0 < chebyshevHitCountRadius steps p δ := by
  unfold chebyshevHitCountRadius
  have hdiv : 0 ≤ hitCountPairwiseCenteredMoment steps p / δ :=
    div_nonneg hM (le_of_lt hδ)
  linarith

theorem hitCountPairwiseCenteredMoment_div_chebyshevRadius_sq_le
    {steps : ℕ} {p δ : ℝ} (hδ : 0 < δ)
    (hM : 0 ≤ hitCountPairwiseCenteredMoment steps p) :
    hitCountPairwiseCenteredMoment steps p /
        (chebyshevHitCountRadius steps p δ) ^ 2 ≤ δ := by
  have hε := chebyshevHitCountRadius_pos (steps := steps) (p := p) hδ hM
  rw [div_le_iff₀ (sq_pos_of_pos hε)]
  unfold chebyshevHitCountRadius
  field_simp [hδ.ne']
  nlinarith [sq_nonneg (hitCountPairwiseCenteredMoment steps p),
    hM, hδ]

theorem chebyshevHitCountBudget_mean_add_radius_le {steps : ℕ} {p δ : ℝ} :
    (steps : ℝ) * p + chebyshevHitCountRadius steps p δ ≤
      (chebyshevHitCountBudget steps p δ : ℝ) := by
  unfold chebyshevHitCountBudget
  exact Nat.le_ceil ((steps : ℝ) * p + chebyshevHitCountRadius steps p δ)

theorem sqMagChebyshevHitCountBudget_mean_add_radius_le {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (i : Fin m) (j : Fin n) (δ : ℝ) :
    (steps : ℝ) * sqMagProb A i j +
        chebyshevHitCountRadius steps (sqMagProb A i j) δ ≤
      (sqMagChebyshevHitCountBudget steps A i j δ : ℝ) := by
  simpa [sqMagChebyshevHitCountBudget] using
    chebyshevHitCountBudget_mean_add_radius_le
      (steps := steps) (p := sqMagProb A i j) (δ := δ)

theorem hitCountDeviationEvent_subset_hitCountAtMostEvent {Ω : Type*}
    {m n steps : ℕ} (X : Ω → ElementwiseTrace m n steps)
    (i : Fin m) (j : Fin n) (μ ε : ℝ) (Q : ℕ)
    (hQ : μ + ε ≤ (Q : ℝ)) :
    hitCountDeviationEvent X i j μ ε ⊆ hitCountAtMostEvent X i j Q := by
  intro ω hω
  have hupper : (hitCount (X ω) i j : ℝ) - μ ≤ ε :=
    (abs_le.mp hω).2
  have hreal : (hitCount (X ω) i j : ℝ) ≤ Q := by
    linarith
  exact_mod_cast hreal

theorem probability_sqMagTraceStability_of_hitCount_deviation
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (ρ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (μ ε : ℝ) (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQreal : μ + ε ≤ (Q : ℝ))
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hprob : ρ ≤ P.eventProb (hitCountDeviationEvent X i j μ ε)) :
    ρ ≤ P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  exact le_trans hprob
    (FiniteProbability.eventProb_mono P
      (Set.Subset.trans
        (hitCountDeviationEvent_subset_hitCountAtMostEvent X i j μ ε Q hQreal)
        (hitCountAtMostEvent_subset_sqMagTraceStabilityEvent fp s A Atilde
          X i j Q hs hAij hQvalid hQ1valid)))

theorem highProbability_sqMagTraceStability_of_pairwise_hitCount_deviation
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ ε : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hε : 0 < ε)
    (hQreal : (steps : ℝ) * sqMagProb A i j + ε ≤ (Q : ℝ))
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j)
    (htail :
      hitCountPairwiseCenteredMoment steps (sqMagProb A i j) / ε ^ 2 ≤ δ) :
    1 - δ ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  have hdev :=
    hitCount_concentrates_sqMag_around_mean_pairwise P A X i j ε δ hε
      hmarginal hpairwise htail
  exact probability_sqMagTraceStability_of_hitCount_deviation fp P
    (1 - δ) s A Atilde X i j ((steps : ℝ) * sqMagProb A i j) ε Q
    hs hAij hQreal hQvalid hQ1valid hdev

theorem highProbability_sqMagTraceStability_of_pairwise_chebyshev_budget
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) (hδ : 0 < δ)
    (hQvalid :
      gammaValid fp (sqMagChebyshevHitCountBudget steps A i j δ))
    (hQ1valid :
      gammaValid fp (sqMagChebyshevHitCountBudget steps A i j δ + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hpairwise : ∀ t u : Fin steps, t ≠ u →
      P.eventProb
        {ω | sampleHits (X ω) t i j ∧ sampleHits (X ω) u i j} =
          sqMagProb A i j * sqMagProb A i j) :
    1 - δ ≤
      P.eventProb
        (sqMagTraceStabilityEvent fp s A Atilde X i j
          (sqMagChebyshevHitCountBudget steps A i j δ)) := by
  let p : ℝ := sqMagProb A i j
  have hmoment_eq :=
    expectationReal_hitCount_centered_sq_eq_pairwise P X i j p
      (by simpa [p] using hmarginal)
      (by simpa [p] using hpairwise)
  have hM_nonneg : 0 ≤ hitCountPairwiseCenteredMoment steps p := by
    rw [← hmoment_eq]
    unfold FiniteProbability.expectationReal
    exact Finset.sum_nonneg fun ω _ =>
      mul_nonneg (P.prob_nonneg ω) (sq_nonneg _)
  have hε :
      0 < chebyshevHitCountRadius steps (sqMagProb A i j) δ := by
    simpa [p] using chebyshevHitCountRadius_pos
      (steps := steps) (p := p) hδ hM_nonneg
  have hQreal :
      (steps : ℝ) * sqMagProb A i j +
          chebyshevHitCountRadius steps (sqMagProb A i j) δ ≤
        (sqMagChebyshevHitCountBudget steps A i j δ : ℝ) :=
    sqMagChebyshevHitCountBudget_mean_add_radius_le A i j δ
  have htail :
      hitCountPairwiseCenteredMoment steps (sqMagProb A i j) /
          (chebyshevHitCountRadius steps (sqMagProb A i j) δ) ^ 2 ≤ δ := by
    simpa [p] using
      hitCountPairwiseCenteredMoment_div_chebyshevRadius_sq_le
        (steps := steps) (p := p) hδ hM_nonneg
  exact highProbability_sqMagTraceStability_of_pairwise_hitCount_deviation fp
    P δ (chebyshevHitCountRadius steps (sqMagProb A i j) δ) s
    A Atilde X i j (sqMagChebyshevHitCountBudget steps A i j δ)
    hs hAij hε hQreal hQvalid hQ1valid hmarginal hpairwise htail

-- ============================================================
-- Stability with the proved hit-count concentration
-- ============================================================

/-- High-probability floating-point stability using the proved Markov
    concentration location for the hit counter. -/
theorem highProbability_sqMagTraceStability_of_marginal_hitProb
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQ : gammaValid fp Q) (hQ1 : gammaValid fp (Q + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j) :
    1 - (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  have hconc :=
    hitCount_concentration_sqMag_markov P A X i j Q hmarginal
  exact probability_sqMagTraceStability_of_hitCount_concentration fp
    P.eventProb
    (1 - (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ))
    s A Atilde X i j Q hs hAij hQ hQ1
    (FiniteProbability.eventProb_mono P) hconc

/-- `1 - δ` high-probability floating-point stability using the proved Markov
    concentration bound for the hit counter.  The hypothesis on `Q` is the
    explicit location where the random counter concentrates. -/
theorem highProbability_sqMagTraceStability_of_marginal_hitProb_of_tail_budget
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j)
    (hQtail :
      (steps : ℝ) * sqMagProb A i j / ((Q + 1 : ℕ) : ℝ) ≤ δ) :
    1 - δ ≤
      P.eventProb (sqMagTraceStabilityEvent fp s A Atilde X i j Q) := by
  have hstab :=
    highProbability_sqMagTraceStability_of_marginal_hitProb fp
      P s A Atilde X i j Q hs hAij hQvalid hQ1valid hmarginal
  linarith

/-- Markov high-probability stability with the natural counter budget already
    chosen as `ceil(steps * pᵢⱼ / δ)`. -/
theorem highProbability_sqMagTraceStability_of_markov_budget
    (fp : FPModel) {Ω : Type*} [Fintype Ω] {m n steps : ℕ}
    (P : FiniteProbability Ω) (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ)
    (X : Ω → ElementwiseTrace m n steps) (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0) (hδ : 0 < δ)
    (hQvalid : gammaValid fp (sqMagMarkovHitCountBudget steps A i j δ))
    (hQ1valid :
      gammaValid fp (sqMagMarkovHitCountBudget steps A i j δ + 1))
    (hmarginal : ∀ t : Fin steps,
      P.eventProb {ω | sampleHits (X ω) t i j} = sqMagProb A i j) :
    1 - δ ≤
      P.eventProb
        (sqMagTraceStabilityEvent fp s A Atilde X i j
          (sqMagMarkovHitCountBudget steps A i j δ)) := by
  have htail :=
    sqMagMarkovHitCountBudget_tail (steps := steps) A i j hδ
  exact highProbability_sqMagTraceStability_of_marginal_hitProb_of_tail_budget
    fp P δ s A Atilde X i j
    (sqMagMarkovHitCountBudget steps A i j δ)
    hs hAij hQvalid hQ1valid hmarginal htail

/-- Chernoff high-probability stability for the canonical independent
    squared-magnitude Algorithm 1 sampler. The exponential-moment hypothesis
    is proved from the product trace distribution in
    `sqMagTraceProbability_chernoff_mgf_bound`. -/
theorem highProbability_sqMagTraceStability_of_independent_chernoff_budget
    (fp : FPModel) {m n steps : ℕ}
    (δ lam : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n)
    (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hlam : 0 < lam) (hδ : 0 < δ)
    (hQvalid :
      gammaValid fp (sqMagChernoffHitCountBudget steps A i j lam δ))
    (hQ1valid :
      gammaValid fp (sqMagChernoffHitCountBudget steps A i j lam δ + 1)) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (sqMagTraceStabilityEvent fp s A Atilde
          (fun samples => samples) i j
          (sqMagChernoffHitCountBudget steps A i j lam δ)) := by
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_independent_budget
      (steps := steps) A hden i j lam δ hlam hδ
  exact highProbability_sqMagTraceStability_of_hitCount_concentration fp
    (sqMagTraceProbability (steps := steps) A hden).eventProb δ s
    A Atilde (fun samples => samples) i j
    (sqMagChernoffHitCountBudget steps A i j lam δ)
    hs hAij hQvalid hQ1valid
    (FiniteProbability.eventProb_mono
      (sqMagTraceProbability (steps := steps) A hden)) hconc

/-- Optimized Chernoff high-probability stability for the canonical independent
    squared-magnitude Algorithm 1 sampler and a supplied budget `Q`. -/
theorem highProbability_sqMagTraceStability_of_independent_chernoff_optimized_tail_budget
    (fp : FPModel) {m n steps : ℕ}
    (δ : ℝ) (s : ℕ)
    (A Atilde : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (i : Fin m) (j : Fin n)
    (Q : ℕ) (hs : (s : ℝ) ≠ 0) (hAij : A i j ≠ 0)
    (hQvalid : gammaValid fp Q) (hQ1valid : gammaValid fp (Q + 1))
    (hμ : 0 < (steps : ℝ) * sqMagProb A i j)
    (hQtailThreshold :
      (steps : ℝ) * sqMagProb A i j < (((Q + 1 : ℕ) : ℝ)))
    (htail : sqMagChernoffOptimizedHitCountTail steps A i j Q ≤ δ) :
    1 - δ ≤
      (sqMagTraceProbability (steps := steps) A hden).eventProb
        (sqMagTraceStabilityEvent fp s A Atilde
          (fun samples => samples) i j Q) := by
  have hconc :=
    hitCount_concentrates_sqMag_chernoff_optimized_independent_of_tail_budget
      A hden i j δ Q hμ hQtailThreshold htail
  exact highProbability_sqMagTraceStability_of_hitCount_concentration fp
    (sqMagTraceProbability (steps := steps) A hden).eventProb δ s
    A Atilde (fun samples => samples) i j Q hs hAij hQvalid hQ1valid
    (FiniteProbability.eventProb_mono
      (sqMagTraceProbability (steps := steps) A hden)) hconc

end NumStability
