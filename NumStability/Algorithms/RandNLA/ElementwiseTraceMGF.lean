-- Algorithms/RandNLA/ElementwiseTraceMGF.lean
--
-- One-step trace-MGF adapters for Algorithm 1 under the canonical
-- squared-magnitude product trace law.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import NumStability.Algorithms.RandNLA.HitCountConcentration
import NumStability.Analysis.LiebTrace
import Mathlib.Data.Fin.Tuple.Basic

namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## One-step trace-MGF adapters

The finite-dimensional Lieb theorem in `Analysis/LiebTrace.lean` proves the
one-step Tropp trace-MGF inequality for an arbitrary repository-native finite
probability space.  This file connects that theorem to Algorithm 1's canonical
independent squared-magnitude trace law.

The results here are still one-step/marginal results.  The remaining red
bottleneck for the CACM equation (2) proof is the independent-sum iteration
from these one-step inequalities to a full matrix Bernstein/Khintchine bound.
-/

/-- The one-sample squared-magnitude law behind Algorithm 1. -/
noncomputable def sqMagSampleProbability {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A) :
    FiniteProbability (ElementwiseSample m n) where
  prob := fun x => sqMagProb A x.1 x.2
  prob_nonneg := fun x => sqMagProb_nonneg A hden x.1 x.2
  prob_sum := sqMagProb_sum_samples_eq_one A hden.ne'

/-- Complex-valued marginal expectation for one coordinate of the canonical
Algorithm 1 product trace law. -/
theorem sqMagTraceProbability_expectationComplex_step_eq {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t0 : Fin steps) (f : ElementwiseSample m n → ℂ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationComplex
      (fun samples => f (samples t0)) =
      ∑ x : ElementwiseSample m n, (sqMagProb A x.1 x.2 : ℂ) * f x := by
  classical
  apply Complex.ext
  · have hre :=
      sqMagTraceProbMass_marginal_one A hden.ne' t0
        (fun x : ElementwiseSample m n => (f x).re)
    simpa [FiniteProbability.expectationComplex, sqMagTraceProbability] using hre
  · have him :=
      sqMagTraceProbMass_marginal_one A hden.ne' t0
        (fun x : ElementwiseSample m n => (f x).im)
    simpa [FiniteProbability.expectationComplex, sqMagTraceProbability] using him

/-- C⋆-matrix-valued marginal expectation for one coordinate of the canonical
Algorithm 1 product trace law. -/
theorem sqMagTraceProbability_expectationCStarMatrix_step_eq
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t0 : Fin steps) {ι : Type*} [Fintype ι]
    (F : ElementwiseSample m n → CStarMatrix ι ι ℂ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationCStarMatrix
      (fun samples => F (samples t0)) =
      ∑ x : ElementwiseSample m n, (sqMagProb A x.1 x.2 : ℂ) • F x := by
  classical
  ext i j
  have h :=
    sqMagTraceProbability_expectationComplex_step_eq A hden t0
      (fun x : ElementwiseSample m n => F x i j)
  change
    (sqMagTraceProbability (steps := steps) A hden).expectationComplex
        (fun samples => F (samples t0) i j) =
      (∑ x : ElementwiseSample m n, (sqMagProb A x.1 x.2 : ℂ) • F x) i j
  rw [show
      (∑ x : ElementwiseSample m n, (sqMagProb A x.1 x.2 : ℂ) • F x) i j =
        ∑ x : ElementwiseSample m n,
          ((sqMagProb A x.1 x.2 : ℂ) • F x) i j by
    exact Matrix.sum_apply i j Finset.univ
      (fun x => ((sqMagProb A x.1 x.2 : ℂ) • F x :
        CStarMatrix ι ι ℂ))]
  simpa [smul_eq_mul] using h

/-- The C⋆ marginal expectation agrees with the explicit one-sample
squared-magnitude probability space. -/
theorem sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t0 : Fin steps) {ι : Type*} [Fintype ι]
    (F : ElementwiseSample m n → CStarMatrix ι ι ℂ) :
    (sqMagTraceProbability (steps := steps) A hden).expectationCStarMatrix
      (fun samples => F (samples t0)) =
      (sqMagSampleProbability A hden).expectationCStarMatrix F := by
  classical
  rw [sqMagTraceProbability_expectationCStarMatrix_step_eq A hden t0 F]
  rw [FiniteProbability.expectationCStarMatrix_eq_sum_smul]
  simp [sqMagSampleProbability]

/-- One-step Tropp trace-MGF domination specialized to one coordinate of the
canonical Algorithm 1 squared-magnitude trace law.

This theorem has no hidden Lieb-concavity hypothesis: it uses
`FiniteProbability.expectationReal_trace_normed_exp_add_le`, whose Lieb
foundation is fully discharged in `Analysis/LiebTrace.lean`. -/
theorem sqMagTraceProbability_expectationReal_trace_normed_exp_add_step_le
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (t0 : Fin steps) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : ElementwiseSample m n → CStarMatrix ι ι ℂ}
    (hX : ∀ x, IsSelfAdjoint (X x)) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        (cstarMatrixTrace
          (NormedSpace.exp (H + X (samples t0)))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun x => NormedSpace.exp (X x)))))).re := by
  let P := sqMagTraceProbability (steps := steps) A hden
  have hbase :=
    FiniteProbability.expectationReal_trace_normed_exp_add_le
      P hH (X := fun samples => X (samples t0))
      (fun samples => hX (samples t0))
  have hmean :
      P.expectationCStarMatrix
        (fun samples => NormedSpace.exp (X (samples t0))) =
      (sqMagSampleProbability A hden).expectationCStarMatrix
        (fun x => NormedSpace.exp (X x)) :=
    sqMagTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
      A hden t0 (fun x => NormedSpace.exp (X x))
  simpa [P, hmean] using hbase

/-- The product trace mass of a trace obtained by appending one last sample
factors into the prefix trace mass times the one-sample mass. -/
theorem sqMagTraceProbMass_snoc {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ)
    (pref : ElementwiseTrace m n steps) (lastSample : ElementwiseSample m n) :
    sqMagTraceProbMass A (Fin.snoc pref lastSample) =
      sqMagTraceProbMass A pref * sqMagProb A lastSample.1 lastSample.2 := by
  classical
  unfold sqMagTraceProbMass
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Conditioning on the last sample for real-valued statistics under the
canonical Algorithm 1 product trace law.

This is the finite product-law identity needed by the independent-sum
trace-MGF induction: an expectation over a trace of length `steps + 1` splits
into an expectation over the prefix trace and a one-sample expectation over the
last coordinate. -/
theorem sqMagTraceProbability_expectationReal_succ_last_eq
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    (F : ElementwiseTrace m n steps → ElementwiseSample m n → ℝ) :
    (sqMagTraceProbability (steps := steps + 1) A hden).expectationReal
      (fun samples =>
        F (Fin.init samples) (samples (Fin.last steps))) =
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun pref =>
        (sqMagSampleProbability A hden).expectationReal
          (fun lastSample => F pref lastSample)) := by
  classical
  let e :
      ElementwiseSample m n × ElementwiseTrace m n steps ≃
        ElementwiseTrace m n (steps + 1) :=
    Fin.snocEquiv (fun _ : Fin (steps + 1) => ElementwiseSample m n)
  unfold FiniteProbability.expectationReal sqMagTraceProbability sqMagSampleProbability
  calc
    ∑ samples : ElementwiseTrace m n (steps + 1),
        sqMagTraceProbMass A samples *
          F (Fin.init samples) (samples (Fin.last steps))
        = ∑ p : ElementwiseSample m n × ElementwiseTrace m n steps,
            sqMagTraceProbMass A (Fin.snoc p.2 p.1) *
              F p.2 p.1 := by
            symm
            refine Fintype.sum_equiv e
              (fun p : ElementwiseSample m n × ElementwiseTrace m n steps =>
                sqMagTraceProbMass A (Fin.snoc p.2 p.1) * F p.2 p.1)
              (fun samples : ElementwiseTrace m n (steps + 1) =>
                sqMagTraceProbMass A samples *
                  F (Fin.init samples) (samples (Fin.last steps))) ?_
            intro p
            have hp :
                ((Fin.snocEquiv
                    (fun _ : Fin (steps + 1) => ElementwiseSample m n)) p) =
                  Fin.snoc p.2 p.1 := by
              rfl
            rw [hp]
            simp [Fin.init_snoc, Fin.snoc_last]
    _ = ∑ p : ElementwiseSample m n × ElementwiseTrace m n steps,
          (sqMagTraceProbMass A p.2 * sqMagProb A p.1.1 p.1.2) *
            F p.2 p.1 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [sqMagTraceProbMass_snoc]
    _ = ∑ pref : ElementwiseTrace m n steps,
          sqMagTraceProbMass A pref *
            (∑ lastSample : ElementwiseSample m n,
              sqMagProb A lastSample.1 lastSample.2 * F pref lastSample) := by
            rw [Fintype.sum_prod_type_right]
            apply Finset.sum_congr rfl
            intro pref _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro lastSample _
            ring

/-- Iterated iid trace-MGF domination for Algorithm 1's squared-magnitude
product trace law.

This is the first non-conditional independent-sum adapter above the one-step
Lieb/Tropp theorem: the expectation of the trace exponential of the sampled sum
is controlled by the trace exponential with one logarithmic mean increment per
sample. -/
theorem sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : ElementwiseSample m n → CStarMatrix ι ι ℂ}
    (hX : ∀ x, IsSelfAdjoint (X x)) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        (cstarMatrixTrace
          (NormedSpace.exp
            (H + ∑ t : Fin steps, X (samples t)))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + ∑ _t : Fin steps,
          CFC.log
            ((sqMagSampleProbability A hden).expectationCStarMatrix
              (fun x => NormedSpace.exp (X x)))))).re := by
  classical
  induction steps generalizing H with
  | zero =>
      exact le_of_eq (by
        simpa using
          (FiniteProbability.expectationReal_const
            (sqMagTraceProbability (steps := 0) A hden)
            ((cstarMatrixTrace (NormedSpace.exp H)).re)))
  | succ steps ih =>
      let K : CStarMatrix ι ι ℂ :=
        CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun x => NormedSpace.exp (X x)))
      have hsplit :
          (sqMagTraceProbability (steps := steps + 1) A hden).expectationReal
            (fun samples =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + ∑ t : Fin (steps + 1), X (samples t)))).re) =
          (sqMagTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (sqMagSampleProbability A hden).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) := by
        calc
          (sqMagTraceProbability (steps := steps + 1) A hden).expectationReal
              (fun samples =>
                (cstarMatrixTrace
                  (NormedSpace.exp
                    (H + ∑ t : Fin (steps + 1), X (samples t)))).re)
              =
            (sqMagTraceProbability (steps := steps + 1) A hden).expectationReal
              (fun samples =>
                (cstarMatrixTrace
                  (NormedSpace.exp
                    (H + (∑ t : Fin steps, X (Fin.init samples t) +
                      X (samples (Fin.last steps)))))).re) := by
                apply congrArg
                funext samples
                congr 3
                rw [Fin.sum_univ_castSucc]
                simp [Fin.init]
          _ =
            (sqMagTraceProbability (steps := steps) A hden).expectationReal
              (fun pref =>
                (sqMagSampleProbability A hden).expectationReal
                  (fun lastSample =>
                    (cstarMatrixTrace
                      (NormedSpace.exp
                        (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) :=
              sqMagTraceProbability_expectationReal_succ_last_eq A hden
                (fun pref lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)
      rw [hsplit]
      have hone :
          (sqMagTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (sqMagSampleProbability A hden).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re))
            ≤
          (sqMagTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + (∑ t : Fin steps, X (pref t) + K)))).re) := by
        apply FiniteProbability.expectationReal_mono
        intro pref
        have hHpref : IsSelfAdjoint (H + ∑ t : Fin steps, X (pref t)) := by
          exact hH.add
            (by
              simpa using
                (cstarMatrix_finset_sum_isSelfAdjoint
                  (s := (Finset.univ : Finset (Fin steps)))
                  (F := fun t : Fin steps => X (pref t))
                  (fun t _ => hX (pref t))))
        have hstep :=
          FiniteProbability.expectationReal_trace_normed_exp_add_le
            (sqMagSampleProbability A hden) hHpref hX
        simpa [K, add_assoc] using hstep
      refine le_trans hone ?_
      have hK : IsSelfAdjoint K := by
        dsimp [K]
        exact cstarMatrix_log_isSelfAdjoint _
      have hHplusK : IsSelfAdjoint (H + K) := hH.add hK
      have hrewrite :
          (sqMagTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + (∑ t : Fin steps, X (pref t) + K)))).re) =
          (sqMagTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  ((H + K) + ∑ t : Fin steps, X (pref t)))).re) := by
        apply congrArg
        funext pref
        congr 3
        ac_rfl
      rw [hrewrite]
      have htail := ih (H := H + K) hHplusK
      refine le_trans htail ?_
      exact le_of_eq (by
        dsimp [K]
        congr 3
        rw [Fin.sum_univ_castSucc]
        ac_rfl)

/-- The logarithmic trace-MGF upper bound produced by the iid C⋆ trace-MGF
iteration, but expressed for repository-native finite real matrices.

This definition keeps downstream Algorithm 1 specializations from repeating
the long `CFC.log (E exp X)` expression in theorem statements. -/
noncomputable def sqMagTraceProbabilityFiniteRealTraceMGFLogBound
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → ι → ℝ)
    (X : ElementwiseSample m n → ι → ι → ℝ) : ℝ :=
  (cstarMatrixTrace
    (NormedSpace.exp
      (finiteComplexCStarMatrix H + ∑ _t : Fin steps,
          CFC.log
            ((sqMagSampleProbability A hden).expectationCStarMatrix
              (fun x =>
                NormedSpace.exp (finiteComplexCStarMatrix (X x))))))).re

/-- Scalar trace-MGF bound from a one-step logarithmic-CGF Loewner bound.

If the repeated one-sample logarithmic mean increment is bounded by `c I`, then
the iid trace-MGF log-bound used by the finite-real concentration interface is
at most `d exp(steps * c)`.  This is the deterministic trace-scalarization
layer between the one-sample matrix-CGF theorem and the largest-eigenvalue
tail theorem. -/
theorem sqMagTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : ElementwiseSample m n → ι → ι → ℝ) {c : ℝ}
    (hK :
      CFC.log
          ((sqMagSampleProbability A hden).expectationCStarMatrix
            (fun x =>
              NormedSpace.exp (finiteComplexCStarMatrix (X x)))) ≤
        (c : ℂ) • (1 : CStarMatrix ι ι ℂ)) :
    sqMagTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := steps) A hden
      (fun _a _b : ι => 0) X ≤
      (Fintype.card ι : ℝ) * Real.exp ((steps : ℝ) * c) := by
  classical
  let K : CStarMatrix ι ι ℂ :=
    CFC.log
      ((sqMagSampleProbability A hden).expectationCStarMatrix
        (fun x =>
          NormedSpace.exp (finiteComplexCStarMatrix (X x))))
  have hKsa : IsSelfAdjoint K := by
    dsimp [K]
    exact cstarMatrix_log_isSelfAdjoint _
  have hsumsa :
      IsSelfAdjoint
        (finiteComplexCStarMatrix (fun _a _b : ι => 0) +
          ∑ _t : Fin steps, K) := by
    have hzero : IsSelfAdjoint (finiteComplexCStarMatrix (fun _a _b : ι => 0)) := by
      rw [finiteComplexCStarMatrix_zero]
      simp
    exact hzero.add
      (cstarMatrix_finset_sum_isSelfAdjoint
        (s := (Finset.univ : Finset (Fin steps)))
        (F := fun _t : Fin steps => K)
        (fun _t _ht => hKsa))
  have hsumLe :
      finiteComplexCStarMatrix (fun _a _b : ι => 0) + ∑ _t : Fin steps, K ≤
        (((steps : ℝ) * c : ℝ) : ℂ) • (1 : CStarMatrix ι ι ℂ) := by
    rw [finiteComplexCStarMatrix_zero, zero_add]
    have hsum :
        (∑ _t : Fin steps, K) ≤
          ∑ _t : Fin steps, ((c : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
      exact Finset.sum_le_sum (fun _t _ht => by simpa [K] using hK)
    refine hsum.trans ?_
    rw [cstarMatrix_fin_sum_const_complex_smul_one]
    simp [mul_comm]
  simpa [sqMagTraceProbabilityFiniteRealTraceMGFLogBound, K] using
    cstarMatrixTrace_normedSpace_exp_re_le_card_mul_exp_of_le_real_smul_one
      hsumsa hsumLe

/-- Finite-real trace-MGF domination obtained by composing the C⋆ iid
trace-MGF theorem with the finite-real matrix-exponential trace bridge.

This is the adapter that lets the finite real matrix-concentration layer consume
the no-hidden-Lieb C⋆ trace-MGF iteration.  It is still not yet a Bernstein
tail bound: the logarithmic mean increment on the right must be bounded by a
scalar-identity CGF before the existing eigenvalue Markov interfaces can be
applied. -/
theorem sqMagTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < sqMagProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : ι → ι → ℝ} (hH : IsSymmetricFiniteMatrix H)
    {X : ElementwiseSample m n → ι → ι → ℝ}
    (hX : ∀ x, IsSymmetricFiniteMatrix (X x)) :
    (sqMagTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun i j => H i j + ∑ t : Fin steps, X (samples t) i j))) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (finiteComplexCStarMatrix H + ∑ _t : Fin steps,
          CFC.log
            ((sqMagSampleProbability A hden).expectationCStarMatrix
              (fun x =>
                NormedSpace.exp (finiteComplexCStarMatrix (X x))))))).re := by
  classical
  let P := sqMagTraceProbability (steps := steps) A hden
  let Hc : CStarMatrix ι ι ℂ := finiteComplexCStarMatrix H
  let Xc : ElementwiseSample m n → CStarMatrix ι ι ℂ :=
    fun x => finiteComplexCStarMatrix (X x)
  have hembed :
      ∀ samples : ElementwiseTrace m n steps,
        finiteComplexCStarMatrix
          (fun i j => H i j + ∑ t : Fin steps, X (samples t) i j) =
        Hc + ∑ t : Fin steps, Xc (samples t) := by
    intro samples
    calc
      finiteComplexCStarMatrix
          (fun i j => H i j + ∑ t : Fin steps, X (samples t) i j)
          =
        finiteComplexCStarMatrix H +
          finiteComplexCStarMatrix
            (fun i j => ∑ t : Fin steps, X (samples t) i j) := by
            rw [finiteComplexCStarMatrix_add]
      _ = Hc + ∑ t : Fin steps, Xc (samples t) := by
            dsimp [Hc, Xc]
            rw [show
                finiteComplexCStarMatrix
                    (fun i j => ∑ t : Fin steps, X (samples t) i j) =
                  ∑ t : Fin steps,
                    finiteComplexCStarMatrix (X (samples t)) by
              simpa using
                (finiteComplexCStarMatrix_finset_sum
                  (s := (Finset.univ : Finset (Fin steps)))
                  (F := fun t : Fin steps => X (samples t)))]
  have htrace_eq :
      P.expectationReal
        (fun samples =>
          finiteTrace
            (finiteMatrixExp
              (fun i j => H i j + ∑ t : Fin steps, X (samples t) i j))) =
      P.expectationReal
        (fun samples =>
          (cstarMatrixTrace
            (NormedSpace.exp
              (Hc + ∑ t : Fin steps, Xc (samples t)))).re) := by
    unfold P FiniteProbability.expectationReal
    apply Finset.sum_congr rfl
    intro samples _
    have hsample :
        finiteTrace
            (finiteMatrixExp
              (fun i j => H i j + ∑ t : Fin steps, X (samples t) i j)) =
          (cstarMatrixTrace
            (NormedSpace.exp
              (Hc + ∑ t : Fin steps, Xc (samples t)))).re := by
      rw [← cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re
        (fun i j => H i j + ∑ t : Fin steps, X (samples t) i j)]
      rw [hembed samples]
    simpa using
      congrArg (fun z => (sqMagTraceProbability A hden).prob samples * z) hsample
  rw [htrace_eq]
  have hHc : IsSelfAdjoint Hc := by
    dsimp [Hc]
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric H hH
  have hXc : ∀ x, IsSelfAdjoint (Xc x) := by
    intro x
    dsimp [Xc]
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric (X x) (hX x)
  simpa [Hc, Xc, P] using
    (sqMagTraceProbability_expectationReal_trace_normed_exp_add_sum_le
      (steps := steps) A hden (H := Hc) hHc (X := Xc) hXc)


end NumStability
