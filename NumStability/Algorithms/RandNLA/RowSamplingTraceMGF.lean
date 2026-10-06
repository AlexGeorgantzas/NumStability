-- Algorithms/RandNLA/RowSamplingTraceMGF.lean
--
-- Trace-MGF adapters for Algorithm 2 row-sampling product laws.
--
-- Reference:
-- Petros Drineas and Michael W. Mahoney, "RandNLA: Randomized Numerical
-- Linear Algebra," Communications of the ACM 59(6), 80-90, 2016.
-- https://dl.acm.org/doi/10.1145/2842602

import NumStability.Algorithms.RandNLA.RowSamplingGram
import NumStability.Analysis.LiebTrace
import Mathlib.Data.Fin.Tuple.Basic

namespace NumStability

open scoped BigOperators ComplexOrder

/-!
## Row-sampling product trace-MGF adapters

The finite-dimensional Lieb theorem in `Analysis/LiebTrace.lean` already proves
Tropp's one-step trace-MGF inequality for arbitrary finite probability spaces.
This file connects that theorem to Algorithm 2's independent row-trace law.

The results here are proof-route infrastructure for the sharper leverage-score
equation (7) analysis.  They do not, by themselves, prove a matrix Chernoff or
subspace-embedding tail bound.
-/

/-- The one-sample norm-squared row law behind Algorithm 2. -/
noncomputable def rowSqNormSampleProbability {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A) :
    FiniteProbability (RowSample m) where
  prob := fun i => rowSqNormProb A i
  prob_nonneg := fun i => rowSqNormProb_nonneg A hden i
  prob_sum := rowSqNormProb_sum_eq_one A hden.ne'

/-- Complex-valued marginal expectation for one coordinate of the Algorithm 2
row product trace law. -/
theorem rowSqNormTraceProbability_expectationComplex_step_eq
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (t0 : Fin steps) (f : RowSample m → ℂ) :
    (rowSqNormTraceProbability (steps := steps) A hden).expectationComplex
      (fun samples => f (samples t0)) =
      ∑ i : RowSample m, (rowSqNormProb A i : ℂ) * f i := by
  classical
  apply Complex.ext
  · have hre :=
      rowSqNormTraceProbMass_marginal_one A hden.ne' t0
        (fun i : RowSample m => (f i).re)
    simpa [FiniteProbability.expectationComplex, rowSqNormTraceProbability] using hre
  · have him :=
      rowSqNormTraceProbMass_marginal_one A hden.ne' t0
        (fun i : RowSample m => (f i).im)
    simpa [FiniteProbability.expectationComplex, rowSqNormTraceProbability] using him

/-- C⋆-matrix-valued marginal expectation for one coordinate of the Algorithm 2
row product trace law. -/
theorem rowSqNormTraceProbability_expectationCStarMatrix_step_eq
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (t0 : Fin steps) {ι : Type*} [Fintype ι]
    (F : RowSample m → CStarMatrix ι ι ℂ) :
    (rowSqNormTraceProbability (steps := steps) A hden).expectationCStarMatrix
      (fun samples => F (samples t0)) =
      ∑ i : RowSample m, (rowSqNormProb A i : ℂ) • F i := by
  classical
  ext a b
  have h :=
    rowSqNormTraceProbability_expectationComplex_step_eq A hden t0
      (fun i : RowSample m => F i a b)
  change
    (rowSqNormTraceProbability (steps := steps) A hden).expectationComplex
        (fun samples => F (samples t0) a b) =
      (∑ i : RowSample m, (rowSqNormProb A i : ℂ) • F i) a b
  rw [show
      (∑ i : RowSample m, (rowSqNormProb A i : ℂ) • F i) a b =
        ∑ i : RowSample m,
          ((rowSqNormProb A i : ℂ) • F i) a b by
    exact Matrix.sum_apply a b Finset.univ
      (fun i => ((rowSqNormProb A i : ℂ) • F i :
        CStarMatrix ι ι ℂ))]
  simpa [smul_eq_mul] using h

/-- The C⋆ marginal expectation agrees with the explicit one-sample row
probability space. -/
theorem rowSqNormTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (t0 : Fin steps) {ι : Type*} [Fintype ι]
    (F : RowSample m → CStarMatrix ι ι ℂ) :
    (rowSqNormTraceProbability (steps := steps) A hden).expectationCStarMatrix
      (fun samples => F (samples t0)) =
      (rowSqNormSampleProbability A hden).expectationCStarMatrix F := by
  classical
  rw [rowSqNormTraceProbability_expectationCStarMatrix_step_eq A hden t0 F]
  rw [FiniteProbability.expectationCStarMatrix_eq_sum_smul]
  simp [rowSqNormSampleProbability]

/-- One-step Tropp trace-MGF domination specialized to one coordinate of the
Algorithm 2 row trace law.

This theorem has no hidden Lieb-concavity hypothesis: it uses
`FiniteProbability.expectationReal_trace_normed_exp_add_le`, whose Lieb
foundation is discharged in `Analysis/LiebTrace.lean`. -/
theorem rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_step_le
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (t0 : Fin steps) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : RowSample m → CStarMatrix ι ι ℂ}
    (hX : ∀ i, IsSelfAdjoint (X i)) :
    (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        (cstarMatrixTrace
          (NormedSpace.exp (H + X (samples t0)))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + CFC.log
          ((rowSqNormSampleProbability A hden).expectationCStarMatrix
            (fun i => NormedSpace.exp (X i)))))).re := by
  let P := rowSqNormTraceProbability (steps := steps) A hden
  have hbase :=
    FiniteProbability.expectationReal_trace_normed_exp_add_le
      P hH (X := fun samples => X (samples t0))
      (fun samples => hX (samples t0))
  have hmean :
      P.expectationCStarMatrix
        (fun samples => NormedSpace.exp (X (samples t0))) =
      (rowSqNormSampleProbability A hden).expectationCStarMatrix
        (fun i => NormedSpace.exp (X i)) :=
    rowSqNormTraceProbability_expectationCStarMatrix_step_eq_sampleExpectation
      A hden t0 (fun i => NormedSpace.exp (X i))
  simpa [P, hmean] using hbase

/-- The row product trace mass of a trace obtained by appending one last sample
factors into the prefix trace mass times the one-sample row mass. -/
theorem rowSqNormTraceProbMass_snoc {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ)
    (pref : RowTrace m steps) (lastSample : RowSample m) :
    rowSqNormTraceProbMass A (Fin.snoc pref lastSample) =
      rowSqNormTraceProbMass A pref * rowSqNormProb A lastSample := by
  classical
  unfold rowSqNormTraceProbMass
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Conditioning on the last row sample for real-valued statistics under the
Algorithm 2 product trace law. -/
theorem rowSqNormTraceProbability_expectationReal_succ_last_eq
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    (F : RowTrace m steps → RowSample m → ℝ) :
    (rowSqNormTraceProbability (steps := steps + 1) A hden).expectationReal
      (fun samples =>
        F (Fin.init samples) (samples (Fin.last steps))) =
    (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
      (fun pref =>
        (rowSqNormSampleProbability A hden).expectationReal
          (fun lastSample => F pref lastSample)) := by
  classical
  let e :
      RowSample m × RowTrace m steps ≃
        RowTrace m (steps + 1) :=
    Fin.snocEquiv (fun _ : Fin (steps + 1) => RowSample m)
  unfold FiniteProbability.expectationReal rowSqNormTraceProbability
    rowSqNormSampleProbability
  calc
    ∑ samples : RowTrace m (steps + 1),
        rowSqNormTraceProbMass A samples *
          F (Fin.init samples) (samples (Fin.last steps))
        = ∑ p : RowSample m × RowTrace m steps,
            rowSqNormTraceProbMass A (Fin.snoc p.2 p.1) *
              F p.2 p.1 := by
            symm
            refine Fintype.sum_equiv e
              (fun p : RowSample m × RowTrace m steps =>
                rowSqNormTraceProbMass A (Fin.snoc p.2 p.1) * F p.2 p.1)
              (fun samples : RowTrace m (steps + 1) =>
                rowSqNormTraceProbMass A samples *
                  F (Fin.init samples) (samples (Fin.last steps))) ?_
            intro p
            have hp :
                ((Fin.snocEquiv
                    (fun _ : Fin (steps + 1) => RowSample m)) p) =
                  Fin.snoc p.2 p.1 := by
              rfl
            rw [hp]
            simp [Fin.init_snoc, Fin.snoc_last]
    _ = ∑ p : RowSample m × RowTrace m steps,
          (rowSqNormTraceProbMass A p.2 * rowSqNormProb A p.1) *
            F p.2 p.1 := by
            apply Finset.sum_congr rfl
            intro p _
            rw [rowSqNormTraceProbMass_snoc]
    _ = ∑ pref : RowTrace m steps,
          rowSqNormTraceProbMass A pref *
            (∑ lastSample : RowSample m,
              rowSqNormProb A lastSample * F pref lastSample) := by
            rw [Fintype.sum_prod_type_right]
            apply Finset.sum_congr rfl
            intro pref _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro lastSample _
            ring

/-- Iterated iid trace-MGF domination for Algorithm 2's row product trace law.

This is the product-law induction layer needed before proving a matrix
Chernoff/Bernstein tail for leverage-score covariance sums. -/
theorem rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : CStarMatrix ι ι ℂ} (hH : IsSelfAdjoint H)
    {X : RowSample m → CStarMatrix ι ι ℂ}
    (hX : ∀ i, IsSelfAdjoint (X i)) :
    (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        (cstarMatrixTrace
          (NormedSpace.exp
            (H + ∑ t : Fin steps, X (samples t)))).re) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (H + ∑ _t : Fin steps,
          CFC.log
            ((rowSqNormSampleProbability A hden).expectationCStarMatrix
              (fun i => NormedSpace.exp (X i)))))).re := by
  classical
  induction steps generalizing H with
  | zero =>
      exact le_of_eq (by
        simpa using
          (FiniteProbability.expectationReal_const
            (rowSqNormTraceProbability (steps := 0) A hden)
            ((cstarMatrixTrace (NormedSpace.exp H)).re)))
  | succ steps ih =>
      let K : CStarMatrix ι ι ℂ :=
        CFC.log
          ((rowSqNormSampleProbability A hden).expectationCStarMatrix
            (fun i => NormedSpace.exp (X i)))
      have hsplit :
          (rowSqNormTraceProbability (steps := steps + 1) A hden).expectationReal
            (fun samples =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + ∑ t : Fin (steps + 1), X (samples t)))).re) =
          (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (rowSqNormSampleProbability A hden).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) := by
        calc
          (rowSqNormTraceProbability (steps := steps + 1) A hden).expectationReal
              (fun samples =>
                (cstarMatrixTrace
                  (NormedSpace.exp
                    (H + ∑ t : Fin (steps + 1), X (samples t)))).re)
              =
            (rowSqNormTraceProbability (steps := steps + 1) A hden).expectationReal
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
            (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
              (fun pref =>
                (rowSqNormSampleProbability A hden).expectationReal
                  (fun lastSample =>
                    (cstarMatrixTrace
                      (NormedSpace.exp
                        (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)) :=
              rowSqNormTraceProbability_expectationReal_succ_last_eq A hden
                (fun pref lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re)
      rw [hsplit]
      have hone :
          (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (rowSqNormSampleProbability A hden).expectationReal
                (fun lastSample =>
                  (cstarMatrixTrace
                    (NormedSpace.exp
                      (H + (∑ t : Fin steps, X (pref t) + X lastSample)))).re))
            ≤
          (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
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
            (rowSqNormSampleProbability A hden) hHpref hX
        simpa [K, add_assoc] using hstep
      refine le_trans hone ?_
      have hK : IsSelfAdjoint K := by
        dsimp [K]
        exact cstarMatrix_log_isSelfAdjoint _
      have hHplusK : IsSelfAdjoint (H + K) := hH.add hK
      have hrewrite :
          (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
            (fun pref =>
              (cstarMatrixTrace
                (NormedSpace.exp
                  (H + (∑ t : Fin steps, X (pref t) + K)))).re) =
          (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
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

/-- Finite-real trace-MGF domination obtained by composing the C⋆ iid
trace-MGF theorem with the finite-real matrix-exponential trace bridge. -/
theorem rowSqNormTraceProbability_expectationReal_finiteTrace_finiteMatrixExp_add_sum_le
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H : ι → ι → ℝ} (hH : IsSymmetricFiniteMatrix H)
    {X : RowSample m → ι → ι → ℝ}
    (hX : ∀ i, IsSymmetricFiniteMatrix (X i)) :
    (rowSqNormTraceProbability (steps := steps) A hden).expectationReal
      (fun samples =>
        finiteTrace
          (finiteMatrixExp
            (fun a b => H a b + ∑ t : Fin steps, X (samples t) a b))) ≤
    (cstarMatrixTrace
      (NormedSpace.exp
        (finiteComplexCStarMatrix H + ∑ _t : Fin steps,
          CFC.log
            ((rowSqNormSampleProbability A hden).expectationCStarMatrix
              (fun i =>
                NormedSpace.exp (finiteComplexCStarMatrix (X i))))))).re := by
  classical
  let P := rowSqNormTraceProbability (steps := steps) A hden
  let Hc : CStarMatrix ι ι ℂ := finiteComplexCStarMatrix H
  let Xc : RowSample m → CStarMatrix ι ι ℂ :=
    fun i => finiteComplexCStarMatrix (X i)
  have hembed :
      ∀ samples : RowTrace m steps,
        finiteComplexCStarMatrix
          (fun a b => H a b + ∑ t : Fin steps, X (samples t) a b) =
        Hc + ∑ t : Fin steps, Xc (samples t) := by
    intro samples
    calc
      finiteComplexCStarMatrix
          (fun a b => H a b + ∑ t : Fin steps, X (samples t) a b)
          =
        finiteComplexCStarMatrix H +
          finiteComplexCStarMatrix
            (fun a b => ∑ t : Fin steps, X (samples t) a b) := by
            rw [finiteComplexCStarMatrix_add]
      _ = Hc + ∑ t : Fin steps, Xc (samples t) := by
            dsimp [Hc, Xc]
            rw [show
                finiteComplexCStarMatrix
                    (fun a b => ∑ t : Fin steps, X (samples t) a b) =
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
              (fun a b => H a b + ∑ t : Fin steps, X (samples t) a b))) =
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
              (fun a b => H a b + ∑ t : Fin steps, X (samples t) a b)) =
          (cstarMatrixTrace
            (NormedSpace.exp
              (Hc + ∑ t : Fin steps, Xc (samples t)))).re := by
      rw [← cstarMatrixTrace_normed_exp_finiteComplexCStarMatrix_re
        (fun a b => H a b + ∑ t : Fin steps, X (samples t) a b)]
      rw [hembed samples]
    simpa using
      congrArg (fun z => (rowSqNormTraceProbability A hden).prob samples * z) hsample
  rw [htrace_eq]
  have hHc : IsSelfAdjoint Hc := by
    dsimp [Hc]
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric H hH
  have hXc : ∀ i, IsSelfAdjoint (Xc i) := by
    intro i
    dsimp [Xc]
    exact finiteComplexCStarMatrix_isSelfAdjoint_of_symmetric (X i) (hX i)
  simpa [Hc, Xc, P] using
    (rowSqNormTraceProbability_expectationReal_trace_normed_exp_add_sum_le
      (steps := steps) A hden (H := Hc) hHc (X := Xc) hXc)

/-- The logarithmic trace-MGF upper bound produced by the iid row-trace C⋆
trace-MGF iteration, expressed for repository-native finite real matrices. -/
noncomputable def rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : ι → ι → ℝ)
    (X : RowSample m → ι → ι → ℝ) : ℝ :=
  (cstarMatrixTrace
    (NormedSpace.exp
      (finiteComplexCStarMatrix H + ∑ _t : Fin steps,
          CFC.log
            ((rowSqNormSampleProbability A hden).expectationCStarMatrix
              (fun i =>
                NormedSpace.exp (finiteComplexCStarMatrix (X i))))))).re

/-- Scalar trace-MGF bound from a one-step logarithmic-CGF Loewner bound for
Algorithm 2 row sampling.

If the repeated one-sample logarithmic mean increment is bounded by `c I`, then
the iid row-trace MGF log-bound is at most `d * exp(steps * c)`. -/
theorem rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound_zero_le_card_mul_exp_of_log_le_real_smul_one
    {m n steps : ℕ}
    (A : Fin m → Fin n → ℝ) (hden : 0 < rowSqNormProbDen A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : RowSample m → ι → ι → ℝ) {c : ℝ}
    (hK :
      CFC.log
          ((rowSqNormSampleProbability A hden).expectationCStarMatrix
            (fun i =>
              NormedSpace.exp (finiteComplexCStarMatrix (X i)))) ≤
        (c : ℂ) • (1 : CStarMatrix ι ι ℂ)) :
    rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound
      (steps := steps) A hden
      (fun _a _b : ι => 0) X ≤
      (Fintype.card ι : ℝ) * Real.exp ((steps : ℝ) * c) := by
  classical
  let K : CStarMatrix ι ι ℂ :=
    CFC.log
      ((rowSqNormSampleProbability A hden).expectationCStarMatrix
        (fun i =>
          NormedSpace.exp (finiteComplexCStarMatrix (X i))))
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
  simpa [rowSqNormTraceProbabilityFiniteRealTraceMGFLogBound, K] using
    cstarMatrixTrace_normedSpace_exp_re_le_card_mul_exp_of_le_real_smul_one
      hsumsa hsumLe

end NumStability
