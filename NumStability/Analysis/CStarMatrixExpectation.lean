-- Analysis/CStarMatrixExpectation.lean
--
-- Finite-probability expectations and order bridges for complex
-- C⋆-matrix-valued random variables used by future trace-MGF arguments.

import NumStability.Analysis.CStarMatrixTrace
import NumStability.Analysis.FiniteProbability

namespace NumStability

open scoped BigOperators ComplexOrder

namespace FiniteProbability

variable {Ω : Type*} [Fintype Ω]

/-!
## Complex and C⋆-matrix expectations

The Lieb/Tropp trace-MGF route needs expressions such as
`E[exp X]` for random self-adjoint complex matrices.  This file adds the
finite-probability expectation and order vocabulary needed to state that route
inside the repository's `FiniteProbability` model.

It deliberately does not prove trace-MGF domination, Lieb trace concavity,
matrix Bernstein, or any RandNLA paper-level concentration theorem.
-/

/-- Expectation of a complex-valued random variable on a finite probability
space. -/
noncomputable def expectationComplex (P : FiniteProbability Ω)
    (X : Ω → ℂ) : ℂ :=
  ∑ ω, (P.prob ω : ℂ) * X ω

/-- Finite sums commute with complex expectation. -/
theorem expectationComplex_sum {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (X : ι → Ω → ℂ) :
    P.expectationComplex (fun ω => ∑ i, X i ω) =
      ∑ i, P.expectationComplex (fun ω => X i ω) := by
  classical
  unfold expectationComplex
  calc
    ∑ ω, (P.prob ω : ℂ) * (∑ i, X i ω)
        = ∑ ω, ∑ i, (P.prob ω : ℂ) * X i ω := by
            apply Finset.sum_congr rfl
            intro ω _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ ω, (P.prob ω : ℂ) * X i ω := by
            rw [Finset.sum_comm]

/-- Complex expectation agrees with real expectation after coercion. -/
theorem expectationComplex_ofReal
    (P : FiniteProbability Ω) (X : Ω → ℝ) :
    P.expectationComplex (fun ω => (X ω : ℂ)) =
      (P.expectationReal X : ℂ) := by
  classical
  simp [expectationComplex, expectationReal]

/-- The real part of a complex expectation is the expectation of real parts. -/
theorem expectationComplex_re
    (P : FiniteProbability Ω) (X : Ω → ℂ) :
    (P.expectationComplex X).re =
      P.expectationReal (fun ω => (X ω).re) := by
  classical
  simp [expectationComplex, expectationReal]

/-- Constant complex random variables have their constant as expectation. -/
theorem expectationComplex_const
    (P : FiniteProbability Ω) (c : ℂ) :
    P.expectationComplex (fun _ => c) = c := by
  classical
  unfold expectationComplex
  calc
    ∑ ω, (P.prob ω : ℂ) * c = (∑ ω, (P.prob ω : ℂ)) * c := by
        rw [Finset.sum_mul]
    _ = c := by
        rw [← Complex.ofReal_sum, P.prob_sum]
        simp

/-- Additivity of complex expectation. -/
theorem expectationComplex_add
    (P : FiniteProbability Ω) (X Y : Ω → ℂ) :
    P.expectationComplex (fun ω => X ω + Y ω) =
      P.expectationComplex X + P.expectationComplex Y := by
  classical
  unfold expectationComplex
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Homogeneity of complex expectation. -/
theorem expectationComplex_smul
    (P : FiniteProbability Ω) (a : ℂ) (X : Ω → ℂ) :
    P.expectationComplex (fun ω => a * X ω) =
      a * P.expectationComplex X := by
  classical
  unfold expectationComplex
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Entrywise expectation of a complex C⋆-matrix-valued random variable. -/
noncomputable def expectationCStarMatrix {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (X : Ω → CStarMatrix ι ι ℂ) :
    CStarMatrix ι ι ℂ :=
  CStarMatrix.ofMatrix
    (fun i j => P.expectationComplex (fun ω => X ω i j))

@[simp]
theorem expectationCStarMatrix_apply {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (X : Ω → CStarMatrix ι ι ℂ) (i j : ι) :
    P.expectationCStarMatrix X i j =
      P.expectationComplex (fun ω => X ω i j) := by
  rfl

/-- C⋆-matrix trace commutes with finite-probability expectation. -/
theorem cstarMatrixTrace_expectationCStarMatrix {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (X : Ω → CStarMatrix ι ι ℂ) :
    cstarMatrixTrace (P.expectationCStarMatrix X) =
      P.expectationComplex (fun ω => cstarMatrixTrace (X ω)) := by
  classical
  change (∑ i, P.expectationComplex (fun ω => X ω i i)) =
    P.expectationComplex (fun ω => ∑ i, X ω i i)
  rw [expectationComplex_sum]

/-- Entrywise expectation commutes with embedding finite real matrices as
complex C⋆-matrices. -/
theorem expectationCStarMatrix_finiteComplexCStarMatrix {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ) :
    P.expectationCStarMatrix (fun ω => finiteComplexCStarMatrix (M ω)) =
      finiteComplexCStarMatrix
        (fun i j => P.expectationReal (fun ω => M ω i j)) := by
  ext i j
  simp [expectationComplex_ofReal]

/-- Constant C⋆-matrix random variables have their constant as expectation. -/
theorem expectationCStarMatrix_const {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix (fun _ => M) = M := by
  ext i j
  simp [expectationComplex_const]

/-- Additivity of C⋆-matrix expectation. -/
theorem expectationCStarMatrix_add {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M N : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix (fun ω => M ω + N ω) =
      P.expectationCStarMatrix M + P.expectationCStarMatrix N := by
  ext i j
  simp [expectationComplex_add]

/-- Homogeneity of C⋆-matrix expectation. -/
theorem expectationCStarMatrix_smul {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (a : ℂ) (M : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix (fun ω => a • M ω) =
      a • P.expectationCStarMatrix M := by
  ext i j
  simp [expectationComplex_smul, smul_eq_mul]

/-- Homogeneity of C⋆-matrix expectation for real scalar multiplication.

The matrix-CGF bounds are naturally stated with real parameters such as
`theta` and Bernstein's quadratic coefficient.  This wrapper keeps those
statements in the real scalar notation used by functional calculus. -/
theorem expectationCStarMatrix_real_smul {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (a : ℝ) (M : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix (fun ω => a • M ω) =
      a • P.expectationCStarMatrix M := by
  change P.expectationCStarMatrix (fun ω => (a : ℂ) • M ω) =
    (a : ℂ) • P.expectationCStarMatrix M
  exact expectationCStarMatrix_smul P (a : ℂ) M

/-- Entrywise C⋆-matrix expectation is the same as the finite weighted matrix
sum. -/
theorem expectationCStarMatrix_eq_sum_smul {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix M = ∑ ω, (P.prob ω : ℂ) • M ω := by
  ext i j
  rw [show (∑ ω, (P.prob ω : ℂ) • M ω) i j =
      ∑ ω, ((P.prob ω : ℂ) • M ω) i j by
    exact Matrix.sum_apply i j Finset.univ
      (fun ω => ((P.prob ω : ℂ) • M ω : CStarMatrix ι ι ℂ))]
  simp [expectationCStarMatrix, expectationComplex, smul_eq_mul]

/-- Entrywise C⋆-matrix expectation as a real weighted finite matrix sum. -/
theorem expectationCStarMatrix_eq_sum_real_smul {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix M = ∑ ω, P.prob ω • M ω := by
  ext i j
  rw [show (∑ ω, P.prob ω • M ω) i j =
      ∑ ω, (P.prob ω • M ω) i j by
    exact Matrix.sum_apply i j Finset.univ
      (fun ω => (P.prob ω • M ω : CStarMatrix ι ι ℂ))]
  simp [expectationCStarMatrix, expectationComplex]

/-- Finite Jensen for concave real-valued functions of C⋆-matrix random
variables, stated with the repository-native C⋆ expectation.  This is the
finite-probability Jensen wrapper needed after a future formal proof of Lieb's
trace concavity.  It does not assert that any particular trace-exponential
function is concave. -/
theorem expectationReal_le_of_concaveOn_expectationCStarMatrix
    {ι : Type*} [Fintype ι] (P : FiniteProbability Ω)
    {s : Set (CStarMatrix ι ι ℂ)}
    {f : CStarMatrix ι ι ℂ → ℝ}
    {M : Ω → CStarMatrix ι ι ℂ}
    (hf : ConcaveOn ℝ s f) (hM : ∀ ω, M ω ∈ s) :
    P.expectationReal (fun ω => f (M ω)) ≤
      f (P.expectationCStarMatrix M) := by
  rw [expectationCStarMatrix_eq_sum_real_smul]
  exact P.expectationReal_le_of_concaveOn hf hM

/-- Conditional one-step trace-exponential Jensen adapter for the Lieb/Tropp
route.

If the map `A ↦ Re tr(exp(H + log A))` is concave on a domain containing the
matrix random variable `M`, then finite Jensen moves expectation inside the
C⋆-matrix expectation.  This is exactly the finite-probability step after
Lieb's trace-concavity theorem; the concavity hypothesis is deliberately
explicit and is not proved here. -/
theorem expectationReal_trace_cfc_exp_add_log_le_of_concaveOn
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : FiniteProbability Ω)
    (H : CStarMatrix ι ι ℂ)
    {s : Set (CStarMatrix ι ι ℂ)}
    {M : Ω → CStarMatrix ι ι ℂ}
    (hconcave :
      ConcaveOn ℝ s
        (fun A =>
          (cstarMatrixTrace
            (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A))).re))
    (hM : ∀ ω, M ω ∈ s) :
    P.expectationReal
        (fun ω =>
          (cstarMatrixTrace
            (cfc (p := IsStarNormal) Complex.exp
              (H + CFC.log (M ω)))).re) ≤
      (cstarMatrixTrace
        (cfc (p := IsStarNormal) Complex.exp
          (H + CFC.log (P.expectationCStarMatrix M)))).re := by
  exact
    P.expectationReal_le_of_concaveOn_expectationCStarMatrix
      (s := s)
      (f := fun A =>
        (cstarMatrixTrace
          (cfc (p := IsStarNormal) Complex.exp (H + CFC.log A))).re)
      hconcave hM

/-- C⋆-matrix expectation preserves nonnegativity. -/
theorem expectationCStarMatrix_nonneg {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ)
    (hM : ∀ ω, 0 ≤ M ω) :
    0 ≤ P.expectationCStarMatrix M := by
  rw [expectationCStarMatrix_eq_sum_smul]
  apply Finset.sum_nonneg
  intro ω _hω
  exact smul_nonneg
    (show 0 ≤ (P.prob ω : ℂ) by exact_mod_cast P.prob_nonneg ω)
    (hM ω)

/-- C⋆-matrix expectation preserves nonnegativity when the nonnegativity
hypothesis is needed only on positive-probability atoms.  Zero-probability
atoms contribute the zero matrix, so this is the support-aware version used by
sampling laws whose pointwise side conditions are proved from `0 < prob`. -/
theorem expectationCStarMatrix_nonneg_of_prob_pos {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ)
    (hM : ∀ ω, 0 < P.prob ω → 0 ≤ M ω) :
    0 ≤ P.expectationCStarMatrix M := by
  classical
  rw [expectationCStarMatrix_eq_sum_smul]
  apply Finset.sum_nonneg
  intro ω _hω
  by_cases hprob : P.prob ω = 0
  · simp [hprob]
  · have hprob_pos : 0 < P.prob ω :=
      lt_of_le_of_ne (P.prob_nonneg ω) (Ne.symm hprob)
    exact smul_nonneg
      (show 0 ≤ (P.prob ω : ℂ) by exact_mod_cast P.prob_nonneg ω)
      (hM ω hprob_pos)

/-- C⋆-matrix expectation preserves strict positivity for finite probability
laws when every sampled matrix is strictly positive.

This is the domain lemma needed before taking `log (E[exp X])` in the
Tropp/Lieb trace-MGF route.  It uses only finite support: one probability atom
has positive mass, that atom contributes a strictly positive summand, and all
remaining summands are nonnegative. -/
theorem expectationCStarMatrix_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ)
    (hM : ∀ ω, IsStrictlyPositive (M ω)) :
    IsStrictlyPositive (P.expectationCStarMatrix M) := by
  classical
  rw [expectationCStarMatrix_eq_sum_smul]
  rcases P.exists_prob_pos with ⟨ω0, hω0⟩
  rw [← Finset.add_sum_erase (Finset.univ : Finset Ω)
      (fun ω => (P.prob ω : ℂ) • M ω) (Finset.mem_univ ω0)]
  have hstrict : IsStrictlyPositive ((P.prob ω0 : ℂ) • M ω0) := by
    exact IsStrictlyPositive.smul
      (show 0 < (P.prob ω0 : ℂ) by exact_mod_cast hω0) (hM ω0)
  have hrest :
      0 ≤ ∑ ω ∈ (Finset.univ : Finset Ω).erase ω0,
        (P.prob ω : ℂ) • M ω := by
    apply Finset.sum_nonneg
    intro ω _hω
    exact smul_nonneg
      (show 0 ≤ (P.prob ω : ℂ) by exact_mod_cast P.prob_nonneg ω)
      (hM ω).nonneg
  exact hstrict.add_nonneg hrest

/-- Negation commutes with C⋆-matrix expectation. -/
theorem expectationCStarMatrix_neg {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix (fun ω => -M ω) =
      -P.expectationCStarMatrix M := by
  ext i j
  simp [expectationCStarMatrix, expectationComplex]

/-- Subtraction commutes with C⋆-matrix expectation. -/
theorem expectationCStarMatrix_sub {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M N : Ω → CStarMatrix ι ι ℂ) :
    P.expectationCStarMatrix (fun ω => M ω - N ω) =
      P.expectationCStarMatrix M - P.expectationCStarMatrix N := by
  change P.expectationCStarMatrix (fun ω => M ω + -N ω) =
    P.expectationCStarMatrix M + -P.expectationCStarMatrix N
  rw [expectationCStarMatrix_add]
  rw [expectationCStarMatrix_neg]

/-- Monotonicity of C⋆-matrix expectation for the C⋆ spectral order. -/
theorem expectationCStarMatrix_mono {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M N : Ω → CStarMatrix ι ι ℂ)
    (hMN : ∀ ω, M ω ≤ N ω) :
    P.expectationCStarMatrix M ≤ P.expectationCStarMatrix N := by
  apply sub_nonneg.mp
  rw [← expectationCStarMatrix_sub]
  apply expectationCStarMatrix_nonneg
  intro ω
  exact sub_nonneg.mpr (hMN ω)

/-- Support-aware monotonicity of C⋆-matrix expectation for the C⋆ spectral
order.  The order comparison is required only on atoms with positive
probability. -/
theorem expectationCStarMatrix_mono_of_prob_pos {ι : Type*} [Fintype ι]
    (P : FiniteProbability Ω) (M N : Ω → CStarMatrix ι ι ℂ)
    (hMN : ∀ ω, 0 < P.prob ω → M ω ≤ N ω) :
    P.expectationCStarMatrix M ≤ P.expectationCStarMatrix N := by
  apply sub_nonneg.mp
  rw [← expectationCStarMatrix_sub]
  apply expectationCStarMatrix_nonneg_of_prob_pos
  intro ω hω
  exact sub_nonneg.mpr (hMN ω hω)

/-- Adding a positive scalar identity to a nonnegative C⋆-matrix expectation
gives a strictly positive C⋆-matrix. -/
theorem expectationCStarMatrix_add_pos_smul_one_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → CStarMatrix ι ι ℂ)
    (hM : ∀ ω, 0 ≤ M ω) {eps : ℝ} (heps : 0 < eps) :
    IsStrictlyPositive
      (P.expectationCStarMatrix M +
        (eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) := by
  have hnonneg : 0 ≤ P.expectationCStarMatrix M :=
    expectationCStarMatrix_nonneg P M hM
  have hstrict :
      IsStrictlyPositive ((eps : ℂ) • (1 : CStarMatrix ι ι ℂ)) :=
    cstarMatrix_pos_real_smul_one_isStrictlyPositive heps
  exact IsStrictlyPositive.nonneg_add hnonneg hstrict

end FiniteProbability

end NumStability
