-- Algorithms/Sylvester/Higham16Minimizers.lean
--
-- Attained-minimum upgrades and the floating-point computed-residual model
-- for Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 16 "The Sylvester Equation".
--
-- This file closes three infimum-model gaps left open by `Higham16.lean` and
-- `SylvesterBackward.lean`:
--
-- 1. (16.26) `sep(A,B)`: the infimum of the Frobenius ratios
--    `||AX - XB||_F / ||X||_F` over nonzero `X` is attained by a unit
--    Frobenius-norm minimizer, so the infimum model `sylvesterSepInf` is a
--    minimum (`IsLeast`).
-- 2. (16.15) backward error `eta(Y)`: with positive weights and a nonempty
--    feasible set, the infimum model `sylvesterBackwardErrorInf` is itself a
--    feasible backward error, attained by an optimal perturbation triple.
-- 3. (16.29) the practical bound's computed-residual hypothesis: the residual
--    `R = C - (A*Xhat - Xhat*B)` evaluated with floating-point matrix products
--    and a rounded subtract/add pipeline admits an explicit `dR` with
--    `Rhat = R + dR` and an entrywise `gamma`-weighted budget, which plugs
--    directly into the diagonal practical error bound of `Higham16.lean`.
--
-- All statements are over the repository's legacy function-shaped matrices
-- `RMatFn m n = Fin m -> Fin n -> Real`, matching the Chapter 16 modules.

import NumStability.Algorithms.Sylvester.Higham16
import NumStability.Algorithms.Sylvester.Higham16VecNorm
import NumStability.Algorithms.MatMul

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Topological helpers for the Frobenius objectives
-- ============================================================

/-- A single squared entry is dominated by the squared Frobenius norm. -/
lemma sq_le_frobNormSq {m n : ℕ} (M : RMatFn m n) (i : Fin m) (j : Fin n) :
    M i j ^ 2 ≤ frobNormSq M := by
  unfold frobNormSq
  have hrow : M i j ^ 2 ≤ ∑ j' : Fin n, M i j' ^ 2 :=
    Finset.single_le_sum (f := fun j' : Fin n => M i j' ^ 2)
      (fun j' _ => sq_nonneg _) (Finset.mem_univ j)
  have hall : (∑ j' : Fin n, M i j' ^ 2) ≤
      ∑ i' : Fin m, ∑ j' : Fin n, M i' j' ^ 2 :=
    Finset.single_le_sum (f := fun i' : Fin m => ∑ j' : Fin n, M i' j' ^ 2)
      (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg _)
      (Finset.mem_univ i)
  linarith

/-- Evaluating a fixed entry of a function-shaped matrix is continuous. -/
lemma continuous_matEntry {m n : ℕ} (i : Fin m) (j : Fin n) :
    Continuous fun M : RMatFn m n => M i j := by
  have h1 : Continuous fun M : RMatFn m n => M i := continuous_apply i
  exact (continuous_apply j).comp h1

/-- The squared Frobenius norm is continuous for the product topology on the
    repository's function-shaped matrices. -/
lemma continuous_frobNormSq {m n : ℕ} :
    Continuous fun M : RMatFn m n => frobNormSq M := by
  unfold frobNormSq
  refine continuous_finset_sum _ fun i _ => ?_
  refine continuous_finset_sum _ fun j _ => ?_
  exact (continuous_matEntry i j).pow 2

/-- The Frobenius norm is continuous for the product topology on the
    repository's function-shaped matrices. -/
lemma continuous_frobNorm {m n : ℕ} :
    Continuous fun M : RMatFn m n => frobNorm M := by
  have h : (fun M : RMatFn m n => frobNorm M) =
      fun M => Real.sqrt (frobNormSq M) :=
    funext fun M => frobNorm_eq_sqrt_frobNormSq M
  rw [h]
  exact Real.continuous_sqrt.comp continuous_frobNormSq

/-- Squared-Frobenius sublevel sets of function-shaped matrices are compact:
    they are closed, and every entry is bounded by the level. -/
lemma isCompact_frobNormSq_sublevel {m n : ℕ} (r : ℝ) :
    IsCompact {M : RMatFn m n | frobNormSq M ≤ r} := by
  have hclosed : IsClosed {M : RMatFn m n | frobNormSq M ≤ r} :=
    isClosed_le continuous_frobNormSq continuous_const
  have hsubset : {M : RMatFn m n | frobNormSq M ≤ r} ⊆
      Metric.closedBall (0 : RMatFn m n) (Real.sqrt r) := by
    intro M hM
    rw [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg r)]
    intro i
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg r)]
    intro j
    rw [Real.norm_eq_abs]
    have hsq : M i j ^ 2 ≤ r := le_trans (sq_le_frobNormSq M i j) hM
    calc
      |M i j| = Real.sqrt (M i j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hsq
  exact IsCompact.of_isClosed_subset
    (isCompact_closedBall (0 : RMatFn m n) (Real.sqrt r)) hclosed hsubset

/-- The unit sphere of the squared Frobenius norm is compact. -/
lemma isCompact_frobNormSq_unit_sphere {m n : ℕ} :
    IsCompact {M : RMatFn m n | frobNormSq M = 1} := by
  have hclosed : IsClosed {M : RMatFn m n | frobNormSq M = 1} :=
    isClosed_eq continuous_frobNormSq continuous_const
  have hsubset : {M : RMatFn m n | frobNormSq M = 1} ⊆
      {M : RMatFn m n | frobNormSq M ≤ 1} :=
    fun M hM => le_of_eq hM
  exact IsCompact.of_isClosed_subset
    (isCompact_frobNormSq_sublevel 1) hclosed hsubset

/-- The Frobenius norm of the Sylvester-operator image is continuous in the
    unknown matrix. -/
lemma continuous_frobNorm_sylvesterOp (n : ℕ) (A B : Fin n → Fin n → ℝ) :
    Continuous fun X : Fin n → Fin n → ℝ => frobNorm (sylvesterOp n A B X) := by
  have hOp : Continuous fun X : Fin n → Fin n → ℝ => sylvesterOp n A B X := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [sylvesterOp, matMul]
    refine Continuous.sub ?_ ?_
    · refine continuous_finset_sum _ fun k _ => ?_
      exact continuous_const.mul (continuous_matEntry k j)
    · refine continuous_finset_sum _ fun k _ => ?_
      exact (continuous_matEntry i k).mul continuous_const
  exact continuous_frobNorm.comp hOp

-- ============================================================
-- Scaling identities for the sep(A,B) normalization
-- ============================================================

/-- Entrywise division scales the squared Frobenius norm by the inverse
    square. -/
lemma frobNormSq_div {m n : ℕ} (M : RMatFn m n) (t : ℝ) :
    frobNormSq (fun i j => M i j / t) = frobNormSq M / t ^ 2 := by
  unfold frobNormSq
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [div_pow]

/-- Entrywise division by a positive scalar scales the Frobenius norm. -/
lemma frobNorm_div {m n : ℕ} (M : RMatFn m n) (t : ℝ) (ht : 0 < t) :
    frobNorm (fun i j => M i j / t) = frobNorm M / t := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNormSq_div,
    Real.sqrt_div (frobNormSq_nonneg M), Real.sqrt_sq ht.le,
    ← frobNorm_eq_sqrt_frobNormSq]

/-- The Sylvester operator commutes with entrywise scalar division. -/
lemma sylvesterOp_div (n : ℕ) (A B X : Fin n → Fin n → ℝ) (t : ℝ) :
    sylvesterOp n A B (fun i j => X i j / t) =
      fun i j => sylvesterOp n A B X i j / t := by
  ext i j
  unfold sylvesterOp matMul
  simp only [← mul_div_assoc, div_mul_eq_mul_div, ← Finset.sum_div, ← sub_div]

-- ============================================================
-- (16.26): the sep(A,B) infimum is an attained minimum
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.3,
    eq (16.26): in positive dimension, `sep(A,B)` modeled as the infimum
    `sylvesterSepInf` of the nonzero Frobenius ratios is attained by a matrix
    of unit Frobenius norm.  The witness additionally minimizes
    `||AX - XB||_F` over the whole unit sphere.  This upgrades the pure
    infimum model of `Higham16.lean` to an attained minimum; it is an
    exact-arithmetic statement with no floating-point content. -/
theorem exists_sylvesterSep_minimizer (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (hn : 0 < n) :
    ∃ X : Fin n → Fin n → ℝ,
      frobNormSq X = 1 ∧
      frobNorm X = 1 ∧
      sylvesterSepInf n A B = frobNorm (sylvesterOp n A B X) ∧
      ∀ Y : Fin n → Fin n → ℝ, frobNormSq Y = 1 →
        frobNorm (sylvesterOp n A B X) ≤ frobNorm (sylvesterOp n A B Y) := by
  classical
  -- the unit sphere is nonempty in positive dimension
  have hne : ({X : Fin n → Fin n → ℝ | frobNormSq X = 1}).Nonempty := by
    refine ⟨fun r c =>
      if (⟨0, hn⟩ : Fin n) = r ∧ (⟨0, hn⟩ : Fin n) = c then (1 : ℝ) else 0, ?_⟩
    have hrect :=
      frobNormSqRect_single_left (⟨0, hn⟩ : Fin n) (⟨0, hn⟩ : Fin n) (1 : ℝ)
    rw [frobNormSqRect_eq_frobNormSq] at hrect
    simpa using hrect
  obtain ⟨X0, hX0mem, hmin⟩ :=
    isCompact_frobNormSq_unit_sphere.exists_isMinOn hne
      (continuous_frobNorm_sylvesterOp n A B).continuousOn
  have hX0sq : frobNormSq X0 = 1 := hX0mem
  have hX0norm : frobNorm X0 = 1 := by
    rw [frobNorm_eq_sqrt_frobNormSq, hX0sq, Real.sqrt_one]
  have hX0ne : ¬ frobNormSq X0 = 0 := by
    rw [hX0sq]
    norm_num
  have hminimizer : ∀ Y : Fin n → Fin n → ℝ, frobNormSq Y = 1 →
      frobNorm (sylvesterOp n A B X0) ≤ frobNorm (sylvesterOp n A B Y) :=
    fun Y hY => hmin hY
  refine ⟨X0, hX0sq, hX0norm, ?_, hminimizer⟩
  apply le_antisymm
  · -- the infimum is below the value of the minimizer
    have h := sylvesterSepInf_le_ratio n A B X0 hX0ne
    rwa [hX0norm, div_one] at h
  · -- the value of the minimizer is below every feasible ratio
    unfold sylvesterSepInf
    apply le_csInf (sylvesterSepRatios_nonempty_of_pos_dim n A B hn)
    intro rho hrho
    obtain ⟨X, hXne, rfl⟩ := hrho
    have hXsq_pos : 0 < frobNormSq X :=
      lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hXne)
    have hXnorm_pos : 0 < frobNorm X := by
      have hs : 0 < frobNorm X ^ 2 := by
        rw [frobNorm_sq]
        exact hXsq_pos
      have hne_norm : ¬ frobNorm X = 0 := sq_pos_iff.mp hs
      exact lt_of_le_of_ne (frobNorm_nonneg X) (Ne.symm hne_norm)
    -- normalize X to the unit sphere
    have hX'sphere : frobNormSq (fun i j => X i j / frobNorm X) = 1 := by
      rw [frobNormSq_div, ← frobNorm_sq]
      exact div_self (pow_ne_zero 2 (ne_of_gt hXnorm_pos))
    have hle : frobNorm (sylvesterOp n A B X0) ≤
        frobNorm (sylvesterOp n A B (fun i j => X i j / frobNorm X)) :=
      hmin hX'sphere
    have hgX' : frobNorm (sylvesterOp n A B (fun i j => X i j / frobNorm X)) =
        frobNorm (sylvesterOp n A B X) / frobNorm X := by
      rw [sylvesterOp_div, frobNorm_div _ _ hXnorm_pos]
    rw [hgX'] at hle
    exact hle

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.3,
    eq (16.26): in positive dimension the infimum model of `sep(A,B)` is a
    member of its own feasible ratio set, i.e. the infimum is attained. -/
theorem sylvesterSepInf_mem_sylvesterSepRatios (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (hn : 0 < n) :
    sylvesterSepInf n A B ∈ sylvesterSepRatios n A B := by
  obtain ⟨X, hXsq, hXnorm, hval, _⟩ := exists_sylvesterSep_minimizer n A B hn
  refine ⟨X, by rw [hXsq]; norm_num, ?_⟩
  rw [hval, hXnorm, div_one]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.3,
    eq (16.26): in positive dimension `sylvesterSepInf` is the least element
    of the feasible Frobenius ratio set, so the source's `min` in (16.26) is
    faithfully realized by the infimum model. -/
theorem isLeast_sylvesterSepRatios (n : ℕ) (A B : Fin n → Fin n → ℝ)
    (hn : 0 < n) :
    IsLeast (sylvesterSepRatios n A B) (sylvesterSepInf n A B) :=
  ⟨sylvesterSepInf_mem_sylvesterSepRatios n A B hn,
    fun _rho hrho => csInf_le (sylvesterSepRatios_bddBelow n A B) hrho⟩

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.3,
    eq. (16.26): source-facing nonzero-ratio form of the `sep(A,B)`
    minimum. In positive dimension there is a nonzero matrix whose
    Frobenius-ratio value is exactly `sylvesterSepInf`, and that value is no
    larger than any other nonzero Frobenius ratio. -/
theorem exists_sylvesterSep_ratio_minimizer (n : ℕ)
    (A B : Fin n → Fin n → ℝ) (hn : 0 < n) :
    ∃ X : Fin n → Fin n → ℝ,
      Not (frobNormSq X = 0) ∧
      sylvesterSepInf n A B =
        frobNorm (sylvesterOp n A B X) / frobNorm X ∧
      ∀ Y : Fin n → Fin n → ℝ, Not (frobNormSq Y = 0) →
        frobNorm (sylvesterOp n A B X) / frobNorm X ≤
          frobNorm (sylvesterOp n A B Y) / frobNorm Y := by
  have hleast := isLeast_sylvesterSepRatios n A B hn
  obtain ⟨X, hXne, hXval⟩ := hleast.1
  refine ⟨X, hXne, hXval, ?_⟩
  intro Y hYne
  have hYmem :
      frobNorm (sylvesterOp n A B Y) / frobNorm Y ∈
        sylvesterSepRatios n A B := by
    exact ⟨Y, hYne, rfl⟩
  simpa [hXval] using hleast.2 hYmem

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for existence of a unit-Frobenius minimizer
    attaining the exact `sep(A,B)` infimum in positive dimension. -/
alias H16_eq16_26_exists_sylvesterSep_minimizer :=
  exists_sylvesterSep_minimizer

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias saying the exact `sep(A,B)` infimum belongs to its
    feasible ratio set in positive dimension. -/
alias H16_eq16_26_sylvesterSepInf_mem_sylvesterSepRatios :=
  sylvesterSepInf_mem_sylvesterSepRatios

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for the least-element realization of the exact
    `sep(A,B)` feasible ratio set in positive dimension. -/
alias H16_eq16_26_isLeast_sylvesterSepRatios :=
  isLeast_sylvesterSepRatios

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for the source-facing nonzero-ratio minimizer form of
    the attained exact `sep(A,B)` minimum. -/
alias H16_eq16_26_exists_sylvesterSep_ratio_minimizer :=
  exists_sylvesterSep_ratio_minimizer

-- ============================================================
-- (16.15): the backward-error infimum is an attained minimum
-- ============================================================

private lemma sq_le_sq_of_nonneg_of_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 ≤ y ^ 2 := by nlinarith

/-- The affine feasibility set of backward-error perturbation triples
    `(DA, DB, DC)` for eq (16.15): the perturbed Sylvester equation holds at
    the fixed approximate solution `Y`. -/
private def sylvesterBackwardFeasibleSet (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) :
    Set ((Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  {p | ∀ i j, sylvesterOp n (fun i' j' => A i' j' + p.1 i' j')
      (fun i' j' => B i' j' + p.2.1 i' j') Y i j = C i j + p.2.2 i j}

private lemma continuous_tripleFst {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → ℝ) => p.1 :=
  continuous_fst

private lemma continuous_tripleSndFst {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → ℝ) => p.2.1 :=
  continuous_fst.comp continuous_snd

private lemma continuous_tripleSndSnd {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → ℝ) => p.2.2 :=
  continuous_snd.comp continuous_snd

private lemma continuous_tripleFst_entry {n : ℕ} (i k : Fin n) :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → ℝ) => p.1 i k :=
  (continuous_matEntry i k).comp continuous_tripleFst

private lemma continuous_tripleSndFst_entry {n : ℕ} (k j : Fin n) :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → ℝ) => p.2.1 k j :=
  (continuous_matEntry k j).comp continuous_tripleSndFst

private lemma continuous_tripleSndSnd_entry {n : ℕ} (i j : Fin n) :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) ×
        (Fin n → Fin n → ℝ) => p.2.2 i j :=
  (continuous_matEntry i j).comp continuous_tripleSndSnd

private lemma isClosed_sylvesterBackwardFeasibleSet (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) :
    IsClosed (sylvesterBackwardFeasibleSet n A B C Y) := by
  have hset : sylvesterBackwardFeasibleSet n A B C Y =
      ⋂ (i : Fin n), ⋂ (j : Fin n),
        {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
          (∑ k : Fin n, (A i k + p.1 i k) * Y k j) -
            (∑ k : Fin n, Y i k * (B k j + p.2.1 k j)) = C i j + p.2.2 i j} := by
    ext p
    constructor
    · intro hp
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro i j
      have h := hp i j
      simp only [sylvesterOp, matMul] at h
      exact h
    · intro hp i j
      simp only [Set.mem_iInter, Set.mem_setOf_eq] at hp
      simp only [sylvesterOp, matMul]
      exact hp i j
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · refine Continuous.sub ?_ ?_
    · refine continuous_finset_sum _ fun k _ => ?_
      exact (continuous_const.add (continuous_tripleFst_entry i k)).mul
        continuous_const
    · refine continuous_finset_sum _ fun k _ => ?_
      exact continuous_const.mul
        (continuous_const.add (continuous_tripleSndFst_entry k j))
  · exact continuous_const.add (continuous_tripleSndSnd_entry i j)

/-- The scaled max-Frobenius objective whose minimum over the feasibility set
    is the backward error `eta(Y)` of eq (16.15). -/
private noncomputable def sylvesterBackwardObjective {n : ℕ}
    (alpha beta gamma : ℝ)
    (p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    ℝ :=
  max (frobNorm p.1 / alpha) (max (frobNorm p.2.1 / beta) (frobNorm p.2.2 / gamma))

private lemma continuous_sylvesterBackwardObjective (n : ℕ)
    (alpha beta gamma : ℝ) :
    Continuous (sylvesterBackwardObjective (n := n) alpha beta gamma) := by
  unfold sylvesterBackwardObjective
  refine Continuous.max ?_ (Continuous.max ?_ ?_)
  · exact (continuous_frobNorm.comp continuous_tripleFst).div_const alpha
  · exact (continuous_frobNorm.comp continuous_tripleSndFst).div_const beta
  · exact (continuous_frobNorm.comp continuous_tripleSndSnd).div_const gamma

private lemma sylvesterBackwardObjective_nonneg {n : ℕ}
    {alpha beta gamma : ℝ} (halpha : 0 < alpha)
    (p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    0 ≤ sylvesterBackwardObjective alpha beta gamma p :=
  le_trans (div_nonneg (frobNorm_nonneg p.1) halpha.le)
    (le_max_left _ _)

/-- A feasible triple certifies its own objective value as a backward error. -/
private lemma isBackwardError_sylvesterBackwardObjective (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) {alpha beta gamma : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ))
    (hp : p ∈ sylvesterBackwardFeasibleSet n A B C Y) :
    IsBackwardError n A B C Y alpha beta gamma
      (sylvesterBackwardObjective alpha beta gamma p) := by
  refine ⟨p.1, p.2.1, p.2.2, hp, ?_, ?_, ?_⟩
  · have h1 : frobNorm p.1 / alpha ≤
        sylvesterBackwardObjective alpha beta gamma p := le_max_left _ _
    have h1' : frobNorm p.1 ≤
        sylvesterBackwardObjective alpha beta gamma p * alpha :=
      (div_le_iff₀ halpha).mp h1
    rw [← frobNorm_sq]
    exact sq_le_sq_of_nonneg_of_le (frobNorm_nonneg _) h1'
  · have h2 : frobNorm p.2.1 / beta ≤
        sylvesterBackwardObjective alpha beta gamma p :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have h2' : frobNorm p.2.1 ≤
        sylvesterBackwardObjective alpha beta gamma p * beta :=
      (div_le_iff₀ hbeta).mp h2
    rw [← frobNorm_sq]
    exact sq_le_sq_of_nonneg_of_le (frobNorm_nonneg _) h2'
  · have h3 : frobNorm p.2.2 / gamma ≤
        sylvesterBackwardObjective alpha beta gamma p :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have h3' : frobNorm p.2.2 ≤
        sylvesterBackwardObjective alpha beta gamma p * gamma :=
      (div_le_iff₀ hgamma).mp h3
    rw [← frobNorm_sq]
    exact sq_le_sq_of_nonneg_of_le (frobNorm_nonneg _) h3'

/-- Any backward-error certificate dominates the objective of its witness. -/
private lemma sylvesterBackwardObjective_le {n : ℕ}
    {alpha beta gamma eta : ℝ}
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (heta : 0 ≤ eta) (DA DB DC : Fin n → Fin n → ℝ)
    (hA : frobNormSq DA ≤ (eta * alpha) ^ 2)
    (hB : frobNormSq DB ≤ (eta * beta) ^ 2)
    (hC : frobNormSq DC ≤ (eta * gamma) ^ 2) :
    sylvesterBackwardObjective alpha beta gamma (DA, DB, DC) ≤ eta := by
  have hfA : frobNorm DA ≤ eta * alpha :=
    frobNorm_le_of_frobNormSq_le_sq DA (mul_nonneg heta halpha.le) hA
  have hfB : frobNorm DB ≤ eta * beta :=
    frobNorm_le_of_frobNormSq_le_sq DB (mul_nonneg heta hbeta.le) hB
  have hfC : frobNorm DC ≤ eta * gamma :=
    frobNorm_le_of_frobNormSq_le_sq DC (mul_nonneg heta hgamma.le) hC
  exact max_le ((div_le_iff₀ halpha).mpr hfA)
    (max_le ((div_le_iff₀ hbeta).mpr hfB) ((div_le_iff₀ hgamma).mpr hfC))

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2,
    eq (16.15): with positive weights `alpha, beta, gamma` and a nonempty
    feasible set, the infimum model `sylvesterBackwardErrorInf` of the
    normwise backward error `eta(Y)` is itself a feasible backward error:
    there is a perturbation triple `(DA, DB, DC)` satisfying the perturbed
    equation with Frobenius bounds at the infimum level, so the infimum is an
    attained minimum.  The nonemptiness hypothesis can be discharged by
    `sylvesterBackwardErrorValues_nonempty_of_svdOptimalPerturbations`. -/
theorem exists_sylvesterBackwardError_minimizer (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hne : (sylvesterBackwardErrorValues n A B C Y alpha beta gamma).Nonempty) :
    IsBackwardError n A B C Y alpha beta gamma
      (sylvesterBackwardErrorInf n A B C Y alpha beta gamma) := by
  classical
  obtain ⟨eta0, heta0⟩ := hne
  have heta0_nonneg : 0 ≤ eta0 := heta0.1
  obtain ⟨DA0, DB0, DC0, hEq0, hA0, hB0, hC0⟩ := heta0.2
  -- compact constraint set: sublevel product intersected with the closed
  -- affine feasibility set
  have hK : IsCompact
      ((({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * alpha) ^ 2} ×ˢ
          ({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * beta) ^ 2} ×ˢ
            {M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * gamma) ^ 2}))) ∩
        sylvesterBackwardFeasibleSet n A B C Y) :=
    IsCompact.inter_right
      ((isCompact_frobNormSq_sublevel _).prod
        ((isCompact_frobNormSq_sublevel _).prod
          (isCompact_frobNormSq_sublevel _)))
      (isClosed_sylvesterBackwardFeasibleSet n A B C Y)
  have hp0 : ((DA0, DB0, DC0) :
      (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) ∈
      ((({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * alpha) ^ 2} ×ˢ
          ({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * beta) ^ 2} ×ˢ
            {M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * gamma) ^ 2}))) ∩
        sylvesterBackwardFeasibleSet n A B C Y) :=
    ⟨⟨hA0, hB0, hC0⟩, hEq0⟩
  obtain ⟨pmin, hpmin, hmin⟩ :=
    hK.exists_isMinOn ⟨(DA0, DB0, DC0), hp0⟩
      (continuous_sylvesterBackwardObjective n alpha beta gamma).continuousOn
  have hfeas : IsBackwardError n A B C Y alpha beta gamma
      (sylvesterBackwardObjective alpha beta gamma pmin) :=
    isBackwardError_sylvesterBackwardObjective n A B C Y
      halpha hbeta hgamma pmin hpmin.2
  have hstar_nonneg : 0 ≤ sylvesterBackwardObjective alpha beta gamma pmin :=
    sylvesterBackwardObjective_nonneg halpha pmin
  have hinf_eq : sylvesterBackwardErrorInf n A B C Y alpha beta gamma =
      sylvesterBackwardObjective alpha beta gamma pmin := by
    apply le_antisymm
    · exact csInf_le
        (sylvesterBackwardErrorValues_bddBelow n A B C Y alpha beta gamma)
        ⟨hstar_nonneg, hfeas⟩
    · unfold sylvesterBackwardErrorInf
      apply le_csInf ⟨eta0, heta0⟩
      rintro eta ⟨heta_nonneg, DA, DB, DC, hEq, hA, hB, hC⟩
      by_cases hcase : eta ≤ eta0
      · -- the witness lies inside the compact constraint set
        have hAle : (eta * alpha) ^ 2 ≤ (eta0 * alpha) ^ 2 :=
          sq_le_sq_of_nonneg_of_le (mul_nonneg heta_nonneg halpha.le)
            (mul_le_mul_of_nonneg_right hcase halpha.le)
        have hBle : (eta * beta) ^ 2 ≤ (eta0 * beta) ^ 2 :=
          sq_le_sq_of_nonneg_of_le (mul_nonneg heta_nonneg hbeta.le)
            (mul_le_mul_of_nonneg_right hcase hbeta.le)
        have hCle : (eta * gamma) ^ 2 ≤ (eta0 * gamma) ^ 2 :=
          sq_le_sq_of_nonneg_of_le (mul_nonneg heta_nonneg hgamma.le)
            (mul_le_mul_of_nonneg_right hcase hgamma.le)
        have hmem : ((DA, DB, DC) :
            (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) ∈
            ((({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * alpha) ^ 2} ×ˢ
                ({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * beta) ^ 2} ×ˢ
                  {M : Fin n → Fin n → ℝ |
                    frobNormSq M ≤ (eta0 * gamma) ^ 2}))) ∩
              sylvesterBackwardFeasibleSet n A B C Y) :=
          ⟨⟨le_trans hA hAle, le_trans hB hBle, le_trans hC hCle⟩, hEq⟩
        have h1 : sylvesterBackwardObjective alpha beta gamma pmin ≤
            sylvesterBackwardObjective alpha beta gamma (DA, DB, DC) :=
          hmin hmem
        have h2 : sylvesterBackwardObjective alpha beta gamma (DA, DB, DC) ≤
            eta :=
          sylvesterBackwardObjective_le halpha hbeta hgamma heta_nonneg
            DA DB DC hA hB hC
        linarith
      · push_neg at hcase
        have h1 : sylvesterBackwardObjective alpha beta gamma pmin ≤
            sylvesterBackwardObjective alpha beta gamma (DA0, DB0, DC0) :=
          hmin hp0
        have h2 : sylvesterBackwardObjective alpha beta gamma
            (DA0, DB0, DC0) ≤ eta0 :=
          sylvesterBackwardObjective_le halpha hbeta hgamma heta0_nonneg
            DA0 DB0 DC0 hA0 hB0 hC0
        linarith
  rw [hinf_eq]
  exact hfeas

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2,
    eq (16.15): under positive weights and a nonempty feasible set, the
    infimum model of the backward error is a member of its own value set. -/
theorem sylvesterBackwardErrorInf_mem_sylvesterBackwardErrorValues (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hne : (sylvesterBackwardErrorValues n A B C Y alpha beta gamma).Nonempty) :
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma ∈
      sylvesterBackwardErrorValues n A B C Y alpha beta gamma :=
  ⟨sylvesterBackwardErrorInf_nonneg n A B C Y alpha beta gamma,
    exists_sylvesterBackwardError_minimizer n A B C Y alpha beta gamma
      halpha hbeta hgamma hne⟩

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2,
    eq (16.15): under positive weights and a nonempty feasible set,
    `sylvesterBackwardErrorInf` is the least feasible backward-error value,
    so the source's `min` in (16.15) is faithfully realized by the infimum
    model. -/
theorem isLeast_sylvesterBackwardErrorValues (n : ℕ)
    (A B C Y : Fin n → Fin n → ℝ) (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hne : (sylvesterBackwardErrorValues n A B C Y alpha beta gamma).Nonempty) :
    IsLeast (sylvesterBackwardErrorValues n A B C Y alpha beta gamma)
      (sylvesterBackwardErrorInf n A B C Y alpha beta gamma) :=
  ⟨sylvesterBackwardErrorInf_mem_sylvesterBackwardErrorValues n A B C Y
      alpha beta gamma halpha hbeta hgamma hne,
    fun _eta heta => csInf_le
      (sylvesterBackwardErrorValues_bddBelow n A B C Y alpha beta gamma) heta⟩

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2,
    eq (16.15): SVD optimal perturbations supply the nonempty feasible set
    needed by `exists_sylvesterBackwardError_minimizer`. -/
theorem exists_sylvesterBackwardError_minimizer_of_svdOptimalPerturbations (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hSVD : IsSVD n Y U V sigma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    IsBackwardError n A B C Y alpha beta gamma
      (sylvesterBackwardErrorInf n A B C Y alpha beta gamma) := by
  exact exists_sylvesterBackwardError_minimizer n A B C Y alpha beta gamma
    halpha hbeta hgamma
    (sylvesterBackwardErrorValues_nonempty_of_svdOptimalPerturbations n
      A B C Y U V sigma alpha beta gamma hSVD hpos)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2,
    eq (16.15): under SVD optimal perturbation hypotheses, the infimum
    backward error is itself a feasible value. -/
theorem sylvesterBackwardErrorInf_mem_sylvesterBackwardErrorValues_of_svdOptimalPerturbations
    (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hSVD : IsSVD n Y U V sigma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma ∈
      sylvesterBackwardErrorValues n A B C Y alpha beta gamma := by
  exact sylvesterBackwardErrorInf_mem_sylvesterBackwardErrorValues n A B C Y
    alpha beta gamma halpha hbeta hgamma
    (sylvesterBackwardErrorValues_nonempty_of_svdOptimalPerturbations n
      A B C Y U V sigma alpha beta gamma hSVD hpos)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2,
    eq (16.15): under SVD optimal perturbation hypotheses,
    `sylvesterBackwardErrorInf` is the least feasible backward-error value. -/
theorem isLeast_sylvesterBackwardErrorValues_of_svdOptimalPerturbations (n : ℕ)
    (A B C Y U V : Fin n → Fin n → ℝ) (sigma : Fin n → ℝ)
    (alpha beta gamma : ℝ)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hSVD : IsSVD n Y U V sigma)
    (hpos : ∀ i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    IsLeast (sylvesterBackwardErrorValues n A B C Y alpha beta gamma)
      (sylvesterBackwardErrorInf n A B C Y alpha beta gamma) := by
  exact isLeast_sylvesterBackwardErrorValues n A B C Y alpha beta gamma
    halpha hbeta hgamma
    (sylvesterBackwardErrorValues_nonempty_of_svdOptimalPerturbations n
      A B C Y U V sigma alpha beta gamma hSVD hpos)

/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.15):
    source-numbered alias for SVD-discharge backward-error minimizer existence. -/
alias H16_eq16_15_exists_sylvesterBackwardError_minimizer_of_svdOptimalPerturbations :=
  exists_sylvesterBackwardError_minimizer_of_svdOptimalPerturbations

/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.15):
    source-numbered alias for SVD-discharge feasible infimum membership. -/
alias H16_eq16_15_sylvesterBackwardErrorInf_mem_sylvesterBackwardErrorValues_of_svdOptimalPerturbations :=
  sylvesterBackwardErrorInf_mem_sylvesterBackwardErrorValues_of_svdOptimalPerturbations

/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.15):
    source-numbered alias for SVD-discharge least feasible backward error. -/
alias H16_eq16_15_isLeast_sylvesterBackwardErrorValues_of_svdOptimalPerturbations :=
  isLeast_sylvesterBackwardErrorValues_of_svdOptimalPerturbations

/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.15):
    source-facing two-sided Sylvester eta/xi infimum bound from SVD data. -/
theorem sylvesterBackwardErrorInf_two_sided_sqrt_xiSq_of_svdOptimalPerturbations
    (n : Nat)
    (A B C Y U V : Fin n -> Fin n -> Real) (sigma : Fin n -> Real)
    (alpha beta gamma : Real)
    (hSVD : IsSVD n Y U V sigma)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hpos : forall i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma / 3) <=
      sylvesterBackwardErrorInf n A B C Y alpha beta gamma ∧
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma <=
      Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma) := by
  constructor
  · exact
      sqrt_xiSq_div_three_le_sylvesterBackwardErrorInf_of_svd n
        A B C Y U V sigma alpha beta gamma hSVD halpha hbeta hgamma hpos
  · exact
      sylvesterBackwardErrorInf_le_sqrt_xiSq_of_svdOptimalPerturbations n
        A B C Y U V sigma alpha beta gamma hSVD hpos

/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.15):
    source-numbered alias for the Sylvester eta/xi two-sided SVD bound. -/
theorem H16_eq16_15_sylvester_eta_xi_bounds_of_svdOptimalPerturbations
    (n : Nat)
    (A B C Y U V : Fin n -> Fin n -> Real) (sigma : Fin n -> Real)
    (alpha beta gamma : Real)
    (hSVD : IsSVD n Y U V sigma)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hpos : forall i j : Fin n,
      0 < alpha ^ 2 * sigma j ^ 2 + beta ^ 2 * sigma i ^ 2 + gamma ^ 2) :
    Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma / 3) <=
      sylvesterBackwardErrorInf n A B C Y alpha beta gamma ∧
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma <=
      Real.sqrt
        (xiSq n (svdResidual n U V (sylvesterResidual n A B C Y))
          sigma alpha beta gamma) := by
  exact
    sylvesterBackwardErrorInf_two_sided_sqrt_xiSq_of_svdOptimalPerturbations
      n A B C Y U V sigma alpha beta gamma hSVD halpha hbeta hgamma hpos

/-- Higham, 2nd ed., Chapter 16, Section 16.2, equation (16.17):
    source-numbered square-case eta residual amplification bound. -/
theorem H16_eq16_17_sylvester_eta_residual_amplification_of_svd (n : Nat)
    (A B C Y U V : Fin n -> Fin n -> Real) (sigma : Fin n -> Real)
    (alpha beta gamma sigma_min : Real)
    (hSVD : IsSVD n Y U V sigma)
    (hsigma_min : forall i : Fin n, sigma_min <= sigma i)
    (hsigma_min_nn : 0 <= sigma_min)
    (hDenom : 0 < (alpha ^ 2 + beta ^ 2) * sigma_min ^ 2 + gamma ^ 2)
    (hScale : 0 < (alpha + beta) * frobNorm Y + gamma) :
    sylvesterBackwardErrorInf n A B C Y alpha beta gamma <=
      sylvesterAmplificationMuSquare alpha beta gamma (frobNorm Y) sigma_min *
        (frobNorm (sylvesterResidual n A B C Y) /
          ((alpha + beta) * frobNorm Y + gamma)) := by
  exact
    sylvesterBackwardErrorInf_le_mu_relative_residual_of_svd n
      A B C Y U V sigma alpha beta gamma sigma_min hSVD hsigma_min
      hsigma_min_nn hDenom hScale

-- ============================================================
-- (16.21): the structured Lyapunov backward-error infimum is attained
-- ============================================================

/-- The affine feasibility set of structured Lyapunov backward-error
    perturbation pairs `(DA, DC)` for eq. (16.21): the perturbed Lyapunov
    equation holds at the fixed approximate solution `Y`, and `DC` is
    symmetric. -/
private def lyapunovBackwardFeasibleSet (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ) :
    Set ((Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) :=
  {p | IsSymmetricFiniteMatrix p.2 ∧
    ∀ i j, lyapunovOp n (fun i' j' => A i' j' + p.1 i' j') Y i j =
      C i j + p.2 i j}

private lemma continuous_pairFst {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) => p.1 :=
  continuous_fst

private lemma continuous_pairSnd {n : ℕ} :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) => p.2 :=
  continuous_snd

private lemma continuous_pairFst_entry {n : ℕ} (i j : Fin n) :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) => p.1 i j :=
  (continuous_matEntry i j).comp continuous_pairFst

private lemma continuous_pairSnd_entry {n : ℕ} (i j : Fin n) :
    Continuous fun p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) => p.2 i j :=
  (continuous_matEntry i j).comp continuous_pairSnd

private lemma isClosed_lyapunovBackwardFeasibleSet (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ) :
    IsClosed (lyapunovBackwardFeasibleSet n A C Y) := by
  have hsym_closed :
      IsClosed {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
        IsSymmetricFiniteMatrix p.2} := by
    have hsym_set :
        {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
            IsSymmetricFiniteMatrix p.2} =
          ⋂ (i : Fin n), ⋂ (j : Fin n),
            {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
              p.2 i j = p.2 j i} := by
      ext p
      simp [IsSymmetricFiniteMatrix]
    rw [hsym_set]
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    exact isClosed_eq (continuous_pairSnd_entry i j) (continuous_pairSnd_entry j i)
  have heq_closed :
      IsClosed (⋂ (i : Fin n), ⋂ (j : Fin n),
        {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
          lyapunovOp n (fun i' j' => A i' j' + p.1 i' j') Y i j =
            C i j + p.2 i j}) := by
    refine isClosed_iInter fun i => isClosed_iInter fun j => ?_
    refine isClosed_eq ?_ ?_
    · unfold lyapunovOp matMul matTranspose
      refine Continuous.add ?_ ?_
      · refine continuous_finset_sum _ fun k _ => ?_
        exact (continuous_const.add (continuous_pairFst_entry i k)).mul
          continuous_const
      · refine continuous_finset_sum _ fun k _ => ?_
        exact continuous_const.mul
          (continuous_const.add (continuous_pairFst_entry j k))
    · exact continuous_const.add (continuous_pairSnd_entry i j)
  have hset : lyapunovBackwardFeasibleSet n A C Y =
      {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
        IsSymmetricFiniteMatrix p.2} ∩
        ⋂ (i : Fin n), ⋂ (j : Fin n),
          {p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ) |
            lyapunovOp n (fun i' j' => A i' j' + p.1 i' j') Y i j =
              C i j + p.2 i j} := by
    ext p
    simp [lyapunovBackwardFeasibleSet]
  rw [hset]
  exact hsym_closed.inter heq_closed

/-- The scaled max-Frobenius objective whose minimum over the structured
    Lyapunov feasibility set is the Lyapunov backward error `eta(Y)`. -/
private noncomputable def lyapunovBackwardObjective {n : ℕ}
    (alpha gamma : ℝ)
    (p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) : ℝ :=
  max (frobNorm p.1 / alpha) (frobNorm p.2 / gamma)

private lemma continuous_lyapunovBackwardObjective (n : ℕ)
    (alpha gamma : ℝ) :
    Continuous (lyapunovBackwardObjective (n := n) alpha gamma) := by
  unfold lyapunovBackwardObjective
  refine Continuous.max ?_ ?_
  · exact (continuous_frobNorm.comp continuous_pairFst).div_const alpha
  · exact (continuous_frobNorm.comp continuous_pairSnd).div_const gamma

private lemma lyapunovBackwardObjective_nonneg {n : ℕ}
    {alpha gamma : ℝ} (halpha : 0 < alpha)
    (p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    0 ≤ lyapunovBackwardObjective alpha gamma p :=
  le_trans (div_nonneg (frobNorm_nonneg p.1) halpha.le)
    (le_max_left _ _)

/-- A feasible structured Lyapunov perturbation pair certifies its own
    objective value as a Lyapunov backward error. -/
private lemma isLyapunovBackwardError_lyapunovBackwardObjective (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ) {alpha gamma : ℝ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (p : (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ))
    (hp : p ∈ lyapunovBackwardFeasibleSet n A C Y) :
    IsLyapunovBackwardError n A C Y alpha gamma
      (lyapunovBackwardObjective alpha gamma p) := by
  refine ⟨p.1, p.2, hp.1, hp.2, ?_, ?_⟩
  · have h1 : frobNorm p.1 / alpha ≤
        lyapunovBackwardObjective alpha gamma p := le_max_left _ _
    have h1' : frobNorm p.1 ≤
        lyapunovBackwardObjective alpha gamma p * alpha :=
      (div_le_iff₀ halpha).mp h1
    rw [← frobNorm_sq]
    exact sq_le_sq_of_nonneg_of_le (frobNorm_nonneg _) h1'
  · have h2 : frobNorm p.2 / gamma ≤
        lyapunovBackwardObjective alpha gamma p := le_max_right _ _
    have h2' : frobNorm p.2 ≤
        lyapunovBackwardObjective alpha gamma p * gamma :=
      (div_le_iff₀ hgamma).mp h2
    rw [← frobNorm_sq]
    exact sq_le_sq_of_nonneg_of_le (frobNorm_nonneg _) h2'

/-- Any structured Lyapunov backward-error certificate dominates the objective
    of its witness. -/
private lemma lyapunovBackwardObjective_le {n : ℕ}
    {alpha gamma eta : ℝ}
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (heta : 0 ≤ eta) (DA DC : Fin n → Fin n → ℝ)
    (hA : frobNormSq DA ≤ (eta * alpha) ^ 2)
    (hC : frobNormSq DC ≤ (eta * gamma) ^ 2) :
    lyapunovBackwardObjective alpha gamma (DA, DC) ≤ eta := by
  have hfA : frobNorm DA ≤ eta * alpha :=
    frobNorm_le_of_frobNormSq_le_sq DA (mul_nonneg heta halpha.le) hA
  have hfC : frobNorm DC ≤ eta * gamma :=
    frobNorm_le_of_frobNormSq_le_sq DC (mul_nonneg heta hgamma.le) hC
  exact max_le ((div_le_iff₀ halpha).mpr hfA) ((div_le_iff₀ hgamma).mpr hfC)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2.1,
    eq (16.21): with positive weights `alpha, gamma` and a nonempty structured
    Lyapunov feasible set, the infimum model `lyapunovBackwardErrorInf` is
    itself a feasible structured Lyapunov backward error.  Equivalently, the
    structured Lyapunov eta model is an attained minimum. -/
theorem exists_lyapunovBackwardError_minimizer (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ) (alpha gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hne : (lyapunovBackwardErrorValues n A C Y alpha gamma).Nonempty) :
    IsLyapunovBackwardError n A C Y alpha gamma
      (lyapunovBackwardErrorInf n A C Y alpha gamma) := by
  classical
  obtain ⟨eta0, heta0⟩ := hne
  have heta0_nonneg : 0 ≤ eta0 := heta0.1
  obtain ⟨DA0, DC0, hDC0_sym, hEq0, hA0, hC0⟩ := heta0.2
  have hK : IsCompact
      ((({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * alpha) ^ 2} ×ˢ
          {M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * gamma) ^ 2})) ∩
        lyapunovBackwardFeasibleSet n A C Y) := by
    exact IsCompact.inter_right
      ((isCompact_frobNormSq_sublevel _).prod
        (isCompact_frobNormSq_sublevel _))
      (isClosed_lyapunovBackwardFeasibleSet n A C Y)
  have hp0 : ((DA0, DC0) :
      (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) ∈
      ((({M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * alpha) ^ 2} ×ˢ
          {M : Fin n → Fin n → ℝ | frobNormSq M ≤ (eta0 * gamma) ^ 2})) ∩
        lyapunovBackwardFeasibleSet n A C Y) :=
    ⟨⟨hA0, hC0⟩, hDC0_sym, hEq0⟩
  obtain ⟨pmin, hpmin, hmin⟩ :=
    hK.exists_isMinOn ⟨(DA0, DC0), hp0⟩
      (continuous_lyapunovBackwardObjective n alpha gamma).continuousOn
  have hfeas : IsLyapunovBackwardError n A C Y alpha gamma
      (lyapunovBackwardObjective alpha gamma pmin) :=
    isLyapunovBackwardError_lyapunovBackwardObjective n A C Y
      halpha hgamma pmin hpmin.2
  have hstar_nonneg : 0 ≤ lyapunovBackwardObjective alpha gamma pmin :=
    lyapunovBackwardObjective_nonneg halpha pmin
  have hinf_eq : lyapunovBackwardErrorInf n A C Y alpha gamma =
      lyapunovBackwardObjective alpha gamma pmin := by
    apply le_antisymm
    · exact csInf_le
        (lyapunovBackwardErrorValues_bddBelow n A C Y alpha gamma)
        ⟨hstar_nonneg, hfeas⟩
    · unfold lyapunovBackwardErrorInf
      apply le_csInf ⟨eta0, heta0⟩
      rintro eta ⟨heta_nonneg, DA, DC, hDC_sym, hEq, hA, hC⟩
      by_cases hcase : eta ≤ eta0
      · have hAle : (eta * alpha) ^ 2 ≤ (eta0 * alpha) ^ 2 :=
          sq_le_sq_of_nonneg_of_le (mul_nonneg heta_nonneg halpha.le)
            (mul_le_mul_of_nonneg_right hcase halpha.le)
        have hCle : (eta * gamma) ^ 2 ≤ (eta0 * gamma) ^ 2 :=
          sq_le_sq_of_nonneg_of_le (mul_nonneg heta_nonneg hgamma.le)
            (mul_le_mul_of_nonneg_right hcase hgamma.le)
        have hmem : ((DA, DC) :
            (Fin n → Fin n → ℝ) × (Fin n → Fin n → ℝ)) ∈
            ((({M : Fin n → Fin n → ℝ |
                frobNormSq M ≤ (eta0 * alpha) ^ 2} ×ˢ
              {M : Fin n → Fin n → ℝ |
                frobNormSq M ≤ (eta0 * gamma) ^ 2})) ∩
              lyapunovBackwardFeasibleSet n A C Y) :=
          ⟨⟨le_trans hA hAle, le_trans hC hCle⟩, hDC_sym, hEq⟩
        have h1 : lyapunovBackwardObjective alpha gamma pmin ≤
            lyapunovBackwardObjective alpha gamma (DA, DC) :=
          hmin hmem
        have h2 : lyapunovBackwardObjective alpha gamma (DA, DC) ≤ eta :=
          lyapunovBackwardObjective_le halpha hgamma heta_nonneg DA DC hA hC
        linarith
      · push_neg at hcase
        have h1 : lyapunovBackwardObjective alpha gamma pmin ≤
            lyapunovBackwardObjective alpha gamma (DA0, DC0) :=
          hmin hp0
        have h2 : lyapunovBackwardObjective alpha gamma (DA0, DC0) ≤ eta0 :=
          lyapunovBackwardObjective_le halpha hgamma heta0_nonneg
            DA0 DC0 hA0 hC0
        linarith
  rw [hinf_eq]
  exact hfeas

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2.1,
    eq (16.21): under positive weights and a nonempty structured feasible set,
    the Lyapunov eta infimum is a member of its own feasible value set. -/
theorem lyapunovBackwardErrorInf_mem_lyapunovBackwardErrorValues (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ) (alpha gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hne : (lyapunovBackwardErrorValues n A C Y alpha gamma).Nonempty) :
    lyapunovBackwardErrorInf n A C Y alpha gamma ∈
      lyapunovBackwardErrorValues n A C Y alpha gamma :=
  ⟨lyapunovBackwardErrorInf_nonneg n A C Y alpha gamma,
    exists_lyapunovBackwardError_minimizer n A C Y alpha gamma
      halpha hgamma hne⟩

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2.1,
    eq (16.21): under positive weights and a nonempty structured feasible set,
    `lyapunovBackwardErrorInf` is the least feasible structured Lyapunov
    backward-error value. -/
theorem isLeast_lyapunovBackwardErrorValues (n : ℕ)
    (A C Y : Fin n → Fin n → ℝ) (alpha gamma : ℝ)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hne : (lyapunovBackwardErrorValues n A C Y alpha gamma).Nonempty) :
    IsLeast (lyapunovBackwardErrorValues n A C Y alpha gamma)
      (lyapunovBackwardErrorInf n A C Y alpha gamma) :=
  ⟨lyapunovBackwardErrorInf_mem_lyapunovBackwardErrorValues n A C Y
      alpha gamma halpha hgamma hne,
    fun _eta heta => csInf_le
      (lyapunovBackwardErrorValues_bddBelow n A C Y alpha gamma) heta⟩

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2.1,
    eq (16.21): for symmetric Lyapunov data with an orthogonal spectral
    decomposition, the optimizer construction supplies nonemptiness, so the
    structured eta infimum is attained. -/
theorem exists_lyapunovBackwardError_minimizer_of_symmetric_spectral (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hpos : ∀ i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    IsLyapunovBackwardError n A C Y alpha gamma
      (lyapunovBackwardErrorInf n A C Y alpha gamma) :=
  exists_lyapunovBackwardError_minimizer n A C Y alpha gamma halpha hgamma
    (lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral n
      A C Y U lam alpha gamma hY hU hC hYsym hpos)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.2.1,
    eq (16.21): for symmetric Lyapunov data with an orthogonal spectral
    decomposition, the structured eta infimum is the least feasible value. -/
theorem isLeast_lyapunovBackwardErrorValues_of_symmetric_spectral (n : ℕ)
    (A C Y U : Fin n → Fin n → ℝ) (lam : Fin n → ℝ)
    (alpha gamma : ℝ)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hpos : ∀ i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    IsLeast (lyapunovBackwardErrorValues n A C Y alpha gamma)
      (lyapunovBackwardErrorInf n A C Y alpha gamma) :=
  isLeast_lyapunovBackwardErrorValues n A C Y alpha gamma halpha hgamma
    (lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral n
      A C Y U lam alpha gamma hY hU hC hYsym hpos)

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered alias for attained structured Lyapunov eta infimum. -/
alias H16_eq16_21_exists_lyapunovBackwardError_minimizer :=
  exists_lyapunovBackwardError_minimizer

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered alias for eta-infimum membership in the feasible value set. -/
alias H16_eq16_21_lyapunovBackwardErrorInf_mem_lyapunovBackwardErrorValues :=
  lyapunovBackwardErrorInf_mem_lyapunovBackwardErrorValues

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered alias for least-value attainment of the structured
    Lyapunov eta feasible set. -/
alias H16_eq16_21_isLeast_lyapunovBackwardErrorValues :=
  isLeast_lyapunovBackwardErrorValues

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered alias for attained structured Lyapunov eta infimum under
    symmetric spectral data. -/
alias H16_eq16_21_exists_lyapunovBackwardError_minimizer_of_symmetric_spectral :=
  exists_lyapunovBackwardError_minimizer_of_symmetric_spectral

/-- Higham, 2nd ed., Chapter 16.2.1, equation (16.21):
    source-numbered alias for least-value attainment under symmetric spectral
    data. -/
alias H16_eq16_21_isLeast_lyapunovBackwardErrorValues_of_symmetric_spectral :=
  isLeast_lyapunovBackwardErrorValues_of_symmetric_spectral

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Chapter 16, Section 16.2.1, equation (16.21): exact-arithmetic
    source-facing two-sided Lyapunov eta/xi infimum bound. This wrapper
    bundles the existing one-sided symmetric-spectral infimum bounds. -/
theorem lyapunovBackwardErrorInf_two_sided_sqrt_lyapunovXiSq_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma / 2) <=
      lyapunovBackwardErrorInf n A C Y alpha gamma ∧
    lyapunovBackwardErrorInf n A C Y alpha gamma <=
      Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma) := by
  constructor
  · exact
      sqrt_lyapunovXiSq_div_two_le_lyapunovBackwardErrorInf_of_symmetric_spectral
        n A C Y U lam alpha gamma hY hU hC hYsym halpha hgamma hpos
  · exact
      lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral
        n A C Y U lam alpha gamma hY hU hC hYsym hpos

/-- Higham, 2nd ed., Chapter 16, Section 16.2.1, equation (16.21):
    source-numbered alias for the Lyapunov eta/xi symmetric-spectral bound. -/
theorem H16_eq16_21_lyapunov_eta_xi_bounds_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2) :
    Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma / 2) <=
      lyapunovBackwardErrorInf n A C Y alpha gamma ∧
    lyapunovBackwardErrorInf n A C Y alpha gamma <=
      Real.sqrt
        (lyapunovXiSq n
          (lyapunovSpectralTransform n U (lyapunovResidual n A C Y))
          lam alpha gamma) := by
  exact
    lyapunovBackwardErrorInf_two_sided_sqrt_lyapunovXiSq_of_symmetric_spectral
      n A C Y U lam alpha gamma hY hU hC hYsym halpha hgamma hpos

/-- Higham, 2nd ed., Chapter 16, Section 16.2.1, equation (16.21):
    Lyapunov eta infimum bounded by the mu-scaled relative residual. -/
theorem lyapunovBackwardErrorInf_le_mu_relative_residual_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma lamStar : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2)
    (hLam : forall i : Fin n, lamStar ^ 2 <= lam i ^ 2)
    (hDenom : 0 < 4 * alpha ^ 2 * lamStar ^ 2 + gamma ^ 2)
    (hScale : 0 < 2 * alpha * frobNorm Y + gamma) :
    lyapunovBackwardErrorInf n A C Y alpha gamma <=
      lyapunovAmplificationMu alpha gamma (frobNorm Y) lamStar *
        (frobNorm (lyapunovResidual n A C Y) /
          (2 * alpha * frobNorm Y + gamma)) := by
  exact
    le_trans
      (lyapunovBackwardErrorInf_le_sqrt_lyapunovXiSq_of_symmetric_spectral
        n A C Y U lam alpha gamma hY hU hC hYsym hpos)
      (sqrt_lyapunovXiSq_le_mu_relative_residual n Y
        (lyapunovResidual n A C Y) U lam alpha gamma lamStar
        hU hLam hDenom hScale)

/-- Higham, 2nd ed., Chapter 16, Section 16.2.1, equation (16.21):
    source-numbered Lyapunov eta residual amplification alias. -/
theorem H16_eq16_21_lyapunov_eta_residual_amplification_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma lamStar : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2)
    (hLam : forall i : Fin n, lamStar ^ 2 <= lam i ^ 2)
    (hDenom : 0 < 4 * alpha ^ 2 * lamStar ^ 2 + gamma ^ 2)
    (hScale : 0 < 2 * alpha * frobNorm Y + gamma) :
    lyapunovBackwardErrorInf n A C Y alpha gamma <=
      lyapunovAmplificationMu alpha gamma (frobNorm Y) lamStar *
        (frobNorm (lyapunovResidual n A C Y) /
          (2 * alpha * frobNorm Y + gamma)) := by
  exact
    lyapunovBackwardErrorInf_le_mu_relative_residual_of_symmetric_spectral n
      A C Y U lam alpha gamma lamStar hY hU hC hYsym hpos hLam hDenom hScale

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Chapter 16, Section 16.2.1, equation (16.21): exact-arithmetic
    source-facing Lyapunov residual-ratio lower bound. This wrapper uses the
    symmetric-spectral optimizer to discharge the feasible-set nonemptiness
    hypothesis; it is not a rounded solver or estimator. -/
theorem lyapunov_relative_residual_le_backwardErrorInf_of_symmetric_spectral
    (n : Nat)
    (A C Y U : Fin n -> Fin n -> Real) (lam : Fin n -> Real)
    (alpha gamma : Real)
    (hY : Y = matMul n U (matMul n (diagMatrix lam) (matTranspose U)))
    (hU : IsOrthogonal n U)
    (hC : IsSymmetricFiniteMatrix C) (hYsym : IsSymmetricFiniteMatrix Y)
    (hpos : forall i j : Fin n,
      0 < 2 * alpha ^ 2 * (lam i ^ 2 + lam j ^ 2) + gamma ^ 2)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma)
    (hscale : 0 < 2 * alpha * frobNorm Y + gamma) :
    frobNorm (lyapunovResidual n A C Y) /
        (2 * alpha * frobNorm Y + gamma) <=
      lyapunovBackwardErrorInf n A C Y alpha gamma := by
  exact
    lyapunov_relative_residual_le_backwardErrorInf n A C Y alpha gamma
      halpha hgamma hscale
      (lyapunovBackwardErrorValues_nonempty_of_symmetric_spectral n
        A C Y U lam alpha gamma hY hU hC hYsym hpos)

/-- Higham, 2nd ed., Chapter 16, Section 16.2.1, equation (16.21):
    source-numbered alias for the Lyapunov residual-ratio lower bound. -/
alias H16_eq16_21_lyapunov_relative_residual_le_backwardErrorInf_of_symmetric_spectral :=
  lyapunov_relative_residual_le_backwardErrorInf_of_symmetric_spectral

-- ============================================================
-- (16.29): floating-point computed-residual dR model
-- ============================================================

/-- Elementary gamma bound: `u ≤ γ₁`. -/
lemma u_le_gamma_one (fp : FPModel) (h1 : gammaValid fp 1) :
    fp.u ≤ gamma fp 1 := by
  have h1' : ((1 : ℕ) : ℝ) * fp.u < 1 := h1
  have hden : (0 : ℝ) < 1 - ((1 : ℕ) : ℝ) * fp.u := by linarith
  unfold gamma
  rw [le_div_iff₀ hden]
  push_cast
  nlinarith [fp.u_nonneg, sq_nonneg fp.u]

/-- Elementary gamma bound: `2u + u² ≤ γ₂`. -/
lemma two_u_add_u_sq_le_gamma_two (fp : FPModel) (h2 : gammaValid fp 2) :
    2 * fp.u + fp.u ^ 2 ≤ gamma fp 2 := by
  have h2' : ((2 : ℕ) : ℝ) * fp.u < 1 := h2
  have hden : (0 : ℝ) < 1 - ((2 : ℕ) : ℝ) * fp.u := by linarith
  unfold gamma
  rw [le_div_iff₀ hden]
  push_cast
  nlinarith [fp.u_nonneg, sq_nonneg fp.u]

/-- Gamma coefficient consolidation for the subtract-then-scale path of the
    computed Sylvester residual: `(2u + u²) + (1+u)² γₘ ≤ γₘ₊₂`. -/
lemma sub_then_scale_coeff_le_gamma (fp : FPModel) (m : ℕ)
    (hval : gammaValid fp (m + 2)) :
    (2 * fp.u + fp.u ^ 2) + (1 + fp.u) ^ 2 * gamma fp m ≤ gamma fp (m + 2) := by
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hval
  have hm : gammaValid fp m := gammaValid_mono fp (by omega) hval
  have hγm : 0 ≤ gamma fp m := gamma_nonneg fp hm
  have hc2 : 2 * fp.u + fp.u ^ 2 ≤ gamma fp 2 :=
    two_u_add_u_sq_le_gamma_two fp h2
  have hexp : (1 + fp.u) ^ 2 = 1 + (2 * fp.u + fp.u ^ 2) := by ring
  have hsq : (1 + fp.u) ^ 2 ≤ 1 + gamma fp 2 := by
    rw [hexp]
    linarith
  have hmul : (1 + fp.u) ^ 2 * gamma fp m ≤ (1 + gamma fp 2) * gamma fp m :=
    mul_le_mul_of_nonneg_right hsq hγm
  have hsum : gamma fp m + gamma fp 2 + gamma fp m * gamma fp 2 ≤
      gamma fp (m + 2) :=
    gamma_sum_le fp m 2 hval
  have hprod : (1 + gamma fp 2) * gamma fp m =
      gamma fp m + gamma fp m * gamma fp 2 := by ring
  linarith

/-- Gamma coefficient consolidation for the add-then-scale path of the
    computed Sylvester residual: `u + (1+u) γₙ ≤ γₙ₊₁`. -/
lemma add_then_scale_coeff_le_gamma (fp : FPModel) (n : ℕ)
    (hval : gammaValid fp (n + 1)) :
    fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) := by
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hval
  have hn : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hγn : 0 ≤ gamma fp n := gamma_nonneg fp hn
  have hc1 : fp.u ≤ gamma fp 1 := u_le_gamma_one fp h1
  have hmul : (1 + fp.u) * gamma fp n ≤ (1 + gamma fp 1) * gamma fp n :=
    mul_le_mul_of_nonneg_right (by linarith) hγn
  have hsum : gamma fp n + gamma fp 1 + gamma fp n * gamma fp 1 ≤
      gamma fp (n + 1) :=
    gamma_sum_le fp n 1 hval
  have hprod : (1 + gamma fp 1) * gamma fp n =
      gamma fp n + gamma fp n * gamma fp 1 := by ring
  linarith

private lemma abs_sub_add_add_le (w x y z : ℝ) :
    |w - x + y + z| ≤ |w| + |x| + |y| + |z| := by
  have h1 : |w - x + y + z| ≤ |w - x + y| + |z| := abs_add_le _ _
  have h2 : |w - x + y| ≤ |w - x| + |y| := abs_add_le _ _
  have h3 : |w - x| ≤ |w| + |x| := by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le w (-x)
  linarith

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29): the floating-point computed Sylvester residual
    `Rhat = fl(C - A*Xhat + Xhat*B)`.  The two matrix products are the
    repository's column-wise `fl_matMul`, and the combination is evaluated as
    `fl(fl(C - (A*Xhat)) + (Xhat*B))`, one rounded subtraction followed by one
    rounded addition per entry. -/
noncomputable def flSylvesterResidualRect (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n) : RMatFn m n :=
  fun i j =>
    fp.fl_add (fp.fl_sub (C i j) (fl_matMul fp m m n A Xhat i j))
      (fl_matMul fp m n n Xhat B i j)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29): the entrywise rounding budget `Ru` for the computed residual,
    the natural gamma-weighted combination of `|A||Xhat|`, `|Xhat||B|`, and
    `|C|` produced by the floating-point evaluation of
    `fl(fl(C - (A*Xhat)) + (Xhat*B))`. -/
noncomputable def flSylvesterResidualBudget (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n) : RMatFn m n :=
  fun i j =>
    gamma fp (m + 2) * (∑ k : Fin m, |A i k| * |Xhat k j|) +
      gamma fp (n + 1) * (∑ k : Fin n, |Xhat i k| * |B k j|) +
      gamma fp 2 * |C i j|

/-- The computed-residual budget of eq (16.29) is entrywise nonnegative. -/
lemma flSylvesterResidualBudget_nonneg (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1)) :
    ∀ i j, 0 ≤ flSylvesterResidualBudget fp m n A B C Xhat i j := by
  intro i j
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hm
  have hS1 : (0 : ℝ) ≤ ∑ k : Fin m, |A i k| * |Xhat k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS2 : (0 : ℝ) ≤ ∑ k : Fin n, |Xhat i k| * |B k j| :=
    Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  exact add_nonneg
    (add_nonneg (mul_nonneg (gamma_nonneg fp hm) hS1)
      (mul_nonneg (gamma_nonneg fp hn) hS2))
    (mul_nonneg (gamma_nonneg fp h2) (abs_nonneg _))

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29): floating-point error model for the computed Sylvester
    residual.  If `Rhat = fl(fl(C - (A*Xhat)) + (Xhat*B))` with the products
    computed by `fl_matMul`, then there is an explicit `dR` with
    `Rhat = R(Xhat) + dR` and the entrywise bound
    `|dR| ≤ γ_{m+2} |A||Xhat| + γ_{n+1} |Xhat||B| + γ₂ |C|`.
    This is the exact per-term budget yielded by the standard model; it is
    slightly sharper than the source's aggregated display and implies it by
    `gamma_mono`.  Scope: this analyzes only the residual computation, not the
    Sylvester solve producing `Xhat`. -/
theorem sylvester_computed_residual_dR_model (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1)) :
    ∃ dR : RMatFn m n,
      (∀ i j, flSylvesterResidualRect fp m n A B C Xhat i j =
        sylvesterResidualRect m n A B C Xhat i j + dR i j) ∧
      ∀ i j, |dR i j| ≤ flSylvesterResidualBudget fp m n A B C Xhat i j := by
  refine ⟨fun i j => flSylvesterResidualRect fp m n A B C Xhat i j -
      sylvesterResidualRect m n A B C Xhat i j, fun i j => by ring, ?_⟩
  intro i j
  have hgmval : gammaValid fp m := gammaValid_mono fp (by omega) hm
  have hgnval : gammaValid fp n := gammaValid_mono fp (by omega) hn
  have h2val : gammaValid fp 2 := gammaValid_mono fp (by omega) hm
  have hu : 0 ≤ fp.u := fp.u_nonneg
  -- forward errors of the two floating-point products
  have hE1 := matMul_error_bound fp m m n A Xhat hgmval i j
  have hE2 := matMul_error_bound fp m n n Xhat B hgnval i j
  -- rounded subtraction and addition
  obtain ⟨δ1, hδ1, hs⟩ :=
    fp.model_sub (C i j) (fl_matMul fp m m n A Xhat i j)
  obtain ⟨δ2, hδ2, ha2⟩ :=
    fp.model_add (fp.fl_sub (C i j) (fl_matMul fp m m n A Xhat i j))
      (fl_matMul fp m n n Xhat B i j)
  set P1 := fl_matMul fp m m n A Xhat i j with hP1
  set P2 := fl_matMul fp m n n Xhat B i j with hP2
  set M1 := ∑ k : Fin m, A i k * Xhat k j with hM1
  set M2 := ∑ k : Fin n, Xhat i k * B k j with hM2
  set S1 := ∑ k : Fin m, |A i k| * |Xhat k j| with hS1
  set S2 := ∑ k : Fin n, |Xhat i k| * |B k j| with hS2
  have hS1nn : 0 ≤ S1 := by
    rw [hS1]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hS2nn : 0 ≤ S2 := by
    rw [hS2]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  -- fold the exact residual and the computed residual
  have hRR : sylvesterResidualRect m n A B C Xhat i j = C i j - (M1 - M2) := by
    simp only [sylvesterResidualRect, sylvesterOpRect, matMulRect]
    rw [← hM1, ← hM2]
  have hfl : flSylvesterResidualRect fp m n A B C Xhat i j =
      fp.fl_add (fp.fl_sub (C i j) P1) P2 := rfl
  have hkey : fp.fl_add (fp.fl_sub (C i j) P1) P2 - (C i j - (M1 - M2)) =
      (C i j - M1) * (δ1 + δ2 + δ1 * δ2) -
        (P1 - M1) * ((1 + δ1) * (1 + δ2)) +
        M2 * δ2 + (P2 - M2) * (1 + δ2) := by
    rw [ha2, hs]
    ring
  -- absolute-value bounds on the four error terms
  have hd12 : |δ1 + δ2 + δ1 * δ2| ≤ 2 * fp.u + fp.u ^ 2 := by
    have habs12 : |δ1 * δ2| ≤ fp.u * fp.u := by
      rw [abs_mul]
      exact mul_le_mul hδ1 hδ2 (abs_nonneg _) hu
    have htri : |δ1 + δ2 + δ1 * δ2| ≤ |δ1 + δ2| + |δ1 * δ2| := abs_add_le _ _
    have htri2 : |δ1 + δ2| ≤ |δ1| + |δ2| := abs_add_le _ _
    nlinarith
  have h1d1 : |1 + δ1| ≤ 1 + fp.u := by
    have h := abs_add_le (1 : ℝ) δ1
    rw [abs_one] at h
    linarith
  have h1d2 : |1 + δ2| ≤ 1 + fp.u := by
    have h := abs_add_le (1 : ℝ) δ2
    rw [abs_one] at h
    linarith
  have he12 : |(1 + δ1) * (1 + δ2)| ≤ (1 + fp.u) ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul h1d1 h1d2 (abs_nonneg _) (by linarith)
  have hM1abs : |M1| ≤ S1 := by
    rw [hM1, hS1]
    calc
      |∑ k : Fin m, A i k * Xhat k j| ≤ ∑ k : Fin m, |A i k * Xhat k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin m, |A i k| * |Xhat k j| :=
        Finset.sum_congr rfl fun k _ => abs_mul _ _
  have hM2abs : |M2| ≤ S2 := by
    rw [hM2, hS2]
    calc
      |∑ k : Fin n, Xhat i k * B k j| ≤ ∑ k : Fin n, |Xhat i k * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin n, |Xhat i k| * |B k j| :=
        Finset.sum_congr rfl fun k _ => abs_mul _ _
  have hCM1 : |C i j - M1| ≤ |C i j| + S1 := by
    have h : |C i j - M1| ≤ |C i j| + |M1| := by
      simpa [sub_eq_add_neg, abs_neg] using abs_add_le (C i j) (-M1)
    linarith
  -- the four bounded terms
  have t1 : |(C i j - M1) * (δ1 + δ2 + δ1 * δ2)| ≤
      (|C i j| + S1) * (2 * fp.u + fp.u ^ 2) := by
    rw [abs_mul]
    exact mul_le_mul hCM1 hd12 (abs_nonneg _)
      (add_nonneg (abs_nonneg _) hS1nn)
  have t2 : |(P1 - M1) * ((1 + δ1) * (1 + δ2))| ≤
      (gamma fp m * S1) * (1 + fp.u) ^ 2 := by
    rw [abs_mul]
    exact mul_le_mul hE1 he12 (abs_nonneg _)
      (mul_nonneg (gamma_nonneg fp hgmval) hS1nn)
  have t3 : |M2 * δ2| ≤ S2 * fp.u := by
    rw [abs_mul]
    exact mul_le_mul hM2abs hδ2 (abs_nonneg _) hS2nn
  have t4 : |(P2 - M2) * (1 + δ2)| ≤ (gamma fp n * S2) * (1 + fp.u) := by
    rw [abs_mul]
    exact mul_le_mul hE2 h1d2 (abs_nonneg _)
      (mul_nonneg (gamma_nonneg fp hgnval) hS2nn)
  -- gamma consolidation of the per-term coefficients
  have hc2 : 2 * fp.u + fp.u ^ 2 ≤ gamma fp 2 :=
    two_u_add_u_sq_le_gamma_two fp h2val
  have hcm : (2 * fp.u + fp.u ^ 2) + (1 + fp.u) ^ 2 * gamma fp m ≤
      gamma fp (m + 2) :=
    sub_then_scale_coeff_le_gamma fp m hm
  have hcn : fp.u + (1 + fp.u) * gamma fp n ≤ gamma fp (n + 1) :=
    add_then_scale_coeff_le_gamma fp n hn
  have hterm1 : (2 * fp.u + fp.u ^ 2) * |C i j| ≤ gamma fp 2 * |C i j| :=
    mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)
  have hterm2 : ((2 * fp.u + fp.u ^ 2) + (1 + fp.u) ^ 2 * gamma fp m) * S1 ≤
      gamma fp (m + 2) * S1 :=
    mul_le_mul_of_nonneg_right hcm hS1nn
  have hterm3 : (fp.u + (1 + fp.u) * gamma fp n) * S2 ≤
      gamma fp (n + 1) * S2 :=
    mul_le_mul_of_nonneg_right hcn hS2nn
  have hbudget : flSylvesterResidualBudget fp m n A B C Xhat i j =
      gamma fp (m + 2) * S1 + gamma fp (n + 1) * S2 + gamma fp 2 * |C i j| := by
    simp only [flSylvesterResidualBudget]
    rw [← hS1, ← hS2]
  -- assemble
  show |flSylvesterResidualRect fp m n A B C Xhat i j -
      sylvesterResidualRect m n A B C Xhat i j| ≤
    flSylvesterResidualBudget fp m n A B C Xhat i j
  rw [hfl, hRR, hkey, hbudget]
  calc
    |(C i j - M1) * (δ1 + δ2 + δ1 * δ2) -
        (P1 - M1) * ((1 + δ1) * (1 + δ2)) +
        M2 * δ2 + (P2 - M2) * (1 + δ2)|
        ≤ |(C i j - M1) * (δ1 + δ2 + δ1 * δ2)| +
            |(P1 - M1) * ((1 + δ1) * (1 + δ2))| +
            |M2 * δ2| + |(P2 - M2) * (1 + δ2)| :=
          abs_sub_add_add_le _ _ _ _
    _ ≤ (|C i j| + S1) * (2 * fp.u + fp.u ^ 2) +
          (gamma fp m * S1) * (1 + fp.u) ^ 2 +
          S2 * fp.u + (gamma fp n * S2) * (1 + fp.u) := by
        linarith
    _ = (2 * fp.u + fp.u ^ 2) * |C i j| +
          ((2 * fp.u + fp.u ^ 2) + (1 + fp.u) ^ 2 * gamma fp m) * S1 +
          (fp.u + (1 + fp.u) * gamma fp n) * S2 := by
        ring
    _ ≤ gamma fp (m + 2) * S1 + gamma fp (n + 1) * S2 +
          gamma fp 2 * |C i j| := by
        linarith

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29): the floating-point computed residual together with its
    gamma-weighted budget satisfies the `IsSylvesterComputedResidualBudget`
    certificate consumed by the practical error bound of `Higham16.lean`. -/
theorem isSylvesterComputedResidualBudget_fl (fp : FPModel) (m n : ℕ)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat : RMatFn m n)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1)) :
    IsSylvesterComputedResidualBudget m n A B C Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat) := by
  obtain ⟨dR, hRhat, hdR⟩ :=
    sylvester_computed_residual_dR_model fp m n A B C Xhat hm hn
  exact sylvesterComputedResidualBudget_of_error_model m n A B C Xhat
    (flSylvesterResidualRect fp m n A B C Xhat)
    (flSylvesterResidualBudget fp m n A B C Xhat) dR hRhat
    (flSylvesterResidualBudget_nonneg fp m n A B C Xhat hm hn) hdR

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), arbitrary-coefficient floating-point residual endpoint:
    a supplied left inverse `Pinv` for the vec/Kronecker Sylvester coefficient,
    an entrywise absolute bound `PinvAbs`, and the floating-point residual
    computation `flSylvesterResidualRect` give the practical relative
    max-entry forward-error bound.  Scope: this models only the residual
    computation in floating point; the exact Sylvester solution `X` and left
    inverse certificate are hypotheses. -/
theorem sylvester_practical_error_bound_fl_of_left_inverse (fp : FPModel)
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      Pinv PinvAbs hX hLeft hPinvAbs
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), spectral-separation floating-point residual endpoint:
    if the entrywise complexifications of `A` and `B` have no common supplied
    complex right eigenvalue, then the floating-point residual computation
    `flSylvesterResidualRect` and budget `flSylvesterResidualBudget` feed the
    practical relative max-entry forward-error bound.  Scope: this models only
    the residual computation in floating point, not the solve algorithm that
    produced `Xhat`. -/
theorem sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate
      m n A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      hno hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), source-numbered alias for the no-common-complex-spectrum
    floating-point residual endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue :=
  sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), spectral-separation floating-point scalar endpoint:
    after the no-common complex spectrum certificate supplies the exact inverse
    budget, a scalar cap on the floating residual practical budget gives the
    source-shaped `eta / ||Xhat||` relative bound. -/
theorem sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_scalar
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_scalar
      m n A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      eta hno hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), spectral-separation floating-point monotone endpoint:
    componentwise larger inverse and residual-budget inputs preserve the
    practical relative bound for the floating residual computation.  This is an
    estimator-ready adapter, not an estimator proof. -/
theorem sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_mono
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono
      m n A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' hno hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), spectral-separation floating-point monotone scalar endpoint:
    after componentwise estimator enlargement, a scalar cap on the enlarged
    practical budget gives the relative max-entry forward-error bound. -/
theorem sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_mono_scalar
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hno : NoCommonComplexRightEigenvalue (realMatrixToComplex A)
      (realMatrixToComplex B))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_no_common_complex_right_eigenvalue_computed_residual_certificate_mono_scalar
      m n A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' eta hno hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), source-numbered alias for the scalar no-common-complex-spectrum
    floating-point residual endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_scalar :=
  sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), source-numbered alias for the monotone no-common-complex-spectrum
    floating-point residual endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_mono :=
  sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_mono

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), source-numbered alias for the monotone scalar
    no-common-complex-spectrum floating-point residual endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_mono_scalar :=
  sylvester_practical_error_bound_fl_of_no_common_complex_right_eigenvalue_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient determinant endpoint:
    nonsingularity of the vec/Kronecker Sylvester coefficient discharges the
    inverse left-inverse hypothesis in the floating-point practical residual
    bound.  Scope: square coefficients; only the residual computation is
    modeled in floating point, not a solve algorithm or condition estimator. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_left_inverse fp n n
      A B C X Xhat
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient determinant scalar endpoint:
    nonsingularity supplies `sylvesterVecCoeffNonsingInvAbs`; a scalar
    component cap on that practical budget gives the source-shaped
    `eta / ||Xhat||` bound.  Scope: square coefficients; only the residual
    computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat)
      (flSylvesterResidualBudget fp n n A B C Xhat)
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient determinant monotone endpoint:
    after the exact nonsingular-inverse budget is obtained from the determinant
    proof, componentwise larger estimator inputs preserve the practical
    floating-point residual bound.  This is an estimator-ready adapter, not a
    LAPACK estimator proof. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient determinant monotone scalar
    endpoint: after monotone estimator enlargement, a scalar component cap on
    the enlarged practical budget gives the source-shaped relative bound.
    Scope: square coefficients; only residual arithmetic is modeled. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29): source-numbered aliases for square
    determinant-certified floating-point practical residual endpoints. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero :=
  sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero

alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar

alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono :=
  sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono

alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov specialization
    of the determinant practical computed-residual certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hdet hXSylv hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov
    specialization of the determinant practical certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru eta
      hdet hXSylv hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    specialization of the determinant practical certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' hdet hXSylv hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    specialization of the determinant practical certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' eta hdet hXSylv hBudget hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov specialization
    of the determinant practical raw computed-residual budget endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hdet hXSylv hRu hRhatSylv hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov
    specialization of the determinant practical raw computed-residual budget
    endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru eta
      hdet hXSylv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    specialization of the determinant practical raw computed-residual budget
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' hdet hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    specialization of the determinant practical raw computed-residual budget
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      PinvAbs' eta hdet hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov specialization
    of the determinant practical explicit residual-error model endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hdet hXSylv hRhatSylv hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov
    specialization of the determinant practical explicit residual-error model
    endpoint. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR eta
      hdet hXSylv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    specialization of the determinant practical explicit residual-error model
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      PinvAbs' hdet hXSylv hPinvAbs_le hRhatSylv hRu hdR
      hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    specialization of the determinant practical explicit residual-error model
    endpoint with supplied inverse and residual estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      PinvAbs' eta hdet hXSylv hPinvAbs_le hRhatSylv hRu hdR
      hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the Lyapunov determinant computed-residual
    certificate practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the scalar Lyapunov determinant
    computed-residual certificate endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the monotone Lyapunov determinant
    computed-residual certificate endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the monotone-scalar Lyapunov determinant
    computed-residual certificate endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the Lyapunov determinant raw computed-residual
    budget practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the scalar Lyapunov determinant raw-budget
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the monotone Lyapunov determinant raw-budget
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the monotone-scalar Lyapunov determinant
    raw-budget practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the Lyapunov determinant explicit residual-error
    model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the scalar Lyapunov determinant explicit
    residual-error model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the monotone Lyapunov determinant explicit
    residual-error model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16, equation (16.29):
    source-numbered alias for the monotone-scalar Lyapunov determinant explicit
    residual-error model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov practical
    computed-residual certificate from a supplied positive separation lower
    bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat Rhat Ru hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov practical
    computed-residual certificate from a supplied positive separation lower
    bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru eta hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    practical computed-residual certificate from a supplied positive
    separation lower bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hBudget
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    practical computed-residual certificate from a supplied positive
    separation lower bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hBudget
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov computed-residual certificate practical endpoint
    from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov computed-residual certificate practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov computed-residual certificate practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov computed-residual certificate
    practical endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov raw residual-budget endpoint from
    `SepLowerBound(A,-A^T)`: the separation certificate gives determinant
    nonsingularity, while the residual and residual-rounding budget stay in
    Lyapunov notation. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A C X Xhat Rhat Ru hdet hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov raw residual-budget endpoint from
    `SepLowerBound(A,-A^T)`: the practical budget is capped by `eta`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A C X Xhat Rhat Ru eta hdet hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    `SepLowerBound(A,-A^T)`: enlarged inverse and residual budgets preserve the
    practical error bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from `SepLowerBound(A,-A^T)`: an `eta` cap on the enlarged
    practical budget gives the source-shaped relative bound. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov explicit residual-error-model endpoint
    from `SepLowerBound(A,-A^T)`: `Rhat = residual + dR` with a componentwise
    bound on `dR`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hdet hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov explicit residual-error-model
    endpoint from `SepLowerBound(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A C X Xhat Rhat Ru dR eta hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov explicit residual-error-model
    endpoint from `SepLowerBound(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov explicit
    residual-error-model endpoint from `SepLowerBound(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
      (fun i j => -matTranspose A i j) sigma hSep
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov raw residual-budget practical endpoint from a
    source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov raw residual-budget practical endpoint from
    a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov raw residual-budget practical endpoint
    from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov raw residual-budget practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov explicit residual-error-model practical endpoint
    from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov explicit residual-error-model practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov explicit residual-error-model practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov explicit residual-error-model
    practical endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov practical
    computed-residual certificate from a supplied operator sigma-min lower
    bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat Rhat Ru hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov practical
    computed-residual certificate from a supplied operator sigma-min lower
    bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru eta hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    practical computed-residual certificate from a supplied operator sigma-min
    lower bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hBudget
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    practical computed-residual certificate from a supplied operator sigma-min
    lower bound. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hBudget
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the Lyapunov operator-sigma-min practical
    computed-residual certificate endpoint. -/
theorem H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
      n A C X Xhat Rhat Ru sigma hsigma hSigmaMin hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered scalar-cap alias for the Lyapunov operator-sigma-min
    practical computed-residual certificate endpoint. -/
theorem H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru sigma hsigma hSigmaMin eta hX hBudget
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered monotone-estimator alias for the Lyapunov operator-sigma-min
    practical computed-residual certificate endpoint. -/
theorem H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' sigma hsigma hSigmaMin PinvAbs'
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered monotone scalar-cap alias for the Lyapunov
    operator-sigma-min practical computed-residual certificate endpoint. -/
theorem H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' sigma hsigma hSigmaMin PinvAbs' eta
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov raw residual-budget endpoint from a
    supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A C X Xhat Rhat Ru hdet hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov raw residual-budget endpoint from
    a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A C X Xhat Rhat Ru eta hdet hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint
    from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov explicit residual-error-model endpoint
    from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hdet hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov explicit residual-error-model
    endpoint from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A C X Xhat Rhat Ru dR eta hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov explicit residual-error-model
    endpoint from a supplied operator sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov explicit
    residual-error-model endpoint from a supplied operator sigma-min
    certificate. -/
theorem lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_lyapunovSpecial_det_ne_zero_of_operator_sigmaMin
      n A sigma hsigma hSigmaMin
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov operator-sigma-min raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov operator-sigma-min raw residual-budget
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov operator-sigma-min raw residual-budget
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov operator-sigma-min raw
    residual-budget practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov operator-sigma-min explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov operator-sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov operator-sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov operator-sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16, equation (16.29), Lyapunov practical
    computed-residual certificate from a positive lower bound on the exact
    separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat Rhat Ru hdet hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), scalar Lyapunov practical
    computed-residual certificate from a positive lower bound on the exact
    separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat Rhat Ru eta hdet hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone Lyapunov
    practical computed-residual certificate from a positive lower bound on the
    exact separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hBudget
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16, equation (16.29), monotone scalar Lyapunov
    practical computed-residual certificate from a positive lower bound on the
    exact separation infimum. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hBudget :
      IsSylvesterComputedResidualBudget n n A
        (fun i j => -matTranspose A i j) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hBudget
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov raw residual-budget endpoint from a
    positive lower bound on the exact `sylvesterSepInf` for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A C X Xhat Rhat Ru hdet hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov raw residual-budget endpoint from a
    positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A C X Xhat Rhat Ru eta hdet hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX hRu
      hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov explicit residual-error-model endpoint
    from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hdet hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov explicit residual-error-model
    endpoint from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A C X Xhat Rhat Ru dR eta hdet hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov explicit residual-error-model
    endpoint from a positive exact-infimum certificate for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov explicit
    residual-error-model endpoint from a positive exact-infimum certificate for
    `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
      (fun i j => -matTranspose A i j) sigma hsigma hle
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta hdet hX
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov computed-residual certificate practical endpoint
    from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov computed-residual certificate practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov computed-residual certificate practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov computed-residual certificate
    practical endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov raw residual-budget practical endpoint from a
    positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov raw residual-budget practical endpoint from
    a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov raw residual-budget practical endpoint
    from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov raw residual-budget practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov explicit residual-error-model practical endpoint
    from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Lyapunov explicit residual-error-model practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov explicit residual-error-model practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Lyapunov explicit residual-error-model
    practical endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: a concrete left-inverse finite-op-norm
    certificate gives determinant nonsingularity, which supplies the canonical
    exact inverse budget for a packaged computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap version of the
    concrete left-inverse finite-op-norm computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone version of the
    concrete left-inverse finite-op-norm computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar cap
    version of the concrete left-inverse finite-op-norm certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real) {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: a positive finite-Gram eigenvalue
    certificate gives determinant nonsingularity for a packaged
    computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap version of the
    Gram-eigenvalue computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone version of the
    Gram-eigenvalue computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar cap
    version of the Gram-eigenvalue computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: a positive sigma-min certificate gives
    determinant nonsingularity for a packaged computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap version of the
    sigma-min computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone version of the
    sigma-min computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar cap
    version of the sigma-min computed-residual certificate route. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse computed-residual certificate
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar concrete-left-inverse computed-residual certificate
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse computed-residual certificate
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar concrete-left-inverse computed-residual
    certificate practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram computed-residual certificate practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar finite-Gram computed-residual certificate practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram computed-residual certificate practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar finite-Gram computed-residual certificate
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min computed-residual certificate practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar concrete sigma-min computed-residual certificate
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min computed-residual certificate
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar concrete sigma-min computed-residual
    certificate practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square
    arbitrary-coefficient endpoint: an operator sigma-min lower-bound
    certificate discharges nonsingularity of the vec/Kronecker Sylvester
    coefficient for a packaged computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar cap endpoint:
    an operator sigma-min lower-bound certificate discharges nonsingularity
    of the vec/Kronecker Sylvester coefficient. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone endpoint:
    an operator sigma-min lower-bound certificate supplies the nonsingular
    inverse budget before componentwise estimator enlargement. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar endpoint:
    an operator sigma-min lower-bound certificate supplies the nonsingular
    inverse budget before estimator enlargement and a scalar component cap. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: an operator sigma-min lower-bound certificate discharges
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), scalar residual-error-model endpoint: an operator
    sigma-min lower-bound certificate discharges determinant nonsingularity,
    and a scalar cap on the practical budget gives the source-shaped relative
    max-entry bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), monotone residual-error-model endpoint: an operator
    sigma-min lower-bound certificate supplies determinant nonsingularity,
    while componentwise larger practical estimates preserve the bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), monotone scalar residual-error-model endpoint: after
    componentwise practical-budget enlargement, a scalar cap gives the
    source-shaped bound under an operator sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: a concrete finite-op-norm left-inverse certificate for the
    vec/Kronecker Sylvester coefficient supplies determinant nonsingularity,
    and the caller supplies the absolute computed-residual budget directly.
    Scope: square coefficients; this is a non-floating residual-budget adapter,
    not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: a positive finite-Gram eigenvalue certificate for the
    vec/Kronecker Sylvester coefficient supplies determinant nonsingularity,
    and the caller supplies the absolute computed-residual budget directly.
    Scope: square coefficients; this is a non-floating residual-budget adapter,
    not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: a positive sigma-min lower-bound certificate for the
    vec/Kronecker Sylvester coefficient supplies determinant nonsingularity,
    and the caller supplies the absolute computed-residual budget directly.
    Scope: square coefficients; this is a non-floating residual-budget adapter,
    not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: a concrete finite-op-norm left-inverse certificate supplies
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, and an explicit residual perturbation model
    supplies the computed-residual certificate.  Scope: this is a certificate
    transfer theorem, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRhat hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    scalar endpoint: a concrete finite-op-norm left-inverse certificate
    supplies determinant nonsingularity, and a scalar cap on the practical
    budget gives the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone endpoint: a concrete finite-op-norm left-inverse certificate
    supplies determinant nonsingularity, while componentwise larger practical
    estimates preserve the bound.  This is a certificate-transfer theorem, not
    an estimator correctness result. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone scalar endpoint: after componentwise practical-budget
    enlargement, a scalar cap gives the source-shaped bound under a concrete
    finite-op-norm left-inverse certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    scalar endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound.  This is a certificate-transfer theorem, not an
    estimator correctness result. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone scalar endpoint: after componentwise practical-budget
    enlargement, a scalar cap gives the source-shaped bound under a positive
    finite-Gram eigenvalue certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    scalar endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound.  This is a certificate-transfer theorem, not an
    estimator correctness result. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient residual-error-model
    monotone scalar endpoint: after componentwise practical-budget
    enlargement, a scalar cap gives the source-shaped bound under a positive
    sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar concrete-left-inverse explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar concrete-left-inverse explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram explicit residual-error-model practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar finite-Gram explicit residual-error-model practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram explicit residual-error-model practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar finite-Gram explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min explicit residual-error-model practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar concrete sigma-min explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar concrete sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: a concrete finite-op-norm left-inverse certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: a concrete finite-op-norm left-inverse certificate
    supplies determinant nonsingularity, while componentwise larger practical
    estimates preserve the bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under a concrete finite-op-norm left-inverse certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A B Pinv hM hLeft hPinv)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    endpoint: an operator sigma-min lower-bound certificate supplies
    determinant nonsingularity, and the caller supplies the absolute computed
    residual budget directly.  Scope: this is a non-floating residual-budget
    adapter, not a solve algorithm or estimator proof. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: an operator sigma-min lower-bound certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.26), (16.28), and (16.29), square arbitrary-coefficient
    Frobenius endpoint: a supplied operator sigma-min lower bound and a raw
    computed-residual certificate give the clean relative Frobenius forward
    error bound once the componentwise residual budget has a Frobenius cap.
    Scope: this consumes a residual-budget certificate; it is not a proof that
    a solver or estimator produced the certificate. -/
theorem sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma eta : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hExact : forall i j, sylvesterOp n A B X i j = C i j := by
    intro i j
    simpa [IsSylvesterSolutionRect, sylvesterOpRect, sylvesterOp,
      matMulRect_square_eq_matMul] using hX i j
  have hRhat_square : forall i j,
      |sylvesterResidual n A B C Xhat i j - Rhat i j| <= Ru i j := by
    intro i j
    simpa [sylvesterResidualRect, sylvesterResidual, sylvesterOpRect,
      sylvesterOp, matMulRect_square_eq_matMul] using hRhat i j
  have hResidualEntry : forall i j,
      |sylvesterResidual n A B C Xhat i j| <=
        1 * |(|Rhat i j| + Ru i j)| := by
    intro i j
    have hnonneg : 0 <= |Rhat i j| + Ru i j :=
      add_nonneg (abs_nonneg _) (hRu i j)
    calc
      |sylvesterResidual n A B C Xhat i j|
          = |Rhat i j +
              (sylvesterResidual n A B C Xhat i j - Rhat i j)| := by
              congr 1
              ring
      _ <= |Rhat i j| +
            |sylvesterResidual n A B C Xhat i j - Rhat i j| :=
          abs_add_le _ _
      _ <= |Rhat i j| + Ru i j := by
          exact add_le_add (le_refl _) (hRhat_square i j)
      _ = 1 * |(|Rhat i j| + Ru i j)| := by
          rw [abs_of_nonneg hnonneg]
          ring
  have hResidualNorm :
      frobNorm (sylvesterResidual n A B C Xhat) <=
        frobNorm (fun i j => |Rhat i j| + Ru i j) := by
    have h :=
      frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        (sylvesterResidual n A B C Xhat)
        (fun i j => |Rhat i j| + Ru i j)
        (c := 1) (by norm_num) hResidualEntry
    simpa using h
  exact
    sylvester_relative_error_le_of_sigmaMin_residual_budget n
      A B C X Xhat sigma eta hsigma hSigmaMin hExact hX_pos
      (hResidualNorm.trans hResidualCap)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.26), (16.28), and (16.29), square arbitrary-coefficient
    Frobenius endpoint: a source `SepLowerBound` certificate discharges the
    operator sigma-min hypothesis of the clean raw residual-budget theorem. -/
theorem sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A B C X Xhat Rhat Ru sigma eta hSep.1
      (sylvesterOp_sigmaMin_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.26), (16.28), and (16.29), square arbitrary-coefficient
    Frobenius endpoint: a positive exact lower bound on `sylvesterSepInf`
    supplies the `SepLowerBound` certificate, then the clean raw
    residual-budget conclusion follows. -/
theorem sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.27)-(16.29), Lyapunov Frobenius endpoint: a supplied
    Lyapunov operator sigma-min lower bound and raw computed-residual budget
    give the clean relative Frobenius forward-error bound. -/
theorem lyapunov_relative_error_le_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma eta : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hSigmaMinSylv : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <=
        frobNorm (sylvesterOp n A (fun i j => -matTranspose A i j) Y) := by
    intro Y
    have h := hSigmaMin Y
    rwa [lyapunovOp_eq_sylvesterOp n A Y] at h
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru sigma eta
      hsigma hSigmaMinSylv hXSylv hRu hRhatSylv hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.27)-(16.29), Lyapunov Frobenius endpoint:
    `SepLowerBound(A,-A^T)` discharges the operator lower-bound hypothesis of
    the clean raw residual-budget theorem. -/
theorem lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A C X Xhat Rhat Ru sigma eta hSep.1
      (lyapunovOp_sigmaMin_of_sepLowerBound n A sigma hSep)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equations (16.27)-(16.29), Lyapunov Frobenius endpoint: a positive
    lower bound on the exact `sep(A,-A^T)` infimum supplies the source
    separation certificate and hence the clean residual-budget bound. -/
theorem lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A C X Xhat Rhat Ru
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Sylvester
    Frobenius relative-error endpoint from a raw computed-residual budget and
    a supplied operator sigma-min lower bound. -/
theorem H16_eq16_29_sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (sigma eta : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A B C X Xhat Rhat Ru sigma eta hsigma hSigmaMin
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Lyapunov
    Frobenius relative-error endpoint from a raw computed-residual budget and
    a supplied Lyapunov operator sigma-min lower bound. -/
theorem H16_eq16_29_lyapunov_relative_error_le_of_operator_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) (sigma eta : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_operator_sigmaMin_computed_residual_budget
      n A C X Xhat Rhat Ru sigma eta hsigma hSigmaMin
      hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Sylvester
    Frobenius relative-error endpoint from a raw computed-residual budget and
    a `SepLowerBound` certificate. -/
theorem H16_eq16_29_sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A B C X Xhat Rhat Ru hSep hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Sylvester
    Frobenius relative-error endpoint when a positive lower bound on
    `sylvesterSepInf` supplies the separation certificate. -/
theorem H16_eq16_29_sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
      n A B C X Xhat Rhat Ru hsigma hle hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Lyapunov
    Frobenius relative-error endpoint from a raw computed-residual budget and
    a `SepLowerBound(A,-A^T)` certificate. -/
theorem H16_eq16_29_lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A C X Xhat Rhat Ru hSep hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Lyapunov
    Frobenius relative-error endpoint when a positive lower bound on
    `sep(A,-A^T)` supplies the separation certificate. -/
theorem H16_eq16_29_lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_budget
      n A C X Xhat Rhat Ru hsigma hle hX hRu hRhat hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Sylvester Frobenius residual-error-model endpoint:
    an explicit `Rhat = residual + dR` model derives the raw residual-budget
    hypothesis under a source `SepLowerBound(A,B)` certificate. -/
theorem sylvester_relative_error_le_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hRhatBudget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j := by
    intro i j
    have hdiff :
        sylvesterResidualRect n n A B C Xhat i j - Rhat i j = -dR i j := by
      rw [hRhat i j]
      ring
    rw [hdiff, abs_neg]
    exact hdR i j
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A B C X Xhat Rhat Ru hSep hX hRu hRhatBudget hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Sylvester
    Frobenius relative-error endpoint from an explicit residual-error model
    and a `SepLowerBound(A,B)` certificate. -/
theorem H16_eq16_29_sylvester_relative_error_le_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR hSep hX hRhat hRu hdR hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Sylvester Frobenius residual-error-model endpoint:
    a positive lower bound on `sylvesterSepInf` supplies the separation
    certificate for the explicit computed-residual model. -/
theorem sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_sepLowerBound_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)
      hX hRhat hRu hdR hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Sylvester
    Frobenius relative-error endpoint from an explicit residual-error model
    and a positive lower bound on `sylvesterSepInf`. -/
theorem H16_eq16_29_sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    sylvester_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR hsigma hle hX hRhat hRu hdR
      hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov Frobenius residual-error-model endpoint:
    an explicit `Rhat = residual + dR` model derives the raw residual-budget
    hypothesis under a source `SepLowerBound(A,-A^T)` certificate. -/
theorem lyapunov_relative_error_le_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  have hRhatBudget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j := by
    intro i j
    have hdiff :
        lyapunovResidual n A C Xhat i j - Rhat i j = -dR i j := by
      rw [hRhat i j]
      ring
    rw [hdiff, abs_neg]
    exact hdR i j
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_budget
      n A C X Xhat Rhat Ru hSep hX hRu hRhatBudget hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Lyapunov
    Frobenius relative-error endpoint from an explicit residual-error model and
    a `SepLowerBound(A,-A^T)` certificate. -/
theorem H16_eq16_29_lyapunov_relative_error_le_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hSep hX hRhat hRu hdR hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov Frobenius residual-error-model endpoint:
    a positive lower bound on the exact `sep(A,-A^T)` infimum supplies the
    separation certificate for the explicit computed-residual model. -/
theorem lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_sepLowerBound_computed_residual_error_model
      n A C X Xhat Rhat Ru dR
      (SepLowerBound_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hRhat hRu hdR hX_pos hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the Lyapunov
    Frobenius relative-error endpoint from an explicit residual-error model
    and a positive lower bound on the exact `sep(A,-A^T)` infimum. -/
theorem H16_eq16_29_lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n) {sigma eta : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hX_pos : 0 < frobNorm X)
    (hResidualCap :
      frobNorm (fun i j => |Rhat i j| + Ru i j) <=
        eta * sigma * frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <= eta := by
  exact
    lyapunov_relative_error_le_of_pos_le_sylvesterSepInf_computed_residual_error_model
      n A C X Xhat Rhat Ru dR hsigma hle hX hRhat hRu hdR hX_pos
      hResidualCap

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: an operator sigma-min lower-bound certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under an operator sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_operator_sigmaMin
        n A B sigma hsigma hSigmaMin)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Sylvester operator-sigma-min practical computed-residual
    certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Sylvester operator-sigma-min practical
    computed-residual certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Sylvester operator-sigma-min practical
    computed-residual certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Sylvester operator-sigma-min practical
    computed-residual certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Sylvester operator-sigma-min explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Sylvester operator-sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Sylvester operator-sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Sylvester operator-sigma-min explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Sylvester operator-sigma-min raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar Sylvester operator-sigma-min raw residual-budget
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Sylvester operator-sigma-min raw residual-budget
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar Sylvester operator-sigma-min raw
    residual-budget practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_operator_sigmaMin_computed_residual_budget_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: a positive finite-Gram eigenvalue certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under a positive finite-Gram eigenvalue certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A B hlam hEig)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget scalar
    endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, and a scalar cap on the practical budget gives
    the source-shaped relative max-entry bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone endpoint: a positive sigma-min lower-bound certificate supplies
    determinant nonsingularity, while componentwise larger practical estimates
    preserve the bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient raw residual-budget
    monotone scalar endpoint: after componentwise estimator enlargement, a
    scalar cap on the enlarged practical budget gives the source-shaped bound
    under a positive sigma-min lower-bound certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A B hsigma hCoeff)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar concrete-left-inverse raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar concrete-left-inverse raw residual-budget
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram raw residual-budget practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar finite-Gram raw residual-budget practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram raw residual-budget practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar finite-Gram raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min raw residual-budget practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar concrete sigma-min raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min raw residual-budget practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar concrete sigma-min raw residual-budget
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized raw residual-budget endpoint:
    a concrete finite-op-norm left inverse for the vec coefficient supplies the
    square practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru Pinv hM
      hXSylv hLeft hPinv hRu hRhatSylv hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov specialization of the raw
    residual-budget endpoint under a concrete finite-op-norm left inverse. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru Pinv hM eta
      hXSylv hLeft hPinv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint:
    a concrete finite-op-norm left inverse and larger practical estimates
    preserve the relative max-entry bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      Pinv PinvAbs' hM hXSylv hLeft hPinv hRu hRhatSylv hPinvAbs_le
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint under a concrete finite-op-norm left-inverse certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      Pinv PinvAbs' hM eta hXSylv hLeft hPinv hRu hRhatSylv hPinvAbs_le
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse Lyapunov raw computed-residual
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete-left-inverse Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete-left-inverse Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_budget_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized raw residual-budget endpoint:
    positive eigenvalue certificates for the finite Gram matrix of the concrete
    vec coefficient give the practical relative max-entry bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hlam hEig hXSylv hRu hRhatSylv hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov specialization of the raw
    residual-budget endpoint from concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hlam hEig eta hXSylv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    concrete Gram-eigenvalue certificates and enlarged practical estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hlam hEig PinvAbs' hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hlam hEig PinvAbs' eta hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram Lyapunov raw computed-residual practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap finite-Gram Lyapunov raw computed-residual
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram Lyapunov raw computed-residual
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap finite-Gram Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_budget_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized raw residual-budget endpoint:
    a concrete sigma-min lower bound for the vec coefficient gives the
    practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hsigma hCoeff hXSylv hRu hRhatSylv hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov specialization of the raw
    residual-budget endpoint from a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru
      hsigma hCoeff eta hXSylv hRu hRhatSylv heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov raw residual-budget endpoint from
    a concrete sigma-min certificate and enlarged practical estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hsigma hCoeff PinvAbs' hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov raw residual-budget
    endpoint from a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |lyapunovResidual n A C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      |sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j -
          Rhat i j| <= Ru i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_budget i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru'
      hsigma hCoeff PinvAbs' eta hXSylv hRu hRhatSylv hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min Lyapunov raw computed-residual
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete sigma-min Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete sigma-min Lyapunov raw
    computed-residual practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_budget_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized residual-error-model
    endpoint: a concrete finite-op-norm left inverse for the vec coefficient
    gives the practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR Pinv hM
      hXSylv hLeft hPinv hRhatSylv hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov residual-error-model endpoint
    under a concrete finite-op-norm left-inverse certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR Pinv hM eta
      hXSylv hLeft hPinv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov residual-error-model endpoint:
    a concrete finite-op-norm left inverse and larger practical estimates
    preserve the relative max-entry bound. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      Pinv PinvAbs' hM hXSylv hLeft hPinv hPinvAbs_le hRhatSylv hRu hdR
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov residual-error-model
    endpoint under a concrete finite-op-norm left-inverse certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      Pinv PinvAbs' hM eta hXSylv hLeft hPinv hPinvAbs_le hRhatSylv hRu hdR
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized residual-error-model
    endpoint from concrete Gram-eigenvalue certificates for the vec
    coefficient. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hlam hEig hXSylv hRhatSylv hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov residual-error-model endpoint from
    concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hlam hEig eta hXSylv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov residual-error-model endpoint
    from concrete Gram-eigenvalue certificates and enlarged practical
    estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hlam hEig PinvAbs' hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat hRu_le
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov residual-error-model
    endpoint from concrete Gram-eigenvalue certificates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hlam hEig PinvAbs' eta hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat
      hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov-specialized residual-error-model
    endpoint from a concrete sigma-min lower bound for the vec coefficient. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j)) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hsigma hCoeff hXSylv hRhatSylv hRu hdR hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov residual-error-model endpoint from
    a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar
    (n : Nat)
    (A C X Xhat Rhat Ru dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hRhat : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j)) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Ru dR
      hsigma hCoeff eta hXSylv hRhatSylv hRu hdR heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov residual-error-model endpoint
    from a concrete sigma-min certificate and enlarged practical estimates. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hsigma hCoeff PinvAbs' hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat
      hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov residual-error-model
    endpoint from a concrete sigma-min certificate. -/
theorem lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = lyapunovResidual n A C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have hXSylv :
      IsSylvesterSolutionRect n n A (fun i j => -matTranspose A i j) C X := by
    intro i j
    change sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j
    have hij := hX i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  have hRhatSylv : forall i j,
      Rhat i j =
        sylvesterResidualRect n n A (fun i j => -matTranspose A i j) C Xhat i j +
          dR i j := by
    intro i j
    simpa [lyapunovResidual_eq_sylvesterResidual_special n A C Xhat] using
      hRhat_eq i j
  exact
    sylvester_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar
      n A (fun i j => -matTranspose A i j) C X Xhat Rhat Rhat' Ru Ru' dR
      hsigma hCoeff PinvAbs' eta hXSylv hPinvAbs_le hRhatSylv hRu hdR hRhat
      hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse Lyapunov explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete-left-inverse Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete-left-inverse Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram Lyapunov explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap finite-Gram Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap finite-Gram Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_gram_eigenvalues_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min Lyapunov explicit residual-error-model
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete sigma-min Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete sigma-min Lyapunov explicit
    residual-error-model practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar :=
  lyapunov_practical_error_bound_of_vecCoeff_sigmaMin_computed_residual_error_model_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient endpoint: a concrete
    left-inverse certificate for the vec/Kronecker Sylvester coefficient,
    together with a finite operator-2 bound and an entrywise absolute bound on
    that inverse, gives the practical relative max-entry forward-error bound.
    Scope: square coefficients; only the residual arithmetic is modeled in
    floating point, not a solve algorithm or estimator. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  have _hdet : Not ((sylvesterVecCoeff n n A B).det = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv
  exact
    sylvester_practical_error_bound_fl_of_left_inverse fp n n
      A B C X Xhat Pinv PinvAbs hX hLeft hPinvAbs hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient scalar endpoint: a
    concrete finite-op-norm left-inverse certificate and a scalar component cap
    on its practical budget give the source-shaped relative bound
    `eta / ||Xhat||`.  Only the residual arithmetic is modeled in floating
    point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have _hdet : Not ((sylvesterVecCoeff n n A B).det = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat)
      (flSylvesterResidualBudget fp n n A B C Xhat)
      Pinv PinvAbs eta hX hLeft hPinvAbs
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient monotone endpoint: a
    concrete finite-op-norm left-inverse certificate supplies the base
    practical bound, and componentwise larger inverse/residual estimates
    preserve the relative max-entry forward-error bound.  This is an
    estimator-ready adapter, not a proof that the estimates were computed by a
    Sylvester solver. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  have _hdet : Not ((sylvesterVecCoeff n n A B).det = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      Pinv PinvAbs PinvAbs' hX hLeft hPinvAbs hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient monotone scalar endpoint:
    after enlarging the finite-op-norm left-inverse budget and computed
    residual budgets, a scalar component cap on the enlarged practical budget
    gives the source-shaped relative bound.  Only residual arithmetic is
    modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  have _hdet : Not ((sylvesterVecCoeff n n A B).det = 0) :=
    sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
      n A B Pinv hM hLeft hPinv
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      Pinv PinvAbs PinvAbs' eta hX hLeft hPinvAbs hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient endpoint: a positive Gram
    eigenvalue lower-bound certificate for the vec/Kronecker Sylvester
    coefficient discharges the nonsingular-inverse left-inverse hypothesis in
    the floating-point practical residual bound.  Scope: square coefficients;
    only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_left_inverse fp n n
      A B C X Xhat
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
            n A B hlam hEig)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient scalar endpoint: a positive Gram
    eigenvalue lower-bound certificate generates the nonsingular-inverse budget
    `sylvesterVecCoeffNonsingInvAbs`; a scalar component cap on that practical
    budget gives the source-shaped `eta / ||Xhat||` bound.  Scope: square
    coefficients; only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat)
      (flSylvesterResidualBudget fp n n A B C Xhat)
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
            n A B hlam hEig)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient monotone endpoint: a positive Gram
    eigenvalue lower-bound certificate generates the nonsingular-inverse budget
    `sylvesterVecCoeffNonsingInvAbs`, and componentwise larger estimator inputs
    preserve the practical floating-point residual bound.  Scope: square
    coefficients; only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
            n A B hlam hEig)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient monotone scalar endpoint: the Gram
    eigenvalue route supplies `sylvesterVecCoeffNonsingInvAbs`; after monotone
    estimator enlargement, a scalar component cap on the enlarged practical
    budget gives the source-shaped relative bound.  Scope: square coefficients;
    only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
            n A B hlam hEig)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient endpoint: a positive sigma-min
    lower-bound certificate for the vec/Kronecker Sylvester coefficient
    discharges the nonsingular-inverse left-inverse hypothesis in the
    floating-point practical residual bound.  Scope: square coefficients;
    only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_left_inverse fp n n
      A B C X Xhat
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
            n A B hsigma hCoeff)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient scalar endpoint: a positive
    sigma-min lower-bound certificate generates the nonsingular-inverse budget
    `sylvesterVecCoeffNonsingInvAbs`; a scalar component cap on that practical
    budget gives the source-shaped `eta / ||Xhat||` bound.  Scope: square
    coefficients; only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat)
      (flSylvesterResidualBudget fp n n A B C Xhat)
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
            n A B hsigma hCoeff)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient monotone endpoint: a positive
    sigma-min lower-bound certificate generates the nonsingular-inverse budget
    `sylvesterVecCoeffNonsingInvAbs`, and componentwise larger estimator inputs
    preserve the practical floating-point residual bound.  Scope: square
    coefficients; only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
            n A B hsigma hCoeff)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), square arbitrary-coefficient monotone scalar endpoint: the
    sigma-min route supplies `sylvesterVecCoeffNonsingInvAbs`; after monotone
    estimator enlargement, a scalar component cap on the enlarged practical
    budget gives the source-shaped relative bound.  Scope: square coefficients;
    only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat
      (flSylvesterResidualRect fp n n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp n n A B C Xhat) Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
            n A B hsigma hCoeff)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp n n A B C Xhat hn2 hn1)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse Sylvester floating-point practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete-left-inverse Sylvester floating-point
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse Sylvester floating-point
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono :=
  sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete-left-inverse Sylvester
    floating-point practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram Sylvester floating-point practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues :=
  sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap finite-Gram Sylvester floating-point practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram Sylvester floating-point practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono :=
  sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap finite-Gram Sylvester floating-point
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min Sylvester floating-point practical
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin :=
  sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete sigma-min Sylvester floating-point
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min Sylvester floating-point
    practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono :=
  sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete sigma-min Sylvester
    floating-point practical endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono_scalar :=
  sylvester_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient endpoint: a supplied
    positive `SepLowerBound` certificate for `sep(A,B)` makes the
    vec/Kronecker Sylvester coefficient nonsingular and hence instantiates the
    floating-point practical residual bound.  Scope: square coefficients; only
    the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_sepLowerBound
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A B C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient scalar endpoint: a supplied
    positive `SepLowerBound` certificate generates the nonsingular-inverse
    budget, and a scalar component cap gives the source-shaped relative bound.
    Scope: square coefficients; only the residual computation is modeled in
    floating point. -/
theorem sylvester_practical_error_bound_fl_of_sepLowerBound_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A B C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      eta hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient monotone endpoint: a
    supplied positive `SepLowerBound` certificate discharges nonsingularity,
    and componentwise larger estimator inputs preserve the floating-point
    practical residual bound.  This is a certificate route, not a LAPACK
    estimator proof. -/
theorem sylvester_practical_error_bound_fl_of_sepLowerBound_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A B C X Xhat Rhat' Ru'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      PinvAbs' hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient monotone scalar endpoint:
    after a supplied positive `SepLowerBound` certificate and monotone
    estimator enlargement, a scalar component cap gives the source-shaped
    relative bound.  Scope: square coefficients; only residual arithmetic is
    modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_sepLowerBound_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A B C X Xhat Rhat' Ru'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      PinvAbs' eta hX hn2 hn1 hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient endpoint: a positive lower
    bound on the exact infimum model `sylvesterSepInf` makes the vec/Kronecker
    Sylvester coefficient nonsingular and hence instantiates the
    floating-point practical residual bound.  Scope: square coefficients; only
    the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A B C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A B
        sigma hsigma hle)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient scalar endpoint: a positive
    lower bound on `sylvesterSepInf` generates the nonsingular-inverse budget,
    and a scalar component cap gives the source-shaped relative bound.  Scope:
    square coefficients; only residual arithmetic is modeled in floating
    point. -/
theorem sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A B C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A B
        sigma hsigma hle)
      eta hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient monotone endpoint: a
    positive lower bound on the exact infimum model `sylvesterSepInf`
    discharges nonsingularity, and componentwise larger estimator inputs
    preserve the floating-point practical residual bound.  This is a
    certificate route, not a LAPACK estimator proof. -/
theorem sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A B C X Xhat Rhat' Ru'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A B
        sigma hsigma hle)
      PinvAbs' hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, eq (16.29), square arbitrary-coefficient monotone scalar endpoint:
    after a positive lower bound on `sylvesterSepInf` and monotone estimator
    enlargement, a scalar component cap gives the source-shaped relative bound.
    Scope: square coefficients; only residual arithmetic is modeled in
    floating point. -/
theorem sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A B C X Xhat Rhat' Ru'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A B
        sigma hsigma hle)
      PinvAbs' eta hX hn2 hn1 hPinvAbs_le hRhat hRu_le
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the
    floating-point practical endpoint supplied by a positive `SepLowerBound`
    certificate. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_sepLowerBound
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_sepLowerBound fp n
      A B C X Xhat hSep hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered scalar alias for the
    floating-point practical endpoint supplied by a positive `SepLowerBound`
    certificate. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_sepLowerBound_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_sepLowerBound_scalar fp n
      A B C X Xhat hSep eta hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered monotone alias for the
    floating-point practical endpoint supplied by a positive `SepLowerBound`
    certificate. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_sepLowerBound_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_sepLowerBound_mono fp n
      A B C X Xhat Rhat' Ru' hSep PinvAbs' hX hn2 hn1
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered monotone scalar alias for
    the floating-point practical endpoint supplied by a positive
    `SepLowerBound` certificate. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_sepLowerBound_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_sepLowerBound_mono_scalar fp n
      A B C X Xhat Rhat' Ru' hSep PinvAbs' eta hX hn2 hn1
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered alias for the
    floating-point practical endpoint supplied by a positive lower bound on
    `sylvesterSepInf`. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B)
          (flSylvesterResidualRect fp n n A B C Xhat)
          (flSylvesterResidualBudget fp n n A B C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf fp n
      A B C X Xhat hsigma hle hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered scalar alias for the
    floating-point practical endpoint supplied by a positive lower bound on
    `sylvesterSepInf`. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A B)
        (flSylvesterResidualRect fp n n A B C Xhat)
        (flSylvesterResidualBudget fp n n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_scalar fp n
      A B C X Xhat hsigma hle eta hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered monotone alias for the
    floating-point practical endpoint supplied by a positive lower bound on
    `sylvesterSepInf`. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono fp n
      A B C X Xhat Rhat' Ru' hsigma hle PinvAbs' hX hn2 hn1
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
    Section 16.4, equation (16.29): source-numbered monotone scalar alias for
    the floating-point practical endpoint supplied by a positive lower bound on
    `sylvesterSepInf`. -/
theorem H16_eq16_29_sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono_scalar
    (fp : FPModel) (n : Nat)
    (A B C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono_scalar fp n
      A B C X Xhat Rhat' Ru' hsigma hle PinvAbs' eta hX hn2 hn1
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), arbitrary-coefficient scalar endpoint: if a nonnegative scalar
    bounds every component of the practical budget formed from the supplied
    left-inverse bound and the floating-point computed residual, then the
    relative max-entry forward-error bound has source-shaped right-hand side
    `eta / ||Xhat||`.  Only the residual computation is modeled in floating
    point. -/
theorem sylvester_practical_error_bound_fl_of_left_inverse_scalar
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs
        (flSylvesterResidualRect fp m n A B C Xhat)
        (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      Pinv PinvAbs eta hX hLeft hPinvAbs
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), arbitrary-coefficient monotone endpoint: replacing the
    supplied left-inverse bound, computed residual, and residual-rounding
    budget by componentwise larger estimates preserves the practical relative
    max-entry forward-error bound.  This is an estimator-ready adapter, not a
    proof that those estimates were computed by a Sylvester solver. -/
theorem sylvester_practical_error_bound_fl_of_left_inverse_mono
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      Pinv PinvAbs PinvAbs' hX hLeft hPinvAbs hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), arbitrary-coefficient monotone scalar endpoint: after
    enlarging the supplied left-inverse bound, computed residual, and
    residual-rounding budget, a scalar component cap on the enlarged practical
    budget gives the source-shaped relative max-entry bound.  Only the residual
    computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_left_inverse_mono_scalar
    (fp : FPModel) (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      Pinv PinvAbs PinvAbs' eta hX hLeft hPinvAbs hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), end-to-end diagonal instantiation: for separated diagonal
    coefficient matrices, the practical relative max-entry forward-error bound
    holds with the residual computed in floating point by
    `flSylvesterResidualRect` and the rounding budget
    `flSylvesterResidualBudget`.  Scope: the coefficient matrices are diagonal
    (the case with an explicit `|P⁻¹|`), the exact solution `X` is a
    hypothesis, and only the residual computation is floating-point. -/
theorem sylvester_practical_error_bound_fl (fp : FPModel) (m n : ℕ)
    (a : Fin m → ℝ) (b : Fin n → ℝ) (C X Xhat : RMatFn m n)
    (hsep : ∀ i j, ¬(a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat ≤
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b)
          (flSylvesterResidualRect fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
          (flSylvesterResidualBudget fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
    m n a b C X Xhat
    (flSylvesterResidualRect fp m n
      (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
    (flSylvesterResidualBudget fp m n
      (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
    hsep hX
    (isSylvesterComputedResidualBudget_fl fp m n
      (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
    hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), scalar-capped floating-point residual instantiation: if a
    scalar `eta` bounds the max norm of the floating-point practical budget,
    the practical relative max-entry forward-error bound has source-shaped
    right-hand side `eta / ||Xhat||`. -/
theorem sylvester_practical_error_bound_fl_scalar (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X Xhat : RMatFn m n)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta :
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b)
          (flSylvesterResidualRect fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
          (flSylvesterResidualBudget fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_fl fp m n a b C X Xhat
      hsep hX hm hn hXhat
  exact hbase.trans
    (div_le_div_of_nonneg_right heta (le_of_lt hXhat))

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), componentwise scalar-capped floating-point residual
    instantiation: if a nonnegative scalar `eta` bounds every component of the
    separated-diagonal practical budget formed from the floating-point computed
    residual, then the practical relative max-entry forward-error bound has
    right-hand side `eta / ||Xhat||`.  Only the residual computation is modeled
    in floating point. -/
theorem sylvester_practical_error_bound_fl_componentwise_scalar
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X Xhat : RMatFn m n)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent :
      forall p,
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b)
          (flSylvesterResidualRect fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
          (flSylvesterResidualBudget fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
      m n a b C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      eta hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), monotone enlarged-budget floating-point residual
    instantiation: after replacing the separated diagonal inverse, computed
    residual, and residual-rounding budgets by componentwise larger estimates,
    the practical relative max-entry forward-error bound uses the enlarged
    practical budget directly.  This only models the separated-diagonal
    residual computation in floating point; it is not a Schur/Bartels-Stewart
    or LAPACK estimator analysis. -/
theorem sylvester_practical_error_bound_fl_mono
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j| <=
        |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j <=
        Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Ru'
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      PinvAbs' hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §16.4,
    eq (16.29), monotone scalar-capped floating-point residual instantiation:
    after replacing the separated diagonal inverse, computed residual, and
    residual-rounding budgets by componentwise larger estimates, a scalar cap on
    the estimated practical budget gives the source-shaped relative max-entry
    bound.  This only models the separated-diagonal residual computation in
    floating point; it is not a Schur/Bartels-Stewart or LAPACK estimator
    analysis. -/
theorem sylvester_practical_error_bound_fl_mono_scalar
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j| <=
        |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j <=
        Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Ru'
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      PinvAbs' eta hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hPinvAbs_le
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), named diagonal endpoint for the floating-point
    computed residual budget. -/
theorem sylvester_practical_error_bound_fl_of_diagonal
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X Xhat : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b)
          (flSylvesterResidualRect fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
          (flSylvesterResidualBudget fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
      m n a b C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar-capped diagonal endpoint for the
    floating-point computed residual budget. -/
theorem sylvester_practical_error_bound_fl_of_diagonal_scalar
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X Xhat : RMatFn m n)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b)
          (flSylvesterResidualRect fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
          (flSylvesterResidualBudget fp m n
            (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
      m n a b C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      eta hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone diagonal endpoint for enlarged estimates
    of the floating-point computed residual budget. -/
theorem sylvester_practical_error_bound_fl_of_diagonal_mono
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j| <=
        |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j <=
        Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
      m n a b C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Ru' PinvAbs' hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar-capped diagonal endpoint for
    enlarged estimates of the floating-point computed residual budget. -/
theorem sylvester_practical_error_bound_fl_of_diagonal_mono_scalar
    (fp : FPModel) (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j| <=
        |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n
          (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j <=
        Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
      m n a b C X Xhat
      (flSylvesterResidualRect fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)
      Ru' PinvAbs' eta hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), supplied Schur-diagonal endpoint for the
    floating-point computed residual budget.  The Schur factors are exact
    hypotheses; only the residual computation is modeled in floating point. -/
theorem sylvester_practical_error_bound_fl_of_schurDiagonal
    (fp : FPModel) (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
      m n U A V B a b C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      hU hV hA hB hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar-capped supplied Schur-diagonal endpoint for
    the floating-point computed residual budget. -/
theorem sylvester_practical_error_bound_fl_of_schurDiagonal_scalar
    (fp : FPModel) (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B)
          (flSylvesterResidualRect fp m n A B C Xhat)
          (flSylvesterResidualBudget fp m n A B C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
      m n U A V B a b C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat)
      (flSylvesterResidualBudget fp m n A B C Xhat)
      eta hU hV hA hB hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone supplied Schur-diagonal endpoint for
    enlarged estimates of the floating-point computed residual budget. -/
theorem sylvester_practical_error_bound_fl_of_schurDiagonal_mono
    (fp : FPModel) (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
      m n U A V B a b C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' hU hV hA hB hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar-capped supplied Schur-diagonal
    endpoint for enlarged estimates of the floating-point computed residual
    budget. -/
theorem sylvester_practical_error_bound_fl_of_schurDiagonal_mono_scalar
    (fp : FPModel) (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hm : gammaValid fp (m + 2)) (hn : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp m n A B C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp m n A B C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
      m n U A V B a b C X Xhat
      (flSylvesterResidualRect fp m n A B C Xhat) Rhat'
      (flSylvesterResidualBudget fp m n A B C Xhat) Ru'
      PinvAbs' eta hU hV hA hB hsep hX
      (isSylvesterComputedResidualBudget_fl fp m n A B C Xhat hm hn)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov specialization of the floating-point
    computed residual budget: `flSylvesterResidualRect` applied to
    `(A,-A^T)` is a certified computed residual for the Lyapunov equation. -/
theorem isLyapunovComputedResidualBudget_fl (fp : FPModel) (n : Nat)
    (A C Xhat : RMatFn n n)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1)) :
    IsSylvesterComputedResidualBudget n n A
      (fun i j => -matTranspose A i j) C Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat) := by
  exact
    isSylvesterComputedResidualBudget_fl fp n n A
      (fun i j => -matTranspose A i j) C Xhat hn2 hn1

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the Lyapunov floating-point computed-residual
    budget certificate. -/
alias H16_eq16_29_isLyapunovComputedResidualBudget_fl :=
  isLyapunovComputedResidualBudget_fl

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov determinant endpoint: nonsingularity of
    the `(A,-A^T)` vec coefficient and the floating-point computed residual
    give the practical relative max-entry forward-error bound. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      hdet hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov determinant endpoint for the
    floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      eta hdet hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov determinant endpoint: replacing
    the floating-point residual and budget by componentwise larger estimates
    preserves the practical bound. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Ru' PinvAbs' hdet hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov determinant endpoint for
    the floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet :
      Not (Matrix.det
        (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) = 0))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Ru' PinvAbs' eta hdet hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov floating-point endpoint from a concrete
    finite-op-norm left inverse for the `(A,-A^T)` vec coefficient. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A (fun i j => -matTranspose A i j) Pinv hM hLeft hPinv)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov finite-op-norm left-inverse route
    for the floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A C X Xhat eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A (fun i j => -matTranspose A i j) Pinv hM hLeft hPinv)
      hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov finite-op-norm left-inverse route
    for enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A C X Xhat Rhat' Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A (fun i j => -matTranspose A i j) Pinv hM hLeft hPinv)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov finite-op-norm
    left-inverse route for enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    (Pinv PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    {M : Real} (hM : 0 < M)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hLeft :
      Pinv * sylvesterVecCoeff n n A (fun i j => -matTranspose A i j) = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A C X Xhat Rhat' Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_left_inverse_finiteOpNorm2Le
        n A (fun i j => -matTranspose A i j) Pinv hM hLeft hPinv)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov floating-point endpoint from a positive
    Gram-eigenvalue lower bound for the `(A,-A^T)` vec coefficient. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A (fun i j => -matTranspose A i j) hlam hEig)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov Gram-eigenvalue route for the
    floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A C X Xhat eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A (fun i j => -matTranspose A i j) hlam hEig)
      hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov Gram-eigenvalue route for
    enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A C X Xhat Rhat' Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A (fun i j => -matTranspose A i j) hlam hEig)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov Gram-eigenvalue route for
    enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {lam : Real} (hlam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j))) p)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A C X Xhat Rhat' Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_gram_eigenvalues
        n A (fun i j => -matTranspose A i j) hlam hEig)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov floating-point endpoint from a positive
    sigma-min lower bound for the `(A,-A^T)` vec coefficient. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A (fun i j => -matTranspose A i j) hsigma hCoeff)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov sigma-min route for the
    floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A C X Xhat eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A (fun i j => -matTranspose A i j) hsigma hCoeff)
      hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov sigma-min route for enlarged
    floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A C X Xhat Rhat' Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A (fun i j => -matTranspose A i j) hsigma hCoeff)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov sigma-min route for
    enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real} (hsigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2
          (Matrix.mulVec
            (sylvesterVecCoeff n n A (fun i j => -matTranspose A i j)) x))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A C X Xhat Rhat' Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin
        n A (fun i j => -matTranspose A i j) hsigma hCoeff)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the Lyapunov determinant floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap Lyapunov determinant floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone Lyapunov determinant floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap Lyapunov determinant floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete-left-inverse Lyapunov floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete-left-inverse Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete-left-inverse Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete-left-inverse Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_left_inverse_finiteOpNorm2Le_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the finite-Gram Lyapunov floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap finite-Gram Lyapunov floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone finite-Gram Lyapunov floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap finite-Gram Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_gram_eigenvalues_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the concrete sigma-min Lyapunov floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap concrete sigma-min Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone concrete sigma-min Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap concrete sigma-min Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_vecCoeff_sigmaMin_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov floating-point endpoint from a
    `SepLowerBound(A,-A^T)` source certificate. -/
theorem lyapunov_practical_error_bound_fl_of_sepLowerBound
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
        (fun i j => -matTranspose A i j) sigma hSep)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov `SepLowerBound(A,-A^T)` route for
    the floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_sepLowerBound_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A C X Xhat eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
        (fun i j => -matTranspose A i j) sigma hSep)
      hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov `SepLowerBound(A,-A^T)` route for
    enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_sepLowerBound_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A C X Xhat Rhat' Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
        (fun i j => -matTranspose A i j) sigma hSep)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov `SepLowerBound(A,-A^T)`
    route for enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_sepLowerBound_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A C X Xhat Rhat' Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A
        (fun i j => -matTranspose A i j) sigma hSep)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov floating-point endpoint from a positive
    lower bound on the exact `sylvesterSepInf` for `(A,-A^T)`. -/
theorem lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero fp n
      A C X Xhat
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov exact-infimum route for the
    floating-point computed residual. -/
theorem lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_scalar fp n
      A C X Xhat eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov exact-infimum route for enlarged
    floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono fp n
      A C X Xhat Rhat' Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov exact-infimum route for
    enlarged floating-point residual estimates. -/
theorem lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_vecCoeff_det_ne_zero_mono_scalar fp n
      A C X Xhat Rhat' Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf n A
        (fun i j => -matTranspose A i j) sigma hsigma hle)
      hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the Lyapunov floating-point practical endpoint
    from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_sepLowerBound :=
  lyapunov_practical_error_bound_fl_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the scalar Lyapunov floating-point practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_sepLowerBound_scalar :=
  lyapunov_practical_error_bound_fl_of_sepLowerBound_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the monotone Lyapunov floating-point practical
    endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_sepLowerBound_mono :=
  lyapunov_practical_error_bound_fl_of_sepLowerBound_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the monotone scalar Lyapunov floating-point
    practical endpoint from a source `SepLowerBound(A,-A^T)` certificate. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_sepLowerBound_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_sepLowerBound_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the Lyapunov floating-point practical endpoint
    from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf :=
  lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the scalar Lyapunov floating-point practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_scalar :=
  lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the monotone Lyapunov floating-point practical
    endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono :=
  lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the monotone scalar Lyapunov floating-point
    practical endpoint from a positive exact `sep(A,-A^T)` lower bound. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_pos_le_sylvesterSepInf_mono_scalar

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), Lyapunov floating-point endpoint from a supplied
    operator sigma-min lower bound. -/
theorem lyapunov_practical_error_bound_fl_of_operator_sigmaMin
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      sigma hsigma hSigmaMin hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar Lyapunov floating-point endpoint from a
    supplied operator sigma-min lower bound. -/
theorem lyapunov_practical_error_bound_fl_of_operator_sigmaMin_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_scalar
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      sigma hsigma hSigmaMin eta hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone Lyapunov floating-point endpoint from a
    supplied operator sigma-min lower bound. -/
theorem lyapunov_practical_error_bound_fl_of_operator_sigmaMin_mono
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Ru' sigma hsigma hSigmaMin PinvAbs' hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar Lyapunov floating-point endpoint
    from a supplied operator sigma-min lower bound. -/
theorem lyapunov_practical_error_bound_fl_of_operator_sigmaMin_mono_scalar
    (fp : FPModel) (n : Nat)
    (A C X Xhat Rhat' Ru' : RMatFn n n) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y))
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_of_operator_sigmaMin_computed_residual_certificate_mono_scalar
      n A C X Xhat
      (flSylvesterResidualRect fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Rhat'
      (flSylvesterResidualBudget fp n n A
        (fun i j => -matTranspose A i j) C Xhat)
      Ru' sigma hsigma hSigmaMin PinvAbs' eta hX
      (isLyapunovComputedResidualBudget_fl fp n A C Xhat hn2 hn1)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), diagonal Lyapunov floating-point endpoint from
    pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_diagonal
    (fp : FPModel) (n : Nat)
    (a : Fin n -> Real) (C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hX : forall i j, lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n (Matrix.diagonal a)
            (fun i j => -matTranspose (Matrix.diagonal a) i j))
          (flSylvesterResidualRect fp n n (Matrix.diagonal a)
            (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat)
          (flSylvesterResidualBudget fp n n (Matrix.diagonal a)
            (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound fp n
      (Matrix.diagonal a) C X Xhat
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n
        a sigma hsigma hgap)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar diagonal Lyapunov floating-point endpoint
    from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_diagonal_scalar
    (fp : FPModel) (n : Nat)
    (a : Fin n -> Real) (C X Xhat : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (eta : Real)
    (hX : forall i j, lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j))
        (flSylvesterResidualRect fp n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat)
        (flSylvesterResidualBudget fp n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound_scalar fp n
      (Matrix.diagonal a) C X Xhat
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n
        a sigma hsigma hgap)
      eta hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone diagonal Lyapunov floating-point endpoint
    from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_diagonal_mono
    (fp : FPModel) (n : Nat)
    (a : Fin n -> Real) (C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat i j| <=
        |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat i j <=
        Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound_mono fp n
      (Matrix.diagonal a) C X Xhat Rhat' Ru'
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n
        a sigma hsigma hgap)
      PinvAbs' hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar diagonal Lyapunov floating-point
    endpoint from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_diagonal_mono_scalar
    (fp : FPModel) (n : Nat)
    (a : Fin n -> Real) (C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n (Matrix.diagonal a) X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat i j| <=
        |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n (Matrix.diagonal a)
          (fun i j => -matTranspose (Matrix.diagonal a) i j) C Xhat i j <=
        Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound_mono_scalar fp n
      (Matrix.diagonal a) C X Xhat Rhat' Ru'
      (SepLowerBound_lyapunov_diagonal_of_entrywise_abs_ge n
        a sigma hsigma hgap)
      PinvAbs' eta hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), supplied spectral-coordinate Lyapunov
    floating-point endpoint from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_spectralDiagonal
    (fp : FPModel) (n : Nat)
    (U A : RMatFn n n) (a : Fin n -> Real) (C X Xhat : RMatFn n n)
    {sigma : Real}
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A
            (fun i j => -matTranspose A i j))
          (flSylvesterResidualRect fp n n A
            (fun i j => -matTranspose A i j) C Xhat)
          (flSylvesterResidualBudget fp n n A
            (fun i j => -matTranspose A i j) C Xhat)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound fp n A C X Xhat
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hX hn2 hn1 hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), scalar supplied spectral-coordinate Lyapunov
    floating-point endpoint from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_spectralDiagonal_scalar
    (fp : FPModel) (n : Nat)
    (U A : RMatFn n n) (a : Fin n -> Real) (C X Xhat : RMatFn n n)
    {sigma : Real}
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
        (sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j))
        (flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat)
        (flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound_scalar fp n A C X Xhat
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      eta hX hn2 hn1 heta hcomponent hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone supplied spectral-coordinate Lyapunov
    floating-point endpoint from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_spectralDiagonal_mono
    (fp : FPModel) (n : Nat)
    (U A : RMatFn n n) (a : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound_mono fp n
      A C X Xhat Rhat' Ru'
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      PinvAbs' hX hn2 hn1 hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Section
    16.4, equation (16.29), monotone scalar supplied spectral-coordinate
    Lyapunov floating-point endpoint from pair-sum gap data. -/
theorem lyapunov_practical_error_bound_fl_of_spectralDiagonal_mono_scalar
    (fp : FPModel) (n : Nat)
    (U A : RMatFn n n) (a : Fin n -> Real)
    (C X Xhat Rhat' Ru' : RMatFn n n)
    {sigma : Real}
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : forall i j, lyapunovOp n A X i j = C i j)
    (hn2 : gammaValid fp (n + 2)) (hn1 : gammaValid fp (n + 1))
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A
          (fun i j => -matTranspose A i j) p q <= PinvAbs' p q)
    (hRhat : forall i j,
      |flSylvesterResidualRect fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j,
      flSylvesterResidualBudget fp n n A
          (fun i j => -matTranspose A i j) C Xhat i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    lyapunov_practical_error_bound_fl_of_sepLowerBound_mono_scalar fp n
      A C X Xhat Rhat' Ru'
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      PinvAbs' eta hX hn2 hn1 hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied operator sigma-min Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_operator_sigmaMin :=
  lyapunov_practical_error_bound_fl_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap supplied operator sigma-min Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_operator_sigmaMin_scalar :=
  lyapunov_practical_error_bound_fl_of_operator_sigmaMin_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone supplied operator sigma-min Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_operator_sigmaMin_mono :=
  lyapunov_practical_error_bound_fl_of_operator_sigmaMin_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap supplied operator sigma-min Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_operator_sigmaMin_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_operator_sigmaMin_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal Lyapunov floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_diagonal :=
  lyapunov_practical_error_bound_fl_of_diagonal

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap diagonal Lyapunov floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_diagonal_scalar :=
  lyapunov_practical_error_bound_fl_of_diagonal_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone diagonal Lyapunov floating-point practical
    endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_diagonal_mono :=
  lyapunov_practical_error_bound_fl_of_diagonal_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap diagonal Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_diagonal_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_diagonal_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied spectral-coordinate Lyapunov floating-point
    practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_spectralDiagonal :=
  lyapunov_practical_error_bound_fl_of_spectralDiagonal

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar-cap supplied spectral-coordinate Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_spectralDiagonal_scalar :=
  lyapunov_practical_error_bound_fl_of_spectralDiagonal_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone supplied spectral-coordinate Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_spectralDiagonal_mono :=
  lyapunov_practical_error_bound_fl_of_spectralDiagonal_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar-cap supplied spectral-coordinate Lyapunov
    floating-point practical endpoint. -/
alias H16_eq16_29_lyapunov_practical_error_bound_fl_of_spectralDiagonal_mono_scalar :=
  lyapunov_practical_error_bound_fl_of_spectralDiagonal_mono_scalar

end NumStability
