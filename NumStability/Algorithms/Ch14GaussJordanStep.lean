-- Algorithms/Ch14GaussJordanStep.lean
--
-- Higham, "Accuracy and Stability of Numerical Algorithms", 2nd ed.,
-- Chapter 14 ("Matrix Inversion"), §14.4 ("Gauss–Jordan Elimination"),
-- equations (14.25a)–(14.26), p. 274.
--
-- PURPOSE.  The Codex-owned `Algorithms/GaussJordan.lean` exposes the GJE
-- second-stage error recurrences (14.25a)/(14.26) as ABSTRACT interfaces:
-- `gje_stage2_matrix_recurrence` and `gje_stage2_rhs_recurrence` each take the
-- per-step rounded bound
--     |Û_{k+1} − N̂ₖ Ûₖ| ≤ γ₃ |N̂ₖ| |Ûₖ|            (14.25b)
-- as a HYPOTHESIS (`hComp`) rather than deriving it from the floating-point
-- model.  This module DERIVES that per-step γ₃ bound from the standard model
-- `fl(a op b) = (a op b)(1 + δ)`, |δ| ≤ u, for the CONCRETE second-stage row
-- operation
--     û_{ij}^{(k+1)} = fl( û_{ij}^{(k)} − fl( m̂ᵢ · û_{kj}^{(k)} ) ),
--     m̂ᵢ = fl( û_{ik}^{(k)} / û_{kk}^{(k)} ),
-- i.e. one division to form the multiplier, one multiply, one subtract — three
-- rounded operations, hence Higham's γ₃.  The stage matrix N̂ₖ stores the EXACT
-- ratio (N̂ₖ)_{ik} = −û_{ik}/û_{kk}, so the division rounding is charged to the
-- per-step error Δₖ, exactly as in the printed derivation.
--
-- Having derived `hComp`, we discharge the two abstract recurrence interfaces
-- UNCONDITIONALLY (no assumed per-step bound), and expose the exact additive
-- backward equation (14.25a) û_{k+1} = N̂ₖ û_k + Δₖ for the concrete step.
--
-- This is an import-only companion to `GaussJordan.lean`: it does not modify
-- Codex's file.  What is NOT closed here (and is flagged in the residual of the
-- task report) is the multi-stage cumulative accumulation (14.27)–(14.30) that
-- aggregates n−1 per-step bounds into the printed overall 8nu/2nu endpoints
-- (14.31)–(14.32); that telescoping is orthogonal to the per-step derivation.

import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.GaussJordan

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

-- ══════════════════════════════════════════════════════════════════════
-- §1  Scalar core: the fused axpy step accumulates a γ₃ relative error
-- ══════════════════════════════════════════════════════════════════════

/-- **Three-operation product bound** (Higham §3.1, Lemma 3.1 at n = 3).

    A product of three relative-error factors `(1+δ₁)(1+δ₂)(1+δ₃)`, each
    `|δᵢ| ≤ u`, equals `1 + θ` with `|θ| ≤ γ₃`.  This is the exact algebraic
    fact underlying the γ₃ constant in (14.25b): the GJE row operation is a
    divide/multiply/subtract chain of three rounded operations. -/
theorem ch14ext_prod_three (fp : FPModel) (h3 : gammaValid fp 3)
    (δ₁ δ₂ δ₃ : ℝ) (h₁ : |δ₁| ≤ fp.u) (h₂ : |δ₂| ≤ fp.u) (h₃ : |δ₃| ≤ fp.u) :
    ∃ θ : ℝ, |θ| ≤ gamma fp 3 ∧ (1 + δ₁) * (1 + δ₂) * (1 + δ₃) = 1 + θ := by
  let δ : Fin 3 → ℝ := fun i => if i = 0 then δ₁ else if i = 1 then δ₂ else δ₃
  have hδ : ∀ i : Fin 3, |δ i| ≤ fp.u := by
    intro i; fin_cases i <;> simp [δ, h₁, h₂, h₃]
  obtain ⟨θ, hθ, hprod⟩ := prod_error_bound fp 3 δ hδ h3
  exact ⟨θ, hθ, by simpa [δ, Fin.prod_univ_three] using hprod⟩

/-- **Per-entry GJE second-stage step error** (Higham (14.25b), scalar core).

    Model the single fused row-combine entry
        s = fl( a − fl( m̂ · r ) ),   m̂ = μ · (1 + δ₁),  |δ₁| ≤ u,
    where `μ` is the EXACT multiplier stored in N̂ₖ, `m̂` is the computed
    multiplier (one division), the inner `fl` is one multiply, the outer `fl`
    is one subtract.  Then the computed `s` differs from the exact combine
    `a − μ·r` by at most `γ₃ (|a| + |μ|·|r|)`.

    This is exactly the (i,j) entry of (14.25b): `a = û_{ij}`, `r = û_{kj}`,
    `μ = û_{ik}/û_{kk}`, and `|a| + |μ|·|r| = (|N̂ₖ| |Ûₖ|)_{ij}`. -/
theorem ch14ext_fused_axpy_error (fp : FPModel) (a r μ mhat δ₁ : ℝ)
    (h3 : gammaValid fp 3) (hδ₁ : |δ₁| ≤ fp.u) (hmhat : mhat = μ * (1 + δ₁)) :
    |fp.fl_sub a (fp.fl_mul mhat r) - (a - μ * r)| ≤
      gamma fp 3 * (|a| + |μ| * |r|) := by
  obtain ⟨δ₂, hδ₂, hmul⟩ := fp.model_mul mhat r
  obtain ⟨δ₃, hδ₃, hsub⟩ := fp.model_sub a (fp.fl_mul mhat r)
  obtain ⟨θ, hθ, hprod⟩ := ch14ext_prod_three fp h3 δ₁ δ₂ δ₃ hδ₁ hδ₂ hδ₃
  have hu3 : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) h3
  -- The computed result minus the exact combine equals a·δ₃ − μ·r·θ.
  have hθeq : θ = (1 + δ₁) * (1 + δ₂) * (1 + δ₃) - 1 := by linarith [hprod]
  have key : fp.fl_sub a (fp.fl_mul mhat r) - (a - μ * r) = a * δ₃ - μ * r * θ := by
    rw [hsub, hmul, hmhat, hθeq]; ring
  rw [key]
  have htri : |a * δ₃ - μ * r * θ| ≤ |a * δ₃| + |μ * r * θ| := by
    calc |a * δ₃ - μ * r * θ| = |a * δ₃ + -(μ * r * θ)| := by rw [sub_eq_add_neg]
      _ ≤ |a * δ₃| + |-(μ * r * θ)| := abs_add_le _ _
      _ = |a * δ₃| + |μ * r * θ| := by rw [abs_neg]
  have hbound : |a * δ₃| + |μ * r * θ| ≤ gamma fp 3 * (|a| + |μ| * |r|) := by
    have e1 : |a * δ₃| = |a| * |δ₃| := abs_mul _ _
    have e2 : |μ * r * θ| = |μ| * |r| * |θ| := by rw [abs_mul, abs_mul]
    rw [e1, e2]
    have b1 : |a| * |δ₃| ≤ |a| * gamma fp 3 :=
      mul_le_mul_of_nonneg_left (le_trans hδ₃ hu3) (abs_nonneg a)
    have b2 : |μ| * |r| * |θ| ≤ |μ| * |r| * gamma fp 3 :=
      mul_le_mul_of_nonneg_left hθ (mul_nonneg (abs_nonneg μ) (abs_nonneg r))
    nlinarith [b1, b2]
  linarith [htri, hbound]

-- ══════════════════════════════════════════════════════════════════════
-- §2  The concrete GJE second-stage matrix step (14.25a) and its γ₃ bound
-- ══════════════════════════════════════════════════════════════════════

/-- Exact multiplier vector `(n̂ₖ)` of the GJE second stage, with the pivot-row
    entry guarded to `0` (Higham: `eᵀᵢ nₖ = 0` for `i ≥ k`; the pivot row `k`
    is never eliminated).  For `i ≠ k` the value is the exact ratio
    `ûᵢₖ / ûₖₖ`, which is the quantity stored in `N̂ₖ` (the division rounding is
    charged to the per-step error, not to `N̂ₖ`). -/
noncomputable def ch14ext_gjeMultVec (n : ℕ) (U : Fin n → Fin n → ℝ) (k : Fin n) :
    Fin n → ℝ :=
  fun i => if i = k then 0 else U i k / U k k

/-- The GJE second-stage matrix `N̂ₖ = I − n̂ₖ eₖᵀ` (Higham (14.25), p. 274),
    with exact-ratio off-diagonal column-`k` entries.  On the (upper triangular)
    stage-1 output `U`, the entries below the pivot vanish, so its support is
    exactly `{i < k}`, matching the printed `nₖ = [−u₁ₖ/uₖₖ, …, −u_{k−1,k}/uₖₖ]ᵀ`. -/
noncomputable def ch14ext_gjeStageMatrix (n : ℕ) (U : Fin n → Fin n → ℝ) (k : Fin n) :
    Fin n → Fin n → ℝ :=
  fun i l => (if i = l then (1:ℝ) else 0) -
    (if l = k then ch14ext_gjeMultVec n U k i else 0)

/-- The CONCRETE computed next matrix `Û_{k+1}` of the GJE second stage.
    Row `i = k` (the pivot row) is untouched; every other row `i` is updated by
    the fused axpy `û_{ij} ← fl( û_{ij} − fl( fl(û_{ik}/û_{kk}) · û_{kj} ) )`,
    i.e. one division, one multiply, one subtract. -/
noncomputable def ch14ext_gjeStepMatrix (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) : Fin n → Fin n → ℝ :=
  fun i j => if i = k then U i j
    else fp.fl_sub (U i j) (fp.fl_mul (fp.fl_div (U i k) (U k k)) (U k j))

/-- The exact matrix product `(N̂ₖ Ûₖ)_{ij} = û_{ij} − (n̂ₖ)ᵢ û_{kj}`.
    Holds uniformly in `i` (including the pivot row, where `(n̂ₖ)ₖ = 0`). -/
theorem ch14ext_gjeStageMatrix_mulVec_row (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) (i j : Fin n) :
    ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * U l j
      = U i j - ch14ext_gjeMultVec n U k i * U k j := by
  unfold ch14ext_gjeStageMatrix
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- **Higham (14.25a)–(14.25b), per-step γ₃ bound — DERIVED from the FP model.**

    For the concrete GJE second-stage matrix step, each entry of the computed
    `Û_{k+1}` differs from the exact product `N̂ₖ Ûₖ` by at most `γ₃ (|N̂ₖ||Ûₖ|)`.
    This DISCHARGES the `hComp` hypothesis of `gje_stage2_matrix_recurrence`
    from `fl(a op b) = (a op b)(1+δ)`, |δ| ≤ u — it is not assumed.

    The pivot must be nonzero (`hpiv`), which is guaranteed when GJE succeeds
    (Higham: all leading principal submatrices nonsingular, Theorem 9.1). -/
theorem ch14ext_gjeStepMatrix_hComp (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    ∀ i j : Fin n,
      |ch14ext_gjeStepMatrix fp n U k i j -
        ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * U l j| ≤
      gamma fp 3 * ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |U l j| := by
  intro i j
  rw [ch14ext_gjeStageMatrix_mulVec_row]
  by_cases hik : i = k
  · -- pivot row: the step leaves the row unchanged, so the residual is 0
    have hstep : ch14ext_gjeStepMatrix fp n U k i j = U i j := by
      simp [ch14ext_gjeStepMatrix, hik]
    have hmult : ch14ext_gjeMultVec n U k i = 0 := by
      simp [ch14ext_gjeMultVec, hik]
    rw [hstep, hmult]
    have hz : U i j - (U i j - (0:ℝ) * U k j) = 0 := by ring
    rw [hz, abs_zero]
    exact mul_nonneg (gamma_nonneg fp h3)
      (Finset.sum_nonneg (fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  · -- eliminated row: apply the scalar fused-axpy bound
    have hstep : ch14ext_gjeStepMatrix fp n U k i j
        = fp.fl_sub (U i j) (fp.fl_mul (fp.fl_div (U i k) (U k k)) (U k j)) := by
      simp [ch14ext_gjeStepMatrix, hik]
    have hmult : ch14ext_gjeMultVec n U k i = U i k / U k k := by
      simp [ch14ext_gjeMultVec, hik]
    rw [hstep, hmult]
    obtain ⟨δ₁, hδ₁, hdiv⟩ := fp.model_div (U i k) (U k k) hpiv
    have hcore := ch14ext_fused_axpy_error fp (U i j) (U k j) (U i k / U k k)
      (fp.fl_div (U i k) (U k k)) δ₁ h3 hδ₁ (by rw [hdiv])
    refine le_trans hcore ?_
    apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp h3)
    -- |û_{ij}| + |μ| |û_{kj}| ≤ ∑_l |(N̂ₖ)_{il}| |û_{lj}|  (drop the ≥0 tail)
    have hNii : ch14ext_gjeStageMatrix n U k i i = 1 := by
      simp [ch14ext_gjeStageMatrix, hik]
    have hNik : ch14ext_gjeStageMatrix n U k i k = -(U i k / U k k) := by
      simp [ch14ext_gjeStageMatrix, ch14ext_gjeMultVec, hik]
    have hpair : ∑ l ∈ ({i, k} : Finset (Fin n)),
        |ch14ext_gjeStageMatrix n U k i l| * |U l j|
        = |ch14ext_gjeStageMatrix n U k i i| * |U i j|
          + |ch14ext_gjeStageMatrix n U k i k| * |U k j| :=
      Finset.sum_pair hik
    have hlow : |ch14ext_gjeStageMatrix n U k i i| * |U i j|
          + |ch14ext_gjeStageMatrix n U k i k| * |U k j|
        ≤ ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |U l j| := by
      rw [← hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [hNii, hNik] at hlow
    simp only [abs_one, one_mul, abs_neg] at hlow
    linarith [hlow]

/-- **Discharge of `gje_stage2_matrix_recurrence` (14.25a) — UNCONDITIONAL.**

    Feeds the derived per-step bound `ch14ext_gjeStepMatrix_hComp` into Codex's
    abstract recurrence interface.  No per-step γ₃ bound is assumed: the only
    hypotheses are pivot nonsingularity and `γ₃` validity. -/
theorem ch14ext_gje_stage2_matrix_recurrence_derived (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    ∀ i j : Fin n,
      |ch14ext_gjeStepMatrix fp n U k i j -
        ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * U l j| ≤
      gamma fp 3 * ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |U l j| :=
  gje_stage2_matrix_recurrence n fp U (ch14ext_gjeStageMatrix n U k)
    (ch14ext_gjeStepMatrix fp n U k) h3 (ch14ext_gjeStepMatrix_hComp fp n U k hpiv h3)

/-- **Higham (14.25a), exact per-step backward equation — DERIVED.**

    `Û_{k+1} = N̂ₖ Ûₖ + Δₖ` with the DERIVED componentwise bound
    `|Δₖ| ≤ γ₃ |N̂ₖ| |Ûₖ|` (14.25b).  `Δₖ` is exhibited concretely (the residual
    of the computed step against the exact product); the content is the bound,
    which comes from `ch14ext_gjeStepMatrix_hComp`. -/
theorem ch14ext_gje_stage2_matrix_backward_eq (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    ∃ Δ : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        ch14ext_gjeStepMatrix fp n U k i j
          = (∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * U l j) + Δ i j) ∧
      (∀ i j : Fin n, |Δ i j| ≤
        gamma fp 3 * ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |U l j|) := by
  refine ⟨fun i j => ch14ext_gjeStepMatrix fp n U k i j
    - ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * U l j, fun i j => by ring, ?_⟩
  intro i j
  simpa using ch14ext_gjeStepMatrix_hComp fp n U k hpiv h3 i j

-- ══════════════════════════════════════════════════════════════════════
-- §3  The concrete GJE second-stage RHS step (14.26) and its γ₃ bound
-- ══════════════════════════════════════════════════════════════════════

/-- Apply the stage matrix `N̂ₖ` to a general vector `v`:
    `(N̂ₖ v)_i = vᵢ − (n̂ₖ)ᵢ vₖ`.  (The (14.25a) matrix identity, per column.) -/
theorem ch14ext_gjeStageMatrix_apply (n : ℕ) (U : Fin n → Fin n → ℝ)
    (k : Fin n) (v : Fin n → ℝ) (i : Fin n) :
    ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * v l
      = v i - ch14ext_gjeMultVec n U k i * v k := by
  unfold ch14ext_gjeStageMatrix
  simp only [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- The CONCRETE computed RHS `x̂_{k+1}` of the GJE second stage (Higham
    (14.26)).  Pivot entry `k` is untouched; entry `i ≠ k` is the fused axpy
    `x̂ᵢ ← fl( x̂ᵢ − fl( fl(û_{ik}/û_{kk}) · x̂ₖ ) )` (same multiplier as `N̂ₖ`). -/
noncomputable def ch14ext_gjeStepVec (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i = k then x i
    else fp.fl_sub (x i) (fp.fl_mul (fp.fl_div (U i k) (U k k)) (x k))

/-- **Higham (14.26), per-step γ₃ bound for the RHS — DERIVED from the FP model.**

    `|x̂_{k+1} − N̂ₖ x̂ₖ| ≤ γ₃ |N̂ₖ| |x̂ₖ|`, discharging the `hComp` hypothesis of
    `gje_stage2_rhs_recurrence`. -/
theorem ch14ext_gjeStepVec_hComp (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (x : Fin n → ℝ)
    (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    ∀ i : Fin n,
      |ch14ext_gjeStepVec fp n U k x i -
        ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * x l| ≤
      gamma fp 3 * ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |x l| := by
  intro i
  rw [ch14ext_gjeStageMatrix_apply]
  by_cases hik : i = k
  · have hstep : ch14ext_gjeStepVec fp n U k x i = x i := by
      simp [ch14ext_gjeStepVec, hik]
    have hmult : ch14ext_gjeMultVec n U k i = 0 := by
      simp [ch14ext_gjeMultVec, hik]
    rw [hstep, hmult]
    have hz : x i - (x i - (0:ℝ) * x k) = 0 := by ring
    rw [hz, abs_zero]
    exact mul_nonneg (gamma_nonneg fp h3)
      (Finset.sum_nonneg (fun l _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  · have hstep : ch14ext_gjeStepVec fp n U k x i
        = fp.fl_sub (x i) (fp.fl_mul (fp.fl_div (U i k) (U k k)) (x k)) := by
      simp [ch14ext_gjeStepVec, hik]
    have hmult : ch14ext_gjeMultVec n U k i = U i k / U k k := by
      simp [ch14ext_gjeMultVec, hik]
    rw [hstep, hmult]
    obtain ⟨δ₁, hδ₁, hdiv⟩ := fp.model_div (U i k) (U k k) hpiv
    have hcore := ch14ext_fused_axpy_error fp (x i) (x k) (U i k / U k k)
      (fp.fl_div (U i k) (U k k)) δ₁ h3 hδ₁ (by rw [hdiv])
    refine le_trans hcore ?_
    apply mul_le_mul_of_nonneg_left _ (gamma_nonneg fp h3)
    have hNii : ch14ext_gjeStageMatrix n U k i i = 1 := by
      simp [ch14ext_gjeStageMatrix, hik]
    have hNik : ch14ext_gjeStageMatrix n U k i k = -(U i k / U k k) := by
      simp [ch14ext_gjeStageMatrix, ch14ext_gjeMultVec, hik]
    have hpair : ∑ l ∈ ({i, k} : Finset (Fin n)),
        |ch14ext_gjeStageMatrix n U k i l| * |x l|
        = |ch14ext_gjeStageMatrix n U k i i| * |x i|
          + |ch14ext_gjeStageMatrix n U k i k| * |x k| :=
      Finset.sum_pair hik
    have hlow : |ch14ext_gjeStageMatrix n U k i i| * |x i|
          + |ch14ext_gjeStageMatrix n U k i k| * |x k|
        ≤ ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |x l| := by
      rw [← hpair]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun l _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [hNii, hNik] at hlow
    simp only [abs_one, one_mul, abs_neg] at hlow
    linarith [hlow]

/-- **Discharge of `gje_stage2_rhs_recurrence` (14.26) — UNCONDITIONAL.** -/
theorem ch14ext_gje_stage2_rhs_recurrence_derived (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (x : Fin n → ℝ)
    (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    ∀ i : Fin n,
      |ch14ext_gjeStepVec fp n U k x i -
        ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * x l| ≤
      gamma fp 3 * ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |x l| :=
  gje_stage2_rhs_recurrence n fp x (ch14ext_gjeStageMatrix n U k)
    (ch14ext_gjeStepVec fp n U k x) h3 (ch14ext_gjeStepVec_hComp fp n U k x hpiv h3)

/-- **Higham (14.26), exact per-step backward equation for the RHS — DERIVED.**
    `x̂_{k+1} = N̂ₖ x̂ₖ + fₖ` with `|fₖ| ≤ γ₃ |N̂ₖ| |x̂ₖ|`. -/
theorem ch14ext_gje_stage2_rhs_backward_eq (fp : FPModel) (n : ℕ)
    (U : Fin n → Fin n → ℝ) (k : Fin n) (x : Fin n → ℝ)
    (hpiv : U k k ≠ 0) (h3 : gammaValid fp 3) :
    ∃ f : Fin n → ℝ,
      (∀ i : Fin n,
        ch14ext_gjeStepVec fp n U k x i
          = (∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * x l) + f i) ∧
      (∀ i : Fin n, |f i| ≤
        gamma fp 3 * ∑ l : Fin n, |ch14ext_gjeStageMatrix n U k i l| * |x l|) := by
  refine ⟨fun i => ch14ext_gjeStepVec fp n U k x i
    - ∑ l : Fin n, ch14ext_gjeStageMatrix n U k i l * x l, fun i => by ring, ?_⟩
  intro i
  simpa using ch14ext_gjeStepVec_hComp fp n U k x hpiv h3 i

end NumStability.Ch14Ext
