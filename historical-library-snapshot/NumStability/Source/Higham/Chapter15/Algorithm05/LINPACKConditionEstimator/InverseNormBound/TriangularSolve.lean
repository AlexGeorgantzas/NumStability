import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.CondEstimation
import NumStability.Algorithms.NormEstimation.OneNorm.LINPACK.Basic
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.Algebra.CondEstimators
import NumStability.Algorithms.NormEstimation.TwoNorm.Dixon.PowerBounds.CondEstimators
import NumStability.Analysis.ConditionEstimatorLowerBound
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Algorithm05.LINPACKConditionEstimator.Basic
import NumStability.Source.Higham.Chapter15.Equation07.DixonBound.Basic

/-!
# TriangularSolve

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.Ch15CondEstimators`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# Ch15CondEstimators (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch15CondEstimators`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

open scoped BigOperators

open scoped Matrix

namespace Ch15

/-- `linpackYSteps` never changes an already-fixed coordinate `j` with `k ≤ j`. -/
private lemma linpackYSteps_stable {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (y : Fin n → ℝ) (j : Fin n),
      k ≤ j.val → linpackYSteps U sgn k hk y j = y j := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro hk y j hkj
    unfold linpackYSteps
    simp only
    have hkj' : k ≤ j.val := by omega
    rw [ih (Nat.le_of_succ_le hk) _ j hkj']
    rw [Function.update_of_ne]
    intro heq
    have : j.val = k := congr_arg Fin.val heq
    omega

/-- **Upper-triangular row split.**  For an upper triangular `U` and a diagonal
    index `jk` with `jk.val = k`, the `jk`-th component of `U y` splits into the
    diagonal term and the partial product over columns `> k`:
      `(U y)_{jk} = U_{jk jk} · y_{jk} + (linpackPartial U k y)_{jk}`. -/
private lemma matMulVec_upperTri_split {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsUpperTriangular U) (k : ℕ) (jk : Fin n) (hjk : jk.val = k)
    (y : Fin n → ℝ) :
    matMulVec n U y jk = U jk jk * y jk + linpackPartial U k y jk := by
  unfold matMulVec linpackPartial
  -- Partition the sum over `Fin n` by comparison of `m.val` with `k`.
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun m : Fin n => m.val < k)]
  have hlow : (∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val < k),
                U jk m * y m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [Finset.mem_filter] at hm
    have : U jk m = 0 := hU jk m (by rw [hjk]; exact hm.2)
    rw [this, zero_mul]
  rw [hlow, zero_add]
  -- The complement `¬ m < k` splits into `m = jk` and `m > k`.
  rw [← Finset.sum_filter_add_sum_filter_not
        (Finset.univ.filter (fun m : Fin n => ¬ m.val < k))
        (fun m : Fin n => m.val = k)]
  have hdiag : (∑ m ∈ (Finset.univ.filter (fun m : Fin n => ¬ m.val < k)).filter
                  (fun m : Fin n => m.val = k), U jk m * y m)
                = U jk jk * y jk := by
    have hset : (Finset.univ.filter (fun m : Fin n => ¬ m.val < k)).filter
                  (fun m : Fin n => m.val = k) = {jk} := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨_, hmk⟩; exact Fin.ext (by rw [hmk, hjk])
      · intro hm; subst hm; exact ⟨by omega, hjk⟩
    rw [hset, Finset.sum_singleton]
  rw [hdiag]
  congr 1
  -- The remaining set `{¬ m < k} ∩ {m ≠ k}` is exactly `{k < m}`.
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext m
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  omega

/-- Processing column `k` fixes coordinate `k` of `y` to `(s − pₖ)/Uₖₖ` and this
    value is preserved to the end of the recursion. -/
private lemma linpackYSteps_value_at {n : ℕ} {U : Fin n → Fin n → ℝ}
    (sgn : Fin n → (Fin n → ℝ) → ℝ)
    (k : ℕ) (hk : k + 1 ≤ n) (y : Fin n → ℝ) :
    linpackYSteps U sgn (k + 1) hk y ⟨k, hk⟩ =
      (sgn ⟨k, hk⟩ (linpackPartial U k y) - linpackPartial U k y ⟨k, hk⟩)
        / U ⟨k, hk⟩ ⟨k, hk⟩ := by
  unfold linpackYSteps
  simp only
  rw [linpackYSteps_stable U sgn k (Nat.le_of_succ_le hk) _ ⟨k, hk⟩ (le_refl k)]
  rw [Function.update_self]

/-- **Correctness of Algorithm 15.5's solve step (any sign rule).**

    If `U` is upper triangular with nonzero diagonal and the sign rule `sgn`
    always returns `±1`, then after processing columns `k−1,…,0` (the call
    `linpackYSteps … k`), every already-solved coordinate `j` (with `j.val < k`)
    of the residual `U y` equals `±1`:
      `(U · (linpackYSteps U sgn k hk y))_j ∈ {1, −1}`  for `j.val < k`.

    This is the exact-arithmetic specification of the loop: `U y = d`, `dⱼ = ±1`.
    It holds for *whatever* sign the look-ahead heuristic picks — the guarantee is
    independent of the (unprovable) quality of the heuristic. -/
private lemma linpackYSteps_solves {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsUpperTriangular U) (hdiag : ∀ i : Fin n, U i i ≠ 0)
    {sgn : Fin n → (Fin n → ℝ) → ℝ}
    (hsgn : ∀ (jk : Fin n) (p : Fin n → ℝ), sgn jk p = 1 ∨ sgn jk p = -1) :
    ∀ (k : ℕ) (hk : k ≤ n) (y : Fin n → ℝ) (j : Fin n), j.val < k →
      matMulVec n U (linpackYSteps U sgn k hk y) j = 1 ∨
      matMulVec n U (linpackYSteps U sgn k hk y) j = -1 := by
  intro k
  induction k with
  | zero => intro _ _ j hj; exact absurd hj (by omega)
  | succ k ih =>
    intro hk y j hj
    -- Peel one recursion step: process column `k`, then recurse on `k`.
    have hstep :
        linpackYSteps U sgn (k + 1) hk y =
          linpackYSteps U sgn k (Nat.le_of_succ_le hk)
            (Function.update y ⟨k, hk⟩
              ((sgn ⟨k, hk⟩ (linpackPartial U k y)
                  - linpackPartial U k y ⟨k, hk⟩) / U ⟨k, hk⟩ ⟨k, hk⟩)) :=
      rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | hjk
    · -- `j.val < k`: reduce to the inductive hypothesis on the recursive call.
      rw [hstep]
      exact ih (Nat.le_of_succ_le hk) _ j hjk
    · -- `j.val = k`: coordinate `k` is the one just solved; residual is the sign.
      have hjeq : j = ⟨k, hk⟩ := Fin.ext hjk
      subst hjeq
      set jk : Fin n := ⟨k, hk⟩ with hjkdef
      set p : Fin n → ℝ := linpackPartial U k y with hpdef
      set s : ℝ := sgn jk p with hsdef
      set yout := linpackYSteps U sgn (k + 1) hk y with houtdef
      -- Split the `jk`-th residual using upper-triangularity.
      rw [matMulVec_upperTri_split hU k jk (by rw [hjkdef]) yout]
      -- Value at the diagonal coordinate.
      have hval : yout jk = (s - p jk) / U jk jk := by
        rw [houtdef, hsdef, hpdef]; exact linpackYSteps_value_at sgn k hk y
      -- The partial product over columns `> k` is unchanged (those `y`s frozen).
      have hpart : linpackPartial U k yout jk = p jk := by
        rw [hpdef]
        unfold linpackPartial
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_filter] at hm
        have hmk : k < m.val := hm.2
        -- `yout m = y m` for `m.val > k` (m ≥ k+1), by stability + update.
        have hym : yout m = y m := by
          rw [hstep]
          rw [linpackYSteps_stable U sgn k (Nat.le_of_succ_le hk) _ m (by omega)]
          rw [Function.update_of_ne]
          intro heq; have := congr_arg Fin.val heq; simp only at this; omega
        rw [hym]
      rw [hval, hpart]
      -- `U jk jk * ((s − p jk)/U jk jk) + p jk = s ∈ {±1}`.
      have hne : U jk jk ≠ 0 := hdiag jk
      have hgoal : U jk jk * ((s - p jk) / U jk jk) + p jk = s := by
        rw [mul_div_cancel₀ _ hne]; ring
      rw [hgoal, hsdef]
      exact hsgn jk p

/-- **Algorithm 15.5 chooses `dⱼ = ±1`** (Higham §15.5, p. 296): for an upper
    triangular `U` with nonzero diagonal and any `±1`-valued sign rule, the
    residual `d = U y` produced by the algorithm is a `±1` vector. -/
theorem linpackD_isPlusMinusOne {n : ℕ} {U : Fin n → Fin n → ℝ}
    (hU : IsUpperTriangular U) (hdiag : ∀ i : Fin n, U i i ≠ 0)
    {sgn : Fin n → (Fin n → ℝ) → ℝ}
    (hsgn : ∀ (jk : Fin n) (p : Fin n → ℝ), sgn jk p = 1 ∨ sgn jk p = -1) :
    IsPlusMinusOne (linpackD U sgn) := by
  intro j
  have hj : j.val < n := j.isLt
  exact linpackYSteps_solves hU hdiag hsgn n (le_refl n) (fun _ => 0) j hj

/-- **Algorithm 15.5 produces a lower bound on `‖U⁻¹‖∞`** (Higham §15.5,
    Algorithm 15.5, step 3, p. 296-297).

    Instantiating the general lower bound at the vector `y` actually returned by
    Algorithm 15.5 with the LINPACK weighted look-ahead sign rule and weights `w`.
    Because the algorithm guarantees `dⱼ = ±1`, we have `‖d‖∞ = 1`, so the estimate
    collapses to `‖y‖∞`, and
        `‖y‖∞ ≤ ‖U⁻¹‖∞`.
    The estimate never overestimates the true `∞`-norm of the inverse. -/
theorem linpackY_infNorm_le_infNorm_inv {n : ℕ} (hn : 0 < n)
    {U Uinv : Fin n → Fin n → ℝ}
    (hU : IsUpperTriangular U) (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hinv : IsLeftInverse n U Uinv) (w : Fin n → ℝ) :
    infNormVec (linpackY U (linpackSign U w)) ≤ infNorm Uinv := by
  set sgn := linpackSign U w with hsgndef
  have hsgn : ∀ (jk : Fin n) (p : Fin n → ℝ), sgn jk p = 1 ∨ sgn jk p = -1 :=
    fun jk p => linpackSign_plusMinusOne U w jk p
  -- `d = U y` is a ±1 vector, hence `‖d‖∞ = 1`.
  have hdpm : IsPlusMinusOne (linpackD U sgn) :=
    linpackD_isPlusMinusOne hU hdiag hsgn
  have hdnorm : infNormVec (linpackD U sgn) = 1 :=
    infNormVec_eq_one_of_plusMinusOne hn hdpm
  have hsolve : matMulVec n U (linpackY U sgn) = linpackD U sgn := rfl
  have hdne : infNormVec (linpackD U sgn) ≠ 0 := by rw [hdnorm]; norm_num
  have hbound :=
    linpack_estimate_le_infNorm_inv hn hinv hsolve hdne
  rwa [hdnorm, div_one] at hbound

/-- **Algorithm 15.5 lower bound, nonsingular form (headline).**

    Higham §15.5, Algorithm 15.5 (p. 296-297).  For a *nonsingular upper
    triangular* `U` — witnessed by a left inverse `Uinv` — and any nonnegative
    weights `w`, the vector `y` returned by Algorithm 15.5 (LINPACK look-ahead)
    satisfies the guaranteed lower bound
        `‖y‖∞ ≤ ‖U⁻¹‖∞`.
    The nonzero-diagonal side condition of `linpackY_infNorm_le_infNorm_inv` is
    here *derived* from nonsingularity + upper-triangularity, not assumed, so the
    only hypotheses are the printed ones (`U` nonsingular upper triangular,
    `w ≥ 0`).  The `w ≥ 0` hypothesis is carried for fidelity to the book; the
    bound in fact holds for every real `w`. -/
theorem linpackY_infNorm_le_infNorm_inv_nonsingular {n : ℕ} (hn : 0 < n)
    {U Uinv : Fin n → Fin n → ℝ}
    (hU : IsUpperTriangular U) (hinv : IsLeftInverse n U Uinv)
    (w : Fin n → ℝ) (_hw : ∀ i, 0 ≤ w i) :
    infNormVec (linpackY U (linpackSign U w)) ≤ infNorm Uinv :=
  linpackY_infNorm_le_infNorm_inv hn hU
    (diag_ne_zero_of_isUpperTriangular_isLeftInverse hU hinv) hinv w

end Ch15
end NumStability
