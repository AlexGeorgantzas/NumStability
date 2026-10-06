-- Algorithms/Ch15CondEstimators.lean
--
-- Chapter 15 (Condition Number Estimation), §15.5 "Other Condition Estimators".
--
-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002),
-- Chapter 15.  This file gives correctly **Chapter-15-labelled** theorems for the
-- two named results of §15.5:
--
--   * **Algorithm 15.5** (LINPACK condition estimator, p. 296-297): the
--     triangular-solve lower-bound estimator for `‖U⁻¹‖`.  Given a nonsingular
--     upper triangular `U ∈ ℝⁿˣⁿ` and nonnegative weights `{wᵢ}`, it computes a
--     vector `y` solving `U y = d` with each `dⱼ = ±1` chosen (by a weighted
--     look-ahead heuristic) to make `‖y‖` large.  Step 3 of the estimator
--     (p. 296) forms `‖x‖/‖y‖ ≈ ‖T⁻¹‖`, and the *guaranteed, deterministic*
--     content is the parenthetical `(≤ ‖T⁻¹‖)`: the estimate is an honest LOWER
--     BOUND — it never exceeds the true norm.  We formalise the algorithm
--     faithfully (the exact `±1`/look-ahead recursion), prove it solves
--     `U y = d` with `d ∈ {±1}ⁿ`, and prove the lower bound
--         ‖y‖_∞ / ‖d‖_∞ ≤ ‖U⁻¹‖_∞      (Higham §15.5, step 3, p. 296).
--
--   * **Theorem 15.6 (Dixon)** (p. 298, eq. (15.7)): a *probabilistic* bound for
--     the estimate `(xᵀ(AAᵀ)⁻ᵏx)^{1/2k}` of `‖A⁻¹‖₂` with `x` uniform on the unit
--     sphere.  The book stresses (p. 298, immediately after (15.7)) that
--         "the left-hand inequality in (15.7) always holds; it is only the
--          right-hand inequality that is in question."
--     That left-hand inequality is the **deterministic core**.  For `k = 1` the
--     book rewrites (15.7) as `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂ ≤ θ‖A⁻¹x‖₂` (p. 298), and the
--     always-true left inequality is exactly `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂` for unit `x`.
--     We formalise (i) the algebraic identity underlying Dixon's estimate,
--         xᵀ(AAᵀ)⁻¹x = ‖A⁻¹x‖₂²      (via `(AAᵀ)⁻¹ = (A⁻¹)ᵀ A⁻¹`),
--     and (ii) the deterministic left inequality at full strength.  The genuinely
--     *probabilistic* tail bound `1 − 0.8 θ^{−k/2} n^{1/2}` is closed in the
--     follow-on modules `Ch15DixonProbability` and `Ch15DixonClosure`; their
--     public source-shaped endpoint is `higham15_6_dixon_closed`.
--
-- IMPORT-ONLY.  This file creates new Chapter-15-labelled results; it never edits
-- existing modules.  It reuses, unchanged, the operator-norm and estimator
-- machinery of `Analysis/MatrixAlgebra` (`infNorm`, `infNormVec`, `opNorm2`,
-- `matMulVec`, the inverse predicates, and the submultiplicative certificates
-- `infNormVec_matMulVec_le`, `opNorm2Le_opNorm2`) and the 1-norm estimator of
-- `Algorithms/CondEstimation` / `Analysis/ConditionEstimatorLowerBound`.
--
-- Honest statement strength.  The lower bound is unconditional: no spectral,
-- separation, or convergence hypothesis is used, and the algorithm's `d ∈ {±1}ⁿ`
-- / `U y = d` guarantee is proved, not assumed.  The estimator may *under*-estimate
-- (that is the meaning of "lower bound"; §15.5 itself records counterexamples),
-- and nothing here silently upgrades it to an equality.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.CondEstimation
import NumStability.Analysis.ConditionEstimatorLowerBound

namespace NumStability

open scoped BigOperators
open scoped Matrix

namespace Ch15

-- ============================================================
-- §15.5  Algorithm 15.5 — the LINPACK triangular-solve estimator
-- ============================================================

/-- Upper-triangularity predicate: `U i j = 0` whenever `j < i`. -/
def IsUpperTriangular {n : ℕ} (U : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, j.val < i.val → U i j = 0

/-- A `±1`-valued vector (the right-hand side `d` produced by Algorithm 15.5). -/
def IsPlusMinusOne {n : ℕ} (d : Fin n → ℝ) : Prop :=
  ∀ j : Fin n, d j = 1 ∨ d j = -1

/-- `IsUpperTriangular` in the repository sense is exactly Mathlib's
    `BlockTriangular … id` on `Fin n` (both say `U i j = 0` when `j < i`). -/
theorem blockTriangular_id_of_isUpperTriangular {n : ℕ}
    {U : Fin n → Fin n → ℝ} (hU : IsUpperTriangular U) :
    (Matrix.of U : Matrix (Fin n) (Fin n) ℝ).BlockTriangular id := by
  intro i j hji
  exact hU i j hji

/-- **Nonsingular upper triangular ⟹ nonzero diagonal.**

    An upper triangular matrix possessing a (left) inverse — i.e. a *nonsingular*
    upper triangular matrix, exactly the hypothesis of Algorithm 15.5 — has all
    diagonal entries nonzero.  This is `det U = ∏ᵢ Uᵢᵢ ≠ 0`.  It lets the
    lower-bound theorems be stated for a nonsingular upper triangular `U` with the
    `Uᵢᵢ ≠ 0` side condition *derived*, not assumed. -/
theorem diag_ne_zero_of_isUpperTriangular_isLeftInverse {n : ℕ}
    {U Uinv : Fin n → Fin n → ℝ} (hU : IsUpperTriangular U)
    (hinv : IsLeftInverse n U Uinv) :
    ∀ i : Fin n, U i i ≠ 0 := by
  -- The left inverse gives `Uinv * U = 1`, so `det U ≠ 0`.
  have hmul : (Matrix.of Uinv : Matrix (Fin n) (Fin n) ℝ) *
      (Matrix.of U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hinv i j
  have hdet_ne : (Matrix.of U : Matrix (Fin n) (Fin n) ℝ).det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hmul
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact one_ne_zero this.symm
  -- `det U = ∏ diagonal`, so the product is nonzero, hence each factor is.
  have hprod : (∏ i : Fin n, (Matrix.of U : Matrix (Fin n) (Fin n) ℝ) i i) ≠ 0 := by
    rw [← Matrix.det_of_upperTriangular
        (blockTriangular_id_of_isUpperTriangular hU)]
    exact hdet_ne
  intro i
  have := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
  simpa using this

/-- The `∞`-norm of a `±1` vector is `1` (when `n > 0`). -/
theorem infNormVec_eq_one_of_plusMinusOne {n : ℕ} (hn : 0 < n)
    {d : Fin n → ℝ} (hd : IsPlusMinusOne d) :
    infNormVec d = 1 := by
  apply le_antisymm
  · -- every coordinate has `|d i| = 1 ≤ 1`
    apply infNormVec_le_of_abs_le
    · intro i
      rcases hd i with h | h <;> simp [h]
    · norm_num
  · -- coordinate `0` attains `1`
    have h0 := abs_le_infNormVec d ⟨0, hn⟩
    rcases hd ⟨0, hn⟩ with h | h <;> simp [h] at h0 <;> linarith

-- ============================================================
-- The LINPACK look-ahead recursion (exact arithmetic)
-- ============================================================

/-- Partial-product vector at column stage `k`: for the current partial
    solution `y` (with entries at indices `> k` already fixed), this is
      `pᵢ = ∑_{m > k} Uᵢₘ yₘ`,
    the quantity called `p(1:n)` in Algorithm 15.5 after columns `n,…,k+1`
    have been processed. -/
noncomputable def linpackPartial {n : ℕ} (U : Fin n → Fin n → ℝ)
    (k : ℕ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ m ∈ Finset.univ.filter (fun m : Fin n => k < m.val), U i m * y m

/-- One column of Algorithm 15.5, driven by an abstract sign-selection function
    `sgn`.  Column `k` (0-indexed) is processed:
    with `p = linpackPartial U k y` the accumulated partial products,
    the sign `s = sgn ⟨k,_⟩ p ∈ {±1}` is chosen (the `±1` value of `dₖ`), and
    the new component is `yₖ = (s − pₖ)/Uₖₖ` (`= (dₖ − pₖ)/uₖₖ` in the book).
    The recursion counts `k` down from `n` (columns processed right-to-left,
    exactly as the `for j = n:−1:1` loop of Algorithm 15.5). -/
noncomputable def linpackYSteps {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) :
    ∀ (k : ℕ), k ≤ n → (Fin n → ℝ) → Fin n → ℝ
  | 0,     _,  y => y
  | k + 1, hk, y =>
      let jk : Fin n := ⟨k, hk⟩
      let p : Fin n → ℝ := linpackPartial U k y
      let s : ℝ := sgn jk p
      let yk : ℝ := (s - p jk) / U jk jk
      linpackYSteps U sgn k (Nat.le_of_succ_le hk) (Function.update y jk yk)

/-- Algorithm 15.5 (LINPACK condition estimator, Higham §15.5, p. 296-297).
    Starting from `y = 0`, process all columns `n−1,…,0`.  Returns the vector `y`
    with `U y = d`, `dⱼ = ±1`, of the estimator. -/
noncomputable def linpackY {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  linpackYSteps U sgn n (le_refl n) (fun _ => 0)

-- ============================================================
-- Structural lemmas for the recursion
-- ============================================================

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

-- ============================================================
-- The LINPACK weighted look-ahead sign rule (Algorithm 15.5)
-- ============================================================

/-- **The LINPACK look-ahead sign choice** (Higham §15.5, Algorithm 15.5,
    the `if … ≥ …` test on p. 296).

    At column `j`, with accumulated partial products `p`, the algorithm forms the
    two candidate solution components `yⱼ⁺ = (1 − pⱼ)/uⱼⱼ`, `yⱼ⁻ = (−1 − pⱼ)/uⱼⱼ`
    and the resulting look-ahead partial products `pᵢ± = pᵢ + Uᵢⱼ yⱼ±` (`i < j`).
    It picks `dⱼ = +1` iff the weighted sum for the `+` branch dominates:
      `wⱼ|1 − pⱼ| + ∑_{i<j} wᵢ|pᵢ⁺|  ≥  wⱼ|1 + pⱼ| + ∑_{i<j} wᵢ|pᵢ⁻|`,
    otherwise `dⱼ = −1`.  (The weights `wᵢ ≥ 0`; LINPACK uses `wᵢ ≡ 1`.) -/
noncomputable def linpackSign {n : ℕ} (U : Fin n → Fin n → ℝ) (w : Fin n → ℝ) :
    Fin n → (Fin n → ℝ) → ℝ :=
  fun jk p =>
    let yplus : ℝ := (1 - p jk) / U jk jk
    let yminus : ℝ := (-1 - p jk) / U jk jk
    let lhs : ℝ := w jk * |1 - p jk| +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < jk.val),
        w i * |p i + U i jk * yplus|
    let rhs : ℝ := w jk * |(-1) - p jk| +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val < jk.val),
        w i * |p i + U i jk * yminus|
    if rhs ≤ lhs then 1 else -1

/-- The LINPACK look-ahead sign rule returns `±1` (a `dⱼ` value).  This is all the
    lower-bound guarantee needs: the value of the heuristic is `±1`, whatever the
    weighted comparison decides. -/
theorem linpackSign_plusMinusOne {n : ℕ} (U : Fin n → Fin n → ℝ) (w : Fin n → ℝ)
    (jk : Fin n) (p : Fin n → ℝ) :
    linpackSign U w jk p = 1 ∨ linpackSign U w jk p = -1 := by
  unfold linpackSign
  simp only
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

-- ============================================================
-- Algorithm 15.5:  `U y = d` with `d = ±1`
-- ============================================================

/-- **The right-hand side `d = U y` of Algorithm 15.5**: the residual of the
    computed `y` under `U`.  By construction `dⱼ = ±1`. -/
noncomputable def linpackD {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) : Fin n → ℝ :=
  matMulVec n U (linpackY U sgn)

/-- **Algorithm 15.5 solves `U y = d`.**  Immediate from `linpackD` being defined
    as the residual `U y`; recorded to match the book's step "solve `U y = d`". -/
theorem linpackY_solves {n : ℕ} (U : Fin n → Fin n → ℝ)
    (sgn : Fin n → (Fin n → ℝ) → ℝ) :
    matMulVec n U (linpackY U sgn) = linpackD U sgn := rfl

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

-- ============================================================
-- §15.5, step 3:  the guaranteed LOWER BOUND on ‖U⁻¹‖
-- ============================================================

/-- **The LINPACK estimate is a lower bound on `‖U⁻¹‖∞` (general solve form).**

    Higham §15.5, step 3 (p. 296): "Estimate `‖T⁻¹‖ ≈ ‖x‖/‖y‖ (≤ ‖T⁻¹‖)`."

    For *any* right-hand side `d` and the exact solution `y` of `U y = d`
    (equivalently `y = U⁻¹ d`), the estimate `‖y‖∞ / ‖d‖∞` never exceeds the true
    norm `‖U⁻¹‖∞`.  This is the honest, unconditional content of the estimator:
    it follows purely from operator-norm submultiplicativity
    `‖U⁻¹ d‖∞ ≤ ‖U⁻¹‖∞ ‖d‖∞`, with no assumption on the quality of `d`.

    `Uinv` is supplied as a left inverse of `U` (`Uinv · U = I`); it then acts as
    `y = Uinv d` on the solution. -/
theorem linpack_estimate_le_infNorm_inv {n : ℕ} (hn : 0 < n)
    {U Uinv : Fin n → Fin n → ℝ} (hinv : IsLeftInverse n U Uinv)
    {y d : Fin n → ℝ} (hsolve : matMulVec n U y = d) (hd : infNormVec d ≠ 0) :
    infNormVec y / infNormVec d ≤ infNorm Uinv := by
  -- `y = Uinv (U y) = Uinv d`.
  have hyeq : y = matMulVec n Uinv d := by
    have h := matMulVec_of_isRightInverse Uinv U hinv y
    rw [hsolve] at h
    exact h.symm
  have hdpos : 0 < infNormVec d :=
    lt_of_le_of_ne (infNormVec_nonneg d) (Ne.symm hd)
  rw [div_le_iff₀ hdpos]
  calc infNormVec y = infNormVec (matMulVec n Uinv d) := by rw [hyeq]
    _ ≤ infNorm Uinv * infNormVec d := infNormVec_matMulVec_le hn Uinv d
    _ = infNorm Uinv * infNormVec d := rfl

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

-- ============================================================
-- §15.5  Theorem 15.6 (Dixon) — the deterministic core
-- ============================================================

/-- The `M`-quadratic form `xᵀ M x`, written through `matMulVec`. -/
noncomputable def quadForm {n : ℕ} (M : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, x i * matMulVec n M x i

/-- **The Gram matrix `BᵀB` is a (two-sided) inverse of `A Aᵀ`.**

    If `B` is a two-sided inverse of `A` (so `B = A⁻¹`), then `(A Aᵀ)⁻¹ = Bᵀ B`.
    Concretely `Bᵀ B = (A⁻¹)ᵀ A⁻¹`, and this is the inverse appearing in Dixon's
    quadratic form `xᵀ(AAᵀ)⁻¹x` (Higham §15.5, eq. (15.7)).  Proved at matrix
    level from `A · B = I` and `B · A = I`. -/
theorem gram_inv_of_isInverse {n : ℕ} {A B : Fin n → Fin n → ℝ}
    (hR : IsRightInverse n A B) (hL : IsLeftInverse n A B) :
    IsInverse n (matMul n A (matTranspose A))
      (matMul n (matTranspose B) B) := by
  -- Work at Mathlib matrix level.
  set AM : Matrix (Fin n) (Fin n) ℝ := Matrix.of A with hAM
  set BM : Matrix (Fin n) (Fin n) ℝ := Matrix.of B with hBM
  have hAB : AM * BM = 1 := by
    ext i j; simpa [hAM, hBM, Matrix.mul_apply, Matrix.one_apply] using hR i j
  have hBA : BM * AM = 1 := by
    ext i j; simpa [hAM, hBM, Matrix.mul_apply, Matrix.one_apply] using hL i j
  -- `Bᵀ` is a two-sided inverse of `Aᵀ`.
  have hAtBt : AMᵀ * BMᵀ = 1 := by
    rw [← Matrix.transpose_mul]; rw [hBA]; simp
  have hBtAt : BMᵀ * AMᵀ = 1 := by
    rw [← Matrix.transpose_mul]; rw [hAB]; simp
  -- `(A Aᵀ)(Bᵀ B) = A (Aᵀ Bᵀ) B = A B = I`, and symmetrically.
  have hprod_right : (AM * AMᵀ) * (BMᵀ * BM) = 1 := by
    calc (AM * AMᵀ) * (BMᵀ * BM)
        = AM * (AMᵀ * BMᵀ) * BM := by
          simp only [Matrix.mul_assoc]
      _ = AM * BM := by rw [hAtBt]; simp
      _ = 1 := hAB
  have hprod_left : (BMᵀ * BM) * (AM * AMᵀ) = 1 := by
    calc (BMᵀ * BM) * (AM * AMᵀ)
        = BMᵀ * (BM * AM) * AMᵀ := by
          simp only [Matrix.mul_assoc]
      _ = BMᵀ * AMᵀ := by rw [hBA]; simp
      _ = 1 := hBtAt
  -- Translate the matrix identities to the repository predicates.
  have hAAt : matMul n A (matTranspose A) = fun i j => (AM * AMᵀ) i j := by
    ext i j; simp [matMul, matTranspose, hAM, Matrix.mul_apply]
  have hBtB : matMul n (matTranspose B) B = fun i j => (BMᵀ * BM) i j := by
    ext i j; simp [matMul, matTranspose, hBM, Matrix.mul_apply]
  constructor
  · -- left inverse: `(BᵀB)(AAᵀ) = I`
    intro i j
    rw [hAAt, hBtB]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hprod_left
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  · -- right inverse: `(AAᵀ)(BᵀB) = I`
    intro i j
    rw [hAAt, hBtB]
    have := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hprod_right
    simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- **Dixon's algebraic identity** (the identity underlying (15.7), Higham §15.5).

    The Dixon quadratic form of the inverse Gram matrix is the squared norm of the
    inverse acting on `x`:
        `xᵀ (Bᵀ B) x = ‖B x‖₂²`,
    where `B = A⁻¹`.  Combined with `gram_inv_of_isInverse` (which identifies
    `Bᵀ B = (A Aᵀ)⁻¹`), this is exactly
        `xᵀ (A Aᵀ)⁻¹ x = ‖A⁻¹ x‖₂²`,
    the `k = 1` content of Dixon's estimate.  Purely algebraic; no randomness. -/
theorem dixon_quadForm_gram_eq {n : ℕ} (B : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    quadForm (matMul n (matTranspose B) B) x = vecNorm2Sq (matMulVec n B x) := by
  unfold quadForm vecNorm2Sq
  -- Let `z = B x`.  `xᵀ(BᵀB)x = ∑ₖ zₖ² = ‖z‖²`.
  set z : Fin n → ℝ := matMulVec n B x with hz
  have hmv : ∀ i : Fin n,
      matMulVec n (matMul n (matTranspose B) B) x i =
        matMulVec n (matTranspose B) z i := by
    intro i; rw [hz]; exact matMulVec_matMul n (matTranspose B) B x i
  calc
    (∑ i : Fin n, x i * matMulVec n (matMul n (matTranspose B) B) x i)
        = ∑ i : Fin n, x i * matMulVec n (matTranspose B) z i := by
          exact Finset.sum_congr rfl (fun i _ => by rw [hmv i])
    _ = ∑ i : Fin n, x i * ∑ k : Fin n, B k i * z k := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          unfold matMulVec matTranspose; rfl
    _ = ∑ i : Fin n, ∑ k : Fin n, x i * (B k i * z k) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
    _ = ∑ k : Fin n, ∑ i : Fin n, x i * (B k i * z k) := Finset.sum_comm
    _ = ∑ k : Fin n, z k * ∑ i : Fin n, B k i * x i := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = ∑ k : Fin n, z k * z k := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          have : (∑ i : Fin n, B k i * x i) = z k := by rw [hz]; unfold matMulVec; rfl
          rw [this]
    _ = ∑ k : Fin n, z k ^ 2 := Finset.sum_congr rfl (fun k _ => by ring)

/-- **Dixon's left inequality always holds** (Higham §15.5, Theorem 15.6,
    the `k = 1` rewriting on p. 298).

    "Note that the left-hand inequality in (15.7) always holds" (p. 298).  For
    `k = 1`, (15.7) reads `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂ ≤ θ‖A⁻¹x‖₂`, and the always-true left
    part is `‖A⁻¹x‖₂ ≤ ‖A⁻¹‖₂` for a unit vector `x`.  With `B = A⁻¹` this is
        `‖B x‖₂ ≤ ‖B‖₂`      for `‖x‖₂ = 1`.
    It is pure operator-norm submultiplicativity — no probability, no hypothesis
    on `x` beyond being a unit vector.  This is the deterministic core Dixon's
    theorem is built on: the estimate `‖A⁻¹x‖₂` is always a lower bound for
    `‖A⁻¹‖₂`. -/
theorem dixon_left_inequality {n : ℕ} (B : Fin n → Fin n → ℝ) {x : Fin n → ℝ}
    (hx : vecNorm2 x = 1) :
    vecNorm2 (matMulVec n B x) ≤ opNorm2 B := by
  have h := opNorm2Le_opNorm2 B x
  rwa [hx, mul_one] at h

/-- **Dixon's left inequality, quadratic-form form** (Higham §15.5, Theorem 15.6,
    eq. (15.7) with `k = 1`).

    Assembling `dixon_quadForm_gram_eq` (`xᵀ(BᵀB)x = ‖Bx‖₂²`) with
    `dixon_left_inequality`: for a unit vector `x` and `B = A⁻¹`,
        `√(xᵀ (Bᵀ B) x) ≤ ‖A⁻¹‖₂`.
    Via `gram_inv_of_isInverse` the matrix `Bᵀ B` is `(A Aᵀ)⁻¹`, so this is
    literally the left inequality of (15.7),
        `(xᵀ (A Aᵀ)⁻¹ x)^{1/2} ≤ ‖A⁻¹‖₂`,
    which the theorem asserts holds *with probability one* (it always holds). -/
theorem dixon_sqrt_quadForm_le_opNorm2 {n : ℕ} (B : Fin n → Fin n → ℝ)
    {x : Fin n → ℝ} (hx : vecNorm2 x = 1) :
    Real.sqrt (quadForm (matMul n (matTranspose B) B) x) ≤ opNorm2 B := by
  -- `√(xᵀ(BᵀB)x) = √(‖Bx‖²) = ‖Bx‖₂ ≤ ‖B‖₂`.
  rw [dixon_quadForm_gram_eq B x]
  have hsqrt : Real.sqrt (vecNorm2Sq (matMulVec n B x)) = vecNorm2 (matMulVec n B x) :=
    rfl
  rw [hsqrt]
  exact dixon_left_inequality B hx

-- ============================================================
-- Theorem 15.6 (Dixon): probabilistic completion
-- ============================================================
-- The declarations above are the original `k = 1` deterministic substrate.
-- `Ch15DixonProbability.lean` now proves the required uniform-sphere
-- one-coordinate small-ball estimate directly from normalized independent
-- Gaussians, including the printed `4/5` constant.  `Ch15DixonClosure.lean`
-- supplies the actual Gram spectral producer for every positive `k`, derives
-- both powered inequalities, and exposes the complete probability statement as
-- `higham15_6_dixon_closed`.  No Beta-marginal or tail-bound premise remains.

end Ch15

end NumStability
