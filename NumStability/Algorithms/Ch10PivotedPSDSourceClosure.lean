import NumStability.Algorithms.Ch10Lemma1011Source

namespace NumStability

open scoped BigOperators

/-!
# Higham 10.14 and the semidefinite stopping tests: actual-run closure

The older chapter surface states (10.26)--(10.28) as predicates over an
unspecified stage matrix.  This file supplies the missing operational object:
the square-root/divide/multiply/subtract complete-pivoting trace
`fl_cpStateFactor`, its computed factor rows, its Gram matrix, and its first
bounded stopping index.  The source-facing theorems below use only this trace.
-/

/-- The computed stage matrix of the factor-form complete-pivoting executor. -/
noncomputable def higham10CpState (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n → Fin n → ℝ :=
  fl_cpStateFactor fp hn A t

/-- The diagonal pivot actually selected by the computed trace. -/
noncomputable def higham10CpPivotValue (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : ℝ :=
  higham10CpState fp hn A t (fl_cpPivotFactor fp hn A t)
    (fl_cpPivotFactor fp hn A t)

/-- A stage passes the complete-pivoting stopping test when its selected
largest computed diagonal does not exceed `tol`. -/
def higham10CpStopsAt (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (tol : ℝ) (t : ℕ) : Prop :=
  higham10CpPivotValue fp hn A t ≤ tol

/-- The computed row emitted at stage `t`.  It contains the rounded square
root at the pivot and rounded divisions away from it. -/
noncomputable def higham10CpRow (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (t : ℕ) : Fin n → ℝ :=
  fl_cpRowOf fp (higham10CpState fp hn A t)
    (fl_cpPivotFactor fp hn A t)

/-- Gram matrix of the first `r` rows emitted by the actual executor. -/
noncomputable def higham10CpGram (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) : Fin n → Fin n → ℝ :=
  fun i j => ∑ t ∈ Finset.range r,
    higham10CpRow fp hn A t i * higham10CpRow fp hn A t j

/-- The all-orders backward error in the exact identity
`Gram + trailing = A + E`. -/
noncomputable def higham10CpBackwardError (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j => higham10CpGram fp hn A r i j +
    higham10CpState fp hn A r i j - A i j

/-- Residual of the truncated computed factor itself. -/
noncomputable def higham10CpFactorResidual (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j => higham10CpGram fp hn A r i j - A i j

/-- Concrete output of `r` stages of complete-pivoted PSD Cholesky. -/
structure Higham10CompletePivotedPSDOutput (n : ℕ) where
  stages : ℕ
  pivot : ℕ → Fin n
  row : ℕ → Fin n → ℝ
  gram : Fin n → Fin n → ℝ
  trailing : Fin n → Fin n → ℝ
  backwardError : Fin n → Fin n → ℝ

/-- The actual fixed-stage executor used in Theorem 10.14. -/
noncomputable def higham10CompletePivotedPSDExecutor (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ) :
    Higham10CompletePivotedPSDOutput n where
  stages := r
  pivot := fl_cpPivotFactor fp hn A
  row := higham10CpRow fp hn A
  gram := higham10CpGram fp hn A r
  trailing := higham10CpState fp hn A r
  backwardError := higham10CpBackwardError fp hn A r

/-- The executor's stored matrices satisfy the displayed backward equation
definitionally, with no factorization certificate supplied by the caller. -/
theorem higham10_completePivotedPSD_executor_backward_equation
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (i j : Fin n) :
    let out := higham10CompletePivotedPSDExecutor fp hn A r
    out.gram i j + out.trailing i j = A i j + out.backwardError i j := by
  dsimp [higham10CompletePivotedPSDExecutor, higham10CpBackwardError]
  ring

/-- Search the bounded run for the first stage whose selected diagonal passes
the stopping tolerance.  `none` means that no stage `t ≤ n` passed. -/
noncomputable def higham10CpFirstStop? (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (tol : ℝ) : Option ℕ := by
  classical
  exact if h : ∃ t : ℕ, t ≤ n ∧ higham10CpStopsAt fp hn A tol t then
    some (Nat.find h)
  else none

/-- The bounded search returns a genuine first stopping stage. -/
theorem higham10CpFirstStop?_spec (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (tol : ℝ)
    (hex : ∃ t : ℕ, t ≤ n ∧ higham10CpStopsAt fp hn A tol t) :
    ∃ r : ℕ,
      higham10CpFirstStop? fp hn A tol = some r ∧
      r ≤ n ∧ higham10CpStopsAt fp hn A tol r ∧
      ∀ s : ℕ, s < r → ¬ higham10CpStopsAt fp hn A tol s := by
  classical
  let r := Nat.find hex
  have hrspec := Nat.find_spec hex
  refine ⟨r, ?_, hrspec.1, hrspec.2, ?_⟩
  · simp [higham10CpFirstStop?, hex, r]
  · intro s hsr hsstop
    exact Nat.find_min hex hsr ⟨le_trans (Nat.le_of_lt hsr) hrspec.1, hsstop⟩

/-- Complete pivoting turns the scalar selected-pivot test into a test on
every computed diagonal entry. -/
theorem higham10CpStopsAt_all_diag (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (tol : ℝ) (r : ℕ)
    (hstop : higham10CpStopsAt fp hn A tol r) :
    ∀ i : Fin n, higham10CpState fp hn A r i i ≤ tol := by
  intro i
  exact le_trans
    (diagArgmax_max hn (higham10CpState fp hn A r) i) hstop

/-- The explicit one-stage rounding contribution in the factor-form trace. -/
noncomputable def higham10CpRoundUnit (fp : FPModel) (δ ρ c : ℝ) : ℝ :=
  fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
    (1 + fp.u) * gamma fp 5 * ((c + δ / 2) ^ 2 / (ρ / 2))

/-- Growth factor for propagating one-stage state error. -/
noncomputable def higham10CpGrowth (_δ ρ c : ℝ) : ℝ :=
  1 + (3 * c ^ 2 + c) / (ρ / 2) ^ 2

/-- Explicit accumulated state-error budget. -/
noncomputable def higham10CpBudget (fp : FPModel) (δ ρ c : ℝ)
    (t : ℕ) : ℝ :=
  higham10CpRoundUnit fp δ ρ c * t * higham10CpGrowth δ ρ c ^ t

/-- The single scalar smallness guard makes the explicit budget admissible for
the pivot-agreement and backward-error inductions. -/
theorem higham10CpBudget_properties (fp : FPModel) (r : ℕ) (δ ρ c : ℝ)
    (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    higham10CpBudget fp δ ρ c 0 = 0 ∧
    (∀ t : ℕ, t < r →
      higham10CpBudget fp δ ρ c t +
          (3 * c ^ 2 * higham10CpBudget fp δ ρ c t +
            c * higham10CpBudget fp δ ρ c t ^ 2) / (ρ / 2) ^ 2 +
          higham10CpRoundUnit fp δ ρ c ≤
        higham10CpBudget fp δ ρ c (t + 1)) ∧
    (∀ t : ℕ, t < r → higham10CpBudget fp δ ρ c t < δ / 2) ∧
    (∀ t : ℕ, t < r → higham10CpBudget fp δ ρ c t ≤ ρ / 4) := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  have hγ5 : 0 ≤ gamma fp 5 := gamma_nonneg fp h5
  let U : ℝ := higham10CpRoundUnit fp δ ρ c
  let K : ℝ := higham10CpGrowth δ ρ c
  let g : ℕ → ℝ := fun t => U * t * K ^ t
  have hU0 : 0 ≤ U := by
    dsimp [U, higham10CpRoundUnit]
    have hcd : (0 : ℝ) ≤ c + δ / 2 := by linarith
    have hq : (0 : ℝ) ≤ (c + δ / 2) ^ 2 / (ρ / 2) := by
      exact div_nonneg (sq_nonneg _) (by linarith)
    exact add_nonneg
      (mul_nonneg fp.u_nonneg (add_nonneg hcd hq))
      (mul_nonneg (mul_nonneg (by linarith [fp.u_nonneg]) hγ5) hq)
  have hK1 : (1 : ℝ) ≤ K := by
    dsimp [K, higham10CpGrowth]
    have : (0 : ℝ) ≤ (3 * c ^ 2 + c) / (ρ / 2) ^ 2 := by
      positivity
    linarith
  have hgle : ∀ t : ℕ, t ≤ r → g t ≤ g r := by
    intro t htr
    dsimp [g]
    have htr' : (t : ℝ) ≤ (r : ℝ) := by exact_mod_cast htr
    have hpow : K ^ t ≤ K ^ r := pow_le_pow_right₀ hK1 htr
    calc
      U * (t : ℝ) * K ^ t ≤ U * (r : ℝ) * K ^ t := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left htr' hU0) (by positivity)
      _ ≤ U * (r : ℝ) * K ^ r := by
        exact mul_le_mul_of_nonneg_left hpow
          (mul_nonneg hU0 (Nat.cast_nonneg r))
  have hg0 : g 0 = 0 := by simp [g]
  have hg_nonneg : ∀ t : ℕ, 0 ≤ g t := by
    intro t
    dsimp [g]
    positivity
  have hsmallg : g r < min (min 1 (δ / 2)) (ρ / 4) := by
    simpa [g, U, K, higham10CpBudget] using hsmall
  have hg1 : ∀ t : ℕ, t < r → g t ≤ 1 := by
    intro t htr
    exact le_trans (hgle t (Nat.le_of_lt htr))
      (le_of_lt (lt_of_lt_of_le hsmallg
        (le_trans (min_le_left _ _) (min_le_left _ _))))
  have hghalf : ∀ t : ℕ, t < r → g t < δ / 2 := by
    intro t htr
    exact lt_of_le_of_lt (hgle t (Nat.le_of_lt htr))
      (lt_of_lt_of_le hsmallg
        (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hgt4 : ∀ t : ℕ, t < r → g t ≤ ρ / 4 := by
    intro t htr
    exact le_trans (hgle t (Nat.le_of_lt htr))
      (le_of_lt (lt_of_lt_of_le hsmallg (min_le_right _ _)))
  have hgstep : ∀ t : ℕ, t < r →
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U ≤
        g (t + 1) := by
    intro t htr
    have hgt0 := hg_nonneg t
    have hgt1 := hg1 t htr
    have habs : 3 * c ^ 2 * g t + c * g t ^ 2 ≤
        (3 * c ^ 2 + c) * g t := by
      nlinarith [mul_nonneg (mul_nonneg hc hgt0)
        (sub_nonneg.mpr hgt1)]
    have hKrec : g t * K + U ≤ g (t + 1) := by
      dsimp [g]
      push_cast
      have hpow : (1 : ℝ) ≤ K ^ (t + 1) := one_le_pow₀ hK1
      have heq : U * (t : ℝ) * K ^ t * K =
          U * (t : ℝ) * K ^ (t + 1) := by
        rw [pow_succ]
        ring
      nlinarith [heq, mul_nonneg hU0 (sub_nonneg.mpr hpow)]
    have hexp : g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 =
        g t * K := by
      dsimp [K, higham10CpGrowth]
      field_simp
    have hdiv : (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 ≤
        (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 := by
      gcongr
    calc
      g t + (3 * c ^ 2 * g t + c * g t ^ 2) / (ρ / 2) ^ 2 + U
          ≤ g t + (3 * c ^ 2 + c) * g t / (ρ / 2) ^ 2 + U := by
            linarith [hdiv]
      _ = g t * K + U := by rw [hexp]
      _ ≤ g (t + 1) := hKrec
  have hgbudget : ∀ t : ℕ, g t = higham10CpBudget fp δ ρ c t := by
    intro t
    rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [← hgbudget 0] using hg0
  · intro t htr
    simpa [← hgbudget t, ← hgbudget (t + 1), U] using hgstep t htr
  · intro t htr
    simpa [← hgbudget t] using hghalf t htr
  · intro t htr
    simpa [← hgbudget t] using hgt4 t htr

/-- A uniform entry bound gives the dimension-costing operator-2-norm bound
used in displays (10.25)--(10.27). -/
theorem opNorm2Le_of_uniform_abs (n : ℕ) (M : Fin n → Fin n → ℝ)
    (b : ℝ) (hb : 0 ≤ b) (hM : ∀ i j : Fin n, |M i j| ≤ b) :
    opNorm2Le M (b * n) := by
  have hones := higham10_7_onesMatrix_opNorm2Le n
  have hscaled := opNorm2Le_smul n (fun _ _ : Fin n => (1 : ℝ)) n b hb hones
  have hdom : ∀ i j : Fin n, |M i j| ≤ b * (1 : ℝ) := by
    intro i j
    simpa using hM i j
  simpa [mul_comm] using
    (opNorm2Le_of_abs_le n M (fun _ _ : Fin n => b * (1 : ℝ))
      hdom (b * n) hscaled)

/-- Explicit all-orders componentwise error constant for the actual factor
rows. -/
noncomputable def higham10CpGramErrorBound (fp : FPModel) (r : ℕ)
    (δ c : ℝ) : ℝ :=
  (r : ℝ) * (fp.u * (c + δ / 2) + (2 * fp.u + fp.u ^ 2) *
    (2 * (1 + fp.u) ^ 2 / (1 - fp.u) ^ 2 *
      Real.sqrt (c + δ / 2)) ^ 2)

/-- The single smallness guard gives exact/computed state proximity at every
stage, including the stopping stage. -/
theorem higham10CpState_close_of_smallness (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    (∀ i j : Fin n,
      |cpState hn A r i j - higham10CpState fp hn A r i j| ≤
        higham10CpBudget fp δ ρ c r) ∧
    (∀ s : ℕ, s < r →
      cpPivot hn A s = fl_cpPivotFactor fp hn A s) := by
  simpa [higham10CpState, higham10CpBudget, higham10CpRoundUnit,
    higham10CpGrowth] using
    (fl_cpPivotFactor_sequence_agrees_small fp hn A r δ ρ c hδ hδρ hc
      h5 hgap hfloor hcap (by
        simpa [higham10CpBudget, higham10CpRoundUnit, higham10CpGrowth]
          using hsmall) r le_rfl)

/-- Displays (10.23)--(10.25), stopping form: a scalar test on the actual
selected computed pivot controls the exact PSD Schur residual, the computed
trailing state, and the latter's operator 2-norm. -/
theorem higham10_23_25_actual_trailing_from_stop (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (r : ℕ) (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4))
    (tol : ℝ) (htol : 0 ≤ tol)
    (hstop : higham10CpStopsAt fp hn A tol r) :
    (∀ i j : Fin n, |cpState hn A r i j| ≤
      tol + higham10CpBudget fp δ ρ c r) ∧
    (∀ i j : Fin n, |higham10CpState fp hn A r i j| ≤
      tol + 2 * higham10CpBudget fp δ ρ c r) ∧
    opNorm2Le (higham10CpState fp hn A r)
      ((tol + 2 * higham10CpBudget fp δ ρ c r) * n) := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  obtain ⟨hclose, _⟩ := higham10CpState_close_of_smallness fp hn A r
    δ ρ c hδ hδρ hc h5 hgap hfloor hcap hsmall
  have hSr : IsPosSemiDef n (cpState hn A r) :=
    cpState_isPosSemiDef hn A hPSD r fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s hs)
  have hcomputedDiag := higham10CpStopsAt_all_diag fp hn A tol r hstop
  have hexactDiag : ∀ i : Fin n,
      cpState hn A r i i ≤ tol + higham10CpBudget fp δ ρ c r := by
    intro i
    have hab := abs_le.mp (hclose i i)
    linarith [hcomputedDiag i, hab.2]
  have hexact : ∀ i j : Fin n, |cpState hn A r i j| ≤
      tol + higham10CpBudget fp δ ρ c r :=
    psd_abs_entry_le_maxdiag (cpState hn A r) hSr
      (tol + higham10CpBudget fp δ ρ c r) hexactDiag
  have hcomputed : ∀ i j : Fin n, |higham10CpState fp hn A r i j| ≤
      tol + 2 * higham10CpBudget fp δ ρ c r := by
    intro i j
    have htri : |higham10CpState fp hn A r i j| ≤
        |cpState hn A r i j| +
          |cpState hn A r i j - higham10CpState fp hn A r i j| := by
      calc
        |higham10CpState fp hn A r i j| =
            |cpState hn A r i j +
              (higham10CpState fp hn A r i j - cpState hn A r i j)| := by
                congr 1
                ring
        _ ≤ |cpState hn A r i j| +
            |higham10CpState fp hn A r i j - cpState hn A r i j| :=
              abs_add_le _ _
        _ = |cpState hn A r i j| +
            |cpState hn A r i j - higham10CpState fp hn A r i j| := by
              rw [abs_sub_comm]
    linarith [htri, hexact i j, hclose i j]
  let i0 : Fin n := ⟨0, hn⟩
  have hg0 : 0 ≤ higham10CpBudget fp δ ρ c r :=
    le_trans (abs_nonneg _) (hclose i0 i0)
  have hb0 : 0 ≤ tol + 2 * higham10CpBudget fp δ ρ c r := by
    linarith
  exact ⟨hexact, hcomputed,
    opNorm2Le_of_uniform_abs n (higham10CpState fp hn A r)
      (tol + 2 * higham10CpBudget fp δ ρ c r) hb0 hcomputed⟩

/-- Theorem 10.14 / displays (10.21)--(10.25), actual-run componentwise
closure under one explicit smallness guard.  The error matrix is the one
computed from the executor, not a caller-supplied certificate. -/
theorem higham10_14_actual_componentwise (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    ∀ i j : Fin n, |higham10CpBackwardError fp hn A r i j| ≤
      higham10CpGramErrorBound fp r δ c := by
  obtain ⟨hg0, hgstep, hghalf, hgt4⟩ :=
    higham10CpBudget_properties fp r δ ρ c hδ hδρ hc h5 hsmall
  intro i j
  simpa [higham10CpBackwardError, higham10CpGram,
    higham10CpRow, higham10CpState, higham10CpGramErrorBound,
    higham10CpRoundUnit] using
    (higham10_14_as_run_backward_error fp hn A r δ ρ c hδ hδρ hc
      h5 hu8 hmul hPSD (higham10CpBudget fp δ ρ c) hg0
      (by simpa [higham10CpRoundUnit] using hgstep) hghalf hgt4
      hgap hfloor hcap i j)

/-- Normwise (10.25) consequence for the actual all-orders backward error. -/
theorem higham10_25_actual_backwardError_opNorm2 (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    opNorm2Le (higham10CpBackwardError fp hn A r)
      (higham10CpGramErrorBound fp r δ c * n) := by
  have hE := higham10_14_actual_componentwise fp hn A r δ ρ c
    hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
  have hcd : (0 : ℝ) ≤ c + δ / 2 := by linarith
  have hB0 : 0 ≤ higham10CpGramErrorBound fp r δ c := by
    dsimp [higham10CpGramErrorBound]
    have hu0 := fp.u_nonneg
    have hcoef : (0 : ℝ) ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact mul_nonneg (Nat.cast_nonneg r)
      (add_nonneg (mul_nonneg hu0 hcd)
        (mul_nonneg hcoef (sq_nonneg _)))
  exact opNorm2Le_of_uniform_abs n (higham10CpBackwardError fp hn A r)
    (higham10CpGramErrorBound fp r δ c) hB0 hE

/-- Combined actual-run certificate for Theorem 10.14 and displays
(10.21)--(10.25). -/
structure Higham10CpActualCertificate (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (δ ρ c tol : ℝ) : Prop where
  stages_le : r ≤ n
  backwardEquation : ∀ i j : Fin n,
    higham10CpGram fp hn A r i j + higham10CpState fp hn A r i j =
      A i j + higham10CpBackwardError fp hn A r i j
  backwardError_componentwise : ∀ i j : Fin n,
    |higham10CpBackwardError fp hn A r i j| ≤
      higham10CpGramErrorBound fp r δ c
  backwardError_normwise :
    opNorm2Le (higham10CpBackwardError fp hn A r)
      (higham10CpGramErrorBound fp r δ c * n)
  exactTrailing_componentwise : ∀ i j : Fin n,
    |cpState hn A r i j| ≤ tol + higham10CpBudget fp δ ρ c r
  computedTrailing_componentwise : ∀ i j : Fin n,
    |higham10CpState fp hn A r i j| ≤
      tol + 2 * higham10CpBudget fp δ ρ c r
  computedTrailing_normwise :
    opNorm2Le (higham10CpState fp hn A r)
      ((tol + 2 * higham10CpBudget fp δ ρ c r) * n)
  factorResidual_componentwise : ∀ i j : Fin n,
    |higham10CpFactorResidual fp hn A r i j| ≤
      higham10CpGramErrorBound fp r δ c + tol +
        2 * higham10CpBudget fp δ ρ c r
  factorResidual_normwise :
    opNorm2Le (higham10CpFactorResidual fp hn A r)
      ((higham10CpGramErrorBound fp r δ c + tol +
        2 * higham10CpBudget fp δ ρ c r) * n)

/-- **Theorem 10.14, actual complete-pivoted PSD source closure.**

The factor rows, trailing matrix, and error are constructed by the executor.
Under the no-tie stage data and the explicit scalar smallness guard, a scalar
computed pivot stop yields the componentwise and operator-norm forms of
(10.21)--(10.25), together with the norm of the truncated-factor residual. -/
theorem higham10_14_completePivotedPSD_actual_source_closed
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hrn : r ≤ n)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4))
    (tol : ℝ) (htol : 0 ≤ tol)
    (hstop : higham10CpStopsAt fp hn A tol r) :
    Higham10CpActualCertificate fp hn A r δ ρ c tol := by
  have hE := higham10_14_actual_componentwise fp hn A r δ ρ c
    hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
  have hEnorm := higham10_25_actual_backwardError_opNorm2 fp hn A r δ ρ c
    hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
  obtain ⟨hexact, htrail, htrailNorm⟩ :=
    higham10_23_25_actual_trailing_from_stop fp hn A hPSD r δ ρ c
      hδ hδρ hc h5 hgap hfloor hcap hsmall tol htol hstop
  have hres : ∀ i j : Fin n,
      |higham10CpFactorResidual fp hn A r i j| ≤
        higham10CpGramErrorBound fp r δ c + tol +
          2 * higham10CpBudget fp δ ρ c r := by
    intro i j
    have heq : higham10CpFactorResidual fp hn A r i j =
        higham10CpBackwardError fp hn A r i j -
          higham10CpState fp hn A r i j := by
      simp only [higham10CpFactorResidual, higham10CpBackwardError]
      ring
    rw [heq]
    have htri : |higham10CpBackwardError fp hn A r i j -
        higham10CpState fp hn A r i j| ≤
        |higham10CpBackwardError fp hn A r i j| +
          |higham10CpState fp hn A r i j| := by
      have h := abs_add_le (higham10CpBackwardError fp hn A r i j)
        (-higham10CpState fp hn A r i j)
      simpa [sub_eq_add_neg] using h
    linarith [htri, hE i j, htrail i j]
  have hcd : (0 : ℝ) ≤ c + δ / 2 := by linarith
  have hB0 : 0 ≤ higham10CpGramErrorBound fp r δ c := by
    dsimp [higham10CpGramErrorBound]
    have hcoef : (0 : ℝ) ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact mul_nonneg (Nat.cast_nonneg r)
      (add_nonneg (mul_nonneg fp.u_nonneg hcd)
        (mul_nonneg hcoef (sq_nonneg _)))
  let i0 : Fin n := ⟨0, hn⟩
  have hg0 : 0 ≤ higham10CpBudget fp δ ρ c r := by
    have hclose := (higham10CpState_close_of_smallness fp hn A r δ ρ c
      hδ hδρ hc h5 hgap hfloor hcap hsmall).1 i0 i0
    exact le_trans (abs_nonneg _) hclose
  have hresB0 : 0 ≤ higham10CpGramErrorBound fp r δ c + tol +
      2 * higham10CpBudget fp δ ρ c r := by linarith
  have hresNorm := opNorm2Le_of_uniform_abs n
    (higham10CpFactorResidual fp hn A r)
    (higham10CpGramErrorBound fp r δ c + tol +
      2 * higham10CpBudget fp δ ρ c r) hresB0 hres
  refine ⟨hrn, ?_, hE, hEnorm, hexact, htrail, htrailNorm, hres, hresNorm⟩
  intro i j
  simp only [higham10CpBackwardError]
  ring

/-- Reading a successful bounded search result exposes both the stopping stage
and its minimality. -/
theorem higham10CpFirstStop?_eq_some (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (tol : ℝ) (r : ℕ)
    (hfirst : higham10CpFirstStop? fp hn A tol = some r) :
    r ≤ n ∧ higham10CpStopsAt fp hn A tol r ∧
      ∀ s : ℕ, s < r → ¬ higham10CpStopsAt fp hn A tol s := by
  classical
  by_cases hex : ∃ t : ℕ, t ≤ n ∧ higham10CpStopsAt fp hn A tol t
  · rw [higham10CpFirstStop?, dif_pos hex] at hfirst
    injection hfirst with hr
    subst r
    have hspec := Nat.find_spec hex
    refine ⟨hspec.1, hspec.2, ?_⟩
    intro s hs hsst
    exact Nat.find_min hex hs
      ⟨le_trans (Nat.le_of_lt hs) hspec.1, hsst⟩
  · rw [higham10CpFirstStop?, dif_neg hex] at hfirst
    simp at hfirst

/-- **Equation (10.26), actual numerical-rank decision.**  If the bounded
executor's first zero-tolerance stop is `r`, the stage-`r` selected pivot is
nonpositive, every computed diagonal is nonpositive, and every earlier
selected pivot was positive. -/
theorem higham10_26_actual_first_nonpositive (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (hfirst : higham10CpFirstStop? fp hn A 0 = some r) :
    higham10_26_nonpositivePivotCriterion
        (higham10CpState fp hn A r) r ∧
      (∀ s : ℕ, s < r → 0 < higham10CpPivotValue fp hn A s) := by
  obtain ⟨_, hstop, hminimal⟩ :=
    higham10CpFirstStop?_eq_some fp hn A 0 r hfirst
  have hall := higham10CpStopsAt_all_diag fp hn A 0 r hstop
  constructor
  · intro i _
    exact hall i
  · intro s hs
    have hnstop := hminimal s hs
    simp only [higham10CpStopsAt, not_le] at hnstop
    exact hnstop

/-- **Equation (10.28), actual numerical-rank decision.**  The returned rank
is the first stage whose largest computed diagonal is at most the stated
fraction of the initial computed pivot. -/
theorem higham10_28_actual_first_relativeDiagonal (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (ε : ℝ) (r : ℕ)
    (hfirst : higham10CpFirstStop? fp hn A
      (ε * higham10CpPivotValue fp hn A 0) = some r) :
    higham10_28_relativeDiagonalStopCriterion
        (higham10CpState fp hn A r) r ε
          (higham10CpPivotValue fp hn A 0) ∧
      (∀ s : ℕ, s < r →
        ε * higham10CpPivotValue fp hn A 0 <
          higham10CpPivotValue fp hn A s) := by
  obtain ⟨_, hstop, hminimal⟩ := higham10CpFirstStop?_eq_some fp hn A
    (ε * higham10CpPivotValue fp hn A 0) r hfirst
  have hall := higham10CpStopsAt_all_diag fp hn A
    (ε * higham10CpPivotValue fp hn A 0) r hstop
  constructor
  · intro i _
    exact hall i
  · intro s hs
    have hnstop := hminimal s hs
    simp only [higham10CpStopsAt, not_le] at hnstop
    exact hnstop

/-- **Equations (10.27)--(10.28), actual residual guarantee.**  A relative
diagonal stop on the computed executor implies the printed residual-norm
criterion with the explicit dimension cost and the honest accumulated-state
term. -/
theorem higham10_28_implies_10_27_actual_residualNorm
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (r : ℕ) (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4))
    (ε : ℝ) (hε : 0 ≤ ε) (hAop : 0 < opNorm2 A)
    (hstop : higham10CpStopsAt fp hn A
      (ε * higham10CpPivotValue fp hn A 0) r) :
    higham10_27_residualStopCriterion
      (opNorm2 (higham10CpState fp hn A r)) (opNorm2 A)
      ((n : ℝ) * ε +
        2 * (n : ℝ) * higham10CpBudget fp δ ρ c r / opNorm2 A) := by
  have hp0 : 0 ≤ higham10CpPivotValue fp hn A 0 := by
    dsimp [higham10CpPivotValue, higham10CpState, fl_cpStateFactor]
    exact isPosSemiDef_diag_nonneg A hPSD _
  have hp0le : higham10CpPivotValue fp hn A 0 ≤ opNorm2 A := by
    dsimp [higham10CpPivotValue, higham10CpState, fl_cpStateFactor]
    exact diag_le_opNorm2Le A (opNorm2 A) (opNorm2Le_opNorm2 A) _
  obtain ⟨_, _, htrailNorm⟩ := higham10_23_25_actual_trailing_from_stop
    fp hn A hPSD r δ ρ c hδ hδρ hc h5 hgap hfloor hcap hsmall
      (ε * higham10CpPivotValue fp hn A 0) (mul_nonneg hε hp0) hstop
  let i0 : Fin n := ⟨0, hn⟩
  have hclose := (higham10CpState_close_of_smallness fp hn A r δ ρ c
    hδ hδρ hc h5 hgap hfloor hcap hsmall).1 i0 i0
  have hg0 : 0 ≤ higham10CpBudget fp δ ρ c r :=
    le_trans (abs_nonneg _) hclose
  have hbound0 : 0 ≤
      (ε * higham10CpPivotValue fp hn A 0 +
        2 * higham10CpBudget fp δ ρ c r) * n := by positivity
  have hnorm := opNorm2_le_of_opNorm2Le
    (higham10CpState fp hn A r) hbound0 htrailNorm
  have hmono :
      (ε * higham10CpPivotValue fp hn A 0 +
          2 * higham10CpBudget fp δ ρ c r) * n ≤
        (ε * opNorm2 A + 2 * higham10CpBudget fp δ ρ c r) * n := by
    gcongr
  have heq :
      ((n : ℝ) * ε +
          2 * (n : ℝ) * higham10CpBudget fp δ ρ c r / opNorm2 A) *
          opNorm2 A =
        (ε * opNorm2 A + 2 * higham10CpBudget fp δ ρ c r) * n := by
    field_simp
  unfold higham10_27_residualStopCriterion
  rw [heq]
  exact hnorm.trans hmono

/-- Source-shaped no-ties wrapper: the auxiliary gap, pivot floor, and entry
cap are constructed from finiteness.  Thus the only quantitative premise left
for a concrete run is the displayed scalar smallness guard on the constructed
budget. -/
theorem higham10_14_completePivotedPSD_actual_of_noTies
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hrn : r ≤ n)
    (hpivot : ∀ t : ℕ, t < r →
      0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hnoTies : Higham10_11NoTies hn A r)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A) :
    ∃ δ ρ c : ℝ,
      0 < δ ∧ δ ≤ ρ ∧ 0 ≤ c ∧
      ∀ (_hsmall : higham10CpBudget fp δ ρ c r <
          min (min 1 (δ / 2)) (ρ / 4))
        (tol : ℝ), 0 ≤ tol → higham10CpStopsAt fp hn A tol r →
          Higham10CpActualCertificate fp hn A r δ ρ c tol := by
  obtain ⟨δ, ρ, c, hδ, hδρ, hc, hgap, hfloor, hcap⟩ :=
    higham10_11_finite_noTies_gap_floor_cap hn A r hpivot hnoTies
  refine ⟨δ, ρ, c, hδ, hδρ, hc, ?_⟩
  intro hsmall tol htol hstop
  exact higham10_14_completePivotedPSD_actual_source_closed fp hn A r hrn
    δ ρ c hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
      tol htol hstop

end NumStability
