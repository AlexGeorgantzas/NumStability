/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Theorem 11.8: honest operational DGTTRF/DGTTRS middle certificate

Higham, 2nd ed., p. 224 says that the symmetric-tridiagonal middle system in
Aasen's method is usually solved by GEPP.  The literal adjacent-pivot executor
in `AasenAdjacentPivotTridiagExecutorCh11Closure` models the corresponding
DGTTRF/DGTTRS storage and arithmetic.  Its previously proposed `gamma_6`
composition is conditional on `DGTTRFFactorForwardCertificate`; the concrete
three-by-three trace in
`AasenAdjacentPivotTridiagForwardCounterexampleCh11` proves that certificate
false after two consecutive adjacent interchanges.

This file therefore does not reintroduce the failed accumulated-factor
premise.  Instead it constructs the canonical rank-one correction directly
from the *observable source residual* of the actual computed solution.  The
correction gives an unconditional exact `AasenDirectMiddleBudget` once the
actual no-breakdown and `gamma_3` guards are supplied.  Its entries are
explicit, so the remaining quantitative gate is exactly the checkable norm
bound on this residual correction; the final theorem feeds that obligation,
without a hidden factor-forward certificate, into the existing printed-radius
Theorem-11.8 assembly.
-/
import NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagForwardCounterexampleCh11
import NumStability.Algorithms.Cholesky.AasenDirectTridiagGEPPSolveCh11Closure
import Mathlib.Algebra.Order.Chebyshev

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenAdjacentOperational

open NumStability
open NumStability.Ch11Closure
open NumStability.Ch11Closure.AasenAdjacentGEPP
open NumStability.Ch11Closure.AasenDirectGEPP
open NumStability.Ch11Closure.AasenDirect
open NumStability.Ch11Closure.AasenNorm
open NumStability.Ch11Closure.Mixed
open NumStability.Ch11Closure.HFactor
open NumStability.Ch11Closure.SparseFactor

/-! ## Pivot-path multiplier bounds and storage stability -/

/-- The rounded quotient selected by the adjacent-pivot comparison has
absolute value at most `1 + u`.  This is the local numerical fact behind the
usual exact `|m| ≤ 1` multiplier bound; the extra factor is precisely the one
rounded division used to store the multiplier. -/
theorem flDGTTRFMultiplier_abs_le_one_add_u (fp : FPModel) (a pivot : ℝ)
    (hpivot : pivot ≠ 0) (ha : |a| ≤ |pivot|) :
    |flDGTTRFMultiplier fp a pivot| ≤ 1 + fp.u := by
  obtain ⟨δ, hδ, hm⟩ :=
    flDGTTRFMultiplier_relative fp a pivot hpivot
  have hquot : |a / pivot| ≤ 1 := by
    rw [abs_div]
    exact (div_le_one (abs_pos.mpr hpivot)).2 ha
  have hone : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ = 1 + |δ| := by rw [abs_one]
      _ ≤ 1 + fp.u := by linarith
  rw [hm, abs_mul]
  calc
    |a / pivot| * |1 + δ| ≤ 1 * |1 + δ| :=
      mul_le_mul_of_nonneg_right hquot (abs_nonneg _)
    _ ≤ 1 * (1 + fp.u) :=
      mul_le_mul_of_nonneg_left hone zero_le_one
    _ = 1 + fp.u := one_mul _

/-- At one literal DGTTRF stage, the chosen nonzero pivot and the adjacent
pivot comparison force the newly stored multiplier to have magnitude at most
`1 + u`, in either branch. -/
theorem flDGTTRFStepAt_dl_abs_le_one_add_u (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (k : Fin n) (hk : k.val + 1 < n)
    (hpivot : if |s.d k| ≥ |s.dl k| then s.d k ≠ 0 else s.dl k ≠ 0) :
    |(flDGTTRFStepAt fp s k hk).dl k| ≤ 1 + fp.u := by
  by_cases hchoice : |s.d k| ≥ |s.dl k|
  · have hp : s.d k ≠ 0 := by simpa [hchoice] using hpivot
    have h := flDGTTRFMultiplier_abs_le_one_add_u fp
      (s.dl k) (s.d k) hp hchoice
    simpa [flDGTTRFStepAt, hchoice, flDGTTRFMultiplier] using h
  · have hp : s.dl k ≠ 0 := by simpa [hchoice] using hpivot
    have hsmall : |s.d k| ≤ |s.dl k| := le_of_not_ge hchoice
    have h := flDGTTRFMultiplier_abs_le_one_add_u fp
      (s.d k) (s.dl k) hp hsmall
    simpa [flDGTTRFStepAt, hchoice, flDGTTRFMultiplier] using h

/-- A DGTTRF stage changes only the multiplier slot belonging to that stage.
This storage fact is what lets the local pivot bound survive to the completed
factor trace. -/
theorem flDGTTRFStepAt_dl_of_ne (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (k j : Fin n) (hk : k.val + 1 < n)
    (hjk : j ≠ k) :
    (flDGTTRFStepAt fp s k hk).dl j = s.dl j := by
  simp only [flDGTTRFStepAt]
  split <;> simp [finReplace_of_ne, hjk]

/-- A reconstructed pivot permutation prefix depends only on the pivot bits
strictly before the end of that prefix.  This is the basic coherence lemma
needed to compare an evolving factor state with its final source-row labels. -/
theorem dgttrfPermEquivRun_congr_prefix {n : ℕ} (s t : DGTTRFData n) :
    ∀ steps : ℕ,
      (∀ i : Fin n, i.val < steps → s.ipiv i = t.ipiv i) →
      dgttrfPermEquivRun s steps = dgttrfPermEquivRun t steps := by
  intro steps
  induction steps with
  | zero =>
      intro _h
      rfl
  | succ steps ih =>
      intro hbits
      simp only [dgttrfPermEquivRun]
      have hpref : ∀ i : Fin n, i.val < steps → s.ipiv i = t.ipiv i := by
        intro i hi
        exact hbits i (by omega)
      rw [ih hpref]
      split
      · rename_i hstep
        let i : Fin n :=
          ⟨steps, Nat.lt_trans (Nat.lt_succ_self steps) hstep⟩
        have hi : s.ipiv i = t.ipiv i := hbits i (by simp [i])
        rw [hi]
      · rfl

/-- A factor stage leaves every earlier (and every other) pivot bit
unchanged. -/
theorem flDGTTRFStepAt_ipiv_of_ne (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (k j : Fin n) (hk : k.val + 1 < n)
    (hjk : j ≠ k) :
    (flDGTTRFStepAt fp s k hk).ipiv j = s.ipiv j := by
  simp only [flDGTTRFStepAt]
  split <;> simp [finReplace_of_ne, hjk]

/-- The mutable source-row labels in a literal factor prefix agree with the
equivalence reconstructed from exactly the pivot bits already executed.
Thus source-row bookkeeping itself introduces no unproved permutation
assumption in a future pathwise residual argument. -/
theorem flDGTTRFRun_perm_eq_dgttrfPermEquivRun (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) :
    ∀ steps : ℕ,
      (flDGTTRFRun fp n T steps).perm =
        dgttrfPermEquivRun (flDGTTRFRun fp n T steps) steps := by
  intro steps
  induction steps with
  | zero =>
      rfl
  | succ steps ih =>
      simp only [flDGTTRFRun]
      split
      · rename_i hstep
        let i : Fin n :=
          ⟨steps, Nat.lt_trans (Nat.lt_succ_self steps) hstep⟩
        let ip : Fin n := ⟨i.val + 1, by simpa [i] using hstep⟩
        let s := flDGTTRFRun fp n T steps
        let t := flDGTTRFStepAt fp s i hstep
        change t.perm = dgttrfPermEquivRun t (steps + 1)
        have hprefix :
            dgttrfPermEquivRun t steps = dgttrfPermEquivRun s steps := by
          apply dgttrfPermEquivRun_congr_prefix
          intro j hj
          exact flDGTTRFStepAt_ipiv_of_ne fp s i j hstep (by
            intro hji
            have := Fin.mk.inj hji
            omega)
        have ih' : s.perm = dgttrfPermEquivRun s steps := by
          simpa [s] using ih
        rw [show dgttrfPermEquivRun t (steps + 1) =
            if t.ipiv i then
              (Equiv.swap i ip).trans (dgttrfPermEquivRun t steps)
            else dgttrfPermEquivRun t steps by
          simp [dgttrfPermEquivRun, hstep, i, ip]]
        by_cases hchoice : |s.d i| ≥ |s.dl i|
        · have htperm : t.perm = s.perm := by
            simp [t, flDGTTRFStepAt, hchoice]
          have htbit : t.ipiv i = false := by
            simp [t, flDGTTRFStepAt, hchoice]
          rw [htperm, htbit]
          simp only [Bool.false_eq_true, if_false]
          simpa [hprefix] using ih'
        · have htperm : t.perm = finSwap s.perm i ip := by
            simp [t, flDGTTRFStepAt, hchoice, ip]
          have htbit : t.ipiv i = true := by
            simp [t, flDGTTRFStepAt, hchoice]
          rw [htperm, htbit, if_pos rfl, hprefix]
          funext j
          have hipi : ip ≠ i := by
            intro h
            have := Fin.mk.inj h
            simp [i] at this
          by_cases hji : j = i
          · subst j
            simpa [finSwap, Equiv.trans_apply, Equiv.swap_apply_left] using
              congrFun ih' ip
          by_cases hjip : j = ip
          · subst j
            simpa [finSwap, hipi, Equiv.trans_apply,
              Equiv.swap_apply_right] using congrFun ih' i
          · simpa [finSwap, hji, hjip, Equiv.trans_apply,
              Equiv.swap_apply_of_ne_of_ne hji hjip] using congrFun ih' j
      · rename_i hstep
        simpa [dgttrfPermEquivRun, hstep] using ih

/-- Completed source-row coherence: the `perm` field of the actual DGTTRF
output is exactly the accumulated adjacent-pivot equivalence used by the
source residual and source envelope definitions. -/
theorem flDGTTRF_perm_eq_dgttrfPermEquiv (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) :
    (flDGTTRF fp n T).perm = dgttrfPermEquiv (flDGTTRF fp n T) := by
  exact flDGTTRFRun_perm_eq_dgttrfPermEquivRun fp n T (n - 1)

/-- A factor stage writes a second-superdiagonal fill only in its own slot. -/
theorem flDGTTRFStepAt_du2_of_ne (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (k j : Fin n) (hk : k.val + 1 < n)
    (hjk : j ≠ k) :
    (flDGTTRFStepAt fp s k hk).du2 j = s.du2 j := by
  simp only [flDGTTRFStepAt]
  split <;> simp [finReplace_of_ne, hjk]

/-- Before a stage is reached, every `du2` slot at or to the right of that
stage is still the initial structural zero. -/
theorem flDGTTRFRun_du2_eq_zero_of_steps_le_val (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) :
    ∀ (steps : ℕ) (j : Fin n), steps ≤ j.val →
      (flDGTTRFRun fp n T steps).du2 j = 0 := by
  intro steps
  induction steps with
  | zero =>
      intro j _hj
      rfl
  | succ steps ih =>
      intro j hj
      simp only [flDGTTRFRun]
      split
      · rename_i hstep
        let i : Fin n :=
          ⟨steps, Nat.lt_trans (Nat.lt_succ_self steps) hstep⟩
        have hji : j ≠ i := by
          intro h
          have := Fin.mk.inj h
          simp [i] at this
          omega
        rw [flDGTTRFStepAt_du2_of_ne fp _ _ _ hstep hji]
        exact ih j (by omega)
      · exact ih j (by omega)

/-- In particular, the active pivot row presented to each literal factor
stage has no stale bandwidth-two fill. -/
theorem flDGTTRFRun_current_du2_eq_zero (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (k : ℕ) (hk : k + 1 < n) :
    let i : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
    (flDGTTRFRun fp n T k).du2 i = 0 := by
  intro i
  exact flDGTTRFRun_du2_eq_zero_of_steps_le_val fp n T k i (by simp [i])

/-! ### Algebra of one combined factor/forward stage -/

/-- Exact no-interchange two-row residual telescope.  The three displayed
differences are, respectively, the rounded multiplier-column residual, the
rounded diagonal-update residual, and the rounded RHS-update residual. -/
theorem dgttrfNoSwap_combined_residual_identity
    (x₀ x₁ d dl du d₁ du₁ m dn q₁ y₀ y₁ y₂ : ℝ) :
    x₁ - (dl * y₀ + d₁ * y₁ + du₁ * y₂) =
      (q₁ - (dn * y₁ + du₁ * y₂)) +
        m * (x₀ - (d * y₀ + du * y₁)) +
        (m * d - dl) * y₀ - (q₁ - (x₁ - m * x₀)) +
        (m * du + dn - d₁) * y₁ := by
  ring

/-- Exact interchange two-row residual telescope.  The extra final term is
the rounded cancellation residual for the generated second-superdiagonal
fill. -/
theorem dgttrfSwap_combined_residual_identity
    (x₀ x₁ d dl du d₁ du₁ m dn dun q₁ y₀ y₁ y₂ : ℝ) :
    x₀ - (d * y₀ + du * y₁) =
      (q₁ - (dn * y₁ + dun * y₂)) +
        m * (x₁ - (dl * y₀ + d₁ * y₁ + du₁ * y₂)) +
        (m * dl - d) * y₀ - (q₁ - (x₀ - m * x₁)) +
        (m * d₁ + dn - du) * y₁ +
        (m * du₁ + dun) * y₂ := by
  ring

/-- Residual of the active bandwidth-two pivot row before its elimination
stage.  On the literal run, the freshness theorem above makes its `du2` term
zero at the moment this row is active. -/
def dgttrfActivePivotResidual {n : ℕ} (s : DGTTRFData n)
    (x : Fin n → ℝ) (k : Fin n) (y₀ y₁ y₂ : ℝ) : ℝ :=
  x k - (s.d k * y₀ + s.du k * y₁ + s.du2 k * y₂)

/-- Residual of the active row immediately below the pivot row. -/
def dgttrfActiveNextResidual {n : ℕ} (s : DGTTRFData n)
    (x : Fin n → ℝ) (k : Fin n) (hk : k.val + 1 < n)
    (y₀ y₁ y₂ : ℝ) : ℝ :=
  let kp : Fin n := ⟨k.val + 1, hk⟩
  x kp - (s.dl k * y₀ + s.d kp * y₁ + s.du kp * y₂)

/-- Residual of a bandwidth-two upper pivot row after one factor stage. -/
def dgttrfUpperPivotResidual {n : ℕ} (s : DGTTRFData n)
    (q : Fin n → ℝ) (k : Fin n) (y₀ y₁ y₂ : ℝ) : ℝ :=
  q k - (s.d k * y₀ + s.du k * y₁ + s.du2 k * y₂)

/-- Residual of the new traveling upper row after one factor stage. -/
def dgttrfUpperNextResidual {n : ℕ} (s : DGTTRFData n)
    (q : Fin n → ℝ) (k : Fin n) (hk : k.val + 1 < n)
    (y₁ y₂ : ℝ) : ℝ :=
  let kp : Fin n := ⟨k.val + 1, hk⟩
  q kp - (s.d kp * y₁ + s.du kp * y₂)

/-- The traveling upper residual produced at stage `k` is exactly the active
pivot residual consumed at stage `k+1` whenever the next `du2` slot is still
fresh.  The third solution component is arbitrary because its coefficient is
that structural zero. -/
theorem dgttrfUpperNextResidual_eq_activePivotResidual_of_du2_eq_zero
    {n : ℕ} (s : DGTTRFData n) (q : Fin n → ℝ)
    (k : Fin n) (hk : k.val + 1 < n) (y₁ y₂ y₃ : ℝ)
    (hdu2 : s.du2 ⟨k.val + 1, hk⟩ = 0) :
    dgttrfUpperNextResidual s q k hk y₁ y₂ =
      dgttrfActivePivotResidual s q ⟨k.val + 1, hk⟩ y₁ y₂ y₃ := by
  simp [dgttrfUpperNextResidual, dgttrfActivePivotResidual, hdu2]

/-- Literal no-interchange factor/forward identity with source-row labels.
The pivot source row is finalized in place; the next source row remains the
traveling row.  Its old residual is exactly the new traveling residual plus
the finalized pivot residual and the three observable local arithmetic
residuals. -/
theorem flDGTTRF_noSwap_combined_source_row_identity (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (x : Fin n → ℝ) (k : Fin n)
    (hk : k.val + 1 < n) (hchoice : |s.d k| ≥ |s.dl k|)
    (hdu2 : s.du2 k = 0) (y₀ y₁ y₂ : ℝ) :
    let kp : Fin n := ⟨k.val + 1, hk⟩
    let t := flDGTTRFStepAt fp s k hk
    let q := flDGTTRSForwardStepAt fp t x k hk
    t.perm k = s.perm k ∧
    t.perm kp = s.perm kp ∧
    dgttrfUpperPivotResidual t q k y₀ y₁ y₂ =
      dgttrfActivePivotResidual s x k y₀ y₁ y₂ ∧
    dgttrfActiveNextResidual s x k hk y₀ y₁ y₂ =
      dgttrfUpperNextResidual t q k hk y₁ y₂ +
        t.dl k * dgttrfActivePivotResidual s x k y₀ y₁ y₂ +
        (t.dl k * s.d k - s.dl k) * y₀ -
        (q kp - (x kp - t.dl k * x k)) +
        (t.dl k * s.du k + t.d kp - s.d kp) * y₁ := by
  let kp : Fin n := ⟨k.val + 1, hk⟩
  have hkp_ne : kp ≠ k := by
    intro h
    have := Fin.mk.inj h
    simp [kp] at this
  have hk_ne : k ≠ kp := Ne.symm hkp_ne
  dsimp only
  constructor
  · simp [flDGTTRFStepAt, hchoice]
  constructor
  · simp [flDGTTRFStepAt, hchoice]
  constructor
  · simp [dgttrfUpperPivotResidual, dgttrfActivePivotResidual,
      flDGTTRFStepAt, flDGTTRSForwardStepAt, hchoice, hdu2,
      finReplace, kp, hkp_ne, hk_ne]
  · simp only [dgttrfActiveNextResidual, dgttrfUpperNextResidual,
      dgttrfActivePivotResidual]
    simp [flDGTTRFStepAt, flDGTTRSForwardStepAt, hchoice, hdu2,
      finReplace, kp, hkp_ne, hk_ne]
    ring

/-- Literal interchange factor/forward identity with source-row labels.  The
old next source row becomes the finalized bandwidth-two pivot row, while the
old pivot source row travels to the next position.  The traveling residual
also receives the one-operation generated-fill residual. -/
theorem flDGTTRF_swap_combined_source_row_identity (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (x : Fin n → ℝ) (k : Fin n)
    (hk : k.val + 1 < n) (hchoice : ¬ |s.d k| ≥ |s.dl k|)
    (hdu2 : s.du2 k = 0) (y₀ y₁ y₂ : ℝ) :
    let kp : Fin n := ⟨k.val + 1, hk⟩
    let t := flDGTTRFStepAt fp s k hk
    let q := flDGTTRSForwardStepAt fp t x k hk
    t.perm k = s.perm kp ∧
    t.perm kp = s.perm k ∧
    dgttrfUpperPivotResidual t q k y₀ y₁ y₂ =
      dgttrfActiveNextResidual s x k hk y₀ y₁ y₂ ∧
    dgttrfActivePivotResidual s x k y₀ y₁ y₂ =
      dgttrfUpperNextResidual t q k hk y₁ y₂ +
        t.dl k * dgttrfActiveNextResidual s x k hk y₀ y₁ y₂ +
        (t.dl k * s.dl k - s.d k) * y₀ -
        (q kp - (x k - t.dl k * x kp)) +
        (t.dl k * s.d kp + t.d kp - s.du k) * y₁ +
        (t.dl k * s.du kp + t.du kp) * y₂ := by
  let kp : Fin n := ⟨k.val + 1, hk⟩
  have hkp_ne : kp ≠ k := by
    intro h
    have := Fin.mk.inj h
    simp [kp] at this
  have hk_ne : k ≠ kp := Ne.symm hkp_ne
  dsimp only
  constructor
  · simp [flDGTTRFStepAt, hchoice, finSwap, kp, hkp_ne, hk_ne]
  constructor
  · simp [flDGTTRFStepAt, hchoice, finSwap, kp, hkp_ne, hk_ne]
  constructor
  · simp [dgttrfUpperPivotResidual, dgttrfActiveNextResidual,
      flDGTTRFStepAt, flDGTTRSForwardStepAt, hchoice, hdu2,
      finReplace, kp, hkp_ne, hk_ne]
  · simp only [dgttrfActiveNextResidual, dgttrfUpperNextResidual,
      dgttrfActivePivotResidual]
    simp [flDGTTRFStepAt, flDGTTRSForwardStepAt, hchoice, hdu2,
      finReplace, kp, hkp_ne, hk_ne]
    ring

/-- The three observable arithmetic terms in the literal no-interchange
source-row identity have exactly the local `u`, `gamma_2`, and `gamma_2`
bounds supplied by the executed divide, factor update, and forward update. -/
theorem flDGTTRF_noSwap_combined_local_error_bounds (fp : FPModel) {n : ℕ}
    (hval2 : gammaValid fp 2) (s : DGTTRFData n) (x : Fin n → ℝ)
    (k : Fin n) (hk : k.val + 1 < n)
    (hchoice : |s.d k| ≥ |s.dl k|) (hpivot : s.d k ≠ 0) :
    let kp : Fin n := ⟨k.val + 1, hk⟩
    let t := flDGTTRFStepAt fp s k hk
    let q := flDGTTRSForwardStepAt fp t x k hk
    |t.dl k * s.d k - s.dl k| ≤ fp.u * |s.dl k| ∧
    |t.dl k * s.du k + t.d kp - s.d kp| ≤
      gamma fp 2 * (|s.d kp| + |t.dl k| * |s.du k|) ∧
    |q kp - (x kp - t.dl k * x k)| ≤
      gamma fp 2 * (|x kp| + |t.dl k| * |x k|) := by
  let kp : Fin n := ⟨k.val + 1, hk⟩
  let t := flDGTTRFStepAt fp s k hk
  let q := flDGTTRSForwardStepAt fp t x k hk
  dsimp only
  constructor
  · have h := flDGTTRF_multiplier_pivot_residual_le_u fp
      (s.dl k) (s.d k) hpivot
    simpa [t, flDGTTRFStepAt, hchoice, flDGTTRFMultiplier] using h
  constructor
  · have h := flDGTTRF_noSwap_diag_residual_le_gamma2 fp hval2
      (s.d kp) (flDGTTRFMultiplier fp (s.dl k) (s.d k)) (s.du k)
    simpa [t, flDGTTRFStepAt, hchoice, flDGTTRFMultiplier,
      flDGTTRFUpdate] using h
  · have h := flDGTTRS_forward_local_residual_le_gamma2 fp hval2
      (x kp) (flDGTTRFMultiplier fp (s.dl k) (s.d k)) (x k)
    simpa [t, q, flDGTTRFStepAt, flDGTTRSForwardStepAt, hchoice,
      flDGTTRFMultiplier, flDGTTRFUpdate, finReplace, kp] using h

/-- The four observable arithmetic terms in the literal interchange
source-row identity have local `u`, `gamma_2`, `u`, and `gamma_2` bounds.
This includes the generated-fill cancellation that has no analogue in the
no-interchange branch. -/
theorem flDGTTRF_swap_combined_local_error_bounds (fp : FPModel) {n : ℕ}
    (hval2 : gammaValid fp 2) (s : DGTTRFData n) (x : Fin n → ℝ)
    (k : Fin n) (hk : k.val + 1 < n)
    (hchoice : ¬ |s.d k| ≥ |s.dl k|) (hpivot : s.dl k ≠ 0) :
    let kp : Fin n := ⟨k.val + 1, hk⟩
    let t := flDGTTRFStepAt fp s k hk
    let q := flDGTTRSForwardStepAt fp t x k hk
    |t.dl k * s.dl k - s.d k| ≤ fp.u * |s.d k| ∧
    |t.dl k * s.d kp + t.d kp - s.du k| ≤
      gamma fp 2 * (|s.du k| + |t.dl k| * |s.d kp|) ∧
    |t.dl k * s.du kp + t.du kp| ≤
      fp.u * |t.dl k| * |s.du kp| ∧
    |q kp - (x k - t.dl k * x kp)| ≤
      gamma fp 2 * (|x k| + |t.dl k| * |x kp|) := by
  let kp : Fin n := ⟨k.val + 1, hk⟩
  let t := flDGTTRFStepAt fp s k hk
  let q := flDGTTRSForwardStepAt fp t x k hk
  dsimp only
  constructor
  · have h := flDGTTRF_multiplier_pivot_residual_le_u fp
      (s.d k) (s.dl k) hpivot
    simpa [t, flDGTTRFStepAt, hchoice, flDGTTRFMultiplier] using h
  constructor
  · have h := flDGTTRF_swap_diag_residual_le_gamma2 fp hval2
      (s.du k) (flDGTTRFMultiplier fp (s.d k) (s.dl k)) (s.d kp)
    simpa [t, flDGTTRFStepAt, hchoice, flDGTTRFMultiplier,
      flDGTTRFUpdate] using h
  constructor
  · have h := flDGTTRF_swap_fill_residual_le_u fp
      (flDGTTRFMultiplier fp (s.d k) (s.dl k)) (s.du kp)
    simpa [t, flDGTTRFStepAt, hchoice, flDGTTRFMultiplier,
      flDGTTRFNegMul] using h
  · have h := flDGTTRS_forward_local_residual_le_gamma2 fp hval2
      (x k) (flDGTTRFMultiplier fp (s.d k) (s.dl k)) (x kp)
    simpa [t, q, flDGTTRFStepAt, flDGTTRSForwardStepAt, hchoice,
      flDGTTRFMultiplier, flDGTTRFUpdate, finReplace, kp] using h

/-- Once stage `j` has written multiplier slot `j`, all later prefixes of the
literal factor run retain that slot verbatim. -/
theorem flDGTTRFRun_dl_eq_after_stage (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (j : Fin n) :
    ∀ steps : ℕ, j.val < steps →
      (flDGTTRFRun fp n T steps).dl j =
        (flDGTTRFRun fp n T (j.val + 1)).dl j := by
  intro steps
  induction steps with
  | zero =>
      intro h
      omega
  | succ steps ih =>
      intro hj
      by_cases heq : j.val = steps
      · subst steps
        rfl
      · have hjlt : j.val < steps := by omega
        simp only [flDGTTRFRun]
        split
        · rename_i hstep
          have hne : j ≠
              (⟨steps, Nat.lt_trans (Nat.lt_succ_self steps) hstep⟩ : Fin n) := by
            intro h
            exact heq (Fin.mk.inj h)
          rw [flDGTTRFStepAt_dl_of_ne fp _ _ _ hstep hne]
          exact ih hjlt
        · exact ih hjlt

/-- Once stage `j` has recorded its adjacent-pivot decision, all later factor
prefixes retain that decision verbatim. -/
theorem flDGTTRFRun_ipiv_eq_after_stage (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (j : Fin n) :
    ∀ steps : ℕ, j.val < steps →
      (flDGTTRFRun fp n T steps).ipiv j =
        (flDGTTRFRun fp n T (j.val + 1)).ipiv j := by
  intro steps
  induction steps with
  | zero =>
      intro h
      omega
  | succ steps ih =>
      intro hj
      by_cases heq : j.val = steps
      · subst steps
        rfl
      · have hjlt : j.val < steps := by omega
        simp only [flDGTTRFRun]
        split
        · rename_i hstep
          have hne : j ≠
              (⟨steps, Nat.lt_trans (Nat.lt_succ_self steps) hstep⟩ : Fin n) := by
            intro h
            exact heq (Fin.mk.inj h)
          rw [flDGTTRFStepAt_ipiv_of_ne fp _ _ _ hstep hne]
          exact ih hjlt
        · exact ih hjlt

/-- A DGTTRS forward stage depends on factor storage only through its own
pivot bit and stored multiplier. -/
theorem flDGTTRSForwardStepAt_eq_of_pivot_data (fp : FPModel) {n : ℕ}
    (s t : DGTTRFData n) (x : Fin n → ℝ) (k : Fin n)
    (hk : k.val + 1 < n) (hdl : s.dl k = t.dl k)
    (hbit : s.ipiv k = t.ipiv k) :
    flDGTTRSForwardStepAt fp s x k hk =
      flDGTTRSForwardStepAt fp t x k hk := by
  simp [flDGTTRSForwardStepAt, hdl, hbit]

/-- The completed factor state and the immediate post-stage factor state have
identical pivot data at the executed stage. -/
theorem flDGTTRF_final_pivot_data_eq_stage (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (k : ℕ) (hk : k + 1 < n) :
    let i : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
    let s := flDGTTRFRun fp n T k
    let t := flDGTTRFStepAt fp s i hk
    (flDGTTRF fp n T).dl i = t.dl i ∧
      (flDGTTRF fp n T).ipiv i = t.ipiv i := by
  intro i s t
  have hifinal : i.val < n - 1 := by simp [i]; omega
  have hdl := flDGTTRFRun_dl_eq_after_stage fp n T i (n - 1) hifinal
  have hbit := flDGTTRFRun_ipiv_eq_after_stage fp n T i (n - 1) hifinal
  have hnext : flDGTTRFRun fp n T (i.val + 1) = t := by
    simp [flDGTTRFRun, i, hk, s, t]
  constructor
  · simpa [flDGTTRF, hnext] using hdl
  · simpa [flDGTTRF, hnext] using hbit

/-- Consequently, the literal forward stage executed from the completed
DGTTRF state is definitionally the same update used by the one-stage
factor/forward telescope at the immediate post-stage state. -/
theorem flDGTTRSForwardStepAt_final_eq_factor_stage (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
    (k : ℕ) (hk : k + 1 < n) :
    let i : Fin n := ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩
    let s := flDGTTRFRun fp n T k
    let t := flDGTTRFStepAt fp s i hk
    flDGTTRSForwardStepAt fp (flDGTTRF fp n T) x i hk =
      flDGTTRSForwardStepAt fp t x i hk := by
  intro i s t
  obtain ⟨hdl, hbit⟩ :=
    flDGTTRF_final_pivot_data_eq_stage fp n T k hk
  exact flDGTTRSForwardStepAt_eq_of_pivot_data fp
    (flDGTTRF fp n T) t x i hk hdl hbit

/-- Every multiplier produced by an executed stage of the literal DGTTRF run
has magnitude at most `1 + u` in the final stored factor data.  The theorem is
global over the actual run but uses only the operational nonzero-pivot
condition; it introduces no residual or target backward-error premise. -/
theorem flDGTTRF_dl_abs_le_one_add_u (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ)
    (hpiv : DGTTRFStepPivotsNonzero fp n T)
    (j : Fin n) (hj : j.val + 1 < n) :
    |(flDGTTRF fp n T).dl j| ≤ 1 + fp.u := by
  let s := flDGTTRFRun fp n T j.val
  have hpivot :
      if |s.d j| ≥ |s.dl j| then s.d j ≠ 0 else s.dl j ≠ 0 := by
    simpa [s] using hpiv j.val hj
  have hstage := flDGTTRFStepAt_dl_abs_le_one_add_u fp s j hj hpivot
  have hsucc :
      (flDGTTRFRun fp n T (j.val + 1)).dl j =
        (flDGTTRFStepAt fp s j hj).dl j := by
    simp [flDGTTRFRun, hj, s]
  have hjfinal : j.val < n - 1 := by omega
  have hstable := flDGTTRFRun_dl_eq_after_stage fp n T j (n - 1) hjfinal
  rw [flDGTTRF, hstable, hsucc]
  exact hstage

/-! ## Zero-reflection of the actual interleaved forward sweep -/

private theorem fp_fl_mul_zero_right (fp : FPModel) (x : ℝ) :
    fp.fl_mul x 0 = 0 := by
  obtain ⟨δ, _hδ, hfl⟩ := fp.model_mul x 0
  simpa using hfl

/-- One adjacent-pivot DGTTRS forward stage cannot map a nonzero vector to the
zero vector.  This is an exact structural fact: both branches retain one old
entry and update the other, while `skipZeroSubFP` copies `x - 0`. -/
theorem flDGTTRSForwardStepAt_eq_zero_imp {n : ℕ} (fp : FPModel)
    (s : DGTTRFData n) (x : Fin n → ℝ) (k : Fin n)
    (hk : k.val + 1 < n)
    (hzero : flDGTTRSForwardStepAt fp s x k hk = 0) :
    x = 0 := by
  let kp : Fin n := ⟨k.val + 1, hk⟩
  have hkp_ne : kp ≠ k := by
    intro h
    have := Fin.mk.inj h
    omega
  have hk_ne : k ≠ kp := Ne.symm hkp_ne
  cases hbit : s.ipiv k with
  | false =>
      have hzero' :
          finReplace x kp
            ((skipZeroSubFP fp).fl_sub (x kp)
              ((skipZeroSubFP fp).fl_mul (s.dl k) (x k))) = 0 := by
        simpa [flDGTTRSForwardStepAt, hbit, kp] using hzero
      have hxk : x k = 0 := by
        have h := congrFun hzero' k
        rw [finReplace_of_ne _ _ _ _ hk_ne] at h
        exact h
      have hxkp : x kp = 0 := by
        have h := congrFun hzero' kp
        rw [finReplace_same] at h
        rw [hxk, fp_fl_mul_zero_right, skipZeroSubFP_fl_sub_zero] at h
        exact h
      funext i
      by_cases hik : i = k
      · subst i
        exact hxk
      by_cases hip : i = kp
      · subst i
        exact hxkp
      have h := congrFun hzero' i
      rw [finReplace_of_ne _ _ _ _ hip] at h
      exact h
  | true =>
      have hzero' :
          finReplace (finReplace x k (x kp)) kp
            ((skipZeroSubFP fp).fl_sub (x k)
              ((skipZeroSubFP fp).fl_mul (s.dl k) (x kp))) = 0 := by
        simpa [flDGTTRSForwardStepAt, hbit, kp] using hzero
      have hxkp : x kp = 0 := by
        have h := congrFun hzero' k
        rw [finReplace_of_ne _ _ _ _ hk_ne, finReplace_same] at h
        exact h
      have hxk : x k = 0 := by
        have h := congrFun hzero' kp
        rw [finReplace_same] at h
        rw [hxkp, fp_fl_mul_zero_right, skipZeroSubFP_fl_sub_zero] at h
        exact h
      funext i
      by_cases hik : i = k
      · subst i
        exact hxk
      by_cases hip : i = kp
      · subst i
        exact hxkp
      have h := congrFun hzero' i
      rw [finReplace_of_ne _ _ _ _ hip,
        finReplace_of_ne _ _ _ _ hik] at h
      exact h

/-- Any finite prefix of the interleaved forward sweep reflects the zero
vector. -/
theorem flDGTTRSForwardRun_eq_zero_imp (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (z : Fin n → ℝ) :
    ∀ steps : ℕ, flDGTTRSForwardRun fp s z steps = 0 → z = 0 := by
  intro steps
  induction steps with
  | zero =>
      intro h
      exact h
  | succ steps ih =>
      intro h
      simp only [flDGTTRSForwardRun] at h
      split at h
      · rename_i hstep
        exact ih (flDGTTRSForwardStepAt_eq_zero_imp fp s
          (flDGTTRSForwardRun fp s z steps)
          ⟨steps, Nat.lt_trans (Nat.lt_succ_self steps) hstep⟩ hstep h)
      · exact ih h

/-- The completed DGTTRS forward sweep reflects zero. -/
theorem flDGTTRSForward_eq_zero_imp (fp : FPModel) {n : ℕ}
    (s : DGTTRFData n) (z : Fin n → ℝ)
    (hzero : flDGTTRSForward fp s z = 0) : z = 0 := by
  exact flDGTTRSForwardRun_eq_zero_imp fp s z (n - 1) hzero

/-- Under actual no-breakdown, a zero output of the complete DGTTRF/DGTTRS
solve can only come from a zero right-hand side.  The bandwidth-two backward
certificate first forces the intermediate forward-sweep vector to vanish;
the preceding structural theorem then recovers the original right-hand side. -/
theorem flDGTTRS_eq_zero_imp_rhs_eq_zero (fp : FPModel) (n : ℕ)
    (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hnb : DGTTRFNoBreakdown fp T)
    (hval3 : gammaValid fp 3)
    (hy : flDGTTRS fp n T z = 0) : z = 0 := by
  let s := flDGTTRF fp n T
  let q := flDGTTRSForward fp s z
  let y := flDGTTRSBackward fp s q
  have hy' : y = 0 := by
    simpa [flDGTTRS, s, q, y] using hy
  have hdiag : ∀ i : Fin n, s.d i ≠ 0 := by
    simpa [s] using hnb.2
  obtain ⟨DeltaU, _hDeltaU, hback⟩ :=
    flDGTTRSBackward_backward_error fp s q hdiag hval3
  have hq : q = 0 := by
    funext i
    have hi : ∑ j : Fin n, (dgttrfU s i j + DeltaU i j) * y j = q i := by
      simpa [y] using hback i
    rw [hy'] at hi
    simpa using hi.symm
  exact flDGTTRSForward_eq_zero_imp fp s z (by simpa [q] using hq)

/-! ## Canonical source-residual correction -/

/-- Observable source residual of a computed middle solution. -/
noncomputable def dgttrsSourceResidual {n : ℕ}
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (i : Fin n) : ℝ :=
  z i - ∑ j : Fin n, T i j * y j

/-- Squared Euclidean denominator used by the canonical rank-one correction. -/
noncomputable def dgttrsSolutionSq {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, y j ^ 2

/-- One-norm of the computed solution, used only to state the exact
a-posteriori norm bridge below. -/
noncomputable def dgttrsSolutionAbsSum {n : ℕ} (y : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, |y j|

/-- Canonical rank-one source correction.  For nonzero `y`, row `i` is the
residual `r_i` times `yᵀ/(yᵀy)`.  If `y=0`, the correction is zero; the actual
solver theorem proves that this branch necessarily has `z=0`. -/
noncomputable def dgttrsResidualCorrection {n : ℕ}
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  if _hy : y = 0 then 0
  else fun i j => dgttrsSourceResidual T z y i * y j / dgttrsSolutionSq y

/-- Nonnegative entrywise budget for the canonical correction. -/
noncomputable def dgttrsResidualBudget {n : ℕ}
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => |dgttrsResidualCorrection T z y i j|

private theorem dgttrsSolutionSq_pos_of_ne_zero {n : ℕ} (y : Fin n → ℝ)
    (hy : y ≠ 0) : 0 < dgttrsSolutionSq y := by
  have hex : ∃ i, y i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  unfold dgttrsSolutionSq
  obtain ⟨i, hi⟩ := hex
  refine Finset.sum_pos' (fun j _ => sq_nonneg (y j)) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg (y i)).lt_of_ne (Ne.symm (pow_ne_zero 2 hi))⟩

/-- For a nonzero solution, the budget has the explicit a posteriori formula
`|r_i| |y_j| / (yᵀy)`. -/
theorem dgttrsResidualBudget_eq_of_ne_zero {n : ℕ}
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (hy : y ≠ 0)
    (i j : Fin n) :
    dgttrsResidualBudget T z y i j =
      |dgttrsSourceResidual T z y i| * |y j| / dgttrsSolutionSq y := by
  have hsq : 0 ≤ dgttrsSolutionSq y :=
    (dgttrsSolutionSq_pos_of_ne_zero y hy).le
  simp [dgttrsResidualBudget, dgttrsResidualCorrection, hy,
    abs_div, abs_mul, abs_of_nonneg hsq]

/-- Quantitative norm theorem for the canonical correction.

No lower bound on `y` is needed: the residual is homogeneous in `y`, and the
factor `yᵀy` in the denominator cancels by Cauchy--Schwarz.  What *is* needed
is a genuine global residual estimate.  In particular, if

`|z_i-(Ty)_i| ≤ c ||T||∞ ||y||₁`,

then the explicit rank-one correction has norm at most `n*c*||T||∞`.  The
literal local DGTTRF/DGTTRS lemmas currently do not produce this global
residual estimate after consecutive adjacent pivots; that, rather than a
nonzero-solution lower bound, is the remaining arithmetic gate. -/
theorem dgttrsResidualBudget_infNorm_le_n_mul_of_sourceResidual_absSum_bound
    {n : ℕ} (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c)
    (hres : ∀ i : Fin n,
      |dgttrsSourceResidual T z y i| ≤
        c * infNorm T * dgttrsSolutionAbsSum y) :
    infNorm (dgttrsResidualBudget T z y) ≤
      (n : ℝ) * c * infNorm T := by
  by_cases hy : y = 0
  · subst y
    have hbudget : dgttrsResidualBudget T z (0 : Fin n → ℝ) = 0 := by
      funext i j
      simp [dgttrsResidualBudget, dgttrsResidualCorrection]
    have hnorm0 : infNorm (0 : Fin n → Fin n → ℝ) = 0 := by
      apply le_antisymm
      · apply infNorm_le_of_row_sum_le
        · simp
        · norm_num
      · exact infNorm_nonneg _
    rw [hbudget, hnorm0]
    exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) hc) (infNorm_nonneg T)
  · have hsqpos : 0 < dgttrsSolutionSq y :=
      dgttrsSolutionSq_pos_of_ne_zero y hy
    have hsum_nonneg : 0 ≤ dgttrsSolutionAbsSum y := by
      exact Finset.sum_nonneg (fun j _ => abs_nonneg (y j))
    have hcs :
        dgttrsSolutionAbsSum y ^ 2 ≤ (n : ℝ) * dgttrsSolutionSq y := by
      have h := sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin n))) (f := fun j : Fin n => |y j|)
      simpa [dgttrsSolutionAbsSum, dgttrsSolutionSq, Finset.card_univ,
        sq_abs] using h
    apply infNorm_le_of_row_sum_le
    · intro i
      have hrow :
          ∑ j : Fin n, |dgttrsResidualBudget T z y i j| =
            |dgttrsSourceResidual T z y i| * dgttrsSolutionAbsSum y /
              dgttrsSolutionSq y := by
        calc
          ∑ j : Fin n, |dgttrsResidualBudget T z y i j|
              = ∑ j : Fin n,
                  (|dgttrsSourceResidual T z y i| * |y j| /
                    dgttrsSolutionSq y) := by
                    apply Finset.sum_congr rfl
                    intro j _
                    have hb : 0 ≤ dgttrsResidualBudget T z y i j := by
                      exact abs_nonneg _
                    rw [abs_of_nonneg hb]
                    exact dgttrsResidualBudget_eq_of_ne_zero T z y hy i j
          _ = (∑ j : Fin n,
                  |dgttrsSourceResidual T z y i| * |y j|) /
                dgttrsSolutionSq y := by rw [Finset.sum_div]
          _ = |dgttrsSourceResidual T z y i| * dgttrsSolutionAbsSum y /
                dgttrsSolutionSq y := by
                  simp only [dgttrsSolutionAbsSum, Finset.mul_sum]
      rw [hrow]
      apply (div_le_iff₀ hsqpos).2
      have hfirst := mul_le_mul_of_nonneg_right (hres i) hsum_nonneg
      have hscale_nonneg : 0 ≤ c * infNorm T :=
        mul_nonneg hc (infNorm_nonneg T)
      calc
        |dgttrsSourceResidual T z y i| * dgttrsSolutionAbsSum y
            ≤ (c * infNorm T * dgttrsSolutionAbsSum y) *
                dgttrsSolutionAbsSum y := hfirst
        _ = (c * infNorm T) * dgttrsSolutionAbsSum y ^ 2 := by ring
        _ ≤ (c * infNorm T) * ((n : ℝ) * dgttrsSolutionSq y) :=
              mul_le_mul_of_nonneg_left hcs hscale_nonneg
        _ = ((n : ℝ) * c * infNorm T) * dgttrsSolutionSq y := by ring
    · exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg n) hc) (infNorm_nonneg T)

/-- The canonical residual correction gives an exact direct middle budget as
soon as the zero-output branch is known to have zero right-hand side.  No
factorization residual, accumulated-lower perturbation, or desired norm bound
is assumed. -/
theorem aasenDirectMiddleBudget_of_canonical_residual {n : ℕ}
    (fp : FPModel) (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ)
    (hzero : y = 0 → z = 0) :
    AasenDirectMiddleBudget fp n T z y
      (dgttrsResidualCorrection T z y)
      (dgttrsResidualBudget T z y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact abs_nonneg _
  · intro i j
    exact le_rfl
  · intro i
    by_cases hy : y = 0
    · have hz : z = 0 := hzero hy
      simp [dgttrsResidualCorrection, hy, hz]
    · have hsqpos : 0 < dgttrsSolutionSq y :=
        dgttrsSolutionSq_pos_of_ne_zero y hy
      have hsqne : dgttrsSolutionSq y ≠ 0 := ne_of_gt hsqpos
      have hcorr :
          ∑ j : Fin n,
              (dgttrsSourceResidual T z y i * y j /
                dgttrsSolutionSq y) * y j =
            dgttrsSourceResidual T z y i := by
        calc
          ∑ j : Fin n,
              (dgttrsSourceResidual T z y i * y j /
                dgttrsSolutionSq y) * y j
              = dgttrsSourceResidual T z y i / dgttrsSolutionSq y *
                  ∑ j : Fin n, y j ^ 2 := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro j _
                    ring
          _ = dgttrsSourceResidual T z y i := by
                simpa [dgttrsSolutionSq] using
                  (div_mul_cancel₀ (dgttrsSourceResidual T z y i) hsqne)
      simp only [dgttrsResidualCorrection, hy, ↓reduceDIte]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, hcorr]
      unfold dgttrsSourceResidual
      ring

/-! ## Row-sparse source-residual correction

The canonical rank-one correction above is convenient, but converting its
Euclidean denominator to an infinity-norm statement loses a factor `n`.  For
the normwise Theorem-11.8 gate there is a sharper exact construction: put the
whole residual of every source row into one column where `|y_j| = ‖y‖∞`.
This is the standard minimum-row-sum correction for the equation
`DeltaT * y = residual` and introduces no dimension loss. -/

/-- A solution coordinate attaining the finite infinity norm. -/
noncomputable def dgttrsMaxSolutionIndex {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℝ) : Fin n :=
  Classical.choose (infNormVec_exists_abs_eq hn y)

/-- The selected solution coordinate really attains `‖y‖∞`. -/
theorem dgttrsMaxSolutionIndex_spec {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℝ) :
    infNormVec y = |y (dgttrsMaxSolutionIndex hn y)| :=
  Classical.choose_spec (infNormVec_exists_abs_eq hn y)

/-- If the solution is nonzero, its selected maximum-magnitude coordinate is
nonzero. -/
theorem dgttrsMaxSolutionIndex_ne_zero_of_ne_zero {n : ℕ} (hn : 0 < n)
    (y : Fin n → ℝ) (hy : y ≠ 0) :
    y (dgttrsMaxSolutionIndex hn y) ≠ 0 := by
  intro hmax
  apply hy
  funext j
  apply abs_eq_zero.mp
  apply le_antisymm
  · calc
      |y j| ≤ infNormVec y := abs_le_infNormVec y j
      _ = |y (dgttrsMaxSolutionIndex hn y)| :=
        dgttrsMaxSolutionIndex_spec hn y
      _ = 0 := by rw [hmax, abs_zero]
  · exact abs_nonneg _

/-- Row-sparse exact source correction.  For nonzero `y`, row `i` has the
single entry `r_i / y_j` in a coordinate `j` attaining `‖y‖∞`. -/
noncomputable def dgttrsSparseResidualCorrection {n : ℕ} (hn : 0 < n)
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  if _hy : y = 0 then 0
  else fun i j =>
    if j = dgttrsMaxSolutionIndex hn y then
      dgttrsSourceResidual T z y i / y (dgttrsMaxSolutionIndex hn y)
    else 0

/-- Nonnegative entrywise budget of the row-sparse correction. -/
noncomputable def dgttrsSparseResidualBudget {n : ℕ} (hn : 0 < n)
    (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => |dgttrsSparseResidualCorrection hn T z y i j|

/-- Exact norm bridge for the row-sparse correction.  A residual estimate in
the natural scale `‖T‖∞ ‖y‖∞` transfers to the correction with no factor of
the dimension. -/
theorem dgttrsSparseResidualBudget_infNorm_le_of_sourceResidual_infNorm_bound
    {n : ℕ} (hn : 0 < n) (T : Fin n → Fin n → ℝ)
    (z y : Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hres : ∀ i : Fin n,
      |dgttrsSourceResidual T z y i| ≤
        c * infNorm T * infNormVec y) :
    infNorm (dgttrsSparseResidualBudget hn T z y) ≤
      c * infNorm T := by
  by_cases hy : y = 0
  · subst y
    have hbudget :
        dgttrsSparseResidualBudget hn T z (0 : Fin n → ℝ) = 0 := by
      funext i j
      simp [dgttrsSparseResidualBudget, dgttrsSparseResidualCorrection]
    rw [hbudget]
    have hnorm0 : infNorm (0 : Fin n → Fin n → ℝ) = 0 := by
      apply le_antisymm
      · apply infNorm_le_of_row_sum_le
        · simp
        · norm_num
      · exact infNorm_nonneg _
    rw [hnorm0]
    exact mul_nonneg hc (infNorm_nonneg T)
  · let jmax := dgttrsMaxSolutionIndex hn y
    have hjmax : y jmax ≠ 0 := by
      simpa [jmax] using
        dgttrsMaxSolutionIndex_ne_zero_of_ne_zero hn y hy
    have hjabs : 0 < |y jmax| := abs_pos.mpr hjmax
    apply infNorm_le_of_row_sum_le
    · intro i
      have hrow :
          (∑ j : Fin n, |dgttrsSparseResidualBudget hn T z y i j|) =
            |dgttrsSourceResidual T z y i| / |y jmax| := by
        calc
          (∑ j : Fin n,
              |dgttrsSparseResidualBudget hn T z y i j|) =
              ∑ j : Fin n, if j = jmax then
                |dgttrsSourceResidual T z y i / y jmax| else 0 := by
            apply Finset.sum_congr rfl
            intro j _hj
            by_cases h : j = jmax <;>
              simp [dgttrsSparseResidualBudget,
                dgttrsSparseResidualCorrection, hy, jmax, h]
          _ = |dgttrsSourceResidual T z y i / y jmax| := by simp
          _ = |dgttrsSourceResidual T z y i| / |y jmax| := abs_div _ _
      rw [hrow]
      apply (div_le_iff₀ hjabs).2
      calc
        |dgttrsSourceResidual T z y i| ≤
            c * infNorm T * infNormVec y := hres i
        _ = (c * infNorm T) * |y jmax| := by
          rw [dgttrsMaxSolutionIndex_spec hn y]
    · exact mul_nonneg hc (infNorm_nonneg T)

/-- The row-sparse residual correction gives an exact direct middle budget.
The zero-output premise is the same operational fact used by the canonical
construction. -/
theorem aasenDirectMiddleBudget_of_sparse_residual {n : ℕ} (hn : 0 < n)
    (fp : FPModel) (T : Fin n → Fin n → ℝ) (z y : Fin n → ℝ)
    (hzero : y = 0 → z = 0) :
    AasenDirectMiddleBudget fp n T z y
      (dgttrsSparseResidualCorrection hn T z y)
      (dgttrsSparseResidualBudget hn T z y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact abs_nonneg _
  · intro i j
    exact le_rfl
  · intro i
    by_cases hy : y = 0
    · have hz : z = 0 := hzero hy
      simp [dgttrsSparseResidualCorrection, hy, hz]
    · let jmax := dgttrsMaxSolutionIndex hn y
      have hjmax : y jmax ≠ 0 := by
        simpa [jmax] using
          dgttrsMaxSolutionIndex_ne_zero_of_ne_zero hn y hy
      have hcorr :
          ∑ j : Fin n,
              dgttrsSparseResidualCorrection hn T z y i j * y j =
            dgttrsSourceResidual T z y i := by
        simp [dgttrsSparseResidualCorrection, hy, jmax, hjmax]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, hcorr]
      unfold dgttrsSourceResidual
      ring

/-! ## Actual DGTTRF/DGTTRS and terminal Aasen endpoints -/

/-- **Corrected operational middle-solve theorem.**  The literal actual
DGTTRF/DGTTRS output always supplies an exact source backward equation with
the explicit canonical residual budget.  This theorem uses only actual
no-breakdown and the `gamma_3` guard needed to certify the bandwidth-two back
solve; it has no `DGTTRFFactorForwardCertificate` premise. -/
theorem higham11_8_actual_dgttrs_operational_middle_budget
    (fp : FPModel) (n : ℕ) (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hnb : DGTTRFNoBreakdown fp T)
    (hval3 : gammaValid fp 3) :
    let y := flDGTTRS fp n T z
    AasenDirectMiddleBudget fp n T z y
      (dgttrsResidualCorrection T z y)
      (dgttrsResidualBudget T z y) := by
  intro y
  apply aasenDirectMiddleBudget_of_canonical_residual
  intro hy
  exact flDGTTRS_eq_zero_imp_rhs_eq_zero fp n T z hnb hval3 (by
    simpa [y] using hy)

/-- **Sharper corrected operational middle-solve theorem.**  The literal
DGTTRF/DGTTRS output also supplies the row-sparse exact source correction.
Unlike the canonical rank-one correction, its infinity norm is controlled
directly by a residual estimate in the natural scale
`‖T‖∞ * ‖y‖∞`, with no dimension loss. -/
theorem higham11_8_actual_dgttrs_sparse_operational_middle_budget
    (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ)
    (hnb : DGTTRFNoBreakdown fp T)
    (hval3 : gammaValid fp 3) :
    let y := flDGTTRS fp n T z
    AasenDirectMiddleBudget fp n T z y
      (dgttrsSparseResidualCorrection hn T z y)
      (dgttrsSparseResidualBudget hn T z y) := by
  intro y
  apply aasenDirectMiddleBudget_of_sparse_residual hn
  intro hy
  exact flDGTTRS_eq_zero_imp_rhs_eq_zero fp n T z hnb hval3 (by
    simpa [y] using hy)

/-- Formal interface discrepancy: the printed `gamma_6` smallness guard alone
does not imply the old accumulated-factor certificate.  The witness is the
executable three-by-three, two-consecutive-pivot trace.  This diagnoses the old
proof interface; it is not a counterexample to the printed `n ≥ 2` theorem. -/
theorem higham11_8_actual_dgttrs_old_factor_forward_interface_not_derivable :
    ¬ (∀ (fp : FPModel) (n : ℕ) (T : Fin n → Fin n → ℝ) (z : Fin n → ℝ),
      gammaValid fp 6 →
      DGTTRFFactorForwardCertificate fp n T z) := by
  intro h
  apply forwardCounter_not_factor_forward_certificate
  exact h forwardCounterFP 3 forwardCounterT forwardCounterZ
    forwardCounter_gammaValid_six

/-- **Theorem 11.8, actual DGTTRF/DGTTRS middle endpoint.**

This corollary feeds the corrected operational certificate into the existing
direct Aasen assembly.  The sole middle-solve quantitative premise is now the
norm of the explicit, executable residual budget itself; there is no hidden
LU-factor product or false coefficient-one forward certificate. -/
theorem higham11_8_aasen_backward_error_direct_of_actual_dgttrs_budget_norm
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (A Pmat : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (k : ℕ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n A)
    (hLhat_cap : ∀ i j : Fin n, |(flAasen fp n A).Lhat i j| ≤ 1)
    (hnb : DGTTRFNoBreakdown fp (flAasen fp n A).That)
    (hBTnorm :
      let T := (flAasen fp n A).That
      let z := fl_forwardSub fp n (flAasen fp n A).Lhat
        (fun i => ∑ j : Fin n, Pmat i j * b j)
      let y := flDGTTRS fp n T z
      infNorm (dgttrsResidualBudget T z y) ≤ gamma fp k * infNorm T)
    (hk : k ≤ 8 * n + 25)
    (hval : gammaValid fp (15 * n + 25)) :
    let Lh := (flAasen fp n A).Lhat
    let Th := (flAasen fp n A).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n Lh rhs
    let y := flDGTTRS fp n Th z
    let DeltaT := dgttrsResidualCorrection Th z y
    let BT := dgttrsResidualBudget Th z y
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w := fl_backSub fp n Uouter y
    let Bfactor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let Bsolve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ Bfactor i j + Bsolve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) ∧
      infNorm DeltaA ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) * infNorm Th := by
  intro Lh Th rhs z y DeltaT BT Uouter w Bfactor Bsolve
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval
  exact higham11_8_aasen_backward_error_direct_of_operational_middle_budget
    fp n hn A Pmat b y DeltaT BT k hsymm hp hLhat_cap
    (higham11_8_actual_dgttrs_operational_middle_budget fp n Th z hnb hval3)
    (by simpa [Th, z, y, BT] using hBTnorm) hk hval

/-- **Theorem 11.8 reduced to the literal source-residual estimate.**

This is the sharpest honest terminal wrapper currently justified by the
executable DGTTRF/DGTTRS development.  It replaces the indirect matrix-budget
premise by the single pathwise scalar estimate that remains to be proved:

`|z_i - (T y)_i| ≤ γ_k ‖T‖∞ ‖y‖∞`.

The row-sparse correction turns that estimate into the required middle
backward-error matrix without an additional factor `n`, and the established
outer Aasen assembly then gives the printed global radius. -/
theorem higham11_8_aasen_backward_error_direct_of_actual_dgttrs_source_residual
    (fp : FPModel) (n : ℕ) (hn : 2 ≤ n)
    (A Pmat : Fin n → Fin n → ℝ) (b : Fin n → ℝ) (k : ℕ)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hp : FlAasenPivots fp n A)
    (hLhat_cap : ∀ i j : Fin n, |(flAasen fp n A).Lhat i j| ≤ 1)
    (hnb : DGTTRFNoBreakdown fp (flAasen fp n A).That)
    (hres :
      let T := (flAasen fp n A).That
      let z := fl_forwardSub fp n (flAasen fp n A).Lhat
        (fun i => ∑ j : Fin n, Pmat i j * b j)
      let y := flDGTTRS fp n T z
      ∀ i : Fin n,
        |dgttrsSourceResidual T z y i| ≤
          gamma fp k * infNorm T * infNormVec y)
    (hk : k ≤ 8 * n + 25)
    (hval : gammaValid fp (15 * n + 25)) :
    let Lh := (flAasen fp n A).Lhat
    let Th := (flAasen fp n A).That
    let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
    let z := fl_forwardSub fp n Lh rhs
    let y := flDGTTRS fp n Th z
    let DeltaT := dgttrsSparseResidualCorrection (by omega) Th z y
    let BT := dgttrsSparseResidualBudget (by omega) Th z y
    let Uouter : Fin n → Fin n → ℝ := fun i j => Lh j i
    let w := fl_backSub fp n Uouter y
    let Bfactor : Fin n → Fin n → ℝ := fun i j =>
      gamma fp (3 * n) *
        ∑ p : Fin n, ∑ q : Fin n, |Lh i p| * |Th p q| * |Lh j q|
    let Bsolve : Fin n → Fin n → ℝ :=
      higham11_15_aasenChainDeltaABound n (gamma fp n) BT Lh Th Uouter
    ∃ DeltaA : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, |DeltaA i j| ≤ Bfactor i j + Bsolve i j) ∧
      (∀ i : Fin n, ∑ j : Fin n, (A i j + DeltaA i j) * w j = rhs i) ∧
      infNorm DeltaA ≤
        ((n - 1 : ℕ) : ℝ) ^ 2 * gamma fp (15 * n + 25) * infNorm Th := by
  intro Lh Th rhs z y DeltaT BT Uouter w Bfactor Bsolve
  have hn0 : 0 < n := by omega
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval
  have hvalk : gammaValid fp k :=
    gammaValid_mono fp (by omega) hval
  have hmiddle : AasenDirectMiddleBudget fp n Th z y DeltaT BT := by
    simpa [DeltaT, BT] using
      (higham11_8_actual_dgttrs_sparse_operational_middle_budget
        fp n hn0 Th z hnb hval3)
  have hBTnorm : infNorm BT ≤ gamma fp k * infNorm Th := by
    have h :=
      dgttrsSparseResidualBudget_infNorm_le_of_sourceResidual_infNorm_bound
        hn0 Th z y (gamma fp k) (gamma_nonneg fp hvalk)
        (by simpa [Th, z, y] using hres)
    simpa [BT] using h
  exact higham11_8_aasen_backward_error_direct_of_operational_middle_budget
    fp n hn A Pmat b y DeltaT BT k hsymm hp hLhat_cap
    hmiddle hBTnorm hk hval

end NumStability.Ch11Closure.AasenAdjacentOperational
