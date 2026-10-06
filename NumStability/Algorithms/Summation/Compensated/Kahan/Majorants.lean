-- Algorithms/Summation/Compensated/Kahan/Majorants.lean

import NumStability.Algorithms.Summation.Compensated.Kahan.LocalCoefficients

namespace NumStability

/-!
# Kahan compensated summation: absolute majorants

This module develops local, prefix-recursive, and input-only absolute
majorants for the Kahan stored sum and retained correction.
-/

/-- Indexed local absolute bound for the retained correction produced by one
Kahan prefix-trace step. -/
theorem kahanTrace_e_abs_le
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    |(kahanTrace fp v i).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          |v i + state.e| := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_abs_le fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Split-input indexed local absolute bound for the retained correction
produced by one Kahan prefix-trace step. -/
theorem kahanTrace_e_abs_le_split
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    let state := kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt)
    |(kahanTrace fp v i).e| ≤
      fp.u * (1 + fp.u) ^ 2 * |state.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|v i| + |state.e|) := by
  dsimp
  simpa [kahanTrace, kahanTrace_deltaWitness] using
    kahanStepDeltaWitness_e_abs_le_split fp (v i)
      (kahanPrefixState fp v i.val (Nat.le_of_lt i.isLt))
      (kahanTrace_deltaWitness fp v i)

/-- Local absolute bound for the stored sum produced by one Kahan step, in
terms of supplied majorants for the previous stored sum and correction. -/
theorem kahanStepDeltaWitness_s_abs_le_inputMajorants
    (fp : FPModel) (x : ℝ) (state : KahanState)
    (w : KahanStepDeltaWitness fp x state) {S E : ℝ}
    (hs : |state.s| ≤ S) (he : |state.e| ≤ E)
    (hS : 0 ≤ S) (hE : 0 ≤ E) :
    |(kahanStepTrace fp x state).s| ≤
      (1 + fp.u) * S + (1 + fp.u) ^ 2 * (|x| + E) := by
  have hdeltaY : |1 + w.deltaY| ≤ 1 + fp.u := by
    calc
      |1 + w.deltaY| ≤ |(1 : ℝ)| + |w.deltaY| :=
        abs_add_le 1 w.deltaY
      _ ≤ 1 + fp.u := by
        exact add_le_add (by norm_num) w.h_deltaY
  have hdeltaS : |1 + w.deltaS| ≤ 1 + fp.u := by
    calc
      |1 + w.deltaS| ≤ |(1 : ℝ)| + |w.deltaS| :=
        abs_add_le 1 w.deltaS
      _ ≤ 1 + fp.u := by
        exact add_le_add (by norm_num) w.h_deltaS
  have hcoef_nonneg : 0 ≤ 1 + fp.u := by
    nlinarith [fp.u_nonneg]
  have hxE_nonneg : 0 ≤ |x| + E := add_nonneg (abs_nonneg _) hE
  have hxe : |x + state.e| ≤ |x| + E :=
    (abs_add_le x state.e).trans (add_le_add (le_refl _) he)
  have hy :
      |(x + state.e) * (1 + w.deltaY)| ≤
        (|x| + E) * (1 + fp.u) := by
    calc
      |(x + state.e) * (1 + w.deltaY)|
          = |x + state.e| * |1 + w.deltaY| := abs_mul _ _
      _ ≤ (|x| + E) * (1 + fp.u) := by
        exact mul_le_mul hxe hdeltaY (abs_nonneg _) hxE_nonneg
  have hinside :
      |state.s + (x + state.e) * (1 + w.deltaY)| ≤
        S + (|x| + E) * (1 + fp.u) := by
    calc
      |state.s + (x + state.e) * (1 + w.deltaY)|
          ≤ |state.s| + |(x + state.e) * (1 + w.deltaY)| :=
        abs_add_le state.s ((x + state.e) * (1 + w.deltaY))
      _ ≤ S + (|x| + E) * (1 + fp.u) := add_le_add hs hy
  have hinside_nonneg :
      0 ≤ S + (|x| + E) * (1 + fp.u) :=
    add_nonneg hS (mul_nonneg hxE_nonneg hcoef_nonneg)
  calc
    |(kahanStepTrace fp x state).s|
        = |(state.s + (x + state.e) * (1 + w.deltaY)) *
            (1 + w.deltaS)| := by
          rw [kahanStepDeltaWitness_s_expanded fp x state w]
    _ = |state.s + (x + state.e) * (1 + w.deltaY)| *
          |1 + w.deltaS| := abs_mul _ _
    _ ≤ (S + (|x| + E) * (1 + fp.u)) * (1 + fp.u) := by
          exact mul_le_mul hinside hdeltaS (abs_nonneg _) hinside_nonneg
    _ = (1 + fp.u) * S + (1 + fp.u) ^ 2 * (|x| + E) := by
          ring

/-- Prefix-recursive majorant for the retained correction in Algorithm 4.2.

The recurrence follows the actual Kahan prefix order.  At each step it uses the
local retained-correction bound in terms of the previous stored sum, the current
input, and the previous correction majorant. -/
noncomputable def kahanCorrectionAbsMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    (k : ℕ) → k ≤ n → ℝ
  | 0, _hk => 0
  | k + 1, hk =>
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev
      fp.u * (1 + fp.u) ^ 2 * |prev.s| +
        fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
          (|v idx| + kahanCorrectionAbsMajorant fp v k hprev)

/-- The retained-correction prefix majorant is nonnegative. -/
theorem kahanCorrectionAbsMajorant_nonneg
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      0 ≤ kahanCorrectionAbsMajorant fp v k hk
  | 0, _hk => by
      simp [kahanCorrectionAbsMajorant]
  | k + 1, hk => by
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev
      have hih := kahanCorrectionAbsMajorant_nonneg fp v k hprev
      have hc1 : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
        exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
      have hc2 : 0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
        exact mul_nonneg hc1 (by nlinarith [fp.u_nonneg])
      dsimp [kahanCorrectionAbsMajorant]
      exact add_nonneg
        (mul_nonneg hc1 (abs_nonneg _))
        (mul_nonneg hc2 (add_nonneg (abs_nonneg _) hih))

/-- All-prefix retained-correction recurrence bound for Algorithm 4.2.

This is the prefix-level closure of the local `e` bound.  The majorant still
mentions actual stored sums; the coupled input-only majorant below supplies the
stored-sum-free replacement used by the remaining Goldberg/Knuth coefficient
recursion route. -/
theorem kahanPrefixState_e_abs_le_correctionMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      |(kahanPrefixState fp v k hk).e| ≤
        kahanCorrectionAbsMajorant fp v k hk
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero,
        kahanCorrectionAbsMajorant]
  | k + 1, hk => by
      have hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanPrefixState fp v k hprev
      have hih := kahanPrefixState_e_abs_le_correctionMajorant fp v k hprev
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prev := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hstep :
          |(kahanStep fp (v idx) prev).e| ≤
            fp.u * (1 + fp.u) ^ 2 * |prev.s| +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + |prev.e|) := by
        simpa [kahanStep, KahanStepTrace.nextState] using
          kahanStepDeltaWitness_e_abs_le_split fp (v idx) prev
            (kahanStepTrace_deltaWitness fp (v idx) prev)
      have hcoef_nonneg :
          0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
        exact mul_nonneg
          (mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u)))
          (by nlinarith [fp.u_nonneg])
      have htail :
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
              (|v idx| + |prev.e|) ≤
            fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
              (|v idx| + kahanCorrectionAbsMajorant fp v k hprev) := by
        exact mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hih)
          hcoef_nonneg
      calc
        |(kahanPrefixState fp v (k + 1) hk).e|
            = |(kahanStep fp (v idx) prev).e| := by rw [hfoldPrefix]
        _ ≤ fp.u * (1 + fp.u) ^ 2 * |prev.s| +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + |prev.e|) := hstep
        _ ≤ fp.u * (1 + fp.u) ^ 2 * |prev.s| +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + kahanCorrectionAbsMajorant fp v k hprev) := by
            exact add_le_add (le_refl _) htail
        _ = kahanCorrectionAbsMajorant fp v (k + 1) hk := by
            rfl

/-- Coupled input-only majorants for the stored Kahan sum and retained
correction.

The `s` and `e` fields are no longer actual Kahan quantities.  They are
recursive nonnegative bounds depending only on previous majorants and source
input magnitudes.  The `e` recurrence is the previous correction majorant with
the actual stored-sum term replaced by the stored-sum majorant. -/
noncomputable def kahanInputAbsMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    (k : ℕ) → k ≤ n → KahanState
  | 0, _hk => { s := 0, e := 0 }
  | k + 1, hk =>
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanInputAbsMajorant fp v k hprev
      { s := (1 + fp.u) * prev.s +
          (1 + fp.u) ^ 2 * (|v idx| + prev.e)
        e := fp.u * (1 + fp.u) ^ 2 * prev.s +
          fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
            (|v idx| + prev.e) }

/-- The coupled input-only Kahan majorants are nonnegative. -/
theorem kahanInputAbsMajorant_nonneg
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      0 ≤ (kahanInputAbsMajorant fp v k hk).s ∧
        0 ≤ (kahanInputAbsMajorant fp v k hk).e
  | 0, _hk => by
      simp [kahanInputAbsMajorant]
  | k + 1, hk => by
      let hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prev := kahanInputAbsMajorant fp v k hprev
      have hih := kahanInputAbsMajorant_nonneg fp v k hprev
      have hu1_nonneg : 0 ≤ 1 + fp.u := by nlinarith [fp.u_nonneg]
      have hu1_sq_nonneg : 0 ≤ (1 + fp.u) ^ 2 := sq_nonneg (1 + fp.u)
      have hc1 : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
        exact mul_nonneg fp.u_nonneg hu1_sq_nonneg
      have hc2 : 0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
        exact mul_nonneg hc1 (by nlinarith [fp.u_nonneg])
      have htail : 0 ≤ |v idx| + prev.e :=
        add_nonneg (abs_nonneg _) hih.2
      dsimp [kahanInputAbsMajorant]
      constructor
      · exact add_nonneg
          (mul_nonneg hu1_nonneg hih.1)
          (mul_nonneg hu1_sq_nonneg htail)
      · exact add_nonneg
          (mul_nonneg hc1 hih.1)
          (mul_nonneg hc2 htail)

/-- All-prefix input-only bounds for Algorithm 4.2's stored sum and retained
correction.

This closes the C4.5 dependency that removes actual stored-sum terms from the
retained-correction recurrence.  It is still a recursive majorant substrate,
not the final Goldberg/Knuth `mu_i` witness construction. -/
theorem kahanPrefixState_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n),
      |(kahanPrefixState fp v k hk).s| ≤
          (kahanInputAbsMajorant fp v k hk).s ∧
        |(kahanPrefixState fp v k hk).e| ≤
          (kahanInputAbsMajorant fp v k hk).e
  | 0, _hk => by
      simp [kahanPrefixState, KahanState.zero, kahanInputAbsMajorant]
  | k + 1, hk => by
      have hprev : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      let idx : Fin n := ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩
      let prevState := kahanPrefixState fp v k hprev
      let prevMaj := kahanInputAbsMajorant fp v k hprev
      have hih := kahanPrefixState_abs_le_inputMajorant fp v k hprev
      have hmaj_nonneg := kahanInputAbsMajorant_nonneg fp v k hprev
      have hfoldPrefix :
          kahanPrefixState fp v (k + 1) hk =
            kahanStep fp (v idx) prevState := by
        unfold kahanPrefixState
        rw [Fin.foldl_succ_last]
        rfl
      have hs_step :
          |(kahanStep fp (v idx) prevState).s| ≤
            (1 + fp.u) * prevMaj.s +
              (1 + fp.u) ^ 2 * (|v idx| + prevMaj.e) := by
        simpa [kahanStep, KahanStepTrace.nextState, prevState, prevMaj] using
          kahanStepDeltaWitness_s_abs_le_inputMajorants
            fp (v idx) prevState
            (kahanStepTrace_deltaWitness fp (v idx) prevState)
            hih.1 hih.2 hmaj_nonneg.1 hmaj_nonneg.2
      have he_step :
          |(kahanStep fp (v idx) prevState).e| ≤
            fp.u * (1 + fp.u) ^ 2 * prevMaj.s +
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + prevMaj.e) := by
        have hlocal :
            |(kahanStep fp (v idx) prevState).e| ≤
              fp.u * (1 + fp.u) ^ 2 * |prevState.s| +
                fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                  (|v idx| + |prevState.e|) := by
          simpa [kahanStep, KahanStepTrace.nextState] using
            kahanStepDeltaWitness_e_abs_le_split fp (v idx) prevState
              (kahanStepTrace_deltaWitness fp (v idx) prevState)
        have hc1 : 0 ≤ fp.u * (1 + fp.u) ^ 2 := by
          exact mul_nonneg fp.u_nonneg (sq_nonneg (1 + fp.u))
        have hc2 : 0 ≤ fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) := by
          exact mul_nonneg hc1 (by nlinarith [fp.u_nonneg])
        have hfirst :
            fp.u * (1 + fp.u) ^ 2 * |prevState.s| ≤
              fp.u * (1 + fp.u) ^ 2 * prevMaj.s :=
          mul_le_mul_of_nonneg_left hih.1 hc1
        have hsecond :
            fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + |prevState.e|) ≤
              fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                (|v idx| + prevMaj.e) :=
          mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hih.2) hc2
        exact hlocal.trans (add_le_add hfirst hsecond)
      constructor
      · calc
          |(kahanPrefixState fp v (k + 1) hk).s|
              = |(kahanStep fp (v idx) prevState).s| := by rw [hfoldPrefix]
          _ ≤ (1 + fp.u) * prevMaj.s +
                (1 + fp.u) ^ 2 * (|v idx| + prevMaj.e) := hs_step
          _ = (kahanInputAbsMajorant fp v (k + 1) hk).s := by rfl
      · calc
          |(kahanPrefixState fp v (k + 1) hk).e|
              = |(kahanStep fp (v idx) prevState).e| := by rw [hfoldPrefix]
          _ ≤ fp.u * (1 + fp.u) ^ 2 * prevMaj.s +
                fp.u * (1 + fp.u) ^ 2 * (2 + fp.u) *
                  (|v idx| + prevMaj.e) := he_step
          _ = (kahanInputAbsMajorant fp v (k + 1) hk).e := by rfl

/-- Stored-sum projection of
`kahanPrefixState_abs_le_inputMajorant`. -/
theorem kahanPrefixState_s_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    |(kahanPrefixState fp v k hk).s| ≤
      (kahanInputAbsMajorant fp v k hk).s :=
  (kahanPrefixState_abs_le_inputMajorant fp v k hk).1

/-- Retained-correction projection of
`kahanPrefixState_abs_le_inputMajorant`. -/
theorem kahanPrefixState_e_abs_le_inputMajorant
    (fp : FPModel) {n : ℕ} (v : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    |(kahanPrefixState fp v k hk).e| ≤
      (kahanInputAbsMajorant fp v k hk).e :=
  (kahanPrefixState_abs_le_inputMajorant fp v k hk).2

end NumStability
