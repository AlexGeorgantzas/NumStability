import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.LinearOperators.MatrixPowers.Spijker.Rational
import NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations
import NumStability.Source.Higham.Chapter28.Section01.HilbertConditioning.HilbertCondition

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28HilbertCondition under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section

namespace NumStability

open Filter Asymptotics Finset

open scoped Topology BigOperators

private theorem sqrtTwo_pow_sq (k : ℕ) :
    ((Real.sqrt 2 : ℝ) ^ k) ^ 2 = 2 ^ k := by
  rw [← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem hilbertCentralDelannoy_eq_sum_sq (n : ℕ) :
    hilbertCentralDelannoy n =
      ∑ k ∈ Finset.range (n + 1),
        ((Nat.choose n k : ℝ) * (Real.sqrt 2 : ℝ) ^ k) ^ 2 := by
  unfold hilbertCentralDelannoy
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_pow, sqrtTwo_pow_sq]

theorem hilbertCentralDelannoy_upper (n : ℕ) :
    hilbertCentralDelannoy n ≤ (1 + Real.sqrt 2) ^ (2 * n) := by
  rw [hilbertCentralDelannoy_eq_sum_sq]
  calc
    (∑ k ∈ Finset.range (n + 1),
        ((Nat.choose n k : ℝ) * (Real.sqrt 2 : ℝ) ^ k) ^ 2) ≤
        (∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * (Real.sqrt 2 : ℝ) ^ k) ^ 2 := by
      exact Finset.sum_sq_le_sq_sum_of_nonneg (fun k _ => mul_nonneg (by positivity) (by positivity))
    _ = (1 + Real.sqrt 2) ^ (2 * n) := by
      rw [hilbertCentralDelannoy_sum_model]
      simpa [mul_comm] using
        (pow_mul (1 + Real.sqrt 2 : ℝ) n 2).symm

theorem hilbertCentralDelannoy_lower (n : ℕ) :
    (1 + Real.sqrt 2) ^ (2 * n) ≤ (n + 1 : ℝ) * hilbertCentralDelannoy n := by
  rw [hilbertCentralDelannoy_eq_sum_sq]
  have hp : ((1 + Real.sqrt 2) ^ n) ^ 2 =
      (1 + Real.sqrt 2) ^ (2 * n) := by
    simpa [mul_comm] using
      (pow_mul (1 + Real.sqrt 2 : ℝ) n 2).symm
  rw [← hp]
  have h := sq_sum_le_card_mul_sum_sq
    (s := Finset.range (n + 1))
    (f := fun k : ℕ => (Nat.choose n k : ℝ) * (Real.sqrt 2 : ℝ) ^ k)
  rw [hilbertCentralDelannoy_sum_model] at h
  simpa [Finset.card_range, Nat.cast_add, Nat.cast_one] using h

private theorem log_nat_succ_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (n + 1 : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have haff : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hsmall : Tendsto
      (fun n : ℕ => Real.log (n + 1 : ℝ) / (n + 1 : ℝ))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using
      (Real.isLittleO_log_id_atTop.comp_tendsto haff).tendsto_div_nhds_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ))⁻¹)
        atTop (nhds (1 + 0)) := tendsto_const_nhds.add hinv
    have h' : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ))⁻¹)
        atTop (nhds 1) := by simpa using h
    apply h'.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp [hn0]
  have hprod := hsmall.mul hratio
  have hprod' : Tendsto
      (fun n : ℕ =>
        (Real.log (n + 1 : ℝ) / (n + 1 : ℝ)) *
          ((n + 1 : ℝ) / (n : ℝ))) atTop (nhds 0) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs0 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hs0]

theorem hilbertCentralDelannoy_log_rate :
    Tendsto
      (fun n : ℕ => Real.log (hilbertCentralDelannoy n) / (n : ℝ))
      atTop (nhds (2 * Real.log (1 + Real.sqrt 2))) := by
  let b : ℝ := 1 + Real.sqrt 2
  have hb : 0 < b := by dsimp [b]; positivity
  have hlowerLim : Tendsto
      (fun n : ℕ => 2 * Real.log b - Real.log (n + 1 : ℝ) / (n : ℝ))
      atTop (nhds (2 * Real.log b)) := by
    simpa using tendsto_const_nhds.sub log_nat_succ_div_nat_tendsto_zero
  have hupperLim : Tendsto (fun _ : ℕ => 2 * Real.log b)
      atTop (nhds (2 * Real.log b)) := tendsto_const_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLim hupperLim
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hD : 0 < hilbertCentralDelannoy n := hilbertCentralDelannoy_pos n
    have hs : (0 : ℝ) < n + 1 := by positivity
    have hpow : 0 < b ^ (2 * n) := pow_pos hb _
    have hbase : b ^ (2 * n) ≤ (n + 1 : ℝ) * hilbertCentralDelannoy n := by
      simpa [b] using hilbertCentralDelannoy_lower n
    have hlog := Real.strictMonoOn_log.monotoneOn hpow
      (mul_pos hs hD) hbase
    rw [Real.log_pow, Real.log_mul hs.ne' hD.ne'] at hlog
    rw [show 2 * Real.log b - Real.log (n + 1 : ℝ) / (n : ℝ) =
      ((n : ℝ) * (2 * Real.log b) - Real.log (n + 1 : ℝ)) / (n : ℝ) by
        field_simp [hnR.ne']]
    apply (div_le_div_iff_of_pos_right hnR).2
    push_cast at hlog
    nlinarith

  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hD : 0 < hilbertCentralDelannoy n := hilbertCentralDelannoy_pos n
    have hpow : 0 < b ^ (2 * n) := pow_pos hb _
    have hbase : hilbertCentralDelannoy n ≤ b ^ (2 * n) := by
      simpa [b] using hilbertCentralDelannoy_upper n
    have hlog := Real.strictMonoOn_log.monotoneOn hD hpow hbase
    rw [Real.log_pow] at hlog
    apply (div_le_iff₀ hnR).2
    push_cast at hlog
    nlinarith

private theorem nat_succ_div_nat_tendsto_one :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n : ℝ)) atTop (nhds 1) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ))⁻¹)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.add hinv)
  apply h.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp [hn0]

private theorem hilbertCentralDelannoy_log_rate_succ_div_nat :
    Tendsto
      (fun n : ℕ => Real.log (hilbertCentralDelannoy (n + 1)) / (n : ℝ))
      atTop (nhds (2 * Real.log (1 + Real.sqrt 2))) := by
  have hshift := hilbertCentralDelannoy_log_rate.comp (tendsto_add_atTop_nat 1)
  have hprod := hshift.mul nat_succ_div_nat_tendsto_one
  have hprod' : Tendsto
      (fun n : ℕ =>
        (Real.log (hilbertCentralDelannoy (n + 1)) / (n + 1 : ℝ)) *
          ((n + 1 : ℝ) / (n : ℝ)))
      atTop (nhds (2 * Real.log (1 + Real.sqrt 2))) := by
    simpa using hprod
  apply hprod'.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hs0 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hs0]

theorem opNorm2_hilbertInverseFormula_log_rate :
    Tendsto
      (fun n : ℕ =>
        Real.log (opNorm2 (hilbertInverseFormula (n + 1))) / (n : ℝ))
      atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
  let b : ℝ := 1 + Real.sqrt 2
  have hD := hilbertCentralDelannoy_log_rate
  have hDsucc := hilbertCentralDelannoy_log_rate_succ_div_nat
  have hlogsucc := log_nat_succ_div_nat_tendsto_zero
  have hlowerLim : Tendsto
      (fun n : ℕ =>
        2 * (Real.log (hilbertCentralDelannoy n) / (n : ℝ)) -
          2 * (Real.log (n + 1 : ℝ) / (n : ℝ)))
      atTop (nhds (4 * Real.log b)) := by
    have h := (hD.const_mul 2).sub (hlogsucc.const_mul 2)
    dsimp [b]
    convert h using 1 <;> ring
  have hupperLim : Tendsto
      (fun n : ℕ =>
        3 * (Real.log (n + 1 : ℝ) / (n : ℝ)) +
          2 * (Real.log (hilbertCentralDelannoy (n + 1)) / (n : ℝ)))
      atTop (nhds (4 * Real.log b)) := by
    have h := (hlogsucc.const_mul 3).add (hDsucc.const_mul 2)
    dsimp [b]
    convert h using 1 <;> ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlowerLim hupperLim
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hDpos : 0 < hilbertCentralDelannoy n := hilbertCentralDelannoy_pos n
    have hspos : (0 : ℝ) < n + 1 := by positivity
    have hbase := hilbertCentralDelannoy_sq_le_opNorm2_hilbertInverseFormula
      (n + 1) (by omega)
    have hbase' : hilbertCentralDelannoy n ^ 2 ≤
        (n + 1 : ℝ) ^ 2 * opNorm2 (hilbertInverseFormula (n + 1)) := by
      simpa [Nat.cast_add, Nat.cast_one] using hbase
    have hoppos : 0 < opNorm2 (hilbertInverseFormula (n + 1)) := by
      have hsqpos : 0 < hilbertCentralDelannoy n ^ 2 := sq_pos_of_pos hDpos
      have hfacpos : (0 : ℝ) < (n + 1) ^ 2 := by positivity
      by_contra hnot
      have hople : opNorm2 (hilbertInverseFormula (n + 1)) ≤ 0 := le_of_not_gt hnot
      have hprodle : (n + 1 : ℝ) ^ 2 *
          opNorm2 (hilbertInverseFormula (n + 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfacpos.le hople
      linarith
    have hsqpos : 0 < hilbertCentralDelannoy n ^ 2 := sq_pos_of_pos hDpos
    have hfacpos : (0 : ℝ) < (n + 1) ^ 2 := by positivity
    have hlog := Real.strictMonoOn_log.monotoneOn hsqpos
      (mul_pos hfacpos hoppos) hbase'
    rw [Real.log_pow, Real.log_mul hfacpos.ne' hoppos.ne', Real.log_pow] at hlog
    rw [show
      2 * (Real.log (hilbertCentralDelannoy n) / (n : ℝ)) -
          2 * (Real.log (n + 1 : ℝ) / (n : ℝ)) =
        (2 * Real.log (hilbertCentralDelannoy n) -
          2 * Real.log (n + 1 : ℝ)) / (n : ℝ) by ring]
    apply (div_le_div_iff_of_pos_right hnR).2
    push_cast at hlog
    nlinarith
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hopnonneg := opNorm2_nonneg (hilbertInverseFormula (n + 1))
    have hDpos : 0 < hilbertCentralDelannoy (n + 1) :=
      hilbertCentralDelannoy_pos (n + 1)
    have hupper := opNorm2_hilbertInverseFormula_upper_delannoy (n + 1)
    have hupper' : opNorm2 (hilbertInverseFormula (n + 1)) ≤
        (n + 1 : ℝ) ^ 3 * hilbertCentralDelannoy (n + 1) ^ 2 := by
      simpa [Nat.cast_add, Nat.cast_one] using hupper
    have hspos : (0 : ℝ) < n + 1 := by positivity
    have hrhspos : (0 : ℝ) <
        ((n + 1 : ℝ) ^ 3 * hilbertCentralDelannoy (n + 1) ^ 2) := by
      positivity
    have hoppos : 0 < opNorm2 (hilbertInverseFormula (n + 1)) := by
      have hlower := hilbertCentralDelannoy_sq_le_opNorm2_hilbertInverseFormula
        (n + 1) (by omega)
      have hlower' : hilbertCentralDelannoy n ^ 2 ≤
          (n + 1 : ℝ) ^ 2 * opNorm2 (hilbertInverseFormula (n + 1)) := by
        simpa [Nat.cast_add, Nat.cast_one] using hlower
      have hsqpos : 0 < hilbertCentralDelannoy n ^ 2 :=
        sq_pos_of_pos (hilbertCentralDelannoy_pos n)
      have hfacpos : (0 : ℝ) < (n + 1) ^ 2 := by positivity
      by_contra hnot
      have hople : opNorm2 (hilbertInverseFormula (n + 1)) ≤ 0 := le_of_not_gt hnot
      have hprodle : (n + 1 : ℝ) ^ 2 *
          opNorm2 (hilbertInverseFormula (n + 1)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hfacpos.le hople
      linarith
    have hlog := Real.strictMonoOn_log.monotoneOn hoppos hrhspos hupper'
    rw [Real.log_mul (show ((n + 1 : ℝ) ^ 3) ≠ 0 by positivity)
      (show hilbertCentralDelannoy (n + 1) ^ 2 ≠ 0 by positivity),
      Real.log_pow, Real.log_pow] at hlog
    rw [show
      3 * (Real.log (n + 1 : ℝ) / (n : ℝ)) +
          2 * (Real.log (hilbertCentralDelannoy (n + 1)) / (n : ℝ)) =
        (3 * Real.log (n + 1 : ℝ) +
          2 * Real.log (hilbertCentralDelannoy (n + 1))) / (n : ℝ) by ring]
    apply (div_le_div_iff_of_pos_right hnR).2
    push_cast at hlog
    nlinarith

theorem opNorm2_hilbertMatrix_log_rate_zero :
    Tendsto
      (fun n : ℕ => Real.log (opNorm2 (hilbertMatrix (n + 1))) / (n : ℝ))
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) from tendsto_const_nhds)
    log_nat_succ_div_nat_tendsto_zero
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hop : (1 : ℝ) ≤ opNorm2 (hilbertMatrix (n + 1)) :=
      one_le_opNorm2_hilbertMatrix_succ n
    have hlog : 0 ≤ Real.log (opNorm2 (hilbertMatrix (n + 1))) :=
      Real.log_nonneg hop
    exact div_nonneg hlog hnR.le
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hoppos : 0 < opNorm2 (hilbertMatrix (n + 1)) :=
      lt_of_lt_of_le zero_lt_one (one_le_opNorm2_hilbertMatrix_succ n)
    have hspos : (0 : ℝ) < n + 1 := by positivity
    have hle := opNorm2_hilbertMatrix_succ_le n
    have hlog := Real.strictMonoOn_log.monotoneOn hoppos hspos hle
    exact (div_le_div_iff_of_pos_right hnR).2 hlog

theorem hilbertConditionTwo_log_rate_succ :
    Tendsto
      (fun n : ℕ => Real.log (hilbertConditionTwo (n + 1)) / (n : ℝ))
      atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
  have hsum := opNorm2_hilbertMatrix_log_rate_zero.add
    opNorm2_hilbertInverseFormula_log_rate
  have hsum' : Tendsto
      (fun n : ℕ =>
        Real.log (opNorm2 (hilbertMatrix (n + 1))) / (n : ℝ) +
          Real.log (opNorm2 (hilbertInverseFormula (n + 1))) / (n : ℝ))
      atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hHpos : 0 < opNorm2 (hilbertMatrix (n + 1)) :=
    lt_of_lt_of_le zero_lt_one (one_le_opNorm2_hilbertMatrix_succ n)
  have hIpos : 0 < opNorm2 (hilbertInverseFormula (n + 1)) := by
    have hlower := hilbertCentralDelannoy_sq_le_opNorm2_hilbertInverseFormula
      (n + 1) (by omega)
    have hlower' : hilbertCentralDelannoy n ^ 2 ≤
        (n + 1 : ℝ) ^ 2 * opNorm2 (hilbertInverseFormula (n + 1)) := by
      simpa [Nat.cast_add, Nat.cast_one] using hlower
    have hsqpos : 0 < hilbertCentralDelannoy n ^ 2 :=
      sq_pos_of_pos (hilbertCentralDelannoy_pos n)
    have hfacpos : (0 : ℝ) < (n + 1) ^ 2 := by positivity
    by_contra hnot
    have hople : opNorm2 (hilbertInverseFormula (n + 1)) ≤ 0 := le_of_not_gt hnot
    have hprodle : (n + 1 : ℝ) ^ 2 *
        opNorm2 (hilbertInverseFormula (n + 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hfacpos.le hople
    linarith
  unfold hilbertConditionTwo
  rw [Real.log_mul hHpos.ne' hIpos.ne']
  ring

private theorem nat_div_succ_tendsto_one :
    Tendsto (fun n : ℕ => (n : ℝ) / (n + 1 : ℝ)) atTop (nhds 1) := by
  have haff : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp haff
  have h : Tendsto (fun n : ℕ => (1 : ℝ) - ((n + 1 : ℝ))⁻¹)
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hinv)
  apply h.congr'
  filter_upwards with n
  have hs0 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hs0]
  ring

/-- Source-faithful exact replacement for the rounded p. 514 display
`κ₂(Hₙ) ∼ exp(3.5n)`: the logarithmic exponential rate is
`4 log(1+√2)` (approximately `3.5255`). -/
theorem hilbertConditionTwo_log_rate :
    Tendsto
      (fun n : ℕ => Real.log (hilbertConditionTwo n) / (n : ℝ))
      atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
  have hprod := hilbertConditionTwo_log_rate_succ.mul nat_div_succ_tendsto_one
  have hshift : Tendsto
      (fun n : ℕ => Real.log (hilbertConditionTwo (n + 1)) / (n + 1 : ℝ))
      atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
    have hprod' : Tendsto
        (fun n : ℕ =>
          (Real.log (hilbertConditionTwo (n + 1)) / (n : ℝ)) *
            ((n : ℝ) / (n + 1 : ℝ)))
        atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
      simpa using hprod
    apply hprod'.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hs0 : (n + 1 : ℝ) ≠ 0 := by positivity
    field_simp [hn0, hs0]
  have hshift' : Tendsto
      (fun n : ℕ =>
        Real.log (hilbertConditionTwo (n + 1)) / ((n + 1 : ℕ) : ℝ))
      atTop (nhds (4 * Real.log (1 + Real.sqrt 2))) := by
    simpa [Nat.cast_add, Nat.cast_one] using hshift
  exact (tendsto_add_atTop_iff_nat 1).mp hshift'

end NumStability

end
