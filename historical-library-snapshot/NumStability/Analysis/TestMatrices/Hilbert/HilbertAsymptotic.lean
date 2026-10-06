import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic
import NumStability.Analysis.TestMatrices.Hilbert.Exact

/-!
# NumStability Analysis TestMatrices Hilbert HilbertAsymptotic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28HilbertAsymptotic` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

open Filter Asymptotics Finset

open scoped Topology BigOperators

/-- The elementary exponential rate of the central binomial coefficient.
This uses only `4^n / n < binom(2n,n) ≤ 4^n`. -/
theorem centralBinomial_log_div_nat_tendsto :
    Tendsto
      (fun n : ℕ => Real.log (Nat.centralBinom n : ℝ) / (n : ℝ))
      atTop (nhds (Real.log 4)) := by
  have hlognat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    simpa [Function.comp_def] using h.tendsto_div_nhds_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (f := fun n : ℕ => Real.log (Nat.centralBinom n : ℝ) / (n : ℝ))
      (g := fun n : ℕ => Real.log 4 - Real.log (n : ℝ) / (n : ℝ))
      (h := fun _ : ℕ => Real.log 4)
      (by simpa using tendsto_const_nhds.sub hlognat) tendsto_const_nhds
  · filter_upwards [eventually_atTop.2 ⟨4, fun _ hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcbpos : (0 : ℝ) < Nat.centralBinom n := by
      exact_mod_cast Nat.centralBinom_pos n
    have hlowerN := Nat.four_pow_lt_mul_centralBinom n hn
    have hlower : (4 : ℝ) ^ n < (n : ℝ) * Nat.centralBinom n := by
      exact_mod_cast hlowerN
    have hloglower : Real.log ((4 : ℝ) ^ n) <
        Real.log ((n : ℝ) * Nat.centralBinom n) :=
      Real.strictMonoOn_log
        (show (0 : ℝ) < (4 : ℝ) ^ n by positivity)
        (mul_pos hnpos hcbpos) hlower
    rw [Real.log_pow, Real.log_mul hnpos.ne' hcbpos.ne'] at hloglower
    have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
    rw [show Real.log 4 - Real.log (n : ℝ) / (n : ℝ) =
      ((n : ℝ) * Real.log 4 - Real.log (n : ℝ)) / (n : ℝ) by
        field_simp [hnne]]
    apply (div_le_div_iff_of_pos_right hnpos).mpr
    linarith
  · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hcbpos : (0 : ℝ) < Nat.centralBinom n := by
      exact_mod_cast Nat.centralBinom_pos n
    have huppN : Nat.centralBinom n ≤ 4 ^ n := by
      calc
        Nat.centralBinom n = (2 * n).choose n := rfl
        _ ≤ 2 ^ (2 * n) := Nat.choose_le_two_pow _ _
        _ = 4 ^ n := by rw [pow_mul]; norm_num
    have hupp : (Nat.centralBinom n : ℝ) ≤ (4 : ℝ) ^ n := by
      exact_mod_cast huppN
    have hlogupp : Real.log (Nat.centralBinom n : ℝ) ≤
        Real.log ((4 : ℝ) ^ n) :=
      Real.strictMonoOn_log.monotoneOn hcbpos
        (show (0 : ℝ) < (4 : ℝ) ^ n by positivity) hupp
    rw [Real.log_pow] at hlogupp
    apply (div_le_iff₀ hnpos).mpr
    simpa [mul_comm] using hlogupp

/-- The squared Cholesky diagonal is the reciprocal of the odd factor times
the square of the central binomial coefficient. -/
theorem hilbertRNat_diag_sq_eq_centralBinomial (n : ℕ) :
    hilbertRNat n n ^ 2 =
      1 / ((2 * n + 1 : ℕ) : ℝ) / (Nat.centralBinom n : ℝ) ^ 2 := by
  rw [hilbertRNat_diag_sq]
  have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have h2fac : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
  have hsucc : ((2 * n + 1).factorial : ℝ) =
      ((2 * n + 1 : ℕ) : ℝ) * ((2 * n).factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    rfl
  have hchoose : ((2 * n).factorial : ℝ) / (n.factorial : ℝ) ^ 2 =
      (Nat.centralBinom n : ℝ) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    simpa [two_mul, pow_two] using
      (Nat.cast_add_choose ℝ (a := n) (b := n)).symm
  rw [hsucc]
  rw [← hchoose]
  field_simp [hnfac, h2fac]

/-- Exact logarithm of one determinant recurrence factor. -/
theorem log_hilbertRNat_diag_sq (n : ℕ) :
    Real.log (hilbertRNat n n ^ 2) =
      -Real.log ((2 * n + 1 : ℕ) : ℝ) -
        2 * Real.log (Nat.centralBinom n : ℝ) := by
  rw [hilbertRNat_diag_sq_eq_centralBinomial]
  have hodd : (((2 * n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcb : (Nat.centralBinom n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.centralBinom_pos n).ne'
  rw [div_eq_mul_inv, Real.log_mul]
  · rw [one_div, Real.log_inv, Real.log_inv, Real.log_pow]
    ring
  · simpa [one_div] using (inv_ne_zero hodd)
  · exact (inv_ne_zero (pow_ne_zero 2 hcb))

/-- The odd logarithmic correction is negligible on the linear scale. -/
theorem log_two_mul_add_one_div_nat_tendsto_zero :
    Tendsto
      (fun n : ℕ => Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have haff : Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity : (0 : ℝ) < 2))
  have hsmall :=
    (Real.isLittleO_log_id_atTop.comp_tendsto haff).tendsto_div_nhds_zero
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ => ((2 : ℝ) * n + 1) / (n : ℝ)) atTop (nhds 2) := by
    have hbase : Tendsto (fun n : ℕ => (2 : ℝ) + ((n : ℝ))⁻¹)
        atTop (nhds (2 + 0)) := tendsto_const_nhds.add hinv
    have hcongr : ∀ᶠ n : ℕ in atTop,
        ((2 : ℝ) * n + 1) / (n : ℝ) = 2 + ((n : ℝ))⁻¹ := by
      filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp [hnR]
    simpa using hbase.congr' (hcongr.mono fun _ h => h.symm)
  have hprod := hsmall.mul hratio
  have hcongr : ∀ᶠ n : ℕ in atTop,
      Real.log (((2 * n + 1 : ℕ) : ℝ)) / (n : ℝ) =
        ((Real.log ∘ fun n : ℕ => (2 : ℝ) * n + 1) n /
          (id ∘ fun n : ℕ => (2 : ℝ) * n + 1) n) *
            (((2 : ℝ) * n + 1) / (n : ℝ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have haffR : (2 : ℝ) * n + 1 = ((2 * n + 1 : ℕ) : ℝ) := by
      push_cast
      ring
    have haffne : (2 : ℝ) * n + 1 ≠ 0 := by positivity
    rw [← haffR]
    simp only [Function.comp_apply, id_eq]
    field_simp [hnR, haffne]
  simpa using hprod.congr' (hcongr.mono fun _ h => h.symm)

/-- Each logarithmic determinant increment has slope `-2 log 4`. -/
theorem log_hilbertRNat_diag_sq_div_nat_tendsto :
    Tendsto
      (fun n : ℕ => Real.log (hilbertRNat n n ^ 2) / (n : ℝ))
      atTop (nhds (-2 * Real.log 4)) := by
  have hcb := centralBinomial_log_div_nat_tendsto
  have hodd := log_two_mul_add_one_div_nat_tendsto_zero
  have hmain := hodd.neg.sub (hcb.const_mul 2)
  have hcongr : ∀ᶠ n : ℕ in atTop,
      Real.log (hilbertRNat n n ^ 2) / (n : ℝ) =
        -(Real.log ((2 * n + 1 : ℕ) : ℝ) / (n : ℝ)) -
          2 * (Real.log (Nat.centralBinom n : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    rw [log_hilbertRNat_diag_sq]
    field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega)]
  have hlim := hmain.congr' (hcongr.mono fun _ h => h.symm)
  simpa using hlim

end NumStability

end
