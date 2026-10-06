import NumStability.Algorithms.TestMatrices.Higham28Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Data.Nat.Choose.Bounds

namespace NumStability

open Filter Asymptotics Finset
open scoped Topology BigOperators

noncomputable section

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

/-- The normalized sum of natural indices tends to one half. -/
private theorem sum_range_natCast_div_sq_tendsto_half :
    Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range n, (k : ℝ)) / (n : ℝ) ^ 2)
      atTop (nhds (1 / 2 : ℝ)) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hmodel : Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) * (1 - ((n : ℝ))⁻¹))
      atTop (nhds ((1 / 2 : ℝ) * (1 - 0))) :=
    tendsto_const_nhds.mul (tendsto_const_nhds.sub hinv)
  have hcongr : ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Finset.range n, (k : ℝ)) / (n : ℝ) ^ 2 =
        (1 / 2 : ℝ) * (1 - ((n : ℝ))⁻¹) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : n ≠ 0 := by omega
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    have hsumNat := Finset.sum_range_id_mul_two n
    have hsumReal := congrArg (fun x : ℕ => (x : ℝ)) hsumNat
    push_cast at hsumReal
    rw [Nat.cast_sub (by omega : 1 ≤ n)] at hsumReal
    norm_num at hsumReal
    field_simp [hnR]
    nlinarith
  simpa using hmodel.congr' (hcongr.mono fun _ h => h.symm)

/-- Summing the logarithmic increments gives the one-half slope factor. -/
private theorem sum_log_hilbertRNat_diag_sq_div_sq_tendsto :
    Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range n, Real.log (hilbertRNat k k ^ 2)) /
          (n : ℝ) ^ 2)
      atTop (nhds (-Real.log 4)) := by
  let t : ℕ → ℝ := fun k => Real.log (hilbertRNat k k ^ 2)
  let c : ℝ := -2 * Real.log 4
  have ht : Tendsto (fun n : ℕ => t n / (n : ℝ)) atTop (nhds c) := by
    simpa [t, c] using log_hilbertRNat_diag_sq_div_nat_tendsto
  have hdiffRatio0 : Tendsto
      (fun n : ℕ => t n / (n : ℝ) - c) atTop (nhds 0) := by
    simpa using ht.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (nhds c))
  have hdiffRatio : Tendsto
      (fun n : ℕ => (t n - c * (n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
    apply hdiffRatio0.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp [hnR]
  have hdiff : (fun n : ℕ => t n - c * (n : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ)) := by
    apply Asymptotics.isLittleO_of_tendsto'
    · filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
      intro hz
      exact (show (n : ℝ) ≠ 0 by exact_mod_cast (show n ≠ 0 by omega)) hz |>.elim
    · exact hdiffRatio
  have hsumAtTop : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, (k : ℝ)) atTop atTop := by
    have hsubNat : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
      rw [tendsto_atTop_atTop]
      intro b
      refine ⟨b + 1, ?_⟩
      intro n hn
      omega
    have hsubReal : Tendsto (fun n : ℕ => ((n - 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_iff.mpr hsubNat
    apply Filter.tendsto_atTop_mono' atTop _ hsubReal
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    apply Finset.single_le_sum
    · intro k _
      positivity
    · exact Finset.mem_range.mpr (by omega)
  have hsumDiff := hdiff.sum_range (fun n => Nat.cast_nonneg n) hsumAtTop
  let sg : ℕ → ℝ := fun n => ∑ k ∈ Finset.range n, (k : ℝ)
  let sf : ℕ → ℝ := fun n =>
    ∑ k ∈ Finset.range n, (t k - c * (k : ℝ))
  have hsumDiff' : sf =o[atTop] sg := by simpa [sf, sg] using hsumDiff
  have hratio : Tendsto (fun n => sf n / sg n) atTop (nhds 0) :=
    hsumDiff'.tendsto_div_nhds_zero
  have hsg := sum_range_natCast_div_sq_tendsto_half
  have hsfSq0 : Tendsto (fun n => sf n / (n : ℝ) ^ 2) atTop (nhds 0) := by
    have hmul := hratio.mul hsg
    have hcongr : ∀ᶠ n : ℕ in atTop,
        sf n / sg n *
            ((∑ k ∈ Finset.range n, (k : ℝ)) / (n : ℝ) ^ 2) =
          sf n / (n : ℝ) ^ 2 := by
      filter_upwards [eventually_atTop.2 ⟨2, fun _ hn => hn⟩] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      have hsgpos : 0 < sg n := by
        dsimp [sg]
        have hone : (1 : ℝ) ≤ ∑ k ∈ Finset.range n, (k : ℝ) := by
          have hle := Finset.single_le_sum
            (s := Finset.range n) (f := fun k : ℕ => (k : ℝ))
            (a := 1) (fun k _ => Nat.cast_nonneg k)
            (Finset.mem_range.mpr (by omega))
          simpa using hle
        linarith
      change sf n / sg n * (sg n / (n : ℝ) ^ 2) = sf n / (n : ℝ) ^ 2
      field_simp [hnR, hsgpos.ne']
    simpa using hmul.congr' hcongr
  have hmain := hsfSq0.add (hsg.const_mul c)
  have hcongr : ∀ᶠ n : ℕ in atTop,
      sf n / (n : ℝ) ^ 2 + c * (sg n / (n : ℝ) ^ 2) =
        (∑ k ∈ Finset.range n, t k) / (n : ℝ) ^ 2 := by
    filter_upwards with n
    have hcsum :
        (∑ k ∈ Finset.range n, c * (k : ℝ)) = c * sg n := by
      rw [Finset.mul_sum]
    simp only [sf, Finset.sum_sub_distrib]
    rw [hcsum]
    ring
  have hlim := hmain.congr' hcongr
  have hlim' : Tendsto
      (fun n : ℕ =>
        (∑ k ∈ Finset.range n, Real.log (hilbertRNat k k ^ 2)) /
          (n : ℝ) ^ 2)
      atTop (nhds (0 + c * (1 / 2))) := by
    simpa [t] using hlim
  have hc : 0 + c * (1 / 2) = -Real.log 4 := by
    dsimp [c]
    ring
  rw [hc] at hlim'
  exact hlim'

/-- The determinant is the product of the proved Cholesky diagonal squares. -/
private theorem hilbert_det_eq_diag_sq_product (n : ℕ) :
    Matrix.det (hilbertMatrix n) =
      ∏ k ∈ Finset.range n, hilbertRNat k k ^ 2 := by
  rw [hilbert_det_formula, hilbert_diag_sq_product_nat]

/-- Logarithm of the Hilbert determinant as the sum of its exact Cholesky
increments. -/
theorem log_hilbert_det_eq_sum (n : ℕ) :
    Real.log (Matrix.det (hilbertMatrix n)) =
      ∑ k ∈ Finset.range n, Real.log (hilbertRNat k k ^ 2) := by
  rw [hilbert_det_eq_diag_sq_product]
  apply Real.log_prod
  intro k hk
  rw [hilbertRNat_diag_sq_eq_centralBinomial]
  exact div_ne_zero
    (div_ne_zero one_ne_zero (by positivity))
    (pow_ne_zero 2 (by exact_mod_cast (Nat.centralBinom_pos k).ne'))

/-- Higham (28.2), interpreted faithfully on the leading-log scale:
`log det(Hₙ) / n² → -2 log 2`. -/
theorem hilbertDetLeadingLogRate_proved : HilbertDetLeadingLogRate := by
  unfold HilbertDetLeadingLogRate
  have h := sum_log_hilbertRNat_diag_sq_div_sq_tendsto
  have hfun : Tendsto
      (fun n : ℕ => Real.log (Matrix.det (hilbertMatrix n)) / (n : ℝ) ^ 2)
      atTop (nhds (-Real.log 4)) := by
    apply h.congr'
    filter_upwards with n
    rw [log_hilbert_det_eq_sum]
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  simpa [hlog4] using hfun

end

end NumStability
