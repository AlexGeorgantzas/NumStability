import HighamBench.P24Definitions

namespace HighamBench

open scoped BigOperators Topology
open Filter

/-- P24-T3: the cycle-reindexed linear majorant constructed in Lemma 21. -/
theorem p24_t3_lemma21_linear_convergence
    (data : P24Lemma21Data) :
    (∀ n, Summable (fun k : ℕ => 2 * data.width (n + 1 + k))) ∧
      (∀ n,
        data.relativeEven n ≤
            p24LinearMajorant data.toP24WidthSequence n ∧
          data.relativeOdd n ≤
            p24LinearMajorant data.toP24WidthSequence n) ∧
      (∀ n, 0 ≤ p24LinearMajorant data.toP24WidthSequence n) ∧
      (∀ n, p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n) ∧
      Tendsto (p24LinearMajorant data.toP24WidthSequence) atTop (nhds 0) := by
  -- PROOF_START P24-T3-H001
  let run : P24WidthSequence := data.toP24WidthSequence
  have hwidth_pow (n k : ℕ) :
      run.width (n + k) ≤ (1 / 2 : ℝ) ^ k * run.width n := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          run.width (n + (k + 1)) = run.width ((n + k) + 1) := by
            congr 1 <;> omega
          _ ≤ (1 / 2 : ℝ) * run.width (n + k) := run.width_half (n + k)
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * run.width n) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * run.width n := by
            rw [pow_succ]
            ring
  have hsummable (n : ℕ) :
      Summable (fun k : ℕ => 2 * run.width (n + 1 + k)) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : ℕ => (2 * run.width (n + 1)) * (1 / 2 : ℝ) ^ k)
      (fun k => mul_nonneg (by norm_num) (run.width_nonneg _)) (fun k => ?_) ?_
    · have h := hwidth_pow (n + 1) k
      have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
      convert h' using 1 <;> ring
    · exact summable_geometric_two.mul_left (2 * run.width (n + 1))
  have htail_nonneg (n : ℕ) : 0 ≤ p24WidthTail run n := by
    exact tsum_nonneg fun k => mul_nonneg (by norm_num) (run.width_nonneg _)
  have htail_split (n : ℕ) :
      p24WidthTail run n =
        2 * run.width (n + 1) + p24WidthTail run (n + 1) := by
    unfold p24WidthTail
    rw [(hsummable n).tsum_eq_zero_add]
    congr 1
    apply tsum_congr
    intro k
    congr 2 <;> omega
  have htail_next_le (n : ℕ) :
      p24WidthTail run (n + 1) ≤ 2 * run.width (n + 1) := by
    calc
      p24WidthTail run (n + 1) =
          ∑' k : ℕ, 2 * run.width ((n + 1) + 1 + k) := rfl
      _ ≤ ∑' k : ℕ, run.width (n + 1) * (1 / 2 : ℝ) ^ k := by
        refine (hsummable (n + 1)).tsum_le_tsum (fun k => ?_)
          (summable_geometric_two.mul_left (run.width (n + 1)))
        have h := hwidth_pow (n + 1) (k + 1)
        have h' := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 2 by norm_num)
        calc
          2 * run.width ((n + 1) + 1 + k) =
              2 * run.width ((n + 1) + (k + 1)) := by congr 2 <;> omega
          _ ≤ 2 * ((1 / 2 : ℝ) ^ (k + 1) * run.width (n + 1)) := h'
          _ = run.width (n + 1) * (1 / 2 : ℝ) ^ k := by
            rw [pow_succ]
            ring
      _ = 2 * run.width (n + 1) := by
        rw [tsum_mul_left, tsum_geometric_two]
        ring
  have htail_double (n : ℕ) :
      2 * p24WidthTail run (n + 1) ≤ p24WidthTail run n := by
    rw [htail_split n]
    linarith [htail_next_le n]
  have hmajorant_nonneg (n : ℕ) : 0 ≤ p24LinearMajorant run n := by
    unfold p24LinearMajorant
    exact sub_nonneg.mpr (Real.one_le_exp (htail_nonneg n))
  have hmajorant_half (n : ℕ) :
      p24LinearMajorant run (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant run n := by
    have hexp : Real.exp (2 * p24WidthTail run (n + 1)) ≤
        Real.exp (p24WidthTail run n) :=
      Real.exp_le_exp.mpr (htail_double n)
    have hsq :
        2 * (Real.exp (p24WidthTail run (n + 1)) - 1) ≤
          Real.exp (2 * p24WidthTail run (n + 1)) - 1 := by
      rw [show 2 * p24WidthTail run (n + 1) =
        p24WidthTail run (n + 1) + p24WidthTail run (n + 1) by ring,
        Real.exp_add]
      nlinarith [sq_nonneg (Real.exp (p24WidthTail run (n + 1)) - 1)]
    unfold p24LinearMajorant
    nlinarith
  have htail_tendsto : Tendsto (p24WidthTail run) atTop (nhds 0) := by
    have h : Tendsto
        (fun n : ℕ => ∑' k : ℕ, 2 * run.width (k + (n + 1)))
        atTop (nhds 0) :=
      (tendsto_sum_nat_add (fun i : ℕ => 2 * run.width i)).comp
        (tendsto_add_atTop_nat 1)
    change Tendsto
      (fun n : ℕ => ∑' k : ℕ, 2 * run.width (n + 1 + k))
      atTop (nhds 0)
    refine h.congr' (Eventually.of_forall fun n => ?_)
    apply tsum_congr
    intro k
    congr 2
    omega
  have hmajorant_tendsto :
      Tendsto (p24LinearMajorant run) atTop (nhds 0) := by
    unfold p24LinearMajorant
    simpa using
      (Real.continuous_exp.continuousAt.tendsto.comp htail_tendsto).sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1))
  change
    (∀ n, Summable (fun k : ℕ => 2 * run.width (n + 1 + k))) ∧
      (∀ n,
        data.relativeEven n ≤ p24LinearMajorant run n ∧
          data.relativeOdd n ≤ p24LinearMajorant run n) ∧
      (∀ n, 0 ≤ p24LinearMajorant run n) ∧
      (∀ n, p24LinearMajorant run (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant run n) ∧
      Tendsto (p24LinearMajorant run) atTop (nhds 0)
  refine ⟨hsummable, ?_, hmajorant_nonneg, hmajorant_half, hmajorant_tendsto⟩
  intro n
  constructor
  · exact data.relative_even_tail n
  · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)

end HighamBench
