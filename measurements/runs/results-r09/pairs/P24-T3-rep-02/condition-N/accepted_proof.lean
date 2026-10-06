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
  have hwidth : ∀ n k : ℕ,
      run.width (n + k) ≤ (1 / 2 : ℝ) ^ k * run.width n := by
    intro n k
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          run.width (n + (k + 1)) = run.width ((n + k) + 1) := by
            congr 1 <;> omega
          _ ≤ (1 / 2 : ℝ) * run.width (n + k) := run.width_half (n + k)
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * run.width n) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * run.width n := by ring
  have hsumm : ∀ n : ℕ, Summable (fun k : ℕ => 2 * run.width (n + 1 + k)) := by
    intro n
    have hgeom : Summable
        (fun k : ℕ => (2 * run.width (n + 1)) * (1 / 2 : ℝ) ^ k) :=
      summable_geometric_two.mul_left (2 * run.width (n + 1))
    refine hgeom.of_nonneg_of_le
      (fun k => mul_nonneg (by norm_num) (run.width_nonneg _)) ?_
    intro k
    have hk := hwidth (n + 1) k
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) k]
  have htail_nonneg : ∀ n : ℕ, 0 ≤ p24WidthTail run n := by
    intro n
    exact tsum_nonneg (fun k => mul_nonneg (by norm_num) (run.width_nonneg _))
  have htail_half : ∀ n : ℕ,
      p24WidthTail run (n + 1) ≤ (1 / 2 : ℝ) * p24WidthTail run n := by
    intro n
    rw [p24WidthTail, p24WidthTail, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun k => ?_) (hsumm (n + 1)) ((hsumm n).mul_left _)
    have hk := run.width_half (n + 1 + k)
    have hk' : run.width (n + 1 + 1 + k) ≤
        (1 / 2 : ℝ) * run.width (n + 1 + k) := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hk
    norm_num at hk' ⊢
    linarith
  have hmajor_nonneg : ∀ n : ℕ, 0 ≤ p24LinearMajorant run n := by
    intro n
    rw [p24LinearMajorant]
    exact sub_nonneg.mpr (Real.one_le_exp (htail_nonneg n))
  have hmajor_half : ∀ n : ℕ,
      p24LinearMajorant run (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant run n := by
    intro n
    have htwice : 2 * p24WidthTail run (n + 1) ≤ p24WidthTail run n := by
      linarith [htail_half n]
    have hexp := (Real.exp_le_exp.mpr htwice)
    rw [show 2 * p24WidthTail run (n + 1) =
      p24WidthTail run (n + 1) + p24WidthTail run (n + 1) by ring,
      Real.exp_add] at hexp
    have hone : 1 ≤ Real.exp (p24WidthTail run (n + 1)) :=
      Real.one_le_exp (htail_nonneg (n + 1))
    rw [p24LinearMajorant, p24LinearMajorant]
    nlinarith [sq_nonneg (Real.exp (p24WidthTail run (n + 1)) - 1)]
  have htail_tendsto : Tendsto (p24WidthTail run) atTop (nhds 0) := by
    have h := tendsto_sum_nat_add (fun m : ℕ => 2 * run.width (m + 1))
    refine h.congr' (Filter.Eventually.of_forall (fun n => ?_))
    rw [p24WidthTail]
    apply tsum_congr
    intro k
    congr 2
    omega
  have hmajor_tendsto : Tendsto (p24LinearMajorant run) atTop (nhds 0) := by
    have hexp : Tendsto (fun n => Real.exp (p24WidthTail run n)) atTop (nhds 1) := by
      simpa using (Real.continuous_exp.tendsto 0).comp htail_tendsto
    simpa [p24LinearMajorant] using hexp.sub_const 1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [run] using hsumm
  · intro n
    have heven : data.relativeEven n ≤ p24LinearMajorant run n := by
      simpa [run, p24LinearMajorant, p24WidthTail] using data.relative_even_tail n
    simpa [run] using ⟨heven, (data.relative_odd_le_even n).trans heven⟩
  · simpa [run] using hmajor_nonneg
  · simpa [run] using hmajor_half
  · simpa [run] using hmajor_tendsto

end HighamBench
