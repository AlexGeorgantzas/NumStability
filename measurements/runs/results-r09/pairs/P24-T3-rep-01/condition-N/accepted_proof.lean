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
  have hwidth_geometric (m k : ℕ) :
      data.width (m + k) ≤ (1 / 2 : ℝ) ^ k * data.width m := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          data.width (m + (k + 1)) = data.width ((m + k) + 1) := by
            congr 1 <;> omega
          _ ≤ (1 / 2 : ℝ) * data.width (m + k) := data.width_half (m + k)
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * data.width m) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * data.width m := by ring
  have hsummable (n : ℕ) :
      Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : ℕ => 2 * ((1 / 2 : ℝ) ^ k * data.width (n + 1)))
      (fun k => mul_nonneg (by norm_num) (data.width_nonneg _)) ?_ ?_
    · intro k
      exact mul_le_mul_of_nonneg_left (hwidth_geometric (n + 1) k) (by norm_num)
    · simpa [mul_assoc, mul_left_comm, mul_comm] using
        summable_geometric_two.mul_right (2 * data.width (n + 1))
  have htail_nonneg (n : ℕ) :
      0 ≤ p24WidthTail data.toP24WidthSequence n := by
    unfold p24WidthTail
    exact tsum_nonneg fun k => mul_nonneg (by norm_num) (data.width_nonneg _)
  have htail_half (n : ℕ) :
      p24WidthTail data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24WidthTail data.toP24WidthSequence n := by
    unfold p24WidthTail
    rw [← (hsummable n).tsum_mul_left (1 / 2 : ℝ)]
    refine (hsummable (n + 1)).tsum_le_tsum ?_ ((hsummable n).mul_left _)
    intro k
    have hw := data.width_half (n + 1 + k)
    norm_num at hw ⊢
    convert (mul_le_mul_of_nonneg_left hw (by norm_num : (0 : ℝ) ≤ 2)) using 1 <;>
      ring_nf
  have hmajor_nonneg (n : ℕ) :
      0 ≤ p24LinearMajorant data.toP24WidthSequence n := by
    unfold p24LinearMajorant
    exact sub_nonneg.mpr (Real.one_le_exp (htail_nonneg n))
  have hmajor_half (n : ℕ) :
      p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n := by
    let a := p24WidthTail data.toP24WidthSequence n
    let b := p24WidthTail data.toP24WidthSequence (n + 1)
    have hab : b ≤ a / 2 := by
      simpa [a, b, div_eq_mul_inv, mul_comm] using htail_half n
    have ha : 0 ≤ a := htail_nonneg n
    have hba : Real.exp b ≤ Real.exp (a / 2) := Real.exp_le_exp.mpr hab
    have heq : Real.exp a = (Real.exp (a / 2)) ^ 2 := by
      rw [show a = a / 2 + a / 2 by ring, Real.exp_add]
      ring
    have hone : 1 ≤ Real.exp (a / 2) := Real.one_le_exp (by linarith)
    unfold p24LinearMajorant
    change Real.exp b - 1 ≤ (1 / 2 : ℝ) * (Real.exp a - 1)
    rw [heq]
    nlinarith [sq_nonneg (Real.exp (a / 2) - 1)]
  have hmajor_geometric (n : ℕ) :
      p24LinearMajorant data.toP24WidthSequence n ≤
        (1 / 2 : ℝ) ^ n * p24LinearMajorant data.toP24WidthSequence 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
              (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n :=
            hmajor_half n
          _ ≤ (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ n * p24LinearMajorant data.toP24WidthSequence 0) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (n + 1) *
              p24LinearMajorant data.toP24WidthSequence 0 := by ring
  have hmajor_tendsto :
      Tendsto (p24LinearMajorant data.toP24WidthSequence) atTop (nhds 0) := by
    apply squeeze_zero hmajor_nonneg hmajor_geometric
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
        (p24LinearMajorant data.toP24WidthSequence 0)
  refine ⟨hsummable, ?_, hmajor_nonneg, hmajor_half, hmajor_tendsto⟩
  intro n
  constructor
  · exact data.relative_even_tail n
  · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)

end HighamBench
