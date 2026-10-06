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
  have hwidth_iter (m k : ℕ) :
      data.width (m + k) ≤ (1 / 2 : ℝ) ^ k * data.width m := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          data.width (m + (k + 1)) = data.width ((m + k) + 1) := by
            congr 1
          _ ≤ (1 / 2 : ℝ) * data.width (m + k) := data.width_half (m + k)
          _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * data.width m) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (k + 1) * data.width m := by
            rw [pow_succ]
            ring
  have hsummable (n : ℕ) :
      Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    refine Summable.of_nonneg_of_le
      (f := fun k : ℕ => (1 / 2 : ℝ) ^ k * (2 * data.width (n + 1)))
      (fun k => mul_nonneg (by norm_num) (data.width_nonneg _))
      (fun k => ?_) ?_
    · have hk := hwidth_iter (n + 1) k
      calc
        2 * data.width (n + 1 + k) ≤
            2 * ((1 / 2 : ℝ) ^ k * data.width (n + 1)) :=
          mul_le_mul_of_nonneg_left hk (by norm_num)
        _ = (1 / 2 : ℝ) ^ k * (2 * data.width (n + 1)) := by ring
    · exact summable_geometric_two.mul_right (2 * data.width (n + 1))
  have htail_nonneg (n : ℕ) :
      0 ≤ p24WidthTail data.toP24WidthSequence n := by
    unfold p24WidthTail
    exact tsum_nonneg (fun k =>
      mul_nonneg (by norm_num) (data.width_nonneg _))
  have hmajorant_nonneg (n : ℕ) :
      0 ≤ p24LinearMajorant data.toP24WidthSequence n := by
    unfold p24LinearMajorant
    have h := Real.exp_monotone (htail_nonneg n)
    simpa using h
  have hrelative (n : ℕ) :
      data.relativeEven n ≤ p24LinearMajorant data.toP24WidthSequence n ∧
        data.relativeOdd n ≤ p24LinearMajorant data.toP24WidthSequence n := by
    constructor
    · simpa [p24LinearMajorant, p24WidthTail] using data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans
        (by simpa [p24LinearMajorant, p24WidthTail] using data.relative_even_tail n)
  have htail_half (n : ℕ) :
      p24WidthTail data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24WidthTail data.toP24WidthSequence n := by
    unfold p24WidthTail
    calc
      (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
          ∑' k : ℕ, (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by
        refine Summable.tsum_le_tsum (fun k => ?_)
          (hsummable (n + 1)) ((hsummable n).mul_left (1 / 2 : ℝ))
        calc
          2 * data.width ((n + 1) + 1 + k) =
              2 * data.width ((n + 1 + k) + 1) := by
            congr 2
            omega
          _ ≤ 2 * ((1 / 2 : ℝ) * data.width (n + 1 + k)) :=
            mul_le_mul_of_nonneg_left (data.width_half (n + 1 + k)) (by norm_num)
          _ = (1 / 2 : ℝ) * (2 * data.width (n + 1 + k)) := by ring
      _ = (1 / 2 : ℝ) * ∑' k : ℕ, 2 * data.width (n + 1 + k) :=
        (hsummable n).tsum_mul_left (1 / 2 : ℝ)
  have hmajorant_half (n : ℕ) :
      p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n := by
    let a := p24WidthTail data.toP24WidthSequence n
    let b := p24WidthTail data.toP24WidthSequence (n + 1)
    have hb : 0 ≤ b := htail_nonneg (n + 1)
    have htwo : 2 * b ≤ a := by
      dsimp [a, b]
      nlinarith [htail_half n]
    have hone : 1 ≤ Real.exp b := by
      simpa using Real.exp_monotone hb
    have hsquare : Real.exp b * Real.exp b ≤ Real.exp a := by
      calc
        Real.exp b * Real.exp b = Real.exp (b + b) := (Real.exp_add b b).symm
        _ = Real.exp (2 * b) := by ring
        _ ≤ Real.exp a := Real.exp_monotone htwo
    unfold p24LinearMajorant
    change Real.exp b - 1 ≤ (1 / 2 : ℝ) * (Real.exp a - 1)
    nlinarith [sq_nonneg (Real.exp b - 1)]
  have htail_tendsto :
      Tendsto (p24WidthTail data.toP24WidthSequence) atTop (nhds 0) := by
    have h := tendsto_sum_nat_add (fun j : ℕ => 2 * data.width (j + 1))
    unfold p24WidthTail
    convert h using 1
    funext i
    apply tsum_congr
    intro k
    congr 2
    omega
  have hmajorant_tendsto :
      Tendsto (p24LinearMajorant data.toP24WidthSequence) atTop (nhds 0) := by
    have h := Real.tendsto_exp_nhds_zero_nhds_one.comp htail_tendsto
    simpa [p24LinearMajorant] using h.sub_const 1
  exact ⟨hsummable, hrelative, hmajorant_nonneg, hmajorant_half,
    hmajorant_tendsto⟩

end HighamBench
