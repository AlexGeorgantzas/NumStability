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
  have hwidth_geometric :
      ∀ m : ℕ, data.width m ≤ (1 / 2 : ℝ) ^ m * data.width 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        calc
          data.width (m + 1) ≤ (1 / 2 : ℝ) * data.width m :=
            data.width_half m
          _ ≤ (1 / 2 : ℝ) *
                ((1 / 2 : ℝ) ^ m * data.width 0) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (m + 1) * data.width 0 := by
            rw [pow_succ]
            ring
  have hsummable :
      ∀ n, Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    intro n
    let C : ℝ := 2 * (1 / 2 : ℝ) ^ (n + 1) * data.width 0
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg (by norm_num) (data.width_nonneg _)) ?_
      (summable_geometric_two.mul_left C)
    intro k
    calc
      2 * data.width (n + 1 + k) ≤
          2 * ((1 / 2 : ℝ) ^ (n + 1 + k) * data.width 0) := by
        exact mul_le_mul_of_nonneg_left (hwidth_geometric _) (by norm_num)
      _ = C * (1 / 2 : ℝ) ^ k := by
        dsimp [C]
        rw [show n + 1 + k = (n + 1) + k by omega, pow_add]
        ring
  have htail_nonneg :
      ∀ n, 0 ≤ p24WidthTail data.toP24WidthSequence n := by
    intro n
    rw [p24WidthTail]
    exact tsum_nonneg (fun k =>
      mul_nonneg (by norm_num) (data.width_nonneg _))
  have hmajorant_nonneg :
      ∀ n, 0 ≤ p24LinearMajorant data.toP24WidthSequence n := by
    intro n
    rw [p24LinearMajorant]
    exact sub_nonneg.mpr (Real.one_le_exp (htail_nonneg n))
  have htail_half :
      ∀ n, p24WidthTail data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24WidthTail data.toP24WidthSequence n := by
    intro n
    rw [p24WidthTail, p24WidthTail]
    calc
      (∑' k : ℕ, 2 * data.width ((n + 1) + 1 + k)) ≤
          ∑' k : ℕ, (1 / 2 : ℝ) *
            (2 * data.width (n + 1 + k)) := by
        apply Summable.tsum_le_tsum
        · intro k
          have hindex : (n + 1) + 1 + k = (n + 1 + k) + 1 := by omega
          rw [hindex]
          nlinarith [data.width_half (n + 1 + k)]
        · exact hsummable (n + 1)
        · exact (hsummable n).mul_left (1 / 2 : ℝ)
      _ = (1 / 2 : ℝ) *
          ∑' k : ℕ, 2 * data.width (n + 1 + k) := by
        exact (hsummable n).tsum_mul_left (1 / 2 : ℝ)
  have hmajorant_half :
      ∀ n, p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
        (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n := by
    intro n
    let x := p24WidthTail data.toP24WidthSequence n
    have hexp_mono :
        Real.exp (p24WidthTail data.toP24WidthSequence (n + 1)) ≤
          Real.exp ((1 / 2 : ℝ) * x) := by
      exact Real.exp_le_exp.mpr (htail_half n)
    have hexp_square : Real.exp x = (Real.exp ((1 / 2 : ℝ) * x)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hmidpoint :
        Real.exp ((1 / 2 : ℝ) * x) - 1 ≤
          (1 / 2 : ℝ) * (Real.exp x - 1) := by
      rw [hexp_square]
      nlinarith [sq_nonneg (Real.exp ((1 / 2 : ℝ) * x) - 1)]
    rw [p24LinearMajorant, p24LinearMajorant]
    exact (sub_le_sub_right hexp_mono 1).trans hmidpoint
  have hrelative :
      ∀ n,
        data.relativeEven n ≤
            p24LinearMajorant data.toP24WidthSequence n ∧
          data.relativeOdd n ≤
            p24LinearMajorant data.toP24WidthSequence n := by
    intro n
    have heven : data.relativeEven n ≤
        p24LinearMajorant data.toP24WidthSequence n := by
      simpa [p24LinearMajorant, p24WidthTail] using
        data.relative_even_tail n
    exact ⟨heven, (data.relative_odd_le_even n).trans heven⟩
  have hmajorant_geometric :
      ∀ n, p24LinearMajorant data.toP24WidthSequence n ≤
        (1 / 2 : ℝ) ^ n *
          p24LinearMajorant data.toP24WidthSequence 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
              (1 / 2 : ℝ) *
                p24LinearMajorant data.toP24WidthSequence n :=
            hmajorant_half n
          _ ≤ (1 / 2 : ℝ) *
                ((1 / 2 : ℝ) ^ n *
                  p24LinearMajorant data.toP24WidthSequence 0) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (n + 1) *
                p24LinearMajorant data.toP24WidthSequence 0 := by
            rw [pow_succ]
            ring
  have hgeometric_tendsto :
      Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) ^ n *
          p24LinearMajorant data.toP24WidthSequence 0)
        atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).mul_const
          (p24LinearMajorant data.toP24WidthSequence 0)
  refine ⟨hsummable, hrelative, hmajorant_nonneg, hmajorant_half, ?_⟩
  exact squeeze_zero hmajorant_nonneg hmajorant_geometric hgeometric_tendsto

end HighamBench
