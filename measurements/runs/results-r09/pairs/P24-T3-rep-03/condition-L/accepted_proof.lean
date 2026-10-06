import HighamBench.P24Definitions

namespace HighamBench

open scoped BigOperators Topology
open Filter

private lemma p24_width_geometric_bound (run : P24WidthSequence) (n k : ℕ) :
    run.width (n + k) ≤ (1 / 2 : ℝ) ^ k * run.width n := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        run.width (n + (k + 1)) = run.width ((n + k) + 1) := by congr 1 <;> omega
        _ ≤ (1 / 2 : ℝ) * run.width (n + k) := run.width_half (n + k)
        _ ≤ (1 / 2 : ℝ) * ((1 / 2 : ℝ) ^ k * run.width n) := by
          exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (k + 1) * run.width n := by ring

private lemma p24_width_tail_summable (run : P24WidthSequence) (n : ℕ) :
    Summable (fun k : ℕ => 2 * run.width (n + 1 + k)) := by
  have hgeom : Summable
      (fun k : ℕ => (2 * run.width (n + 1)) * (1 / 2 : ℝ) ^ k) := by
    exact summable_geometric_two.mul_left (2 * run.width (n + 1))
  apply hgeom.of_nonneg_of_le
  · intro k
    exact mul_nonneg (by norm_num) (run.width_nonneg _)
  · intro k
    have h := p24_width_geometric_bound run (n + 1) k
    nlinarith

private lemma p24_width_tail_nonneg (run : P24WidthSequence) (n : ℕ) :
    0 ≤ p24WidthTail run n := by
  apply tsum_nonneg
  intro k
  exact mul_nonneg (by norm_num) (run.width_nonneg _)

private lemma p24_width_tail_double_next_le (run : P24WidthSequence) (n : ℕ) :
    2 * p24WidthTail run (n + 1) ≤ p24WidthTail run n := by
  have hnext := (p24_width_tail_summable run (n + 1)).mul_left 2
  have hnow := p24_width_tail_summable run n
  have hpoint : ∀ k : ℕ,
      2 * (2 * run.width ((n + 1) + 1 + k)) ≤
        2 * run.width (n + 1 + k) := by
    intro k
    have h := run.width_half (n + 1 + k)
    have heq : (n + 1 + k) + 1 = (n + 1) + 1 + k := by omega
    rw [heq] at h
    nlinarith
  have hsum := Summable.tsum_le_tsum hpoint hnext hnow
  unfold p24WidthTail
  rw [← tsum_mul_left]
  exact hsum

private lemma p24_majorant_half (run : P24WidthSequence) (n : ℕ) :
    p24LinearMajorant run (n + 1) ≤
      (1 / 2 : ℝ) * p24LinearMajorant run n := by
  have htail := p24_width_tail_double_next_le run n
  have htail_nonneg := p24_width_tail_nonneg run (n + 1)
  have hexp : Real.exp (2 * p24WidthTail run (n + 1)) ≤
      Real.exp (p24WidthTail run n) := Real.exp_le_exp.mpr htail
  have hexp_sq : (Real.exp (p24WidthTail run (n + 1))) ^ 2 ≤
      Real.exp (p24WidthTail run n) := by
    calc
      (Real.exp (p24WidthTail run (n + 1))) ^ 2 =
          Real.exp (2 * p24WidthTail run (n + 1)) := by
            rw [pow_two, ← Real.exp_add]
            congr 1
            ring
      _ ≤ Real.exp (p24WidthTail run n) := hexp
  have hone : 1 ≤ Real.exp (p24WidthTail run (n + 1)) :=
    Real.one_le_exp htail_nonneg
  have hconvex :
      2 * (Real.exp (p24WidthTail run (n + 1)) - 1) ≤
        (Real.exp (p24WidthTail run (n + 1))) ^ 2 - 1 := by
    nlinarith [sq_nonneg (Real.exp (p24WidthTail run (n + 1)) - 1)]
  unfold p24LinearMajorant
  nlinarith

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
  have hsummable : ∀ n,
      Summable (fun k : ℕ => 2 * data.width (n + 1 + k)) := by
    intro n
    exact p24_width_tail_summable data.toP24WidthSequence n
  have hmajorizes : ∀ n,
      data.relativeEven n ≤ p24LinearMajorant data.toP24WidthSequence n ∧
        data.relativeOdd n ≤ p24LinearMajorant data.toP24WidthSequence n := by
    intro n
    constructor
    · exact data.relative_even_tail n
    · exact (data.relative_odd_le_even n).trans (data.relative_even_tail n)
  have hnonneg : ∀ n, 0 ≤ p24LinearMajorant data.toP24WidthSequence n := by
    intro n
    unfold p24LinearMajorant
    have h := Real.one_le_exp (p24_width_tail_nonneg data.toP24WidthSequence n)
    linarith
  have hhalf : ∀ n, p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
      (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n := by
    intro n
    exact p24_majorant_half data.toP24WidthSequence n
  have hgeom : ∀ n, p24LinearMajorant data.toP24WidthSequence n ≤
      (1 / 2 : ℝ) ^ n * p24LinearMajorant data.toP24WidthSequence 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          p24LinearMajorant data.toP24WidthSequence (n + 1) ≤
              (1 / 2 : ℝ) * p24LinearMajorant data.toP24WidthSequence n := hhalf n
          _ ≤ (1 / 2 : ℝ) *
              ((1 / 2 : ℝ) ^ n * p24LinearMajorant data.toP24WidthSequence 0) := by
                exact mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = (1 / 2 : ℝ) ^ (n + 1) *
              p24LinearMajorant data.toP24WidthSequence 0 := by ring
  have hgeom_tendsto : Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) ^ n *
        p24LinearMajorant data.toP24WidthSequence 0) atTop (nhds 0) := by
    have hp : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num)
    simpa using hp.mul_const (p24LinearMajorant data.toP24WidthSequence 0)
  refine ⟨hsummable, hmajorizes, hnonneg, hhalf, ?_⟩
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall hnonneg
  · exact Filter.Eventually.of_forall hgeom
  · exact hgeom_tendsto

end HighamBench
