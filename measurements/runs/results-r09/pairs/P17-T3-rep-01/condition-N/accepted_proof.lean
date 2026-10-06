import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

private lemma p17_prod_add_eq_main_add_remainder
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (f g : ι → ℝ) :
    (∏ k ∈ I, (f k + g k)) =
      (∏ k ∈ I, f k) +
        ∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k := by
  rw [Finset.prod_add]
  let F : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k
  change ∑ K ∈ I.powerset, F K =
    (∏ k ∈ I, f k) + ∑ K ∈ I.powerset.erase I, F K
  rw [← Finset.add_sum_erase I.powerset F
    (Finset.mem_powerset.mpr (show I ⊆ I from fun _ h => h))]
  simp [F]

private lemma p17_abs_prod_add_remainder_le
    {ι : Type*} [DecidableEq ι] (I : Finset ι) (f g : ι → ℝ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ k ∈ I, |f k| ≤ a) (hg : ∀ k ∈ I, |g k| ≤ b) :
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| ≤
      (a + b) ^ I.card - a ^ I.card := by
  let F : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, a) * ∏ k ∈ I \ K, b
  have hterm : ∀ K ∈ I.powerset,
      |(∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| ≤ F K := by
    intro K hK
    have hKI : K ⊆ I := Finset.mem_powerset.mp hK
    dsimp [F]
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    gcongr
    · exact hf _ (hKI ‹_›)
    · exact hg _ (Finset.mem_sdiff.mp ‹_›).1
  have hsum :
      |∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| ≤
        ∑ K ∈ I.powerset.erase I, F K := by
    calc
      |∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| ≤
          ∑ K ∈ I.powerset.erase I,
            |(∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ K ∈ I.powerset.erase I, F K := by
        apply Finset.sum_le_sum
        intro K hK
        exact hterm K (Finset.mem_of_mem_erase hK)
  have hfull : ∑ K ∈ I.powerset, F K = (a + b) ^ I.card := by
    dsimp [F]
    rw [← Finset.prod_add (fun _ : ι => a) (fun _ : ι => b) I]
    simp
  have htop : F I = a ^ I.card := by
    simp [F]
  have herase :
      ∑ K ∈ I.powerset.erase I, F K =
        (a + b) ^ I.card - a ^ I.card := by
    have hsplit := Finset.add_sum_erase I.powerset F
      (Finset.mem_powerset.mpr (show I ⊆ I from fun _ h => h))
    rw [hfull, htop] at hsplit
    linarith
  rw [← herase]
  exact hsum

theorem p17_t3_centered_product_decomposition
    {n : ℕ} {Ω : Type*} [Fintype Ω]
    (run : P17Lemma310Run n Ω) :
    (∀ k X,
      p17HistoryMeasurable (p17ProductAlpha run) k X →
        p17Expectation run.probability
          (fun ω => X ω * p17ProductAlpha run k ω) = 0) ∧
      (∀ i ω,
        (∏ k ∈ p17SuffixIndexSet i, (1 + run.delta k ω)) =
          (∏ k ∈ p17SuffixIndexSet i,
              (1 + p17ProductAlpha run k ω)) +
            p17Lemma310BiasRemainder run i ω) ∧
      ∀ i ω,
        |p17Lemma310BiasRemainder run i ω| ≤
          p17Gamma (p17SuffixIndexSet i).card
              (run.unitRoundoff + run.biasRoundoff) -
            p17Gamma (p17SuffixIndexSet i).card run.unitRoundoff := by
  -- PROOF_START P17-T3-H001
  classical
  constructor
  · intro k X hX
    have hmean := run.conditional_mean_from_alpha_history k X hX
    simp only [p17Expectation, p17ProductAlpha, mul_sub,
      Finset.sum_sub_distrib]
    simpa only [p17Expectation] using sub_eq_zero.mpr hmean
  constructor
  · intro i ω
    let I := p17SuffixIndexSet i
    change (∏ k ∈ I, (1 + run.delta k ω)) =
      (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
        ∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, (1 + p17ProductAlpha run k ω)) *
            ∏ k ∈ I \ K, run.beta k ω
    rw [show (∏ k ∈ I, (1 + run.delta k ω)) =
        ∏ k ∈ I,
          ((1 + p17ProductAlpha run k ω) + run.beta k ω) by
      apply Finset.prod_congr rfl
      intro k hk
      simp only [p17ProductAlpha]
      ring]
    exact p17_prod_add_eq_main_add_remainder I
      (fun k => 1 + p17ProductAlpha run k ω) (fun k => run.beta k ω)
  · intro i ω
    let I := p17SuffixIndexSet i
    change |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + p17ProductAlpha run k ω)) *
          ∏ k ∈ I \ K, run.beta k ω| ≤
      p17Gamma I.card (run.unitRoundoff + run.biasRoundoff) -
        p17Gamma I.card run.unitRoundoff
    have hbound := p17_abs_prod_add_remainder_le I
      (fun k => 1 + p17ProductAlpha run k ω) (fun k => run.beta k ω)
      (1 + run.unitRoundoff) run.biasRoundoff
      (by linarith [run.unitRoundoff_nonneg]) run.biasRoundoff_nonneg
      (by
        intro k hk
        calc
          |1 + p17ProductAlpha run k ω| ≤
              |(1 : ℝ)| + |p17ProductAlpha run k ω| := abs_add_le _ _
          _ ≤ 1 + run.unitRoundoff := by
            simp only [abs_one, add_le_add_iff_left]
            exact run.alpha_bound k ω)
      (by
        intro k hk
        exact run.beta_bound k ω)
    simp only [p17Gamma]
    convert hbound using 1 <;> ring

end HighamBench
