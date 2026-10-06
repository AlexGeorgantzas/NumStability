import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

private theorem p17_product_decomposition_aux
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (a b : ι → ℝ) :
    (∏ k ∈ I, (a k + b k)) =
      (∏ k ∈ I, a k) +
        ∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k := by
  rw [Finset.prod_add]
  calc
    (∑ K ∈ I.powerset,
        (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k) =
        (∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k) +
          (∏ k ∈ I, a k) * ∏ k ∈ I \ I, b k :=
      (Finset.sum_erase_add I.powerset
        (fun K => (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k)
        (Finset.mem_powerset.mpr (fun _ h => h))).symm
    _ = (∏ k ∈ I, a k) +
        ∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k := by
      simp [add_comm]

private theorem p17_bias_sum_bound_aux
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (a b : ι → ℝ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : ∀ k ∈ I, |a k| ≤ u)
    (hb : ∀ k ∈ I, |b k| ≤ v) :
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
      (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
  have hterm : ∀ K ∈ I.powerset,
      |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
        (1 + u) ^ K.card * v ^ (I.card - K.card) := by
    intro K hK
    have hKI : K ⊆ I := Finset.mem_powerset.mp hK
    have hA : |∏ k ∈ K, (1 + a k)| ≤ (1 + u) ^ K.card := by
      rw [Finset.abs_prod, ← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro k hk
        exact abs_nonneg _
      · intro k hk
        calc
          |1 + a k| ≤ |(1 : ℝ)| + |a k| := abs_add_le _ _
          _ ≤ 1 + u := by
            simpa using add_le_add_left (ha k (hKI hk)) 1
    have hB : |∏ k ∈ I \ K, b k| ≤ v ^ (I.card - K.card) := by
      rw [Finset.abs_prod, ← Finset.card_sdiff_of_subset hKI,
        ← Finset.prod_const]
      apply Finset.prod_le_prod
      · intro k hk
        exact abs_nonneg _
      · intro k hk
        exact hb k (Finset.mem_sdiff.mp hk).1
    rw [abs_mul]
    exact mul_le_mul hA hB (abs_nonneg _)
      (pow_nonneg (by linarith) _)
  calc
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
        ∑ K ∈ I.powerset.erase I,
          |(∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K ∈ I.powerset.erase I,
        (1 + u) ^ K.card * v ^ (I.card - K.card) := by
      apply Finset.sum_le_sum
      intro K hK
      exact hterm K (Finset.mem_of_mem_erase hK)
    _ = (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
      have hI : I ∈ I.powerset :=
        Finset.mem_powerset.mpr (fun _ h => h)
      have herase := Finset.sum_erase_add I.powerset
        (fun K => (1 + u) ^ K.card * v ^ (I.card - K.card)) hI
      rw [Finset.sum_pow_mul_eq_add_pow] at herase
      simp only [Nat.sub_self, pow_zero, mul_one] at herase
      linarith

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
    have hmean := run.conditional_mean_from_alpha_history k X (by
      simpa only [p17ProductAlpha] using hX)
    unfold p17Expectation at hmean ⊢
    calc
      (∑ ω, run.probability.prob ω *
          (X ω * p17ProductAlpha run k ω)) =
          (∑ ω, run.probability.prob ω * (X ω * run.delta k ω)) -
            ∑ ω, run.probability.prob ω * (X ω * run.beta k ω) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro ω hω
        simp only [p17ProductAlpha]
        ring
      _ = 0 := sub_eq_zero.mpr hmean
  constructor
  · intro i ω
    let I := p17SuffixIndexSet i
    have hfactor : ∀ k,
        1 + run.delta k ω =
          (1 + p17ProductAlpha run k ω) + run.beta k ω := by
      intro k
      simp only [p17ProductAlpha]
      ring
    calc
      (∏ k ∈ p17SuffixIndexSet i, (1 + run.delta k ω)) =
          ∏ k ∈ I,
            ((1 + p17ProductAlpha run k ω) + run.beta k ω) := by
        apply Finset.prod_congr rfl
        intro k hk
        exact hfactor k
      _ = (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
          ∑ K ∈ I.powerset.erase I,
            (∏ k ∈ K, (1 + p17ProductAlpha run k ω)) *
              ∏ k ∈ I \ K, run.beta k ω :=
        p17_product_decomposition_aux I
          (fun k => 1 + p17ProductAlpha run k ω)
          (fun k => run.beta k ω)
      _ = (∏ k ∈ p17SuffixIndexSet i,
              (1 + p17ProductAlpha run k ω)) +
            p17Lemma310BiasRemainder run i ω := by
        rfl
  · intro i ω
    unfold p17Lemma310BiasRemainder p17Gamma
    have hbound := p17_bias_sum_bound_aux (p17SuffixIndexSet i)
      (fun k => p17ProductAlpha run k ω)
      (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg run.biasRoundoff_nonneg
      (fun k hk => run.alpha_bound k ω)
      (fun k hk => run.beta_bound k ω)
    convert hbound using 1 <;> ring

end HighamBench
