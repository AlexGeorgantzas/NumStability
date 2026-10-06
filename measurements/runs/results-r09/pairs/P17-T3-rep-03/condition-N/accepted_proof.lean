import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

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
      simpa [p17ProductAlpha] using hX)
    calc
      p17Expectation run.probability
          (fun ω => X ω * p17ProductAlpha run k ω) =
          p17Expectation run.probability (fun ω => X ω * run.delta k ω) -
            p17Expectation run.probability (fun ω => X ω * run.beta k ω) := by
              simp [p17Expectation, p17ProductAlpha, mul_sub,
                Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hmean
  constructor
  · intro i ω
    let I := p17SuffixIndexSet i
    let f : Fin n → ℝ := fun k => 1 + p17ProductAlpha run k ω
    let g : Fin n → ℝ := fun k => run.beta k ω
    have hdelta : ∀ k, 1 + run.delta k ω = f k + g k := by
      intro k
      simp [f, g, p17ProductAlpha]
      ring
    rw [show (∏ k ∈ p17SuffixIndexSet i, (1 + run.delta k ω)) =
        ∏ k ∈ I, (f k + g k) by simp_rw [I, hdelta]]
    rw [Finset.prod_add]
    have hI : I ∈ I.powerset := Finset.mem_powerset.mpr (by simp)
    rw [← Finset.add_sum_erase I.powerset
      (fun K => (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k) hI]
    simp [I, f, g, p17Lemma310BiasRemainder]
  · intro i ω
    let I := p17SuffixIndexSet i
    let a := run.unitRoundoff
    let b := run.biasRoundoff
    let f : Fin n → ℝ := fun k => 1 + p17ProductAlpha run k ω
    let g : Fin n → ℝ := fun k => run.beta k ω
    have ha : 0 ≤ a := run.unitRoundoff_nonneg
    have hb : 0 ≤ b := run.biasRoundoff_nonneg
    have hf : ∀ k, |f k| ≤ 1 + a := by
      intro k
      calc
        |f k| = |1 + p17ProductAlpha run k ω| := rfl
        _ ≤ |(1 : ℝ)| + |p17ProductAlpha run k ω| := abs_add_le _ _
        _ ≤ 1 + a := by
          simpa [a, p17ProductAlpha] using
            add_le_add_left (run.alpha_bound k ω) 1
    have hg : ∀ k, |g k| ≤ b := by
      intro k
      simpa [g, b] using run.beta_bound k ω
    have hterm : ∀ K ∈ I.powerset.erase I,
        |(∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| ≤
          (1 + a) ^ K.card * b ^ (I.card - K.card) := by
      intro K hK
      have hKI : K ⊆ I := Finset.mem_powerset.mp
        (Finset.mem_of_mem_erase hK)
      rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
      have hfprod : (∏ k ∈ K, |f k|) ≤ ∏ _k ∈ K, (1 + a) := by
        exact Finset.prod_le_prod
          (fun k _ => abs_nonneg (f k)) (fun k _ => hf k)
      have hgprod : (∏ k ∈ I \ K, |g k|) ≤ ∏ _k ∈ I \ K, b := by
        exact Finset.prod_le_prod
          (fun k _ => abs_nonneg (g k)) (fun k _ => hg k)
      calc
        (∏ k ∈ K, |f k|) * ∏ k ∈ I \ K, |g k| ≤
            (∏ _k ∈ K, (1 + a)) * ∏ _k ∈ I \ K, b := by
              exact mul_le_mul hfprod hgprod
                (Finset.prod_nonneg fun k _ => abs_nonneg (g k))
                (Finset.prod_nonneg fun _ _ => add_nonneg zero_le_one ha)
        _ = (1 + a) ^ K.card * b ^ (I.card - K.card) := by
          rw [Finset.prod_const, Finset.prod_const,
            Finset.card_sdiff_of_subset hKI]
    calc
      |p17Lemma310BiasRemainder run i ω| =
          |∑ K ∈ I.powerset.erase I,
            (∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| := by
              simp [p17Lemma310BiasRemainder, I, f, g]
      _ ≤ ∑ K ∈ I.powerset.erase I,
          |(∏ k ∈ K, f k) * ∏ k ∈ I \ K, g k| := by
            exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ K ∈ I.powerset.erase I,
          (1 + a) ^ K.card * b ^ (I.card - K.card) := by
            exact Finset.sum_le_sum fun K hK => hterm K hK
      _ = (1 + a + b) ^ I.card - (1 + a) ^ I.card := by
        have hI : I ∈ I.powerset := Finset.mem_powerset.mpr (by simp)
        have hbinom := Finset.sum_pow_mul_eq_add_pow (1 + a) b I
        rw [← Finset.sum_erase_add _ _ hI] at hbinom
        simpa using eq_sub_of_add_eq hbinom
      _ = p17Gamma (p17SuffixIndexSet i).card
              (run.unitRoundoff + run.biasRoundoff) -
            p17Gamma (p17SuffixIndexSet i).card run.unitRoundoff := by
        simp [p17Gamma, I, a, b]
        ring

end HighamBench
