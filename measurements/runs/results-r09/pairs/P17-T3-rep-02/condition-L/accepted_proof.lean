import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

private lemma p17_abs_prod_add_sub_prod_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k ∈ s, |a k| ≤ A)
    (hb : ∀ k ∈ s, |b k| ≤ B) :
    |(∏ k ∈ s, (a k + b k)) - ∏ k ∈ s, a k| ≤
      (A + B) ^ s.card - A ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      have hax : |a x| ≤ A := ha x (Finset.mem_insert_self x s)
      have hbx : |b x| ≤ B := hb x (Finset.mem_insert_self x s)
      have has : ∀ k ∈ s, |a k| ≤ A := by
        intro k hk
        exact ha k (Finset.mem_insert_of_mem hk)
      have hbs : ∀ k ∈ s, |b k| ≤ B := by
        intro k hk
        exact hb k (Finset.mem_insert_of_mem hk)
      have hih := ih has hbs
      have hprod :
          |∏ k ∈ s, (a k + b k)| ≤ (A + B) ^ s.card := by
        calc
          |∏ k ∈ s, (a k + b k)| =
              ∏ k ∈ s, |a k + b k| := by
                simpa using
                  (Finset.abs_prod s (fun k => a k + b k))
          _ ≤ ∏ _k ∈ s, (A + B) := by
                apply Finset.prod_le_prod
                · intro k hk
                  exact abs_nonneg _
                · intro k hk
                  exact le_trans (abs_add_le _ _)
                    (add_le_add (has k hk) (hbs k hk))
          _ = (A + B) ^ s.card := by simp
      rw [Finset.prod_insert hx, Finset.prod_insert hx,
        Finset.card_insert_of_notMem hx]
      calc
        |(a x + b x) * (∏ k ∈ s, (a k + b k)) -
            a x * ∏ k ∈ s, a k| =
            |b x * (∏ k ∈ s, (a k + b k)) +
              a x * ((∏ k ∈ s, (a k + b k)) - ∏ k ∈ s, a k)| := by
                congr 1
                ring
        _ ≤ |b x * (∏ k ∈ s, (a k + b k))| +
              |a x * ((∏ k ∈ s, (a k + b k)) - ∏ k ∈ s, a k)| :=
                abs_add_le _ _
        _ = |b x| * |∏ k ∈ s, (a k + b k)| +
              |a x| * |(∏ k ∈ s, (a k + b k)) - ∏ k ∈ s, a k| := by
                rw [abs_mul, abs_mul]
        _ ≤ B * (A + B) ^ s.card +
              A * ((A + B) ^ s.card - A ^ s.card) := by
                apply add_le_add
                · exact mul_le_mul hbx hprod (abs_nonneg _) hB
                · exact mul_le_mul hax hih (abs_nonneg _) hA
        _ = (A + B) ^ (s.card + 1) - A ^ (s.card + 1) := by
                rw [pow_succ, pow_succ]
                ring

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
    have h := run.conditional_mean_from_alpha_history k X hX
    simp only [p17Expectation, p17ProductAlpha, mul_sub,
      Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr h
  constructor
  · intro i ω
    let I := p17SuffixIndexSet i
    let f : Finset (Fin n) → ℝ := fun K =>
      (∏ k ∈ K, (1 + p17ProductAlpha run k ω)) *
        ∏ k ∈ I \ K, run.beta k ω
    have hI : I ∈ I.powerset := by simp
    have hsum :
        ∑ K ∈ I.powerset, f K =
          (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
            ∑ K ∈ I.powerset.erase I, f K := by
      have h := (Finset.sum_erase_add I.powerset f hI).symm
      simpa [f, add_comm] using h
    calc
      (∏ k ∈ p17SuffixIndexSet i, (1 + run.delta k ω)) =
          ∏ k ∈ I,
            ((1 + p17ProductAlpha run k ω) + run.beta k ω) := by
              apply Finset.prod_congr rfl
              intro k hk
              simp only [p17ProductAlpha]
              ring
      _ = ∑ K ∈ I.powerset, f K := by
            simpa [f] using
              (Finset.prod_add
                (fun k => 1 + p17ProductAlpha run k ω)
                (fun k => run.beta k ω) I)
      _ = (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
            ∑ K ∈ I.powerset.erase I, f K := hsum
      _ = (∏ k ∈ p17SuffixIndexSet i,
              (1 + p17ProductAlpha run k ω)) +
            p17Lemma310BiasRemainder run i ω := by
              simp [I, f, p17Lemma310BiasRemainder]
  · intro i ω
    let I := p17SuffixIndexSet i
    let f : Finset (Fin n) → ℝ := fun K =>
      (∏ k ∈ K, (1 + p17ProductAlpha run k ω)) *
        ∏ k ∈ I \ K, run.beta k ω
    have hI : I ∈ I.powerset := by simp
    have hsum :
        ∑ K ∈ I.powerset, f K =
          (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
            p17Lemma310BiasRemainder run i ω := by
      have h := (Finset.sum_erase_add I.powerset f hI).symm
      simpa [f, p17Lemma310BiasRemainder, I, add_comm] using h
    have hdecomp :
        (∏ k ∈ I, (1 + run.delta k ω)) =
          (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
            p17Lemma310BiasRemainder run i ω := by
      calc
        (∏ k ∈ I, (1 + run.delta k ω)) =
            ∏ k ∈ I,
              ((1 + p17ProductAlpha run k ω) + run.beta k ω) := by
                apply Finset.prod_congr rfl
                intro k hk
                simp only [p17ProductAlpha]
                ring
        _ = ∑ K ∈ I.powerset, f K := by
              simpa [f] using
                (Finset.prod_add
                  (fun k => 1 + p17ProductAlpha run k ω)
                  (fun k => run.beta k ω) I)
        _ = (∏ k ∈ I, (1 + p17ProductAlpha run k ω)) +
              p17Lemma310BiasRemainder run i ω := hsum
    have hdelta :
        (∏ k ∈ I,
            ((1 + p17ProductAlpha run k ω) + run.beta k ω)) =
          ∏ k ∈ I, (1 + run.delta k ω) := by
      apply Finset.prod_congr rfl
      intro k hk
      simp only [p17ProductAlpha]
      ring
    have hrem :
        p17Lemma310BiasRemainder run i ω =
          (∏ k ∈ I,
              ((1 + p17ProductAlpha run k ω) + run.beta k ω)) -
            ∏ k ∈ I, (1 + p17ProductAlpha run k ω) := by
      rw [hdelta]
      linarith
    have halpha : ∀ k ∈ I,
        |1 + p17ProductAlpha run k ω| ≤ 1 + run.unitRoundoff := by
      intro k hk
      calc
        |1 + p17ProductAlpha run k ω| ≤
            |(1 : ℝ)| + |p17ProductAlpha run k ω| := abs_add_le _ _
        _ ≤ 1 + run.unitRoundoff := by
              simpa [p17ProductAlpha] using
                add_le_add_left (run.alpha_bound k ω) (1 : ℝ)
    have hbeta : ∀ k ∈ I,
        |run.beta k ω| ≤ run.biasRoundoff := by
      intro k hk
      exact run.beta_bound k ω
    rw [hrem]
    have hbound := p17_abs_prod_add_sub_prod_le I
      (fun k => 1 + p17ProductAlpha run k ω)
      (fun k => run.beta k ω)
      (1 + run.unitRoundoff) run.biasRoundoff
      (by linarith [run.unitRoundoff_nonneg])
      run.biasRoundoff_nonneg halpha hbeta
    simpa only [I, p17Gamma, add_assoc, sub_sub_sub_cancel_right] using hbound

end HighamBench
