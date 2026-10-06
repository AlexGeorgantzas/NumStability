import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

private lemma p17_powerset_remainder_bound
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x y : ι → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : ∀ k ∈ s, |x k| ≤ A)
    (hy : ∀ k ∈ s, |y k| ≤ B) :
    |∑ t ∈ s.powerset.erase s,
        (∏ k ∈ t, x k) * ∏ k ∈ s \ t, y k| ≤
      (A + B) ^ s.card - A ^ s.card := by
  classical
  let F : Finset ι → ℝ := fun t =>
    (∏ k ∈ t, x k) * ∏ k ∈ s \ t, y k
  let G : Finset ι → ℝ := fun t =>
    A ^ t.card * B ^ (s \ t).card
  have hterm : ∀ t ∈ s.powerset.erase s, |F t| ≤ G t := by
    intro t ht
    have hts : t ⊆ s :=
      Finset.mem_powerset.mp (Finset.mem_erase.mp ht).2
    have hxprod : (∏ k ∈ t, |x k|) ≤ A ^ t.card := by
      simpa only [Finset.prod_const] using
        (Finset.prod_le_prod
          (fun k hk => abs_nonneg (x k))
          (fun k hk => hx k (hts hk)))
    have hyprod : (∏ k ∈ s \ t, |y k|) ≤ B ^ (s \ t).card := by
      simpa only [Finset.prod_const] using
        (Finset.prod_le_prod
          (fun k hk => abs_nonneg (y k))
          (fun k hk => hy k (Finset.sdiff_subset hk)))
    unfold F G
    rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
    exact mul_le_mul hxprod hyprod
      (Finset.prod_nonneg fun k hk => abs_nonneg (y k))
      (pow_nonneg hA _)
  have hsum :
      |∑ t ∈ s.powerset.erase s, F t| ≤
        ∑ t ∈ s.powerset.erase s, G t :=
    (Finset.abs_sum_le_sum_abs F (s.powerset.erase s)).trans
      (Finset.sum_le_sum hterm)
  have hfull :
      (A + B) ^ s.card = ∑ t ∈ s.powerset, G t := by
    simpa only [G, Finset.prod_const] using
      (Finset.prod_add (fun _ : ι => A) (fun _ : ι => B) s)
  have herase :
      (∑ t ∈ s.powerset.erase s, G t) + A ^ s.card =
        ∑ t ∈ s.powerset, G t := by
    simpa [G] using
      (Finset.sum_erase_add s.powerset G
        (Finset.mem_powerset.mpr (Finset.Subset.refl s)))
  unfold F at hsum
  rw [← hfull] at herase
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
    have hmean :=
      run.conditional_mean_from_alpha_history k X hX
    simpa [p17Expectation, p17ProductAlpha, mul_sub] using
      (sub_eq_zero.mpr hmean)
  constructor
  · intro i ω
    unfold p17Lemma310BiasRemainder
    let I := p17SuffixIndexSet i
    let a : Fin n → ℝ := fun k => 1 + p17ProductAlpha run k ω
    let b : Fin n → ℝ := fun k => run.beta k ω
    have hfactor : ∀ k ∈ I, 1 + run.delta k ω = a k + b k := by
      intro k hk
      simp [a, b, p17ProductAlpha]
      ring
    calc
      (∏ k ∈ I, (1 + run.delta k ω)) =
          ∏ k ∈ I, (a k + b k) := by
            exact Finset.prod_congr rfl hfactor
      _ = ∑ K ∈ I.powerset,
          (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k :=
            Finset.prod_add a b I
      _ = (∑ K ∈ I.powerset.erase I,
          (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k) +
          ∏ k ∈ I, a k := by
            symm
            simpa using
              (Finset.sum_erase_add I.powerset
                (fun K => (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k)
                (Finset.mem_powerset.mpr (Finset.Subset.refl I)))
      _ = (∏ k ∈ I, a k) +
          ∑ K ∈ I.powerset.erase I,
            (∏ k ∈ K, a k) * ∏ k ∈ I \ K, b k := add_comm _ _
  · intro i ω
    unfold p17Lemma310BiasRemainder
    have hbound := p17_powerset_remainder_bound
      (p17SuffixIndexSet i)
      (fun k => 1 + p17ProductAlpha run k ω)
      (fun k => run.beta k ω)
      (1 + run.unitRoundoff) run.biasRoundoff
      (by linarith [run.unitRoundoff_nonneg])
      run.biasRoundoff_nonneg
      (by
        intro k hk
        calc
          |1 + p17ProductAlpha run k ω| ≤
              |(1 : ℝ)| + |p17ProductAlpha run k ω| := abs_add_le _ _
          _ ≤ 1 + run.unitRoundoff := by
            simpa [p17ProductAlpha] using
              (add_le_add_left (run.alpha_bound k ω) 1))
      (by
        intro k hk
        exact run.beta_bound k ω)
    simpa [p17Gamma, add_assoc] using hbound

end HighamBench
