import HighamBench.P17Definitions

namespace HighamBench

open scoped BigOperators

private lemma p17_prod_add_extract_full
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
      (I.powerset.sum_erase_add _ (Finset.mem_powerset_self I)).symm
    _ = _ := by simp [add_comm]

private lemma p17_abs_powerset_remainder_le
    {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (a b : ι → ℝ) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (ha : ∀ k ∈ I, |a k| ≤ u)
    (hb : ∀ k ∈ I, |b k| ≤ v) :
    |∑ K ∈ I.powerset.erase I,
        (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k| ≤
      (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
  let F : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, (1 + a k)) * ∏ k ∈ I \ K, b k
  let M : Finset ι → ℝ := fun K =>
    (∏ k ∈ K, (1 + u)) * ∏ k ∈ I \ K, v
  have hterm : ∀ K ∈ I.powerset.erase I, |F K| ≤ M K := by
    intro K hK
    have hKI : K ⊆ I := Finset.mem_powerset.mp (Finset.mem_of_mem_erase hK)
    have hleft :
        |∏ k ∈ K, (1 + a k)| ≤ ∏ k ∈ K, (1 + u) := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod
        (fun k hk => abs_nonneg (1 + a k))
        (fun k hk => by
          calc
            |1 + a k| ≤ |(1 : ℝ)| + |a k| := abs_add_le _ _
            _ ≤ 1 + u := by simpa using add_le_add_left (ha k (hKI hk)) 1)
    have hright :
        |∏ k ∈ I \ K, b k| ≤ ∏ k ∈ I \ K, v := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod
        (fun k hk => abs_nonneg (b k))
        (fun k hk => hb k (Finset.mem_sdiff.mp hk).1)
    have hleft_nonneg : 0 ≤ ∏ k ∈ K, (1 + u) := by
      exact Finset.prod_nonneg fun k hk => by linarith
    have hright_nonneg : 0 ≤ |∏ k ∈ I \ K, b k| := abs_nonneg _
    simpa only [F, M, abs_mul] using
      mul_le_mul hleft hright hright_nonneg hleft_nonneg
  calc
    |∑ K ∈ I.powerset.erase I, F K| ≤
        ∑ K ∈ I.powerset.erase I, |F K| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ K ∈ I.powerset.erase I, M K := by
          exact Finset.sum_le_sum fun K hK => hterm K hK
    _ = (1 + u + v) ^ I.card - (1 + u) ^ I.card := by
      have hadd := Finset.prod_add
        (fun _ : ι => (1 + u : ℝ)) (fun _ : ι => v) I
      have hfull :
          (∑ K ∈ I.powerset, M K) = (1 + u + v) ^ I.card := by
        simpa only [M, Finset.prod_const] using hadd.symm
      have herase := I.powerset.sum_erase_add (fun K => M K)
        (Finset.mem_powerset_self I)
      have hMI : M I = (1 + u) ^ I.card := by simp [M]
      change (∑ K ∈ I.powerset.erase I, M K) + M I =
        ∑ K ∈ I.powerset, M K at herase
      rw [hMI] at herase
      rw [hfull] at herase
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
  constructor
  · intro k X hX
    have hmean := run.conditional_mean_from_alpha_history k X (by
      simpa only [p17ProductAlpha] using hX)
    simpa only [p17Expectation, p17ProductAlpha, mul_sub,
      Finset.sum_sub_distrib, sub_eq_zero] using hmean
  constructor
  · intro i ω
    let I := p17SuffixIndexSet i
    have h := p17_prod_add_extract_full I
      (fun k => 1 + p17ProductAlpha run k ω)
      (fun k => run.beta k ω)
    convert h using 1 <;>
      simp only [I, p17ProductAlpha, p17Lemma310BiasRemainder] <;> ring
  · intro i ω
    let I := p17SuffixIndexSet i
    have h := p17_abs_powerset_remainder_le I
      (fun k => p17ProductAlpha run k ω)
      (fun k => run.beta k ω)
      run.unitRoundoff run.biasRoundoff
      run.unitRoundoff_nonneg run.biasRoundoff_nonneg
      (fun k hk => run.alpha_bound k ω)
      (fun k hk => run.beta_bound k ω)
    convert h using 1 <;>
      simp only [I, p17Lemma310BiasRemainder, p17Gamma] <;> ring

end HighamBench
