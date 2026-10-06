import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

lemma pairwise_sum_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      (∑ i : Fin (2 ^ r), v (rightIndex r i)) := by
  have hpow : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by
    rw [pow_succ]
    omega
  let e : Fin (2 ^ r) ⊕ Fin (2 ^ r) ≃ Fin (2 ^ (r + 1)) :=
    finSumFinEquiv.trans (finCongr hpow)
  calc
    (∑ i : Fin (2 ^ (r + 1)), v i) = ∑ i, v (e i) :=
      (Equiv.sum_comp e v).symm
    _ = (∑ i : Fin (2 ^ r), v (e (Sum.inl i))) +
        (∑ i : Fin (2 ^ r), v (e (Sum.inr i))) :=
      Fintype.sum_sum_type _
    _ = _ := by
      apply congrArg₂ (· + ·)
      · apply Fintype.sum_congr
        intro i
        congr 1
      · apply Fintype.sum_congr
        intro i
        congr 1
        apply Fin.ext
        simp [e, rightIndex, finCongr]

lemma gamma_nonneg_of_valid {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u n) : 0 ≤ gamma u n := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu)
    (le_of_lt (sub_pos.mpr hvalid))

lemma gamma_step_bound {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u (n + 1)) :
    gamma u n + u * (gamma u n + 1) ≤ gamma u (n + 1) := by
  unfold GammaValid at hvalid
  norm_num [Nat.cast_add, Nat.cast_one] at hvalid
  have hnvalid : (n : ℝ) * u < 1 := by
    nlinarith
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hnvalid
  have hdnext : 0 < 1 - ((n : ℝ) + 1) * u := sub_pos.mpr hvalid
  have hnum : 0 ≤ ((n : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  have halg :
      gamma u n + u * (gamma u n + 1) =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    unfold gamma
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [halg]
  unfold gamma
  norm_num [Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ hdn hdnext).2
  apply mul_le_mul_of_nonneg_left _ hnum
  nlinarith

lemma rounded_pair_merge_bound {u : ℝ} {n : ℕ} {a b x y δ : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1))
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : |x - a| ≤ gamma u n * a)
    (hy : |y - b| ≤ gamma u n * b)
    (hδ : |δ| ≤ u) :
    |(x + y) * (1 + δ) - (a + b)| ≤ gamma u (n + 1) * (a + b) := by
  have hnvalid : GammaValid u n := by
    unfold GammaValid at hvalid ⊢
    norm_num [Nat.cast_add, Nat.cast_one] at hvalid
    nlinarith
  have hg : 0 ≤ gamma u n := gamma_nonneg_of_valid hu hnvalid
  have hxy : |x + y| ≤ (gamma u n + 1) * (a + b) := by
    calc
      |x + y| = |(x - a) + (y - b) + (a + b)| := by
        congr 1
        ring
      _ ≤ |(x - a) + (y - b)| + |a + b| := abs_add_le _ _
      _ ≤ (|x - a| + |y - b|) + (a + b) := by
        rw [abs_of_nonneg (add_nonneg ha hb)]
        linarith [abs_add_le (x - a) (y - b)]
      _ ≤ (gamma u n + 1) * (a + b) := by
        nlinarith
  have hraw :
      |(x + y) * (1 + δ) - (a + b)| ≤
        |x - a| + |y - b| + |δ| * |x + y| := by
    calc
      |(x + y) * (1 + δ) - (a + b)| =
          |(x - a) + (y - b) + δ * (x + y)| := by
        congr 1
        ring
      _ ≤ |(x - a) + (y - b)| + |δ * (x + y)| := abs_add_le _ _
      _ = |(x - a) + (y - b)| + |δ| * |x + y| := by
        rw [abs_mul]
      _ ≤ (|x - a| + |y - b|) + |δ| * |x + y| := by
        linarith [abs_add_le (x - a) (y - b)]
      _ = _ := by ring
  calc
    |(x + y) * (1 + δ) - (a + b)| ≤
        |x - a| + |y - b| + |δ| * |x + y| := hraw
    _ ≤ gamma u n * a + gamma u n * b +
        u * ((gamma u n + 1) * (a + b)) := by
      exact add_le_add (add_le_add hx hy)
        (mul_le_mul hδ hxy (abs_nonneg _) hu)
    _ = (gamma u n + u * (gamma u n + 1)) * (a + b) := by ring
    _ ≤ gamma u (n + 1) * (a + b) :=
      mul_le_mul_of_nonneg_right (gamma_step_bound hu hvalid) (add_nonneg ha hb)

theorem p01_t1_pairwise_nonnegative
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r)
    (hv : ∀ i, 0 ≤ v i) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  -- PROOF_START P01-T1-H001
  induction r with
  | zero =>
      simp [pairwiseSum, gamma]
  | succ r ih =>
      have hvalid_r : GammaValid fp.u r := by
        unfold GammaValid at hvalid ⊢
        norm_num [Nat.cast_add, Nat.cast_one] at hvalid
        nlinarith [fp.u_nonneg]
      have hleft_nonneg : ∀ i : Fin (2 ^ r), 0 ≤ v (leftIndex r i) :=
        fun i => hv _
      have hright_nonneg : ∀ i : Fin (2 ^ r), 0 ≤ v (rightIndex r i) :=
        fun i => hv _
      have hleft := ih (fun i => v (leftIndex r i)) hvalid_r hleft_nonneg
      have hright := ih (fun i => v (rightIndex r i)) hvalid_r hright_nonneg
      have hsum_left : 0 ≤ ∑ i : Fin (2 ^ r), v (leftIndex r i) := by
        exact Finset.sum_nonneg fun i _ => hv _
      have hsum_right : 0 ≤ ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
        exact Finset.sum_nonneg fun i _ => hv _
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (pairwiseSum fp.fl_add r (fun i => v (leftIndex r i)))
        (pairwiseSum fp.fl_add r (fun i => v (rightIndex r i)))
      rw [pairwiseSum, hfl, pairwise_sum_split]
      exact rounded_pair_merge_bound fp.u_nonneg hvalid
        hsum_left hsum_right hleft hright hδ

end HighamBench
