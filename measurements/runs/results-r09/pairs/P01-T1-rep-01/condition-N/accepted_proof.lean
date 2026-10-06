import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma sum_pairwise_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  have hp : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by
    rw [pow_succ]
    omega
  let e : Fin (2 ^ r + 2 ^ r) ≃ Fin (2 ^ (r + 1)) := finCongr hp
  calc
    (∑ i : Fin (2 ^ (r + 1)), v i) =
        ∑ i : Fin (2 ^ r + 2 ^ r), v (e i) := by
      symm
      exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
    _ = (∑ i : Fin (2 ^ r), v (e (Fin.castAdd (2 ^ r) i))) +
          ∑ i : Fin (2 ^ r), v (e (Fin.natAdd (2 ^ r) i)) :=
      Fin.sum_univ_add (fun i ↦ v (e i))
    _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
          ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
      apply congrArg₂ (fun x y : ℝ ↦ x + y)
      · apply Fintype.sum_congr
        intro i
        congr 1
      · apply Fintype.sum_congr
        intro i
        congr 1
        apply Fin.ext
        simp [e, rightIndex]

private lemma gamma_step_bound (u : ℝ) (r : ℕ) (hu : 0 ≤ u)
    (hvalid : GammaValid u (r + 1)) :
    gamma u r + u * (gamma u r + 1) ≤ gamma u (r + 1) := by
  have hv : ((r : ℝ) + 1) * u < 1 := by
    simpa [GammaValid, Nat.cast_add, Nat.cast_one] using hvalid
  have hr : (r : ℝ) * u < 1 := by nlinarith
  have hdr : 0 < 1 - (r : ℝ) * u := by linarith
  have hds : 0 < 1 - ((r : ℝ) + 1) * u := by linarith
  have hn : 0 ≤ ((r : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  have hden : 1 - ((r : ℝ) + 1) * u ≤ 1 - (r : ℝ) * u := by
    nlinarith
  have hdiv :
      (((r : ℝ) + 1) * u) / (1 - (r : ℝ) * u) ≤
        (((r : ℝ) + 1) * u) / (1 - ((r : ℝ) + 1) * u) :=
    div_le_div_of_nonneg_left hn hds hden
  calc
    gamma u r + u * (gamma u r + 1) =
        (((r : ℝ) + 1) * u) / (1 - (r : ℝ) * u) := by
          dsimp [gamma]
          field_simp
          ring
    _ ≤ (((r : ℝ) + 1) * u) /
          (1 - ((r : ℝ) + 1) * u) := hdiv
    _ = gamma u (r + 1) := by
      simp [gamma, Nat.cast_add, Nat.cast_one]

private lemma combine_pairwise_error
    (u : ℝ) (r : ℕ) (hu : 0 ≤ u) (hvalid : GammaValid u (r + 1))
    (a b s₁ s₂ δ : ℝ) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (ha : |a - s₁| ≤ gamma u r * s₁)
    (hb : |b - s₂| ≤ gamma u r * s₂) (hδ : |δ| ≤ u) :
    |(a + b) * (1 + δ) - (s₁ + s₂)| ≤ gamma u (r + 1) * (s₁ + s₂) := by
  have hs : 0 ≤ s₁ + s₂ := add_nonneg hs₁ hs₂
  have herr : |(a + b) - (s₁ + s₂)| ≤ gamma u r * (s₁ + s₂) := by
    calc
      |(a + b) - (s₁ + s₂)| = |(a - s₁) + (b - s₂)| := by ring_nf
      _ ≤ |a - s₁| + |b - s₂| := abs_add_le _ _
      _ ≤ gamma u r * s₁ + gamma u r * s₂ := add_le_add ha hb
      _ = gamma u r * (s₁ + s₂) := by ring
  have hab : |a + b| ≤ gamma u r * (s₁ + s₂) + (s₁ + s₂) := by
    calc
      |a + b| = |((a + b) - (s₁ + s₂)) + (s₁ + s₂)| := by ring_nf
      _ ≤ |(a + b) - (s₁ + s₂)| + |s₁ + s₂| := abs_add_le _ _
      _ ≤ gamma u r * (s₁ + s₂) + (s₁ + s₂) := by
        rw [abs_of_nonneg hs]
        exact add_le_add herr le_rfl
  have hround :
      |δ * (a + b)| ≤ u * (gamma u r * (s₁ + s₂) + (s₁ + s₂)) := by
    calc
      |δ * (a + b)| = |δ| * |a + b| := abs_mul _ _
      _ ≤ u * |a + b| := mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
      _ ≤ u * (gamma u r * (s₁ + s₂) + (s₁ + s₂)) :=
        mul_le_mul_of_nonneg_left hab hu
  calc
    |(a + b) * (1 + δ) - (s₁ + s₂)| =
        |((a + b) - (s₁ + s₂)) + δ * (a + b)| := by ring_nf
    _ ≤ |(a + b) - (s₁ + s₂)| + |δ * (a + b)| := abs_add_le _ _
    _ ≤ gamma u r * (s₁ + s₂) +
          u * (gamma u r * (s₁ + s₂) + (s₁ + s₂)) :=
      add_le_add herr hround
    _ = (gamma u r + u * (gamma u r + 1)) * (s₁ + s₂) := by ring
    _ ≤ gamma u (r + 1) * (s₁ + s₂) :=
      mul_le_mul_of_nonneg_right (gamma_step_bound u r hu hvalid) hs

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
      let v₁ : Fin (2 ^ r) → ℝ := fun i ↦ v (leftIndex r i)
      let v₂ : Fin (2 ^ r) → ℝ := fun i ↦ v (rightIndex r i)
      let s₁ : ℝ := ∑ i : Fin (2 ^ r), v₁ i
      let s₂ : ℝ := ∑ i : Fin (2 ^ r), v₂ i
      have hvalid_r : GammaValid fp.u r := by
        unfold GammaValid at hvalid ⊢
        simp only [Nat.cast_add, Nat.cast_one] at hvalid
        nlinarith [fp.u_nonneg]
      have hs₁ : 0 ≤ s₁ := Finset.sum_nonneg fun i _ ↦ hv _
      have hs₂ : 0 ≤ s₂ := Finset.sum_nonneg fun i _ ↦ hv _
      have ha := ih v₁ hvalid_r (fun i ↦ hv _)
      have hb := ih v₂ hvalid_r (fun i ↦ hv _)
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add
        (pairwiseSum fp.fl_add r v₁) (pairwiseSum fp.fl_add r v₂)
      rw [pairwiseSum, show (fun i ↦ v (leftIndex r i)) = v₁ from rfl,
        show (fun i ↦ v (rightIndex r i)) = v₂ from rfl, hadd,
        sum_pairwise_split]
      change |(pairwiseSum fp.fl_add r v₁ + pairwiseSum fp.fl_add r v₂) *
          (1 + δ) - (s₁ + s₂)| ≤ gamma fp.u (r + 1) * (s₁ + s₂)
      exact combine_pairwise_error fp.u r fp.u_nonneg hvalid
        _ _ _ _ δ hs₁ hs₂ ha hb hδ

end HighamBench
