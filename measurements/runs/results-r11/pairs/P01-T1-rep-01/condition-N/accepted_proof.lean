import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg_of_valid (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : GammaValid u n) :
    0 ≤ gamma u n := by
  unfold GammaValid at hvalid
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu)
    (le_of_lt (sub_pos.mpr hvalid))

private lemma gamma_step_bound (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1)) :
    gamma u n + u * (1 + gamma u n) ≤ gamma u (n + 1) := by
  unfold GammaValid at hvalid
  norm_num at hvalid
  have hn : (n : ℝ) * u < 1 := by nlinarith
  have hden_n : 0 < 1 - (n : ℝ) * u := by linarith
  have hden_s : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  simp only [gamma, Nat.cast_add, Nat.cast_one]
  have hlhs :
      (n : ℝ) * u / (1 - (n : ℝ) * u) +
          u * (1 + (n : ℝ) * u / (1 - (n : ℝ) * u)) =
        ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  rw [hlhs]
  rw [div_le_div_iff₀ hden_n hden_s]
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) hu]

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
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let sl : ℝ := ∑ i, vl i
      let sr : ℝ := ∑ i, vr i
      let al : ℝ := pairwiseSum fp.fl_add r vl
      let ar : ℝ := pairwiseSum fp.fl_add r vr
      have hvalid_r : GammaValid fp.u r := by
        unfold GammaValid at hvalid ⊢
        norm_num at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hvl : ∀ i, 0 ≤ vl i := fun i => hv _
      have hvr : ∀ i, 0 ≤ vr i := fun i => hv _
      have hsl : 0 ≤ sl := Finset.sum_nonneg fun i _ => hvl i
      have hsr : 0 ≤ sr := Finset.sum_nonneg fun i _ => hvr i
      have hel : |al - sl| ≤ gamma fp.u r * sl := by
        exact ih vl hvalid_r hvl
      have her : |ar - sr| ≤ gamma fp.u r * sr := by
        exact ih vr hvalid_r hvr
      have hg : 0 ≤ gamma fp.u r :=
        gamma_nonneg_of_valid fp.u r fp.u_nonneg hvalid_r
      have hpow : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by
        simp [pow_succ, Nat.mul_two]
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = sl + sr := by
        calc
          (∑ i : Fin (2 ^ (r + 1)), v i) =
              ∑ i : Fin (2 ^ r + 2 ^ r), v (Fin.cast hpow i) := by
                symm
                exact Equiv.sum_comp (Fin.castOrderIso hpow).toEquiv v
          _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
                ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
                rw [Fin.sum_univ_add]
                congr 1
                apply Finset.sum_congr rfl
                intro i hi
                congr 1
                apply Fin.ext
                change 2 ^ r + i.val = i.val + 2 ^ r
                omega
          _ = sl + sr := by rfl
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add al ar
      have habs_add : |al + ar| ≤ (1 + gamma fp.u r) * (sl + sr) := by
        calc
          |al + ar| = |(al - sl) + (ar - sr) + (sl + sr)| := by ring_nf
          _ ≤ |al - sl| + |ar - sr| + |sl + sr| := by
            exact le_trans (abs_add_le _ _)
              (add_le_add (abs_add_le _ _) le_rfl)
          _ ≤ gamma fp.u r * sl + gamma fp.u r * sr + (sl + sr) := by
            rw [abs_of_nonneg (add_nonneg hsl hsr)]
            exact add_le_add (add_le_add hel her) le_rfl
          _ = (1 + gamma fp.u r) * (sl + sr) := by ring
      have hround :
          |(al + ar) * (1 + δ) - (sl + sr)| ≤
            (gamma fp.u r + fp.u * (1 + gamma fp.u r)) * (sl + sr) := by
        calc
          |(al + ar) * (1 + δ) - (sl + sr)| =
              |((al - sl) + (ar - sr)) + δ * (al + ar)| := by ring_nf
          _ ≤ |(al - sl) + (ar - sr)| + |δ * (al + ar)| := abs_add_le _ _
          _ ≤ (|al - sl| + |ar - sr|) + |δ| * |al + ar| := by
            rw [abs_mul]
            exact add_le_add (abs_add_le _ _) le_rfl
          _ ≤ (gamma fp.u r * sl + gamma fp.u r * sr) +
                fp.u * ((1 + gamma fp.u r) * (sl + sr)) := by
            exact add_le_add (add_le_add hel her)
              (mul_le_mul hδ habs_add (abs_nonneg _) fp.u_nonneg)
          _ = (gamma fp.u r + fp.u * (1 + gamma fp.u r)) * (sl + sr) := by
            ring
      have hstep := gamma_step_bound fp.u r fp.u_nonneg hvalid
      change |fp.fl_add al ar - ∑ i : Fin (2 ^ (r + 1)), v i| ≤
        gamma fp.u (r + 1) * ∑ i : Fin (2 ^ (r + 1)), v i
      rw [hadd, hsum]
      exact hround.trans (mul_le_mul_of_nonneg_right hstep (add_nonneg hsl hsr))

end HighamBench
