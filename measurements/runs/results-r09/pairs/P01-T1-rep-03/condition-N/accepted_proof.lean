import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

lemma sum_pairwise_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i, v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      (∑ i : Fin (2 ^ r), v (rightIndex r i)) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ]
    omega
  let e : Fin (2 ^ (r + 1)) ≃ Fin (2 ^ r + 2 ^ r) := finCongr hpow
  calc
    (∑ i, v i) = ∑ j, v (e.symm j) := (Equiv.sum_comp e.symm v).symm
    _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
        (∑ i : Fin (2 ^ r), v (rightIndex r i)) := by
      simpa [e, leftIndex, rightIndex] using
        (Fin.sum_univ_add (fun j => v (e.symm j)))

lemma gamma_nonneg_of_valid {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u n) : 0 ≤ gamma u n := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu)
    (le_of_lt (sub_pos.mpr hvalid))

lemma gamma_step_bound {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u (n + 1)) :
    gamma u n + u * (1 + gamma u n) ≤ gamma u (n + 1) := by
  have hv : ((n : ℝ) + 1) * u < 1 := by
    simpa [GammaValid, Nat.cast_add, Nat.cast_one] using hvalid
  have hn : (n : ℝ) * u < 1 := by nlinarith
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hd' : 0 < 1 - ((n : ℝ) * u + u) := by
    nlinarith
  have hz : 0 ≤ (n : ℝ) * u + u := by positivity
  have heq :
      gamma u n + u * (1 + gamma u n) =
        ((n : ℝ) * u + u) / (1 - (n : ℝ) * u) := by
    unfold gamma
    field_simp [ne_of_gt hd]
    ring
  rw [heq]
  unfold gamma
  norm_num [Nat.cast_add, Nat.cast_one]
  convert div_le_div_of_nonneg_left hz hd' (by linarith :
      1 - ((n : ℝ) * u + u) ≤ 1 - (n : ℝ) * u) using 1 <;> ring

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
      simp only [pairwiseSum]
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let sl : ℝ := ∑ i, vl i
      let sr : ℝ := ∑ i, vr i
      let al : ℝ := pairwiseSum fp.fl_add r vl
      let ar : ℝ := pairwiseSum fp.fl_add r vr
      have hvalid_r : GammaValid fp.u r := by
        unfold GammaValid at hvalid ⊢
        norm_num [Nat.cast_add, Nat.cast_one] at hvalid ⊢
        have hu := fp.u_nonneg
        nlinarith
      have hsl : 0 ≤ sl := Finset.sum_nonneg fun i _ => hv _
      have hsr : 0 ≤ sr := Finset.sum_nonneg fun i _ => hv _
      have hl : |al - sl| ≤ gamma fp.u r * sl :=
        ih vl hvalid_r (fun i => hv _)
      have hr : |ar - sr| ≤ gamma fp.u r * sr :=
        ih vr hvalid_r (fun i => hv _)
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add al ar
      rw [hadd]
      rw [sum_pairwise_split r v]
      change |(al + ar) * (1 + δ) - (sl + sr)| ≤
        gamma fp.u (r + 1) * (sl + sr)
      have hg : 0 ≤ gamma fp.u r :=
        gamma_nonneg_of_valid fp.u_nonneg hvalid_r
      have hs : 0 ≤ sl + sr := add_nonneg hsl hsr
      have herr : |(al + ar) - (sl + sr)| ≤
          gamma fp.u r * (sl + sr) := by
        calc
          |(al + ar) - (sl + sr)| = |(al - sl) + (ar - sr)| := by ring_nf
          _ ≤ |al - sl| + |ar - sr| := abs_add_le _ _
          _ ≤ gamma fp.u r * sl + gamma fp.u r * sr :=
            add_le_add hl hr
          _ = gamma fp.u r * (sl + sr) := by ring
      have hab : |al + ar| ≤
          (1 + gamma fp.u r) * (sl + sr) := by
        calc
          |al + ar| = |((al + ar) - (sl + sr)) + (sl + sr)| := by
            congr 1
            ring
          _ ≤ |(al + ar) - (sl + sr)| + |sl + sr| := abs_add_le _ _
          _ ≤ gamma fp.u r * (sl + sr) + (sl + sr) := by
            rw [abs_of_nonneg hs]
            exact add_le_add_left herr _
          _ = (1 + gamma fp.u r) * (sl + sr) := by ring
      calc
        |(al + ar) * (1 + δ) - (sl + sr)| =
            |((al + ar) - (sl + sr)) + δ * (al + ar)| := by
              congr 1
              ring
        _ ≤ |(al + ar) - (sl + sr)| + |δ * (al + ar)| := abs_add_le _ _
        _ = |(al + ar) - (sl + sr)| + |δ| * |al + ar| := by
          rw [abs_mul]
        _ ≤ gamma fp.u r * (sl + sr) +
            fp.u * ((1 + gamma fp.u r) * (sl + sr)) := by
          exact add_le_add herr
            (mul_le_mul hδ hab (abs_nonneg _) fp.u_nonneg)
        _ = (gamma fp.u r + fp.u * (1 + gamma fp.u r)) *
            (sl + sr) := by ring
        _ ≤ gamma fp.u (r + 1) * (sl + sr) :=
          mul_le_mul_of_nonneg_right
            (gamma_step_bound fp.u_nonneg hvalid) hs

end HighamBench
