import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

lemma pairwiseSum_exact_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  have hpow : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by
    rw [pow_succ]
    omega
  calc
    (∑ i : Fin (2 ^ (r + 1)), v i) =
        ∑ i : Fin (2 ^ r + 2 ^ r), v (finCongr hpow i) :=
      (Equiv.sum_comp (finCongr hpow) v).symm
    _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
          ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
      rw [Fin.sum_univ_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      apply Fin.ext
      simp [rightIndex]

lemma gamma_step_bound (u : ℝ) (hu : 0 ≤ u) (r : ℕ)
    (hvalid : GammaValid u (r + 1)) :
    gamma u r + u * (1 + gamma u r) ≤ gamma u (r + 1) := by
  unfold GammaValid at hvalid
  unfold gamma
  push_cast at hvalid ⊢
  have hdr : 0 < 1 - (r : ℝ) * u := by
    nlinarith
  have hds : 0 < 1 - ((r : ℝ) + 1) * u := by
    nlinarith
  have heq :
      (r : ℝ) * u / (1 - (r : ℝ) * u) +
          u * (1 + (r : ℝ) * u / (1 - (r : ℝ) * u)) =
        ((r : ℝ) + 1) * u / (1 - (r : ℝ) * u) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ hdr hds).2
  have hN : 0 ≤ ((r : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  nlinarith [mul_nonneg hN hu]

theorem p01_t1_pairwise_nonnegative
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r)
    (hv : ∀ i, 0 ≤ v i) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  -- PROOF_START P01-T1-H001
  induction r with
  | zero =>
      simp [pairwiseSum, gamma, Fin.sum_univ_one]
  | succ r ih =>
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let sl : ℝ := ∑ i : Fin (2 ^ r), vl i
      let sr : ℝ := ∑ i : Fin (2 ^ r), vr i
      let al : ℝ := pairwiseSum fp.fl_add r vl
      let ar : ℝ := pairwiseSum fp.fl_add r vr
      have hvalid_r : GammaValid fp.u r := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      have hsl : 0 ≤ sl := by
        apply Finset.sum_nonneg
        intro i hi
        exact hv _
      have hsr : 0 ≤ sr := by
        apply Finset.sum_nonneg
        intro i hi
        exact hv _
      have hleft : |al - sl| ≤ gamma fp.u r * sl := by
        dsimp [al, sl, vl]
        exact ih (fun i => v (leftIndex r i)) hvalid_r (fun i => hv _)
      have hright : |ar - sr| ≤ gamma fp.u r * sr := by
        dsimp [ar, sr, vr]
        exact ih (fun i => v (rightIndex r i)) hvalid_r (fun i => hv _)
      have hsum :
          (∑ i : Fin (2 ^ (r + 1)), v i) = sl + sr := by
        simpa [sl, sr, vl, vr] using pairwiseSum_exact_split r v
      have hs : 0 ≤ sl + sr := add_nonneg hsl hsr
      have hgamma : 0 ≤ gamma fp.u r := by
        unfold gamma
        have hd : 0 < 1 - (r : ℝ) * fp.u := by
          unfold GammaValid at hvalid_r
          nlinarith
        exact div_nonneg
          (mul_nonneg (by positivity) fp.u_nonneg) (le_of_lt hd)
      have habs :
          |al + ar| ≤ (1 + gamma fp.u r) * (sl + sr) := by
        calc
          |al + ar| = |(al - sl) + (ar - sr) + (sl + sr)| := by
            congr 1
            ring
          _ ≤ |al - sl| + |ar - sr| + |sl + sr| := by
            calc
              |(al - sl) + (ar - sr) + (sl + sr)| ≤
                  |(al - sl) + (ar - sr)| + |sl + sr| := abs_add_le _ _
              _ ≤ (|al - sl| + |ar - sr|) + |sl + sr| := by
                gcongr
                exact abs_add_le _ _
          _ ≤ gamma fp.u r * sl + gamma fp.u r * sr + (sl + sr) := by
            rw [abs_of_nonneg hs]
            gcongr
          _ = (1 + gamma fp.u r) * (sl + sr) := by ring
      obtain ⟨δ, hδ, hround⟩ := fp.model_add al ar
      have hδ' : |δ| ≤ fp.u := hδ
      have hmain :
          |(al + ar) * (1 + δ) - (sl + sr)| ≤
            gamma fp.u (r + 1) * (sl + sr) := by
        calc
          |(al + ar) * (1 + δ) - (sl + sr)| =
              |(al - sl) + (ar - sr) + δ * (al + ar)| := by
            congr 1
            ring
          _ ≤ |al - sl| + |ar - sr| + |δ| * |al + ar| := by
            calc
              |(al - sl) + (ar - sr) + δ * (al + ar)| ≤
                  |(al - sl) + (ar - sr)| + |δ * (al + ar)| := abs_add_le _ _
              _ ≤ (|al - sl| + |ar - sr|) + |δ * (al + ar)| := by
                gcongr
                exact abs_add_le _ _
              _ = |al - sl| + |ar - sr| + |δ| * |al + ar| := by
                rw [abs_mul]
          _ ≤ gamma fp.u r * sl + gamma fp.u r * sr +
                fp.u * ((1 + gamma fp.u r) * (sl + sr)) := by
            gcongr
            exact fp.u_nonneg
          _ = (gamma fp.u r + fp.u * (1 + gamma fp.u r)) *
                (sl + sr) := by ring
          _ ≤ gamma fp.u (r + 1) * (sl + sr) := by
            exact mul_le_mul_of_nonneg_right
              (gamma_step_bound fp.u fp.u_nonneg r hvalid) hs
      change |fp.fl_add al ar - ∑ i : Fin (2 ^ (r + 1)), v i| ≤
        gamma fp.u (r + 1) * ∑ i : Fin (2 ^ (r + 1)), v i
      rw [hround, hsum]
      exact hmain

end HighamBench
