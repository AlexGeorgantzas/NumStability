import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma gammaValid_of_le (u : ℝ) (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (h : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at h ⊢
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  exact lt_of_le_of_lt hmul h

private lemma gamma_nonneg_of_valid (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) (le_of_lt (sub_pos.mpr h))

private lemma gamma_step (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (h : GammaValid u (n + 1)) :
    gamma u n + u * (1 + gamma u n) ≤ gamma u (n + 1) := by
  have hn : GammaValid u n :=
    gammaValid_of_le u hu (Nat.le_succ n) h
  unfold GammaValid at h hn
  unfold gamma
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hdns : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  have hnum : 0 ≤ ((n + 1 : ℕ) : ℝ) * u :=
    mul_nonneg (Nat.cast_nonneg _) hu
  have hid :
      (n : ℝ) * u / (1 - (n : ℝ) * u) +
          u * (1 + (n : ℝ) * u / (1 - (n : ℝ) * u)) =
        ((n + 1 : ℕ) : ℝ) * u / (1 - (n : ℝ) * u) := by
    field_simp
    push_cast
    ring
  rw [hid]
  apply (div_le_div_iff₀ hdn hdns).2
  have hdenle : 1 - ((n + 1 : ℕ) : ℝ) * u ≤ 1 - (n : ℝ) * u := by
    push_cast
    nlinarith
  exact mul_le_mul_of_nonneg_left hdenle hnum

private lemma sum_pairwise_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ]
    omega
  let w : Fin (2 ^ r + 2 ^ r) → ℝ := fun i =>
    v (Fin.cast hpow.symm i)
  have hw := Fin.sum_univ_add w
  have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = ∑ i, w i := by
    apply Fintype.sum_equiv (Fin.castOrderIso hpow).toEquiv
    intro i
    simp [w]
  rw [hsum]
  simpa [w, leftIndex, rightIndex] using hw

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
      have hvalid_r : GammaValid fp.u r :=
        gammaValid_of_le fp.u fp.u_nonneg (Nat.le_succ r) hvalid
      have hvl : ∀ i, 0 ≤ vl i := by
        intro i
        exact hv _
      have hvr : ∀ i, 0 ≤ vr i := by
        intro i
        exact hv _
      have hsl : 0 ≤ sl := Finset.sum_nonneg fun i _ => hvl i
      have hsr : 0 ≤ sr := Finset.sum_nonneg fun i _ => hvr i
      have hil : |al - sl| ≤ gamma fp.u r * sl := by
        exact ih vl hvalid_r hvl
      have hir : |ar - sr| ≤ gamma fp.u r * sr := by
        exact ih vr hvalid_r hvr
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add al ar
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = sl + sr := by
        simpa [vl, vr, sl, sr] using sum_pairwise_split r v
      rw [pairwiseSum, show pairwiseSum fp.fl_add r (fun i => v (leftIndex r i)) = al by rfl,
        show pairwiseSum fp.fl_add r (fun i => v (rightIndex r i)) = ar by rfl,
        hadd, hsum]
      have hg : 0 ≤ gamma fp.u r :=
        gamma_nonneg_of_valid fp.u r fp.u_nonneg hvalid_r
      have hal : |al| ≤ (1 + gamma fp.u r) * sl := by
        calc
          |al| = |(al - sl) + sl| := by ring_nf
          _ ≤ |al - sl| + |sl| := abs_add_le _ _
          _ ≤ gamma fp.u r * sl + sl := by
            exact add_le_add hil (le_of_eq (abs_of_nonneg hsl))
          _ = (1 + gamma fp.u r) * sl := by ring
      have har : |ar| ≤ (1 + gamma fp.u r) * sr := by
        calc
          |ar| = |(ar - sr) + sr| := by ring_nf
          _ ≤ |ar - sr| + |sr| := abs_add_le _ _
          _ ≤ gamma fp.u r * sr + sr := by
            exact add_le_add hir (le_of_eq (abs_of_nonneg hsr))
          _ = (1 + gamma fp.u r) * sr := by ring
      have halar : |al + ar| ≤ (1 + gamma fp.u r) * (sl + sr) := by
        calc
          |al + ar| ≤ |al| + |ar| := abs_add_le _ _
          _ ≤ (1 + gamma fp.u r) * sl +
                (1 + gamma fp.u r) * sr := add_le_add hal har
          _ = (1 + gamma fp.u r) * (sl + sr) := by ring
      have herr :
          (al + ar) * (1 + δ) - (sl + sr) =
            ((al - sl) + (ar - sr)) + δ * (al + ar) := by
        ring
      rw [herr]
      calc
        |(al - sl) + (ar - sr) + δ * (al + ar)| ≤
            (|al - sl| + |ar - sr|) + |δ| * |al + ar| := by
          calc
            |(al - sl) + (ar - sr) + δ * (al + ar)| ≤
                |(al - sl) + (ar - sr)| + |δ * (al + ar)| := abs_add_le _ _
            _ ≤ (|al - sl| + |ar - sr|) + |δ * (al + ar)| := by
              gcongr
              exact abs_add_le _ _
            _ = (|al - sl| + |ar - sr|) + |δ| * |al + ar| := by
              rw [abs_mul]
        _ ≤ (gamma fp.u r * sl + gamma fp.u r * sr) +
              fp.u * ((1 + gamma fp.u r) * (sl + sr)) := by
          apply add_le_add
          · exact add_le_add hil hir
          · exact mul_le_mul hδ halar (abs_nonneg _) fp.u_nonneg
        _ = (gamma fp.u r + fp.u * (1 + gamma fp.u r)) * (sl + sr) := by
          ring
        _ ≤ gamma fp.u (r + 1) * (sl + sr) := by
          exact mul_le_mul_of_nonneg_right
            (gamma_step fp.u r fp.u_nonneg hvalid) (add_nonneg hsl hsr)

end HighamBench
