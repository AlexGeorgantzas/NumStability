import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma sum_pairwise_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
        ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  let e : Fin (2 ^ (r + 1)) ≃ Fin (2 ^ r + 2 ^ r) :=
    finCongr (by simp [pow_succ, mul_two])
  calc
    (∑ i : Fin (2 ^ (r + 1)), v i) =
        ∑ j : Fin (2 ^ r + 2 ^ r), v (e.symm j) := by
          apply Fintype.sum_equiv e
          intro i
          simp
    _ = (∑ i : Fin (2 ^ r), v (e.symm (Fin.castAdd (2 ^ r) i))) +
          ∑ i : Fin (2 ^ r), v (e.symm (Fin.natAdd (2 ^ r) i)) :=
        Fin.sum_univ_add _
    _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
          ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
        congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;>
          congr 1 <;> apply Fin.ext <;>
            simp [e, leftIndex, rightIndex, Fin.natAdd] <;> omega

private lemma pairwise_nonnegative_error (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ),
      GammaValid fp.u r → (∀ i, 0 ≤ v i) →
        0 ≤ pairwiseSum fp.fl_add r v ∧
          |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
            gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  intro r
  induction r with
  | zero =>
      intro v hvalid hv
      constructor
      · simpa [pairwiseSum] using hv (0 : Fin 1)
      · simp [pairwiseSum, gamma]
  | succ r ih =>
      intro v hvalid hv
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let pl : ℝ := pairwiseSum fp.fl_add r vl
      let pr : ℝ := pairwiseSum fp.fl_add r vr
      let sl : ℝ := ∑ i : Fin (2 ^ r), vl i
      let sr : ℝ := ∑ i : Fin (2 ^ r), vr i
      have hvalid' : GammaValid fp.u r := by
        simp only [GammaValid, Nat.cast_add, Nat.cast_one] at hvalid ⊢
        nlinarith [fp.u_nonneg, mul_nonneg (Nat.cast_nonneg r) fp.u_nonneg]
      have hvl : ∀ i, 0 ≤ vl i := fun i => hv _
      have hvr : ∀ i, 0 ≤ vr i := fun i => hv _
      obtain ⟨hpl, hel⟩ := ih vl hvalid' hvl
      obtain ⟨hpr, her⟩ := ih vr hvalid' hvr
      change 0 ≤ pl at hpl
      change 0 ≤ pr at hpr
      change |pl - sl| ≤ gamma fp.u r * sl at hel
      change |pr - sr| ≤ gamma fp.u r * sr at her
      have hsl : 0 ≤ sl := Finset.sum_nonneg fun i hi => hvl i
      have hsr : 0 ≤ sr := Finset.sum_nonneg fun i hi => hvr i
      have hs : (∑ i : Fin (2 ^ (r + 1)), v i) = sl + sr := by
        simpa [vl, vr, sl, sr] using sum_pairwise_split r v
      obtain ⟨δ, hδ, hround⟩ := fp.model_add pl pr
      have hcomputed : pairwiseSum fp.fl_add (r + 1) v =
          (pl + pr) * (1 + δ) := by
        simpa [pairwiseSum, vl, vr, pl, pr] using hround
      have hu_lt_one : fp.u < 1 := by
        simp only [GammaValid, Nat.cast_add, Nat.cast_one] at hvalid
        nlinarith [fp.u_nonneg, mul_nonneg (Nat.cast_nonneg r) fp.u_nonneg]
      have hfactor : 0 ≤ 1 + δ := by
        have hδ' := (abs_le.mp hδ).1
        nlinarith
      have hden_r : 0 < 1 - (r : ℝ) * fp.u := by
        exact sub_pos.mpr hvalid'
      have hden_succ : 0 < 1 - ((r + 1 : ℕ) : ℝ) * fp.u := by
        exact sub_pos.mpr hvalid
      have hgamma : 0 ≤ gamma fp.u r := by
        exact div_nonneg
          (mul_nonneg (Nat.cast_nonneg r) fp.u_nonneg) (le_of_lt hden_r)
      have hcoeff :
          gamma fp.u r + fp.u * (1 + gamma fp.u r) ≤
            gamma fp.u (r + 1) := by
        have heq :
            gamma fp.u r + fp.u * (1 + gamma fp.u r) =
              (((r + 1 : ℕ) : ℝ) * fp.u) /
                (1 - (r : ℝ) * fp.u) := by
          unfold gamma
          field_simp [ne_of_gt hden_r]
          push_cast
          ring
        rw [heq]
        unfold gamma
        apply div_le_div₀
        · exact mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
        · exact le_rfl
        · exact hden_succ
        · push_cast
          nlinarith [fp.u_nonneg]
      constructor
      · rw [hcomputed]
        exact mul_nonneg (add_nonneg hpl hpr) hfactor
      · rw [hcomputed, hs]
        have hpl_upper : pl ≤ (1 + gamma fp.u r) * sl := by
          have h := le_trans (le_abs_self (pl - sl)) hel
          nlinarith
        have hpr_upper : pr ≤ (1 + gamma fp.u r) * sr := by
          have h := le_trans (le_abs_self (pr - sr)) her
          nlinarith
        have hp_upper : pl + pr ≤
            (1 + gamma fp.u r) * (sl + sr) := by
          calc
            pl + pr ≤ (1 + gamma fp.u r) * sl +
                (1 + gamma fp.u r) * sr := add_le_add hpl_upper hpr_upper
            _ = (1 + gamma fp.u r) * (sl + sr) := by ring
        calc
          |(pl + pr) * (1 + δ) - (sl + sr)| =
              |(pl - sl) + (pr - sr) + δ * (pl + pr)| := by
                congr 1
                ring
          _ ≤ |pl - sl| + |pr - sr| + |δ * (pl + pr)| := by
                calc
                  |(pl - sl) + (pr - sr) + δ * (pl + pr)| ≤
                      |(pl - sl) + (pr - sr)| + |δ * (pl + pr)| :=
                    abs_add_le _ _
                  _ ≤ (|pl - sl| + |pr - sr|) + |δ * (pl + pr)| :=
                    add_le_add_left (abs_add_le _ _) _
          _ = |pl - sl| + |pr - sr| + |δ| * (pl + pr) := by
                rw [abs_mul, abs_of_nonneg (add_nonneg hpl hpr)]
          _ ≤ gamma fp.u r * sl + gamma fp.u r * sr +
                fp.u * (pl + pr) := by
              exact add_le_add (add_le_add hel her)
                (mul_le_mul_of_nonneg_right hδ (add_nonneg hpl hpr))
          _ ≤ gamma fp.u r * sl + gamma fp.u r * sr +
                fp.u * ((1 + gamma fp.u r) * (sl + sr)) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hp_upper fp.u_nonneg) _
          _ = (gamma fp.u r + fp.u * (1 + gamma fp.u r)) *
                (sl + sr) := by ring
          _ ≤ gamma fp.u (r + 1) * (sl + sr) := by
              exact mul_le_mul_of_nonneg_right hcoeff (add_nonneg hsl hsr)

theorem p01_t1_pairwise_nonnegative
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r)
    (hv : ∀ i, 0 ≤ v i) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), v i := by
  -- PROOF_START P01-T1-H001
  exact (pairwise_nonnegative_error fp r v hvalid hv).2

end HighamBench
