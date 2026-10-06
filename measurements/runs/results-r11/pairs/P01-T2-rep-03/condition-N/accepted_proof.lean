import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg_of_valid (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (h : GammaValid u n) : 0 ≤ gamma u n := by
  rw [gamma]
  apply div_nonneg
  · positivity
  · exact le_of_lt (sub_pos.mpr h)

private lemma gamma_step (u : ℝ) (n : ℕ) (hu : 0 ≤ u)
    (h : GammaValid u (n + 1)) :
    (1 + u) * gamma u n + u ≤ gamma u (n + 1) := by
  have hden₁ : 0 < 1 - (n : ℝ) * u := by
    unfold GammaValid at h
    push_cast at h
    have hn : (n : ℝ) * u ≤ ((n : ℝ) + 1) * u := by
      nlinarith
    nlinarith
  have hden₂ : 0 < 1 - ((n : ℝ) + 1) * u := by
    simpa [GammaValid] using h
  have hnum : 0 ≤ ((n : ℝ) + 1) * u := by positivity
  have hden₁' : 1 - u * (n : ℝ) ≠ 0 := by
    nlinarith [hden₁]
  rw [gamma, gamma]
  push_cast
  have hid :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    apply (eq_div_iff (ne_of_gt hden₁)).2
    field_simp [hden₁']
    ring
  rw [hid]
  apply div_le_div_of_nonneg_left hnum hden₂
  nlinarith

private lemma gammaValid_of_le (u : ℝ) {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (h : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at h ⊢
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) h

private lemma recursive_running_bound
    (fp : StandardAddModel) (n : ℕ) (v : Fin n → ℝ) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      fp.u * ∑ i : Fin n, |recursivePreRound fp.fl_add v i| := by
  induction n with
  | zero => simp [recursiveSum]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simpa [recursiveSum, recursivePreRound] using
        (mul_nonneg fp.u_nonneg (abs_nonneg (v 0)))
    · let w : Fin n → ℝ := fun i => v i.castSucc
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add
        (recursiveSum fp.fl_add n w) (v (Fin.last n))
      have hpre_last :
          recursivePreRound fp.fl_add v (Fin.last n) =
            recursiveSum fp.fl_add n w + v (Fin.last n) := by
        unfold recursivePreRound
        congr 2
      have hpre_cast (i : Fin n) :
          recursivePreRound fp.fl_add v i.castSucc =
            recursivePreRound fp.fl_add w i := by
        simp only [recursivePreRound, w]
        congr 2
      have hrec :
          recursiveSum fp.fl_add (n + 1) v =
            (recursiveSum fp.fl_add n w + v (Fin.last n)) * (1 + δ) := by
        simp only [recursiveSum, hn, ↓reduceDIte]
        exact hadd
      rw [hrec, Fin.sum_univ_castSucc]
      calc
        |(recursiveSum fp.fl_add n w + v (Fin.last n)) * (1 + δ) -
            ((∑ i : Fin n, v i.castSucc) + v (Fin.last n))| =
            |(recursiveSum fp.fl_add n w - ∑ i : Fin n, w i) +
              (recursiveSum fp.fl_add n w + v (Fin.last n)) * δ| := by
                congr 1
                simp only [w]
                ring
        _ ≤ |recursiveSum fp.fl_add n w - ∑ i : Fin n, w i| +
              |recursiveSum fp.fl_add n w + v (Fin.last n)| * |δ| := by
                simpa [abs_mul] using abs_add_le
                  (recursiveSum fp.fl_add n w - ∑ i : Fin n, w i)
                  ((recursiveSum fp.fl_add n w + v (Fin.last n)) * δ)
        _ ≤ fp.u * (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) +
              |recursiveSum fp.fl_add n w + v (Fin.last n)| * fp.u := by
                gcongr
                exact ih w
        _ = fp.u * ∑ i : Fin (n + 1), |recursivePreRound fp.fl_add v i| := by
              rw [Fin.sum_univ_castSucc]
              simp_rw [hpre_cast]
              rw [hpre_last]
              ring

private lemma recursive_gamma_bound
    (fp : StandardAddModel) (n : ℕ) (v : Fin n → ℝ)
    (hvalid : GammaValid fp.u (n - 1)) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  induction n with
  | zero => simp [recursiveSum, gamma]
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      simp [recursiveSum, gamma]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let w : Fin n → ℝ := fun i => v i.castSucc
      let old : ℝ := recursiveSum fp.fl_add n w
      let exact : ℝ := ∑ i : Fin n, w i
      let total : ℝ := (∑ i : Fin n, |w i|) + |v (Fin.last n)|
      have hvalid_n : GammaValid fp.u n := by
        simpa using hvalid
      have hvalid_prev : GammaValid fp.u (n - 1) := by
        unfold GammaValid at hvalid_n ⊢
        have hcast : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (Nat.sub_le n 1)
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid_n
      have hγ : 0 ≤ gamma fp.u (n - 1) :=
        gamma_nonneg_of_valid fp.u (n - 1) fp.u_nonneg hvalid_prev
      have htotal : 0 ≤ total := by
        dsimp [total]
        positivity
      have hsum_split :
          (∑ i : Fin (n + 1), |v i|) = total := by
        rw [Fin.sum_univ_castSucc]
      have hsmall : (∑ i : Fin n, |w i|) ≤ total := by
        dsimp [total]
        exact le_add_of_nonneg_right (abs_nonneg _)
      have hprev := ih w hvalid_prev
      have hprev_total : |old - exact| ≤ gamma fp.u (n - 1) * total := by
        calc
          |old - exact| ≤ gamma fp.u (n - 1) * ∑ i : Fin n, |w i| := hprev
          _ ≤ gamma fp.u (n - 1) * total :=
            mul_le_mul_of_nonneg_left hsmall hγ
      have hexact : |exact + v (Fin.last n)| ≤ total := by
        have habs : |exact| ≤ ∑ i : Fin n, |w i| := by
          exact Finset.abs_sum_le_sum_abs w Finset.univ
        calc
          |exact + v (Fin.last n)| ≤ |exact| + |v (Fin.last n)| :=
            abs_add_le _ _
          _ ≤ (∑ i : Fin n, |w i|) + |v (Fin.last n)| :=
            add_le_add habs (le_refl _)
          _ = total := rfl
      have hpre :
          |old + v (Fin.last n)| ≤
            (gamma fp.u (n - 1) + 1) * total := by
        calc
          |old + v (Fin.last n)| =
              |(old - exact) + (exact + v (Fin.last n))| := by
                congr 1
                ring
          _ ≤ |old - exact| + |exact + v (Fin.last n)| := abs_add_le _ _
          _ ≤ gamma fp.u (n - 1) * total + total :=
            add_le_add hprev_total hexact
          _ = (gamma fp.u (n - 1) + 1) * total := by ring
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add old (v (Fin.last n))
      have hrec :
          recursiveSum fp.fl_add (n + 1) v =
            (old + v (Fin.last n)) * (1 + δ) := by
        simp only [recursiveSum, hn, ↓reduceDIte]
        exact hadd
      rw [hrec, Fin.sum_univ_castSucc, hsum_split]
      change
        |(old + v (Fin.last n)) * (1 + δ) -
          (exact + v (Fin.last n))| ≤ _
      calc
        |(old + v (Fin.last n)) * (1 + δ) -
            (exact + v (Fin.last n))| =
            |(old - exact) + (old + v (Fin.last n)) * δ| := by
              congr 1
              ring
        _ ≤ |old - exact| + |old + v (Fin.last n)| * |δ| := by
              simpa [abs_mul] using
                abs_add_le (old - exact) ((old + v (Fin.last n)) * δ)
        _ ≤ |old - exact| + |old + v (Fin.last n)| * fp.u := by
              gcongr
        _ ≤ gamma fp.u (n - 1) * total +
              ((gamma fp.u (n - 1) + 1) * total) * fp.u := by
              exact add_le_add hprev_total
                (mul_le_mul_of_nonneg_right hpre fp.u_nonneg)
        _ = ((1 + fp.u) * gamma fp.u (n - 1) + fp.u) * total := by
              ring
        _ ≤ gamma fp.u n * total := by
              apply mul_le_mul_of_nonneg_right _ htotal
              have hs := gamma_step fp.u (n - 1) fp.u_nonneg
                (by simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using hvalid_n)
              simpa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)] using hs

private lemma two_pow_sum_split {M : Type*} [AddCommMonoid M]
    (r : ℕ) (f : Fin (2 ^ (r + 1)) → M) :
    (∑ i, f i) =
      (∑ i : Fin (2 ^ r), f (leftIndex r i)) +
      (∑ i : Fin (2 ^ r), f (rightIndex r i)) := by
  let hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    simp [pow_succ, mul_two]
  rw [Fintype.sum_equiv (finCongr hp) f
    (fun j => f ((finCongr hp).symm j)) (fun _ => rfl)]
  rw [Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;>
    congr 1 <;> apply Fin.ext <;> simp [rightIndex]

private lemma pairwise_gamma_bound
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u r) :
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
      gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  induction r with
  | zero => simp [pairwiseSum, gamma]
  | succ r ih =>
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let al : ℝ := pairwiseSum fp.fl_add r vl
      let ar : ℝ := pairwiseSum fp.fl_add r vr
      let sl : ℝ := ∑ i : Fin (2 ^ r), vl i
      let sr : ℝ := ∑ i : Fin (2 ^ r), vr i
      let ml : ℝ := ∑ i : Fin (2 ^ r), |vl i|
      let mr : ℝ := ∑ i : Fin (2 ^ r), |vr i|
      let total : ℝ := ml + mr
      have hvalid_prev : GammaValid fp.u r := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid
        have hcast : (r : ℝ) ≤ (r : ℝ) + 1 := by linarith
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
      have hγ : 0 ≤ gamma fp.u r :=
        gamma_nonneg_of_valid fp.u r fp.u_nonneg hvalid_prev
      have htotal : 0 ≤ total := by
        dsimp [total, ml, mr]
        positivity
      have hleft := ih vl hvalid_prev
      have hright := ih vr hvalid_prev
      have hcombined :
          |(al + ar) - (sl + sr)| ≤ gamma fp.u r * total := by
        calc
          |(al + ar) - (sl + sr)| = |(al - sl) + (ar - sr)| := by
            congr 1
            ring
          _ ≤ |al - sl| + |ar - sr| := abs_add_le _ _
          _ ≤ gamma fp.u r * ml + gamma fp.u r * mr :=
            add_le_add hleft hright
          _ = gamma fp.u r * total := by ring
      have hexact : |sl + sr| ≤ total := by
        have hl : |sl| ≤ ml := by
          exact Finset.abs_sum_le_sum_abs vl Finset.univ
        have hr : |sr| ≤ mr := by
          exact Finset.abs_sum_le_sum_abs vr Finset.univ
        calc
          |sl + sr| ≤ |sl| + |sr| := abs_add_le _ _
          _ ≤ ml + mr := add_le_add hl hr
          _ = total := rfl
      have hpre : |al + ar| ≤ (gamma fp.u r + 1) * total := by
        calc
          |al + ar| = |((al + ar) - (sl + sr)) + (sl + sr)| := by
            congr 1
            ring
          _ ≤ |(al + ar) - (sl + sr)| + |sl + sr| := abs_add_le _ _
          _ ≤ gamma fp.u r * total + total := add_le_add hcombined hexact
          _ = (gamma fp.u r + 1) * total := by ring
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add al ar
      have hrec : pairwiseSum fp.fl_add (r + 1) v =
          (al + ar) * (1 + δ) := by
        simp only [pairwiseSum]
        exact hadd
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = sl + sr := by
        simpa [vl, vr, sl, sr] using two_pow_sum_split r v
      have hmass : (∑ i : Fin (2 ^ (r + 1)), |v i|) = total := by
        simpa [vl, vr, ml, mr, total] using
          two_pow_sum_split r (fun i => |v i|)
      rw [hrec, hsum, hmass]
      calc
        |(al + ar) * (1 + δ) - (sl + sr)| =
            |((al + ar) - (sl + sr)) + (al + ar) * δ| := by
              congr 1
              ring
        _ ≤ |(al + ar) - (sl + sr)| + |al + ar| * |δ| := by
              simpa [abs_mul] using
                abs_add_le ((al + ar) - (sl + sr)) ((al + ar) * δ)
        _ ≤ |(al + ar) - (sl + sr)| + |al + ar| * fp.u := by
              gcongr
        _ ≤ gamma fp.u r * total +
              ((gamma fp.u r + 1) * total) * fp.u := by
              exact add_le_add hcombined
                (mul_le_mul_of_nonneg_right hpre fp.u_nonneg)
        _ = ((1 + fp.u) * gamma fp.u r + fp.u) * total := by ring
        _ ≤ gamma fp.u (r + 1) * total := by
              exact mul_le_mul_of_nonneg_right
                (gamma_step fp.u r fp.u_nonneg hvalid) htotal

private lemma rank_le_two_pow_sub_one (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by decide)
      omega

theorem p01_t2_recursive_running_and_pairwise_bounds
    (fp : StandardAddModel) (r : ℕ) (v : Fin (2 ^ r) → ℝ)
    (hvalid : GammaValid fp.u (2 ^ r - 1)) :
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        fp.u * ∑ i : Fin (2 ^ r), |recursivePreRound fp.fl_add v i| ∧
    |recursiveSum fp.fl_add (2 ^ r) v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u (2 ^ r - 1) * ∑ i : Fin (2 ^ r), |v i| ∧
    |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  -- PROOF_START P01-T2-H001
  refine ⟨recursive_running_bound fp (2 ^ r) v, ?_, ?_⟩
  · exact recursive_gamma_bound fp (2 ^ r) v hvalid
  · apply pairwise_gamma_bound fp r v
    exact gammaValid_of_le fp.u fp.u_nonneg
      (rank_le_two_pow_sub_one r) hvalid

end HighamBench
