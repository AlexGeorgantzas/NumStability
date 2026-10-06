import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hvalid
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma gamma_step {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : GammaValid u (n + 1)) :
    (1 + u) * gamma u n + u ≤ gamma u (n + 1) := by
  unfold GammaValid at hvalid
  have hn1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  have hn : 0 < 1 - (n : ℝ) * u := by
    norm_num at hvalid ⊢
    nlinarith
  have hn1' : 0 < 1 - ((n : ℝ) + 1) * u := by
    convert hn1 using 1 <;> norm_num
  unfold gamma
  norm_num at hvalid ⊢
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    apply (eq_div_iff (ne_of_gt hn)).2
    calc
      ((1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u) *
            (1 - (n : ℝ) * u) =
          (1 + u) * (((n : ℝ) * u / (1 - (n : ℝ) * u)) *
            (1 - (n : ℝ) * u)) + u * (1 - (n : ℝ) * u) := by ring
      _ = (1 + u) * ((n : ℝ) * u) + u * (1 - (n : ℝ) * u) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hn)]
      _ = ((n : ℝ) + 1) * u := by ring
  rw [heq]
  apply (div_le_div_iff₀ hn hn1').2
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) hu]

private lemma gammaValid_of_le {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hvalid : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at hvalid ⊢
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hmn) hu) hvalid

private lemma recursive_running_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ),
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        fp.u * ∑ i : Fin n, |recursivePreRound fp.fl_add v i| := by
  intro n
  induction n with
  | zero =>
      intro v
      simp [recursiveSum]
  | succ n ih =>
      intro v
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, recursivePreRound]
        exact mul_nonneg fp.u_nonneg (abs_nonneg _)
      · let w : Fin n → ℝ := fun i => v i.castSucc
        let s : ℝ := recursiveSum fp.fl_add n w
        let x : ℝ := v (Fin.last n)
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add s x
        have hrec :
            |s - ∑ i : Fin n, w i| ≤
              fp.u * ∑ i : Fin n, |recursivePreRound fp.fl_add w i| := ih w
        have hpre (i : Fin n) :
            recursivePreRound fp.fl_add v i.castSucc =
              recursivePreRound fp.fl_add w i := by
          unfold recursivePreRound
          simp only [Fin.val_castSucc, w]
          congr 2
        have hlast : recursivePreRound fp.fl_add v (Fin.last n) = s + x := by
          simp only [recursivePreRound, Fin.val_last, s, x, w]
          congr 1
        rw [recursiveSum]
        simp only [dif_neg hn]
        rw [hadd, Fin.sum_univ_castSucc]
        calc
          |(s + x) * (1 + δ) - ((∑ i : Fin n, w i) + x)|
              = |(s - ∑ i : Fin n, w i) + (s + x) * δ| := by ring_nf
          _ ≤ |s - ∑ i : Fin n, w i| + |(s + x) * δ| := abs_add_le _ _
          _ ≤ fp.u * (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) +
                fp.u * |s + x| := by
              gcongr
              simpa [abs_mul, mul_comm] using
                mul_le_mul_of_nonneg_left hδ (abs_nonneg (s + x))
          _ = fp.u * ∑ i : Fin (n + 1),
                |recursivePreRound fp.fl_add v i| := by
              rw [Fin.sum_univ_castSucc]
              simp_rw [hpre]
              rw [hlast, mul_add]

private lemma recursive_magnitude_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ), GammaValid fp.u (n - 1) →
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hvalid
      simp [recursiveSum]
  | succ n ih =>
      intro v hvalid
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, gamma]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hsub : n - 1 + 1 = n := Nat.sub_add_cancel hnpos
        have hvalidN : GammaValid fp.u n := by simpa using hvalid
        have hvalidPrev : GammaValid fp.u (n - 1) :=
          gammaValid_of_le fp.u_nonneg (Nat.sub_le n 1) hvalidN
        have hvalidStep : GammaValid fp.u ((n - 1) + 1) := by
          rwa [hsub]
        have hstep := gamma_step fp.u_nonneg hvalidStep
        rw [hsub] at hstep
        have hgammaPrev : 0 ≤ gamma fp.u (n - 1) :=
          gamma_nonneg fp.u_nonneg hvalidPrev
        have huGamma : fp.u ≤ gamma fp.u n := by
          have hprod : 0 ≤ (1 + fp.u) * gamma fp.u (n - 1) :=
            mul_nonneg (by linarith [fp.u_nonneg]) hgammaPrev
          linarith
        let w : Fin n → ℝ := fun i => v i.castSucc
        let s : ℝ := recursiveSum fp.fl_add n w
        let x : ℝ := v (Fin.last n)
        let t : ℝ := ∑ i : Fin n, w i
        let a : ℝ := ∑ i : Fin n, |w i|
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add s x
        have hrec : |s - t| ≤ gamma fp.u (n - 1) * a := by
          simpa [s, t, a] using ih w hvalidPrev
        have hfactor : |1 + δ| ≤ 1 + fp.u := by
          calc
            |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
            _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
        have hsum : |t + x| ≤ a + |x| := by
          calc
            |t + x| ≤ |t| + |x| := abs_add_le _ _
            _ ≤ a + |x| := by
              gcongr
              exact Finset.abs_sum_le_sum_abs _ _
        have ha : 0 ≤ a := by
          dsimp [a]
          positivity
        rw [recursiveSum]
        simp only [dif_neg hn]
        rw [hadd, Fin.sum_univ_castSucc]
        change |(s + x) * (1 + δ) - (t + x)| ≤ _
        calc
          |(s + x) * (1 + δ) - (t + x)| =
              |(s - t) * (1 + δ) + (t + x) * δ| := by ring_nf
          _ ≤ |(s - t) * (1 + δ)| + |(t + x) * δ| := abs_add_le _ _
          _ = |s - t| * |1 + δ| + |t + x| * |δ| := by
            rw [abs_mul, abs_mul]
          _ ≤ (gamma fp.u (n - 1) * a) * (1 + fp.u) +
                (a + |x|) * fp.u := by
            exact add_le_add
              (mul_le_mul hrec hfactor (abs_nonneg _) (mul_nonneg hgammaPrev ha))
              (mul_le_mul hsum hδ (abs_nonneg _) (by positivity))
          _ = ((1 + fp.u) * gamma fp.u (n - 1) + fp.u) * a +
                fp.u * |x| := by ring
          _ ≤ gamma fp.u n * a + gamma fp.u n * |x| := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right hstep ha)
              (mul_le_mul_of_nonneg_right huGamma (abs_nonneg x))
          _ = gamma fp.u ((n + 1) - 1) *
                ∑ i : Fin (n + 1), |v i| := by
            rw [Fin.sum_univ_castSucc, mul_add]
            simp only [Nat.add_sub_cancel, a, w, x]

private lemma sum_pairwise_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  have hp : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    simp [pow_succ, mul_two]
  let e : Fin (2 ^ (r + 1)) ≃ Fin (2 ^ r + 2 ^ r) :=
    (Fin.castOrderIso hp).toEquiv
  let f : Fin (2 ^ r + 2 ^ r) → ℝ := fun i => v (e.symm i)
  have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = ∑ i, f i := by
    simpa [f] using e.sum_comp f
  have hleft (i : Fin (2 ^ r)) :
      f (Fin.castAdd (2 ^ r) i) = v (leftIndex r i) := by
    dsimp [f, e]
    congr 1
  have hright (i : Fin (2 ^ r)) :
      f (Fin.natAdd (2 ^ r) i) = v (rightIndex r i) := by
    dsimp [f, e]
    congr 1
    apply Fin.ext
    simp [rightIndex, Nat.add_comm]
  rw [hsum, Fin.sum_univ_add]
  exact congrArg₂ (· + ·)
    (Finset.sum_congr rfl (fun i _ => hleft i))
    (Finset.sum_congr rfl (fun i _ => hright i))

private lemma pairwise_magnitude_bound (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ), GammaValid fp.u r →
      |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  intro r
  induction r with
  | zero =>
      intro v hvalid
      simp [pairwiseSum, gamma]
  | succ r ih =>
      intro v hvalid
      have hvalidPrev : GammaValid fp.u r :=
        gammaValid_of_le fp.u_nonneg (Nat.le_succ r) hvalid
      have hgammaPrev : 0 ≤ gamma fp.u r :=
        gamma_nonneg fp.u_nonneg hvalidPrev
      have hstep := gamma_step fp.u_nonneg hvalid
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let sl : ℝ := pairwiseSum fp.fl_add r vl
      let sr : ℝ := pairwiseSum fp.fl_add r vr
      let tl : ℝ := ∑ i : Fin (2 ^ r), vl i
      let tr : ℝ := ∑ i : Fin (2 ^ r), vr i
      let al : ℝ := ∑ i : Fin (2 ^ r), |vl i|
      let ar : ℝ := ∑ i : Fin (2 ^ r), |vr i|
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add sl sr
      have hl : |sl - tl| ≤ gamma fp.u r * al := by
        simpa [sl, tl, al] using ih vl hvalidPrev
      have hr : |sr - tr| ≤ gamma fp.u r * ar := by
        simpa [sr, tr, ar] using ih vr hvalidPrev
      have hal : 0 ≤ al := by
        dsimp [al]
        positivity
      have har : 0 ≤ ar := by
        dsimp [ar]
        positivity
      have herr :
          |(sl - tl) + (sr - tr)| ≤ gamma fp.u r * (al + ar) := by
        calc
          |(sl - tl) + (sr - tr)| ≤ |sl - tl| + |sr - tr| := abs_add_le _ _
          _ ≤ gamma fp.u r * al + gamma fp.u r * ar := add_le_add hl hr
          _ = gamma fp.u r * (al + ar) := by ring
      have hfactor : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hsum : |tl + tr| ≤ al + ar := by
        calc
          |tl + tr| ≤ |tl| + |tr| := abs_add_le _ _
          _ ≤ al + ar := by
            apply add_le_add
            · dsimp [tl, al]
              exact Finset.abs_sum_le_sum_abs _ _
            · dsimp [tr, ar]
              exact Finset.abs_sum_le_sum_abs _ _
      have habsSplit := sum_pairwise_split r (fun i => |v i|)
      rw [pairwiseSum]
      rw [hadd, sum_pairwise_split r v]
      change |(sl + sr) * (1 + δ) - (tl + tr)| ≤ _
      calc
        |(sl + sr) * (1 + δ) - (tl + tr)| =
            |((sl - tl) + (sr - tr)) * (1 + δ) + (tl + tr) * δ| := by
              ring_nf
        _ ≤ |((sl - tl) + (sr - tr)) * (1 + δ)| +
              |(tl + tr) * δ| := abs_add_le _ _
        _ = |(sl - tl) + (sr - tr)| * |1 + δ| + |tl + tr| * |δ| := by
              rw [abs_mul, abs_mul]
        _ ≤ (gamma fp.u r * (al + ar)) * (1 + fp.u) +
              (al + ar) * fp.u := by
              exact add_le_add
                (mul_le_mul herr hfactor (abs_nonneg _)
                  (mul_nonneg hgammaPrev (add_nonneg hal har)))
                (mul_le_mul hsum hδ (abs_nonneg _) (add_nonneg hal har))
        _ = ((1 + fp.u) * gamma fp.u r + fp.u) * (al + ar) := by ring
        _ ≤ gamma fp.u (r + 1) * (al + ar) :=
              mul_le_mul_of_nonneg_right hstep (add_nonneg hal har)
        _ = gamma fp.u (r + 1) * ∑ i : Fin (2 ^ (r + 1)), |v i| := by
              rw [habsSplit]

private lemma rank_le_pow_sub (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hp := Nat.one_le_two_pow (n := r)
      rw [pow_succ]
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
  · exact recursive_magnitude_bound fp (2 ^ r) v hvalid
  · exact pairwise_magnitude_bound fp r v
      (gammaValid_of_le fp.u_nonneg (rank_le_pow_sub r) hvalid)

end HighamBench
