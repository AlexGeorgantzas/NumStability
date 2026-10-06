import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma gammaValid_mono {u : ℝ} (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (h : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at h ⊢
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  linarith

private lemma gamma_nonneg {u : ℝ} (hu : 0 ≤ u) {n : ℕ}
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  unfold gamma
  exact div_nonneg (mul_nonneg (by positivity) hu) (le_of_lt (sub_pos.mpr h))

private lemma gamma_step {u : ℝ} (hu : 0 ≤ u) (n : ℕ)
    (h : GammaValid u (n + 1)) :
    (1 + u) * gamma u n + u ≤ gamma u (n + 1) := by
  have hn : GammaValid u n := gammaValid_mono hu (Nat.le_succ n) h
  unfold GammaValid at h hn
  unfold gamma
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  have hdS : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        ((n + 1 : ℕ) : ℝ) * u / (1 - (n : ℝ) * u) := by
    have hdn' : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
    field_simp [hdn']
    push_cast
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left
  · positivity
  · exact hdS
  · push_cast
    nlinarith

private lemma recursivePreRound_castSucc (flAdd : ℝ → ℝ → ℝ)
    {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin n) :
    recursivePreRound flAdd v i.castSucc =
      recursivePreRound flAdd (fun j : Fin n => v j.castSucc) i := by
  simp [recursivePreRound]

private lemma sum_pow_succ_split {M : Type*} [AddCommMonoid M]
    (r : ℕ) (f : Fin (2 ^ (r + 1)) → M) :
    (∑ i : Fin (2 ^ (r + 1)), f i) =
      (∑ i : Fin (2 ^ r), f (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), f (rightIndex r i) := by
  let h : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by
    rw [pow_succ]
    omega
  rw [← (Fin.castOrderIso h).sum_comp f]
  rw [Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi
  · apply congrArg f
    apply Fin.ext
    simp [rightIndex]

private lemma recursivePreRound_last (flAdd : ℝ → ℝ → ℝ)
    {n : ℕ} (v : Fin (n + 1) → ℝ) :
    recursivePreRound flAdd v (Fin.last n) =
      recursiveSum flAdd n (fun j : Fin n => v j.castSucc) + v (Fin.last n) := by
  unfold recursivePreRound
  congr 2

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
        have hnonneg : 0 ≤ fp.u * |v 0| :=
          mul_nonneg fp.u_nonneg (abs_nonneg _)
        simpa [recursiveSum, recursivePreRound] using hnonneg
      · let w : Fin n → ℝ := fun i => v i.castSucc
        let a : ℝ := recursiveSum fp.fl_add n w
        let b : ℝ := v (Fin.last n)
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
        have hsum : (∑ i : Fin (n + 1), v i) = (∑ i : Fin n, w i) + b := by
          rw [Fin.sum_univ_castSucc]
        have hrec : recursiveSum fp.fl_add (n + 1) v = fp.fl_add a b := by
          simp [recursiveSum, hn, a, b, w]
        have hpre :
            (∑ i : Fin (n + 1), |recursivePreRound fp.fl_add v i|) =
              (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) + |a + b| := by
          rw [Fin.sum_univ_castSucc]
          congr 1
        have htri :
            |(a - ∑ i : Fin n, w i) + (a + b) * δ| ≤
              |a - ∑ i : Fin n, w i| + |a + b| * |δ| := by
          calc
            |(a - ∑ i : Fin n, w i) + (a + b) * δ| ≤
                |a - ∑ i : Fin n, w i| + |(a + b) * δ| := abs_add_le _ _
            _ = _ := by rw [abs_mul]
        rw [hrec, hsum, hadd, hpre]
        have hi := ih w
        calc
          |(a + b) * (1 + δ) - ((∑ i : Fin n, w i) + b)| =
              |(a - ∑ i : Fin n, w i) + (a + b) * δ| := by ring_nf
          _ ≤ |a - ∑ i : Fin n, w i| + |a + b| * |δ| := htri
          _ ≤ fp.u * (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) +
                |a + b| * fp.u := by gcongr
          _ = fp.u * ((∑ i : Fin n, |recursivePreRound fp.fl_add w i|) + |a + b|) := by
                ring

private lemma recursive_input_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin (n + 1) → ℝ), GammaValid fp.u n →
      |recursiveSum fp.fl_add (n + 1) v - ∑ i : Fin (n + 1), v i| ≤
        gamma fp.u n * ∑ i : Fin (n + 1), |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hvalid
      simp [recursiveSum, gamma]
  | succ n ih =>
      intro v hvalid
      let w : Fin (n + 1) → ℝ := fun i => v i.castSucc
      let a : ℝ := recursiveSum fp.fl_add (n + 1) w
      let b : ℝ := v (Fin.last (n + 1))
      let s : ℝ := ∑ i : Fin (n + 1), w i
      let A : ℝ := ∑ i : Fin (n + 1), |w i|
      let B : ℝ := |b|
      have hprev : GammaValid fp.u n :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ n) hvalid
      have hi := ih w hprev
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
      have hsum : (∑ i : Fin (n + 2), v i) = s + b := by
        rw [Fin.sum_univ_castSucc]
      have hsumabs : (∑ i : Fin (n + 2), |v i|) = A + B := by
        rw [Fin.sum_univ_castSucc]
      have hrec : recursiveSum fp.fl_add (n + 2) v = fp.fl_add a b := by
        simp [recursiveSum, a, b, w]
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      have hB : 0 ≤ B := by
        exact abs_nonneg _
      have hgamma : 0 ≤ gamma fp.u n :=
        gamma_nonneg fp.u_nonneg hprev
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have hsabs : |s| ≤ A := by
        exact Finset.abs_sum_le_sum_abs w Finset.univ
      have hexact : |s + b| ≤ A + B := by
        calc
          |s + b| ≤ |s| + |b| := abs_add_le _ _
          _ ≤ A + B := add_le_add hsabs le_rfl
      have hstep := gamma_step fp.u_nonneg n hvalid
      have hu_le : fp.u ≤ gamma fp.u (n + 1) := by
        calc
          fp.u ≤ (1 + fp.u) * gamma fp.u n + fp.u := by
            exact le_add_of_nonneg_left (mul_nonneg (by linarith [fp.u_nonneg]) hgamma)
          _ ≤ gamma fp.u (n + 1) := hstep
      rw [hrec, hsum, hadd, hsumabs]
      change |(a + b) * (1 + δ) - (s + b)| ≤ gamma fp.u (n + 1) * (A + B)
      calc
        |(a + b) * (1 + δ) - (s + b)| =
            |(1 + δ) * (a - s) + δ * (s + b)| := by ring_nf
        _ ≤ |1 + δ| * |a - s| + |δ| * |s + b| := by
          calc
            |(1 + δ) * (a - s) + δ * (s + b)| ≤
                |(1 + δ) * (a - s)| + |δ * (s + b)| := abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u n * A) + fp.u * (A + B) := by
          gcongr
          all_goals linarith [fp.u_nonneg]
        _ = ((1 + fp.u) * gamma fp.u n + fp.u) * A + fp.u * B := by ring
        _ ≤ gamma fp.u (n + 1) * A + gamma fp.u (n + 1) * B :=
          add_le_add (mul_le_mul_of_nonneg_right hstep hA)
            (mul_le_mul_of_nonneg_right hu_le hB)
        _ = gamma fp.u (n + 1) * (A + B) := by ring

private lemma recursive_input_bound_general (fp : StandardAddModel) (n : ℕ)
    (v : Fin n → ℝ) (hn : 0 < n) (hvalid : GammaValid fp.u (n - 1)) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  cases n with
  | zero => simp at hn
  | succ n =>
      simpa using recursive_input_bound fp n v hvalid

private lemma le_two_pow_sub_one (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hp : 1 ≤ 2 ^ r := by exact one_le_pow₀ (by omega)
      rw [pow_succ]
      omega

private lemma pairwise_input_bound (fp : StandardAddModel) :
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
      let wL : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let wR : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let a : ℝ := pairwiseSum fp.fl_add r wL
      let b : ℝ := pairwiseSum fp.fl_add r wR
      let sL : ℝ := ∑ i : Fin (2 ^ r), wL i
      let sR : ℝ := ∑ i : Fin (2 ^ r), wR i
      let A : ℝ := ∑ i : Fin (2 ^ r), |wL i|
      let B : ℝ := ∑ i : Fin (2 ^ r), |wR i|
      have hprev : GammaValid fp.u r :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ r) hvalid
      have hiL := ih wL hprev
      have hiR := ih wR hprev
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = sL + sR := by
        rw [sum_pow_succ_split]
      have hsumabs : (∑ i : Fin (2 ^ (r + 1)), |v i|) = A + B := by
        rw [sum_pow_succ_split]
      have hrec : pairwiseSum fp.fl_add (r + 1) v = fp.fl_add a b := by
        simp [pairwiseSum, a, b, wL, wR]
      have hA : 0 ≤ A := by
        dsimp [A]
        positivity
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      have hgamma : 0 ≤ gamma fp.u r :=
        gamma_nonneg fp.u_nonneg hprev
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
      have herrs : |(a - sL) + (b - sR)| ≤ gamma fp.u r * (A + B) := by
        calc
          |(a - sL) + (b - sR)| ≤ |a - sL| + |b - sR| := abs_add_le _ _
          _ ≤ gamma fp.u r * A + gamma fp.u r * B := add_le_add hiL hiR
          _ = gamma fp.u r * (A + B) := by ring
      have hsLabs : |sL| ≤ A := by
        exact Finset.abs_sum_le_sum_abs wL Finset.univ
      have hsRabs : |sR| ≤ B := by
        exact Finset.abs_sum_le_sum_abs wR Finset.univ
      have hexact : |sL + sR| ≤ A + B := by
        calc
          |sL + sR| ≤ |sL| + |sR| := abs_add_le _ _
          _ ≤ A + B := add_le_add hsLabs hsRabs
      have hstep := gamma_step fp.u_nonneg r hvalid
      rw [hrec, hsum, hadd, hsumabs]
      change |(a + b) * (1 + δ) - (sL + sR)| ≤ gamma fp.u (r + 1) * (A + B)
      calc
        |(a + b) * (1 + δ) - (sL + sR)| =
            |(1 + δ) * ((a - sL) + (b - sR)) + δ * (sL + sR)| := by ring_nf
        _ ≤ |1 + δ| * |(a - sL) + (b - sR)| + |δ| * |sL + sR| := by
          calc
            |(1 + δ) * ((a - sL) + (b - sR)) + δ * (sL + sR)| ≤
                |(1 + δ) * ((a - sL) + (b - sR))| + |δ * (sL + sR)| :=
              abs_add_le _ _
            _ = _ := by rw [abs_mul, abs_mul]
        _ ≤ (1 + fp.u) * (gamma fp.u r * (A + B)) + fp.u * (A + B) := by
          gcongr
          all_goals linarith [fp.u_nonneg]
        _ = ((1 + fp.u) * gamma fp.u r + fp.u) * (A + B) := by ring
        _ ≤ gamma fp.u (r + 1) * (A + B) :=
          mul_le_mul_of_nonneg_right hstep (add_nonneg hA hB)

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
  have hpairvalid : GammaValid fp.u r :=
    gammaValid_mono fp.u_nonneg (le_two_pow_sub_one r) hvalid
  exact ⟨recursive_running_bound fp (2 ^ r) v,
    recursive_input_bound_general fp (2 ^ r) v (by positivity) hvalid,
    pairwise_input_bound fp r v hpairvalid⟩

end HighamBench
