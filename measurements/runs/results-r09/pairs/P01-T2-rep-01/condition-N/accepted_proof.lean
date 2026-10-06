import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma gammaValid_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hn : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at *
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  nlinarith

private lemma gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at hv
  unfold gamma
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  exact div_nonneg (mul_nonneg hn hu) (le_of_lt (sub_pos.mpr hv))

private lemma gamma_step {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) :
    gamma u n * (1 + u) + u ≤ gamma u (n + 1) := by
  unfold GammaValid at hv
  rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num] at hv
  have hvn : (n : ℝ) * u < 1 := by
    have hn : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  unfold gamma
  rw [Nat.cast_add, Nat.cast_one]
  have hd0 : 0 < 1 - (n : ℝ) * u := by linarith
  have hd1 : 0 < 1 - ((n : ℝ) + 1) * u := by linarith
  rw [show
    (n : ℝ) * u / (1 - (n : ℝ) * u) * (1 + u) + u =
      ((n : ℝ) + 1) * u / (1 - (n : ℝ) * u) by
        field_simp
        <;> ring]
  apply (div_le_div_iff₀ hd0 hd1).2
  nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) hu]

private lemma u_le_gamma_succ {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : GammaValid u (n + 1)) : u ≤ gamma u (n + 1) := by
  have hs := gamma_step (n := n) hu hv
  have hg : 0 ≤ gamma u n :=
    gamma_nonneg hu (gammaValid_mono hu (Nat.le_succ n) hv)
  have h1 : 0 ≤ 1 + u := by linarith
  nlinarith

private lemma rounded_add_gamma (fp : StandardAddModel) (n : ℕ)
    (a b x y A B : ℝ) (hv : GammaValid fp.u (n + 1))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : |a - x| ≤ gamma fp.u n * A)
    (hb : |b - y| ≤ gamma fp.u n * B)
    (hx : |x| ≤ A) (hy : |y| ≤ B) :
    |fp.fl_add a b - (x + y)| ≤ gamma fp.u (n + 1) * (A + B) := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
  have hg : 0 ≤ gamma fp.u n :=
    gamma_nonneg fp.u_nonneg
      (gammaValid_mono fp.u_nonneg (Nat.le_succ n) hv)
  have hδ1 : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by simpa using add_le_add_left hδ 1
  have hstep := gamma_step fp.u_nonneg hv
  calc
    |fp.fl_add a b - (x + y)| =
        |((a - x) + (b - y)) * (1 + δ) + (x + y) * δ| := by
          rw [hfl]
          congr 1
          ring
    _ ≤ |(a - x) + (b - y)| * |1 + δ| + |x + y| * |δ| := by
          simpa only [abs_mul] using
            (abs_add_le (((a - x) + (b - y)) * (1 + δ)) ((x + y) * δ))
    _ ≤ (|a - x| + |b - y|) * |1 + δ| + (|x| + |y|) * |δ| := by
          gcongr <;> apply abs_add_le
    _ ≤ (gamma fp.u n * A + gamma fp.u n * B) * (1 + fp.u) +
          (A + B) * fp.u := by
          gcongr
    _ = (gamma fp.u n * (1 + fp.u) + fp.u) * (A + B) := by ring
    _ ≤ gamma fp.u (n + 1) * (A + B) := by
          exact mul_le_mul_of_nonneg_right hstep (add_nonneg hA hB)

private lemma recursivePreRound_castSucc (flAdd : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    recursivePreRound flAdd v i.castSucc =
      recursivePreRound flAdd (fun j : Fin n => v j.castSucc) i := by
  rfl

private lemma recursivePreRound_last (flAdd : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    recursivePreRound flAdd v (Fin.last n) =
      recursiveSum flAdd n (fun i : Fin n => v i.castSucc) + v (Fin.last n) := by
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
        simp [recursiveSum, recursivePreRound]
        exact mul_nonneg fp.u_nonneg (abs_nonneg _)
      · let w : Fin n → ℝ := fun i => v i.castSucc
        let a : ℝ := recursiveSum fp.fl_add n w
        let x : ℝ := ∑ i : Fin n, w i
        let y : ℝ := v (Fin.last n)
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add a y
        have hih := ih w
        have hsum : (∑ i : Fin (n + 1), v i) = x + y := by
          rw [Fin.sum_univ_castSucc]
        have hrec : recursiveSum fp.fl_add (n + 1) v = fp.fl_add a y := by
          simp [recursiveSum, hn, a, y, w]
        have hpre :
            (∑ i : Fin (n + 1), |recursivePreRound fp.fl_add v i|) =
              (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) + |a + y| := by
          rw [Fin.sum_univ_castSucc]
          simp_rw [recursivePreRound_castSucc]
          rw [recursivePreRound_last]
        calc
          |recursiveSum fp.fl_add (n + 1) v - ∑ i : Fin (n + 1), v i| =
              |(a - x) + (a + y) * δ| := by
                rw [hrec, hsum, hfl]
                congr 1
                ring
          _ ≤ |a - x| + |a + y| * |δ| := by
                simpa only [abs_mul] using abs_add_le (a - x) ((a + y) * δ)
          _ ≤ fp.u * (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) +
                |a + y| * fp.u := by
                gcongr
          _ = fp.u * ∑ i : Fin (n + 1), |recursivePreRound fp.fl_add v i| := by
                rw [hpre]
                ring

private lemma recursive_gamma_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ), GammaValid fp.u (n - 1) →
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp [recursiveSum, gamma]
  | succ n ih =>
      intro v hv
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, gamma]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hvn : GammaValid fp.u n := by simpa using hv
        have hvprev : GammaValid fp.u (n - 1) :=
          gammaValid_mono fp.u_nonneg (Nat.sub_le n 1) hvn
        let w : Fin n → ℝ := fun i => v i.castSucc
        let a : ℝ := recursiveSum fp.fl_add n w
        let x : ℝ := ∑ i : Fin n, w i
        let y : ℝ := v (Fin.last n)
        let A : ℝ := ∑ i : Fin n, |w i|
        let B : ℝ := |y|
        have ha : |a - x| ≤ gamma fp.u (n - 1) * A := ih w hvprev
        have hb : |y - y| ≤ gamma fp.u (n - 1) * B := by
          rw [sub_self, abs_zero]
          exact mul_nonneg (gamma_nonneg fp.u_nonneg hvprev) (abs_nonneg _)
        have hx : |x| ≤ A := by
          exact Finset.abs_sum_le_sum_abs w Finset.univ
        have hy : |y| ≤ B := le_rfl
        have hA : 0 ≤ A := by positivity
        have hB : 0 ≤ B := abs_nonneg _
        have hcombine := rounded_add_gamma fp (n - 1) a y x y A B
          (by simpa [Nat.sub_add_cancel hnpos] using hvn) hA hB ha hb hx hy
        have hrec : recursiveSum fp.fl_add (n + 1) v = fp.fl_add a y := by
          simp [recursiveSum, hn, a, y, w]
        have hsum : (∑ i : Fin (n + 1), v i) = x + y := by
          rw [Fin.sum_univ_castSucc]
        have habs : (∑ i : Fin (n + 1), |v i|) = A + B := by
          rw [Fin.sum_univ_castSucc]
        rw [hrec, hsum, habs]
        simpa [Nat.sub_add_cancel hnpos] using hcombine

private lemma sum_pow_succ_split (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  have hpow : 2 ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [pow_succ]
    omega
  let e : Fin (2 ^ (r + 1)) ≃ Fin (2 ^ r + 2 ^ r) :=
    (Fin.castOrderIso hpow).toEquiv
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
              simp [e, leftIndex, rightIndex, Fin.castOrderIso, Fin.natAdd] <;> omega

private lemma pairwise_gamma_bound (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin (2 ^ r) → ℝ), GammaValid fp.u r →
      |pairwiseSum fp.fl_add r v - ∑ i : Fin (2 ^ r), v i| ≤
        gamma fp.u r * ∑ i : Fin (2 ^ r), |v i| := by
  intro r
  induction r with
  | zero =>
      intro v hv
      simp [pairwiseSum, gamma]
  | succ r ih =>
      intro v hv
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let a : ℝ := pairwiseSum fp.fl_add r vl
      let b : ℝ := pairwiseSum fp.fl_add r vr
      let x : ℝ := ∑ i : Fin (2 ^ r), vl i
      let y : ℝ := ∑ i : Fin (2 ^ r), vr i
      let A : ℝ := ∑ i : Fin (2 ^ r), |vl i|
      let B : ℝ := ∑ i : Fin (2 ^ r), |vr i|
      have hvr : GammaValid fp.u r :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ r) hv
      have ha : |a - x| ≤ gamma fp.u r * A := ih vl hvr
      have hb : |b - y| ≤ gamma fp.u r * B := ih vr hvr
      have hx : |x| ≤ A := Finset.abs_sum_le_sum_abs vl Finset.univ
      have hy : |y| ≤ B := Finset.abs_sum_le_sum_abs vr Finset.univ
      have hA : 0 ≤ A := by positivity
      have hB : 0 ≤ B := by positivity
      have hcombine := rounded_add_gamma fp r a b x y A B hv hA hB ha hb hx hy
      have hrec : pairwiseSum fp.fl_add (r + 1) v = fp.fl_add a b := by
        simp [pairwiseSum, a, b, vl, vr]
      have hsum : (∑ i : Fin (2 ^ (r + 1)), v i) = x + y := by
        rw [sum_pow_succ_split]
      have habs : (∑ i : Fin (2 ^ (r + 1)), |v i|) = A + B := by
        rw [sum_pow_succ_split]
      rw [hrec, hsum, habs]
      exact hcombine

private lemma le_two_pow_sub_one : ∀ r : ℕ, r ≤ 2 ^ r - 1 := by
  intro r
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
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
  exact ⟨recursive_running_bound fp (2 ^ r) v,
    recursive_gamma_bound fp (2 ^ r) v hvalid,
    pairwise_gamma_bound fp r v
      (gammaValid_mono fp.u_nonneg (le_two_pow_sub_one r) hvalid)⟩

end HighamBench
