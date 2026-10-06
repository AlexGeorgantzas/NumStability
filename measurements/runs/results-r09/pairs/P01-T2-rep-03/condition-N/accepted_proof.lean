import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private lemma recursivePreRound_castSucc (flAdd : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) (i : Fin n) :
    recursivePreRound flAdd v i.castSucc =
      recursivePreRound flAdd (fun j => v j.castSucc) i := by
  rfl

private lemma recursivePreRound_last (flAdd : ℝ → ℝ → ℝ) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    recursivePreRound flAdd v (Fin.last n) =
      recursiveSum flAdd n (fun i => v i.castSucc) + v (Fin.last n) := by
  rfl

private lemma gamma_nonneg_of_valid {u : ℝ} (hu : 0 ≤ u) {n : ℕ}
    (h : GammaValid u n) : 0 ≤ gamma u n := by
  unfold GammaValid at h
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) (le_of_lt (sub_pos.mpr h))

private lemma gamma_step_bound {u : ℝ} (hu : 0 ≤ u) {n : ℕ}
    (h : GammaValid u (n + 1)) :
    (1 + u) * gamma u n + u ≤ gamma u (n + 1) := by
  unfold GammaValid at h
  have hn1 : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := sub_pos.mpr h
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [hcast] at hn1
  have hn : 0 < 1 - (n : ℝ) * u := by
    nlinarith
  unfold gamma
  rw [Nat.cast_add, Nat.cast_one]
  have heq :
      (1 + u) * ((n : ℝ) * u / (1 - (n : ℝ) * u)) + u =
        (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
    have hd' : 1 - u * (n : ℝ) ≠ 0 := by nlinarith
    apply (eq_div_iff (ne_of_gt hn)).2
    field_simp [ne_of_gt hn, hd']
    <;> ring
  rw [heq]
  apply (div_le_div_iff₀ hn hn1).2
  have hnum : 0 ≤ ((n : ℝ) + 1) * u :=
    mul_nonneg (by positivity) hu
  nlinarith

private lemma gammaValid_mono {u : ℝ} (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (h : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at h ⊢
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) hu) h

private lemma depth_le_two_pow_sub_one (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [pow_succ]
      have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
      omega

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
        simpa [recursiveSum, recursivePreRound] using
          mul_nonneg fp.u_nonneg (abs_nonneg (v 0))
      · let a := recursiveSum fp.fl_add n (fun i => v i.castSucc)
        let x := v (Fin.last n)
        let s := ∑ i : Fin n, v i.castSucc
        obtain ⟨δ, hδ, hadd⟩ := fp.model_add a x
        have hih := ih (fun i => v i.castSucc)
        rw [recursiveSum, dif_neg hn]
        change |fp.fl_add a x - ∑ i : Fin (n + 1), v i| ≤
          fp.u * ∑ i : Fin (n + 1), |recursivePreRound fp.fl_add v i|
        rw [hadd]
        rw [Fin.sum_univ_castSucc (fun i => v i)]
        rw [Fin.sum_univ_castSucc
          (fun i => |recursivePreRound fp.fl_add v i|)]
        simp_rw [recursivePreRound_castSucc]
        rw [recursivePreRound_last]
        change |(a + x) * (1 + δ) - (s + x)| ≤
          fp.u * ((∑ i : Fin n,
            |recursivePreRound fp.fl_add (fun j => v j.castSucc) i|) +
            |a + x|)
        have herr : (a + x) * (1 + δ) - (s + x) =
            (a - s) + δ * (a + x) := by ring
        rw [herr]
        calc
          |(a - s) + δ * (a + x)|
              ≤ |a - s| + |δ * (a + x)| := abs_add_le _ _
          _ = |a - s| + |δ| * |a + x| := by rw [abs_mul]
          _ ≤ |a - s| + fp.u * |a + x| := by
            gcongr
          _ ≤ fp.u * (∑ i : Fin n,
                |recursivePreRound fp.fl_add (fun j => v j.castSucc) i|) +
                fp.u * |a + x| := by
            gcongr
          _ = fp.u * ((∑ i : Fin n,
                |recursivePreRound fp.fl_add (fun j => v j.castSucc) i|) +
                |a + x|) := by ring

private lemma recursive_magnitude_succ (fp : StandardAddModel) :
    ∀ (m : ℕ) (v : Fin (m + 1) → ℝ), GammaValid fp.u m →
      |recursiveSum fp.fl_add (m + 1) v - ∑ i : Fin (m + 1), v i| ≤
        gamma fp.u m * ∑ i : Fin (m + 1), |v i| := by
  intro m
  induction m with
  | zero =>
      intro v hvalid
      simp [recursiveSum, gamma]
  | succ m ih =>
      intro v hvalid
      have hvalid_m : GammaValid fp.u m :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ m) hvalid
      let a := recursiveSum fp.fl_add (m + 1) (fun i => v i.castSucc)
      let s := ∑ i : Fin (m + 1), v i.castSucc
      let x := v (Fin.last (m + 1))
      let b := ∑ i : Fin (m + 1), |v i.castSucc|
      let t := b + |x|
      obtain ⟨δ, hδ, hadd⟩ := fp.model_add a x
      have hih := ih (fun i => v i.castSucc) hvalid_m
      have hs : |s| ≤ b := by
        dsimp [s, b]
        simpa using Finset.abs_sum_le_sum_abs
          (fun i : Fin (m + 1) => v i.castSucc) Finset.univ
      have hb : 0 ≤ b := by
        dsimp [b]
        positivity
      have ht : 0 ≤ t := by
        dsimp [t]
        positivity
      have hbt : b ≤ t := by
        dsimp [t]
        exact le_add_of_nonneg_right (abs_nonneg x)
      have hgamma : 0 ≤ gamma fp.u m :=
        gamma_nonneg_of_valid fp.u_nonneg hvalid_m
      have hstep : (1 + fp.u) * gamma fp.u m + fp.u ≤
          gamma fp.u (m + 1) :=
        gamma_step_bound fp.u_nonneg hvalid
      rw [recursiveSum, dif_neg (Nat.succ_ne_zero m)]
      change |fp.fl_add a x - ∑ i : Fin ((m + 1) + 1), v i| ≤
        gamma fp.u (m + 1) * ∑ i : Fin ((m + 1) + 1), |v i|
      rw [hadd]
      rw [Fin.sum_univ_castSucc (fun i => v i)]
      rw [Fin.sum_univ_castSucc (fun i => |v i|)]
      change |(a + x) * (1 + δ) - (s + x)| ≤
        gamma fp.u (m + 1) * t
      have herr : (a + x) * (1 + δ) - (s + x) =
          (a - s) + δ * (a + x) := by ring
      have hax : |a + x| ≤ |a - s| + t := by
        calc
          |a + x| = |(a - s) + (s + x)| := by congr 1 <;> ring
          _ ≤ |a - s| + |s + x| := abs_add_le _ _
          _ ≤ |a - s| + (|s| + |x|) := by gcongr; exact abs_add_le _ _
          _ ≤ |a - s| + t := by
            dsimp [t]
            gcongr
      rw [herr]
      calc
        |(a - s) + δ * (a + x)|
            ≤ |a - s| + |δ * (a + x)| := abs_add_le _ _
        _ = |a - s| + |δ| * |a + x| := by rw [abs_mul]
        _ ≤ |a - s| + fp.u * |a + x| := by gcongr
        _ ≤ |a - s| + fp.u * (|a - s| + t) := by
          nlinarith [mul_le_mul_of_nonneg_left hax fp.u_nonneg]
        _ = (1 + fp.u) * |a - s| + fp.u * t := by ring
        _ ≤ (1 + fp.u) * (gamma fp.u m * b) + fp.u * t := by
          have hcoef : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
          have hih' : |a - s| ≤ gamma fp.u m * b := hih
          nlinarith [mul_le_mul_of_nonneg_left hih' hcoef]
        _ ≤ ((1 + fp.u) * gamma fp.u m + fp.u) * t := by
          have hc : 0 ≤ (1 + fp.u) * gamma fp.u m :=
            mul_nonneg (by linarith [fp.u_nonneg]) hgamma
          nlinarith
        _ ≤ gamma fp.u (m + 1) * t := by
          exact mul_le_mul_of_nonneg_right hstep ht

private lemma sum_two_pow_split {M : Type*} [AddCommMonoid M]
    (r : ℕ) (f : Fin (2 ^ (r + 1)) → M) :
    (∑ i : Fin (2 ^ (r + 1)), f i) =
      (∑ i : Fin (2 ^ r), f (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), f (rightIndex r i) := by
  have hp : 2 ^ r + 2 ^ r = 2 ^ (r + 1) := by
    rw [pow_succ, Nat.mul_two]
  let e : Fin (2 ^ r + 2 ^ r) ≃ Fin (2 ^ (r + 1)) := finCongr hp
  calc
    (∑ i : Fin (2 ^ (r + 1)), f i) =
        ∑ i : Fin (2 ^ r + 2 ^ r), f (e i) := by
          symm
          exact Equiv.sum_comp e f
    _ = (∑ i : Fin (2 ^ r), f (e (Fin.castAdd (2 ^ r) i))) +
        ∑ i : Fin (2 ^ r), f (e (Fin.natAdd (2 ^ r) i)) := by
          exact Fin.sum_univ_add (fun i => f (e i))
    _ = (∑ i : Fin (2 ^ r), f (leftIndex r i)) +
        ∑ i : Fin (2 ^ r), f (rightIndex r i) := by
          have hleft (i : Fin (2 ^ r)) :
              e (Fin.castAdd (2 ^ r) i) = leftIndex r i := by
            apply Fin.ext
            rfl
          have hright (i : Fin (2 ^ r)) :
              e (Fin.natAdd (2 ^ r) i) = rightIndex r i := by
            apply Fin.ext
            change 2 ^ r + i.val = i.val + 2 ^ r
            omega
          simp_rw [hleft, hright]

private lemma rounded_combine_bound (fp : StandardAddModel)
    {a b s t A B g g' : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : |s| ≤ A) (ht : |t| ≤ B)
    (hg : 0 ≤ g)
    (ha : |a - s| ≤ g * A) (hb : |b - t| ≤ g * B)
    (hstep : (1 + fp.u) * g + fp.u ≤ g') :
    |fp.fl_add a b - (s + t)| ≤ g' * (A + B) := by
  obtain ⟨δ, hδ, hadd⟩ := fp.model_add a b
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have he : |a - s| + |b - t| ≤ g * (A + B) := by
    calc
      |a - s| + |b - t| ≤ g * A + g * B := add_le_add ha hb
      _ = g * (A + B) := by ring
  have hab : |a + b| ≤ (|a - s| + |b - t|) + (A + B) := by
    calc
      |a + b| = |((a - s) + (b - t)) + (s + t)| := by
        congr 1
        ring
      _ ≤ |(a - s) + (b - t)| + |s + t| := abs_add_le _ _
      _ ≤ (|a - s| + |b - t|) + (|s| + |t|) := by
        exact add_le_add (abs_add_le _ _) (abs_add_le _ _)
      _ ≤ (|a - s| + |b - t|) + (A + B) := by
        gcongr
  rw [hadd]
  have herr : (a + b) * (1 + δ) - (s + t) =
      ((a - s) + (b - t)) + δ * (a + b) := by ring
  rw [herr]
  calc
    |((a - s) + (b - t)) + δ * (a + b)|
        ≤ |(a - s) + (b - t)| + |δ * (a + b)| := abs_add_le _ _
    _ ≤ (|a - s| + |b - t|) + |δ| * |a + b| := by
      rw [abs_mul]
      gcongr
      exact abs_add_le _ _
    _ ≤ (|a - s| + |b - t|) + fp.u * |a + b| := by gcongr
    _ ≤ (|a - s| + |b - t|) +
        fp.u * ((|a - s| + |b - t|) + (A + B)) := by
      nlinarith [mul_le_mul_of_nonneg_left hab fp.u_nonneg]
    _ = (1 + fp.u) * (|a - s| + |b - t|) + fp.u * (A + B) := by ring
    _ ≤ (1 + fp.u) * (g * (A + B)) + fp.u * (A + B) := by
      have hc : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      nlinarith [mul_le_mul_of_nonneg_left he hc]
    _ = ((1 + fp.u) * g + fp.u) * (A + B) := by ring
    _ ≤ g' * (A + B) := mul_le_mul_of_nonneg_right hstep hAB

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
      have hvalid_r : GammaValid fp.u r :=
        gammaValid_mono fp.u_nonneg (Nat.le_succ r) hvalid
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let a := pairwiseSum fp.fl_add r vl
      let b := pairwiseSum fp.fl_add r vr
      let s := ∑ i : Fin (2 ^ r), vl i
      let t := ∑ i : Fin (2 ^ r), vr i
      let A := ∑ i : Fin (2 ^ r), |vl i|
      let B := ∑ i : Fin (2 ^ r), |vr i|
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hB : 0 ≤ B := by dsimp [B]; positivity
      have hs : |s| ≤ A := by
        dsimp [s, A]
        simpa using Finset.abs_sum_le_sum_abs vl Finset.univ
      have ht : |t| ≤ B := by
        dsimp [t, B]
        simpa using Finset.abs_sum_le_sum_abs vr Finset.univ
      have ha : |a - s| ≤ gamma fp.u r * A := ih vl hvalid_r
      have hb : |b - t| ≤ gamma fp.u r * B := ih vr hvalid_r
      have hg : 0 ≤ gamma fp.u r :=
        gamma_nonneg_of_valid fp.u_nonneg hvalid_r
      have hstep : (1 + fp.u) * gamma fp.u r + fp.u ≤
          gamma fp.u (r + 1) := gamma_step_bound fp.u_nonneg hvalid
      rw [pairwiseSum]
      change |fp.fl_add a b - ∑ i : Fin (2 ^ (r + 1)), v i| ≤
        gamma fp.u (r + 1) * ∑ i : Fin (2 ^ (r + 1)), |v i|
      rw [sum_two_pow_split r v]
      rw [sum_two_pow_split r (fun i => |v i|)]
      change |fp.fl_add a b - (s + t)| ≤ gamma fp.u (r + 1) * (A + B)
      exact rounded_combine_bound fp hA hB hs ht hg ha hb hstep

private lemma recursive_magnitude_bound (fp : StandardAddModel) (n : ℕ)
    (v : Fin n → ℝ) (hn : 0 < n) (hvalid : GammaValid fp.u (n - 1)) :
    |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
      gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  cases n with
  | zero => omega
  | succ m =>
      simpa using recursive_magnitude_succ fp m v hvalid

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
  constructor
  · exact recursive_running_bound fp (2 ^ r) v
  constructor
  · exact recursive_magnitude_bound fp (2 ^ r) v (by positivity) hvalid
  · have hvalid_r : GammaValid fp.u r :=
      gammaValid_mono fp.u_nonneg (depth_le_two_pow_sub_one r) hvalid
    exact pairwise_magnitude_bound fp r v hvalid_r

end HighamBench
