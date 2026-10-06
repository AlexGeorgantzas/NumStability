import HighamBench.P01Definitions

namespace HighamBench

open scoped BigOperators

private theorem gammaValid_mono {u : ℝ} (hu : 0 ≤ u) {m n : ℕ}
    (hmn : m ≤ n) (hvalid : GammaValid u n) : GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hvalid

private theorem gamma_nonneg_of_valid {u : ℝ} (hu : 0 ≤ u) {n : ℕ}
    (hvalid : GammaValid u n) : 0 ≤ gamma u n := by
  rw [gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr hvalid))

private theorem gamma_step_bound {u : ℝ} (hu : 0 ≤ u) (k : ℕ)
    (hvalid : GammaValid u (k + 1)) :
    0 ≤ gamma u k ∧ (1 + u) * gamma u k + u ≤ gamma u (k + 1) := by
  have hkvalid : GammaValid u k :=
    gammaValid_mono hu (Nat.le_add_right k 1) hvalid
  have hkpos : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hkvalid
  have hkne' : 1 - u * (k : ℝ) ≠ 0 := by
    rw [mul_comm]
    exact ne_of_gt hkpos
  have hskpos : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  constructor
  · exact gamma_nonneg_of_valid hu hkvalid
  · calc
      (1 + u) * gamma u k + u =
          (((k + 1 : ℕ) : ℝ) * u) / (1 - (k : ℝ) * u) := by
            rw [gamma]
            norm_num [Nat.cast_add]
            field_simp [ne_of_gt hkpos, hkne']
            ring
      _ ≤ (((k + 1 : ℕ) : ℝ) * u) /
            (1 - ((k + 1 : ℕ) : ℝ) * u) := by
            apply div_le_div_of_nonneg_left
            · exact mul_nonneg (Nat.cast_nonneg _) hu
            · exact hskpos
            · norm_num at *
              nlinarith
      _ = gamma u (k + 1) := by rfl

private theorem sum_halves (r : ℕ) (v : Fin (2 ^ (r + 1)) → ℝ) :
    (∑ i : Fin (2 ^ (r + 1)), v i) =
      (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
      ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
  let N := 2 ^ r
  have hpow : N + N = 2 ^ (r + 1) := by
    dsimp [N]
    rw [pow_succ]
    omega
  let e : Fin (N + N) ≃ Fin (2 ^ (r + 1)) := finCongr hpow
  calc
    (∑ i : Fin (2 ^ (r + 1)), v i) =
        ∑ i : Fin (N + N), v (e i) := (e.sum_comp v).symm
    _ = (∑ i : Fin N, v (e (Fin.castAdd N i))) +
          ∑ i : Fin N, v (e (Fin.natAdd N i)) := Fin.sum_univ_add _
    _ = (∑ i : Fin (2 ^ r), v (leftIndex r i)) +
          ∑ i : Fin (2 ^ r), v (rightIndex r i) := by
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi
        congr 1
        apply Fin.ext
        simp [e, N, leftIndex, rightIndex]

private theorem recursive_running_bound (fp : StandardAddModel) :
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
        let c := recursiveSum fp.fl_add n w
        let a := ∑ i : Fin n, w i
        let x := v (Fin.last n)
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add c x
        have hpre (i : Fin n) :
            recursivePreRound fp.fl_add w i =
              recursivePreRound fp.fl_add v i.castSucc := by
          rfl
        have hprelast :
            recursivePreRound fp.fl_add v (Fin.last n) = c + x := by
          rfl
        rw [recursiveSum]
        simp only [hn, ↓reduceDIte]
        rw [hfl, Fin.sum_univ_castSucc]
        change |(c + x) * (1 + δ) - (a + x)| ≤ _
        calc
          |(c + x) * (1 + δ) - (a + x)| =
              |(c - a) + (c + x) * δ| := by congr 1 <;> ring
          _ ≤ |c - a| + |(c + x) * δ| := abs_add_le _ _
          _ = |c - a| + |c + x| * |δ| := by rw [abs_mul]
          _ ≤ fp.u * (∑ i : Fin n, |recursivePreRound fp.fl_add w i|) +
                fp.u * |c + x| := by
              exact add_le_add (ih w)
                (by
                  simpa [mul_comm] using
                    (mul_le_mul_of_nonneg_left hδ (abs_nonneg (c + x))))
          _ = fp.u * ∑ i : Fin (n + 1),
                |recursivePreRound fp.fl_add v i| := by
              rw [Fin.sum_univ_castSucc]
              simp_rw [← hpre]
              rw [hprelast]
              ring

private theorem pairwise_gamma_bound (fp : StandardAddModel) :
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
      let vl : Fin (2 ^ r) → ℝ := fun i => v (leftIndex r i)
      let vr : Fin (2 ^ r) → ℝ := fun i => v (rightIndex r i)
      let pl := pairwiseSum fp.fl_add r vl
      let pr := pairwiseSum fp.fl_add r vr
      let al := ∑ i : Fin (2 ^ r), vl i
      let ar := ∑ i : Fin (2 ^ r), vr i
      let ml := ∑ i : Fin (2 ^ r), |vl i|
      let mr := ∑ i : Fin (2 ^ r), |vr i|
      have hrvalid : GammaValid fp.u r :=
        gammaValid_mono fp.u_nonneg (Nat.le_add_right r 1) hvalid
      have hstep := gamma_step_bound fp.u_nonneg r hvalid
      have hpl : |pl - al| ≤ gamma fp.u r * ml := ih vl hrvalid
      have hpr : |pr - ar| ≤ gamma fp.u r * mr := ih vr hrvalid
      have hml : 0 ≤ ml := by
        dsimp [ml]
        positivity
      have hmr : 0 ≤ mr := by
        dsimp [mr]
        positivity
      have hal : |al| ≤ ml := by
        dsimp [al, ml]
        exact Finset.abs_sum_le_sum_abs _ _
      have har : |ar| ≤ mr := by
        dsimp [ar, mr]
        exact Finset.abs_sum_le_sum_abs _ _
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add pl pr
      have hone : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by norm_num; exact hδ
      have hexact : |al + ar| ≤ ml + mr := by
        calc
          |al + ar| ≤ |al| + |ar| := abs_add_le _ _
          _ ≤ ml + mr := add_le_add hal har
      have habs := sum_halves r (fun i => |v i|)
      rw [pairwiseSum, hfl, sum_halves r v, habs]
      change |(pl + pr) * (1 + δ) - (al + ar)| ≤
        gamma fp.u (r + 1) * (ml + mr)
      calc
        |(pl + pr) * (1 + δ) - (al + ar)| =
            |((pl - al) + (pr - ar)) * (1 + δ) + (al + ar) * δ| := by
              congr 1
              ring
        _ ≤ |((pl - al) + (pr - ar)) * (1 + δ)| + |(al + ar) * δ| :=
              abs_add_le _ _
        _ = |(pl - al) + (pr - ar)| * |1 + δ| + |al + ar| * |δ| := by
              rw [abs_mul, abs_mul]
        _ ≤ (|pl - al| + |pr - ar|) * (1 + fp.u) +
              (ml + mr) * fp.u := by
            apply add_le_add
            · calc
                |(pl - al) + (pr - ar)| * |1 + δ| ≤
                    (|pl - al| + |pr - ar|) * |1 + δ| := by
                      exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg _)
                _ ≤ (|pl - al| + |pr - ar|) * (1 + fp.u) := by
                      exact mul_le_mul_of_nonneg_left hone (by positivity)
            · calc
                |al + ar| * |δ| ≤ (ml + mr) * |δ| := by
                  exact mul_le_mul_of_nonneg_right hexact (abs_nonneg _)
                _ ≤ (ml + mr) * fp.u := by
                  exact mul_le_mul_of_nonneg_left hδ (add_nonneg hml hmr)
        _ ≤ (gamma fp.u r * ml + gamma fp.u r * mr) * (1 + fp.u) +
              (ml + mr) * fp.u := by
            exact add_le_add
              (mul_le_mul_of_nonneg_right (add_le_add hpl hpr)
                (by linarith [fp.u_nonneg]))
              (le_refl _)
        _ = ((1 + fp.u) * gamma fp.u r + fp.u) * (ml + mr) := by ring
        _ ≤ gamma fp.u (r + 1) * (ml + mr) := by
            exact mul_le_mul_of_nonneg_right hstep.2 (add_nonneg hml hmr)

private theorem recursive_gamma_bound (fp : StandardAddModel) :
    ∀ (n : ℕ) (v : Fin n → ℝ), GammaValid fp.u (n - 1) →
      |recursiveSum fp.fl_add n v - ∑ i : Fin n, v i| ≤
        gamma fp.u (n - 1) * ∑ i : Fin n, |v i| := by
  intro n
  induction n with
  | zero =>
      intro v hvalid
      simp [recursiveSum, gamma]
  | succ n ih =>
      intro v hvalid
      by_cases hn : n = 0
      · subst n
        simp [recursiveSum, gamma]
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hnvalid : GammaValid fp.u n := by simpa using hvalid
        have hprevvalid : GammaValid fp.u (n - 1) :=
          gammaValid_mono fp.u_nonneg (Nat.sub_le n 1) hnvalid
        have hstep :
            0 ≤ gamma fp.u (n - 1) ∧
              (1 + fp.u) * gamma fp.u (n - 1) + fp.u ≤ gamma fp.u n := by
          simpa [Nat.sub_add_cancel hnpos] using
            (gamma_step_bound fp.u_nonneg (n - 1)
              (show GammaValid fp.u ((n - 1) + 1) by
                simpa [Nat.sub_add_cancel hnpos] using hnvalid))
        let w : Fin n → ℝ := fun i => v i.castSucc
        let c := recursiveSum fp.fl_add n w
        let a := ∑ i : Fin n, w i
        let m := ∑ i : Fin n, |w i|
        let x := v (Fin.last n)
        have hm : 0 ≤ m := by
          dsimp [m]
          positivity
        have hca : |c - a| ≤ gamma fp.u (n - 1) * m := ih w hprevvalid
        have ha : |a| ≤ m := by
          dsimp [a, m]
          exact Finset.abs_sum_le_sum_abs _ _
        have hexact : |a + x| ≤ m + |x| := by
          calc
            |a + x| ≤ |a| + |x| := abs_add_le _ _
            _ ≤ m + |x| := add_le_add ha (le_refl _)
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add c x
        have hone : |1 + δ| ≤ 1 + fp.u := by
          calc
            |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
            _ ≤ 1 + fp.u := by norm_num; exact hδ
        have hsum : (∑ i : Fin (n + 1), v i) = a + x := by
          rw [Fin.sum_univ_castSucc]
        have habs : (∑ i : Fin (n + 1), |v i|) = m + |x| := by
          rw [Fin.sum_univ_castSucc]
        rw [recursiveSum]
        simp only [hn, ↓reduceDIte]
        rw [hfl, hsum, habs]
        simp only [Nat.add_sub_cancel]
        change |(c + x) * (1 + δ) - (a + x)| ≤
          gamma fp.u n * (m + |x|)
        calc
          |(c + x) * (1 + δ) - (a + x)| =
              |(c - a) * (1 + δ) + (a + x) * δ| := by
                congr 1
                ring
          _ ≤ |(c - a) * (1 + δ)| + |(a + x) * δ| := abs_add_le _ _
          _ = |c - a| * |1 + δ| + |a + x| * |δ| := by
                rw [abs_mul, abs_mul]
          _ ≤ |c - a| * (1 + fp.u) + (m + |x|) * fp.u := by
              apply add_le_add
              · exact mul_le_mul_of_nonneg_left hone (abs_nonneg _)
              · calc
                  |a + x| * |δ| ≤ (m + |x|) * |δ| := by
                    exact mul_le_mul_of_nonneg_right hexact (abs_nonneg _)
                  _ ≤ (m + |x|) * fp.u := by
                    exact mul_le_mul_of_nonneg_left hδ
                      (add_nonneg hm (abs_nonneg _))
          _ ≤ (gamma fp.u (n - 1) * m) * (1 + fp.u) +
                (m + |x|) * fp.u := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right hca (by linarith [fp.u_nonneg]))
                (le_refl _)
          _ ≤ (gamma fp.u (n - 1) * (m + |x|)) * (1 + fp.u) +
                (m + |x|) * fp.u := by
              apply add_le_add
              · apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_left
                    (le_add_of_nonneg_right (abs_nonneg x)) hstep.1
                · linarith [fp.u_nonneg]
              · exact le_refl _
          _ = ((1 + fp.u) * gamma fp.u (n - 1) + fp.u) * (m + |x|) := by ring
          _ ≤ gamma fp.u n * (m + |x|) := by
              exact mul_le_mul_of_nonneg_right hstep.2
                (add_nonneg hm (abs_nonneg _))

private theorem depth_le_number_of_roundings (r : ℕ) : r ≤ 2 ^ r - 1 := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hp : 1 ≤ 2 ^ r := Nat.one_le_two_pow
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
  refine ⟨recursive_running_bound fp (2 ^ r) v,
    recursive_gamma_bound fp (2 ^ r) v hvalid, ?_⟩
  exact pairwise_gamma_bound fp r v
    (gammaValid_mono fp.u_nonneg (depth_le_number_of_roundings r) hvalid)

end HighamBench
