import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators


lemma fin_prefix_abs_le_aux {q : ℕ} (v : Fin q → ℝ)
    (k : ℕ) (hk : k ≤ q) :
    (∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) ≤
      ∑ i : Fin q, |v i| := by
  let f : ℕ → ℝ := fun i => if hi : i < q then |v ⟨i, hi⟩| else 0
  calc
    (∑ i : Fin k, |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) =
        ∑ i : Fin k, f i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [f]
          rw [dif_pos (Nat.lt_of_lt_of_le i.isLt hk)]
    _ = ∑ i ∈ Finset.range k, f i := Fin.sum_univ_eq_sum_range f k
    _ ≤ ∑ i ∈ Finset.range q, f i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hk)
          intro i hi hnot
          dsimp only [f]
          split <;> positivity
    _ = ∑ i : Fin q, f i := (Fin.sum_univ_eq_sum_range f q).symm
    _ = ∑ i : Fin q, |v i| := by
          apply Finset.sum_congr rfl
          intro i hi
          simp only [f]
          rw [dif_pos i.isLt]

lemma twoSumPrefix_succ_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (k : ℕ) (hk : k + 1 ≤ q) :
    twoSumPrefix fp v (k + 1) hk =
      (fp.twoSum
        (twoSumPrefix fp v k (Nat.le_trans (Nat.le_succ k) hk))
        (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 := by
  unfold twoSumPrefix
  rw [Fin.foldl_succ_last]
  rfl

lemma twoSumPrefix_exact_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (k : ℕ) (hk : k ≤ q) :
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩ := by
  induction k with
  | zero =>
      simp [twoSumPrefix]
  | succ k ih =>
      have hk0 : k ≤ q := Nat.le_trans (Nat.le_succ k) hk
      rw [twoSumPrefix_succ_aux fp v k hk]
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [show twoSumCorrection fp v ⟨k, Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk⟩ =
          (fp.twoSum (twoSumPrefix fp v k hk0)
            (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).2 by
        rfl]
      calc
        (fp.twoSum (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 +
              ((∑ i : Fin k, twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩) +
                (fp.twoSum (twoSumPrefix fp v k hk0)
                  (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).2) =
            ((fp.twoSum (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).1 +
             (fp.twoSum (twoSumPrefix fp v k hk0)
              (v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩)).2) +
              ∑ i : Fin k, twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩ := by ring
        _ = (twoSumPrefix fp v k hk0 +
              v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩) +
              ∑ i : Fin k, twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩ := by
              rw [fp.twoSum_exact]
        _ = (twoSumPrefix fp v k hk0 +
              ∑ i : Fin k, twoSumCorrection fp v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk0⟩) +
              v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩ := by ring
        _ = (∑ i : Fin (k + 1),
              v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk0)⟩) +
              v ⟨k + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hk)⟩ := by
              rw [ih hk0]

lemma vecSum_exact_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) :
    ∑ i, vecSum fp v i = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  rw [add_comm]
  exact twoSumPrefix_exact_aux fp v q (Nat.le_refl q)

lemma twoSumPrefix_abs_le_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) (i : Fin q) :
    |twoSumPrefix fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt)| ≤
      (∑ j : Fin (q + 1), |v j|) +
        ∑ j : Fin q, |twoSumCorrection fp v j| := by
  let c : Fin q → ℝ := fun j => twoSumCorrection fp v j
  have hex := twoSumPrefix_exact_aux fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt)
  have heq :
      twoSumPrefix fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt) =
        (∑ j : Fin (i.val + 2),
          v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt))⟩) -
        ∑ j : Fin (i.val + 1),
          twoSumCorrection fp v
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩ := by
    linarith
  rw [heq]
  calc
    |(∑ j : Fin (i.val + 2),
          v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt))⟩) -
        ∑ j : Fin (i.val + 1),
          twoSumCorrection fp v
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩| ≤
      |∑ j : Fin (i.val + 2),
          v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt))⟩| +
        |∑ j : Fin (i.val + 1),
          twoSumCorrection fp v
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩| := abs_sub _ _
    _ ≤ (∑ j : Fin (i.val + 2),
          |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt))⟩|) +
        ∑ j : Fin (i.val + 1),
          |twoSumCorrection fp v
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩| := by
      apply add_le_add
      · simpa using (Finset.abs_sum_le_sum_abs
          (fun j : Fin (i.val + 2) =>
            v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
              (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt))⟩) Finset.univ)
      · simpa using (Finset.abs_sum_le_sum_abs
          (fun j : Fin (i.val + 1) =>
            twoSumCorrection fp v
              ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt i.isLt)⟩) Finset.univ)
    _ ≤ (∑ j : Fin (q + 1), |v j|) +
        ∑ j : Fin q, |twoSumCorrection fp v j| := by
      apply add_le_add
      · exact fin_prefix_abs_le_aux (fun j : Fin (q + 1) => v j)
          (i.val + 2) (Nat.succ_le_succ (Nat.succ_le_of_lt i.isLt))
      · exact fin_prefix_abs_le_aux c (i.val + 1) (Nat.succ_le_of_lt i.isLt)

lemma correction_sum_le_mul_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) :
    (∑ i : Fin q, |twoSumCorrection fp v i|) ≤
      fp.u * ((q : ℝ) *
        ((∑ j : Fin (q + 1), |v j|) +
          ∑ j : Fin q, |twoSumCorrection fp v j|)) := by
  calc
    (∑ i : Fin q, |twoSumCorrection fp v i|) ≤
        ∑ i : Fin q,
          fp.u * |twoSumPrefix fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt)| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [twoSumPrefix_succ_aux fp v i.val (Nat.succ_le_of_lt i.isLt)]
      exact fp.twoSum_low_le _ _
    _ = fp.u * ∑ i : Fin q,
          |twoSumPrefix fp v (i.val + 1) (Nat.succ_le_of_lt i.isLt)| := by
      rw [Finset.mul_sum]
    _ ≤ fp.u * ∑ _i : Fin q,
          ((∑ j : Fin (q + 1), |v j|) +
            ∑ j : Fin q, |twoSumCorrection fp v j|) := by
      apply mul_le_mul_of_nonneg_left _ fp.u_nonneg
      apply Finset.sum_le_sum
      intro i hi
      exact twoSumPrefix_abs_le_aux fp v i
    _ = fp.u * ((q : ℝ) *
        ((∑ j : Fin (q + 1), |v j|) +
          ∑ j : Fin q, |twoSumCorrection fp v j|)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma correction_sum_le_gamma_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ)
    (hvalid : (q : ℝ) * fp.u < 1) :
    (∑ i : Fin q, |twoSumCorrection fp v i|) ≤
      gamma fp.u q * ∑ j : Fin (q + 1), |v j| := by
  let A : ℝ := ∑ j : Fin (q + 1), |v j|
  let C : ℝ := ∑ i : Fin q, |twoSumCorrection fp v i|
  let a : ℝ := (q : ℝ) * fp.u
  let b : ℝ := (q : ℝ) * fp.u
  let g : ℝ := gamma fp.u q
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    positivity
  have ha : 0 ≤ a := by
    dsimp only [a]
    exact mul_nonneg (Nat.cast_nonneg q) fp.u_nonneg
  have hb : b = a := by
    dsimp only [a, b]
  have hb1 : b < 1 := by exact hvalid
  have hbden : 0 < 1 - b := by linarith
  have hgdef : g = b / (1 - b) := by
    dsimp only [g, b, gamma]
  have hg0 : 0 ≤ g := by
    rw [hgdef]
    exact div_nonneg (by rw [hb]; positivity) (le_of_lt hbden)
  have hgrel : g * (1 - b) = b := by
    rw [hgdef]
    field_simp
  have hraw : C ≤ a * (A + C) := by
    convert correction_sum_le_mul_aux fp v using 1 <;> dsimp only [A, C, a] <;> ring
  change C ≤ g * A
  nlinarith [mul_nonneg (show 0 ≤ 1 - a by nlinarith) hA,
    mul_nonneg hg0 hA]

lemma two_mul_gamma_le_gamma_two_aux (u : ℝ) (hu : 0 ≤ u) (q : ℕ)
    (hvalid : (2 : ℝ) * (q : ℝ) * u < 1) :
    2 * gamma u q ≤ gamma u (2 * q) := by
  let a : ℝ := (q : ℝ) * u
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg q) hu
  have h2a : 2 * a < 1 := by
    dsimp only [a]
    nlinarith [hvalid]
  have hd1 : 0 < 1 - a := by nlinarith
  have hd2 : 0 < 1 - 2 * a := by nlinarith
  have hrewrite1 : gamma u q = a / (1 - a) := by
    dsimp only [gamma, a]
  have hrewrite2 : gamma u (2 * q) = (2 * a) / (1 - 2 * a) := by
    dsimp only [gamma, a]
    norm_num
    ring
  rw [hrewrite1, hrewrite2]
  rw [show 2 * (a / (1 - a)) = (2 * a) / (1 - a) by ring]
  apply (div_le_div_iff₀ hd1 hd2).2
  nlinarith [mul_nonneg (show 0 ≤ 2 * a by positivity) (show 0 ≤ a by exact ha)]

lemma vecSum_abs_sum_le_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ)
    (hvalid : (2 : ℝ) * (q : ℝ) * fp.u < 1) :
    (∑ i : Fin (q + 1), |vecSum fp v i|) ≤
      |∑ i : Fin (q + 1), v i| +
        (2 * gamma fp.u q) * ∑ i : Fin (q + 1), |v i| := by
  let C : ℝ := ∑ i : Fin q, |twoSumCorrection fp v i|
  let Cs : ℝ := ∑ i : Fin q, twoSumCorrection fp v i
  let A : ℝ := ∑ i : Fin (q + 1), |v i|
  let S : ℝ := ∑ i : Fin (q + 1), v i
  let H : ℝ := twoSumPrefix fp v q (Nat.le_refl q)
  have hqvalid : (q : ℝ) * fp.u < 1 := by
    have hu := fp.u_nonneg
    nlinarith
  have hC : C ≤ gamma fp.u q * A := by
    simpa only [C, A] using correction_sum_le_gamma_aux fp v hqvalid
  have hCA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hCsabs : |Cs| ≤ C := by
    dsimp only [Cs, C]
    simpa using (Finset.abs_sum_le_sum_abs
      (fun i : Fin q => twoSumCorrection fp v i) Finset.univ)
  have hex : H + Cs = S := by
    simpa only [H, Cs, S] using twoSumPrefix_exact_aux fp v q (Nat.le_refl q)
  have hH : |H| ≤ |S| + C := by
    have hheq : H = S - Cs := by linarith
    rw [hheq]
    nlinarith [abs_sub S Cs]
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  change C + |H| ≤ |S| + (2 * gamma fp.u q) * A
  calc
    C + |H| ≤ |S| + 2 * C := by linarith
    _ ≤ |S| + 2 * (gamma fp.u q * A) := by linarith
    _ = |S| + (2 * gamma fp.u q) * A := by ring

lemma u_le_gamma_aux (u : ℝ) (hu : 0 ≤ u) (r : ℕ) (hr : 1 ≤ r)
    (hvalid : (r : ℝ) * u < 1) :
    u ≤ gamma u r := by
  have hd : 0 < 1 - (r : ℝ) * u := by linarith
  rw [gamma, le_div_iff₀ hd]
  have hrc : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  nlinarith [mul_nonneg (sub_nonneg.mpr hrc) hu]

lemma gamma_step_aux (u : ℝ) (hu : 0 ≤ u) (r : ℕ) (hr : 1 ≤ r)
    (hvalid : (r : ℝ) * u < 1) :
    (1 + u) * gamma u (r - 1) + u ≤ gamma u r := by
  have hrc : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcast : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub hr]
    norm_num
  have hd : 0 < 1 - (r : ℝ) * u := by linarith
  have hdp : 0 < 1 - ((r - 1 : ℕ) : ℝ) * u := by
    rw [hcast]
    nlinarith
  rw [gamma, gamma]
  rw [le_div_iff₀ hd]
  rw [show (1 + u) * (((r - 1 : ℕ) : ℝ) * u /
      (1 - ((r - 1 : ℕ) : ℝ) * u)) + u =
      ((r : ℝ) * u) / (1 - ((r - 1 : ℕ) : ℝ) * u) by
        let d : ℝ := 1 - ((r - 1 : ℕ) : ℝ) * u
        calc
          (1 + u) * (((r - 1 : ℕ) : ℝ) * u / d) + u =
              ((1 + u) * (((r - 1 : ℕ) : ℝ) * u) + u * d) / d := by
                field_simp [d, hdp.ne']
          _ = ((r : ℝ) * u) / d := by
                congr 1
                dsimp only [d]
                rw [hcast]
                ring]
  rw [div_mul_eq_mul_div, div_le_iff₀ hdp]
  nlinarith [mul_nonneg (show 0 ≤ (r : ℝ) * u by positivity)
    (show 0 ≤ u by exact hu)]

lemma recursiveSum_error_aux (fp : StandardAddModel) :
    ∀ (r : ℕ) (v : Fin r → ℝ),
      (((r - 1 : ℕ) : ℝ) * fp.u < 1) →
      |recursiveSum fp.fl_add r v - ∑ i : Fin r, v i| ≤
        gamma fp.u (r - 1) * ∑ i : Fin r, |v i| := by
  intro r
  induction r with
  | zero =>
      intro v hvalid
      simp [recursiveSum, gamma]
  | succ r ih =>
      intro v hvalid
      by_cases hr0 : r = 0
      · subst r
        simp [recursiveSum, gamma]
      · have hr : 1 ≤ r := Nat.one_le_iff_ne_zero.mpr hr0
        let vp : Fin r → ℝ := fun i => v i.castSucc
        let a : ℝ := recursiveSum fp.fl_add r vp
        let s : ℝ := ∑ i : Fin r, vp i
        let b : ℝ := v (Fin.last r)
        let A : ℝ := ∑ i : Fin r, |vp i|
        have hrv : (r : ℝ) * fp.u < 1 := by
          simpa using hvalid
        have hprev : (((r - 1 : ℕ) : ℝ) * fp.u < 1) := by
          have hcastle : ((r - 1 : ℕ) : ℝ) ≤ (r : ℝ) := by
            exact_mod_cast (Nat.sub_le r 1)
          nlinarith [mul_le_mul_of_nonneg_right hcastle fp.u_nonneg]
        have hrec : |a - s| ≤ gamma fp.u (r - 1) * A := by
          simpa only [a, s, A, vp] using ih vp hprev
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add a b
        have hδone : |1 + δ| ≤ 1 + fp.u := by
          calc
            |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
            _ ≤ 1 + fp.u := by norm_num; linarith
        have hsabs : |s + b| ≤ A + |b| := by
          calc
            |s + b| ≤ |s| + |b| := abs_add_le s b
            _ ≤ A + |b| := by
              gcongr
              dsimp only [s, A]
              simpa using (Finset.abs_sum_le_sum_abs vp Finset.univ)
        have hgpvalid : ((r - 1 : ℕ) : ℝ) * fp.u < 1 := hprev
        have hgp0 : 0 ≤ gamma fp.u (r - 1) := by
          rw [gamma]
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
            (by linarith)
        have hg0 : 0 ≤ gamma fp.u r := by
          rw [gamma]
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg)
            (by linarith)
        have hstep :
            (1 + fp.u) * gamma fp.u (r - 1) + fp.u ≤ gamma fp.u r :=
          gamma_step_aux fp.u fp.u_nonneg r hr hrv
        have hug : fp.u ≤ gamma fp.u r :=
          u_le_gamma_aux fp.u fp.u_nonneg r hr hrv
        have hA : 0 ≤ A := by dsimp only [A]; positivity
        have hbabs : 0 ≤ |b| := abs_nonneg b
        have honeu : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
        have hmain :
            |a - s| * (1 + fp.u) + fp.u * (A + |b|) ≤
              gamma fp.u r * (A + |b|) := by
          calc
            |a - s| * (1 + fp.u) + fp.u * (A + |b|) ≤
                (gamma fp.u (r - 1) * A) * (1 + fp.u) +
                  fp.u * (A + |b|) := by
              gcongr
            _ = ((1 + fp.u) * gamma fp.u (r - 1) + fp.u) * A +
                  fp.u * |b| := by ring
            _ ≤ gamma fp.u r * A + gamma fp.u r * |b| := by
              exact add_le_add
                (mul_le_mul_of_nonneg_right hstep hA)
                (mul_le_mul_of_nonneg_right hug hbabs)
            _ = gamma fp.u r * (A + |b|) := by ring
        rw [show recursiveSum fp.fl_add (r + 1) v = fp.fl_add a b by
          simp only [recursiveSum, hr0, ↓reduceDIte, a, b, vp]]
        rw [hfl, Fin.sum_univ_castSucc]
        rw [Fin.sum_univ_castSucc]
        simp only [Nat.add_sub_cancel]
        change |(a + b) * (1 + δ) - (s + b)| ≤
          gamma fp.u r * (A + |b|)
        calc
          |(a + b) * (1 + δ) - (s + b)| =
              |(a - s) * (1 + δ) + δ * (s + b)| := by congr 1; ring
          _ ≤ |a - s| * |1 + δ| + |δ| * |s + b| := by
            simpa [abs_mul] using
              (abs_add_le ((a - s) * (1 + δ)) (δ * (s + b)))
          _ ≤ |a - s| * (1 + fp.u) + fp.u * (A + |b|) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hδone (abs_nonneg (a - s)))
              (mul_le_mul hδ hsabs (abs_nonneg (s + b)) fp.u_nonneg)
          _ ≤ gamma fp.u r * (A + |b|) := hmain

lemma recursive_vecSum_error_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (hq : 1 ≤ q) (v : Fin (q + 1) → ℝ)
    (hvalid : (q : ℝ) * fp.u < 1) :
    |recursiveSum fp.fl_add (q + 1) (vecSum fp v) -
        ∑ i : Fin (q + 1), v i| ≤
      fp.u * |∑ i : Fin (q + 1), v i| +
        ((1 + fp.u) * gamma fp.u (q - 1) * gamma fp.u q) *
          ∑ i : Fin (q + 1), |v i| := by
  let c : Fin q → ℝ := fun i => twoSumCorrection fp v i
  let C : ℝ := ∑ i : Fin q, |c i|
  let Cs : ℝ := ∑ i : Fin q, c i
  let H : ℝ := twoSumPrefix fp v q (Nat.le_refl q)
  let R : ℝ := recursiveSum fp.fl_add q c
  let S : ℝ := ∑ i : Fin (q + 1), v i
  let A : ℝ := ∑ i : Fin (q + 1), |v i|
  have hprev : (((q - 1 : ℕ) : ℝ) * fp.u < 1) := by
    have hcastle : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (Nat.sub_le q 1)
    nlinarith [mul_le_mul_of_nonneg_right hcastle fp.u_nonneg]
  have hR : |R - Cs| ≤ gamma fp.u (q - 1) * C := by
    simpa only [R, Cs, C, c] using
      recursiveSum_error_aux fp.toStandardAddModel q c hprev
  have hC : C ≤ gamma fp.u q * A := by
    simpa only [C, A, c] using correction_sum_le_gamma_aux fp v hvalid
  have hgp0 : 0 ≤ gamma fp.u (q - 1) := by
    rw [gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hp0 : 0 ≤ gamma fp.u q := by
    rw [gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hRC : |R - Cs| ≤ gamma fp.u (q - 1) * gamma fp.u q * A := by
    simpa only [mul_assoc] using
      le_trans hR (mul_le_mul_of_nonneg_left hC hgp0)
  have hex : H + Cs = S := by
    simpa only [H, Cs, S, c] using twoSumPrefix_exact_aux fp v q (Nat.le_refl q)
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add R H
  have hδone : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le 1 δ
      _ ≤ 1 + fp.u := by norm_num; linarith
  have honeu : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
  rw [show recursiveSum fp.fl_add (q + 1) (vecSum fp v) = fp.fl_add R H by
    simp only [recursiveSum, Nat.one_le_iff_ne_zero.mp hq, ↓reduceDIte,
      R, H, c, vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]]
  rw [hfl]
  change |(R + H) * (1 + δ) - S| ≤
    fp.u * |S| + ((1 + fp.u) * gamma fp.u (q - 1) * gamma fp.u q) * A
  have hid : (R + H) * (1 + δ) - S =
      (R - Cs) * (1 + δ) + δ * S := by
    rw [← hex]
    ring
  rw [hid]
  calc
    |(R - Cs) * (1 + δ) + δ * S| ≤
        |R - Cs| * |1 + δ| + |δ| * |S| := by
      simpa [abs_mul] using
        (abs_add_le ((R - Cs) * (1 + δ)) (δ * S))
    _ ≤ |R - Cs| * (1 + fp.u) + fp.u * |S| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hδone (abs_nonneg (R - Cs)))
        (mul_le_mul_of_nonneg_right hδ (abs_nonneg S))
    _ ≤ (gamma fp.u (q - 1) * gamma fp.u q * A) * (1 + fp.u) +
        fp.u * |S| := by
      gcongr
    _ = fp.u * |S| +
        ((1 + fp.u) * gamma fp.u (q - 1) * gamma fp.u q) * A := by ring

lemma iteratedVecSum_exact_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (t : ℕ) (v : Fin (q + 1) → ℝ) :
    ∑ i : Fin (q + 1), iteratedVecSum fp t v i =
      ∑ i : Fin (q + 1), v i := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show iteratedVecSum fp (t + 1) v =
        vecSum fp (iteratedVecSum fp t v) by rfl]
      rw [vecSum_exact_aux, ih]

lemma sumK_constants_aux (fp : ErrorFreeAddModel) (q : ℕ) (hq : 1 ≤ q)
    (hhalf : (2 : ℝ) * (q : ℝ) * fp.u ≤ (1 : ℝ) / 2) :
    let p := gamma fp.u q
    let g := gamma fp.u (2 * q)
    let d := (1 + fp.u) * gamma fp.u (q - 1) * p
    0 ≤ p ∧ 0 ≤ g ∧ 2 * p ≤ g ∧ 0 ≤ 1 - 2 * p ∧
      d ≤ (1 - 2 * p) * g ^ 2 := by
  dsimp only
  have hvalid2 : (2 : ℝ) * (q : ℝ) * fp.u < 1 := by linarith
  have hvalidq : (q : ℝ) * fp.u < 1 := by
    nlinarith [fp.u_nonneg]
  have hp0 : 0 ≤ gamma fp.u q := by
    rw [gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have hg0 : 0 ≤ gamma fp.u (2 * q) := by
    rw [gamma]
    have hcast : (((2 * q : ℕ) : ℝ) * fp.u) =
        (2 : ℝ) * (q : ℝ) * fp.u := by norm_num
    rw [hcast]
    exact div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg q)) fp.u_nonneg)
      (by linarith)
  have hdouble : 2 * gamma fp.u q ≤ gamma fp.u (2 * q) :=
    two_mul_gamma_le_gamma_two_aux fp.u fp.u_nonneg q hvalid2
  let a : ℝ := (q : ℝ) * fp.u
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    exact mul_nonneg (Nat.cast_nonneg q) fp.u_nonneg
  have haquarter : a ≤ (1 : ℝ) / 4 := by
    dsimp only [a]
    nlinarith
  have hpdef : gamma fp.u q = a / (1 - a) := by
    dsimp only [gamma, a]
  have hden : 0 < 1 - a := by linarith
  have hp13 : gamma fp.u q ≤ (1 : ℝ) / 3 := by
    rw [hpdef, div_le_iff₀ hden]
    nlinarith
  have hfactor : (1 : ℝ) / 3 ≤ 1 - 2 * gamma fp.u q := by
    linarith
  have hfactor0 : 0 ≤ 1 - 2 * gamma fp.u q := by linarith
  have hstep := gamma_step_aux fp.u fp.u_nonneg q hq hvalidq
  have hdsmall :
      (1 + fp.u) * gamma fp.u (q - 1) * gamma fp.u q ≤
        (gamma fp.u q) ^ 2 := by
    have hc : (1 + fp.u) * gamma fp.u (q - 1) ≤ gamma fp.u q := by
      nlinarith [fp.u_nonneg]
    have := mul_le_mul_of_nonneg_right hc hp0
    nlinarith
  have hsq : (2 * gamma fp.u q) ^ 2 ≤ (gamma fp.u (2 * q)) ^ 2 :=
    (sq_le_sq₀ (by positivity) hg0).2 hdouble
  have hthird :
      ((1 : ℝ) / 3) * (gamma fp.u (2 * q)) ^ 2 ≤
        (1 - 2 * gamma fp.u q) * (gamma fp.u (2 * q)) ^ 2 :=
    mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)
  have hpsq : (gamma fp.u q) ^ 2 ≤
      ((1 : ℝ) / 3) * (gamma fp.u (2 * q)) ^ 2 := by
    nlinarith [sq_nonneg (gamma fp.u q)]
  exact ⟨hp0, hg0, hdouble, hfactor0,
    le_trans hdsmall (le_trans hpsq hthird)⟩

lemma iteratedVecSum_weighted_aux (fp : ErrorFreeAddModel) {q : ℕ}
    (hq : 1 ≤ q)
    (hhalf : (2 : ℝ) * (q : ℝ) * fp.u ≤ (1 : ℝ) / 2)
    (t : ℕ) (v : Fin (q + 1) → ℝ) :
    ((1 + fp.u) * gamma fp.u (q - 1) * gamma fp.u q) *
        (∑ i : Fin (q + 1), |iteratedVecSum fp t v i|) ≤
      (gamma fp.u (2 * q)) ^ 2 * |∑ i : Fin (q + 1), v i| +
        (gamma fp.u (2 * q)) ^ (t + 2) *
          ∑ i : Fin (q + 1), |v i| := by
  let p : ℝ := gamma fp.u q
  let g : ℝ := gamma fp.u (2 * q)
  let c : ℝ := 2 * p
  let d : ℝ := (1 + fp.u) * gamma fp.u (q - 1) * p
  let S : ℝ := ∑ i : Fin (q + 1), v i
  let A : ℝ := ∑ i : Fin (q + 1), |v i|
  obtain ⟨hp0, hg0, hcg, hfactor0, hd⟩ :=
    sumK_constants_aux fp q hq hhalf
  change d * (∑ i : Fin (q + 1), |iteratedVecSum fp t v i|) ≤
    g ^ 2 * |S| + g ^ (t + 2) * A
  have hc0 : 0 ≤ c := by dsimp only [c, p]; positivity
  have hd0 : 0 ≤ d := by
    dsimp only [d, p]
    have hvalidPrev : (((q - 1 : ℕ) : ℝ) * fp.u < 1) := by
      have hvalidq : (q : ℝ) * fp.u < 1 := by
        nlinarith [fp.u_nonneg]
      have hcastle : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.sub_le q 1)
      nlinarith [mul_le_mul_of_nonneg_right hcastle fp.u_nonneg]
    have hgp0 : 0 ≤ gamma fp.u (q - 1) := by
      rw [gamma]
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
    exact mul_nonneg (mul_nonneg (by linarith [fp.u_nonneg]) hgp0) hp0
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hSabs : 0 ≤ |S| := abs_nonneg S
  have hdg : d ≤ g ^ 2 := by
    have hf : (1 - c) * g ^ 2 ≤ g ^ 2 := by
      have hc1 : 1 - c ≤ 1 := by linarith
      nlinarith [sq_nonneg g]
    exact le_trans hd hf
  have hvalid2 : (2 : ℝ) * (q : ℝ) * fp.u < 1 := by linarith
  induction t with
  | zero =>
      simp only [iteratedVecSum, Nat.zero_add, pow_two]
      change d * A ≤ g * g * |S| + g * g * A
      have hm := mul_le_mul_of_nonneg_right hdg hA
      nlinarith [mul_nonneg (mul_nonneg hg0 hg0) hSabs]
  | succ t ih =>
      rw [show iteratedVecSum fp (t + 1) v =
        vecSum fp (iteratedVecSum fp t v) by rfl]
      have hone :
          (∑ i : Fin (q + 1),
              |vecSum fp (iteratedVecSum fp t v) i|) ≤
            |S| + c *
              ∑ i : Fin (q + 1), |iteratedVecSum fp t v i| := by
        simpa only [S, c, p, iteratedVecSum_exact_aux fp t v] using
          vecSum_abs_sum_le_aux fp (iteratedVecSum fp t v) hvalid2
      have hmulone := mul_le_mul_of_nonneg_left hone hd0
      have hcoef : d + c * g ^ 2 ≤ g ^ 2 := by
        nlinarith
      have hcoefmul := mul_le_mul_of_nonneg_right hcoef hSabs
      have hpowA : 0 ≤ g ^ (t + 2) * A :=
        mul_nonneg (pow_nonneg hg0 _) hA
      have hres := mul_le_mul_of_nonneg_right hcg hpowA
      calc
        d * (∑ i : Fin (q + 1),
            |vecSum fp (iteratedVecSum fp t v) i|) ≤
            d * (|S| + c *
              ∑ i : Fin (q + 1), |iteratedVecSum fp t v i|) := hmulone
        _ = d * |S| + c *
              (d * ∑ i : Fin (q + 1), |iteratedVecSum fp t v i|) := by ring
        _ ≤ d * |S| + c * (g ^ 2 * |S| + g ^ (t + 2) * A) := by
          gcongr
        _ = (d + c * g ^ 2) * |S| + c * (g ^ (t + 2) * A) := by ring
        _ ≤ g ^ 2 * |S| + g * (g ^ (t + 2) * A) :=
          add_le_add hcoefmul hres
        _ = g ^ 2 * |S| + g ^ (t + 1 + 2) * A := by
          rw [show t + 1 + 2 = (t + 2) + 1 by omega, pow_succ]
          ring

lemma sumK_error_aux (fp : ErrorFreeAddModel) {q L : ℕ}
    (hq : 1 ≤ q) (hL : 2 ≤ L)
    (hhalf : (2 : ℝ) * (q : ℝ) * fp.u ≤ (1 : ℝ) / 2)
    (v : Fin (q + 1) → ℝ) :
    |sumK fp L v - ∑ i : Fin (q + 1), v i| ≤
      (fp.u + (gamma fp.u (2 * q)) ^ 2) *
          |∑ i : Fin (q + 1), v i| +
        (gamma fp.u (2 * q)) ^ L *
          ∑ i : Fin (q + 1), |v i| := by
  let t : ℕ := L - 2
  let z : Fin (q + 1) → ℝ := iteratedVecSum fp t v
  let d : ℝ := (1 + fp.u) * gamma fp.u (q - 1) * gamma fp.u q
  let g : ℝ := gamma fp.u (2 * q)
  let S : ℝ := ∑ i : Fin (q + 1), v i
  let A : ℝ := ∑ i : Fin (q + 1), |v i|
  have hsub : L - 1 = t + 1 := by dsimp only [t]; omega
  have hzsum : (∑ i : Fin (q + 1), z i) = S := by
    simpa only [z, S] using iteratedVecSum_exact_aux fp t v
  have hvalidq : (q : ℝ) * fp.u < 1 := by
    nlinarith [fp.u_nonneg]
  have hfinal := recursive_vecSum_error_aux fp hq z hvalidq
  have hweighted : d * (∑ i : Fin (q + 1), |z i|) ≤
      g ^ 2 * |S| + g ^ (t + 2) * A := by
    simpa only [d, g, z, S, A] using
      iteratedVecSum_weighted_aux fp hq hhalf t v
  have htexp : t + 2 = L := by dsimp only [t]; omega
  rw [sumK, hsub]
  rw [show iteratedVecSum fp (t + 1) v = vecSum fp z by rfl]
  change |recursiveSum fp.fl_add (q + 1) (vecSum fp z) - S| ≤
    (fp.u + g ^ 2) * |S| + g ^ L * A
  calc
    |recursiveSum fp.fl_add (q + 1) (vecSum fp z) - S| =
        |recursiveSum fp.fl_add (q + 1) (vecSum fp z) -
          ∑ i : Fin (q + 1), z i| := by rw [hzsum]
    _ ≤ fp.u * |∑ i : Fin (q + 1), z i| +
        d * ∑ i : Fin (q + 1), |z i| := by
      simpa only [d] using hfinal
    _ = fp.u * |S| + d * ∑ i : Fin (q + 1), |z i| := by rw [hzsum]
    _ ≤ fp.u * |S| + (g ^ 2 * |S| + g ^ (t + 2) * A) := by
      gcongr
    _ = (fp.u + g ^ 2) * |S| + g ^ L * A := by
      rw [htexp]
      ring

lemma dotKTransform_sum_aux (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    ∑ j : Fin ((2 * n + 1) + 1), dotKTransform fp x y j = exactDot x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let w : Fin (n + 1) → ℝ := vecSum fp.toErrorFreeAddModel hi
  let e : Fin ((2 * n + 1) + 1) ≃ Fin ((n + 1) + (n + 1)) :=
    finCongr (by omega)
  calc
    (∑ j : Fin ((2 * n + 1) + 1), dotKTransform fp x y j) =
        ∑ j : Fin ((2 * n + 1) + 1), Fin.addCases lo w (e j) := by rfl
    _ = ∑ j : Fin ((n + 1) + (n + 1)), Fin.addCases lo w j :=
      Equiv.sum_comp e (Fin.addCases lo w)
    _ = (∑ i : Fin (n + 1), lo i) + ∑ i : Fin (n + 1), w i := by
      rw [Fin.sum_univ_add]
      congr 1
      · apply Finset.sum_congr rfl
        intro i hi_mem
        exact Fin.addCases_left i
      · apply Finset.sum_congr rfl
        intro i hi_mem
        exact Fin.addCases_right i
    _ = (∑ i : Fin (n + 1), lo i) + ∑ i : Fin (n + 1), hi i := by
      rw [vecSum_exact_aux]
    _ = ∑ i : Fin (n + 1), (lo i + hi i) := by
      rw [Finset.sum_add_distrib]
    _ = exactDot x y := by
      apply Finset.sum_congr rfl
      intro i hi_mem
      dsimp only [lo, hi, exactDot]
      rw [add_comm, fp.twoProduct_exact]

lemma gamma_mono_index_aux (u : ℝ) (hu : 0 ≤ u) {a b : ℕ}
    (hab : a ≤ b) (hvalid : (b : ℝ) * u < 1) :
    gamma u a ≤ gamma u b := by
  have habc : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hda : 0 < 1 - (a : ℝ) * u := by
    nlinarith [mul_le_mul_of_nonneg_right habc hu]
  have hdb : 0 < 1 - (b : ℝ) * u := by linarith
  rw [gamma, gamma]
  apply (div_le_div_iff₀ hda hdb).2
  nlinarith [mul_le_mul_of_nonneg_right habc hu]

lemma dotKTransform_abs_sum_aux (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    (∑ j : Fin ((2 * n + 1) + 1), |dotKTransform fp x y j|) ≤
      |exactDot x y| + gamma fp.u (4 * (n + 1) - 2) * dotMagnitude x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let w : Fin (n + 1) → ℝ := vecSum fp.toErrorFreeAddModel hi
  let L : ℝ := ∑ i : Fin (n + 1), |lo i|
  let H : ℝ := ∑ i : Fin (n + 1), |hi i|
  let W : ℝ := ∑ i : Fin (n + 1), |w i|
  let M : ℝ := dotMagnitude x y
  let S : ℝ := exactDot x y
  let gm : ℝ := gamma fp.u (4 * (n + 1) - 2)
  let e : Fin ((2 * n + 1) + 1) ≃ Fin ((n + 1) + (n + 1)) :=
    finCongr (by omega)
  have hm_lt : (((4 * (n + 1) - 2 : ℕ) : ℝ)) <
      (8 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 4 * (n + 1) - 2 < 8 * (n + 1) by omega)
  have hvalidm : (((4 * (n + 1) - 2 : ℕ) : ℝ)) * fp.u < 1 := by
    by_cases hu0 : fp.u = 0
    · rw [hu0]
      norm_num
    · have hupos : 0 < fp.u := lt_of_le_of_ne fp.u_nonneg (Ne.symm hu0)
      have hmul := mul_lt_mul_of_pos_right hm_lt hupos
      nlinarith
  have hvalid2n : (2 : ℝ) * (n : ℝ) * fp.u < 1 := by
    have hidx : (2 * n : ℕ) ≤ 4 * (n + 1) - 2 := by omega
    have hidxc : (((2 * n : ℕ) : ℝ)) ≤ (((4 * (n + 1) - 2 : ℕ) : ℝ)) := by
      exact_mod_cast hidx
    have hmul := mul_le_mul_of_nonneg_right hidxc fp.u_nonneg
    norm_num at hmul
    nlinarith
  have hvalidN : (((n + 1 : ℕ) : ℝ) * fp.u < 1) := by
    have hidx : n + 1 ≤ 4 * (n + 1) - 2 := by omega
    have hidxc : (((n + 1 : ℕ) : ℝ)) ≤ (((4 * (n + 1) - 2 : ℕ) : ℝ)) := by
      exact_mod_cast hidx
    nlinarith [mul_le_mul_of_nonneg_right hidxc fp.u_nonneg]
  have hvalid2N : (((2 * (n + 1) : ℕ) : ℝ) * fp.u < 1) := by
    have hidx : 2 * (n + 1) ≤ 4 * (n + 1) - 2 := by omega
    have hidxc : (((2 * (n + 1) : ℕ) : ℝ)) ≤
        (((4 * (n + 1) - 2 : ℕ) : ℝ)) := by exact_mod_cast hidx
    nlinarith [mul_le_mul_of_nonneg_right hidxc fp.u_nonneg]
  have hL : L ≤ fp.u * M := by
    dsimp only [L, M, lo, dotMagnitude]
    calc
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2|) ≤
          ∑ i : Fin (n + 1), fp.u * |x i * y i| := by
        apply Finset.sum_le_sum
        intro i hi_mem
        exact fp.twoProduct_low_le_exact _ _
      _ = fp.u * ∑ i : Fin (n + 1), |x i| * |y i| := by
        rw [Finset.mul_sum]
        congr 1
        funext i
        rw [abs_mul]
  have hM0 : 0 ≤ M := by dsimp only [M, dotMagnitude]; positivity
  have hL0 : 0 ≤ L := by dsimp only [L]; positivity
  have hH : H ≤ M + L := by
    dsimp only [H, M, L, hi, lo, dotMagnitude]
    calc
      (∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).1|) ≤
          ∑ i : Fin (n + 1),
            (|x i * y i| + |(fp.twoProduct (x i) (y i)).2|) := by
        apply Finset.sum_le_sum
        intro i hi_mem
        have he := fp.twoProduct_exact (x i) (y i)
        have hv : (fp.twoProduct (x i) (y i)).1 =
            x i * y i - (fp.twoProduct (x i) (y i)).2 := by linarith
        rw [hv]
        exact abs_sub _ _
      _ = (∑ i : Fin (n + 1), |x i| * |y i|) +
          ∑ i : Fin (n + 1), |(fp.twoProduct (x i) (y i)).2| := by
        rw [Finset.sum_add_distrib]
        congr 1
        apply Finset.sum_congr rfl
        intro i hi_mem
        rw [abs_mul]
  have hHM : H ≤ (1 + fp.u) * M := by
    calc
      H ≤ M + L := hH
      _ ≤ M + fp.u * M := add_le_add_right hL M
      _ = (1 + fp.u) * M := by ring
  have hsumlo : |∑ i : Fin (n + 1), lo i| ≤ L := by
    dsimp only [L]
    simpa using (Finset.abs_sum_le_sum_abs lo Finset.univ)
  have hsums : (∑ i : Fin (n + 1), lo i) +
      ∑ i : Fin (n + 1), hi i = S := by
    dsimp only [S, lo, hi, exactDot]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi_mem
    rw [add_comm, fp.twoProduct_exact]
  have hsumhi : |∑ i : Fin (n + 1), hi i| ≤ |S| + L := by
    have heq : (∑ i : Fin (n + 1), hi i) =
        S - ∑ i : Fin (n + 1), lo i := by linarith [hsums]
    rw [heq]
    exact le_trans (abs_sub _ _) (add_le_add_right hsumlo |S|)
  have hW : W ≤ |S| + L + (2 * gamma fp.u n) * H := by
    have hv := vecSum_abs_sum_le_aux fp.toErrorFreeAddModel hi hvalid2n
    change W ≤ |S| + L + (2 * gamma fp.u n) * H
    exact le_trans hv (add_le_add_left hsumhi _)
  have hAt :
      (∑ j : Fin ((2 * n + 1) + 1), |dotKTransform fp x y j|) = L + W := by
    let aw : Fin ((n + 1) + (n + 1)) → ℝ := fun j => Fin.addCases lo w j
    calc
      (∑ j : Fin ((2 * n + 1) + 1), |dotKTransform fp x y j|) =
          ∑ j : Fin ((2 * n + 1) + 1),
            |aw (e j)| := by rfl
      _ = ∑ j : Fin ((n + 1) + (n + 1)), |aw j| :=
        Equiv.sum_comp e (fun j => |aw j|)
      _ = L + W := by
        dsimp only [aw]
        rw [Fin.sum_univ_add]
        change (∑ i : Fin (n + 1), |Fin.addCases lo w (Fin.castAdd (n + 1) i)|) +
            (∑ i : Fin (n + 1), |Fin.addCases lo w (Fin.natAdd (n + 1) i)|) = L + W
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi_mem
          rw [Fin.addCases_left]
        · apply Finset.sum_congr rfl
          intro i hi_mem
          rw [Fin.addCases_right]
  have hstep : (1 + fp.u) * gamma fp.u n + fp.u ≤ gamma fp.u (n + 1) :=
    gamma_step_aux fp.u fp.u_nonneg (n + 1) (by omega) hvalidN
  have hdouble : 2 * gamma fp.u (n + 1) ≤ gamma fp.u (2 * (n + 1)) := by
    have hv : (2 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u < 1 := by
      norm_num at hvalid2N ⊢
      nlinarith
    exact two_mul_gamma_le_gamma_two_aux fp.u fp.u_nonneg (n + 1) hv
  have hmono : gamma fp.u (2 * (n + 1)) ≤ gm := by
    dsimp only [gm]
    exact gamma_mono_index_aux fp.u fp.u_nonneg (by omega) hvalidm
  have hvalidn : (n : ℝ) * fp.u < 1 := by
    have hidx : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hidx fp.u_nonneg]
  have hgn0 : 0 ≤ gamma fp.u n := by
    rw [gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  rw [hAt]
  change L + W ≤ |S| + gm * M
  calc
    L + W ≤ L + (|S| + L + (2 * gamma fp.u n) * H) :=
      add_le_add_right hW L
    _ ≤ fp.u * M + (|S| + fp.u * M +
        (2 * gamma fp.u n) * ((1 + fp.u) * M)) := by
      have hch := mul_le_mul_of_nonneg_left hHM (by positivity : 0 ≤ 2 * gamma fp.u n)
      linarith
    _ = |S| + (2 * (fp.u + (1 + fp.u) * gamma fp.u n)) * M := by ring
    _ ≤ |S| + (2 * gamma fp.u (n + 1)) * M := by
      have hc : 2 * (fp.u + (1 + fp.u) * gamma fp.u n) ≤
          2 * gamma fp.u (n + 1) := by nlinarith
      exact add_le_add_right (mul_le_mul_of_nonneg_right hc hM0) |S|
    _ ≤ |S| + gm * M := by
      have hc : 2 * gamma fp.u (n + 1) ≤ gm := le_trans hdouble hmono
      exact add_le_add_right (mul_le_mul_of_nonneg_right hc hM0) |S|

theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START P02-T3-H001
  let q : ℕ := 2 * n + 1
  let L : ℕ := K - 1
  let v : Fin (q + 1) → ℝ := dotKTransform fp x y
  let g : ℝ := gamma fp.u (4 * (n + 1) - 2)
  let S : ℝ := exactDot x y
  let M : ℝ := dotMagnitude x y
  have hq : 1 ≤ q := by dsimp only [q]; omega
  have hL : 2 ≤ L := by dsimp only [L]; omega
  have hidx : 2 * q = 4 * (n + 1) - 2 := by dsimp only [q]; omega
  have hcoef : ((2 * q : ℕ) : ℝ) ≤
      (4 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 2 * q ≤ 4 * (n + 1) by dsimp only [q]; omega)
  have hhalf : (2 : ℝ) * (q : ℝ) * fp.u ≤ (1 : ℝ) / 2 := by
    have hm := mul_le_mul_of_nonneg_right hcoef fp.u_nonneg
    have hs : (4 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ (1 : ℝ) / 2 := by
      nlinarith [hsmall]
    have heq : (((2 * q : ℕ) : ℝ)) = (2 : ℝ) * (q : ℝ) := by norm_num
    rw [← heq]
    exact le_trans hm hs
  have hsum := sumK_error_aux fp.toErrorFreeAddModel hq hL hhalf v
  have hvsum : (∑ i : Fin (q + 1), v i) = S := by
    simpa only [q, v, S] using dotKTransform_sum_aux fp x y
  have hvabs : (∑ i : Fin (q + 1), |v i|) ≤ |S| + g * M := by
    simpa only [q, v, S, g, M] using dotKTransform_abs_sum_aux fp x y hsmall
  have hbase : |dotK fp K x y - S| ≤
      (fp.u + g ^ 2) * |S| + g ^ L *
        (∑ i : Fin (q + 1), |v i|) := by
    simpa only [dotK, L, v, q, hidx, g, hvsum] using hsum
  have hmidx_lt : (((4 * (n + 1) - 2 : ℕ) : ℝ)) <
      (8 : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 4 * (n + 1) - 2 < 8 * (n + 1) by omega)
  have hvalidg : (((4 * (n + 1) - 2 : ℕ) : ℝ)) * fp.u < 1 := by
    by_cases hu0 : fp.u = 0
    · rw [hu0]
      norm_num
    · have hupos : 0 < fp.u := lt_of_le_of_ne fp.u_nonneg (Ne.symm hu0)
      have hm := mul_lt_mul_of_pos_right hmidx_lt hupos
      nlinarith
  have hg0 : 0 ≤ g := by
    dsimp only [g]
    rw [gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (by linarith)
  have harg_half : (((4 * (n + 1) - 2 : ℕ) : ℝ)) * fp.u ≤ (1 : ℝ) / 2 := by
    have heq : (((4 * (n + 1) - 2 : ℕ) : ℝ)) = ((2 * q : ℕ) : ℝ) := by
      rw [hidx]
    rw [heq]
    norm_num at hhalf ⊢
    exact hhalf
  have hg1 : g ≤ 1 := by
    let a : ℝ := (((4 * (n + 1) - 2 : ℕ) : ℝ)) * fp.u
    have ha0 : 0 ≤ a := by
      dsimp only [a]
      exact mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg
    have ha : a ≤ (1 : ℝ) / 2 := harg_half
    have hd : 0 < 1 - a := by linarith
    have hgdef : g = a / (1 - a) := by dsimp only [g, gamma, a]
    rw [hgdef, div_le_iff₀ hd]
    nlinarith
  have hpow : g ^ L ≤ g ^ 2 := by
    apply pow_le_pow_of_le_one hg0 hg1
    exact hL
  have hpow0 : 0 ≤ g ^ L := pow_nonneg hg0 L
  have hM0 : 0 ≤ M := by dsimp only [M, dotMagnitude]; positivity
  have hSabs : 0 ≤ |S| := abs_nonneg S
  have huseabs := mul_le_mul_of_nonneg_left hvabs hpow0
  calc
    |dotK fp K x y - exactDot x y| = |dotK fp K x y - S| := by rfl
    _ ≤ (fp.u + g ^ 2) * |S| + g ^ L *
        (∑ i : Fin (q + 1), |v i|) := hbase
    _ ≤ (fp.u + g ^ 2) * |S| + g ^ L * (|S| + g * M) := by
      exact add_le_add_right huseabs _
    _ = (fp.u + g ^ 2 + g ^ L) * |S| + (g ^ L * g) * M := by ring
    _ ≤ (fp.u + 2 * g ^ 2) * |S| + (g ^ L * g) * M := by
      have hc : fp.u + g ^ 2 + g ^ L ≤ fp.u + 2 * g ^ 2 := by
        linarith [hpow]
      exact add_le_add_left
        (mul_le_mul_of_nonneg_right hc hSabs) ((g ^ L * g) * M)
    _ = (fp.u + 2 * g ^ 2) * |S| + g ^ K * M := by
      have hLK : L + 1 = K := by dsimp only [L]; omega
      rw [← pow_succ, hLK]
    _ = (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) *
        |exactDot x y| +
          (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by rfl

end HighamBench
