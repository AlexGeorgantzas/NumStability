import HighamBench.P02Definitions

namespace HighamBench

open scoped BigOperators

private lemma twoSumPrefix_zero (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    twoSumPrefix fp v 0 (Nat.zero_le n) = v ⟨0, Nat.succ_pos n⟩ := by
  simp [twoSumPrefix]

private lemma twoSumPrefix_succ (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (hk : k < n) :
    twoSumPrefix fp v (k + 1) (Nat.succ_le_of_lt hk) =
      (fp.twoSum (twoSumPrefix fp v k (Nat.le_of_lt hk))
        (v ⟨k + 1, Nat.succ_lt_succ hk⟩)).1 := by
  simp only [twoSumPrefix, Fin.foldl_succ_last]
  congr 3 <;> simp

private lemma twoSum_prefix_exact (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (hk : k ≤ n) :
    twoSumPrefix fp v k hk +
        ∑ i : Fin k,
          twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩ =
      ∑ i : Fin (k + 1),
        v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩ := by
  induction k with
  | zero =>
      simp [twoSumPrefix_zero]
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      rw [twoSumPrefix_succ fp v hkn]
      have he := fp.twoSum_exact
        (twoSumPrefix fp v k hk')
        (v ⟨k + 1, Nat.succ_lt_succ hkn⟩)
      have hi := ih hk'
      have he' :
          (fp.twoSum (twoSumPrefix fp v k hk')
              (v ⟨k + 1, Nat.succ_lt_succ hkn⟩)).1 +
            twoSumCorrection fp v ⟨k, hkn⟩ =
          twoSumPrefix fp v k hk' +
            v ⟨k + 1, Nat.succ_lt_succ hkn⟩ := by
        simpa [twoSumCorrection] using he
      have hcore :
          (fp.twoSum (twoSumPrefix fp v k hk')
                (v ⟨k + 1, Nat.succ_lt_succ hkn⟩)).1 +
              (∑ i : Fin k, twoSumCorrection fp v
                ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk'⟩) +
              twoSumCorrection fp v ⟨k, hkn⟩ =
            (∑ i : Fin (k + 1),
              v ⟨i.val,
                Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩) +
              v ⟨k + 1, Nat.succ_lt_succ hkn⟩ := by
        linarith [he', hi]
      simpa [add_assoc] using hcore

private lemma vecSum_sum (fp : ErrorFreeAddModel) {n : ℕ}
    (v : Fin (n + 1) → ℝ) :
    (∑ i, vecSum fp v i) = ∑ i, v i := by
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have h := twoSum_prefix_exact fp v (Nat.le_refl n)
  simpa [add_comm] using h

private lemma iteratedVecSum_sum (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) :
    (∑ i, iteratedVecSum fp k v i) = ∑ i, v i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [iteratedVecSum, vecSum_sum, ih]

private lemma twoSumPrefix_abs_bound (fp : ErrorFreeAddModel) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (hk : k ≤ n)
    (hku : (2 : ℝ) * (k : ℝ) * fp.u ≤ 1) :
    |twoSumPrefix fp v k hk| ≤
      (1 + 2 * (k : ℝ) * fp.u) *
        ∑ i : Fin (k + 1),
          |v ⟨i.val,
            Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk)⟩| := by
  induction k with
  | zero =>
      simp [twoSumPrefix_zero, abs_nonneg]
  | succ k ih =>
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hku' : (2 : ℝ) * (k : ℝ) * fp.u ≤ 1 := by
        have hu := fp.u_nonneg
        push_cast at hku ⊢
        nlinarith
      have hpre := ih hk' hku'
      rw [twoSumPrefix_succ fp v hkn]
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add
        (twoSumPrefix fp v k hk')
        (v ⟨k + 1, Nat.succ_lt_succ hkn⟩)
      rw [fp.twoSum_high, hfl, abs_mul, Fin.sum_univ_castSucc]
      have hadd :
          |twoSumPrefix fp v k hk' +
              v ⟨k + 1, Nat.succ_lt_succ hkn⟩| ≤
            |twoSumPrefix fp v k hk'| +
              |v ⟨k + 1, Nat.succ_lt_succ hkn⟩| :=
        abs_add_le _ _
      have hfac : |1 + δ| ≤ 1 + fp.u := by
        calc
          |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
          _ ≤ 1 + fp.u := by norm_num; linarith
      have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
      have hv0 : 0 ≤ |v ⟨k + 1, Nat.succ_lt_succ hkn⟩| := abs_nonneg _
      have hs0 : 0 ≤
          ∑ i : Fin (k + 1),
            |v ⟨i.val,
              Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩| :=
        Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hmul := mul_le_mul hadd hfac (abs_nonneg _) (by positivity)
      have hcoef0 : 0 ≤ 1 + 2 * (k : ℝ) * fp.u := by
        have := mul_nonneg (show 0 ≤ (2 : ℝ) * (k : ℝ) by positivity)
          fp.u_nonneg
        linarith
      have hmul' := mul_le_mul
        (add_le_add hpre (le_refl
          |v ⟨k + 1, Nat.succ_lt_succ hkn⟩|))
        (le_refl (1 + fp.u)) hfac0
        (add_nonneg (mul_nonneg hcoef0 hs0) hv0 : 0 ≤
          (1 + 2 * (k : ℝ) * fp.u) *
              (∑ i : Fin (k + 1),
                |v ⟨i.val,
                  Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩|) +
            |v ⟨k + 1, Nat.succ_lt_succ hkn⟩|)
      calc
        |twoSumPrefix fp v k hk' +
              v ⟨k + 1, Nat.succ_lt_succ hkn⟩| * |1 + δ| ≤
            (|twoSumPrefix fp v k hk'| +
              |v ⟨k + 1, Nat.succ_lt_succ hkn⟩|) *
                (1 + fp.u) := hmul
        _ ≤ (((1 + 2 * (k : ℝ) * fp.u) *
              (∑ i : Fin (k + 1),
                |v ⟨i.val,
                  Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩|)) +
              |v ⟨k + 1, Nat.succ_lt_succ hkn⟩|) *
                (1 + fp.u) := hmul'
        _ ≤ (1 + 2 * ((k + 1 : ℕ) : ℝ) * fp.u) *
              ((∑ i : Fin (k + 1),
                |v ⟨i.val,
                  Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ hk')⟩|) +
                |v ⟨k + 1, Nat.succ_lt_succ hkn⟩|) := by
          have hprod : 0 ≤ fp.u * (1 - 2 * (k : ℝ) * fp.u) :=
            mul_nonneg fp.u_nonneg (sub_nonneg.mpr hku')
          have hcoef :
              (1 + 2 * (k : ℝ) * fp.u) * (1 + fp.u) ≤
                1 + 2 * ((k + 1 : ℕ) : ℝ) * fp.u := by
            push_cast
            nlinarith
          have hone : 1 + fp.u ≤
              1 + 2 * ((k + 1 : ℕ) : ℝ) * fp.u := by
            push_cast
            nlinarith [fp.u_nonneg]
          have hp := mul_le_mul_of_nonneg_right hcoef hs0
          have hv := mul_le_mul_of_nonneg_right hone hv0
          push_cast at hp hv ⊢
          nlinarith

private noncomputable def lowMagnitude {q : ℕ}
    (v : Fin (q + 1) → ℝ) : ℝ :=
  ∑ i : Fin q, |v i.castSucc|

private lemma initial_abs_sum_le_lowMagnitude {q k : ℕ}
    (v : Fin (q + 1) → ℝ) (hk : k ≤ q) :
    (∑ i : Fin k,
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt
          (Nat.le_trans hk (Nat.le_succ q))⟩|) ≤
      lowMagnitude v := by
  let e : Fin k ↪ Fin q :=
    ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin q)) := by
    intro i hi
    simp
  have hle :
      (∑ i ∈ Finset.univ.map e, |v i.castSucc|) ≤
        ∑ i : Fin q, |v i.castSucc| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i hi hni
    positivity
  rw [Finset.sum_map] at hle
  simpa [lowMagnitude, e] using hle

private lemma initial_abs_sum_le_total {q k : ℕ}
    (v : Fin (q + 1) → ℝ) (hk : k ≤ q + 1) :
    (∑ i : Fin k,
        |v ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩|) ≤
      ∑ i, |v i| := by
  let e : Fin k ↪ Fin (q + 1) :=
    ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have hsub : Finset.univ.map e ⊆ (Finset.univ : Finset (Fin (q + 1))) := by
    intro i hi
    simp
  have hle :
      (∑ i ∈ Finset.univ.map e, |v i|) ≤ ∑ i, |v i| := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i hi hni
    positivity
  rw [Finset.sum_map] at hle
  simpa [e] using hle

private lemma lowMagnitude_nonneg {q : ℕ}
    (v : Fin (q + 1) → ℝ) : 0 ≤ lowMagnitude v :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma prefinal_corrections_bound (fp : ErrorFreeAddModel)
    {q : ℕ} (v : Fin (q + 1) → ℝ)
    (hq : 1 ≤ q) (hqu : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1) :
    (∑ i : Fin (q - 1),
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)⟩|) ≤
      (2 * (q : ℝ) * fp.u) * lowMagnitude v := by
  have hterm : ∀ i : Fin (q - 1),
      |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)⟩| ≤
        2 * fp.u * lowMagnitude v := by
    intro i
    have hiq : i.val < q :=
      Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)
    have hik : i.val + 1 ≤ q := Nat.succ_le_of_lt hiq
    have hiku : (2 : ℝ) * ((i.val + 1 : ℕ) : ℝ) * fp.u ≤ 1 := by
      have hu := fp.u_nonneg
      push_cast
      have hicast : ((i.val : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast hik
      nlinarith
    have hp := twoSumPrefix_abs_bound fp v hik hiku
    have hpart := initial_abs_sum_le_lowMagnitude v
      (show i.val + 2 ≤ q by omega)
    have hcoef : 1 + 2 * ((i.val + 1 : ℕ) : ℝ) * fp.u ≤ 2 := by
      have hu := fp.u_nonneg
      have hicast : ((i.val + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast hik
      have himul := mul_le_mul_of_nonneg_right hicast hu
      nlinarith [hqu, himul]
    have hprefix :
        |twoSumPrefix fp v (i.val + 1) hik| ≤
          2 * lowMagnitude v := by
      have hs := lowMagnitude_nonneg v
      calc
        |twoSumPrefix fp v (i.val + 1) hik| ≤
            (1 + 2 * ((i.val + 1 : ℕ) : ℝ) * fp.u) *
              (∑ j : Fin (i.val + 2),
                |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
                  (Nat.succ_le_succ hik)⟩|) := hp
        _ ≤ 2 * lowMagnitude v := by
          exact mul_le_mul hcoef hpart
            (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity)
    have hlo := fp.twoSum_low_le
      (twoSumPrefix fp v i.val (Nat.le_of_lt hiq))
      (v ⟨i.val + 1, Nat.succ_lt_succ hiq⟩)
    have hhigh := twoSumPrefix_succ fp v hiq
    have hlo' :
        |twoSumCorrection fp v ⟨i.val, hiq⟩| ≤
          fp.u * |twoSumPrefix fp v (i.val + 1) hik| := by
      simpa [twoSumCorrection, hhigh] using hlo
    calc
      |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)⟩| ≤
          fp.u * |twoSumPrefix fp v (i.val + 1) hik| := by
            simpa using hlo'
      _ ≤ fp.u * (2 * lowMagnitude v) :=
        mul_le_mul_of_nonneg_left hprefix fp.u_nonneg
      _ = 2 * fp.u * lowMagnitude v := by ring
  calc
    (∑ i : Fin (q - 1),
        |twoSumCorrection fp v
          ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)⟩|) ≤
        ∑ _i : Fin (q - 1), 2 * fp.u * lowMagnitude v :=
      Finset.sum_le_sum fun i _ => hterm i
    _ ≤ (2 * (q : ℝ) * fp.u) * lowMagnitude v := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hu := fp.u_nonneg
      have hs := lowMagnitude_nonneg v
      have hc : (((q - 1 : ℕ) : ℝ)) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.sub_le q 1)
      have hcoef : 0 ≤ 2 * fp.u * lowMagnitude v := by positivity
      have hm := mul_le_mul_of_nonneg_right hc hcoef
      nlinarith

private lemma lowMagnitude_vecSum_basic (fp : ErrorFreeAddModel)
    {q : ℕ} (v : Fin (q + 1) → ℝ)
    (hq : 1 ≤ q) (hqu : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1) :
    (1 - fp.u) * lowMagnitude (vecSum fp v) ≤
      (2 * (q : ℝ) * fp.u) * lowMagnitude v +
        fp.u * |∑ i, v i| := by
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0) with ⟨r, hr⟩
  subst q
  let q : ℕ := r + 1
  have hqeq : r + 1 = (r + 1 - 1) + 1 := by omega
  have hsplit :
      lowMagnitude (vecSum fp v) =
        (∑ i : Fin (q - 1),
          |twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)⟩|) +
          |twoSumCorrection fp v
            ⟨r + 1 - 1, by omega⟩| := by
    unfold lowMagnitude
    rw [Fin.sum_univ_castSucc]
    simp only [vecSum, Fin.lastCases_castSucc]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · apply Finset.sum_congr rfl
      intro i hi
      congr 2
    · congr 2
  have hpre := prefinal_corrections_bound fp v hq hqu
  have hexact := twoSum_prefix_exact fp v (Nat.le_refl q)
  have hcorrabs :
      |∑ i : Fin q, twoSumCorrection fp v i| ≤
        lowMagnitude (vecSum fp v) := by
    calc
      |∑ i : Fin q, twoSumCorrection fp v i| ≤
          ∑ i : Fin q, |twoSumCorrection fp v i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = lowMagnitude (vecSum fp v) := by
        unfold lowMagnitude
        apply Finset.sum_congr rfl
        intro i hi
        simp [vecSum]
  have hhigh :
      |twoSumPrefix fp v q (Nat.le_refl q)| ≤
        |∑ i, v i| + lowMagnitude (vecSum fp v) := by
    have hid :
        twoSumPrefix fp v q (Nat.le_refl q) =
          (∑ i, v i) - ∑ i : Fin q, twoSumCorrection fp v i := by
      linarith [hexact]
    rw [hid]
    calc
      |(∑ i, v i) - ∑ i : Fin q, twoSumCorrection fp v i| ≤
          |∑ i, v i| + |∑ i : Fin q, twoSumCorrection fp v i| :=
        abs_sub _ _
      _ ≤ |∑ i, v i| + lowMagnitude (vecSum fp v) :=
        add_le_add_right hcorrabs _
  have hlastlt : q - 1 < q := by omega
  have hlo := fp.twoSum_low_le
    (twoSumPrefix fp v (q - 1) (Nat.le_of_lt hlastlt))
    (v ⟨(q - 1) + 1, Nat.succ_lt_succ hlastlt⟩)
  have hprefinal := twoSumPrefix_succ fp v hlastlt
  have hlast :
      |twoSumCorrection fp v ⟨q - 1, hlastlt⟩| ≤
        fp.u * |twoSumPrefix fp v q (Nat.le_refl q)| := by
    have hprefinal' :
        (fp.twoSum
          (twoSumPrefix fp v (q - 1) (Nat.le_of_lt hlastlt))
          (v ⟨(q - 1) + 1, Nat.succ_lt_succ hlastlt⟩)).1 =
            twoSumPrefix fp v q (Nat.le_refl q) := by
      rw [← hprefinal]
      congr 2
    change
      |(fp.twoSum
          (twoSumPrefix fp v (q - 1) (Nat.le_of_lt hlastlt))
          (v ⟨(q - 1) + 1, Nat.succ_lt_succ hlastlt⟩)).2| ≤
        fp.u * |twoSumPrefix fp v q (Nat.le_refl q)|
    exact hlo.trans_eq (congrArg (fun z => fp.u * |z|) hprefinal')
  have hlow :
      lowMagnitude (vecSum fp v) ≤
        (2 * (q : ℝ) * fp.u) * lowMagnitude v +
          fp.u * (|∑ i, v i| + lowMagnitude (vecSum fp v)) := by
    calc
      lowMagnitude (vecSum fp v) =
          (∑ i : Fin (q - 1),
          |twoSumCorrection fp v
            ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.sub_le q 1)⟩|) +
          |twoSumCorrection fp v ⟨q - 1, by omega⟩| := hsplit
      _ ≤
          (2 * (q : ℝ) * fp.u) * lowMagnitude v +
            fp.u * |twoSumPrefix fp v q (Nat.le_refl q)| :=
        add_le_add hpre (by simpa using hlast)
      _ ≤ (2 * (q : ℝ) * fp.u) * lowMagnitude v +
          fp.u * (|∑ i, v i| + lowMagnitude (vecSum fp v)) :=
        add_le_add_right (mul_le_mul_of_nonneg_left hhigh fp.u_nonneg) _
  nlinarith

private lemma gamma_contraction_properties (u : ℝ) (q : ℕ)
    (hu : 0 ≤ u) (hq : 1 ≤ q)
    (hsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * u ≤ 1) :
    let g := gamma u (2 * q)
    0 ≤ g ∧ g ≤ 1 ∧
      (2 * (q : ℝ) * u) / (1 - u) ≤ g ∧
      u / (1 - u) ≤ g * (1 - g) := by
  let A : ℝ := 2 * (q : ℝ) * u
  let g : ℝ := gamma u (2 * q)
  have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hA_ge_two_u : 2 * u ≤ A := by
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_right hqR hu]
  have hbudget : 2 * A + 4 * u ≤ 1 := by
    dsimp [A]
    push_cast at hsmall
    nlinarith
  have hu_lt : u < 1 := by nlinarith
  have hAhalf : A < 1 / 2 := by nlinarith
  have hA_lt : A < 1 := by nlinarith
  have hdenu : 0 < 1 - u := by linarith
  have hdenA : 0 < 1 - A := by linarith
  have hg : g = A / (1 - A) := by
    simp only [g, gamma, A]
    push_cast
    ring
  have hg0 : 0 ≤ g := by
    rw [hg]
    positivity
  have hg1 : g ≤ 1 := by
    rw [hg]
    apply (div_le_iff₀ hdenA).2
    nlinarith
  have hcoef : A / (1 - u) ≤ g := by
    by_cases hu0 : u = 0
    · subst u
      simp [A, hg]
    · have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hApos : 0 < A := lt_of_lt_of_le (by nlinarith) hA_ge_two_u
      rw [hg]
      exact (div_le_div_iff_of_pos_left hApos hdenu hdenA).2 (by
        nlinarith [hA_ge_two_u])
  have hpoly : u * (1 - A) ^ 2 ≤ A * (1 - u) * (1 - 2 * A) := by
    have hClo : -1 ≤ A ^ 2 + A - 1 := by nlinarith [sq_nonneg A]
    have hCup : A ^ 2 + A - 1 ≤ 0 := by
      have hm := mul_nonpos_of_nonneg_of_nonpos hA0 (show A - 1 / 2 ≤ 0 by
        linarith)
      nlinarith
    by_cases hcase : A ≤ 1 / 4
    · have huC := mul_le_mul_of_nonneg_left hClo hu
      have hbase : A / 2 ≤ A - 2 * A ^ 2 := by
        have hm := mul_nonneg hA0 (show 0 ≤ 1 / 2 - 2 * A by linarith)
        nlinarith
      have huA : u ≤ A / 2 := by nlinarith [hA_ge_two_u]
      nlinarith
    · have hquarter : 1 / 4 ≤ A := le_of_not_ge hcase
      have huB : u ≤ (1 - 2 * A) / 4 := by nlinarith [hbudget]
      have hmulC := mul_le_mul_of_nonpos_right huB hCup
      have hfac1 : 0 ≤ 1 - 2 * A := by linarith
      have hfac2 : 0 ≤ A ^ 2 + 5 * A - 1 := by
        nlinarith [sq_nonneg A]
      have hprod := mul_nonneg hfac1 hfac2
      nlinarith
  have hinj : u / (1 - u) ≤ g * (1 - g) := by
    rw [hg]
    have hform :
        A / (1 - A) * (1 - A / (1 - A)) =
          (A * (1 - 2 * A)) / (1 - A) ^ 2 := by
      field_simp
      ring
    rw [hform]
    apply (div_le_div_iff₀ hdenu (sq_pos_of_pos hdenA)).2
    nlinarith [hpoly]
  exact ⟨hg0, hg1, by simpa [A] using hcoef, hinj⟩

private lemma lowMagnitude_vecSum_contract (fp : ErrorFreeAddModel)
    {q : ℕ} (v : Fin (q + 1) → ℝ)
    (hq : 1 ≤ q)
    (hsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    lowMagnitude (vecSum fp v) ≤
      gamma fp.u (2 * q) * lowMagnitude v +
        gamma fp.u (2 * q) * (1 - gamma fp.u (2 * q)) *
          |∑ i, v i| := by
  obtain ⟨hg0, hg1, hcoef, hinj⟩ :=
    gamma_contraction_properties fp.u q fp.u_nonneg hq hsmall
  have hqu : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1 := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    push_cast at hsmall
    nlinarith [mul_nonneg hq0 fp.u_nonneg]
  have hbasic := lowMagnitude_vecSum_basic fp v hq hqu
  have hden : 0 < 1 - fp.u := by
    have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hqmul := mul_le_mul_of_nonneg_right hqR fp.u_nonneg
    push_cast at hsmall
    nlinarith [hqmul]
  have hdiv :
      lowMagnitude (vecSum fp v) ≤
        ((2 * (q : ℝ) * fp.u) * lowMagnitude v +
          fp.u * |∑ i, v i|) / (1 - fp.u) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hbasic)
  have hsep :
      ((2 * (q : ℝ) * fp.u) * lowMagnitude v +
          fp.u * |∑ i, v i|) / (1 - fp.u) =
        ((2 * (q : ℝ) * fp.u) / (1 - fp.u)) * lowMagnitude v +
          (fp.u / (1 - fp.u)) * |∑ i, v i| := by
    field_simp
  rw [hsep] at hdiv
  calc
    lowMagnitude (vecSum fp v) ≤
        ((2 * (q : ℝ) * fp.u) / (1 - fp.u)) * lowMagnitude v +
          (fp.u / (1 - fp.u)) * |∑ i, v i| := hdiv
    _ ≤ gamma fp.u (2 * q) * lowMagnitude v +
        (gamma fp.u (2 * q) * (1 - gamma fp.u (2 * q))) *
          |∑ i, v i| :=
      add_le_add
        (mul_le_mul_of_nonneg_right hcoef (lowMagnitude_nonneg v))
        (mul_le_mul_of_nonneg_right hinj (abs_nonneg _))

private lemma lowMagnitude_iterated_bound (fp : ErrorFreeAddModel)
    {q k : ℕ} (v : Fin (q + 1) → ℝ)
    (hq : 1 ≤ q)
    (hsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    lowMagnitude (iteratedVecSum fp k v) ≤
      gamma fp.u (2 * q) * |∑ i, v i| +
        (gamma fp.u (2 * q)) ^ k * lowMagnitude v := by
  let g := gamma fp.u (2 * q)
  obtain ⟨hg0, hg1, hcoef, hinj⟩ :=
    gamma_contraction_properties fp.u q fp.u_nonneg hq hsmall
  induction k with
  | zero =>
      simp only [iteratedVecSum, pow_zero, one_mul]
      exact le_add_of_nonneg_left (mul_nonneg hg0 (abs_nonneg _))
  | succ k ih =>
      rw [iteratedVecSum]
      have hstep := lowMagnitude_vecSum_contract fp
        (iteratedVecSum fp k v) hq hsmall
      have hsum := iteratedVecSum_sum fp v (k := k)
      rw [hsum] at hstep
      have hmul := mul_le_mul_of_nonneg_left ih hg0
      change g * lowMagnitude (iteratedVecSum fp k v) ≤
        g * (g * |∑ i, v i| + g ^ k * lowMagnitude v) at hmul
      calc
        lowMagnitude (vecSum fp (iteratedVecSum fp k v)) ≤
            g * lowMagnitude (iteratedVecSum fp k v) +
              g * (1 - g) * |∑ i, v i| := by simpa [g] using hstep
        _ ≤ g * (g * |∑ i, v i| + g ^ k * lowMagnitude v) +
              g * (1 - g) * |∑ i, v i| :=
          add_le_add hmul (le_refl (g * (1 - g) * |∑ i, v i|))
        _ = g * |∑ i, v i| + g ^ (k + 1) * lowMagnitude v := by
          ring

private lemma recursiveSum_error_bound (fp : StandardAddModel)
    {q : ℕ} (v : Fin q → ℝ)
    (hqu : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1) :
    |recursiveSum fp.fl_add q v - ∑ i, v i| ≤
      (2 * ((q - 1 : ℕ) : ℝ) * fp.u) * ∑ i, |v i| := by
  induction q with
  | zero => simp [recursiveSum]
  | succ q ih =>
      by_cases hq0 : q = 0
      · subst q
        simp [recursiveSum]
      · have hqpos : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
        have hqu' : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1 := by
          have hu := fp.u_nonneg
          push_cast at hqu ⊢
          nlinarith
        have hi := ih (fun i : Fin q => v i.castSucc) hqu'
        obtain ⟨δ, hδ, hfl⟩ := fp.model_add
          (recursiveSum fp.fl_add q (fun i : Fin q => v i.castSucc))
          (v (Fin.last q))
        rw [recursiveSum, dif_neg hq0, hfl, Fin.sum_univ_castSucc,
          Fin.sum_univ_castSucc]
        let a := recursiveSum fp.fl_add q (fun i : Fin q => v i.castSucc)
        let t := ∑ i : Fin q, v i.castSucc
        let b := v (Fin.last q)
        let S := ∑ i : Fin q, |v i.castSucc|
        have hid :
            (a + b) * (1 + δ) - (t + b) =
              δ * (t + b) + (1 + δ) * (a - t) := by ring
        rw [hid]
        have habs := abs_add_le (δ * (t + b)) ((1 + δ) * (a - t))
        have hd : |δ| ≤ fp.u := hδ
        have hfac : |1 + δ| ≤ 1 + fp.u := by
          calc
            |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
            _ ≤ 1 + fp.u := by norm_num; linarith
        have hsumabs : |t + b| ≤ S + |b| := by
          dsimp [t, b, S]
          exact le_trans (abs_add_le _ _)
            (add_le_add (Finset.abs_sum_le_sum_abs _ _) (le_refl _))
        have hi' : |a - t| ≤
            (2 * ((q - 1 : ℕ) : ℝ) * fp.u) * S := by
          simpa [a, t, S] using hi
        have hu1 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
        have hfirst : |δ * (t + b)| ≤ fp.u * (S + |b|) := by
          rw [abs_mul]
          exact mul_le_mul hd hsumabs (abs_nonneg _) fp.u_nonneg
        have hsecond : |(1 + δ) * (a - t)| ≤
            (1 + fp.u) *
              ((2 * ((q - 1 : ℕ) : ℝ) * fp.u) * S) := by
          rw [abs_mul]
          exact mul_le_mul hfac hi' (abs_nonneg _) hu1
        calc
          |δ * (t + b) + (1 + δ) * (a - t)| ≤
              |δ * (t + b)| + |(1 + δ) * (a - t)| := habs
          _ ≤ fp.u * (S + |b|) +
              (1 + fp.u) *
                ((2 * ((q - 1 : ℕ) : ℝ) * fp.u) * S) :=
            add_le_add hfirst hsecond
          _ ≤ (2 * (((q + 1) - 1 : ℕ) : ℝ) * fp.u) *
              (S + |b|) := by
            have hS : 0 ≤ S := by
              dsimp [S]
              exact Finset.sum_nonneg fun _ _ => abs_nonneg _
            have hb : 0 ≤ |b| := abs_nonneg _
            have hu := fp.u_nonneg
            have hprod : 0 ≤ fp.u *
                (1 - 2 * ((q - 1 : ℕ) : ℝ) * fp.u) := by
              apply mul_nonneg hu
              have hcast : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
                exact_mod_cast (Nat.sub_le q 1)
              have hm := mul_le_mul_of_nonneg_right hcast hu
              nlinarith [hqu']
            have hsubcast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
              rw [Nat.cast_sub hqpos]
              norm_num
            have hcoefS : fp.u +
                (1 + fp.u) * (2 * ((q - 1 : ℕ) : ℝ) * fp.u) ≤
                  2 * (q : ℝ) * fp.u := by
              nlinarith [hprod]
            have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqpos
            have hcoefB : fp.u ≤ 2 * (q : ℝ) * fp.u := by
              have hm := mul_le_mul_of_nonneg_right hqR hu
              nlinarith
            have hmS := mul_le_mul_of_nonneg_right hcoefS hS
            have hmB := mul_le_mul_of_nonneg_right hcoefB hb
            push_cast
            nlinarith [hmS, hmB]

private lemma recursiveSum_lowMagnitude_error (fp : ErrorFreeAddModel)
    {q : ℕ} (v : Fin (q + 1) → ℝ)
    (hq : 1 ≤ q)
    (hsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |recursiveSum fp.fl_add (q + 1) v - ∑ i, v i| ≤
      fp.u * |∑ i, v i| +
        gamma fp.u (2 * q) * lowMagnitude v := by
  have hqu : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1 := by
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
    push_cast at hsmall
    nlinarith [mul_nonneg hq0 fp.u_nonneg]
  have hrec := recursiveSum_error_bound fp.toStandardAddModel
    (fun i : Fin q => v i.castSucc) hqu
  obtain ⟨hg0, hg1, hcoef, hinj⟩ :=
    gamma_contraction_properties fp.u q fp.u_nonneg hq hsmall
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add
    (recursiveSum fp.fl_add q (fun i : Fin q => v i.castSucc))
    (v (Fin.last q))
  rw [recursiveSum, dif_neg (by omega), hfl, Fin.sum_univ_castSucc]
  let a := recursiveSum fp.fl_add q (fun i : Fin q => v i.castSucc)
  let t := ∑ i : Fin q, v i.castSucc
  let b := v (Fin.last q)
  let R := lowMagnitude v
  have hR : R = ∑ i : Fin q, |v i.castSucc| := rfl
  have hid :
      (a + b) * (1 + δ) - (t + b) =
        δ * (t + b) + (1 + δ) * (a - t) := by ring
  rw [hid]
  have habs := abs_add_le (δ * (t + b)) ((1 + δ) * (a - t))
  have hfac : |1 + δ| ≤ 1 + fp.u := by
    calc
      |1 + δ| ≤ |(1 : ℝ)| + |δ| := abs_add_le _ _
      _ ≤ 1 + fp.u := by norm_num; linarith
  have hfirst : |δ * (t + b)| ≤ fp.u * |t + b| := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hδ (abs_nonneg _)
  have hrec' : |a - t| ≤
      (2 * ((q - 1 : ℕ) : ℝ) * fp.u) * R := by
    simpa [a, t, R, lowMagnitude] using hrec
  have hsecond : |(1 + δ) * (a - t)| ≤
      ((1 + fp.u) * (2 * ((q - 1 : ℕ) : ℝ) * fp.u)) * R := by
    rw [abs_mul]
    have hfac0 : 0 ≤ 1 + fp.u := by linarith [fp.u_nonneg]
    calc
      |1 + δ| * |a - t| ≤ (1 + fp.u) * |a - t| :=
        mul_le_mul_of_nonneg_right hfac (abs_nonneg _)
      _ ≤ (1 + fp.u) *
          ((2 * ((q - 1 : ℕ) : ℝ) * fp.u) * R) :=
        mul_le_mul_of_nonneg_left hrec' hfac0
      _ = ((1 + fp.u) *
          (2 * ((q - 1 : ℕ) : ℝ) * fp.u)) * R := by ring
  have hcoef_final :
      (1 + fp.u) * (2 * ((q - 1 : ℕ) : ℝ) * fp.u) ≤
        gamma fp.u (2 * q) := by
    have hsubcast : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
      rw [Nat.cast_sub hq]
      norm_num
    have hqm1 : ((q - 1 : ℕ) : ℝ) * fp.u ≤ 1 := by
      have hcast : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast (Nat.sub_le q 1)
      have hm := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
      nlinarith [hqu]
    have htoA :
        (1 + fp.u) * (2 * ((q - 1 : ℕ) : ℝ) * fp.u) ≤
          2 * (q : ℝ) * fp.u := by
      nlinarith [mul_nonneg fp.u_nonneg (sub_nonneg.mpr hqm1)]
    have hden : 0 < 1 - fp.u := by
      have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have hm := mul_le_mul_of_nonneg_right hqR fp.u_nonneg
      push_cast at hsmall
      nlinarith
    have hAdiv : 2 * (q : ℝ) * fp.u ≤
        (2 * (q : ℝ) * fp.u) / (1 - fp.u) := by
      apply (le_div_iff₀ hden).2
      have hA0 : 0 ≤ 2 * (q : ℝ) * fp.u :=
        mul_nonneg (by positivity) fp.u_nonneg
      nlinarith [mul_nonneg hA0 fp.u_nonneg]
    exact le_trans htoA (le_trans hAdiv hcoef)
  have hsecond' : |(1 + δ) * (a - t)| ≤
      gamma fp.u (2 * q) * R :=
    le_trans hsecond (mul_le_mul_of_nonneg_right hcoef_final
      (lowMagnitude_nonneg v))
  calc
    |δ * (t + b) + (1 + δ) * (a - t)| ≤
        |δ * (t + b)| + |(1 + δ) * (a - t)| := habs
    _ ≤ fp.u * |t + b| + gamma fp.u (2 * q) * R :=
      add_le_add hfirst hsecond'

private lemma sumK_error_bound (fp : ErrorFreeAddModel)
    {q J : ℕ} (v : Fin (q + 1) → ℝ)
    (hq : 1 ≤ q) (hJ : 1 ≤ J)
    (hsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |sumK fp J v - ∑ i, v i| ≤
      (fp.u + (gamma fp.u (2 * q)) ^ 2) * |∑ i, v i| +
        (gamma fp.u (2 * q)) ^ J * ∑ i, |v i| := by
  let g := gamma fp.u (2 * q)
  let w := iteratedVecSum fp (J - 1) v
  have hsum : (∑ i, w i) = ∑ i, v i :=
    iteratedVecSum_sum fp v
  have hfinal := recursiveSum_lowMagnitude_error fp w hq hsmall
  rw [hsum] at hfinal
  have hlow := lowMagnitude_iterated_bound fp v (k := J - 1) hq hsmall
  have hg0 : 0 ≤ g :=
    (gamma_contraction_properties fp.u q fp.u_nonneg hq hsmall).1
  have hmul := mul_le_mul_of_nonneg_left hlow hg0
  change g * lowMagnitude w ≤
    g * (g * |∑ i, v i| + g ^ (J - 1) * lowMagnitude v) at hmul
  have hpow : g * g ^ (J - 1) = g ^ J := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
    simp [pow_succ, mul_comm]
  have hlowtotal : lowMagnitude v ≤ ∑ i, |v i| := by
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hgpow0 : 0 ≤ g ^ J := pow_nonneg hg0 _
  unfold sumK
  change |recursiveSum fp.fl_add (q + 1) w - ∑ i, v i| ≤ _
  calc
    |recursiveSum fp.fl_add (q + 1) w - ∑ i, v i| ≤
        fp.u * |∑ i, v i| + g * lowMagnitude w := by
      simpa [g, w] using hfinal
    _ ≤ fp.u * |∑ i, v i| +
        g * (g * |∑ i, v i| + g ^ (J - 1) * lowMagnitude v) :=
      add_le_add (le_refl _) hmul
    _ = (fp.u + g ^ 2) * |∑ i, v i| +
        (g * g ^ (J - 1)) * lowMagnitude v := by ring
    _ = (fp.u + g ^ 2) * |∑ i, v i| +
        g ^ J * lowMagnitude v := by rw [hpow]
    _ ≤ (fp.u + g ^ 2) * |∑ i, v i| +
        g ^ J * ∑ i, |v i| :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hlowtotal hgpow0)

private lemma dotKTransform_sum (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ) :
    (∑ i, dotKTransform fp x y i) = exactDot x y := by
  let d := (2 * n + 1) + 1
  let a := (n + 1) + (n + 1)
  have hda : d = a := by dsimp [d, a]; omega
  let e : Fin d ≃ Fin a :=
    { toFun := fun i => ⟨i.val, by rw [← hda]; exact i.isLt⟩
      invFun := fun i => ⟨i.val, by rw [hda]; exact i.isLt⟩
      left_inv := by intro i; apply Fin.ext; rfl
      right_inv := by intro i; apply Fin.ext; rfl }
  have hcast :
      (∑ i : Fin d, dotKTransform fp x y i) =
        ∑ i : Fin a,
          Fin.addCases
            (fun j : Fin (n + 1) => (fp.twoProduct (x j) (y j)).2)
            (vecSum fp.toErrorFreeAddModel
              (fun j : Fin (n + 1) => (fp.twoProduct (x j) (y j)).1)) i := by
    apply Fintype.sum_equiv e
    intro i
    unfold dotKTransform
    apply congrArg (Fin.addCases
      (fun j : Fin (n + 1) => (fp.twoProduct (x j) (y j)).2)
      (vecSum fp.toErrorFreeAddModel
        (fun j : Fin (n + 1) => (fp.twoProduct (x j) (y j)).1)))
    apply Fin.ext
    rfl
  rw [hcast, Fin.sum_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right]
  rw [vecSum_sum]
  unfold exactDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [add_comm] using fp.twoProduct_exact (x i) (y i)

private lemma lowMagnitude_vecSum_bound (fp : ErrorFreeAddModel)
    {q : ℕ} (v : Fin (q + 1) → ℝ)
    (hqu : (2 : ℝ) * (q : ℝ) * fp.u ≤ 1) :
    lowMagnitude (vecSum fp v) ≤
      (2 * (q : ℝ) * fp.u) * ∑ i, |v i| := by
  have hterm : ∀ i : Fin q,
      |twoSumCorrection fp v i| ≤ 2 * fp.u * ∑ j, |v j| := by
    intro i
    have hik : i.val + 1 ≤ q := Nat.succ_le_of_lt i.isLt
    have hiku : (2 : ℝ) * ((i.val + 1 : ℕ) : ℝ) * fp.u ≤ 1 := by
      have hicast : ((i.val + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hik
      have hm := mul_le_mul_of_nonneg_right hicast fp.u_nonneg
      nlinarith [hqu]
    have hp := twoSumPrefix_abs_bound fp v hik hiku
    have hpart :
        (∑ j : Fin (i.val + 2),
          |v ⟨j.val, Nat.lt_of_lt_of_le j.isLt
            (Nat.succ_le_succ hik)⟩|) ≤ ∑ j, |v j| := by
      exact initial_abs_sum_le_total v (show i.val + 2 ≤ q + 1 by omega)
    have hcoef :
        1 + 2 * ((i.val + 1 : ℕ) : ℝ) * fp.u ≤ 2 := by
      have hicast : ((i.val + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by
        exact_mod_cast hik
      have hm := mul_le_mul_of_nonneg_right hicast fp.u_nonneg
      nlinarith [hqu]
    have hprefix : |twoSumPrefix fp v (i.val + 1) hik| ≤
        2 * ∑ j, |v j| := by
      exact le_trans hp (mul_le_mul hcoef hpart
        (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by positivity))
    have hlo := fp.twoSum_low_le
      (twoSumPrefix fp v i.val (Nat.le_of_lt i.isLt))
      (v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    have hhigh := twoSumPrefix_succ fp v i.isLt
    have hlo' : |twoSumCorrection fp v i| ≤
        fp.u * |twoSumPrefix fp v (i.val + 1) hik| := by
      simpa [twoSumCorrection, hhigh] using hlo
    calc
      |twoSumCorrection fp v i| ≤
          fp.u * |twoSumPrefix fp v (i.val + 1) hik| := hlo'
      _ ≤ fp.u * (2 * ∑ j, |v j|) :=
        mul_le_mul_of_nonneg_left hprefix fp.u_nonneg
      _ = 2 * fp.u * ∑ j, |v j| := by ring
  unfold lowMagnitude
  simp only [vecSum, Fin.lastCases_castSucc]
  calc
    (∑ i : Fin q, |twoSumCorrection fp v i|) ≤
        ∑ _i : Fin q, 2 * fp.u * ∑ j, |v j| :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (2 * (q : ℝ) * fp.u) * ∑ j, |v j| := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring

private lemma vecSum_abs_sum_bound (fp : ErrorFreeAddModel) {q : ℕ}
    (v : Fin (q + 1) → ℝ) :
    (∑ i, |vecSum fp v i|) ≤
      |∑ i, v i| + 2 * lowMagnitude (vecSum fp v) := by
  have hexact := twoSum_prefix_exact fp v (Nat.le_refl q)
  have hcorrabs :
      |∑ i : Fin q, twoSumCorrection fp v i| ≤
        lowMagnitude (vecSum fp v) := by
    calc
      |∑ i : Fin q, twoSumCorrection fp v i| ≤
          ∑ i : Fin q, |twoSumCorrection fp v i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = lowMagnitude (vecSum fp v) := by
        unfold lowMagnitude
        apply Finset.sum_congr rfl
        intro i hi
        simp [vecSum]
  have hhigh : |twoSumPrefix fp v q (Nat.le_refl q)| ≤
      |∑ i, v i| + lowMagnitude (vecSum fp v) := by
    have hid : twoSumPrefix fp v q (Nat.le_refl q) =
        (∑ i, v i) - ∑ i : Fin q, twoSumCorrection fp v i := by
      linarith [hexact]
    rw [hid]
    exact le_trans (abs_sub _ _)
      (add_le_add (le_refl _) hcorrabs)
  rw [Fin.sum_univ_castSucc]
  simp only [vecSum, Fin.lastCases_castSucc, Fin.lastCases_last]
  have hloweq :
      (∑ i : Fin q, |twoSumCorrection fp v i|) =
        lowMagnitude (vecSum fp v) := by
    unfold lowMagnitude
    apply Finset.sum_congr rfl
    intro i hi
    simp [vecSum]
  rw [hloweq]
  linarith

private lemma dotKTransform_abs_sum_bound (fp : ErrorFreeDotModel) {n : ℕ}
    (x y : Fin (n + 1) → ℝ)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    (∑ i, |dotKTransform fp x y i|) ≤
      |exactDot x y| +
        gamma fp.u (4 * (n + 1) - 2) * dotMagnitude x y := by
  let lo : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).2
  let hi : Fin (n + 1) → ℝ := fun i => (fp.twoProduct (x i) (y i)).1
  let L : ℝ := ∑ i, |lo i|
  let H : ℝ := ∑ i, |hi i|
  let M : ℝ := dotMagnitude x y
  let q : ℕ := 2 * n + 1
  let g : ℝ := gamma fp.u (2 * q)
  have hM0 : 0 ≤ M := by
    dsimp [M, dotMagnitude]
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hL : L ≤ fp.u * M := by
    dsimp [L, M, lo, dotMagnitude]
    calc
      (∑ i, |(fp.twoProduct (x i) (y i)).2|) ≤
          ∑ i, fp.u * |x i * y i| :=
        Finset.sum_le_sum fun i _ => fp.twoProduct_low_le_exact (x i) (y i)
      _ = fp.u * ∑ i, |x i| * |y i| := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi_mem
        rw [abs_mul]
  have hH : H ≤ (1 + fp.u) * M := by
    dsimp [H, M, hi, dotMagnitude]
    calc
      (∑ i, |(fp.twoProduct (x i) (y i)).1|) ≤
          ∑ i, (1 + fp.u) * (|x i| * |y i|) := by
        apply Finset.sum_le_sum
        intro i hi_mem
        have he := fp.twoProduct_exact (x i) (y i)
        have hlo := fp.twoProduct_low_le_exact (x i) (y i)
        have htri : |(fp.twoProduct (x i) (y i)).1| ≤
            |x i * y i| + |(fp.twoProduct (x i) (y i)).2| := by
          have hid : (fp.twoProduct (x i) (y i)).1 =
              x i * y i - (fp.twoProduct (x i) (y i)).2 := by linarith
          rw [hid]
          exact abs_sub _ _
        rw [abs_mul] at htri hlo
        nlinarith [mul_nonneg fp.u_nonneg
          (mul_nonneg (abs_nonneg (x i)) (abs_nonneg (y i)))]
      _ = (1 + fp.u) * ∑ i, |x i| * |y i| := by
        rw [Finset.mul_sum]
  have h2nu : (2 : ℝ) * (n : ℝ) * fp.u ≤ 1 := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    push_cast at hsmall
    nlinarith [mul_nonneg hn0 fp.u_nonneg]
  have hC := lowMagnitude_vecSum_bound fp.toErrorFreeAddModel hi h2nu
  have hC' : lowMagnitude (vecSum fp.toErrorFreeAddModel hi) ≤
      (2 * (n : ℝ) * fp.u) * ((1 + fp.u) * M) :=
    le_trans hC (mul_le_mul_of_nonneg_left hH
      (mul_nonneg (by positivity) fp.u_nonneg))
  have hsumprod : (∑ i, hi i) + ∑ i, lo i = exactDot x y := by
    dsimp [hi, lo, exactDot]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi_mem
    exact fp.twoProduct_exact (x i) (y i)
  have hlosum : |∑ i, lo i| ≤ L := by
    dsimp [L]
    exact Finset.abs_sum_le_sum_abs _ _
  have hhisum : |∑ i, hi i| ≤ |exactDot x y| + L := by
    have hid : (∑ i, hi i) = exactDot x y - ∑ i, lo i := by
      linarith [hsumprod]
    rw [hid]
    exact le_trans (abs_sub _ _) (add_le_add (le_refl _) hlosum)
  have hvec := vecSum_abs_sum_bound fp.toErrorFreeAddModel hi
  have hdecomp :
      (∑ i, |dotKTransform fp x y i|) =
        L + ∑ i, |vecSum fp.toErrorFreeAddModel hi i| := by
    let d := (2 * n + 1) + 1
    let a := (n + 1) + (n + 1)
    have hda : d = a := by dsimp [d, a]; omega
    let e : Fin d ≃ Fin a :=
      { toFun := fun i => ⟨i.val, by rw [← hda]; exact i.isLt⟩
        invFun := fun i => ⟨i.val, by rw [hda]; exact i.isLt⟩
        left_inv := by intro i; apply Fin.ext; rfl
        right_inv := by intro i; apply Fin.ext; rfl }
    have hcast :
        (∑ i : Fin d, |dotKTransform fp x y i|) =
          ∑ i : Fin a,
            |Fin.addCases lo (vecSum fp.toErrorFreeAddModel hi) i| := by
      apply Fintype.sum_equiv e
      intro i
      unfold dotKTransform
      apply congrArg abs
      apply congrArg (Fin.addCases lo (vecSum fp.toErrorFreeAddModel hi))
      apply Fin.ext
      rfl
    rw [hcast, Fin.sum_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rfl
  have hraw :
      (∑ i, |dotKTransform fp x y i|) ≤
        |exactDot x y| +
          (2 * fp.u + 4 * (n : ℝ) * fp.u * (1 + fp.u)) * M := by
    rw [hdecomp]
    calc
      L + ∑ i, |vecSum fp.toErrorFreeAddModel hi i| ≤
          L + (|∑ i, hi i| +
            2 * lowMagnitude (vecSum fp.toErrorFreeAddModel hi)) :=
        add_le_add (le_refl _) hvec
      _ ≤ L + ((|exactDot x y| + L) +
            2 * ((2 * (n : ℝ) * fp.u) * ((1 + fp.u) * M))) :=
        add_le_add (le_refl _) (add_le_add hhisum
          (mul_le_mul_of_nonneg_left hC' (by norm_num)))
      _ ≤ |exactDot x y| +
          (2 * fp.u + 4 * (n : ℝ) * fp.u * (1 + fp.u)) * M := by
        have hL0 : 0 ≤ L := by
          dsimp [L]
          exact Finset.sum_nonneg fun _ _ => abs_nonneg _
        nlinarith [hL]
  have hqsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * fp.u ≤ 1 := by
    dsimp [q]
    push_cast at hsmall ⊢
    nlinarith
  obtain ⟨hg0, hg1, hcoef, hinj⟩ :=
    gamma_contraction_properties fp.u q fp.u_nonneg (by dsimp [q]; omega) hqsmall
  have hden : 0 < 1 - fp.u := by
    push_cast at hsmall
    nlinarith [fp.u_nonneg]
  have hcdiv :
      2 * fp.u + 4 * (n : ℝ) * fp.u * (1 + fp.u) ≤
        (2 * (q : ℝ) * fp.u) / (1 - fp.u) := by
    apply (le_div_iff₀ hden).2
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hnonneg : 0 ≤ (n : ℝ) * fp.u * (fp.u ^ 2) :=
      mul_nonneg (mul_nonneg hn0 fp.u_nonneg) (sq_nonneg fp.u)
    dsimp [q]
    push_cast
    nlinarith [sq_nonneg fp.u, hnonneg]
  have hcg :
      2 * fp.u + 4 * (n : ℝ) * fp.u * (1 + fp.u) ≤ g :=
    le_trans hcdiv (by simpa [g] using hcoef)
  have hfinish := add_le_add_left (mul_le_mul_of_nonneg_right hcg hM0)
    |exactDot x y|
  have hgindex : 2 * q = 4 * (n + 1) - 2 := by
    dsimp [q]
    omega
  change
    (2 * fp.u + 4 * (n : ℝ) * fp.u * (1 + fp.u)) * M +
        |exactDot x y| ≤
      gamma fp.u (2 * q) * M + |exactDot x y| at hfinish
  rw [hgindex] at hfinish
  exact le_trans hraw (by simpa [M, add_comm] using hfinish)

theorem p02_t3_dotK_error_bound
    (fp : ErrorFreeDotModel) (n K : ℕ) (x y : Fin (n + 1) → ℝ)
    (hK : 3 ≤ K)
    (hsmall : (8 : ℝ) * ((n + 1 : ℕ) : ℝ) * fp.u ≤ 1) :
    |dotK fp K x y - exactDot x y| ≤
      (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) * |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
  -- PROOF_START P02-T3-H001
  let q : ℕ := 2 * n + 1
  let J : ℕ := K - 1
  let r : Fin (q + 1) → ℝ := dotKTransform fp x y
  let g : ℝ := gamma fp.u (2 * q)
  have hq : 1 ≤ q := by dsimp [q]; omega
  have hJ : 1 ≤ J := by dsimp [J]; omega
  have hqsmall : (4 : ℝ) * ((q + 1 : ℕ) : ℝ) * fp.u ≤ 1 := by
    dsimp [q]
    push_cast at hsmall ⊢
    nlinarith
  have hsum : (∑ i, r i) = exactDot x y := by
    simpa [r, q] using dotKTransform_sum fp x y
  have hmag : (∑ i, |r i|) ≤
      |exactDot x y| + g * dotMagnitude x y := by
    have h := dotKTransform_abs_sum_bound fp x y hsmall
    have hidx : 2 * q = 4 * (n + 1) - 2 := by
      dsimp [q]
      omega
    rw [← hidx] at h
    simpa [r, g, q] using h
  have hbase := sumK_error_bound fp.toErrorFreeAddModel r hq hJ hqsmall
  rw [hsum] at hbase
  obtain ⟨hg0, hg1, hcoef, hinj⟩ :=
    gamma_contraction_properties fp.u q fp.u_nonneg hq hqsmall
  change 0 ≤ g at hg0
  change g ≤ 1 at hg1
  have hgpow0 : 0 ≤ g ^ J := pow_nonneg hg0 _
  have hmagmul := mul_le_mul_of_nonneg_left hmag hgpow0
  have hpowone : ∀ t : ℕ, g ^ t ≤ 1 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
        rw [pow_succ]
        exact le_trans (mul_le_mul ih hg1 hg0 (by norm_num)) (by norm_num)
  have hJtwo : 2 ≤ J := by dsimp [J]; omega
  have hpowJ : g ^ J ≤ g ^ 2 := by
    obtain ⟨t, ht⟩ : ∃ t, J = 2 + t := by
      exact ⟨J - 2, by omega⟩
    rw [ht, pow_add]
    simpa using mul_le_mul_of_nonneg_left (hpowone t) (pow_nonneg hg0 2)
  have hpowK : g ^ J * g = g ^ K := by
    have hJK : J + 1 = K := by dsimp [J]; omega
    rw [← pow_succ, hJK]
  have habs0 : 0 ≤ |exactDot x y| := abs_nonneg _
  have hM0 : 0 ≤ dotMagnitude x y := by
    unfold dotMagnitude
    exact Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  unfold dotK
  change |sumK fp.toErrorFreeAddModel J r - exactDot x y| ≤ _
  have hidx : 2 * q = 4 * (n + 1) - 2 := by
    dsimp [q]
    omega
  calc
    |sumK fp.toErrorFreeAddModel J r - exactDot x y| ≤
        (fp.u + g ^ 2) * |exactDot x y| +
          g ^ J * ∑ i, |r i| := by
      simpa [g] using hbase
    _ ≤ (fp.u + g ^ 2) * |exactDot x y| +
          g ^ J * (|exactDot x y| + g * dotMagnitude x y) :=
      add_le_add (le_refl _) hmagmul
    _ = (fp.u + g ^ 2 + g ^ J) * |exactDot x y| +
          (g ^ J * g) * dotMagnitude x y := by ring
    _ = (fp.u + g ^ 2 + g ^ J) * |exactDot x y| +
          g ^ K * dotMagnitude x y := by rw [hpowK]
    _ ≤ (fp.u + 2 * g ^ 2) * |exactDot x y| +
          g ^ K * dotMagnitude x y := by
      have hcoeff : fp.u + g ^ 2 + g ^ J ≤ fp.u + 2 * g ^ 2 := by
        linarith [hpowJ]
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoeff habs0) (le_refl _)
    _ = (fp.u + 2 * (gamma fp.u (4 * (n + 1) - 2)) ^ 2) *
          |exactDot x y| +
        (gamma fp.u (4 * (n + 1) - 2)) ^ K * dotMagnitude x y := by
      rw [← hidx]

end HighamBench
