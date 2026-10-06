import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma sum_eq_diag_add_lower {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hupper : ∀ j : Fin n, i.val < j.val → f j = 0) :
    ∑ j : Fin n, f j = f i +
      ∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      by_cases hi : i = Fin.last n
      · subst i
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_last]
        rw [add_comm]
        congr 1
      · let i' : Fin n := i.castPred hi
        have hii : i'.castSucc = i := by
          apply Fin.ext
          rfl
        rw [Fin.sum_univ_castSucc]
        have hlast : f (Fin.last n) = 0 := hupper (Fin.last n) (by
          rw [← hii]
          exact Fin.castSucc_lt_last i')
        rw [hlast, add_zero]
        have hrec := ih (fun j : Fin n => f j.castSucc) i'
          (fun j hj => hupper j.castSucc (by simpa [i'] using hj))
        rw [hrec]
        congr 1

private lemma sum_upper_bij {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩ =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), f j := by
  refine Finset.sum_bij
    (fun t _ => (⟨i.val + 1 + t.val, by omega⟩ : Fin n)) ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  · intro t₁ ht₁ t₂ ht₂ heq
    apply Fin.ext
    have := congrArg Fin.val heq
    simp only [Fin.val_mk] at this
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    let t : Fin (n - i.val - 1) := ⟨j.val - i.val - 1, by omega⟩
    refine ⟨t, Finset.mem_univ t, ?_⟩
    apply Fin.ext
    simp only [t, Fin.val_mk]
    omega
  · intro t ht
    rfl

private lemma sum_eq_diag_add_upper {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hlower : ∀ j : Fin n, j.val < i.val → f j = 0) :
    ∑ j : Fin n, f j = f i +
      ∑ t : Fin (n - i.val - 1),
        f ⟨i.val + 1 + t.val, by omega⟩ := by
  calc
    ∑ j : Fin n, f j =
        ∑ j : Fin n, ((if j = i then f i else 0) +
          if i.val < j.val then f j else 0) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hji : j = i
            · subst j
              simp
            · by_cases hlt : j.val < i.val
              · rw [hlower j hlt]
                simp [hji, hlt]
              · have hgt : i.val < j.val := by
                  have hne : i.val ≠ j.val := by
                    intro h
                    exact hji (Fin.ext h.symm)
                  omega
                simp [hji, hgt]
    _ = (∑ j : Fin n, if j = i then f i else 0) +
          ∑ j : Fin n, if i.val < j.val then f j else 0 := by
            rw [Finset.sum_add_distrib]
    _ = f i + ∑ j ∈ Finset.univ.filter
          (fun j : Fin n => i.val < j.val), f j := by
            simp
            rw [Finset.sum_filter]
    _ = f i + ∑ t : Fin (n - i.val - 1),
          f ⟨i.val + 1 + t.val, by omega⟩ := by
            rw [sum_upper_bij]

private lemma gamma_nonneg {u : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hv : P29GammaValid u n) : 0 ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hv))

private lemma gamma_mono {u : ℝ} {m n : ℕ} (hu : 0 ≤ u)
    (hmn : m ≤ n) (hv : P29GammaValid u n) :
    p29Gamma u m ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmul : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hmpos : 0 < 1 - (m : ℝ) * u := by linarith
  have hnpos : 0 < 1 - (n : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hmpos hnpos).2
  nlinarith

private lemma gamma_mul_step {u q d : ℝ} {k : ℕ} (hu : 0 ≤ u)
    (hv : P29GammaValid u (k + 1)) (hq : |q - 1| ≤ p29Gamma u k)
    (hd : |d| ≤ u) :
    |q * (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hvk : P29GammaValid u k := by
    unfold P29GammaValid at *
    have hk : (k : ℝ) ≤ (k + 1 : ℕ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hk hu]
  have hgk := gamma_nonneg hu hvk
  have hqabs : |q| ≤ 1 + p29Gamma u k := by
    calc
      |q| = |(q - 1) + 1| := by ring_nf
      _ ≤ |q - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ p29Gamma u k + 1 := by norm_num; linarith
      _ = 1 + p29Gamma u k := by ring
  calc
    |q * (1 + d) - 1| = |(q - 1) + q * d| := by congr 1 <;> ring
    _ ≤ |q - 1| + |q * d| := abs_add_le _ _
    _ ≤ p29Gamma u k + (1 + p29Gamma u k) * u := by
      rw [abs_mul]
      gcongr
    _ ≤ p29Gamma u (k + 1) := by
      unfold p29Gamma P29GammaValid at *
      rw [Nat.cast_add, Nat.cast_one] at hv ⊢
      have hkpos : 0 < 1 - (k : ℝ) * u := by nlinarith
      have hnextpos : 0 < 1 - ((k : ℝ) + 1) * u := by nlinarith
      have hnextpos' : 0 < 1 - (k : ℝ) * u - u := by nlinarith
      have hnum : 0 ≤ (k : ℝ) * u + u := by positivity
      have heq1 :
          (k : ℝ) * u / (1 - (k : ℝ) * u) +
              (1 + (k : ℝ) * u / (1 - (k : ℝ) * u)) * u =
            ((k : ℝ) * u + u) / (1 - (k : ℝ) * u) := by
        field_simp [ne_of_gt hkpos]
        ring
      have heq2 :
          ((k : ℝ) + 1) * u / (1 - ((k : ℝ) + 1) * u) =
            ((k : ℝ) * u + u) /
              (1 - (k : ℝ) * u - u) := by ring_nf
      rw [heq1, heq2]
      exact div_le_div_of_nonneg_left hnum hnextpos' (by linarith)

private lemma gamma_div_step {u q d : ℝ} {k : ℕ} (hu : 0 ≤ u)
    (hv : P29GammaValid u (k + 1)) (hq : |q - 1| ≤ p29Gamma u k)
    (hd : |d| ≤ u) :
    |q / (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hu_lt : u < 1 := by
    unfold P29GammaValid at hv
    rw [Nat.cast_add, Nat.cast_one] at hv
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
  have hdlo : -u ≤ d := (abs_le.mp hd).1
  have hden : 0 < 1 + d := by linarith
  have hvk : P29GammaValid u k := by
    unfold P29GammaValid at *
    rw [Nat.cast_add, Nat.cast_one] at hv
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
  have hgk := gamma_nonneg hu hvk
  rw [show q / (1 + d) - 1 = ((q - 1) - d) / (1 + d) by field_simp; ring,
    abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  calc
    |q - 1 - d| ≤ |q - 1| + |d| := by
      simpa [sub_eq_add_neg] using abs_add_le (q - 1) (-d)
    _ ≤ p29Gamma u k + u := by linarith
    _ ≤ p29Gamma u (k + 1) * (1 + d) := by
      have hbase : p29Gamma u k + u ≤
          p29Gamma u (k + 1) * (1 - u) := by
        unfold p29Gamma P29GammaValid at *
        rw [Nat.cast_add, Nat.cast_one] at hv ⊢
        have hkpos : 0 < 1 - (k : ℝ) * u := by
          nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
        have hnextpos : 0 < 1 - ((k : ℝ) + 1) * u := by nlinarith
        have hnextpos' : 0 < 1 - (k : ℝ) * u - u := by nlinarith
        have hnum : 0 ≤ (k : ℝ) * u + u := by positivity
        have heq1 :
            (k : ℝ) * u / (1 - (k : ℝ) * u) + u =
              ((k : ℝ) * u + u - (k : ℝ) * u * u) /
                (1 - (k : ℝ) * u) := by
          field_simp [ne_of_gt hkpos]
          ring
        have heq2 :
            ((k : ℝ) + 1) * u / (1 - ((k : ℝ) + 1) * u) * (1 - u) =
              ((k : ℝ) * u + u) * (1 - u) /
                (1 - (k : ℝ) * u - u) := by ring_nf
        rw [heq1, heq2]
        apply (div_le_div_iff₀ hkpos hnextpos').2
        nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
      have hgn := gamma_nonneg hu hv
      nlinarith

private lemma rounded_fold_backward (fp : P29FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (c : ℝ) (hv : P29GammaValid fp.u m) :
    ∃ (q : ℝ) (e : Fin m → ℝ),
      c = q * Fin.foldl m
          (fun s j => fp.fl_sub s (fp.fl_mul (a j) (x j))) c +
          ∑ j : Fin m, (a j + e j) * x j ∧
      |q - 1| ≤ p29Gamma fp.u m ∧
      ∀ j, |e j| ≤ p29Gamma fp.u m * |a j| := by
  induction m with
  | zero =>
      refine ⟨1, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
      · simp [p29Gamma]
      · simp [p29Gamma]
      · intro j
        exact Fin.elim0 j
  | succ m ih =>
      have hvm : P29GammaValid fp.u m := by
        unfold P29GammaValid at *
        rw [Nat.cast_add, Nat.cast_one] at hv
        have hm : (m : ℝ) * fp.u ≤ ((m : ℝ) + 1) * fp.u := by
          nlinarith [fp.u_nonneg]
        linarith
      let s : ℝ := Fin.foldl m
        (fun r j => fp.fl_sub r (fp.fl_mul (a j.castSucc) (x j.castSucc))) c
      obtain ⟨q, e, heq, hq, he⟩ :=
        ih (fun j => a j.castSucc) (fun j => x j.castSucc) hvm
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last m)) (x (Fin.last m))
      obtain ⟨σ, hσ, hsub⟩ := fp.model_sub s
        (fp.fl_mul (a (Fin.last m)) (x (Fin.last m)))
      let q' := q / (1 + σ)
      let elast := (q * (1 + μ) - 1) * a (Fin.last m)
      let e' : Fin (m + 1) → ℝ := Fin.lastCases elast e
      refine ⟨q', e', ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
        change c = q' * fp.fl_sub s
              (fp.fl_mul (a (Fin.last m)) (x (Fin.last m))) +
            ((∑ j : Fin m, (a j.castSucc + e' j.castSucc) * x j.castSucc) +
              (a (Fin.last m) + e' (Fin.last m)) * x (Fin.last m))
        rw [hsub, hmul]
        simp only [e', Fin.lastCases_castSucc, Fin.lastCases_last]
        have hden : 1 + σ ≠ 0 := by
          have hu_lt : fp.u < 1 := by
            unfold P29GammaValid at hv
            rw [Nat.cast_add, Nat.cast_one] at hv
            nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
          have := (abs_le.mp hσ).1
          nlinarith
        dsimp only [q', elast]
        symm
        calc
          _ = q * s + ∑ j : Fin m,
                (a j.castSucc + e j) * x j.castSucc := by
              field_simp [hden]
              ring
          _ = c := by simpa [s] using heq.symm
      · exact gamma_div_step fp.u_nonneg hv hq hσ
      · intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [e', Fin.lastCases_last, elast]
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right
            (gamma_mul_step fp.u_nonneg hv hq hμ) (abs_nonneg _)
        · simp only [e', Fin.lastCases_castSucc]
          exact le_trans (he i)
            (mul_le_mul_of_nonneg_right
              (gamma_mono fp.u_nonneg (Nat.le_succ m) hv) (abs_nonneg _))

private lemma rounded_fold_div_backward (fp : P29FPModel) (m : ℕ)
    (a x : Fin m → ℝ) (c d : ℝ) (hd0 : d ≠ 0)
    (hv : P29GammaValid fp.u (m + 1)) :
    ∃ (ed : ℝ) (e : Fin m → ℝ),
      |ed| ≤ p29Gamma fp.u (m + 1) * |d| ∧
      (∀ j, |e j| ≤ p29Gamma fp.u (m + 1) * |a j|) ∧
      (d + ed) *
          fp.fl_div
            (Fin.foldl m
              (fun s j => fp.fl_sub s (fp.fl_mul (a j) (x j))) c) d +
        ∑ j : Fin m, (a j + e j) * x j = c := by
  have hvm : P29GammaValid fp.u m := by
    unfold P29GammaValid at *
    rw [Nat.cast_add, Nat.cast_one] at hv
    nlinarith [fp.u_nonneg]
  obtain ⟨q, e, heq, hq, he⟩ := rounded_fold_backward fp m a x c hvm
  let s := Fin.foldl m
    (fun r j => fp.fl_sub r (fp.fl_mul (a j) (x j))) c
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s d hd0
  let coeff := q / (1 + δ)
  let ed := (coeff - 1) * d
  refine ⟨ed, e, ?_, ?_, ?_⟩
  · dsimp only [ed]
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (gamma_div_step fp.u_nonneg hv hq hδ) (abs_nonneg _)
  · intro j
    exact le_trans (he j)
      (mul_le_mul_of_nonneg_right
        (gamma_mono fp.u_nonneg (Nat.le_succ m) hv) (abs_nonneg _))
  · change (d + ed) * fp.fl_div s d +
        ∑ j : Fin m, (a j + e j) * x j = c
    rw [hdiv]
    have hden : 1 + δ ≠ 0 := by
      have hu_lt : fp.u < 1 := by
        unfold P29GammaValid at hv
        rw [Nat.cast_add, Nat.cast_one] at hv
        nlinarith [mul_nonneg (Nat.cast_nonneg m) fp.u_nonneg]
      have := (abs_le.mp hδ).1
      nlinarith
    dsimp only [ed, coeff]
    rw [show d + (q / (1 + δ) - 1) * d = q / (1 + δ) * d by ring]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    field_simp [hden, hd0]
    nlinarith [heq]

private lemma forward_steps_spec (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := p29ForwardSubSteps fp n L b k hk x
      (∀ j, j.val < n - k → y j = x j) ∧
      (∀ j, n - k ≤ j.val →
        y j = fp.fl_div
          (Fin.foldl j.val
            (fun s t => fp.fl_sub s
              (fp.fl_mul (L j ⟨t.val, by omega⟩) (y ⟨t.val, by omega⟩)))
            (b j)) (L j j)) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simp only [p29ForwardSubSteps.eq_1]
      constructor
      · aesop
      · intro j hj
        omega
  | succ k ih =>
      intro hk x
      rw [p29ForwardSubSteps.eq_2]
      let i : Fin n := ⟨n - k - 1, by omega⟩
      let s : ℝ := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L i ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b i)
      let x' : Fin n → ℝ := Function.update x i (fp.fl_div s (L i i))
      have hs := ih (Nat.le_of_succ_le hk) x'
      let y := p29ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      change (∀ j, j.val < n - (k + 1) → y j = x j) ∧
        (∀ j, n - (k + 1) ≤ j.val →
          y j = fp.fl_div
            (Fin.foldl j.val
              (fun r t => fp.fl_sub r
                (fp.fl_mul (L j ⟨t.val, by omega⟩) (y ⟨t.val, by omega⟩)))
              (b j)) (L j j))
      change ((∀ j, j.val < n - k → y j = x' j) ∧ _) at hs
      constructor
      · intro j hj
        rw [hs.1 j (by omega)]
        have hne : j ≠ i := by
          intro heq
          have : j.val = i.val := congrArg Fin.val heq
          simp only [i] at this
          omega
        simp [x', hne]
      · intro j hj
        by_cases hji : j.val = n - k - 1
        · have hji' : j = i := by
            apply Fin.ext
            simpa [i] using hji
          subst j
          rw [hs.1 i (by simp [i]; omega)]
          simp only [x', Function.update_self]
          apply congrArg (fun v => fp.fl_div v (L i i))
          simp only [i, s]
          congr 1
          funext acc t
          congr 2
          have hyt := hs.1 (⟨t.val, by omega⟩) (by simp [i] at t ⊢; omega)
          rw [hyt]
          have hne : (⟨t.val, by omega⟩ : Fin n) ≠ i := by
            intro heq
            have := congrArg Fin.val heq
            simp only [i] at this
            omega
          simp [x', hne]
        · apply hs.2 j
          omega

private lemma forward_sub_spec (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) (j : Fin n) :
    p29ForwardSub fp n L b j = fp.fl_div
      (Fin.foldl j.val
        (fun s t => fp.fl_sub s
          (fp.fl_mul (L j ⟨t.val, by omega⟩)
            (p29ForwardSub fp n L b ⟨t.val, by omega⟩)))
        (b j)) (L j j) := by
  exact (forward_steps_spec fp n L b n (le_refl n) (fun _ => 0)).2 j (by simp)

private lemma back_steps_spec (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := p29BackSubSteps fp n U b k hk x
      (∀ j, k ≤ j.val → y j = x j) ∧
      (∀ j, j.val < k →
        y j = fp.fl_div
          (Fin.foldl (n - j.val - 1)
            (fun s t => fp.fl_sub s
              (fp.fl_mul (U j ⟨j.val + 1 + t.val, by omega⟩)
                (y ⟨j.val + 1 + t.val, by omega⟩)))
            (b j)) (U j j)) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simp only [p29BackSubSteps.eq_1]
      constructor
      · aesop
      · intro j hj
        omega
  | succ k ih =>
      intro hk x
      rw [p29BackSubSteps.eq_2]
      let i : Fin n := ⟨k, by omega⟩
      let s : ℝ := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (U i ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b i)
      let x' : Fin n → ℝ := Function.update x i (fp.fl_div s (U i i))
      have hs := ih (Nat.le_of_succ_le hk) x'
      let y := p29BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
      change (∀ j, k + 1 ≤ j.val → y j = x j) ∧
        (∀ j, j.val < k + 1 →
          y j = fp.fl_div
            (Fin.foldl (n - j.val - 1)
              (fun r t => fp.fl_sub r
                (fp.fl_mul (U j ⟨j.val + 1 + t.val, by omega⟩)
                  (y ⟨j.val + 1 + t.val, by omega⟩)))
              (b j)) (U j j))
      change ((∀ j, k ≤ j.val → y j = x' j) ∧ _) at hs
      constructor
      · intro j hj
        rw [hs.1 j (by omega)]
        have hne : j ≠ i := by
          intro heq
          have := congrArg Fin.val heq
          simp only [i] at this
          omega
        simp [x', hne]
      · intro j hj
        by_cases hji : j.val = k
        · have hji' : j = i := by
            apply Fin.ext
            simpa [i] using hji
          subst j
          rw [hs.1 i (by simp [i])]
          simp only [x', Function.update_self]
          apply congrArg (fun v => fp.fl_div v (U i i))
          simp only [i, s]
          congr 1
          funext acc t
          congr 2
          have hyt := hs.1 (⟨k + 1 + t.val, by omega⟩)
            (by change k ≤ k + 1 + t.val; omega)
          rw [hyt]
          have hne : (⟨k + 1 + t.val, by omega⟩ : Fin n) ≠ i := by
            intro heq
            have := congrArg Fin.val heq
            simp only [i] at this
            omega
          simp [x', hne]
        · apply hs.2 j
          omega

private lemma back_sub_spec (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) (j : Fin n) :
    p29BackSub fp n U b j = fp.fl_div
      (Fin.foldl (n - j.val - 1)
        (fun s t => fp.fl_sub s
          (fp.fl_mul (U j ⟨j.val + 1 + t.val, by omega⟩)
            (p29BackSub fp n U b ⟨j.val + 1 + t.val, by omega⟩)))
        (b j)) (U j j) := by
  exact (back_steps_spec fp n U b n (le_refl n) (fun _ => 0)).2 j (by omega)

private lemma forward_backward_error (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔL : P29Matrix n n,
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
  classical
  let y := p29ForwardSub fp n L b
  have hw : ∀ i : Fin n, ∃ (ed : ℝ) (e : Fin i.val → ℝ),
      |ed| ≤ p29Gamma fp.u (i.val + 1) * |L i i| ∧
      (∀ t, |e t| ≤ p29Gamma fp.u (i.val + 1) *
        |L i ⟨t.val, by omega⟩|) ∧
      (L i i + ed) * y i +
        ∑ t : Fin i.val, (L i ⟨t.val, by omega⟩ + e t) *
          y ⟨t.val, by omega⟩ = b i := by
    intro i
    have hvi : P29GammaValid fp.u (i.val + 1) := by
      unfold P29GammaValid at *
      have hle : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast i.isLt
      nlinarith [mul_le_mul_of_nonneg_right hle fp.u_nonneg]
    obtain ⟨ed, e, hed, he, heq⟩ := rounded_fold_div_backward fp i.val
      (fun t => L i ⟨t.val, by omega⟩)
      (fun t => y ⟨t.val, by omega⟩) (b i) (L i i) (hdiag i) hvi
    refine ⟨ed, e, hed, he, ?_⟩
    rw [← heq]
    congr 2
    simpa [y] using forward_sub_spec fp n L b i
  choose ed e hed he heq using hw
  let ΔL : P29Matrix n n := fun i j =>
    if h : j.val < i.val then e i ⟨j.val, h⟩
    else if j = i then ed i else 0
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    by_cases hlt : j.val < i.val
    · simp only [ΔL, dif_pos hlt]
      exact le_trans (he i ⟨j.val, hlt⟩)
        (mul_le_mul_of_nonneg_right
          (gamma_mono fp.u_nonneg (by omega) hvalid) (abs_nonneg _))
    · by_cases hji : j = i
      · subst j
        simp only [ΔL, lt_self_iff_false, dif_neg, ite_true]
        exact le_trans (hed i)
          (mul_le_mul_of_nonneg_right
            (gamma_mono fp.u_nonneg (by omega) hvalid) (abs_nonneg _))
      · simp only [ΔL, dif_neg hlt, if_neg hji, abs_zero]
        exact mul_nonneg (gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
  · intro i
    let f : Fin n → ℝ := fun j => (L i j + ΔL i j) * y j
    rw [sum_eq_diag_add_lower f i]
    · have hdiagf : f i = (L i i + ed i) * y i := by
        simp [f, ΔL]
      rw [hdiagf]
      convert heq i using 1
      apply congrArg (fun s : ℝ => (L i i + ed i) * y i + s)
      apply Finset.sum_congr rfl
      intro t ht
      have hlt : (⟨t.val, by omega⟩ : Fin n).val < i.val := t.isLt
      simp only [f, ΔL, dif_pos hlt]
    · intro j hij
      have hnot : ¬j.val < i.val := by omega
      have hne : j ≠ i := by
        intro h
        subst j
        omega
      simp only [f, ΔL, dif_neg hnot, if_neg hne,
        hlower i j hij, zero_add, zero_mul]

private lemma back_backward_error (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔU : P29Matrix n n,
      (∀ i j, |ΔU i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * p29BackSub fp n U b j = b i := by
  classical
  let x := p29BackSub fp n U b
  have hw : ∀ i : Fin n,
      ∃ (ed : ℝ) (e : Fin (n - i.val - 1) → ℝ),
      |ed| ≤ p29Gamma fp.u (n - i.val - 1 + 1) * |U i i| ∧
      (∀ t, |e t| ≤ p29Gamma fp.u (n - i.val - 1 + 1) *
        |U i ⟨i.val + 1 + t.val, by omega⟩|) ∧
      (U i i + ed) * x i +
        ∑ t : Fin (n - i.val - 1),
          (U i ⟨i.val + 1 + t.val, by omega⟩ + e t) *
            x ⟨i.val + 1 + t.val, by omega⟩ = b i := by
    intro i
    have hvi : P29GammaValid fp.u (n - i.val - 1 + 1) := by
      unfold P29GammaValid at *
      have hle : (((n - i.val - 1 + 1 : ℕ) : ℝ)) ≤ (n : ℝ) := by
        exact_mod_cast (show n - i.val - 1 + 1 ≤ n by omega)
      nlinarith [mul_le_mul_of_nonneg_right hle fp.u_nonneg]
    obtain ⟨ed, e, hed, he, heq⟩ := rounded_fold_div_backward fp
      (n - i.val - 1)
      (fun t => U i ⟨i.val + 1 + t.val, by omega⟩)
      (fun t => x ⟨i.val + 1 + t.val, by omega⟩)
      (b i) (U i i) (hdiag i) hvi
    refine ⟨ed, e, hed, he, ?_⟩
    rw [← heq]
    congr 2
    simpa [x] using back_sub_spec fp n U b i
  choose ed e hed he heq using hw
  let ΔU : P29Matrix n n := fun i j =>
    if h : i.val < j.val then
      e i ⟨j.val - i.val - 1, by omega⟩
    else if j = i then ed i else 0
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    by_cases hlt : i.val < j.val
    · simp only [ΔU, dif_pos hlt]
      have hle : n - i.val - 1 + 1 ≤ n := by omega
      let t : Fin (n - i.val - 1) := ⟨j.val - i.val - 1, by omega⟩
      have hidx : (⟨i.val + 1 + t.val, by omega⟩ : Fin n) = j := by
        apply Fin.ext
        simp only [t, Fin.val_mk]
        omega
      have hlocal := he i t
      rw [hidx] at hlocal
      exact le_trans hlocal
        (mul_le_mul_of_nonneg_right
          (gamma_mono fp.u_nonneg hle hvalid) (abs_nonneg (U i j)))
    · by_cases hji : j = i
      · subst j
        simp only [ΔU, lt_self_iff_false, dif_neg, ite_true]
        have hle : n - i.val - 1 + 1 ≤ n := by omega
        exact le_trans (hed i)
          (mul_le_mul_of_nonneg_right
            (gamma_mono fp.u_nonneg hle hvalid) (abs_nonneg _))
      · simp only [ΔU, dif_neg hlt, if_neg hji, abs_zero]
        exact mul_nonneg (gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
  · intro i
    let f : Fin n → ℝ := fun j => (U i j + ΔU i j) * x j
    rw [sum_eq_diag_add_upper f i]
    · have hdiagf : f i = (U i i + ed i) * x i := by
        simp [f, ΔU]
      rw [hdiagf]
      convert heq i using 1
      apply congrArg (fun s : ℝ => (U i i + ed i) * x i + s)
      apply Finset.sum_congr rfl
      intro t ht
      have hlt : i.val <
          (⟨i.val + 1 + t.val, by omega⟩ : Fin n).val := by
        change i.val < i.val + 1 + t.val
        omega
      simp only [f, ΔU, dif_pos hlt]
      congr 3
      apply Fin.ext
      simp
      omega
    · intro j hji
      have hnot : ¬i.val < j.val := by omega
      have hne : j ≠ i := by
        intro h
        subst j
        omega
      simp only [f, ΔU, dif_neg hnot, if_neg hne,
        hupper i j hji, zero_add, zero_mul]

private lemma entryNorm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  positivity

private lemma entry_abs_le_norm {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    |A i j| ≤ ∑ k : Fin n, |A i k| := by
      exact Finset.single_le_sum (fun k _ => abs_nonneg (A i k))
        (Finset.mem_univ j)
    _ ≤ ∑ r : Fin m, ∑ k : Fin n, |A r k| := by
      exact Finset.single_le_sum
        (fun r _ => Finset.sum_nonneg (fun k _ => abs_nonneg (A r k)))
        (Finset.mem_univ i)

private lemma entryNorm_add {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A + B) ≤ p29EntryNorm A + p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |(A + B) i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |A i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |B i j| := by
      simp_rw [Finset.sum_add_distrib]

private lemma entryNorm_add_three {m n : ℕ} (A B C : P29Matrix m n) :
    p29EntryNorm (A + B + C) ≤
      (p29EntryNorm A + p29EntryNorm B) + p29EntryNorm C := by
  exact le_trans (entryNorm_add (A + B) C)
    (add_le_add (entryNorm_add A B) (le_refl _))

private lemma entryNorm_sub {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A - B) ≤ p29EntryNorm A + p29EntryNorm B := by
  simpa [sub_eq_add_neg, p29EntryNorm] using entryNorm_add A (-B)

private lemma entryNorm_of_bound {m n : ℕ} (c : ℝ)
    (A E : P29Matrix m n) (h : ∀ i j, |E i j| ≤ c * |A i j|) :
    p29EntryNorm E ≤ c * p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |E i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |A i j| := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h i j))
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |A i j| := by
      simp_rw [Finset.mul_sum]

private lemma entryNorm_matmul {m n p : ℕ}
    (A : P29Matrix m n) (B : P29Matrix n p) :
    p29EntryNorm (p29MatMul A B) ≤
      (m : ℝ) * (n : ℝ) * (p : ℝ) *
        p29EntryNorm A * p29EntryNorm B := by
  unfold p29EntryNorm p29MatMul
  calc
    ∑ i : Fin m, ∑ j : Fin p, |∑ k : Fin n, A i k * B k j| ≤
        ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n,
          (p29EntryNorm A * p29EntryNorm B) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      calc
        |∑ k : Fin n, A i k * B k j| ≤
            ∑ k : Fin n, |A i k * B k j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k : Fin n, p29EntryNorm A * p29EntryNorm B := by
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          exact mul_le_mul (entry_abs_le_norm A i k)
            (entry_abs_le_norm B k j) (abs_nonneg _) (entryNorm_nonneg A)
    _ = (m : ℝ) * (n : ℝ) * (p : ℝ) *
          p29EntryNorm A * p29EntryNorm B := by
      simp
      ring

private lemma entryNorm_square_triple {n : ℕ}
    (A B C : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul A B) *
          p29EntryNorm C := by
      simpa [pow_succ] using entryNorm_matmul (p29MatMul A B) C
    _ ≤ (n : ℝ) ^ 3 *
          ((n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B) *
          p29EntryNorm C := by
      apply mul_le_mul_of_nonneg_right _ (entryNorm_nonneg C)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [pow_succ] using entryNorm_matmul A B
    _ = (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B *
          p29EntryNorm C := by ring

private lemma matmul_vec_assoc {n : ℕ} (P Q : P29Matrix n n)
    (v w : Fin n → ℝ)
    (hQ : ∀ i, ∑ j : Fin n, Q i j * v j = w i) :
    ∀ i, ∑ j : Fin n, p29MatMul P Q i j * v j =
      ∑ k : Fin n, P i k * w k := by
  intro i
  simp only [p29MatMul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (∑ x : Fin n, P i k * Q k x * v x) =
      P i k * ∑ x : Fin n, Q k x * v x by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring]
  rw [hQ k]

private lemma combined_backward_expand {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  ext i j
  simp only [p29CombinedBackwardError, p29PerturbedLDLT, p29LDLT,
    p29MatMul, Matrix.add_apply, Matrix.sub_apply]
  simp only [mul_add, add_mul, Finset.sum_add_distrib]
  ring

set_option maxHeartbeats 1000000 in
private lemma combined_backward_norm_bound (fp : P29FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P29Matrix n n)
    (hvalid : P29GammaValid fp.u n) (heta : 0 ≤ eta)
    (hL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let g := p29Gamma fp.u n
  let N := (n : ℝ) ^ 6
  have hg : 0 ≤ g := gamma_nonneg fp.u_nonneg hvalid
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hΔL : p29EntryNorm ΔL ≤ g * p29EntryNorm L := by
    exact entryNorm_of_bound g L ΔL hL
  have hΔU : p29EntryNorm ΔU ≤
      g * p29EntryNorm (p29Transpose L) := by
    exact entryNorm_of_bound g (p29Transpose L) ΔU hU
  have hDadd : p29EntryNorm (D + ΔD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤ p29EntryNorm D + p29EntryNorm ΔD :=
        entryNorm_add D ΔD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D := by linarith
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hTadd : p29EntryNorm (p29Transpose L + ΔU) ≤
      (1 + g) * p29EntryNorm (p29Transpose L) := by
    calc
      p29EntryNorm (p29Transpose L + ΔU) ≤
          p29EntryNorm (p29Transpose L) + p29EntryNorm ΔU :=
        entryNorm_add (p29Transpose L) ΔU
      _ ≤ p29EntryNorm (p29Transpose L) +
          g * p29EntryNorm (p29Transpose L) := by linarith
      _ = (1 + g) * p29EntryNorm (p29Transpose L) := by ring
  have ht1 : p29EntryNorm
      (p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)) ≤
      N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm (p29MatMul (p29MatMul ΔL (D + ΔD))
          (p29Transpose L + ΔU)) ≤
          N * p29EntryNorm ΔL * p29EntryNorm (D + ΔD) *
            p29EntryNorm (p29Transpose L + ΔU) := by
        simpa [N] using entryNorm_square_triple ΔL (D + ΔD)
          (p29Transpose L + ΔU)
      _ ≤ N * (g * p29EntryNorm L) * p29EntryNorm (D + ΔD) *
            p29EntryNorm (p29Transpose L + ΔU) := by
        apply mul_le_mul_of_nonneg_right _
          (entryNorm_nonneg (p29Transpose L + ΔU))
        apply mul_le_mul_of_nonneg_right _ (entryNorm_nonneg (D + ΔD))
        exact mul_le_mul_of_nonneg_left hΔL hN
      _ ≤ N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
            p29EntryNorm (p29Transpose L + ΔU) := by
        apply mul_le_mul_of_nonneg_right _
          (entryNorm_nonneg (p29Transpose L + ΔU))
        exact mul_le_mul_of_nonneg_left hDadd
          (mul_nonneg hN (mul_nonneg hg (entryNorm_nonneg L)))
      _ ≤ N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
            ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        exact mul_le_mul_of_nonneg_left hTadd
          (mul_nonneg
            (mul_nonneg hN (mul_nonneg hg (entryNorm_nonneg L)))
            (mul_nonneg (by linarith) (entryNorm_nonneg D)))
  have ht2 : p29EntryNorm
      (p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)) ≤
      N * p29EntryNorm L * (eta * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm (p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)) ≤
          N * p29EntryNorm L * p29EntryNorm ΔD *
            p29EntryNorm (p29Transpose L + ΔU) := by
        simpa [N] using entryNorm_square_triple L ΔD (p29Transpose L + ΔU)
      _ ≤ N * p29EntryNorm L * (eta * p29EntryNorm D) *
            p29EntryNorm (p29Transpose L + ΔU) := by
        apply mul_le_mul_of_nonneg_right _
          (entryNorm_nonneg (p29Transpose L + ΔU))
        exact mul_le_mul_of_nonneg_left hD
          (mul_nonneg hN (entryNorm_nonneg L))
      _ ≤ N * p29EntryNorm L * (eta * p29EntryNorm D) *
            ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        exact mul_le_mul_of_nonneg_left hTadd
          (mul_nonneg (mul_nonneg hN (entryNorm_nonneg L))
            (mul_nonneg heta (entryNorm_nonneg D)))
  have ht3 : p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) ≤
      N * p29EntryNorm L * p29EntryNorm D *
        (g * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) ≤
          N * p29EntryNorm L * p29EntryNorm D * p29EntryNorm ΔU := by
        simpa [N] using entryNorm_square_triple L D ΔU
      _ ≤ N * p29EntryNorm L * p29EntryNorm D *
            (g * p29EntryNorm (p29Transpose L)) := by
        exact mul_le_mul_of_nonneg_left hΔU
          (mul_nonneg (mul_nonneg hN (entryNorm_nonneg L))
            (entryNorm_nonneg D))
  rw [combined_backward_expand]
  calc
    p29EntryNorm
        (p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
          p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
          p29MatMul (p29MatMul L D) ΔU) ≤
        (p29EntryNorm (p29MatMul (p29MatMul ΔL (D + ΔD))
            (p29Transpose L + ΔU)) +
          p29EntryNorm (p29MatMul (p29MatMul L ΔD)
            (p29Transpose L + ΔU))) +
          p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) := by
      exact entryNorm_add_three _ _ _
    _ ≤
        (N * (g * p29EntryNorm L) * ((1 + eta) * p29EntryNorm D) *
            ((1 + g) * p29EntryNorm (p29Transpose L)) +
          N * p29EntryNorm L * (eta * p29EntryNorm D) *
            ((1 + g) * p29EntryNorm (p29Transpose L))) +
          N * p29EntryNorm L * p29EntryNorm D *
            (g * p29EntryNorm (p29Transpose L)) := by
      exact add_le_add (add_le_add ht1 ht2) ht3
    _ = p29SolveBackwardFactor fp n eta L D := by
      simp only [p29SolveBackwardFactor, N, g]
      ring

/-- P29-T2: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p29_t2_ldlt_solve_backward_stability
    (fp : P29FPModel) (n : ℕ) (A L D E0 : P29Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p29LDLT L D = A + E0)
    (hE0 : p29EntryNorm E0 ≤ factorEta * p29EntryNorm A)
    (hDsolve : P29BlockSolveStable n D
      (p29ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P29Matrix n n),
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      p29EntryNorm ΔD ≤ eta * p29EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p29Gamma fp.u n * |p29Transpose L i j|) ∧
      F = p29TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j = b i) ∧
      p29EntryNorm F ≤
        p29TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P29-T2-H001
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    forward_backward_error fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  have htdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have htupper : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hback⟩ :=
    back_backward_error fp n (p29Transpose L) z htdiag htupper hvalid
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · let x := p29BackSub fp n (p29Transpose L) z
    let y := p29ForwardSub fp n L b
    have hpert : ∀ i, ∑ j : Fin n,
        p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j = b i := by
      intro i
      calc
        ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j =
            ∑ k : Fin n, p29MatMul (L + ΔL) (D + ΔD) i k * z k := by
          exact matmul_vec_assoc
            (p29MatMul (L + ΔL) (D + ΔD))
            (p29Transpose L + ΔU) x z hback i
        _ = ∑ k : Fin n, (L i k + ΔL i k) * y k := by
          simpa only [Matrix.add_apply] using
            matmul_vec_assoc (L + ΔL) (D + ΔD) z y hblock i
        _ = b i := hforward i
    have hAF : ∀ i j,
        A i j + F i j = p29PerturbedLDLT L D ΔL ΔD ΔU i j := by
      intro i j
      have hf := congrArg (fun M : P29Matrix n n => M i j) hfactor
      simp only [Matrix.add_apply] at hf
      simp only [F, p29TotalBackwardError, p29CombinedBackwardError,
        Matrix.add_apply, Matrix.sub_apply]
      rw [hf]
      ring
    intro i
    calc
      ∑ j : Fin n, (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j =
          ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hAF i j]
      _ = b i := hpert i
  · have hc := combined_backward_norm_bound fp n eta L D ΔL ΔD ΔU
        hvalid heta hΔL hΔD hΔU
    calc
      p29EntryNorm F ≤ p29EntryNorm E0 +
          p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) := by
        simpa only [F, p29TotalBackwardError] using
          entryNorm_add E0 (p29CombinedBackwardError L D ΔL ΔD ΔU)
      _ ≤ factorEta * p29EntryNorm A +
          p29SolveBackwardFactor fp n eta L D := by linarith
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
