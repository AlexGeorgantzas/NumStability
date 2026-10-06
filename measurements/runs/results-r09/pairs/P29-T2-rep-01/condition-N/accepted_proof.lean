import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29_gamma_nonneg_of_valid (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hvalid : P29GammaValid u n) :
    0 ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr hvalid))

private lemma p29_gamma_mono (u : ℝ) {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hvalid : P29GammaValid u n) :
    p29Gamma u m ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  have hmn' : (m : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hm : (m : ℝ) * u < 1 := lt_of_le_of_lt hmn' hvalid
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

private lemma p29_one_add_ne_zero (u d : ℝ) (hu : 0 ≤ u)
    (hu1 : u < 1) (hd : |d| ≤ u) : 1 + d ≠ 0 := by
  have hneg : -u ≤ d := (abs_le.mp hd).1
  have : -1 < d := by linarith
  linarith

private lemma p29_gamma_mul_step (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hv : (m + 1 : ℝ) * u < 1)
    {e d : ℝ} (he : |e| ≤ p29Gamma u m) (hd : |d| ≤ u) :
    |(1 + e) * (1 + d) - 1| ≤ p29Gamma u (m + 1) := by
  have hm : (m : ℝ) * u < 1 := by
    norm_num at hv ⊢
    nlinarith
  have hg : 0 ≤ p29Gamma u m := by
    apply p29_gamma_nonneg_of_valid u m hu
    exact hm
  calc
    |(1 + e) * (1 + d) - 1|
        = |e + d + e * d| := by ring_nf
    _ ≤ |e| + |d| + |e| * |d| := by
      calc
        |e + d + e * d| ≤ |e + d| + |e * d| := abs_add_le _ _
        _ ≤ (|e| + |d|) + |e| * |d| := by
          rw [abs_mul]
          gcongr
          exact abs_add_le _ _
    _ ≤ p29Gamma u m + u + p29Gamma u m * u := by gcongr
    _ ≤ p29Gamma u (m + 1) := by
      unfold p29Gamma
      rw [Nat.cast_add, Nat.cast_one]
      have hmden : 0 < 1 - (m : ℝ) * u := by linarith
      have hsden : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
      have heq :
          (m : ℝ) * u / (1 - (m : ℝ) * u) + u +
              (m : ℝ) * u / (1 - (m : ℝ) * u) * u =
            (((m : ℝ) + 1) * u) / (1 - (m : ℝ) * u) := by
        field_simp
        ring
      rw [heq]
      exact div_le_div_of_nonneg_left (by positivity) hsden (by nlinarith)

private lemma p29_gamma_div_step (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hv : (m + 1 : ℝ) * u < 1)
    {e d : ℝ} (he : |e| ≤ p29Gamma u m) (hd : |d| ≤ u) :
    |(1 + e) / (1 + d) - 1| ≤ p29Gamma u (m + 1) := by
  have hu1 : u < 1 := by
    have hm1 : (1 : ℝ) ≤ (m + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    nlinarith
  have hdpos : 0 < 1 + d := by
    have hneg : -u ≤ d := (abs_le.mp hd).1
    linarith
  have hdne : 1 + d ≠ 0 := ne_of_gt hdpos
  have hm : (m : ℝ) * u < 1 := by
    norm_num at hv ⊢
    nlinarith
  have hg : 0 ≤ p29Gamma u m :=
    p29_gamma_nonneg_of_valid u m hu hm
  rw [div_sub_one hdne, abs_div, abs_of_pos hdpos]
  calc
    |1 + e - (1 + d)| / (1 + d) = |e - d| / (1 + d) := by ring_nf
    _ ≤ (p29Gamma u m + u) / (1 - u) := by
      exact div_le_div₀ (by positivity)
        (le_trans (abs_sub _ _) (add_le_add he hd)) (by linarith)
        (by have := (abs_le.mp hd).1; linarith)
    _ ≤ p29Gamma u (m + 1) := by
      unfold p29Gamma
      rw [Nat.cast_add, Nat.cast_one]
      have hmden : 0 < 1 - (m : ℝ) * u := by linarith
      have huden : 0 < 1 - u := by linarith
      have hsden : 0 < 1 - ((m : ℝ) + 1) * u := by linarith
      have hnum : 0 ≤ ((m : ℝ) + 1) * u := by positivity
      have hfirst :
          ((m : ℝ) * u / (1 - (m : ℝ) * u) + u) / (1 - u) ≤
            ((((m : ℝ) + 1) * u) / (1 - (m : ℝ) * u)) / (1 - u) := by
        apply div_le_div_of_nonneg_right
        · have hgu : 0 ≤ (m : ℝ) * u / (1 - (m : ℝ) * u) * u := by
            positivity
          have heq :
              (m : ℝ) * u / (1 - (m : ℝ) * u) + u +
                  (m : ℝ) * u / (1 - (m : ℝ) * u) * u =
                (((m : ℝ) + 1) * u) / (1 - (m : ℝ) * u) := by
            field_simp
            ring
          linarith
        · exact le_of_lt huden
      calc
        ((m : ℝ) * u / (1 - (m : ℝ) * u) + u) / (1 - u)
            ≤ ((((m : ℝ) + 1) * u) / (1 - (m : ℝ) * u)) / (1 - u) := hfirst
        _ = ((m : ℝ) + 1) * u /
              ((1 - (m : ℝ) * u) * (1 - u)) := by rw [div_div]
        _ ≤ ((m : ℝ) + 1) * u / (1 - ((m : ℝ) + 1) * u) := by
          apply div_le_div_of_nonneg_left hnum hsden
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hu) hu]

private lemma p29_rounded_fold_backward
    (fp : P29FPModel) (m : ℕ) (a x : Fin m → ℝ) (b : ℝ)
    (hvalid : P29GammaValid fp.u m) :
    ∃ (q : ℝ) (c : Fin m → ℝ),
      q ≠ 0 ∧
      |1 / q - 1| ≤ p29Gamma fp.u m ∧
      b =
        Fin.foldl m
            (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) b / q +
          ∑ i : Fin m, (a i + c i) * x i ∧
      ∀ i, |c i| ≤ p29Gamma fp.u m * |a i| := by
  induction m with
  | zero =>
      refine ⟨1, (fun i => Fin.elim0 i), one_ne_zero, ?_, ?_, ?_⟩
      · simp [p29Gamma]
      · simp
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      have hmvalid : P29GammaValid fp.u m := by
        unfold P29GammaValid at hvalid ⊢
        have hu := fp.u_nonneg
        norm_num at hvalid ⊢
        nlinarith
      obtain ⟨q, c, hq, hqerr, hexact, hc⟩ :=
        ih (fun i => a i.castSucc) (fun i => x i.castSucc) hmvalid
      let s : ℝ :=
        Fin.foldl m
          (fun acc i =>
            fp.fl_sub acc (fp.fl_mul (a i.castSucc) (x i.castSucc))) b
      obtain ⟨mu, hmu, hmul⟩ := fp.model_mul (a (Fin.last m)) (x (Fin.last m))
      obtain ⟨sigma, hsigma, hsub⟩ :=
        fp.model_sub s (fp.fl_mul (a (Fin.last m)) (x (Fin.last m)))
      have hu1 : fp.u < 1 := by
        unfold P29GammaValid at hvalid
        have hone : (1 : ℝ) ≤ (m + 1 : ℕ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
        nlinarith [fp.u_nonneg]
      have hsne : 1 + sigma ≠ 0 :=
        p29_one_add_ne_zero fp.u sigma fp.u_nonneg hu1 hsigma
      let e : ℝ := 1 / q - 1
      have he : |e| ≤ p29Gamma fp.u m := hqerr
      have hcastvalid : ((m + 1 : ℕ) : ℝ) * fp.u < 1 := hvalid
      have hnewCoeff :
          |(1 + mu) / q - 1| ≤ p29Gamma fp.u (m + 1) := by
        have hcastvalid' : ((m : ℝ) + 1) * fp.u < 1 := by
          simpa [Nat.cast_add, Nat.cast_one] using hcastvalid
        have hstep := p29_gamma_mul_step fp.u m fp.u_nonneg hcastvalid' he hmu
        have hid : (1 + mu) / q = (1 + e) * (1 + mu) := by
          dsimp [e]
          field_simp
          ring
        rwa [hid]
      have hnewQ :
          |1 / (q * (1 + sigma)) - 1| ≤ p29Gamma fp.u (m + 1) := by
        have hcastvalid' : ((m : ℝ) + 1) * fp.u < 1 := by
          simpa [Nat.cast_add, Nat.cast_one] using hcastvalid
        have hstep := p29_gamma_div_step fp.u m fp.u_nonneg hcastvalid' he hsigma
        have hid : 1 / (q * (1 + sigma)) = (1 + e) / (1 + sigma) := by
          dsimp [e]
          field_simp
          ring
        rwa [hid]
      let c' : Fin (m + 1) → ℝ :=
        Fin.lastCases
          (a (Fin.last m) * ((1 + mu) / q - 1))
          (fun i => c i)
      refine ⟨q * (1 + sigma), c', mul_ne_zero hq hsne, hnewQ, ?_, ?_⟩
      · rw [Fin.foldl_succ_last]
        change b =
          fp.fl_sub s (fp.fl_mul (a (Fin.last m)) (x (Fin.last m))) /
                (q * (1 + sigma)) +
            ∑ i : Fin (m + 1), (a i + c' i) * x i
        rw [Fin.sum_univ_castSucc]
        simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last]
        change b = s / q + ∑ i : Fin m, (a i.castSucc + c i) * x i.castSucc at hexact
        rw [hsub, hmul]
        rw [hexact]
        field_simp
        ring
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [c', Fin.lastCases_last]
          rw [abs_mul]
          calc
            |a (Fin.last m)| * |(1 + mu) / q - 1| =
                |(1 + mu) / q - 1| * |a (Fin.last m)| := mul_comm _ _
            _ ≤ p29Gamma fp.u (m + 1) * |a (Fin.last m)| :=
              mul_le_mul_of_nonneg_right hnewCoeff (abs_nonneg _)
        · simp only [c', Fin.lastCases_castSucc]
          exact le_trans (hc j)
            (mul_le_mul_of_nonneg_right
              (p29_gamma_mono fp.u fp.u_nonneg (Nat.le_succ m) hvalid)
              (abs_nonneg _))

private lemma p29_rounded_row_backward
    (fp : P29FPModel) (n m : ℕ) (hmn : m + 1 ≤ n)
    (a x : Fin m → ℝ) (b d : ℝ) (hd : d ≠ 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ (c : Fin m → ℝ) (ed : ℝ),
      (∀ i, |c i| ≤ p29Gamma fp.u n * |a i|) ∧
      |ed| ≤ p29Gamma fp.u n * |d| ∧
      b =
        (∑ i : Fin m, (a i + c i) * x i) +
          (d + ed) *
            fp.fl_div
              (Fin.foldl m
                (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) b) d := by
  have hmle : m ≤ n := le_trans (Nat.le_succ m) hmn
  have hmvalid : P29GammaValid fp.u m := by
    unfold P29GammaValid at hvalid ⊢
    have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmle
    nlinarith [fp.u_nonneg]
  obtain ⟨q, c, hq, hqerr, hexact, hc⟩ :=
    p29_rounded_fold_backward fp m a x b hmvalid
  let s : ℝ :=
    Fin.foldl m
      (fun acc i => fp.fl_sub acc (fp.fl_mul (a i) (x i))) b
  obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div s d hd
  have hmnvalid : P29GammaValid fp.u (m + 1) := by
    unfold P29GammaValid at hvalid ⊢
    have hcast : ((m + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hmn
    nlinarith [fp.u_nonneg]
  have hu1 : fp.u < 1 := by
    unfold P29GammaValid at hmnvalid
    have hone : (1 : ℝ) ≤ (m + 1 : ℕ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    nlinarith [fp.u_nonneg]
  have hdone : 1 + delta ≠ 0 :=
    p29_one_add_ne_zero fp.u delta fp.u_nonneg hu1 hdelta
  let e : ℝ := 1 / q - 1
  have he : |e| ≤ p29Gamma fp.u m := hqerr
  have hcastvalid : ((m : ℝ) + 1) * fp.u < 1 := by
    simpa [P29GammaValid, Nat.cast_add, Nat.cast_one] using hmnvalid
  have hdiagstep :
      |1 / (q * (1 + delta)) - 1| ≤ p29Gamma fp.u (m + 1) := by
    have hstep := p29_gamma_div_step fp.u m fp.u_nonneg hcastvalid he hdelta
    have hid : 1 / (q * (1 + delta)) = (1 + e) / (1 + delta) := by
      dsimp [e]
      field_simp
      ring
    rwa [hid]
  let ed : ℝ := d * (1 / (q * (1 + delta)) - 1)
  refine ⟨c, ed, ?_, ?_, ?_⟩
  · intro i
    exact le_trans (hc i)
      (mul_le_mul_of_nonneg_right
        (p29_gamma_mono fp.u fp.u_nonneg hmle hvalid) (abs_nonneg _))
  · dsimp [ed]
    rw [abs_mul]
    calc
      |d| * |1 / (q * (1 + delta)) - 1| =
          |1 / (q * (1 + delta)) - 1| * |d| := mul_comm _ _
      _ ≤ p29Gamma fp.u (m + 1) * |d| :=
        mul_le_mul_of_nonneg_right hdiagstep (abs_nonneg _)
      _ ≤ p29Gamma fp.u n * |d| :=
        mul_le_mul_of_nonneg_right
          (p29_gamma_mono fp.u fp.u_nonneg hmn hvalid) (abs_nonneg _)
  · change b = (∑ i : Fin m, (a i + c i) * x i) + (d + ed) * fp.fl_div s d
    change b = s / q + ∑ i : Fin m, (a i + c i) * x i at hexact
    rw [hdiv]
    rw [hexact]
    dsimp [ed]
    field_simp
    ring

private lemma p29_forward_steps_preserve
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k → p29ForwardSubSteps fp n L b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      simp [p29ForwardSubSteps]
  | succ k ih =>
      intro hk x i hi
      rw [p29ForwardSubSteps]
      have hi' : i.val < n - k := by omega
      rw [ih (Nat.le_of_succ_le hk) _ i hi']
      rw [Function.update_apply, if_neg]
      intro heq
      have hval : i.val = n - k - 1 := congrArg Fin.val heq
      omega

private lemma p29_forward_steps_spec
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n - k ≤ i.val →
      let y := p29ForwardSubSteps fp n L b k hk x
      y i =
        fp.fl_div
          (Fin.foldl i.val
            (fun acc t =>
              fp.fl_sub acc
                (fp.fl_mul (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
                  (y ⟨t.val, lt_trans t.isLt i.isLt⟩)))
            (b i))
          (L i i) := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      rw [p29ForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s : ℝ := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      change
        let y := p29ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
        y i =
          fp.fl_div
            (Fin.foldl i.val
              (fun acc t => fp.fl_sub acc
                (fp.fl_mul (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
                  (y ⟨t.val, lt_trans t.isLt i.isLt⟩)))
              (b i)) (L i i)
      dsimp only
      by_cases hieq : i = ik
      · rw [hieq]
        have hiklt : ik.val < n - k := by dsimp [ik]; omega
        rw [p29_forward_steps_preserve fp n L b k (Nat.le_of_succ_le hk) x' ik hiklt]
        have hx' : x' ik = fp.fl_div s (L ik ik) := by
          dsimp [x']
          rw [Function.update_apply, if_pos rfl]
        rw [hx']
        congr 1
        dsimp [s, ik]
        congr 1
        funext acc t
        congr 3
        have htlt : t.val < n - k := by omega
        rw [p29_forward_steps_preserve fp n L b k (Nat.le_of_succ_le hk) x'
          ⟨t.val, by omega⟩ htlt]
        dsimp [x']
        rw [Function.update_apply, if_neg]
        intro heq
        have hval : t.val = n - k - 1 := congrArg Fin.val heq
        omega
      · have higt : n - k ≤ i.val := by
          have hneval : i.val ≠ n - k - 1 := by
            intro heq
            apply hieq
            apply Fin.ext
            dsimp [ik]
            exact heq
          omega
        exact ih (Nat.le_of_succ_le hk) x' i higt

private lemma p29_forward_sub_spec
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ)
    (i : Fin n) :
    let y := p29ForwardSub fp n L b
    y i =
      fp.fl_div
        (Fin.foldl i.val
          (fun acc t => fp.fl_sub acc
            (fp.fl_mul (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
              (y ⟨t.val, lt_trans t.isLt i.isLt⟩)))
          (b i)) (L i i) := by
  exact p29_forward_steps_spec fp n L b n (le_refl n)
    (fun _ => 0) i (by omega)

private lemma p29_back_steps_preserve
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      k ≤ i.val → p29BackSubSteps fp n U b k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      simp [p29BackSubSteps]
  | succ k ih =>
      intro hk x i hi
      rw [p29BackSubSteps]
      have hi' : k ≤ i.val := by omega
      rw [ih (Nat.le_of_succ_le hk) _ i hi']
      rw [Function.update_apply, if_neg]
      intro heq
      have hval : i.val = k := congrArg Fin.val heq
      omega

private lemma p29_back_steps_spec
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < k →
      let y := p29BackSubSteps fp n U b k hk x
      y i =
        fp.fl_div
          (Fin.foldl (n - i.val - 1)
            (fun acc t =>
              fp.fl_sub acc
                (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                  (y ⟨i.val + 1 + t.val, by omega⟩)))
            (b i))
          (U i i) := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      rw [p29BackSubSteps]
      let ik : Fin n := ⟨k, by omega⟩
      let count := n - k - 1
      let s : ℝ := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      change
        let y := p29BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x'
        y i =
          fp.fl_div
            (Fin.foldl (n - i.val - 1)
              (fun acc t => fp.fl_sub acc
                (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                  (y ⟨i.val + 1 + t.val, by omega⟩)))
              (b i)) (U i i)
      dsimp only
      by_cases hieq : i = ik
      · rw [hieq]
        have hik : k ≤ ik.val := by simp [ik]
        rw [p29_back_steps_preserve fp n U b k (Nat.le_of_succ_le hk) x' ik hik]
        have hx' : x' ik = fp.fl_div s (U ik ik) := by
          dsimp [x']
          rw [Function.update_apply, if_pos rfl]
        rw [hx']
        congr 1
        dsimp [s, count, ik]
        congr 1
        funext acc t
        congr 3
        have ht : k ≤ k + 1 + t.val := by omega
        rw [p29_back_steps_preserve fp n U b k (Nat.le_of_succ_le hk) x'
          ⟨k + 1 + t.val, by omega⟩ ht]
        dsimp [x']
        rw [Function.update_apply, if_neg]
        intro heq
        have hval : k + 1 + t.val = k := congrArg Fin.val heq
        omega
      · have hilt : i.val < k := by
          have hneval : i.val ≠ k := by
            intro heq
            apply hieq
            apply Fin.ext
            dsimp [ik]
            exact heq
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hilt

private lemma p29_back_sub_spec
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ)
    (i : Fin n) :
    let y := p29BackSub fp n U b
    y i =
      fp.fl_div
        (Fin.foldl (n - i.val - 1)
          (fun acc t => fp.fl_sub acc
            (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
              (y ⟨i.val + 1 + t.val, by omega⟩)))
          (b i)) (U i i) := by
  exact p29_back_steps_spec fp n U b n (le_refl n)
    (fun _ => 0) i i.isLt

private lemma p29_fin_sum_lower_diag {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hz : ∀ j : Fin n, i.val < j.val → f j = 0) :
    ∑ j : Fin n, f j =
      (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) + f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert hz
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · intro hz
        rw [Fin.sum_univ_castSucc]
        rfl
      · intro hz
        rw [Fin.sum_univ_castSucc]
        have hlast : f (Fin.last n) = 0 := hz (Fin.last n) (by simp)
        rw [hlast, add_zero]
        have hrec := ih (fun j : Fin n => f j.castSucc) i'
          (fun j hj => hz j.castSucc hj)
        rw [hrec]
        congr 1

private lemma p29_fin_sum_diag_upper {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hz : ∀ j : Fin n, j.val < i.val → f j = 0) :
    ∑ j : Fin n, f j =
      f i + ∑ t : Fin (n - i.val - 1),
        f ⟨i.val + 1 + t.val, by omega⟩ := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      revert hz
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · intro hz
        rw [Fin.sum_univ_castSucc]
        have hzero : ∑ j : Fin n, f j.castSucc = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          exact hz j.castSucc (by simp)
        rw [hzero]
        have hsumzero :
            ∑ t : Fin (n + 1 - (Fin.last n).val - 1),
              f ⟨(Fin.last n).val + 1 + t.val, by omega⟩ = 0 := by
          apply Finset.sum_eq_zero
          intro t ht
          have himpossible := t.isLt
          simp [Fin.val_last] at himpossible
        rw [hsumzero]
        ring
      · intro hz
        rw [Fin.sum_univ_castSucc]
        have hrec := ih (fun j : Fin n => f j.castSucc) i'
          (fun j hj => hz j.castSucc hj)
        rw [hrec]
        have hcount : n - i'.val = (n - i'.val - 1) + 1 := by omega
        have hsum :
            (∑ t : Fin (n - i'.val),
              f ⟨i'.val + 1 + t.val, by omega⟩) =
              (∑ t : Fin (n - i'.val - 1),
                f ⟨i'.val + 1 + t.val, by omega⟩) + f (Fin.last n) := by
          calc
            (∑ t : Fin (n - i'.val),
                f ⟨i'.val + 1 + t.val, by omega⟩) =
              ∑ t : Fin ((n - i'.val - 1) + 1),
                f ⟨i'.val + 1 + t.val, by omega⟩ := by
                  apply Fintype.sum_equiv (Fin.castOrderIso hcount).toEquiv
                  intro t
                  congr 1
            _ = _ := by
              rw [Fin.sum_univ_castSucc]
              congr 1
              apply congrArg f
              apply Fin.ext
              simp [Fin.val_last]
              omega
        have htargetCount :
            n + 1 - i'.castSucc.val - 1 = n - i'.val := by
          simp [Fin.val_castSucc]
          omega
        have htarget :
            (∑ t : Fin (n + 1 - i'.castSucc.val - 1),
              f ⟨i'.castSucc.val + 1 + t.val, by omega⟩) =
              (∑ t : Fin (n - i'.val - 1),
                (fun j : Fin n => f j.castSucc)
                  ⟨i'.val + 1 + t.val, by omega⟩) + f (Fin.last n) := by
          calc
            (∑ t : Fin (n + 1 - i'.castSucc.val - 1),
                f ⟨i'.castSucc.val + 1 + t.val, by omega⟩) =
              ∑ t : Fin (n - i'.val),
                f ⟨i'.val + 1 + t.val, by omega⟩ := by
                  apply Fintype.sum_equiv (Fin.castOrderIso htargetCount).toEquiv
                  intro t
                  congr 1
            _ = _ := by
              rw [hsum]
              congr 1
        rw [htarget]
        ring

private lemma p29_forward_backward_error
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔL : P29Matrix n n,
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
  classical
  let y := p29ForwardSub fp n L b
  have hrow : ∀ i : Fin n, ∃ (c : Fin i.val → ℝ) (ed : ℝ),
      (∀ t, |c t| ≤ p29Gamma fp.u n *
        |L i ⟨t.val, lt_trans t.isLt i.isLt⟩|) ∧
      |ed| ≤ p29Gamma fp.u n * |L i i| ∧
      b i =
        (∑ t : Fin i.val,
          (L i ⟨t.val, lt_trans t.isLt i.isLt⟩ + c t) *
            y ⟨t.val, lt_trans t.isLt i.isLt⟩) +
          (L i i + ed) * y i := by
    intro i
    obtain ⟨c, ed, hc, hed, heq⟩ :=
      p29_rounded_row_backward fp n i.val (by omega)
        (fun t => L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
        (fun t => y ⟨t.val, lt_trans t.isLt i.isLt⟩)
        (b i) (L i i) (hdiag i) hvalid
    refine ⟨c, ed, hc, hed, ?_⟩
    have hspec := p29_forward_sub_spec fp n L b i
    change y i = _ at hspec
    rw [← hspec] at heq
    exact heq
  choose c ed hc hed heq using hrow
  let ΔL : P29Matrix n n := fun i j =>
    if hlt : j.val < i.val then
      c i ⟨j.val, hlt⟩
    else if j = i then ed i else 0
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    by_cases hlt : j.val < i.val
    · simp only [ΔL, hlt, dite_true]
      exact hc i ⟨j.val, hlt⟩
    · by_cases heji : j = i
      · subst j
        simp only [ΔL, lt_self_iff_false, dite_false, if_pos]
        exact hed i
      · have hij : i.val < j.val := by
          have hne : j.val ≠ i.val := by
            intro h
            apply heji
            exact Fin.ext h
          omega
        simp only [ΔL, hlt, dite_false, heji, if_false, abs_zero]
        rw [hlower i j hij]
        simp
  · intro i
    change ∑ j : Fin n, (L i j + ΔL i j) * y j = b i
    rw [heq i]
    rw [p29_fin_sum_lower_diag
      (fun j => (L i j + ΔL i j) * y j) i]
    · congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        simp only [ΔL, t.isLt, dite_true]
      · simp only [ΔL, lt_self_iff_false, dite_false, if_pos]
    · intro j hij
      have hz : L i j = 0 := hlower i j hij
      have hnlt : ¬ j.val < i.val := by omega
      have hne : j ≠ i := by
        intro h
        subst j
        omega
      have hdL : ΔL i j = 0 := by
        dsimp [ΔL]
        split
        · rename_i h
          exact (hnlt h).elim
        · simp [hne]
      rw [hz, hdL]
      simp

private lemma p29_back_backward_error
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔU : P29Matrix n n,
      (∀ i j, |ΔU i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * p29BackSub fp n U b j = b i := by
  classical
  let x := p29BackSub fp n U b
  have hrow : ∀ i : Fin n,
      ∃ (c : Fin (n - i.val - 1) → ℝ) (ed : ℝ),
      (∀ t, |c t| ≤ p29Gamma fp.u n *
        |U i ⟨i.val + 1 + t.val, by omega⟩|) ∧
      |ed| ≤ p29Gamma fp.u n * |U i i| ∧
      b i =
        (∑ t : Fin (n - i.val - 1),
          (U i ⟨i.val + 1 + t.val, by omega⟩ + c t) *
            x ⟨i.val + 1 + t.val, by omega⟩) +
          (U i i + ed) * x i := by
    intro i
    obtain ⟨c, ed, hc, hed, heq⟩ :=
      p29_rounded_row_backward fp n (n - i.val - 1) (by omega)
        (fun t => U i ⟨i.val + 1 + t.val, by omega⟩)
        (fun t => x ⟨i.val + 1 + t.val, by omega⟩)
        (b i) (U i i) (hdiag i) hvalid
    refine ⟨c, ed, hc, hed, ?_⟩
    have hspec := p29_back_sub_spec fp n U b i
    change x i = _ at hspec
    rw [← hspec] at heq
    exact heq
  choose c ed hc hed heq using hrow
  let ΔU : P29Matrix n n := fun i j =>
    if hlt : i.val < j.val then
      c i ⟨j.val - i.val - 1, by omega⟩
    else if j = i then ed i else 0
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    by_cases hlt : i.val < j.val
    · simp only [ΔU, hlt, dite_true]
      have hind :
          (⟨i.val + 1 + (j.val - i.val - 1), by omega⟩ : Fin n) = j := by
        apply Fin.ext
        change i.val + 1 + (j.val - i.val - 1) = j.val
        omega
      simpa only [hind] using hc i ⟨j.val - i.val - 1, by omega⟩
    · by_cases heji : j = i
      · subst j
        simp only [ΔU, lt_self_iff_false, dite_false, if_pos]
        exact hed i
      · have hji : j.val < i.val := by
          have hne : j.val ≠ i.val := by
            intro h
            apply heji
            exact Fin.ext h
          omega
        simp only [ΔU, hlt, dite_false, heji, if_false, abs_zero]
        rw [hupper i j hji]
        simp
  · intro i
    change ∑ j : Fin n, (U i j + ΔU i j) * x j = b i
    rw [heq i]
    rw [p29_fin_sum_diag_upper
      (fun j => (U i j + ΔU i j) * x j) i]
    · rw [add_comm]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        have hlt : i.val < i.val + 1 + t.val := by omega
        simp only [ΔU, hlt, dite_true]
        congr 3
        apply Fin.ext
        change i.val + 1 + t.val - i.val - 1 = t.val
        omega
      · simp only [ΔU, lt_self_iff_false, dite_false, if_pos]
    · intro j hji
      have hz : U i j = 0 := hupper i j hji
      have hnlt : ¬ i.val < j.val := by omega
      have hne : j ≠ i := by
        intro h
        subst j
        omega
      have hdU : ΔU i j = 0 := by
        dsimp [ΔU]
        split
        · rename_i h
          exact (hnlt h).elim
        · simp [hne]
      rw [hz, hdU]
      simp

private lemma p29_matmul_mul_vec {n : ℕ}
    (X Y : P29Matrix n n) (v : Fin n → ℝ) (i : Fin n) :
    ∑ j : Fin n, p29MatMul X Y i j * v j =
      ∑ k : Fin n, X i k * (∑ j : Fin n, Y k j * v j) := by
  unfold p29MatMul
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p29_entryNorm_nonneg {m n : ℕ} (X : P29Matrix m n) :
    0 ≤ p29EntryNorm X := by
  unfold p29EntryNorm
  positivity

private lemma p29_entry_abs_le_norm {m n : ℕ} (X : P29Matrix m n)
    (i : Fin m) (j : Fin n) :
    |X i j| ≤ p29EntryNorm X := by
  unfold p29EntryNorm
  calc
    |X i j| ≤ ∑ j' : Fin n, |X i j'| := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun j' => |X i j'|)
        (fun j' _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |X i' j'| := by
      exact Finset.single_le_sum
        (s := Finset.univ) (f := fun i' => ∑ j' : Fin n, |X i' j'|)
        (fun i' _ => by positivity)
        (Finset.mem_univ i)

private lemma p29_entryNorm_add {m n : ℕ} (X Y : P29Matrix m n) :
    p29EntryNorm (X + Y) ≤ p29EntryNorm X + p29EntryNorm Y := by
  unfold p29EntryNorm
  simp only [Matrix.add_apply]
  calc
    (∑ i, ∑ j, |X i j + Y i j|) ≤
        ∑ i, ∑ j, (|X i j| + |Y i j|) := by
      gcongr with i j
      exact abs_add_le _ _
    _ = (∑ i, ∑ j, |X i j|) + (∑ i, ∑ j, |Y i j|) := by
      simp_rw [Finset.sum_add_distrib]

private lemma p29_entryNorm_sub {m n : ℕ} (X Y : P29Matrix m n) :
    p29EntryNorm (X - Y) ≤ p29EntryNorm X + p29EntryNorm Y := by
  unfold p29EntryNorm
  simp only [Matrix.sub_apply]
  calc
    (∑ i, ∑ j, |X i j - Y i j|) ≤
        ∑ i, ∑ j, (|X i j| + |Y i j|) := by
      gcongr with i j
      exact abs_sub _ _
    _ = (∑ i, ∑ j, |X i j|) + (∑ i, ∑ j, |Y i j|) := by
      simp_rw [Finset.sum_add_distrib]

private lemma p29_entryNorm_smul_bound {m n : ℕ}
    (X E : P29Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (hE : ∀ i j, |E i j| ≤ c * |X i j|) :
    p29EntryNorm E ≤ c * p29EntryNorm X := by
  unfold p29EntryNorm
  calc
    (∑ i, ∑ j, |E i j|) ≤ ∑ i, ∑ j, c * |X i j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hE i j
    _ = c * ∑ i, ∑ j, |X i j| := by
      simp_rw [Finset.mul_sum]

private lemma p29_entryNorm_mul {n : ℕ} (X Y : P29Matrix n n) :
    p29EntryNorm (p29MatMul X Y) ≤
      (n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y := by
  have hx := p29_entryNorm_nonneg X
  have hy := p29_entryNorm_nonneg Y
  unfold p29EntryNorm p29MatMul
  calc
    (∑ i, ∑ j, |∑ k, X i k * Y k j|) ≤
        ∑ i, ∑ j, ∑ k, |X i k * Y k j| := by
      gcongr with i j
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n,
        p29EntryNorm X * p29EntryNorm Y := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul (p29_entry_abs_le_norm X i k)
        (p29_entry_abs_le_norm Y k j) (abs_nonneg _) hx
    _ = (n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y := by
      simp [pow_succ]
      ring

private lemma p29_entryNorm_mul3 {n : ℕ}
    (X Y Z : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
      (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y * p29EntryNorm Z := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul X Y) * p29EntryNorm Z :=
      p29_entryNorm_mul _ _
    _ ≤ (n : ℝ) ^ 3 *
          ((n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y) *
          p29EntryNorm Z := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (p29_entryNorm_mul X Y) (by positivity))
        (p29_entryNorm_nonneg Z)
    _ = (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y * p29EntryNorm Z := by
      ring

private lemma p29_entryNorm_transpose {n : ℕ} (X : P29Matrix n n) :
    p29EntryNorm (p29Transpose X) = p29EntryNorm X := by
  unfold p29EntryNorm p29Transpose
  rw [Finset.sum_comm]

private lemma p29_matmul_add_left {n : ℕ}
    (X Y Z : P29Matrix n n) :
    p29MatMul (X + Y) Z = p29MatMul X Z + p29MatMul Y Z := by
  ext i j
  simp only [p29MatMul, Matrix.add_apply]
  simp_rw [add_mul, Finset.sum_add_distrib]

private lemma p29_matmul_add_right {n : ℕ}
    (X Y Z : P29Matrix n n) :
    p29MatMul X (Y + Z) = p29MatMul X Y + p29MatMul X Z := by
  ext i j
  simp only [p29MatMul, Matrix.add_apply]
  simp_rw [mul_add, Finset.sum_add_distrib]

private lemma p29_combined_telescope {n : ℕ}
    (L D T ΔL ΔD ΔU : P29Matrix n n) :
    p29MatMul (p29MatMul (L + ΔL) (D + ΔD)) (T + ΔU) -
        p29MatMul (p29MatMul L D) T =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU) +
      p29MatMul (p29MatMul L ΔD) (T + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  rw [p29_matmul_add_left L ΔL (D + ΔD)]
  rw [p29_matmul_add_left]
  rw [p29_matmul_add_right L D ΔD]
  rw [p29_matmul_add_left (p29MatMul L D) (p29MatMul L ΔD) (T + ΔU)]
  rw [p29_matmul_add_right (p29MatMul L D) T ΔU]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  ring

private lemma p29_combined_norm_bound
    (fp : P29FPModel) (n : ℕ) (eta : ℝ)
    (L D ΔL ΔD ΔU : P29Matrix n n)
    (heta : 0 ≤ eta) (hvalid : P29GammaValid fp.u n)
    (hΔL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hΔD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hΔU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let g := p29Gamma fp.u n
  let T := p29Transpose L
  have hg : 0 ≤ g := p29_gamma_nonneg_of_valid fp.u n fp.u_nonneg hvalid
  have hn : 0 ≤ (n : ℝ) ^ 6 := by positivity
  have hL : 0 ≤ p29EntryNorm L := p29_entryNorm_nonneg L
  have hD : 0 ≤ p29EntryNorm D := p29_entryNorm_nonneg D
  have hT : 0 ≤ p29EntryNorm T := p29_entryNorm_nonneg T
  have hdL : p29EntryNorm ΔL ≤ g * p29EntryNorm L :=
    p29_entryNorm_smul_bound L ΔL g hg hΔL
  have hdU : p29EntryNorm ΔU ≤ g * p29EntryNorm T :=
    p29_entryNorm_smul_bound T ΔU g hg hΔU
  have hDp : p29EntryNorm (D + ΔD) ≤ (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤ p29EntryNorm D + p29EntryNorm ΔD :=
        p29_entryNorm_add D ΔD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D := add_le_add (le_refl _) hΔD
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hTp : p29EntryNorm (T + ΔU) ≤ (1 + g) * p29EntryNorm T := by
    calc
      p29EntryNorm (T + ΔU) ≤ p29EntryNorm T + p29EntryNorm ΔU :=
        p29_entryNorm_add T ΔU
      _ ≤ p29EntryNorm T + g * p29EntryNorm T := add_le_add (le_refl _) hdU
      _ = (1 + g) * p29EntryNorm T := by ring
  let X := p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU)
  let Y := p29MatMul (p29MatMul L ΔD) (T + ΔU)
  let Z := p29MatMul (p29MatMul L D) ΔU
  have hX : p29EntryNorm X ≤
      (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
        ((1 + eta) * p29EntryNorm D) * ((1 + g) * p29EntryNorm T) := by
    calc
      p29EntryNorm X ≤ (n : ℝ) ^ 6 * p29EntryNorm ΔL *
          p29EntryNorm (D + ΔD) * p29EntryNorm (T + ΔU) :=
        p29_entryNorm_mul3 _ _ _
      _ ≤ (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          p29EntryNorm (D + ΔD) * p29EntryNorm (T + ΔU) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hdL hn)
            (p29_entryNorm_nonneg (D + ΔD)))
          (p29_entryNorm_nonneg (T + ΔU))
      _ ≤ (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) * p29EntryNorm (T + ΔU) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDp (mul_nonneg hn (mul_nonneg hg hL)))
          (p29_entryNorm_nonneg (T + ΔU))
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left hTp
          (mul_nonneg
            (mul_nonneg hn (mul_nonneg hg hL))
            (mul_nonneg (by linarith) hD))
  have hY : p29EntryNorm Y ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * (eta * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm T) := by
    calc
      p29EntryNorm Y ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm ΔD * p29EntryNorm (T + ΔU) :=
        p29_entryNorm_mul3 _ _ _
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          (eta * p29EntryNorm D) * p29EntryNorm (T + ΔU) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hΔD (mul_nonneg hn hL))
          (p29_entryNorm_nonneg (T + ΔU))
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left hTp
          (mul_nonneg (mul_nonneg hn hL) (mul_nonneg heta hD))
  have hZ : p29EntryNorm Z ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        (g * p29EntryNorm T) := by
    calc
      p29EntryNorm Z ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm D * p29EntryNorm ΔU := p29_entryNorm_mul3 _ _ _
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_left hdU
          (mul_nonneg (mul_nonneg hn hL) hD)
  unfold p29CombinedBackwardError p29PerturbedLDLT p29LDLT
  change p29EntryNorm
      (p29MatMul (p29MatMul (L + ΔL) (D + ΔD)) (T + ΔU) -
        p29MatMul (p29MatMul L D) T) ≤ _
  rw [p29_combined_telescope]
  change p29EntryNorm (X + Y + Z) ≤ _
  calc
    p29EntryNorm (X + Y + Z) ≤
        p29EntryNorm (X + Y) + p29EntryNorm Z := p29_entryNorm_add _ _
    _ ≤ (p29EntryNorm X + p29EntryNorm Y) + p29EntryNorm Z := by
      gcongr
      exact p29_entryNorm_add X Y
    _ ≤
        ((n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) * ((1 + g) * p29EntryNorm T)) +
        ((n : ℝ) ^ 6 * p29EntryNorm L * (eta * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm T)) +
        ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (g * p29EntryNorm T)) := add_le_add (add_le_add hX hY) hZ
    _ = p29SolveBackwardFactor fp n eta L D := by
      dsimp [g, T]
      unfold p29SolveBackwardFactor
      rw [p29_entryNorm_transpose]
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
  classical
  obtain ⟨ΔD, hΔD, hDsolve'⟩ := hDsolve
  obtain ⟨ΔL, hΔL, hLsolve⟩ :=
    p29_forward_backward_error fp n L b hdiag hlower hvalid
  have hdiagT : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hupperT : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hUsolve⟩ :=
    p29_back_backward_error fp n (p29Transpose L) z hdiagT hupperT hvalid
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · let x := p29BackSub fp n (p29Transpose L) z
    let y := p29ForwardSub fp n L b
    have hAF : A + F = p29PerturbedLDLT L D ΔL ΔD ΔU := by
      ext i j
      have hf := congrArg (fun M : P29Matrix n n => M i j) hfactor
      simp only [Matrix.add_apply] at hf ⊢
      dsimp [F]
      unfold p29TotalBackwardError p29CombinedBackwardError
      simp only [Matrix.add_apply, Matrix.sub_apply]
      linarith
    intro i
    change ∑ j : Fin n, (A + F) i j * x j = b i
    rw [hAF]
    unfold p29PerturbedLDLT
    rw [p29_matmul_mul_vec]
    rw [p29_matmul_mul_vec]
    simp only [Matrix.add_apply]
    dsimp [x, y]
    simp_rw [hUsolve]
    simp_rw [hDsolve']
    exact hLsolve i
  · dsimp [F]
    unfold p29TotalBackwardBound
    calc
      p29EntryNorm (p29TotalBackwardError E0 L D ΔL ΔD ΔU) ≤
          p29EntryNorm E0 +
            p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) := by
        unfold p29TotalBackwardError
        exact p29_entryNorm_add _ _
      _ ≤ factorEta * p29EntryNorm A + p29SolveBackwardFactor fp n eta L D :=
        add_le_add hE0
          (p29_combined_norm_bound fp n eta L D ΔL ΔD ΔU
            heta hvalid hΔL hΔD hΔU)

end HighamBench
