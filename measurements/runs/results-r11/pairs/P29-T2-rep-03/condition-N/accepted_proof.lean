import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29_gamma_nonneg (u : ℝ) (n : ℕ)
    (hu : 0 ≤ u) (hv : P29GammaValid u n) :
    0 ≤ p29Gamma u n := by
  unfold p29Gamma P29GammaValid at *
  apply div_nonneg
  · positivity
  · linarith

private lemma p29_factor_bounds_step (u : ℝ) (n c : ℕ) (p d : ℝ)
    (hu : 0 ≤ u) (hv : P29GammaValid u n) (hc : c + 1 ≤ n)
    (hp0 : 1 - (c : ℝ) * u ≤ p)
    (hp1 : p ≤ 1 / (1 - (c : ℝ) * u))
    (hd : |d| ≤ u) :
    1 - ((c + 1 : ℕ) : ℝ) * u ≤ p * (1 + d) ∧
      p * (1 + d) ≤ 1 / (1 - ((c + 1 : ℕ) : ℝ) * u) := by
  unfold P29GammaValid at hv
  have hcn : ((c + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hc0 : (c : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
    omega
  have hnpos : 0 < 1 - (n : ℝ) * u := by linarith
  have hcspos : 0 < 1 - ((c + 1 : ℕ) : ℝ) * u := by linarith
  have hcpos : 0 < 1 - (c : ℝ) * u := by linarith
  have hdlo : -u ≤ d := (abs_le.mp hd).1
  have hdhi : d ≤ u := (abs_le.mp hd).2
  have hp : 0 < p := lt_of_lt_of_le hcpos hp0
  have hu1 : 0 ≤ 1 + d := by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
    have : u < 1 := by nlinarith
    linarith
  constructor
  · have hmul := mul_le_mul hp0 (show 1 - u ≤ 1 + d by linarith)
        (show 0 ≤ 1 - u by
          have : u < 1 := by
            have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
            nlinarith
          linarith)
        (le_of_lt hp)
    norm_num at hmul ⊢
    nlinarith [mul_nonneg (show 0 ≤ (c : ℝ) by positivity) hu]
  · apply (le_div_iff₀ hcspos).2
    have hpd : p * (1 + d) ≤ (1 / (1 - (c : ℝ) * u)) * (1 + u) := by
      gcongr
    have haux : (1 + u) * (1 - ((c + 1 : ℕ) : ℝ) * u) ≤
        1 - (c : ℝ) * u := by
      push_cast
      have hc1nonneg : (0 : ℝ) ≤ (c : ℝ) + 1 := by positivity
      nlinarith [mul_nonneg hc1nonneg (sq_nonneg u)]
    rw [one_div] at hpd
    calc
      p * (1 + d) * (1 - ((c + 1 : ℕ) : ℝ) * u)
          ≤ ((1 - (c : ℝ) * u)⁻¹ * (1 + u)) *
              (1 - ((c + 1 : ℕ) : ℝ) * u) := by gcongr
      _ = (1 - (c : ℝ) * u)⁻¹ *
              ((1 + u) * (1 - ((c + 1 : ℕ) : ℝ) * u)) := by ring
      _ ≤ (1 - (c : ℝ) * u)⁻¹ * (1 - (c : ℝ) * u) := by
            gcongr
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hcpos)

private lemma p29_ratio_gamma (u : ℝ) (n c : ℕ) (p d : ℝ)
    (hu : 0 ≤ u) (hv : P29GammaValid u n) (hc : c + 1 ≤ n)
    (hp0 : 1 - (c : ℝ) * u ≤ p)
    (hp1 : p ≤ 1 / (1 - (c : ℝ) * u))
    (hd : |d| ≤ u) :
    |(1 + d) / p - 1| ≤ p29Gamma u n := by
  unfold P29GammaValid at hv
  have hcn : ((c + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hc0 : (c : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
    omega
  have hn0 : 0 ≤ (n : ℝ) * u := mul_nonneg (by positivity) hu
  have hnpos : 0 < 1 - (n : ℝ) * u := by linarith
  have hcpos : 0 < 1 - (c : ℝ) * u := by linarith
  have hp : 0 < p := lt_of_lt_of_le hcpos hp0
  have hn : (1 : ℝ) ≤ n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega : n ≠ 0))
  have hu_lt : u < 1 := by nlinarith
  have hdlo : -u ≤ d := (abs_le.mp hd).1
  have hdhi : d ≤ u := (abs_le.mp hd).2
  have hnum0 : 0 ≤ 1 + d := by linarith
  have hcp : (1 - (c : ℝ) * u) * p ≤ 1 := by
    calc
      (1 - (c : ℝ) * u) * p
          ≤ (1 - (c : ℝ) * u) * (1 / (1 - (c : ℝ) * u)) := by gcongr
      _ = 1 := by field_simp
  have hrecip : 1 - (c : ℝ) * u ≤ 1 / p := by
    exact (le_div_iff₀ hp).2 (by simpa [mul_comm] using hcp)
  have hratio_lo : 1 - (n : ℝ) * u ≤ (1 + d) / p := by
    rw [div_eq_mul_inv]
    have hm := mul_le_mul (show 1 - u ≤ 1 + d by linarith) hrecip
      (show 0 ≤ 1 - (c : ℝ) * u by linarith)
      (show 0 ≤ 1 + d by exact hnum0)
    push_cast at hcn
    have hprod : 1 - ((c : ℝ) + 1) * u ≤
        (1 - u) * (1 - (c : ℝ) * u) := by
      nlinarith [mul_nonneg (show 0 ≤ (c : ℝ) by positivity) (sq_nonneg u)]
    have hm' : (1 - u) * (1 - (c : ℝ) * u) ≤ (1 + d) * p⁻¹ := by
      simpa [one_div] using hm
    exact (show 1 - (n : ℝ) * u ≤ 1 - ((c : ℝ) + 1) * u by linarith) |>.trans
      (hprod.trans hm')
  have hratio_mid : (1 + d) / p ≤
      (1 + u) / (1 - (c : ℝ) * u) := by
    apply (div_le_iff₀ hp).2
    have hx0 : 0 ≤ (1 + u) / (1 - (c : ℝ) * u) := by positivity
    calc
      1 + d ≤ 1 + u := by linarith
      _ = ((1 + u) / (1 - (c : ℝ) * u)) *
          (1 - (c : ℝ) * u) := by
            symm
            exact div_mul_cancel₀ _ (ne_of_gt hcpos)
      _ ≤ ((1 + u) / (1 - (c : ℝ) * u)) * p := by gcongr
  have hratio_hi : (1 + d) / p ≤ 1 / (1 - (n : ℝ) * u) := by
    refine hratio_mid.trans ?_
    apply (div_le_div_iff₀ hcpos hnpos).2
    push_cast at hcn
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) by positivity) (sq_nonneg u)]
  have hgamma_ge : (n : ℝ) * u ≤
      ((n : ℝ) * u) / (1 - (n : ℝ) * u) := by
    apply (le_div_iff₀ hnpos).2
    nlinarith [sq_nonneg ((n : ℝ) * u)]
  have hid : 1 / (1 - (n : ℝ) * u) - 1 =
      ((n : ℝ) * u) / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  rw [abs_le, p29Gamma]
  constructor
  · linarith
  · rw [← hid]
    linarith

private lemma p29_inverse_product_gamma (u : ℝ) (n c : ℕ) (p d : ℝ)
    (hu : 0 ≤ u) (hv : P29GammaValid u n) (hc : c + 1 ≤ n)
    (hp0 : 1 - (c : ℝ) * u ≤ p)
    (hp1 : p ≤ 1 / (1 - (c : ℝ) * u))
    (hd : |d| ≤ u) :
    |1 / (p * (1 + d)) - 1| ≤ p29Gamma u n := by
  have hs := p29_factor_bounds_step u n c p d hu hv hc hp0 hp1 hd
  unfold P29GammaValid at hv
  have hcn : ((c + 1 : ℕ) : ℝ) * u ≤ (n : ℝ) * u := by gcongr
  have hn0 : 0 ≤ (n : ℝ) * u := mul_nonneg (by positivity) hu
  have hnpos : 0 < 1 - (n : ℝ) * u := by linarith
  have hmpos : 0 < 1 - ((c + 1 : ℕ) : ℝ) * u := by linarith
  have hqpos : 0 < p * (1 + d) := lt_of_lt_of_le hmpos hs.1
  have hmq : (1 - ((c + 1 : ℕ) : ℝ) * u) * (p * (1 + d)) ≤ 1 := by
    calc
      (1 - ((c + 1 : ℕ) : ℝ) * u) * (p * (1 + d))
          ≤ (1 - ((c + 1 : ℕ) : ℝ) * u) *
              (1 / (1 - ((c + 1 : ℕ) : ℝ) * u)) := by
                exact mul_le_mul_of_nonneg_left hs.2 (le_of_lt hmpos)
      _ = 1 := by field_simp
  have hlo : 1 - (n : ℝ) * u ≤ 1 / (p * (1 + d)) := by
    have hmrec : 1 - ((c + 1 : ℕ) : ℝ) * u ≤
        1 / (p * (1 + d)) := (le_div_iff₀ hqpos).2 (by
          simpa [mul_comm] using hmq)
    linarith
  have hhi : 1 / (p * (1 + d)) ≤ 1 / (1 - (n : ℝ) * u) := by
    apply one_div_le_one_div_of_le hnpos
    exact le_trans (by linarith : 1 - (n : ℝ) * u ≤
      1 - ((c + 1 : ℕ) : ℝ) * u) hs.1
  have hgamma_ge : (n : ℝ) * u ≤
      ((n : ℝ) * u) / (1 - (n : ℝ) * u) := by
    apply (le_div_iff₀ hnpos).2
    nlinarith [sq_nonneg ((n : ℝ) * u)]
  have hid : 1 / (1 - (n : ℝ) * u) - 1 =
      ((n : ℝ) * u) / (1 - (n : ℝ) * u) := by
    field_simp
    ring
  rw [abs_le, p29Gamma]
  constructor
  · linarith
  · rw [← hid]
    linarith

private lemma p29_rounded_sub_fold_backward (fp : P29FPModel) (n : ℕ)
    (hvalid : P29GammaValid fp.u n) :
    ∀ (c : ℕ), c ≤ n → ∀ (a x : Fin c → ℝ) (b : ℝ),
      ∃ (p : ℝ) (e : Fin c → ℝ),
        Fin.foldl c
            (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) b =
          p * (b - ∑ t : Fin c, (a t + e t) * x t) ∧
        1 - (c : ℝ) * fp.u ≤ p ∧
        p ≤ 1 / (1 - (c : ℝ) * fp.u) ∧
        ∀ t, |e t| ≤ p29Gamma fp.u n * |a t| := by
  intro c
  induction c with
  | zero =>
      intro hc a x b
      refine ⟨1, fun t => Fin.elim0 t, ?_⟩
      simp
  | succ c ih =>
      intro hc a x b
      have hc' : c ≤ n := by omega
      obtain ⟨p, e, hfold, hp0, hp1, he⟩ :=
        ih hc' (fun t => a t.castSucc) (fun t => x t.castSucc) b
      obtain ⟨mu, hmu, hmul⟩ :=
        fp.model_mul (a (Fin.last c)) (x (Fin.last c))
      obtain ⟨d, hd, hsub⟩ := fp.model_sub
        (Fin.foldl c
          (fun acc t => fp.fl_sub acc
            (fp.fl_mul (a t.castSucc) (x t.castSucc))) b)
        (fp.fl_mul (a (Fin.last c)) (x (Fin.last c)))
      have hp_pos : 0 < p := by
        have hcu : (c : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
          gcongr
          exact fp.u_nonneg
        have : 0 < 1 - (c : ℝ) * fp.u := by
          unfold P29GammaValid at hvalid
          linarith
        exact lt_of_lt_of_le this hp0
      let elast : ℝ := a (Fin.last c) * ((1 + mu) / p - 1)
      let enew : Fin (c + 1) → ℝ := Fin.lastCases elast e
      refine ⟨p * (1 + d), enew, ?_, ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ_last, hsub, hmul, hfold,
          Fin.sum_univ_castSucc]
        simp only [enew, Fin.lastCases_castSucc, Fin.lastCases_last]
        dsimp [elast]
        field_simp [ne_of_gt hp_pos]
        ring
      · exact (p29_factor_bounds_step fp.u n c p d fp.u_nonneg hvalid hc
          hp0 hp1 hd).1
      · exact (p29_factor_bounds_step fp.u n c p d fp.u_nonneg hvalid hc
          hp0 hp1 hd).2
      · intro t
        refine Fin.lastCases ?_ (fun i => ?_) t
        · simp only [enew, Fin.lastCases_last, elast]
          rw [abs_mul]
          have hr := p29_ratio_gamma fp.u n c p mu fp.u_nonneg hvalid hc
            hp0 hp1 hmu
          nlinarith [abs_nonneg (a (Fin.last c))]
        · simpa [enew] using he i

private lemma p29_rounded_row_backward (fp : P29FPModel) (n c : ℕ)
    (hvalid : P29GammaValid fp.u n) (hc : c + 1 ≤ n)
    (a x : Fin c → ℝ) (b diag : ℝ) (hdiag : diag ≠ 0) :
    ∃ (e : Fin c → ℝ) (ediag q : ℝ),
      (∀ t, |e t| ≤ p29Gamma fp.u n * |a t|) ∧
      |ediag| ≤ p29Gamma fp.u n * |diag| ∧
      q = fp.fl_div
        (Fin.foldl c
          (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) b)
        diag ∧
      (∑ t : Fin c, (a t + e t) * x t) + (diag + ediag) * q = b := by
  obtain ⟨p, e, hfold, hp0, hp1, he⟩ :=
    p29_rounded_sub_fold_backward fp n hvalid c (by omega) a x b
  obtain ⟨rho, hrho, hdiv⟩ := fp.model_div
    (Fin.foldl c
      (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) b)
    diag hdiag
  let ediag := diag * (1 / (p * (1 + rho)) - 1)
  let q := fp.fl_div
    (Fin.foldl c
      (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) b)
    diag
  have hp_pos : 0 < p := by
    have hcu : (c : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
      gcongr
      exact fp.u_nonneg
      omega
    have : 0 < 1 - (c : ℝ) * fp.u := by
      unfold P29GammaValid at hvalid
      linarith
    exact lt_of_lt_of_le this hp0
  have hprod_pos : 0 < p * (1 + rho) := by
    have hs := p29_factor_bounds_step fp.u n c p rho fp.u_nonneg
      hvalid hc hp0 hp1 hrho
    have hcn : ((c + 1 : ℕ) : ℝ) * fp.u ≤ (n : ℝ) * fp.u := by
      gcongr
      exact fp.u_nonneg
    have : 0 < 1 - ((c + 1 : ℕ) : ℝ) * fp.u := by
      unfold P29GammaValid at hvalid
      linarith
    exact lt_of_lt_of_le this hs.1
  have hrho1 : 1 + rho ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hprod_pos
    linarith
  refine ⟨e, ediag, q, he, ?_, rfl, ?_⟩
  · dsimp [ediag]
    rw [abs_mul]
    have hi := p29_inverse_product_gamma fp.u n c p rho fp.u_nonneg
      hvalid hc hp0 hp1 hrho
    nlinarith [abs_nonneg diag]
  · dsimp [q, ediag]
    rw [hdiv, hfold]
    field_simp [hdiag, ne_of_gt hp_pos, ne_of_gt hprod_pos, hrho1]
    ring

private noncomputable def p29ForwardRow (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_div
    (Fin.foldl i.val
      (fun acc (t : Fin i.val) =>
        fp.fl_sub acc
          (fp.fl_mul (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
            (x ⟨t.val, lt_trans t.isLt i.isLt⟩)))
      (b i))
    (L i i)

private lemma p29_forward_steps_spec (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let r := p29ForwardSubSteps fp n L b k hk x
      (∀ j : Fin n, j.val < n - k → r j = x j) ∧
      (∀ j : Fin n, n - k ≤ j.val → r j = p29ForwardRow fp n L b r j) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simp [p29ForwardSubSteps]
  | succ k ih =>
      intro hk x
      rw [p29ForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hs := ih (Nat.le_of_succ_le hk) x'
      dsimp only at hs ⊢
      constructor
      · intro j hj
        have hj' : j.val < n - k := by omega
        rw [hs.1 j hj']
        have hji : j ≠ ik := by
          intro hji
          have : j.val = ik.val := congrArg Fin.val hji
          dsimp [ik] at this
          omega
        simp [x', hji]
      · intro j hj
        by_cases hji : j = ik
        · subst j
          have hik : ik.val < n - k := by
            dsimp [ik]
            omega
          rw [hs.1 ik hik]
          have hxik : x' ik = fp.fl_div s (L ik ik) := by
            simp [x']
          rw [hxik]
          dsimp only [p29ForwardRow]
          congr 1
          · dsimp [s, count, ik]
            apply congrArg (fun f => Fin.foldl (n - k - 1) f (b ⟨n - k - 1, by omega⟩))
            funext acc t
            congr 3
            rw [hs.1]
            · have hti : (⟨t.val, by omega⟩ : Fin n) ≠ ik := by
                intro h
                have := congrArg Fin.val h
                dsimp [ik] at this
                omega
              simp [x', hti]
            · simp
              omega
        · have hjgt : n - k ≤ j.val := by
            have : ik.val < j.val := by
              dsimp [ik]
              have hne : j.val ≠ n - k - 1 := by
                intro heq
                apply hji
                apply Fin.ext
                simpa [ik] using heq
              omega
            dsimp [ik] at this
            omega
          exact hs.2 j hjgt

private noncomputable def p29LowerRowError {n : ℕ} (i : Fin n)
    (e : Fin i.val → ℝ) (ediag : ℝ) (j : Fin n) : ℝ :=
  if h : j.val < i.val then e ⟨j.val, h⟩
  else if j = i then ediag else 0

private lemma p29_lower_row_sum {n : ℕ} (L : P29Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) (e : Fin i.val → ℝ) (ediag : ℝ)
    (hlower : ∀ j : Fin n, i.val < j.val → L i j = 0) :
    (∑ j : Fin n, (L i j + p29LowerRowError i e ediag j) * x j) =
      (∑ t : Fin i.val,
        (L i ⟨t.val, lt_trans t.isLt i.isLt⟩ + e t) *
          x ⟨t.val, lt_trans t.isLt i.isLt⟩) +
        (L i i + ediag) * x i := by
  let f : ℕ → ℝ := fun k => if hk : k < n then
    (L i ⟨k, hk⟩ + p29LowerRowError i e ediag ⟨k, hk⟩) * x ⟨k, hk⟩
    else 0
  have htorange :
      (∑ j : Fin n, (L i j + p29LowerRowError i e ediag j) * x j) =
        ∑ k ∈ Finset.range n, f k := by
    calc
      (∑ j : Fin n, (L i j + p29LowerRowError i e ediag j) * x j) =
          ∑ j : Fin n, f j.val := by
            apply Finset.univ.sum_congr rfl
            intro j hj
            simp [f, j.isLt]
      _ = ∑ k ∈ Finset.range n, f k := Fin.sum_univ_eq_sum_range f n
  have hs : (∑ k ∈ Finset.range n, f k) =
      ∑ k ∈ Finset.range (i.val + 1), f k := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_iff.mpr i.isLt))
    intro k hkn hki
    have hkn' : k < n := Finset.mem_range.mp hkn
    have hik : i.val < k := by
      simp only [Finset.mem_range, not_lt] at hki
      omega
    have hzero := hlower ⟨k, hkn'⟩ hik
    simp only [f, dif_pos hkn', hzero, zero_add, p29LowerRowError]
    split_ifs with hlt heq
    · omega
    · have := congrArg Fin.val heq
      simp at this
      omega
    · ring
  rw [htorange, hs, Finset.sum_range_succ]
  have hprefix : (∑ k ∈ Finset.range i.val, f k) =
      ∑ t : Fin i.val,
        (L i ⟨t.val, lt_trans t.isLt i.isLt⟩ + e t) *
          x ⟨t.val, lt_trans t.isLt i.isLt⟩ := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => f k) i.val]
    apply Finset.univ.sum_congr rfl
    intro t ht
    simp [f, p29LowerRowError, t.isLt, lt_trans t.isLt i.isLt]
  rw [hprefix]
  simp [f, i.isLt, p29LowerRowError]

private lemma p29_forward_sub_spec (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ i, p29ForwardSub fp n L b i =
      p29ForwardRow fp n L b (p29ForwardSub fp n L b) i := by
  intro i
  have hs := (p29_forward_steps_spec fp n L b n (le_refl n)
    (fun _ => 0)).2 i (by omega)
  exact hs

private lemma p29_forward_backward_error (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔL : P29Matrix n n,
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
  let y := p29ForwardSub fp n L b
  have hy : ∀ i, y i = p29ForwardRow fp n L b y i :=
    p29_forward_sub_spec fp n L b
  have hrow : ∀ i : Fin n, ∃ (e : Fin i.val → ℝ) (ediag : ℝ),
      (∀ t, |e t| ≤ p29Gamma fp.u n *
        |L i ⟨t.val, lt_trans t.isLt i.isLt⟩|) ∧
      |ediag| ≤ p29Gamma fp.u n * |L i i| ∧
      (∑ t : Fin i.val,
        (L i ⟨t.val, lt_trans t.isLt i.isLt⟩ + e t) *
          y ⟨t.val, lt_trans t.isLt i.isLt⟩) +
        (L i i + ediag) * y i = b i := by
    intro i
    obtain ⟨e, ediag, q, he, hed, hq, heq⟩ :=
      p29_rounded_row_backward fp n i.val hvalid (by omega)
        (fun t => L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
        (fun t => y ⟨t.val, lt_trans t.isLt i.isLt⟩)
        (b i) (L i i) (hdiag i)
    refine ⟨e, ediag, he, hed, ?_⟩
    have hyi := hy i
    dsimp only [p29ForwardRow] at hyi
    rw [← hq] at hyi
    rw [hyi]
    exact heq
  choose e ediag he hed heq using hrow
  let ΔL : P29Matrix n n := fun i j => p29LowerRowError i (e i) (ediag i) j
  refine ⟨ΔL, ?_, ?_⟩
  · intro i j
    dsimp only [ΔL, p29LowerRowError]
    split_ifs with hlt heqi
    · simpa using he i ⟨j.val, hlt⟩
    · subst j
      exact hed i
    · simp only [abs_zero]
      exact mul_nonneg (p29_gamma_nonneg fp.u n fp.u_nonneg hvalid) (abs_nonneg _)
  · intro i
    rw [p29_lower_row_sum L y i (e i) (ediag i) (hlower i)]
    exact heq i

private noncomputable def p29BackRow (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b x : Fin n → ℝ) (i : Fin n) : ℝ :=
  fp.fl_div
    (Fin.foldl (n - i.val - 1)
      (fun acc (t : Fin (n - i.val - 1)) =>
        fp.fl_sub acc
          (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
            (x ⟨i.val + 1 + t.val, by omega⟩)))
      (b i))
    (U i i)

private lemma p29_back_steps_spec (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let r := p29BackSubSteps fp n U b k hk x
      (∀ j : Fin n, k ≤ j.val → r j = x j) ∧
      (∀ j : Fin n, j.val < k → r j = p29BackRow fp n U b r j) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      simp [p29BackSubSteps]
  | succ k ih =>
      intro hk x
      rw [p29BackSubSteps]
      let ik : Fin n := ⟨k, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hs := ih (Nat.le_of_succ_le hk) x'
      dsimp only at hs ⊢
      constructor
      · intro j hj
        have hj' : k ≤ j.val := by omega
        rw [hs.1 j hj']
        have hji : j ≠ ik := by
          intro hji
          have := congrArg Fin.val hji
          dsimp [ik] at this
          omega
        simp [x', hji]
      · intro j hj
        by_cases hji : j = ik
        · subst j
          have hik : k ≤ ik.val := by simp [ik]
          rw [hs.1 ik hik]
          have hxik : x' ik = fp.fl_div s (U ik ik) := by simp [x']
          rw [hxik]
          dsimp only [p29BackRow]
          congr 1
          dsimp [s, count, ik]
          apply congrArg (fun f => Fin.foldl (n - k - 1) f (b ⟨k, by omega⟩))
          funext acc t
          congr 3
          rw [hs.1]
          · have hti : (⟨k + 1 + t.val, by omega⟩ : Fin n) ≠ ik := by
              intro h
              have := congrArg Fin.val h
              dsimp [ik] at this
              omega
            simp [x', hti]
          · simp
            omega
        · have hjlt : j.val < k := by
            have hne : j.val ≠ k := by
              intro heq
              apply hji
              apply Fin.ext
              simpa [ik] using heq
            omega
          exact hs.2 j hjlt

private lemma p29_back_sub_spec (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ i, p29BackSub fp n U b i =
      p29BackRow fp n U b (p29BackSub fp n U b) i := by
  intro i
  have hs := (p29_back_steps_spec fp n U b n (le_refl n)
    (fun _ => 0)).2 i i.isLt
  exact hs

private noncomputable def p29UpperRowError {n : ℕ} (i : Fin n)
    (e : Fin (n - i.val - 1) → ℝ) (ediag : ℝ) (j : Fin n) : ℝ :=
  if h : i.val < j.val then e ⟨j.val - i.val - 1, by omega⟩
  else if j = i then ediag else 0

private lemma p29_upper_row_sum {n : ℕ} (U : P29Matrix n n)
    (x : Fin n → ℝ) (i : Fin n) (e : Fin (n - i.val - 1) → ℝ)
    (ediag : ℝ)
    (hupper : ∀ j : Fin n, j.val < i.val → U i j = 0) :
    (∑ j : Fin n, (U i j + p29UpperRowError i e ediag j) * x j) =
      (U i i + ediag) * x i +
      ∑ t : Fin (n - i.val - 1),
        (U i ⟨i.val + 1 + t.val, by omega⟩ + e t) *
          x ⟨i.val + 1 + t.val, by omega⟩ := by
  let f : ℕ → ℝ := fun k => if hk : k < n then
    (U i ⟨k, hk⟩ + p29UpperRowError i e ediag ⟨k, hk⟩) * x ⟨k, hk⟩
    else 0
  have htorange :
      (∑ j : Fin n, (U i j + p29UpperRowError i e ediag j) * x j) =
        ∑ k ∈ Finset.range n, f k := by
    calc
      _ = ∑ j : Fin n, f j.val := by
        apply Finset.univ.sum_congr rfl
        intro j hj
        simp [f, j.isLt]
      _ = _ := Fin.sum_univ_eq_sum_range f n
  rw [htorange]
  conv_lhs =>
    rw [show n = (i.val + 1) + (n - i.val - 1) by omega,
      Finset.sum_range_add]
  rw [Finset.sum_range_succ]
  have hprefix : (∑ k ∈ Finset.range i.val, f k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hki : k < i.val := Finset.mem_range.mp hk
    have hkn : k < n := lt_trans hki i.isLt
    have hz := hupper ⟨k, hkn⟩ hki
    simp only [f, dif_pos hkn, hz, zero_add, p29UpperRowError]
    split_ifs with hgt heq
    · omega
    · have := congrArg Fin.val heq
      simp at this
      omega
    · ring
  rw [hprefix, zero_add]
  have hdiagv : f i.val = (U i i + ediag) * x i := by
    simp [f, i.isLt, p29UpperRowError]
  rw [hdiagv]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range
    (fun k => f (i.val + 1 + k)) (n - i.val - 1)]
  apply Finset.univ.sum_congr rfl
  intro t ht
  simp only [f]
  rw [dif_pos (by omega)]
  simp only [p29UpperRowError]
  rw [dif_pos (by omega)]
  congr
  omega

private lemma p29_back_backward_error (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔU : P29Matrix n n,
      (∀ i j, |ΔU i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * p29BackSub fp n U b j = b i := by
  let x := p29BackSub fp n U b
  have hx : ∀ i, x i = p29BackRow fp n U b x i :=
    p29_back_sub_spec fp n U b
  have hrow : ∀ i : Fin n,
      ∃ (e : Fin (n - i.val - 1) → ℝ) (ediag : ℝ),
      (∀ t, |e t| ≤ p29Gamma fp.u n *
        |U i ⟨i.val + 1 + t.val, by omega⟩|) ∧
      |ediag| ≤ p29Gamma fp.u n * |U i i| ∧
      (U i i + ediag) * x i +
        (∑ t : Fin (n - i.val - 1),
          (U i ⟨i.val + 1 + t.val, by omega⟩ + e t) *
            x ⟨i.val + 1 + t.val, by omega⟩) = b i := by
    intro i
    obtain ⟨e, ediag, q, he, hed, hq, heq⟩ :=
      p29_rounded_row_backward fp n (n - i.val - 1) hvalid (by omega)
        (fun t => U i ⟨i.val + 1 + t.val, by omega⟩)
        (fun t => x ⟨i.val + 1 + t.val, by omega⟩)
        (b i) (U i i) (hdiag i)
    refine ⟨e, ediag, he, hed, ?_⟩
    have hxi := hx i
    dsimp only [p29BackRow] at hxi
    rw [← hq] at hxi
    rw [hxi]
    linarith
  choose e ediag he hed heq using hrow
  let ΔU : P29Matrix n n := fun i j => p29UpperRowError i (e i) (ediag i) j
  refine ⟨ΔU, ?_, ?_⟩
  · intro i j
    dsimp only [ΔU, p29UpperRowError]
    split_ifs with hgt heqi
    · have he' := he i ⟨j.val - i.val - 1, by omega⟩
      have hj : (⟨i.val + 1 + (j.val - i.val - 1), by omega⟩ : Fin n) = j := by
        apply Fin.ext
        simp
        omega
      rw [hj] at he'
      exact he'
    · subst j
      exact hed i
    · simp only [abs_zero]
      exact mul_nonneg (p29_gamma_nonneg fp.u n fp.u_nonneg hvalid) (abs_nonneg _)
  · intro i
    rw [p29_upper_row_sum U x i (e i) (ediag i) (hupper i)]
    exact heq i

private noncomputable def p29MatVec {m n : ℕ}
    (M : P29Matrix m n) (x : Fin n → ℝ) : Fin m → ℝ :=
  fun i => ∑ j : Fin n, M i j * x j

private lemma p29_matvec_matmul {m n p : ℕ}
    (A : P29Matrix m n) (B : P29Matrix n p) (x : Fin p → ℝ) :
    p29MatVec (p29MatMul A B) x = p29MatVec A (p29MatVec B x) := by
  funext i
  simp only [p29MatVec, p29MatMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.univ.sum_congr rfl
  intro k hk
  apply Finset.univ.sum_congr rfl
  intro j hj
  ring

private lemma p29_entry_norm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  positivity

private lemma p29_entry_le_norm {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    |A i j| ≤ ∑ j' : Fin n, |A i j'| := by
      exact Finset.single_le_sum (fun k hk => abs_nonneg (A i k)) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |A i' j'| := by
      exact Finset.single_le_sum
        (fun k hk => Finset.sum_nonneg (fun j' hj' => abs_nonneg (A k j')))
        (Finset.mem_univ i)

private lemma p29_entry_norm_of_component_bound {m n : ℕ}
    (X Y : P29Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, |X i j| ≤ c * |Y i j|) :
    p29EntryNorm X ≤ c * p29EntryNorm Y := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |X i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |Y i j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact h i j
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |Y i j| := by
      simp_rw [Finset.mul_sum]

private lemma p29_entry_norm_add {m n : ℕ} (X Y : P29Matrix m n) :
    p29EntryNorm (X + Y) ≤ p29EntryNorm X + p29EntryNorm Y := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |(X + Y) i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, (|X i j| + |Y i j|) := by
      gcongr with i j
      exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |X i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |Y i j| := by
      simp_rw [Finset.sum_add_distrib]

private lemma p29_entry_norm_matmul (n : ℕ)
    (X Y : P29Matrix n n) :
    p29EntryNorm (p29MatMul X Y) ≤
      (n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y := by
  have hxy : 0 ≤ p29EntryNorm X * p29EntryNorm Y :=
    mul_nonneg (p29_entry_norm_nonneg X) (p29_entry_norm_nonneg Y)
  have hij : ∀ i j : Fin n,
      |p29MatMul X Y i j| ≤ (n : ℝ) *
        (p29EntryNorm X * p29EntryNorm Y) := by
    intro i j
    unfold p29MatMul
    calc
      |∑ k : Fin n, X i k * Y k j| ≤
          ∑ k : Fin n, |X i k * Y k j| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun k : Fin n => X i k * Y k j) Finset.univ
      _ ≤ ∑ k : Fin n, p29EntryNorm X * p29EntryNorm Y := by
        gcongr with k
        rw [abs_mul]
        exact mul_le_mul (p29_entry_le_norm X i k)
          (p29_entry_le_norm Y k j) (abs_nonneg _) (p29_entry_norm_nonneg X)
      _ = (n : ℝ) * (p29EntryNorm X * p29EntryNorm Y) := by simp
  unfold p29EntryNorm
  calc
    (∑ i : Fin n, ∑ j : Fin n, |p29MatMul X Y i j|) ≤
        ∑ i : Fin n, ∑ j : Fin n,
          (n : ℝ) * (p29EntryNorm X * p29EntryNorm Y) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hij i j
    _ = (n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y := by
      simp
      ring

private lemma p29_entry_norm_triple (n : ℕ)
    (X Y Z : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
      (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y * p29EntryNorm Z := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul X Y) * p29EntryNorm Z :=
      p29_entry_norm_matmul n _ _
    _ ≤ (n : ℝ) ^ 3 *
        ((n : ℝ) ^ 3 * p29EntryNorm X * p29EntryNorm Y) *
          p29EntryNorm Z := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left (p29_entry_norm_matmul n X Y) (by positivity)
      · exact p29_entry_norm_nonneg Z
    _ = (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y *
        p29EntryNorm Z := by ring

private lemma p29_entry_norm_triple_mono (n : ℕ)
    (X Y Z : P29Matrix n n) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : p29EntryNorm X ≤ a) (hY : p29EntryNorm Y ≤ b)
    (hZ : p29EntryNorm Z ≤ c) :
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
      (n : ℝ) ^ 6 * a * b * c := by
  have hn : 0 ≤ (n : ℝ) ^ 6 := by positivity
  calc
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
        (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y * p29EntryNorm Z :=
      p29_entry_norm_triple n X Y Z
    _ ≤ (n : ℝ) ^ 6 * a * p29EntryNorm Y * p29EntryNorm Z := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hX hn
        · exact p29_entry_norm_nonneg Y
      · exact p29_entry_norm_nonneg Z
    _ ≤ (n : ℝ) ^ 6 * a * b * p29EntryNorm Z := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hY (mul_nonneg hn ha)
      · exact p29_entry_norm_nonneg Z
    _ ≤ (n : ℝ) ^ 6 * a * b * c := by
      exact mul_le_mul_of_nonneg_left hZ (mul_nonneg (mul_nonneg hn ha) hb)

private lemma p29_combined_backward_error_expand {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  unfold p29CombinedBackwardError p29PerturbedLDLT p29LDLT
  change ((L + ΔL) * (D + ΔD)) * (p29Transpose L + ΔU) -
      (L * D) * p29Transpose L =
    (ΔL * (D + ΔD)) * (p29Transpose L + ΔU) +
      (L * ΔD) * (p29Transpose L + ΔU) + (L * D) * ΔU
  noncomm_ring

private lemma p29_combined_backward_error_bound (fp : P29FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P29Matrix n n)
    (heta : 0 ≤ eta) (hvalid : P29GammaValid fp.u n)
    (hL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let g := p29Gamma fp.u n
  let Ln := p29EntryNorm L
  let Dn := p29EntryNorm D
  let Un := p29EntryNorm (p29Transpose L)
  have hg : 0 ≤ g := p29_gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hLn : 0 ≤ Ln := p29_entry_norm_nonneg L
  have hDn : 0 ≤ Dn := p29_entry_norm_nonneg D
  have hUn : 0 ≤ Un := p29_entry_norm_nonneg (p29Transpose L)
  have hΔL : p29EntryNorm ΔL ≤ g * Ln :=
    p29_entry_norm_of_component_bound ΔL L g hg hL
  have hΔU : p29EntryNorm ΔU ≤ g * Un :=
    p29_entry_norm_of_component_bound ΔU (p29Transpose L) g hg hU
  have hDplus : p29EntryNorm (D + ΔD) ≤ (1 + eta) * Dn := by
    calc
      p29EntryNorm (D + ΔD) ≤ p29EntryNorm D + p29EntryNorm ΔD :=
        p29_entry_norm_add D ΔD
      _ ≤ Dn + eta * Dn := by dsimp only [Dn]; linarith
      _ = (1 + eta) * Dn := by ring
  have hUplus : p29EntryNorm (p29Transpose L + ΔU) ≤ (1 + g) * Un := by
    calc
      p29EntryNorm (p29Transpose L + ΔU) ≤
          p29EntryNorm (p29Transpose L) + p29EntryNorm ΔU :=
        p29_entry_norm_add _ _
      _ ≤ Un + g * Un := by dsimp only [Un]; linarith
      _ = (1 + g) * Un := by ring
  let T1 := p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)
  let T2 := p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)
  let T3 := p29MatMul (p29MatMul L D) ΔU
  have hT1 : p29EntryNorm T1 ≤
      (n : ℝ) ^ 6 * (g * Ln) * ((1 + eta) * Dn) * ((1 + g) * Un) := by
    exact p29_entry_norm_triple_mono n ΔL (D + ΔD)
      (p29Transpose L + ΔU) (g * Ln) ((1 + eta) * Dn) ((1 + g) * Un)
      (mul_nonneg hg hLn) (mul_nonneg (by linarith) hDn) hΔL hDplus hUplus
  have hT2 : p29EntryNorm T2 ≤
      (n : ℝ) ^ 6 * Ln * (eta * Dn) * ((1 + g) * Un) := by
    exact p29_entry_norm_triple_mono n L ΔD (p29Transpose L + ΔU)
      Ln (eta * Dn) ((1 + g) * Un) hLn (mul_nonneg heta hDn)
      (le_refl _) hD hUplus
  have hT3 : p29EntryNorm T3 ≤
      (n : ℝ) ^ 6 * Ln * Dn * (g * Un) := by
    exact p29_entry_norm_triple_mono n L D ΔU Ln Dn (g * Un)
      hLn hDn (le_refl _) (le_refl _) hΔU
  rw [p29_combined_backward_error_expand]
  change p29EntryNorm (T1 + T2 + T3) ≤ _
  have hadd1 := p29_entry_norm_add (T1 + T2) T3
  have hadd2 := p29_entry_norm_add T1 T2
  unfold p29SolveBackwardFactor
  dsimp only [g, Ln, Dn, Un] at hT1 hT2 hT3 ⊢
  calc
    p29EntryNorm (T1 + T2 + T3) ≤
        p29EntryNorm (T1 + T2) + p29EntryNorm T3 := hadd1
    _ ≤ (p29EntryNorm T1 + p29EntryNorm T2) + p29EntryNorm T3 := by
      linarith
    _ ≤ ((n : ℝ) ^ 6 * (p29Gamma fp.u n * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          ((1 + p29Gamma fp.u n) * p29EntryNorm (p29Transpose L))) +
        ((n : ℝ) ^ 6 * p29EntryNorm L *
          (eta * p29EntryNorm D) *
          ((1 + p29Gamma fp.u n) * p29EntryNorm (p29Transpose L))) +
        ((n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (p29Gamma fp.u n * p29EntryNorm (p29Transpose L))) := by linarith
    _ = (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        p29EntryNorm (p29Transpose L) *
        (p29Gamma fp.u n * (1 + eta) * (1 + p29Gamma fp.u n) +
          eta * (1 + p29Gamma fp.u n) + p29Gamma fp.u n) := by ring

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
    p29_forward_backward_error fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  have htdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have htupper : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hback⟩ :=
    p29_back_backward_error fp n (p29Transpose L) z htdiag htupper hvalid
  let y := p29ForwardSub fp n L b
  let x := p29BackSub fp n (p29Transpose L) z
  have hforward' : p29MatVec (L + ΔL) y = b := by
    funext i
    simpa [p29MatVec, y] using hforward i
  have hblock' : p29MatVec (D + ΔD) z = y := by
    funext i
    simpa [p29MatVec, y] using hblock i
  have hback' : p29MatVec (p29Transpose L + ΔU) x = z := by
    funext i
    simpa [p29MatVec, x] using hback i
  have hpert : p29MatVec (p29PerturbedLDLT L D ΔL ΔD ΔU) x = b := by
    unfold p29PerturbedLDLT
    rw [p29_matvec_matmul, p29_matvec_matmul, hback', hblock', hforward']
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  have hAF : A + F = p29PerturbedLDLT L D ΔL ΔD ΔU := by
    dsimp only [F]
    unfold p29TotalBackwardError p29CombinedBackwardError
    rw [hfactor]
    abel
  have hsolve : ∀ i, ∑ j : Fin n, (A i j + F i j) * x j = b i := by
    intro i
    change p29MatVec (A + F) x i = b i
    rw [hAF]
    exact congrFun hpert i
  have hcombined := p29_combined_backward_error_bound fp n eta L D ΔL ΔD ΔU
    heta hvalid hΔL hΔD hΔU
  have hFnorm : p29EntryNorm F ≤
      p29TotalBackwardBound fp n eta factorEta A L D := by
    dsimp only [F]
    calc
      p29EntryNorm (p29TotalBackwardError E0 L D ΔL ΔD ΔU) ≤
          p29EntryNorm E0 + p29EntryNorm
            (p29CombinedBackwardError L D ΔL ΔD ΔU) := by
        unfold p29TotalBackwardError
        exact p29_entry_norm_add _ _
      _ ≤ factorEta * p29EntryNorm A + p29SolveBackwardFactor fp n eta L D := by
        exact add_le_add hE0 hcombined
      _ = p29TotalBackwardBound fp n eta factorEta A L D := by
        rfl
  exact ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl,
    by simpa [x] using hsolve, hFnorm⟩

end HighamBench
