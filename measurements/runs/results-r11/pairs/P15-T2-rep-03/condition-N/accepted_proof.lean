import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u n) : 0 ≤ gamma u n := by
  rw [gamma]
  have hd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  positivity

private lemma p15_gamma_mono {u : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hkn : k ≤ n) (hvalid : GammaValid u n) :
    gamma u k ≤ gamma u n := by
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hkd : 0 < 1 - (k : ℝ) * u := by
    dsimp [GammaValid] at hvalid
    linarith
  have hnd : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  rw [gamma, gamma]
  apply (div_le_div_iff₀ hkd hnd).2
  nlinarith

private lemma p15_gamma_mul_step {u : ℝ} {k : ℕ} {e d : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + 1))
    (he : |e| ≤ gamma u k) (hd : |d| ≤ u) :
    |(1 + e) * (1 + d) - 1| ≤ gamma u (k + 1) := by
  have hkvalid : GammaValid u k := by
    dsimp [GammaValid] at hvalid ⊢
    have hc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ k
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  have hgn : 0 ≤ gamma u k := p15_gamma_nonneg hu hkvalid
  have hnum : gamma u k + u + gamma u k * u ≤ gamma u (k + 1) := by
    have hkd : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hkvalid
    have hsd : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
    rw [gamma, gamma]
    have heq :
        (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
              (k : ℝ) * u / (1 - (k : ℝ) * u) * u =
            ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
      field_simp [ne_of_gt hkd]
      ring
    rw [heq]
    norm_num [Nat.cast_add, Nat.cast_one] at hsd ⊢
    apply div_le_div_of_nonneg_left
    · positivity
    · exact sub_pos.mpr hsd
    · push_cast
      nlinarith
  calc
    |(1 + e) * (1 + d) - 1| = |e + d + e * d| := by ring_nf
    _ ≤ |e| + |d| + |e| * |d| := by
      calc
        |e + d + e * d| ≤ |e + d| + |e * d| := abs_add_le _ _
        _ ≤ (|e| + |d|) + |e| * |d| := by
          rw [abs_mul]
          gcongr
          exact abs_add_le e d
    _ ≤ gamma u k + u + gamma u k * u := by gcongr
    _ ≤ gamma u (k + 1) := hnum

private lemma p15_gamma_inv_step {u : ℝ} {k : ℕ} {a d : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (k + 1))
    (ha : |a - 1| ≤ gamma u k) (hd : |d| ≤ u) :
    |a / (1 + d) - 1| ≤ gamma u (k + 1) := by
  have hu_lt : u < 1 := by
    dsimp [GammaValid] at hvalid
    have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    nlinarith [mul_le_mul_of_nonneg_right hk1 hu]
  have hden : 0 < 1 + d := by
    have := (abs_le.mp hd).1
    linarith
  have hkvalid : GammaValid u k := by
    dsimp [GammaValid] at hvalid ⊢
    have hc : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ k
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  have hgn : 0 ≤ gamma u k := p15_gamma_nonneg hu hkvalid
  have hnum : (gamma u k + u) / (1 - u) ≤ gamma u (k + 1) := by
    have hud : 0 < 1 - u := sub_pos.mpr hu_lt
    have hkd : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hkvalid
    have hsd : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
    rw [gamma, gamma]
    apply (div_le_div_iff₀ hud hsd).2
    push_cast
    have hid :
        ((k : ℝ) + 1) * u * (1 - u) -
              ((k : ℝ) * u / (1 - (k : ℝ) * u) + u) *
                (1 - ((k : ℝ) + 1) * u) =
            (k : ℝ) * u ^ 2 / (1 - (k : ℝ) * u) := by
      field_simp [ne_of_gt hkd]
      ring
    rw [← sub_nonneg, hid]
    positivity
  rw [div_sub_one (ne_of_gt hden), abs_div, abs_of_pos hden]
  have htop : |a - (1 + d)| ≤ gamma u k + u := by
    calc
      |a - (1 + d)| = |(a - 1) - d| := by ring_nf
      _ ≤ |a - 1| + |d| := abs_sub _ _
      _ ≤ gamma u k + u := add_le_add ha hd
  calc
    |a - (1 + d)| / (1 + d) ≤ (gamma u k + u) / (1 + d) :=
      div_le_div_of_nonneg_right htop hden.le
    _ ≤ (gamma u k + u) / (1 - u) := by
      apply div_le_div_of_nonneg_left
      · positivity
      · linarith
      · linarith [(abs_le.mp hd).1]
    _ ≤ gamma u (k + 1) := hnum

private lemma p15_roundedDotProduct_backward (fp : StandardFPModel) :
    ∀ (n : ℕ) (A x : Fin n → ℝ), GammaValid fp.u n →
      ∃ e : Fin n → ℝ,
        (∀ j, |e j| ≤ gamma fp.u n) ∧
        roundedDotProduct fp n A x =
          ∑ j : Fin n, (A j * (1 + e j)) * x j := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      intro A x hn
      refine ⟨fun j => Fin.elim0 j, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · simp [roundedDotProduct]
  | one =>
      intro A x hn
      obtain ⟨d, hd, hmul⟩ := fp.model_mul (A 0) (x 0)
      refine ⟨fun _ => d, ?_, ?_⟩
      · intro j
        have hstep := p15_gamma_mul_step fp.u_nonneg hn
          (k := 0) (e := 0) (d := d) (by simp [gamma]) hd
        simpa using hstep
      · simp [roundedDotProduct, hmul]
        ring
  | more k ihk ihk1 =>
      intro A x hn
      let A' : Fin (k + 1) → ℝ := fun j => A j.castSucc
      let x' : Fin (k + 1) → ℝ := fun j => x j.castSucc
      have hn' : GammaValid fp.u (k + 1) := by
        dsimp [GammaValid] at hn ⊢
        have hc : ((k + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ (k + 1)
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      obtain ⟨e, he, heq⟩ := ihk1 A' x' hn'
      let last : Fin (k + 2) := Fin.last (k + 1)
      obtain ⟨dm, hdm, hmm⟩ := fp.model_mul (A last) (x last)
      obtain ⟨da, hda, hadd⟩ := fp.model_add
        (roundedDotProduct fp (k + 1) A' x')
        (fp.fl_mul (A last) (x last))
      let eLast : ℝ := (1 + dm) * (1 + da) - 1
      let eFull : Fin (k + 2) → ℝ :=
        Fin.lastCases eLast (fun j => (1 + e j) * (1 + da) - 1)
      refine ⟨eFull, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun q => ?_) j
        · dsimp [eFull, eLast]
          have hdm1 : |dm| ≤ gamma fp.u 1 := by
            have hs := p15_gamma_mul_step fp.u_nonneg
              (k := 0) (e := 0) (d := dm) (by
                dsimp [GammaValid] at hn ⊢
                norm_num
                calc
                  fp.u = (1 : ℝ) * fp.u := by ring
                  _ ≤ ((k + 2 : ℕ) : ℝ) * fp.u := by
                    apply mul_le_mul_of_nonneg_right _ fp.u_nonneg
                    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (k + 1))
                  _ < 1 := hn) (by simp [gamma]) hdm
            simpa using hs
          have htwo : GammaValid fp.u 2 := by
            dsimp [GammaValid] at hn ⊢
            have hc : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
              exact_mod_cast Nat.add_le_add_right (Nat.zero_le k) 2
            nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
          exact le_trans
            (by simpa using
              (p15_gamma_mul_step fp.u_nonneg htwo hdm1 hda))
            (p15_gamma_mono (k := 2) (n := k + 2)
              fp.u_nonneg (by omega) hn)
        · dsimp [eFull]
          simpa [Nat.add_assoc] using
            (p15_gamma_mul_step fp.u_nonneg hn (he q) hda)
      · rw [show roundedDotProduct fp (k + 2) A x =
              fp.fl_add (roundedDotProduct fp (k + 1) A' x')
                (fp.fl_mul (A last) (x last)) by
              simp [roundedDotProduct, Fin.foldl_succ_last, A', x', last]]
        rw [hadd, heq, hmm]
        rw [show
          (∑ j : Fin (k + 2), (A j * (1 + eFull j)) * x j) =
              (∑ j : Fin (k + 1),
                (A j.castSucc * (1 + eFull j.castSucc)) * x j.castSucc) +
              (A (Fin.last (k + 1)) *
                (1 + eFull (Fin.last (k + 1)))) *
                x (Fin.last (k + 1)) by
            exact Fin.sum_univ_castSucc _]
        dsimp [eFull, eLast, A', x', last]
        rw [add_mul, Finset.sum_mul]
        apply congrArg₂ (· + ·)
        · apply Finset.sum_congr rfl
          intro j hj
          rw [Fin.lastCases_castSucc]
          ring
        · rw [Fin.lastCases_last]
          ring

private lemma p15_frobNorm_le_of_entrywise {m n : ℕ}
    (E A : P15RectMatrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i j, |E i j| ≤ c * |A i j|) :
    p15RectFrobNorm E ≤ c * p15RectFrobNorm A := by
  have hs :
      (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
        c ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hij := h i j
    have hsq := (sq_le_sq₀ (abs_nonneg (E i j))
      (mul_nonneg hc (abs_nonneg (A i j)))).2 hij
    rw [sq_abs, mul_pow, sq_abs] at hsq
    exact hsq
  unfold p15RectFrobNorm
  calc
    Real.sqrt (∑ i : Fin m, ∑ j : Fin n, E i j ^ 2) ≤
        Real.sqrt (c ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
      Real.sqrt_le_sqrt hs
    _ = Real.sqrt (c ^ 2) *
        Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c)]
    _ = c * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_sq hc]

private lemma p15_roundedRectMatVec_backward (fp : StandardFPModel)
    {m n : ℕ} (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hn : GammaValid fp.u n) :
    ∃ ΔA : P15RectMatrix m n,
      p15RectFrobNorm ΔA ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A ΔA) x := by
  classical
  choose e he heq using fun i : Fin m =>
    p15_roundedDotProduct_backward fp n (A i) x hn
  let ΔA : P15RectMatrix m n := fun i j => A i j * e i j
  refine ⟨ΔA, ?_, ?_⟩
  · apply p15_frobNorm_le_of_entrywise ΔA A (gamma fp.u n)
      (p15_gamma_nonneg fp.u_nonneg hn)
    intro i j
    dsimp [ΔA]
    rw [abs_mul]
    calc
      |A i j| * |e i j| ≤ |A i j| * gamma fp.u n := by
        gcongr
        exact he i j
      _ = gamma fp.u n * |A i j| := by ring
  · funext i
    dsimp [p15RoundedRectMatVec, roundedMatVec, p15RectMatVec,
      p15RectAdd]
    rw [heq i]
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [ΔA]
    ring

private lemma p15_roundedSubFold_backward (fp : StandardFPModel) :
    ∀ (q : ℕ) (A x : Fin q → ℝ) (z : ℝ), GammaValid fp.u q →
      ∃ a : ℝ, ∃ d : Fin q → ℝ,
        |a - 1| ≤ gamma fp.u q ∧
        (∀ j, |d j| ≤ gamma fp.u q) ∧
        z = a * Fin.foldl q
              (fun acc j => fp.fl_sub acc (fp.fl_mul (A j) (x j))) z +
            ∑ j : Fin q, (1 + d j) * (A j * x j) := by
  intro q
  induction q with
  | zero =>
      intro A x z hq
      refine ⟨1, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
      · simp [gamma]
      · intro j
        exact Fin.elim0 j
      · simp
  | succ q ih =>
      intro A x z hq
      let A' : Fin q → ℝ := fun j => A j.castSucc
      let x' : Fin q → ℝ := fun j => x j.castSucc
      have hq' : GammaValid fp.u q := by
        dsimp [GammaValid] at hq ⊢
        have hc : (q : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_succ q
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      obtain ⟨a, d, ha, hd, heq⟩ := ih A' x' z hq'
      let last : Fin (q + 1) := Fin.last q
      let sPrev := Fin.foldl q
        (fun acc j => fp.fl_sub acc (fp.fl_mul (A' j) (x' j))) z
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (A last) (x last)
      obtain ⟨ds, hds, hsub⟩ := fp.model_sub sPrev
        (fp.fl_mul (A last) (x last))
      have hu_lt : fp.u < 1 := by
        dsimp [GammaValid] at hq
        have hone : (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
        nlinarith [mul_le_mul_of_nonneg_right hone fp.u_nonneg]
      have hden : 1 + ds ≠ 0 := by
        have := (abs_le.mp hds).1
        nlinarith
      let aNew := a / (1 + ds)
      let dLast := a * (1 + dm) - 1
      let dNew : Fin (q + 1) → ℝ := Fin.lastCases dLast d
      refine ⟨aNew, dNew, ?_, ?_, ?_⟩
      · dsimp [aNew]
        exact p15_gamma_inv_step fp.u_nonneg hq ha hds
      · intro j
        refine Fin.lastCases ?_ (fun t => ?_) j
        · dsimp [dNew, dLast]
          have hm := p15_gamma_mul_step fp.u_nonneg hq
            (e := a - 1) (d := dm) ha hdm
          rw [Fin.lastCases_last]
          convert hm using 1 <;> ring
        · rw [show dNew t.castSucc = d t by simp [dNew]]
          exact le_trans (hd t)
            (p15_gamma_mono fp.u_nonneg (Nat.le_succ q) hq)
      · calc
          z = a * sPrev +
                ∑ j : Fin q, (1 + d j) * (A' j * x' j) := heq
          _ = aNew * Fin.foldl (q + 1)
                  (fun acc j => fp.fl_sub acc (fp.fl_mul (A j) (x j))) z +
                ∑ j : Fin (q + 1), (1 + dNew j) * (A j * x j) := by
            rw [show
              Fin.foldl (q + 1)
                  (fun acc j => fp.fl_sub acc (fp.fl_mul (A j) (x j))) z =
                fp.fl_sub sPrev (fp.fl_mul (A last) (x last)) by
                  simp [Fin.foldl_succ_last, sPrev, A', x', last]]
            rw [show
              (∑ j : Fin (q + 1), (1 + dNew j) * (A j * x j)) =
                  (∑ j : Fin q,
                    (1 + dNew j.castSucc) *
                      (A j.castSucc * x j.castSucc)) +
                  (1 + dNew (Fin.last q)) *
                    (A (Fin.last q) * x (Fin.last q)) by
                exact Fin.sum_univ_castSucc _]
            dsimp [aNew, dNew, dLast, A', x', last]
            rw [Fin.lastCases_last]
            have hpref :
                (∑ j : Fin q, (1 + d j) *
                    (A j.castSucc * x j.castSucc)) =
                  ∑ j : Fin q,
                    (1 + Fin.lastCases (a * (1 + dm) - 1) d j.castSucc) *
                      (A j.castSucc * x j.castSucc) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [Fin.lastCases_castSucc]
            rw [← hpref, hsub, hmul]
            field_simp [hden]
            ring

private noncomputable def p15ForwardRow (fp : StandardFPModel) (n : ℕ)
    (L : P15Matrix n) (v x : P15Vector n) (i : Fin n) : ℝ :=
  fp.fl_div
    (Fin.foldl i.val
      (fun acc (t : Fin i.val) =>
        fp.fl_sub acc
          (fp.fl_mul (L i ⟨t.val, lt_trans t.isLt i.isLt⟩)
            (x ⟨t.val, lt_trans t.isLt i.isLt⟩)))
      (v i))
    (L i i)

private lemma p15ForwardRow_update_of_le (fp : StandardFPModel) {n : ℕ}
    (L : P15Matrix n) (v x : P15Vector n) (i q : Fin n) (z : ℝ)
    (hiq : i.val ≤ q.val) :
    p15ForwardRow fp n L v (Function.update x q z) i =
      p15ForwardRow fp n L v x i := by
  classical
  unfold p15ForwardRow
  congr 2
  funext acc t
  rw [Function.update_apply, if_neg]
  intro he
  have hval : t.val = q.val := congrArg Fin.val he
  omega

private lemma p15_roundedForwardSubSteps_spec (fp : StandardFPModel)
    (n : ℕ) (L : P15Matrix n) (v : P15Vector n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : P15Vector n),
      (∀ i, i.val < n - k → x i = p15ForwardRow fp n L v x i) →
      let y := roundedForwardSubSteps fp n L v k hk x
      ∀ i, y i = p15ForwardRow fp n L v y i := by
  intro k
  induction k with
  | zero =>
      intro hk x hx
      simp only [roundedForwardSubSteps]
      intro i
      apply hx i
      omega
  | succ k ih =>
      intro hk x hx
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (v ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      have hx' : ∀ i, i.val < n - k →
          x' i = p15ForwardRow fp n L v x' i := by
        intro i hi
        have hile : i.val ≤ ik.val := by
          dsimp [ik]
          omega
        rw [p15ForwardRow_update_of_le fp L v x i ik
          (fp.fl_div s (L ik ik)) hile]
        dsimp only [x']
        by_cases hieq : i = ik
        · subst i
          rw [Function.update_self]
          dsimp [p15ForwardRow, s, ik]
        · rw [Function.update_apply, if_neg hieq]
          apply hx
          dsimp [ik] at hieq ⊢
          have hne : i.val ≠ n - k - 1 := by
            intro hval
            apply hieq
            exact Fin.ext hval
          omega
      simpa only [roundedForwardSubSteps, ik, s, x'] using
        ih (Nat.le_of_succ_le hk) x' hx'

private lemma p15_roundedForwardSub_spec (fp : StandardFPModel)
    (n : ℕ) (L : P15Matrix n) (v : P15Vector n) :
    ∀ i, roundedForwardSub fp n L v i =
      p15ForwardRow fp n L v (roundedForwardSub fp n L v) i := by
  have h := p15_roundedForwardSubSteps_spec fp n L v n (le_refl n)
    (fun _ => 0) (by
      intro i hi
      omega)
  simpa [roundedForwardSub] using h

private lemma p15_sum_eq_prefix_add_diagonal {n : ℕ} (i : Fin n)
    (F : Fin n → ℝ) (hzero : ∀ j, i.val < j.val → F j = 0) :
    (∑ j : Fin n, F j) =
      (∑ t : Fin i.val, F ⟨t.val, lt_trans t.isLt i.isLt⟩) + F i := by
  classical
  let emb : Fin i.val → Fin n :=
    fun t => ⟨t.val, lt_trans t.isLt i.isLt⟩
  let e : Fin i.val ≃ {j : Fin n // j < i} := {
    toFun := fun t => ⟨emb t, by
      show (emb t).val < i.val
      exact t.isLt⟩
    invFun := fun j => ⟨j.val, by exact j.property⟩
    left_inv := by intro t; ext; rfl
    right_inv := by intro j; ext; rfl
  }
  have hprefix :
      (∑ t : Fin i.val, F (emb t)) =
        (Finset.Iio i).sum F := by
    rw [Finset.sum_subtype (p := fun j : Fin n => j < i)
      (Finset.Iio i) (by simp) F]
    exact e.sum_comp (fun j => F j.val)
  have hrestrict :
      (Finset.Iic i).sum F = ∑ j : Fin n, F j := by
    apply Finset.sum_subset (by simp)
    intro j hj hji
    apply hzero j
    simpa using hji
  rw [← hrestrict, Finset.Iic_eq_cons_Iio]
  simp only [Finset.sum_cons]
  rw [← hprefix]
  dsimp [emb]
  ring

private lemma p15_roundedForwardSub_backward (fp : StandardFPModel)
    (n : ℕ) (L : P15Matrix n) (v : P15Vector n)
    (hdiag : ∀ i, L i i ≠ 0) (hlower : p15LowerTriangular L)
    (hn : GammaValid fp.u n) :
    let x := roundedForwardSub fp n L v
    ∃ ΔL : P15Matrix n,
      p15RectFrobNorm ΔL ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L ΔL) x = v := by
  classical
  let x := roundedForwardSub fp n L v
  have hrow : ∀ i : Fin n, ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ gamma fp.u n) ∧
      (∑ j : Fin n, (L i j * (1 + e j)) * x j) = v i := by
    intro i
    let emb : Fin i.val → Fin n :=
      fun t => ⟨t.val, lt_trans t.isLt i.isLt⟩
    let A : Fin i.val → ℝ := fun t => L i (emb t)
    let xp : Fin i.val → ℝ := fun t => x (emb t)
    let s := Fin.foldl i.val
      (fun acc t => fp.fl_sub acc (fp.fl_mul (A t) (xp t))) (v i)
    have hiValid : GammaValid fp.u i.val := by
      dsimp [GammaValid] at hn ⊢
      have hc : (i.val : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast Nat.le_of_lt i.isLt
      nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
    have hi1Valid : GammaValid fp.u (i.val + 1) := by
      dsimp [GammaValid] at hn ⊢
      have hc : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast i.isLt
      nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
    obtain ⟨a, d, ha, hd, hfold⟩ :=
      p15_roundedSubFold_backward fp i.val A xp (v i) hiValid
    obtain ⟨dd, hdd, hdiv⟩ := fp.model_div s (L i i) (hdiag i)
    have hxdiv : x i = fp.fl_div s (L i i) := by
      have hs := p15_roundedForwardSub_spec fp n L v i
      simpa [x, p15ForwardRow, s, A, xp, emb] using hs
    have hu_lt : fp.u < 1 := by
      dsimp [GammaValid] at hi1Valid
      have hone : (1 : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le i.val)
      nlinarith [mul_le_mul_of_nonneg_right hone fp.u_nonneg]
    have hden : 1 + dd ≠ 0 := by
      have := (abs_le.mp hdd).1
      nlinarith
    have hs : s = L i i * x i / (1 + dd) := by
      rw [hxdiv, hdiv]
      field_simp [hdiag i, hden]
    let diagErr := a / (1 + dd) - 1
    let e : Fin n → ℝ := fun j =>
      if hji : j.val < i.val then d ⟨j.val, hji⟩
      else if j = i then diagErr else 0
    refine ⟨e, ?_, ?_⟩
    · intro j
      dsimp [e]
      split_ifs with hji hji
      · exact le_trans (hd ⟨j.val, hji⟩)
          (p15_gamma_mono fp.u_nonneg
            (Nat.le_of_lt i.isLt) hn)
      · dsimp [diagErr]
        exact le_trans
          (p15_gamma_inv_step fp.u_nonneg hi1Valid ha hdd)
          (p15_gamma_mono fp.u_nonneg
            (Nat.succ_le_iff.mpr i.isLt) hn)
      · simpa using p15_gamma_nonneg fp.u_nonneg hn
    · rw [p15_sum_eq_prefix_add_diagonal i
          (fun j => (L i j * (1 + e j)) * x j) (by
            intro j hij
            change L i j * (1 + e j) * x j = 0
            rw [hlower i j hij]
            ring)]
      have hprefix :
          (∑ t : Fin i.val,
              (L i (emb t) * (1 + e (emb t))) * x (emb t)) =
            ∑ t : Fin i.val, (1 + d t) * (A t * xp t) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hlt : (emb t).val < i.val := by
          dsimp [emb]
          exact t.isLt
        rw [show e (emb t) = d t by
          simp only [e, dif_pos hlt]
          congr]
        dsimp [A, xp]
        ring
      rw [hprefix]
      have hei : e i = diagErr := by
        simp [e]
      rw [hei]
      dsimp [diagErr]
      rw [hfold]
      change
        (∑ t : Fin i.val, (1 + d t) * (A t * xp t)) +
            L i i * (1 + (a / (1 + dd) - 1)) * x i =
          a * s + ∑ t : Fin i.val, (1 + d t) * (A t * xp t)
      rw [hs]
      field_simp [hden]
      ring
  choose e he heq using hrow
  let ΔL : P15Matrix n := fun i j => L i j * e i j
  refine ⟨ΔL, ?_, ?_⟩
  · apply p15_frobNorm_le_of_entrywise ΔL L (gamma fp.u n)
      (p15_gamma_nonneg fp.u_nonneg hn)
    intro i j
    dsimp [ΔL]
    rw [abs_mul]
    calc
      |L i j| * |e i j| ≤ |L i j| * gamma fp.u n := by
        gcongr
        exact he i j
      _ = gamma fp.u n * |L i j| := by ring
  · funext i
    dsimp [p15RectMatVec, p15RectAdd, ΔL]
    rw [← heq i]
    apply Finset.sum_congr rfl
    intro j hj
    ring

private lemma p15_rectMatVec_mul_assoc {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- P15-T2: the two-block instance of equation (4.22) in the proof of
Theorem 4.4, with the source's low-rank and triangular-solve perturbations. -/
theorem p15_t2_two_block_equation_4_22
    {b r : ℕ} (fp : StandardFPModel)
    (T₀ T₁ : P15Matrix b) (X Y : P15RectMatrix b r)
    (v₀ v₁ : P15Vector b)
    (hT₀diag : ∀ i, T₀ i i ≠ 0)
    (hT₁diag : ∀ i, T₁ i i ≠ 0)
    (hT₀lower : p15LowerTriangular T₀)
    (hT₁lower : p15LowerTriangular T₁)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let rhsHat := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
    let x₁ := roundedForwardSub fp b T₁ rhsHat
    ∃ ΔT₀ : P15Matrix b, ∃ ΔYT : P15RectMatrix r b,
      ∃ ΔX : P15RectMatrix b r, ∃ θ : P15Vector b,
      ∃ ΔT₁ : P15Matrix b, ∃ ΔT₁₀ : P15Matrix b,
        p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ ∧
        p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
        p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
        (∀ i, |θ i| ≤ fp.u) ∧
        p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ ∧
        p15RectMatVec (p15RectAdd T₀ ΔT₀) x₀ = v₀ ∧
        wInner = p15RectMatVec
          (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ ∧
        wHat = p15RectMatVec (p15RectAdd X ΔX) wInner ∧
        (∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i)) ∧
        p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ = rhsHat ∧
        (∀ i j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j) ∧
        ∀ i,
          p15RectMatVec
                (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
              p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
            v₁ i * (1 + θ i) := by
  -- PROOF_START P15-T2-H001
  classical
  dsimp only
  let x₀ := roundedForwardSub fp b T₀ v₀
  let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  let wHat := p15RoundedRectMatVec fp X wInner
  let rhsHat : P15Vector b := fun i => fp.fl_sub (v₁ i) (wHat i)
  let x₁ := roundedForwardSub fp b T₁ rhsHat
  obtain ⟨ΔT₀, hΔT₀, hx₀⟩ :=
    p15_roundedForwardSub_backward fp b T₀ v₀
      hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hwInner⟩ :=
    p15_roundedRectMatVec_backward fp (p15RectTranspose Y) x₀ hb
  obtain ⟨ΔX, hΔX, hwHat⟩ :=
    p15_roundedRectMatVec_backward fp X wInner hr
  choose θ hθ hrhs using fun i : Fin b => fp.model_sub (v₁ i) (wHat i)
  obtain ⟨ΔT₁, hΔT₁, hx₁⟩ :=
    p15_roundedForwardSub_backward fp b T₁ rhsHat
      hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j =>
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  have hT₁₀ : ∀ i j,
      p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
        (1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
    intro i j
    dsimp [p15RectAdd, ΔT₁₀]
    ring
  have hcross : ∀ i,
      p15RectMatVec
          (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
        (1 + θ i) * wHat i := by
    intro i
    calc
      p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          p15RectMatVec
            (fun q j => (1 + θ q) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) q j) x₀ i := by
            unfold p15RectMatVec
            apply Finset.sum_congr rfl
            intro j hj
            rw [hT₁₀]
      _ = (1 + θ i) *
          p15RectMatVec
            (p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i := by
            unfold p15RectMatVec
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ = (1 + θ i) * wHat i := by
            rw [p15_rectMatVec_mul_assoc]
            rw [← hwInner, ← hwHat]
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, hx₀, hwInner, hwHat, hrhs,
    hx₁, hT₁₀, ?_⟩
  intro i
  rw [hcross i, congrFun hx₁ i]
  change (1 + θ i) * wHat i + fp.fl_sub (v₁ i) (wHat i) =
    v₁ i * (1 + θ i)
  rw [hrhs i]
  ring

end HighamBench
