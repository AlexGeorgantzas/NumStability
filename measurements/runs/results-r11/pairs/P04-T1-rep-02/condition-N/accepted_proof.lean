import HighamBench.P04Definitions

namespace HighamBench

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u m) :
    0 ≤ gamma u m := by
  unfold GammaValid at hvalid
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hvalid))

private lemma p04_gamma_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (m + 1)) :
    u + gamma u m + u * gamma u m ≤ gamma u (m + 1) := by
  have hvalid_m : GammaValid u m := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  have hden_m : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hvalid_m
  have hden_succ : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr hvalid
  have hid :
      u + gamma u m + u * gamma u m =
        (((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u) := by
    have hg : (1 - (m : ℝ) * u) * gamma u m = (m : ℝ) * u := by
      unfold gamma
      field_simp
    apply (eq_div_iff (ne_of_gt hden_m)).2
    calc
      (u + gamma u m + u * gamma u m) * (1 - (m : ℝ) * u) =
          u * (1 - (m : ℝ) * u) +
            (1 + u) * ((1 - (m : ℝ) * u) * gamma u m) := by ring
      _ = (((m + 1 : ℕ) : ℝ) * u) := by rw [hg]; push_cast; ring
  rw [hid]
  unfold gamma
  apply div_le_div_of_nonneg_left
  · positivity
  · exact hden_succ
  · push_cast
    nlinarith

private lemma p04_prod_error_bound (m : ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hvalid : GammaValid u m)
    (e : Fin m → ℝ) (he : ∀ i, |e i| ≤ u) :
    |(∏ i : Fin m, (1 + e i)) - 1| ≤ gamma u m := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
      have hvalid_m : GammaValid u m := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith
      let tail : Fin m → ℝ := fun i => e i.succ
      have htail : ∀ i, |tail i| ≤ u := fun i => he i.succ
      have hih := ih hvalid_m tail htail
      have hgm : 0 ≤ gamma u m := p04_gamma_nonneg hu hvalid_m
      rw [Fin.prod_univ_succ]
      let t : ℝ := ∏ i : Fin m, (1 + tail i)
      have ht : |t - 1| ≤ gamma u m := hih
      have htri :
          |(1 + e 0) * t - 1| ≤
            |e 0| + |t - 1| + |e 0| * |t - 1| := by
        have hid : (1 + e 0) * t - 1 = e 0 + (t - 1) + e 0 * (t - 1) := by ring
        rw [hid]
        calc
          |e 0 + (t - 1) + e 0 * (t - 1)|
              ≤ |e 0 + (t - 1)| + |e 0 * (t - 1)| := abs_add_le _ _
          _ = |e 0 + (t - 1)| + |e 0| * |t - 1| := by rw [abs_mul]
          _ ≤ (|e 0| + |t - 1|) + |e 0| * |t - 1| := by
            gcongr
            exact abs_add_le _ _
      calc
        |(1 + e 0) * t - 1|
            ≤ |e 0| + |t - 1| + |e 0| * |t - 1| := htri
        _ ≤ u + gamma u m + u * gamma u m := by
          have hmul : |e 0| * |t - 1| ≤ u * gamma u m :=
            mul_le_mul (he 0) ht (abs_nonneg _) hu
          linarith [he 0, ht]
        _ ≤ gamma u (m + 1) := p04_gamma_step hu hvalid

private lemma p04_gamma_mono {u : ℝ} {a m : ℕ}
    (hu : 0 ≤ u) (ham : a ≤ m) (hvalid : GammaValid u m) :
    gamma u a ≤ gamma u m := by
  have hnum : (a : ℝ) * u ≤ (m : ℝ) * u := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast ham) hu
  have hden : 1 - (m : ℝ) * u ≤ 1 - (a : ℝ) * u := by linarith
  have hden_pos : 0 < 1 - (m : ℝ) * u := by
    exact sub_pos.mpr hvalid
  unfold gamma
  exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg _) hu) hnum hden_pos hden

private lemma p04_finset_prod_error_bound (s : Finset ℕ) (u : ℝ)
    (hu : 0 ≤ u) (hvalid : GammaValid u s.card)
    (e : ℕ → ℝ) (he : ∀ i ∈ s, |e i| ≤ u) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u s.card := by
  induction s using Finset.induction_on with
  | empty => simp [gamma]
  | @insert a s ha ih =>
      have hvalid_succ : GammaValid u (s.card + 1) := by
        simpa [Finset.card_insert_of_notMem ha] using hvalid
      have hvalid_s : GammaValid u s.card := by
        unfold GammaValid at hvalid ⊢
        rw [Finset.card_insert_of_notMem ha] at hvalid
        push_cast at hvalid ⊢
        nlinarith
      have hih := ih hvalid_s (fun i hi => he i (Finset.mem_insert_of_mem hi))
      have hgm : 0 ≤ gamma u s.card := p04_gamma_nonneg hu hvalid_s
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      let t : ℝ := ∏ i ∈ s, (1 + e i)
      have ht : |t - 1| ≤ gamma u s.card := hih
      have hea : |e a| ≤ u := he a (Finset.mem_insert_self _ _)
      have htri :
          |(1 + e a) * t - 1| ≤
            |e a| + |t - 1| + |e a| * |t - 1| := by
        have hid : (1 + e a) * t - 1 = e a + (t - 1) + e a * (t - 1) := by ring
        rw [hid]
        calc
          |e a + (t - 1) + e a * (t - 1)|
              ≤ |e a + (t - 1)| + |e a * (t - 1)| := abs_add_le _ _
          _ = |e a + (t - 1)| + |e a| * |t - 1| := by rw [abs_mul]
          _ ≤ (|e a| + |t - 1|) + |e a| * |t - 1| := by
            gcongr
            exact abs_add_le _ _
      calc
        |(1 + e a) * t - 1|
            ≤ |e a| + |t - 1| + |e a| * |t - 1| := htri
        _ ≤ u + gamma u s.card + u * gamma u s.card := by
          have hmul : |e a| * |t - 1| ≤ u * gamma u s.card :=
            mul_le_mul hea ht (abs_nonneg _) hu
          linarith
        _ ≤ gamma u (s.card + 1) := p04_gamma_step hu hvalid_succ

private lemma p04_effective_nonneg (uBar uFma uOut : ℝ)
    (hFma : 0 ≤ uFma) (hOut : 0 ≤ uOut) :
    0 ≤ p04EffectiveFmaRoundoff uBar uFma uOut := by
  simp only [p04EffectiveFmaRoundoff]
  split_ifs <;> positivity

private noncomputable def p04ValueAt {q : ℕ} (a : Fin q → ℝ) (k : ℕ) : ℝ :=
  if h : k < q then a ⟨k, h⟩ else 0

private lemma p04_state_unroll {q : ℕ}
    (a carry delta : Fin q → ℝ) (state : ℕ → ℝ)
    (hzero : state 0 = 0)
    (hstep : ∀ k : Fin q,
      state (k.val + 1) =
        (state k.val * (1 + carry k) + a k) * (1 + delta k)) :
    state q = ∑ k : Fin q,
      a k * p04StrictErrorProduct carry k * p04InclusiveErrorProduct delta k := by
  have aux : ∀ t : ℕ, t ≤ q →
      state t = ∑ k ∈ Finset.range t,
        p04ValueAt a k *
          (∏ l ∈ Finset.Ico (k + 1) t, (1 + p04ErrorAt carry l)) *
          (∏ l ∈ Finset.Ico k t, (1 + p04ErrorAt delta l)) := by
    intro t
    induction t with
    | zero =>
        intro ht
        simpa using hzero
    | succ t ih =>
        intro ht
        have htq : t < q := Nat.lt_of_succ_le ht
        let ft : Fin q := ⟨t, htq⟩
        have hs := hstep ft
        have hi := ih (Nat.le_of_lt htq)
        have hcprod : ∀ k ∈ Finset.range t,
            (∏ l ∈ Finset.Ico (k + 1) (t + 1),
                (1 + p04ErrorAt carry l)) =
              (∏ l ∈ Finset.Ico (k + 1) t,
                (1 + p04ErrorAt carry l)) * (1 + carry ft) := by
          intro k hk
          rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hk))]
          simp [p04ErrorAt, ft, htq]
        have hdprod : ∀ k ∈ Finset.range t,
            (∏ l ∈ Finset.Ico k (t + 1),
                (1 + p04ErrorAt delta l)) =
              (∏ l ∈ Finset.Ico k t,
                (1 + p04ErrorAt delta l)) * (1 + delta ft) := by
          intro k hk
          rw [Finset.prod_Ico_succ_top (Nat.le_of_lt (Finset.mem_range.mp hk))]
          simp [p04ErrorAt, ft, htq]
        have hsum :
            (∑ k ∈ Finset.range t,
              p04ValueAt a k *
                (∏ l ∈ Finset.Ico (k + 1) (t + 1),
                  (1 + p04ErrorAt carry l)) *
                (∏ l ∈ Finset.Ico k (t + 1),
                  (1 + p04ErrorAt delta l))) =
              (∑ k ∈ Finset.range t,
                p04ValueAt a k *
                  (∏ l ∈ Finset.Ico (k + 1) t,
                    (1 + p04ErrorAt carry l)) *
                  (∏ l ∈ Finset.Ico k t,
                    (1 + p04ErrorAt delta l))) *
                (1 + carry ft) * (1 + delta ft) := by
          calc
            (∑ k ∈ Finset.range t,
              p04ValueAt a k *
                (∏ l ∈ Finset.Ico (k + 1) (t + 1),
                  (1 + p04ErrorAt carry l)) *
                (∏ l ∈ Finset.Ico k (t + 1),
                  (1 + p04ErrorAt delta l))) =
                ∑ k ∈ Finset.range t,
                  (p04ValueAt a k *
                    (∏ l ∈ Finset.Ico (k + 1) t,
                      (1 + p04ErrorAt carry l)) *
                    (∏ l ∈ Finset.Ico k t,
                      (1 + p04ErrorAt delta l))) *
                    (1 + carry ft) * (1 + delta ft) := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [hcprod k hk, hdprod k hk]
                      ring
            _ = (∑ k ∈ Finset.range t,
                  p04ValueAt a k *
                    (∏ l ∈ Finset.Ico (k + 1) t,
                      (1 + p04ErrorAt carry l)) *
                    (∏ l ∈ Finset.Ico k t,
                      (1 + p04ErrorAt delta l))) *
                    (1 + carry ft) * (1 + delta ft) := by
                      rw [Finset.sum_mul, Finset.sum_mul]
        rw [Finset.sum_range_succ, hsum]
        have ha : p04ValueAt a t = a ft := by simp [p04ValueAt, ft, htq]
        have hcnew :
            (∏ l ∈ Finset.Ico (t + 1) (t + 1),
              (1 + p04ErrorAt carry l)) = 1 := by simp
        have hdnew :
            (∏ l ∈ Finset.Ico t (t + 1),
              (1 + p04ErrorAt delta l)) = 1 + delta ft := by
          rw [Finset.prod_Ico_succ_top (Nat.le_refl t)]
          simp [p04ErrorAt, ft, htq]
        rw [ha, hcnew, hdnew]
        simp only [mul_one]
        have hs' :
            state (t + 1) =
              (state t * (1 + carry ft) + a ft) * (1 + delta ft) := by
          simpa [ft] using hs
        rw [hs', hi]
        ring
  rw [aux q le_rfl]
  rw [← Fin.sum_univ_eq_sum_range (fun k =>
    p04ValueAt a k *
      (∏ l ∈ Finset.Ico (k + 1) q, (1 + p04ErrorAt carry l)) *
      (∏ l ∈ Finset.Ico k q, (1 + p04ErrorAt delta l))) q]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [p04ValueAt, k.isLt, ↓reduceDIte]
  rfl

private lemma p04_gamma_valid_of_le {u : ℝ} {a m : ℕ}
    (hu : 0 ≤ u) (ham : a ≤ m) (hvalid : GammaValid u m) :
    GammaValid u a := by
  unfold GammaValid at hvalid ⊢
  have hcast : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
  nlinarith [mul_le_mul_of_nonneg_right hcast hu]

private lemma p04_factor_difference_bound
    (x y alpha beta A B : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (ha : |alpha| ≤ A) (hb : |beta| ≤ B) :
    |x * y - x * y * (1 + alpha) * (1 + beta)| ≤
      (A + B + A * B) * (|x| * |y|) := by
  have habmul : |alpha| * |beta| ≤ A * B :=
    mul_le_mul ha hb (abs_nonneg _) hA0
  have hab : |alpha + beta + alpha * beta| ≤ A + B + A * B := by
    calc
      |alpha + beta + alpha * beta|
          ≤ |alpha + beta| + |alpha * beta| := abs_add_le _ _
      _ = |alpha + beta| + |alpha| * |beta| := by rw [abs_mul]
      _ ≤ (|alpha| + |beta|) + |alpha| * |beta| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ A + B + A * B := by linarith
  have hxy : 0 ≤ |x| * |y| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  calc
    |x * y - x * y * (1 + alpha) * (1 + beta)| =
        (|x| * |y|) * |alpha + beta + alpha * beta| := by
          have hid :
              x * y - x * y * (1 + alpha) * (1 + beta) =
                -(x * y) * (alpha + beta + alpha * beta) := by ring
          rw [hid, abs_mul, abs_neg, abs_mul]
    _ ≤ (|x| * |y|) * (A + B + A * B) :=
      mul_le_mul_of_nonneg_left hab hxy
    _ = (A + B + A * B) * (|x| * |y|) := by ring

private lemma p04_blocked_factor_error_bound {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (A B : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (ha : ∀ k j, |alpha k j| ≤ A)
    (hb : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  let z : Fin q → Fin b → ℝ := fun k j =>
    x k j * y k j -
      x k j * y k j * (1 + alpha k j) * (1 + beta k j)
  have hz : ∀ k j,
      |z k j| ≤ (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    exact p04_factor_difference_bound _ _ _ _ _ _ hA0 hB0 (ha k j) (hb k j)
  rw [p04BlockedDot, p04BlockedAbsDot]
  have hdiff :
      (∑ k : Fin q, ∑ j : Fin b, x k j * y k j) -
          (∑ k : Fin q, ∑ j : Fin b,
            x k j * y k j * (1 + alpha k j) * (1 + beta k j)) =
        ∑ k : Fin q, ∑ j : Fin b, z k j := by
    simp only [z]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_sub_distrib]
  rw [hdiff]
  calc
    |∑ k : Fin q, ∑ j : Fin b, z k j|
        ≤ ∑ k : Fin q, |∑ j : Fin b, z k j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b, |z k j| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        (A + B + A * B) * (|x k j| * |y k j|) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      exact hz k j
    _ = (A + B + A * B) *
        (∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j|) := by
      simp only [Finset.mul_sum]

private lemma p04_add_sub_one_le_mul {q b : ℕ} (hq : 0 < q) (hb : 0 < b) :
    q + b - 1 ≤ q * b := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hq)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hb)
  have hid : (q + 1) + (b + 1) - 1 = q + b + 1 := by omega
  rw [hid]
  nlinarith [Nat.zero_le (q * b)]

theorem p04_t1_chained_rounding_factor
    {n b q : ℕ} (run : P04BlockFmaDotRun n b q) :
    ∃ alpha beta : Fin q → Fin b → ℝ,
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) ∧
      (∀ k j, |alpha k j| ≤
        gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q) ∧
      (∀ k j, |beta k j| ≤ gamma run.uBar n) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff
            (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
            run.uBar q n *
          p04BlockedAbsDot run.x run.y ∧
      (run.order = P04BlockEvaluationOrder.rightToLeft →
        (∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1)) ∧
        |p04BlockedDot run.x run.y - run.computed| ≤
          p04BlockFmaCoeff
              (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut)
              run.uBar q (q + b - 1) *
            p04BlockedAbsDot run.x run.y) ∧
      (run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
        (∀ k j, alpha k j = 0) ∧
        |p04BlockedDot run.x run.y - run.computed| ≤
          gamma run.uBar n * p04BlockedAbsDot run.x run.y) := by
  -- PROOF_START P04-T1-H001
  let uEff : ℝ := p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut
  let alpha : Fin q → Fin b → ℝ := fun k _ =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k - 1
  have huEff : 0 ≤ uEff :=
    p04_effective_nonneg _ _ _ run.uFma_nonneg run.uOut_nonneg
  have hA0 : 0 ≤ gamma uEff q :=
    p04_gamma_nonneg huEff run.effective_gamma_valid
  have hB0 : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have hunroll :
      run.state q = ∑ k : Fin q,
        (∑ j : Fin b,
          run.x k j * run.y k j * (1 + run.termTheta k j)) *
          p04StrictErrorProduct run.carryTheta k *
          p04InclusiveErrorProduct run.delta k := by
    apply p04_state_unroll
    · exact run.state_zero
    · intro k
      exact run.state_step k
  have hcomputed :
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) := by
    rw [P04BlockFmaDotRun.computed, hunroll]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [alpha, beta]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have halpha : ∀ k j, |alpha k j| ≤ gamma uEff q := by
    intro k j
    have he : ∀ l ∈ Finset.Ico k.val q,
        |p04ErrorAt run.delta l| ≤ uEff := by
      intro l hl
      have hlq : l < q := (Finset.mem_Ico.mp hl).2
      simp only [p04ErrorAt, hlq, ↓reduceDIte]
      exact run.delta_bound ⟨l, hlq⟩
    have hcard : (Finset.Ico k.val q).card ≤ q := by
      simp
    have hvalid_card : GammaValid uEff (Finset.Ico k.val q).card :=
      p04_gamma_valid_of_le huEff hcard run.effective_gamma_valid
    have hp := p04_finset_prod_error_bound
      (Finset.Ico k.val q) uEff huEff hvalid_card
      (p04ErrorAt run.delta) he
    have hm := p04_gamma_mono huEff hcard run.effective_gamma_valid
    exact hp.trans hm
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    have hp := p04_prod_error_bound n run.uBar run.uBar_nonneg
      run.internal_gamma_valid (run.innerPathError k j)
      (run.inner_path_error_bound k j)
    rw [run.inner_path_factor k j] at hp
    exact hp
  have herr :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    rw [hcomputed]
    simpa [p04BlockFmaCoeff] using
      (p04_blocked_factor_error_bound run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar n) hA0 hB0 halpha hbeta)
  refine ⟨alpha, beta, hcomputed, halpha, hbeta, herr, ?_, ?_⟩
  · intro horder
    have hshort : q + b - 1 ≤ n := by
      rw [run.dimension_eq]
      exact p04_add_sub_one_le_mul run.block_count_pos run.block_size_pos
    have hvalid_short : GammaValid run.uBar (q + b - 1) :=
      p04_gamma_valid_of_le run.uBar_nonneg hshort run.internal_gamma_valid
    have hBshort0 : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hvalid_short
    have hbeta_short : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hp := p04_prod_error_bound (q + b - 1) run.uBar
        run.uBar_nonneg hvalid_short (run.rightToLeftPathError k j)
        (run.right_to_left_path_error_bound horder k j)
      rw [run.right_to_left_path_factor horder k j] at hp
      exact hp
    refine ⟨hbeta_short, ?_⟩
    rw [hcomputed]
    simpa [p04BlockFmaCoeff] using
      (p04_blocked_factor_error_bound run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar (q + b - 1))
        hA0 hBshort0 halpha hbeta_short)
  · rintro ⟨hOut, hBar⟩
    have heff : uEff = 0 := by
      simp only [uEff, p04EffectiveFmaRoundoff]
      rw [if_neg (not_lt_of_ge hOut)]
      rw [if_pos]
      simpa [hBar]
    have hdelta : ∀ k, run.delta k = 0 := by
      intro k
      apply abs_eq_zero.mp
      have hd := run.delta_bound k
      rw [show p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut = 0 from heff] at hd
      exact le_antisymm hd (abs_nonneg _)
    have halpha_zero : ∀ k j, alpha k j = 0 := by
      intro k j
      simp [alpha, p04InclusiveErrorProduct, p04ErrorAt, hdelta]
    refine ⟨halpha_zero, ?_⟩
    rw [hcomputed]
    have htight := p04_blocked_factor_error_bound run.x run.y alpha beta
      0 (gamma run.uBar n) (le_refl 0) hB0
      (fun k j => by simp [halpha_zero k j]) hbeta
    simpa using htight

end HighamBench
