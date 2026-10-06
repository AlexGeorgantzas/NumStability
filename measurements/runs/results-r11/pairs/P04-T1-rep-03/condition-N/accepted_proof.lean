import HighamBench.P04Definitions

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_step_le (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hvalid : GammaValid u (m + 1)) :
    gamma u m + u + gamma u m * u ≤ gamma u (m + 1) := by
  unfold GammaValid at hvalid
  have hm_le : (m : ℝ) * u ≤ ((m + 1 : ℕ) : ℝ) * u := by
    gcongr
    norm_num
  have hm : (m : ℝ) * u < 1 := lt_of_le_of_lt hm_le hvalid
  have hdm : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hm
  have hds : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  unfold gamma
  rw [show ((m : ℝ) * u / (1 - (m : ℝ) * u) + u +
        (m : ℝ) * u / (1 - (m : ℝ) * u) * u) =
      (((m + 1 : ℕ) : ℝ) * u) / (1 - (m : ℝ) * u) by
        field_simp [ne_of_gt hdm]
        push_cast
        ring]
  exact div_le_div_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hu)
    hds (by nlinarith)

private lemma p04_gamma_nonneg (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (sub_nonneg.mpr (le_of_lt hv))

private lemma p04_gamma_mono_nat (u : ℝ) {m M : ℕ}
    (hu : 0 ≤ u) (hmM : m ≤ M) (hv : GammaValid u M) :
    gamma u m ≤ gamma u M := by
  unfold GammaValid at hv
  have hmul : (m : ℝ) * u ≤ (M : ℝ) * u := by
    gcongr
  have hm : (m : ℝ) * u < 1 := lt_of_le_of_lt hmul hv
  unfold gamma
  rw [div_le_div_iff₀ (sub_pos.mpr hm) (sub_pos.mpr hv)]
  nlinarith

private lemma p04_gamma_valid_of_le (u : ℝ) {m M : ℕ}
    (hu : 0 ≤ u) (hmM : m ≤ M) (hv : GammaValid u M) :
    GammaValid u m := by
  unfold GammaValid at *
  have hmul : (m : ℝ) * u ≤ (M : ℝ) * u := by gcongr
  exact lt_of_le_of_lt hmul hv

private lemma p04_effective_nonneg (uBar uFma uOut : ℝ)
    (hbar : 0 ≤ uBar) (hfma : 0 ≤ uFma) (hout : 0 ≤ uOut) :
    0 ≤ p04EffectiveFmaRoundoff uBar uFma uOut := by
  unfold p04EffectiveFmaRoundoff
  split_ifs <;> positivity

private lemma p04_add_sub_one_le_mul {q b : ℕ} (hq : 0 < q) (hb : 0 < b) :
    q + b - 1 ≤ q * b := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add]
  omega

private lemma p04_prod_error_bound (u : ℝ) : ∀ (m : ℕ) (e : Fin m → ℝ),
    0 ≤ u → GammaValid u m → (∀ i, |e i| ≤ u) →
      |(∏ i : Fin m, (1 + e i)) - 1| ≤ gamma u m := by
  intro m
  induction m with
  | zero =>
      intro e hu hv he
      simp [gamma]
  | succ m ih =>
      intro e hu hv he
      have hv_m : GammaValid u m := by
        unfold GammaValid at hv ⊢
        have hle : (m : ℝ) * u ≤ ((m + 1 : ℕ) : ℝ) * u := by
          gcongr
          norm_num
        exact lt_of_le_of_lt hle hv
      have htail := ih (fun i : Fin m => e i.succ) hu hv_m (fun i => he i.succ)
      rw [Fin.prod_univ_succ]
      calc
        |(1 + e 0) * ∏ i : Fin m, (1 + e i.succ) - 1| =
            |((∏ i : Fin m, (1 + e i.succ)) - 1) + e 0 +
              e 0 * ((∏ i : Fin m, (1 + e i.succ)) - 1)| := by ring_nf
        _ ≤ |(∏ i : Fin m, (1 + e i.succ)) - 1| + |e 0| +
              |e 0| * |(∏ i : Fin m, (1 + e i.succ)) - 1| := by
            calc
              _ ≤ |(∏ i : Fin m, (1 + e i.succ)) - 1| + |e 0| +
                    |e 0 * ((∏ i : Fin m, (1 + e i.succ)) - 1)| := by
                  exact (abs_add_le _ _).trans
                    (add_le_add (abs_add_le _ _) le_rfl)
              _ = _ := by rw [abs_mul]
        _ ≤ gamma u m + u + u * gamma u m := by
            gcongr
            · exact he 0
            · exact he 0
        _ = gamma u m + u + gamma u m * u := by ring
        _ ≤ gamma u (m + 1) := p04_gamma_step_le u m hu hv

private lemma p04_finset_prod_error_bound {I : Type*} [DecidableEq I]
    (u : ℝ) (M : ℕ) (s : Finset I) (e : I → ℝ)
    (hu : 0 ≤ u) (hv : GammaValid u M) (hcard : s.card ≤ M)
    (he : ∀ i ∈ s, |e i| ≤ u) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u M := by
  have hvcard : GammaValid u s.card := by
    unfold GammaValid at hv ⊢
    have hmul : (s.card : ℝ) * u ≤ (M : ℝ) * u := by
      gcongr
    exact lt_of_le_of_lt hmul hv
  have hlocal : |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u s.card := by
    induction s using Finset.induction_on with
    | empty => simp [gamma]
    | @insert a s ha ih =>
        have hcard_s : s.card ≤ M := by
          rw [Finset.card_insert_of_notMem ha] at hcard
          omega
        have hvs : GammaValid u s.card := by
          unfold GammaValid at hvcard ⊢
          rw [Finset.card_insert_of_notMem ha] at hvcard
          have hle : (s.card : ℝ) * u ≤ ((s.card + 1 : ℕ) : ℝ) * u := by
            gcongr
            norm_num
          exact lt_of_le_of_lt hle hvcard
        have hvins : GammaValid u (s.card + 1) := by
          simpa [Finset.card_insert_of_notMem ha] using hvcard
        have his := ih hcard_s (fun i hi => he i (Finset.mem_insert_of_mem hi)) hvs
        rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
        calc
          |(1 + e a) * ∏ i ∈ s, (1 + e i) - 1| =
              |((∏ i ∈ s, (1 + e i)) - 1) + e a +
                e a * ((∏ i ∈ s, (1 + e i)) - 1)| := by ring_nf
          _ ≤ |(∏ i ∈ s, (1 + e i)) - 1| + |e a| +
                |e a| * |(∏ i ∈ s, (1 + e i)) - 1| := by
              calc
                _ ≤ |(∏ i ∈ s, (1 + e i)) - 1| + |e a| +
                      |e a * ((∏ i ∈ s, (1 + e i)) - 1)| := by
                    exact (abs_add_le _ _).trans
                      (add_le_add (abs_add_le _ _) le_rfl)
                _ = _ := by rw [abs_mul]
          _ ≤ gamma u s.card + u + u * gamma u s.card := by
              gcongr
              · exact he a (Finset.mem_insert_self a s)
              · exact he a (Finset.mem_insert_self a s)
          _ = gamma u s.card + u + gamma u s.card * u := by ring
          _ ≤ gamma u (s.card + 1) := p04_gamma_step_le u s.card hu hvins
  exact hlocal.trans (p04_gamma_mono_nat u hu hcard hv)

private lemma p04_affine_unroll (s t c d : ℕ → ℝ) : ∀ q : ℕ,
    s 0 = 0 →
    (∀ k, k < q → s (k + 1) = (s k * (1 + c k) + t k) * (1 + d k)) →
    s q = ∑ k ∈ Finset.range q,
      t k * (∏ l ∈ Finset.Ico (k + 1) q, (1 + c l)) *
        (∏ l ∈ Finset.Ico k q, (1 + d l)) := by
  intro q
  induction q with
  | zero =>
      intro hs hstep
      simpa using hs
  | succ q ih =>
      intro hs hstep
      have hi := ih hs (fun k hk => hstep k (Nat.lt.step hk))
      have hsum :
          (∑ k ∈ Finset.range q,
              t k * (∏ l ∈ Finset.Ico (k + 1) (q + 1), (1 + c l)) *
                (∏ l ∈ Finset.Ico k (q + 1), (1 + d l))) =
            (∑ k ∈ Finset.range q,
              t k * (∏ l ∈ Finset.Ico (k + 1) q, (1 + c l)) *
                (∏ l ∈ Finset.Ico k q, (1 + d l))) *
              ((1 + c q) * (1 + d q)) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hkq : k < q := Finset.mem_range.mp hk
        rw [Finset.prod_Ico_succ_top (Nat.succ_le_iff.mpr hkq),
          Finset.prod_Ico_succ_top (Nat.le_of_lt hkq)]
        ring
      rw [hstep q (Nat.lt_succ_self q), hi, Finset.sum_range_succ, hsum]
      simp
      ring

private lemma p04_run_unroll {n b q : ℕ} (run : P04BlockFmaDotRun n b q) :
    run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j *
        p04InclusiveErrorProduct run.delta k *
        ((1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k) := by
  let t : ℕ → ℝ := fun k =>
    if hk : k < q then
      ∑ j : Fin b, run.x ⟨k, hk⟩ j * run.y ⟨k, hk⟩ j *
        (1 + run.termTheta ⟨k, hk⟩ j)
    else 0
  have hu := p04_affine_unroll run.state t
    (p04ErrorAt run.carryTheta) (p04ErrorAt run.delta) q
    run.state_zero (by
      intro k hk
      simpa [t, p04ErrorAt, hk] using run.state_step ⟨k, hk⟩)
  unfold P04BlockFmaDotRun.computed
  rw [Finset.sum_range] at hu
  have hu' :
      run.state q = ∑ k : Fin q,
        (∑ j : Fin b, run.x k j * run.y k j * (1 + run.termTheta k j)) *
          p04StrictErrorProduct run.carryTheta k *
          p04InclusiveErrorProduct run.delta k := by
    simpa [t, p04StrictErrorProduct, p04InclusiveErrorProduct] using hu
  rw [hu']
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p04_factored_sum_error_bound {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (ga gb : ℝ)
    (hga : 0 ≤ ga) (hgb : 0 ≤ gb)
    (ha : ∀ k j, |alpha k j| ≤ ga)
    (hb : ∀ k j, |beta k j| ≤ gb) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (ga + gb + ga * gb) * p04BlockedAbsDot x y := by
  have hpoint : ∀ k j,
      |x k j * y k j - x k j * y k j *
          (1 + alpha k j) * (1 + beta k j)| ≤
        (ga + gb + ga * gb) * (|x k j| * |y k j|) := by
    intro k j
    have hab : |alpha k j + beta k j + alpha k j * beta k j| ≤
        ga + gb + ga * gb := by
      calc
        |alpha k j + beta k j + alpha k j * beta k j| ≤
            |alpha k j| + |beta k j| + |alpha k j * beta k j| := by
              exact (abs_add_le _ _).trans
                (add_le_add (abs_add_le _ _) le_rfl)
        _ = |alpha k j| + |beta k j| + |alpha k j| * |beta k j| := by
              rw [abs_mul]
        _ ≤ ga + gb + ga * gb := by
          gcongr
          · exact ha k j
          · exact hb k j
          · exact ha k j
          · exact hb k j
    calc
      |x k j * y k j - x k j * y k j *
          (1 + alpha k j) * (1 + beta k j)| =
          (|x k j| * |y k j|) *
            |alpha k j + beta k j + alpha k j * beta k j| := by
              rw [show x k j * y k j - x k j * y k j *
                    (1 + alpha k j) * (1 + beta k j) =
                  -(x k j * y k j) *
                    (alpha k j + beta k j + alpha k j * beta k j) by ring,
                abs_mul, abs_neg, abs_mul]
      _ ≤ (|x k j| * |y k j|) * (ga + gb + ga * gb) :=
        mul_le_mul_of_nonneg_left hab (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (ga + gb + ga * gb) * (|x k j| * |y k j|) := by ring
  unfold p04BlockedDot p04BlockedAbsDot
  calc
    |(∑ k : Fin q, ∑ j : Fin b, x k j * y k j) -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
      |∑ k : Fin q, ∑ j : Fin b,
        (x k j * y k j - x k j * y k j *
          (1 + alpha k j) * (1 + beta k j))| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k hk
            rw [← Finset.sum_sub_distrib]
    _ ≤ ∑ k : Fin q, |∑ j : Fin b,
        (x k j * y k j - x k j * y k j *
          (1 + alpha k j) * (1 + beta k j))| :=
            Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        |x k j * y k j - x k j * y k j *
          (1 + alpha k j) * (1 + beta k j)| := by
            apply Finset.sum_le_sum
            intro k hk
            exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        (ga + gb + ga * gb) * (|x k j| * |y k j|) := by
            apply Finset.sum_le_sum
            intro k hk
            apply Finset.sum_le_sum
            intro j hj
            exact hpoint k j
    _ = (ga + gb + ga * gb) *
        ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j| := by
          simp_rw [Finset.mul_sum]

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
  let uEff := p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut
  let alpha : Fin q → Fin b → ℝ := fun k _ =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have huEff : 0 ≤ uEff := p04_effective_nonneg _ _ _
    run.uBar_nonneg run.uFma_nonneg run.uOut_nonneg
  have hga : 0 ≤ gamma uEff q :=
    p04_gamma_nonneg _ _ huEff run.effective_gamma_valid
  have hgb : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg _ _ run.uBar_nonneg run.internal_gamma_valid
  have hrepr : run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j * (1 + alpha k j) * (1 + beta k j) := by
    rw [p04_run_unroll run]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    rw [← run.inner_path_factor k j]
    dsimp [alpha, beta]
    ring
  have halpha : ∀ k j, |alpha k j| ≤ gamma uEff q := by
    intro k j
    dsimp [alpha]
    unfold p04InclusiveErrorProduct
    apply p04_finset_prod_error_bound uEff q
    · exact huEff
    · exact run.effective_gamma_valid
    · simp
    · intro l hl
      have hlq : l < q := (Finset.mem_Ico.mp hl).2
      simp only [p04ErrorAt, dif_pos hlq]
      exact run.delta_bound ⟨l, hlq⟩
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    dsimp [beta]
    exact p04_prod_error_bound run.uBar n (run.innerPathError k j)
      run.uBar_nonneg run.internal_gamma_valid (run.inner_path_error_bound k j)
  have herror :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    rw [hrepr]
    simpa [p04BlockFmaCoeff] using
      p04_factored_sum_error_bound run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar n) hga hgb halpha hbeta
  refine ⟨alpha, beta, hrepr, halpha, hbeta, ?_, ?_, ?_⟩
  · simpa [uEff] using herror
  · intro horder
    have hlen : q + b - 1 ≤ n := by
      rw [run.dimension_eq]
      exact p04_add_sub_one_le_mul run.block_count_pos run.block_size_pos
    have hvrtl : GammaValid run.uBar (q + b - 1) :=
      p04_gamma_valid_of_le run.uBar run.uBar_nonneg hlen run.internal_gamma_valid
    have hgbrtl : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg _ _ run.uBar_nonneg hvrtl
    have hbetartl : ∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hp := p04_prod_error_bound run.uBar (q + b - 1)
        (run.rightToLeftPathError k j) run.uBar_nonneg hvrtl
        (run.right_to_left_path_error_bound horder k j)
      dsimp [beta]
      rw [run.inner_path_factor k j]
      rw [← run.right_to_left_path_factor horder k j]
      exact hp
    refine ⟨hbetartl, ?_⟩
    rw [hrepr]
    simpa [p04BlockFmaCoeff, uEff] using
      p04_factored_sum_error_bound run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar (q + b - 1))
        hga hgbrtl halpha hbetartl
  · rintro ⟨hout, hbarfma⟩
    have heff : uEff = 0 := by
      dsimp [uEff]
      simp [p04EffectiveFmaRoundoff, not_lt_of_ge hout, hbarfma.symm.le]
    have hdelta0 : ∀ k, run.delta k = 0 := by
      intro k
      have hd := run.delta_bound k
      rw [show p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut = 0 by
        simpa [uEff] using heff] at hd
      exact abs_eq_zero.mp (le_antisymm hd (abs_nonneg _))
    have halpha0 : ∀ k j, alpha k j = 0 := by
      intro k j
      dsimp [alpha]
      simp [p04InclusiveErrorProduct, p04ErrorAt, hdelta0]
    refine ⟨halpha0, ?_⟩
    rw [hrepr]
    simpa using
      p04_factored_sum_error_bound run.x run.y alpha beta
        0 (gamma run.uBar n) (by positivity) hgb
        (fun k j => by simp [halpha0 k j]) hbeta

end HighamBench
