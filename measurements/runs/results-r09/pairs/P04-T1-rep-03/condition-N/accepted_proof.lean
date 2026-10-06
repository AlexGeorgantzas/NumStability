import HighamBench.P04Definitions

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold GammaValid at hv
  unfold gamma
  have hd : 0 < 1 - (m : ℝ) * u := by linarith
  positivity

private lemma p04_gamma_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (m + 1)) :
    gamma u m * (1 + u) + u ≤ gamma u (m + 1) := by
  unfold GammaValid at hv
  have hdm : 0 < 1 - (m : ℝ) * u := by
    norm_num [Nat.cast_add, Nat.cast_one] at hv ⊢
    nlinarith
  have hdms : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr hv
  have hrec :
      gamma u m * (1 + u) + u =
        ((m + 1 : ℕ) : ℝ) * u / (1 - (m : ℝ) * u) := by
    unfold gamma
    have hne : 1 - (m : ℝ) * u ≠ 0 := ne_of_gt hdm
    field_simp
    push_cast
    ring
  rw [hrec]
  unfold gamma
  apply div_le_div_of_nonneg_left
  · positivity
  · exact hdms
  · norm_num [Nat.cast_add, Nat.cast_one]
    nlinarith

private lemma p04_abs_prod_sub_one_le_gamma :
    ∀ (m : ℕ) (e : Fin m → ℝ) (u : ℝ),
      0 ≤ u → GammaValid u m → (∀ i, |e i| ≤ u) →
      |(∏ i, (1 + e i)) - 1| ≤ gamma u m := by
  intro m
  induction m with
  | zero =>
      intro e u hu hv he
      simp [gamma]
  | succ m ih =>
      intro e u hu hv he
      have hv' : GammaValid u m := by
        unfold GammaValid at hv ⊢
        norm_num [Nat.cast_add, Nat.cast_one] at hv ⊢
        nlinarith
      have hp := ih (fun i : Fin m => e i.succ) u hu hv'
        (fun i => he i.succ)
      have he0 := he (0 : Fin (m + 1))
      have h_one : |1 + e 0| ≤ 1 + u := by
        calc
          |1 + e 0| ≤ |(1 : ℝ)| + |e 0| := abs_add_le _ _
          _ ≤ 1 + u := by simpa using add_le_add_left he0 1
      have hgamma := p04_gamma_nonneg hu hv'
      calc
        |(∏ i, (1 + e i)) - 1| =
            |(1 + e 0) * (∏ i : Fin m, (1 + e i.succ)) - 1| := by
              rw [Fin.prod_univ_succ]
        _ = |((∏ i : Fin m, (1 + e i.succ)) - 1) * (1 + e 0) + e 0| := by
              congr 1
              ring
        _ ≤ |(∏ i : Fin m, (1 + e i.succ)) - 1| * |1 + e 0| + |e 0| := by
              simpa [abs_mul] using
                (abs_add_le
                  (((∏ i : Fin m, (1 + e i.succ)) - 1) * (1 + e 0))
                  (e 0))
        _ ≤ gamma u m * (1 + u) + u := by
              gcongr
        _ ≤ gamma u (m + 1) := p04_gamma_step hu hv

private noncomputable def p04PrefixProduct {q : ℕ}
    (e : Fin q → ℝ) (a t : ℕ) : ℝ :=
  ∏ l ∈ Finset.Ico a t, (1 + p04ErrorAt e l)

private noncomputable def p04RunTermAt {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (k : ℕ) : ℝ :=
  if h : k < q then
    ∑ j : Fin b,
      run.x ⟨k, h⟩ j * run.y ⟨k, h⟩ j * (1 + run.termTheta ⟨k, h⟩ j)
  else 0

private lemma p04_prefix_product_succ {q a t : ℕ} (e : Fin q → ℝ)
    (h : a ≤ t) :
    p04PrefixProduct e a (t + 1) =
      p04PrefixProduct e a t * (1 + p04ErrorAt e t) := by
  unfold p04PrefixProduct
  exact Finset.prod_Ico_succ_top h _

private lemma p04_state_prefix {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    ∀ t : ℕ, t ≤ q →
      run.state t =
        ∑ k : Fin t,
          p04RunTermAt run k.val *
            p04PrefixProduct run.delta k.val t *
            p04PrefixProduct run.carryTheta (k.val + 1) t := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp [run.state_zero]
  | succ t ih =>
      intro ht
      have htq : t < q := by omega
      have htle : t ≤ q := by omega
      have hdelta : p04ErrorAt run.delta t = run.delta ⟨t, htq⟩ := by
        simp [p04ErrorAt, htq]
      have hcarry : p04ErrorAt run.carryTheta t = run.carryTheta ⟨t, htq⟩ := by
        simp [p04ErrorAt, htq]
      have hterm : p04RunTermAt run t =
          ∑ j : Fin b,
            run.x ⟨t, htq⟩ j * run.y ⟨t, htq⟩ j *
              (1 + run.termTheta ⟨t, htq⟩ j) := by
        simp [p04RunTermAt, htq]
      rw [run.state_step ⟨t, htq⟩, ih htle]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      rw [hterm]
      have hlast_delta : p04PrefixProduct run.delta t (t + 1) =
          1 + run.delta ⟨t, htq⟩ := by
        rw [p04_prefix_product_succ run.delta (le_refl t), hdelta]
        simp [p04PrefixProduct]
      have hlast_carry : p04PrefixProduct run.carryTheta (t + 1) (t + 1) = 1 := by
        simp [p04PrefixProduct]
      rw [hlast_delta, hlast_carry, mul_one]
      have hold_delta : ∀ k : Fin t,
          p04PrefixProduct run.delta k.val (t + 1) =
            p04PrefixProduct run.delta k.val t * (1 + run.delta ⟨t, htq⟩) := by
        intro k
        rw [p04_prefix_product_succ run.delta (by omega), hdelta]
      have hold_carry : ∀ k : Fin t,
          p04PrefixProduct run.carryTheta (k.val + 1) (t + 1) =
            p04PrefixProduct run.carryTheta (k.val + 1) t *
              (1 + run.carryTheta ⟨t, htq⟩) := by
        intro k
        rw [p04_prefix_product_succ run.carryTheta (by omega), hcarry]
      rw [Finset.sum_mul]
      rw [add_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [hold_delta k, hold_carry k]
        ring

private lemma p04_state_unroll {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed =
      ∑ k : Fin q,
        (∑ j : Fin b,
          run.x k j * run.y k j * (1 + run.termTheta k j)) *
          p04InclusiveErrorProduct run.delta k *
          p04StrictErrorProduct run.carryTheta k := by
  rw [P04BlockFmaDotRun.computed, p04_state_prefix run q (le_refl q)]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [p04RunTermAt, dif_pos k.isLt]
  unfold p04InclusiveErrorProduct p04StrictErrorProduct p04PrefixProduct
  rfl

private lemma p04_gamma_mono_nat {u : ℝ} {a m : ℕ}
    (hu : 0 ≤ u) (ham : a ≤ m) (hv : GammaValid u m) :
    gamma u a ≤ gamma u m := by
  unfold GammaValid at hv
  have hau : (a : ℝ) * u ≤ (m : ℝ) * u := by
    gcongr
  have hda : 0 < 1 - (a : ℝ) * u := by linarith
  have hdm : 0 < 1 - (m : ℝ) * u := by linarith
  unfold gamma
  apply (div_le_div_iff₀ hda hdm).2
  nlinarith

private lemma p04_abs_finset_prod_sub_one_le_gamma
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (hv : GammaValid u s.card)
    (he : ∀ i ∈ s, |e i| ≤ u) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u s.card := by
  induction s using Finset.induction with
  | empty => simp [gamma]
  | @insert a s ha ih =>
      have hvsucc : GammaValid u (s.card + 1) := by
        simpa [Finset.card_insert_of_notMem ha] using hv
      have hv' : GammaValid u s.card := by
        unfold GammaValid at hv ⊢
        rw [Finset.card_insert_of_notMem ha] at hv
        norm_num [Nat.cast_add, Nat.cast_one] at hv ⊢
        nlinarith
      have hp := ih hv' (fun i hi => he i (Finset.mem_insert_of_mem hi))
      have hea := he a (Finset.mem_insert_self a s)
      have h_one : |1 + e a| ≤ 1 + u := by
        calc
          |1 + e a| ≤ |(1 : ℝ)| + |e a| := abs_add_le _ _
          _ ≤ 1 + u := by simpa using add_le_add_left hea 1
      have hgamma := p04_gamma_nonneg hu hv'
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      calc
        |(1 + e a) * (∏ i ∈ s, (1 + e i)) - 1| =
            |((∏ i ∈ s, (1 + e i)) - 1) * (1 + e a) + e a| := by
              congr 1
              ring
        _ ≤ |(∏ i ∈ s, (1 + e i)) - 1| * |1 + e a| + |e a| := by
              simpa [abs_mul] using
                (abs_add_le
                  (((∏ i ∈ s, (1 + e i)) - 1) * (1 + e a)) (e a))
        _ ≤ gamma u s.card * (1 + u) + u := by gcongr
        _ ≤ gamma u (s.card + 1) := p04_gamma_step hu hvsucc

private lemma p04_inclusive_error_bound {q : ℕ} (e : Fin q → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hv : GammaValid u q)
    (he : ∀ i, |e i| ≤ u) (k : Fin q) :
    |p04InclusiveErrorProduct e k - 1| ≤ gamma u q := by
  let s := Finset.Ico k.val q
  have hcard : s.card ≤ q := by
    have hc := Finset.card_le_card (by
      intro i hi
      change i ∈ Finset.Ico k.val q at hi
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2)
    simpa [s] using hc
  have hvs : GammaValid u s.card := by
    unfold GammaValid at hv ⊢
    have hc : (s.card : ℝ) ≤ (q : ℝ) := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  calc
    |p04InclusiveErrorProduct e k - 1| =
        |(∏ i ∈ s, (1 + p04ErrorAt e i)) - 1| := by
          rfl
    _ ≤ gamma u s.card := p04_abs_finset_prod_sub_one_le_gamma
          s (p04ErrorAt e) u hu hvs (by
            intro i hi
            have hiq : i < q := by
              simp only [s, Finset.mem_Ico] at hi
              exact hi.2
            simpa [p04ErrorAt, hiq] using he ⟨i, hiq⟩)
    _ ≤ gamma u q := p04_gamma_mono_nat hu hcard hv

private lemma p04_factorized_error_bound {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (A B : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ k j, |alpha k j| ≤ A)
    (hB : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hterm : ∀ k : Fin q, ∀ j : Fin b,
      |x k j * y k j -
        x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    have hab : |alpha k j * beta k j| ≤ A * B := by
      rw [abs_mul]
      gcongr
      · exact hA k j
      · exact hB k j
    have hs : |alpha k j + beta k j + alpha k j * beta k j| ≤
        A + B + A * B := by
      calc
        |alpha k j + beta k j + alpha k j * beta k j| ≤
            |alpha k j| + |beta k j| + |alpha k j * beta k j| :=
              abs_add_three _ _ _
        _ ≤ A + B + A * B := by
          gcongr
          · exact hA k j
          · exact hB k j
    rw [show x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
        -(x k j * y k j) *
          (alpha k j + beta k j + alpha k j * beta k j) by ring]
    rw [abs_mul, abs_neg, abs_mul]
    calc
      |x k j| * |y k j| *
          |alpha k j + beta k j + alpha k j * beta k j| ≤
        |x k j| * |y k j| * (A + B + A * B) := by gcongr
      _ = (A + B + A * B) * (|x k j| * |y k j|) := by ring
  unfold p04BlockedDot p04BlockedAbsDot
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin q, ∑ j : Fin b,
        (x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j))| ≤
      ∑ k : Fin q, |∑ j : Fin b,
        (x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| := by
          apply Finset.sum_le_sum
          intro k hk
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        (A + B + A * B) * (|x k j| * |y k j|) := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.sum_le_sum
          intro j hj
          exact hterm k j
    _ = (A + B + A * B) *
        ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j| := by
          simp_rw [← Finset.mul_sum]

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
  have huEff : 0 ≤ uEff := by
    unfold uEff p04EffectiveFmaRoundoff
    split_ifs
    · exact run.uOut_nonneg
    · positivity
    · exact run.uFma_nonneg
  have hrepr : run.computed =
      ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) := by
    rw [p04_state_unroll run]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [alpha, beta]
    rw [run.inner_path_factor k j]
    ring
  have halpha : ∀ k j, |alpha k j| ≤ gamma uEff q := by
    intro k j
    exact p04_inclusive_error_bound run.delta uEff huEff
      run.effective_gamma_valid run.delta_bound k
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    exact p04_abs_prod_sub_one_le_gamma n
      (run.innerPathError k j) run.uBar run.uBar_nonneg
      run.internal_gamma_valid (run.inner_path_error_bound k j)
  have hgammaEff : 0 ≤ gamma uEff q :=
    p04_gamma_nonneg huEff run.effective_gamma_valid
  have hgammaBar : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have herr :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    rw [hrepr]
    simpa [p04BlockFmaCoeff] using
      (p04_factorized_error_bound run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar n)
        hgammaEff hgammaBar halpha hbeta)
  refine ⟨alpha, beta, hrepr, halpha, hbeta, herr, ?_, ?_⟩
  · intro horder
    have hqb : q + b - 1 ≤ n := by
      have hmul : b - 1 ≤ q * (b - 1) :=
        Nat.le_mul_of_pos_left (b - 1) run.block_count_pos
      have heq : q + q * (b - 1) = q * b := by
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        have hqmul : q ≤ q * b :=
          Nat.le_mul_of_pos_right q run.block_size_pos
        omega
      rw [run.dimension_eq]
      calc
        q + b - 1 = q + (b - 1) := by
          have hb := run.block_size_pos
          omega
        _ ≤ q + q * (b - 1) := Nat.add_le_add_left hmul q
        _ = q * b := heq
    have hvalidR : GammaValid run.uBar (q + b - 1) := by
      have hvN := run.internal_gamma_valid
      unfold GammaValid at hvN ⊢
      have hc : ((q + b - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hqb
      nlinarith [mul_le_mul_of_nonneg_right hc run.uBar_nonneg]
    have hbetaR : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hfac :
          (∏ r : Fin n, (1 + run.innerPathError k j r)) =
            ∏ r : Fin (q + b - 1),
              (1 + run.rightToLeftPathError k j r) := by
        rw [run.inner_path_factor k j,
          run.right_to_left_path_factor horder k j]
      simp only [beta, hfac]
      exact p04_abs_prod_sub_one_le_gamma (q + b - 1)
        (run.rightToLeftPathError k j) run.uBar run.uBar_nonneg
        hvalidR (run.right_to_left_path_error_bound horder k j)
    have hgammaR : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hvalidR
    refine ⟨hbetaR, ?_⟩
    rw [hrepr]
    simpa [p04BlockFmaCoeff] using
      (p04_factorized_error_bound run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar (q + b - 1))
        hgammaEff hgammaR halpha hbetaR)
  · rintro ⟨hout, hbar⟩
    have huEffZero : uEff = 0 := by
      unfold uEff p04EffectiveFmaRoundoff
      rw [if_neg (not_lt.mpr hout)]
      rw [if_pos (by simpa [hbar])]
    have halphaZero : ∀ k j, alpha k j = 0 := by
      intro k j
      have h := halpha k j
      rw [huEffZero] at h
      simp [gamma] at h
      exact h
    refine ⟨halphaZero, ?_⟩
    simpa [p04BlockFmaCoeff, huEffZero, gamma] using herr

end HighamBench
