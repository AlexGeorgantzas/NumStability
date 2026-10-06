import HighamBench.P04Definitions

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hv))

private lemma p04_gamma_mono_nat {u : ℝ} {m M : ℕ}
    (hu : 0 ≤ u) (hmM : m ≤ M) (hM : GammaValid u M) :
    gamma u m ≤ gamma u M := by
  have hcast : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hm : (m : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hM
  unfold gamma
  apply (div_le_div_iff₀ (sub_pos.mpr hm) (sub_pos.mpr hM)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hcast) hu]

private lemma p04_gamma_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (m + 1)) :
    gamma u m * (1 + u) + u ≤ gamma u (m + 1) := by
  unfold GammaValid at hv
  norm_num only [Nat.cast_add, Nat.cast_one] at hv
  have hm : (m : ℝ) * u < 1 :=
    lt_of_le_of_lt (by nlinarith : (m : ℝ) * u ≤ ((m : ℝ) + 1) * u) hv
  have hnum : 0 ≤ ((m : ℝ) + 1) * u := by positivity
  simp only [gamma, Nat.cast_add, Nat.cast_one]
  have heq :
      ((m : ℝ) * u / (1 - (m : ℝ) * u)) * (1 + u) + u =
        ((m : ℝ) + 1) * u / (1 - (m : ℝ) * u) := by
    field_simp [ne_of_gt (sub_pos.mpr hm)]
    ring
  rw [heq]
  apply (div_le_div_iff₀ (sub_pos.mpr hm) (sub_pos.mpr hv)).2
  nlinarith

private lemma p04_abs_prod_one_add_sub_one_le_gamma
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ) (u : ℝ)
    (hu : 0 ≤ u) (he : ∀ i ∈ s, |e i| ≤ u)
    (hv : GammaValid u s.card) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u s.card := by
  induction s using Finset.induction_on with
  | empty => simp [gamma]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
      have hvnext : GammaValid u (s.card + 1) := by
        simpa [Finset.card_insert_of_notMem ha] using hv
      have hv' : GammaValid u s.card := by
        unfold GammaValid at hvnext ⊢
        have hc : (s.card : ℝ) ≤ ((s.card + 1 : ℕ) : ℝ) := by norm_num
        exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hvnext
      have he_s : ∀ i ∈ s, |e i| ≤ u := by
        intro i hi
        exact he i (Finset.mem_insert_of_mem hi)
      have hea : |e a| ≤ u := he a (Finset.mem_insert_self _ _)
      have hfactor : |1 + e a| ≤ 1 + u := by
        calc
          |1 + e a| ≤ |(1 : ℝ)| + |e a| := abs_add_le _ _
          _ ≤ 1 + u := by simpa using add_le_add_left hea 1
      calc
        |(1 + e a) * (∏ i ∈ s, (1 + e i)) - 1|
            = |((∏ i ∈ s, (1 + e i)) - 1) * (1 + e a) + e a| := by ring_nf
        _ ≤ |(∏ i ∈ s, (1 + e i)) - 1| * |1 + e a| + |e a| := by
          simpa [abs_mul] using
            (abs_add_le (((∏ i ∈ s, (1 + e i)) - 1) * (1 + e a)) (e a))
        _ ≤ gamma u s.card * |1 + e a| + |e a| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_right (ih he_s hv') (abs_nonneg _)) le_rfl
        _ ≤ gamma u s.card * (1 + u) + |e a| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hfactor (p04_gamma_nonneg hu hv')) le_rfl
        _ ≤ gamma u s.card * (1 + u) + u := add_le_add le_rfl hea
        _ ≤ gamma u (s.card + 1) := p04_gamma_step hu hvnext

private lemma p04_abs_prod_one_add_sub_one_le_gamma_of_card_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℝ) (u : ℝ) (N : ℕ)
    (hu : 0 ≤ u) (he : ∀ i ∈ s, |e i| ≤ u)
    (hcard : s.card ≤ N) (hv : GammaValid u N) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u N := by
  have hvcard : GammaValid u s.card := by
    unfold GammaValid at hv ⊢
    have hc : (s.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hv
  exact (p04_abs_prod_one_add_sub_one_le_gamma s e u hu he hvcard).trans
    (p04_gamma_mono_nat hu hcard hv)

private lemma p04_effective_nonneg (uBar uFma uOut : ℝ)
    (huFma : 0 ≤ uFma) (huOut : 0 ≤ uOut) :
    0 ≤ p04EffectiveFmaRoundoff uBar uFma uOut := by
  unfold p04EffectiveFmaRoundoff
  split_ifs <;> positivity

private lemma p04_weighted_sum_error {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (ga gb : ℝ)
    (hga : 0 ≤ ga) (hgb : 0 ≤ gb)
    (ha : ∀ k j, |alpha k j| ≤ ga)
    (hb : ∀ k j, |beta k j| ≤ gb) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (ga + gb + ga * gb) * p04BlockedAbsDot x y := by
  have hpoint : ∀ k j,
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
        (ga + gb + ga * gb) * (|x k j| * |y k j|) := by
    intro k j
    have hab : |alpha k j + beta k j + alpha k j * beta k j| ≤
        ga + gb + ga * gb := by
      calc
        |alpha k j + beta k j + alpha k j * beta k j| ≤
            |alpha k j| + |beta k j| + |alpha k j * beta k j| := by
          calc
            _ ≤ |alpha k j + beta k j| +
                |alpha k j * beta k j| := abs_add_le _ _
            _ ≤ _ := by
              nlinarith [abs_add_le (alpha k j) (beta k j)]
        _ = |alpha k j| + |beta k j| +
            |alpha k j| * |beta k j| := by rw [abs_mul]
        _ ≤ ga + gb + ga * gb := by
          have hmul := mul_le_mul (ha k j) (hb k j) (abs_nonneg _) hga
          nlinarith [ha k j, hb k j]
    have hid : x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
        -(x k j * y k j) *
          (alpha k j + beta k j + alpha k j * beta k j) := by ring
    calc
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
          (|x k j| * |y k j|) *
            |alpha k j + beta k j + alpha k j * beta k j| := by
              rw [hid, abs_mul, abs_neg, abs_mul]
      _ ≤ (|x k j| * |y k j|) * (ga + gb + ga * gb) :=
        mul_le_mul_of_nonneg_left hab (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (ga + gb + ga * gb) * (|x k j| * |y k j|) := by ring
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
        (ga + gb + ga * gb) * (|x k j| * |y k j|) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint k j
    _ = (ga + gb + ga * gb) *
        ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]

private lemma p04_unroll_affine (N : ℕ) (s A B : ℕ → ℝ)
    (hzero : s 0 = 0)
    (hstep : ∀ k < N, s (k + 1) = s k * A k + B k) :
    s N = ∑ k ∈ Finset.range N,
      B k * ∏ l ∈ Finset.Ico (k + 1) N, A l := by
  induction N with
  | zero => simpa using hzero
  | succ N ih =>
      have hlast := hstep N (Nat.lt_succ_self N)
      have hprev : ∀ k < N, s (k + 1) = s k * A k + B k := by
        intro k hk
        exact hstep k (lt_trans hk (Nat.lt_succ_self N))
      rw [hlast, ih hprev, Finset.sum_mul, Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt (Finset.mem_range.mp hk))]
        ring
      · simp

private lemma p04_state_factorization {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j * (1 + run.termTheta k j) *
        p04StrictErrorProduct run.carryTheta k *
        p04InclusiveErrorProduct run.delta k := by
  let A : ℕ → ℝ := fun l =>
    (1 + p04ErrorAt run.carryTheta l) * (1 + p04ErrorAt run.delta l)
  let B : ℕ → ℝ := fun k =>
    if hk : k < q then
      (∑ j : Fin b,
        run.x ⟨k, hk⟩ j * run.y ⟨k, hk⟩ j *
          (1 + run.termTheta ⟨k, hk⟩ j)) *
        (1 + p04ErrorAt run.delta k)
    else 0
  have hstep : ∀ k < q,
      run.state (k + 1) = run.state k * A k + B k := by
    intro k hk
    rw [run.state_step ⟨k, hk⟩]
    simp only [A, B, p04ErrorAt, dif_pos hk]
    ring
  have hu := p04_unroll_affine q run.state A B run.state_zero hstep
  unfold P04BlockFmaDotRun.computed
  rw [hu, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  have hkq : k < q := Finset.mem_range.mp hk
  simp only [B, dif_pos hkq]
  rw [Finset.prod_mul_distrib]
  simp only [dif_pos hkq, p04StrictErrorProduct,
    p04InclusiveErrorProduct]
  have hdelta :
      (1 + p04ErrorAt run.delta k) *
          (∏ x ∈ Finset.Ico (k + 1) q, (1 + p04ErrorAt run.delta x)) =
        ∏ x ∈ Finset.Ico k q, (1 + p04ErrorAt run.delta x) :=
    (Finset.prod_eq_prod_Ico_succ_bot hkq
      (fun x => 1 + p04ErrorAt run.delta x)).symm
  calc
    (∑ j : Fin b,
        run.x ⟨k, hkq⟩ j * run.y ⟨k, hkq⟩ j *
          (1 + run.termTheta ⟨k, hkq⟩ j)) *
          (1 + p04ErrorAt run.delta k) *
          ((∏ x ∈ Finset.Ico (k + 1) q,
              (1 + p04ErrorAt run.carryTheta x)) *
            ∏ x ∈ Finset.Ico (k + 1) q,
              (1 + p04ErrorAt run.delta x)) =
      (∑ j : Fin b,
        run.x ⟨k, hkq⟩ j * run.y ⟨k, hkq⟩ j *
          (1 + run.termTheta ⟨k, hkq⟩ j)) *
          (∏ x ∈ Finset.Ico (k + 1) q,
            (1 + p04ErrorAt run.carryTheta x)) *
          ((1 + p04ErrorAt run.delta k) *
            ∏ x ∈ Finset.Ico (k + 1) q,
              (1 + p04ErrorAt run.delta x)) := by ring
    _ = (∑ j : Fin b,
        run.x ⟨k, hkq⟩ j * run.y ⟨k, hkq⟩ j *
          (1 + run.termTheta ⟨k, hkq⟩ j)) *
          (∏ x ∈ Finset.Ico (k + 1) q,
            (1 + p04ErrorAt run.carryTheta x)) *
          (∏ x ∈ Finset.Ico k q,
            (1 + p04ErrorAt run.delta x)) := by rw [hdelta]
    _ = _ := by
      rw [Finset.sum_mul, Finset.sum_mul]

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
  let uE := p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut
  let alpha : Fin q → Fin b → ℝ := fun k _ =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have huE : 0 ≤ uE :=
    p04_effective_nonneg run.uBar run.uFma run.uOut
      run.uFma_nonneg run.uOut_nonneg
  have hfactor : run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j *
        (1 + alpha k j) * (1 + beta k j) := by
    rw [p04_state_factorization run]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    dsimp only [alpha, beta]
    rw [run.inner_path_factor k j]
    ring
  have halpha : ∀ k j, |alpha k j| ≤ gamma uE q := by
    intro k j
    dsimp only [alpha]
    apply p04_abs_prod_one_add_sub_one_le_gamma_of_card_le
      (Finset.Ico k.val q) (p04ErrorAt run.delta) uE q huE
    · intro l hl
      have hlq : l < q := (Finset.mem_Ico.mp hl).2
      simpa [p04ErrorAt, hlq, uE] using run.delta_bound ⟨l, hlq⟩
    · simp
    · exact run.effective_gamma_valid
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    dsimp only [beta]
    apply p04_abs_prod_one_add_sub_one_le_gamma_of_card_le
      (Finset.univ : Finset (Fin n))
      (run.innerPathError k j) run.uBar n run.uBar_nonneg
    · intro r hr
      exact run.inner_path_error_bound k j r
    · simp
    · simpa using run.internal_gamma_valid
  have hga : 0 ≤ gamma uE q :=
    p04_gamma_nonneg huE run.effective_gamma_valid
  have hgb : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have herror :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uE run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    rw [hfactor]
    simpa only [p04BlockFmaCoeff] using
      p04_weighted_sum_error run.x run.y alpha beta
        (gamma uE q) (gamma run.uBar n) hga hgb halpha hbeta
  have hright : run.order = P04BlockEvaluationOrder.rightToLeft →
      (∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1)) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uE run.uBar q (q + b - 1) *
          p04BlockedAbsDot run.x run.y := by
    intro hord
    have hqb : q + b - 1 ≤ q * b := by
      have hq1 : 1 ≤ q := run.block_count_pos
      have hb1 : 1 ≤ b := run.block_size_pos
      have hmul : b - 1 ≤ q * (b - 1) := by
        simpa [mul_comm] using Nat.mul_le_mul_right (b - 1) hq1
      calc
        q + b - 1 = q + (b - 1) := by omega
        _ ≤ q + q * (b - 1) := Nat.add_le_add_left hmul q
        _ = q * (1 + (b - 1)) := by ring
        _ = q * b := by
          congr 1
          omega
    have hlen : q + b - 1 ≤ n := by
      rw [run.dimension_eq]
      exact hqb
    have hvlen : GammaValid run.uBar (q + b - 1) := by
      have hvn := run.internal_gamma_valid
      unfold GammaValid at hvn ⊢
      have hc : ((q + b - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hlen
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_right hc run.uBar_nonneg)
        hvn
    have hbeta_right : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      dsimp only [beta]
      rw [run.inner_path_factor k j]
      rw [← run.right_to_left_path_factor hord k j]
      apply p04_abs_prod_one_add_sub_one_le_gamma_of_card_le
        (Finset.univ : Finset (Fin (q + b - 1)))
        (run.rightToLeftPathError k j) run.uBar (q + b - 1)
        run.uBar_nonneg
      · intro r hr
        exact run.right_to_left_path_error_bound hord k j r
      · simp
      · simpa using hvlen
    refine ⟨hbeta_right, ?_⟩
    have hgb_right : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hvlen
    rw [hfactor]
    simpa only [p04BlockFmaCoeff] using
      p04_weighted_sum_error run.x run.y alpha beta
        (gamma uE q) (gamma run.uBar (q + b - 1))
        hga hgb_right halpha hbeta_right
  have hspecial : run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
      (∀ k j, alpha k j = 0) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        gamma run.uBar n * p04BlockedAbsDot run.x run.y := by
    rintro ⟨hout, hbar⟩
    have huEzero : uE = 0 := by
      dsimp only [uE]
      simp [p04EffectiveFmaRoundoff, not_lt_of_ge hout, hbar]
    have halpha_zero : ∀ k j, alpha k j = 0 := by
      intro k j
      have habs : |alpha k j| = 0 := by
        apply le_antisymm
        · simpa [huEzero, gamma] using halpha k j
        · exact abs_nonneg _
      exact abs_eq_zero.mp habs
    refine ⟨halpha_zero, ?_⟩
    simpa [huEzero, p04BlockFmaCoeff, gamma] using herror
  exact ⟨alpha, beta, hfactor, halpha, hbeta, herror, hright, hspecial⟩

end HighamBench
