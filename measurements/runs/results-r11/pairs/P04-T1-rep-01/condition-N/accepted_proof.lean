import HighamBench.P04Definitions

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  have hd : 0 < 1 - (m : ℝ) * u := sub_pos.mpr hv
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) hd.le

private lemma p04_gamma_valid_of_le {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hv : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hc : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hc hu) hv

private lemma p04_gamma_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hv : GammaValid u n) :
    gamma u m ≤ gamma u n := by
  unfold gamma GammaValid at *
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hmu : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hmnR hu
  have hdn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hv
  have hdm : 0 < 1 - (m : ℝ) * u := lt_of_lt_of_le hdn (sub_le_sub_left hmu 1)
  apply (div_le_div_iff₀ hdm hdn).2
  nlinarith

private lemma p04_gamma_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (m + 1)) :
    gamma u m + u * (1 + gamma u m) ≤ gamma u (m + 1) := by
  unfold gamma GammaValid at *
  have hmcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
  rw [hmcast] at hv ⊢
  have hdu : 0 < 1 - ((m : ℝ) + 1) * u := sub_pos.mpr hv
  have hdm : 0 < 1 - (m : ℝ) * u := by nlinarith
  have heq :
      (m : ℝ) * u / (1 - (m : ℝ) * u) +
          u * (1 + (m : ℝ) * u / (1 - (m : ℝ) * u)) =
        ((m : ℝ) + 1) * u / (1 - (m : ℝ) * u) := by
    field_simp [ne_of_gt hdm]
    ring
  rw [heq]
  apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) hu) hdu
  nlinarith

private lemma p04_prod_error_bound {m : ℕ} (u : ℝ) (e : Fin m → ℝ)
    (hu : 0 ≤ u) (hv : GammaValid u m) (he : ∀ i, |e i| ≤ u) :
    |(∏ i : Fin m, (1 + e i)) - 1| ≤ gamma u m := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
      let e' : Fin m → ℝ := fun i ↦ e i.castSucc
      have hv' : GammaValid u m := by
        unfold GammaValid at hv ⊢
        have hm : (m : ℝ) ≤ (m + 1 : ℕ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hm hu]
      have hi := ih e' hv' (fun i ↦ he i.castSucc)
      have hs := p04_gamma_step hu hv
      have hp : |∏ i : Fin m, (1 + e' i)| ≤ 1 + gamma u m := by
        calc
          |∏ i : Fin m, (1 + e' i)| =
              |((∏ i : Fin m, (1 + e' i)) - 1) + 1| := by ring_nf
          _ ≤ |(∏ i : Fin m, (1 + e' i)) - 1| + 1 := by
            simpa using abs_add_le ((∏ i : Fin m, (1 + e' i)) - 1) 1
          _ ≤ gamma u m + 1 := add_le_add hi le_rfl
          _ = 1 + gamma u m := add_comm _ _
      calc
        |(∏ i : Fin (m + 1), (1 + e i)) - 1| =
            |((∏ i : Fin m, (1 + e' i)) - 1) +
              e (Fin.last m) * (∏ i : Fin m, (1 + e' i))| := by
                simp only [e', Fin.prod_univ_castSucc]
                ring_nf
        _ ≤ |(∏ i : Fin m, (1 + e' i)) - 1| +
              |e (Fin.last m)| * |∏ i : Fin m, (1 + e' i)| := by
                simpa only [abs_mul] using
                  abs_add_le ((∏ i : Fin m, (1 + e' i)) - 1)
                    (e (Fin.last m) * (∏ i : Fin m, (1 + e' i)))
        _ ≤ gamma u m + u * (1 + gamma u m) := by
              gcongr
              · exact he (Fin.last m)
        _ ≤ gamma u (m + 1) := hs

private lemma p04_finset_prod_error_bound {I : Type*} [DecidableEq I]
    (s : Finset I) (u : ℝ) (e : I → ℝ)
    (hu : 0 ≤ u) (hv : GammaValid u s.card)
    (he : ∀ i ∈ s, |e i| ≤ u) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u s.card := by
  induction s using Finset.induction_on with
  | empty => simp [gamma]
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha] at hv ⊢
      have hv' : GammaValid u s.card := by
        unfold GammaValid at hv ⊢
        have hm : (s.card : ℝ) ≤ (s.card + 1 : ℕ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hm hu]
      have hi := ih hv' (fun i hi ↦ he i (Finset.mem_insert_of_mem hi))
      have hs := p04_gamma_step hu hv
      have hp : |∏ i ∈ s, (1 + e i)| ≤ 1 + gamma u s.card := by
        calc
          |∏ i ∈ s, (1 + e i)| =
              |((∏ i ∈ s, (1 + e i)) - 1) + 1| := by ring_nf
          _ ≤ |(∏ i ∈ s, (1 + e i)) - 1| + 1 := by
            simpa using abs_add_le ((∏ i ∈ s, (1 + e i)) - 1) 1
          _ ≤ gamma u s.card + 1 := add_le_add hi le_rfl
          _ = 1 + gamma u s.card := add_comm _ _
      calc
        |(∏ i ∈ insert a s, (1 + e i)) - 1| =
            |((∏ i ∈ s, (1 + e i)) - 1) +
              e a * (∏ i ∈ s, (1 + e i))| := by
                rw [Finset.prod_insert ha]
                ring_nf
        _ ≤ |(∏ i ∈ s, (1 + e i)) - 1| +
              |e a| * |∏ i ∈ s, (1 + e i)| := by
                simpa only [abs_mul] using
                  abs_add_le ((∏ i ∈ s, (1 + e i)) - 1)
                    (e a * (∏ i ∈ s, (1 + e i)))
        _ ≤ gamma u s.card + u * (1 + gamma u s.card) := by
              gcongr
              exact he a (Finset.mem_insert_self _ _)
        _ ≤ gamma u (s.card + 1) := hs

private lemma p04_finset_prod_error_bound_le {I : Type*} [DecidableEq I]
    (s : Finset I) (N : ℕ) (u : ℝ) (e : I → ℝ)
    (hu : 0 ≤ u) (hv : GammaValid u N) (hcard : s.card ≤ N)
    (he : ∀ i ∈ s, |e i| ≤ u) :
    |(∏ i ∈ s, (1 + e i)) - 1| ≤ gamma u N := by
  have hv' : GammaValid u s.card := by
    unfold GammaValid at hv ⊢
    have hc : (s.card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcard
    nlinarith [mul_le_mul_of_nonneg_right hc hu]
  exact (p04_finset_prod_error_bound s u e hu hv' he).trans
    (p04_gamma_mono hu hcard hv)

private lemma p04_affine_chain (Q : ℕ)
    (s c d z : ℕ → ℝ) (hzero : s 0 = 0)
    (hstep : ∀ k < Q, s (k + 1) = (s k * c k + z k) * d k) :
    s Q = ∑ k ∈ Finset.range Q,
      z k * (∏ l ∈ Finset.Ico (k + 1) Q, c l) *
        (∏ l ∈ Finset.Ico k Q, d l) := by
  induction Q with
  | zero => simpa using hzero
  | succ m ih =>
      rw [hstep m (Nat.lt_succ_self m)]
      have ih' := ih (fun k hk ↦ hstep k (lt_trans hk (Nat.lt_succ_self m)))
      rw [ih', add_mul, Finset.sum_mul, Finset.sum_mul,
        Finset.sum_range_succ]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hkm : k ≤ m := Nat.le_of_lt (Finset.mem_range.mp hk)
        rw [Finset.prod_Ico_succ_top (Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)),
          Finset.prod_Ico_succ_top hkm]
        ring
      · simp

private lemma p04_run_expansion {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j * (1 + run.termTheta k j) *
        p04StrictErrorProduct run.carryTheta k *
        p04InclusiveErrorProduct run.delta k := by
  let c : ℕ → ℝ := fun k ↦ 1 + p04ErrorAt run.carryTheta k
  let d : ℕ → ℝ := fun k ↦ 1 + p04ErrorAt run.delta k
  let z : ℕ → ℝ := fun k ↦
    if h : k < q then
      ∑ j : Fin b, run.x ⟨k, h⟩ j * run.y ⟨k, h⟩ j *
        (1 + run.termTheta ⟨k, h⟩ j)
    else 0
  have hstep : ∀ k < q,
      run.state (k + 1) = (run.state k * c k + z k) * d k := by
    intro k hk
    simpa [c, d, z, p04ErrorAt, hk] using run.state_step ⟨k, hk⟩
  have hchain := p04_affine_chain q run.state c d z run.state_zero hstep
  unfold P04BlockFmaDotRun.computed
  calc
    run.state q = ∑ k ∈ Finset.range q,
        z k * (∏ l ∈ Finset.Ico (k + 1) q, c l) *
          (∏ l ∈ Finset.Ico k q, d l) := hchain
    _ = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j * (1 + run.termTheta k j) *
          p04StrictErrorProduct run.carryTheta k *
          p04InclusiveErrorProduct run.delta k := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [z, c, d, k.isLt, dite_true, p04StrictErrorProduct,
        p04InclusiveErrorProduct]
      rw [Finset.sum_mul, Finset.sum_mul]

private lemma p04_factored_sum_error {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k j, |alpha k j| ≤ A)
    (hb : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hterm : ∀ k j,
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
        (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    have hab : |alpha k j + beta k j + alpha k j * beta k j| ≤
        A + B + A * B := by
      calc
        |alpha k j + beta k j + alpha k j * beta k j| ≤
            |alpha k j| + |beta k j| + |alpha k j| * |beta k j| := by
              calc
                |alpha k j + beta k j + alpha k j * beta k j| ≤
                    |alpha k j + beta k j| + |alpha k j * beta k j| :=
                      abs_add_le _ _
                _ ≤ (|alpha k j| + |beta k j|) +
                    |alpha k j| * |beta k j| := by
                      rw [abs_mul]
                      gcongr
                      exact abs_add_le _ _
        _ ≤ A + B + A * B := by
          have hmul : |alpha k j| * |beta k j| ≤ A * B :=
            mul_le_mul (ha k j) (hb k j) (abs_nonneg _) hA
          linarith [ha k j, hb k j]
      
    rw [show x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
        -(x k j * y k j) *
          (alpha k j + beta k j + alpha k j * beta k j) by ring,
      abs_mul, abs_neg, abs_mul]
    calc
      |x k j| * |y k j| *
          |alpha k j + beta k j + alpha k j * beta k j| ≤
          |x k j| * |y k j| * (A + B + A * B) := by
            gcongr
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
  let alpha : Fin q → Fin b → ℝ := fun k _ ↦
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j ↦
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have huEff : 0 ≤ uEff := by
    dsimp [uEff]
    unfold p04EffectiveFmaRoundoff
    split
    · exact run.uOut_nonneg
    · split
      · exact le_rfl
      · exact run.uFma_nonneg
  have hgammaEff : 0 ≤ gamma uEff q :=
    p04_gamma_nonneg huEff run.effective_gamma_valid
  have hgammaN : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have hAlpha : ∀ k j, |alpha k j| ≤ gamma uEff q := by
    intro k j
    dsimp [alpha, p04InclusiveErrorProduct]
    apply p04_finset_prod_error_bound_le
        (Finset.Ico k.val q) q uEff (p04ErrorAt run.delta)
        huEff run.effective_gamma_valid
    · simp
    · intro l hl
      have hlq : l < q := (Finset.mem_Ico.mp hl).2
      simpa [p04ErrorAt, hlq] using run.delta_bound ⟨l, hlq⟩
  have hBeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    dsimp [beta]
    exact p04_prod_error_bound run.uBar (run.innerPathError k j)
      run.uBar_nonneg run.internal_gamma_valid
      (run.inner_path_error_bound k j)
  have hComputed : run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j *
        (1 + alpha k j) * (1 + beta k j) := by
    rw [p04_run_expansion]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [alpha, beta]
    rw [run.inner_path_factor k j]
    ring
  have hError :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    rw [hComputed]
    simpa [p04BlockFmaCoeff] using
      p04_factored_sum_error run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar n)
        hgammaEff hgammaN hAlpha hBeta
  have hlen : q + b - 1 ≤ n := by
    have hbpos := run.block_size_pos
    calc
      q + b - 1 = q + (b - 1) := by omega
      _ ≤ q + q * (b - 1) :=
        Nat.add_le_add_left
          (Nat.le_mul_of_pos_left (b - 1) run.block_count_pos) q
      _ = q * ((b - 1) + 1) := by ring
      _ = q * b := by
        have hb : b - 1 + 1 = b :=
          Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
            (Nat.ne_of_gt run.block_size_pos))
        rw [hb]
      _ = n := run.dimension_eq.symm
  have hvalidShort : GammaValid run.uBar (q + b - 1) :=
    p04_gamma_valid_of_le run.uBar_nonneg hlen run.internal_gamma_valid
  have hgammaShort : 0 ≤ gamma run.uBar (q + b - 1) :=
    p04_gamma_nonneg run.uBar_nonneg hvalidShort
  have hRight : run.order = P04BlockEvaluationOrder.rightToLeft →
      (∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1)) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q (q + b - 1) *
          p04BlockedAbsDot run.x run.y := by
    intro horder
    have hBetaRight : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      dsimp [beta]
      rw [run.inner_path_factor k j,
        ← run.right_to_left_path_factor horder k j]
      exact p04_prod_error_bound run.uBar
        (run.rightToLeftPathError k j) run.uBar_nonneg hvalidShort
        (run.right_to_left_path_error_bound horder k j)
    refine ⟨hBetaRight, ?_⟩
    rw [hComputed]
    simpa [p04BlockFmaCoeff] using
      p04_factored_sum_error run.x run.y alpha beta
        (gamma uEff q) (gamma run.uBar (q + b - 1))
        hgammaEff hgammaShort hAlpha hBetaRight
  have hSpecial : run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
      (∀ k j, alpha k j = 0) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        gamma run.uBar n * p04BlockedAbsDot run.x run.y := by
    rintro ⟨hout, hbar⟩
    have heff : uEff = 0 := by
      dsimp [uEff]
      unfold p04EffectiveFmaRoundoff
      rw [if_neg (not_lt_of_ge hout)]
      simp [hbar]
    have hAlphaZero : ∀ k j, alpha k j = 0 := by
      intro k j
      have ha := hAlpha k j
      rw [heff] at ha
      simp [gamma] at ha
      exact ha
    refine ⟨hAlphaZero, ?_⟩
    rw [hComputed]
    simpa using
      p04_factored_sum_error run.x run.y alpha beta
        0 (gamma run.uBar n) le_rfl hgammaN
        (fun k j ↦ by simp [hAlphaZero k j]) hBeta
  exact ⟨alpha, beta, hComputed, hAlpha, hBeta, hError, hRight, hSpecial⟩

end HighamBench
