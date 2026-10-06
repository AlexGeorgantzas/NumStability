import HighamBench.P04Definitions

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold GammaValid at hv
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu)
    (le_of_lt (sub_pos.mpr hv))

private lemma p04_gamma_step {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u (m + 1)) :
    gamma u m + u + gamma u m * u ≤ gamma u (m + 1) := by
  unfold GammaValid at hv
  unfold gamma
  have hden : 0 < 1 - (m : ℝ) * u := by
    norm_num at hv ⊢
    nlinarith
  have hden' : 0 < 1 - ((m + 1 : ℕ) : ℝ) * u := by
    exact sub_pos.mpr hv
  have heq :
      (m : ℝ) * u / (1 - (m : ℝ) * u) + u +
          (m : ℝ) * u / (1 - (m : ℝ) * u) * u =
        ((m + 1 : ℕ) : ℝ) * u / (1 - (m : ℝ) * u) := by
    field_simp [ne_of_gt hden]
    push_cast
    ring
  rw [heq, div_le_div_iff₀ hden hden']
  norm_num at hv ⊢
  nlinarith [mul_nonneg (by positivity : 0 ≤ (m + 1 : ℝ)) hu]

private lemma p04_product_gamma_bound {m : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hv : GammaValid u m)
    (e : Fin m → ℝ) (he : ∀ i, |e i| ≤ u) :
    |(∏ i : Fin m, (1 + e i)) - 1| ≤ gamma u m := by
  induction m with
  | zero => simp [gamma]
  | succ m ih =>
      rw [Fin.prod_univ_succ]
      have hv_m : GammaValid u m := by
        unfold GammaValid at hv ⊢
        norm_num at hv ⊢
        nlinarith
      have hi := ih hv_m (fun i => e i.succ) (fun i => he i.succ)
      have he0 := he 0
      have hgm := p04_gamma_nonneg hu hv_m
      calc
        |(1 + e 0) * (∏ i : Fin m, (1 + e i.succ)) - 1|
            = |((∏ i : Fin m, (1 + e i.succ)) - 1) + e 0 +
                ((∏ i : Fin m, (1 + e i.succ)) - 1) * e 0| := by ring_nf
        _ ≤ |(∏ i : Fin m, (1 + e i.succ)) - 1| + |e 0| +
              |(∏ i : Fin m, (1 + e i.succ)) - 1| * |e 0| := by
              calc
                |(∏ i : Fin m, (1 + e i.succ)) - 1 + e 0 +
                    ((∏ i : Fin m, (1 + e i.succ)) - 1) * e 0|
                    ≤ |(∏ i : Fin m, (1 + e i.succ)) - 1 + e 0| +
                        |((∏ i : Fin m, (1 + e i.succ)) - 1) * e 0| :=
                      abs_add_le _ _
                _ ≤ (|(∏ i : Fin m, (1 + e i.succ)) - 1| + |e 0|) +
                        |((∏ i : Fin m, (1 + e i.succ)) - 1) * e 0| := by
                      gcongr
                      exact abs_add_le _ _
                _ = _ := by rw [abs_mul]
        _ ≤ gamma u m + u + gamma u m * u := by
              gcongr
        _ ≤ gamma u (m + 1) := p04_gamma_step hu hv

private lemma p04_inclusive_gamma_bound {q : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hv : GammaValid u q)
    (e : Fin q → ℝ) (he : ∀ i, |e i| ≤ u) (k : Fin q) :
    |p04InclusiveErrorProduct e k - 1| ≤ gamma u q := by
  let ep : Fin q → ℝ := fun i => if k.val ≤ i.val then e i else 0
  have hep : ∀ i, |ep i| ≤ u := by
    intro i
    dsimp [ep]
    split_ifs
    · exact he i
    · simpa using hu
  have hprod :
      (∏ i : Fin q, (1 + ep i)) = p04InclusiveErrorProduct e k := by
    unfold p04InclusiveErrorProduct
    calc
      (∏ i : Fin q, (1 + ep i)) =
          ∏ i ∈ Finset.univ.filter (fun i : Fin q => k.val ≤ i.val),
            (1 + ep i) := by
        symm
        apply Finset.prod_subset (Finset.subset_univ _)
        intro i _ hi
        have hnot : ¬ k.val ≤ i.val := by simpa using hi
        have hnot' : ¬ k ≤ i := by exact hnot
        simp [ep, hnot']
      _ = ∏ i ∈ Finset.Ico k.val q, (1 + p04ErrorAt e i) := by
        apply Finset.prod_bij (fun i _ => i.val)
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
          exact Finset.mem_Ico.mpr ⟨hi, i.isLt⟩
        · intro i₁ _ i₂ _ heq
          exact Fin.ext heq
        · intro l hl
          have hl' := Finset.mem_Ico.mp hl
          refine ⟨⟨l, hl'.2⟩, ?_, rfl⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hl'.1
        · intro i hi
          have hki : k.val ≤ i.val := by
            simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
          have hki' : k ≤ i := by exact hki
          simp [ep, hki', p04ErrorAt, i.isLt]
  rw [← hprod]
  exact p04_product_gamma_bound hu hv ep hep

private noncomputable def p04RunTermAt {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (k : ℕ) : ℝ :=
  if h : k < q then
    ∑ j : Fin b, run.x ⟨k, h⟩ j * run.y ⟨k, h⟩ j *
      (1 + run.termTheta ⟨k, h⟩ j)
  else 0

private noncomputable def p04UnrollTerm {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (m k : ℕ) : ℝ :=
  p04RunTermAt run k *
      (∏ l ∈ Finset.Ico (k + 1) m,
        (1 + p04ErrorAt run.carryTheta l)) *
      (∏ l ∈ Finset.Ico k m,
        (1 + p04ErrorAt run.delta l))

private lemma p04_unroll_term_succ_of_lt {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) {m k : ℕ}
    (hk : k < m) (hm : m < q) :
    p04UnrollTerm run (m + 1) k =
      p04UnrollTerm run m k * (1 + run.carryTheta ⟨m, hm⟩) *
        (1 + run.delta ⟨m, hm⟩) := by
  unfold p04UnrollTerm
  rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt hk)]
  rw [Finset.prod_Ico_succ_top (Nat.le_of_lt hk)]
  simp only [p04ErrorAt, dif_pos hm]
  ring

private lemma p04_unroll_term_self {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) {m : ℕ} (hm : m < q) :
    p04UnrollTerm run (m + 1) m =
      (∑ j : Fin b, run.x ⟨m, hm⟩ j * run.y ⟨m, hm⟩ j *
        (1 + run.termTheta ⟨m, hm⟩ j)) *
          (1 + run.delta ⟨m, hm⟩) := by
  simp [p04UnrollTerm, p04RunTermAt, p04ErrorAt, hm]

private lemma p04_state_unroll_aux {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (m : ℕ) (hm : m ≤ q) :
    run.state m = ∑ k ∈ Finset.range m, p04UnrollTerm run m k := by
  induction m with
  | zero => simp [run.state_zero]
  | succ m ih =>
      have hm_lt : m < q := lt_of_lt_of_le (Nat.lt_succ_self m) hm
      let km : Fin q := ⟨m, hm_lt⟩
      have hsum :
          (∑ k ∈ Finset.range m, p04UnrollTerm run (m + 1) k) =
            (∑ k ∈ Finset.range m, p04UnrollTerm run m k) *
              (1 + run.carryTheta km) * (1 + run.delta km) := by
        calc
          (∑ k ∈ Finset.range m, p04UnrollTerm run (m + 1) k) =
              ∑ k ∈ Finset.range m,
                p04UnrollTerm run m k * (1 + run.carryTheta km) *
                  (1 + run.delta km) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    exact p04_unroll_term_succ_of_lt run
                      (Finset.mem_range.mp hk) hm_lt
          _ = (∑ k ∈ Finset.range m, p04UnrollTerm run m k) *
                (1 + run.carryTheta km) * (1 + run.delta km) := by
                  rw [Finset.sum_mul, Finset.sum_mul]
      rw [Finset.sum_range_succ, hsum]
      rw [run.state_step km, ih (Nat.le_of_succ_le hm)]
      rw [p04_unroll_term_self run hm_lt]
      ring

private lemma p04_unroll_term_final {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (k : Fin q) :
    p04UnrollTerm run q k.val =
      ∑ j : Fin b, run.x k j * run.y k j *
        p04InclusiveErrorProduct run.delta k *
          (∏ r : Fin n, (1 + run.innerPathError k j r)) := by
  unfold p04UnrollTerm p04RunTermAt
  simp only [dif_pos k.isLt]
  unfold p04InclusiveErrorProduct
  simp_rw [run.inner_path_factor]
  unfold p04StrictErrorProduct
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

private lemma p04_state_factorization {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed =
      ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          p04InclusiveErrorProduct run.delta k *
            (∏ r : Fin n, (1 + run.innerPathError k j r)) := by
  rw [P04BlockFmaDotRun.computed, p04_state_unroll_aux run q le_rfl]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro k _
  exact p04_unroll_term_final run k

private lemma p04_effective_nonneg (uBar uFma uOut : ℝ)
    (hFma : 0 ≤ uFma) (hOut : 0 ≤ uOut) :
    0 ≤ p04EffectiveFmaRoundoff uBar uFma uOut := by
  unfold p04EffectiveFmaRoundoff
  split_ifs <;> positivity

private lemma p04_gamma_valid_mono {u : ℝ} {a c : ℕ}
    (hu : 0 ≤ u) (hac : a ≤ c) (hv : GammaValid u c) : GammaValid u a := by
  unfold GammaValid at hv ⊢
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hac) hu) hv

private lemma p04_sum_factor_error_bound {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ha : ∀ k j, |alpha k j| ≤ A)
    (hb : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hpoint : ∀ k j,
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
        (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    have hfac :
        |1 - (1 + alpha k j) * (1 + beta k j)| ≤ A + B + A * B := by
      rw [show 1 - (1 + alpha k j) * (1 + beta k j) =
        -(alpha k j + beta k j + alpha k j * beta k j) by ring]
      rw [abs_neg]
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
            exact add_le_add
              (add_le_add (ha k j) (hb k j))
              (mul_le_mul (ha k j) (hb k j) (abs_nonneg _) hA)
    rw [show x k j * y k j -
        x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
      (x k j * y k j) *
        (1 - (1 + alpha k j) * (1 + beta k j)) by ring]
    rw [abs_mul, abs_mul]
    calc
      (|x k j| * |y k j|) * |1 - (1 + alpha k j) * (1 + beta k j)| ≤
          (|x k j| * |y k j|) * (A + B + A * B) := by
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
      intro k _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
          (A + B + A * B) * (|x k j| * |y k j|) := by
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro j _
      exact hpoint k j
    _ = (A + B + A * B) * ∑ k : Fin q, ∑ j : Fin b,
          |x k j| * |y k j| := by
      simp_rw [Finset.mul_sum]

private lemma p04_right_length_le_dimension {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) : q + b - 1 ≤ n := by
  rw [run.dimension_eq]
  obtain ⟨q, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt run.block_count_pos)
  obtain ⟨b, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt run.block_size_pos)
  calc
    (q + 1) + (b + 1) - 1 = q + b + 1 := by omega
    _ ≤ q * b + (q + b + 1) := by omega
    _ = (q + 1) * (b + 1) := by ring

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
  have hgammaE : 0 ≤ gamma uE q :=
    p04_gamma_nonneg huE run.effective_gamma_valid
  have hgammaN : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have hrepr :
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) := by
    simpa [alpha, beta] using p04_state_factorization run
  have halpha : ∀ k j, |alpha k j| ≤ gamma uE q := by
    intro k j
    exact p04_inclusive_gamma_bound huE run.effective_gamma_valid
      run.delta run.delta_bound k
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    exact p04_product_gamma_bound run.uBar_nonneg run.internal_gamma_valid
      (fun r => run.innerPathError k j r)
      (fun r => run.inner_path_error_bound k j r)
  have hmain :
      |p04BlockedDot run.x run.y - run.computed| ≤
        (gamma uE q + gamma run.uBar n +
            gamma uE q * gamma run.uBar n) *
          p04BlockedAbsDot run.x run.y := by
    rw [hrepr]
    exact p04_sum_factor_error_bound run.x run.y alpha beta
      hgammaE hgammaN halpha hbeta
  refine ⟨alpha, beta, hrepr, ?_, hbeta, ?_, ?_, ?_⟩
  · simpa [uE] using halpha
  · simpa [p04BlockFmaCoeff, uE] using hmain
  · intro horder
    have hlen : q + b - 1 ≤ n := p04_right_length_le_dimension run
    have hvalidRight : GammaValid run.uBar (q + b - 1) :=
      p04_gamma_valid_mono run.uBar_nonneg hlen run.internal_gamma_valid
    have hgammaRight : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hvalidRight
    have hbetaRight : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hpaths :
          (∏ r : Fin n, (1 + run.innerPathError k j r)) =
            ∏ r : Fin (q + b - 1),
              (1 + run.rightToLeftPathError k j r) :=
        (run.inner_path_factor k j).trans
          ((run.right_to_left_path_factor horder k j).symm)
      dsimp [beta]
      rw [hpaths]
      exact p04_product_gamma_bound run.uBar_nonneg hvalidRight
        (fun r => run.rightToLeftPathError k j r)
        (fun r => run.right_to_left_path_error_bound horder k j r)
    refine ⟨hbetaRight, ?_⟩
    rw [hrepr]
    simpa [p04BlockFmaCoeff, uE] using
      (p04_sum_factor_error_bound run.x run.y alpha beta
        hgammaE hgammaRight halpha hbetaRight)
  · rintro ⟨hout, hbar⟩
    have huEzero : uE = 0 := by
      simp [uE, p04EffectiveFmaRoundoff, not_lt_of_ge hout, hbar]
    have halphaZero : ∀ k j, alpha k j = 0 := by
      intro k j
      have h := halpha k j
      rw [huEzero] at h
      simp only [gamma, Nat.cast_ofNat, mul_zero, zero_div] at h
      exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
    refine ⟨halphaZero, ?_⟩
    simpa [huEzero, gamma] using hmain

end HighamBench
