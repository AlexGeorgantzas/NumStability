import HighamBench.P04Definitions
import NumStability.Analysis.Rounding

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u m) : 0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p04_GammaValid_mono {u : ℝ} {k m : ℕ}
    (hu : 0 ≤ u) (hkm : k ≤ m) (hm : GammaValid u m) :
    GammaValid u k := by
  unfold GammaValid at *
  have hcast : (k : ℝ) ≤ (m : ℝ) := by exact_mod_cast hkm
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hm

private lemma p04_fin_prod_error_bound {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u m)
    (error : Fin m → ℝ) (herror : ∀ i, |error i| ≤ u) :
    |(∏ i : Fin m, (1 + error i)) - 1| ≤ gamma u m := by
  let fp := NumStability.FPModel.exactWithUnitRoundoff u hu
  have hvalid' : NumStability.gammaValid fp m := by
    simpa [fp, NumStability.gammaValid, GammaValid] using hvalid
  obtain ⟨theta, htheta, hprod⟩ :=
    NumStability.prod_error_bound fp m error herror hvalid'
  have htheta' : |theta| ≤ gamma u m := by
    simpa [fp, NumStability.gamma, gamma] using htheta
  rw [hprod]
  simpa using htheta'

private lemma p04_Ico_error_bound {u : ℝ} {q : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u q)
    (error : Fin q → ℝ) (herror : ∀ i, |error i| ≤ u) (a : ℕ) :
    |(∏ l ∈ Finset.Ico a q, (1 + p04ErrorAt error l)) - 1| ≤ gamma u q := by
  let padded : Fin q → ℝ := fun i => if a ≤ i.val then error i else 0
  have hpadded : ∀ i, |padded i| ≤ u := by
    intro i
    simp only [padded]
    split_ifs
    · exact herror i
    · simpa using hu
  have hbound := p04_fin_prod_error_bound hu hvalid padded hpadded
  have hprod :
      (∏ i : Fin q, (1 + padded i)) =
        ∏ l ∈ Finset.Ico a q, (1 + p04ErrorAt error l) := by
    dsimp only [padded]
    calc
      (∏ i : Fin q, (1 + if a ≤ i.val then error i else 0)) =
          ∏ i : Fin q,
            (1 + if a ≤ i.val then p04ErrorAt error i.val else 0) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [p04ErrorAt, i.isLt]
      _ = ∏ l ∈ Finset.range q,
          (1 + if a ≤ l then p04ErrorAt error l else 0) :=
        Fin.prod_univ_eq_prod_range
          (fun l => 1 + if a ≤ l then p04ErrorAt error l else 0) q
      _ = ∏ l ∈ Finset.Ico a q, (1 + p04ErrorAt error l) := by
        simp_rw [show ∀ l : ℕ,
          (1 + if a ≤ l then p04ErrorAt error l else 0) =
            if a ≤ l then (1 + p04ErrorAt error l) else 1 by
              intro l; split_ifs <;> ring]
        rw [← Finset.prod_filter]
        congr 1
        ext l
        simp [Finset.mem_Ico, and_comm]
  rwa [hprod] at hbound

private lemma p04_unroll_state {q : ℕ}
    (state : ℕ → ℝ) (carry delta block : Fin q → ℝ)
    (hzero : state 0 = 0)
    (hstep : ∀ k : Fin q,
      state (k.val + 1) =
        (state k.val * (1 + carry k) + block k) * (1 + delta k)) :
    state q = ∑ k : Fin q, block k *
      p04StrictErrorProduct carry k * p04InclusiveErrorProduct delta k := by
  let B : ℕ → ℝ := fun k => if hk : k < q then block ⟨k, hk⟩ else 0
  let C : ℕ → ℝ := p04ErrorAt carry
  let D : ℕ → ℝ := p04ErrorAt delta
  have formula : ∀ m : ℕ, m ≤ q →
      state m = ∑ k ∈ Finset.range m,
        B k * (∏ l ∈ Finset.Ico (k + 1) m, (1 + C l)) *
          (∏ l ∈ Finset.Ico k m, (1 + D l)) := by
    intro m hm
    induction m with
    | zero => simpa using hzero
    | succ m ih =>
      have hmq : m < q := Nat.lt_of_succ_le hm
      have ihm := ih (Nat.le_of_succ_le hm)
      rw [hstep ⟨m, hmq⟩, ihm, Finset.sum_range_succ]
      have hC : C m = carry ⟨m, hmq⟩ := by simp [C, p04ErrorAt, hmq]
      have hD : D m = delta ⟨m, hmq⟩ := by simp [D, p04ErrorAt, hmq]
      have hB : B m = block ⟨m, hmq⟩ := by simp [B, hmq]
      rw [← hC, ← hD, ← hB]
      rw [add_mul, Finset.sum_mul, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hkm : k < m := Finset.mem_range.mp hk
        rw [Finset.prod_Ico_succ_top (Nat.succ_le_of_lt hkm),
          Finset.prod_Ico_succ_top (Nat.le_of_lt hkm)]
        ring
      · simp
  have hq := formula q le_rfl
  rw [hq]
  calc
    (∑ k ∈ Finset.range q,
        B k * (∏ l ∈ Finset.Ico (k + 1) q, (1 + C l)) *
          (∏ l ∈ Finset.Ico k q, (1 + D l))) =
      ∑ k : Fin q,
        B k.val * (∏ l ∈ Finset.Ico (k.val + 1) q, (1 + C l)) *
          (∏ l ∈ Finset.Ico k.val q, (1 + D l)) :=
        (Fin.sum_univ_eq_sum_range (fun k =>
          B k * (∏ l ∈ Finset.Ico (k + 1) q, (1 + C l)) *
            (∏ l ∈ Finset.Ico k q, (1 + D l))) q).symm
    _ = ∑ k : Fin q, block k *
        p04StrictErrorProduct carry k * p04InclusiveErrorProduct delta k := by
      apply Finset.sum_congr rfl
      intro k hk
      simp only [B, dif_pos k.isLt, p04StrictErrorProduct,
        p04InclusiveErrorProduct, C, D]

private lemma p04_factored_sum_error {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : ∀ k j, |alpha k j| ≤ A)
    (hbeta : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hterm : ∀ k j,
      |x k j * y k j - x k j * y k j *
          (1 + alpha k j) * (1 + beta k j)| ≤
        (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    have habs : |alpha k j + beta k j + alpha k j * beta k j| ≤
        A + B + A * B := by
      calc
        |alpha k j + beta k j + alpha k j * beta k j| ≤
            |alpha k j + beta k j| + |alpha k j * beta k j| := abs_add_le _ _
        _ ≤ |alpha k j| + |beta k j| +
            |alpha k j| * |beta k j| := by
          exact add_le_add (abs_add_le _ _) (by rw [abs_mul])
        _ ≤ A + B + A * B := by
          exact add_le_add (add_le_add (halpha k j) (hbeta k j))
            (mul_le_mul (halpha k j) (hbeta k j) (abs_nonneg _) hA)
    rw [show x k j * y k j - x k j * y k j *
        (1 + alpha k j) * (1 + beta k j) =
          -(x k j * y k j) *
            (alpha k j + beta k j + alpha k j * beta k j) by ring,
      abs_mul, abs_neg, abs_mul]
    calc
      |x k j| * |y k j| *
          |alpha k j + beta k j + alpha k j * beta k j| ≤
          (|x k j| * |y k j|) * (A + B + A * B) :=
        mul_le_mul_of_nonneg_left habs
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (A + B + A * B) * (|x k j| * |y k j|) := by ring
  rw [p04BlockedDot, p04BlockedAbsDot, ← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin q,
        ((∑ j : Fin b, x k j * y k j) -
          ∑ j : Fin b, x k j * y k j *
            (1 + alpha k j) * (1 + beta k j))| ≤
        ∑ k : Fin q, |(∑ j : Fin b, x k j * y k j) -
          ∑ j : Fin b, x k j * y k j *
            (1 + alpha k j) * (1 + beta k j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        (A + B + A * B) * (|x k j| * |y k j|) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Finset.sum_sub_distrib]
      exact le_trans (Finset.abs_sum_le_sum_abs _ _)
        (Finset.sum_le_sum fun j _ => hterm k j)
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
  let alpha : Fin q → Fin b → ℝ := fun k _ =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have huEff : 0 ≤ uEff := by
    dsimp only [uEff, p04EffectiveFmaRoundoff]
    split_ifs
    · exact run.uOut_nonneg
    · exact le_rfl
    · exact run.uFma_nonneg
  have halpha : ∀ k j, |alpha k j| ≤ gamma uEff q := by
    intro k j
    exact p04_Ico_error_bound huEff run.effective_gamma_valid
      run.delta run.delta_bound k.val
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    exact p04_fin_prod_error_bound run.uBar_nonneg run.internal_gamma_valid
      (run.innerPathError k j) (run.inner_path_error_bound k j)
  have hcomputed : run.computed =
      ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j * (1 + alpha k j) * (1 + beta k j) := by
    have hunroll := p04_unroll_state run.state run.carryTheta run.delta
      (fun k => ∑ j : Fin b,
        run.x k j * run.y k j * (1 + run.termTheta k j))
      run.state_zero run.state_step
    unfold P04BlockFmaDotRun.computed
    rw [hunroll]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    have hpath := run.inner_path_factor k j
    dsimp only [alpha, beta]
    rw [hpath]
    ring
  have hA : 0 ≤ gamma uEff q :=
    p04_gamma_nonneg huEff run.effective_gamma_valid
  have hB : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have herror :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    have h := p04_factored_sum_error run.x run.y alpha beta
      (gamma uEff q) (gamma run.uBar n) hA hB halpha hbeta
    rw [← hcomputed] at h
    simpa [p04BlockFmaCoeff] using h
  have hshort : q + b - 1 ≤ n := by
    calc
      q + b - 1 ≤ q * b := Nat.add_sub_one_le_mul
        (Nat.ne_of_gt run.block_count_pos) (Nat.ne_of_gt run.block_size_pos)
      _ = n := run.dimension_eq.symm
  have hshortValid : GammaValid run.uBar (q + b - 1) :=
    p04_GammaValid_mono run.uBar_nonneg hshort run.internal_gamma_valid
  have hright : run.order = P04BlockEvaluationOrder.rightToLeft →
      (∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1)) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uEff run.uBar q (q + b - 1) *
          p04BlockedAbsDot run.x run.y := by
    intro horder
    have hbetaRight : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hinner := run.inner_path_factor k j
      have hrtl := run.right_to_left_path_factor horder k j
      have heq :
          (∏ r : Fin n, (1 + run.innerPathError k j r)) =
            ∏ r : Fin (q + b - 1),
              (1 + run.rightToLeftPathError k j r) := hinner.trans hrtl.symm
      dsimp only [beta]
      rw [heq]
      exact p04_fin_prod_error_bound run.uBar_nonneg hshortValid
        (run.rightToLeftPathError k j)
        (run.right_to_left_path_error_bound horder k j)
    refine ⟨hbetaRight, ?_⟩
    have hBRight : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hshortValid
    have h := p04_factored_sum_error run.x run.y alpha beta
      (gamma uEff q) (gamma run.uBar (q + b - 1))
      hA hBRight halpha hbetaRight
    rw [← hcomputed] at h
    simpa [p04BlockFmaCoeff] using h
  have hexact : run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
      (∀ k j, alpha k j = 0) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        gamma run.uBar n * p04BlockedAbsDot run.x run.y := by
    rintro ⟨hout, hubar⟩
    have huEffZero : uEff = 0 := by
      simp [uEff, p04EffectiveFmaRoundoff, not_lt_of_ge hout, hubar]
    have hdeltaZero : ∀ k, run.delta k = 0 := by
      intro k
      have hk := run.delta_bound k
      change |run.delta k| ≤ uEff at hk
      rw [huEffZero] at hk
      exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
    have halphaZero : ∀ k j, alpha k j = 0 := by
      intro k j
      simp [alpha, p04InclusiveErrorProduct, p04ErrorAt, hdeltaZero]
    refine ⟨halphaZero, ?_⟩
    have h := p04_factored_sum_error run.x run.y alpha beta
      0 (gamma run.uBar n) (le_rfl) hB
      (by intro k j; simp [halphaZero k j]) hbeta
    rw [← hcomputed] at h
    simpa using h
  exact ⟨alpha, beta, hcomputed, halpha, hbeta, herror, hright, hexact⟩

end HighamBench
