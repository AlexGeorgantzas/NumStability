import HighamBench.P04Definitions
import NumStability.Analysis.Rounding

namespace HighamBench

open scoped BigOperators

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u m) :
    0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p04_product_error_le_gamma {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u m)
    (error : Fin m → ℝ) (herror : ∀ i, |error i| ≤ u) :
    |(∏ i : Fin m, (1 + error i)) - 1| ≤ gamma u m := by
  let fp := NumStability.FPModel.exactWithUnitRoundoff u hu
  have hvalid' : NumStability.gammaValid fp m := by
    simpa [fp, NumStability.FPModel.exactWithUnitRoundoff,
      NumStability.gammaValid, GammaValid] using hvalid
  obtain ⟨theta, htheta, hprod⟩ :=
    NumStability.prod_error_bound fp m error (by
      intro i
      simpa [fp, NumStability.FPModel.exactWithUnitRoundoff] using herror i)
      hvalid'
  calc
    |(∏ i : Fin m, (1 + error i)) - 1| = |theta| := by rw [hprod]; ring_nf
    _ ≤ NumStability.gamma fp m := htheta
    _ = gamma u m := by
      simp [fp, NumStability.gamma, gamma,
        NumStability.FPModel.exactWithUnitRoundoff]

private lemma p04_gammaValid_mono {u : ℝ} (hu : 0 ≤ u) {r m : ℕ}
    (hrm : r ≤ m) (hm : GammaValid u m) : GammaValid u r := by
  unfold GammaValid at *
  have hcast : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hrm
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hm

private lemma p04_add_sub_one_le_mul {q b : ℕ} (hq : 0 < q) (hb : 0 < b) :
    q + b - 1 ≤ q * b := by
  cases q with
  | zero => omega
  | succ q =>
    cases b with
    | zero => omega
    | succ b =>
      have hleft : Nat.succ q + Nat.succ b - 1 = q + b + 1 := by omega
      have hright : Nat.succ q * Nat.succ b = q * b + q + b + 1 := by
        simp [Nat.succ_mul, Nat.mul_succ]
        omega
      rw [hleft, hright]
      omega

private lemma p04_inclusive_product_eq_masked {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) :
    p04InclusiveErrorProduct error k =
      ∏ i : Fin q, (1 + if k.val ≤ i.val then error i else 0) := by
  unfold p04InclusiveErrorProduct
  calc
    (∏ l ∈ Finset.Ico k.val q, (1 + p04ErrorAt error l)) =
        ∏ l ∈ Finset.range q,
          (1 + if k.val ≤ l then p04ErrorAt error l else 0) := by
      apply Finset.prod_subset_one_on_sdiff
      · intro l hl
        simp only [Finset.mem_Ico] at hl
        simpa using hl.2
      · intro l hl
        simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico] at hl
        have hnot : ¬ k.val ≤ l := by
          intro hkl
          exact hl.2 ⟨hkl, hl.1⟩
        simp [hnot]
      · intro l hl
        simp only [Finset.mem_Ico] at hl
        simp [hl.1]
    _ = ∏ i : Fin q, (1 + if k.val ≤ i.val then error i else 0) := by
      rw [← Fin.prod_univ_eq_prod_range
        (fun l => 1 + if k.val ≤ l then p04ErrorAt error l else 0) q]
      apply Finset.prod_congr rfl
      intro i _
      simp [p04ErrorAt, i.isLt]

private lemma p04_inclusive_product_error_le_gamma {q : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (hvalid : GammaValid u q)
    (error : Fin q → ℝ) (herror : ∀ i, |error i| ≤ u) (k : Fin q) :
    |p04InclusiveErrorProduct error k - 1| ≤ gamma u q := by
  rw [p04_inclusive_product_eq_masked]
  apply p04_product_error_le_gamma hu hvalid
  intro i
  split_ifs with h
  · exact herror i
  · simp [hu]

private lemma p04_two_factor_sum_error
    {q b : ℕ} (x y alpha beta : Fin q → Fin b → ℝ)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : ∀ k j, |alpha k j| ≤ A)
    (hbeta : ∀ k j, |beta k j| ≤ B) :
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
            |alpha k j| + |beta k j| + |alpha k j * beta k j| := by
              calc
                |alpha k j + beta k j + alpha k j * beta k j| ≤
                    |alpha k j + beta k j| + |alpha k j * beta k j| :=
                      abs_add_le _ _
                _ ≤ |alpha k j| + |beta k j| +
                    |alpha k j * beta k j| := by
                      linarith [abs_add_le (alpha k j) (beta k j)]
        _ = |alpha k j| + |beta k j| +
            |alpha k j| * |beta k j| := by rw [abs_mul]
        _ ≤ A + B + A * B := by
          exact add_le_add
            (add_le_add (halpha k j) (hbeta k j))
            (mul_le_mul (halpha k j) (hbeta k j) (abs_nonneg _) hA)
    calc
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
          (|x k j| * |y k j|) *
            |alpha k j + beta k j + alpha k j * beta k j| := by
              have heq : x k j * y k j -
                  x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
                    -(x k j * y k j) *
                      (alpha k j + beta k j + alpha k j * beta k j) := by
                ring
              rw [heq, abs_mul, abs_neg, abs_mul]
      _ ≤ (|x k j| * |y k j|) * (A + B + A * B) := by
        exact mul_le_mul_of_nonneg_left hab
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = (A + B + A * B) * (|x k j| * |y k j|) := by ring
  unfold p04BlockedDot p04BlockedAbsDot
  calc
    |(∑ k, ∑ j, x k j * y k j) -
        ∑ k, ∑ j, x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
        |∑ k, ∑ j, (x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j))| := by
            congr 1
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k, |∑ j, (x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ j, |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, ∑ j, (A + B + A * B) * (|x k j| * |y k j|) := by
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum (fun j _ => hterm k j)
    _ = (A + B + A * B) * ∑ k, ∑ j, |x k j| * |y k j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.mul_sum]

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
  let blockTerm : Fin q → ℝ := fun k =>
    ∑ j : Fin b, run.x k j * run.y k j * (1 + run.termTheta k j)
  let blockTermAt : ℕ → ℝ := fun k =>
    if h : k < q then blockTerm ⟨k, h⟩ else 0
  have state_expansion : ∀ m : ℕ, ∀ hm : m ≤ q,
      run.state m =
        ∑ k ∈ Finset.range m,
          blockTermAt k *
            (∏ l ∈ Finset.Ico (k + 1) m,
              (1 + p04ErrorAt run.carryTheta l)) *
            (∏ l ∈ Finset.Ico k m,
              (1 + p04ErrorAt run.delta l)) := by
    intro m hm
    induction m with
    | zero => simp [run.state_zero]
    | succ m ih =>
      have hmq : m < q := Nat.lt_of_succ_le hm
      have ihm := ih (Nat.le_of_lt hmq)
      rw [run.state_step ⟨m, hmq⟩, ihm, Finset.sum_range_succ]
      have hold :
          (∑ k ∈ Finset.range m,
            blockTermAt k *
                (∏ l ∈ Finset.Ico (k + 1) (m + 1),
                  (1 + p04ErrorAt run.carryTheta l)) *
                (∏ l ∈ Finset.Ico k (m + 1),
                  (1 + p04ErrorAt run.delta l))) =
            (∑ k ∈ Finset.range m,
              blockTermAt k *
                  (∏ l ∈ Finset.Ico (k + 1) m,
                    (1 + p04ErrorAt run.carryTheta l)) *
                  (∏ l ∈ Finset.Ico k m,
                    (1 + p04ErrorAt run.delta l))) *
              (1 + run.carryTheta ⟨m, hmq⟩) *
              (1 + run.delta ⟨m, hmq⟩) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hkm : k < m := Finset.mem_range.mp hk
        rw [Finset.prod_Ico_succ_top (Nat.succ_le_iff.mpr hkm),
          Finset.prod_Ico_succ_top (Nat.le_of_lt hkm)]
        simp only [p04ErrorAt, dif_pos hmq]
        ring
      rw [hold]
      simp [blockTermAt, blockTerm, p04ErrorAt, hmq,
        Finset.prod_Ico_succ_top]
      ring
  let alpha : Fin q → Fin b → ℝ := fun k _ =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have heff_nonneg : 0 ≤
      p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut := by
    unfold p04EffectiveFmaRoundoff
    split_ifs <;>
      linarith [run.uBar_nonneg, run.uFma_nonneg, run.uOut_nonneg]
  have hcomputed : run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j * (1 + alpha k j) * (1 + beta k j) := by
    rw [P04BlockFmaDotRun.computed, state_expansion q le_rfl]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    simp only [blockTermAt, dif_pos k.isLt]
    dsimp only [blockTerm, alpha, beta]
    unfold p04InclusiveErrorProduct
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [run.inner_path_factor k j]
    simp only [p04StrictErrorProduct, Nat.add_comm]
    ring
  have halpha : ∀ k j, |alpha k j| ≤
      gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q := by
    intro k j
    dsimp [alpha]
    exact p04_inclusive_product_error_le_gamma
      heff_nonneg
      run.effective_gamma_valid run.delta run.delta_bound k
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    dsimp [beta]
    exact p04_product_error_le_gamma run.uBar_nonneg
      run.internal_gamma_valid (run.innerPathError k j)
      (run.inner_path_error_bound k j)
  have hgamma_eff_nonneg :
      0 ≤ gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q :=
    p04_gamma_nonneg heff_nonneg run.effective_gamma_valid
  have hgamma_internal_nonneg : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  refine ⟨alpha, beta, hcomputed, halpha, hbeta, ?_, ?_, ?_⟩
  · rw [hcomputed]
    simpa [p04BlockFmaCoeff] using
      p04_two_factor_sum_error run.x run.y alpha beta
        hgamma_eff_nonneg hgamma_internal_nonneg halpha hbeta
  · intro horder
    have hcount : q + b - 1 ≤ n := by
      rw [run.dimension_eq]
      exact p04_add_sub_one_le_mul run.block_count_pos run.block_size_pos
    have hright_valid : GammaValid run.uBar (q + b - 1) :=
      p04_gammaValid_mono run.uBar_nonneg hcount run.internal_gamma_valid
    have hbeta_right : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hproducts :
          (∏ r : Fin n, (1 + run.innerPathError k j r)) =
            ∏ r : Fin (q + b - 1),
              (1 + run.rightToLeftPathError k j r) := by
        calc
          (∏ r : Fin n, (1 + run.innerPathError k j r)) =
              (1 + run.termTheta k j) *
                p04StrictErrorProduct run.carryTheta k :=
            run.inner_path_factor k j
          _ = ∏ r : Fin (q + b - 1),
                (1 + run.rightToLeftPathError k j r) :=
            (run.right_to_left_path_factor horder k j).symm
      dsimp [beta]
      rw [hproducts]
      exact p04_product_error_le_gamma run.uBar_nonneg hright_valid
        (run.rightToLeftPathError k j)
        (run.right_to_left_path_error_bound horder k j)
    refine ⟨hbeta_right, ?_⟩
    rw [hcomputed]
    have hgamma_right_nonneg : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hright_valid
    simpa [p04BlockFmaCoeff] using
      p04_two_factor_sum_error run.x run.y alpha beta
        hgamma_eff_nonneg hgamma_right_nonneg halpha hbeta_right
  · rintro ⟨huout, hubar⟩
    have heff_zero :
        p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut = 0 := by
      unfold p04EffectiveFmaRoundoff
      rw [if_neg (not_lt.mpr huout)]
      simp [hubar]
    have hdelta_zero : ∀ k, run.delta k = 0 := by
      intro k
      have hk := run.delta_bound k
      rw [heff_zero] at hk
      exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
    have halpha_zero : ∀ k j, alpha k j = 0 := by
      intro k j
      dsimp [alpha]
      have herrorAt : ∀ l, p04ErrorAt run.delta l = 0 := by
        intro l
        unfold p04ErrorAt
        split_ifs with hl
        · exact hdelta_zero ⟨l, hl⟩
        · rfl
      simp [p04InclusiveErrorProduct, herrorAt]
    refine ⟨halpha_zero, ?_⟩
    rw [hcomputed]
    simpa using
      p04_two_factor_sum_error run.x run.y alpha beta
        (show (0 : ℝ) ≤ 0 by norm_num) hgamma_internal_nonneg
        (fun k j => by simp [halpha_zero k j]) hbeta

end HighamBench
