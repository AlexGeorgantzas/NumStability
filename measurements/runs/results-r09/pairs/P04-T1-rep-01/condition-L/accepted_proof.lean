import HighamBench.P04Definitions
import NumStability.Analysis.Rounding

namespace HighamBench

open scoped BigOperators

private noncomputable def p04TermAt {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (k : ℕ) : ℝ :=
  if h : k < q then
    ∑ j : Fin b, run.x ⟨k, h⟩ j * run.y ⟨k, h⟩ j *
      (1 + run.termTheta ⟨k, h⟩ j)
  else 0

private lemma p04_state_expansion_aux {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (t : ℕ) (ht : t ≤ q) :
    run.state t =
      ∑ k ∈ Finset.range t, p04TermAt run k *
        (∏ l ∈ Finset.Ico (k + 1) t,
          (1 + p04ErrorAt run.carryTheta l)) *
        (∏ l ∈ Finset.Ico k t,
          (1 + p04ErrorAt run.delta l)) := by
  induction t with
  | zero => simp [run.state_zero]
  | succ t ih =>
      have hlt : t < q := Nat.lt_of_succ_le ht
      let kt : Fin q := ⟨t, hlt⟩
      have hcarry : p04ErrorAt run.carryTheta t = run.carryTheta kt := by
        simp [p04ErrorAt, hlt, kt]
      have hdelta : p04ErrorAt run.delta t = run.delta kt := by
        simp [p04ErrorAt, hlt, kt]
      have hterm : p04TermAt run t =
          ∑ j : Fin b, run.x kt j * run.y kt j *
            (1 + run.termTheta kt j) := by
        simp [p04TermAt, hlt, kt]
      have hold :
          (∑ k ∈ Finset.range t, p04TermAt run k *
              (∏ l ∈ Finset.Ico (k + 1) (t + 1),
                (1 + p04ErrorAt run.carryTheta l)) *
              (∏ l ∈ Finset.Ico k (t + 1),
                (1 + p04ErrorAt run.delta l))) =
            ((∑ k ∈ Finset.range t, p04TermAt run k *
                (∏ l ∈ Finset.Ico (k + 1) t,
                  (1 + p04ErrorAt run.carryTheta l)) *
                (∏ l ∈ Finset.Ico k t,
                  (1 + p04ErrorAt run.delta l))) *
              (1 + run.carryTheta kt)) * (1 + run.delta kt) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hkle : k + 1 ≤ t := by
          exact Finset.mem_range.mp hk
        rw [Finset.prod_Ico_succ_top hkle,
          Finset.prod_Ico_succ_top (Nat.le_of_lt (Finset.mem_range.mp hk)),
          hcarry, hdelta]
        ring
      rw [run.state_step kt, ih (Nat.le_trans (Nat.le_succ t) ht)]
      rw [Finset.sum_range_succ, hold, hterm]
      simp only [Finset.Ico_self, Finset.prod_empty, one_mul,
        Finset.prod_Ico_succ_top (Nat.le_refl t), hdelta]
      ring

private lemma p04_state_expansion {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j * (1 + run.termTheta k j) *
        p04StrictErrorProduct run.carryTheta k *
        p04InclusiveErrorProduct run.delta k := by
  rw [P04BlockFmaDotRun.computed, p04_state_expansion_aux run q (le_refl q)]
  rw [← Fin.sum_univ_eq_sum_range
    (fun k : ℕ => p04TermAt run k *
      (∏ l ∈ Finset.Ico (k + 1) q,
        (1 + p04ErrorAt run.carryTheta l)) *
      (∏ l ∈ Finset.Ico k q,
        (1 + p04ErrorAt run.delta l))) q]
  apply Finset.sum_congr rfl
  intro k hk
  simp [p04TermAt, k.isLt, p04StrictErrorProduct,
    p04InclusiveErrorProduct, Finset.sum_mul]

private lemma p04_prod_sub_one_bound {m : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (d : Fin m → ℝ) (hd : ∀ i, |d i| ≤ u)
    (hv : GammaValid u m) :
    |(∏ i : Fin m, (1 + d i)) - 1| ≤ gamma u m := by
  let fp := NumStability.FPModel.exactWithUnitRoundoff u hu
  have hv' : NumStability.gammaValid fp m := by
    simpa [fp, NumStability.FPModel.exactWithUnitRoundoff,
      NumStability.gammaValid, GammaValid] using hv
  have hd' : ∀ i, |d i| ≤ fp.u := by
    intro i
    simpa [fp, NumStability.FPModel.exactWithUnitRoundoff] using hd i
  obtain ⟨theta, htheta, hprod⟩ :=
    NumStability.prod_error_bound fp m d hd' hv'
  rw [hprod]
  simpa [fp, NumStability.FPModel.exactWithUnitRoundoff,
    NumStability.gamma, gamma] using htheta

private lemma p04_inclusive_error_product_bound {q : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (d : Fin q → ℝ) (hd : ∀ i, |d i| ≤ u)
    (hv : GammaValid u q) (k : Fin q) :
    |p04InclusiveErrorProduct d k - 1| ≤ gamma u q := by
  let padded : Fin q → ℝ := fun i =>
    if k ≤ i then d i else 0
  have hpadded : ∀ i, |padded i| ≤ u := by
    intro i
    by_cases hki : k ≤ i
    · simpa [padded, hki] using hd i
    · simp [padded, hki, hu]
  have hbound := p04_prod_sub_one_bound hu padded hpadded hv
  have hprod : (∏ i : Fin q, (1 + padded i)) =
      p04InclusiveErrorProduct d k := by
    rw [p04InclusiveErrorProduct]
    calc
      (∏ i : Fin q, (1 + padded i)) =
          ∏ i : Fin q, (if k ≤ i then 1 + d i else 1) := by
              apply Finset.prod_congr rfl
              intro i hi
              by_cases hki : k ≤ i <;> simp [padded, hki]
      _ =
          ∏ l ∈ Finset.range q,
            (if k.val ≤ l then 1 + p04ErrorAt d l else 1) := by
              simpa [p04ErrorAt] using
                (Fin.prod_univ_eq_prod_range
                  (fun l : ℕ =>
                    if k.val ≤ l then 1 + p04ErrorAt d l else 1) q)
      _ = ∏ l ∈ (Finset.range q).filter (fun l => k.val ≤ l),
            (1 + p04ErrorAt d l) := by
              rw [Finset.prod_filter]
      _ = ∏ l ∈ Finset.Ico k.val q,
            (1 + p04ErrorAt d l) := by
              congr 1
              ext l
              simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
              omega
  rwa [hprod] at hbound

private lemma p04_gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hv : GammaValid u m) : 0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p04_right_path_length_le_dimension {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) : q + b - 1 ≤ n := by
  have hq := run.block_count_pos
  have hb := run.block_size_pos
  rw [run.dimension_eq]
  rcases q with _ | q
  · omega
  rcases b with _ | b
  · omega
  simp only [Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add]
  have hz : 0 ≤ q * b := Nat.zero_le _
  omega

private lemma p04_gamma_valid_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hv : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hv

private lemma p04_forward_error_of_factors {q b : ℕ}
    (x y : Fin q → Fin b → ℝ) (computed ga gb : ℝ)
    (alpha beta : Fin q → Fin b → ℝ)
    (hcomputed : computed = ∑ k : Fin q, ∑ j : Fin b,
      x k j * y k j * (1 + alpha k j) * (1 + beta k j))
    (hga : 0 ≤ ga) (hgb : 0 ≤ gb)
    (halpha : ∀ k j, |alpha k j| ≤ ga)
    (hbeta : ∀ k j, |beta k j| ≤ gb) :
    |p04BlockedDot x y - computed| ≤
      (ga + gb + ga * gb) * p04BlockedAbsDot x y := by
  rw [p04BlockedDot, p04BlockedAbsDot, hcomputed]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin q,
        ((∑ j : Fin b, x k j * y k j) -
          ∑ j : Fin b,
            x k j * y k j * (1 + alpha k j) * (1 + beta k j))| ≤
        ∑ k : Fin q,
          |(∑ j : Fin b, x k j * y k j) -
            ∑ j : Fin b,
              x k j * y k j * (1 + alpha k j) * (1 + beta k j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin q,
          |∑ j : Fin b,
            (x k j * y k j -
              x k j * y k j * (1 + alpha k j) * (1 + beta k j))| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.sum_sub_distrib]
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
        have hab :
            |alpha k j + beta k j + alpha k j * beta k j| ≤
              ga + gb + ga * gb := by
          calc
            |alpha k j + beta k j + alpha k j * beta k j| ≤
                |alpha k j| + |beta k j| + |alpha k j * beta k j| :=
              abs_add_three _ _ _
            _ = |alpha k j| + |beta k j| +
                |alpha k j| * |beta k j| := by rw [abs_mul]
            _ ≤ ga + gb + ga * gb := by
              have hmul : |alpha k j| * |beta k j| ≤ ga * gb :=
                mul_le_mul (halpha k j) (hbeta k j) (abs_nonneg _) hga
              linarith [halpha k j, hbeta k j]
        calc
          |x k j * y k j -
              x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
              |x k j| * |y k j| *
                |alpha k j + beta k j + alpha k j * beta k j| := by
                  rw [show x k j * y k j -
                      x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
                        -(x k j * y k j) *
                          (alpha k j + beta k j + alpha k j * beta k j) by ring,
                    abs_mul, abs_neg, abs_mul]
          _ ≤ |x k j| * |y k j| * (ga + gb + ga * gb) :=
            mul_le_mul_of_nonneg_left hab
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _ = (ga + gb + ga * gb) * (|x k j| * |y k j|) := by ring
    _ = (ga + gb + ga * gb) *
          ∑ k : Fin q, ∑ j : Fin b, |x k j| * |y k j| := by
        simp only [Finset.mul_sum]

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
  let alpha : Fin q → Fin b → ℝ := fun k _j =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have heffective_nonneg :
      0 ≤ p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut := by
    unfold p04EffectiveFmaRoundoff
    split
    · exact run.uOut_nonneg
    · split
      · exact le_refl 0
      · exact run.uFma_nonneg
  have hcomputed :
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) := by
    rw [p04_state_expansion run]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [alpha, beta]
    rw [run.inner_path_factor k j]
    ring
  have halpha : ∀ k j, |alpha k j| ≤
      gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q := by
    intro k j
    exact p04_inclusive_error_product_bound heffective_nonneg run.delta
      run.delta_bound run.effective_gamma_valid k
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    exact p04_prod_sub_one_bound run.uBar_nonneg
      (run.innerPathError k j) (run.inner_path_error_bound k j)
      run.internal_gamma_valid
  have hgamma_effective_nonneg :
      0 ≤ gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q :=
    p04_gamma_nonneg heffective_nonneg run.effective_gamma_valid
  have hgamma_internal_nonneg : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  refine ⟨alpha, beta, hcomputed, halpha, hbeta, ?_, ?_, ?_⟩
  · simpa [p04BlockFmaCoeff] using
      (p04_forward_error_of_factors run.x run.y run.computed
        (gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q)
        (gamma run.uBar n) alpha beta hcomputed
        hgamma_effective_nonneg hgamma_internal_nonneg halpha hbeta)
  · intro horder
    have hlength : q + b - 1 ≤ n :=
      p04_right_path_length_le_dimension run
    have hright_valid : GammaValid run.uBar (q + b - 1) :=
      p04_gamma_valid_mono run.uBar_nonneg hlength run.internal_gamma_valid
    have hbeta_right : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hbeta_eq : beta k j =
          (∏ r : Fin (q + b - 1),
            (1 + run.rightToLeftPathError k j r)) - 1 := by
        dsimp [beta]
        rw [run.inner_path_factor k j,
          ← run.right_to_left_path_factor horder k j]
      rw [hbeta_eq]
      exact p04_prod_sub_one_bound run.uBar_nonneg
        (run.rightToLeftPathError k j)
        (run.right_to_left_path_error_bound horder k j) hright_valid
    refine ⟨hbeta_right, ?_⟩
    have hgamma_right_nonneg : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar_nonneg hright_valid
    simpa [p04BlockFmaCoeff] using
      (p04_forward_error_of_factors run.x run.y run.computed
        (gamma (p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut) q)
        (gamma run.uBar (q + b - 1)) alpha beta hcomputed
        hgamma_effective_nonneg hgamma_right_nonneg halpha hbeta_right)
  · rintro ⟨huOut, huBar⟩
    have heffective_zero :
        p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut = 0 := by
      simp [p04EffectiveFmaRoundoff, not_lt_of_ge huOut, huBar]
    have halpha_zero : ∀ k j, alpha k j = 0 := by
      intro k j
      have h := halpha k j
      rw [heffective_zero] at h
      simp [gamma] at h
      exact h
    refine ⟨halpha_zero, ?_⟩
    simpa using
      (p04_forward_error_of_factors run.x run.y run.computed
        0 (gamma run.uBar n) alpha beta hcomputed
        (le_refl 0) hgamma_internal_nonneg
        (by intro k j; simp [halpha_zero k j]) hbeta)

end HighamBench
