import HighamBench.P04Definitions
import NumStability.Analysis.Rounding

namespace HighamBench

open scoped BigOperators

private noncomputable def p04TermAt {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) (k : ℕ) : ℝ :=
  if h : k < q then
    ∑ j : Fin b,
      run.x ⟨k, h⟩ j * run.y ⟨k, h⟩ j * (1 + run.termTheta ⟨k, h⟩ j)
  else 0

private lemma p04_state_expansion {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    ∀ m : ℕ, m ≤ q →
      run.state m =
        ∑ k ∈ Finset.range m,
          p04TermAt run k *
            (∏ l ∈ Finset.Ico (k + 1) m,
              (1 + p04ErrorAt run.carryTheta l)) *
            (∏ l ∈ Finset.Ico k m,
              (1 + p04ErrorAt run.delta l)) := by
  intro m hm
  induction m with
  | zero => simp [run.state_zero]
  | succ m ih =>
      have hmq : m < q := Nat.lt_of_succ_le hm
      let km : Fin q := ⟨m, hmq⟩
      rw [show run.state (m + 1) =
          (run.state m * (1 + run.carryTheta km) +
            ∑ j : Fin b,
              run.x km j * run.y km j * (1 + run.termTheta km j)) *
            (1 + run.delta km) from run.state_step km]
      rw [ih (Nat.le_of_lt hmq)]
      have hcarry : p04ErrorAt run.carryTheta m = run.carryTheta km := by
        simp [p04ErrorAt, hmq, km]
      have hdelta : p04ErrorAt run.delta m = run.delta km := by
        simp [p04ErrorAt, hmq, km]
      have hterm : p04TermAt run m =
          ∑ j : Fin b,
            run.x km j * run.y km j * (1 + run.termTheta km j) := by
        simp [p04TermAt, hmq, km]
      rw [Finset.sum_range_succ]
      rw [hterm]
      have hcurcarry :
          (∏ l ∈ Finset.Ico (m + 1) (m + 1),
            (1 + p04ErrorAt run.carryTheta l)) = 1 := by simp
      have hcurdelta :
          (∏ l ∈ Finset.Ico m (m + 1),
            (1 + p04ErrorAt run.delta l)) = 1 + run.delta km := by
        rw [Finset.prod_Ico_succ_top (le_refl m)]
        simp [hdelta]
      rw [hcurcarry, hcurdelta]
      simp only [mul_one]
      rw [add_mul]
      apply congrArg (fun z : ℝ => z +
        (∑ j : Fin b,
          run.x km j * run.y km j * (1 + run.termTheta km j)) *
          (1 + run.delta km))
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k < m := Finset.mem_range.mp hk
      rw [Finset.prod_Ico_succ_top (by omega : k + 1 ≤ m),
        Finset.prod_Ico_succ_top (by omega : k ≤ m)]
      rw [hcarry, hdelta]
      ring

private lemma p04_computed_expansion {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed =
      ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j * (1 + run.termTheta k j) *
          p04StrictErrorProduct run.carryTheta k *
          p04InclusiveErrorProduct run.delta k := by
  rw [P04BlockFmaDotRun.computed, p04_state_expansion run q (le_refl q)]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [p04TermAt, k.isLt, dite_true,
    p04StrictErrorProduct, p04InclusiveErrorProduct]
  rw [Finset.sum_mul, Finset.sum_mul]

private lemma p04_effective_nonneg (uBar uFma uOut : ℝ)
    (hBar : 0 ≤ uBar) (hFma : 0 ≤ uFma) (hOut : 0 ≤ uOut) :
    0 ≤ p04EffectiveFmaRoundoff uBar uFma uOut := by
  unfold p04EffectiveFmaRoundoff
  split
  · exact hOut
  · split
    · positivity
    · exact hFma

private lemma p04_prod_error_bound (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (error : Fin m → ℝ)
    (herror : ∀ r, |error r| ≤ u) (hvalid : GammaValid u m) :
    ∃ theta : ℝ, |theta| ≤ gamma u m ∧
      (∏ r : Fin m, (1 + error r)) = 1 + theta := by
  let fp := NumStability.FPModel.exactWithUnitRoundoff u hu
  have hv : NumStability.gammaValid fp m := by
    simpa [NumStability.gammaValid, fp,
      NumStability.FPModel.exactWithUnitRoundoff] using hvalid
  obtain ⟨theta, htheta, hprod⟩ :=
    NumStability.prod_error_bound fp m error (by simpa [fp] using herror) hv
  refine ⟨theta, ?_, hprod⟩
  simpa [gamma, NumStability.gamma, fp,
    NumStability.FPModel.exactWithUnitRoundoff] using htheta

private noncomputable def p04DeltaPath {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) (r : Fin q) : ℝ :=
  if k.val ≤ r.val then p04ErrorAt error r.val else 0

private lemma p04_delta_path_product {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) :
    (∏ r : Fin q, (1 + p04DeltaPath error k r)) =
      p04InclusiveErrorProduct error k := by
  change (∏ r : Fin q,
      (fun i : ℕ => 1 + if k.val ≤ i then p04ErrorAt error i else 0) r.val) =
    p04InclusiveErrorProduct error k
  rw [Fin.prod_univ_eq_prod_range
    (fun i : ℕ => 1 + if k.val ≤ i then p04ErrorAt error i else 0) q]
  unfold p04InclusiveErrorProduct
  change (∏ i ∈ Finset.range q,
      (1 + if k.val ≤ i then p04ErrorAt error i else 0)) =
    ∏ i ∈ Finset.Ico k.val q, (1 + p04ErrorAt error i)
  calc
    (∏ i ∈ Finset.range q,
        (1 + if k.val ≤ i then p04ErrorAt error i else 0)) =
        ∏ i ∈ Finset.range q,
          (if k.val ≤ i then 1 + p04ErrorAt error i else 1) := by
            apply Finset.prod_congr rfl
            intro i _hi
            split <;> simp_all
    _ = ∏ i ∈ Finset.Ico k.val q,
        (if k.val ≤ i then 1 + p04ErrorAt error i else 1) := by
      symm
      apply Finset.prod_subset
      · intro i hi
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
      · intro i hiRange hiNot
        have hlt : i < k.val := by
          have hir := Finset.mem_range.mp hiRange
          have hni := hiNot
          simp only [Finset.mem_Ico] at hni
          omega
        simp [show ¬ k.val ≤ i by omega]
    _ = ∏ i ∈ Finset.Ico k.val q, (1 + p04ErrorAt error i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hki := (Finset.mem_Ico.mp hi).1
      simp [hki]

private lemma p04_sum_factor_error_bound {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (A B : ℝ)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hA : ∀ k j, |alpha k j| ≤ A)
    (hB : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hdiff :
      p04BlockedDot x y -
          ∑ k : Fin q, ∑ j : Fin b,
            x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
        ∑ k : Fin q, ∑ j : Fin b,
          (x k j * y k j -
            x k j * y k j * (1 + alpha k j) * (1 + beta k j)) := by
    simp only [p04BlockedDot, Finset.sum_sub_distrib]
  rw [hdiff]
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
      intro k _hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
        (A + B + A * B) * (|x k j| * |y k j|) := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro j _hj
      have hab : |alpha k j * beta k j| ≤ A * B := by
        rw [abs_mul]
        exact mul_le_mul (hA k j) (hB k j) (abs_nonneg _) hA0
      have hfactor :
          |alpha k j + beta k j + alpha k j * beta k j| ≤
            A + B + A * B := by
        calc
          |alpha k j + beta k j + alpha k j * beta k j| ≤
              |alpha k j| + |beta k j| + |alpha k j * beta k j| := by
                exact le_trans (abs_add_le _ _)
                  (add_le_add (abs_add_le _ _) (le_refl _))
          _ ≤ A + B + A * B := add_le_add (add_le_add (hA k j) (hB k j)) hab
      calc
        |x k j * y k j -
            x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
            |x k j * y k j| *
              |alpha k j + beta k j + alpha k j * beta k j| := by
                rw [show x k j * y k j -
                    x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
                    -(x k j * y k j) *
                      (alpha k j + beta k j + alpha k j * beta k j) by ring]
                rw [abs_mul, abs_neg]
        _ ≤ |x k j * y k j| * (A + B + A * B) :=
          mul_le_mul_of_nonneg_left hfactor (abs_nonneg _)
        _ = (A + B + A * B) * (|x k j| * |y k j|) := by
          rw [abs_mul]
          ring
    _ = (A + B + A * B) * p04BlockedAbsDot x y := by
      unfold p04BlockedAbsDot
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Finset.mul_sum]

private lemma p04_gamma_nonneg (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hvalid : GammaValid u m) :
    0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  apply div_nonneg
  · positivity
  · linarith

private lemma p04_gamma_valid_mono (u : ℝ) {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hn : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ n := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hn

private lemma p04_right_path_length_le {q b : ℕ}
    (hq : 0 < q) (hb : 0 < b) : q + b - 1 ≤ q * b := by
  obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hb)
  have hnonneg : 0 ≤ q' * b' := Nat.zero_le _
  simp only [Nat.succ_eq_add_one]
  calc
    q' + 1 + (b' + 1) - 1 = q' + b' + 1 := by omega
    _ ≤ q' * b' + (q' + b' + 1) := by omega
    _ = (q' + 1) * (b' + 1) := by ring

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
  let uE : ℝ := p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut
  have huE : 0 ≤ uE := by
    exact p04_effective_nonneg run.uBar run.uFma run.uOut
      run.uBar_nonneg run.uFma_nonneg run.uOut_nonneg
  let alpha : Fin q → Fin b → ℝ := fun k _j =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k - 1

  have halpha : ∀ k j, |alpha k j| ≤ gamma uE q := by
    intro k j
    have hpath : ∀ r : Fin q, |p04DeltaPath run.delta k r| ≤ uE := by
      intro r
      unfold p04DeltaPath
      split
      · simpa [p04ErrorAt, r.isLt, uE] using run.delta_bound r
      · simpa using huE
    obtain ⟨theta, htheta, hprod⟩ :=
      p04_prod_error_bound uE q huE (p04DeltaPath run.delta k)
        hpath run.effective_gamma_valid
    have hinc : p04InclusiveErrorProduct run.delta k = 1 + theta := by
      calc
        p04InclusiveErrorProduct run.delta k =
            ∏ r : Fin q, (1 + p04DeltaPath run.delta k r) :=
          (p04_delta_path_product run.delta k).symm
        _ = 1 + theta := hprod
    dsimp [alpha]
    rw [hinc]
    simpa using htheta

  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    obtain ⟨theta, htheta, hprod⟩ :=
      p04_prod_error_bound run.uBar n run.uBar_nonneg
        (run.innerPathError k j) (run.inner_path_error_bound k j)
        run.internal_gamma_valid
    have hfactor :
        (1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k =
          1 + theta := by
      calc
        (1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k =
            ∏ r : Fin n, (1 + run.innerPathError k j r) :=
          (run.inner_path_factor k j).symm
        _ = 1 + theta := hprod
    dsimp [beta]
    rw [hfactor]
    simpa using htheta

  have hcomputed :
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) := by
    calc
      run.computed =
          ∑ k : Fin q, ∑ j : Fin b,
            run.x k j * run.y k j * (1 + run.termTheta k j) *
              p04StrictErrorProduct run.carryTheta k *
              p04InclusiveErrorProduct run.delta k :=
        p04_computed_expansion run
      _ = ∑ k : Fin q, ∑ j : Fin b,
          run.x k j * run.y k j *
            (1 + alpha k j) * (1 + beta k j) := by
        apply Finset.sum_congr rfl
        intro k _hk
        apply Finset.sum_congr rfl
        intro j _hj
        dsimp [alpha, beta]
        ring

  have hgammaE : 0 ≤ gamma uE q :=
    p04_gamma_nonneg uE q huE run.effective_gamma_valid
  have hgammaN : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar n run.uBar_nonneg run.internal_gamma_valid
  have herror :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uE run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    have h := p04_sum_factor_error_bound run.x run.y alpha beta
      (gamma uE q) (gamma run.uBar n) hgammaE hgammaN halpha hbeta
    rw [← hcomputed] at h
    simpa [p04BlockFmaCoeff] using h

  have hlength : q + b - 1 ≤ n := by
    rw [run.dimension_eq]
    exact p04_right_path_length_le run.block_count_pos run.block_size_pos
  have hvalidRight : GammaValid run.uBar (q + b - 1) :=
    p04_gamma_valid_mono run.uBar run.uBar_nonneg hlength
      run.internal_gamma_valid
  have hgammaRight : 0 ≤ gamma run.uBar (q + b - 1) :=
    p04_gamma_nonneg run.uBar (q + b - 1) run.uBar_nonneg hvalidRight

  have hright : run.order = P04BlockEvaluationOrder.rightToLeft →
      (∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1)) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff uE run.uBar q (q + b - 1) *
          p04BlockedAbsDot run.x run.y := by
    intro horder
    have hbetaRight :
        ∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      obtain ⟨theta, htheta, hprod⟩ :=
        p04_prod_error_bound run.uBar (q + b - 1) run.uBar_nonneg
          (run.rightToLeftPathError k j)
          (run.right_to_left_path_error_bound horder k j) hvalidRight
      have hfactor :
          (1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k =
            1 + theta := by
        calc
          (1 + run.termTheta k j) * p04StrictErrorProduct run.carryTheta k =
              ∏ r : Fin (q + b - 1),
                (1 + run.rightToLeftPathError k j r) :=
            (run.right_to_left_path_factor horder k j).symm
          _ = 1 + theta := hprod
      dsimp [beta]
      rw [hfactor]
      simpa using htheta
    refine ⟨hbetaRight, ?_⟩
    have h := p04_sum_factor_error_bound run.x run.y alpha beta
      (gamma uE q) (gamma run.uBar (q + b - 1))
      hgammaE hgammaRight halpha hbetaRight
    rw [← hcomputed] at h
    simpa [p04BlockFmaCoeff] using h

  have hspecial : run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
      (∀ k j, alpha k j = 0) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        gamma run.uBar n * p04BlockedAbsDot run.x run.y := by
    rintro ⟨hout, hbar⟩
    have huEzero : uE = 0 := by
      dsimp [uE]
      unfold p04EffectiveFmaRoundoff
      rw [if_neg (not_lt_of_ge hout)]
      rw [if_pos (by simpa [hbar])]
    have hdeltaZero : ∀ k, run.delta k = 0 := by
      intro k
      have hk := run.delta_bound k
      rw [show p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut = 0 by
        simpa [uE] using huEzero] at hk
      have habs : |run.delta k| = 0 :=
        le_antisymm hk (abs_nonneg _)
      exact abs_eq_zero.mp habs
    have halphaZero : ∀ k j, alpha k j = 0 := by
      intro k j
      dsimp [alpha]
      have hinc : p04InclusiveErrorProduct run.delta k = 1 := by
        unfold p04InclusiveErrorProduct
        apply Finset.prod_eq_one
        intro l hl
        unfold p04ErrorAt
        split
        · simp [hdeltaZero]
        · simp
      rw [hinc]
      ring
    refine ⟨halphaZero, ?_⟩
    have hzeroBound : ∀ k j, |alpha k j| ≤ (0 : ℝ) := by
      intro k j
      rw [halphaZero k j]
      simp
    have h := p04_sum_factor_error_bound run.x run.y alpha beta
      0 (gamma run.uBar n) (le_refl 0) hgammaN hzeroBound hbeta
    rw [← hcomputed] at h
    simpa using h

  exact ⟨alpha, beta, hcomputed, halpha, hbeta, herror, hright, hspecial⟩

end HighamBench
