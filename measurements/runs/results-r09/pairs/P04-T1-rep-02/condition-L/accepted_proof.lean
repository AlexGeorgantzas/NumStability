import HighamBench.P04Definitions
import NumStability.Analysis.Rounding

namespace HighamBench

open scoped BigOperators

private lemma p04_prod_error_bound
    (u : ℝ) (hu : 0 ≤ u) (m : ℕ) (e : Fin m → ℝ)
    (he : ∀ i, |e i| ≤ u) (hv : GammaValid u m) :
    ∃ t : ℝ, |t| ≤ gamma u m ∧
      (∏ i : Fin m, (1 + e i)) = 1 + t := by
  let fp := NumStability.FPModel.exactWithUnitRoundoff u hu
  have he' : ∀ i, |e i| ≤ fp.u := by
    simpa [fp, NumStability.FPModel.exactWithUnitRoundoff] using he
  have hv' : NumStability.gammaValid fp m := by
    simpa [GammaValid, NumStability.gammaValid, fp,
      NumStability.FPModel.exactWithUnitRoundoff] using hv
  obtain ⟨t, ht, hprod⟩ := NumStability.prod_error_bound fp m e he' hv'
  refine ⟨t, ?_, hprod⟩
  simpa [gamma, NumStability.gamma, fp,
    NumStability.FPModel.exactWithUnitRoundoff] using ht

private lemma p04_recurrence_unroll {q : ℕ}
    (s : ℕ → ℝ) (carry delta term : Fin q → ℝ)
    (hs0 : s 0 = 0)
    (hstep : ∀ k : Fin q,
      s (k.val + 1) =
        (s k.val * (1 + carry k) + term k) * (1 + delta k)) :
    s q = ∑ k : Fin q,
      term k * p04StrictErrorProduct carry k *
        p04InclusiveErrorProduct delta k := by
  classical
  have hstate : ∀ m : ℕ, m ≤ q →
      s m =
        ∑ k ∈ Finset.range m,
          p04ErrorAt term k *
          (∏ l ∈ Finset.Ico (k + 1) m,
            (1 + p04ErrorAt carry l)) *
          (∏ l ∈ Finset.Ico k m,
            (1 + p04ErrorAt delta l)) := by
    intro m hm
    induction m with
    | zero => simp [hs0]
    | succ m ih =>
      have hm_lt : m < q := by omega
      let km : Fin q := ⟨m, hm_lt⟩
      rw [hstep km, ih (by omega)]
      rw [Finset.sum_range_succ]
      have hsum :
          (∑ k ∈ Finset.range m,
              p04ErrorAt term k *
                (∏ l ∈ Finset.Ico (k + 1) (m + 1),
                  (1 + p04ErrorAt carry l)) *
                (∏ l ∈ Finset.Ico k (m + 1),
                  (1 + p04ErrorAt delta l))) =
            (∑ k ∈ Finset.range m,
              p04ErrorAt term k *
                (∏ l ∈ Finset.Ico (k + 1) m,
                  (1 + p04ErrorAt carry l)) *
                (∏ l ∈ Finset.Ico k m,
                  (1 + p04ErrorAt delta l))) *
              (1 + carry km) * (1 + delta km) := by
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k hk
        have hkm : k < m := Finset.mem_range.mp hk
        have hkq : k < q := lt_trans hkm hm_lt
        rw [Finset.prod_Ico_succ_top (by omega),
          Finset.prod_Ico_succ_top (by omega)]
        simp [p04ErrorAt, hkq, hm_lt, km]
        ring
      rw [hsum]
      simp [p04ErrorAt, hm_lt, km]
      ring
  rw [hstate q le_rfl]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [p04StrictErrorProduct, p04InclusiveErrorProduct]
  simp [p04ErrorAt, k.isLt]

private lemma p04_state_unroll {n b q : ℕ}
    (run : P04BlockFmaDotRun n b q) :
    run.computed =
      ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          ((1 + run.termTheta k j) *
            p04StrictErrorProduct run.carryTheta k) *
          p04InclusiveErrorProduct run.delta k := by
  let term : Fin q → ℝ := fun k =>
    ∑ j : Fin b, run.x k j * run.y k j * (1 + run.termTheta k j)
  have hu := p04_recurrence_unroll run.state run.carryTheta run.delta term
    run.state_zero (by
      intro k
      simpa [term] using run.state_step k)
  rw [P04BlockFmaDotRun.computed, hu]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [term]
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

private lemma p04_inclusive_eq_masked {q : ℕ}
    (e : Fin q → ℝ) (k : Fin q) :
    p04InclusiveErrorProduct e k =
      ∏ r : Fin q, (1 + if k.val ≤ r.val then e r else 0) := by
  classical
  let f : ℕ → ℝ := fun r =>
    if k.val ≤ r then 1 + p04ErrorAt e r else 1
  calc
    p04InclusiveErrorProduct e k =
        ∏ r ∈ Finset.Ico k.val q, f r := by
          unfold p04InclusiveErrorProduct
          apply Finset.prod_congr rfl
          intro r hr
          simp [f, Finset.mem_Ico.mp hr]
    _ = ∏ r ∈ Finset.range q, f r := by
          apply Finset.prod_subset
          · intro r hr
            exact Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2
          · intro r hr hri
            have hrq : r < q := Finset.mem_range.mp hr
            have hrk : r < k.val := by
              by_contra h
              exact hri (Finset.mem_Ico.mpr ⟨by omega, hrq⟩)
            simp [f, show ¬k.val ≤ r by omega]
    _ = ∏ r : Fin q, (1 + if k.val ≤ r.val then e r else 0) := by
          symm
          rw [Finset.prod_fin_eq_prod_range]
          apply Finset.prod_congr rfl
          intro r hr
          have hrq : r < q := Finset.mem_range.mp hr
          by_cases hkr : k.val ≤ r
          · simp [f, hkr, p04ErrorAt, hrq]
          · simp [f, hkr]

private lemma p04_gamma_nonneg (u : ℝ) (m : ℕ)
    (hu : 0 ≤ u) (hv : GammaValid u m) :
    0 ≤ gamma u m := by
  unfold gamma
  unfold GammaValid at hv
  exact div_nonneg
    (mul_nonneg (by positivity) hu) (by linarith)

private lemma p04_gamma_valid_mono (u : ℝ) {r m : ℕ}
    (hu : 0 ≤ u) (hrm : r ≤ m) (hm : GammaValid u m) :
    GammaValid u r := by
  unfold GammaValid at hm ⊢
  have hcast : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hrm
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hm

private lemma p04_factored_sum_error {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) (computed A B : ℝ)
    (hcomputed : computed = ∑ k : Fin q, ∑ j : Fin b,
      x k j * y k j * (1 + alpha k j) * (1 + beta k j))
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : ∀ k j, |alpha k j| ≤ A)
    (hbeta : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y - computed| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hpoint : ∀ k j,
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
        (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    have hab : |alpha k j * beta k j| ≤ A * B := by
      rw [abs_mul]
      exact mul_le_mul (halpha k j) (hbeta k j)
        (abs_nonneg _) hA
    have hfactor :
        |alpha k j + beta k j + alpha k j * beta k j| ≤
          A + B + A * B := by
      calc
        |alpha k j + beta k j + alpha k j * beta k j|
            ≤ |alpha k j + beta k j| + |alpha k j * beta k j| :=
              abs_add_le _ _
        _ ≤ (|alpha k j| + |beta k j|) +
              |alpha k j * beta k j| := by
              gcongr
              exact abs_add_le _ _
        _ ≤ A + B + A * B := by linarith [halpha k j, hbeta k j, hab]
    rw [show x k j * y k j -
        x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
          -(x k j * y k j) *
            (alpha k j + beta k j + alpha k j * beta k j) by ring]
    rw [abs_mul, abs_neg, abs_mul]
    have hxy : 0 ≤ |x k j| * |y k j| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc
      |x k j| * |y k j| *
          |alpha k j + beta k j + alpha k j * beta k j|
          ≤ |x k j| * |y k j| * (A + B + A * B) :=
            mul_le_mul_of_nonneg_left hfactor hxy
      _ = (A + B + A * B) * (|x k j| * |y k j|) := by ring
  rw [p04BlockedDot, p04BlockedAbsDot, hcomputed]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ k : Fin q,
        ((∑ j : Fin b, x k j * y k j) -
          ∑ j : Fin b,
            x k j * y k j * (1 + alpha k j) * (1 + beta k j))|
        ≤ ∑ k : Fin q,
            |(∑ j : Fin b, x k j * y k j) -
              ∑ j : Fin b,
                x k j * y k j * (1 + alpha k j) * (1 + beta k j)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
          |x k j * y k j -
            x k j * y k j * (1 + alpha k j) * (1 + beta k j)| := by
          apply Finset.sum_le_sum
          intro k hk
          rw [← Finset.sum_sub_distrib]
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
          (A + B + A * B) * (|x k j| * |y k j|) := by
          apply Finset.sum_le_sum
          intro k hk
          apply Finset.sum_le_sum
          intro j hj
          exact hpoint k j
    _ = (A + B + A * B) *
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
  let ueff : ℝ :=
    p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut
  let alpha : Fin q → Fin b → ℝ := fun k _j =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have hueff : 0 ≤ ueff := by
    dsimp [ueff]
    unfold p04EffectiveFmaRoundoff
    split_ifs
    · exact run.uOut_nonneg
    · exact le_rfl
    · exact run.uFma_nonneg
  have hA : 0 ≤ gamma ueff q :=
    p04_gamma_nonneg ueff q hueff run.effective_gamma_valid
  have hB : 0 ≤ gamma run.uBar n :=
    p04_gamma_nonneg run.uBar n run.uBar_nonneg
      run.internal_gamma_valid
  have halpha : ∀ k j, |alpha k j| ≤ gamma ueff q := by
    intro k j
    let masked : Fin q → ℝ := fun r =>
      if k.val ≤ r.val then run.delta r else 0
    have hmasked : ∀ r, |masked r| ≤ ueff := by
      intro r
      dsimp [masked]
      split_ifs
      · exact run.delta_bound r
      · simp [hueff]
    obtain ⟨t, ht, hprod⟩ :=
      p04_prod_error_bound ueff hueff q masked hmasked
        run.effective_gamma_valid
    have hinc : p04InclusiveErrorProduct run.delta k =
        ∏ r : Fin q, (1 + masked r) := by
      simpa [masked] using p04_inclusive_eq_masked run.delta k
    have hat : alpha k j = t := by
      dsimp [alpha]
      rw [hinc, hprod]
      ring
    rw [hat]
    exact ht
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    obtain ⟨t, ht, hprod⟩ :=
      p04_prod_error_bound run.uBar run.uBar_nonneg n
        (run.innerPathError k j) (run.inner_path_error_bound k j)
        run.internal_gamma_valid
    have hbt : beta k j = t := by
      dsimp [beta]
      rw [hprod]
      ring
    rw [hbt]
    exact ht
  have hcomputed : run.computed = ∑ k : Fin q, ∑ j : Fin b,
      run.x k j * run.y k j *
        (1 + alpha k j) * (1 + beta k j) := by
    rw [p04_state_unroll run]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro j hj
    dsimp [alpha, beta]
    rw [run.inner_path_factor k j]
    ring
  have herror :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff ueff run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    simpa [p04BlockFmaCoeff] using
      p04_factored_sum_error run.x run.y alpha beta run.computed
        (gamma ueff q) (gamma run.uBar n)
        hcomputed hA hB halpha hbeta
  refine ⟨alpha, beta, hcomputed, ?_, hbeta, herror, ?_, ?_⟩
  · simpa [ueff] using halpha
  · intro horder
    have hcount : q + b - 1 ≤ n := by
      rw [run.dimension_eq]
      obtain ⟨q', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt run.block_count_pos)
      obtain ⟨b', rfl⟩ := Nat.exists_eq_succ_of_ne_zero
        (Nat.ne_of_gt run.block_size_pos)
      simp only [Nat.succ_eq_add_one]
      calc
        (q' + 1) + (b' + 1) - 1 = q' + b' + 1 := by omega
        _ ≤ q' * b' + q' + b' + 1 := by omega
        _ = (q' + 1) * (b' + 1) := by ring
    have hvalidR : GammaValid run.uBar (q + b - 1) :=
      p04_gamma_valid_mono run.uBar run.uBar_nonneg hcount
        run.internal_gamma_valid
    have hBR : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04_gamma_nonneg run.uBar (q + b - 1) run.uBar_nonneg hvalidR
    have hbetaR : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      obtain ⟨t, ht, hprod⟩ :=
        p04_prod_error_bound run.uBar run.uBar_nonneg (q + b - 1)
          (run.rightToLeftPathError k j)
          (run.right_to_left_path_error_bound horder k j) hvalidR
      have hpaths :
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
      have hbt : beta k j = t := by
        dsimp [beta]
        rw [hpaths, hprod]
        ring
      rw [hbt]
      exact ht
    refine ⟨hbetaR, ?_⟩
    simpa [p04BlockFmaCoeff] using
      p04_factored_sum_error run.x run.y alpha beta run.computed
        (gamma ueff q) (gamma run.uBar (q + b - 1))
        hcomputed hA hBR halpha hbetaR
  · rintro ⟨hout, hbar⟩
    have heff : ueff = 0 := by
      dsimp [ueff]
      unfold p04EffectiveFmaRoundoff
      simp [not_lt_of_ge hout, hbar]
    have halpha0 : ∀ k j, alpha k j = 0 := by
      intro k j
      have hz : gamma ueff q = 0 := by simp [heff, gamma]
      have habs : |alpha k j| = 0 :=
        le_antisymm (by simpa [hz] using halpha k j) (abs_nonneg _)
      exact abs_eq_zero.mp habs
    refine ⟨halpha0, ?_⟩
    have hs := p04_factored_sum_error run.x run.y alpha beta run.computed
      0 (gamma run.uBar n) hcomputed (le_refl 0) hB
      (by intro k j; simp [halpha0 k j]) hbeta
    simpa using hs

end HighamBench
