import HighamBench.P04Definitions
import NumStability.Analysis.Error.RoundingProducts.Core

namespace HighamBench

open scoped BigOperators

private lemma p04Gamma_nonneg {u : ℝ} {m : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u m) :
    0 ≤ gamma u m := by
  unfold gamma GammaValid at *
  exact div_nonneg (mul_nonneg (by positivity) hu) (le_of_lt (sub_pos.mpr hvalid))

private lemma p04GammaValid_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hvalid : GammaValid u n) :
    GammaValid u m := by
  unfold GammaValid at *
  have hcast : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hcast hu) hvalid

private lemma p04Prod_one_add_sub_one_le_gamma {m : ℕ} (hm : 0 < m)
    {u : ℝ} (hu : 0 ≤ u) (hvalid : GammaValid u m)
    (e : Fin m → ℝ) (he : ∀ r, |e r| ≤ u) :
    |(∏ r : Fin m, (1 + e r)) - 1| ≤ gamma u m := by
  simpa [gamma, GammaValid] using
    NumStability.prod_one_add_delta_abs_sub_one_le_gamma_radius
      m hm hu hvalid e he

private lemma p04InclusiveErrorProduct_eq_prod_mask {q : ℕ}
    (error : Fin q → ℝ) (k : Fin q) :
    p04InclusiveErrorProduct error k =
      ∏ r : Fin q, (1 + if k.val ≤ r.val then error r else 0) := by
  have hIco : Finset.Ico k.val q =
      (Finset.range q).filter (fun r => k.val ≤ r) := by
    ext r
    simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
    omega
  rw [p04InclusiveErrorProduct, hIco, Finset.prod_filter,
    Finset.prod_fin_eq_prod_range]
  apply Finset.prod_congr rfl
  intro r hr
  have hrq : r < q := Finset.mem_range.mp hr
  by_cases hkr : k.val ≤ r <;> simp [p04ErrorAt, hrq, hkr]

private lemma p04State_expansion {q b : ℕ}
    (v : Fin q → Fin b → ℝ) (carry delta : Fin q → ℝ)
    (state : ℕ → ℝ) (hzero : state 0 = 0)
    (hstep : ∀ k : Fin q,
      state (k.val + 1) =
        (state k.val * (1 + carry k) + ∑ j : Fin b, v k j) *
          (1 + delta k)) :
    state q = ∑ k : Fin q, ∑ j : Fin b,
      v k j * p04StrictErrorProduct carry k *
        p04InclusiveErrorProduct delta k := by
  let V : ℕ → ℝ := fun k =>
    if hk : k < q then ∑ j : Fin b, v ⟨k, hk⟩ j else 0
  have hprefix : ∀ t : ℕ, t ≤ q →
      state t = ∑ k ∈ Finset.range t,
        V k *
          (∏ l ∈ Finset.Ico (k + 1) t, (1 + p04ErrorAt carry l)) *
          (∏ l ∈ Finset.Ico k t, (1 + p04ErrorAt delta l)) := by
    intro t ht
    induction t with
    | zero =>
        simp [hzero]
    | succ t ih =>
        have htq : t < q := Nat.lt_of_succ_le ht
        let kt : Fin q := ⟨t, htq⟩
        have hcarryAt : p04ErrorAt carry t = carry kt := by
          simp [p04ErrorAt, kt, htq]
        have hdeltaAt : p04ErrorAt delta t = delta kt := by
          simp [p04ErrorAt, kt, htq]
        have hV : V t = ∑ j : Fin b, v kt j := by
          simp [V, kt, htq]
        have hold :
            (∑ k ∈ Finset.range t,
                V k *
                  (∏ l ∈ Finset.Ico (k + 1) (t + 1),
                    (1 + p04ErrorAt carry l)) *
                  (∏ l ∈ Finset.Ico k (t + 1),
                    (1 + p04ErrorAt delta l))) =
              (∑ k ∈ Finset.range t,
                V k *
                  (∏ l ∈ Finset.Ico (k + 1) t,
                    (1 + p04ErrorAt carry l)) *
                  (∏ l ∈ Finset.Ico k t,
                    (1 + p04ErrorAt delta l))) *
                (1 + carry kt) * (1 + delta kt) := by
          calc
            _ = ∑ k ∈ Finset.range t,
                (V k *
                  (∏ l ∈ Finset.Ico (k + 1) t,
                    (1 + p04ErrorAt carry l)) *
                  (∏ l ∈ Finset.Ico k t,
                    (1 + p04ErrorAt delta l))) *
                  (1 + carry kt) * (1 + delta kt) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    have hkt : k < t := Finset.mem_range.mp hk
                    rw [Finset.prod_Ico_succ_top (Nat.succ_le_iff.mpr hkt),
                      Finset.prod_Ico_succ_top (Nat.le_of_lt hkt),
                      hcarryAt, hdeltaAt]
                    ring
            _ = _ := by
              rw [Finset.sum_mul, Finset.sum_mul]
        rw [hstep kt, ih (Nat.le_of_succ_le ht), Finset.sum_range_succ]
        rw [hold, hV]
        have hnewCarry :
            (∏ l ∈ Finset.Ico (t + 1) (t + 1),
              (1 + p04ErrorAt carry l)) = 1 := by simp
        have hnewDelta :
            (∏ l ∈ Finset.Ico t (t + 1),
              (1 + p04ErrorAt delta l)) = 1 + delta kt := by
          rw [Finset.prod_Ico_succ_top (le_refl t), hdeltaAt]
          simp
        rw [hnewCarry, hnewDelta]
        ring
  calc
    state q = ∑ k ∈ Finset.range q,
        V k *
          (∏ l ∈ Finset.Ico (k + 1) q, (1 + p04ErrorAt carry l)) *
          (∏ l ∈ Finset.Ico k q, (1 + p04ErrorAt delta l)) :=
      hprefix q le_rfl
    _ = ∑ k : Fin q, ∑ j : Fin b,
        v k j * p04StrictErrorProduct carry k *
          p04InclusiveErrorProduct delta k := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hkq : k < q := Finset.mem_range.mp hk
      simp only [dif_pos hkq]
      simp [V, hkq, p04StrictErrorProduct, p04InclusiveErrorProduct,
        Finset.sum_mul]

private lemma p04Factorized_sum_error_bound {q b : ℕ}
    (x y alpha beta : Fin q → Fin b → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (halpha : ∀ k j, |alpha k j| ≤ A)
    (hbeta : ∀ k j, |beta k j| ≤ B) :
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
      (A + B + A * B) * p04BlockedAbsDot x y := by
  have hpoint : ∀ k j,
      |x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| ≤
        (A + B + A * B) * (|x k j| * |y k j|) := by
    intro k j
    have habsmul : |alpha k j| * |beta k j| ≤ A * B :=
      mul_le_mul (halpha k j) (hbeta k j) (abs_nonneg _) hA
    have hab :
        |alpha k j + beta k j + alpha k j * beta k j| ≤
          A + B + A * B := by
      calc
        _ ≤ |alpha k j| + |beta k j| + |alpha k j * beta k j| := by
          exact abs_add_three _ _ _
        _ = |alpha k j| + |beta k j| + |alpha k j| * |beta k j| := by
          rw [abs_mul]
        _ ≤ A + B + A * B := by linarith [halpha k j, hbeta k j, habsmul]
    rw [show x k j * y k j -
          x k j * y k j * (1 + alpha k j) * (1 + beta k j) =
        -(x k j * y k j) *
          (alpha k j + beta k j + alpha k j * beta k j) by ring,
      abs_mul, abs_neg, abs_mul]
    calc
      _ ≤ (|x k j| * |y k j|) * (A + B + A * B) :=
        mul_le_mul_of_nonneg_left hab
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  calc
    |p04BlockedDot x y -
        ∑ k : Fin q, ∑ j : Fin b,
          x k j * y k j * (1 + alpha k j) * (1 + beta k j)| =
      |∑ k : Fin q, ∑ j : Fin b,
          (x k j * y k j -
            x k j * y k j * (1 + alpha k j) * (1 + beta k j))| := by
        congr 1
        simp [p04BlockedDot, Finset.sum_sub_distrib]
    _ ≤ ∑ k : Fin q, |∑ j : Fin b,
          (x k j * y k j -
            x k j * y k j * (1 + alpha k j) * (1 + beta k j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
          |x k j * y k j -
            x k j * y k j * (1 + alpha k j) * (1 + beta k j)| := by
      exact Finset.sum_le_sum fun k _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin q, ∑ j : Fin b,
          (A + B + A * B) * (|x k j| * |y k j|) := by
      exact Finset.sum_le_sum fun k _ =>
        Finset.sum_le_sum fun j _ => hpoint k j
    _ = (A + B + A * B) * p04BlockedAbsDot x y := by
      simp [p04BlockedAbsDot, Finset.mul_sum]

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
  let eps : ℝ :=
    p04EffectiveFmaRoundoff run.uBar run.uFma run.uOut
  let alpha : Fin q → Fin b → ℝ := fun k _ =>
    p04InclusiveErrorProduct run.delta k - 1
  let beta : Fin q → Fin b → ℝ := fun k j =>
    (∏ r : Fin n, (1 + run.innerPathError k j r)) - 1
  have heps_nonneg : 0 ≤ eps := by
    dsimp [eps]
    unfold p04EffectiveFmaRoundoff
    split_ifs
    · exact run.uOut_nonneg
    · exact le_refl 0
    · exact run.uFma_nonneg
  have hgamma_eps_nonneg : 0 ≤ gamma eps q :=
    p04Gamma_nonneg heps_nonneg run.effective_gamma_valid
  have hgamma_n_nonneg : 0 ≤ gamma run.uBar n :=
    p04Gamma_nonneg run.uBar_nonneg run.internal_gamma_valid
  have halpha : ∀ k j, |alpha k j| ≤ gamma eps q := by
    intro k j
    rw [show alpha k j =
      (∏ r : Fin q,
        (1 + if k.val ≤ r.val then run.delta r else 0)) - 1 by
      simp only [alpha]
      rw [p04InclusiveErrorProduct_eq_prod_mask]]
    apply p04Prod_one_add_sub_one_le_gamma (m := q) run.block_count_pos
      heps_nonneg run.effective_gamma_valid
    intro r
    by_cases hkr : k.val ≤ r.val
    · simpa [hkr, eps] using run.delta_bound r
    · simp [hkr, heps_nonneg]
  have hbeta : ∀ k j, |beta k j| ≤ gamma run.uBar n := by
    intro k j
    exact p04Prod_one_add_sub_one_le_gamma (m := n) run.dimension_pos
      run.uBar_nonneg run.internal_gamma_valid
      (run.innerPathError k j) (run.inner_path_error_bound k j)
  have hexpand :
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        (run.x k j * run.y k j * (1 + run.termTheta k j)) *
          p04StrictErrorProduct run.carryTheta k *
          p04InclusiveErrorProduct run.delta k := by
    unfold P04BlockFmaDotRun.computed
    apply p04State_expansion
    · exact run.state_zero
    · intro k
      exact run.state_step k
  have hrepresentation :
      run.computed = ∑ k : Fin q, ∑ j : Fin b,
        run.x k j * run.y k j *
          (1 + alpha k j) * (1 + beta k j) := by
    rw [hexpand]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro j _
    simp only [alpha, beta]
    rw [run.inner_path_factor k j]
    ring
  have herror :
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff eps run.uBar q n *
          p04BlockedAbsDot run.x run.y := by
    rw [hrepresentation]
    simpa [p04BlockFmaCoeff] using
      p04Factorized_sum_error_bound run.x run.y alpha beta
        hgamma_eps_nonneg hgamma_n_nonneg halpha hbeta
  have hright : run.order = P04BlockEvaluationOrder.rightToLeft →
      (∀ k j, |beta k j| ≤ gamma run.uBar (q + b - 1)) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        p04BlockFmaCoeff eps run.uBar q (q + b - 1) *
          p04BlockedAbsDot run.x run.y := by
    intro horder
    have hqpos : 0 < q := run.block_count_pos
    have hbpos : 0 < b := run.block_size_pos
    have hcount_pos : 0 < q + b - 1 := by omega
    have hcount_le_n : q + b - 1 ≤ n := by
      calc
        q + b - 1 ≤ q * b :=
          Nat.add_sub_one_le_mul (Nat.ne_of_gt hqpos) (Nat.ne_of_gt hbpos)
        _ = n := run.dimension_eq.symm
    have hvalid_count : GammaValid run.uBar (q + b - 1) :=
      p04GammaValid_mono run.uBar_nonneg hcount_le_n
        run.internal_gamma_valid
    have hgamma_count_nonneg : 0 ≤ gamma run.uBar (q + b - 1) :=
      p04Gamma_nonneg run.uBar_nonneg hvalid_count
    have hbeta_right : ∀ k j,
        |beta k j| ≤ gamma run.uBar (q + b - 1) := by
      intro k j
      have hpaths :
          (∏ r : Fin n, (1 + run.innerPathError k j r)) =
            ∏ r : Fin (q + b - 1),
              (1 + run.rightToLeftPathError k j r) := by
        rw [run.inner_path_factor k j,
          run.right_to_left_path_factor horder k j]
      rw [show beta k j =
          (∏ r : Fin (q + b - 1),
            (1 + run.rightToLeftPathError k j r)) - 1 by
        simp only [beta]
        rw [hpaths]]
      exact p04Prod_one_add_sub_one_le_gamma (m := q + b - 1) hcount_pos
        run.uBar_nonneg hvalid_count
        (run.rightToLeftPathError k j)
        (run.right_to_left_path_error_bound horder k j)
    refine ⟨hbeta_right, ?_⟩
    rw [hrepresentation]
    simpa [p04BlockFmaCoeff] using
      p04Factorized_sum_error_bound run.x run.y alpha beta
        hgamma_eps_nonneg hgamma_count_nonneg halpha hbeta_right
  have hexact : run.uOut ≤ run.uFma ∧ run.uBar = run.uFma →
      (∀ k j, alpha k j = 0) ∧
      |p04BlockedDot run.x run.y - run.computed| ≤
        gamma run.uBar n * p04BlockedAbsDot run.x run.y := by
    rintro ⟨hout, hbar⟩
    have heps_zero : eps = 0 := by
      simp [eps, p04EffectiveFmaRoundoff, not_lt.mpr hout,
        le_of_eq hbar.symm]
    have hdelta_zero : ∀ k, run.delta k = 0 := by
      intro k
      have hk : |run.delta k| ≤ 0 := by
        simpa [eps, heps_zero] using run.delta_bound k
      exact abs_eq_zero.mp (le_antisymm hk (abs_nonneg _))
    have halpha_zero : ∀ k j, alpha k j = 0 := by
      intro k j
      simp [alpha, p04InclusiveErrorProduct, p04ErrorAt, hdelta_zero]
    refine ⟨halpha_zero, ?_⟩
    rw [hrepresentation]
    have hzero_bound : ∀ k j, |alpha k j| ≤ (0 : ℝ) := by
      simp [halpha_zero]
    simpa using
      p04Factorized_sum_error_bound run.x run.y alpha beta
        (le_refl 0) hgamma_n_nonneg hzero_bound hbeta
  exact ⟨alpha, beta, hrepresentation, halpha, hbeta, herror, hright, hexact⟩

end HighamBench
