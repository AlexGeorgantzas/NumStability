import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : (k : ℝ) * u < 1) : 0 ≤ p29Gamma u k := by
  rw [p29Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (le_of_lt (sub_pos.mpr hk))

private lemma gamma_mono (u : ℝ) {k n : ℕ} (hu : 0 ≤ u)
    (hkn : k ≤ n) (hn : (n : ℝ) * u < 1) :
    p29Gamma u k ≤ p29Gamma u n := by
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hcast hu
  have hkden : 0 < 1 - (k : ℝ) * u := sub_pos.mpr (lt_of_le_of_lt hku hn)
  have hnden : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hn
  rw [p29Gamma, p29Gamma]
  apply (div_le_div_iff₀ hkden hnden).2
  nlinarith

private lemma gamma_step_mul (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : ((k + 1 : ℕ) : ℝ) * u < 1) (a d : ℝ)
    (ha : |a - 1| ≤ p29Gamma u k) (hd : |d| ≤ u) :
    |a * (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hku : (k : ℝ) * u < 1 := by
    have hnon : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
    norm_num at hk ⊢
    nlinarith
  have hg := gamma_nonneg u k hu hku
  have htri : |a * (1 + d) - 1| ≤ |a - 1| + |d| + |a - 1| * |d| := by
    calc
      |a * (1 + d) - 1| = |(a - 1) + d + (a - 1) * d| := by ring_nf
      _ ≤ |a - 1| + |d| + |(a - 1) * d| := by
        refine (abs_add_le _ _).trans ?_
        simpa [add_assoc] using
          add_le_add (abs_add_le (a - 1) d) (le_refl |(a - 1) * d|)
      _ = |a - 1| + |d| + |a - 1| * |d| := by rw [abs_mul]
  have hcoarse : |a - 1| + |d| + |a - 1| * |d| ≤
      p29Gamma u k + u + p29Gamma u k * u := by
    gcongr
  calc
    |a * (1 + d) - 1| ≤ p29Gamma u k + u + p29Gamma u k * u :=
      htri.trans hcoarse
    _ ≤ p29Gamma u (k + 1) := by
      rw [p29Gamma, p29Gamma]
      norm_num [Nat.cast_add, Nat.cast_one] at hk ⊢
      have hd0 : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hku
      have hd1 : 0 < 1 - ((k : ℝ) + 1) * u := sub_pos.mpr hk
      have hid :
          (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
              (k : ℝ) * u / (1 - (k : ℝ) * u) * u =
            ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
        field_simp [ne_of_gt hd0]
        ring
      rw [hid]
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by positivity) hu) hd1 (by nlinarith)

private lemma gamma_step_div (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hk : ((k + 1 : ℕ) : ℝ) * u < 1) (a d : ℝ)
    (ha : |a - 1| ≤ p29Gamma u k) (hd : |d| ≤ u) :
    |a / (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hu1 : u < 1 := by
    have hle : u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      push_cast
      nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
    exact lt_of_le_of_lt hle hk
  have hden : 0 < 1 + d := by
    have := (abs_le.mp hd).1
    nlinarith
  have hku : (k : ℝ) * u < 1 := by
    norm_num at hk ⊢
    nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
  have hg := gamma_nonneg u k hu hku
  have hdenne : 1 + d ≠ 0 := ne_of_gt hden
  rw [div_sub_one hdenne, abs_div, abs_of_pos hden]
  have hnum : |a - (1 + d)| ≤ p29Gamma u k + u := by
    calc
      |a - (1 + d)| = |(a - 1) - d| := by ring_nf
      _ ≤ |a - 1| + |d| := abs_sub _ _
      _ ≤ p29Gamma u k + u := add_le_add ha hd
  have hdenlo : 1 - u ≤ 1 + d := by
    have := (abs_le.mp hd).1
    linarith
  calc
    |a - (1 + d)| / (1 + d) ≤
        (p29Gamma u k + u) / (1 + d) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ ≤ (p29Gamma u k + u) / (1 - u) := by
      exact div_le_div_of_nonneg_left (add_nonneg hg hu) (sub_pos.mpr hu1) hdenlo
    _ ≤ p29Gamma u (k + 1) := by
      rw [p29Gamma, p29Gamma]
      norm_num [Nat.cast_add, Nat.cast_one] at hk ⊢
      have hd0 : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hku
      have hd1 : 0 < 1 - ((k : ℝ) + 1) * u := sub_pos.mpr hk
      have hu0 : 0 < 1 - u := sub_pos.mpr hu1
      have hnum :
          (k : ℝ) * u / (1 - (k : ℝ) * u) + u ≤
            ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
        have hku0 : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
        calc
          (k : ℝ) * u / (1 - (k : ℝ) * u) + u =
              ((k : ℝ) * u + u * (1 - (k : ℝ) * u)) /
                (1 - (k : ℝ) * u) := by
            field_simp [ne_of_gt hd0]
          _ ≤ ((k : ℝ) + 1) * u / (1 - (k : ℝ) * u) := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hd0)
            nlinarith [mul_nonneg hku0 hu]
      calc
        ((k : ℝ) * u / (1 - (k : ℝ) * u) + u) / (1 - u)
            ≤ (((k : ℝ) + 1) * u / (1 - (k : ℝ) * u)) / (1 - u) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hu0)
        _ = ((k : ℝ) + 1) * u /
              ((1 - (k : ℝ) * u) * (1 - u)) := by
          rw [div_div]
        _ ≤ ((k : ℝ) + 1) * u / (1 - ((k : ℝ) + 1) * u) := by
          apply div_le_div_of_nonneg_left (mul_nonneg (by positivity) hu) hd1
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) hu]

private lemma rounded_fold_backward (fp : P29FPModel) :
    ∀ (m : ℕ) (a x : Fin m → ℝ) (b : ℝ),
      (m : ℝ) * fp.u < 1 →
      ∃ (α : ℝ) (e : Fin m → ℝ),
        |α - 1| ≤ p29Gamma fp.u m ∧
        (∀ t, |e t| ≤ p29Gamma fp.u m * |a t|) ∧
        b = α * Fin.foldl m
              (fun acc t ↦ fp.fl_sub acc (fp.fl_mul (a t) (x t))) b +
            ∑ t : Fin m, (a t + e t) * x t := by
  intro m
  induction m with
  | zero =>
      intro a x b hm
      refine ⟨1, fun t ↦ Fin.elim0 t, ?_, ?_, ?_⟩
      · simp [p29Gamma]
      · intro t
        exact Fin.elim0 t
      · simp
  | succ k ih =>
      intro a x b hm
      have hku : (k : ℝ) * fp.u < 1 := by
        have hu := fp.u_nonneg
        norm_num [Nat.cast_add, Nat.cast_one] at hm ⊢
        nlinarith [mul_nonneg (Nat.cast_nonneg k) hu]
      obtain ⟨α, e, hα, he, hEq⟩ :=
        ih (fun t ↦ a t.castSucc) (fun t ↦ x t.castSucc) b hku
      let s := Fin.foldl k
        (fun acc t ↦
          fp.fl_sub acc (fp.fl_mul (a t.castSucc) (x t.castSucc))) b
      obtain ⟨μ, hμ, hmul⟩ := fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨σ, hσ, hsub⟩ :=
        fp.model_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      have hu1 : fp.u < 1 := by
        have hle : fp.u ≤ ((k + 1 : ℕ) : ℝ) * fp.u := by
          norm_num [Nat.cast_add, Nat.cast_one]
          nlinarith [mul_nonneg (Nat.cast_nonneg k) fp.u_nonneg]
        exact lt_of_le_of_lt hle hm
      have hden : 1 + σ ≠ 0 := by
        have hslo := (abs_le.mp hσ).1
        nlinarith
      let enew : Fin (k + 1) → ℝ := Fin.lastCases
        (a (Fin.last k) * (α * (1 + μ) - 1)) e
      refine ⟨α / (1 + σ), enew, ?_, ?_, ?_⟩
      · exact gamma_step_div fp.u k fp.u_nonneg hm α σ hα hσ
      · intro t
        refine Fin.lastCases ?_ (fun i ↦ ?_) t
        · simp only [enew, Fin.lastCases_last]
          rw [abs_mul]
          simpa [mul_comm] using mul_le_mul_of_nonneg_right
            (gamma_step_mul fp.u k fp.u_nonneg hm α μ hα hμ)
              (abs_nonneg (a (Fin.last k)))
        · simp only [enew, Fin.lastCases_castSucc]
          exact (he i).trans (mul_le_mul_of_nonneg_right
            (gamma_mono fp.u fp.u_nonneg (Nat.le_succ k) hm) (abs_nonneg _))
      · rw [Fin.foldl_succ_last]
        change b = α / (1 + σ) *
            fp.fl_sub s (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) + _
        rw [hsub, hmul]
        rw [Fin.sum_univ_castSucc]
        simp only [enew, Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [hEq]
        field_simp [hden]
        ring

private lemma fin_sum_eq_lower_add {R : Type*} [AddCommMonoid R] :
    ∀ {n : ℕ} (i : Fin n) (f : Fin n → R),
      (∀ j, i.val < j.val → f j = 0) →
      ∑ j : Fin n, f j =
        (∑ t : Fin i.val, f ⟨t.val, lt_trans t.isLt i.isLt⟩) + f i := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i f hupper
      induction i using Fin.cases with
      | zero =>
        rw [Fin.sum_univ_succ]
        have hz : ∑ j : Fin n, f j.succ = 0 := by
          apply Fintype.sum_eq_zero
          intro j
          exact hupper j.succ (by simp)
        simp [hz]
      | succ i' =>
        rw [Fin.sum_univ_succ]
        rw [ih i' (fun j ↦ f j.succ) (by
          intro j hj
          exact hupper j.succ (Nat.succ_lt_succ hj))]
        change f 0 + ((∑ t : Fin i'.val, f ⟨t.val + 1, by omega⟩) + f i'.succ) =
          (∑ t : Fin (i'.val + 1), f ⟨t.val, by omega⟩) + f i'.succ
        rw [Fin.sum_univ_succ]
        simp only [Fin.val_zero, Fin.val_succ, add_assoc]
        congr 1

private lemma rounded_lower_row_backward (fp : P29FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (i : Fin n) (b : ℝ)
    (hdiag : a i ≠ 0)
    (hupper : ∀ j, i.val < j.val → a j = 0)
    (hvalid : P29GammaValid fp.u n) :
    let s := Fin.foldl i.val
      (fun acc t ↦
        fp.fl_sub acc
          (fp.fl_mul (a ⟨t.val, lt_trans t.isLt i.isLt⟩)
            (x ⟨t.val, lt_trans t.isLt i.isLt⟩))) b
    let q := fp.fl_div s (a i)
    ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ p29Gamma fp.u n * |a j|) ∧
      ∑ j : Fin n, (a j + e j) * (Function.update x i q) j = b := by
  dsimp only
  have hiValid : (i.val : ℝ) * fp.u < 1 := by
    apply lt_of_le_of_lt _ hvalid
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt i.isLt) fp.u_nonneg
  obtain ⟨α, elow, hα, helow, hEq⟩ := rounded_fold_backward fp i.val
    (fun t ↦ a ⟨t.val, lt_trans t.isLt i.isLt⟩)
    (fun t ↦ x ⟨t.val, lt_trans t.isLt i.isLt⟩) b hiValid
  let s := Fin.foldl i.val
    (fun acc t ↦
      fp.fl_sub acc
        (fp.fl_mul (a ⟨t.val, lt_trans t.isLt i.isLt⟩)
          (x ⟨t.val, lt_trans t.isLt i.isLt⟩))) b
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s (a i) hdiag
  have hisucc : i.val + 1 ≤ n := i.isLt
  have hisuccValid : ((i.val + 1 : ℕ) : ℝ) * fp.u < 1 := by
    apply lt_of_le_of_lt _ hvalid
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hisucc) fp.u_nonneg
  have hu1 : fp.u < 1 := by
    have hle : fp.u ≤ ((i.val + 1 : ℕ) : ℝ) * fp.u := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg (Nat.cast_nonneg i.val) fp.u_nonneg]
    exact lt_of_le_of_lt hle hisuccValid
  have hden : 1 + δ ≠ 0 := by
    have hlo := (abs_le.mp hδ).1
    nlinarith
  let ediag := a i * (α / (1 + δ) - 1)
  let e : Fin n → ℝ := fun j ↦
    if hj : j.val < i.val then
      elow ⟨j.val, hj⟩
    else if j = i then ediag else 0
  refine ⟨e, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < i.val
    · simp only [e, dif_pos hj]
      exact (helow ⟨j.val, hj⟩).trans
        (mul_le_mul_of_nonneg_right
          (gamma_mono fp.u fp.u_nonneg (Nat.le_of_lt i.isLt) hvalid)
          (abs_nonneg _))
    · by_cases hji : j = i
      · subst j
        simp only [e, dif_neg (lt_irrefl i.val), if_pos rfl, ediag, abs_mul]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right
          ((gamma_step_div fp.u i.val fp.u_nonneg hisuccValid α δ hα hδ).trans
            (gamma_mono fp.u fp.u_nonneg hisucc hvalid)) (abs_nonneg (a i))
      · simp only [e, dif_neg hj, if_neg hji, abs_zero]
        exact mul_nonneg (gamma_nonneg fp.u n fp.u_nonneg hvalid) (abs_nonneg _)
  · rw [fin_sum_eq_lower_add i]
    · have hlower :
          (∑ t : Fin i.val,
              (a ⟨t.val, lt_trans t.isLt i.isLt⟩ + elow t) *
                x ⟨t.val, lt_trans t.isLt i.isLt⟩) =
            ∑ t : Fin i.val,
              (a ⟨t.val, lt_trans t.isLt i.isLt⟩ +
                e ⟨t.val, lt_trans t.isLt i.isLt⟩) *
              (Function.update x i (fp.fl_div s (a i)))
                ⟨t.val, lt_trans t.isLt i.isLt⟩ := by
          apply Fintype.sum_congr
          intro t
          have hti :
              (⟨t.val, lt_trans t.isLt i.isLt⟩ : Fin n) ≠ i := by
            intro h
            have hv : t.val = i.val := congrArg Fin.val h
            exact (Nat.ne_of_lt t.isLt) hv
          have ht : (⟨t.val, t.isLt⟩ : Fin i.val) = t := Fin.ext rfl
          rw [Function.update_of_ne hti]
          simp only [e, dif_pos t.isLt]
      change
        (∑ t : Fin i.val,
            (a ⟨t.val, lt_trans t.isLt i.isLt⟩ +
              e ⟨t.val, lt_trans t.isLt i.isLt⟩) *
              (Function.update x i (fp.fl_div s (a i)))
                ⟨t.val, lt_trans t.isLt i.isLt⟩) +
            (a i + e i) * (Function.update x i (fp.fl_div s (a i))) i = b
      rw [← hlower]
      rw [Function.update_self]
      have hediag : e i = ediag := by simp [e]
      rw [hediag]
      dsimp only [ediag]
      have hterm :
          (a i + a i * (α / (1 + δ) - 1)) * fp.fl_div s (a i) = α * s := by
        rw [hdiv]
        field_simp [hdiag, hden]
        ring
      rw [hterm]
      have hEq' : b = α * s +
          ∑ t : Fin i.val,
            (a ⟨t.val, lt_trans t.isLt i.isLt⟩ + elow t) *
              x ⟨t.val, lt_trans t.isLt i.isLt⟩ := hEq
      simpa [add_comm] using hEq'.symm
    · intro j hj
      have hnotlt : ¬j.val < i.val := by omega
      have hne : j ≠ i := by
        intro h
        subst j
        omega
      simp only [hupper j hj, e, dif_neg hnotlt, if_neg hne, zero_add, zero_mul]

private lemma forward_steps_backward (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      ∃ Δ : P29Matrix n n,
        (∀ i j, |Δ i j| ≤ p29Gamma fp.u n * |L i j|) ∧
        (∀ i, n - k ≤ i.val →
          ∑ j : Fin n, (L i j + Δ i j) *
            p29ForwardSubSteps fp n L b k hk x j = b i) ∧
        (∀ i, i.val < n - k →
          p29ForwardSubSteps fp n L b k hk x i = x i) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      refine ⟨0, ?_, ?_, ?_⟩
      · intro i j
        simpa using mul_nonneg (gamma_nonneg fp.u n fp.u_nonneg hvalid)
          (abs_nonneg (L i j))
      · intro i hi
        omega
      · intro i hi
        rfl
  | succ k ih =>
      intro hk x
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      obtain ⟨Δtail, hΔtail, htailEq, htailKeep⟩ := ih hk' x'
      obtain ⟨erow, herow, hrowEq⟩ := rounded_lower_row_backward fp n
        (L ik) x ik (b ik) (hdiag ik) (hlower ik) hvalid
      have hrowEq' :
          ∑ j : Fin n, (L ik j + erow j) * x' j = b ik := by
        simpa only [ik, count, s, x'] using hrowEq
      let Δ : P29Matrix n n := fun i j ↦ if i = ik then erow j else Δtail i j
      refine ⟨Δ, ?_, ?_, ?_⟩
      · intro i j
        by_cases hi : i = ik
        · subst i
          simpa [Δ] using herow j
        · simpa [Δ, hi] using hΔtail i j
      · intro i hi
        have hstep :
            p29ForwardSubSteps fp n L b (k + 1) hk x =
              p29ForwardSubSteps fp n L b k hk' x' := by
          rfl
        rw [hstep]
        by_cases hii : i = ik
        · subst i
          have hsame :
              ∑ j : Fin n, (L ik j + Δ ik j) *
                  p29ForwardSubSteps fp n L b k hk' x' j =
                ∑ j : Fin n, (L ik j + erow j) * x' j := by
            apply Fintype.sum_congr
            intro j
            simp only [Δ, if_pos rfl]
            by_cases hj : j.val < n - k
            · rw [htailKeep j hj]
            · have hij : ik.val < j.val := by
                dsimp only [ik]
                omega
              rw [hlower ik j hij]
              have herowzero : erow j = 0 := by
                have hb := herow j
                rw [hlower ik j hij, abs_zero, mul_zero] at hb
                exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
              simp [herowzero]
          rw [hsame, hrowEq']
        · have hitail : n - k ≤ i.val := by
              have hv : i.val ≠ n - k - 1 := by
                intro hv
                apply hii
                apply Fin.ext
                exact hv
              omega
          simpa [Δ, hii] using htailEq i hitail
      · intro i hi
        have hstep :
            p29ForwardSubSteps fp n L b (k + 1) hk x =
              p29ForwardSubSteps fp n L b k hk' x' := by
          rfl
        rw [hstep, htailKeep i (by omega)]
        have hne : i ≠ ik := by
          intro h
          have hv := congrArg Fin.val h
          dsimp only [ik] at hv
          omega
        dsimp only [x']
        exact Function.update_of_ne hne _ _

private lemma fin_sum_eq_self_add_upper {R : Type*} [AddCommMonoid R] :
    ∀ {n : ℕ} (i : Fin n) (f : Fin n → R),
      (∀ j, j.val < i.val → f j = 0) →
      ∑ j : Fin n, f j = f i +
        ∑ t : Fin (n - (i.val + 1)),
          f ⟨i.val + 1 + t.val, by omega⟩ := by
  intro n
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i f hlower
      induction i using Fin.cases with
      | zero =>
        rw [Fin.sum_univ_succ]
        congr 1
        apply Fintype.sum_congr
        intro t
        apply congrArg f
        apply Fin.ext
        exact Nat.add_comm _ _
      | succ i' =>
        rw [Fin.sum_univ_succ]
        have hf0 : f 0 = 0 := hlower 0 (by simp)
        rw [hf0, zero_add]
        rw [ih i' (fun j ↦ f j.succ) (by
          intro j hj
          exact hlower j.succ (Nat.succ_lt_succ hj))]
        simp only [Fin.val_succ, Nat.succ_eq_add_one, Nat.succ_sub_succ_eq_sub]
        congr 1
        have hc : n + 1 - (i'.val + 1 + 1) = n - (i'.val + 1) := by omega
        refine Fintype.sum_equiv (finCongr hc.symm) _ _ ?_
        intro t
        apply congrArg f
        apply Fin.ext
        simp only [finCongr_apply, Fin.coe_cast, Fin.val_succ]
        omega

private lemma rounded_upper_row_backward (fp : P29FPModel) (n : ℕ)
    (a x : Fin n → ℝ) (i : Fin n) (b : ℝ)
    (hdiag : a i ≠ 0)
    (hlower : ∀ j, j.val < i.val → a j = 0)
    (hvalid : P29GammaValid fp.u n) :
    let count := n - (i.val + 1)
    let s := Fin.foldl count
      (fun acc t ↦
        fp.fl_sub acc
          (fp.fl_mul (a ⟨i.val + 1 + t.val, by omega⟩)
            (x ⟨i.val + 1 + t.val, by omega⟩))) b
    let q := fp.fl_div s (a i)
    ∃ e : Fin n → ℝ,
      (∀ j, |e j| ≤ p29Gamma fp.u n * |a j|) ∧
      ∑ j : Fin n, (a j + e j) * (Function.update x i q) j = b := by
  dsimp only
  let count := n - (i.val + 1)
  have hcountle : count ≤ n := Nat.sub_le _ _
  have hcountValid : (count : ℝ) * fp.u < 1 := by
    apply lt_of_le_of_lt _ hvalid
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcountle) fp.u_nonneg
  obtain ⟨α, eup, hα, heup, hEq⟩ := rounded_fold_backward fp count
    (fun t ↦ a ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩)
    (fun t ↦ x ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩)
    b hcountValid
  let s := Fin.foldl count
    (fun acc t ↦
      fp.fl_sub acc
        (fp.fl_mul (a ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩)
          (x ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩))) b
  obtain ⟨δ, hδ, hdiv⟩ := fp.model_div s (a i) hdiag
  have hcountsucc : count + 1 ≤ n := by
    dsimp only [count]
    omega
  have hcountsuccValid : ((count + 1 : ℕ) : ℝ) * fp.u < 1 := by
    apply lt_of_le_of_lt _ hvalid
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcountsucc) fp.u_nonneg
  have hu1 : fp.u < 1 := by
    have hle : fp.u ≤ ((count + 1 : ℕ) : ℝ) * fp.u := by
      norm_num [Nat.cast_add, Nat.cast_one]
      nlinarith [mul_nonneg (Nat.cast_nonneg count) fp.u_nonneg]
    exact lt_of_le_of_lt hle hcountsuccValid
  have hden : 1 + δ ≠ 0 := by
    have hlo := (abs_le.mp hδ).1
    nlinarith
  let ediag := a i * (α / (1 + δ) - 1)
  let e : Fin n → ℝ := fun j ↦
    if hj : i.val < j.val then
      eup ⟨j.val - (i.val + 1), by dsimp only [count]; omega⟩
    else if j = i then ediag else 0
  refine ⟨e, ?_, ?_⟩
  · intro j
    by_cases hj : i.val < j.val
    · simp only [e, dif_pos hj]
      let t : Fin count := ⟨j.val - (i.val + 1), by dsimp only [count]; omega⟩
      have htj : (⟨i.val + 1 + t.val, by dsimp only [count, t]; omega⟩ : Fin n) = j := by
        apply Fin.ext
        dsimp only [t]
        omega
      have hb := heup t
      rw [htj] at hb
      exact hb.trans
        (mul_le_mul_of_nonneg_right
          (gamma_mono fp.u fp.u_nonneg hcountle hvalid) (abs_nonneg (a j)))
    · by_cases hji : j = i
      · subst j
        simp only [e, dif_neg (lt_irrefl i.val), ediag, abs_mul]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right
          ((gamma_step_div fp.u count fp.u_nonneg hcountsuccValid α δ hα hδ).trans
            (gamma_mono fp.u fp.u_nonneg hcountsucc hvalid)) (abs_nonneg (a i))
      · simp only [e, dif_neg hj, if_neg hji, abs_zero]
        exact mul_nonneg (gamma_nonneg fp.u n fp.u_nonneg hvalid) (abs_nonneg _)
  · rw [fin_sum_eq_self_add_upper i]
    · have hupperSum :
          (∑ t : Fin count,
              (a ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩ + eup t) *
                x ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩) =
            ∑ t : Fin count,
              (a ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩ +
                e ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩) *
              (Function.update x i (fp.fl_div s (a i)))
                ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩ := by
          apply Fintype.sum_congr
          intro t
          let j : Fin n := ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩
          have hij : i.val < j.val := by dsimp only [j]; omega
          have hji : j ≠ i := by
            intro h
            have := congrArg Fin.val h
            omega
          rw [Function.update_of_ne hji]
          have ht : (⟨j.val - (i.val + 1), by dsimp only [count, j]; omega⟩ : Fin count) = t := by
            apply Fin.ext
            dsimp only [j]
            omega
          have hej : e j = eup t := by
            simp only [e, dif_pos hij]
            rw [ht]
          change (a j + eup t) * x j = (a j + e j) * x j
          rw [hej]
      change
        (a i + e i) * (Function.update x i (fp.fl_div s (a i))) i +
          (∑ t : Fin count,
            (a ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩ +
              e ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩) *
              (Function.update x i (fp.fl_div s (a i)))
                ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩) = b
      rw [← hupperSum, Function.update_self]
      have hediag : e i = ediag := by simp [e]
      rw [hediag]
      dsimp only [ediag]
      have hterm :
          (a i + a i * (α / (1 + δ) - 1)) * fp.fl_div s (a i) = α * s := by
        rw [hdiv]
        field_simp [hdiag, hden]
        ring
      rw [hterm]
      have hEq' : b = α * s +
          ∑ t : Fin count,
            (a ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩ + eup t) *
              x ⟨i.val + 1 + t.val, by dsimp only [count] at t; omega⟩ := hEq
      exact hEq'.symm
    · intro j hj
      have hnotupper : ¬i.val < j.val := by omega
      have hne : j ≠ i := by
        intro h
        subst j
        omega
      simp only [hlower j hj, e, dif_neg hnotupper, if_neg hne, zero_add, zero_mul]

private lemma back_steps_backward (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      ∃ Δ : P29Matrix n n,
        (∀ i j, |Δ i j| ≤ p29Gamma fp.u n * |U i j|) ∧
        (∀ i, i.val < k →
          ∑ j : Fin n, (U i j + Δ i j) *
            p29BackSubSteps fp n U b k hk x j = b i) ∧
        (∀ i, k ≤ i.val →
          p29BackSubSteps fp n U b k hk x i = x i) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      refine ⟨0, ?_, ?_, ?_⟩
      · intro i j
        simpa using mul_nonneg (gamma_nonneg fp.u n fp.u_nonneg hvalid)
          (abs_nonneg (U i j))
      · intro i hi
        omega
      · intro i hi
        rfl
  | succ k ih =>
      intro hk x
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) ↦
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      obtain ⟨Δtail, hΔtail, htailEq, htailKeep⟩ := ih hk' x'
      obtain ⟨erow, herow, hrowEq⟩ := rounded_upper_row_backward fp n
        (U ik) x ik (b ik) (hdiag ik) (hupper ik) hvalid
      have hrowEq' :
          ∑ j : Fin n, (U ik j + erow j) * x' j = b ik := by
        simpa only [ik, count, s, x', Nat.sub_sub] using hrowEq
      let Δ : P29Matrix n n := fun i j ↦ if i = ik then erow j else Δtail i j
      refine ⟨Δ, ?_, ?_, ?_⟩
      · intro i j
        by_cases hi : i = ik
        · subst i
          simpa [Δ] using herow j
        · simpa [Δ, hi] using hΔtail i j
      · intro i hi
        have hstep :
            p29BackSubSteps fp n U b (k + 1) hk x =
              p29BackSubSteps fp n U b k hk' x' := by
          rfl
        rw [hstep]
        by_cases hii : i = ik
        · subst i
          have hsame :
              ∑ j : Fin n, (U ik j + Δ ik j) *
                  p29BackSubSteps fp n U b k hk' x' j =
                ∑ j : Fin n, (U ik j + erow j) * x' j := by
            apply Fintype.sum_congr
            intro j
            simp only [Δ, if_pos rfl]
            by_cases hj : k ≤ j.val
            · rw [htailKeep j hj]
            · have hji : j.val < ik.val := by
                dsimp only [ik]
                omega
              rw [hupper ik j hji]
              have herowzero : erow j = 0 := by
                have hb := herow j
                rw [hupper ik j hji, abs_zero, mul_zero] at hb
                exact abs_eq_zero.mp (le_antisymm hb (abs_nonneg _))
              simp [herowzero]
          rw [hsame, hrowEq']
        · have hitail : i.val < k := by
              have hv : i.val ≠ k := by
                intro hv
                apply hii
                apply Fin.ext
                exact hv
              omega
          simpa [Δ, hii] using htailEq i hitail
      · intro i hi
        have hstep :
            p29BackSubSteps fp n U b (k + 1) hk x =
              p29BackSubSteps fp n U b k hk' x' := by
          rfl
        rw [hstep, htailKeep i (by omega)]
        have hne : i ≠ ik := by
          intro h
          have hv := congrArg Fin.val h
          dsimp only [ik] at hv
          omega
        dsimp only [x']
        exact Function.update_of_ne hne _ _

private lemma forward_sub_backward (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ Δ : P29Matrix n n,
      (∀ i j, |Δ i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n, (L i j + Δ i j) * p29ForwardSub fp n L b j = b i := by
  obtain ⟨Δ, hΔ, hEq, hkeep⟩ :=
    forward_steps_backward fp n L b hdiag hlower hvalid n (le_refl n) (fun _ ↦ 0)
  refine ⟨Δ, hΔ, ?_⟩
  intro i
  exact hEq i (by omega)

private lemma back_sub_backward (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ Δ : P29Matrix n n,
      (∀ i j, |Δ i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, ∑ j : Fin n, (U i j + Δ i j) * p29BackSub fp n U b j = b i := by
  obtain ⟨Δ, hΔ, hEq, hkeep⟩ :=
    back_steps_backward fp n U b hdiag hupper hvalid n (le_refl n) (fun _ ↦ 0)
  refine ⟨Δ, hΔ, ?_⟩
  intro i
  exact hEq i i.isLt

private lemma entryNorm_nonneg {m n : ℕ} (A : P29Matrix m n) :
    0 ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  positivity

private lemma entry_abs_le_norm {m n : ℕ} (A : P29Matrix m n)
    (i : Fin m) (j : Fin n) : |A i j| ≤ p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    |A i j| ≤ ∑ j' : Fin n, |A i j'| := by
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j' ↦ |A i j'|)
        (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |A i' j'| := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun i' ↦ ∑ j' : Fin n, |A i' j'|)
        (fun _ _ ↦ by positivity) (Finset.mem_univ i)

private lemma entryNorm_of_componentwise {m n : ℕ}
    (A E : P29Matrix m n) (c : ℝ)
    (h : ∀ i j, |E i j| ≤ c * |A i j|) :
    p29EntryNorm E ≤ c * p29EntryNorm A := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |E i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |A i j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact h i j
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |A i j| := by
      simp_rw [Finset.mul_sum]

private lemma entryNorm_add {m n : ℕ} (A B : P29Matrix m n) :
    p29EntryNorm (A + B) ≤ p29EntryNorm A + p29EntryNorm B := by
  unfold p29EntryNorm
  calc
    ∑ i : Fin m, ∑ j : Fin n, |(A + B) i j| ≤
        ∑ i : Fin m, ∑ j : Fin n, (|A i j| + |B i j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |A i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |B i j| := by
      simp_rw [Finset.sum_add_distrib]

private lemma entryNorm_matmul_square (n : ℕ) (A B : P29Matrix n n) :
    p29EntryNorm (p29MatMul A B) ≤
      (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
  have hentry : ∀ i j, |p29MatMul A B i j| ≤
      (n : ℝ) * p29EntryNorm A * p29EntryNorm B := by
    intro i j
    unfold p29MatMul
    calc
      |∑ k : Fin n, A i k * B k j| ≤ ∑ k : Fin n, |A i k * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin n, p29EntryNorm A * p29EntryNorm B := by
        apply Finset.sum_le_sum
        intro k hk
        rw [abs_mul]
        exact mul_le_mul (entry_abs_le_norm A i k) (entry_abs_le_norm B k j)
          (abs_nonneg _) (entryNorm_nonneg A)
      _ = (n : ℝ) * p29EntryNorm A * p29EntryNorm B := by
        simp
        ring
  unfold p29EntryNorm
  calc
    ∑ i : Fin n, ∑ j : Fin n, |p29MatMul A B i j| ≤
        ∑ _i : Fin n, ∑ _j : Fin n,
          ((n : ℝ) * p29EntryNorm A * p29EntryNorm B) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hentry i j
    _ = (n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B := by
      simp
      ring

private lemma entryNorm_three_mul (n : ℕ) (A B C : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
      (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul A B) C) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul A B) * p29EntryNorm C :=
      entryNorm_matmul_square n _ _
    _ ≤ (n : ℝ) ^ 3 *
          ((n : ℝ) ^ 3 * p29EntryNorm A * p29EntryNorm B) * p29EntryNorm C := by
      apply mul_le_mul_of_nonneg_right _ (entryNorm_nonneg C)
      exact mul_le_mul_of_nonneg_left (entryNorm_matmul_square n A B) (by positivity)
    _ = (n : ℝ) ^ 6 * p29EntryNorm A * p29EntryNorm B * p29EntryNorm C := by ring

private lemma matmul_add_left {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul (A + B) C = p29MatMul A C + p29MatMul B C := by
  ext i j
  simp [p29MatMul, add_mul, Finset.sum_add_distrib]

private lemma matmul_add_right {n : ℕ} (A B C : P29Matrix n n) :
    p29MatMul A (B + C) = p29MatMul A B + p29MatMul A C := by
  ext i j
  simp [p29MatMul, mul_add, Finset.sum_add_distrib]

private lemma combined_backward_error_expand {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  rw [p29CombinedBackwardError, p29PerturbedLDLT, p29LDLT]
  rw [matmul_add_left L ΔL (D + ΔD)]
  rw [matmul_add_left]
  rw [matmul_add_right L D ΔD]
  rw [matmul_add_left]
  rw [matmul_add_right (p29MatMul L D) (p29Transpose L) ΔU]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  ring

private lemma combined_backward_error_bound (fp : P29FPModel) (n : ℕ)
    (eta : ℝ) (L D ΔL ΔD ΔU : P29Matrix n n)
    (hvalid : P29GammaValid fp.u n) (heta : 0 ≤ eta)
    (hΔL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hΔD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hΔU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let g := p29Gamma fp.u n
  have hg : 0 ≤ g := gamma_nonneg fp.u n fp.u_nonneg hvalid
  have hNL : p29EntryNorm ΔL ≤ g * p29EntryNorm L :=
    entryNorm_of_componentwise L ΔL g hΔL
  have hNU : p29EntryNorm ΔU ≤ g * p29EntryNorm (p29Transpose L) :=
    entryNorm_of_componentwise (p29Transpose L) ΔU g hΔU
  have hLD : p29EntryNorm (D + ΔD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤ p29EntryNorm D + p29EntryNorm ΔD :=
        entryNorm_add D ΔD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D :=
        add_le_add (le_refl _) hΔD
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hLU : p29EntryNorm (p29Transpose L + ΔU) ≤
      (1 + g) * p29EntryNorm (p29Transpose L) := by
    calc
      p29EntryNorm (p29Transpose L + ΔU) ≤
          p29EntryNorm (p29Transpose L) + p29EntryNorm ΔU :=
        entryNorm_add _ _
      _ ≤ p29EntryNorm (p29Transpose L) +
          g * p29EntryNorm (p29Transpose L) := add_le_add (le_refl _) hNU
      _ = (1 + g) * p29EntryNorm (p29Transpose L) := by ring
  have hn6 : 0 ≤ (n : ℝ) ^ 6 := by positivity
  have hL0 : 0 ≤ p29EntryNorm L := entryNorm_nonneg L
  have hD0 : 0 ≤ p29EntryNorm D := entryNorm_nonneg D
  have hDL0 : 0 ≤ p29EntryNorm ΔL := entryNorm_nonneg ΔL
  have hDD0 : 0 ≤ p29EntryNorm ΔD := entryNorm_nonneg ΔD
  have hDU0 : 0 ≤ p29EntryNorm ΔU := entryNorm_nonneg ΔU
  have hT0 : 0 ≤ p29EntryNorm (p29Transpose L) := entryNorm_nonneg _
  have hDs0 : 0 ≤ p29EntryNorm (D + ΔD) := entryNorm_nonneg _
  have hUs0 : 0 ≤ p29EntryNorm (p29Transpose L + ΔU) := entryNorm_nonneg _
  have heta1 : 0 ≤ 1 + eta := by linarith
  have hg1 : 0 ≤ 1 + g := by linarith
  let T1 := p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)
  let T2 := p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)
  let T3 := p29MatMul (p29MatMul L D) ΔU
  have hT1 : p29EntryNorm T1 ≤
      (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
        ((1 + eta) * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm T1 ≤ (n : ℝ) ^ 6 * p29EntryNorm ΔL *
          p29EntryNorm (D + ΔD) * p29EntryNorm (p29Transpose L + ΔU) := by
        exact entryNorm_three_mul n _ _ _
      _ ≤ (n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        gcongr <;> positivity
  have hT2 : p29EntryNorm T2 ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * (eta * p29EntryNorm D) *
        ((1 + g) * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm T2 ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm ΔD * p29EntryNorm (p29Transpose L + ΔU) := by
        exact entryNorm_three_mul n _ _ _
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L * (eta * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) := by
        gcongr <;> positivity
  have hT3 : p29EntryNorm T3 ≤
      (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
        (g * p29EntryNorm (p29Transpose L)) := by
    calc
      p29EntryNorm T3 ≤ (n : ℝ) ^ 6 * p29EntryNorm L *
          p29EntryNorm D * p29EntryNorm ΔU := by
        exact entryNorm_three_mul n _ _ _
      _ ≤ (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (g * p29EntryNorm (p29Transpose L)) := by
        gcongr <;> positivity
  rw [combined_backward_error_expand]
  change p29EntryNorm (T1 + T2 + T3) ≤ _
  calc
    p29EntryNorm (T1 + T2 + T3) ≤
        (p29EntryNorm T1 + p29EntryNorm T2) + p29EntryNorm T3 :=
      (entryNorm_add (T1 + T2) T3).trans
        (add_le_add (entryNorm_add T1 T2) (le_refl _))
    _ ≤
        ((n : ℝ) ^ 6 * (g * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L)) +
        (n : ℝ) ^ 6 * p29EntryNorm L * (eta * p29EntryNorm D) *
          ((1 + g) * p29EntryNorm (p29Transpose L))) +
        (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (g * p29EntryNorm (p29Transpose L)) :=
      add_le_add (add_le_add hT1 hT2) hT3
    _ = p29SolveBackwardFactor fp n eta L D := by
      dsimp only [g]
      rw [p29SolveBackwardFactor]
      ring

private lemma three_mul_action {n : ℕ}
    (P Q R : P29Matrix n n) (x z y b : Fin n → ℝ)
    (hR : ∀ i, ∑ j : Fin n, R i j * x j = z i)
    (hQ : ∀ i, ∑ j : Fin n, Q i j * z j = y i)
    (hP : ∀ i, ∑ j : Fin n, P i j * y j = b i) :
    ∀ i, ∑ j : Fin n,
      p29MatMul (p29MatMul P Q) R i j * x j = b i := by
  intro i
  simp only [p29MatMul]
  calc
    ∑ j : Fin n, (∑ k : Fin n, (∑ l : Fin n, P i l * Q l k) * R k j) * x j =
        ∑ k : Fin n, (∑ l : Fin n, P i l * Q l k) *
          (∑ j : Fin n, R k j * x j) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      ring
    _ = ∑ k : Fin n, (∑ l : Fin n, P i l * Q l k) * z k := by
      apply Fintype.sum_congr
      intro k
      rw [hR k]
    _ = ∑ l : Fin n, P i l * (∑ k : Fin n, Q l k * z k) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      ring
    _ = ∑ l : Fin n, P i l * y l := by
      apply Fintype.sum_congr
      intro l
      rw [hQ l]
    _ = b i := hP i

/-- P29-T2: the normwise backward-stability conclusion for the `LDLᵀ`
solution phase in Appendix B. -/
theorem p29_t2_ldlt_solve_backward_stability
    (fp : P29FPModel) (n : ℕ) (A L D E0 : P29Matrix n n)
    (b z : Fin n → ℝ) (eta factorEta : ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n)
    (heta : 0 ≤ eta)
    (hfactor : p29LDLT L D = A + E0)
    (hE0 : p29EntryNorm E0 ≤ factorEta * p29EntryNorm A)
    (hDsolve : P29BlockSolveStable n D
      (p29ForwardSub fp n L b) z eta) :
    ∃ (ΔL ΔD ΔU F : P29Matrix n n),
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      p29EntryNorm ΔD ≤ eta * p29EntryNorm D ∧
      (∀ i j, |ΔU i j| ≤
        p29Gamma fp.u n * |p29Transpose L i j|) ∧
      F = p29TotalBackwardError E0 L D ΔL ΔD ΔU ∧
      (∀ i, ∑ j : Fin n,
        (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j = b i) ∧
      p29EntryNorm F ≤
        p29TotalBackwardBound fp n eta factorEta A L D := by
  -- PROOF_START P29-T2-H001
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    forward_sub_backward fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  have htdiag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have htupper : ∀ i j : Fin n, j.val < i.val → p29Transpose L i j = 0 := by
    intro i j hij
    exact hlower j i hij
  obtain ⟨ΔU, hΔU, hback⟩ :=
    back_sub_backward fp n (p29Transpose L) z htdiag htupper hvalid
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · have hchain : ∀ i, ∑ j : Fin n,
        p29PerturbedLDLT L D ΔL ΔD ΔU i j *
          p29BackSub fp n (p29Transpose L) z j = b i := by
      exact three_mul_action
        (L + ΔL) (D + ΔD) (p29Transpose L + ΔU)
        (p29BackSub fp n (p29Transpose L) z) z (p29ForwardSub fp n L b) b
        hback hblock hforward
    have hAF : A + F = p29PerturbedLDLT L D ΔL ΔD ΔU := by
      dsimp only [F]
      rw [p29TotalBackwardError, p29CombinedBackwardError]
      rw [← add_assoc, ← hfactor]
      abel
    intro i
    change ∑ j : Fin n, (A + F) i j *
      p29BackSub fp n (p29Transpose L) z j = b i
    rw [hAF]
    exact hchain i
  · dsimp only [F]
    rw [p29TotalBackwardError]
    calc
      p29EntryNorm (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
          p29EntryNorm E0 + p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) :=
        entryNorm_add _ _
      _ ≤ factorEta * p29EntryNorm A + p29SolveBackwardFactor fp n eta L D :=
        add_le_add hE0
          (combined_backward_error_bound fp n eta L D ΔL ΔD ΔU
            hvalid heta hΔL hΔD hΔU)
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
