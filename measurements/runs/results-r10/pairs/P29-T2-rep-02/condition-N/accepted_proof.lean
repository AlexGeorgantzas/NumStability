import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29_gamma_nonneg {u : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hk : (k : ℝ) * u < 1) :
    0 ≤ p29Gamma u k := by
  rw [p29Gamma]
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (sub_nonneg.mpr (le_of_lt hk))

private lemma p29_gamma_mono_nat {u : ℝ} {k n : ℕ}
    (hu : 0 ≤ u) (hvalid : P29GammaValid u n) (hkn : k ≤ n) :
    p29Gamma u k ≤ p29Gamma u n := by
  rw [p29Gamma, p29Gamma]
  have hku : (k : ℝ) * u ≤ (n : ℝ) * u := by
    gcongr
  have hdenn : 0 < 1 - (n : ℝ) * u := sub_pos.mpr hvalid
  have hdenk : 0 < 1 - (k : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hdenk hdenn).mpr
  nlinarith

private lemma p29_gamma_mul_step {u q d : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hq : |q - 1| ≤ p29Gamma u k) (hd : |d| ≤ u) :
    |q * (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hku : (k : ℝ) * u < 1 := by
    have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hcast hu]
  have hg : 0 ≤ p29Gamma u k := p29_gamma_nonneg hu hku
  have had : |1 + d| ≤ 1 + u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + u := by norm_num; linarith
  calc
    |q * (1 + d) - 1| = |(q - 1) * (1 + d) + d| := by ring_nf
    _ ≤ |q - 1| * |1 + d| + |d| := by
      simpa [abs_mul] using abs_add_le ((q - 1) * (1 + d)) d
    _ ≤ p29Gamma u k * (1 + u) + u := by gcongr
    _ ≤ p29Gamma u (k + 1) := by
      rw [p29Gamma, p29Gamma]
      have hd0 : 0 < 1 - (k : ℝ) * u := by linarith
      have hd1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
      rw [show (k : ℝ) * u / (1 - (k : ℝ) * u) * (1 + u) + u =
          ((k : ℝ) * u * (1 + u) + u * (1 - (k : ℝ) * u)) /
            (1 - (k : ℝ) * u) by field_simp]
      have heq : (k : ℝ) * u * (1 + u) + u * (1 - (k : ℝ) * u) =
          ((k + 1 : ℕ) : ℝ) * u := by
        push_cast
        ring
      rw [heq]
      apply div_le_div_of_nonneg_left (by positivity) hd1
      push_cast
      nlinarith

private lemma p29_gamma_div_step {u q d : ℝ} {k : ℕ}
    (hu : 0 ≤ u) (hk : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hq : |q - 1| ≤ p29Gamma u k) (hd : |d| ≤ u) :
    |q / (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hu1 : u < 1 := by
    have hkpos : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hkpos hu]
  have hden : 0 < 1 + d := by
    have hneg : -u ≤ d := (abs_le.mp hd).1
    linarith
  have hku : (k : ℝ) * u < 1 := by
    have hcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hcast hu]
  have hg : 0 ≤ p29Gamma u k := p29_gamma_nonneg hu hku
  have halg : q / (1 + d) - 1 = (q - (1 + d)) / (1 + d) := by
    field_simp [ne_of_gt hden]
  rw [halg, abs_div, abs_of_pos hden]
  have hnum : |q - (1 + d)| ≤ p29Gamma u k + u := by
    calc
      |q - (1 + d)| = |(q - 1) - d| := by ring_nf
      _ ≤ |q - 1| + |d| := by
        simpa using abs_sub_le (q - 1) 0 d
      _ ≤ p29Gamma u k + u := by linarith
  calc
    |q - (1 + d)| / (1 + d) ≤
        (p29Gamma u k + u) / (1 - u) := by
      calc
        |q - (1 + d)| / (1 + d) ≤
            (p29Gamma u k + u) / (1 + d) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
        _ ≤ (p29Gamma u k + u) / (1 - u) := by
          apply div_le_div_of_nonneg_left (by positivity) (by linarith)
          linarith [(abs_le.mp hd).1]
    _ ≤ p29Gamma u (k + 1) := by
      rw [p29Gamma, p29Gamma]
      have hd0 : 0 < 1 - (k : ℝ) * u := by linarith
      have hd1 : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
      rw [show (k : ℝ) * u / (1 - (k : ℝ) * u) + u =
          ((k : ℝ) * u + u * (1 - (k : ℝ) * u)) /
            (1 - (k : ℝ) * u) by field_simp]
      rw [div_div]
      have hleftden : 0 < (1 - (k : ℝ) * u) * (1 - u) :=
        mul_pos hd0 (by linarith)
      calc
        ((k : ℝ) * u + u * (1 - (k : ℝ) * u)) /
              ((1 - (k : ℝ) * u) * (1 - u)) ≤
            (((k + 1 : ℕ) : ℝ) * u) /
              ((1 - (k : ℝ) * u) * (1 - u)) := by
          apply div_le_div_of_nonneg_right _ hleftden.le
          push_cast
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) hu]
        _ ≤ (((k + 1 : ℕ) : ℝ) * u) /
              (1 - ((k + 1 : ℕ) : ℝ) * u) := by
          apply div_le_div_of_nonneg_left (by positivity) hd1
          push_cast
          nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hu) hu]

private lemma p29_rounded_sub_fold_backward
    (fp : P29FPModel) (N count : ℕ) (hcount : count ≤ N)
    (hvalid : P29GammaValid fp.u N)
    (a x : Fin count → ℝ) (b : ℝ) :
    ∃ (q : ℝ) (Δ : Fin count → ℝ),
      |q - 1| ≤ p29Gamma fp.u count ∧
      (∀ t, |Δ t| ≤ p29Gamma fp.u count * |a t|) ∧
      b = q * Fin.foldl count
          (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) b +
        ∑ t : Fin count, (a t + Δ t) * x t := by
  induction count generalizing b with
  | zero =>
      refine ⟨1, fun t => Fin.elim0 t, ?_, ?_, ?_⟩
      · simp [p29Gamma]
      · intro t
        exact Fin.elim0 t
      · simp [Fin.foldl_zero]
  | succ k ih =>
      have hkN : k ≤ N := by omega
      obtain ⟨q, Δ, hq, hΔ, heq⟩ :=
        ih hkN (fun t => a t.castSucc) (fun t => x t.castSucc) b
      let old := Fin.foldl k
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (a t.castSucc) (x t.castSucc))) b
      obtain ⟨μ, hμ, hm⟩ := fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨σ, hσ, hs⟩ :=
        fp.model_sub old (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      have hstepvalid : (((k + 1 : ℕ) : ℝ) * fp.u) < 1 := by
        have hcast : ((k + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcount
        have hmul := mul_le_mul_of_nonneg_right hcast fp.u_nonneg
        exact lt_of_le_of_lt hmul hvalid
      have hu1 : fp.u < 1 := by
        have hone : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hone fp.u_nonneg]
      have hσne : 1 + σ ≠ 0 := by
        have := (abs_le.mp hσ).1
        linarith
      let Δ' : Fin (k + 1) → ℝ := Fin.lastCases
        (a (Fin.last k) * (q * (1 + μ) - 1)) Δ
      refine ⟨q / (1 + σ), Δ',
        p29_gamma_div_step fp.u_nonneg hstepvalid hq hσ, ?_, ?_⟩
      · intro t
        refine Fin.lastCases ?_ (fun i => ?_) t
        · simp only [Δ', Fin.lastCases_last]
          rw [abs_mul]
          calc
            |a (Fin.last k)| * |q * (1 + μ) - 1| ≤
                |a (Fin.last k)| * p29Gamma fp.u (k + 1) :=
              mul_le_mul_of_nonneg_left
                (p29_gamma_mul_step fp.u_nonneg hstepvalid hq hμ)
                (abs_nonneg _)
            _ = p29Gamma fp.u (k + 1) * |a (Fin.last k)| := by ring
        · simp only [Δ', Fin.lastCases_castSucc]
          calc
            |Δ i| ≤ p29Gamma fp.u k * |a i.castSucc| := hΔ i
            _ ≤ p29Gamma fp.u (k + 1) * |a i.castSucc| := by
              gcongr
              exact p29_gamma_mono_nat fp.u_nonneg hstepvalid (by omega)
      · rw [Fin.foldl_succ_last]
        change b = q / (1 + σ) *
            fp.fl_sub old (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) + _
        rw [Fin.sum_univ_castSucc]
        simp only [Δ', Fin.lastCases_castSucc, Fin.lastCases_last]
        rw [hs, hm]
        rw [show q / (1 + σ) *
              ((old - a (Fin.last k) * x (Fin.last k) * (1 + μ)) *
                (1 + σ)) =
              q * (old - a (Fin.last k) * x (Fin.last k) * (1 + μ)) by
          field_simp [hσne]]
        rw [heq]
        ring

private lemma p29_sum_lt_diag {n : ℕ} (i : Fin n)
    (f : Fin n → ℝ) (d : ℝ) :
    (∑ j : Fin n,
      if j.val < i.val then f j
      else if j = i then d else 0) =
      (∑ t : Fin i.val,
        f ⟨t.val, lt_trans t.isLt i.isLt⟩) + d := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ k ih =>
      refine Fin.lastCases ?_ (fun i₀ => ?_) i
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, Fin.lastCases_last]
        have hall : ∀ j : Fin k, j.val < k := fun j => j.isLt
        simp only [hall, if_true]
        congr 1
        simp
      · rw [Fin.sum_univ_castSucc]
        simp only [Fin.val_castSucc, Fin.val_last, Fin.lastCases_castSucc]
        have hlast : ¬ k < i₀.val := by omega
        simp only [hlast, if_false]
        have hne : Fin.last k ≠ i₀.castSucc := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [hne, if_false, add_zero]
        simpa using ih i₀ (fun j : Fin k => f j.castSucc)

private lemma p29_forward_steps_preserve
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (r : Fin n)
    (hr : r.val < n - k) :
    p29ForwardSubSteps fp n L b k hk x r = x r := by
  induction k generalizing x with
  | zero => simp [p29ForwardSubSteps]
  | succ k ih =>
      rw [p29ForwardSubSteps]
      rw [ih]
      · simp [Function.update, Finset.mem_singleton]
        intro heq
        have hv := congrArg Fin.val heq
        simp at hv
        omega
      · omega

private lemma p29_forward_steps_backward
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    let y := p29ForwardSubSteps fp n L b k hk x
    ∃ Δ : P29Matrix n n,
      (∀ i j, |Δ i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, n - k ≤ i.val →
        ∑ j : Fin n, (L i j + Δ i j) * y j = b i := by
  induction k generalizing x with
  | zero =>
      dsimp only [p29ForwardSubSteps]
      refine ⟨0, ?_, ?_⟩
      · intro i j
        rw [show (0 : P29Matrix n n) i j = 0 by rfl, abs_zero]
        exact mul_nonneg (p29_gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
      · intro i hi
        omega
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let xi := fp.fl_div s (L ik ik)
      let x' : Fin n → ℝ := Function.update x ik xi
      let hk' : k ≤ n := Nat.le_of_succ_le hk
      let y := p29ForwardSubSteps fp n L b k hk' x'
      obtain ⟨Δr, hΔr, hyr⟩ := ih hk' x'
      obtain ⟨q, δ, hq, hδ, hfold⟩ :=
        p29_rounded_sub_fold_backward fp n count (by omega) hvalid
          (fun t => L ik ⟨t.val, by omega⟩)
          (fun t => x ⟨t.val, by omega⟩) (b ik)
      obtain ⟨d, hd, hdiv⟩ := fp.model_div s (L ik ik) (hdiag ik)
      have hcountstep : (((count + 1 : ℕ) : ℝ) * fp.u) < 1 := by
        have hc : count + 1 ≤ n := by omega
        have hcast : ((count + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
      have hudiv : 1 + d ≠ 0 := by
        have hu1 : fp.u < 1 := by
          have hone : (1 : ℝ) ≤ ((count + 1 : ℕ) : ℝ) := by norm_num
          nlinarith [mul_le_mul_of_nonneg_right hone fp.u_nonneg]
        have := (abs_le.mp hd).1
        linarith
      let row : Fin n → ℝ := fun j =>
        if hj : j.val < ik.val then δ ⟨j.val, by simpa [ik, count] using hj⟩
        else if j = ik then L ik ik * (q / (1 + d) - 1) else 0
      let Δ : P29Matrix n n := fun i j => if i = ik then row j else Δr i j
      refine ⟨Δ, ?_, ?_⟩
      · intro i j
        dsimp only [Δ]
        split_ifs with hi
        · subst i
          dsimp only [row]
          split_ifs with hj hji
          · calc
              |δ ⟨j.val, by simpa [ik, count] using hj⟩| ≤
                  p29Gamma fp.u count * |L ik j| := by
                simpa using hδ ⟨j.val, by simpa [ik, count] using hj⟩
              _ ≤ p29Gamma fp.u n * |L ik j| := by
                gcongr
                exact p29_gamma_mono_nat fp.u_nonneg hvalid (by omega)
          · subst j
            rw [abs_mul]
            calc
              |L ik ik| * |q / (1 + d) - 1| ≤
                  |L ik ik| * p29Gamma fp.u (count + 1) :=
                mul_le_mul_of_nonneg_left
                  (p29_gamma_div_step fp.u_nonneg hcountstep hq hd)
                  (abs_nonneg _)
              _ ≤ p29Gamma fp.u n * |L ik ik| := by
                rw [mul_comm]
                gcongr
                exact p29_gamma_mono_nat fp.u_nonneg hvalid (by omega)
          · simp only [abs_zero]
            exact mul_nonneg (p29_gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
        · exact hΔr i j
      · intro i hi
        dsimp only [Δ]
        by_cases hik : i = ik
        · subst i
          simp only [if_pos]
          have hy_prev : ∀ t : Fin count,
              y ⟨t.val, by omega⟩ = x ⟨t.val, by omega⟩ := by
            intro t
            dsimp only [y]
            rw [p29_forward_steps_preserve]
            · simp [x', Function.update]
              intro he
              have hv := congrArg Fin.val he
              simp [ik, count] at hv
              omega
            · simp [ik, count]
              omega
          have hy_diag : y ik = xi := by
            dsimp only [y]
            rw [p29_forward_steps_preserve]
            · simp [x', Function.update]
            · simp [ik]
              omega
          have hdiagterm :
              (L ik ik + L ik ik * (q / (1 + d) - 1)) * xi = q * s := by
            dsimp only [xi]
            rw [hdiv]
            field_simp [hdiag ik, hudiv]
            ring
          calc
            (∑ j : Fin n, (L ik j + row j) * y j) =
                ∑ j : Fin n,
                  if j.val < ik.val then
                    (L ik j + row j) * y j
                  else if j = ik then
                    (L ik ik + L ik ik * (q / (1 + d) - 1)) * y ik
                  else 0 := by
              apply Finset.sum_congr rfl
              intro j hjmem
              dsimp only [row]
              split_ifs with hj hji
              · rfl
              · subst j
                rfl
              · rw [hlower ik j]
                · simp
                · by_contra hnlt
                  have hle : j.val ≤ ik.val := Nat.le_of_not_gt hnlt
                  have heqv : j.val = ik.val := Nat.le_antisymm hle (Nat.le_of_not_gt hj)
                  apply hji
                  exact Fin.ext heqv
            _ = (∑ t : Fin ik.val,
                    (L ik ⟨t.val, lt_trans t.isLt ik.isLt⟩ +
                      row ⟨t.val, lt_trans t.isLt ik.isLt⟩) *
                      y ⟨t.val, lt_trans t.isLt ik.isLt⟩) +
                  (L ik ik + L ik ik * (q / (1 + d) - 1)) * y ik := by
              apply p29_sum_lt_diag
            _ = (∑ t : Fin count,
                    (L ik ⟨t.val, by omega⟩ + δ t) *
                      x ⟨t.val, by omega⟩) + q * s := by
              rw [hy_diag, hdiagterm]
              congr 1
              apply Finset.sum_congr
              · simp [ik, count]
              · intro t ht
                simp only [row]
                rw [dif_pos]
                · rw [hy_prev]
                · simpa [ik, count] using t.isLt
            _ = b ik := by
              change b ik = q * s +
                ∑ t : Fin count,
                  (L ik ⟨t.val, by omega⟩ + δ t) * x ⟨t.val, by omega⟩ at hfold
              linarith [hfold]
        · simp only [if_neg hik]
          apply hyr i
          have hival : i.val ≠ ik.val := by
            intro hv
            apply hik
            exact Fin.ext hv
          simp [ik] at hival ⊢
          omega

private lemma p29_sum_diag_gt_rev {n : ℕ} (i : Fin n)
    (f : Fin n → ℝ) (d : ℝ) :
    (∑ j : Fin n,
      if i.val < j.val then f j
      else if j = i then d else 0) =
      d + ∑ t : Fin (Fin.rev i).val,
        f (Fin.rev ⟨t.val, lt_trans t.isLt (Fin.rev i).isLt⟩) := by
  calc
    (∑ j : Fin n,
      if i.val < j.val then f j else if j = i then d else 0) =
        ∑ r : Fin n,
          if r.val < (Fin.rev i).val then f (Fin.rev r)
          else if r = Fin.rev i then d else 0 := by
      apply Fintype.sum_equiv Fin.revPerm
      intro j
      simp only [Fin.revPerm_apply, Fin.rev_rev]
      split_ifs <;> simp_all [Fin.rev] <;> omega
    _ = (∑ t : Fin (Fin.rev i).val,
          f (Fin.rev ⟨t.val, lt_trans t.isLt (Fin.rev i).isLt⟩)) + d := by
      apply p29_sum_lt_diag
    _ = d + ∑ t : Fin (Fin.rev i).val,
          f (Fin.rev ⟨t.val, lt_trans t.isLt (Fin.rev i).isLt⟩) := by ring

private lemma p29_sum_diag_gt {n : ℕ} (i : Fin n)
    (f : Fin n → ℝ) (d : ℝ) :
    (∑ j : Fin n,
      if i.val < j.val then f j
      else if j = i then d else 0) =
      d + ∑ t : Fin (Fin.rev i).val,
        f ⟨i.val + 1 + t.val, by
          have hir : i.val + 1 + (Fin.rev i).val = n := by simp [Fin.rev]
          omega⟩ := by
  rw [p29_sum_diag_gt_rev]
  congr 1
  let g : Fin (Fin.rev i).val → ℝ := fun t =>
    f ⟨i.val + 1 + t.val, by
      have hir : i.val + 1 + (Fin.rev i).val = n := by simp [Fin.rev]
      omega⟩
  calc
    (∑ t : Fin (Fin.rev i).val,
        f (Fin.rev ⟨t.val, lt_trans t.isLt (Fin.rev i).isLt⟩)) =
        ∑ t : Fin (Fin.rev i).val, g (Fin.rev t) := by
      apply Finset.sum_congr rfl
      intro t ht
      dsimp only [g]
      congr 1
      apply Fin.ext
      simp [Fin.rev]
      omega
    _ = ∑ t : Fin (Fin.rev i).val, g t := by
      apply Fintype.sum_equiv Fin.revPerm
      intro t
      rfl
    _ = ∑ t : Fin (Fin.rev i).val,
        f ⟨i.val + 1 + t.val, by
          have hir : i.val + 1 + (Fin.rev i).val = n := by simp [Fin.rev]
          omega⟩ := rfl

private lemma p29_back_steps_preserve
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (r : Fin n)
    (hr : k ≤ r.val) :
    p29BackSubSteps fp n U b k hk x r = x r := by
  induction k generalizing x with
  | zero => simp [p29BackSubSteps]
  | succ k ih =>
      rw [p29BackSubSteps]
      rw [ih]
      · simp [Function.update]
        intro heq
        have hv := congrArg Fin.val heq
        simp at hv
        omega
      · omega

private lemma p29_back_steps_backward
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    let y := p29BackSubSteps fp n U b k hk x
    ∃ Δ : P29Matrix n n,
      (∀ i j, |Δ i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, i.val < k →
        ∑ j : Fin n, (U i j + Δ i j) * y j = b i := by
  induction k generalizing x with
  | zero =>
      dsimp only [p29BackSubSteps]
      refine ⟨0, ?_, ?_⟩
      · intro i j
        rw [show (0 : P29Matrix n n) i j = 0 by rfl, abs_zero]
        exact mul_nonneg (p29_gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
      · intro i hi
        omega
  | succ k ih =>
      let ik : Fin n := ⟨k, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let xi := fp.fl_div s (U ik ik)
      let x' : Fin n → ℝ := Function.update x ik xi
      let hk' : k ≤ n := Nat.le_of_succ_le hk
      let y := p29BackSubSteps fp n U b k hk' x'
      obtain ⟨Δr, hΔr, hyr⟩ := ih hk' x'
      obtain ⟨q, δ, hq, hδ, hfold⟩ :=
        p29_rounded_sub_fold_backward fp n count (by omega) hvalid
          (fun t => U ik ⟨k + 1 + t.val, by omega⟩)
          (fun t => x ⟨k + 1 + t.val, by omega⟩) (b ik)
      obtain ⟨d, hd, hdiv⟩ := fp.model_div s (U ik ik) (hdiag ik)
      have hcountstep : (((count + 1 : ℕ) : ℝ) * fp.u) < 1 := by
        have hc : count + 1 ≤ n := by omega
        have hcast : ((count + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hc
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hvalid
      have hudiv : 1 + d ≠ 0 := by
        have hu1 : fp.u < 1 := by
          have hone : (1 : ℝ) ≤ ((count + 1 : ℕ) : ℝ) := by norm_num
          nlinarith [mul_le_mul_of_nonneg_right hone fp.u_nonneg]
        have := (abs_le.mp hd).1
        linarith
      let row : Fin n → ℝ := fun j =>
        if hj : ik.val < j.val then
          δ ⟨j.val - k - 1, by simp [ik, count] at hj ⊢; omega⟩
        else if j = ik then U ik ik * (q / (1 + d) - 1) else 0
      let Δ : P29Matrix n n := fun i j => if i = ik then row j else Δr i j
      refine ⟨Δ, ?_, ?_⟩
      · intro i j
        dsimp only [Δ]
        split_ifs with hi
        · subst i
          dsimp only [row]
          split_ifs with hj hji
          · let tj : Fin count :=
              ⟨j.val - k - 1, by simp [ik, count] at hj ⊢; omega⟩
            have heqj : (⟨k + 1 + tj.val, by omega⟩ : Fin n) = j := by
              apply Fin.ext
              dsimp only [tj]
              simp [ik] at hj
              omega
            calc
              |δ ⟨j.val - k - 1, by simp [ik, count] at hj ⊢; omega⟩| =
                  |δ tj| := rfl
              _ ≤ p29Gamma fp.u count * |U ik ⟨k + 1 + tj.val, by omega⟩| := hδ tj
              _ = p29Gamma fp.u count * |U ik j| := by rw [heqj]
              _ ≤ p29Gamma fp.u n * |U ik j| := by
                gcongr
                exact p29_gamma_mono_nat fp.u_nonneg hvalid (by omega)
          · subst j
            rw [abs_mul]
            calc
              |U ik ik| * |q / (1 + d) - 1| ≤
                  |U ik ik| * p29Gamma fp.u (count + 1) :=
                mul_le_mul_of_nonneg_left
                  (p29_gamma_div_step fp.u_nonneg hcountstep hq hd)
                  (abs_nonneg _)
              _ ≤ p29Gamma fp.u n * |U ik ik| := by
                rw [mul_comm]
                gcongr
                exact p29_gamma_mono_nat fp.u_nonneg hvalid (by omega)
          · rw [abs_zero]
            exact mul_nonneg (p29_gamma_nonneg fp.u_nonneg hvalid) (abs_nonneg _)
        · exact hΔr i j
      · intro i hi
        dsimp only [Δ]
        by_cases hik : i = ik
        · subst i
          simp only [if_pos]
          have hy_after : ∀ t : Fin count,
              y ⟨k + 1 + t.val, by omega⟩ = x ⟨k + 1 + t.val, by omega⟩ := by
            intro t
            dsimp only [y]
            rw [p29_back_steps_preserve]
            · simp [x', Function.update]
              intro he
              have hv := congrArg Fin.val he
              simp [ik] at hv
              omega
            · simpa [Nat.add_assoc] using Nat.le_add_right k (1 + t.val)
          have hy_diag : y ik = xi := by
            dsimp only [y]
            rw [p29_back_steps_preserve]
            · simp [x', Function.update]
            · simp [ik]
          have hdiagterm :
              (U ik ik + U ik ik * (q / (1 + d) - 1)) * xi = q * s := by
            dsimp only [xi]
            rw [hdiv]
            field_simp [hdiag ik, hudiv]
            ring
          calc
            (∑ j : Fin n, (U ik j + row j) * y j) =
                ∑ j : Fin n,
                  if ik.val < j.val then (U ik j + row j) * y j
                  else if j = ik then
                    (U ik ik + U ik ik * (q / (1 + d) - 1)) * y ik
                  else 0 := by
              apply Finset.sum_congr rfl
              intro j hjmem
              dsimp only [row]
              split_ifs with hj hji
              · rfl
              · subst j
                rfl
              · rw [hupper ik j]
                · simp
                · by_contra hnlt
                  have hle : ik.val ≤ j.val := Nat.le_of_not_gt hnlt
                  have heqv : j.val = ik.val := Nat.le_antisymm (Nat.le_of_not_gt hj) hle
                  apply hji
                  exact Fin.ext heqv
            _ = (U ik ik + U ik ik * (q / (1 + d) - 1)) * y ik +
                  ∑ t : Fin (Fin.rev ik).val,
                    (U ik ⟨ik.val + 1 + t.val, by
                        have hir : ik.val + 1 + (Fin.rev ik).val = n := by simp [Fin.rev]
                        omega⟩ +
                      row ⟨ik.val + 1 + t.val, by
                        have hir : ik.val + 1 + (Fin.rev ik).val = n := by simp [Fin.rev]
                        omega⟩) *
                      y ⟨ik.val + 1 + t.val, by
                        have hir : ik.val + 1 + (Fin.rev ik).val = n := by simp [Fin.rev]
                        omega⟩ := by
              apply p29_sum_diag_gt
            _ = q * s + ∑ t : Fin count,
                    (U ik ⟨k + 1 + t.val, by omega⟩ + δ t) *
                      x ⟨k + 1 + t.val, by omega⟩ := by
              rw [hy_diag, hdiagterm]
              congr 1
              have hcount : (Fin.rev ik).val = count := by
                simp [Fin.rev, ik, count]
                omega
              apply Fintype.sum_equiv (finCongr hcount)
              intro t
              let tc : Fin count := finCongr hcount t
              let jl : Fin n := ⟨ik.val + 1 + t.val, by
                have hir : ik.val + 1 + (Fin.rev ik).val = n := by simp [Fin.rev]
                omega⟩
              let jr : Fin n := ⟨k + 1 + tc.val, by omega⟩
              have hj : jl = jr := by
                apply Fin.ext
                simp [jl, jr, ik, tc]
              have hgt : ik.val < jl.val := by
                dsimp only [jl]
                exact lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
              change (U ik jl + row jl) * y jl = (U ik jr + δ tc) * x jr
              dsimp only [row]
              rw [dif_pos hgt]
              have htidx :
                  (⟨jl.val - k - 1, by
                    simp [jl, ik, count] at t ⊢
                    omega⟩ : Fin count) = tc := by
                apply Fin.ext
                simp [jl, ik, tc]
                omega
              rw [htidx]
              calc
                (U ik jl + δ tc) * y jl = (U ik jr + δ tc) * y jr :=
                  congrArg (fun j => (U ik j + δ tc) * y j) hj
                _ = (U ik jr + δ tc) * x jr := by
                  exact congrArg (fun v => (U ik jr + δ tc) * v) (hy_after tc)
            _ = b ik := by
              change b ik = q * s +
                ∑ t : Fin count,
                  (U ik ⟨k + 1 + t.val, by omega⟩ + δ t) *
                    x ⟨k + 1 + t.val, by omega⟩ at hfold
              linarith [hfold]
        · simp only [if_neg hik]
          apply hyr i
          have hival : i.val ≠ ik.val := by
            intro hv
            apply hik
            exact Fin.ext hv
          simp [ik] at hival ⊢
          omega

private lemma p29_entryNorm_nonneg {m n : ℕ} (X : P29Matrix m n) :
    0 ≤ p29EntryNorm X := by
  unfold p29EntryNorm
  positivity

private lemma p29_entry_abs_le_norm {m n : ℕ} (X : P29Matrix m n)
    (i : Fin m) (j : Fin n) :
    |X i j| ≤ p29EntryNorm X := by
  unfold p29EntryNorm
  calc
    |X i j| ≤ ∑ j' : Fin n, |X i j'| := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j' : Fin n => |X i j'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin m, ∑ j' : Fin n, |X i' j'| := by
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun i' : Fin m => ∑ j' : Fin n, |X i' j'|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        (Finset.mem_univ i)

private lemma p29_entryNorm_add {m n : ℕ} (X Y : P29Matrix m n) :
    p29EntryNorm (X + Y) ≤ p29EntryNorm X + p29EntryNorm Y := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |(X + Y) i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, (|X i j| + |Y i j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact abs_add_le _ _
    _ = (∑ i : Fin m, ∑ j : Fin n, |X i j|) +
        ∑ i : Fin m, ∑ j : Fin n, |Y i j| := by
      simp_rw [Finset.sum_add_distrib]

private lemma p29_entryNorm_neg {m n : ℕ} (X : P29Matrix m n) :
    p29EntryNorm (-X) = p29EntryNorm X := by
  unfold p29EntryNorm
  simp

private lemma p29_entryNorm_sub {m n : ℕ} (X Y : P29Matrix m n) :
    p29EntryNorm (X - Y) ≤ p29EntryNorm X + p29EntryNorm Y := by
  simpa [sub_eq_add_neg, p29_entryNorm_neg] using p29_entryNorm_add X (-Y)

private lemma p29_entryNorm_of_componentwise {m n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (X Δ : P29Matrix m n)
    (h : ∀ i j, |Δ i j| ≤ c * |X i j|) :
    p29EntryNorm Δ ≤ c * p29EntryNorm X := by
  unfold p29EntryNorm
  calc
    (∑ i : Fin m, ∑ j : Fin n, |Δ i j|) ≤
        ∑ i : Fin m, ∑ j : Fin n, c * |X i j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact h i j
    _ = c * ∑ i : Fin m, ∑ j : Fin n, |X i j| := by
      simp_rw [← Finset.mul_sum]

private lemma p29_entryNorm_add_perturbation {m n : ℕ}
    (c : ℝ) (hc : 0 ≤ c) (X Δ : P29Matrix m n)
    (h : ∀ i j, |Δ i j| ≤ c * |X i j|) :
    p29EntryNorm (X + Δ) ≤ (1 + c) * p29EntryNorm X := by
  calc
    p29EntryNorm (X + Δ) ≤ p29EntryNorm X + p29EntryNorm Δ :=
      p29_entryNorm_add X Δ
    _ ≤ p29EntryNorm X + c * p29EntryNorm X := by
      gcongr
      exact p29_entryNorm_of_componentwise c hc X Δ h
    _ = (1 + c) * p29EntryNorm X := by ring

private lemma p29_entryNorm_matMul {m n p : ℕ}
    (X : P29Matrix m n) (Y : P29Matrix n p) :
    p29EntryNorm (p29MatMul X Y) ≤
      (m : ℝ) * (n : ℝ) * (p : ℝ) *
        (p29EntryNorm X * p29EntryNorm Y) := by
  unfold p29EntryNorm p29MatMul
  calc
    (∑ i : Fin m, ∑ j : Fin p, |∑ k : Fin n, X i k * Y k j|) ≤
        ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n, |X i k * Y k j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, ∑ j : Fin p, ∑ k : Fin n,
        (p29EntryNorm X * p29EntryNorm Y) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [abs_mul]
      exact mul_le_mul
        (p29_entry_abs_le_norm X i k) (p29_entry_abs_le_norm Y k j)
        (abs_nonneg _) (p29_entryNorm_nonneg X)
    _ = (m : ℝ) * (n : ℝ) * (p : ℝ) *
        (p29EntryNorm X * p29EntryNorm Y) := by
      simp [Fintype.card_fin]
      ring

private lemma p29_entryNorm_triple {n : ℕ}
    (X Y Z : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
      (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y * p29EntryNorm Z := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
        (n : ℝ) * (n : ℝ) * (n : ℝ) *
          (p29EntryNorm (p29MatMul X Y) * p29EntryNorm Z) :=
      p29_entryNorm_matMul _ _
    _ ≤ (n : ℝ) * (n : ℝ) * (n : ℝ) *
          (((n : ℝ) * (n : ℝ) * (n : ℝ) *
            (p29EntryNorm X * p29EntryNorm Y)) * p29EntryNorm Z) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_right
          (p29_entryNorm_matMul X Y) (p29_entryNorm_nonneg Z)
      · positivity
    _ = (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y *
          p29EntryNorm Z := by ring

private lemma p29_combined_expansion {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  change ((L + ΔL) * (D + ΔD)) * (p29Transpose L + ΔU) -
      (L * D) * p29Transpose L =
    (ΔL * (D + ΔD)) * (p29Transpose L + ΔU) +
      (L * ΔD) * (p29Transpose L + ΔU) + (L * D) * ΔU
  noncomm_ring

private lemma p29_entryNorm_triple_bound {n : ℕ}
    (X Y Z : P29Matrix n n) (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hX : p29EntryNorm X ≤ a) (hY : p29EntryNorm Y ≤ b)
    (hZ : p29EntryNorm Z ≤ c) :
    p29EntryNorm (p29MatMul (p29MatMul X Y) Z) ≤
      (n : ℝ) ^ 6 * a * b * c := by
  have hn6 : 0 ≤ (n : ℝ) ^ 6 := by positivity
  have h1 : (n : ℝ) ^ 6 * p29EntryNorm X ≤ (n : ℝ) ^ 6 * a :=
    mul_le_mul_of_nonneg_left hX hn6
  have h2 : (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y ≤
      (n : ℝ) ^ 6 * a * b :=
    mul_le_mul h1 hY (p29_entryNorm_nonneg Y) (mul_nonneg hn6 ha)
  have h3 : (n : ℝ) ^ 6 * p29EntryNorm X * p29EntryNorm Y *
      p29EntryNorm Z ≤ (n : ℝ) ^ 6 * a * b * c :=
    mul_le_mul h2 hZ (p29_entryNorm_nonneg Z)
      (mul_nonneg (mul_nonneg hn6 ha) hb)
  exact le_trans (p29_entryNorm_triple X Y Z) h3

private lemma p29_combined_bound {fp : P29FPModel} {n : ℕ}
    (eta : ℝ) (heta : 0 ≤ eta)
    (L D ΔL ΔD ΔU : P29Matrix n n)
    (hvalid : P29GammaValid fp.u n)
    (hL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let γ := p29Gamma fp.u n
  have hγ : 0 ≤ γ := p29_gamma_nonneg fp.u_nonneg hvalid
  have hnD : 0 ≤ p29EntryNorm D := p29_entryNorm_nonneg D
  have hD0 : 0 ≤ p29EntryNorm ΔD := p29_entryNorm_nonneg ΔD
  have hDadd : p29EntryNorm (D + ΔD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤ p29EntryNorm D + p29EntryNorm ΔD :=
        p29_entryNorm_add D ΔD
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D := by linarith
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hUadd : p29EntryNorm (p29Transpose L + ΔU) ≤
      (1 + γ) * p29EntryNorm (p29Transpose L) :=
    p29_entryNorm_add_perturbation γ hγ _ _ hU
  have hLn : p29EntryNorm ΔL ≤ γ * p29EntryNorm L :=
    p29_entryNorm_of_componentwise γ hγ _ _ hL
  have hUn : p29EntryNorm ΔU ≤ γ * p29EntryNorm (p29Transpose L) :=
    p29_entryNorm_of_componentwise γ hγ _ _ hU
  rw [p29_combined_expansion]
  calc
    p29EntryNorm
        (p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
          p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
          p29MatMul (p29MatMul L D) ΔU) ≤
        p29EntryNorm (p29MatMul (p29MatMul ΔL (D + ΔD))
          (p29Transpose L + ΔU)) +
        p29EntryNorm (p29MatMul (p29MatMul L ΔD)
          (p29Transpose L + ΔU)) +
        p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) := by
      calc
        p29EntryNorm
            ((p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
              p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)) +
              p29MatMul (p29MatMul L D) ΔU) ≤
            p29EntryNorm
              (p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
                p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU)) +
              p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) :=
          p29_entryNorm_add _ _
        _ ≤ (p29EntryNorm
                (p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU)) +
              p29EntryNorm
                (p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU))) +
              p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) := by
          gcongr
          exact p29_entryNorm_add _ _
    _ ≤ (n : ℝ) ^ 6 * (γ * p29EntryNorm L) *
          ((1 + eta) * p29EntryNorm D) *
          ((1 + γ) * p29EntryNorm (p29Transpose L)) +
        (n : ℝ) ^ 6 * p29EntryNorm L *
          (eta * p29EntryNorm D) *
          ((1 + γ) * p29EntryNorm (p29Transpose L)) +
        (n : ℝ) ^ 6 * p29EntryNorm L * p29EntryNorm D *
          (γ * p29EntryNorm (p29Transpose L)) := by
      apply add_le_add
      · apply add_le_add
        · exact p29_entryNorm_triple_bound _ _ _ _ _ _
            (mul_nonneg hγ (p29_entryNorm_nonneg L))
            (mul_nonneg (by linarith) hnD)
            (mul_nonneg (by linarith) (p29_entryNorm_nonneg (p29Transpose L)))
            hLn hDadd hUadd
        · exact p29_entryNorm_triple_bound _ _ _ _ _ _
            (p29_entryNorm_nonneg L)
            (mul_nonneg heta hnD)
            (mul_nonneg (by linarith) (p29_entryNorm_nonneg (p29Transpose L)))
            (le_refl _) hD hUadd
      · exact p29_entryNorm_triple_bound _ _ _ _ _ _
          (p29_entryNorm_nonneg L) hnD
          (mul_nonneg hγ (p29_entryNorm_nonneg (p29Transpose L)))
          (le_refl _) (le_refl _) hUn
    _ = p29SolveBackwardFactor fp n eta L D := by
      unfold p29SolveBackwardFactor γ
      ring

private lemma p29_matMul_vec_assoc {m n p : ℕ}
    (X : P29Matrix m n) (Y : P29Matrix n p) (v : Fin p → ℝ)
    (i : Fin m) :
    (∑ j : Fin p, p29MatMul X Y i j * v j) =
      ∑ k : Fin n, X i k * (∑ j : Fin p, Y k j * v j) := by
  unfold p29MatMul
  calc
    (∑ j : Fin p, (∑ k : Fin n, X i k * Y k j) * v j) =
        ∑ j : Fin p, ∑ k : Fin n, (X i k * Y k j) * v j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ k : Fin n, ∑ j : Fin p, (X i k * Y k j) * v j :=
      Finset.sum_comm
    _ = ∑ k : Fin n, X i k * (∑ j : Fin p, Y k j * v j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

private lemma p29_perturbed_solve {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) (b y z x : Fin n → ℝ)
    (hL : ∀ i, ∑ j : Fin n, (L i j + ΔL i j) * y j = b i)
    (hD : ∀ i, ∑ j : Fin n, (D i j + ΔD i j) * z j = y i)
    (hU : ∀ i, ∑ j : Fin n,
      (p29Transpose L i j + ΔU i j) * x j = z i) :
    ∀ i, ∑ j : Fin n,
      p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j = b i := by
  intro i
  rw [show p29PerturbedLDLT L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul (L + ΔL) (D + ΔD))
        (p29Transpose L + ΔU) by rfl]
  rw [p29_matMul_vec_assoc]
  simp only [Matrix.add_apply]
  simp_rw [hU]
  rw [p29_matMul_vec_assoc]
  simp only [Matrix.add_apply]
  simp_rw [hD]
  exact hL i

private lemma p29_total_error_identity {n : ℕ}
    (A L D E0 ΔL ΔD ΔU : P29Matrix n n)
    (hfactor : p29LDLT L D = A + E0) :
    A + p29TotalBackwardError E0 L D ΔL ΔD ΔU =
      p29PerturbedLDLT L D ΔL ΔD ΔU := by
  ext i j
  have hf := congrArg (fun M : P29Matrix n n => M i j) hfactor
  simp only [Matrix.add_apply] at hf ⊢
  unfold p29TotalBackwardError p29CombinedBackwardError
  simp only [Matrix.add_apply, Matrix.sub_apply]
  linarith

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
  have hdiagT : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have hupperT : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔL, hΔL, hforward⟩ :=
    p29_forward_steps_backward fp n L b hdiag hlower hvalid n (le_refl n)
      (fun _ => 0)
  have hforward' : ∀ i, ∑ j : Fin n,
      (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
    intro i
    simpa [p29ForwardSub] using hforward i (by omega)
  obtain ⟨ΔD, hΔD, hblock⟩ := hDsolve
  obtain ⟨ΔU, hΔU, hback⟩ :=
    p29_back_steps_backward fp n (p29Transpose L) z hdiagT hupperT
      hvalid n (le_refl n) (fun _ => 0)
  have hback' : ∀ i, ∑ j : Fin n,
      (p29Transpose L i j + ΔU i j) *
        p29BackSub fp n (p29Transpose L) z j = z i := by
    intro i
    simpa [p29BackSub] using hback i i.isLt
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · have hpert := p29_perturbed_solve L D ΔL ΔD ΔU b
      (p29ForwardSub fp n L b) z
      (p29BackSub fp n (p29Transpose L) z)
      hforward' hblock hback'
    have hid := p29_total_error_identity A L D E0 ΔL ΔD ΔU hfactor
    intro i
    calc
      (∑ j : Fin n, (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j) =
          ∑ j : Fin n,
            p29PerturbedLDLT L D ΔL ΔD ΔU i j *
              p29BackSub fp n (p29Transpose L) z j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hij := congrArg (fun M : P29Matrix n n => M i j) hid
        simpa [F] using congrArg
          (fun r : ℝ => r * p29BackSub fp n (p29Transpose L) z j) hij
      _ = b i := hpert i
  · have hcombined := p29_combined_bound (fp := fp) eta heta L D ΔL ΔD ΔU
      hvalid hΔL hΔD hΔU
    calc
      p29EntryNorm F ≤ p29EntryNorm E0 +
          p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) := by
        dsimp only [F]
        unfold p29TotalBackwardError
        exact p29_entryNorm_add _ _
      _ ≤ factorEta * p29EntryNorm A +
          p29SolveBackwardFactor fp n eta L D :=
        add_le_add hE0 hcombined
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
