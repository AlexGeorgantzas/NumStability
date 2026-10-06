import HighamBench.P29Definitions

namespace HighamBench

open scoped BigOperators

private lemma p29_gamma_den_pos {u : ℝ} {n : ℕ}
    (h : (n : ℝ) * u < 1) : 0 < 1 - (n : ℝ) * u := by
  linarith

private lemma p29_gamma_nonneg {u : ℝ} {n N : ℕ}
    (hu : 0 ≤ u) (hn : n ≤ N) (hN : (N : ℝ) * u < 1) :
    0 ≤ p29Gamma u n := by
  rw [p29Gamma]
  have hn' : (n : ℝ) * u ≤ (N : ℝ) * u := by
    gcongr
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p29_gamma_mono {u : ℝ} {n N : ℕ}
    (hu : 0 ≤ u) (hn : n ≤ N) (hN : (N : ℝ) * u < 1) :
    p29Gamma u n ≤ p29Gamma u N := by
  rw [p29Gamma, p29Gamma]
  have hn' : (n : ℝ) * u ≤ (N : ℝ) * u := by
    gcongr
  have hd1 : 0 < 1 - (n : ℝ) * u := by linarith
  have hd2 : 0 < 1 - (N : ℝ) * u := by linarith
  apply (div_le_div_iff₀ hd1 hd2).2
  nlinarith

private lemma p29_gamma_mul_step {u e d : ℝ} {k N : ℕ}
    (hu : 0 ≤ u) (hk : k + 1 ≤ N) (hN : (N : ℝ) * u < 1)
    (he : |e| ≤ p29Gamma u k) (hd : |d| ≤ u) :
    |(1 + e) * (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hkN : k ≤ N := by omega
  have hknN : k + 1 ≤ N := hk
  have hkvalid : (k : ℝ) * u < 1 := by
    have : (k : ℝ) * u ≤ (N : ℝ) * u := by gcongr
    linarith
  have hksvalid : ((k + 1 : ℕ) : ℝ) * u < 1 := by
    have : ((k + 1 : ℕ) : ℝ) * u ≤ (N : ℝ) * u := by gcongr
    linarith
  have hg : 0 ≤ p29Gamma u k := p29_gamma_nonneg hu hkN hN
  calc
    |(1 + e) * (1 + d) - 1| = |e + d + e * d| := by ring_nf
    _ ≤ |e| + |d| + |e| * |d| := by
      calc
        |e + d + e * d| ≤ |e| + |d| + |e * d| := by
          simpa [add_assoc] using abs_add_three e d (e * d)
        _ = |e| + |d| + |e| * |d| := by rw [abs_mul]
    _ ≤ p29Gamma u k + u + p29Gamma u k * u := by gcongr
    _ ≤ p29Gamma u (k + 1) := by
      rw [p29Gamma, p29Gamma]
      push_cast
      have hd0 : 0 < 1 - (k : ℝ) * u := by linarith
      have hd1 : 0 < 1 - ((k : ℝ) + 1) * u := by
        norm_num at hksvalid ⊢
        exact hksvalid
      have heq :
          (k : ℝ) * u / (1 - (k : ℝ) * u) + u +
              (k : ℝ) * u / (1 - (k : ℝ) * u) * u =
            (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
        field_simp [ne_of_gt hd0]
        ring
      rw [heq]
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hd1
      · linarith

private lemma p29_gamma_div_step {u e d : ℝ} {k N : ℕ}
    (hu : 0 ≤ u) (hk : k + 1 ≤ N) (hN : (N : ℝ) * u < 1)
    (he : |e| ≤ p29Gamma u k) (hd : |d| ≤ u) :
    |(1 + e) / (1 + d) - 1| ≤ p29Gamma u (k + 1) := by
  have hkN : k ≤ N := by omega
  have hu_lt_one : u < 1 := by
    have hN1 : (1 : ℕ) ≤ N := le_trans (by omega) hk
    have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
    nlinarith [mul_le_mul_of_nonneg_right hN1' hu]
  have hden : 0 < 1 + d := by
    have := (abs_le.mp hd).1
    linarith
  have hkvalid : (k : ℝ) * u < 1 := by
    have : (k : ℝ) * u ≤ (N : ℝ) * u := by gcongr
    linarith
  have hksvalid : ((k + 1 : ℕ) : ℝ) * u < 1 := by
    have : ((k + 1 : ℕ) : ℝ) * u ≤ (N : ℝ) * u := by gcongr
    linarith
  calc
    |(1 + e) / (1 + d) - 1| = |e - d| / |1 + d| := by
      rw [div_sub_one (ne_of_gt hden), abs_div]
      ring_nf
    _ ≤ (p29Gamma u k + u) / (1 - u) := by
      apply div_le_div₀
      · exact add_nonneg (p29_gamma_nonneg hu hkN hN) hu
      · exact (abs_sub e d).trans (add_le_add he hd)
      · linarith
      · rw [abs_of_pos hden]
        have := (abs_le.mp hd).1
        linarith
    _ ≤ p29Gamma u (k + 1) := by
      rw [p29Gamma, p29Gamma]
      push_cast
      have hd0 : 0 < 1 - (k : ℝ) * u := by linarith
      have hdu : 0 < 1 - u := by linarith
      have hd1 : 0 < 1 - ((k : ℝ) + 1) * u := by
        norm_num at hksvalid ⊢
        exact hksvalid
      rw [div_le_div_iff₀ hdu hd1]
      field_simp [ne_of_gt hd0]
      have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
      nlinarith [mul_nonneg hku hu]

private lemma p29_rounded_sub_fold_backward
    (fp : P29FPModel) {N : ℕ} (hvalid : P29GammaValid fp.u N) :
    ∀ (k : ℕ), k ≤ N → ∀ (a x : Fin k → ℝ) (b : ℝ),
      ∃ e0 : ℝ, ∃ e : Fin k → ℝ,
        |e0| ≤ p29Gamma fp.u k ∧
        (∀ t, |e t| ≤ p29Gamma fp.u k) ∧
        b = (1 + e0) *
              Fin.foldl k
                (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (x t))) b +
            ∑ t : Fin k, (1 + e t) * (a t * x t) := by
  intro k hk
  induction k with
  | zero =>
      intro a x b
      refine ⟨0, fun t => Fin.elim0 t, ?_, ?_, ?_⟩
      · simp [p29Gamma]
      · intro t
        exact Fin.elim0 t
      · simp
  | succ k ih =>
      intro a x b
      have hk0 : k ≤ N := by omega
      obtain ⟨e0, e, he0, he, heq⟩ :=
        ih hk0 (fun t => a t.castSucc) (fun t => x t.castSucc) b
      let sprev := Fin.foldl k
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (a t.castSucc) (x t.castSucc))) b
      obtain ⟨mu, hmu, hmul⟩ := fp.model_mul (a (Fin.last k)) (x (Fin.last k))
      obtain ⟨sigma, hsigma, hsub⟩ :=
        fp.model_sub sprev (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))
      let enew0 := (1 + e0) / (1 + sigma) - 1
      let elast := (1 + e0) * (1 + mu) - 1
      let enew : Fin (k + 1) → ℝ := Fin.lastCases elast e
      refine ⟨enew0, enew, ?_, ?_, ?_⟩
      · exact p29_gamma_div_step fp.u_nonneg hk hvalid he0 hsigma
      · intro t
        refine Fin.lastCases ?_ (fun i => ?_) t
        · simpa only [enew, Fin.lastCases_last] using
            (p29_gamma_mul_step fp.u_nonneg hk hvalid he0 hmu)
        · have henew : enew i.castSucc = e i := by
            simp only [enew, Fin.lastCases_castSucc]
          have hksvalid : ((k + 1 : ℕ) : ℝ) * fp.u < 1 := by
            have hle : ((k + 1 : ℕ) : ℝ) * fp.u ≤ (N : ℝ) * fp.u := by
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk) fp.u_nonneg
            exact lt_of_le_of_lt hle hvalid
          rw [henew]
          exact (he i).trans
            (p29_gamma_mono (N := k + 1) fp.u_nonneg (by omega) hksvalid)
      · have hu_lt_one : fp.u < 1 := by
          have hN1 : (1 : ℕ) ≤ N := le_trans (by omega) hk
          have hN1' : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
          dsimp [P29GammaValid] at hvalid
          nlinarith [mul_le_mul_of_nonneg_right hN1' fp.u_nonneg]
        have hspos : 0 < 1 + sigma := by
          have := (abs_le.mp hsigma).1
          linarith
        have hstep :
            sprev =
              (fp.fl_sub sprev
                  (fp.fl_mul (a (Fin.last k)) (x (Fin.last k)))) /
                  (1 + sigma) +
                (a (Fin.last k) * x (Fin.last k)) * (1 + mu) := by
          rw [hsub, hmul]
          field_simp [ne_of_gt hspos]
          ring
        rw [Fin.foldl_succ_last]
        change b = (1 + enew0) *
              fp.fl_sub sprev
                (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) +
            ∑ t : Fin (k + 1), (1 + enew t) * (a t * x t)
        rw [Fin.sum_univ_castSucc]
        simp only [enew, Fin.lastCases_castSucc, Fin.lastCases_last]
        calc
          b = (1 + e0) * sprev +
                ∑ t : Fin k, (1 + e t) *
                  (a t.castSucc * x t.castSucc) := by
              simpa [sprev] using heq
          _ = (1 + e0) *
                  (fp.fl_sub sprev
                      (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) /
                      (1 + sigma) +
                    (a (Fin.last k) * x (Fin.last k)) * (1 + mu)) +
                ∑ t : Fin k, (1 + e t) *
                  (a t.castSucc * x t.castSucc) := by
              exact congrArg
                (fun q => (1 + e0) * q +
                  ∑ t : Fin k, (1 + e t) *
                    (a t.castSucc * x t.castSucc)) hstep
          _ = (1 + enew0) *
                  fp.fl_sub sprev
                    (fp.fl_mul (a (Fin.last k)) (x (Fin.last k))) +
                ((∑ t : Fin k, (1 + e t) *
                    (a t.castSucc * x t.castSucc)) +
                  (1 + elast) *
                    (a (Fin.last k) * x (Fin.last k))) := by
              dsimp [enew0, elast]
              field_simp [ne_of_gt hspos]
              ring

private lemma p29_forward_steps_spec (fp : P29FPModel) (n : ℕ)
    (L : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let out := p29ForwardSubSteps fp n L b k hk x
      (∀ i : Fin n, i.val < n - k → out i = x i) ∧
      (∀ i : Fin n, n - k ≤ i.val →
        out i = fp.fl_div
          (Fin.foldl i.val
            (fun acc (t : Fin i.val) =>
              fp.fl_sub acc
                (fp.fl_mul (L i ⟨t.val, by omega⟩)
                  (out ⟨t.val, by omega⟩)))
            (b i))
          (L i i)) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro i hi
        rfl
      · intro i hi
        omega
  | succ k ih =>
      intro hk x
      have hlt : n - k - 1 < n := by omega
      let ik : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have ih' := ih (Nat.le_of_succ_le hk) x'
      change
        (∀ i : Fin n, i.val < n - (k + 1) →
            p29ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' i = x i) ∧
        (∀ i : Fin n, n - (k + 1) ≤ i.val →
          p29ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x' i =
            fp.fl_div
              (Fin.foldl i.val
                (fun acc (t : Fin i.val) =>
                  fp.fl_sub acc
                    (fp.fl_mul (L i ⟨t.val, by omega⟩)
                      (p29ForwardSubSteps fp n L b k
                        (Nat.le_of_succ_le hk) x' ⟨t.val, by omega⟩)))
                (b i))
              (L i i))
      constructor
      · intro i hi
        rw [ih'.1 i (by omega)]
        have hne : i ≠ ik := by
          intro heq
          have hv := congrArg Fin.val heq
          dsimp [ik] at hv
          omega
        exact Function.update_of_ne hne (fp.fl_div s (L ik ik)) x
      · intro i hi
        by_cases hbig : n - k ≤ i.val
        · exact ih'.2 i hbig
        · have hival : i.val = n - k - 1 := by omega
          have hieq : i = ik := by
            apply Fin.ext
            simpa [ik] using hival
          subst i
          rw [ih'.1 ik (by simp [ik]; omega)]
          simp only [x', Function.update_self]
          congr 1
          dsimp [s, count]
          dsimp [ik]
          congr 1
          funext acc t
          congr 2
          have ht0 := t.isLt
          change t.val < n - k - 1 at ht0
          have htn : t.val < n := by omega
          let jt : Fin n := ⟨t.val, htn⟩
          have hout := ih'.1 jt (by dsimp [jt]; omega)
          have hne : jt ≠ ik := by
            intro heq
            have hv := congrArg Fin.val heq
            dsimp [jt, ik] at hv
            omega
          have hx' : x' jt = x jt :=
            Function.update_of_ne hne (fp.fl_div s (L ik ik)) x
          have hvalue := hout.trans hx'
          simpa only [jt] using hvalue.symm

private lemma p29_back_steps_spec (fp : P29FPModel) (n : ℕ)
    (U : P29Matrix n n) (b : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let out := p29BackSubSteps fp n U b k hk x
      (∀ i : Fin n, k ≤ i.val → out i = x i) ∧
      (∀ i : Fin n, i.val < k →
        out i = fp.fl_div
          (Fin.foldl (n - i.val - 1)
            (fun acc (t : Fin (n - i.val - 1)) =>
              fp.fl_sub acc
                (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                  (out ⟨i.val + 1 + t.val, by omega⟩)))
            (b i))
          (U i i)) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro i hi
        rfl
      · intro i hi
        omega
  | succ k ih =>
      intro hk x
      have hlt : k < n := hk
      let ik : Fin n := ⟨k, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (U ik ⟨k + 1 + t.val, by omega⟩)
              (x ⟨k + 1 + t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (U ik ik))
      have ih' := ih (Nat.le_of_succ_le hk) x'
      change
        (∀ i : Fin n, k + 1 ≤ i.val →
            p29BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' i = x i) ∧
        (∀ i : Fin n, i.val < k + 1 →
          p29BackSubSteps fp n U b k (Nat.le_of_succ_le hk) x' i =
            fp.fl_div
              (Fin.foldl (n - i.val - 1)
                (fun acc (t : Fin (n - i.val - 1)) =>
                  fp.fl_sub acc
                    (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
                      (p29BackSubSteps fp n U b k
                        (Nat.le_of_succ_le hk) x'
                        ⟨i.val + 1 + t.val, by omega⟩)))
                (b i))
              (U i i))
      constructor
      · intro i hi
        rw [ih'.1 i (by omega)]
        have hne : i ≠ ik := by
          intro heq
          have hv := congrArg Fin.val heq
          dsimp [ik] at hv
          omega
        exact Function.update_of_ne hne (fp.fl_div s (U ik ik)) x
      · intro i hi
        by_cases hsmall : i.val < k
        · exact ih'.2 i hsmall
        · have hival : i.val = k := by omega
          have hieq : i = ik := by
            apply Fin.ext
            simpa [ik] using hival
          subst i
          rw [ih'.1 ik (by simp [ik])]
          simp only [x', Function.update_self]
          congr 1
          dsimp [s, count, ik]
          congr 1
          funext acc t
          congr 2
          have ht0 := t.isLt
          change t.val < n - k - 1 at ht0
          have htn : k + 1 + t.val < n := by omega
          let jt : Fin n := ⟨k + 1 + t.val, htn⟩
          have hout := ih'.1 jt (by dsimp [jt]; omega)
          have hne : jt ≠ ik := by
            intro heq
            have hv := congrArg Fin.val heq
            dsimp [jt, ik] at hv
            omega
          have hx' : x' jt = x jt :=
            Function.update_of_ne hne (fp.fl_div s (U ik ik)) x
          have hvalue := hout.trans hx'
          simpa only [jt] using hvalue.symm

private lemma p29_sum_below_add_diag {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hz : ∀ j : Fin n, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  classical
  let g : ℕ → ℝ := fun j => if h : j < n then f ⟨j, h⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := by
    simpa [g] using (Finset.sum_fin_eq_sum_range f)
  have hbelow :
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) =
        ∑ j ∈ Finset.range i.val, g j := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < i.val := Finset.mem_range.mp hj
    simp [g, hjlt, lt_trans hjlt i.isLt]
  have hshort :
      (∑ j ∈ Finset.range (i.val + 1), g j) =
        ∑ j ∈ Finset.range n, g j := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro j hjn hji
    have hjlt : j < n := Finset.mem_range.mp hjn
    have hjge : i.val + 1 ≤ j := by
      simpa [Finset.mem_range] using hji
    rw [show g j = f ⟨j, hjlt⟩ by simp [g, hjlt]]
    exact hz ⟨j, hjlt⟩ (Nat.lt_of_succ_le hjge)
  rw [hall, hbelow]
  calc
    (∑ j ∈ Finset.range n, g j) =
        ∑ j ∈ Finset.range (i.val + 1), g j := hshort.symm
    _ = (∑ j ∈ Finset.range i.val, g j) + g i.val :=
      Finset.sum_range_succ g i.val
    _ = (∑ j ∈ Finset.range i.val, g j) + f i := by
      simp [g, i.isLt]

private lemma p29_sum_diag_add_above {n : ℕ} (f : Fin n → ℝ) (i : Fin n)
    (hz : ∀ j : Fin n, j.val < i.val → f j = 0) :
    (∑ j : Fin n, f j) = f i +
      ∑ t : Fin (n - i.val - 1), f ⟨i.val + 1 + t.val, by omega⟩ := by
  classical
  let g : ℕ → ℝ := fun j => if h : j < n then f ⟨j, h⟩ else 0
  have hall : (∑ j : Fin n, f j) = ∑ j ∈ Finset.range n, g j := by
    simpa [g] using (Finset.sum_fin_eq_sum_range f)
  have hn : i.val + 1 + (n - i.val - 1) = n := by omega
  have hprefix : (∑ j ∈ Finset.range (i.val + 1), g j) = f i := by
    rw [Finset.sum_range_succ]
    have hzsum : (∑ j ∈ Finset.range i.val, g j) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : j < i.val := Finset.mem_range.mp hj
      have hjn : j < n := lt_trans hjlt i.isLt
      rw [show g j = f ⟨j, hjn⟩ by simp [g, hjn]]
      exact hz ⟨j, hjn⟩ hjlt
    rw [hzsum, zero_add]
    simp [g, i.isLt]
  have habove :
      (∑ t : Fin (n - i.val - 1),
          f ⟨i.val + 1 + t.val, by omega⟩) =
        ∑ t ∈ Finset.range (n - i.val - 1), g (i.val + 1 + t) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro t ht
    have htlt : t < n - i.val - 1 := Finset.mem_range.mp ht
    have htn : i.val + 1 + t < n := by omega
    simp [g, htlt, htn]
  rw [hall]
  calc
    (∑ j ∈ Finset.range n, g j) =
        ∑ j ∈ Finset.range (i.val + 1 + (n - i.val - 1)), g j := by
          rw [hn]
    _ = (∑ j ∈ Finset.range (i.val + 1), g j) +
          ∑ t ∈ Finset.range (n - i.val - 1), g (i.val + 1 + t) := by
          rw [Finset.sum_range_add]
    _ = f i + ∑ t : Fin (n - i.val - 1),
          f ⟨i.val + 1 + t.val, by omega⟩ := by
          rw [hprefix, habove]

private lemma p29_forward_backward_stable
    (fp : P29FPModel) (n : ℕ) (L : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔL : P29Matrix n n,
      (∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + ΔL i j) * p29ForwardSub fp n L b j = b i := by
  classical
  let y := p29ForwardSub fp n L b
  have hrow : ∀ i : Fin n, ∃ drow : Fin n → ℝ,
      (∀ j, |drow j| ≤ p29Gamma fp.u n * |L i j|) ∧
      (∑ j : Fin n, (L i j + drow j) * y j) = b i := by
    intro i
    let s := Fin.foldl i.val
      (fun acc (t : Fin i.val) =>
        fp.fl_sub acc
          (fp.fl_mul (L i ⟨t.val, by omega⟩)
            (y ⟨t.val, by omega⟩)))
      (b i)
    have hy : y i = fp.fl_div s (L i i) := by
      have hs := (p29_forward_steps_spec fp n L b n (le_refl n)
        (fun _ => 0)).2 i (by simp)
      simpa [y, p29ForwardSub, s] using hs
    obtain ⟨e0, e, he0, he, heq⟩ :=
      p29_rounded_sub_fold_backward fp hvalid i.val i.isLt.le
        (fun t => L i ⟨t.val, by omega⟩)
        (fun t => y ⟨t.val, by omega⟩) (b i)
    change b i = (1 + e0) * s +
      ∑ t : Fin i.val, (1 + e t) *
        (L i ⟨t.val, by omega⟩ * y ⟨t.val, by omega⟩) at heq
    obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div s (L i i) (hdiag i)
    let ediag := (1 + e0) / (1 + delta) - 1
    have hediag : |ediag| ≤ p29Gamma fp.u (i.val + 1) :=
      p29_gamma_div_step fp.u_nonneg (by omega) hvalid he0 hdelta
    have hu_lt_one : fp.u < 1 := by
      have hn1 : (1 : ℕ) ≤ n :=
        le_trans (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt i.isLt)
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      dsimp [P29GammaValid] at hvalid
      nlinarith [mul_le_mul_of_nonneg_right hn1' fp.u_nonneg]
    have hdpos : 0 < 1 + delta := by
      have := (abs_le.mp hdelta).1
      linarith
    have hdiagterm :
        (1 + ediag) * (L i i * y i) = (1 + e0) * s := by
      rw [hy, hdiv]
      dsimp [ediag]
      field_simp [hdiag i, ne_of_gt hdpos]
      ring
    let drow : Fin n → ℝ := fun j =>
      if hj : j.val < i.val then e ⟨j.val, hj⟩ * L i j
      else if j = i then ediag * L i j else 0
    refine ⟨drow, ?_, ?_⟩
    · intro j
      by_cases hj : j.val < i.val
      · simp only [drow, hj, ↓reduceDIte, abs_mul]
        calc
          |e ⟨j.val, hj⟩| * |L i j| ≤
              p29Gamma fp.u i.val * |L i j| := by
                exact mul_le_mul_of_nonneg_right (he _) (abs_nonneg _)
          _ ≤ p29Gamma fp.u n * |L i j| := by
            gcongr
            exact p29_gamma_mono fp.u_nonneg i.isLt.le hvalid
      · by_cases hji : j = i
        · subst j
          simp only [drow, lt_self_iff_false, ↓reduceDIte, ite_true, abs_mul]
          calc
            |ediag| * |L i i| ≤
                p29Gamma fp.u (i.val + 1) * |L i i| := by gcongr
            _ ≤ p29Gamma fp.u n * |L i i| := by
              gcongr
              exact p29_gamma_mono fp.u_nonneg (by omega) hvalid
        · simp only [drow, hj, ↓reduceDIte, hji, ite_false, abs_zero]
          exact mul_nonneg (p29_gamma_nonneg fp.u_nonneg (le_refl n) hvalid)
            (abs_nonneg _)
    · have habove : ∀ j : Fin n, i.val < j.val →
          (L i j + drow j) * y j = 0 := by
        intro j hij
        have hji : j ≠ i := by
          intro h
          subst j
          omega
        simp [drow, show ¬j.val < i.val by omega, hji, hlower i j hij]
      rw [p29_sum_below_add_diag
        (fun j => (L i j + drow j) * y j) i habove]
      have hbelow :
          (∑ t : Fin i.val,
              (L i ⟨t.val, by omega⟩ + drow ⟨t.val, by omega⟩) *
                y ⟨t.val, by omega⟩) =
            ∑ t : Fin i.val, (1 + e t) *
              (L i ⟨t.val, by omega⟩ * y ⟨t.val, by omega⟩) := by
        apply Finset.sum_congr rfl
        intro t ht
        simp only [drow, t.isLt, ↓reduceDIte]
        ring
      rw [hbelow]
      have hdiageq : (L i i + drow i) * y i = (1 + ediag) * (L i i * y i) := by
        simp only [drow, lt_self_iff_false, ↓reduceDIte, ite_true]
        ring
      rw [hdiageq, hdiagterm, heq]
      ring
  choose rows hrows_bound hrows_eq using hrow
  refine ⟨fun i j => rows i j, hrows_bound, ?_⟩
  intro i
  exact hrows_eq i

private lemma p29_back_backward_stable
    (fp : P29FPModel) (n : ℕ) (U : P29Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, U i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hvalid : P29GammaValid fp.u n) :
    ∃ ΔU : P29Matrix n n,
      (∀ i j, |ΔU i j| ≤ p29Gamma fp.u n * |U i j|) ∧
      ∀ i, ∑ j : Fin n,
        (U i j + ΔU i j) * p29BackSub fp n U b j = b i := by
  classical
  let x := p29BackSub fp n U b
  have hrow : ∀ i : Fin n, ∃ drow : Fin n → ℝ,
      (∀ j, |drow j| ≤ p29Gamma fp.u n * |U i j|) ∧
      (∑ j : Fin n, (U i j + drow j) * x j) = b i := by
    intro i
    let count := n - i.val - 1
    let s := Fin.foldl count
      (fun acc (t : Fin count) =>
        fp.fl_sub acc
          (fp.fl_mul (U i ⟨i.val + 1 + t.val, by omega⟩)
            (x ⟨i.val + 1 + t.val, by omega⟩)))
      (b i)
    have hx : x i = fp.fl_div s (U i i) := by
      have hs := (p29_back_steps_spec fp n U b n (le_refl n)
        (fun _ => 0)).2 i i.isLt
      simpa [x, p29BackSub, s, count] using hs
    obtain ⟨e0, e, he0, he, heq⟩ :=
      p29_rounded_sub_fold_backward fp hvalid count (by
        dsimp [count]
        omega)
        (fun t => U i ⟨i.val + 1 + t.val, by omega⟩)
        (fun t => x ⟨i.val + 1 + t.val, by omega⟩) (b i)
    change b i = (1 + e0) * s +
      ∑ t : Fin count, (1 + e t) *
        (U i ⟨i.val + 1 + t.val, by omega⟩ *
          x ⟨i.val + 1 + t.val, by omega⟩) at heq
    obtain ⟨delta, hdelta, hdiv⟩ := fp.model_div s (U i i) (hdiag i)
    let ediag := (1 + e0) / (1 + delta) - 1
    have hcount : count + 1 ≤ n := by
      dsimp [count]
      omega
    have hediag : |ediag| ≤ p29Gamma fp.u (count + 1) :=
      p29_gamma_div_step fp.u_nonneg hcount hvalid he0 hdelta
    have hu_lt_one : fp.u < 1 := by
      have hn1 : (1 : ℕ) ≤ n :=
        le_trans (Nat.succ_le_succ (Nat.zero_le _)) (Nat.succ_le_of_lt i.isLt)
      have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      dsimp [P29GammaValid] at hvalid
      nlinarith [mul_le_mul_of_nonneg_right hn1' fp.u_nonneg]
    have hdpos : 0 < 1 + delta := by
      have := (abs_le.mp hdelta).1
      linarith
    have hdiagterm :
        (1 + ediag) * (U i i * x i) = (1 + e0) * s := by
      rw [hx, hdiv]
      dsimp [ediag]
      field_simp [hdiag i, ne_of_gt hdpos]
      ring
    let drow : Fin n → ℝ := fun j =>
      if hj : i.val < j.val then
        e ⟨j.val - i.val - 1, by dsimp [count]; omega⟩ * U i j
      else if j = i then ediag * U i j else 0
    refine ⟨drow, ?_, ?_⟩
    · intro j
      by_cases hj : i.val < j.val
      · simp only [drow, hj, ↓reduceDIte, abs_mul]
        calc
          |e ⟨j.val - i.val - 1, by dsimp [count]; omega⟩| * |U i j| ≤
              p29Gamma fp.u count * |U i j| := by
                exact mul_le_mul_of_nonneg_right (he _) (abs_nonneg _)
          _ ≤ p29Gamma fp.u n * |U i j| := by
            gcongr
            exact p29_gamma_mono fp.u_nonneg (by dsimp [count]; omega) hvalid
      · by_cases hji : j = i
        · subst j
          simp only [drow, lt_self_iff_false, ↓reduceDIte, ite_true, abs_mul]
          calc
            |ediag| * |U i i| ≤
                p29Gamma fp.u (count + 1) * |U i i| := by gcongr
            _ ≤ p29Gamma fp.u n * |U i i| := by
              gcongr
              exact p29_gamma_mono fp.u_nonneg hcount hvalid
        · simp only [drow, hj, ↓reduceDIte, hji, ite_false, abs_zero]
          exact mul_nonneg (p29_gamma_nonneg fp.u_nonneg (le_refl n) hvalid)
            (abs_nonneg _)
    · have hbelow : ∀ j : Fin n, j.val < i.val →
          (U i j + drow j) * x j = 0 := by
        intro j hij
        have hji : j ≠ i := by
          intro h
          subst j
          omega
        simp [drow, hji, hupper i j hij]
      rw [p29_sum_diag_add_above
        (fun j => (U i j + drow j) * x j) i hbelow]
      have habove :
          (∑ t : Fin count,
              (U i ⟨i.val + 1 + t.val, by omega⟩ +
                  drow ⟨i.val + 1 + t.val, by omega⟩) *
                x ⟨i.val + 1 + t.val, by omega⟩) =
            ∑ t : Fin count, (1 + e t) *
              (U i ⟨i.val + 1 + t.val, by omega⟩ *
                x ⟨i.val + 1 + t.val, by omega⟩) := by
        apply Finset.sum_congr rfl
        intro t ht
        have hidx : i.val + 1 + t.val - i.val - 1 = t.val := by omega
        simp only [drow, show i.val < i.val + 1 + t.val by omega,
          ↓reduceDIte]
        have heidx :
            (⟨i.val + 1 + t.val - i.val - 1,
                by dsimp [count]; omega⟩ : Fin count) = t := by
          apply Fin.ext
          exact hidx
        rw [heidx]
        ring
      have hdiageq : (U i i + drow i) * x i = (1 + ediag) * (U i i * x i) := by
        simp only [drow, lt_self_iff_false, ↓reduceDIte, ite_true]
        ring
      rw [hdiageq, hdiagterm, habove, heq]
  choose rows hrows_bound hrows_eq using hrow
  refine ⟨fun i j => rows i j, hrows_bound, ?_⟩
  intro i
  exact hrows_eq i

private lemma p29_matmul_apply_vec {n : ℕ} (M N : P29Matrix n n)
    (v : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, p29MatMul M N i j * v j) =
      ∑ k : Fin n, M i k * (∑ j : Fin n, N k j * v j) := by
  simp only [p29MatMul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  ring

private lemma p29_entry_norm_nonneg {m n : ℕ} (M : P29Matrix m n) :
    0 ≤ p29EntryNorm M := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

private lemma p29_entry_abs_le_norm {m n : ℕ} (M : P29Matrix m n)
    (i : Fin m) (j : Fin n) :
    |M i j| ≤ p29EntryNorm M := by
  unfold p29EntryNorm
  have hrow : |M i j| ≤ ∑ k : Fin n, |M i k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (M i k)) (Finset.mem_univ j)
  have htotal : (∑ k : Fin n, |M i k|) ≤
      ∑ q : Fin m, ∑ k : Fin n, |M q k| :=
    Finset.single_le_sum (s := Finset.univ)
      (f := fun q : Fin m => ∑ k : Fin n, |M q k|)
      (fun q _ => Finset.sum_nonneg fun k _ => abs_nonneg (M q k))
      (Finset.mem_univ i)
  exact hrow.trans htotal

private lemma p29_entry_norm_add {m n : ℕ} (M N : P29Matrix m n) :
    p29EntryNorm (M + N) ≤ p29EntryNorm M + p29EntryNorm N := by
  simp only [p29EntryNorm, Matrix.add_apply]
  calc
    (∑ i, ∑ j, |M i j + N i j|) ≤
        ∑ i, ∑ j, (|M i j| + |N i j|) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact abs_add_le _ _
    _ = (∑ i, ∑ j, |M i j|) + ∑ i, ∑ j, |N i j| := by
      simp_rw [Finset.sum_add_distrib]

private lemma p29_entry_norm_of_componentwise {m n : ℕ}
    (c : ℝ) (M E : P29Matrix m n) (hc : 0 ≤ c)
    (h : ∀ i j, |E i j| ≤ c * |M i j|) :
    p29EntryNorm E ≤ c * p29EntryNorm M := by
  simp only [p29EntryNorm]
  calc
    (∑ i, ∑ j, |E i j|) ≤ ∑ i, ∑ j, c * |M i j| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact h i j
    _ = c * ∑ i, ∑ j, |M i j| := by
      simp_rw [Finset.mul_sum]

private lemma p29_entry_norm_matmul {n : ℕ} (M N : P29Matrix n n) :
    p29EntryNorm (p29MatMul M N) ≤
      (n : ℝ) ^ 3 * p29EntryNorm M * p29EntryNorm N := by
  simp only [p29EntryNorm, p29MatMul]
  calc
    (∑ i, ∑ j, |∑ k, M i k * N k j|) ≤
        ∑ i, ∑ j, ∑ k, |M i k * N k j| := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ∑ _k : Fin n,
          p29EntryNorm M * p29EntryNorm N := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum
          intro k hk
          rw [abs_mul]
          exact mul_le_mul
            (p29_entry_abs_le_norm M i k)
            (p29_entry_abs_le_norm N k j)
            (abs_nonneg _) (p29_entry_norm_nonneg M)
    _ = (n : ℝ) ^ 3 * p29EntryNorm M * p29EntryNorm N := by
      simp [Fintype.card_fin]
      ring

private lemma p29_entry_norm_triple {n : ℕ} (M N P : P29Matrix n n) :
    p29EntryNorm (p29MatMul (p29MatMul M N) P) ≤
      (n : ℝ) ^ 6 * p29EntryNorm M * p29EntryNorm N * p29EntryNorm P := by
  calc
    p29EntryNorm (p29MatMul (p29MatMul M N) P) ≤
        (n : ℝ) ^ 3 * p29EntryNorm (p29MatMul M N) * p29EntryNorm P :=
      p29_entry_norm_matmul _ _
    _ ≤ (n : ℝ) ^ 3 *
          ((n : ℝ) ^ 3 * p29EntryNorm M * p29EntryNorm N) *
          p29EntryNorm P := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (p29_entry_norm_matmul M N)
          (pow_nonneg (Nat.cast_nonneg n) 3))
        (p29_entry_norm_nonneg P)
    _ = (n : ℝ) ^ 6 * p29EntryNorm M * p29EntryNorm N *
          p29EntryNorm P := by ring

private lemma p29_combined_error_expansion {n : ℕ}
    (L D ΔL ΔD ΔU : P29Matrix n n) :
    p29CombinedBackwardError L D ΔL ΔD ΔU =
      p29MatMul (p29MatMul ΔL (D + ΔD)) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L ΔD) (p29Transpose L + ΔU) +
      p29MatMul (p29MatMul L D) ΔU := by
  ext i j
  simp only [p29CombinedBackwardError, p29PerturbedLDLT, p29LDLT,
    Matrix.sub_apply, Matrix.add_apply, p29MatMul]
  simp_rw [add_mul, mul_add, Finset.sum_add_distrib]
  ring_nf
  simp_rw [Finset.sum_add_distrib]
  ring

private lemma p29_entry_norm_transpose {n : ℕ} (M : P29Matrix n n) :
    p29EntryNorm (p29Transpose M) = p29EntryNorm M := by
  simp only [p29EntryNorm, p29Transpose]
  rw [Finset.sum_comm]

private lemma p29_combined_error_norm_bound
    (fp : P29FPModel) (n : ℕ) (eta : ℝ)
    (L D ΔL ΔD ΔU : P29Matrix n n)
    (hvalid : P29GammaValid fp.u n) (heta : 0 ≤ eta)
    (hL : ∀ i j, |ΔL i j| ≤ p29Gamma fp.u n * |L i j|)
    (hD : p29EntryNorm ΔD ≤ eta * p29EntryNorm D)
    (hU : ∀ i j, |ΔU i j| ≤
      p29Gamma fp.u n * |p29Transpose L i j|) :
    p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) ≤
      p29SolveBackwardFactor fp n eta L D := by
  let g := p29Gamma fp.u n
  let T := p29Transpose L
  have hg : 0 ≤ g := p29_gamma_nonneg fp.u_nonneg (le_refl n) hvalid
  have hΔL : p29EntryNorm ΔL ≤ g * p29EntryNorm L :=
    p29_entry_norm_of_componentwise g L ΔL hg hL
  have hΔU : p29EntryNorm ΔU ≤ g * p29EntryNorm T :=
    p29_entry_norm_of_componentwise g T ΔU hg hU
  have hDadd : p29EntryNorm (D + ΔD) ≤
      (1 + eta) * p29EntryNorm D := by
    calc
      p29EntryNorm (D + ΔD) ≤ p29EntryNorm D + p29EntryNorm ΔD :=
        p29_entry_norm_add _ _
      _ ≤ p29EntryNorm D + eta * p29EntryNorm D := by linarith
      _ = (1 + eta) * p29EntryNorm D := by ring
  have hTadd : p29EntryNorm (T + ΔU) ≤
      (1 + g) * p29EntryNorm T := by
    calc
      p29EntryNorm (T + ΔU) ≤ p29EntryNorm T + p29EntryNorm ΔU :=
        p29_entry_norm_add _ _
      _ ≤ p29EntryNorm T + g * p29EntryNorm T := by linarith
      _ = (1 + g) * p29EntryNorm T := by ring
  let q : ℝ := (n : ℝ) ^ 6
  have hq : 0 ≤ q := by positivity
  have hnone : 0 ≤ 1 + eta := by linarith
  have hgnone : 0 ≤ 1 + g := by linarith
  have hL0 : 0 ≤ p29EntryNorm L := p29_entry_norm_nonneg L
  have hD0 : 0 ≤ p29EntryNorm D := p29_entry_norm_nonneg D
  have hT0 : 0 ≤ p29EntryNorm T := p29_entry_norm_nonneg T
  have hΔL0 : 0 ≤ p29EntryNorm ΔL := p29_entry_norm_nonneg ΔL
  have hΔD0 : 0 ≤ p29EntryNorm ΔD := p29_entry_norm_nonneg ΔD
  have hΔU0 : 0 ≤ p29EntryNorm ΔU := p29_entry_norm_nonneg ΔU
  have hDadd0 : 0 ≤ p29EntryNorm (D + ΔD) := p29_entry_norm_nonneg _
  have hTadd0 : 0 ≤ p29EntryNorm (T + ΔU) := p29_entry_norm_nonneg _
  have hterm1 :
      p29EntryNorm (p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU)) ≤
        q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T *
          (g * (1 + eta) * (1 + g)) := by
    calc
      p29EntryNorm (p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU)) ≤
          q * p29EntryNorm ΔL * p29EntryNorm (D + ΔD) *
            p29EntryNorm (T + ΔU) := p29_entry_norm_triple _ _ _
      _ ≤ q * (g * p29EntryNorm L) *
            ((1 + eta) * p29EntryNorm D) *
            ((1 + g) * p29EntryNorm T) := by
          gcongr <;> positivity
      _ = q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T *
            (g * (1 + eta) * (1 + g)) := by ring
  have hterm2 :
      p29EntryNorm (p29MatMul (p29MatMul L ΔD) (T + ΔU)) ≤
        q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T *
          (eta * (1 + g)) := by
    calc
      p29EntryNorm (p29MatMul (p29MatMul L ΔD) (T + ΔU)) ≤
          q * p29EntryNorm L * p29EntryNorm ΔD *
            p29EntryNorm (T + ΔU) := p29_entry_norm_triple _ _ _
      _ ≤ q * p29EntryNorm L * (eta * p29EntryNorm D) *
            ((1 + g) * p29EntryNorm T) := by
          gcongr <;> positivity
      _ = q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T *
            (eta * (1 + g)) := by ring
  have hterm3 :
      p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) ≤
        q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T * g := by
    calc
      p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) ≤
          q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm ΔU :=
        p29_entry_norm_triple _ _ _
      _ ≤ q * p29EntryNorm L * p29EntryNorm D *
            (g * p29EntryNorm T) := by
          gcongr <;> positivity
      _ = q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T * g := by ring
  rw [p29_combined_error_expansion]
  calc
    p29EntryNorm
        (p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU) +
          p29MatMul (p29MatMul L ΔD) (T + ΔU) +
          p29MatMul (p29MatMul L D) ΔU) ≤
      p29EntryNorm (p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU)) +
        p29EntryNorm (p29MatMul (p29MatMul L ΔD) (T + ΔU)) +
        p29EntryNorm (p29MatMul (p29MatMul L D) ΔU) := by
          linarith [p29_entry_norm_add
            (p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU))
            (p29MatMul (p29MatMul L ΔD) (T + ΔU)),
            p29_entry_norm_add
              (p29MatMul (p29MatMul ΔL (D + ΔD)) (T + ΔU) +
                p29MatMul (p29MatMul L ΔD) (T + ΔU))
              (p29MatMul (p29MatMul L D) ΔU)]
    _ ≤ q * p29EntryNorm L * p29EntryNorm D * p29EntryNorm T *
          (g * (1 + eta) * (1 + g) + eta * (1 + g) + g) := by
      linarith
    _ = p29SolveBackwardFactor fp n eta L D := by
      simp only [p29SolveBackwardFactor, q, g, T]

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
    p29_forward_backward_stable fp n L b hdiag hlower hvalid
  obtain ⟨ΔD, hΔD, hDsolve_eq⟩ := hDsolve
  have ht_diag : ∀ i, p29Transpose L i i ≠ 0 := by
    intro i
    exact hdiag i
  have ht_upper : ∀ i j : Fin n, j.val < i.val →
      p29Transpose L i j = 0 := by
    intro i j hji
    exact hlower j i hji
  obtain ⟨ΔU, hΔU, hback⟩ :=
    p29_back_backward_stable fp n (p29Transpose L) z
      ht_diag ht_upper hvalid
  let F := p29TotalBackwardError E0 L D ΔL ΔD ΔU
  refine ⟨ΔL, ΔD, ΔU, F, hΔL, hΔD, hΔU, rfl, ?_, ?_⟩
  · let x := p29BackSub fp n (p29Transpose L) z
    have hpert : ∀ i, ∑ j : Fin n,
        p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j = b i := by
      have hback' : ∀ k, ∑ j : Fin n,
          (p29Transpose L k j + ΔU k j) * x j = z k := by
        intro k
        simpa only [x] using hback k
      intro i
      rw [p29PerturbedLDLT, p29_matmul_apply_vec]
      simp only [Matrix.add_apply]
      simp_rw [hback']
      rw [p29_matmul_apply_vec]
      simp only [Matrix.add_apply]
      simp_rw [hDsolve_eq]
      simpa only [Matrix.add_apply, x] using hforward i
    intro i
    calc
      (∑ j : Fin n, (A i j + F i j) *
          p29BackSub fp n (p29Transpose L) z j) =
        ∑ j : Fin n, p29PerturbedLDLT L D ΔL ΔD ΔU i j * x j := by
          apply Finset.sum_congr rfl
          intro j hj
          have hfac := congrArg (fun M : P29Matrix n n => M i j) hfactor
          simp only [Matrix.add_apply] at hfac
          dsimp [F, p29TotalBackwardError, p29CombinedBackwardError, x]
          rw [hfac]
          ring
      _ = b i := hpert i
  · calc
      p29EntryNorm F =
          p29EntryNorm (E0 + p29CombinedBackwardError L D ΔL ΔD ΔU) := rfl
      _ ≤ p29EntryNorm E0 +
          p29EntryNorm (p29CombinedBackwardError L D ΔL ΔD ΔU) :=
        p29_entry_norm_add _ _
      _ ≤ factorEta * p29EntryNorm A +
          p29SolveBackwardFactor fp n eta L D := by
        exact add_le_add hE0
          (p29_combined_error_norm_bound fp n eta L D ΔL ΔD ΔU
            hvalid heta hΔL hΔD hΔU)
      _ = p29TotalBackwardBound fp n eta factorEta A L D := rfl

end HighamBench
