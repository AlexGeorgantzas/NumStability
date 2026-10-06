import HighamBench.P26Definitions

namespace HighamBench

open scoped BigOperators

private lemma p26ForwardSubSteps_preserves
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∀ j : Fin n, j.val < n - k →
      p26ForwardSubSteps fp n L b k hk x j = x j := by
  induction k generalizing x with
  | zero => simp [p26ForwardSubSteps]
  | succ k ih =>
      intro j hj
      simp only [p26ForwardSubSteps]
      rw [ih _ _ j (by omega)]
      have hne : j ≠ ⟨n - k - 1, by omega⟩ := by
        intro h
        have : j.val = n - k - 1 := congrArg Fin.val h
        omega
      simp [Function.update_apply, hne]

private noncomputable def p26FoldRow
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b q : Fin n → ℝ) (i : Fin n) : ℝ :=
  Fin.foldl i.val
    (fun acc (t : Fin i.val) =>
      fp.fl_sub acc
        (fp.fl_mul (L i ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)
          (q ⟨t.val, Nat.lt_trans t.isLt i.isLt⟩)))
    (b i)

private lemma p26ForwardSubSteps_equation
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b x : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    let q := p26ForwardSubSteps fp n L b k hk x
    ∀ i : Fin n, n - k ≤ i.val →
      q i = fp.fl_div (p26FoldRow fp n L b q i) (L i i) := by
  induction k generalizing x with
  | zero =>
      dsimp only
      intro i hi
      omega
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := p26FoldRow fp n L b x ik
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let q := p26ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      have hdef : p26ForwardSubSteps fp n L b (k + 1) hk x = q := by
        simp only [p26ForwardSubSteps]
        rfl
      dsimp only
      rw [hdef]
      intro i hi
      by_cases hik : i = ik
      · subst i
        have hqik : q ik = x' ik :=
          p26ForwardSubSteps_preserves fp n L b x' k _ ik (by
            dsimp [ik]
            omega)
        rw [hqik]
        have hfold : p26FoldRow fp n L b q ik = s := by
          dsimp only [p26FoldRow, s]
          congr 1
          funext acc t
          have hqt : q ⟨t.val, Nat.lt_trans t.isLt ik.isLt⟩ =
              x ⟨t.val, Nat.lt_trans t.isLt ik.isLt⟩ := by
            dsimp only [q]
            rw [p26ForwardSubSteps_preserves fp n L b x' k _]
            · have hne : (⟨t.val, Nat.lt_trans t.isLt ik.isLt⟩ : Fin n) ≠ ik := by
                intro h
                have hv := congrArg Fin.val h
                exact (Nat.ne_of_lt t.isLt) hv
              simp [x', hne]
            · dsimp [ik]
              omega
          rw [hqt]
        rw [hfold]
        simp [x']
      · have hvalne : i.val ≠ ik.val := by
          intro h
          exact hik (Fin.ext h)
        apply ih x' _ i
        dsimp [ik] at hi hvalne
        omega

private lemma p26ForwardSub_equation
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b : Fin n → ℝ) (i : Fin n) :
    let q := p26ForwardSub fp n L b
    q i = fp.fl_div (p26FoldRow fp n L b q i) (L i i) := by
  dsimp only [p26ForwardSub]
  apply p26ForwardSubSteps_equation
  omega

private lemma p26Gamma_mono_nat
    {u : ℝ} (hu : 0 ≤ u) {a b : ℕ} (hab : a ≤ b)
    (hb : (b : ℝ) * u < 1) :
    p26Gamma u a ≤ p26Gamma u b := by
  have habr : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have ha : (a : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right habr hu) hb
  rw [p26Gamma, p26Gamma]
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [mul_nonneg (mul_nonneg (Nat.cast_nonneg a) hu)
    (mul_nonneg (Nat.cast_nonneg b) hu)]

private lemma p26Gamma_mul_update
    {u : ℝ} (hu : 0 ≤ u) {r N : ℕ} (hrN : r + 1 ≤ N)
    (hN : (N : ℝ) * u < 1) {a e : ℝ}
    (ha : |a| ≤ p26Gamma u r) (he : |e| ≤ u) :
    |(1 + a) * (1 + e) - 1| ≤ p26Gamma u (r + 1) := by
  have hrN' : ((r + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hrN
  have hr1 : ((r + 1 : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrN' hu) hN
  have hr : (r : ℝ) * u < 1 := by
    have : (r : ℝ) ≤ (r + 1 : ℕ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right this hu]
  have hg : 0 ≤ p26Gamma u r := by
    rw [p26Gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg r) hu) (by linarith)
  calc
    |(1 + a) * (1 + e) - 1| = |a + e + a * e| := by ring
    _ ≤ |a| + |e| + |a| * |e| := by
      calc
        |a + e + a * e| ≤ |a| + |e| + |a * e| := by
          exact (abs_add_le (a + e) (a * e)).trans
            (by simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (abs_add_le a e) |a * e|)
        _ = |a| + |e| + |a| * |e| := by rw [abs_mul]
    _ ≤ p26Gamma u r + u + p26Gamma u r * u := by nlinarith [abs_nonneg a, abs_nonneg e]
    _ ≤ p26Gamma u (r + 1) := by
      rw [p26Gamma, p26Gamma]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hd0 : 0 < 1 - (r : ℝ) * u := by linarith
      have hd1 : 0 < 1 - ((r : ℝ) + 1) * u := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hr1
        linarith
      have heq :
          (r : ℝ) * u / (1 - (r : ℝ) * u) + u +
              (r : ℝ) * u / (1 - (r : ℝ) * u) * u =
            ((r : ℝ) + 1) * u / (1 - (r : ℝ) * u) := by
        field_simp [ne_of_gt hd0]
        ring
      rw [heq]
      exact div_le_div_of_nonneg_left
        (mul_nonneg (by positivity) hu) hd1 (by nlinarith)

private lemma p26Gamma_div_update
    {u : ℝ} (hu : 0 ≤ u) {r N : ℕ} (hrN : r + 1 ≤ N)
    (hN : (N : ℝ) * u < 1) {a e : ℝ}
    (ha : |a| ≤ p26Gamma u r) (he : |e| ≤ u) :
    |(1 + a) / (1 + e) - 1| ≤ p26Gamma u (r + 1) := by
  have hrN' : ((r + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hrN
  have hr1 : ((r + 1 : ℕ) : ℝ) * u < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hrN' hu) hN
  have hu1 : u < 1 := by
    have hru : u ≤ ((r + 1 : ℕ) : ℝ) * u := by
      have : (1 : ℝ) ≤ (r + 1 : ℕ) := by norm_num
      nlinarith
    linarith
  have hr : (r : ℝ) * u < 1 := by
    have : (r : ℝ) ≤ (r + 1 : ℕ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right this hu]
  have hg : 0 ≤ p26Gamma u r := by
    rw [p26Gamma]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg r) hu) (by linarith)
  have helo : -u ≤ e := (abs_le.mp he).1
  have hden : 0 < 1 + e := by linarith
  have hnum : |a - e| ≤ p26Gamma u r + u := by
    calc
      |a - e| ≤ |a| + |e| := abs_sub _ _
      _ ≤ p26Gamma u r + u := add_le_add ha he
  rw [div_sub_one (ne_of_gt hden), abs_div, abs_of_pos hden]
  calc
    |1 + a - (1 + e)| / (1 + e) = |a - e| / (1 + e) := by ring_nf
    _ ≤ (p26Gamma u r + u) / (1 - u) := by
      exact div_le_div₀ (add_nonneg hg hu) hnum (by linarith) (by linarith)
    _ ≤ p26Gamma u (r + 1) := by
      rw [p26Gamma, p26Gamma]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hdu : 0 < 1 - u := by linarith
      have hd0 : 0 < 1 - (r : ℝ) * u := by linarith
      have hd1 : 0 < 1 - ((r : ℝ) + 1) * u := by
        norm_num only [Nat.cast_add, Nat.cast_one] at hr1
        linarith
      have heqL :
          ((r : ℝ) * u / (1 - (r : ℝ) * u) + u) / (1 - u) =
            (u * ((r : ℝ) + 1 - (r : ℝ) * u)) /
              ((1 - (r : ℝ) * u) * (1 - u)) := by
        field_simp [ne_of_gt hdu, ne_of_gt hd0]
        ring
      rw [heqL]
      apply div_le_div₀
      · exact mul_nonneg (by positivity) hu
      · nlinarith [mul_nonneg (Nat.cast_nonneg r) hu]
      · exact hd1
      · nlinarith [mul_nonneg (Nat.cast_nonneg r) (sq_nonneg u)]

private noncomputable def p26RoundedFold
    (fp : P26FPModel) (c : ℕ) (a x : ℕ → ℝ) (b : ℝ) : ℝ :=
  Fin.foldl c
    (fun acc t => fp.fl_sub acc (fp.fl_mul (a t.val) (x t.val))) b

private lemma p26RoundedFold_backward
    (fp : P26FPModel) (N : ℕ)
    (hN : (N : ℝ) * fp.u < 1) (c : ℕ) (hcN : c ≤ N)
    (a x : ℕ → ℝ) (b : ℝ) :
    ∃ (theta : Fin c → ℝ) (rho : ℝ),
      (∀ j, |theta j| ≤ p26Gamma fp.u c) ∧
      |rho| ≤ p26Gamma fp.u c ∧
      b = ∑ j : Fin c, a j.val * x j.val * (1 + theta j) +
        p26RoundedFold fp c a x b * (1 + rho) := by
  induction c with
  | zero =>
      refine ⟨fun j => Fin.elim0 j, 0, ?_, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · simp [p26Gamma]
      · simp [p26RoundedFold]
  | succ c ih =>
      have hcN' : c ≤ N := Nat.le_trans (Nat.le_succ c) hcN
      obtain ⟨theta, rho, htheta, hrho, hrep⟩ := ih hcN'
      let sold := p26RoundedFold fp c a x b
      obtain ⟨mu, hmu, hmul⟩ := fp.model_mul (a c) (x c)
      obtain ⟨sigma, hsigma, hsub⟩ :=
        fp.model_sub sold (fp.fl_mul (a c) (x c))
      have hu1 : fp.u < 1 := by
        have hcast : ((c + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcN
        have hcu : ((c + 1 : ℕ) : ℝ) * fp.u < 1 :=
          lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hN
        have : fp.u ≤ ((c + 1 : ℕ) : ℝ) * fp.u := by
          have hc : (1 : ℝ) ≤ (c + 1 : ℕ) := by norm_num
          nlinarith [fp.u_nonneg]
        linarith
      have hsden : 1 + sigma ≠ 0 := by
        have := (abs_le.mp hsigma).1
        linarith
      let thetaLast := (1 + rho) * (1 + mu) - 1
      let rho' := (1 + rho) / (1 + sigma) - 1
      let theta' : Fin (c + 1) → ℝ := Fin.lastCases thetaLast theta
      refine ⟨theta', rho', ?_, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun t => ?_) j
        · dsimp [theta', thetaLast]
          simpa [theta', thetaLast] using
            p26Gamma_mul_update fp.u_nonneg hcN hN hrho hmu
        · dsimp [theta']
          simpa [theta'] using (htheta t).trans
              (p26Gamma_mono_nat fp.u_nonneg (Nat.le_succ c)
                (lt_of_le_of_lt
                  (mul_le_mul_of_nonneg_right
                    (by exact_mod_cast hcN : ((c + 1 : ℕ) : ℝ) ≤ (N : ℝ))
                    fp.u_nonneg) hN))
      · dsimp [rho']
        exact p26Gamma_div_update fp.u_nonneg hcN hN hrho hsigma
      · have hsnew : p26RoundedFold fp (c + 1) a x b =
            fp.fl_sub sold (fp.fl_mul (a c) (x c)) := by
          simp [p26RoundedFold, Fin.foldl_succ_last, sold]
        have hsold : sold =
            a c * x c * (1 + mu) +
              p26RoundedFold fp (c + 1) a x b / (1 + sigma) := by
          rw [hsnew, hsub, hmul]
          field_simp [hsden]
          ring
        rw [Fin.sum_univ_castSucc]
        simp only [theta', Fin.lastCases_castSucc, Fin.lastCases_last,
          Fin.val_castSucc, Fin.val_last]
        calc
          b = ∑ j : Fin c, a j.val * x j.val * (1 + theta j) +
                sold * (1 + rho) := by simpa only [sold] using hrep
          _ = ∑ j : Fin c, a j.val * x j.val * (1 + theta j) +
                a c * x c * (1 + thetaLast) +
                p26RoundedFold fp (c + 1) a x b * (1 + rho') := by
            rw [hsold]
            dsimp only [thetaLast, rho']
            field_simp [hsden]
            ring

private lemma p26ForwardSub_row_backward
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : (n : ℝ) * fp.u < 1) (k : Fin n) :
    let q := p26ForwardSub fp n L b
    ∃ drow : Fin n → ℝ,
      (∀ j, |drow j| ≤ p26Gamma fp.u n * |L k j|) ∧
      (∑ j : Fin n, (L k j + drow j) * q j) = b k := by
  let q := p26ForwardSub fp n L b
  let aa : ℕ → ℝ := fun t => if ht : t < n then L k ⟨t, ht⟩ else 0
  let xx : ℕ → ℝ := fun t => if ht : t < n then q ⟨t, ht⟩ else 0
  obtain ⟨theta, rho, htheta, hrho, hrep⟩ :=
    p26RoundedFold_backward fp n hvalid k.val (Nat.le_of_lt k.isLt) aa xx (b k)
  have hfold : p26RoundedFold fp k.val aa xx (b k) =
      p26FoldRow fp n L b q k := by
    dsimp only [p26RoundedFold, p26FoldRow]
    congr 1
    funext acc t
    have ht : t.val < n := Nat.lt_trans t.isLt k.isLt
    simp [aa, xx, ht]
  have hrep' :
      b k = ∑ j : Fin k.val,
          L k ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩ *
            q ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩ * (1 + theta j) +
        p26FoldRow fp n L b q k * (1 + rho) := by
    have haa : ∀ j : Fin k.val,
        aa j.val = L k ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩ := by
      intro j
      simp [aa, Nat.lt_trans j.isLt k.isLt]
    have hxx : ∀ j : Fin k.val,
        xx j.val = q ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩ := by
      intro j
      simp [xx, Nat.lt_trans j.isLt k.isLt]
    simpa only [haa, hxx, hfold] using hrep
  obtain ⟨delta, hdelta, hdiv⟩ :=
    fp.model_div (p26FoldRow fp n L b q k) (L k k) (hdiag k)
  have hq : q k =
      (p26FoldRow fp n L b q k / L k k) * (1 + delta) := by
    dsimp only [q]
    rw [p26ForwardSub_equation fp n L b k]
    exact hdiv
  have hu1 : fp.u < 1 := by
    have hnpos : 0 < n := Nat.pos_of_ne_zero (by
      intro hn
      simpa [hn] using k.isLt)
    have hnu : fp.u ≤ (n : ℝ) * fp.u := by
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
      nlinarith [fp.u_nonneg]
    linarith
  have hdden : 1 + delta ≠ 0 := by
    have := (abs_le.mp hdelta).1
    linarith
  have hsdiag : p26FoldRow fp n L b q k =
      L k k * q k / (1 + delta) := by
    field_simp [hdiag k, hdden] at hq ⊢
    nlinarith
  let thetaDiag := (1 + rho) / (1 + delta) - 1
  have hthetaDiag : |thetaDiag| ≤ p26Gamma fp.u (k.val + 1) := by
    dsimp only [thetaDiag]
    exact p26Gamma_div_update fp.u_nonneg (Nat.succ_le_iff.mpr k.isLt)
      hvalid hrho hdelta
  let drow : Fin n → ℝ := fun j =>
    if hj : j.val < k.val then L k j * theta ⟨j.val, hj⟩
    else if j = k then L k k * thetaDiag else 0
  refine ⟨drow, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < k.val
    · have hgam : |theta ⟨j.val, hj⟩| ≤ p26Gamma fp.u n :=
        (htheta ⟨j.val, hj⟩).trans
          (p26Gamma_mono_nat fp.u_nonneg (Nat.le_of_lt k.isLt) hvalid)
      simp only [drow, dif_pos hj, abs_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left hgam (abs_nonneg (L k j))
    · by_cases hjk : j = k
      · subst j
        have hgam : |thetaDiag| ≤ p26Gamma fp.u n :=
          hthetaDiag.trans
            (p26Gamma_mono_nat fp.u_nonneg (Nat.succ_le_iff.mpr k.isLt) hvalid)
        simp only [drow, lt_self_iff_false, dite_false, if_pos, abs_mul]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left hgam (abs_nonneg (L k k))
      · have hgamma : 0 ≤ p26Gamma fp.u n := by
          rw [p26Gamma]
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) fp.u_nonneg)
            (by linarith)
        have hj' : ¬ j < k := hj
        simp [drow, hj, hj', hjk, mul_nonneg hgamma (abs_nonneg (L k j))]
  · let f : Fin n → ℝ := fun j => (L k j + drow j) * q j
    have hsubset : Finset.range (k.val + 1) ⊆ Finset.range n :=
      Finset.range_mono (Nat.succ_le_iff.mpr k.isLt)
    have hzero : ∀ z, z ∈ Finset.range n → z ∉ Finset.range (k.val + 1) →
        (if hz : z < n then f ⟨z, hz⟩ else 0) = 0 := by
      intro z hzn hzk
      have hzn' : z < n := Finset.mem_range.mp hzn
      have hkz : k.val < z := by
        have : ¬ z < k.val + 1 := by simpa using hzk
        omega
      simp only [hzn', dif_pos]
      have hL : L k ⟨z, hzn'⟩ = 0 := hlower k ⟨z, hzn'⟩ hkz
      have hne : (⟨z, hzn'⟩ : Fin n) ≠ k := by
        intro h
        have : z = k.val := by simpa using congrArg Fin.val h
        omega
      simp [f, drow, hL, hne]
    have htruncate := Finset.sum_subset hsubset hzero
    have hfull : (∑ j : Fin n, f j) =
        ∑ z ∈ Finset.range (k.val + 1),
          if hz : z < n then f ⟨z, hz⟩ else 0 := by
      calc
        (∑ j : Fin n, f j) = ∑ z ∈ Finset.range n,
            if hz : z < n then f ⟨z, hz⟩ else 0 := by
          simpa using (Fin.sum_univ_eq_sum_range
            (fun z => if hz : z < n then f ⟨z, hz⟩ else 0) n)
        _ = _ := htruncate.symm
    change (∑ j : Fin n, f j) = b k
    rw [hfull, Finset.sum_range_succ]
    simp only [show k.val < n from k.isLt, dif_pos]
    have hlowerSum :
        (∑ z ∈ Finset.range k.val,
            if hz : z < n then f ⟨z, hz⟩ else 0) =
          ∑ j : Fin k.val,
            L k ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩ *
              q ⟨j.val, Nat.lt_trans j.isLt k.isLt⟩ * (1 + theta j) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      have hjn : j.val < n := Nat.lt_trans j.isLt k.isLt
      have hjk : (⟨j.val, hjn⟩ : Fin n) < k := j.isLt
      simp [f, drow, hjn, hjk]
      ring
    rw [hlowerSum]
    have hdiagTerm : f k = L k k * q k * (1 + thetaDiag) := by
      simp [f, drow]
      ring
    rw [hdiagTerm, hrep', hsdiag]
    dsimp only [thetaDiag]
    field_simp [hdden]
    ring

private lemma p26VecNormSq_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ p26VecNormSq x := by
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

private lemma p26VecNorm_sq {n : ℕ} (x : Fin n → ℝ) :
    p26VecNorm x ^ 2 = p26VecNormSq x := by
  exact Real.sq_sqrt (p26VecNormSq_nonneg x)

private lemma p26FrobNormSq_nonneg {m n : ℕ} (A : P26Matrix m n) :
    0 ≤ p26FrobNormSq A := by
  exact Finset.sum_nonneg fun _ _ => p26VecNormSq_nonneg _

private lemma p26FrobNorm_sq {m n : ℕ} (A : P26Matrix m n) :
    p26FrobNorm A ^ 2 = p26FrobNormSq A := by
  exact Real.sq_sqrt (p26FrobNormSq_nonneg A)

theorem p26_t1_lemma_3_2
    (fp : P26FPModel) (m n : ℕ)
    (X : P26Matrix m n) (R : P26Matrix n n) (xNorm : ℝ)
    (hdiag : ∀ i, R i i ≠ 0)
    (hupper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hvalid : P26GammaValid fp.u n)
    (hxNorm : 0 ≤ xNorm)
    (hperturb : P26RowPerturbationsControlled fp X R xNorm)
    (hQFrob : p26FrobNorm (p26RoundedQ fp X R) ≤
      Real.sqrt (3 * (n : ℝ))) :
    p26FrobNorm
        (p26Residual (p26RoundedQ fp X R) R X) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
  -- PROOF_START P26-T1-H001
  classical
  let Q := p26RoundedQ fp X R
  let E := p26Residual Q R X
  let C : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hlower : ∀ i j : Fin n, i.val < j.val → p26Transpose R i j = 0 := by
    intro i j hij
    exact hupper j i hij
  have hback : ∀ i : Fin m, ∃ deltaL : P26Matrix n n,
      (∀ k j, |deltaL k j| ≤ p26Gamma fp.u n * |R j k|) ∧
      (∀ k, ∑ j : Fin n,
        (p26Transpose R k j + deltaL k j) * Q i j = X i k) := by
    intro i
    have hrows : ∀ k : Fin n, ∃ drow : Fin n → ℝ,
        (∀ j, |drow j| ≤ p26Gamma fp.u n * |p26Transpose R k j|) ∧
        (∑ j : Fin n, (p26Transpose R k j + drow j) * Q i j) = X i k := by
      intro k
      simpa only [Q, p26RoundedQ, p26Transpose] using
        (p26ForwardSub_row_backward fp n (p26Transpose R) (X i)
          (by intro j; exact hdiag j) hlower hvalid k)
    choose drow hdrow hroweq using hrows
    refine ⟨fun k j => drow k j, ?_, ?_⟩
    · intro k j
      simpa only [p26Transpose] using hdrow k j
    · intro k
      exact hroweq k
  have hrowNorm : ∀ i : Fin m,
      p26VecNorm (E i) ≤ C * p26VecNorm (Q i) := by
    intro i
    obtain ⟨deltaL, hdeltaL, heq⟩ := hback i
    dsimp only [P26RowPerturbationsControlled] at hperturb
    simpa only [Q, E, C] using hperturb i deltaL hdeltaL heq
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) fp.u_nonneg)
      hxNorm
  have hsumsq : p26FrobNormSq E ≤ C ^ 2 * p26FrobNormSq Q := by
    dsimp only [p26FrobNormSq]
    calc
      (∑ i : Fin m, p26VecNormSq (E i)) ≤
          ∑ i : Fin m, C ^ 2 * p26VecNormSq (Q i) := by
        apply Finset.sum_le_sum
        intro i _
        have hEi := hrowNorm i
        have hEnon : 0 ≤ p26VecNorm (E i) := Real.sqrt_nonneg _
        have hQnon : 0 ≤ p26VecNorm (Q i) := Real.sqrt_nonneg _
        rw [← p26VecNorm_sq, ← p26VecNorm_sq]
        nlinarith [sq_nonneg (C * p26VecNorm (Q i) - p26VecNorm (E i))]
      _ = C ^ 2 * ∑ i : Fin m, p26VecNormSq (Q i) := by
        rw [Finset.mul_sum]
  have hglobal : p26FrobNorm E ≤ C * p26FrobNorm Q := by
    have hEnon : 0 ≤ p26FrobNorm E := Real.sqrt_nonneg _
    have hQnon : 0 ≤ p26FrobNorm Q := Real.sqrt_nonneg _
    rw [← p26FrobNorm_sq, ← p26FrobNorm_sq] at hsumsq
    have hs : p26FrobNorm E ^ 2 ≤ (C * p26FrobNorm Q) ^ 2 := by
      simpa [mul_pow] using hsumsq
    exact (sq_le_sq₀ hEnon (mul_nonneg hC hQnon)).mp hs
  have hsqrt :
      (11 : ℝ) / 10 * Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) ≤
        2 * (n : ℝ) := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs3 : Real.sqrt (3 : ℝ) ≤ 20 / 11 := by
      rw [Real.sqrt_le_iff]
      constructor <;> norm_num
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      (11 : ℝ) / 10 * Real.sqrt (n : ℝ) *
          (Real.sqrt 3 * Real.sqrt (n : ℝ)) =
          ((11 : ℝ) / 10 * Real.sqrt 3) *
            (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = ((11 : ℝ) / 10 * Real.sqrt 3) * (n : ℝ) := by
        rw [Real.sq_sqrt hn]
      _ ≤ 2 * (n : ℝ) := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs3 (by norm_num : (0 : ℝ) ≤ 11 / 10)) hn
        norm_num at this ⊢
        exact this
  have hCQ : C * p26FrobNorm Q ≤ C * Real.sqrt (3 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (by simpa only [Q] using hQFrob) hC
  have hfinal : C * Real.sqrt (3 * (n : ℝ)) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    have hfac : 0 ≤ (n : ℝ) * fp.u * xNorm :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) fp.u_nonneg) hxNorm
    have hmul := mul_le_mul_of_nonneg_right hsqrt hfac
    dsimp only [C]
    convert hmul using 1 <;> ring
  simpa only [Q, E] using hglobal.trans (hCQ.trans hfinal)

end HighamBench
