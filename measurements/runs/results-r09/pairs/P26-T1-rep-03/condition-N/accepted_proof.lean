import HighamBench.P26Definitions

namespace HighamBench

open scoped BigOperators

private def p26CoeffGood (u : ℝ) (k : ℕ) (c : ℝ) : Prop :=
  1 - (k : ℝ) * u ≤ c ∧ c ≤ 1 / (1 - (k : ℝ) * u)

private lemma p26_coeffGood_one (u : ℝ) : p26CoeffGood u 0 1 := by
  simp [p26CoeffGood]

private lemma p26_coeffGood_mul
    {u c e : ℝ} {k : ℕ} (hu : 0 ≤ u)
    (hvalid : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hc : p26CoeffGood u k c) (he : |e| ≤ u) :
    p26CoeffGood u (k + 1) (c * (1 + e)) := by
  have hku : (k : ℝ) * u < 1 := by
    have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  have hkp : 0 < 1 - (k : ℝ) * u := by linarith
  have hk1p : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  have helo : -u ≤ e := (abs_le.mp he).1
  have hehi : e ≤ u := (abs_le.mp he).2
  have hu1 : u < 1 := by
    have : u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
      simpa using (mul_le_mul_of_nonneg_right hk1 hu)
    linarith
  have hone : 0 ≤ 1 + e := by
    linarith
  constructor
  · calc
      1 - ((k + 1 : ℕ) : ℝ) * u
          ≤ (1 - (k : ℝ) * u) * (1 - u) := by
              push_cast
              nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hu]
      _ ≤ c * (1 + e) := by
              exact mul_le_mul hc.1 (by linarith) (by linarith) (by linarith [hc.1])
  · apply (le_div_iff₀ hk1p).2
    have hc' : c * (1 - (k : ℝ) * u) ≤ 1 := by
      exact (le_div_iff₀ hkp).mp hc.2
    calc
      c * (1 + e) * (1 - ((k + 1 : ℕ) : ℝ) * u)
          ≤ c * (1 + u) * (1 - ((k + 1 : ℕ) : ℝ) * u) := by
              have hc0 : 0 ≤ c := le_trans (by linarith) hc.1
              gcongr
      _ ≤ c * (1 - (k : ℝ) * u) := by
              have hc0 : 0 ≤ c := le_trans (by linarith) hc.1
              rw [mul_assoc]
              apply mul_le_mul_of_nonneg_left _ hc0
              push_cast
              nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hu,
                mul_nonneg hu hu]
      _ ≤ 1 := hc'

private lemma p26_coeffGood_div
    {u c e : ℝ} {k : ℕ} (hu : 0 ≤ u)
    (hvalid : ((k + 1 : ℕ) : ℝ) * u < 1)
    (hc : p26CoeffGood u k c) (he : |e| ≤ u) :
    p26CoeffGood u (k + 1) (c / (1 + e)) := by
  have hu1 : u < 1 := by
    have hu_le : u ≤ ((k + 1 : ℕ) : ℝ) * u := by
      have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
      simpa using (mul_le_mul_of_nonneg_right hk1 hu)
    linarith
  have helo : -u ≤ e := (abs_le.mp he).1
  have hehi : e ≤ u := (abs_le.mp he).2
  have hep : 0 < 1 + e := by linarith
  have hku : (k : ℝ) * u < 1 := by
    have hk : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  have hkp : 0 < 1 - (k : ℝ) * u := by linarith
  have hk1p : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := by linarith
  constructor
  · apply (le_div_iff₀ hep).2
    calc
      (1 - ((k + 1 : ℕ) : ℝ) * u) * (1 + e)
          ≤ (1 - ((k + 1 : ℕ) : ℝ) * u) * (1 + u) := by
              gcongr
      _ ≤ 1 - (k : ℝ) * u := by
              push_cast
              nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hu,
                mul_nonneg hu hu]
      _ ≤ c := hc.1
  · rw [div_le_iff₀ hep]
    rw [show 1 / (1 - ((k + 1 : ℕ) : ℝ) * u) * (1 + e) =
        (1 + e) / (1 - ((k + 1 : ℕ) : ℝ) * u) by
          simp [div_eq_mul_inv, mul_comm]]
    apply (le_div_iff₀ hk1p).2
    have hc' : c * (1 - (k : ℝ) * u) ≤ 1 :=
      (le_div_iff₀ hkp).mp hc.2
    have hres : c * (1 - ((k + 1 : ℕ) : ℝ) * u) ≤ 1 + e := by
      calc
        c * (1 - ((k + 1 : ℕ) : ℝ) * u)
          ≤ c * ((1 - (k : ℝ) * u) * (1 - u)) := by
              have hc0 : 0 ≤ c := le_trans (by linarith) hc.1
              apply mul_le_mul_of_nonneg_left _ hc0
              push_cast
              nlinarith [mul_nonneg (show 0 ≤ (k : ℝ) by positivity) hu]
        _ ≤ 1 + e := by
              have h1mu : 0 ≤ 1 - u := by linarith
              calc
                c * ((1 - (k : ℝ) * u) * (1 - u)) =
                    (c * (1 - (k : ℝ) * u)) * (1 - u) := by ring
                _ ≤ 1 - u := by
                  simpa using mul_le_mul_of_nonneg_right hc' h1mu
                _ ≤ 1 + e := by linarith
    simpa using hres

private lemma p26_coeffGood_mono
    {u c : ℝ} {k l : ℕ} (hu : 0 ≤ u)
    (hkl : k ≤ l) (hvalid : (l : ℝ) * u < 1)
    (hc : p26CoeffGood u k c) : p26CoeffGood u l c := by
  have hlp : 0 < 1 - (l : ℝ) * u := by linarith
  have hkp : 0 < 1 - (k : ℝ) * u := by
    have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    nlinarith
  constructor
  · have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    exact le_trans (by nlinarith) hc.1
  · apply le_trans hc.2
    exact one_div_le_one_div_of_le hlp (by
      have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
      nlinarith)

private lemma p26_coeffGood_abs_gamma
    {u c : ℝ} {n : ℕ} (hu : 0 ≤ u)
    (hvalid : (n : ℝ) * u < 1) (hc : p26CoeffGood u n c) :
    |c - 1| ≤ p26Gamma u n := by
  have hp : 0 < 1 - (n : ℝ) * u := by linarith
  rw [abs_le]
  constructor
  · dsimp [p26Gamma]
    have hnu : 0 ≤ (n : ℝ) * u := mul_nonneg (by positivity) hu
    have hfrac : (n : ℝ) * u ≤
        (n : ℝ) * u / (1 - (n : ℝ) * u) := by
      apply (le_div_iff₀ hp).2
      nlinarith [mul_nonneg hnu hnu]
    linarith [hc.1]
  · dsimp [p26Gamma]
    rw [le_div_iff₀ hp]
    have hc' : c * (1 - (n : ℝ) * u) ≤ 1 :=
      (le_div_iff₀ hp).mp hc.2
    nlinarith

private lemma p26_fold_backward (fp : P26FPModel) :
    ∀ (r : ℕ) (a x : Fin r → ℝ) (b : ℝ),
      (r : ℝ) * fp.u < 1 →
      ∃ (cs : ℝ) (c : Fin r → ℝ),
        p26CoeffGood fp.u r cs ∧
        (∀ j, p26CoeffGood fp.u r (c j)) ∧
        b =
          (Fin.foldl r
            (fun acc j ↦ fp.fl_sub acc (fp.fl_mul (a j) (x j))) b) * cs +
          ∑ j, (a j * x j) * c j := by
  intro r
  induction r with
  | zero =>
      intro a x b hr
      refine ⟨1, fun j ↦ Fin.elim0 j, p26_coeffGood_one fp.u, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · simp
  | succ r ih =>
      intro a x b hr
      have hr' : (r : ℝ) * fp.u < 1 := by
        have hu := fp.u_nonneg
        norm_num at hr ⊢
        nlinarith
      obtain ⟨cs, c, hcs, hc, heq⟩ :=
        ih (fun j ↦ a j.castSucc) (fun j ↦ x j.castSucc) b hr'
      obtain ⟨em, hem, hm⟩ := fp.model_mul (a (Fin.last r)) (x (Fin.last r))
      let s0 := Fin.foldl r
        (fun acc j ↦ fp.fl_sub acc (fp.fl_mul (a j.castSucc) (x j.castSucc))) b
      obtain ⟨es, hes, hs⟩ :=
        fp.model_sub s0 (fp.fl_mul (a (Fin.last r)) (x (Fin.last r)))
      let c' : Fin (r + 1) → ℝ :=
        Fin.lastCases (cs * (1 + em)) c
      refine ⟨cs / (1 + es), c', ?_, ?_, ?_⟩
      · exact p26_coeffGood_div fp.u_nonneg hr hcs hes
      · intro j
        refine Fin.lastCases ?_ (fun t ↦ ?_) j
        · simpa [c'] using p26_coeffGood_mul fp.u_nonneg hr hcs hem
        · simpa [c'] using
            p26_coeffGood_mono fp.u_nonneg (Nat.le_succ r) hr (hc t)
      · rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
        simp only [c', Fin.lastCases_castSucc, Fin.lastCases_last]
        have hes0 : 1 + es ≠ 0 := by
          have hu1 : fp.u < 1 := by
            have hu_le : fp.u ≤ ((r + 1 : ℕ) : ℝ) * fp.u := by
              have hcast : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by norm_num
              simpa using mul_le_mul_of_nonneg_right hcast fp.u_nonneg
            linarith
          have := (abs_le.mp hes).1
          linarith
        change b =
          fp.fl_sub s0 (fp.fl_mul (a (Fin.last r)) (x (Fin.last r))) *
              (cs / (1 + es)) +
            ((∑ j : Fin r, (a j.castSucc * x j.castSucc) * c j) +
              (a (Fin.last r) * x (Fin.last r)) * (cs * (1 + em)))
        rw [heq, hs, hm]
        field_simp
        ring

private lemma p26_sum_below_diag {n : ℕ} (r : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j, r.val < j.val → f j = 0) :
    ∑ j, f j =
      (∑ t : Fin r.val, f ⟨t.val, lt_trans t.isLt r.isLt⟩) + f r := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun j ↦ j.val ≤ r.val)
  let T : Finset (Fin n) := Finset.univ.filter (fun j ↦ j.val < r.val)
  have hsub : S ⊆ Finset.univ := by intro j hj; simp
  have hSU : (∑ j ∈ S, f j) = ∑ j, f j := by
    apply Finset.sum_subset hsub
    intro j hjU hjS
    apply hzero j
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjS
    omega
  have hrS : r ∈ S := by simp [S]
  have herase : S.erase r = T := by
    ext j
    simp only [S, T, Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hne, hj⟩
      omega
    · intro hj
      constructor
      · intro heq
        subst j
        omega
      · omega
  have hsplit : (∑ j ∈ T, f j) + f r = ∑ j ∈ S, f j := by
    rw [← herase]
    exact Finset.sum_erase_add S f hrS
  let e : Fin r.val ≃ {j : Fin n // j.val < r.val} :=
    { toFun := fun t ↦ ⟨⟨t.val, lt_trans t.isLt r.isLt⟩, t.isLt⟩
      invFun := fun j ↦ ⟨j.1.val, j.2⟩
      left_inv := by intro t; ext; rfl
      right_inv := by intro j; ext; rfl }
  have hTsub : (∑ j ∈ T, f j) =
      ∑ j : {j : Fin n // j.val < r.val}, f j := by
    apply Finset.sum_subtype
    intro j
    simp [T]
  have heq : ∑ j : {j : Fin n // j.val < r.val}, f j =
      ∑ t : Fin r.val, f ⟨t.val, lt_trans t.isLt r.isLt⟩ := by
    symm
    apply Fintype.sum_equiv e
    intro t
    rfl
  rw [← hSU, ← hsplit, hTsub, heq]

private lemma p26_one_row_backward (fp : P26FPModel) {n : ℕ}
    (L : P26Matrix n n) (b y x : Fin n → ℝ) (r : Fin n)
    (hdiag : L r r ≠ 0)
    (hlower : ∀ j : Fin n, r.val < j.val → L r j = 0)
    (hvalid : P26GammaValid fp.u n)
    (hbelow : ∀ t : Fin r.val,
      y ⟨t.val, lt_trans t.isLt r.isLt⟩ =
        x ⟨t.val, lt_trans t.isLt r.isLt⟩)
    (hy : y r = fp.fl_div
      (Fin.foldl r.val
        (fun acc t ↦ fp.fl_sub acc
          (fp.fl_mul
            (L r ⟨t.val, lt_trans t.isLt r.isLt⟩)
            (x ⟨t.val, lt_trans t.isLt r.isLt⟩)))
        (b r)) (L r r)) :
    ∃ d : Fin n → ℝ,
      (∀ j, |d j| ≤ p26Gamma fp.u n * |L r j|) ∧
      ∑ j : Fin n, (L r j + d j) * y j = b r := by
  have hnvalid : (n : ℝ) * fp.u < 1 := hvalid
  have hrle : r.val + 1 ≤ n := r.isLt
  have hrvalid : (r.val : ℝ) * fp.u < 1 := by
    have hcast : (r.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt r.isLt
    nlinarith [fp.u_nonneg]
  obtain ⟨cs, c, hcs, hc, hfold⟩ :=
    p26_fold_backward fp r.val
      (fun t ↦ L r ⟨t.val, lt_trans t.isLt r.isLt⟩)
      (fun t ↦ x ⟨t.val, lt_trans t.isLt r.isLt⟩)
      (b r) hrvalid
  let s := Fin.foldl r.val
    (fun acc t ↦ fp.fl_sub acc
      (fp.fl_mul
        (L r ⟨t.val, lt_trans t.isLt r.isLt⟩)
        (x ⟨t.val, lt_trans t.isLt r.isLt⟩)))
    (b r)
  obtain ⟨ed, hed, hdiv⟩ := fp.model_div s (L r r) hdiag
  have hu1 : fp.u < 1 := by
    have hu_le : fp.u ≤ (n : ℝ) * fp.u := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by
          intro hn
          subst n
          exact Fin.elim0 r))
      simpa using mul_le_mul_of_nonneg_right hn1 fp.u_nonneg
    linarith
  have hed0 : 1 + ed ≠ 0 := by
    have := (abs_le.mp hed).1
    linarith
  have hr1valid : ((r.val + 1 : ℕ) : ℝ) * fp.u < 1 := by
    have hcast : ((r.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hrle
    nlinarith [fp.u_nonneg]
  have hcdiag : p26CoeffGood fp.u (r.val + 1) (cs / (1 + ed)) :=
    p26_coeffGood_div fp.u_nonneg hr1valid hcs hed
  let d : Fin n → ℝ := fun j ↦
    if hj : j.val < r.val then
      L r j * (c ⟨j.val, hj⟩ - 1)
    else if j = r then
      L r r * (cs / (1 + ed) - 1)
    else 0
  refine ⟨d, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < r.val
    · have hcj : p26CoeffGood fp.u n (c ⟨j.val, hj⟩) :=
        p26_coeffGood_mono fp.u_nonneg (Nat.le_of_lt r.isLt)
          hnvalid (hc ⟨j.val, hj⟩)
      have habs := p26_coeffGood_abs_gamma fp.u_nonneg hnvalid hcj
      dsimp only [d]
      simp only [dif_pos hj, abs_mul]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left habs (abs_nonneg (L r j))
    · by_cases heq : j = r
      · subst j
        have hcj : p26CoeffGood fp.u n (cs / (1 + ed)) :=
          p26_coeffGood_mono fp.u_nonneg hrle hnvalid hcdiag
        have habs := p26_coeffGood_abs_gamma fp.u_nonneg hnvalid hcj
        simp only [d, lt_self_iff_false, dite_false, if_pos, abs_mul]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_left habs (abs_nonneg (L r r))
      · have hg0 : 0 ≤ p26Gamma fp.u n := by
          dsimp [p26Gamma]
          apply div_nonneg
          · exact mul_nonneg (by positivity) fp.u_nonneg
          · linarith
        change |(if hj' : j.val < r.val then
          L r j * (c ⟨j.val, hj'⟩ - 1) else
          if j = r then L r r * (cs / (1 + ed) - 1) else 0)| ≤ _
        rw [dif_neg hj, if_neg heq]
        simpa using mul_nonneg hg0 (abs_nonneg (L r j))
  · rw [p26_sum_below_diag r]
    · have hsdiag : s * cs = L r r * y r * (cs / (1 + ed)) := by
        rw [hy, hdiv]
        field_simp
      have hprefix :
          (∑ t : Fin r.val,
              (L r ⟨t.val, lt_trans t.isLt r.isLt⟩ +
                d ⟨t.val, lt_trans t.isLt r.isLt⟩) *
                y ⟨t.val, lt_trans t.isLt r.isLt⟩) =
            ∑ t : Fin r.val,
              (L r ⟨t.val, lt_trans t.isLt r.isLt⟩ *
                x ⟨t.val, lt_trans t.isLt r.isLt⟩) * c t := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [hbelow t]
        simp only [d, dif_pos t.isLt]
        ring
      rw [hprefix]
      have hdiagterm : (L r r + d r) * y r =
          L r r * y r * (cs / (1 + ed)) := by
        simp only [d, lt_self_iff_false, dite_false, if_pos]
        ring
      rw [hdiagterm, ← hsdiag]
      change (∑ t : Fin r.val,
          (L r ⟨t.val, lt_trans t.isLt r.isLt⟩ *
            x ⟨t.val, lt_trans t.isLt r.isLt⟩) * c t) + s * cs = b r
      rw [add_comm]
      exact hfold.symm
    · intro j hrj
      have hjnot : ¬j.val < r.val := by omega
      have hjne : j ≠ r := by
        intro heq
        subst j
        omega
      rw [hlower j hrj]
      have hdj : d j = 0 := by
        change (if hj' : j.val < r.val then
          L r j * (c ⟨j.val, hj'⟩ - 1) else
          if j = r then L r r * (cs / (1 + ed) - 1) else 0) = 0
        rw [dif_neg hjnot, if_neg hjne]
      rw [hdj]
      ring

private lemma p26_forwardSub_backward (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ r, L r r ≠ 0)
    (hlower : ∀ r j : Fin n, r.val < j.val → L r j = 0)
    (hvalid : P26GammaValid fp.u n) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ),
      let y := p26ForwardSubSteps fp n L b k hk x
      (∀ j : Fin n, j.val < n - k → y j = x j) ∧
      (∀ r : Fin n, n - k ≤ r.val →
        ∃ d : Fin n → ℝ,
          (∀ j, |d j| ≤ p26Gamma fp.u n * |L r j|) ∧
          ∑ j : Fin n, (L r j + d j) * y j = b r) := by
  intro k
  induction k with
  | zero =>
      intro hk x
      constructor
      · intro j hj
        rfl
      · intro r hr
        omega
  | succ k ih =>
      intro hk x
      have hk' : k ≤ n := Nat.le_trans (Nat.le_succ k) hk
      have hlt : n - k - 1 < n := by omega
      let r : Fin n := ⟨n - k - 1, hlt⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) ↦
          fp.fl_sub acc
            (fp.fl_mul (L r ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b r)
      let x' : Fin n → ℝ := Function.update x r (fp.fl_div s (L r r))
      have hstep : p26ForwardSubSteps fp n L b (k + 1) hk x =
          p26ForwardSubSteps fp n L b k hk' x' := by
        rw [p26ForwardSubSteps]
      rw [hstep]
      obtain ⟨hpres, hrows⟩ := ih hk' x'
      constructor
      · intro j hj
        rw [hpres j (by omega)]
        have hjne : j ≠ r := by
          intro heq
          subst j
          dsimp only [r] at hj
          omega
        simp [x', Function.update_apply, hjne]
      · intro q hq
        by_cases hqr : q = r
        · subst q
          have hbelow : ∀ t : Fin r.val,
              (p26ForwardSubSteps fp n L b k hk' x')
                  ⟨t.val, lt_trans t.isLt r.isLt⟩ =
                x ⟨t.val, lt_trans t.isLt r.isLt⟩ := by
            intro t
            have htval : t.val < r.val := t.isLt
            have htlt : t.val < n - k := by
              dsimp only [r] at htval
              omega
            rw [hpres _ htlt]
            have htne : (⟨t.val, lt_trans t.isLt r.isLt⟩ : Fin n) ≠ r := by
              intro heq
              have heqv := congrArg Fin.val heq
              change t.val = r.val at heqv
              omega
            simp [x', Function.update_apply, htne]
          have hyr : (p26ForwardSubSteps fp n L b k hk' x') r =
              fp.fl_div s (L r r) := by
            rw [hpres r (by
              dsimp only [r]
              omega)]
            simp [x']
          apply p26_one_row_backward fp L b
            (p26ForwardSubSteps fp n L b k hk' x') x r
            (hdiag r) (hlower r) hvalid hbelow
          simpa [s, count, r] using hyr
        · apply hrows q
          have hqval : r.val < q.val := by
            have hqle : r.val ≤ q.val := by
              dsimp only [r] at hq ⊢
              omega
            have hneval : r.val ≠ q.val := by
              intro heq
              apply hqr
              apply Fin.ext
              exact heq.symm
            omega
          dsimp only [r] at hqval ⊢
          omega

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
  have hdiagT : ∀ r : Fin n, p26Transpose R r r ≠ 0 := by
    intro r
    exact hdiag r
  have hlowerT : ∀ r j : Fin n, r.val < j.val →
      p26Transpose R r j = 0 := by
    intro r j hrj
    exact hupper j r hrj
  have hrow : ∀ i : Fin m,
      p26VecNorm (p26Residual (p26RoundedQ fp X R) R X i) ≤
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
          p26VecNorm (p26RoundedQ fp X R i) := by
    intro i
    obtain ⟨hpres, hrows⟩ := p26_forwardSub_backward fp n
      (p26Transpose R) (X i) hdiagT hlowerT hvalid n (le_refl n) (fun _ ↦ 0)
    have hw : ∀ k : Fin n, ∃ d : Fin n → ℝ,
        (∀ j, |d j| ≤ p26Gamma fp.u n * |p26Transpose R k j|) ∧
        ∑ j : Fin n,
          (p26Transpose R k j + d j) *
              p26ForwardSub fp n (p26Transpose R) (X i) j = X i k := by
      intro k
      simpa [p26ForwardSub] using hrows k (by omega)
    let deltaL : P26Matrix n n := fun k ↦ Classical.choose (hw k)
    apply hperturb i deltaL
    · intro k j
      have hk := (Classical.choose_spec (hw k)).1 j
      simpa [deltaL, p26Transpose] using hk
    · intro k
      have hk := (Classical.choose_spec (hw k)).2
      simpa [deltaL, p26RoundedQ] using hk
  let C : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Real.sqrt_nonneg n))
        fp.u_nonneg)
      hxNorm
  have hsq : ∀ i : Fin m,
      p26VecNormSq (p26Residual (p26RoundedQ fp X R) R X i) ≤
        C ^ 2 * p26VecNormSq (p26RoundedQ fp X R i) := by
    intro i
    have hr0 : 0 ≤
        p26VecNormSq (p26Residual (p26RoundedQ fp X R) R X i) := by
      dsimp [p26VecNormSq]
      positivity
    have hq0 : 0 ≤ p26VecNormSq (p26RoundedQ fp X R i) := by
      dsimp [p26VecNormSq]
      positivity
    have hsqr := (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg hC (Real.sqrt_nonneg _))).2 (by
        simpa [C] using hrow i)
    rw [mul_pow, Real.sq_sqrt hr0, Real.sq_sqrt hq0] at hsqr
    exact hsqr
  have hsum :
      p26FrobNormSq (p26Residual (p26RoundedQ fp X R) R X) ≤
        C ^ 2 * p26FrobNormSq (p26RoundedQ fp X R) := by
    dsimp only [p26FrobNormSq]
    calc
      (∑ i : Fin m,
          p26VecNormSq (p26Residual (p26RoundedQ fp X R) R X i)) ≤
          ∑ i : Fin m, C ^ 2 * p26VecNormSq (p26RoundedQ fp X R i) := by
            exact Finset.sum_le_sum fun i hi ↦ hsq i
      _ = C ^ 2 * ∑ i : Fin m, p26VecNormSq (p26RoundedQ fp X R i) := by
            rw [Finset.mul_sum]
  have hFrob :
      p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        C * p26FrobNorm (p26RoundedQ fp X R) := by
    dsimp only [p26FrobNorm]
    calc
      Real.sqrt (p26FrobNormSq
          (p26Residual (p26RoundedQ fp X R) R X)) ≤
          Real.sqrt (C ^ 2 * p26FrobNormSq (p26RoundedQ fp X R)) :=
            Real.sqrt_le_sqrt hsum
      _ = C * Real.sqrt (p26FrobNormSq (p26RoundedQ fp X R)) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs, abs_of_nonneg hC]
  calc
    p26FrobNorm (p26Residual (p26RoundedQ fp X R) R X) ≤
        C * p26FrobNorm (p26RoundedQ fp X R) := hFrob
    _ ≤ C * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hC
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      have hsqrt3 : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
        have hs3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
        have hs30 := Real.sqrt_nonneg 3
        nlinarith
      have hsqrtn := Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)
      have hsqrtprod : Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) =
          Real.sqrt 3 * (n : ℝ) := by
        rw [Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
        nlinarith [Real.sqrt_nonneg (n : ℝ)]
      have hfactor : 0 ≤ (n : ℝ) ^ 2 * fp.u * xNorm :=
        mul_nonneg (mul_nonneg (sq_nonneg (n : ℝ)) fp.u_nonneg) hxNorm
      dsimp only [C]
      calc
        ((11 : ℝ) / 10 * (n : ℝ) * Real.sqrt (n : ℝ) * fp.u * xNorm) *
              Real.sqrt (3 * (n : ℝ)) =
            ((11 : ℝ) / 10 * (n : ℝ) * fp.u * xNorm) *
              (Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ))) := by ring
        _ = (11 : ℝ) / 10 * (n : ℝ) *
              (Real.sqrt 3 * (n : ℝ)) * fp.u * xNorm := by
            rw [hsqrtprod]
            ring
        _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
              ((n : ℝ) ^ 2 * fp.u * xNorm) := by ring
        _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) :=
          mul_le_mul_of_nonneg_right hsqrt3 hfactor
        _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring

end HighamBench
