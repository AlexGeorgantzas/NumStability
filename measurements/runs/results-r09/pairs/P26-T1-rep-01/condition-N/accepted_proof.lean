import HighamBench.P26Definitions

namespace HighamBench

open scoped BigOperators

lemma p26_gamma_step_mul (u a d : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hvalid : ((k + 1 : ℕ) : ℝ) * u < 1)
    (ha : |a| ≤ p26Gamma u k) (hd : |d| ≤ u) :
    |(1 + a) * (1 + d) - 1| ≤ p26Gamma u (k + 1) := by
  have hk0 : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hk1 : (k : ℝ) * u < 1 := by
    have hkcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  have hden : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hk1
  have hden' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  have hg0 : 0 ≤ p26Gamma u k := by
    unfold p26Gamma
    positivity
  calc
    |(1 + a) * (1 + d) - 1| = |a + d + a * d| := by ring_nf
    _ ≤ |a| + |d| + |a| * |d| := by
      calc
        |a + d + a * d| ≤ |a| + |d| + |a * d| := by
          calc
            |a + d + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
            _ ≤ (|a| + |d|) + |a * d| := by
              nlinarith [abs_add_le a d]
            _ = |a| + |d| + |a * d| := rfl
        _ = |a| + |d| + |a| * |d| := by rw [abs_mul]
    _ ≤ p26Gamma u k + u + p26Gamma u k * u := by
      nlinarith [mul_le_mul ha hd (abs_nonneg d) hg0]
    _ ≤ p26Gamma u (k + 1) := by
      have heq : p26Gamma u k + u + p26Gamma u k * u =
          (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
        unfold p26Gamma
        field_simp [ne_of_gt hden]
        ring
      rw [heq]
      unfold p26Gamma
      norm_num at hvalid hden' ⊢
      have hden2 : 0 < 1 - ((k : ℝ) + 1) * u := by linarith
      apply div_le_div_of_nonneg_left
      · positivity
      · exact hden2
      · nlinarith

lemma p26_gamma_step_div (u a d : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hvalid : ((k + 1 : ℕ) : ℝ) * u < 1)
    (ha : |a| ≤ p26Gamma u k) (hd : |d| ≤ u) :
    |(1 + a) / (1 + d) - 1| ≤ p26Gamma u (k + 1) := by
  have hu1 : u < 1 := by
    have hkpos : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hkpos hu]
  have hdp : 0 < 1 + d := by
    have := (abs_le.mp hd).1
    linarith
  have hk0 : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  have hk1 : (k : ℝ) * u < 1 := by
    have hkcast : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by norm_num
    nlinarith
  have hden : 0 < 1 - (k : ℝ) * u := sub_pos.mpr hk1
  have hden' : 0 < 1 - ((k + 1 : ℕ) : ℝ) * u := sub_pos.mpr hvalid
  have hg0 : 0 ≤ p26Gamma u k := by
    unfold p26Gamma
    positivity
  have hdp0 : 1 + d ≠ 0 := ne_of_gt hdp
  rw [div_sub_one hdp0, abs_div, abs_of_pos hdp]
  calc
    |1 + a - (1 + d)| / (1 + d) = |a - d| / (1 + d) := by ring_nf
    _ ≤ (p26Gamma u k + u) / (1 - u) := by
      apply (div_le_div_iff₀ hdp (sub_pos.mpr hu1)).2
      have hnum : |a - d| ≤ p26Gamma u k + u := by
        calc
          |a - d| ≤ |a| + |d| := abs_sub _ _
          _ ≤ p26Gamma u k + u := add_le_add ha hd
      have hdlo := (abs_le.mp hd).1
      nlinarith [mul_le_mul_of_nonneg_right hnum (sub_nonneg.mpr hu)]
    _ ≤ p26Gamma u (k + 1) := by
      have heq : (p26Gamma u k + u) / (1 - u) =
          (((k : ℝ) + 1) * u - (k : ℝ) * u ^ 2) /
            ((1 - (k : ℝ) * u) * (1 - u)) := by
        unfold p26Gamma
        field_simp [ne_of_gt hden, ne_of_gt (sub_pos.mpr hu1)]
        ring
      rw [heq]
      unfold p26Gamma
      norm_num at hvalid hden' ⊢
      have hden2 : 0 < 1 - ((k : ℝ) + 1) * u := by linarith
      apply (div_le_div_iff₀ (mul_pos hden (sub_pos.mpr hu1)) hden2).2
      nlinarith [mul_pos hden hden2, mul_nonneg hk0 hu]

lemma p26_fold_backward (fp : P26FPModel) (N : ℕ)
    (a x : Fin N → ℝ) (b : ℝ)
    (hvalid : (N : ℝ) * fp.u < 1) :
    ∃ (theta : Fin N → ℝ) (eta : ℝ),
      (∀ j, |theta j| ≤ p26Gamma fp.u (j.val + 1)) ∧
      |eta| ≤ p26Gamma fp.u N ∧
      b = ∑ j : Fin N, a j * x j * (1 + theta j) +
        Fin.foldl N
          (fun s j ↦ fp.fl_sub s (fp.fl_mul (a j) (x j))) b * (1 + eta) := by
  induction N with
  | zero =>
      refine ⟨fun j ↦ Fin.elim0 j, 0, ?_, ?_, ?_⟩
      · intro j
        exact Fin.elim0 j
      · simp [p26Gamma]
      · simp
  | succ k ih =>
      let a' : Fin k → ℝ := fun j ↦ a j.castSucc
      let x' : Fin k → ℝ := fun j ↦ x j.castSucc
      let s : ℝ := Fin.foldl k
        (fun s j ↦ fp.fl_sub s (fp.fl_mul (a' j) (x' j))) b
      have hkvalid : (k : ℝ) * fp.u < 1 := by
        have hcast : (k : ℝ) ≤ (k + 1 : ℕ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hcast fp.u_nonneg]
      obtain ⟨theta, eta, htheta, heta, hid⟩ := ih a' x' hkvalid
      let last : Fin (k + 1) := Fin.last k
      obtain ⟨dm, hdm, hmul⟩ := fp.model_mul (a last) (x last)
      obtain ⟨ds, hds, hsub⟩ := fp.model_sub s (fp.fl_mul (a last) (x last))
      have hu_lt : fp.u < 1 := by
        have hone : (1 : ℝ) ≤ (k + 1 : ℕ) := by norm_num
        nlinarith [mul_le_mul_of_nonneg_right hone fp.u_nonneg]
      have hds0 : 1 + ds ≠ 0 := by
        have := (abs_le.mp hds).1
        nlinarith
      let thetaLast : ℝ := (1 + eta) * (1 + dm) - 1
      let eta' : ℝ := (1 + eta) / (1 + ds) - 1
      let theta' : Fin (k + 1) → ℝ :=
        Fin.lastCases thetaLast theta
      refine ⟨theta', eta', ?_, ?_, ?_⟩
      · intro j
        refine Fin.lastCases ?_ (fun t ↦ ?_) j
        · simp only [theta', Fin.lastCases_last, Fin.val_last]
          exact p26_gamma_step_mul fp.u eta dm k fp.u_nonneg hvalid heta hdm
        · simpa [theta'] using htheta t
      · dsimp only [eta']
        exact p26_gamma_step_div fp.u eta ds k fp.u_nonneg hvalid heta hds
      · rw [Fin.sum_univ_castSucc]
        simp only [theta', Fin.lastCases_castSucc, Fin.lastCases_last]
        change b = (∑ j : Fin k, a' j * x' j * (1 + theta j)) +
            a last * x last * (1 + thetaLast) +
          Fin.foldl (k + 1)
            (fun s j ↦ fp.fl_sub s (fp.fl_mul (a j) (x j))) b * (1 + eta')
        rw [Fin.foldl_succ_last]
        change b = (∑ j : Fin k, a' j * x' j * (1 + theta j)) +
            a last * x last * (1 + thetaLast) +
          fp.fl_sub s (fp.fl_mul (a last) (x last)) * (1 + eta')
        rw [hid, hsub, hmul]
        dsimp only [thetaLast, eta']
        field_simp [hds0]
        ring

lemma p26_sum_below_diag {n : ℕ} (r : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j, r.val < j.val → f j = 0) :
    (∑ j, f j) = (∑ j ∈ Finset.Iio r, f j) + f r := by
  classical
  have hdis : Disjoint (Finset.Iic r) (Finset.Ioi r) := by
    rw [Finset.disjoint_left]
    intro j hjle hjgt
    exact (not_lt_of_ge (Finset.mem_Iic.mp hjle)) (Finset.mem_Ioi.mp hjgt)
  have hunion : Finset.Iic r ∪ Finset.Ioi r = Finset.univ := by
    ext j
    simp only [Finset.mem_union, Finset.mem_Iic, Finset.mem_Ioi, Finset.mem_univ,
      iff_true]
    exact le_or_gt j r
  calc
    ∑ j, f j = ∑ j ∈ Finset.Iic r ∪ Finset.Ioi r, f j := by rw [hunion]
    _ = (∑ j ∈ Finset.Iic r, f j) + ∑ j ∈ Finset.Ioi r, f j :=
      Finset.sum_union hdis
    _ = (∑ j ∈ Finset.Iic r, f j) + 0 := by
      congr 1
      exact Finset.sum_eq_zero (fun j hj ↦ hzero j (by
        simpa only [Fin.lt_iff_val_lt_val] using (Finset.mem_Ioi.mp hj)))
    _ = (∑ j ∈ Finset.Iio r, f j) + f r := by
      rw [add_zero, ← Finset.Iio_insert r, Finset.sum_insert]
      · ac_rfl
      · simp

lemma p26_sum_Iio_fin {n : ℕ} (r : Fin n) (f : Fin n → ℝ) :
    (∑ j ∈ Finset.Iio r, f j) =
      ∑ t : Fin r.val, f ⟨t.val, lt_trans t.isLt r.isLt⟩ := by
  classical
  let e : Fin r.val ≃ {j : Fin n // j ∈ Finset.Iio r} :=
    { toFun := fun t ↦ ⟨⟨t.val, lt_trans t.isLt r.isLt⟩, by
        apply Finset.mem_Iio.mpr
        exact t.isLt⟩
      invFun := fun j ↦ ⟨j.val.val, by
        exact (@Finset.mem_Iio (Fin n) _ _ r j.val).mp j.property⟩
      left_inv := fun t ↦ by ext; rfl
      right_inv := fun j ↦ by ext; rfl }
  have hatt : (Finset.Iio r).attach = Finset.univ := by
    ext j
    simp
  rw [← Finset.sum_attach, hatt]
  exact (e.sum_comp (fun j ↦ f j.val)).symm

lemma p26_steps_preserve (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n)
    (x : Fin n → ℝ) (i : Fin n) (hi : i.val < n - k) :
    p26ForwardSubSteps fp n L b k hk x i = x i := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [p26ForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      rw [ih (Nat.le_of_succ_le hk) x' (by omega)]
      have hne : i ≠ ik := by
        intro heq
        have hv := congrArg Fin.val heq
        dsimp only [ik] at hv
        omega
      simp [x', hne]

lemma p26_gamma_mono (u : ℝ) {a b : ℕ} (hu : 0 ≤ u)
    (hab : a ≤ b) (hb : (b : ℝ) * u < 1) :
    p26Gamma u a ≤ p26Gamma u b := by
  have hmul : (a : ℝ) * u ≤ (b : ℝ) * u := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) hu
  have hdenb : 0 < 1 - (b : ℝ) * u := sub_pos.mpr hb
  have hdena : 0 < 1 - (a : ℝ) * u := by linarith
  unfold p26Gamma
  exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg _) hu) hmul hdenb (by linarith)

lemma p26_steps_backward (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : (n : ℝ) * fp.u < 1)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    ∃ delta : P26Matrix n n,
      (∀ i j, |delta i j| ≤ p26Gamma fp.u n * |L i j|) ∧
      ∀ i, n - k ≤ i.val →
        ∑ j : Fin n,
          (L i j + delta i j) *
            p26ForwardSubSteps fp n L b k hk x j = b i := by
  induction k generalizing x with
  | zero =>
      refine ⟨fun _ _ ↦ 0, ?_, ?_⟩
      · intro i j
        have hg : 0 ≤ p26Gamma fp.u n := by
          unfold p26Gamma
          have : 0 < 1 - (n : ℝ) * fp.u := sub_pos.mpr hvalid
          exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) this.le
        simpa using mul_nonneg hg (abs_nonneg (L i j))
      · intro i hi
        omega
  | succ k ih =>
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let a : Fin count → ℝ := fun t ↦ L ik ⟨t.val, by omega⟩
      let y : Fin count → ℝ := fun t ↦ x ⟨t.val, by omega⟩
      let s : ℝ := Fin.foldl count
        (fun acc t ↦ fp.fl_sub acc (fp.fl_mul (a t) (y t))) (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      obtain ⟨deltaOld, hdeltaOld, heqOld⟩ := ih hk' x'
      have hcount : (count : ℝ) * fp.u < 1 := by
        have hc : count ≤ n := by dsimp only [count]; omega
        have hcast : (count : ℝ) ≤ n := by exact_mod_cast hc
        nlinarith [mul_le_mul_of_nonneg_right hcast fp.u_nonneg]
      obtain ⟨theta, eta, htheta, heta, hfold⟩ :=
        p26_fold_backward fp count a y (b ik) hcount
      obtain ⟨dd, hdd, hdiv⟩ := fp.model_div s (L ik ik) (hdiag ik)
      have hu_lt : fp.u < 1 := by
        have hnpos : 1 ≤ n := by omega
        have hncast : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
        nlinarith [mul_le_mul_of_nonneg_right hncast fp.u_nonneg]
      have hdd0 : 1 + dd ≠ 0 := by
        have := (abs_le.mp hdd).1
        nlinarith
      let thetaDiag : ℝ := (1 + eta) / (1 + dd) - 1
      have hthetaDiag : |thetaDiag| ≤ p26Gamma fp.u (count + 1) := by
        exact p26_gamma_step_div fp.u eta dd count fp.u_nonneg (by
          have hc : count + 1 ≤ n := by dsimp only [count]; omega
          have hcast : ((count + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hc
          nlinarith [mul_le_mul_of_nonneg_right hcast fp.u_nonneg]) heta hdd
      let deltaRow : Fin n → ℝ := fun j ↦
        if hj : j.val < ik.val then
          L ik j * theta ⟨j.val, by simpa [count, ik] using hj⟩
        else if j = ik then L ik ik * thetaDiag else 0
      let delta : P26Matrix n n := fun i j ↦
        if i = ik then deltaRow j else deltaOld i j
      refine ⟨delta, ?_, ?_⟩
      · intro i j
        by_cases hi : i = ik
        · subst i
          simp only [delta, if_pos]
          by_cases hj : j.val < ik.val
          · simp only [deltaRow, dif_pos hj]
            rw [abs_mul]
            rw [mul_comm (p26Gamma fp.u n) |L ik j|]
            apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg (L ik j))
            exact (htheta ⟨j.val, by simpa [count, ik] using hj⟩).trans
              (p26_gamma_mono fp.u fp.u_nonneg (by
                dsimp only [count, ik]
                omega) hvalid)
          · simp only [deltaRow, dif_neg hj]
            by_cases heq : j = ik
            · subst j
              simp only [if_pos, abs_mul]
              rw [mul_comm (p26Gamma fp.u n) |L ik ik|]
              apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg (L ik ik))
              exact hthetaDiag.trans (p26_gamma_mono fp.u fp.u_nonneg (by
                dsimp only [count, ik]
                omega) hvalid)
            · simp only [if_neg heq, abs_zero]
              exact mul_nonneg (by
                unfold p26Gamma
                have : 0 < 1 - (n : ℝ) * fp.u := sub_pos.mpr hvalid
                exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) this.le)
                (abs_nonneg (L ik j))
        · simp only [delta, if_neg hi]
          exact hdeltaOld i j
      · intro i hi
        by_cases hir : i = ik
        · subst i
          simp only [delta, if_pos]
          let q := p26ForwardSubSteps fp n L b (k + 1) hk x
          have hqdef : q = p26ForwardSubSteps fp n L b k hk' x' := by
            dsimp only [q]
            rw [p26ForwardSubSteps.eq_def fp n L b (k + 1) hk x]
          have hsum := p26_sum_below_diag ik
            (fun j ↦ (L ik j + deltaRow j) * q j) (by
              intro j hj
              have hnot : ¬ j.val < ik.val := by omega
              have hne : j ≠ ik := by
                intro he
                subst j
                omega
              simp [deltaRow, hnot, hne, hlower ik j hj])
          rw [hsum, p26_sum_Iio_fin]
          simp only [q, hqdef]
          have hbelow : ∀ t : Fin ik.val,
              p26ForwardSubSteps fp n L b k hk' x'
                ⟨t.val, lt_trans t.isLt ik.isLt⟩ =
              x ⟨t.val, lt_trans t.isLt ik.isLt⟩ := by
            intro t
            rw [p26_steps_preserve fp n L b k hk' x']
            · have hne : ⟨t.val, lt_trans t.isLt ik.isLt⟩ ≠ ik := by
                intro he
                have hv := congrArg Fin.val he
                dsimp only [ik] at hv
                omega
              simp [x', hne]
            · dsimp only [ik]
              omega
          have hdiagq : p26ForwardSubSteps fp n L b k hk' x' ik =
              fp.fl_div s (L ik ik) := by
            rw [p26_steps_preserve fp n L b k hk' x' ik]
            · simp [x']
            · dsimp only [ik]
              omega
          have hdeltaBelow : ∀ t : Fin ik.val,
              deltaRow ⟨t.val, lt_trans t.isLt ik.isLt⟩ =
                L ik ⟨t.val, lt_trans t.isLt ik.isLt⟩ * theta t := by
            intro t
            simp only [deltaRow, dif_pos t.isLt]
            congr 2
          have hdeltaDiag : deltaRow ik = L ik ik * thetaDiag := by
            simp [deltaRow]
          simp_rw [hbelow, hdeltaBelow]
          rw [hdeltaDiag]
          rw [hdiagq, hdiv]
          have hsumalg :
              (∑ t : Fin ik.val,
                (L ik ⟨t.val, lt_trans t.isLt ik.isLt⟩ +
                  L ik ⟨t.val, lt_trans t.isLt ik.isLt⟩ * theta t) *
                    x ⟨t.val, lt_trans t.isLt ik.isLt⟩) =
              ∑ t : Fin ik.val,
                L ik ⟨t.val, lt_trans t.isLt ik.isLt⟩ *
                  x ⟨t.val, lt_trans t.isLt ik.isLt⟩ * (1 + theta t) := by
            apply Finset.sum_congr rfl
            intro t _
            ring
          rw [hsumalg]
          rw [hfold]
          change _ = (∑ t : Fin count, a t * y t * (1 + theta t)) + s * (1 + eta)
          dsimp only [a, y, thetaDiag]
          field_simp [hdd0, hdiag ik]
          ring
        · simp only [delta, if_neg hir]
          rw [p26ForwardSubSteps.eq_def]
          apply heqOld i
          have hval : i.val ≠ n - k - 1 := by
            intro hv
            apply hir
            apply Fin.ext
            simpa [ik] using hv
          omega

lemma p26_forward_backward (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : (n : ℝ) * fp.u < 1) :
    ∃ delta : P26Matrix n n,
      (∀ i j, |delta i j| ≤ p26Gamma fp.u n * |L i j|) ∧
      ∀ i, ∑ j : Fin n,
        (L i j + delta i j) * p26ForwardSub fp n L b j = b i := by
  obtain ⟨delta, hdelta, heq⟩ :=
    p26_steps_backward fp n L b hdiag hlower hvalid n (le_refl n) (fun _ ↦ 0)
  refine ⟨delta, hdelta, ?_⟩
  intro i
  exact heq i (by omega)

lemma p26_frob_of_row_bound {m n : ℕ} (A B : P26Matrix m n) (C : ℝ)
    (hC : 0 ≤ C)
    (hrow : ∀ i, p26VecNorm (A i) ≤ C * p26VecNorm (B i)) :
    p26FrobNorm A ≤ C * p26FrobNorm B := by
  have hvecsq_nonneg (v : Fin n → ℝ) : 0 ≤ p26VecNormSq v := by
    unfold p26VecNormSq
    positivity
  have hfrobsq_nonneg (M : P26Matrix m n) : 0 ≤ p26FrobNormSq M := by
    unfold p26FrobNormSq
    exact Finset.sum_nonneg (fun i _ ↦ hvecsq_nonneg (M i))
  have hrowsq : ∀ i, p26VecNormSq (A i) ≤ C ^ 2 * p26VecNormSq (B i) := by
    intro i
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).2
      (hrow i)
    unfold p26VecNorm at hs
    rw [Real.sq_sqrt (hvecsq_nonneg (A i)), mul_pow,
      Real.sq_sqrt (hvecsq_nonneg (B i))] at hs
    exact hs
  have htotal : p26FrobNormSq A ≤ C ^ 2 * p26FrobNormSq B := by
    unfold p26FrobNormSq
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ ↦ hrowsq i)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg hC (Real.sqrt_nonneg _))).1
  rw [Real.sq_sqrt (hfrobsq_nonneg A), mul_pow,
    Real.sq_sqrt (hfrobsq_nonneg B)]
  exact htotal

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
  let Q := p26RoundedQ fp X R
  let E := p26Residual Q R X
  let C : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (Real.sqrt_nonneg _))
        fp.u_nonneg) hxNorm
  have hrow : ∀ i, p26VecNorm (E i) ≤ C * p26VecNorm (Q i) := by
    intro i
    have hdiagT : ∀ k, p26Transpose R k k ≠ 0 := by
      intro k
      simpa [p26Transpose] using hdiag k
    have hlowerT : ∀ k j : Fin n, k.val < j.val → p26Transpose R k j = 0 := by
      intro k j hkj
      simpa [p26Transpose] using hupper j k hkj
    obtain ⟨deltaL, hdeltaL, heqL⟩ := p26_forward_backward fp n
      (p26Transpose R) (X i) hdiagT hlowerT hvalid
    dsimp only [P26RowPerturbationsControlled] at hperturb
    have hi := hperturb i deltaL (by
      intro k j
      simpa [p26Transpose] using hdeltaL k j) (by
      intro k
      simpa [Q, p26RoundedQ] using heqL k)
    simpa [E, C, Q] using hi
  have hFrob : p26FrobNorm E ≤ C * p26FrobNorm Q :=
    p26_frob_of_row_bound E Q C hC hrow
  have hsqrt3 : Real.sqrt (3 : ℝ) ≤ (20 : ℝ) / 11 := by
    have hs0 : 0 ≤ Real.sqrt (3 : ℝ) := Real.sqrt_nonneg _
    have hs2 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hcoeff : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
    nlinarith
  have hscale :
      C * Real.sqrt (3 * (n : ℝ)) ≤
        2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    have hsqn : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn
    have hp : 0 ≤ (n : ℝ) ^ 2 * fp.u * xNorm :=
      mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      C * (Real.sqrt 3 * Real.sqrt (n : ℝ)) =
          ((11 : ℝ) / 10 * Real.sqrt 3) *
            ((n : ℝ) ^ 2 * fp.u * xNorm) := by
              dsimp only [C]
              calc
                (11 / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm) *
                    (Real.sqrt 3 * Real.sqrt n) =
                    (11 / 10 * Real.sqrt 3) *
                      ((n : ℝ) * (Real.sqrt n * Real.sqrt n) * fp.u * xNorm) := by ring
                _ = (11 / 10 * Real.sqrt 3) * ((n : ℝ) ^ 2 * fp.u * xNorm) := by
                  rw [hsqn]
                  ring
      _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) :=
        mul_le_mul_of_nonneg_right hcoeff hp
      _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring
  change p26FrobNorm E ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm
  calc
    p26FrobNorm E ≤ C * p26FrobNorm Q := hFrob
    _ ≤ C * Real.sqrt (3 * (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hQFrob hC
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := hscale

end HighamBench
