import HighamBench.P26Definitions

namespace HighamBench

open scoped BigOperators

private lemma p26_vecNorm_sq {n : ℕ} (v : Fin n → ℝ) :
    p26VecNorm v ^ 2 = p26VecNormSq v := by
  rw [p26VecNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun j _ => sq_nonneg (v j)

private lemma p26_frob_row_bound {m n : ℕ}
    (A B : P26Matrix m n) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ i, p26VecNorm (A i) ≤ c * p26VecNorm (B i)) :
    p26FrobNorm A ≤ c * p26FrobNorm B := by
  have hs : p26FrobNormSq A ≤ c ^ 2 * p26FrobNormSq B := by
    simp only [p26FrobNormSq]
    calc
      ∑ i : Fin m, p26VecNormSq (A i) =
          ∑ i : Fin m, p26VecNorm (A i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            exact (p26_vecNorm_sq (A i)).symm
      _ ≤ ∑ i : Fin m, c ^ 2 * p26VecNorm (B i) ^ 2 := by
            apply Finset.sum_le_sum
            intro i hi
            have ha := Real.sqrt_nonneg (p26VecNormSq (A i))
            have hb := Real.sqrt_nonneg (p26VecNormSq (B i))
            change 0 ≤ p26VecNorm (A i) at ha
            change 0 ≤ p26VecNorm (B i) at hb
            nlinarith [h i]
      _ = c ^ 2 * ∑ i : Fin m, p26VecNormSq (B i) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [p26_vecNorm_sq]
  have hAsq : 0 ≤ p26FrobNormSq A := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)
  have hBsq : 0 ≤ p26FrobNormSq B := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (B i j)
  rw [p26FrobNorm, p26FrobNorm]
  have hsqrt := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc] at hsqrt
  exact hsqrt

private lemma p26_cast_mul_lt_one_of_le
    (u : ℝ) (n k : ℕ) (hu : 0 ≤ u)
    (hn : (n : ℝ) * u < 1) (hk : k ≤ n) :
    (k : ℝ) * u < 1 := by
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  nlinarith

private lemma p26_gamma_nonneg
    (u : ℝ) (k : ℕ) (hu : 0 ≤ u) (hk : (k : ℝ) * u < 1) :
    0 ≤ p26Gamma u k := by
  unfold p26Gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hu) (by linarith)

private lemma p26_gamma_mono
    (u : ℝ) (n k : ℕ) (hu : 0 ≤ u)
    (hn : (n : ℝ) * u < 1) (hk : k ≤ n) :
    p26Gamma u k ≤ p26Gamma u n := by
  have hk' := p26_cast_mul_lt_one_of_le u n k hu hn hk
  unfold p26Gamma
  apply (div_le_div_iff₀ (by linarith : 0 < 1 - (k : ℝ) * u)
    (by linarith : 0 < 1 - (n : ℝ) * u)).2
  have hcast : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  nlinarith

private lemma p26_gamma_mul_step
    (u : ℝ) (n k : ℕ) (hu : 0 ≤ u)
    (hn : (n : ℝ) * u < 1) (hk : k + 1 ≤ n)
    (c d : ℝ) (hc : |c - 1| ≤ p26Gamma u k) (hd : |d| ≤ u) :
    |c * (1 + d) - 1| ≤ p26Gamma u (k + 1) := by
  have hku := p26_cast_mul_lt_one_of_le u n k hu hn (by omega)
  have hksu := p26_cast_mul_lt_one_of_le u n (k + 1) hu hn hk
  have hdu : |1 + d| ≤ 1 + u := by
    calc
      |1 + d| ≤ |(1 : ℝ)| + |d| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left hd 1
  have hsplit : c * (1 + d) - 1 = (c - 1) * (1 + d) + d := by ring
  rw [hsplit]
  calc
    |(c - 1) * (1 + d) + d| ≤ |c - 1| * |1 + d| + |d| := by
      simpa [abs_mul] using abs_add_le ((c - 1) * (1 + d)) d
    _ ≤ p26Gamma u k * (1 + u) + u := by
      exact add_le_add
        (mul_le_mul hc hdu (abs_nonneg _) (p26_gamma_nonneg u k hu hku)) hd
    _ ≤ p26Gamma u (k + 1) := by
      have hgk : 0 ≤ p26Gamma u k := p26_gamma_nonneg u k hu hku
      have hgks : 0 ≤ p26Gamma u (k + 1) :=
        p26_gamma_nonneg u (k + 1) hu hksu
      have egk : p26Gamma u k * (1 - (k : ℝ) * u) = (k : ℝ) * u := by
        unfold p26Gamma
        exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
      have egks : p26Gamma u (k + 1) * (1 - (k + 1 : ℕ) * u) =
          (k + 1 : ℕ) * u := by
        unfold p26Gamma
        exact div_mul_cancel₀ _ (ne_of_gt (by linarith [hksu]))
      push_cast at egks hksu
      nlinarith [mul_nonneg hgk hu, mul_nonneg hgks hu]

private lemma p26_gamma_div_step
    (u : ℝ) (n k : ℕ) (hu : 0 ≤ u)
    (hn : (n : ℝ) * u < 1) (hk : k + 1 ≤ n)
    (c d : ℝ) (hc : |c - 1| ≤ p26Gamma u k) (hd : |d| ≤ u) :
    |c / (1 + d) - 1| ≤ p26Gamma u (k + 1) := by
  have hku := p26_cast_mul_lt_one_of_le u n k hu hn (by omega)
  have hksu := p26_cast_mul_lt_one_of_le u n (k + 1) hu hn hk
  have hu_lt : u < 1 := by
    have hnpos : 0 < n := by omega
    have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    nlinarith
  have hden : 0 < 1 + d := by
    have hneg : -u ≤ d := (abs_le.mp hd).1
    linarith
  have hid : c / (1 + d) - 1 = ((c - 1) - d) / (1 + d) := by
    field_simp
    <;> ring
  rw [hid, abs_div, abs_of_pos hden]
  apply (div_le_iff₀ hden).2
  have hnum : |(c - 1) - d| ≤ p26Gamma u k + u := by
    calc
      |(c - 1) - d| ≤ |c - 1| + |d| := abs_sub _ _
      _ ≤ p26Gamma u k + u := add_le_add hc hd
  calc
    |(c - 1) - d| ≤ p26Gamma u k + u := hnum
    _ ≤ p26Gamma u (k + 1) * (1 + d) := by
      have hdneg : -u ≤ d := (abs_le.mp hd).1
      have hgk : 0 ≤ p26Gamma u k := p26_gamma_nonneg u k hu hku
      have hgks : 0 ≤ p26Gamma u (k + 1) :=
        p26_gamma_nonneg u (k + 1) hu hksu
      have egk : p26Gamma u k * (1 - (k : ℝ) * u) = (k : ℝ) * u := by
        unfold p26Gamma
        exact div_mul_cancel₀ _ (ne_of_gt (by linarith))
      have egks : p26Gamma u (k + 1) * (1 - (k + 1 : ℕ) * u) =
          (k + 1 : ℕ) * u := by
        unfold p26Gamma
        exact div_mul_cancel₀ _ (ne_of_gt (by linarith [hksu]))
      push_cast at egks hksu
      nlinarith [mul_nonneg hgk hu, mul_nonneg hgks hu,
        mul_nonneg hgks (by linarith : 0 ≤ d + u)]

private lemma p26_fold_backward
    (fp : P26FPModel) (n k : ℕ) (hk : k ≤ n)
    (a q : Fin k → ℝ) (b : ℝ) (hvalid : P26GammaValid fp.u n) :
    ∃ cs : ℝ, ∃ ca : Fin k → ℝ,
      b = cs * Fin.foldl k
          (fun acc t => fp.fl_sub acc (fp.fl_mul (a t) (q t))) b +
          ∑ t : Fin k, ca t * a t * q t ∧
      |cs - 1| ≤ p26Gamma fp.u k ∧
      ∀ t, |ca t - 1| ≤ p26Gamma fp.u k := by
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hn : (n : ℝ) * fp.u < 1 := hvalid
  induction k with
  | zero =>
      refine ⟨1, fun t => Fin.elim0 t, ?_, ?_, ?_⟩
      · simp
      · simp [p26Gamma]
      · intro t
        exact Fin.elim0 t
  | succ k ih =>
      have hk0 : k ≤ n := by omega
      obtain ⟨cs, ca, heq, hcs, hca⟩ :=
        ih hk0 (fun t => a t.castSucc) (fun t => q t.castSucc)
      let s0 := Fin.foldl k
        (fun acc t => fp.fl_sub acc
          (fp.fl_mul (a t.castSucc) (q t.castSucc))) b
      obtain ⟨mu, hmu, hmul⟩ :=
        fp.model_mul (a (Fin.last k)) (q (Fin.last k))
      obtain ⟨d, hd, hsub⟩ :=
        fp.model_sub s0 (fp.fl_mul (a (Fin.last k)) (q (Fin.last k)))
      have hu_lt : fp.u < 1 := by
        have hnpos : 0 < n := by omega
        have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
        nlinarith
      have hdpos : 0 < 1 + d := by
        have := (abs_le.mp hd).1
        linarith
      let cs' := cs / (1 + d)
      let ca' : Fin (k + 1) → ℝ :=
        fun t => Fin.lastCases (cs * (1 + mu)) ca t
      refine ⟨cs', ca', ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ_last]
        change b = cs' * fp.fl_sub s0
            (fp.fl_mul (a (Fin.last k)) (q (Fin.last k))) +
          ∑ t : Fin (k + 1), ca' t * a t * q t
        rw [Fin.sum_univ_castSucc]
        simp only [ca', Fin.lastCases_castSucc, Fin.lastCases_last]
        have heq' : b = cs * s0 +
            ∑ t : Fin k, ca t * a t.castSucc * q t.castSucc := heq
        rw [heq', hsub, hmul]
        dsimp [cs']
        field_simp
        <;> ring
      · dsimp [cs']
        exact p26_gamma_div_step fp.u n k hu hn hk cs d hcs hd
      · intro t
        refine Fin.lastCases ?_ (fun j => ?_) t
        · simp only [ca', Fin.lastCases_last]
          exact p26_gamma_mul_step fp.u n k hu hn hk cs mu hcs hmu
        · simp only [ca', Fin.lastCases_castSucc]
          exact le_trans (hca j) (p26_gamma_mono fp.u (k + 1) k hu
            (p26_cast_mul_lt_one_of_le fp.u n (k + 1) hu hn hk) (by omega))

private lemma p26_steps_preserve_lt
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (j : Fin n)
    (hj : j.val < n - k) :
    p26ForwardSubSteps fp n L b k hk x j = x j := by
  induction k generalizing x j with
  | zero => simp [p26ForwardSubSteps]
  | succ k ih =>
      rw [p26ForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      rw [ih (Nat.le_of_succ_le hk) x' j (by omega)]
      have hne : j ≠ ik := by
        intro heq
        have hv : j.val = ik.val := congrArg Fin.val heq
        dsimp [ik] at hv
        omega
      simp [x', hne]

private lemma p26_steps_component
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    let y := p26ForwardSubSteps fp n L b k hk x
    ∀ i : Fin n, n - k ≤ i.val →
      y i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) =>
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨t.val, by omega⟩)
                (y ⟨t.val, by omega⟩)))
          (b i))
        (L i i) := by
  induction k generalizing x with
  | zero =>
      dsimp
      intro i hi
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
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let y := p26ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      have hydef : p26ForwardSubSteps fp n L b (k + 1) hk x = y := by
        rw [p26ForwardSubSteps]
      dsimp only
      intro i hi
      rw [hydef]
      by_cases hieq : i = ik
      · subst i
        have hiklt : ik.val < n - k := by dsimp [ik]; omega
        have hyik : y ik = x' ik :=
          p26_steps_preserve_lt fp n L b k (Nat.le_of_succ_le hk) x' ik hiklt
        rw [hyik]
        have hxik : x' ik = fp.fl_div s (L ik ik) := by simp [x']
        rw [hxik]
        congr 2
        change Fin.foldl count
            (fun acc (t : Fin count) => fp.fl_sub acc
              (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                (x ⟨t.val, by omega⟩))) (b ik) =
          Fin.foldl count
            (fun acc (t : Fin count) => fp.fl_sub acc
              (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                (y ⟨t.val, by omega⟩))) (b ik)
        apply congrArg (fun f => Fin.foldl count f (b ik))
        funext acc t
        have hcount : count = n - k - 1 := rfl
        have htlt : (⟨t.val, by omega⟩ : Fin n).val < n - k := by
          change t.val < n - k
          omega
        have hyt : y (⟨t.val, by omega⟩ : Fin n) =
            x' (⟨t.val, by omega⟩ : Fin n) :=
          p26_steps_preserve_lt fp n L b k (Nat.le_of_succ_le hk) x'
            ⟨t.val, by omega⟩ htlt
        have htne : (⟨t.val, by omega⟩ : Fin n) ≠ ik := by
          intro heq
          have hv := congrArg Fin.val heq
          dsimp [ik] at hv
          omega
        rw [hyt]
        simp [x', htne]
      · have higt : ik.val < i.val := by
          have hikval : ik.val = n - k - 1 := rfl
          omega
        have hirange : n - k ≤ i.val := by
          have hikval : ik.val = n - k - 1 := rfl
          omega
        exact ih (Nat.le_of_succ_le hk) x' i hirange

private lemma p26_forwardSub_component
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n) (b : Fin n → ℝ)
    (i : Fin n) :
    p26ForwardSub fp n L b i = fp.fl_div
      (Fin.foldl i.val
        (fun acc (t : Fin i.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L i ⟨t.val, by omega⟩)
              (p26ForwardSub fp n L b ⟨t.val, by omega⟩)))
        (b i))
      (L i i) := by
  exact p26_steps_component fp n L b n (le_refl n) (fun _ => 0) i (by omega)

private lemma p26_sum_below {n : ℕ} (k : Fin n) (f : Fin n → ℝ) :
    (∑ j : Fin n, if j.val < k.val then f j else 0) =
      ∑ t : Fin k.val, f ⟨t.val, by omega⟩ := by
  let e : Fin k.val ≃ {j : Fin n // j.val < k.val} :=
    { toFun := fun t => ⟨⟨t.val, by omega⟩, t.isLt⟩
      invFun := fun j => ⟨j.1.val, j.2⟩
      left_inv := by intro t; ext; rfl
      right_inv := by intro j; ext; rfl }
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  simpa only [Finset.subtype_univ] using
    (Fintype.sum_equiv e (fun t : Fin k.val => f ⟨t.val, by omega⟩)
      (fun j : {j : Fin n // j.val < k.val} => f j.1) (by
        intro t
        rfl)).symm

private lemma p26_sum_below_dite {n : ℕ} (k : Fin n)
    (f : ∀ j : Fin n, j.val < k.val → ℝ) :
    (∑ j : Fin n, if hj : j.val < k.val then f j hj else 0) =
      ∑ t : Fin k.val,
        f ⟨t.val, lt_trans t.isLt k.isLt⟩ t.isLt := by
  let g : Fin n → ℝ := fun j => if hj : j.val < k.val then f j hj else 0
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun j : Fin n => j.val < k.val) g
  have hcompl : (∑ j : {j : Fin n // ¬j.val < k.val}, g j.1) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    dsimp [g]
    rw [dif_neg j.2]
  rw [hcompl, add_zero] at hsplit
  rw [← hsplit]
  let e : Fin k.val ≃ {j : Fin n // j.val < k.val} :=
    { toFun := fun t => ⟨⟨t.val, by omega⟩, t.isLt⟩
      invFun := fun j => ⟨j.1.val, j.2⟩
      left_inv := by intro t; ext; rfl
      right_inv := by intro j; ext; rfl }
  simpa [g] using
    (Fintype.sum_equiv e
      (fun t : Fin k.val =>
        f ⟨t.val, lt_trans t.isLt k.isLt⟩ t.isLt)
      (fun j : {j : Fin n // j.val < k.val} => g j.1) (by
        intro t
        dsimp [e, g]
        rw [dif_pos t.isLt])).symm

private lemma p26_forwardSub_backward_row
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P26GammaValid fp.u n) (k : Fin n) :
    let q := p26ForwardSub fp n L b
    ∃ d : Fin n → ℝ,
      (∀ j, |d j| ≤ p26Gamma fp.u n * |L k j|) ∧
      ∑ j : Fin n, (L k j + d j) * q j = b k := by
  let q := p26ForwardSub fp n L b
  let s := Fin.foldl k.val
    (fun acc (t : Fin k.val) =>
      fp.fl_sub acc
        (fp.fl_mul (L k ⟨t.val, by omega⟩)
          (q ⟨t.val, by omega⟩)))
    (b k)
  have hq : q k = fp.fl_div s (L k k) := by
    exact p26_forwardSub_component fp n L b k
  obtain ⟨cs, ca, heq, hcs, hca⟩ :=
    p26_fold_backward fp n k.val (Nat.le_of_lt k.isLt)
      (fun t => L k ⟨t.val, by omega⟩)
      (fun t => q ⟨t.val, by omega⟩) (b k) hvalid
  obtain ⟨eta, heta, hdiv⟩ := fp.model_div s (L k k) (hdiag k)
  have hn : (n : ℝ) * fp.u < 1 := hvalid
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hu_lt : fp.u < 1 := by
    have hnpos : 0 < n := Nat.zero_lt_of_lt k.isLt
    have hone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    nlinarith
  have hetapos : 0 < 1 + eta := by
    have := (abs_le.mp heta).1
    linarith
  let cd := cs / (1 + eta)
  have hcd0 : |cd - 1| ≤ p26Gamma fp.u (k.val + 1) := by
    exact p26_gamma_div_step fp.u n k.val hu hn (by omega) cs eta hcs heta
  have hcd : |cd - 1| ≤ p26Gamma fp.u n :=
    le_trans hcd0 (p26_gamma_mono fp.u n (k.val + 1) hu hn (by omega))
  have hca' : ∀ t, |ca t - 1| ≤ p26Gamma fp.u n := by
    intro t
    exact le_trans (hca t)
      (p26_gamma_mono fp.u n k.val hu hn (Nat.le_of_lt k.isLt))
  let coeff : Fin n → ℝ := fun j =>
    if hj : j < k then ca ⟨j.val, hj⟩
    else if j = k then cd else 1
  let d : Fin n → ℝ := fun j => (coeff j - 1) * L k j
  refine ⟨d, ?_, ?_⟩
  · intro j
    rw [show d j = (coeff j - 1) * L k j by rfl, abs_mul]
    apply mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    by_cases hj : j < k
    · simp only [coeff, hj, ↓reduceDIte]
      exact hca' ⟨j.val, hj⟩
    · by_cases hjk : j = k
      · simp [coeff, hj, hjk]
        exact hcd
      · simp [coeff, hj, hjk]
        exact p26_gamma_nonneg fp.u n hu hn
  · have hdiagterm : cd * L k k * q k = cs * s := by
      rw [hq, hdiv]
      dsimp [cd]
      field_simp [hdiag k, ne_of_gt hetapos]
      <;> ring
    calc
      ∑ j : Fin n, (L k j + d j) * q j =
          ∑ j : Fin n,
            (if hj : j.val < k.val then
              ca ⟨j.val, hj⟩ * L k j * q j
            else if j = k then cd * L k j * q j else 0) := by
              apply Finset.sum_congr rfl
              intro j hjmem
              by_cases hj : j < k
              · have hcoeff : coeff j = ca ⟨j.val, hj⟩ := by simp [coeff, hj]
                rw [show d j = (coeff j - 1) * L k j by rfl, hcoeff]
                have hjv : j.val < k.val := hj
                rw [dif_pos hjv]
                ring
              · by_cases hjk : j = k
                · subst j
                  rw [show d k = (coeff k - 1) * L k k by rfl]
                  have hcoeff : coeff k = cd := by simp [coeff]
                  rw [hcoeff]
                  rw [dif_neg (by omega : ¬k.val < k.val)]
                  simp only [↓reduceIte]
                  ring
                · have hkj : k.val < j.val := by omega
                  have hzero := hlower k j hkj
                  simp [d, coeff, hj, hjk, hzero]
      _ = (∑ j : Fin n,
            if hj : j.val < k.val then
              ca ⟨j.val, hj⟩ * L k j * q j else 0) +
          ∑ j : Fin n, if j = k then cd * L k j * q j else 0 := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro j hjmem
            by_cases hjv : j.val < k.val
            · have hjk : j ≠ k := by
                intro heq
                subst j
                omega
              simp [hjv, hjk]
            · by_cases hjk : j = k
              · subst j
                simp
              · simp [hjv, hjk]
      _ = (∑ t : Fin k.val,
            ca t * L k ⟨t.val, by omega⟩ * q ⟨t.val, by omega⟩) +
          cd * L k k * q k := by
            rw [p26_sum_below_dite]
            simp
      _ = b k := by
            rw [hdiagterm]
            linarith [heq]

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
  let A := p26Residual Q R X
  let c := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hrow : ∀ i, p26VecNorm (A i) ≤ c * p26VecNorm (Q i) := by
    intro i
    have hex : ∀ k : Fin n, ∃ d : Fin n → ℝ,
        (∀ j, |d j| ≤ p26Gamma fp.u n * |p26Transpose R k j|) ∧
        ∑ j : Fin n, (p26Transpose R k j + d j) *
            p26ForwardSub fp n (p26Transpose R) (X i) j = X i k := by
      intro k
      exact p26_forwardSub_backward_row fp n (p26Transpose R) (X i)
        (fun t => by simpa [p26Transpose] using hdiag t)
        (fun t j htj => by simpa [p26Transpose] using hupper j t htj)
        hvalid k
    choose d hd heq using hex
    have hi := hperturb i (fun k j => d k j)
      (fun k j => by simpa [p26Transpose] using hd k j)
      (fun k => by simpa [p26RoundedQ] using heq k)
    simpa [A, Q, c] using hi
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have haggregate : p26FrobNorm A ≤ c * p26FrobNorm Q :=
    p26_frob_row_bound A Q c hc hrow
  have hthroughQ : p26FrobNorm A ≤ c * Real.sqrt (3 * (n : ℝ)) :=
    le_trans haggregate (mul_le_mul_of_nonneg_left hQFrob hc)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  let a := Real.sqrt (n : ℝ)
  let b := Real.sqrt (3 * (n : ℝ))
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = (n : ℝ) := by
    dsimp [a]
    rw [Real.sq_sqrt hn0]
  have hb2 : b ^ 2 = 3 * (n : ℝ) := by
    dsimp [b]
    rw [Real.sq_sqrt (mul_nonneg (by norm_num) hn0)]
  have hab2 : (a * b) ^ 2 = 3 * (n : ℝ) ^ 2 := by
    rw [mul_pow, ha2, hb2]
    ring
  have hconstant : (11 : ℝ) / 10 * a * b ≤ 2 * (n : ℝ) := by
    have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
    nlinarith [sq_nonneg (11 * (a * b) + 20 * (n : ℝ))]
  have hz : 0 ≤ (n : ℝ) * fp.u * xNorm :=
    mul_nonneg (mul_nonneg hn0 fp.u_nonneg) hxNorm
  have hscaled := mul_le_mul_of_nonneg_right hconstant hz
  calc
    p26FrobNorm (p26Residual Q R X) = p26FrobNorm A := rfl
    _ ≤ c * Real.sqrt (3 * (n : ℝ)) := hthroughQ
    _ ≤ 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
      dsimp [c, a, b] at hscaled ⊢
      nlinarith

end HighamBench
