import HighamBench.P26Definitions

namespace HighamBench

open scoped BigOperators

lemma p26FinFoldl_congr {A : Sort*} (c : ℕ)
    (f g : A → Fin c → A) (a : A)
    (h : ∀ x i, f x i = g x i) :
    Fin.foldl c f a = Fin.foldl c g a := by
  congr 1
  funext x i
  exact h x i

lemma p26FinSum_prefix {n : ℕ} (f : Fin n → ℝ) (k : Fin n)
    (hz : ∀ j : Fin n, k.val < j.val → f j = 0) :
    ∑ j : Fin n, f j =
      (∑ j : Fin k.val, f ⟨j.val, by omega⟩) + f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
      by_cases hk : k = Fin.last n
      · subst k
        simpa using Fin.sum_univ_castSucc f
      · have hklt : k.val < n := by
          have hkle : k.val ≤ n := Nat.le_of_lt_succ k.isLt
          have hkne : k.val ≠ n := by
            intro h
            apply hk
            apply Fin.ext
            simpa using h
          omega
        let k' : Fin n := ⟨k.val, hklt⟩
        have hkeq : k'.castSucc = k := Fin.ext rfl
        rw [← hkeq, Fin.sum_univ_castSucc]
        have hlast : f (Fin.last n) = 0 := hz (Fin.last n) (by simp [k']; omega)
        rw [hlast, add_zero]
        have hrec := ih (fun j : Fin n => f j.castSucc) k'
          (fun j hj => hz j.castSucc (by simpa [k'] using hj))
        simpa [k'] using hrec

lemma p26ForwardSubSteps_eq_of_lt
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (j : Fin n) (hj : j.val < n - k) :
    p26ForwardSubSteps fp n L b k hk x j = x j := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
      rw [p26ForwardSubSteps]
      have hk' : k ≤ n := Nat.le_of_succ_le hk
      have hj' : j.val < n - k := by omega
      rw [ih hk' _ hj']
      rw [Function.update_of_ne]
      intro heq
      have hv : j.val = n - k - 1 := congrArg Fin.val heq
      omega

lemma p26ForwardSubSteps_spec
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n)
    (b : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ)
    (r : Fin n) (hr : n - k ≤ r.val) :
    let y := p26ForwardSubSteps fp n L b k hk x
    y r = fp.fl_div
      (Fin.foldl r.val
        (fun acc (t : Fin r.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L r ⟨t.val, by omega⟩) (y ⟨t.val, by omega⟩)))
        (b r))
      (L r r) := by
  induction k generalizing x with
  | zero => omega
  | succ k ih =>
      rw [p26ForwardSubSteps]
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) =>
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b ik)
      let x' : Fin n → ℝ := Function.update x ik (fp.fl_div s (L ik ik))
      let y := p26ForwardSubSteps fp n L b k (Nat.le_of_succ_le hk) x'
      change y r = _
      by_cases hre : r = ik
      · rw [hre]
        have hyik : y ik = x' ik := by
          apply p26ForwardSubSteps_eq_of_lt
          simp [ik]
          omega
        rw [hyik]
        simp only [x', Function.update_self]
        congr 2
        dsimp only [s]
        change Fin.foldl (n - k - 1) _ (b ik) =
          Fin.foldl (n - k - 1) _ (b ik)
        apply p26FinFoldl_congr
        intro acc t
        congr 2
        have hyt : y ⟨t.val, by omega⟩ = x ⟨t.val, by omega⟩ := by
          dsimp only [y]
          rw [p26ForwardSubSteps_eq_of_lt]
          · dsimp only [x']
            rw [Function.update_of_ne]
            intro heq
            have hv := congrArg Fin.val heq
            simp [ik] at hv
            omega
          · simp [ik]
            omega
        exact hyt.symm
      · apply ih (Nat.le_of_succ_le hk) x'
        have hr' : n - (k + 1) = ik.val := by simp [ik]; omega
        rw [hr'] at hr
        have : ik.val < r.val := by
          have hne : ik.val ≠ r.val := by
            intro h
            apply hre
            exact Fin.ext h.symm
          omega
        simp [ik]
        omega

lemma p26Gamma_mul_step (u t a e : ℝ)
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hnext : (t + 1) * u < 1)
    (ha : |a - 1| ≤ t * u / (1 - t * u)) (he : |e| ≤ u) :
    |a * (1 + e) - 1| ≤ (t + 1) * u / (1 - (t + 1) * u) := by
  have htu : t * u < 1 := by nlinarith
  have hden : 0 < 1 - t * u := by linarith
  have hden' : 0 < 1 - (t + 1) * u := by linarith
  have hone : |1 + e| ≤ 1 + u := by
    calc
      |1 + e| ≤ |(1 : ℝ)| + |e| := abs_add_le _ _
      _ ≤ 1 + u := by simpa using add_le_add_left he 1
  calc
    |a * (1 + e) - 1| = |(a - 1) * (1 + e) + e| := by ring_nf
    _ ≤ |a - 1| * |1 + e| + |e| := by
      simpa [abs_mul] using abs_add_le ((a - 1) * (1 + e)) e
    _ ≤ (t * u / (1 - t * u)) * (1 + u) + u := by gcongr
    _ ≤ (t + 1) * u / (1 - (t + 1) * u) := by
      rw [show (t * u / (1 - t * u)) * (1 + u) + u =
          (t + 1) * u / (1 - t * u) by
        field_simp
        ring]
      exact div_le_div₀ (by positivity) le_rfl hden' (by nlinarith)

lemma p26Gamma_mono (u a b : ℝ)
    (hu : 0 ≤ u) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b * u < 1) :
    a * u / (1 - a * u) ≤ b * u / (1 - b * u) := by
  have hdenb : 0 < 1 - b * u := by linarith
  have hdena : 0 < 1 - a * u := by
    have : a * u ≤ b * u := mul_le_mul_of_nonneg_right hab hu
    linarith
  apply div_le_div₀ (mul_nonneg (by linarith) hu)
    (mul_le_mul_of_nonneg_right hab hu) hdenb
  nlinarith [mul_le_mul_of_nonneg_right hab hu]

lemma p26Gamma_div_step (u t a e : ℝ)
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hnext : (t + 1) * u < 1)
    (ha : |a - 1| ≤ t * u / (1 - t * u)) (he : |e| ≤ u) :
    1 + e ≠ 0 ∧
      |a / (1 + e) - 1| ≤ (t + 1) * u / (1 - (t + 1) * u) := by
  have hu1 : u < 1 := by nlinarith
  have he_lower : -u ≤ e := (abs_le.mp he).1
  have he_pos : 0 < 1 + e := by linarith
  have htu : t * u < 1 := by nlinarith
  have hden : 0 < 1 - t * u := by linarith
  have hden' : 0 < 1 - (t + 1) * u := by linarith
  refine ⟨ne_of_gt he_pos, ?_⟩
  rw [show a / (1 + e) - 1 = (a - 1 - e) / (1 + e) by
    field_simp; ring]
  rw [abs_div, abs_of_pos he_pos]
  apply (div_le_iff₀ he_pos).2
  calc
    |a - 1 - e| ≤ |a - 1| + |e| := by
      simpa [sub_eq_add_neg] using abs_add_le (a - 1) (-e)
    _ ≤ t * u / (1 - t * u) + u := add_le_add ha he
    _ ≤ ((t + 1) * u / (1 - (t + 1) * u)) * (1 + e) := by
      have hcore : t * u / (1 - t * u) + u ≤
          ((t + 1) * u / (1 - (t + 1) * u)) * (1 - u) := by
        rw [show t * u / (1 - t * u) + u =
            ((t + 1) * u - t * u ^ 2) / (1 - t * u) by
          field_simp
          ring]
        rw [show ((t + 1) * u / (1 - (t + 1) * u)) * (1 - u) =
            ((t + 1) * u * (1 - u)) / (1 - (t + 1) * u) by ring]
        rw [div_le_div_iff₀ hden hden']
        have htu2 : 0 ≤ t * u ^ 2 := mul_nonneg ht (sq_nonneg u)
        nlinarith
      calc
        t * u / (1 - t * u) + u
            ≤ ((t + 1) * u / (1 - (t + 1) * u)) * (1 - u) := hcore
        _ ≤ ((t + 1) * u / (1 - (t + 1) * u)) * (1 + e) := by
          have hg : 0 ≤ (t + 1) * u / (1 - (t + 1) * u) := by positivity
          gcongr
          linarith

lemma p26RoundedFold_backward
    (fp : P26FPModel) (c : ℕ) (v w : Fin c → ℝ) (b : ℝ)
    (hc : (c : ℝ) * fp.u < 1) :
    ∃ (theta : Fin c → ℝ) (rho : ℝ),
      b = ∑ j : Fin c, theta j * (v j * w j) +
          rho * Fin.foldl c
            (fun acc j => fp.fl_sub acc (fp.fl_mul (v j) (w j))) b ∧
      (∀ j, |theta j - 1| ≤
        (c : ℝ) * fp.u / (1 - (c : ℝ) * fp.u)) ∧
      |rho - 1| ≤ (c : ℝ) * fp.u / (1 - (c : ℝ) * fp.u) := by
  induction c with
  | zero =>
      refine ⟨fun j => Fin.elim0 j, 1, ?_, ?_, ?_⟩
      · simp
      · intro j
        exact Fin.elim0 j
      · simp
  | succ c ih =>
      let v0 : Fin c → ℝ := fun j => v j.castSucc
      let w0 : Fin c → ℝ := fun j => w j.castSucc
      let prev := Fin.foldl c
        (fun acc j => fp.fl_sub acc (fp.fl_mul (v0 j) (w0 j))) b
      let p := fp.fl_mul (v (Fin.last c)) (w (Fin.last c))
      have hc0 : (c : ℝ) * fp.u < 1 := by
        have hu := fp.u_nonneg
        norm_num [Nat.cast_succ] at hc ⊢
        nlinarith
      obtain ⟨theta0, rho0, hrepr, htheta0, hrho0⟩ := ih v0 w0 hc0
      obtain ⟨dm, hdm, hp⟩ := fp.model_mul (v (Fin.last c)) (w (Fin.last c))
      obtain ⟨ds, hds, hs⟩ := fp.model_sub prev p
      have hnext : ((c : ℝ) + 1) * fp.u < 1 := by
        norm_num [Nat.cast_succ] at hc ⊢
        exact hc
      have hrhoStep := p26Gamma_div_step fp.u (c : ℝ) rho0 ds
        fp.u_nonneg (by positivity) hnext hrho0 hds
      have hdsne : 1 + ds ≠ 0 := hrhoStep.1
      have hfold :
          Fin.foldl (c + 1)
              (fun acc j => fp.fl_sub acc (fp.fl_mul (v j) (w j))) b =
            fp.fl_sub prev p := by
        rw [Fin.foldl_succ_last]
      have hprev : prev =
          (v (Fin.last c) * w (Fin.last c)) * (1 + dm) +
            fp.fl_sub prev p / (1 + ds) := by
        have hsdiv : fp.fl_sub prev p / (1 + ds) = prev - p := by
          rw [hs]
          field_simp
        have hp' : p = (v (Fin.last c) * w (Fin.last c)) * (1 + dm) := by
          simpa only [p] using hp
        rw [hsdiv, hp']
        ring
      let theta : Fin (c + 1) → ℝ :=
        Fin.lastCases (rho0 * (1 + dm)) theta0
      refine ⟨theta, rho0 / (1 + ds), ?_, ?_, ?_⟩
      · rw [hfold, Fin.sum_univ_castSucc]
        simp only [theta, Fin.lastCases_castSucc, Fin.lastCases_last]
        calc
          b = ∑ j : Fin c, theta0 j * (v0 j * w0 j) + rho0 * prev := hrepr
          _ = (∑ j : Fin c, theta0 j * (v j.castSucc * w j.castSucc)) +
                rho0 * ((v (Fin.last c) * w (Fin.last c)) * (1 + dm) +
                  fp.fl_sub prev p / (1 + ds)) := by
                    simpa only [v0, w0] using congrArg
                      (fun z => (∑ j : Fin c,
                        theta0 j * (v j.castSucc * w j.castSucc)) + rho0 * z) hprev
          _ = (∑ j : Fin c, theta0 j * (v j.castSucc * w j.castSucc)) +
                rho0 * (1 + dm) * (v (Fin.last c) * w (Fin.last c)) +
                rho0 / (1 + ds) * fp.fl_sub prev p := by
                  field_simp
                  ring
      · intro j
        refine Fin.lastCases ?_ (fun j0 => ?_) j
        · simp only [theta, Fin.lastCases_last]
          simpa only [Nat.cast_succ] using
            p26Gamma_mul_step fp.u (c : ℝ) rho0 dm fp.u_nonneg
              (by positivity) hnext hrho0 hdm
        · simp only [theta, Fin.lastCases_castSucc]
          simpa only [Nat.cast_succ, mul_one, add_zero] using
            p26Gamma_mul_step fp.u (c : ℝ) (theta0 j0) 0 fp.u_nonneg
              (by positivity) hnext (htheta0 j0) (by simpa using fp.u_nonneg)
      · simpa only [Nat.cast_succ] using hrhoStep.2

lemma p26ForwardSub_row_backward
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P26GammaValid fp.u n) (k : Fin n) :
    let q := p26ForwardSub fp n L b
    ∃ d : Fin n → ℝ,
      (∀ j, |d j| ≤ p26Gamma fp.u n * |L k j|) ∧
      ∑ j : Fin n, (L k j + d j) * q j = b k := by
  classical
  let q := p26ForwardSub fp n L b
  have hspec : q k = fp.fl_div
      (Fin.foldl k.val
        (fun acc (t : Fin k.val) =>
          fp.fl_sub acc
            (fp.fl_mul (L k ⟨t.val, by omega⟩) (q ⟨t.val, by omega⟩)))
        (b k))
      (L k k) := by
    simpa only [q, p26ForwardSub] using
      p26ForwardSubSteps_spec fp n L b n (le_refl n) (fun _ => 0) k (by simp)
  let v : Fin k.val → ℝ := fun j => L k ⟨j.val, by omega⟩
  let w : Fin k.val → ℝ := fun j => q ⟨j.val, by omega⟩
  let s := Fin.foldl k.val
    (fun acc j => fp.fl_sub acc (fp.fl_mul (v j) (w j))) (b k)
  have hspec' : q k = fp.fl_div s (L k k) := by
    simpa only [s, v, w] using hspec
  have hkvalid : (k.val : ℝ) * fp.u < 1 := by
    have hkn : (k.val : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.le_of_lt k.isLt
    have hmul := mul_le_mul_of_nonneg_right hkn fp.u_nonneg
    unfold P26GammaValid at hvalid
    linarith
  obtain ⟨theta, rho, hrepr, htheta, hrho⟩ :=
    p26RoundedFold_backward fp k.val v w (b k) hkvalid
  obtain ⟨dd, hdd, hd⟩ := fp.model_div s (L k k) (hdiag k)
  have hq : q k = (s / L k k) * (1 + dd) := hspec'.trans hd
  have hk1valid : ((k.val : ℝ) + 1) * fp.u < 1 := by
    have hk1n : (k.val : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast k.isLt
    have hmul := mul_le_mul_of_nonneg_right hk1n fp.u_nonneg
    unfold P26GammaValid at hvalid
    linarith
  have hdiagStep := p26Gamma_div_step fp.u (k.val : ℝ) rho dd
    fp.u_nonneg (by positivity) hk1valid hrho hdd
  have hddne : 1 + dd ≠ 0 := hdiagStep.1
  let thetaDiag := rho / (1 + dd)
  have hs_q : s = L k k * q k / (1 + dd) := by
    symm
    rw [hq]
    field_simp [hdiag k]
  have hrow : b k =
      (∑ j : Fin k.val, theta j *
        (L k ⟨j.val, by omega⟩ * q ⟨j.val, by omega⟩)) +
        thetaDiag * (L k k * q k) := by
    calc
      b k = ∑ j : Fin k.val, theta j * (v j * w j) + rho * s := hrepr
      _ = (∑ j : Fin k.val, theta j *
            (L k ⟨j.val, by omega⟩ * q ⟨j.val, by omega⟩)) +
            thetaDiag * (L k k * q k) := by
          rw [hs_q]
          dsimp only [v, w, thetaDiag]
          field_simp
  have hgamma0 : 0 ≤ p26Gamma fp.u n := by
    unfold P26GammaValid at hvalid
    unfold p26Gamma
    have hden : 0 < 1 - (n : ℝ) * fp.u := by linarith
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) fp.u_nonneg) (le_of_lt hden)
  have hgammaTheta : ∀ j : Fin k.val,
      |theta j - 1| ≤ p26Gamma fp.u n := by
    intro j
    apply (htheta j).trans
    unfold P26GammaValid at hvalid
    unfold p26Gamma
    apply p26Gamma_mono fp.u (k.val : ℝ) (n : ℝ)
        fp.u_nonneg (by positivity)
    · exact_mod_cast Nat.le_of_lt k.isLt
    · exact hvalid
  have hgammaDiag : |thetaDiag - 1| ≤ p26Gamma fp.u n := by
    apply hdiagStep.2.trans
    unfold P26GammaValid at hvalid
    unfold p26Gamma
    apply p26Gamma_mono fp.u ((k.val : ℝ) + 1) (n : ℝ)
        fp.u_nonneg (by positivity)
    · exact_mod_cast k.isLt
    · exact hvalid
  let d : Fin n → ℝ := fun j =>
    if hj : j.val < k.val then
      (theta ⟨j.val, hj⟩ - 1) * L k j
    else if j = k then
      (thetaDiag - 1) * L k j
    else 0
  refine ⟨d, ?_, ?_⟩
  · intro j
    by_cases hj : j.val < k.val
    · simp only [d, hj, dite_true, abs_mul]
      exact mul_le_mul_of_nonneg_right (hgammaTheta ⟨j.val, hj⟩) (abs_nonneg _)
    · by_cases hjk : j = k
      · subst j
        simp only [d]
        simp only [lt_self_iff_false, dite_false, ↓reduceIte, abs_mul]
        exact mul_le_mul_of_nonneg_right hgammaDiag (abs_nonneg _)
      · simp only [d, hj, dite_false, hjk, if_false, abs_zero]
        exact mul_nonneg hgamma0 (abs_nonneg _)
  · rw [p26FinSum_prefix (fun j => (L k j + d j) * q j) k]
    · calc
        (∑ j : Fin k.val,
            (L k ⟨j.val, by omega⟩ + d ⟨j.val, by omega⟩) *
              q ⟨j.val, by omega⟩) + (L k k + d k) * q k =
            (∑ j : Fin k.val, theta j *
              (L k ⟨j.val, by omega⟩ * q ⟨j.val, by omega⟩)) +
              thetaDiag * (L k k * q k) := by
                congr 1
                · apply Finset.sum_congr rfl
                  intro j hjmem
                  simp only [d]
                  have hjlt : j.val < k.val := j.isLt
                  simp only [hjlt, dite_true]
                  ring
                · simp only [d]
                  simp
                  ring
        _ = b k := hrow.symm
    · intro j hkj
      have hnot : ¬j.val < k.val := by omega
      have hne : j ≠ k := by
        intro heq
        subst j
        omega
      have hL : L k j = 0 := hlower k j hkj
      simp [d, hnot, hne, hL]

lemma p26ForwardSub_backward
    (fp : P26FPModel) (n : ℕ) (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P26GammaValid fp.u n) :
    ∃ deltaL : P26Matrix n n,
      (∀ k j, |deltaL k j| ≤ p26Gamma fp.u n * |L k j|) ∧
      (∀ k, ∑ j : Fin n,
        (L k j + deltaL k j) * p26ForwardSub fp n L b j = b k) := by
  classical
  have hr := fun k =>
    p26ForwardSub_row_backward fp n L b hdiag hlower hvalid k
  choose d hdbound hdeq using hr
  refine ⟨fun k j => d k j, ?_, ?_⟩
  · intro k j
    exact hdbound k j
  · intro k
    exact hdeq k

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
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hrow : ∀ i : Fin m,
      p26VecNorm (E i) ≤ C * p26VecNorm (Q i) := by
    intro i
    have hdiagT : ∀ k, p26Transpose R k k ≠ 0 := by
      intro k
      simpa only [p26Transpose] using hdiag k
    have hlowerT : ∀ k j : Fin n,
        k.val < j.val → p26Transpose R k j = 0 := by
      intro k j hkj
      simpa only [p26Transpose] using hupper j k hkj
    obtain ⟨deltaL, hdelta, heq⟩ :=
      p26ForwardSub_backward fp n (p26Transpose R) (X i)
        hdiagT hlowerT hvalid
    have hp := hperturb i deltaL
    have hp' := hp (by
      intro k j
      simpa only [p26Transpose] using hdelta k j) (by
      intro k
      simpa only [p26RoundedQ] using heq k)
    simpa only [Q, E, C] using hp'
  have hsum : p26FrobNormSq E ≤ C ^ 2 * p26FrobNormSq Q := by
    unfold p26FrobNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hEi : 0 ≤ p26VecNormSq (E i) := by
      unfold p26VecNormSq
      positivity
    have hQi : 0 ≤ p26VecNormSq (Q i) := by
      unfold p26VecNormSq
      positivity
    have hsquare := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).2
      (hrow i)
    unfold p26VecNorm at hsquare
    rw [Real.sq_sqrt hEi, mul_pow, Real.sq_sqrt hQi] at hsquare
    exact hsquare
  have hFrob : p26FrobNorm E ≤ C * p26FrobNorm Q := by
    unfold p26FrobNorm
    calc
      Real.sqrt (p26FrobNormSq E) ≤
          Real.sqrt (C ^ 2 * p26FrobNormSq Q) := Real.sqrt_le_sqrt hsum
      _ = C * Real.sqrt (p26FrobNormSq Q) := by
        rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq_eq_abs, abs_of_nonneg hC]
  have hfirst : p26FrobNorm E ≤ C * Real.sqrt (3 * (n : ℝ)) := by
    calc
      p26FrobNorm E ≤ C * p26FrobNorm Q := hFrob
      _ ≤ C * Real.sqrt (3 * (n : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [Q] using hQFrob
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsqrtprod : Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) =
      Real.sqrt 3 * (n : ℝ) := by
    calc
      Real.sqrt (n : ℝ) * Real.sqrt (3 * (n : ℝ)) =
          Real.sqrt (n : ℝ) * (Real.sqrt 3 * Real.sqrt (n : ℝ)) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ = Real.sqrt 3 * (Real.sqrt (n : ℝ)) ^ 2 := by ring
      _ = Real.sqrt 3 * (n : ℝ) := by rw [Real.sq_sqrt hn]
  have hcoef : (11 : ℝ) / 10 * Real.sqrt 3 ≤ 2 := by
    have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
    have hs3non := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  have hnumeric : C * Real.sqrt (3 * (n : ℝ)) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    calc
      C * Real.sqrt (3 * (n : ℝ)) =
          ((11 : ℝ) / 10 * Real.sqrt 3) *
            ((n : ℝ) ^ 2 * fp.u * xNorm) := by
              dsimp only [C]
              calc
                (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm *
                    Real.sqrt (3 * (n : ℝ)) =
                    (11 : ℝ) / 10 * (n : ℝ) *
                      (Real.sqrt n * Real.sqrt (3 * (n : ℝ))) * fp.u * xNorm := by ring
                _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
                    ((n : ℝ) ^ 2 * fp.u * xNorm) := by rw [hsqrtprod]; ring
      _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) := by
        apply mul_le_mul_of_nonneg_right hcoef
        exact mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
      _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring
  simpa only [E, Q] using hfirst.trans hnumeric

end HighamBench
