import HighamBench.P15Definitions

namespace HighamBench

private lemma p15_gamma_nonneg {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u n) :
    0 ≤ gamma u n := by
  unfold GammaValid at hvalid
  unfold gamma
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg n) hu) (by linarith)

private lemma p15_u_le_gamma_succ {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1)) :
    u ≤ gamma u (n + 1) := by
  unfold GammaValid at hvalid
  unfold gamma
  have hden : 0 < 1 - ((n + 1 : ℕ) : ℝ) * u := by linarith
  rw [le_div_iff₀ hden]
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hnu : 0 ≤ (((n + 1 : ℕ) : ℝ) * u) :=
    mul_nonneg (by positivity) hu
  calc
    u * (1 - ((n + 1 : ℕ) : ℝ) * u) ≤ u * ((n + 1 : ℕ) : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ hu
      have hone : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by simp
      linarith
    _ = ((n + 1 : ℕ) : ℝ) * u := by ring

private lemma p15_gamma_step {u a d : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1))
    (ha : |a| ≤ gamma u n) (hd : |d| ≤ u) :
    |(1 + a) * (1 + d) - 1| ≤ gamma u (n + 1) := by
  have hprev : GammaValid u n := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  have hg : 0 ≤ gamma u n := p15_gamma_nonneg hu hprev
  have habs : |(1 + a) * (1 + d) - 1| ≤
      gamma u n + u + gamma u n * u := by
    calc
      |(1 + a) * (1 + d) - 1| = |a + d + a * d| := by ring_nf
      _ ≤ |a| + |d| + |a * d| := by
        calc
          |a + d + a * d| ≤ |a + d| + |a * d| := abs_add_le _ _
          _ ≤ |a| + |d| + |a * d| := by gcongr; exact abs_add_le _ _
      _ = |a| + |d| + |a| * |d| := by rw [abs_mul]
      _ ≤ gamma u n + u + gamma u n * u := by nlinarith [mul_le_mul ha hd (abs_nonneg d) hg]
  calc
    |(1 + a) * (1 + d) - 1| ≤ gamma u n + u + gamma u n * u := habs
    _ ≤ gamma u (n + 1) := by
      unfold GammaValid at hvalid
      unfold gamma
      push_cast at hvalid ⊢
      have hden0 : 0 < 1 - (n : ℝ) * u := by nlinarith
      have hden1 : 0 < 1 - ((n : ℝ) + 1) * u := by nlinarith
      have heq :
          (n : ℝ) * u / (1 - (n : ℝ) * u) + u +
              (n : ℝ) * u / (1 - (n : ℝ) * u) * u =
            (((n : ℝ) + 1) * u) / (1 - (n : ℝ) * u) := by
        field_simp
        ring
      rw [heq]
      exact div_le_div₀ (mul_nonneg (by positivity) hu) le_rfl hden1 (by nlinarith)

private lemma p15_gamma_mono_step {u : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1)) :
    gamma u n ≤ gamma u (n + 1) := by
  have hprev : GammaValid u n := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  have hg := p15_gamma_nonneg hu hprev
  have h := p15_gamma_step (n := n) hu hvalid
    (a := gamma u n) (d := 0) (by simpa [abs_of_nonneg hg]) (by simpa using hu)
  simpa [abs_of_nonneg hg] using h

private lemma p15_gamma_mono {u : ℝ} {m n : ℕ}
    (hu : 0 ≤ u) (hmn : m ≤ n) (hvalid : GammaValid u n) :
    gamma u m ≤ gamma u n := by
  unfold GammaValid at hvalid
  unfold gamma
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  have hnum : (m : ℝ) * u ≤ (n : ℝ) * u :=
    mul_le_mul_of_nonneg_right hmn' hu
  have hden : 0 < 1 - (n : ℝ) * u := by linarith
  exact div_le_div₀ (mul_nonneg (Nat.cast_nonneg n) hu) hnum hden (by linarith)

private lemma p15_gamma_div_step {u a d : ℝ} {n : ℕ}
    (hu : 0 ≤ u) (hvalid : GammaValid u (n + 1))
    (ha : |a| ≤ gamma u n) (hd : |d| ≤ u) :
    |(1 + a) / (1 + d) - 1| ≤ gamma u (n + 1) := by
  have hprev : GammaValid u n := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  have hg : 0 ≤ gamma u n := p15_gamma_nonneg hu hprev
  have hu_lt : u < 1 := by
    unfold GammaValid at hvalid
    push_cast at hvalid
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    nlinarith [mul_le_mul_of_nonneg_right hn hu]
  have hdlo : -u ≤ d := (abs_le.mp hd).1
  have hden : 0 < 1 + d := by linarith
  have hnum : |a - d| ≤ gamma u n + u := by
    calc
      |a - d| ≤ |a| + |d| := abs_sub _ _
      _ ≤ gamma u n + u := add_le_add ha hd
  have hratio :
      (gamma u n + u) / (1 - u) ≤ gamma u (n + 1) := by
    unfold GammaValid at hvalid
    unfold gamma
    push_cast at hvalid ⊢
    have hden0 : 0 < 1 - (n : ℝ) * u := by nlinarith
    have hdenu : 0 < 1 - u := by linarith
    have hden1 : 0 < 1 - ((n : ℝ) + 1) * u := by nlinarith
    have htu : 0 ≤ (n : ℝ) * u := mul_nonneg (Nat.cast_nonneg n) hu
    have htuu : 0 ≤ ((n : ℝ) * u) * u := mul_nonneg htu hu
    have heq :
        (((n : ℝ) * u / (1 - (n : ℝ) * u)) + u) / (1 - u) =
          ((n : ℝ) * u + u - (n : ℝ) * u * u) /
            ((1 - (n : ℝ) * u) * (1 - u)) := by
      field_simp
      ring
    rw [heq]
    convert div_le_div₀
      (show 0 ≤ (n : ℝ) * u + u by positivity)
      (show (n : ℝ) * u + u - (n : ℝ) * u * u ≤
          (n : ℝ) * u + u by linarith)
      hden1
      (show 1 - ((n : ℝ) + 1) * u ≤
          (1 - (n : ℝ) * u) * (1 - u) by nlinarith) using 1 <;> ring
  calc
    |(1 + a) / (1 + d) - 1| = |a - d| / (1 + d) := by
      rw [show (1 + a) / (1 + d) - 1 = (a - d) / (1 + d) by
        field_simp
        ring]
      rw [abs_div, abs_of_pos hden]
    _ ≤ (gamma u n + u) / (1 - u) := by
      exact div_le_div₀ (by positivity) hnum (by linarith) (by linarith)
    _ ≤ gamma u (n + 1) := hratio

private lemma p15_rounded_subtractions_backward
    (fp : StandardFPModel) (n : ℕ) (rhs : ℝ) (a x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ e : Fin n → ℝ, ∃ er : ℝ,
      (∀ i, |e i| ≤ gamma fp.u n) ∧
      |er| ≤ gamma fp.u n ∧
      rhs = (∑ i, (a i * x i) * (1 + e i)) +
        Fin.foldl n
          (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) rhs *
            (1 + er) := by
  induction n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, 0, ?_, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [gamma]
      · simp
  | succ n ih =>
      let a' : Fin n → ℝ := fun i ↦ a i.castSucc
      let x' : Fin n → ℝ := fun i ↦ x i.castSucc
      have hvalid' : GammaValid fp.u n := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith
      obtain ⟨e, er, he, her, hexact⟩ := ih a' x' hvalid'
      let sold := Fin.foldl n
        (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a' i) (x' i))) rhs
      let lastTerm := fp.fl_mul (a (Fin.last n)) (x (Fin.last n))
      obtain ⟨dm, hdm, hmuleq⟩ :=
        fp.model_mul (a (Fin.last n)) (x (Fin.last n))
      obtain ⟨ds, hds, hsubeq⟩ := fp.model_sub sold lastTerm
      let lastError := (1 + dm) * (1 + er) - 1
      let residualError := (1 + er) / (1 + ds) - 1
      let e' : Fin (n + 1) → ℝ :=
        Fin.lastCases lastError e
      refine ⟨e', residualError, ?_, ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp only [e', Fin.lastCases_last, lastError]
          simpa [mul_comm] using
            (p15_gamma_step fp.u_nonneg hvalid her hdm)
        · simp only [e', Fin.lastCases_castSucc]
          exact (he j).trans (p15_gamma_mono_step fp.u_nonneg hvalid)
      · simp only [residualError]
        exact p15_gamma_div_step fp.u_nonneg hvalid her hds
      · have hu_lt : fp.u < 1 := by
          unfold GammaValid at hvalid
          push_cast at hvalid
          have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          nlinarith [mul_le_mul_of_nonneg_right hn fp.u_nonneg]
        have hdslo : -fp.u ≤ ds := (abs_le.mp hds).1
        have hden : 1 + ds ≠ 0 := by nlinarith
        have hfold :
            Fin.foldl (n + 1)
                (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) rhs =
              fp.fl_sub sold lastTerm := by
          simp [Fin.foldl_succ_last, sold, lastTerm, a', x']
        have hsolve : sold =
            fp.fl_sub sold lastTerm / (1 + ds) + lastTerm := by
          rw [hsubeq]
          field_simp
          ring
        have hsum :
            (∑ i : Fin (n + 1), (a i * x i) * (1 + e' i)) =
              (∑ i : Fin n, (a' i * x' i) * (1 + e i)) +
                (a (Fin.last n) * x (Fin.last n)) *
                  (1 + lastError) := by
          rw [Fin.sum_univ_castSucc]
          simp only [e', Fin.lastCases_castSucc, Fin.lastCases_last, a', x']
        have hlast : lastTerm =
            (a (Fin.last n) * x (Fin.last n)) * (1 + dm) := by
          simpa [lastTerm] using hmuleq
        have halg : sold * (1 + er) =
            (a (Fin.last n) * x (Fin.last n)) * (1 + lastError) +
              fp.fl_sub sold lastTerm * (1 + residualError) := by
          calc
            sold * (1 + er) =
                (fp.fl_sub sold lastTerm / (1 + ds) + lastTerm) *
                  (1 + er) := congrArg (fun q ↦ q * (1 + er)) hsolve
            _ = _ := by
              rw [hlast]
              simp only [lastError, residualError]
              ring
        calc
          rhs = (∑ i : Fin n, (a' i * x' i) * (1 + e i)) +
              sold * (1 + er) := by simpa [sold] using hexact
          _ = (∑ i : Fin n, (a' i * x' i) * (1 + e i)) +
                (a (Fin.last n) * x (Fin.last n)) *
                    (1 + lastError) +
                  fp.fl_sub sold lastTerm * (1 + residualError) := by
            rw [halg]
            ring
          _ = (∑ i : Fin (n + 1),
                  (a i * x i) * (1 + e' i)) +
                fp.fl_sub sold lastTerm * (1 + residualError) := by
            rw [hsum]
          _ = (∑ i : Fin (n + 1),
                  (a i * x i) * (1 + e' i)) +
                Fin.foldl (n + 1)
                    (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) rhs *
                  (1 + residualError) := by rw [hfold]

private lemma p15_forward_row_backward
    (fp : StandardFPModel) (q : ℕ) (rhs diag : ℝ)
    (a x : Fin q → ℝ) (hdiag : diag ≠ 0)
    (hvalid : GammaValid fp.u (q + 1)) :
    let s := Fin.foldl q
      (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) rhs
    let z := fp.fl_div s diag
    ∃ e : Fin q → ℝ, ∃ ed : ℝ,
      (∀ i, |e i| ≤ gamma fp.u (q + 1)) ∧
      |ed| ≤ gamma fp.u (q + 1) ∧
      rhs = (∑ i, (a i * x i) * (1 + e i)) +
        (diag * z) * (1 + ed) := by
  dsimp only
  have hvalid' : GammaValid fp.u q := by
    unfold GammaValid at hvalid ⊢
    push_cast at hvalid ⊢
    nlinarith
  obtain ⟨e, er, he, her, hacc⟩ :=
    p15_rounded_subtractions_backward fp q rhs a x hvalid'
  let s := Fin.foldl q
    (fun acc i ↦ fp.fl_sub acc (fp.fl_mul (a i) (x i))) rhs
  obtain ⟨dd, hdd, hdiveq⟩ := fp.model_div s diag hdiag
  have hu_lt : fp.u < 1 := by
    unfold GammaValid at hvalid
    push_cast at hvalid
    have hn : (1 : ℝ) ≤ (q : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le q)
    nlinarith [mul_le_mul_of_nonneg_right hn fp.u_nonneg]
  have hddlo : -fp.u ≤ dd := (abs_le.mp hdd).1
  have hddne : 1 + dd ≠ 0 := by nlinarith
  let ed := (1 + er) / (1 + dd) - 1
  refine ⟨e, ed, ?_, ?_, ?_⟩
  · intro i
    exact (he i).trans (p15_gamma_mono_step fp.u_nonneg hvalid)
  · simp only [ed]
    exact p15_gamma_div_step fp.u_nonneg hvalid her hdd
  · have hsolve : s = diag * fp.fl_div s diag / (1 + dd) := by
      rw [hdiveq]
      field_simp
    have halg : s * (1 + er) =
        (diag * fp.fl_div s diag) * (1 + ed) := by
      calc
        s * (1 + er) =
            (diag * fp.fl_div s diag / (1 + dd)) * (1 + er) :=
          congrArg (fun q ↦ q * (1 + er)) hsolve
        _ = _ := by
          simp only [ed]
          ring
    calc
      rhs = (∑ i, (a i * x i) * (1 + e i)) +
          s * (1 + er) := by simpa [s] using hacc
      _ = (∑ i, (a i * x i) * (1 + e i)) +
          (diag * fp.fl_div s diag) * (1 + ed) := by
        rw [halg]
      _ = _ := by simp only [s]

private lemma p15_steps_preserve_before
    (fp : StandardFPModel) {n : ℕ} (L : Fin n → Fin n → ℝ)
    (rhs : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      i.val < n - k →
      roundedForwardSubSteps fp n L rhs k hk x i = x i := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      rfl
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (rhs ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      change roundedForwardSubSteps fp n L rhs k _ x' i = x i
      rw [ih (Nat.le_of_succ_le hk) x' i (by omega)]
      simp only [x', Function.update]
      split
      · rename_i heq
        have hv : i.val = ik.val := congrArg Fin.val heq
        simp only [ik] at hv
        omega
      · rfl

private lemma p15_steps_apply_processed
    (fp : StandardFPModel) {n : ℕ} (L : Fin n → Fin n → ℝ)
    (rhs : Fin n → ℝ) :
    ∀ (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n),
      n - k ≤ i.val →
      let z := roundedForwardSubSteps fp n L rhs k hk x
      z i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) ↦
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨t.val, by omega⟩)
                (z ⟨t.val, by omega⟩)))
          (rhs i))
        (L i i) := by
  intro k
  induction k with
  | zero =>
      intro hk x i hi
      omega
  | succ k ih =>
      intro hk x i hi
      let ik : Fin n := ⟨n - k - 1, by omega⟩
      let s := Fin.foldl (n - k - 1)
        (fun acc (t : Fin (n - k - 1)) ↦
          fp.fl_sub acc
            (fp.fl_mul (L ik ⟨t.val, by omega⟩) (x ⟨t.val, by omega⟩)))
        (rhs ik)
      let x' := Function.update x ik (fp.fl_div s (L ik ik))
      let z := roundedForwardSubSteps fp n L rhs k
        (Nat.le_of_succ_le hk) x'
      change z i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) ↦
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨t.val, by omega⟩)
                (z ⟨t.val, by omega⟩)))
          (rhs i))
        (L i i)
      have hikval : ik.val = n - k - 1 := rfl
      rcases lt_or_eq_of_le hi with hlt | heq
      · have hki : n - k ≤ i.val := by omega
        exact ih (Nat.le_of_succ_le hk) x' i hki
      · have hieq : i = ik := by
          apply Fin.ext
          simp only [ik]
          omega
        have hzprev : ∀ (j : Fin n), j.val < ik.val → z j = x j := by
          intro j hj
          rw [show z j = x' j by
            exact p15_steps_preserve_before fp L rhs k
              (Nat.le_of_succ_le hk) x' j (by simp only [ik] at hj ⊢; omega)]
          simp only [x', Function.update]
          split
          · rename_i hji
            have hv : j.val = ik.val := congrArg Fin.val hji
            omega
          · rfl
        have hzcurrent : z ik = fp.fl_div s (L ik ik) := by
          rw [show z ik = x' ik by
            exact p15_steps_preserve_before fp L rhs k
              (Nat.le_of_succ_le hk) x' ik (by simp only [ik]; omega)]
          simp [x']
        have hcurrent : z ik = fp.fl_div
            (Fin.foldl ik.val
              (fun acc (t : Fin ik.val) ↦
                fp.fl_sub acc
                  (fp.fl_mul (L ik ⟨t.val, by omega⟩)
                    (z ⟨t.val, by omega⟩)))
              (rhs ik))
            (L ik ik) := by
          rw [hzcurrent]
          congr 1
          simp only [ik]
          simp only [s]
          apply congrArg
            (fun f ↦ Fin.foldl (n - k - 1) f (rhs ik))
          funext acc t
          have hjlt : (⟨t.val, by omega⟩ : Fin n).val < ik.val := by
            simp only [ik]
            exact t.isLt
          rw [hzprev ⟨t.val, by omega⟩ hjlt]
        exact hieq.symm ▸ hcurrent

private lemma p15_sum_row_prefix {n : ℕ} (i : Fin n) (f : Fin n → ℝ)
    (hzero : ∀ j, i.val < j.val → f j = 0) :
    (∑ j : Fin n, f j) =
      (∑ t : Fin i.val, f ⟨t.val, by omega⟩) + f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      by_cases hilast : i = Fin.last n
      · have hcast :
            (∑ j : Fin n, f j.castSucc) =
              ∑ t : Fin i.val, f ⟨t.val, by omega⟩ := by
            subst i
            rfl
        rw [hcast]
        congr 1
        exact congrArg f hilast.symm
      · have hilt : i.val < n := by
          have hle : i.val ≤ n := Nat.le_of_lt_succ i.isLt
          have hne : i.val ≠ n := by
            intro heq
            apply hilast
            apply Fin.ext
            simpa using heq
          omega
        let i' : Fin n := ⟨i.val, hilt⟩
        have hlastzero : f (Fin.last n) = 0 :=
          hzero (Fin.last n) (by simp only [Fin.val_last]; omega)
        rw [hlastzero, add_zero]
        have hrec := ih i' (fun j : Fin n ↦ f j.castSucc)
          (fun j hj ↦ hzero j.castSucc (by
            simp only [i'] at hj ⊢
            exact hj))
        simpa only [i'] using hrec

private lemma p15_frob_relative_bound_for_solve {m n : ℕ}
    (A e : P15RectMatrix m n) {g : ℝ} (hg : 0 ≤ g)
    (he : ∀ i j, |e i j| ≤ g) :
    p15RectFrobNorm (fun i j ↦ A i j * e i j) ≤
      g * p15RectFrobNorm A := by
  have hsq :
      (∑ i : Fin m, ∑ j : Fin n, (A i j * e i j) ^ 2) ≤
        g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, g ^ 2 * A i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hesq : (e i j) ^ 2 ≤ g ^ 2 := by
          rw [sq_le_sq]
          simpa [abs_of_nonneg hg] using he i j
        nlinarith [sq_nonneg (A i j)]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  unfold p15RectFrobNorm
  calc
    Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j * e i j) ^ 2) ≤
        Real.sqrt (g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (g ^ 2) *
        Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg g)]
    _ = g * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_sq hg]

private lemma p15_roundedForwardSub_backward
    (fp : StandardFPModel) (n : ℕ) (L : P15Matrix n)
    (rhs : P15Vector n) (hdiag : ∀ i, L i i ≠ 0)
    (hlower : p15LowerTriangular L) (hvalid : GammaValid fp.u n) :
    ∃ E : P15Matrix n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm L ∧
      p15RectMatVec (p15RectAdd L E)
          (roundedForwardSub fp n L rhs) = rhs := by
  classical
  let z := roundedForwardSub fp n L rhs
  have hz : ∀ i : Fin n,
      z i = fp.fl_div
        (Fin.foldl i.val
          (fun acc (t : Fin i.val) ↦
            fp.fl_sub acc
              (fp.fl_mul (L i ⟨t.val, by omega⟩)
                (z ⟨t.val, by omega⟩)))
          (rhs i))
        (L i i) := by
    intro i
    exact p15_steps_apply_processed fp L rhs n (le_refl n)
      (fun _ ↦ 0) i (by omega)
  have hrow : ∀ i : Fin n,
      ∃ e : Fin i.val → ℝ, ∃ ed : ℝ,
        (∀ j, |e j| ≤ gamma fp.u (i.val + 1)) ∧
        |ed| ≤ gamma fp.u (i.val + 1) ∧
        rhs i =
          (∑ j : Fin i.val,
            (L i ⟨j.val, by omega⟩ * z ⟨j.val, by omega⟩) *
              (1 + e j)) +
          (L i i * z i) * (1 + ed) := by
    intro i
    have hvalidi : GammaValid fp.u (i.val + 1) := by
      unfold GammaValid at hvalid ⊢
      have hle : i.val + 1 ≤ n := i.isLt
      have hle' : ((i.val + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle' fp.u_nonneg) hvalid
    obtain ⟨e, ed, he, hed, heq⟩ := p15_forward_row_backward fp i.val
      (rhs i) (L i i)
      (fun j ↦ L i ⟨j.val, by omega⟩)
      (fun j ↦ z ⟨j.val, by omega⟩)
      (hdiag i) hvalidi
    refine ⟨e, ed, he, hed, ?_⟩
    rw [hz i]
    exact heq
  choose e ed he hed heq using hrow
  let rel : P15Matrix n := fun i j ↦
    if h : j.val < i.val then e i ⟨j.val, h⟩
    else if j = i then ed i else 0
  let E : P15Matrix n := fun i j ↦ L i j * rel i j
  have hrel : ∀ i j, |rel i j| ≤ gamma fp.u n := by
    intro i j
    simp only [rel]
    split
    · rename_i hj
      exact (he i ⟨j.val, hj⟩).trans
        (p15_gamma_mono fp.u_nonneg i.isLt hvalid)
    · split
      · exact (hed i).trans
          (p15_gamma_mono fp.u_nonneg i.isLt hvalid)
      · simpa using p15_gamma_nonneg fp.u_nonneg hvalid
  refine ⟨E, ?_, ?_⟩
  · exact p15_frob_relative_bound_for_solve L rel
      (p15_gamma_nonneg fp.u_nonneg hvalid) hrel
  · funext i
    unfold p15RectMatVec p15RectAdd
    have hzero : ∀ j, i.val < j.val →
        (L i j + E i j) * z j = 0 := by
      intro j hj
      have hL := hlower i j hj
      simp [E, hL]
    rw [p15_sum_row_prefix i (fun j ↦ (L i j + E i j) * z j) hzero]
    rw [heq i]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [E, rel]
      rw [dif_pos j.isLt]
      ring
    · simp only [E, rel]
      simp only [dif_neg (lt_irrefl _), ↓reduceIte]
      ring

private lemma p15_roundedDotProduct_backward_succ
    (fp : StandardFPModel) (n : ℕ) (x y : Fin (n + 1) → ℝ)
    (hvalid : GammaValid fp.u (n + 1)) :
    ∃ e : Fin (n + 1) → ℝ,
      (∀ i, |e i| ≤ gamma fp.u (n + 1)) ∧
      roundedDotProduct fp (n + 1) x y =
        ∑ i, (x i * y i) * (1 + e i) := by
  induction n with
  | zero =>
      obtain ⟨d, hd, heq⟩ := fp.model_mul (x 0) (y 0)
      refine ⟨fun _ ↦ d, ?_, ?_⟩
      · intro i
        exact hd.trans (p15_u_le_gamma_succ fp.u_nonneg hvalid)
      · simpa [roundedDotProduct] using heq
  | succ n ih =>
      let x' : Fin (n + 1) → ℝ := fun i ↦ x i.castSucc
      let y' : Fin (n + 1) → ℝ := fun i ↦ y i.castSucc
      have hvalid' : GammaValid fp.u (n + 1) := by
        unfold GammaValid at hvalid ⊢
        push_cast at hvalid ⊢
        nlinarith [fp.u_nonneg]
      obtain ⟨e, he, hdot⟩ := ih x' y' hvalid'
      obtain ⟨dm, hdm, hmuleq⟩ :=
        fp.model_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1)))
      obtain ⟨da, hda, haddeq⟩ := fp.model_add
        (roundedDotProduct fp (n + 1) x' y')
        (fp.fl_mul (x (Fin.last (n + 1))) (y (Fin.last (n + 1))))
      let e' : Fin (n + 2) → ℝ :=
        Fin.lastCases ((1 + dm) * (1 + da) - 1)
          (fun i ↦ (1 + e i) * (1 + da) - 1)
      refine ⟨e', ?_, ?_⟩
      · intro i
        refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simp only [e', Fin.lastCases_last]
          apply p15_gamma_step fp.u_nonneg hvalid
          · exact hdm.trans (p15_u_le_gamma_succ fp.u_nonneg hvalid')
          · exact hda
        · simp only [e', Fin.lastCases_castSucc]
          exact p15_gamma_step fp.u_nonneg hvalid (he j) hda
      · have hrec :
            roundedDotProduct fp (n + 2) x y =
              fp.fl_add (roundedDotProduct fp (n + 1) x' y')
                (fp.fl_mul (x (Fin.last (n + 1)))
                  (y (Fin.last (n + 1)))) := by
            simp [roundedDotProduct, Fin.foldl_succ_last, x', y']
        have hcast :
            (∑ i : Fin (n + 1),
                (x i.castSucc * y i.castSucc) * (1 + e' i.castSucc)) =
              (∑ i : Fin (n + 1), (x' i * y' i) * (1 + e i)) *
                (1 + da) := by
          calc
            _ = ∑ i : Fin (n + 1),
                  ((x' i * y' i) * (1 + e i)) * (1 + da) := by
                apply Finset.sum_congr rfl
                intro i hi
                simp only [e', Fin.lastCases_castSucc, x', y']
                ring
            _ = _ := (Finset.sum_mul ..).symm
        rw [hrec, haddeq, hmuleq, hdot]
        symm
        rw [Fin.sum_univ_castSucc, hcast]
        simp only [e', Fin.lastCases_last]
        ring

private lemma p15_roundedDotProduct_backward
    (fp : StandardFPModel) (n : ℕ) (x y : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ e : Fin n → ℝ,
      (∀ i, |e i| ≤ gamma fp.u n) ∧
      roundedDotProduct fp n x y =
        ∑ i, (x i * y i) * (1 + e i) := by
  cases n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [roundedDotProduct]
  | succ n => exact p15_roundedDotProduct_backward_succ fp n x y hvalid

private lemma p15_frob_relative_bound {m n : ℕ}
    (A e : P15RectMatrix m n) {g : ℝ} (hg : 0 ≤ g)
    (he : ∀ i j, |e i j| ≤ g) :
    p15RectFrobNorm (fun i j ↦ A i j * e i j) ≤
      g * p15RectFrobNorm A := by
  have hsq :
      (∑ i : Fin m, ∑ j : Fin n, (A i j * e i j) ^ 2) ≤
        g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
    calc
      _ ≤ ∑ i : Fin m, ∑ j : Fin n, g ^ 2 * A i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        have hesq : (e i j) ^ 2 ≤ g ^ 2 := by
          rw [sq_le_sq]
          simpa [abs_of_nonneg hg] using he i j
        nlinarith [sq_nonneg (A i j)]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
  unfold p15RectFrobNorm
  calc
    Real.sqrt (∑ i : Fin m, ∑ j : Fin n, (A i j * e i j) ^ 2) ≤
        Real.sqrt (g ^ 2 * (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2)) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (g ^ 2) *
        Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg g)]
    _ = g * Real.sqrt (∑ i : Fin m, ∑ j : Fin n, A i j ^ 2) := by
      rw [Real.sqrt_sq hg]

private lemma p15_roundedRectMatVec_backward
    (fp : StandardFPModel) {m n : ℕ}
    (A : P15RectMatrix m n) (x : Fin n → ℝ)
    (hvalid : GammaValid fp.u n) :
    ∃ E : P15RectMatrix m n,
      p15RectFrobNorm E ≤ gamma fp.u n * p15RectFrobNorm A ∧
      p15RoundedRectMatVec fp A x =
        p15RectMatVec (p15RectAdd A E) x := by
  classical
  have hrow : ∀ i : Fin m,
      ∃ e : Fin n → ℝ,
        (∀ j, |e j| ≤ gamma fp.u n) ∧
        roundedDotProduct fp n (A i) x =
          ∑ j, (A i j * x j) * (1 + e j) :=
    fun i ↦ p15_roundedDotProduct_backward fp n (A i) x hvalid
  choose e he hdot using hrow
  let E : P15RectMatrix m n := fun i j ↦ A i j * e i j
  refine ⟨E, ?_, ?_⟩
  · exact p15_frob_relative_bound A e
      (p15_gamma_nonneg fp.u_nonneg hvalid) he
  · funext i
    rw [show p15RoundedRectMatVec fp A x i =
        roundedDotProduct fp n (A i) x by rfl, hdot i]
    unfold p15RectMatVec p15RectAdd
    apply Finset.sum_congr rfl
    intro j hj
    simp only [E]
    ring

private lemma p15_rectMatVec_mul {m n p : ℕ}
    (A : P15RectMatrix m n) (B : P15RectMatrix n p)
    (x : Fin p → ℝ) :
    p15RectMatVec (p15RectMatMul A B) x =
      p15RectMatVec A (p15RectMatVec B x) := by
  funext i
  unfold p15RectMatVec p15RectMatMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- P15-T2: the two-block instance of equation (4.22) in the proof of
Theorem 4.4, with the source's low-rank and triangular-solve perturbations. -/
theorem p15_t2_two_block_equation_4_22
    {b r : ℕ} (fp : StandardFPModel)
    (T₀ T₁ : P15Matrix b) (X Y : P15RectMatrix b r)
    (v₀ v₁ : P15Vector b)
    (hT₀diag : ∀ i, T₀ i i ≠ 0)
    (hT₁diag : ∀ i, T₁ i i ≠ 0)
    (hT₀lower : p15LowerTriangular T₀)
    (hT₁lower : p15LowerTriangular T₁)
    (hb : GammaValid fp.u b) (hr : GammaValid fp.u r) :
    let x₀ := roundedForwardSub fp b T₀ v₀
    let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
    let wHat := p15RoundedRectMatVec fp X wInner
    let rhsHat := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
    let x₁ := roundedForwardSub fp b T₁ rhsHat
    ∃ ΔT₀ : P15Matrix b, ∃ ΔYT : P15RectMatrix r b,
      ∃ ΔX : P15RectMatrix b r, ∃ θ : P15Vector b,
      ∃ ΔT₁ : P15Matrix b, ∃ ΔT₁₀ : P15Matrix b,
        p15RectFrobNorm ΔT₀ ≤ gamma fp.u b * p15RectFrobNorm T₀ ∧
        p15RectFrobNorm ΔYT ≤
          gamma fp.u b * p15RectFrobNorm (p15RectTranspose Y) ∧
        p15RectFrobNorm ΔX ≤ gamma fp.u r * p15RectFrobNorm X ∧
        (∀ i, |θ i| ≤ fp.u) ∧
        p15RectFrobNorm ΔT₁ ≤ gamma fp.u b * p15RectFrobNorm T₁ ∧
        p15RectMatVec (p15RectAdd T₀ ΔT₀) x₀ = v₀ ∧
        wInner = p15RectMatVec
          (p15RectAdd (p15RectTranspose Y) ΔYT) x₀ ∧
        wHat = p15RectMatVec (p15RectAdd X ΔX) wInner ∧
        (∀ i, rhsHat i = (v₁ i - wHat i) * (1 + θ i)) ∧
        p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ = rhsHat ∧
        (∀ i j,
          p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
            (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j) ∧
        ∀ i,
          p15RectMatVec
                (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i +
              p15RectMatVec (p15RectAdd T₁ ΔT₁) x₁ i =
            v₁ i * (1 + θ i) := by
  -- PROOF_START P15-T2-H001
  dsimp only
  let x₀ := roundedForwardSub fp b T₀ v₀
  let wInner := p15RoundedRectMatVec fp (p15RectTranspose Y) x₀
  let wHat := p15RoundedRectMatVec fp X wInner
  let rhsHat : P15Vector b := fun i ↦ fp.fl_sub (v₁ i) (wHat i)
  let x₁ := roundedForwardSub fp b T₁ rhsHat
  obtain ⟨ΔT₀, hΔT₀, hx₀⟩ :=
    p15_roundedForwardSub_backward fp b T₀ v₀
      hT₀diag hT₀lower hb
  obtain ⟨ΔYT, hΔYT, hwInner⟩ :=
    p15_roundedRectMatVec_backward fp (p15RectTranspose Y) x₀ hb
  obtain ⟨ΔX, hΔX, hwHat⟩ :=
    p15_roundedRectMatVec_backward fp X wInner hr
  have hsub : ∀ i : Fin b, ∃ d : ℝ,
      |d| ≤ fp.u ∧ rhsHat i = (v₁ i - wHat i) * (1 + d) := by
    intro i
    exact fp.model_sub (v₁ i) (wHat i)
  choose θ hθ hθeq using hsub
  obtain ⟨ΔT₁, hΔT₁, hx₁⟩ :=
    p15_roundedForwardSub_backward fp b T₁ rhsHat
      hT₁diag hT₁lower hb
  let ΔT₁₀ : P15Matrix b := fun i j ↦
    (1 + θ i) *
        p15RectMatMul (p15RectAdd X ΔX)
          (p15RectAdd (p15RectTranspose Y) ΔYT) i j -
      p15LowRankMatrix X Y i j
  have hΔT₁₀ : ∀ i j,
      p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀ i j =
        (1 + θ i) *
          p15RectMatMul (p15RectAdd X ΔX)
            (p15RectAdd (p15RectTranspose Y) ΔYT) i j := by
    intro i j
    simp only [p15RectAdd, ΔT₁₀]
    ring
  refine ⟨ΔT₀, ΔYT, ΔX, θ, ΔT₁, ΔT₁₀,
    hΔT₀, hΔYT, hΔX, hθ, hΔT₁, ?_, ?_, ?_, hθeq, ?_, hΔT₁₀, ?_⟩
  · simpa only [x₀] using hx₀
  · simpa only [wInner, x₀] using hwInner
  · simpa only [wHat, wInner] using hwHat
  · simpa only [x₁] using hx₁
  · intro i
    have hprod :
        p15RectMatVec
            (p15RectMatMul (p15RectAdd X ΔX)
              (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i =
          wHat i := by
      rw [p15_rectMatVec_mul]
      rw [← hwInner, ← hwHat]
    have hoff :
        p15RectMatVec
            (p15RectAdd (p15LowRankMatrix X Y) ΔT₁₀) x₀ i =
          (1 + θ i) * wHat i := by
      unfold p15RectMatVec
      simp_rw [hΔT₁₀ i]
      change (∑ j : Fin b,
          (1 + θ i) *
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j * x₀ j) = _
      calc
        _ = (1 + θ i) *
            (∑ j : Fin b,
              p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT) i j * x₀ j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (1 + θ i) * wHat i := by
          change (1 + θ i) *
            p15RectMatVec
              (p15RectMatMul (p15RectAdd X ΔX)
                (p15RectAdd (p15RectTranspose Y) ΔYT)) x₀ i = _
          rw [hprod]
    rw [hoff, hx₁]
    rw [hθeq i]
    ring

end HighamBench
