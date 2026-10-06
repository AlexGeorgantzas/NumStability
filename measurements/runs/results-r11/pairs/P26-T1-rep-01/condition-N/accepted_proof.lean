import HighamBench.P26Definitions

namespace HighamBench

open scoped BigOperators

private lemma gamma_nonneg (u : ℝ) (k : ℕ) (hu : 0 ≤ u)
    (hv : (k : ℝ) * u < 1) :
    0 ≤ p26Gamma u k := by
  unfold p26Gamma
  exact div_nonneg (mul_nonneg (by positivity) hu) (by linarith)

private lemma gamma_mono (u : ℝ) (k l : ℕ) (hu : 0 ≤ u)
    (hkl : k ≤ l) (hv : (l : ℝ) * u < 1) :
    p26Gamma u k ≤ p26Gamma u l := by
  have hk : (k : ℝ) * u < 1 := by
    have hcast : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
    nlinarith
  unfold p26Gamma
  apply (div_le_div_iff₀ (by linarith) (by linarith)).2
  nlinarith [show (k : ℝ) * u ≤ (l : ℝ) * u by
    gcongr]

private lemma gamma_step_div (u a e : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : ((k + 1 : ℕ) : ℝ) * u < 1)
    (ha : |a - 1| ≤ p26Gamma u k) (he : |e| ≤ u) :
    |a / (1 + e) - 1| ≤ p26Gamma u (k + 1) := by
  have hu1 : u < 1 := by
    norm_num at hv ⊢
    have hk0 : (0 : ℝ) ≤ k := by positivity
    nlinarith
  have hden : 0 < 1 + e := by
    have := (abs_le.mp he).1
    linarith
  have hvk : (k : ℝ) * u < 1 := by
    norm_num at hv
    have huk : 0 ≤ (k : ℝ) * u := mul_nonneg (by positivity) hu
    nlinarith
  have hnum : |(a - 1) - e| ≤ p26Gamma u k + u := by
    calc
      |(a - 1) - e| ≤ |a - 1| + |e| := abs_sub _ _
      _ ≤ p26Gamma u k + u := add_le_add ha he
  have hfrac :
      |a / (1 + e) - 1| ≤
        (p26Gamma u k + u) / (1 - u) := by
    rw [show a / (1 + e) - 1 = ((a - 1) - e) / (1 + e) by
      field_simp [ne_of_gt hden]
      <;> ring]
    rw [abs_div, abs_of_pos hden]
    apply (div_le_div_iff₀ hden (by linarith)).2
    have hleft : |(a - 1) - e| * (1 - u) ≤
        (p26Gamma u k + u) * (1 - u) := by
      exact mul_le_mul_of_nonneg_right hnum (by linarith)
    have hdenle : 1 - u ≤ 1 + e := by
      have := (abs_le.mp he).1
      linarith
    have hnonneg : 0 ≤ p26Gamma u k + u :=
      add_nonneg (gamma_nonneg u k hu hvk) hu
    nlinarith
  apply hfrac.trans
  unfold p26Gamma at *
  norm_num at hv ⊢
  have hkden : 0 < 1 - (k : ℝ) * u := by linarith
  have hsden : 0 < 1 - ((k : ℝ) + 1) * u := by linarith
  rw [div_le_div_iff₀ (by linarith : 0 < 1 - u) hsden]
  field_simp [ne_of_gt hkden]
  have hid :
      u * (1 - (k : ℝ) * u) * ((k : ℝ) + 1) * (1 - u) -
          u * ((k : ℝ) + (1 - (k : ℝ) * u)) *
            (1 - u * ((k : ℝ) + 1)) = (k : ℝ) * u ^ 2 := by
    ring
  nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ k) (sq_nonneg u)]

private lemma gamma_step_mul (u a e : ℝ) (k : ℕ)
    (hu : 0 ≤ u) (hv : ((k + 1 : ℕ) : ℝ) * u < 1)
    (ha : |a - 1| ≤ p26Gamma u k) (he : |e| ≤ u) :
    |a * (1 + e) - 1| ≤ p26Gamma u (k + 1) := by
  have hvk : (k : ℝ) * u < 1 := by
    norm_num at hv
    have huk : 0 ≤ (k : ℝ) * u := mul_nonneg (by positivity) hu
    nlinarith
  have habsa : |a| ≤ 1 + p26Gamma u k := by
    calc
      |a| = |(a - 1) + 1| := by ring_nf
      _ ≤ |a - 1| + |(1 : ℝ)| := abs_add_le _ _
      _ ≤ p26Gamma u k + 1 := by norm_num; linarith
      _ = 1 + p26Gamma u k := by ring
  calc
    |a * (1 + e) - 1| = |(a - 1) + a * e| := by ring_nf
    _ ≤ |a - 1| + |a * e| := abs_add_le _ _
    _ = |a - 1| + |a| * |e| := by rw [abs_mul]
    _ ≤ p26Gamma u k + (1 + p26Gamma u k) * u := by
      have hg := gamma_nonneg u k hu hvk
      gcongr
    _ ≤ p26Gamma u (k + 1) := by
      unfold p26Gamma
      norm_num at hv ⊢
      have hkden : 0 < 1 - (k : ℝ) * u := by linarith
      have hsden : 0 < 1 - ((k : ℝ) + 1) * u := by linarith
      have heq :
          (k : ℝ) * u / (1 - (k : ℝ) * u) +
              (1 + (k : ℝ) * u / (1 - (k : ℝ) * u)) * u =
            (((k : ℝ) + 1) * u) / (1 - (k : ℝ) * u) := by
        field_simp [ne_of_gt hkden]
        ring
      rw [heq]
      exact div_le_div_of_nonneg_left (mul_nonneg (by positivity) hu)
        hsden (by nlinarith)

private lemma fold_backward (fp : P26FPModel) (r : ℕ)
    (a x : Fin r → ℝ) (b : ℝ)
    (hv : (r : ℝ) * fp.u < 1) :
    ∃ (alpha : ℝ) (beta : Fin r → ℝ),
      b = alpha *
          Fin.foldl r
            (fun acc j => fp.fl_sub acc (fp.fl_mul (a j) (x j))) b +
          ∑ j : Fin r, beta j * (a j * x j) ∧
      |alpha - 1| ≤ p26Gamma fp.u r ∧
      ∀ j, |beta j - 1| ≤ p26Gamma fp.u r := by
  induction r generalizing b with
  | zero =>
      refine ⟨1, fun j => Fin.elim0 j, ?_, ?_, ?_⟩
      · simp [Fin.foldl_zero]
      · simp [p26Gamma]
      · exact fun j => Fin.elim0 j
  | succ r ih =>
      have hvr : (r : ℝ) * fp.u < 1 := by
        norm_num at hv
        have hru : 0 ≤ (r : ℝ) * fp.u :=
          mul_nonneg (by positivity) fp.u_nonneg
        nlinarith
      let a0 : Fin r → ℝ := fun j => a j.castSucc
      let x0 : Fin r → ℝ := fun j => x j.castSucc
      obtain ⟨alpha, beta, heq, halpha, hbeta⟩ :=
        ih a0 x0 b hvr
      let s0 := Fin.foldl r
        (fun acc j => fp.fl_sub acc (fp.fl_mul (a0 j) (x0 j))) b
      obtain ⟨mu, hmu, hmul⟩ := fp.model_mul (a (Fin.last r)) (x (Fin.last r))
      obtain ⟨sigma, hsigma, hsub⟩ :=
        fp.model_sub s0 (fp.fl_mul (a (Fin.last r)) (x (Fin.last r)))
      have hu_lt : fp.u < 1 := by
        norm_num at hv
        have hru : 0 ≤ (r : ℝ) * fp.u :=
          mul_nonneg (by positivity) fp.u_nonneg
        nlinarith
      have hsigpos : 0 < 1 + sigma := by
        have := (abs_le.mp hsigma).1
        linarith
      let beta' : Fin (r + 1) → ℝ :=
        Fin.lastCases (alpha * (1 + mu)) beta
      refine ⟨alpha / (1 + sigma), beta', ?_, ?_, ?_⟩
      · rw [Fin.foldl_succ_last]
        change b = alpha / (1 + sigma) *
            fp.fl_sub s0 (fp.fl_mul (a (Fin.last r)) (x (Fin.last r))) +
          ∑ j : Fin (r + 1), beta' j * (a j * x j)
        rw [Fin.sum_univ_castSucc]
        simp only [beta', Fin.lastCases_castSucc, Fin.lastCases_last]
        have heq' : b = alpha * s0 +
            ∑ j : Fin r, beta j * (a j.castSucc * x j.castSucc) := by
          simpa [s0, a0, x0] using heq
        rw [hsub, hmul]
        rw [show (∑ j : Fin r, beta j * (a j.castSucc * x j.castSucc)) =
            b - alpha * s0 by linarith [heq']]
        field_simp [ne_of_gt hsigpos]
        ring
      · exact gamma_step_div fp.u alpha sigma r fp.u_nonneg hv halpha hsigma
      · intro j
        refine Fin.lastCases ?_ (fun t => ?_) j
        · simp only [beta', Fin.lastCases_last]
          exact gamma_step_mul fp.u alpha mu r fp.u_nonneg hv halpha hmu
        · simp only [beta', Fin.lastCases_castSucc]
          exact (hbeta t).trans
            (gamma_mono fp.u r (r + 1) fp.u_nonneg (by omega) hv)

private lemma forward_steps_eq_of_lt (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) (i : Fin n)
    (hi : i.val < n - k) :
    p26ForwardSubSteps fp n L b k hk x i = x i := by
  induction k generalizing x with
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
      change p26ForwardSubSteps fp n L b k _ x' i = x i
      rw [ih (Nat.le_of_succ_le hk) x' (by omega)]
      exact Function.update_of_ne (by
        intro heq
        have := congrArg Fin.val heq
        simp only [ik] at this
        omega) _ _

private lemma forward_steps_backward (fp : P26FPModel) (n : ℕ)
    (L : P26Matrix n n) (b : Fin n → ℝ)
    (hdiag : ∀ i, L i i ≠ 0)
    (hlower : ∀ i j : Fin n, i.val < j.val → L i j = 0)
    (hvalid : P26GammaValid fp.u n)
    (k : ℕ) (hk : k ≤ n) (x : Fin n → ℝ) :
    ∃ deltaL : P26Matrix n n,
      (∀ i j, |deltaL i j| ≤ p26Gamma fp.u n * |L i j|) ∧
      ∀ i, n - k ≤ i.val →
        ∑ j : Fin n,
          (L i j + deltaL i j) *
            p26ForwardSubSteps fp n L b k hk x j = b i := by
  classical
  induction k generalizing x with
  | zero =>
      refine ⟨fun _ _ => 0, ?_, ?_⟩
      · intro i j
        have hgamma : 0 ≤ p26Gamma fp.u n :=
          gamma_nonneg fp.u n fp.u_nonneg hvalid
        simpa only [abs_zero] using mul_nonneg hgamma (abs_nonneg (L i j))
      · intro i hi
        omega
  | succ k ih =>
      let i0 : Fin n := ⟨n - k - 1, by omega⟩
      let count := n - k - 1
      let s := Fin.foldl count
        (fun acc (t : Fin count) =>
          fp.fl_sub acc
            (fp.fl_mul (L i0 ⟨t.val, by omega⟩)
              (x ⟨t.val, by omega⟩)))
        (b i0)
      let q := fp.fl_div s (L i0 i0)
      let x' : Fin n → ℝ := Function.update x i0 q
      obtain ⟨oldDelta, holdBound, holdEq⟩ :=
        ih (Nat.le_of_succ_le hk) x'
      have hcount : count = i0.val := by rfl
      have hcount_succ : count + 1 ≤ n := by
        simp only [count]
        omega
      have hvalidCount : (count : ℝ) * fp.u < 1 := by
        have hc : (count : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_trans (by omega : count ≤ count + 1) hcount_succ)
        unfold P26GammaValid at hvalid
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      let avec : Fin count → ℝ := fun t => L i0 ⟨t.val, by omega⟩
      let xvec : Fin count → ℝ := fun t => x ⟨t.val, by omega⟩
      obtain ⟨alpha, beta, hfold, halpha, hbeta⟩ :=
        fold_backward fp count avec xvec (b i0) hvalidCount
      obtain ⟨eta, heta, hdiv⟩ := fp.model_div s (L i0 i0) (hdiag i0)
      have hvalidStep : (((count + 1 : ℕ) : ℝ) * fp.u) < 1 := by
        have hc : ((count + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcount_succ
        unfold P26GammaValid at hvalid
        nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
      have hdiagCoeff :
          |alpha / (1 + eta) - 1| ≤ p26Gamma fp.u n := by
        exact (gamma_step_div fp.u alpha eta count fp.u_nonneg hvalidStep
          halpha heta).trans
          (gamma_mono fp.u (count + 1) n fp.u_nonneg hcount_succ hvalid)
      let rowDelta : Fin n → ℝ := fun j =>
        if hj : j.val < count then
          (beta ⟨j.val, hj⟩ - 1) * L i0 j
        else if j = i0 then
          (alpha / (1 + eta) - 1) * L i0 j
        else 0
      let deltaL : P26Matrix n n := Function.update oldDelta i0 rowDelta
      refine ⟨deltaL, ?_, ?_⟩
      · intro i j
        by_cases hi : i = i0
        · subst i
          rw [show deltaL i0 j = rowDelta j by
            simp [deltaL, Function.update_apply]]
          by_cases hj : j.val < count
          · simp only [rowDelta, dif_pos hj]
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right
              ((hbeta ⟨j.val, hj⟩).trans
                (gamma_mono fp.u count n fp.u_nonneg
                  (le_trans (by omega : count ≤ count + 1) hcount_succ) hvalid))
              (abs_nonneg _)
          · by_cases hji : j = i0
            · simp only [rowDelta, dif_neg hj, if_pos hji]
              rw [abs_mul]
              exact mul_le_mul_of_nonneg_right hdiagCoeff (abs_nonneg _)
            · simp only [rowDelta, dif_neg hj, if_neg hji, abs_zero]
              exact mul_nonneg
                (gamma_nonneg fp.u n fp.u_nonneg hvalid) (abs_nonneg _)
        · rw [show deltaL i j = oldDelta i j by
            change Function.update oldDelta i0 rowDelta i j = oldDelta i j
            rw [Function.update_of_ne hi]]
          exact holdBound i j
      · intro i hi
        by_cases hieq : i = i0
        · subst i
          -- The newly processed row follows from the fold and division models.
          rw [p26ForwardSubSteps]
          change (∑ j : Fin n,
              (L i0 j + deltaL i0 j) *
                p26ForwardSubSteps fp n L b k _ x' j) = b i0
          have hdrow (j : Fin n) : deltaL i0 j = rowDelta j := by
            simp [deltaL]
          simp_rw [hdrow]
          let y := p26ForwardSubSteps fp n L b k
            (Nat.le_of_succ_le hk) x'
          have hy (j : Fin n) (hj : j.val < count + 1) : y j = x' j := by
            exact forward_steps_eq_of_lt fp n L b k
              (Nat.le_of_succ_le hk) x' j (by
                omega)
          have hsum :
              (∑ j : Fin n, (L i0 j + rowDelta j) * y j) =
                (∑ t : Fin count, beta t * (avec t * xvec t)) +
                  (alpha / (1 + eta)) * (L i0 i0 * q) := by
            let F : Fin n → ℝ := fun j => (L i0 j + rowDelta j) * y j
            let lower : Finset (Fin n) := Finset.univ.filter (fun j => j.val < count)
            have hi0val : i0.val = count := by rfl
            have hLowerSum :
                (∑ t : Fin count, beta t * (avec t * xvec t)) =
                  ∑ j ∈ lower, F j := by
              change (∑ t ∈ Finset.univ, beta t * (avec t * xvec t)) =
                ∑ j ∈ lower, F j
              refine Finset.sum_bij
                (fun t _ => (⟨t.val, lt_of_lt_of_le t.isLt
                  (le_trans (by omega : count ≤ count + 1) hcount_succ)⟩ : Fin n))
                ?_ ?_ ?_ ?_
              · intro t ht
                simp [lower, t.isLt]
              · intro t₁ ht₁ t₂ ht₂ he
                apply Fin.ext
                simpa using congrArg (fun z : Fin n => z.val) he
              · intro j hj
                have hjlt : j.val < count := by
                  simpa [lower] using hj
                refine ⟨⟨j.val, hjlt⟩, Finset.mem_univ _, ?_⟩
                apply Fin.ext
                rfl
              · intro t ht
                let j : Fin n := ⟨t.val, lt_of_lt_of_le t.isLt
                  (le_trans (by omega : count ≤ count + 1) hcount_succ)⟩
                have hjlt : j.val < count := t.isLt
                have hjne : j ≠ i0 := by
                  intro he
                  have := congrArg Fin.val he
                  simp only [j, hi0val] at this
                  omega
                have hyj : y j = x j := by
                  rw [hy j (by omega)]
                  exact Function.update_of_ne hjne q x
                simp [F, rowDelta, j, hjlt, hyj, avec, xvec]
                ring
            have hdiagTerm :
                F i0 = (alpha / (1 + eta)) * (L i0 i0 * q) := by
              have hyn : y i0 = q := by
                rw [hy i0 (by omega)]
                simp [x', Function.update_apply]
              simp [F, rowDelta, hi0val, hyn]
              ring
            have hi0not : i0 ∉ lower := by
              simp [lower, hi0val]
            have hrestricted :
                ∑ j ∈ insert i0 lower, F j = ∑ j ∈ (Finset.univ : Finset (Fin n)), F j := by
              apply Finset.sum_subset (by simp)
              intro j hj hjnot
              have hjnotlower : j ∉ lower := by
                intro hmem
                exact hjnot (by simp [hmem])
              have hjne : j ≠ i0 := by
                intro he
                subst j
                exact hjnot (by simp)
              have hjge : count ≤ j.val := by
                simpa [lower] using hjnotlower
              have hjgt : i0.val < j.val := by
                rw [hi0val]
                omega
              have hLzero : L i0 j = 0 := hlower i0 j hjgt
              have hrowzero : rowDelta j = 0 := by
                simp [rowDelta, show ¬j.val < count by omega, hjne]
              simp [F, hLzero, hrowzero]
            calc
              (∑ j, F j) = ∑ j ∈ insert i0 lower, F j := hrestricted.symm
              _ = F i0 + ∑ j ∈ lower, F j := Finset.sum_insert hi0not
              _ = (∑ t : Fin count, beta t * (avec t * xvec t)) +
                    alpha / (1 + eta) * (L i0 i0 * q) := by
                rw [hdiagTerm, ← hLowerSum]
                ring
          change (∑ j : Fin n, (L i0 j + rowDelta j) * y j) = b i0
          rw [hsum]
          have hetaPos : 0 < 1 + eta := by
            have hu_lt : fp.u < 1 := by
              have hc : (1 : ℝ) ≤ (count + 1 : ℕ) := by norm_num
              nlinarith [mul_le_mul_of_nonneg_right hc fp.u_nonneg]
            have := (abs_le.mp heta).1
            linarith
          have hq : q = (s / L i0 i0) * (1 + eta) := by
            exact hdiv
          have hfold' : b i0 = alpha * s +
              ∑ t : Fin count, beta t * (avec t * xvec t) := by
            simpa [s] using hfold
          rw [hq]
          calc
            (∑ x, beta x * (avec x * xvec x)) +
                alpha / (1 + eta) *
                  (L i0 i0 * (s / L i0 i0 * (1 + eta))) =
                (∑ x, beta x * (avec x * xvec x)) + alpha * s := by
              field_simp [ne_of_gt hetaPos, hdiag i0]
              <;> ring
            _ = b i0 := by linarith [hfold']
        · have hirange : n - k ≤ i.val := by
            simp only [i0] at hieq
            omega
          have heq := holdEq i hirange
          rw [show deltaL i = oldDelta i by
            change Function.update oldDelta i0 rowDelta i = oldDelta i
            exact Function.update_of_ne hieq rowDelta oldDelta]
          exact heq

private lemma vecNormSq_nonneg {n : ℕ} (v : Fin n → ℝ) :
    0 ≤ p26VecNormSq v := by
  unfold p26VecNormSq
  positivity

private lemma frobNormSq_nonneg {m n : ℕ} (A : P26Matrix m n) :
    0 ≤ p26FrobNormSq A := by
  unfold p26FrobNormSq
  exact Finset.sum_nonneg fun i _ => vecNormSq_nonneg (A i)

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
  let c : ℝ := (11 : ℝ) / 10 * (n : ℝ) * Real.sqrt n * fp.u * xNorm
  have hc : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (by positivity)) (Real.sqrt_nonneg _))
        fp.u_nonneg)
      hxNorm
  have hlower : ∀ i j : Fin n,
      i.val < j.val → p26Transpose R i j = 0 := by
    intro i j hij
    exact hupper j i hij
  have hdiagT : ∀ i, p26Transpose R i i ≠ 0 := by
    intro i
    exact hdiag i
  have hrow (i : Fin m) :
      p26VecNorm (E i) ≤ c * p26VecNorm (Q i) := by
    obtain ⟨deltaL, hdeltaBound, hdeltaEq⟩ :=
      forward_steps_backward fp n (p26Transpose R) (X i)
        hdiagT hlower hvalid n (le_refl n) (fun _ => 0)
    apply hperturb i deltaL
    · intro k j
      simpa [p26Transpose] using hdeltaBound k j
    · intro k
      have heq := hdeltaEq k (by omega)
      simpa [Q, p26RoundedQ, p26ForwardSub] using heq
  have hrowSq (i : Fin m) :
      p26VecNormSq (E i) ≤ c ^ 2 * p26VecNormSq (Q i) := by
    have hnormE : 0 ≤ p26VecNorm (E i) := by
      unfold p26VecNorm
      positivity
    have hnormQ : 0 ≤ p26VecNorm (Q i) := by
      unfold p26VecNorm
      positivity
    have hsquare := (sq_le_sq₀ hnormE (mul_nonneg hc hnormQ)).2 (hrow i)
    unfold p26VecNorm at hsquare
    rw [Real.sq_sqrt (vecNormSq_nonneg (E i))] at hsquare
    calc
      p26VecNormSq (E i) ≤ (c * Real.sqrt (p26VecNormSq (Q i))) ^ 2 := hsquare
      _ = c ^ 2 * p26VecNormSq (Q i) := by
        rw [mul_pow, Real.sq_sqrt (vecNormSq_nonneg (Q i))]
  have hsumSq : p26FrobNormSq E ≤ c ^ 2 * p26FrobNormSq Q := by
    unfold p26FrobNormSq
    calc
      (∑ i : Fin m, p26VecNormSq (E i)) ≤
          ∑ i : Fin m, c ^ 2 * p26VecNormSq (Q i) := by
        exact Finset.sum_le_sum fun i _ => hrowSq i
      _ = c ^ 2 * ∑ i : Fin m, p26VecNormSq (Q i) := by
        rw [Finset.mul_sum]
  have hFrob : p26FrobNorm E ≤ c * p26FrobNorm Q := by
    unfold p26FrobNorm
    calc
      Real.sqrt (p26FrobNormSq E) ≤
          Real.sqrt (c ^ 2 * p26FrobNormSq Q) :=
        Real.sqrt_le_sqrt hsumSq
      _ = c * Real.sqrt (p26FrobNormSq Q) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs,
          abs_of_nonneg hc]
  have hwithQ : p26FrobNorm E ≤ c * Real.sqrt (3 * (n : ℝ)) := by
    exact hFrob.trans (mul_le_mul_of_nonneg_left hQFrob hc)
  have hsqrt3 : Real.sqrt (3 : ℝ) ≤ (20 : ℝ) / 11 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hconstant : c * Real.sqrt (3 * (n : ℝ)) ≤
      2 * (n : ℝ) ^ 2 * fp.u * xNorm := by
    have hn : 0 ≤ (n : ℝ) := by positivity
    have hscale : 0 ≤ (n : ℝ) ^ 2 * fp.u * xNorm :=
      mul_nonneg (mul_nonneg (sq_nonneg _) fp.u_nonneg) hxNorm
    calc
      c * Real.sqrt (3 * (n : ℝ)) =
          ((11 : ℝ) / 10 * Real.sqrt 3) *
            ((n : ℝ) ^ 2 * fp.u * xNorm) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
        calc
          c * (Real.sqrt 3 * Real.sqrt (n : ℝ)) =
              ((11 : ℝ) / 10 * Real.sqrt 3) *
                ((n : ℝ) * Real.sqrt (n : ℝ) ^ 2 * fp.u * xNorm) := by
            dsimp [c]
            ring
          _ = ((11 : ℝ) / 10 * Real.sqrt 3) *
                ((n : ℝ) ^ 2 * fp.u * xNorm) := by
            rw [Real.sq_sqrt hn]
            ring
      _ ≤ 2 * ((n : ℝ) ^ 2 * fp.u * xNorm) := by
        apply mul_le_mul_of_nonneg_right _ hscale
        nlinarith [hsqrt3]
      _ = 2 * (n : ℝ) ^ 2 * fp.u * xNorm := by ring
  exact hwithQ.trans hconstant

end HighamBench
