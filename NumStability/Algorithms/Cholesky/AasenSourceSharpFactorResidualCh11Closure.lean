-- Algorithms/Cholesky/AasenSourceSharpFactorResidualCh11Closure.lean
--
-- Higham, 2nd ed., p. 224, proof of Theorem 11.8: operational Aasen
-- factorization residual with the source coefficient γ_(n+3).
--
-- The earlier ambient-mask executor rounds structural trailing zeros and is
-- therefore intentionally not used for the source-sharp count.  This module
-- exposes the source operation order by skipping zero addends, proves the
-- tridiagonal H = T Lᵀ formation bound γ₃, proves A = L H with γ_n (including
-- the Stewart-counter backward analysis of the rounded multiplier update),
-- and folds the two certificates to γ_(n+3).

import NumStability.Algorithms.Cholesky.AasenFactorResidualCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirect.SourceSharp

open NumStability

noncomputable def zeroSkip (fp : FPModel) : FPModel where
  u := fp.u
  u_nonneg := fp.u_nonneg
  fl_add := fun x y => if x = 0 then y else if y = 0 then x else fp.fl_add x y
  fl_sub := fp.fl_sub
  fl_mul := fp.fl_mul
  fl_div := fp.fl_div
  fl_sqrt := fp.fl_sqrt
  fl_add_zero := by intro x; simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · subst x
      refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
      simp
    · by_cases hy : y = 0
      · subst y
        refine ⟨0, by simpa using fp.u_nonneg, ?_⟩
        simp [hx]
      · obtain ⟨δ, hδ, hfl⟩ := fp.model_add x y
        exact ⟨δ, hδ, by simp [hx, hy, hfl]⟩
  model_sub := fp.model_sub
  model_mul := fp.model_mul
  model_div := fp.model_div
  model_sqrt := fp.model_sqrt

theorem zeroSkip_add_right_zero (fp : FPModel) (x : ℝ) :
    (zeroSkip fp).fl_add x 0 = x := by
  by_cases hx : x = 0
  · subst x; simp [zeroSkip]
  · simp [zeroSkip, hx]

theorem fl_mul_zero_left (fp : FPModel) (x : ℝ) : fp.fl_mul 0 x = 0 := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_mul 0 x
  simpa using hfl

theorem fl_dotProduct_succ_last (fp : FPModel) (n : ℕ)
    (x y : Fin (n + 1) → ℝ) :
    fl_dotProduct fp (n + 1) x y =
      fp.fl_add
        (fl_dotProduct fp n (fun i => x i.castSucc) (fun i => y i.castSucc))
        (fp.fl_mul (x (Fin.last n)) (y (Fin.last n))) := by
  cases n with
  | zero => simp [fl_dotProduct, fp.fl_add_zero]
  | succ n =>
      simp only [fl_dotProduct]
      rw [Fin.foldl_succ_last]
      congr 1

theorem fin_foldl_eq_list_ofFn (α : Type*) :
    ∀ (n : ℕ) (f : α → Fin n → α) (init : α),
      Fin.foldl n f init =
        (List.ofFn (fun i : Fin n => i)).foldl f init := by
  intro n
  induction n with
  | zero => intro f init; simp
  | succ n ih =>
      intro f init
      rw [Fin.foldl_succ, List.ofFn_succ]
      simp only [List.foldl_cons]
      rw [List.ofFn_comp' (fun i : Fin n => i) Fin.succ, List.foldl_map]
      exact ih (fun acc i => f acc i.succ) (f init 0)

theorem fl_dotProduct_eq_list_foldl (fp : FPModel) (n : ℕ)
    (x y : Fin n → ℝ) :
    fl_dotProduct fp n x y =
      (List.ofFn (fun i : Fin n => fp.fl_mul (x i) (y i))).foldl fp.fl_add 0 := by
  cases n with
  | zero => simp [fl_dotProduct]
  | succ n =>
      rw [List.ofFn_succ]
      simp only [List.foldl_cons, fp.fl_add_zero]
      simp only [fl_dotProduct]
      rw [fin_foldl_eq_list_ofFn]
      rw [List.ofFn_comp' (fun i : Fin n => i)
        (fun i => fp.fl_mul (x i.succ) (y i.succ)), List.foldl_map]

theorem list_foldl_replicate_zero (fp : FPModel)
    (hzero : ∀ x : ℝ, fp.fl_add x 0 = x) (d : ℕ) (init : ℝ) :
    (List.replicate d 0).foldl fp.fl_add init = init := by
  induction d generalizing init with
  | zero => simp
  | succ d ih =>
      rw [List.replicate_succ, List.foldl_cons, hzero]
      exact ih init

theorem fl_dotProduct_append_zero_right (fp : FPModel)
    (hzero : ∀ x : ℝ, fp.fl_add x 0 = x)
    (m d : ℕ) (x y : Fin m → ℝ) (z : Fin d → ℝ) :
    fl_dotProduct fp (m + d) (Fin.append x (fun _ => 0)) (Fin.append y z) =
      fl_dotProduct fp m x y := by
  rw [fl_dotProduct_eq_list_foldl, fl_dotProduct_eq_list_foldl]
  have hproducts :
      List.ofFn (fun i : Fin (m + d) =>
          fp.fl_mul ((Fin.append x (fun _ => 0)) i) ((Fin.append y z) i)) =
        List.ofFn (fun i : Fin m => fp.fl_mul (x i) (y i)) ++
          List.replicate d 0 := by
    have hfun :
        (fun i : Fin (m + d) =>
          fp.fl_mul ((Fin.append x (fun _ => 0)) i) ((Fin.append y z) i)) =
        Fin.append (fun i : Fin m => fp.fl_mul (x i) (y i)) (fun _ : Fin d => 0) := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [Fin.append_left]
      · intro j
        simp only [Fin.append_right]
        exact fl_mul_zero_left fp _
    rw [hfun, List.ofFn_fin_append, List.ofFn_const]
  rw [hproducts, List.foldl_append, list_foldl_replicate_zero fp hzero]

theorem fl_dotProduct_zero_cons_any_local (fp : FPModel) {n : ℕ}
    (v b : Fin n → ℝ) (b0 : ℝ) :
    fl_dotProduct fp (n + 1) (Fin.cases 0 v) (Fin.cases b0 b) =
      fl_dotProduct fp n v b := by
  cases n with
  | zero => simp [fl_dotProduct, fl_mul_zero_left]
  | succ m =>
      simp [fl_dotProduct, Fin.foldl_succ, fl_mul_zero_left, fp.fl_add_zero]

theorem dotProduct_error_bound_band3 (fp : FPModel)
    (hadd0r : ∀ x : ℝ, fp.fl_add x 0 = x) :
    ∀ (n : ℕ) (x y : Fin n → ℝ) (c : Fin n),
      (∀ q : Fin n, c.val + 1 < q.val ∨ q.val + 1 < c.val → x q = 0) →
      gammaValid fp 3 →
      |fl_dotProduct fp n x y - ∑ q : Fin n, x q * y q| ≤
        gamma fp 3 * ∑ q : Fin n, |x q| * |y q| := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x y c hsupp hval3
      by_cases hn : n ≤ 3
      · have hvaln : gammaValid fp n := gammaValid_mono fp hn hval3
        have hb := dotProduct_error_bound fp n x y hvaln
        have hg : gamma fp n ≤ gamma fp 3 := gamma_mono fp hn hval3
        have hsum0 : 0 ≤ ∑ q : Fin n, |x q| * |y q| := by
          apply Finset.sum_nonneg
          intro q _
          positivity
        exact hb.trans (mul_le_mul_of_nonneg_right hg hsum0)
      · have hn4 : 4 ≤ n := by omega
        by_cases hc : 2 ≤ c.val
        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          have hm3 : 3 ≤ m := by omega
          let x' : Fin m → ℝ := fun q => x q.succ
          let y' : Fin m → ℝ := fun q => y q.succ
          let c' : Fin m := ⟨c.val - 1, by omega⟩
          have hx0 : x 0 = 0 := hsupp 0 (Or.inr (by simp; omega))
          have hsupp' : ∀ q : Fin m,
              c'.val + 1 < q.val ∨ q.val + 1 < c'.val → x' q = 0 := by
            intro q hq
            apply hsupp q.succ
            dsimp [c', x'] at hq ⊢
            omega
          have hb := ih m (by omega) x' y' c' hsupp' hval3
          have hdot : fl_dotProduct fp (m + 1) x y = fl_dotProduct fp m x' y' := by
            have h := fl_dotProduct_zero_cons_any_local fp x' y' (y 0)
            have hxfun : x = Fin.cases 0 x' := by
              funext q
              refine Fin.cases ?_ ?_ q
              · simpa using hx0
              · intro i; rfl
            have hyfun : y = Fin.cases (y 0) y' := by
              funext q
              refine Fin.cases ?_ ?_ q
              · rfl
              · intro i; rfl
            rw [hxfun, hyfun]
            exact h
          have hsum : (∑ q : Fin (m + 1), x q * y q) =
              ∑ q : Fin m, x' q * y' q := by
            rw [Fin.sum_univ_succ, hx0, zero_mul, zero_add]
          have habs : (∑ q : Fin (m + 1), |x q| * |y q|) =
              ∑ q : Fin m, |x' q| * |y' q| := by
            rw [Fin.sum_univ_succ, hx0, abs_zero, zero_mul, zero_add]
          simpa [hdot, hsum, habs] using hb

        · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
          have hm3 : 3 ≤ m := by omega
          let x' : Fin m → ℝ := fun q => x q.castSucc
          let y' : Fin m → ℝ := fun q => y q.castSucc
          let c' : Fin m := ⟨c.val, by omega⟩
          have hxlast : x (Fin.last m) = 0 := hsupp (Fin.last m) (Or.inl (by simp; omega))
          have hsupp' : ∀ q : Fin m,
              c'.val + 1 < q.val ∨ q.val + 1 < c'.val → x' q = 0 := by
            intro q hq
            apply hsupp q.castSucc
            simpa [c', x'] using hq
          have hb := ih m (by omega) x' y' c' hsupp' hval3
          have hdot : fl_dotProduct fp (m + 1) x y = fl_dotProduct fp m x' y' := by
            rw [fl_dotProduct_succ_last, hxlast, fl_mul_zero_left, hadd0r]
          have hsum : (∑ q : Fin (m + 1), x q * y q) =
              ∑ q : Fin m, x' q * y' q := by
            rw [Fin.sum_univ_castSucc, hxlast, zero_mul, add_zero]
          have habs : (∑ q : Fin (m + 1), |x q| * |y q|) =
              ∑ q : Fin m, |x' q| * |y' q| := by
            rw [Fin.sum_univ_castSucc, hxlast, abs_zero, zero_mul, add_zero]
          simpa [hdot, hsum, habs] using hb

/-! Source-sharp Aasen executor: the existing coupled state machine is run
with zero addends skipped.  Every nonzero primitive operation is exactly the
one supplied by `fp`; only source-absent structural-zero additions are elided. -/

noncomputable def flAasenSource (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : FlAasenState n :=
  flAasen (zeroSkip fp) n A

def FlAasenSourcePivots (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) : Prop :=
  FlAasenPivots (zeroSkip fp) n A

theorem flAasenSource_H_eq_TLT_residual_upper (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (j i : Fin n) (hji : j.val < i.val)
    (hval3 : gammaValid fp 3) :
    |(flAasenSource fp n A).Hhat j i -
        (∑ q : Fin n, (flAasenSource fp n A).That j q *
          (flAasenSource fp n A).Lhat i q)| ≤
      gamma fp 3 * ∑ q : Fin n,
        |(flAasenSource fp n A).That j q| *
          |(flAasenSource fp n A).Lhat i q| := by
  let sfp := zeroSkip fp
  have hrow : (flAasenSource fp n A).Hhat j i =
      fl_dotProduct sfp n
        (fun q => (flAasenSource fp n A).That j q)
        (fun q => (flAasenSource fp n A).Lhat i q) := by
    change (flAasen sfp n A).Hhat j i = _
    rw [flAasen_Hhat_upper sfp n A i j hji]
    unfold aUpperH
    congr 1
    · funext q
      exact That_iter_eq_flAasen sfp n A j q i.val
        (by have := Nat.min_le_left j.val q.val; omega)
    · funext q
      exact Lhat_row_iter_eq_flAasen sfp n A i q
  rw [hrow]
  have hsupp : ∀ q : Fin n,
      j.val + 1 < q.val ∨ q.val + 1 < j.val →
        (flAasenSource fp n A).That j q = 0 := by
    intro q hq
    change (flAasen sfp n A).That j q = 0
    exact flAasen_T_band sfp n A j q hq
  have hval3' : gammaValid sfp 3 := by
    simpa [sfp, zeroSkip, gammaValid] using hval3
  have hb := dotProduct_error_bound_band3 sfp
    (by intro x; exact zeroSkip_add_right_zero fp x)
    n (fun q => (flAasenSource fp n A).That j q)
      (fun q => (flAasenSource fp n A).Lhat i q) j hsupp hval3'
  simpa [sfp, zeroSkip, gamma] using hb

/-- The α-extraction part of Aasen is a one-product/one-subtraction
calculation, hence its `H = T Lᵀ` diagonal residual needs only `γ₃`,
independently of the ambient dimension. -/
theorem flAasen_H_eq_TLT_residual_diag_gamma3 (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i : Fin n) (hval3 : gammaValid fp 3) :
    |(flAasen fp n A).Hhat i i -
        (∑ q : Fin n, (flAasen fp n A).That i q * (flAasen fp n A).Lhat i q)| ≤
      gamma fp 3 * ∑ q : Fin n,
        |(flAasen fp n A).That i q| * |(flAasen fp n A).Lhat i q| := by
  set F := flAasen fp n A with hF
  have hLdiag : F.Lhat i i = 1 := by
    rw [hF]
    exact flAasen_L_unit_diag fp n A i
  have hsupp : ∀ q : Fin n, i.val < q.val ∨ q.val + 1 < i.val →
      F.That i q * F.Lhat i q = 0 := by
    intro q hq
    rcases hq with hq | hq
    · rw [show F.Lhat i q = 0 from by
          rw [hF]; exact flAasen_L_upper_zero fp n A i q hq, mul_zero]
    · rw [show F.That i q = 0 from by
          rw [hF]; exact flAasen_T_band fp n A i q (Or.inr hq), zero_mul]
  have hsupp_abs : ∀ q : Fin n, i.val < q.val ∨ q.val + 1 < i.val →
      |F.That i q| * |F.Lhat i q| = 0 := by
    intro q hq
    rcases hq with hq | hq
    · rw [show F.Lhat i q = 0 from by
          rw [hF]; exact flAasen_L_upper_zero fp n A i q hq, abs_zero, mul_zero]
    · rw [show F.That i q = 0 from by
          rw [hF]; exact flAasen_T_band fp n A i q (Or.inr hq), abs_zero, zero_mul]
  have halpha : F.That i i = fp.fl_sub (F.Hhat i i)
      (∑ p : Fin n, if p.val + 1 = i.val then
        fp.fl_mul (F.That i p) (F.Lhat i p) else 0) := by
    rw [hF]
    exact flAasen_alpha_extraction fp n A i
  have hsum_eq : (∑ q : Fin n, F.That i q * F.Lhat i q) =
      (∑ p : Fin n, if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0) +
        F.That i i * F.Lhat i i := by
    simpa using sum_supported_on_prev_self n i
      (fun q => F.That i q * F.Lhat i q) hsupp
  have habs_eq : (∑ q : Fin n, |F.That i q| * |F.Lhat i q|) =
      (∑ p : Fin n, if p.val + 1 = i.val then
        |F.That i p| * |F.Lhat i p| else 0) +
        |F.That i i| * |F.Lhat i i| := by
    simpa using sum_supported_on_prev_self n i
      (fun q => |F.That i q| * |F.Lhat i q|) hsupp_abs
  set H := F.Hhat i i
  set S := ∑ p : Fin n, if p.val + 1 = i.val then
    fp.fl_mul (F.That i p) (F.Lhat i p) else 0
  set Sexact := ∑ p : Fin n, if p.val + 1 = i.val then
    F.That i p * F.Lhat i p else 0
  set maskedAbs := ∑ p : Fin n, if p.val + 1 = i.val then
    |F.That i p| * |F.Lhat i p| else 0
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub H S
  have hTval : F.That i i = (H - S) * (1 + δs) := by
    rw [halpha, hsub]
  have hres : F.Hhat i i - (∑ q : Fin n, F.That i q * F.Lhat i q) =
      (S - Sexact) - (H - S) * δs := by
    rw [hsum_eq, hTval, hLdiag]
    ring
  have hSS : |S - Sexact| ≤ fp.u * maskedAbs := by
    change |(∑ p : Fin n, if p.val + 1 = i.val then
      fp.fl_mul (F.That i p) (F.Lhat i p) else 0) -
      (∑ p : Fin n, if p.val + 1 = i.val then
        F.That i p * F.Lhat i p else 0)| ≤ _
    rw [← Finset.sum_sub_distrib]
    calc
      |∑ p : Fin n,
          ((if p.val + 1 = i.val then fp.fl_mul (F.That i p) (F.Lhat i p) else 0) -
            (if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0))| ≤
          ∑ p : Fin n,
            |(if p.val + 1 = i.val then fp.fl_mul (F.That i p) (F.Lhat i p) else 0) -
              (if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : Fin n, if p.val + 1 = i.val then
          fp.u * (|F.That i p| * |F.Lhat i p|) else 0 := by
        apply Finset.sum_le_sum
        intro p _
        by_cases hp : p.val + 1 = i.val
        · rw [if_pos hp, if_pos hp, if_pos hp]
          obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (F.That i p) (F.Lhat i p)
          rw [hmul, show F.That i p * F.Lhat i p * (1 + δm) -
              F.That i p * F.Lhat i p = (F.That i p * F.Lhat i p) * δm by ring,
            abs_mul]
          calc
            |F.That i p * F.Lhat i p| * |δm| ≤
                |F.That i p * F.Lhat i p| * fp.u :=
              mul_le_mul_of_nonneg_left hδm (abs_nonneg _)
            _ = fp.u * (|F.That i p| * |F.Lhat i p|) := by
              rw [abs_mul]
              ring
        · rw [if_neg hp, if_neg hp, if_neg hp, sub_zero, abs_zero]
      _ = fp.u * maskedAbs := by
        change (∑ p : Fin n, if p.val + 1 = i.val then
          fp.u * (|F.That i p| * |F.Lhat i p|) else 0) =
          fp.u * (∑ p : Fin n, if p.val + 1 = i.val then
            |F.That i p| * |F.Lhat i p| else 0)
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        split_ifs <;> ring
  have hu1 : fp.u < 1 := by
    have h := gammaValid_mono fp (by norm_num : 1 ≤ 3) hval3
    unfold gammaValid at h
    simpa using h
  have hHS : |(H - S) * δs| ≤ gamma fp 1 * |F.That i i| := by
    have hkey := absMulTheta_le (F.That i i) (H - S) δs fp.u hTval hδs hu1
    have hg1 : fp.u / (1 - fp.u) = gamma fp 1 := by simp [gamma]
    rwa [hg1] at hkey
  have hM_nonneg : 0 ≤ maskedAbs := by
    change 0 ≤ ∑ p : Fin n, if p.val + 1 = i.val then
      |F.That i p| * |F.Lhat i p| else 0
    apply Finset.sum_nonneg
    intro p _
    split_ifs
    · positivity
    · rfl
  have hu_le : fp.u ≤ gamma fp 3 := u_le_gamma fp (by norm_num) hval3
  have hg1_le : gamma fp 1 ≤ gamma fp 3 := gamma_mono fp (by norm_num) hval3
  have hLabs : |F.Lhat i i| = 1 := by rw [hLdiag, abs_one]
  rw [habs_eq, hres, hLabs, mul_one]
  calc
    |(S - Sexact) - (H - S) * δs| ≤ |S - Sexact| + |(H - S) * δs| := by
      rw [sub_eq_add_neg]
      simpa using abs_add_le (S - Sexact) (-((H - S) * δs))
    _ ≤ fp.u * maskedAbs + gamma fp 1 * |F.That i i| := add_le_add hSS hHS
    _ ≤ gamma fp 3 * maskedAbs + gamma fp 3 * |F.That i i| :=
      add_le_add (mul_le_mul_of_nonneg_right hu_le hM_nonneg)
        (mul_le_mul_of_nonneg_right hg1_le (abs_nonneg _))
    _ = gamma fp 3 * (maskedAbs + |F.That i i|) := by ring

/-- Source-sharp `H = T Lᵀ` residual.  The upper entries execute only the
three-term tridiagonal row window, diagonal extraction is local, and the
remaining Hessenberg cases are exact. -/
theorem flAasenSource_H_eq_TLT_residual (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hval3 : gammaValid fp 3) (j i : Fin n) :
    |(flAasenSource fp n A).Hhat j i -
        (∑ q : Fin n, (flAasenSource fp n A).That j q *
          (flAasenSource fp n A).Lhat i q)| ≤
      gamma fp 3 * ∑ q : Fin n,
        |(flAasenSource fp n A).That j q| *
          |(flAasenSource fp n A).Lhat i q| := by
  let sfp := zeroSkip fp
  set F := flAasenSource fp n A with hF
  rcases lt_trichotomy j.val i.val with hlt | heq | hgt
  · rw [hF]
    exact flAasenSource_H_eq_TLT_residual_upper fp n A j i hlt hval3
  · have hji : j = i := Fin.ext heq
    subst hji
    rw [hF]
    have hval3' : gammaValid sfp 3 := by
      simpa [sfp, zeroSkip, gammaValid] using hval3
    have hb := flAasen_H_eq_TLT_residual_diag_gamma3 sfp n A j hval3'
    simpa [flAasenSource, sfp, zeroSkip, gamma] using hb
  · rcases Nat.lt_or_ge (i.val + 1) j.val with hbelow | hle
    · have hH0 : F.Hhat j i = 0 := by
        rw [hF]
        change (flAasen sfp n A).Hhat j i = 0
        exact flAasen_H_upperHessenberg sfp n A j i hbelow
      have hsum0 : (∑ q : Fin n, F.That j q * F.Lhat i q) = 0 := by
        apply Finset.sum_eq_zero
        intro q _
        by_cases hq : q.val ≤ i.val
        · rw [show F.That j q = 0 from by
              rw [hF]
              change (flAasen sfp n A).That j q = 0
              exact flAasen_T_band sfp n A j q (Or.inr (by omega)), zero_mul]
        · rw [show F.Lhat i q = 0 from by
              rw [hF]
              change (flAasen sfp n A).Lhat i q = 0
              exact flAasen_L_upper_zero sfp n A i q (by omega), mul_zero]
      rw [hH0, hsum0, sub_zero, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hval3)
        (Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

    · have hji' : j.val = i.val + 1 := by omega
      have hnext : i.val + 1 < n := by rw [← hji']; exact j.isLt
      have hje : j = (⟨i.val + 1, hnext⟩ : Fin n) := Fin.ext hji'
      have hLdiag_i : F.Lhat i i = 1 := by
        rw [hF]
        change (flAasen sfp n A).Lhat i i = 1
        exact flAasen_L_unit_diag sfp n A i
      have hsum : (∑ q : Fin n, F.That j q * F.Lhat i q) = F.That j i := by
        rw [Finset.sum_eq_single i]
        · rw [hLdiag_i, mul_one]
        · intro q _ hqi
          by_cases hq : q.val ≤ i.val
          · rw [show F.That j q = 0 from by
                rw [hF]
                change (flAasen sfp n A).That j q = 0
                exact flAasen_T_band sfp n A j q
                  (Or.inr (by have : q.val ≠ i.val := fun h => hqi (Fin.ext h); omega)),
              zero_mul]
          · rw [show F.Lhat i q = 0 from by
                rw [hF]
                change (flAasen sfp n A).Lhat i q = 0
                exact flAasen_L_upper_zero sfp n A i q (by omega), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ i) h
      have hTH : F.That j i = F.Hhat j i := by
        rw [hF, hje]
        change (flAasen sfp n A).That ⟨i.val + 1, hnext⟩ i =
          (flAasen sfp n A).Hhat ⟨i.val + 1, hnext⟩ i
        exact flAasen_T_subdiagonal_eq_H sfp n A i hnext
      rw [hsum, hTH, sub_self, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hval3)
        (Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

theorem rounded_sub_dot_self_residual_gamma_n (fp : FPModel) (n : ℕ)
    (hn : 0 < n) (hval : gammaValid fp n)
    (a s msum mabs hself δ : ℝ)
    (hdot : |s - msum| ≤ gamma fp n * mabs)
    (hδ : |δ| ≤ fp.u)
    (hselfeq : hself = (a - s) * (1 + δ)) :
    |(msum + hself) - a| ≤ gamma fp n * (mabs + |hself|) := by
  have hu1 : fp.u < 1 := by
    have h := gammaValid_mono fp (show 1 ≤ n from hn) hval
    unfold gammaValid at h
    simpa using h
  have hback : |(a - s) * δ| ≤ gamma fp 1 * |hself| := by
    have hkey := absMulTheta_le hself (a - s) δ fp.u hselfeq hδ hu1
    have hg1 : fp.u / (1 - fp.u) = gamma fp 1 := by simp [gamma]
    rwa [hg1] at hkey
  have hg1n : gamma fp 1 ≤ gamma fp n := gamma_mono fp hn hval
  have hres : (msum + hself) - a = (msum - s) + (a - s) * δ := by
    rw [hselfeq]
    ring
  rw [hres]
  calc
    |(msum - s) + (a - s) * δ| ≤ |msum - s| + |(a - s) * δ| := abs_add_le _ _
    _ = |s - msum| + |(a - s) * δ| := by rw [abs_sub_comm]
    _ ≤ gamma fp n * mabs + gamma fp 1 * |hself| := add_le_add hdot hback
    _ ≤ gamma fp n * mabs + gamma fp n * |hself| :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hg1n (abs_nonneg _))
    _ = gamma fp n * (mabs + |hself|) := by ring

theorem flAasen_A_eq_LH_residual_diag_gamma_n (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i : Fin n) (hval : gammaValid fp n) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat i j * (flAasen fp n A).Hhat j i) - A i i| ≤
      gamma fp n * ∑ j : Fin n,
        |(flAasen fp n A).Lhat i j| * |(flAasen fp n A).Hhat j i| := by
  set F := flAasen fp n A with hF
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hLdiag : F.Lhat i i = 1 := by
    rw [hF]
    exact flAasen_L_unit_diag fp n A i
  have hsupp : ∀ j : Fin n, i.val < j.val → F.Lhat i j * F.Hhat j i = 0 := by
    intro j hj
    rw [show F.Lhat i j = 0 from by
      rw [hF]; exact flAasen_L_upper_zero fp n A i j hj, zero_mul]
  have hsupp_abs : ∀ j : Fin n, i.val < j.val →
      |F.Lhat i j| * |F.Hhat j i| = 0 := by
    intro j hj
    rw [show F.Lhat i j = 0 from by
      rw [hF]; exact flAasen_L_upper_zero fp n A i j hj, abs_zero, zero_mul]
  have hsum_split := sum_split_lt_self n i
    (fun j => F.Lhat i j * F.Hhat j i) hsupp
  have habs_split := sum_split_lt_self n i
    (fun j => |F.Lhat i j| * |F.Hhat j i|) hsupp_abs
  simp only at hsum_split habs_split
  have hrec : F.Hhat i i = fp.fl_sub (A i i)
      (fl_dotProduct fp n (fun j => if j.val < i.val then F.Lhat i j else 0)
        (fun j => if j.val < i.val then F.Hhat j i else 0)) := by
    rw [hF]
    exact flAasen_recurrence_diagonal fp n A i
  have hb := dotProduct_error_bound fp n
    (fun j => if j.val < i.val then F.Lhat i j else 0)
    (fun j => if j.val < i.val then F.Hhat j i else 0) hval
  have hconv1 : (∑ j : Fin n, (if j.val < i.val then F.Lhat i j else 0) *
        (if j.val < i.val then F.Hhat j i else 0)) =
      ∑ j : Fin n, if j.val < i.val then F.Lhat i j * F.Hhat j i else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hconv2 : (∑ j : Fin n, |if j.val < i.val then F.Lhat i j else 0| *
        |if j.val < i.val then F.Hhat j i else 0|) =
      ∑ j : Fin n, if j.val < i.val then |F.Lhat i j| * |F.Hhat j i| else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hconv1, hconv2] at hb
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (A i i)
    (fl_dotProduct fp n (fun j => if j.val < i.val then F.Lhat i j else 0)
      (fun j => if j.val < i.val then F.Hhat j i else 0))
  set s := fl_dotProduct fp n (fun j => if j.val < i.val then F.Lhat i j else 0)
    (fun j => if j.val < i.val then F.Hhat j i else 0)
  set msum := ∑ j : Fin n, if j.val < i.val then F.Lhat i j * F.Hhat j i else 0
  set mabs := ∑ j : Fin n, if j.val < i.val then |F.Lhat i j| * |F.Hhat j i| else 0
  have hself : F.Hhat i i = (A i i - s) * (1 + δ) := by
    rw [hrec, hsub]
  have hlocal := rounded_sub_dot_self_residual_gamma_n fp n hn hval
    (A i i) s msum mabs (F.Hhat i i) δ hb hδ hself
  rw [hsum_split, habs_split, hLdiag, one_mul, abs_one, one_mul]
  exact hlocal

theorem flAasen_A_eq_LH_residual_subdiag_gamma_n (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (i k : Fin n) (hk : k.val = i.val + 1)
    (hval : gammaValid fp n) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat k j * (flAasen fp n A).Hhat j i) - A k i| ≤
      gamma fp n * ∑ j : Fin n,
        |(flAasen fp n A).Lhat k j| * |(flAasen fp n A).Hhat j i| := by
  set F := flAasen fp n A with hF
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hnext : i.val + 1 < n := by rw [← hk]; exact k.isLt
  have hke : k = (⟨i.val + 1, hnext⟩ : Fin n) := Fin.ext hk
  have hLdiag : F.Lhat k k = 1 := by
    rw [hF]
    exact flAasen_L_unit_diag fp n A k
  have hsupp : ∀ j : Fin n, k.val < j.val → F.Lhat k j * F.Hhat j i = 0 := by
    intro j hj
    rw [show F.Lhat k j = 0 from by
      rw [hF]; exact flAasen_L_upper_zero fp n A k j hj, zero_mul]
  have hsupp_abs : ∀ j : Fin n, k.val < j.val →
      |F.Lhat k j| * |F.Hhat j i| = 0 := by
    intro j hj
    rw [show F.Lhat k j = 0 from by
      rw [hF]; exact flAasen_L_upper_zero fp n A k j hj, abs_zero, zero_mul]
  have hsum_split := sum_split_le_next n i k hk
    (fun j => F.Lhat k j * F.Hhat j i) hsupp
  have habs_split := sum_split_le_next n i k hk
    (fun j => |F.Lhat k j| * |F.Hhat j i|) hsupp_abs
  simp only at hsum_split habs_split
  have hrec : F.Hhat k i = fp.fl_sub (A k i)
      (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
        (fun j => if j.val ≤ i.val then F.Hhat j i else 0)) := by
    rw [hF, hke]
    exact flAasen_recurrence_subdiagonal fp n A i hnext
  have hb := dotProduct_error_bound fp n
    (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0) hval
  have hconv1 : (∑ j : Fin n, (if j.val ≤ i.val then F.Lhat k j else 0) *
        (if j.val ≤ i.val then F.Hhat j i else 0)) =
      ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hconv2 : (∑ j : Fin n, |if j.val ≤ i.val then F.Lhat k j else 0| *
        |if j.val ≤ i.val then F.Hhat j i else 0|) =
      ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hconv1, hconv2] at hb
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub (A k i)
    (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
      (fun j => if j.val ≤ i.val then F.Hhat j i else 0))
  set s := fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0)
  set msum := ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0
  set mabs := ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0
  have hself : F.Hhat k i = (A k i - s) * (1 + δ) := by
    rw [hrec, hsub]
  have hlocal := rounded_sub_dot_self_residual_gamma_n fp n hn hval
    (A k i) s msum mabs (F.Hhat k i) δ hb hδ hself
  rw [hsum_split, habs_split, hLdiag, one_mul, abs_one, one_mul]
  exact hlocal

/-- Backward form of a rounded subtraction followed by a rounded division.
Keeping the two primitive factors separate makes their reciprocal a Stewart
counter `<2>`; no `γ₂/(1-γ₂) ≤ γ₄` inflation is needed. -/
theorem rounded_sub_div_product_backward_gamma2 (fp : FPModel)
    (a s h l : ℝ) (hh : h ≠ 0) (hval2 : gammaValid fp 2)
    (hl : l = fp.fl_div (fp.fl_sub a s) h) :
    |l * h - (a - s)| ≤ gamma fp 2 * (|l| * |h|) := by
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub a s
  obtain ⟨δd, hδd, hdiv⟩ := fp.model_div (fp.fl_sub a s) h hh
  have hu : fp.u < 1 := by
    have h1 := gammaValid_mono fp (by norm_num : 1 ≤ 2) hval2
    unfold gammaValid at h1
    simpa using h1
  have hfs : 1 + δs ≠ 0 := by
    have : -fp.u ≤ δs := (neg_le_of_abs_le hδs)
    linarith
  have hfd : 1 + δd ≠ 0 := by
    have : -fp.u ≤ δd := (neg_le_of_abs_le hδd)
    linarith
  have hforward : l * h = (a - s) * (1 + δs) * (1 + δd) := by
    rw [hl, hdiv, hsub]
    field_simp [hh]
  have hcs : relErrorCounter fp 1 (1 + δs) := by
    refine ⟨fun _ => δs, fun _ => false, ?_, ?_⟩
    · intro q
      simpa using hδs
    · simp
  have hcd : relErrorCounter fp 1 (1 + δd) := by
    refine ⟨fun _ => δd, fun _ => false, ?_, ?_⟩
    · intro q
      simpa using hδd
    · simp
  have hcsi : relErrorCounter fp 1 (1 / (1 + δs)) :=
    relErrorCounter_inv fp 1 (1 + δs) hcs hu
  have hcdi : relErrorCounter fp 1 (1 / (1 + δd)) :=
    relErrorCounter_inv fp 1 (1 + δd) hcd hu
  let c := (1 / (1 + δs)) * (1 / (1 + δd))
  have hc : relErrorCounter fp 2 c := by
    have hm := relErrorCounter_mul fp 1 1
      (1 / (1 + δs)) (1 / (1 + δd)) hcsi hcdi
    simpa [c] using hm
  have hcb : |c - 1| ≤ gamma fp 2 :=
    relErrorCounter_abs_sub_one_le_gamma fp 2 c hc hval2
  have hback : a - s = (l * h) * c := by
    rw [hforward]
    dsimp [c]
    field_simp [hfs, hfd]
  have hres : l * h - (a - s) = -(l * h) * (c - 1) := by
    rw [hback]
    ring
  rw [hres, abs_mul, abs_neg, abs_mul]
  calc
    (|l| * |h|) * |c - 1| ≤ (|l| * |h|) * gamma fp 2 :=
      mul_le_mul_of_nonneg_left hcb (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = gamma fp 2 * (|l| * |h|) := by ring

theorem flAasen_A_eq_LH_residual_general_gamma_n (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hpivots : FlAasenPivots fp n A)
    (i : Fin n) (hnext : i.val + 1 < n) (k : Fin n)
    (hk : i.val + 2 ≤ k.val) (hval : gammaValid fp n) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat k j * (flAasen fp n A).Hhat j i) - A k i| ≤
      gamma fp n * ∑ j : Fin n,
        |(flAasen fp n A).Lhat k j| * |(flAasen fp n A).Hhat j i| := by
  set F := flAasen fp n A with hF
  have hn3 : 3 ≤ n := by omega
  have hval2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hval
  set next : Fin n := ⟨i.val + 1, hnext⟩
  have hnextval : next.val = i.val + 1 := rfl
  have hpiv : F.Hhat next i ≠ 0 := by
    rw [hF]
    exact hpivots i.val hnext
  have hsupp : ∀ j : Fin n, next.val < j.val →
      F.Lhat k j * F.Hhat j i = 0 := by
    intro j hj
    rw [show F.Hhat j i = 0 from by
      rw [hF]; exact flAasen_H_upperHessenberg fp n A j i (by omega), mul_zero]
  have hsupp_abs : ∀ j : Fin n, next.val < j.val →
      |F.Lhat k j| * |F.Hhat j i| = 0 := by
    intro j hj
    rw [show F.Hhat j i = 0 from by
      rw [hF]; exact flAasen_H_upperHessenberg fp n A j i (by omega), abs_zero, mul_zero]
  have hsum_split := sum_split_le_next n i next hnextval
    (fun j => F.Lhat k j * F.Hhat j i) hsupp
  have habs_split := sum_split_le_next n i next hnextval
    (fun j => |F.Lhat k j| * |F.Hhat j i|) hsupp_abs
  simp only at hsum_split habs_split
  have hrec : F.Lhat k next = fp.fl_div
      (fp.fl_sub (A k i)
        (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
          (fun j => if j.val ≤ i.val then F.Hhat j i else 0)))
      (F.Hhat next i) := by
    rw [hF]
    exact flAasen_recurrence_nextColumn fp n A i hnext k hk
  have hb := dotProduct_error_bound fp n
    (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0) hval
  have hconv1 : (∑ j : Fin n, (if j.val ≤ i.val then F.Lhat k j else 0) *
        (if j.val ≤ i.val then F.Hhat j i else 0)) =
      ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hconv2 : (∑ j : Fin n, |if j.val ≤ i.val then F.Lhat k j else 0| *
        |if j.val ≤ i.val then F.Hhat j i else 0|) =
      ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  rw [hconv1, hconv2] at hb
  set s := fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0)
  set msum := ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0
  set mabs := ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0
  have hback := rounded_sub_div_product_backward_gamma2 fp
    (A k i) s (F.Hhat next i) (F.Lhat k next) hpiv hval2 hrec
  have hg2n : gamma fp 2 ≤ gamma fp n := gamma_mono fp (by omega) hval
  have hres : (∑ j : Fin n, F.Lhat k j * F.Hhat j i) - A k i =
      (msum - s) + (F.Lhat k next * F.Hhat next i - (A k i - s)) := by
    rw [hsum_split]
    ring
  rw [habs_split, hres]
  calc
    |(msum - s) + (F.Lhat k next * F.Hhat next i - (A k i - s))| ≤
        |msum - s| + |F.Lhat k next * F.Hhat next i - (A k i - s)| := abs_add_le _ _
    _ = |s - msum| + |F.Lhat k next * F.Hhat next i - (A k i - s)| := by
      rw [abs_sub_comm msum s]
    _ ≤ gamma fp n * mabs +
        gamma fp 2 * (|F.Lhat k next| * |F.Hhat next i|) := add_le_add hb hback
    _ ≤ gamma fp n * mabs +
        gamma fp n * (|F.Lhat k next| * |F.Hhat next i|) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right hg2n
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    _ = gamma fp n * (mabs + |F.Lhat k next| * |F.Hhat next i|) := by ring

theorem flAasen_A_eq_LH_residual_gamma_n (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hpivots : FlAasenPivots fp n A)
    (hval : gammaValid fp n) (k i : Fin n) (hki : i.val ≤ k.val) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat k j * (flAasen fp n A).Hhat j i) - A k i| ≤
      gamma fp n * ∑ j : Fin n,
        |(flAasen fp n A).Lhat k j| * |(flAasen fp n A).Hhat j i| := by
  rcases Nat.lt_or_ge i.val k.val with hlt | hge
  · rcases Nat.lt_or_ge (i.val + 1) k.val with hgen | hsub
    · exact flAasen_A_eq_LH_residual_general_gamma_n fp n A hpivots i
        (by omega) k (by omega) hval
    · exact flAasen_A_eq_LH_residual_subdiag_gamma_n fp n A i k (by omega) hval
  · have hik : k = i := Fin.ext (by omega)
    subst hik
    exact flAasen_A_eq_LH_residual_diag_gamma_n fp n A k hval

theorem flAasenSource_A_eq_LH_residual_gamma_n (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hpivots : FlAasenSourcePivots fp n A)
    (hval : gammaValid fp n) (k i : Fin n) (hki : i.val ≤ k.val) :
    |(∑ j : Fin n, (flAasenSource fp n A).Lhat k j *
        (flAasenSource fp n A).Hhat j i) - A k i| ≤
      gamma fp n * ∑ j : Fin n,
        |(flAasenSource fp n A).Lhat k j| *
          |(flAasenSource fp n A).Hhat j i| := by
  let sfp := zeroSkip fp
  have hval' : gammaValid sfp n := by
    simpa [sfp, zeroSkip, gammaValid] using hval
  have hb := flAasen_A_eq_LH_residual_gamma_n sfp n A hpivots hval' k i hki
  simpa [flAasenSource, sfp, zeroSkip, gamma] using hb

theorem flAasenSource_factorization_residual_lower_gamma_n_add_3
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hpivots : FlAasenSourcePivots fp n A)
    (hval : gammaValid fp (n + 3)) (i j : Fin n) (hji : j.val ≤ i.val) :
    |(∑ p : Fin n, ∑ q : Fin n,
        (flAasenSource fp n A).Lhat i p * (flAasenSource fp n A).That p q *
          (flAasenSource fp n A).Lhat j q) - A i j| ≤
      gamma fp (n + 3) *
        (∑ p : Fin n, ∑ q : Fin n,
          |(flAasenSource fp n A).Lhat i p| * |(flAasenSource fp n A).That p q| *
            |(flAasenSource fp n A).Lhat j q|) := by
  set F := flAasenSource fp n A with hF
  have hvaln : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hval3 : gammaValid fp 3 := gammaValid_mono fp (by omega) hval
  set P := ∑ p : Fin n, ∑ q : Fin n, F.Lhat i p * F.That p q * F.Lhat j q
  set TAsum := ∑ p : Fin n, ∑ q : Fin n,
    |F.Lhat i p| * |F.That p q| * |F.Lhat j q|
  set Q := ∑ p : Fin n, F.Lhat i p * F.Hhat p j
  set SH := ∑ p : Fin n, |F.Lhat i p| * |F.Hhat p j|
  have hTA_eq : TAsum = ∑ p : Fin n, |F.Lhat i p| *
      (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) := by
    change (∑ p : Fin n, ∑ q : Fin n,
      |F.Lhat i p| * |F.That p q| * |F.Lhat j q|) = _
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hTA_nonneg : 0 ≤ TAsum := by
    change 0 ≤ ∑ p : Fin n, ∑ q : Fin n,
      |F.Lhat i p| * |F.That p q| * |F.Lhat j q|
    positivity
  have hB1 : |Q - A i j| ≤ gamma fp n * SH := by
    change |(∑ p : Fin n, F.Lhat i p * F.Hhat p j) - A i j| ≤
      gamma fp n * (∑ p : Fin n, |F.Lhat i p| * |F.Hhat p j|)
    rw [hF]
    exact flAasenSource_A_eq_LH_residual_gamma_n fp n A hpivots hvaln i j hji
  have hPQ_eq : P - Q = ∑ p : Fin n, F.Lhat i p *
      ((∑ q : Fin n, F.That p q * F.Lhat j q) - F.Hhat p j) := by
    change (∑ p : Fin n, ∑ q : Fin n,
      F.Lhat i p * F.That p q * F.Lhat j q) -
      (∑ p : Fin n, F.Lhat i p * F.Hhat p j) = _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hPQ_le : |P - Q| ≤ gamma fp 3 * TAsum := by
    rw [hPQ_eq]
    calc
      |∑ p : Fin n, F.Lhat i p *
          ((∑ q : Fin n, F.That p q * F.Lhat j q) - F.Hhat p j)| ≤
          ∑ p : Fin n, |F.Lhat i p *
            ((∑ q : Fin n, F.That p q * F.Lhat j q) - F.Hhat p j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : Fin n, |F.Lhat i p| *
          (gamma fp 3 * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|)) := by
        apply Finset.sum_le_sum
        intro p _
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_sub_comm]
        rw [hF]
        exact flAasenSource_H_eq_TLT_residual fp n A hval3 p j
      _ = gamma fp 3 * TAsum := by
        rw [hTA_eq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
  have hSH_le : SH ≤ (1 + gamma fp 3) * TAsum := by
    change (∑ p : Fin n, |F.Lhat i p| * |F.Hhat p j|) ≤ _
    calc
      (∑ p : Fin n, |F.Lhat i p| * |F.Hhat p j|) ≤
          ∑ p : Fin n, |F.Lhat i p| *
            ((1 + gamma fp 3) * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|)) := by
        apply Finset.sum_le_sum
        intro p _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        have hb2 : |F.Hhat p j - (∑ q : Fin n, F.That p q * F.Lhat j q)| ≤
            gamma fp 3 * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) := by
          rw [hF]
          exact flAasenSource_H_eq_TLT_residual fp n A hval3 p j
        have htl : |∑ q : Fin n, F.That p q * F.Lhat j q| ≤
            ∑ q : Fin n, |F.That p q| * |F.Lhat j q| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          apply Finset.sum_le_sum
          intro q _
          rw [abs_mul]
        calc
          |F.Hhat p j| = |(∑ q : Fin n, F.That p q * F.Lhat j q) +
              (F.Hhat p j - ∑ q : Fin n, F.That p q * F.Lhat j q)| := by
            congr 1
            ring
          _ ≤ |∑ q : Fin n, F.That p q * F.Lhat j q| +
              |F.Hhat p j - ∑ q : Fin n, F.That p q * F.Lhat j q| := abs_add_le _ _
          _ ≤ (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) +
              gamma fp 3 * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) :=
            add_le_add htl hb2
          _ = (1 + gamma fp 3) *
              (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) := by ring
      _ = (1 + gamma fp 3) * TAsum := by
        rw [hTA_eq, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        ring
  have hcombine : |P - A i j| ≤ |Q - A i j| + |P - Q| := by
    have h := abs_add_le (Q - A i j) (P - Q)
    rw [show Q - A i j + (P - Q) = P - A i j by ring] at h
    exact h
  have hfold : gamma fp n + gamma fp n * gamma fp 3 + gamma fp 3 ≤
      gamma fp (n + 3) := by
    have h := gamma_sum_le fp n 3 hval
    linarith
  calc
    |P - A i j| ≤ |Q - A i j| + |P - Q| := hcombine
    _ ≤ gamma fp n * SH + gamma fp 3 * TAsum := add_le_add hB1 hPQ_le
    _ ≤ gamma fp n * ((1 + gamma fp 3) * TAsum) + gamma fp 3 * TAsum :=
      add_le_add (mul_le_mul_of_nonneg_left hSH_le (gamma_nonneg fp hvaln)) le_rfl
    _ = (gamma fp n + gamma fp n * gamma fp 3 + gamma fp 3) * TAsum := by ring
    _ ≤ gamma fp (n + 3) * TAsum :=
      mul_le_mul_of_nonneg_right hfold hTA_nonneg

/-- Operational source-sharp Aasen factorization residual with Higham's
factorization coefficient exactly: `γ_(n+3) |L̂| |T̂| |L̂ᵀ|`. -/
theorem flAasenSource_factorization_residual_gamma_n_add_3
    (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hpivots : FlAasenSourcePivots fp n A)
    (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hval : gammaValid fp (n + 3)) (i j : Fin n) :
    |(∑ p : Fin n, ∑ q : Fin n,
        (flAasenSource fp n A).Lhat i p * (flAasenSource fp n A).That p q *
          (flAasenSource fp n A).Lhat j q) - A i j| ≤
      gamma fp (n + 3) *
        (∑ p : Fin n, ∑ q : Fin n,
          |(flAasenSource fp n A).Lhat i p| * |(flAasenSource fp n A).That p q| *
            |(flAasenSource fp n A).Lhat j q|) := by
  rcases le_total j.val i.val with hji | hij
  · exact flAasenSource_factorization_residual_lower_gamma_n_add_3
      fp n A hpivots hval i j hji
  · have hlow := flAasenSource_factorization_residual_lower_gamma_n_add_3
      fp n A hpivots hval j i hij
    let sfp := zeroSkip fp
    have hTsym : ∀ r c : Fin n,
        (flAasenSource fp n A).That r c = (flAasenSource fp n A).That c r := by
      intro r c
      change (flAasen sfp n A).That r c = (flAasen sfp n A).That c r
      exact flAasen_T_symm sfp n A r c
    have hPsym : (∑ p : Fin n, ∑ q : Fin n,
          (flAasenSource fp n A).Lhat j p * (flAasenSource fp n A).That p q *
            (flAasenSource fp n A).Lhat i q) =
        ∑ p : Fin n, ∑ q : Fin n,
          (flAasenSource fp n A).Lhat i p * (flAasenSource fp n A).That p q *
            (flAasenSource fp n A).Lhat j q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hTsym b a]
      ring
    have hTAsym : (∑ p : Fin n, ∑ q : Fin n,
          |(flAasenSource fp n A).Lhat j p| * |(flAasenSource fp n A).That p q| *
            |(flAasenSource fp n A).Lhat i q|) =
        ∑ p : Fin n, ∑ q : Fin n,
          |(flAasenSource fp n A).Lhat i p| * |(flAasenSource fp n A).That p q| *
            |(flAasenSource fp n A).Lhat j q| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [hTsym b a]
      ring
    rw [hPsym, hTAsym, hsymm j i] at hlow
    exact hlow

end NumStability.Ch11Closure.AasenDirect.SourceSharp
