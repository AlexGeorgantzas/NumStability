-- Algorithms/Cholesky/AasenFactorResidualCh11Closure.lean
--
-- Higham, 2nd ed., Chapter 11, Theorem 11.8 — module #3 of the faithful 11.8
-- closure: the *direct* factorization residual of the computed Aasen factors.
--
-- Module #2 (`AasenCoupledFpCh11Closure`) constructed the computed factors
-- `L̂, Ĥ, T̂` by running Aasen's algorithm in floating point, and proved that
-- the rounded recurrences (11.12)/(11.13)/(11.14) hold *by definition* of the
-- coupled step.  This file turns those rounded recurrences into a componentwise
-- residual bound on the computed factorization
--
--   L̂ T̂ L̂ᵀ = A + ΔA ,   |ΔA_{ij}| ≤ γ_{3n} (|L̂| |T̂| |L̂ᵀ|)_{ij} .
--
-- The bound is a *residual on the computed factors*: nothing is ever compared
-- to an exact reference `L, T`, and no residual is ever divided by a pivot.
-- The only hypotheses are `gammaValid fp (3*n)`, symmetry of `A`, and the
-- nonzero-subdiagonal-pivot predicate `FlAasenPivots` (needed so the (11.14)
-- divisions are governed by the standard model).
--
-- Deliverables (consumed by module #4, the assembly):
--   * `flAasen_A_eq_LH_residual`  (B1) — lower-triangle residual of `A = L̂ Ĥ`;
--   * `flAasen_H_eq_TLT_residual` (B2) — residual of `Ĥ = T̂ L̂ᵀ`;
--   * `fl_aasen_factorization_residual` (B3, headline) — the `L̂ T̂ L̂ᵀ`
--     residual with the explicit `γ_{3n}` constant.

import NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirect

open NumStability

/-! ### Arithmetic helpers

Two small real-arithmetic facts used to convert the standard-model relative
errors of the rounded Aasen operations into additive residual budgets. -/

/-- **Backward residual of a forward relative error.**  If `X = Y (1+θ)` (the
computed quantity `X` equals the exact quantity `Y` times a relative-error
factor) and `|θ| ≤ c < 1`, then the additive residual `Y θ = X − Y` is bounded
by `c/(1−c)` times the *computed* magnitude `|X|`.  This is the standard trick
that lets a residual be expressed in the computed factors rather than in the
unavailable exact ones. -/
theorem absMulTheta_le
    (X Y θ c : ℝ) (hXY : X = Y * (1 + θ)) (hθ : |θ| ≤ c) (hc : c < 1) :
    |Y * θ| ≤ c / (1 - c) * |X| := by
  have hc0 : 0 ≤ c := le_trans (abs_nonneg θ) hθ
  have hden : 0 < 1 - c := by linarith
  have hθbounds : -c ≤ θ ∧ θ ≤ c := abs_le.mp hθ
  have hpos : 0 < 1 + θ := by linarith [hθbounds.1]
  have hXabs : |X| = |Y| * (1 + θ) := by
    rw [hXY, abs_mul, abs_of_pos hpos]
  have hYc : |Y| * (1 - c) ≤ |X| := by
    rw [hXabs]
    have hle : (1 - c) ≤ (1 + θ) := by linarith [hθbounds.1]
    exact mul_le_mul_of_nonneg_left hle (abs_nonneg Y)
  rw [abs_mul]
  calc |Y| * |θ|
      ≤ |Y| * c := mul_le_mul_of_nonneg_left hθ (abs_nonneg Y)
    _ ≤ c / (1 - c) * |X| := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hden]
        nlinarith [mul_le_mul_of_nonneg_left hYc hc0]

/-- **The self-reciprocal coefficient folds one index.**  The coefficient
`γ_k/(1−γ_k)` produced by `absMulTheta_le` (with `c = γ_k`) is bounded by
`γ_{2k}`.  Concretely `γ_k/(1−γ_k) = ku/(1−2ku) = γ_{2k}/2 ≤ γ_{2k}`. -/
theorem gamma_selfDiv_le (fp : FPModel) (k : ℕ) (hval : gammaValid fp (2 * k)) :
    gamma fp k / (1 - gamma fp k) ≤ gamma fp (2 * k) := by
  have hk : gammaValid fp k := gammaValid_mono fp (by omega) hval
  have hku : (k : ℝ) * fp.u < 1 := hk
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
  have h2 : 2 * (k : ℝ) * fp.u < 1 := by
    have h : ((2 * k : ℕ) : ℝ) * fp.u < 1 := hval
    rw [hcast] at h; linarith
  have ha_nonneg : 0 ≤ (k : ℝ) * fp.u :=
    mul_nonneg (by exact_mod_cast k.zero_le) fp.u_nonneg
  have hd1 : 0 < 1 - (k : ℝ) * fp.u := by linarith
  have hd2 : 0 < 1 - 2 * (k : ℝ) * fp.u := by linarith
  have hgk : gamma fp k = (k : ℝ) * fp.u / (1 - (k : ℝ) * fp.u) := rfl
  have hg2k : gamma fp (2 * k) = 2 * (k : ℝ) * fp.u / (1 - 2 * (k : ℝ) * fp.u) := by
    unfold gamma; rw [hcast]
  have hlhs : gamma fp k / (1 - gamma fp k)
      = (k : ℝ) * fp.u / (1 - 2 * (k : ℝ) * fp.u) := by
    rw [hgk]; field_simp; ring
  rw [hlhs, hg2k, div_le_div_iff₀ hd2 hd2]
  nlinarith [ha_nonneg, hd2, mul_nonneg ha_nonneg (le_of_lt hd2)]

/-! ### Freezing the per-stage rows into the final state

Module #2 states the per-stage quantities `aUpperH`, `aTdiag` over the
*intermediate* iterate `flAasenIter … i.val`.  To feed them to the
`dotProduct_error_bound` residual we must re-express the intermediate rows of
`T̂` and `L̂` as the final `flAasen` rows.  Since every entry, once written, is
never overwritten, the two agree; these lemmas make that precise. -/

/-- A diagonal `T̂` entry, once written at stage `a`, equals the final value from
any later iterate. -/
theorem flAasen_That_diag_iter_eq (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (a : Fin n) (m : ℕ) (ham : a.val < m) :
    (flAasenIter fp n A m).That a a = (flAasen fp n A).That a a := by
  have han : a.val < n := a.isLt
  unfold flAasen
  have hm : flAasenIter fp n A m
          = flAasenIter fp n A (a.val + 1 + (m - (a.val + 1))) := by congr 1; omega
  have hn : flAasenIter fp n A n
          = flAasenIter fp n A (a.val + 1 + (n - (a.val + 1))) := by congr 1; omega
  rw [hm, hn, flAasenIter_That_diag_freeze fp n A a (m - (a.val + 1)),
    flAasenIter_That_diag_freeze fp n A a (n - (a.val + 1))]

/-- A subdiagonal `T̂` entry `(a, b)` with `a = b+1`, once written at stage `b`,
equals the final value from any later iterate. -/
theorem flAasen_That_sub_iter_eq (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (a b : Fin n) (hab : a.val = b.val + 1) (m : ℕ) (hbm : b.val < m) :
    (flAasenIter fp n A m).That a b = (flAasen fp n A).That a b := by
  have han : a.val < n := a.isLt
  have hnext : b.val + 1 < n := by omega
  have hae : a = (⟨b.val + 1, hnext⟩ : Fin n) := Fin.ext (by omega)
  rw [hae]
  unfold flAasen
  have hm : flAasenIter fp n A m
          = flAasenIter fp n A (b.val + 1 + (m - (b.val + 1))) := by congr 1; omega
  have hn : flAasenIter fp n A n
          = flAasenIter fp n A (b.val + 1 + (n - (b.val + 1))) := by congr 1; omega
  rw [hm, hn, flAasenIter_That_sub_freeze fp n A b hnext (m - (b.val + 1)),
    flAasenIter_That_sub_freeze fp n A b hnext (n - (b.val + 1))]

/-- **Any `T̂` entry `(r,c)` with `min(r,c) < m` is frozen at the final state.**
Combines the diagonal/subdiagonal freezes (using symmetry for the superdiagonal
and the tridiagonal band for the rest). -/
theorem That_iter_eq_flAasen (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (r c : Fin n) (m : ℕ) (hm : min r.val c.val < m) :
    (flAasenIter fp n A m).That r c = (flAasen fp n A).That r c := by
  by_cases hband : r.val + 1 < c.val ∨ c.val + 1 < r.val
  · rw [(structInv_iter fp n A m).2.2.2.2 r c hband, flAasen_T_band fp n A r c hband]
  · push_neg at hband
    obtain ⟨hb1, hb2⟩ := hband
    rcases lt_trichotomy r.val c.val with hlt | heq | hgt
    · -- superdiagonal: c = r + 1
      have hcr : c.val = r.val + 1 := by omega
      rw [(structInv_iter fp n A m).2.2.2.1 r c, flAasen_T_symm fp n A r c]
      exact flAasen_That_sub_iter_eq fp n A c r hcr m (by omega)
    · -- diagonal
      have hrc : r = c := Fin.ext heq
      subst hrc
      exact flAasen_That_diag_iter_eq fp n A r m (by omega)
    · -- subdiagonal: r = c + 1
      have hrc : r.val = c.val + 1 := by omega
      exact flAasen_That_sub_iter_eq fp n A r c hrc m (by omega)

/-- **Row `i` of `L̂` is frozen at the final state.**  For `q ≤ i` this is the
module-#2 freeze; for `q > i` both sides vanish by upper triangularity. -/
theorem Lhat_row_iter_eq_flAasen (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i q : Fin n) :
    (flAasenIter fp n A i.val).Lhat i q = (flAasen fp n A).Lhat i q := by
  by_cases hq : q.val ≤ i.val
  · exact flAasenIter_Lhat_eq_flAasen fp n A i q i.val hq
  · push_neg at hq
    rw [(structInv_iter fp n A i.val).2.1 i q hq, flAasen_L_upper_zero fp n A i q hq]

/-- **α-extraction at the final state.**  The computed diagonal `T̂_{i,i}` is the
floating-point subtraction, from `Ĥ_{i,i}`, of the single product
`fl(T̂_{i,i-1} · L̂_{i,i-1})` (masked to the index `p = i-1`).  This is
`flAasen_T_diag_eq` with the intermediate rows frozen into the final state. -/
theorem flAasen_alpha_extraction (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) :
    (flAasen fp n A).That i i
      = fp.fl_sub ((flAasen fp n A).Hhat i i)
          (∑ p : Fin n, if p.val + 1 = i.val then
            fp.fl_mul ((flAasen fp n A).That i p) ((flAasen fp n A).Lhat i p) else 0) := by
  rw [flAasen_T_diag_eq fp n A i]
  unfold aTdiag
  rw [← flAasen_Hhat_diag fp n A i]
  simp only [Fin.eta]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : p.val + 1 = i.val
  · rw [if_pos hp, if_pos hp,
      That_iter_eq_flAasen fp n A i p i.val (by have := Nat.min_le_right i.val p.val; omega),
      Lhat_row_iter_eq_flAasen fp n A i p]
  · rw [if_neg hp, if_neg hp]

/-! ### B2 — the `Ĥ = T̂ L̂ᵀ` residual -/

/-- A finite sum whose summand `g` vanishes outside the two indices `i-1` and
`i` splits into the masked `p = i-1` term plus the `q = i` term.  Used to
evaluate the diagonal entry `(T̂ L̂ᵀ)_{i,i} = ∑_q T̂_{i,q} L̂_{i,q}` (both the
signed sum and its absolute-value analogue). -/
theorem sum_supported_on_prev_self (n : ℕ) (i : Fin n) (g : Fin n → ℝ)
    (hsupp : ∀ q : Fin n, i.val < q.val ∨ q.val + 1 < i.val → g q = 0) :
    (∑ q : Fin n, g q)
      = (∑ p : Fin n, if p.val + 1 = i.val then g p else 0) + g i := by
  have hpt : ∀ q : Fin n, g q
      = (if q.val + 1 = i.val then g q else 0) + (if q = i then g q else 0) := by
    intro q
    by_cases h1 : q.val + 1 = i.val
    · have h2 : q ≠ i := by intro h; rw [h] at h1; omega
      rw [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : q = i
      · rw [if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero]
        have hqi : q.val ≠ i.val := fun h => h2 (Fin.ext h)
        exact hsupp q (by omega)
  calc (∑ q : Fin n, g q)
      = ∑ q : Fin n,
          ((if q.val + 1 = i.val then g q else 0) + (if q = i then g q else 0)) :=
        Finset.sum_congr rfl (fun q _ => hpt q)
    _ = (∑ q : Fin n, if q.val + 1 = i.val then g q else 0)
          + (∑ q : Fin n, if q = i then g q else 0) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ p : Fin n, if p.val + 1 = i.val then g p else 0) + g i := by
        congr 1; simp

/-- **B2, diagonal case.**  The residual `Ĥ_{i,i} − (T̂ L̂ᵀ)_{i,i}` is bounded by
`γ_n ∑_q |T̂_{i,q}| |L̂_{i,q}|`.  Uses the α-extraction: `T̂_{i,i}` is the rounded
subtraction of `fl(T̂_{i,i-1} L̂_{i,i-1})` from `Ĥ_{i,i}`. -/
theorem flAasen_H_eq_TLT_residual_diag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hval : gammaValid fp n) :
    |(flAasen fp n A).Hhat i i
        - (∑ q : Fin n, (flAasen fp n A).That i q * (flAasen fp n A).Lhat i q)|
      ≤ gamma fp n * ∑ q : Fin n,
          |(flAasen fp n A).That i q| * |(flAasen fp n A).Lhat i q| := by
  set F := flAasen fp n A with hF
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hLdiag : F.Lhat i i = 1 := by rw [hF]; exact flAasen_L_unit_diag fp n A i
  have hsupp : ∀ q : Fin n, i.val < q.val ∨ q.val + 1 < i.val →
      F.That i q * F.Lhat i q = 0 := by
    intro q hq
    rcases hq with hq | hq
    · rw [show F.Lhat i q = 0 from by rw [hF]; exact flAasen_L_upper_zero fp n A i q hq, mul_zero]
    · rw [show F.That i q = 0 from by rw [hF]; exact flAasen_T_band fp n A i q (Or.inr hq),
        zero_mul]
  have hsupp_abs : ∀ q : Fin n, i.val < q.val ∨ q.val + 1 < i.val →
      |F.That i q| * |F.Lhat i q| = 0 := by
    intro q hq
    rcases hq with hq | hq
    · rw [show F.Lhat i q = 0 from by rw [hF]; exact flAasen_L_upper_zero fp n A i q hq,
        abs_zero, mul_zero]
    · rw [show F.That i q = 0 from by rw [hF]; exact flAasen_T_band fp n A i q (Or.inr hq),
        abs_zero, zero_mul]
  have halpha : F.That i i
      = fp.fl_sub (F.Hhat i i)
          (∑ p : Fin n, if p.val + 1 = i.val then
            fp.fl_mul (F.That i p) (F.Lhat i p) else 0) := by
    rw [hF]; exact flAasen_alpha_extraction fp n A i
  have hsum_eq : (∑ q : Fin n, F.That i q * F.Lhat i q)
      = (∑ p : Fin n, if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0)
          + F.That i i * F.Lhat i i := by
    simpa using sum_supported_on_prev_self n i (fun q => F.That i q * F.Lhat i q) hsupp
  have habs_eq : (∑ q : Fin n, |F.That i q| * |F.Lhat i q|)
      = (∑ p : Fin n, if p.val + 1 = i.val then |F.That i p| * |F.Lhat i p| else 0)
          + |F.That i i| * |F.Lhat i i| := by
    simpa using sum_supported_on_prev_self n i (fun q => |F.That i q| * |F.Lhat i q|) hsupp_abs
  set H := F.Hhat i i with hHdef
  set S := ∑ p : Fin n, if p.val + 1 = i.val then fp.fl_mul (F.That i p) (F.Lhat i p) else 0
    with hSdef
  set Sexact := ∑ p : Fin n, if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0
    with hSEdef
  set maskedAbs := ∑ p : Fin n, if p.val + 1 = i.val then |F.That i p| * |F.Lhat i p| else 0
    with hMdef
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub H S
  have hTval : F.That i i = (H - S) * (1 + δs) := by rw [halpha, hsub]
  have hres : F.Hhat i i - (∑ q : Fin n, F.That i q * F.Lhat i q)
      = (S - Sexact) - (H - S) * δs := by
    rw [hsum_eq, hTval, hLdiag]; ring
  -- |S - Sexact| ≤ u * maskedAbs
  have hSS : |S - Sexact| ≤ fp.u * maskedAbs := by
    rw [hSdef, hSEdef, ← Finset.sum_sub_distrib]
    calc |∑ p : Fin n,
              ((if p.val + 1 = i.val then fp.fl_mul (F.That i p) (F.Lhat i p) else 0)
                - (if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0))|
        ≤ ∑ p : Fin n,
            |(if p.val + 1 = i.val then fp.fl_mul (F.That i p) (F.Lhat i p) else 0)
              - (if p.val + 1 = i.val then F.That i p * F.Lhat i p else 0)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : Fin n,
            (if p.val + 1 = i.val then fp.u * (|F.That i p| * |F.Lhat i p|) else 0) := by
          apply Finset.sum_le_sum
          intro p _
          by_cases hp : p.val + 1 = i.val
          · rw [if_pos hp, if_pos hp, if_pos hp]
            obtain ⟨δm, hδm, hmul⟩ := fp.model_mul (F.That i p) (F.Lhat i p)
            rw [hmul,
              show F.That i p * F.Lhat i p * (1 + δm) - F.That i p * F.Lhat i p
                = (F.That i p * F.Lhat i p) * δm from by ring, abs_mul]
            calc |F.That i p * F.Lhat i p| * |δm|
                ≤ |F.That i p * F.Lhat i p| * fp.u :=
                  mul_le_mul_of_nonneg_left hδm (abs_nonneg _)
              _ = fp.u * (|F.That i p| * |F.Lhat i p|) := by rw [abs_mul]; ring
          · rw [if_neg hp, if_neg hp, if_neg hp, sub_zero, abs_zero]
      _ = fp.u * maskedAbs := by
          rw [hMdef, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _; split_ifs <;> ring
  -- |(H - S) * δs| ≤ gamma fp 1 * |T̂_{i,i}|
  have hu1 : fp.u < 1 := by
    have h := gammaValid_mono fp hnpos hval; unfold gammaValid at h; simpa using h
  have hHS : |(H - S) * δs| ≤ gamma fp 1 * |F.That i i| := by
    have hkey := absMulTheta_le (F.That i i) (H - S) δs fp.u hTval hδs hu1
    have hg1 : fp.u / (1 - fp.u) = gamma fp 1 := by simp [gamma]
    rwa [hg1] at hkey
  -- assemble
  have hM_nonneg : 0 ≤ maskedAbs := by
    rw [hMdef]; apply Finset.sum_nonneg; intro p _
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · exact le_refl 0
  have hu_le : fp.u ≤ gamma fp n := u_le_gamma fp hnpos hval
  have hg1_le : gamma fp 1 ≤ gamma fp n := gamma_mono fp hnpos hval
  have hLabs : |F.Lhat i i| = 1 := by rw [hLdiag, abs_one]
  rw [habs_eq, hres]
  have htri : |(S - Sexact) - (H - S) * δs| ≤ |S - Sexact| + |(H - S) * δs| := by
    rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
  calc |(S - Sexact) - (H - S) * δs|
      ≤ |S - Sexact| + |(H - S) * δs| := htri
    _ ≤ fp.u * maskedAbs + gamma fp 1 * |F.That i i| := add_le_add hSS hHS
    _ ≤ gamma fp n * maskedAbs + gamma fp n * |F.That i i| :=
        add_le_add (mul_le_mul_of_nonneg_right hu_le hM_nonneg)
          (mul_le_mul_of_nonneg_right hg1_le (abs_nonneg _))
    _ = gamma fp n * (maskedAbs + |F.That i i| * |F.Lhat i i|) := by
        rw [hLabs, mul_one]; ring

/-- **B2, strictly-upper case** (`j < i`).  Here `Ĥ_{j,i}` is literally the
rounded dot product `fl(T̂ row j · L̂ row i)`, so the residual is the standard
`γ_n` dot-product formation error. -/
theorem flAasen_H_eq_TLT_residual_upper (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (j i : Fin n) (hji : j.val < i.val) (hval : gammaValid fp n) :
    |(flAasen fp n A).Hhat j i
        - (∑ q : Fin n, (flAasen fp n A).That j q * (flAasen fp n A).Lhat i q)|
      ≤ gamma fp n * ∑ q : Fin n,
          |(flAasen fp n A).That j q| * |(flAasen fp n A).Lhat i q| := by
  have hrow : (flAasen fp n A).Hhat j i
      = fl_dotProduct fp n (fun q => (flAasen fp n A).That j q)
          (fun q => (flAasen fp n A).Lhat i q) := by
    rw [flAasen_Hhat_upper fp n A i j hji]
    unfold aUpperH
    congr 1
    · funext q
      exact That_iter_eq_flAasen fp n A j q i.val
        (by have := Nat.min_le_left j.val q.val; omega)
    · funext q; exact Lhat_row_iter_eq_flAasen fp n A i q
  rw [hrow]
  exact dotProduct_error_bound fp n (fun q => (flAasen fp n A).That j q)
    (fun q => (flAasen fp n A).Lhat i q) hval

/-- **B2 (headline for the middle factor).**  The computed working array `Ĥ`
equals the computed product `T̂ L̂ᵀ` up to a componentwise residual with the
`γ_n` coefficient:
`|Ĥ_{j,i} − ∑_q T̂_{j,q} L̂_{i,q}| ≤ γ_n ∑_q |T̂_{j,q}| |L̂_{i,q}|`.  The four cases
are: strictly-upper (dot-product error), diagonal (α-extraction), subdiagonal
(exact, `β̂_i = Ĥ_{i+1,i}`), and below-subdiagonal (both sides zero). -/
theorem flAasen_H_eq_TLT_residual (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hval : gammaValid fp n) (j i : Fin n) :
    |(flAasen fp n A).Hhat j i
        - (∑ q : Fin n, (flAasen fp n A).That j q * (flAasen fp n A).Lhat i q)|
      ≤ gamma fp n * ∑ q : Fin n,
          |(flAasen fp n A).That j q| * |(flAasen fp n A).Lhat i q| := by
  set F := flAasen fp n A with hF
  rcases lt_trichotomy j.val i.val with hlt | heq | hgt
  · rw [hF]; exact flAasen_H_eq_TLT_residual_upper fp n A j i hlt hval
  · have hji : j = i := Fin.ext heq
    subst hji
    rw [hF]; exact flAasen_H_eq_TLT_residual_diag fp n A j hval
  · rcases Nat.lt_or_ge (i.val + 1) j.val with hbelow | hle
    · -- below the subdiagonal: both sides vanish
      have hH0 : F.Hhat j i = 0 := by
        rw [hF]; exact flAasen_H_upperHessenberg fp n A j i hbelow
      have hsum0 : (∑ q : Fin n, F.That j q * F.Lhat i q) = 0 := by
        apply Finset.sum_eq_zero; intro q _
        by_cases hq : q.val ≤ i.val
        · rw [show F.That j q = 0 from by
              rw [hF]; exact flAasen_T_band fp n A j q (Or.inr (by omega)), zero_mul]
        · rw [show F.Lhat i q = 0 from by
              rw [hF]; exact flAasen_L_upper_zero fp n A i q (by omega), mul_zero]
      rw [hH0, hsum0, sub_zero, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hval)
        (Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
    · -- subdiagonal `j = i+1`: exact (residual zero)
      have hji' : j.val = i.val + 1 := by omega
      have hnext : i.val + 1 < n := by rw [← hji']; exact j.isLt
      have hje : j = (⟨i.val + 1, hnext⟩ : Fin n) := Fin.ext hji'
      have hLdiag_i : F.Lhat i i = 1 := by rw [hF]; exact flAasen_L_unit_diag fp n A i
      have hsum : (∑ q : Fin n, F.That j q * F.Lhat i q) = F.That j i := by
        rw [Finset.sum_eq_single i]
        · rw [hLdiag_i, mul_one]
        · intro q _ hqi
          by_cases hq : q.val ≤ i.val
          · rw [show F.That j q = 0 from by
                rw [hF]; exact flAasen_T_band fp n A j q
                  (Or.inr (by have : q.val ≠ i.val := fun h => hqi (Fin.ext h); omega)),
              zero_mul]
          · rw [show F.Lhat i q = 0 from by
                rw [hF]; exact flAasen_L_upper_zero fp n A i q (by omega), mul_zero]
        · intro h; exact absurd (Finset.mem_univ i) h
      have hTH : F.That j i = F.Hhat j i := by
        rw [hF, hje]; exact flAasen_T_subdiagonal_eq_H fp n A i hnext
      rw [hsum, hTH, sub_self, abs_zero]
      exact mul_nonneg (gamma_nonneg fp hval)
        (Finset.sum_nonneg (fun q _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))

/-! ### B1 — the `A = L̂ Ĥ` residual on the lower triangle -/

/-- Split a finite sum whose summand vanishes above index `c` into its
`j < c` part plus the `j = c` term.  This isolates the "self" term written by
each Aasen recurrence (the diagonal `Ĥ_{i,i}`, or the pivot product). -/
theorem sum_split_lt_self (n : ℕ) (c : Fin n) (g : Fin n → ℝ)
    (hsupp : ∀ j : Fin n, c.val < j.val → g j = 0) :
    (∑ j : Fin n, g j) = (∑ j : Fin n, if j.val < c.val then g j else 0) + g c := by
  have hpt : ∀ j : Fin n,
      g j = (if j.val < c.val then g j else 0) + (if j = c then g j else 0) := by
    intro j
    by_cases h1 : j.val < c.val
    · have h2 : j ≠ c := by intro h; rw [h] at h1; omega
      rw [if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : j = c
      · rw [if_neg h1, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h2, add_zero]
        have hjc : j.val ≠ c.val := fun h => h2 (Fin.ext h)
        exact hsupp j (by omega)
  calc (∑ j : Fin n, g j)
      = ∑ j : Fin n,
          ((if j.val < c.val then g j else 0) + (if j = c then g j else 0)) :=
        Finset.sum_congr rfl (fun j _ => hpt j)
    _ = (∑ j : Fin n, if j.val < c.val then g j else 0)
          + (∑ j : Fin n, if j = c then g j else 0) := by rw [Finset.sum_add_distrib]
    _ = (∑ j : Fin n, if j.val < c.val then g j else 0) + g c := by congr 1; simp

/-- Split variant with the `j ≤ i` mask used by the subdiagonal/next-column
recurrences (self term at `next`, `next = i+1`). -/
theorem sum_split_le_next (n : ℕ) (i next : Fin n) (hnext : next.val = i.val + 1)
    (g : Fin n → ℝ) (hsupp : ∀ j : Fin n, next.val < j.val → g j = 0) :
    (∑ j : Fin n, g j) = (∑ j : Fin n, if j.val ≤ i.val then g j else 0) + g next := by
  rw [sum_split_lt_self n next g hsupp]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val ≤ i.val
  · rw [if_pos (by omega : j.val < next.val), if_pos hj]
  · rw [if_neg (by omega : ¬ j.val < next.val), if_neg hj]

/-- **B1, diagonal case** (`k = i`, equation (11.12)).  The residual
`(L̂ Ĥ)_{i,i} − A_{i,i}` is the rounding of the `fl_sub`/`fl_dotProduct` that
defines `Ĥ_{i,i}`; it is bounded by `γ_{2n} ∑_j |L̂_{i,j}| |Ĥ_{j,i}|`. -/
theorem flAasen_A_eq_LH_residual_diag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i : Fin n) (hval : gammaValid fp (2 * n)) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat i j * (flAasen fp n A).Hhat j i) - A i i|
      ≤ gamma fp (2 * n)
        * ∑ j : Fin n, |(flAasen fp n A).Lhat i j| * |(flAasen fp n A).Hhat j i| := by
  set F := flAasen fp n A with hF
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hvaln : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hu1 : fp.u < 1 := by
    have h := gammaValid_mono fp (show 1 ≤ n from hnpos) hvaln
    unfold gammaValid at h; simpa using h
  have hLdiag : F.Lhat i i = 1 := by rw [hF]; exact flAasen_L_unit_diag fp n A i
  have hsupp : ∀ j : Fin n, i.val < j.val → F.Lhat i j * F.Hhat j i = 0 := fun j hj => by
    rw [show F.Lhat i j = 0 from by rw [hF]; exact flAasen_L_upper_zero fp n A i j hj, zero_mul]
  have hsupp_abs : ∀ j : Fin n, i.val < j.val → |F.Lhat i j| * |F.Hhat j i| = 0 := fun j hj => by
    rw [show F.Lhat i j = 0 from by rw [hF]; exact flAasen_L_upper_zero fp n A i j hj,
      abs_zero, zero_mul]
  have hsum_split := sum_split_lt_self n i (fun j => F.Lhat i j * F.Hhat j i) hsupp
  have habs_split := sum_split_lt_self n i (fun j => |F.Lhat i j| * |F.Hhat j i|) hsupp_abs
  simp only at hsum_split habs_split
  have hrec : F.Hhat i i = fp.fl_sub (A i i)
      (fl_dotProduct fp n (fun j => if j.val < i.val then F.Lhat i j else 0)
        (fun j => if j.val < i.val then F.Hhat j i else 0)) := by
    rw [hF]; exact flAasen_recurrence_diagonal fp n A i
  have hb := dotProduct_error_bound fp n
    (fun j => if j.val < i.val then F.Lhat i j else 0)
    (fun j => if j.val < i.val then F.Hhat j i else 0) hvaln
  have hconv1 : (∑ j : Fin n, (if j.val < i.val then F.Lhat i j else 0)
        * (if j.val < i.val then F.Hhat j i else 0))
      = ∑ j : Fin n, if j.val < i.val then F.Lhat i j * F.Hhat j i else 0 :=
    Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hconv2 : (∑ j : Fin n, |if j.val < i.val then F.Lhat i j else 0|
        * |if j.val < i.val then F.Hhat j i else 0|)
      = ∑ j : Fin n, if j.val < i.val then |F.Lhat i j| * |F.Hhat j i| else 0 :=
    Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  rw [hconv1, hconv2] at hb
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (A i i)
    (fl_dotProduct fp n (fun j => if j.val < i.val then F.Lhat i j else 0)
      (fun j => if j.val < i.val then F.Hhat j i else 0))
  set s := fl_dotProduct fp n (fun j => if j.val < i.val then F.Lhat i j else 0)
    (fun j => if j.val < i.val then F.Hhat j i else 0) with hsdef
  set msum := ∑ j : Fin n, if j.val < i.val then F.Lhat i j * F.Hhat j i else 0 with hmsum
  set mabs := ∑ j : Fin n, if j.val < i.val then |F.Lhat i j| * |F.Hhat j i| else 0 with hmabs
  have hHii : F.Hhat i i = (A i i - s) * (1 + δs) := by rw [hrec, hsub]
  have hres : (∑ j : Fin n, F.Lhat i j * F.Hhat j i) - A i i
      = (msum - s) + (A i i - s) * δs := by
    rw [hsum_split, hLdiag, one_mul, hHii]; ring
  have hAs : |(A i i - s) * δs| ≤ gamma fp 1 * |F.Hhat i i| := by
    have hkey := absMulTheta_le (F.Hhat i i) (A i i - s) δs fp.u hHii hδs hu1
    have hg1 : fp.u / (1 - fp.u) = gamma fp 1 := by simp [gamma]
    rwa [hg1] at hkey
  have hmabs_nonneg : 0 ≤ mabs := by
    rw [hmabs]; apply Finset.sum_nonneg; intro j _
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · exact le_refl 0
  have hg_n_le : gamma fp n ≤ gamma fp (2 * n) := gamma_mono fp (by omega) hval
  have hg_1_le : gamma fp 1 ≤ gamma fp (2 * n) := gamma_mono fp (by omega) hval
  have hLabs : |F.Lhat i i| = 1 := by rw [hLdiag, abs_one]
  rw [habs_split, hLabs, one_mul, hres]
  calc |(msum - s) + (A i i - s) * δs|
      ≤ |msum - s| + |(A i i - s) * δs| := abs_add_le _ _
    _ = |s - msum| + |(A i i - s) * δs| := by rw [abs_sub_comm]
    _ ≤ gamma fp n * mabs + gamma fp 1 * |F.Hhat i i| := add_le_add hb hAs
    _ ≤ gamma fp (2 * n) * mabs + gamma fp (2 * n) * |F.Hhat i i| :=
        add_le_add (mul_le_mul_of_nonneg_right hg_n_le hmabs_nonneg)
          (mul_le_mul_of_nonneg_right hg_1_le (abs_nonneg _))
    _ = gamma fp (2 * n) * (mabs + |F.Hhat i i|) := by ring

/-- **B1, subdiagonal case** (`k = i+1`, equation (11.13)).  Same structure as
the diagonal case, with the `j ≤ i` mask and the unit-diagonal self term
`Ĥ_{k,i}`. -/
theorem flAasen_A_eq_LH_residual_subdiag (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (i k : Fin n) (hk : k.val = i.val + 1) (hval : gammaValid fp (2 * n)) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat k j * (flAasen fp n A).Hhat j i) - A k i|
      ≤ gamma fp (2 * n)
        * ∑ j : Fin n, |(flAasen fp n A).Lhat k j| * |(flAasen fp n A).Hhat j i| := by
  set F := flAasen fp n A with hF
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hvaln : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hu1 : fp.u < 1 := by
    have h := gammaValid_mono fp (show 1 ≤ n from hnpos) hvaln
    unfold gammaValid at h; simpa using h
  have hn : i.val + 1 < n := by rw [← hk]; exact k.isLt
  have hke : k = (⟨i.val + 1, hn⟩ : Fin n) := Fin.ext hk
  have hLdiag : F.Lhat k k = 1 := by rw [hF]; exact flAasen_L_unit_diag fp n A k
  have hsupp : ∀ j : Fin n, k.val < j.val → F.Lhat k j * F.Hhat j i = 0 := fun j hj => by
    rw [show F.Lhat k j = 0 from by rw [hF]; exact flAasen_L_upper_zero fp n A k j hj, zero_mul]
  have hsupp_abs : ∀ j : Fin n, k.val < j.val → |F.Lhat k j| * |F.Hhat j i| = 0 := fun j hj => by
    rw [show F.Lhat k j = 0 from by rw [hF]; exact flAasen_L_upper_zero fp n A k j hj,
      abs_zero, zero_mul]
  have hsum_split := sum_split_le_next n i k hk (fun j => F.Lhat k j * F.Hhat j i) hsupp
  have habs_split := sum_split_le_next n i k hk (fun j => |F.Lhat k j| * |F.Hhat j i|) hsupp_abs
  simp only at hsum_split habs_split
  have hrec : F.Hhat k i = fp.fl_sub (A k i)
      (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
        (fun j => if j.val ≤ i.val then F.Hhat j i else 0)) := by
    rw [hF, hke]; exact flAasen_recurrence_subdiagonal fp n A i hn
  have hb := dotProduct_error_bound fp n
    (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0) hvaln
  have hconv1 : (∑ j : Fin n, (if j.val ≤ i.val then F.Lhat k j else 0)
        * (if j.val ≤ i.val then F.Hhat j i else 0))
      = ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0 :=
    Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hconv2 : (∑ j : Fin n, |if j.val ≤ i.val then F.Lhat k j else 0|
        * |if j.val ≤ i.val then F.Hhat j i else 0|)
      = ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0 :=
    Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  rw [hconv1, hconv2] at hb
  obtain ⟨δs, hδs, hsub⟩ := fp.model_sub (A k i)
    (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
      (fun j => if j.val ≤ i.val then F.Hhat j i else 0))
  set s := fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0) with hsdef
  set msum := ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0 with hmsum
  set mabs := ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0 with hmabs
  have hHki : F.Hhat k i = (A k i - s) * (1 + δs) := by rw [hrec, hsub]
  have hres : (∑ j : Fin n, F.Lhat k j * F.Hhat j i) - A k i
      = (msum - s) + (A k i - s) * δs := by
    rw [hsum_split, hLdiag, one_mul, hHki]; ring
  have hAs : |(A k i - s) * δs| ≤ gamma fp 1 * |F.Hhat k i| := by
    have hkey := absMulTheta_le (F.Hhat k i) (A k i - s) δs fp.u hHki hδs hu1
    have hg1 : fp.u / (1 - fp.u) = gamma fp 1 := by simp [gamma]
    rwa [hg1] at hkey
  have hmabs_nonneg : 0 ≤ mabs := by
    rw [hmabs]; apply Finset.sum_nonneg; intro j _
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · exact le_refl 0
  have hg_n_le : gamma fp n ≤ gamma fp (2 * n) := gamma_mono fp (by omega) hval
  have hg_1_le : gamma fp 1 ≤ gamma fp (2 * n) := gamma_mono fp (by omega) hval
  have hLabs : |F.Lhat k k| = 1 := by rw [hLdiag, abs_one]
  rw [habs_split, hLabs, one_mul, hres]
  calc |(msum - s) + (A k i - s) * δs|
      ≤ |msum - s| + |(A k i - s) * δs| := abs_add_le _ _
    _ = |s - msum| + |(A k i - s) * δs| := by rw [abs_sub_comm]
    _ ≤ gamma fp n * mabs + gamma fp 1 * |F.Hhat k i| := add_le_add hb hAs
    _ ≤ gamma fp (2 * n) * mabs + gamma fp (2 * n) * |F.Hhat k i| :=
        add_le_add (mul_le_mul_of_nonneg_right hg_n_le hmabs_nonneg)
          (mul_le_mul_of_nonneg_right hg_1_le (abs_nonneg _))
    _ = gamma fp (2 * n) * (mabs + |F.Hhat k i|) := by ring

/-- **B1, general lower case** (`k ≥ i+2`, equation (11.14)).  Here the "self"
term is the pivot product `L̂_{k,i+1} Ĥ_{i+1,i}`, whose defining `fl_div`/`fl_sub`
carries a two-operation relative error `θ` (`|θ| ≤ γ₂`); the backward-reciprocal
bound folds it into the `γ_{2n}` coefficient. -/
theorem flAasen_A_eq_LH_residual_general (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hpivots : FlAasenPivots fp n A) (i : Fin n) (hnext : i.val + 1 < n) (k : Fin n)
    (hk : i.val + 2 ≤ k.val) (hval : gammaValid fp (2 * n)) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat k j * (flAasen fp n A).Hhat j i) - A k i|
      ≤ gamma fp (2 * n)
        * ∑ j : Fin n, |(flAasen fp n A).Lhat k j| * |(flAasen fp n A).Hhat j i| := by
  set F := flAasen fp n A with hF
  have hklt : k.val < n := k.isLt
  have hn3 : 3 ≤ n := by omega
  have hvaln : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hval2 : gammaValid fp 2 := gammaValid_mono fp (by omega) hval
  have hval4 : gammaValid fp (2 * 2) := gammaValid_mono fp (by omega) hval
  have hγ2_lt1 : gamma fp 2 < 1 := by
    have h4 : ((2 * 2 : ℕ) : ℝ) * fp.u < 1 := hval4
    have h4' : (4 : ℝ) * fp.u < 1 := by push_cast at h4; linarith
    have hu0 : (0 : ℝ) ≤ fp.u := fp.u_nonneg
    unfold gamma
    rw [div_lt_one (by push_cast; nlinarith)]
    push_cast; nlinarith
  set next := (⟨i.val + 1, hnext⟩ : Fin n) with hnextdef
  have hnextval : next.val = i.val + 1 := rfl
  have hpiv : F.Hhat next i ≠ 0 := by rw [hF, hnextdef]; exact hpivots i.val hnext
  have hsupp : ∀ j : Fin n, next.val < j.val → F.Lhat k j * F.Hhat j i = 0 := fun j hj => by
    rw [show F.Hhat j i = 0 from by
        rw [hF]; exact flAasen_H_upperHessenberg fp n A j i (by omega), mul_zero]
  have hsupp_abs : ∀ j : Fin n, next.val < j.val → |F.Lhat k j| * |F.Hhat j i| = 0 :=
    fun j hj => by
      rw [show F.Hhat j i = 0 from by
          rw [hF]; exact flAasen_H_upperHessenberg fp n A j i (by omega), abs_zero, mul_zero]
  have hsum_split := sum_split_le_next n i next hnextval
    (fun j => F.Lhat k j * F.Hhat j i) hsupp
  have habs_split := sum_split_le_next n i next hnextval
    (fun j => |F.Lhat k j| * |F.Hhat j i|) hsupp_abs
  simp only at hsum_split habs_split
  have hrec_L : F.Lhat k next = fp.fl_div
      (fp.fl_sub (A k i)
        (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
          (fun j => if j.val ≤ i.val then F.Hhat j i else 0)))
      (F.Hhat next i) := by
    rw [hF, hnextdef]; exact flAasen_recurrence_nextColumn fp n A i hnext k hk
  have hb := dotProduct_error_bound fp n
    (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0) hvaln
  have hconv1 : (∑ j : Fin n, (if j.val ≤ i.val then F.Lhat k j else 0)
        * (if j.val ≤ i.val then F.Hhat j i else 0))
      = ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0 :=
    Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  have hconv2 : (∑ j : Fin n, |if j.val ≤ i.val then F.Lhat k j else 0|
        * |if j.val ≤ i.val then F.Hhat j i else 0|)
      = ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0 :=
    Finset.sum_congr rfl (fun j _ => by split_ifs <;> simp)
  rw [hconv1, hconv2] at hb
  obtain ⟨θ, hθ, hrel⟩ := higham11_14_fl_aasen_next_column_update_rel_error fp (A k i)
    (fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
      (fun j => if j.val ≤ i.val then F.Hhat j i else 0)) (F.Hhat next i) hpiv hval2
  set s := fl_dotProduct fp n (fun j => if j.val ≤ i.val then F.Lhat k j else 0)
    (fun j => if j.val ≤ i.val then F.Hhat j i else 0) with hsdef
  set msum := ∑ j : Fin n, if j.val ≤ i.val then F.Lhat k j * F.Hhat j i else 0 with hmsum
  set mabs := ∑ j : Fin n, if j.val ≤ i.val then |F.Lhat k j| * |F.Hhat j i| else 0 with hmabs
  have hgnext : F.Lhat k next * F.Hhat next i = (A k i - s) * (1 + θ) := by
    rw [hrec_L, hrel]; field_simp
  have hres : (∑ j : Fin n, F.Lhat k j * F.Hhat j i) - A k i
      = (msum - s) + (A k i - s) * θ := by
    rw [hsum_split, hgnext]; ring
  have hAs : |(A k i - s) * θ|
      ≤ gamma fp (2 * n) * (|F.Lhat k next| * |F.Hhat next i|) := by
    have hkey := absMulTheta_le (F.Lhat k next * F.Hhat next i) (A k i - s) θ
      (gamma fp 2) hgnext hθ hγ2_lt1
    have hcoef : gamma fp 2 / (1 - gamma fp 2) ≤ gamma fp (2 * n) :=
      le_trans (gamma_selfDiv_le fp 2 hval4) (gamma_mono fp (by omega) hval)
    calc |(A k i - s) * θ|
        ≤ gamma fp 2 / (1 - gamma fp 2) * |F.Lhat k next * F.Hhat next i| := hkey
      _ ≤ gamma fp (2 * n) * |F.Lhat k next * F.Hhat next i| :=
          mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
      _ = gamma fp (2 * n) * (|F.Lhat k next| * |F.Hhat next i|) := by rw [abs_mul]
  have hmabs_nonneg : 0 ≤ mabs := by
    rw [hmabs]; apply Finset.sum_nonneg; intro j _
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
    · exact le_refl 0
  have hg_n_le : gamma fp n ≤ gamma fp (2 * n) := gamma_mono fp (by omega) hval
  rw [habs_split, hres]
  calc |(msum - s) + (A k i - s) * θ|
      ≤ |msum - s| + |(A k i - s) * θ| := abs_add_le _ _
    _ = |s - msum| + |(A k i - s) * θ| := by rw [abs_sub_comm]
    _ ≤ gamma fp n * mabs + gamma fp (2 * n) * (|F.Lhat k next| * |F.Hhat next i|) :=
        add_le_add hb hAs
    _ ≤ gamma fp (2 * n) * mabs
          + gamma fp (2 * n) * (|F.Lhat k next| * |F.Hhat next i|) :=
        add_le_add (mul_le_mul_of_nonneg_right hg_n_le hmabs_nonneg) (le_refl _)
    _ = gamma fp (2 * n) * (mabs + |F.Lhat k next| * |F.Hhat next i|) := by ring

/-- **B1 (headline for `A = L̂ Ĥ`).**  On the lower triangle (`i ≤ k`) the
computed product `L̂ Ĥ` reproduces `A` up to the componentwise residual
`|(L̂ Ĥ)_{k,i} − A_{k,i}| ≤ γ_{2n} ∑_j |L̂_{k,j}| |Ĥ_{j,i}|`.  Dispatches to the
diagonal (11.12), subdiagonal (11.13), and general (11.14) cases. -/
theorem flAasen_A_eq_LH_residual (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hpivots : FlAasenPivots fp n A) (hval : gammaValid fp (2 * n)) (k i : Fin n)
    (hki : i.val ≤ k.val) :
    |(∑ j : Fin n, (flAasen fp n A).Lhat k j * (flAasen fp n A).Hhat j i) - A k i|
      ≤ gamma fp (2 * n)
        * ∑ j : Fin n, |(flAasen fp n A).Lhat k j| * |(flAasen fp n A).Hhat j i| := by
  have hkn : k.val < n := k.isLt
  rcases Nat.lt_or_ge i.val k.val with hlt | hge
  · rcases Nat.lt_or_ge (i.val + 1) k.val with hgen | hsub
    · exact flAasen_A_eq_LH_residual_general fp n A hpivots i (by omega) k (by omega) hval
    · exact flAasen_A_eq_LH_residual_subdiag fp n A i k (by omega) hval
  · have hik : k = i := Fin.ext (by omega)
    subst hik
    exact flAasen_A_eq_LH_residual_diag fp n A k hval

/-! ### B3 — the headline `L̂ T̂ L̂ᵀ` factorization residual -/

/-- **B3 on the lower triangle** (`j ≤ i`).  Combines B1 (`A = L̂ Ĥ`) with B2
(`Ĥ = T̂ L̂ᵀ`): writing `L̂ T̂ L̂ᵀ = L̂ (Ĥ − E₂) = A + E₁ − L̂ E₂` and folding the
constants `γ_{2n}(1+γ_n)+γ_n ≤ γ_{3n}`. -/
theorem fl_aasen_factorization_residual_lower (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hpivots : FlAasenPivots fp n A) (hval : gammaValid fp (3 * n))
    (i j : Fin n) (hji : j.val ≤ i.val) :
    |(∑ p : Fin n, ∑ q : Fin n,
        (flAasen fp n A).Lhat i p * (flAasen fp n A).That p q * (flAasen fp n A).Lhat j q)
        - A i j|
      ≤ gamma fp (3 * n)
        * (∑ p : Fin n, ∑ q : Fin n,
            |(flAasen fp n A).Lhat i p| * |(flAasen fp n A).That p q|
              * |(flAasen fp n A).Lhat j q|) := by
  set F := flAasen fp n A with hF
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hvaln : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hval2n : gammaValid fp (2 * n) := gammaValid_mono fp (by omega) hval
  set P := ∑ p : Fin n, ∑ q : Fin n, F.Lhat i p * F.That p q * F.Lhat j q with hPdef
  set TAsum := ∑ p : Fin n, ∑ q : Fin n, |F.Lhat i p| * |F.That p q| * |F.Lhat j q| with hTAdef
  set Q := ∑ p : Fin n, F.Lhat i p * F.Hhat p j with hQdef
  set SH := ∑ p : Fin n, |F.Lhat i p| * |F.Hhat p j| with hSHdef
  have hTA_eq : TAsum = ∑ p : Fin n, |F.Lhat i p| * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) := by
    rw [hTAdef]; apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring
  have hTA_nonneg : 0 ≤ TAsum := by
    rw [hTAdef]; apply Finset.sum_nonneg; intro p _; apply Finset.sum_nonneg; intro q _
    positivity
  have hB1 : |Q - A i j| ≤ gamma fp (2 * n) * SH :=
    flAasen_A_eq_LH_residual fp n A hpivots hval2n i j hji
  -- P - Q rewritten by rows
  have hPQ_eq : P - Q
      = ∑ p : Fin n, F.Lhat i p * ((∑ q : Fin n, F.That p q * F.Lhat j q) - F.Hhat p j) := by
    rw [hPdef, hQdef, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro p _
    rw [mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl; intro q _; ring
  have hPQ_le : |P - Q| ≤ gamma fp n * TAsum := by
    rw [hPQ_eq]
    calc |∑ p : Fin n, F.Lhat i p * ((∑ q : Fin n, F.That p q * F.Lhat j q) - F.Hhat p j)|
        ≤ ∑ p : Fin n, |F.Lhat i p * ((∑ q : Fin n, F.That p q * F.Lhat j q) - F.Hhat p j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p : Fin n,
            |F.Lhat i p| * (gamma fp n * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|)) := by
          apply Finset.sum_le_sum; intro p _
          rw [abs_mul]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_sub_comm]
          exact flAasen_H_eq_TLT_residual fp n A hvaln p j
      _ = gamma fp n * TAsum := by
          rw [hTA_eq, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  have hSH_le : SH ≤ (1 + gamma fp n) * TAsum := by
    rw [hSHdef]
    calc ∑ p : Fin n, |F.Lhat i p| * |F.Hhat p j|
        ≤ ∑ p : Fin n,
            |F.Lhat i p| * ((1 + gamma fp n) * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|)) := by
          apply Finset.sum_le_sum; intro p _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          have hb2 := flAasen_H_eq_TLT_residual fp n A hvaln p j
          have htl : |(∑ q : Fin n, F.That p q * F.Lhat j q)|
              ≤ ∑ q : Fin n, |F.That p q| * |F.Lhat j q| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
            apply Finset.sum_le_sum; intro q _; rw [abs_mul]
          calc |F.Hhat p j|
              = |(∑ q : Fin n, F.That p q * F.Lhat j q)
                  + (F.Hhat p j - ∑ q : Fin n, F.That p q * F.Lhat j q)| := by congr 1; ring
            _ ≤ |(∑ q : Fin n, F.That p q * F.Lhat j q)|
                  + |F.Hhat p j - (∑ q : Fin n, F.That p q * F.Lhat j q)| := abs_add_le _ _
            _ ≤ (∑ q : Fin n, |F.That p q| * |F.Lhat j q|)
                  + gamma fp n * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) := add_le_add htl hb2
            _ = (1 + gamma fp n) * (∑ q : Fin n, |F.That p q| * |F.Lhat j q|) := by ring
      _ = (1 + gamma fp n) * TAsum := by
          rw [hTA_eq, Finset.mul_sum]; apply Finset.sum_congr rfl; intro p _; ring
  -- combine
  have hcombine : |P - A i j| ≤ |Q - A i j| + |P - Q| := by
    have h := abs_add_le (Q - A i j) (P - Q)
    rw [show Q - A i j + (P - Q) = P - A i j from by ring] at h
    exact h
  have hfold : gamma fp (2 * n) + gamma fp (2 * n) * gamma fp n + gamma fp n
      ≤ gamma fp (3 * n) := by
    have h := gamma_sum_le fp (2 * n) n (by rw [show 2 * n + n = 3 * n from by ring]; exact hval)
    rw [show 2 * n + n = 3 * n from by ring] at h
    linarith
  calc |P - A i j|
      ≤ |Q - A i j| + |P - Q| := hcombine
    _ ≤ gamma fp (2 * n) * SH + gamma fp n * TAsum := add_le_add hB1 hPQ_le
    _ ≤ gamma fp (2 * n) * ((1 + gamma fp n) * TAsum) + gamma fp n * TAsum :=
        add_le_add (mul_le_mul_of_nonneg_left hSH_le (gamma_nonneg fp hval2n)) (le_refl _)
    _ = (gamma fp (2 * n) + gamma fp (2 * n) * gamma fp n + gamma fp n) * TAsum := by ring
    _ ≤ gamma fp (3 * n) * TAsum := mul_le_mul_of_nonneg_right hfold hTA_nonneg

/-- **B3 (headline): the direct Aasen factorization residual.**  The computed
factors `L̂, T̂` (from the coupled floating-point Aasen sweep of module #2)
satisfy
`|(L̂ T̂ L̂ᵀ)_{i,j} − A_{i,j}| ≤ γ_{3n} (|L̂| |T̂| |L̂ᵀ|)_{i,j}`
for every entry.  This is a residual on the *computed* factors — no exact
reference `L, T` appears, and no residual is divided by a pivot.  The only
hypotheses are the nonzero-pivot predicate, symmetry of `A`, and the standard
`gammaValid fp (3*n)` regime.

Constant note.  The printed Theorem 11.8 displays `γ_{3n+1}`; the coefficient
proved here is `γ_{3n}`, which is *smaller*, hence a strictly stronger bound of
the same first-order class.  It arises as `γ_{2n}(1+γ_n) + γ_n ≤ γ_{3n}`, where
`γ_{2n}` is the `A = L̂ Ĥ` (B1) coefficient and `γ_n` the `Ĥ = T̂ L̂ᵀ` (B2) one.
Module #4 feeds this residual to
`higham11_8_aasen_source_backward_error_of_factor_and_solve_residuals`. -/
theorem fl_aasen_factorization_residual (fp : FPModel) (n : ℕ) (A : Fin n → Fin n → ℝ)
    (hpivots : FlAasenPivots fp n A) (hsymm : ∀ i j : Fin n, A i j = A j i)
    (hval : gammaValid fp (3 * n)) (i j : Fin n) :
    |(∑ p : Fin n, ∑ q : Fin n,
        (flAasen fp n A).Lhat i p * (flAasen fp n A).That p q * (flAasen fp n A).Lhat j q)
        - A i j|
      ≤ gamma fp (3 * n)
        * (∑ p : Fin n, ∑ q : Fin n,
            |(flAasen fp n A).Lhat i p| * |(flAasen fp n A).That p q|
              * |(flAasen fp n A).Lhat j q|) := by
  rcases le_total j.val i.val with hji | hij
  · exact fl_aasen_factorization_residual_lower fp n A hpivots hval i j hji
  · have hlow := fl_aasen_factorization_residual_lower fp n A hpivots hval j i hij
    have hTsym : ∀ r c : Fin n, (flAasen fp n A).That r c = (flAasen fp n A).That c r :=
      flAasen_T_symm fp n A
    have hPsym : (∑ p : Fin n, ∑ q : Fin n,
          (flAasen fp n A).Lhat j p * (flAasen fp n A).That p q * (flAasen fp n A).Lhat i q)
        = ∑ p : Fin n, ∑ q : Fin n,
          (flAasen fp n A).Lhat i p * (flAasen fp n A).That p q * (flAasen fp n A).Lhat j q := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [hTsym b a]; ring
    have hTAsym : (∑ p : Fin n, ∑ q : Fin n,
          |(flAasen fp n A).Lhat j p| * |(flAasen fp n A).That p q| * |(flAasen fp n A).Lhat i q|)
        = ∑ p : Fin n, ∑ q : Fin n,
          |(flAasen fp n A).Lhat i p| * |(flAasen fp n A).That p q| * |(flAasen fp n A).Lhat j q| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro a _
      apply Finset.sum_congr rfl; intro b _
      rw [hTsym b a]; ring
    rw [hPsym, hTAsym, hsymm j i] at hlow
    exact hlow

end NumStability.Ch11Closure.AasenDirect
