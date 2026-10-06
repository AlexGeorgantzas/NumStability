import HighamBench.P12Definitions

namespace HighamBench


private lemma p12_betaR_pos (fmt : P12RadixFormat) : 0 < fmt.betaR := by
  rw [P12RadixFormat.betaR]
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) fmt.beta_ge_two)

private lemma p12_scale_pos (fmt : P12RadixFormat) (e : ℤ) :
    0 < fmt.scale e := by
  exact zpow_pos (p12_betaR_pos fmt) e

private lemma p12_mantissaBound_pos (fmt : P12RadixFormat) :
    0 < fmt.mantissaBound := by
  exact pow_pos (p12_betaR_pos fmt) fmt.precision

private lemma p12_mantissaBound_eq_natCast (fmt : P12RadixFormat) :
    fmt.mantissaBound = (fmt.beta ^ fmt.precision : ℕ) := by
  simp [P12RadixFormat.mantissaBound, P12RadixFormat.betaR]

private lemma p12_condition7Ceiling_lt_mantissaBound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  have hbpos : 0 < fmt.beta := lt_of_lt_of_le (by decide) fmt.beta_ge_two
  have hhpos : 0 < fmt.beta / 2 := Nat.div_pos fmt.beta_ge_two (by decide)
  have hpowpos : 0 < fmt.beta ^ fmt.precision := pow_pos hbpos _
  have hn : fmt.beta ^ fmt.precision - fmt.beta / 2 <
      fmt.beta ^ fmt.precision := Nat.sub_lt hpowpos hhpos
  rw [P12RadixFormat.condition7Ceiling, P12RadixFormat.mantissaBound,
    P12RadixFormat.betaR]
  exact_mod_cast hn

private lemma p12_half_add_condition7 (fmt : P12RadixFormat) :
    fmt.halfRadixFloor + fmt.condition7Ceiling = fmt.mantissaBound := by
  have hbpos : 0 < fmt.beta := lt_of_lt_of_le (by decide) fmt.beta_ge_two
  have hbpow : fmt.beta ≤ fmt.beta ^ fmt.precision := Nat.le_pow fmt.precision_pos
  have hh : fmt.beta / 2 ≤ fmt.beta ^ fmt.precision :=
    le_trans (Nat.div_le_self _ _) hbpow
  rw [P12RadixFormat.halfRadixFloor, P12RadixFormat.condition7Ceiling,
    p12_mantissaBound_eq_natCast]
  norm_cast
  omega

private lemma p12_two_scale_le_succ (fmt : P12RadixFormat) (e : ℤ) :
    2 * fmt.scale e ≤ fmt.scale (e + 1) := by
  have hscale : fmt.scale (e + 1) = fmt.scale e * fmt.betaR := by
    change fmt.betaR ^ (e + 1) = fmt.betaR ^ e * fmt.betaR
    exact zpow_add_one₀ (ne_of_gt (p12_betaR_pos fmt)) e
  have hb2 : (2 : ℝ) ≤ fmt.betaR := by
    rw [P12RadixFormat.betaR]
    exact_mod_cast fmt.beta_ge_two
  rw [hscale]
  nlinarith [p12_scale_pos fmt e]

private lemma p12_scale_of_le (fmt : P12RadixFormat) {e₁ e₂ : ℤ}
    (h : e₁ ≤ e₂) :
    fmt.scale e₂ = fmt.scale e₁ * (fmt.beta ^ (e₂ - e₁).toNat : ℕ) := by
  have hn : ((e₂ - e₁).toNat : ℤ) = e₂ - e₁ :=
    Int.toNat_of_nonneg (sub_nonneg.mpr h)
  have he : e₂ = e₁ + ((e₂ - e₁).toNat : ℤ) := by omega
  have hb : fmt.betaR ≠ 0 := ne_of_gt (p12_betaR_pos fmt)
  calc
    fmt.scale e₂ = fmt.betaR ^ e₂ := rfl
    _ = fmt.betaR ^ (e₁ + ((e₂ - e₁).toNat : ℤ)) :=
      congrArg (fun e : ℤ ↦ fmt.betaR ^ e) he
    _ = fmt.betaR ^ e₁ * fmt.betaR ^ ((e₂ - e₁).toNat : ℤ) :=
      zpow_add₀ hb _ _
    _ = fmt.betaR ^ e₁ * fmt.betaR ^ (e₂ - e₁).toNat := by
      rw [zpow_natCast]
    _ = fmt.scale e₁ * (fmt.beta ^ (e₂ - e₁).toNat : ℕ) := by
      rw [P12RadixFormat.scale]
      congr 1
      simp [P12RadixFormat.betaR]

private lemma p12_scale_mono (fmt : P12RadixFormat) {e₁ e₂ : ℤ}
    (h : e₁ ≤ e₂) : fmt.scale e₁ ≤ fmt.scale e₂ := by
  rw [p12_scale_of_le fmt h]
  have hb : 1 ≤ fmt.beta := le_trans (by decide) fmt.beta_ge_two
  have hq : (1 : ℝ) ≤ (fmt.beta ^ (e₂ - e₁).toNat : ℕ) := by
    exact_mod_cast one_le_pow₀ hb
  nlinarith [p12_scale_pos fmt e₁]

private def p12_representation_at_lower_exponent
    (fmt : P12RadixFormat) {v : ℝ} (r : P12Representation fmt v)
    {e : ℤ} (hemin : fmt.emin ≤ e) (he : e ≤ r.exponent)
    (hv : |v| < fmt.mantissaBound * fmt.scale e) :
    P12Representation fmt v := by
  let q : ℕ := fmt.beta ^ (r.exponent - e).toNat
  let m : ℤ := r.mantissa * (q : ℤ)
  have hscale : fmt.scale r.exponent = fmt.scale e * (q : ℕ) := by
    simpa [q] using p12_scale_of_le fmt he
  have hvalue : v = (m : ℝ) * fmt.scale e := by
    rw [r.value_eq, hscale]
    simp only [m, Int.cast_mul, Int.cast_natCast, Nat.cast_pow]
    ring
  have hmabs : |(m : ℝ)| < fmt.mantissaBound := by
    rw [hvalue, abs_mul, abs_of_pos (p12_scale_pos fmt e)] at hv
    nlinarith [p12_scale_pos fmt e]
  have hmbounds := (abs_lt.mp hmabs)
  exact
    { mantissa := m
      exponent := e
      mantissa_lower := hmbounds.1
      mantissa_upper := hmbounds.2
      exponent_lower := hemin
      exponent_upper := le_trans he r.exponent_upper
      value_eq := hvalue }

private def p12_neg_representation
    (fmt : P12RadixFormat) {v : ℝ} (r : P12Representation fmt v) :
    P12Representation fmt (-v) :=
  { mantissa := -r.mantissa
    exponent := r.exponent
    mantissa_lower := by
      norm_num at ⊢
      linarith [r.mantissa_upper]
    mantissa_upper := by
      norm_num at ⊢
      linarith [r.mantissa_lower]
    exponent_lower := r.exponent_lower
    exponent_upper := r.exponent_upper
    value_eq := by
      calc
        -v = -((r.mantissa : ℝ) * fmt.scale r.exponent) :=
          congrArg Neg.neg r.value_eq
        _ = ((-r.mantissa : ℤ) : ℝ) * fmt.scale r.exponent := by
          push_cast
          ring }

private def p12_representation_congr
    (fmt : P12RadixFormat) {a b : ℝ} (h : a = b)
    (r : P12Representation fmt a) : P12Representation fmt b := by
  subst b
  exact r

private lemma p12_representation_congr_exponent
    (fmt : P12RadixFormat) {a b : ℝ} (h : a = b)
    (r : P12Representation fmt a) :
    (p12_representation_congr fmt h r).exponent = r.exponent := by
  subst b
  rfl

private lemma p12_abs_lt_bound_of_exponent_le
    (fmt : P12RadixFormat) {v : ℝ} (r : P12Representation fmt v)
    {e : ℤ} (he : r.exponent ≤ e) :
    |v| < fmt.mantissaBound * fmt.scale e := by
  have hm : |(r.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨r.mantissa_lower, r.mantissa_upper⟩
  have hv0 : |v| < fmt.mantissaBound * fmt.scale r.exponent := by
    calc
      |v| = |(r.mantissa : ℝ) * fmt.scale r.exponent| :=
        congrArg abs r.value_eq
      _ = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
        rw [abs_mul, abs_of_pos (p12_scale_pos fmt r.exponent)]
      _ < fmt.mantissaBound * fmt.scale r.exponent :=
        mul_lt_mul_of_pos_right hm (p12_scale_pos fmt r.exponent)
  exact lt_of_lt_of_le hv0 (mul_le_mul_of_nonneg_left
    (p12_scale_mono fmt he) (le_of_lt (p12_mantissaBound_pos fmt)))

private def p12_sub_representation_of_bound
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    {e : ℤ} (hemin : fmt.emin ≤ e)
    (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent)
    (hab : |a - b| < fmt.mantissaBound * fmt.scale e) :
    P12Representation fmt (a - b) := by
  let qa : ℕ := fmt.beta ^ (ra.exponent - e).toNat
  let qb : ℕ := fmt.beta ^ (rb.exponent - e).toNat
  let m : ℤ := ra.mantissa * (qa : ℤ) - rb.mantissa * (qb : ℤ)
  have hscalea : fmt.scale ra.exponent = fmt.scale e * (qa : ℕ) := by
    simpa [qa] using p12_scale_of_le fmt hea
  have hscaleb : fmt.scale rb.exponent = fmt.scale e * (qb : ℕ) := by
    simpa [qb] using p12_scale_of_le fmt heb
  have hvalue : a - b = (m : ℝ) * fmt.scale e := by
    rw [ra.value_eq, rb.value_eq, hscalea, hscaleb]
    simp only [m, Int.cast_sub, Int.cast_mul, Int.cast_natCast]
    ring
  have hmabs : |(m : ℝ)| < fmt.mantissaBound := by
    rw [hvalue, abs_mul, abs_of_pos (p12_scale_pos fmt e)] at hab
    nlinarith [p12_scale_pos fmt e]
  have hmbounds := abs_lt.mp hmabs
  exact
    { mantissa := m
      exponent := e
      mantissa_lower := hmbounds.1
      mantissa_upper := hmbounds.2
      exponent_lower := hemin
      exponent_upper := le_trans hea ra.exponent_upper
      value_eq := hvalue }

private lemma p12_sub_representable_of_bound
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    {e : ℤ} (hemin : fmt.emin ≤ e)
    (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent)
    (hab : |a - b| < fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt (a - b) :=
  ⟨p12_sub_representation_of_bound fmt ra rb hemin hea heb hab⟩

private lemma p12_sub_representation_of_bound_exponent
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    {e : ℤ} (hemin : fmt.emin ≤ e)
    (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent)
    (hab : |a - b| < fmt.mantissaBound * fmt.scale e) :
    (p12_sub_representation_of_bound fmt ra rb hemin hea heb hab).exponent = e := by
  rfl

private lemma p12_boundary_representable
    (fmt : P12RadixFormat) {v : ℝ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hv : |v| = fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt v := by
  let p : ℕ := fmt.precision - 1
  have hp : p + 1 = fmt.precision := by
    have hp0 := fmt.precision_pos
    dsimp [p]
    exact Nat.sub_add_cancel (by omega)
  have hbpos : 0 < fmt.beta := lt_of_lt_of_le (by decide) fmt.beta_ge_two
  have hbone : 1 < fmt.beta := lt_of_lt_of_le (by decide) fmt.beta_ge_two
  have hppos : 0 < fmt.beta ^ p := pow_pos hbpos _
  have hpow : fmt.beta ^ fmt.precision = fmt.beta ^ p * fmt.beta := by
    rw [← hp, pow_succ]
  have hsmallNat : fmt.beta ^ p < fmt.beta ^ fmt.precision := by
    rw [hpow]
    calc
      fmt.beta ^ p = fmt.beta ^ p * 1 := by omega
      _ < fmt.beta ^ p * fmt.beta := (Nat.mul_lt_mul_left hppos).mpr hbone
  have hsmall : (fmt.beta ^ p : ℕ) < fmt.mantissaBound := by
    rw [P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
    exact_mod_cast hsmallNat
  have hscale : fmt.scale (e + 1) = fmt.scale e * fmt.betaR := by
    change fmt.betaR ^ (e + 1) = fmt.betaR ^ e * fmt.betaR
    exact zpow_add_one₀ (ne_of_gt (p12_betaR_pos fmt)) e
  have hpowR : fmt.mantissaBound = (fmt.beta ^ p : ℕ) * fmt.betaR := by
    rw [P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
    exact_mod_cast hpow
  have hboundary : fmt.mantissaBound * fmt.scale e =
      (fmt.beta ^ p : ℕ) * fmt.scale (e + 1) := by
    rw [hpowR, hscale]
    ring
  have hnonneg : 0 ≤ fmt.mantissaBound * fmt.scale e :=
    le_of_lt (mul_pos (p12_mantissaBound_pos fmt) (p12_scale_pos fmt e))
  rcases (abs_eq hnonneg).mp hv with hvpos | hvneg
  · refine ⟨
      { mantissa := (fmt.beta ^ p : ℕ)
        exponent := e + 1
        mantissa_lower := ?_
        mantissa_upper := ?_
        exponent_lower := by omega
        exponent_upper := by omega
        value_eq := ?_ }⟩
    · have : (0 : ℝ) < (fmt.beta ^ p : ℕ) := by exact_mod_cast hppos
      norm_num at ⊢
      have hneg : -fmt.mantissaBound < 0 := neg_lt_zero.mpr (p12_mantissaBound_pos fmt)
      exact lt_trans hneg (by positivity)
    · exact hsmall
    · rw [hvpos, hboundary]
      norm_num
  · refine ⟨
      { mantissa := -(fmt.beta ^ p : ℕ)
        exponent := e + 1
        mantissa_lower := ?_
        mantissa_upper := ?_
        exponent_lower := by omega
        exponent_upper := by omega
        value_eq := ?_ }⟩
    · simpa only [Int.cast_neg, Int.cast_natCast, neg_lt_neg_iff] using hsmall
    · have : (0 : ℝ) < (fmt.beta ^ p : ℕ) := by exact_mod_cast hppos
      norm_num at ⊢
      exact lt_trans (neg_lt_zero.mpr (by positivity)) (p12_mantissaBound_pos fmt)
    · rw [hvneg, hboundary]
      push_cast
      ring

private lemma p12_sub_representable_of_bound_le
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    {e : ℤ} (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent)
    (hab : |a - b| ≤ fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt (a - b) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact p12_sub_representable_of_bound fmt ra rb hemin hea heb hlt
  · exact p12_boundary_representable fmt hemin hemax heq

private lemma p12_nearest_error_same_exponent
    (fmt : P12RadixFormat) {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (hexp : ry.exponent = rx.exponent)
    (hemax : rx.exponent < fmt.emax)
    (hnearest : p12NearestInFormat fmt (x + y) s) :
    |s - (x + y)| ≤ fmt.halfRadixFloor * fmt.scale rx.exponent := by
  let B : ℕ := fmt.beta ^ fmt.precision
  let b : ℤ := fmt.beta
  let k : ℤ := rx.mantissa + ry.mantissa
  let q : ℤ := k / b
  let r : ℤ := k % b
  have hbNat : 2 ≤ fmt.beta := fmt.beta_ge_two
  have hbpos : (0 : ℤ) < b := by
    dsimp [b]
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hbNat)
  have hbne : b ≠ 0 := ne_of_gt hbpos
  have hBpos : 0 < B := by
    exact pow_pos (lt_of_lt_of_le (by decide) hbNat) _
  have hbB : fmt.beta ≤ B := by
    dsimp [B]
    exact Nat.le_pow fmt.precision_pos
  have hBreal : (B : ℝ) = fmt.mantissaBound := by
    symm
    simpa [B] using p12_mantissaBound_eq_natCast fmt
  have hmxlo : -(B : ℤ) < rx.mantissa := by
    have hm := rx.mantissa_lower
    rw [← hBreal] at hm
    exact_mod_cast hm
  have hmxhi : rx.mantissa < (B : ℤ) := by
    have hm := rx.mantissa_upper
    rw [← hBreal] at hm
    exact_mod_cast hm
  have hmylo : -(B : ℤ) < ry.mantissa := by
    have hm := ry.mantissa_lower
    rw [← hBreal] at hm
    exact_mod_cast hm
  have hmyhi : ry.mantissa < (B : ℤ) := by
    have hm := ry.mantissa_upper
    rw [← hBreal] at hm
    exact_mod_cast hm
  have hklo : -(2 * (B : ℤ)) + 2 ≤ k := by
    dsimp [k]
    omega
  have hkhi : k ≤ 2 * (B : ℤ) - 2 := by
    dsimp [k]
    omega
  have hdiv : b * q + r = k := by
    dsimp [q, r]
    exact Int.ediv_add_emod k b
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Int.emod_nonneg k hbne
  have hrb : r < b := by
    dsimp [r]
    exact Int.emod_lt_of_pos k hbpos
  have hhalf : (fmt.beta : ℤ) ≤ 2 * (fmt.beta / 2 : ℕ) + 1 := by
    have hm := Nat.mod_lt fmt.beta (by decide : 0 < 2)
    have hd := Nat.div_add_mod fmt.beta 2
    omega
  let c : ℤ := if r ≤ (fmt.beta / 2 : ℕ) then q else q + 1
  have hb2 : (2 : ℤ) ≤ b := by
    dsimp [b]
    exact_mod_cast hbNat
  have hbB' : b ≤ (B : ℤ) := by
    dsimp [b]
    exact_mod_cast hbB
  have hB1 : (1 : ℤ) ≤ (B : ℤ) := by exact_mod_cast hBpos
  have hbc_nonneg :
      0 ≤ ((b : ℤ) - 2) * ((B : ℤ) - 1) := by
    exact mul_nonneg (sub_nonneg.mpr hb2) (sub_nonneg.mpr hB1)
  have hcBounds : -(B : ℤ) < c ∧ c < (B : ℤ) := by
    dsimp [c]
    split_ifs with hsmall
    · constructor
      · by_contra hn
        have hq : q ≤ -(B : ℤ) := by omega
        have hmul : b * q ≤ b * (-(B : ℤ)) :=
          mul_le_mul_of_nonneg_left hq (le_of_lt hbpos)
        linarith
      · by_contra hn
        have hq : (B : ℤ) ≤ q := by omega
        have hmul : b * (B : ℤ) ≤ b * q :=
          mul_le_mul_of_nonneg_left hq (le_of_lt hbpos)
        have hprod : 2 * (B : ℤ) ≤ b * B :=
          mul_le_mul_of_nonneg_right hb2 (by omega)
        linarith
    · constructor
      · by_contra hn
        have hq : q + 1 ≤ -(B : ℤ) := by omega
        have hq' : q ≤ -(B : ℤ) - 1 := by omega
        have hmul : b * q ≤ b * (-(B : ℤ) - 1) :=
          mul_le_mul_of_nonneg_left hq' (le_of_lt hbpos)
        have hprod : 2 * (B : ℤ) ≤ b * B :=
          mul_le_mul_of_nonneg_right hb2 (by omega)
        linarith
      · by_contra hn
        have hq : (B : ℤ) ≤ q + 1 := by omega
        have hq' : (B : ℤ) - 1 ≤ q := by omega
        have hmul : b * ((B : ℤ) - 1) ≤ b * q :=
          mul_le_mul_of_nonneg_left hq' (le_of_lt hbpos)
        have hprod : 2 * ((B : ℤ) - 1) ≤ b * (B - 1) :=
          mul_le_mul_of_nonneg_right hb2 (by omega)
        have hrpos : 1 ≤ r := by omega
        linarith
  have hcoeffError : |k - b * c| ≤ (fmt.beta / 2 : ℕ) := by
    dsimp [c]
    split_ifs with hsmall
    · have heq : k - b * q = r := by linarith
      rw [heq, abs_of_nonneg hr0]
      exact hsmall
    · have heq : k - b * (q + 1) = r - b := by linarith
      rw [heq, abs_of_nonpos (by omega)]
      omega
  let candidate : ℝ := (c : ℝ) * fmt.scale (rx.exponent + 1)
  have hcandrep : p12Representable fmt candidate := by
    refine ⟨
      { mantissa := c
        exponent := rx.exponent + 1
        mantissa_lower := ?_
        mantissa_upper := ?_
        exponent_lower := le_trans rx.exponent_lower (by omega)
        exponent_upper := by omega
        value_eq := rfl }⟩
    · rw [p12_mantissaBound_eq_natCast]
      exact_mod_cast hcBounds.1
    · rw [p12_mantissaBound_eq_natCast]
      exact_mod_cast hcBounds.2
  have hscale : fmt.scale (rx.exponent + 1) =
      fmt.scale rx.exponent * fmt.betaR := by
    change fmt.betaR ^ (rx.exponent + 1) =
      fmt.betaR ^ rx.exponent * fmt.betaR
    exact zpow_add_one₀ (ne_of_gt (p12_betaR_pos fmt)) rx.exponent
  have hxy : x + y = (k : ℝ) * fmt.scale rx.exponent := by
    calc
      x + y = (rx.mantissa : ℝ) * fmt.scale rx.exponent +
          (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
            rw [← rx.value_eq, ← ry.value_eq]
      _ = (k : ℝ) * fmt.scale rx.exponent := by
        rw [hexp]
        dsimp [k]
        push_cast
        ring
  have herrCandidate : |(x + y) - candidate| ≤
      fmt.halfRadixFloor * fmt.scale rx.exponent := by
    have hcalc : (x + y) - candidate =
        ((k - b * c : ℤ) : ℝ) * fmt.scale rx.exponent := by
      rw [hxy]
      dsimp [candidate]
      rw [hscale]
      dsimp [b]
      simp only [P12RadixFormat.betaR]
      push_cast
      ring
    rw [hcalc, abs_mul, abs_of_pos (p12_scale_pos fmt rx.exponent)]
    apply mul_le_mul_of_nonneg_right _ (le_of_lt (p12_scale_pos fmt rx.exponent))
    rw [P12RadixFormat.halfRadixFloor]
    rw [← Int.cast_abs]
    exact (Int.cast_le).mpr hcoeffError
  calc
    |s - (x + y)| = |(x + y) - s| := abs_sub_comm _ _
    _ ≤ |(x + y) - candidate| := hnearest.2 candidate hcandrep
    _ ≤ fmt.halfRadixFloor * fmt.scale rx.exponent := herrCandidate

private lemma p12_top_large_sub_bound
    (fmt : P12RadixFormat) {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (rs : P12Representation fmt s)
    (hexp : ry.exponent = rx.exponent)
    (htop : rx.exponent = fmt.emax)
    (hlarge : fmt.mantissaBound * fmt.scale rx.exponent ≤ |x + y|)
    (herror : |s - (x + y)| ≤ |y|) :
    |s - x| < fmt.mantissaBound * fmt.scale rs.exponent := by
  let A : ℝ := fmt.mantissaBound * fmt.scale rx.exponent
  have hApos : 0 < A := mul_pos (p12_mantissaBound_pos fmt)
    (p12_scale_pos fmt rx.exponent)
  have hxA : |x| < A := p12_abs_lt_bound_of_exponent_le fmt rx le_rfl
  have hyA : |y| < A := by
    apply p12_abs_lt_bound_of_exponent_le fmt ry
    omega
  have hsA : |s| < A := by
    apply p12_abs_lt_bound_of_exponent_le fmt rs
    calc
      rs.exponent ≤ fmt.emax := rs.exponent_upper
      _ = rx.exponent := htop.symm
  have hsOwn : |s| < fmt.mantissaBound * fmt.scale rs.exponent :=
    p12_abs_lt_bound_of_exponent_le fmt rs le_rfl
  by_cases hz : 0 ≤ x + y
  · have hzA : A ≤ x + y := by
      dsimp [A]
      rw [abs_of_nonneg hz] at hlarge
      exact hlarge
    have hxlt : x < A := (abs_lt.mp hxA).2
    have hylt : y < A := (abs_lt.mp hyA).2
    have hxpos : 0 < x := by linarith
    have hypos : 0 < y := by linarith
    have hsge : x ≤ s := by
      rw [abs_of_pos hypos] at herror
      have := (neg_le_abs (s - (x + y)))
      linarith
    have hslt : s < A := (abs_lt.mp hsA).2
    rw [abs_of_nonneg (sub_nonneg.mpr hsge)]
    have hsOwnUpper : s < fmt.mantissaBound * fmt.scale rs.exponent :=
      (abs_lt.mp hsOwn).2
    linarith
  · have hz0 : x + y ≤ 0 := le_of_not_ge hz
    have hzA : x + y ≤ -A := by
      dsimp [A]
      rw [abs_of_nonpos hz0] at hlarge
      linarith
    have hxlo : -A < x := (abs_lt.mp hxA).1
    have hylo : -A < y := (abs_lt.mp hyA).1
    have hxneg : x < 0 := by linarith
    have hyneg : y < 0 := by linarith
    have hsle : s ≤ x := by
      rw [abs_of_neg hyneg] at herror
      have := (le_abs_self (s - (x + y)))
      linarith
    have hslo : -A < s := (abs_lt.mp hsA).1
    rw [abs_of_nonpos (sub_nonpos.mpr hsle)]
    have hsOwnLower : - (fmt.mantissaBound * fmt.scale rs.exponent) < s :=
      (abs_lt.mp hsOwn).1
    linarith

private lemma p12_nearest_exponent_ge_of_large
    (fmt : P12RadixFormat) {z s : ℝ}
    (rs : P12Representation fmt s) {e : ℤ}
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hlarge : fmt.mantissaBound * fmt.scale e ≤ |z|)
    (hnearest : p12NearestInFormat fmt z s) :
    e ≤ rs.exponent := by
  let B : ℕ := fmt.beta ^ fmt.precision
  let F : ℝ := (B - 1 : ℕ) * fmt.scale e
  let A : ℝ := fmt.mantissaBound * fmt.scale e
  have hbB : fmt.beta ≤ B := by
    dsimp [B]
    exact Nat.le_pow fmt.precision_pos
  have hB2 : 2 ≤ B := le_trans fmt.beta_ge_two hbB
  have hBm1pos : 0 < B - 1 := by omega
  have hFpos : 0 < F := by
    dsimp [F]
    exact mul_pos (by exact_mod_cast hBm1pos) (p12_scale_pos fmt e)
  have hApos : 0 < A := by
    exact mul_pos (p12_mantissaBound_pos fmt) (p12_scale_pos fmt e)
  have hBreal : (B : ℝ) = fmt.mantissaBound := by
    symm
    simpa [B] using p12_mantissaBound_eq_natCast fmt
  have hFrep : p12Representable fmt F := by
    refine ⟨
      { mantissa := (B - 1 : ℕ)
        exponent := e
        mantissa_lower := ?_
        mantissa_upper := ?_
        exponent_lower := hemin
        exponent_upper := hemax
        value_eq := rfl }⟩
    · rw [← hBreal]
      norm_num at ⊢
      have hBp : (0 : ℝ) < (B : ℕ) := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hB2)
      nlinarith
    · rw [← hBreal]
      exact_mod_cast (Nat.sub_lt (by omega : 0 < B) (by decide : 0 < 1))
  have hnFrep : p12Representable fmt (-F) := by
    rcases hFrep with ⟨rF⟩
    exact ⟨p12_neg_representation fmt rF⟩
  by_contra hn
  have hse : rs.exponent < e := lt_of_not_ge hn
  have hsOwn : |s| < fmt.mantissaBound * fmt.scale rs.exponent :=
    p12_abs_lt_bound_of_exponent_le fmt rs le_rfl
  have hstep : 2 * fmt.scale rs.exponent ≤ fmt.scale e := by
    calc
      2 * fmt.scale rs.exponent ≤ fmt.scale (rs.exponent + 1) :=
        p12_two_scale_le_succ fmt rs.exponent
      _ ≤ fmt.scale e := p12_scale_mono fmt (by omega)
  have hBineqNat : B ≤ 2 * (B - 1) := by omega
  have hBineq : fmt.mantissaBound ≤ 2 * (B - 1 : ℕ) := by
    rw [← hBreal]
    exact_mod_cast hBineqNat
  have hsF : |s| < F := by
    apply lt_of_lt_of_le hsOwn
    dsimp [F]
    calc
      fmt.mantissaBound * fmt.scale rs.exponent ≤
          (2 * (B - 1 : ℕ)) * fmt.scale rs.exponent :=
        mul_le_mul_of_nonneg_right hBineq (le_of_lt (p12_scale_pos fmt rs.exponent))
      _ = (B - 1 : ℕ) * (2 * fmt.scale rs.exponent) := by ring
      _ ≤ (B - 1 : ℕ) * fmt.scale e :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
  have hslo : -F < s := (abs_lt.mp hsF).1
  have hshi : s < F := (abs_lt.mp hsF).2
  by_cases hz : 0 ≤ z
  · have hzA : A ≤ z := by
      dsimp [A]
      rw [abs_of_nonneg hz] at hlarge
      exact hlarge
    have hFA : F < A := by
      dsimp [F, A]
      rw [← hBreal]
      apply mul_lt_mul_of_pos_right _ (p12_scale_pos fmt e)
      exact_mod_cast (Nat.sub_lt (by omega : 0 < B) (by decide : 0 < 1))
    have hstrict : |z - F| < |z - s| := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_trans (le_of_lt hFA) hzA)),
        abs_of_nonneg (sub_nonneg.mpr
          (le_trans (le_of_lt hshi) (le_trans (le_of_lt hFA) hzA)))]
      linarith
    exact (not_lt_of_ge (hnearest.2 F hFrep)) hstrict
  · have hz0 : z ≤ 0 := le_of_not_ge hz
    have hzA : z ≤ -A := by
      dsimp [A]
      rw [abs_of_nonpos hz0] at hlarge
      linarith
    have hFA : F < A := by
      dsimp [F, A]
      rw [← hBreal]
      apply mul_lt_mul_of_pos_right _ (p12_scale_pos fmt e)
      exact_mod_cast (Nat.sub_lt (by omega : 0 < B) (by decide : 0 < 1))
    have hstrict : |z - (-F)| < |z - s| := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_trans hzA (by linarith))),
        abs_of_nonpos (sub_nonpos.mpr (le_trans hzA (by linarith)))]
      linarith
    exact (not_lt_of_ge (hnearest.2 (-F) hnFrep)) hstrict

private lemma p12_nearest_exponent_gt_of_large
    (fmt : P12RadixFormat) {z s : ℝ}
    (rs : P12Representation fmt s) {e upper : ℤ}
    (hemin : fmt.emin ≤ e) (heupper : e < upper)
    (hupper : upper ≤ fmt.emax)
    (hlarge : fmt.mantissaBound * fmt.scale e ≤ |z|)
    (hnearest : p12NearestInFormat fmt z s) :
    e < rs.exponent := by
  let A : ℝ := fmt.mantissaBound * fmt.scale e
  have hApos : 0 < A := mul_pos (p12_mantissaBound_pos fmt) (p12_scale_pos fmt e)
  have heymax : e < fmt.emax := lt_of_lt_of_le heupper hupper
  have hposrep : p12Representable fmt A := by
    apply p12_boundary_representable fmt hemin heymax
    exact abs_of_pos hApos
  have hnegrep : p12Representable fmt (-A) := by
    apply p12_boundary_representable fmt hemin heymax
    rw [abs_neg, abs_of_pos hApos]
  by_contra hnle
  have hes : rs.exponent ≤ e := le_of_not_gt hnle
  have hms : |(rs.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨rs.mantissa_lower, rs.mantissa_upper⟩
  have hs0 : |s| < fmt.mantissaBound * fmt.scale rs.exponent := by
    calc
      |s| = |(rs.mantissa : ℝ) * fmt.scale rs.exponent| :=
        congrArg abs rs.value_eq
      _ = |(rs.mantissa : ℝ)| * fmt.scale rs.exponent := by
        rw [abs_mul, abs_of_pos (p12_scale_pos fmt rs.exponent)]
      _ < fmt.mantissaBound * fmt.scale rs.exponent :=
        mul_lt_mul_of_pos_right hms (p12_scale_pos fmt rs.exponent)
  have hsA : |s| < A := by
    apply lt_of_lt_of_le hs0
    exact mul_le_mul_of_nonneg_left (p12_scale_mono fmt hes)
      (le_of_lt (p12_mantissaBound_pos fmt))
  have hslo : -A < s := (abs_lt.mp hsA).1
  have hshi : s < A := (abs_lt.mp hsA).2
  by_cases hz : 0 ≤ z
  · have hzA : A ≤ z := by
      dsimp [A]
      rw [abs_of_nonneg hz] at hlarge
      exact hlarge
    have hstrict : |z - A| < |z - s| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hzA),
        abs_of_nonneg (sub_nonneg.mpr (le_trans (le_of_lt hshi) hzA))]
      linarith
    exact (not_lt_of_ge (hnearest.2 A hposrep)) hstrict
  · have hz0 : z ≤ 0 := le_of_not_ge hz
    have hzA : z ≤ -A := by
      dsimp [A]
      rw [abs_of_nonpos hz0] at hlarge
      linarith
    have hstrict : |z - (-A)| < |z - s| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hzA),
        abs_of_nonpos (sub_nonpos.mpr (le_trans hzA (le_of_lt hslo)))]
      linarith
    exact (not_lt_of_ge (hnearest.2 (-A) hnegrep)) hstrict

private lemma p12_faithful_eq_of_representable
    (fmt : P12RadixFormat) {exact rounded : ℝ}
    (hfaithful : p12FaithfulInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  rcases hfaithful with ⟨_, hgap⟩
  rcases lt_trichotomy rounded exact with hlt | heq | hgt
  · exact False.elim (hgap exact hexact (Or.inl ⟨hlt, le_rfl⟩))
  · exact heq
  · exact False.elim (hgap exact hexact (Or.inr ⟨le_rfl, hgt⟩))

theorem p12_t1_fast_two_sum_exact
    (fmt : P12RadixFormat) (x y : ℝ) (tr : P12FastTwoSumTrace)
    (hx : p12Representable fmt x) (hy : p12Representable fmt y)
    (hcondition7 : ∃ rx : P12Representation fmt x,
      |y| ≤ fmt.condition7Ceiling * fmt.scale rx.exponent)
    (run : P12FastTwoSumExecution fmt x y tr) :
    tr.t = tr.s - x ∧
      tr.e = y - tr.t ∧
      tr.s + tr.e = x + y ∧
      |tr.s - (x + y)| ≤ |y| := by
  -- PROOF_START P12-T1-H001
  rcases hcondition7 with ⟨rx, hcondition7⟩
  rcases hy with ⟨ry⟩
  rcases run.add.1 with ⟨rs⟩
  have hy_lt_rx : |y| < fmt.mantissaBound * fmt.scale rx.exponent :=
    lt_of_le_of_lt hcondition7 (mul_lt_mul_of_pos_right
      (p12_condition7Ceiling_lt_mantissaBound fmt)
      (p12_scale_pos fmt rx.exponent))
  obtain ⟨ry₀, hry₀x⟩ : ∃ ry₀ : P12Representation fmt y,
      ry₀.exponent ≤ rx.exponent := by
    by_cases h : ry.exponent ≤ rx.exponent
    · exact ⟨ry, h⟩
    · have hxr : rx.exponent ≤ ry.exponent := le_of_not_ge h
      exact ⟨p12_representation_at_lower_exponent fmt ry
        rx.exponent_lower hxr hy_lt_rx, le_rfl⟩
  have herror : |tr.s - (x + y)| ≤ |y| := by
    calc
      |tr.s - (x + y)| = |(x + y) - tr.s| := abs_sub_comm _ _
      _ ≤ |(x + y) - x| := run.add.2 x hx
      _ = |y| := by congr 1 <;> ring
  have hyOwn : |y| < fmt.mantissaBound * fmt.scale ry₀.exponent :=
    p12_abs_lt_bound_of_exponent_le fmt ry₀ le_rfl
  have htStrong : ∃ rt : P12Representation fmt (tr.s - x),
      ry₀.exponent ≤ rt.exponent := by
    rcases lt_or_eq_of_le hry₀x with hryx | hryx
    · by_cases hsmall : |x + y| <
          fmt.mantissaBound * fmt.scale ry₀.exponent
      · have hsumrep : p12Representable fmt (x + y) := by
          have hsmall' : |x - -y| <
              fmt.mantissaBound * fmt.scale ry₀.exponent := by
            simpa only [sub_neg_eq_add] using hsmall
          simpa only [sub_neg_eq_add] using
            (p12_sub_representable_of_bound fmt rx
              (p12_neg_representation fmt ry₀) ry₀.exponent_lower
              hry₀x le_rfl hsmall')
        have hsExact : tr.s = x + y := by
          have hz := run.add.2 (x + y) hsumrep
          have hz0 : |(x + y) - tr.s| = 0 :=
            le_antisymm (by simpa using hz) (abs_nonneg _)
          exact (sub_eq_zero.mp (abs_eq_zero.mp hz0)).symm
        have hdEq : tr.s - x = y := by rw [hsExact]; ring
        let rt := p12_representation_congr fmt hdEq.symm ry₀
        refine ⟨rt, ?_⟩
        rw [p12_representation_congr_exponent]
      · have hlarge : fmt.mantissaBound * fmt.scale ry₀.exponent ≤
            |x + y| := le_of_not_gt hsmall
        have hrsLarge : ry₀.exponent < rs.exponent :=
          p12_nearest_exponent_gt_of_large fmt rs ry₀.exponent_lower
            hryx rx.exponent_upper hlarge run.add
        have hdBound : |tr.s - x| <
            fmt.mantissaBound * fmt.scale (ry₀.exponent + 1) := by
          calc
            |tr.s - x| = |(tr.s - (x + y)) + y| := by
              congr 1 <;> ring
            _ ≤ |tr.s - (x + y)| + |y| := abs_add_le _ _
            _ ≤ |y| + |y| := add_le_add herror le_rfl
            _ < 2 * (fmt.mantissaBound * fmt.scale ry₀.exponent) := by
              linarith
            _ = fmt.mantissaBound * (2 * fmt.scale ry₀.exponent) := by ring
            _ ≤ fmt.mantissaBound * fmt.scale (ry₀.exponent + 1) :=
              mul_le_mul_of_nonneg_left (p12_two_scale_le_succ fmt ry₀.exponent)
                (le_of_lt (p12_mantissaBound_pos fmt))
        let rt := p12_sub_representation_of_bound fmt rs rx
          (show fmt.emin ≤ ry₀.exponent + 1 from
            le_trans ry₀.exponent_lower (by omega))
          (show ry₀.exponent + 1 ≤ rs.exponent by omega)
          (show ry₀.exponent + 1 ≤ rx.exponent by omega) hdBound
        refine ⟨rt, ?_⟩
        rw [p12_sub_representation_of_bound_exponent]
        omega
    · have hryeq : ry₀.exponent = rx.exponent := hryx
      by_cases hsmall : |x + y| <
          fmt.mantissaBound * fmt.scale ry₀.exponent
      · have hsumrep : p12Representable fmt (x + y) := by
          have hsmall' : |x - -y| <
              fmt.mantissaBound * fmt.scale ry₀.exponent := by
            simpa only [sub_neg_eq_add] using hsmall
          simpa only [sub_neg_eq_add] using
            (p12_sub_representable_of_bound fmt rx
              (p12_neg_representation fmt ry₀) ry₀.exponent_lower
              hry₀x le_rfl hsmall')
        have hsExact : tr.s = x + y := by
          have hz := run.add.2 (x + y) hsumrep
          have hz0 : |(x + y) - tr.s| = 0 :=
            le_antisymm (by simpa using hz) (abs_nonneg _)
          exact (sub_eq_zero.mp (abs_eq_zero.mp hz0)).symm
        have hdEq : tr.s - x = y := by rw [hsExact]; ring
        let rt := p12_representation_congr fmt hdEq.symm ry₀
        refine ⟨rt, ?_⟩
        rw [p12_representation_congr_exponent]
      · have hlarge : fmt.mantissaBound * fmt.scale ry₀.exponent ≤
            |x + y| := le_of_not_gt hsmall
        have hrsGe : ry₀.exponent ≤ rs.exponent :=
          p12_nearest_exponent_ge_of_large fmt rs ry₀.exponent_lower
            (le_trans hry₀x rx.exponent_upper) hlarge run.add
        by_cases hnotTop : rx.exponent < fmt.emax
        · have hround := p12_nearest_error_same_exponent fmt rx ry₀
            hryeq hnotTop run.add
          have hdLe : |tr.s - x| ≤
              fmt.mantissaBound * fmt.scale rx.exponent := by
            calc
              |tr.s - x| = |(tr.s - (x + y)) + y| := by
                congr 1 <;> ring
              _ ≤ |tr.s - (x + y)| + |y| := abs_add_le _ _
              _ ≤ fmt.halfRadixFloor * fmt.scale rx.exponent +
                  fmt.condition7Ceiling * fmt.scale rx.exponent :=
                add_le_add hround hcondition7
              _ = fmt.mantissaBound * fmt.scale rx.exponent := by
                rw [← add_mul, p12_half_add_condition7]
          rcases lt_or_eq_of_le hdLe with hdLt | hdEq
          · have hrsx : rx.exponent ≤ rs.exponent := by omega
            let rt := p12_sub_representation_of_bound fmt rs rx
                rx.exponent_lower hrsx le_rfl hdLt
            refine ⟨rt, ?_⟩
            rw [p12_sub_representation_of_bound_exponent]
            exact hry₀x
          · rcases p12_boundary_representable fmt rx.exponent_lower hnotTop hdEq with ⟨rt⟩
            have hrtGe : rx.exponent ≤ rt.exponent := by
              by_contra hn
              have hrte : rt.exponent ≤ rx.exponent := le_of_not_ge hn
              have hlt := p12_abs_lt_bound_of_exponent_le fmt rt hrte
              linarith
            exact ⟨rt, by omega⟩
        · have htop : rx.exponent = fmt.emax :=
            le_antisymm rx.exponent_upper (le_of_not_gt hnotTop)
          have hdBound := p12_top_large_sub_bound fmt rx ry₀ rs
            hryeq htop (by simpa [hryeq] using hlarge) herror
          have hrsx : rs.exponent ≤ rx.exponent := by
            calc
              rs.exponent ≤ fmt.emax := rs.exponent_upper
              _ = rx.exponent := htop.symm
          let rt := p12_sub_representation_of_bound fmt rs rx rs.exponent_lower
            le_rfl hrsx hdBound
          refine ⟨rt, ?_⟩
          rw [p12_sub_representation_of_bound_exponent]
          exact hrsGe
  rcases htStrong with ⟨rtExact, hryt⟩
  have htRep : p12Representable fmt (tr.s - x) := ⟨rtExact⟩
  have ht : tr.t = tr.s - x :=
    p12_faithful_eq_of_representable fmt run.first_sub htRep
  have heError : |y - (tr.s - x)| ≤ |y| := by
    calc
      |y - (tr.s - x)| = |(x + y) - tr.s| := by
        congr 1 <;> ring
      _ = |tr.s - (x + y)| := abs_sub_comm _ _
      _ ≤ |y| := herror
  have heBound : |y - (tr.s - x)| <
      fmt.mantissaBound * fmt.scale ry₀.exponent :=
    lt_of_le_of_lt heError hyOwn
  have heRep0 : p12Representable fmt (y - (tr.s - x)) :=
    p12_sub_representable_of_bound fmt ry₀ rtExact ry₀.exponent_lower
      le_rfl hryt heBound
  have heRep : p12Representable fmt (y - tr.t) := by simpa [ht] using heRep0
  have he : tr.e = y - tr.t :=
    p12_faithful_eq_of_representable fmt run.second_sub heRep
  refine ⟨ht, he, ?_, herror⟩
  rw [he, ht]
  ring

end HighamBench
