import HighamBench.P12Definitions

namespace HighamBench

private lemma p12_beta_pos (fmt : P12RadixFormat) : 0 < fmt.beta :=
  lt_of_lt_of_le Nat.zero_lt_two fmt.beta_ge_two

private lemma p12_scale_pos (fmt : P12RadixFormat) (e : ℤ) :
    0 < fmt.scale e := by
  unfold P12RadixFormat.scale P12RadixFormat.betaR
  apply zpow_pos
  exact_mod_cast p12_beta_pos fmt

private lemma p12_mantissaBound_pos (fmt : P12RadixFormat) :
    0 < fmt.mantissaBound := by
  unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
  exact pow_pos (by exact_mod_cast p12_beta_pos fmt) _

private lemma p12_beta_le_mantissaBound (fmt : P12RadixFormat) :
    fmt.beta ≤ fmt.beta ^ fmt.precision := by
  obtain ⟨q, hq⟩ := Nat.exists_eq_succ_of_ne_zero (by
    exact Nat.ne_of_gt fmt.precision_pos)
  rw [hq, pow_succ]
  exact Nat.le_mul_of_pos_left fmt.beta (Nat.pow_pos (p12_beta_pos fmt))

private lemma p12_scale_align (fmt : P12RadixFormat) {e f : ℤ} (hef : e ≤ f) :
    fmt.scale f =
      ((fmt.beta ^ (f - e).toNat : ℕ) : ℝ) * fmt.scale e := by
  have hb0 : (fmt.betaR : ℝ) ≠ 0 := by
    unfold P12RadixFormat.betaR
    exact_mod_cast (Nat.ne_of_gt (p12_beta_pos fmt))
  let d : ℕ := (f - e).toNat
  have hfe : (d : ℤ) = f - e := by
    exact Int.toNat_sub_of_le hef
  have hf : f = e + (d : ℤ) := by rw [hfe]; ring
  unfold P12RadixFormat.scale
  calc
    fmt.betaR ^ f = fmt.betaR ^ (e + (d : ℤ)) := congrArg _ hf
    _ = fmt.betaR ^ e * fmt.betaR ^ (d : ℤ) :=
      zpow_add₀ hb0 e _
    _ = fmt.betaR ^ e * fmt.betaR ^ d := by
      rw [zpow_natCast]
    _ = ((fmt.beta ^ d : ℕ) : ℝ) * fmt.betaR ^ e := by
      unfold P12RadixFormat.betaR
      push_cast
      ring
    _ = ((fmt.beta ^ (f - e).toNat : ℕ) : ℝ) * fmt.betaR ^ e := by
      rfl

private lemma p12_representable_of_scaled_int
    (fmt : P12RadixFormat) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hm : |(m : ℝ)| < fmt.mantissaBound) :
    p12Representable fmt ((m : ℝ) * fmt.scale e) := by
  refine ⟨⟨m, e, ?_, ?_, hemin, hemax, rfl⟩⟩
  · exact (abs_lt.mp hm).1
  · exact (abs_lt.mp hm).2

private lemma p12_zero_representable (fmt : P12RadixFormat) :
    p12Representable fmt 0 := by
  have hzero : |(((0 : ℤ) : ℝ))| < fmt.mantissaBound := by
    simpa using p12_mantissaBound_pos fmt
  simpa only [Int.cast_zero, zero_mul] using
    p12_representable_of_scaled_int fmt 0 fmt.emin
      (le_rfl) fmt.emin_le_emax hzero

private lemma p12_faithful_eq_of_representable
    (fmt : P12RadixFormat) {exact rounded : ℝ}
    (hfaith : p12FaithfulInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  rcases hfaith with ⟨_, hgap⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hgap exact hexact (Or.inl ⟨hlt, le_rfl⟩)
  · exact hgap exact hexact (Or.inr ⟨le_rfl, hgt⟩)

private lemma p12_representation_abs_lt
    {fmt : P12RadixFormat} {x : ℝ} (r : P12Representation fmt x) :
    |x| < fmt.mantissaBound * fmt.scale r.exponent := by
  have hx : |x| = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
    calc
      |x| = |(r.mantissa : ℝ) * fmt.scale r.exponent| :=
        congrArg abs r.value_eq
      _ = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
        rw [abs_mul, abs_of_pos (p12_scale_pos fmt r.exponent)]
  rw [hx]
  have hm : |(r.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨r.mantissa_lower, r.mantissa_upper⟩
  exact mul_lt_mul_of_pos_right hm (p12_scale_pos fmt r.exponent)

private lemma p12_scaled_int_align
    (fmt : P12RadixFormat) (m : ℤ) {e f : ℤ} (hef : e ≤ f) :
    (m : ℝ) * fmt.scale f =
      ((m * (fmt.beta ^ (f - e).toNat : ℕ) : ℤ) : ℝ) * fmt.scale e := by
  rw [p12_scale_align fmt hef]
  push_cast
  ring

private lemma p12_representable_neg
    {fmt : P12RadixFormat} {x : ℝ} (hx : p12Representable fmt x) :
    p12Representable fmt (-x) := by
  rcases hx with ⟨r⟩
  refine ⟨⟨-r.mantissa, r.exponent, ?_, ?_, r.exponent_lower,
    r.exponent_upper, ?_⟩⟩
  · have h := neg_lt_neg r.mantissa_upper
    simpa only [Int.cast_neg, neg_neg] using h
  · have h := neg_lt_neg r.mantissa_lower
    simpa only [Int.cast_neg, neg_neg] using h
  · calc
      -x = -((r.mantissa : ℝ) * fmt.scale r.exponent) :=
        congrArg Neg.neg r.value_eq
      _ = ((-r.mantissa : ℤ) : ℝ) * fmt.scale r.exponent := by push_cast; ring

private lemma p12_condition7_lt_bound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  have hhalf : 0 < fmt.beta / 2 := Nat.div_pos fmt.beta_ge_two (by decide)
  have hpow : 0 < fmt.beta ^ fmt.precision :=
    Nat.pow_pos (p12_beta_pos fmt)
  have hnat : fmt.beta ^ fmt.precision - fmt.beta / 2 <
      fmt.beta ^ fmt.precision := Nat.sub_lt hpow hhalf
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.mantissaBound
    P12RadixFormat.betaR
  exact_mod_cast hnat

private lemma p12_condition7_add_half (fmt : P12RadixFormat) :
    fmt.condition7Ceiling + fmt.halfRadixFloor = fmt.mantissaBound := by
  have hle : fmt.beta / 2 ≤ fmt.beta ^ fmt.precision :=
    le_trans (Nat.div_le_self fmt.beta 2) (p12_beta_le_mantissaBound fmt)
  have hnat : fmt.beta ^ fmt.precision - fmt.beta / 2 + fmt.beta / 2 =
      fmt.beta ^ fmt.precision := Nat.sub_add_cancel hle
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.halfRadixFloor
    P12RadixFormat.mantissaBound P12RadixFormat.betaR
  exact_mod_cast hnat

private lemma p12_lower_representation
    {fmt : P12RadixFormat} {a : ℝ} (r : P12Representation fmt a)
    (e : ℤ) (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (ha : |a| < fmt.mantissaBound * fmt.scale e) :
    ∃ r' : P12Representation fmt a, r'.exponent ≤ e := by
  by_cases hre : r.exponent ≤ e
  · exact ⟨r, hre⟩
  · have her : e ≤ r.exponent := le_of_lt (lt_of_not_ge hre)
    let m : ℤ := r.mantissa * (fmt.beta ^ (r.exponent - e).toNat : ℕ)
    have hav : a = (m : ℝ) * fmt.scale e := by
      calc
        a = (r.mantissa : ℝ) * fmt.scale r.exponent := r.value_eq
        _ = (m : ℝ) * fmt.scale e := by
          exact p12_scaled_int_align fmt r.mantissa her
    have hm : |(m : ℝ)| < fmt.mantissaBound := by
      have hs := p12_scale_pos fmt e
      have habs : |a| = |(m : ℝ)| * fmt.scale e := by
        calc
          |a| = |(m : ℝ) * fmt.scale e| := congrArg abs hav
          _ = |(m : ℝ)| * fmt.scale e := by rw [abs_mul, abs_of_pos hs]
      nlinarith
    refine ⟨⟨m, e, (abs_lt.mp hm).1, (abs_lt.mp hm).2,
      hemin, hemax, hav⟩, le_rfl⟩

private lemma p12_abs_lt_endpoint_of_exponent_lt
    {fmt : P12RadixFormat} {a : ℝ} (r : P12Representation fmt a)
    {e : ℤ} (hre : r.exponent < e) :
    |a| < ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e := by
  let d : ℕ := (e - r.exponent).toNat
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hz : e - r.exponent ≤ 0 := Int.toNat_eq_zero.mp hd
    omega
  have hfactor : fmt.beta ≤ fmt.beta ^ d := Nat.le_pow hdpos
  have hfactor2 : 2 ≤ fmt.beta ^ d := le_trans fmt.beta_ge_two hfactor
  let B : ℕ := fmt.beta ^ fmt.precision
  have hB2 : 2 ≤ B := le_trans fmt.beta_ge_two (p12_beta_le_mantissaBound fmt)
  have hBm : 1 ≤ B - 1 := by omega
  have hcoeff : B ≤ (B - 1) * fmt.beta ^ d := by
    calc
      B = (B - 1) + 1 := by omega
      _ ≤ (B - 1) + (B - 1) := Nat.add_le_add_left hBm _
      _ = (B - 1) * 2 := by ring
      _ ≤ (B - 1) * fmt.beta ^ d := Nat.mul_le_mul_left _ hfactor2
  have hscale := p12_scale_align fmt (le_of_lt hre)
  have ha := p12_representation_abs_lt r
  have hspos := p12_scale_pos fmt r.exponent
  have hcoeffR : (B : ℝ) ≤ ((B - 1) * fmt.beta ^ d : ℕ) := by
    exact_mod_cast hcoeff
  have hdeq : d = (e - r.exponent).toNat := rfl
  have hbound : fmt.mantissaBound = (B : ℝ) := by
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR B
    norm_cast
  rw [← hdeq] at hscale
  rw [hbound] at ha
  change |a| < (B - 1 : ℕ) * fmt.scale e
  rw [hscale]
  push_cast at hcoeffR ⊢
  have hmul := mul_le_mul_of_nonneg_right hcoeffR (le_of_lt hspos)
  nlinarith

private lemma p12_endpoint_representable
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax) :
    p12Representable fmt
        (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e) ∧
      p12Representable fmt
        (-(((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e)) := by
  let B : ℕ := fmt.beta ^ fmt.precision
  have hB : 0 < B := Nat.pow_pos (p12_beta_pos fmt)
  have hltNat : B - 1 < B := by omega
  have hbound : fmt.mantissaBound = (B : ℝ) := by
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR B
    norm_cast
  have hm : |(((B - 1 : ℕ) : ℤ) : ℝ)| < fmt.mantissaBound := by
    rw [hbound]
    norm_num only [abs_of_nonneg, Int.cast_nonneg]
    exact_mod_cast hltNat
  have hpos := p12_representable_of_scaled_int fmt
    ((B - 1 : ℕ) : ℤ) e hemin hemax hm
  have hpos' : p12Representable fmt
      (((B - 1 : ℕ) : ℝ) * fmt.scale e) := by
    simpa using hpos
  exact ⟨by simpa [B] using hpos', p12_representable_neg hpos'⟩

private lemma p12_nearest_scaled_integer
    (fmt : P12RadixFormat) (e : ℤ) (n : ℤ) (rounded : ℝ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hnear : p12NearestInFormat fmt ((n : ℝ) * fmt.scale e) rounded) :
    rounded = (n : ℝ) * fmt.scale e ∨
      (fmt.mantissaBound ≤ |(n : ℝ)| ∧
        ∃ r : P12Representation fmt rounded, e ≤ r.exponent) := by
  rcases hnear with ⟨⟨r⟩, hnear⟩
  by_cases hn : |(n : ℝ)| < fmt.mantissaBound
  · left
    have hrep := p12_representable_of_scaled_int fmt n e hemin hemax hn
    have hd := hnear ((n : ℝ) * fmt.scale e) hrep
    have hd' : |(n : ℝ) * fmt.scale e - rounded| ≤ 0 := by
      simpa using hd
    have hz : |(n : ℝ) * fmt.scale e - rounded| = 0 := by
      exact le_antisymm hd' (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp hz) |>.symm
  · right
    have hnlarge : fmt.mantissaBound ≤ |(n : ℝ)| := le_of_not_gt hn
    refine ⟨hnlarge, r, ?_⟩
    by_contra her
    have hre : r.exponent < e := lt_of_not_ge her
    have hrs := p12_abs_lt_endpoint_of_exponent_lt r hre
    let B : ℕ := fmt.beta ^ fmt.precision
    let q : ℝ := fmt.scale e
    have hq : 0 < q := p12_scale_pos fmt e
    have hB : 0 < B := Nat.pow_pos (p12_beta_pos fmt)
    have hbound : fmt.mantissaBound = (B : ℝ) := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR B
      norm_cast
    have hnlarge' : (B : ℝ) ≤ |(n : ℝ)| := by simpa [hbound] using hnlarge
    have hendpos := (p12_endpoint_representable fmt e hemin hemax).1
    have hendneg := (p12_endpoint_representable fmt e hemin hemax).2
    change |rounded| < (B - 1 : ℕ) * q at hrs
    have hBmnonneg : (0 : ℝ) ≤ (B - 1 : ℕ) := by positivity
    rcases le_total 0 (n : ℝ) with hnnonneg | hnnonpos
    · have hnB : (B : ℝ) ≤ (n : ℝ) := by
        rw [abs_of_nonneg hnnonneg] at hnlarge'
        exact hnlarge'
      have hznonneg : 0 ≤ (n : ℝ) * q := mul_nonneg hnnonneg (le_of_lt hq)
      have hcandidate_nonneg :
          0 ≤ (n : ℝ) * q - (B - 1 : ℕ) * q := by
        have hBmB : ((B - 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
          exact_mod_cast (Nat.sub_le B 1)
        nlinarith
      have hcomp := hnear (((B - 1 : ℕ) : ℝ) * q) (by
        simpa [B, q] using hendpos)
      have hrev := abs_sub_abs_le_abs_sub ((n : ℝ) * q) rounded
      rw [abs_of_nonneg hznonneg] at hrev
      rw [abs_of_nonneg hcandidate_nonneg] at hcomp
      nlinarith
    · have hnB : (n : ℝ) ≤ -(B : ℝ) := by
        rw [abs_of_nonpos hnnonpos] at hnlarge'
        linarith
      have hznonpos : (n : ℝ) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hnnonpos (le_of_lt hq)
      have hcandidate_nonpos :
          (n : ℝ) * q - (-((B - 1 : ℕ) * q)) ≤ 0 := by
        have hBmB : ((B - 1 : ℕ) : ℝ) ≤ (B : ℝ) := by
          exact_mod_cast (Nat.sub_le B 1)
        nlinarith
      have hcomp := hnear (-(((B - 1 : ℕ) : ℝ) * q)) (by
        simpa [B, q] using hendneg)
      have hrev := abs_sub_abs_le_abs_sub ((n : ℝ) * q) rounded
      rw [abs_of_nonpos hznonpos] at hrev
      rw [abs_of_nonpos hcandidate_nonpos] at hcomp
      nlinarith

private lemma p12_nat_near_multiple
    (beta B a : ℕ) (hbeta : 2 ≤ beta) (hbetaB : beta ≤ B)
    (ha : a < 2 * B - beta / 2) :
    ∃ l : ℕ, l < B ∧
      beta * l ≤ a + beta / 2 ∧ a ≤ beta * l + beta / 2 := by
  let l := (a + beta / 2) / beta
  have hbetapos : 0 < beta := lt_of_lt_of_le Nat.zero_lt_two hbeta
  have hqle : beta / 2 ≤ B :=
    le_trans (Nat.div_le_self beta 2) hbetaB
  have haq : a + beta / 2 < 2 * B := by omega
  have htwo : 2 * B ≤ B * beta := by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_right B hbeta
  have hl : l < B := by
    apply Nat.div_lt_of_lt_mul
    dsimp [l]
    exact lt_of_lt_of_le haq (by simpa [Nat.mul_comm] using htwo)
  have hlower : beta * l ≤ a + beta / 2 := by
    simpa [l, Nat.mul_comm] using Nat.mul_div_le (a + beta / 2) beta
  have hupper0 : a + beta / 2 < beta * (l + 1) := by
    simpa [l] using Nat.lt_mul_div_succ (a + beta / 2) hbetapos
  have hdiv : beta ≤ 2 * (beta / 2) + 1 := by omega
  have hupper : a ≤ beta * l + beta / 2 := by
    simp only [Nat.mul_add, Nat.mul_one] at hupper0
    omega
  exact ⟨l, hl, hlower, hupper⟩

private lemma p12_exists_near_radix_multiple
    (fmt : P12RadixFormat) (n : ℤ)
    (hn : |(n : ℝ)| <
      2 * fmt.mantissaBound - fmt.halfRadixFloor) :
    ∃ l : ℤ, |(l : ℝ)| < fmt.mantissaBound ∧
      |(n : ℝ) - (fmt.beta : ℝ) * (l : ℝ)| ≤
        fmt.halfRadixFloor := by
  let B : ℕ := fmt.beta ^ fmt.precision
  let q : ℕ := fmt.beta / 2
  have hbound : fmt.mantissaBound = (B : ℝ) := by
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR B
    norm_cast
  have hhalf : fmt.halfRadixFloor = (q : ℝ) := by
    rfl
  have hbetaB : fmt.beta ≤ B := p12_beta_le_mantissaBound fmt
  have hqB : q ≤ B := le_trans (Nat.div_le_self fmt.beta 2) hbetaB
  have hq2B : q ≤ 2 * B := le_trans hqB (by omega)
  have hsubcast : ((2 * B - q : ℕ) : ℝ) =
      2 * (B : ℝ) - (q : ℝ) := by
    rw [Nat.cast_sub hq2B]
    push_cast
    rfl
  by_cases hnnonneg : 0 ≤ n
  · let a := n.toNat
    have haCast : (a : ℤ) = n := Int.toNat_of_nonneg hnnonneg
    have hn' : (a : ℝ) < 2 * (B : ℝ) - (q : ℝ) := by
      rw [hbound, hhalf] at hn
      rw [abs_of_nonneg (by exact_mod_cast hnnonneg)] at hn
      have haCastR : (a : ℝ) = (n : ℝ) := by exact_mod_cast haCast
      simpa [haCastR] using hn
    have ha : a < 2 * B - q := by
      rw [← hsubcast] at hn'
      exact_mod_cast hn'
    obtain ⟨l, hlB, hlower, hupper⟩ :=
      p12_nat_near_multiple fmt.beta B a fmt.beta_ge_two hbetaB (by simpa [q] using ha)
    refine ⟨(l : ℕ), ?_, ?_⟩
    · rw [hbound]
      norm_num only [abs_of_nonneg, Int.cast_nonneg]
      exact_mod_cast hlB
    · rw [hhalf]
      have hlowerZ : (fmt.beta : ℤ) * (l : ℤ) ≤ a + q := by exact_mod_cast hlower
      have hupperZ : (a : ℤ) ≤ (fmt.beta : ℤ) * (l : ℤ) + q := by
        exact_mod_cast hupper
      rw [← haCast]
      push_cast
      rw [abs_le]
      have hbounds :
          -((q : ℤ)) ≤ (a : ℤ) - fmt.beta * l ∧
            (a : ℤ) - fmt.beta * l ≤ q := by omega
      constructor
      · exact_mod_cast hbounds.1
      · exact_mod_cast hbounds.2
  · have hnneg : n < 0 := lt_of_not_ge hnnonneg
    let a := (-n).toNat
    have hnegNonneg : 0 ≤ -n := by omega
    have haCast : (a : ℤ) = -n := Int.toNat_of_nonneg hnegNonneg
    have hn' : (a : ℝ) < 2 * (B : ℝ) - (q : ℝ) := by
      rw [hbound, hhalf] at hn
      rw [abs_of_neg (by exact_mod_cast hnneg)] at hn
      have haCastR : (a : ℝ) = -(n : ℝ) := by exact_mod_cast haCast
      simpa [haCastR] using hn
    have ha : a < 2 * B - q := by
      rw [← hsubcast] at hn'
      exact_mod_cast hn'
    obtain ⟨l, hlB, hlower, hupper⟩ :=
      p12_nat_near_multiple fmt.beta B a fmt.beta_ge_two hbetaB (by simpa [q] using ha)
    refine ⟨-((l : ℕ) : ℤ), ?_, ?_⟩
    · rw [hbound]
      norm_num only [Int.cast_neg, abs_neg, abs_of_nonneg, Int.cast_nonneg]
      exact_mod_cast hlB
    · rw [hhalf]
      have hlowerZ : (fmt.beta : ℤ) * (l : ℤ) ≤ a + q := by exact_mod_cast hlower
      have hupperZ : (a : ℤ) ≤ (fmt.beta : ℤ) * (l : ℤ) + q := by
        exact_mod_cast hupper
      have hbounds :
          -((q : ℤ)) ≤ (a : ℤ) - fmt.beta * l ∧
            (a : ℤ) - fmt.beta * l ≤ q := by omega
      rw [show n = -(a : ℤ) by omega]
      push_cast
      rw [show -(a : ℝ) - (fmt.beta : ℝ) * -(l : ℝ) =
          -((a : ℝ) - (fmt.beta : ℝ) * (l : ℝ)) by ring, abs_neg, abs_le]
      constructor
      · exact_mod_cast hbounds.1
      · exact_mod_cast hbounds.2

private lemma p12_representable_of_lattice_and_abs_lt
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e)
    (habs : |z| < fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt z := by
  have hs := p12_scale_pos fmt e
  have hm : |(m : ℝ)| < fmt.mantissaBound := by
    have hzabs : |z| = |(m : ℝ)| * fmt.scale e := by
      calc
        |z| = |(m : ℝ) * fmt.scale e| := congrArg abs hz
        _ = |(m : ℝ)| * fmt.scale e := by rw [abs_mul, abs_of_pos hs]
    nlinarith
  rw [hz]
  exact p12_representable_of_scaled_int fmt m e hemin hemax hm

private lemma p12_bound_scale_representable_at_succ
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e + 1 ≤ fmt.emax) :
    p12Representable fmt (fmt.mantissaBound * fmt.scale e) ∧
      p12Representable fmt (-(fmt.mantissaBound * fmt.scale e)) := by
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fmt.precision_pos)
  let c : ℕ := fmt.beta ^ p
  have hcpos : 0 < c := Nat.pow_pos (p12_beta_pos fmt)
  have hBnat : fmt.beta ^ fmt.precision = c * fmt.beta := by
    rw [hp, pow_succ]
  have hcB : c < fmt.beta ^ fmt.precision := by
    rw [hBnat]
    nlinarith [fmt.beta_ge_two]
  have hm : |(((c : ℕ) : ℤ) : ℝ)| < fmt.mantissaBound := by
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
    norm_num only [abs_of_nonneg, Int.cast_nonneg]
    exact_mod_cast hcB
  have hrep := p12_representable_of_scaled_int fmt (c : ℤ) (e + 1)
    (by omega) hemax hm
  have hscale := p12_scale_align fmt (show e ≤ e + 1 by omega)
  have hvalue : ((c : ℤ) : ℝ) * fmt.scale (e + 1) =
      fmt.mantissaBound * fmt.scale e := by
    rw [hscale]
    have hpow : (e + 1 - e).toNat = 1 := by norm_num
    rw [hpow, pow_one]
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
    rw [hp, pow_succ]
    push_cast
    simp [c]
    ring
  rw [hvalue] at hrep
  exact ⟨hrep, p12_representable_neg hrep⟩

private lemma p12_representable_of_lattice_and_abs_le_of_lt_emax
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e + 1 ≤ fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e)
    (habs : |z| ≤ fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt z := by
  by_cases hlt : |z| < fmt.mantissaBound * fmt.scale e
  · exact p12_representable_of_lattice_and_abs_lt fmt z m e hemin
      (by omega) hz hlt
  · have heq : |z| = fmt.mantissaBound * fmt.scale e :=
      le_antisymm habs (le_of_not_gt hlt)
    have hs := p12_scale_pos fmt e
    have hmabs : |(m : ℝ)| = fmt.mantissaBound := by
      have hzabs : |z| = |(m : ℝ)| * fmt.scale e := by
        calc
          |z| = |(m : ℝ) * fmt.scale e| := congrArg abs hz
          _ = |(m : ℝ)| * fmt.scale e := by rw [abs_mul, abs_of_pos hs]
      nlinarith
    rcases le_total 0 m with hmnonneg | hmnonpos
    · have hmval : (m : ℝ) = fmt.mantissaBound := by
        rw [abs_of_nonneg (by exact_mod_cast hmnonneg)] at hmabs
        exact hmabs
      have hzval : z = fmt.mantissaBound * fmt.scale e := by
        rw [hz, hmval]
      rw [hzval]
      exact (p12_bound_scale_representable_at_succ fmt e hemin hemax).1
    · have hmval : (m : ℝ) = -fmt.mantissaBound := by
        rw [abs_of_nonpos (by exact_mod_cast hmnonpos)] at hmabs
        linarith
      have hzval : z = -(fmt.mantissaBound * fmt.scale e) := by
        rw [hz, hmval]
        ring
      rw [hzval]
      exact (p12_bound_scale_representable_at_succ fmt e hemin hemax).2

private lemma p12_same_exponent_first_sub_representable
    (fmt : P12RadixFormat) (x y s : ℝ) (mx my : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hmx : |(mx : ℝ)| < fmt.mantissaBound)
    (hmy : |(my : ℝ)| < fmt.mantissaBound)
    (hxv : x = (mx : ℝ) * fmt.scale e)
    (hyv : y = (my : ℝ) * fmt.scale e)
    (hcondition : |y| ≤ fmt.condition7Ceiling * fmt.scale e)
    (hnear : p12NearestInFormat fmt (x + y) s) :
    p12Representable fmt (s - x) := by
  let q := fmt.scale e
  let n : ℤ := mx + my
  have hq : 0 < q := p12_scale_pos fmt e
  change |y| ≤ fmt.condition7Ceiling * q at hcondition
  have hzv : x + y = (n : ℝ) * q := by
    rw [hxv, hyv]
    change (mx : ℝ) * q + (my : ℝ) * q = (n : ℝ) * q
    dsimp [n]
    push_cast
    ring
  have hxrep : p12Representable fmt x := by
    rw [hxv]
    exact p12_representable_of_scaled_int fmt mx e hemin hemax hmx
  have hyrep : p12Representable fmt y := by
    rw [hyv]
    exact p12_representable_of_scaled_int fmt my e hemin hemax hmy
  have herr : |(x + y) - s| ≤ |y| := by
    have h := hnear.2 x hxrep
    convert h using 1 <;> ring_nf
  have hmyC : |(my : ℝ)| ≤ fmt.condition7Ceiling := by
    have hyabs : |y| = |(my : ℝ)| * q := by
      calc
        |y| = |(my : ℝ) * q| := congrArg abs hyv
        _ = |(my : ℝ)| * q := by rw [abs_mul, abs_of_pos hq]
    nlinarith
  have hnsmall : |(n : ℝ)| <
      2 * fmt.mantissaBound - fmt.halfRadixFloor := by
    have htri : |(n : ℝ)| ≤ |(mx : ℝ)| + |(my : ℝ)| := by
      dsimp [n]
      push_cast
      exact abs_add_le _ _
    have hid := p12_condition7_add_half fmt
    linarith
  have hnear' : p12NearestInFormat fmt ((n : ℝ) * q) s := by
    rw [← hzv]
    exact hnear
  rcases p12_nearest_scaled_integer fmt e n s hemin hemax hnear' with hs | hs
  · have hsub : s - x = y := by rw [hs, ← hzv]; ring
    rw [hsub]
    exact hyrep
  · rcases hs with ⟨hnlarge, rs, hrs⟩
    have hBqpos : 0 < fmt.mantissaBound * q :=
      mul_pos (p12_mantissaBound_pos fmt) hq
    have hzlarge : fmt.mantissaBound * q ≤ |x + y| := by
      rw [hzv, abs_mul, abs_of_pos hq]
      exact mul_le_mul_of_nonneg_right hnlarge (le_of_lt hq)
    rcases eq_or_lt_of_le hrs with hrse | hrsgt
    · have hrse' : rs.exponent = e := hrse.symm
      have hsv : s = (rs.mantissa : ℝ) * q := by
        simpa [q, hrse'] using rs.value_eq
      have hsabs : |s| < fmt.mantissaBound * q := by
        simpa [q, hrse'] using p12_representation_abs_lt rs
      have hxabs : |x| < fmt.mantissaBound * q := by
        rw [hxv, abs_mul, abs_of_pos hq]
        exact mul_lt_mul_of_pos_right hmx hq
      have hcondStrict : |y| < fmt.mantissaBound * q :=
        lt_of_le_of_lt hcondition
          (mul_lt_mul_of_pos_right (p12_condition7_lt_bound fmt) hq)
      have herrStrict : |(x + y) - s| < |x + y| :=
        lt_of_le_of_lt herr (lt_of_lt_of_le hcondStrict hzlarge)
      have hsame : (0 ≤ x ∧ 0 ≤ s) ∨ (x ≤ 0 ∧ s ≤ 0) := by
        rcases le_total 0 (x + y) with hznonneg | hznonpos
        · left
          have hzlower : fmt.mantissaBound * q ≤ x + y := by
            simpa [abs_of_nonneg hznonneg] using hzlarge
          have hzpos : 0 < x + y := lt_of_lt_of_le hBqpos
            hzlower
          have hspos : 0 < s := by
            have herrZ : |(x + y) - s| < x + y := by
              rw [abs_of_pos hzpos] at herrStrict
              exact herrStrict
            have hh := (abs_lt.mp herrZ).2
            linarith
          have hxnonneg : 0 ≤ x := by
            have hyupper : y ≤ |y| := le_abs_self y
            have hid := p12_condition7_add_half fmt
            have hhpos : 0 < fmt.halfRadixFloor := by
              unfold P12RadixFormat.halfRadixFloor
              exact_mod_cast Nat.div_pos fmt.beta_ge_two (by decide)
            have hidq := congrArg (fun a : ℝ => a * q) hid
            dsimp at hidq
            ring_nf at hidq
            have hhq : 0 < fmt.halfRadixFloor * q := mul_pos hhpos hq
            nlinarith [hzlower]
          exact ⟨hxnonneg, le_of_lt hspos⟩
        · right
          have hzupper : x + y ≤ -(fmt.mantissaBound * q) := by
            have habs : |x + y| = -(x + y) := abs_of_nonpos hznonpos
            rw [habs] at hzlarge
            linarith
          have hzneg : x + y < 0 := by
            nlinarith [hzupper, hBqpos]
          have hsneg : s < 0 := by
            have herrZ : |(x + y) - s| < -(x + y) := by
              rw [abs_of_neg hzneg] at herrStrict
              exact herrStrict
            have hh := (abs_lt.mp herrZ).1
            linarith
          have hxnonpos : x ≤ 0 := by
            have hylower : -|y| ≤ y := neg_abs_le y
            have hid := p12_condition7_add_half fmt
            have hhpos : 0 < fmt.halfRadixFloor := by
              unfold P12RadixFormat.halfRadixFloor
              exact_mod_cast Nat.div_pos fmt.beta_ge_two (by decide)
            have hidq := congrArg (fun a : ℝ => a * q) hid
            dsimp at hidq
            ring_nf at hidq
            have hhq : 0 < fmt.halfRadixFloor * q := mul_pos hhpos hq
            nlinarith [hzupper]
          exact ⟨hxnonpos, le_of_lt hsneg⟩
      have hsubabs : |s - x| < fmt.mantissaBound * q := by
        rcases hsame with hpos | hneg
        · rcases hpos with ⟨hx0, hs0⟩
          rw [abs_lt]
          constructor
          · have hxupper : x < fmt.mantissaBound * q :=
              lt_of_abs_lt hxabs
            nlinarith
          · have hsupper : s < fmt.mantissaBound * q :=
              lt_of_abs_lt hsabs
            nlinarith
        · rcases hneg with ⟨hx0, hs0⟩
          rw [abs_lt]
          constructor
          · have hslower : -(fmt.mantissaBound * q) < s :=
              neg_lt_of_abs_lt hsabs
            nlinarith
          · have hxlower : -(fmt.mantissaBound * q) < x :=
              neg_lt_of_abs_lt hxabs
            nlinarith
      have hsubv : s - x = ((rs.mantissa - mx : ℤ) : ℝ) * q := by
        calc
          s - x = (rs.mantissa : ℝ) * q - x := congrArg (fun a => a - x) hsv
          _ = (rs.mantissa : ℝ) * q - (mx : ℝ) * q := by rw [hxv]
          _ = ((rs.mantissa - mx : ℤ) : ℝ) * q := by push_cast; ring
      exact p12_representable_of_lattice_and_abs_lt fmt (s - x)
        (rs.mantissa - mx) e hemin hemax hsubv (by simpa [q] using hsubabs)
    · have hesucc : e + 1 ≤ fmt.emax :=
        le_trans (by omega : e + 1 ≤ rs.exponent) rs.exponent_upper
      obtain ⟨l, hl, hnl⟩ := p12_exists_near_radix_multiple fmt n hnsmall
      have hscaleSucc := p12_scale_align fmt (show e ≤ e + 1 by omega)
      have hpow : (e + 1 - e).toNat = 1 := by norm_num
      rw [hpow, pow_one] at hscaleSucc
      have hcandidate : p12Representable fmt ((l : ℝ) * fmt.scale (e + 1)) :=
        p12_representable_of_scaled_int fmt l (e + 1) (by omega) hesucc hl
      have hcomp := hnear'.2 ((l : ℝ) * fmt.scale (e + 1)) hcandidate
      have herror : |(x + y) - s| ≤ fmt.halfRadixFloor * q := by
        have hcanddist :
            |(n : ℝ) * q - (l : ℝ) * fmt.scale (e + 1)| =
              |(n : ℝ) - (fmt.beta : ℝ) * (l : ℝ)| * q := by
          rw [hscaleSucc]
          rw [show (n : ℝ) * q - (l : ℝ) * ((fmt.beta : ℝ) * fmt.scale e) =
              ((n : ℝ) - (fmt.beta : ℝ) * (l : ℝ)) * q by
                dsimp [q]; ring]
          rw [abs_mul, abs_of_pos hq]
        rw [hcanddist] at hcomp
        have hh := le_trans hcomp (mul_le_mul_of_nonneg_right hnl (le_of_lt hq))
        simpa [hzv] using hh
      have hsuble : |s - x| ≤ fmt.mantissaBound * q := by
        have htri : |s - x| ≤ |(x + y) - s| + |y| := by
          have := abs_add_le (s - (x + y)) y
          rw [abs_sub_comm] at this
          convert this using 1 <;> ring_nf
        have hid := p12_condition7_add_half fmt
        nlinarith
      let S : ℤ := rs.mantissa *
        (fmt.beta ^ (rs.exponent - e).toNat : ℕ)
      have hsv : s = (S : ℝ) * q := by
        calc
          s = (rs.mantissa : ℝ) * fmt.scale rs.exponent := rs.value_eq
          _ = (S : ℝ) * fmt.scale e :=
            p12_scaled_int_align fmt rs.mantissa hrs
          _ = (S : ℝ) * q := rfl
      have hsubv : s - x = ((S - mx : ℤ) : ℝ) * q := by
        rw [hsv, hxv]
        push_cast
        ring
      exact p12_representable_of_lattice_and_abs_le_of_lt_emax fmt (s - x)
        (S - mx) e hemin hesucc hsubv (by simpa [q] using hsuble)

private lemma p12_two_scale_le_scale_of_lt
    (fmt : P12RadixFormat) {e f : ℤ} (hef : e < f) :
    2 * fmt.scale e ≤ fmt.scale f := by
  let d : ℕ := (f - e).toNat
  have hdpos : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd
    have hz : f - e ≤ 0 := Int.toNat_eq_zero.mp hd
    omega
  have hfactor : fmt.beta ≤ fmt.beta ^ d := Nat.le_pow hdpos
  have htwo : 2 ≤ fmt.beta ^ d := le_trans fmt.beta_ge_two hfactor
  have hscale := p12_scale_align fmt (le_of_lt hef)
  have hd : d = (f - e).toNat := rfl
  rw [← hd] at hscale
  rw [hscale]
  have htwoR : (2 : ℝ) ≤ (fmt.beta ^ d : ℕ) := by exact_mod_cast htwo
  exact mul_le_mul_of_nonneg_right htwoR (le_of_lt (p12_scale_pos fmt e))

private lemma p12_large_nearest_rep_exponent_gt
    (fmt : P12RadixFormat) (e : ℤ) (n : ℤ) (rounded : ℝ)
    (hemin : fmt.emin ≤ e) (hemax : e + 1 ≤ fmt.emax)
    (hnear : p12NearestInFormat fmt ((n : ℝ) * fmt.scale e) rounded)
    (hnlarge : fmt.mantissaBound ≤ |(n : ℝ)|)
    (r : P12Representation fmt rounded) (her : e ≤ r.exponent) :
    e < r.exponent := by
  rcases eq_or_lt_of_le her with heq | hlt
  · exfalso
    have hre : r.exponent = e := heq.symm
    let q := fmt.scale e
    have hq : 0 < q := p12_scale_pos fmt e
    have hrabs : |rounded| < fmt.mantissaBound * q := by
      simpa [q, hre] using p12_representation_abs_lt r
    have hends := p12_bound_scale_representable_at_succ fmt e hemin hemax
    rcases le_total 0 (n : ℝ) with hnnonneg | hnnonpos
    · have hnB : fmt.mantissaBound ≤ (n : ℝ) := by
        simpa [abs_of_nonneg hnnonneg] using hnlarge
      have hznonneg : 0 ≤ (n : ℝ) * q := mul_nonneg hnnonneg (le_of_lt hq)
      have hdiffnonneg :
          0 ≤ (n : ℝ) * q - fmt.mantissaBound * q := by nlinarith
      have hcomp := hnear.2 (fmt.mantissaBound * q) (by simpa [q] using hends.1)
      have hrev := abs_sub_abs_le_abs_sub ((n : ℝ) * q) rounded
      rw [abs_of_nonneg hznonneg] at hrev
      rw [abs_of_nonneg hdiffnonneg] at hcomp
      nlinarith
    · have hnB : (n : ℝ) ≤ -fmt.mantissaBound := by
        rw [abs_of_nonpos hnnonpos] at hnlarge
        linarith
      have hznonpos : (n : ℝ) * q ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnnonpos (le_of_lt hq)
      have hdiffnonpos :
          (n : ℝ) * q - (-(fmt.mantissaBound * q)) ≤ 0 := by nlinarith
      have hcomp := hnear.2 (-(fmt.mantissaBound * q)) (by simpa [q] using hends.2)
      have hrev := abs_sub_abs_le_abs_sub ((n : ℝ) * q) rounded
      rw [abs_of_nonpos hznonpos] at hrev
      rw [abs_of_nonpos hdiffnonpos] at hcomp
      nlinarith
  · exact hlt
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
  rcases hcondition7 with ⟨rx, hcondition⟩
  rcases hy with ⟨ry₀⟩
  have hyltRx : |y| < fmt.mantissaBound * fmt.scale rx.exponent :=
    lt_of_le_of_lt hcondition
      (mul_lt_mul_of_pos_right (p12_condition7_lt_bound fmt)
        (p12_scale_pos fmt rx.exponent))
  obtain ⟨ry, hryx⟩ := p12_lower_representation ry₀ rx.exponent
    rx.exponent_lower rx.exponent_upper hyltRx
  have hmx : |(rx.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨rx.mantissa_lower, rx.mantissa_upper⟩
  have hmy : |(ry.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨ry.mantissa_lower, ry.mantissa_upper⟩
  let q := fmt.scale ry.exponent
  have hq : 0 < q := p12_scale_pos fmt ry.exponent
  let X : ℤ := rx.mantissa *
    (fmt.beta ^ (rx.exponent - ry.exponent).toNat : ℕ)
  have hxv : x = (X : ℝ) * q := by
    calc
      x = (rx.mantissa : ℝ) * fmt.scale rx.exponent := rx.value_eq
      _ = (X : ℝ) * fmt.scale ry.exponent :=
        p12_scaled_int_align fmt rx.mantissa hryx
      _ = (X : ℝ) * q := rfl
  have hyv : y = (ry.mantissa : ℝ) * q := by
    simpa [q] using ry.value_eq
  let n : ℤ := X + ry.mantissa
  have hzv : x + y = (n : ℝ) * q := by
    rw [hxv, hyv]
    dsimp [n]
    push_cast
    ring
  have hnear' : p12NearestInFormat fmt ((n : ℝ) * q) tr.s := by
    rw [← hzv]
    exact run.add
  have hround := p12_nearest_scaled_integer fmt ry.exponent n tr.s
    ry.exponent_lower ry.exponent_upper hnear'
  have herror : |(x + y) - tr.s| ≤ |y| := by
    have h := run.add.2 x hx
    convert h using 1 <;> ring_nf
  have hylt : |y| < fmt.mantissaBound * q := by
    simpa [q] using p12_representation_abs_lt ry
  have hsubRep : p12Representable fmt (tr.s - x) := by
    by_cases heq : ry.exponent = rx.exponent
    · have hxv' : x = (rx.mantissa : ℝ) * fmt.scale rx.exponent := rx.value_eq
      have hyv' : y = (ry.mantissa : ℝ) * fmt.scale rx.exponent := by
        simpa [heq] using ry.value_eq
      exact p12_same_exponent_first_sub_representable fmt x y tr.s
        rx.mantissa ry.mantissa rx.exponent rx.exponent_lower rx.exponent_upper
        hmx hmy hxv' hyv' hcondition run.add
    · have hryxlt : ry.exponent < rx.exponent := lt_of_le_of_ne hryx heq
      rcases hround with hs | hs
      · have hsub : tr.s - x = y := by rw [hs, ← hzv]; ring
        rw [hsub]
        exact ⟨ry⟩
      · rcases hs with ⟨hnlarge, rs, hrs⟩
        have hesucc : ry.exponent + 1 ≤ fmt.emax :=
          le_trans (by omega : ry.exponent + 1 ≤ rx.exponent) rx.exponent_upper
        have hrsgt : ry.exponent < rs.exponent :=
          p12_large_nearest_rep_exponent_gt fmt ry.exponent n tr.s
            ry.exponent_lower hesucc hnear' hnlarge rs hrs
        let k : ℤ := min rs.exponent rx.exponent
        have hkr : k ≤ rs.exponent := min_le_left _ _
        have hkx : k ≤ rx.exponent := min_le_right _ _
        have heyk : ry.exponent < k := lt_min hrsgt hryxlt
        have hkmin : fmt.emin ≤ k :=
          le_min (le_trans ry.exponent_lower (le_of_lt hrsgt))
            (le_trans ry.exponent_lower (le_of_lt hryxlt))
        have hkmax : k ≤ fmt.emax := le_trans hkx rx.exponent_upper
        have hscale2 : 2 * q ≤ fmt.scale k := by
          simpa [q] using p12_two_scale_le_scale_of_lt fmt heyk
        have hsubabs : |tr.s - x| < fmt.mantissaBound * fmt.scale k := by
          have htri : |tr.s - x| ≤ |(x + y) - tr.s| + |y| := by
            have hh := abs_add_le (tr.s - (x + y)) y
            rw [abs_sub_comm] at hh
            convert hh using 1 <;> ring_nf
          have htwice :
              2 * (fmt.mantissaBound * q) ≤
                fmt.mantissaBound * fmt.scale k := by
            have hmnonneg : 0 ≤ fmt.mantissaBound :=
              le_of_lt (p12_mantissaBound_pos fmt)
            have hh := mul_le_mul_of_nonneg_left hscale2 hmnonneg
            nlinarith
          nlinarith
        let S : ℤ := rs.mantissa *
          (fmt.beta ^ (rs.exponent - k).toNat : ℕ)
        let Xk : ℤ := rx.mantissa *
          (fmt.beta ^ (rx.exponent - k).toNat : ℕ)
        have hsv : tr.s = (S : ℝ) * fmt.scale k := by
          calc
            tr.s = (rs.mantissa : ℝ) * fmt.scale rs.exponent := rs.value_eq
            _ = (S : ℝ) * fmt.scale k :=
              p12_scaled_int_align fmt rs.mantissa hkr
        have hxvk : x = (Xk : ℝ) * fmt.scale k := by
          calc
            x = (rx.mantissa : ℝ) * fmt.scale rx.exponent := rx.value_eq
            _ = (Xk : ℝ) * fmt.scale k :=
              p12_scaled_int_align fmt rx.mantissa hkx
        have hsubv : tr.s - x = ((S - Xk : ℤ) : ℝ) * fmt.scale k := by
          calc
            tr.s - x = (S : ℝ) * fmt.scale k - x :=
              congrArg (fun a => a - x) hsv
            _ = (S : ℝ) * fmt.scale k - (Xk : ℝ) * fmt.scale k := by
              rw [hxvk]
            _ = ((S - Xk : ℤ) : ℝ) * fmt.scale k := by push_cast; ring
        exact p12_representable_of_lattice_and_abs_lt fmt (tr.s - x)
          (S - Xk) k hkmin hkmax hsubv hsubabs
  have ht : tr.t = tr.s - x :=
    p12_faithful_eq_of_representable fmt run.first_sub hsubRep
  obtain ⟨S, hsv⟩ : ∃ S : ℤ, tr.s = (S : ℝ) * q := by
    rcases hround with hs | hs
    · refine ⟨n, ?_⟩
      rw [hs]
    · rcases hs with ⟨_, rs, hrs⟩
      let S : ℤ := rs.mantissa *
        (fmt.beta ^ (rs.exponent - ry.exponent).toNat : ℕ)
      refine ⟨S, ?_⟩
      calc
        tr.s = (rs.mantissa : ℝ) * fmt.scale rs.exponent := rs.value_eq
        _ = (S : ℝ) * fmt.scale ry.exponent :=
          p12_scaled_int_align fmt rs.mantissa hrs
        _ = (S : ℝ) * q := rfl
  have hresv : y - (tr.s - x) =
      ((X + ry.mantissa - S : ℤ) : ℝ) * q := by
    calc
      y - (tr.s - x) = (x + y) - tr.s := by ring
      _ = (n : ℝ) * q - tr.s := by rw [hzv]
      _ = (n : ℝ) * q - (S : ℝ) * q := by rw [hsv]
      _ = ((X + ry.mantissa - S : ℤ) : ℝ) * q := by
        dsimp [n]
        push_cast
        ring
  have hresabs : |y - (tr.s - x)| < fmt.mantissaBound * q := by
    have heqabs : |y - (tr.s - x)| = |(x + y) - tr.s| := by
      congr 1
      ring
    rw [heqabs]
    exact lt_of_le_of_lt herror hylt
  have hresRep : p12Representable fmt (y - (tr.s - x)) :=
    p12_representable_of_lattice_and_abs_lt fmt _ _ ry.exponent
      ry.exponent_lower ry.exponent_upper hresv (by simpa [q] using hresabs)
  have hresRep' : p12Representable fmt (y - tr.t) := by
    rw [ht]
    exact hresRep
  have he : tr.e = y - tr.t :=
    p12_faithful_eq_of_representable fmt run.second_sub hresRep'
  refine ⟨ht, he, ?_, ?_⟩
  · rw [he, ht]
    ring
  · rw [abs_sub_comm]
    exact herror

end HighamBench
