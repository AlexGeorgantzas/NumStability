import HighamBench.P12Definitions

namespace HighamBench

private lemma p12_betaR_pos (fmt : P12RadixFormat) : 0 < fmt.betaR := by
  unfold P12RadixFormat.betaR
  exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) fmt.beta_ge_two)

private lemma p12_betaR_ne_zero (fmt : P12RadixFormat) : fmt.betaR ≠ 0 :=
  ne_of_gt (p12_betaR_pos fmt)

private lemma p12_scale_pos (fmt : P12RadixFormat) (e : ℤ) : 0 < fmt.scale e := by
  unfold P12RadixFormat.scale
  exact zpow_pos (p12_betaR_pos fmt) e

private lemma p12_scale_succ (fmt : P12RadixFormat) (e : ℤ) :
    fmt.scale (e + 1) = fmt.betaR * fmt.scale e := by
  unfold P12RadixFormat.scale
  rw [zpow_add₀ (p12_betaR_ne_zero fmt)]
  simp [mul_comm]

private lemma p12_scale_mono (fmt : P12RadixFormat) {e f : ℤ} (hef : e ≤ f) :
    fmt.scale e ≤ fmt.scale f := by
  unfold P12RadixFormat.scale
  apply zpow_le_zpow_right₀
  · have htwo : (2 : ℝ) ≤ fmt.betaR := by
      unfold P12RadixFormat.betaR
      exact_mod_cast fmt.beta_ge_two
    linarith
  · exact hef

private lemma p12_mantissaBound_pos (fmt : P12RadixFormat) :
    0 < fmt.mantissaBound := by
  unfold P12RadixFormat.mantissaBound
  exact pow_pos (p12_betaR_pos fmt) _

private lemma p12_mantissaBound_eq_cast (fmt : P12RadixFormat) :
    fmt.mantissaBound = (fmt.beta ^ fmt.precision : ℕ) := by
  simp [P12RadixFormat.mantissaBound, P12RadixFormat.betaR]

private lemma p12_half_pos (fmt : P12RadixFormat) :
    0 < fmt.halfRadixFloor := by
  unfold P12RadixFormat.halfRadixFloor
  exact_mod_cast ((Nat.one_le_div_iff (by omega : 0 < 2)).2 fmt.beta_ge_two)

private lemma p12_condition7_add_half (fmt : P12RadixFormat) :
    fmt.condition7Ceiling + fmt.halfRadixFloor = fmt.mantissaBound := by
  have hp : fmt.beta ≤ fmt.beta ^ fmt.precision := Nat.le_pow fmt.precision_pos
  have hh : fmt.beta / 2 ≤ fmt.beta ^ fmt.precision :=
    le_trans (Nat.div_le_self _ _) hp
  rw [p12_mantissaBound_eq_cast]
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.halfRadixFloor
  norm_cast
  exact Nat.sub_add_cancel hh

private lemma p12_condition7_lt_bound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  have := p12_condition7_add_half fmt
  have := p12_half_pos fmt
  linarith

private lemma p12_rep_abs_bound
    (fmt : P12RadixFormat) {z : ℝ} (r : P12Representation fmt z) :
    |z| < fmt.mantissaBound * fmt.scale r.exponent := by
  have hm : |(r.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨r.mantissa_lower, r.mantissa_upper⟩
  calc
    |z| = |(r.mantissa : ℝ) * fmt.scale r.exponent| :=
      congrArg abs r.value_eq
    _ = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
      rw [abs_mul, abs_of_pos (p12_scale_pos fmt _)]
    _ < fmt.mantissaBound * fmt.scale r.exponent :=
      mul_lt_mul_of_pos_right hm (p12_scale_pos fmt _)

private lemma p12_representable_zero (fmt : P12RadixFormat) :
    p12Representable fmt 0 := by
  have hbound : 0 < fmt.mantissaBound := by
    unfold P12RadixFormat.mantissaBound
    exact pow_pos (p12_betaR_pos fmt) _
  exact ⟨
    { mantissa := 0
      exponent := fmt.emin
      mantissa_lower := by simpa using neg_lt_zero.mpr hbound
      mantissa_upper := by simpa using hbound
      exponent_lower := le_rfl
      exponent_upper := fmt.emin_le_emax
      value_eq := by simp }⟩

private def p12_rep_of_int_mul_scale
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e)
    (habs : |z| < fmt.mantissaBound * fmt.scale e) :
    P12Representation fmt z := by
  have hs := p12_scale_pos fmt e
  have hmabs : |(m : ℝ)| < fmt.mantissaBound := by
    rw [hz, abs_mul, abs_of_pos hs] at habs
    nlinarith
  exact
    { mantissa := m
      exponent := e
      mantissa_lower := (abs_lt.mp hmabs).1
      mantissa_upper := (abs_lt.mp hmabs).2
      exponent_lower := hemin
      exponent_upper := hemax
      value_eq := hz }

private lemma p12_coeff_at_lower_exponent
    (fmt : P12RadixFormat) {z : ℝ} (r : P12Representation fmt z)
    (e : ℤ) (he : e ≤ r.exponent) :
    ∃ m : ℤ, z = (m : ℝ) * fmt.scale e := by
  let d : ℕ := (r.exponent - e).toNat
  have hdiff : (d : ℤ) = r.exponent - e := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr he)
  refine ⟨r.mantissa * (fmt.beta : ℤ) ^ d, ?_⟩
  have hexp : r.exponent = e + (d : ℤ) := by omega
  calc
    z = (r.mantissa : ℝ) * fmt.scale r.exponent := r.value_eq
    _ = (r.mantissa : ℝ) * fmt.scale (e + (d : ℤ)) := by rw [hexp]
    _ = ((r.mantissa * (fmt.beta : ℤ) ^ d : ℤ) : ℝ) * fmt.scale e := by
      unfold P12RadixFormat.scale
      rw [zpow_add₀ (p12_betaR_ne_zero fmt), zpow_natCast]
      simp only [P12RadixFormat.betaR, Int.cast_mul, Int.cast_pow,
        Int.cast_natCast]
      ring

private lemma p12_rep_sub_of_common_scale
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (e : ℤ) (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent)
    (habs : |a - b| < fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt (a - b) := by
  rcases p12_coeff_at_lower_exponent fmt ra e hea with ⟨ma, hma⟩
  rcases p12_coeff_at_lower_exponent fmt rb e heb with ⟨mb, hmb⟩
  refine ⟨p12_rep_of_int_mul_scale fmt (a - b) (ma - mb) e hemin hemax ?_ habs⟩
  · rw [hma, hmb]
    push_cast
    ring

private lemma p12_exists_rep_at_lower_exponent
    (fmt : P12RadixFormat) {z : ℝ} (r : P12Representation fmt z)
    (e : ℤ) (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (he : e ≤ r.exponent)
    (habs : |z| < fmt.mantissaBound * fmt.scale e) :
    ∃ r' : P12Representation fmt z, r'.exponent = e := by
  rcases p12_coeff_at_lower_exponent fmt r e he with ⟨m, hm⟩
  exact ⟨p12_rep_of_int_mul_scale fmt z m e hemin hemax hm habs, rfl⟩

private lemma p12_boundary_coeff_ge (fmt : P12RadixFormat) :
    fmt.mantissaBound ≤
      (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.betaR) := by
  have hb : (2 : ℝ) ≤ fmt.betaR := by
    unfold P12RadixFormat.betaR
    exact_mod_cast fmt.beta_ge_two
  have hpN : fmt.beta ≤ fmt.beta ^ fmt.precision := Nat.le_pow fmt.precision_pos
  have hp : fmt.betaR ≤ fmt.mantissaBound := by
    simpa [P12RadixFormat.betaR, p12_mantissaBound_eq_cast] using
      (show (fmt.beta : ℝ) ≤ (fmt.beta ^ fmt.precision : ℕ) by exact_mod_cast hpN)
  have hnpos : 0 < fmt.beta ^ fmt.precision :=
    Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_two fmt.beta_ge_two)
  have hn : 1 ≤ fmt.beta ^ fmt.precision := by omega
  have hcast : ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) =
      (fmt.beta ^ fmt.precision : ℕ) - 1 := by
    rw [Nat.cast_sub hn]
    simp
  have hprod : 0 ≤ (fmt.mantissaBound - fmt.betaR) * (fmt.betaR - 1) :=
    mul_nonneg (sub_nonneg.mpr hp) (by linarith)
  rw [hcast, ← p12_mantissaBound_eq_cast]
  nlinarith

private lemma p12_boundary_representable
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax) :
    p12Representable fmt
      (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e) := by
  let n : ℕ := fmt.beta ^ fmt.precision
  have hn : 0 < n := by
    dsimp [n]
    exact Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_two fmt.beta_ge_two)
  have hcast : fmt.mantissaBound = (n : ℝ) := by
    simpa [n] using p12_mantissaBound_eq_cast fmt
  have hs := p12_scale_pos fmt e
  refine ⟨p12_rep_of_int_mul_scale fmt _ (n - 1 : ℕ) e hemin hemax ?_ ?_⟩
  · simp [n]
  · rw [abs_of_nonneg (mul_nonneg (by positivity) hs.le), hcast]
    exact mul_lt_mul_of_pos_right (by exact_mod_cast (Nat.sub_lt hn (by omega))) hs

private lemma p12_neg_representable
    (fmt : P12RadixFormat) {z : ℝ} (hz : p12Representable fmt z) :
    p12Representable fmt (-z) := by
  rcases hz with ⟨r⟩
  refine ⟨
    { mantissa := -r.mantissa
      exponent := r.exponent
      mantissa_lower := ?_
      mantissa_upper := ?_
      exponent_lower := r.exponent_lower
      exponent_upper := r.exponent_upper
      value_eq := ?_ }⟩
  · push_cast
    linarith [r.mantissa_upper]
  · push_cast
    linarith [r.mantissa_lower]
  · calc
      -z = -((r.mantissa : ℝ) * fmt.scale r.exponent) :=
        congrArg Neg.neg r.value_eq
      _ = ((-r.mantissa : ℤ) : ℝ) * fmt.scale r.exponent := by
        push_cast
        ring

private lemma p12_nearest_large_exponent
    (fmt : P12RadixFormat) {z s : ℝ}
    (hnear : p12NearestInFormat fmt z s)
    (rs : P12Representation fmt s) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hzlarge : fmt.mantissaBound * fmt.scale e ≤ |z|) :
    e ≤ rs.exponent := by
  let a : ℝ := ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e
  have hscale := p12_scale_pos fmt e
  have hbound := p12_mantissaBound_pos fmt
  have hBscale : 0 < fmt.mantissaBound * fmt.scale e := mul_pos hbound hscale
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have ha_lt : a < fmt.mantissaBound * fmt.scale e := by
    dsimp [a]
    rw [p12_mantissaBound_eq_cast]
    apply mul_lt_mul_of_pos_right _ hscale
    have hnpos : 0 < fmt.beta ^ fmt.precision :=
      Nat.pow_pos (lt_of_lt_of_le Nat.zero_lt_two fmt.beta_ge_two)
    exact_mod_cast (Nat.sub_lt hnpos (by omega : 0 < 1))
  have habs_s : a ≤ |s| := by
    rcases le_total 0 z with hznonneg | hznonpos
    · have hzB : fmt.mantissaBound * fmt.scale e ≤ z := by
        simpa [abs_of_nonneg hznonneg] using hzlarge
      have hza : a ≤ z := le_trans ha_lt.le hzB
      have hnear_a := hnear.2 a (by
        dsimp [a]
        exact p12_boundary_representable fmt e hemin hemax)
      rw [abs_of_nonneg (sub_nonneg.mpr hza)] at hnear_a
      have hzs : z - s ≤ |z - s| := le_abs_self _
      have has : a ≤ s := by linarith
      exact le_trans has (le_abs_self s)
    · have hzB : z ≤ -(fmt.mantissaBound * fmt.scale e) := by
        rw [abs_of_nonpos hznonpos] at hzlarge
        linarith
      have hza : z ≤ -a := by linarith
      have hnear_a := hnear.2 (-a) (by
        apply p12_neg_representable fmt
        dsimp [a]
        exact p12_boundary_representable fmt e hemin hemax)
      have hzplus : z + a ≤ 0 := by linarith
      rw [show z - -a = z + a by ring, abs_of_nonpos hzplus] at hnear_a
      have hsz : -(z - s) ≤ |z - s| := neg_le_abs _
      have hsa : s ≤ -a := by linarith
      exact le_trans (by linarith : a ≤ -s) (neg_le_abs s)
  by_contra hnot
  have hre : rs.exponent ≤ e - 1 := by omega
  have hscale_le : fmt.scale rs.exponent ≤ fmt.scale (e - 1) :=
    p12_scale_mono fmt hre
  have hsbound := p12_rep_abs_bound fmt rs
  have hmul_le : fmt.mantissaBound * fmt.scale rs.exponent ≤
      fmt.mantissaBound * fmt.scale (e - 1) :=
    mul_le_mul_of_nonneg_left hscale_le hbound.le
  have hboundary : fmt.mantissaBound * fmt.scale (e - 1) ≤ a := by
    have hc := mul_le_mul_of_nonneg_right (p12_boundary_coeff_ge fmt)
      (p12_scale_pos fmt (e - 1)).le
    dsimp [a]
    calc
      fmt.mantissaBound * fmt.scale (e - 1)
          ≤ (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.betaR) *
              fmt.scale (e - 1) := hc
      _ = ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e := by
        rw [show e = (e - 1) + 1 by ring, p12_scale_succ]
        ring
  linarith

private lemma p12_nat_nearest_multiple (n b : ℕ) (hb : 0 < b) :
    ∃ q : ℤ,
      -((b / 2 : ℕ) : ℤ) ≤ (n : ℤ) - (b : ℤ) * q ∧
        (n : ℤ) - (b : ℤ) * q ≤ ((b / 2 : ℕ) : ℤ) := by
  have hrnonneg : 0 ≤ n % b := Nat.zero_le _
  have hrlt : n % b < b := Nat.mod_lt _ hb
  have hdecomp : n % b + b * (n / b) = n := Nat.mod_add_div n b
  have hdecompZ0 : ((n % b : ℕ) : ℤ) +
      (b : ℤ) * ((n / b : ℕ) : ℤ) = (n : ℤ) := by
    exact_mod_cast hdecomp
  have hdecompZ : (n : ℤ) =
      (b : ℤ) * ((n / b : ℕ) : ℤ) + (n % b : ℕ) := by
    omega
  by_cases hsmall : n % b ≤ b / 2
  · have hsmallZ : (n % b : ℤ) ≤ (b / 2 : ℕ) := by exact_mod_cast hsmall
    refine ⟨(n / b : ℕ), ?_, ?_⟩ <;> omega
  · have hother : b - n % b ≤ b / 2 := by omega
    have hotherZ : ((b - n % b : ℕ) : ℤ) ≤ (b / 2 : ℕ) := by
      exact_mod_cast hother
    have hrle : n % b ≤ b := hrlt.le
    have hsubZ : ((b - n % b : ℕ) : ℤ) = (b : ℤ) - (n % b : ℕ) := by
      rw [Nat.cast_sub hrle]
    have hres : (n : ℤ) - (b : ℤ) * (((n / b : ℕ) : ℤ) + 1) =
        -((b : ℤ) - (n % b : ℕ)) := by
      rw [hdecompZ]
      ring
    refine ⟨((n / b : ℕ) : ℤ) + 1, ?_, ?_⟩ <;> rw [hres] <;> omega

private lemma p12_int_nearest_multiple (n : ℤ) (b : ℕ) (hb : 0 < b) :
    ∃ q : ℤ, |n - (b : ℤ) * q| ≤ (b / 2 : ℕ) := by
  cases n with
  | ofNat n =>
      rcases p12_nat_nearest_multiple n b hb with ⟨q, hlo, hhi⟩
      refine ⟨q, (abs_le.mpr ?_)⟩
      simpa using And.intro hlo hhi
  | negSucc n =>
      rcases p12_nat_nearest_multiple (n + 1) b hb with ⟨q, hlo, hhi⟩
      have hn : Int.negSucc n = -((n + 1 : ℕ) : ℤ) := by omega
      refine ⟨-q, ?_⟩
      rw [hn]
      have heq : -((n + 1 : ℕ) : ℤ) - (b : ℤ) * -q =
          -(((n + 1 : ℕ) : ℤ) - (b : ℤ) * q) := by ring
      rw [heq, abs_neg]
      exact abs_le.mpr ⟨hlo, hhi⟩

private lemma p12_nearest_error_at_common_scale
    (fmt : P12RadixFormat) {z s : ℝ}
    (hnear : p12NearestInFormat fmt z s)
    (e : ℤ) (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (n : ℤ) (hz : z = (n : ℝ) * fmt.scale e)
    (hzabs : |z| <
      (2 * fmt.mantissaBound - fmt.halfRadixFloor) * fmt.scale e) :
    |z - s| ≤ fmt.halfRadixFloor * fmt.scale e := by
  have hbetaN : 0 < fmt.beta := lt_of_lt_of_le Nat.zero_lt_two fmt.beta_ge_two
  rcases p12_int_nearest_multiple n fmt.beta hbetaN with ⟨q, hq⟩
  have hqR : |(n : ℝ) - fmt.betaR * (q : ℝ)| ≤ fmt.halfRadixFloor := by
    have hqcast : ((|n - (fmt.beta : ℤ) * q| : ℤ) : ℝ) ≤
        (((fmt.beta / 2 : ℕ) : ℤ) : ℝ) := by
      exact_mod_cast hq
    unfold P12RadixFormat.betaR P12RadixFormat.halfRadixFloor
    simpa using hqcast
  have hscale := p12_scale_pos fmt e
  have hnabs : |(n : ℝ)| < 2 * fmt.mantissaBound - fmt.halfRadixFloor := by
    have hzrewrite : |z| = |(n : ℝ)| * fmt.scale e := by
      rw [hz, abs_mul, abs_of_pos hscale]
    rw [hzrewrite] at hzabs
    nlinarith
  have hbeta : (2 : ℝ) ≤ fmt.betaR := by
    unfold P12RadixFormat.betaR
    exact_mod_cast fmt.beta_ge_two
  have hqnonneg : 0 ≤ |(q : ℝ)| := abs_nonneg _
  have hbetaq_abs : fmt.betaR * |(q : ℝ)| < 2 * fmt.mantissaBound := by
    have htri : |fmt.betaR * (q : ℝ)| ≤
        |(n : ℝ)| + |(n : ℝ) - fmt.betaR * (q : ℝ)| := by
      calc
        |fmt.betaR * (q : ℝ)| =
            |(n : ℝ) + -( (n : ℝ) - fmt.betaR * (q : ℝ))| := by
              congr 1
              ring
        _ ≤ |(n : ℝ)| + |-( (n : ℝ) - fmt.betaR * (q : ℝ))| :=
          abs_add_le _ _
        _ = |(n : ℝ)| + |(n : ℝ) - fmt.betaR * (q : ℝ)| := by rw [abs_neg]
    rw [abs_mul, abs_of_pos (p12_betaR_pos fmt)] at htri
    linarith
  have hqbound : |(q : ℝ)| < fmt.mantissaBound := by
    nlinarith
  let c : ℝ := (q : ℝ) * fmt.scale (e + 1)
  have hcabs : |c| < fmt.mantissaBound * fmt.scale (e + 1) := by
    dsimp [c]
    rw [abs_mul, abs_of_pos (p12_scale_pos fmt _)]
    exact mul_lt_mul_of_pos_right hqbound (p12_scale_pos fmt _)
  have hcrep : p12Representable fmt c := by
    refine ⟨p12_rep_of_int_mul_scale fmt c q (e + 1) ?_ ?_ rfl hcabs⟩
    · omega
    · omega
  have hzc : |z - c| ≤ fmt.halfRadixFloor * fmt.scale e := by
    have heq : z - c = ((n : ℝ) - fmt.betaR * (q : ℝ)) * fmt.scale e := by
      dsimp [c]
      rw [hz, p12_scale_succ]
      ring
    rw [heq, abs_mul, abs_of_pos hscale]
    exact mul_le_mul_of_nonneg_right hqR hscale.le
  exact le_trans (hnear.2 c hcrep) hzc

private lemma p12_bound_scale_representable_succ
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax) :
    p12Representable fmt (fmt.mantissaBound * fmt.scale e) := by
  cases hp : fmt.precision with
  | zero =>
      have hpos := fmt.precision_pos
      omega
  | succ k =>
      have hbeta : (1 : ℝ) < fmt.betaR := by
        have htwo : (2 : ℝ) ≤ fmt.betaR := by
          unfold P12RadixFormat.betaR
          exact_mod_cast fmt.beta_ge_two
        linarith
      let m : ℤ := (fmt.beta ^ k : ℕ)
      have hmcast : (m : ℝ) = fmt.betaR ^ k := by
        dsimp [m]
        simp [P12RadixFormat.betaR]
      have hvalue : fmt.mantissaBound * fmt.scale e =
          (m : ℝ) * fmt.scale (e + 1) := by
        rw [p12_scale_succ, hmcast]
        simp [P12RadixFormat.mantissaBound, hp, pow_succ]
        ring
      have hm_lt : |(m : ℝ)| < fmt.mantissaBound := by
        rw [hmcast, abs_of_pos (pow_pos (p12_betaR_pos fmt) _)]
        simp [P12RadixFormat.mantissaBound, hp, pow_succ]
        have hkpos := pow_pos (p12_betaR_pos fmt) k
        nlinarith [mul_pos hkpos (sub_pos.mpr hbeta)]
      have habs : |fmt.mantissaBound * fmt.scale e| <
          fmt.mantissaBound * fmt.scale (e + 1) := by
        rw [hvalue, abs_mul, abs_of_pos (p12_scale_pos fmt _)]
        exact mul_lt_mul_of_pos_right hm_lt (p12_scale_pos fmt _)
      exact ⟨p12_rep_of_int_mul_scale fmt _ m (e + 1) (by omega) (by omega)
        hvalue habs⟩

private lemma p12_nearest_large_exponent_succ
    (fmt : P12RadixFormat) {z s : ℝ}
    (hnear : p12NearestInFormat fmt z s)
    (rs : P12Representation fmt s) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hzlarge : fmt.mantissaBound * fmt.scale e ≤ |z|) :
    e < rs.exponent := by
  let a : ℝ := fmt.mantissaBound * fmt.scale e
  have harep : p12Representable fmt a := by
    dsimp [a]
    exact p12_bound_scale_representable_succ fmt e hemin hemax
  have habs_s : a ≤ |s| := by
    rcases le_total 0 z with hznonneg | hznonpos
    · have hza : a ≤ z := by simpa [a, abs_of_nonneg hznonneg] using hzlarge
      have hn := hnear.2 a harep
      rw [abs_of_nonneg (sub_nonneg.mpr hza)] at hn
      have hzs : z - s ≤ |z - s| := le_abs_self _
      have has : a ≤ s := by linarith
      exact le_trans has (le_abs_self s)
    · have hza : z ≤ -a := by
        rw [abs_of_nonpos hznonpos] at hzlarge
        dsimp [a]
        linarith
      have hn := hnear.2 (-a) (p12_neg_representable fmt harep)
      have hza₀ : z + a ≤ 0 := by linarith
      rw [show z - -a = z + a by ring, abs_of_nonpos hza₀] at hn
      have hsz : -(z - s) ≤ |z - s| := neg_le_abs _
      have hsa : s ≤ -a := by linarith
      exact le_trans (by linarith : a ≤ -s) (neg_le_abs s)
  by_contra hnot
  have hre : rs.exponent ≤ e := by omega
  have hsbound := p12_rep_abs_bound fmt rs
  have hscale := p12_scale_mono fmt hre
  have hmul := mul_le_mul_of_nonneg_left hscale (p12_mantissaBound_pos fmt).le
  dsimp [a] at habs_s
  linarith

private lemma p12_rep_sub_of_common_scale_le
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    (e : ℤ) (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent)
    (habs : |a - b| ≤ fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt (a - b) := by
  by_cases hstrict : |a - b| < fmt.mantissaBound * fmt.scale e
  · exact p12_rep_sub_of_common_scale fmt ra rb e hemin hemax.le hea heb hstrict
  · have heq : |a - b| = fmt.mantissaBound * fmt.scale e :=
      le_antisymm habs (le_of_not_gt hstrict)
    rcases le_total 0 (a - b) with hnonneg | hnonpos
    · rw [abs_of_nonneg hnonneg] at heq
      rw [heq]
      exact p12_bound_scale_representable_succ fmt e hemin hemax
    · rw [abs_of_nonpos hnonpos] at heq
      have hneg : a - b = -(fmt.mantissaBound * fmt.scale e) := by linarith
      rw [hneg]
      apply p12_neg_representable fmt
      exact p12_bound_scale_representable_succ fmt e hemin hemax

private lemma p12_nearest_eq_of_representable
    (fmt : P12RadixFormat) {exact rounded : ℝ}
    (hnear : p12NearestInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  have h := hnear.2 exact hexact
  simp only [sub_self, abs_zero] at h
  have hz : exact - rounded = 0 := abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  linarith

private lemma p12_faithful_eq_of_representable
    (fmt : P12RadixFormat) {exact rounded : ℝ}
    (hfaith : p12FaithfulInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  by_contra hne
  have hnot := hfaith.2 exact hexact
  apply hnot
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl ⟨hlt, le_rfl⟩
  · exact Or.inr ⟨le_rfl, hgt⟩

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
  rcases hcondition7 with ⟨rx, hy_condition⟩
  rcases hy with ⟨ry₀⟩
  rcases run.add.1 with ⟨rs⟩
  have hy_lt_x : |y| < fmt.mantissaBound * fmt.scale rx.exponent := by
    calc
      |y| ≤ fmt.condition7Ceiling * fmt.scale rx.exponent := hy_condition
      _ < fmt.mantissaBound * fmt.scale rx.exponent :=
        mul_lt_mul_of_pos_right (p12_condition7_lt_bound fmt)
          (p12_scale_pos fmt rx.exponent)
  obtain ⟨ry, heyx⟩ : ∃ ry : P12Representation fmt y,
      ry.exponent ≤ rx.exponent := by
    by_cases hle : ry₀.exponent ≤ rx.exponent
    · exact ⟨ry₀, hle⟩
    · have hxe : rx.exponent ≤ ry₀.exponent := by omega
      rcases p12_exists_rep_at_lower_exponent fmt ry₀ rx.exponent
          rx.exponent_lower rx.exponent_upper hxe hy_lt_x with ⟨ry, hry⟩
      exact ⟨ry, by omega⟩
  have hy_rep_bound := p12_rep_abs_bound fmt ry
  have herror : |tr.s - (x + y)| ≤ |y| := by
    calc
      |tr.s - (x + y)| = |(x + y) - tr.s| := abs_sub_comm _ _
      _ ≤ |(x + y) - x| := run.add.2 x hx
      _ = |y| := by congr 1 <;> ring
  rcases p12_coeff_at_lower_exponent fmt rx ry.exponent heyx with ⟨mx, hxc⟩
  rcases p12_coeff_at_lower_exponent fmt ry ry.exponent le_rfl with ⟨my, hyc⟩
  let n : ℤ := mx + my
  have hsumc : x + y = (n : ℝ) * fmt.scale ry.exponent := by
    dsimp [n]
    calc
      x + y = (mx : ℝ) * fmt.scale ry.exponent +
          (my : ℝ) * fmt.scale ry.exponent := congrArg₂ (.+.) hxc hyc
      _ = ((mx + my : ℤ) : ℝ) * fmt.scale ry.exponent := by
        push_cast
        ring
  have htriangle : |tr.s - x| ≤ |tr.s - (x + y)| + |y| := by
    calc
      |tr.s - x| = |(tr.s - (x + y)) + y| := by congr 1 <;> ring
      _ ≤ |tr.s - (x + y)| + |y| := abs_add_le _ _
  have hmain : p12Representable fmt (tr.s - x) ∧
      ∃ ms : ℤ, tr.s = (ms : ℝ) * fmt.scale ry.exponent := by
    by_cases hsmall : |x + y| < fmt.mantissaBound * fmt.scale ry.exponent
    · have hsumrep : p12Representable fmt (x + y) :=
        ⟨p12_rep_of_int_mul_scale fmt (x + y) n ry.exponent
          ry.exponent_lower ry.exponent_upper hsumc hsmall⟩
      have hs_exact : tr.s = x + y :=
        p12_nearest_eq_of_representable fmt run.add hsumrep
      have hsubrep : p12Representable fmt (tr.s - x) := by
        have heq : tr.s - x = y := by rw [hs_exact]; ring
        rw [heq]
        exact ⟨ry⟩
      refine ⟨hsubrep, n, ?_⟩
      exact hs_exact.trans hsumc
    · have hlarge : fmt.mantissaBound * fmt.scale ry.exponent ≤ |x + y| :=
        le_of_not_gt hsmall
      have hrse : ry.exponent ≤ rs.exponent :=
        p12_nearest_large_exponent fmt run.add rs ry.exponent
          ry.exponent_lower ry.exponent_upper hlarge
      have hsubrep : p12Representable fmt (tr.s - x) := by
        by_cases heyl : ry.exponent < rx.exponent
        · have heyrx : ry.exponent + 1 ≤ rx.exponent := by omega
          have heymax : ry.exponent < fmt.emax :=
            lt_of_lt_of_le heyl rx.exponent_upper
          have hrs_strict : ry.exponent < rs.exponent :=
            p12_nearest_large_exponent_succ fmt run.add rs ry.exponent
              ry.exponent_lower heymax hlarge
          have heyrs : ry.exponent + 1 ≤ rs.exponent := by omega
          have htwo : (2 : ℝ) ≤ fmt.betaR := by
            unfold P12RadixFormat.betaR
            exact_mod_cast fmt.beta_ge_two
          have hbasepos : 0 < fmt.mantissaBound * fmt.scale ry.exponent :=
            mul_pos (p12_mantissaBound_pos fmt) (p12_scale_pos fmt _)
          have hlt_two : |tr.s - x| <
              2 * (fmt.mantissaBound * fmt.scale ry.exponent) := by
            nlinarith
          have htwo_next :
              2 * (fmt.mantissaBound * fmt.scale ry.exponent) ≤
                fmt.mantissaBound * fmt.scale (ry.exponent + 1) := by
            rw [p12_scale_succ]
            nlinarith [mul_nonneg (p12_mantissaBound_pos fmt).le
              (p12_scale_pos fmt ry.exponent).le]
          exact p12_rep_sub_of_common_scale fmt rs rx (ry.exponent + 1)
            (le_trans ry.exponent_lower (by omega))
            (le_trans heyrx rx.exponent_upper) heyrs heyrx
            (lt_of_lt_of_le hlt_two htwo_next)
        · have heqexp : ry.exponent = rx.exponent := by omega
          by_cases hexmax : rx.exponent < fmt.emax
          · have hsum_abs : |x + y| <
                (2 * fmt.mantissaBound - fmt.halfRadixFloor) *
                  fmt.scale ry.exponent := by
              have hx_abs := p12_rep_abs_bound fmt rx
              have hxy := abs_add_le x y
              have hconst := p12_condition7_add_half fmt
              rw [heqexp]
              nlinarith [p12_scale_pos fmt rx.exponent]
            have hhalf := p12_nearest_error_at_common_scale fmt run.add
              ry.exponent ry.exponent_lower (by omega) n hsumc hsum_abs
            have hle_bound : |tr.s - x| ≤
                fmt.mantissaBound * fmt.scale ry.exponent := by
              have hconst := p12_condition7_add_half fmt
              calc
                |tr.s - x| ≤ |tr.s - (x + y)| + |y| := htriangle
                _ ≤ fmt.halfRadixFloor * fmt.scale ry.exponent +
                    fmt.condition7Ceiling * fmt.scale ry.exponent := by
                      gcongr
                      · simpa only [abs_sub_comm] using hhalf
                      · simpa [heqexp] using hy_condition
                _ = fmt.mantissaBound * fmt.scale ry.exponent := by
                      rw [← hconst]
                      ring
            exact p12_rep_sub_of_common_scale_le fmt rs rx ry.exponent
              ry.exponent_lower (by simpa [heqexp] using hexmax) hrse heyx hle_bound
          · have hex_eq_max : rx.exponent = fmt.emax :=
              le_antisymm rx.exponent_upper (le_of_not_gt hexmax)
            have hs_abs₀ := p12_rep_abs_bound fmt rs
            have hs_scale : fmt.scale rs.exponent ≤ fmt.scale ry.exponent := by
              apply p12_scale_mono fmt
              rw [heqexp, hex_eq_max]
              exact rs.exponent_upper
            have hs_abs : |tr.s| < fmt.mantissaBound * fmt.scale ry.exponent :=
              lt_of_lt_of_le hs_abs₀
                (mul_le_mul_of_nonneg_left hs_scale (p12_mantissaBound_pos fmt).le)
            have hx_abs₀ := p12_rep_abs_bound fmt rx
            have hx_abs : |x| < fmt.mantissaBound * fmt.scale ry.exponent := by
              simpa [heqexp] using hx_abs₀
            have hzero := run.add.2 0 (p12_representable_zero fmt)
            simp only [sub_zero, abs_zero] at hzero
            have hstrict : |tr.s - x| <
                fmt.mantissaBound * fmt.scale ry.exponent := by
              rcases le_total 0 (x + y) with hznonneg | hznonpos
              · have hzB : fmt.mantissaBound * fmt.scale ry.exponent ≤ x + y := by
                  simpa [abs_of_nonneg hznonneg] using hlarge
                have hxpos : 0 ≤ x := by
                  by_contra hxneg
                  have hyle : y ≤ |y| := le_abs_self y
                  nlinarith
                have hspos : 0 ≤ tr.s := by
                  rw [abs_of_nonneg hznonneg] at hzero
                  have hzsub : (x + y) - tr.s ≤ |(x + y) - tr.s| := le_abs_self _
                  linarith
                rcases (abs_lt.mp hs_abs) with ⟨hslo, hshi⟩
                rcases (abs_lt.mp hx_abs) with ⟨hxlo, hxhi⟩
                rw [abs_lt]
                constructor <;> linarith
              · have hzB : x + y ≤ -(fmt.mantissaBound * fmt.scale ry.exponent) := by
                  rw [abs_of_nonpos hznonpos] at hlarge
                  linarith
                have hxneg : x ≤ 0 := by
                  by_contra hxpos
                  have hylo : -|y| ≤ y := neg_abs_le y
                  nlinarith
                have hsneg : tr.s ≤ 0 := by
                  rw [abs_of_nonpos hznonpos] at hzero
                  have hzsub : -((x + y) - tr.s) ≤ |(x + y) - tr.s| := neg_le_abs _
                  linarith
                rcases (abs_lt.mp hs_abs) with ⟨hslo, hshi⟩
                rcases (abs_lt.mp hx_abs) with ⟨hxlo, hxhi⟩
                rw [abs_lt]
                constructor <;> linarith
            exact p12_rep_sub_of_common_scale fmt rs rx ry.exponent
              ry.exponent_lower ry.exponent_upper hrse (by omega) hstrict
      rcases p12_coeff_at_lower_exponent fmt rs ry.exponent hrse with ⟨ms, hms⟩
      exact ⟨hsubrep, ms, hms⟩
  rcases hmain with ⟨hsubrep, ms, hsc⟩
  have ht : tr.t = tr.s - x :=
    p12_faithful_eq_of_representable fmt run.first_sub hsubrep
  have hres_eq : y - (tr.s - x) = ((mx + my - ms : ℤ) : ℝ) *
      fmt.scale ry.exponent := by
    calc
      y - (tr.s - x) = (my : ℝ) * fmt.scale ry.exponent - (tr.s - x) :=
        congrArg (fun yy => yy - (tr.s - x)) hyc
      _ = (my : ℝ) * fmt.scale ry.exponent -
          ((ms : ℝ) * fmt.scale ry.exponent - x) :=
        congrArg (fun ss => (my : ℝ) * fmt.scale ry.exponent - (ss - x)) hsc
      _ = (my : ℝ) * fmt.scale ry.exponent -
          ((ms : ℝ) * fmt.scale ry.exponent -
            (mx : ℝ) * fmt.scale ry.exponent) :=
        congrArg (fun xx => (my : ℝ) * fmt.scale ry.exponent -
          ((ms : ℝ) * fmt.scale ry.exponent - xx)) hxc
      _ = ((mx + my - ms : ℤ) : ℝ) * fmt.scale ry.exponent := by
        push_cast
        ring
  have hres_abs : |y - (tr.s - x)| <
      fmt.mantissaBound * fmt.scale ry.exponent := by
    calc
      |y - (tr.s - x)| = |(x + y) - tr.s| := by
        congr 1
        ring
      _ = |tr.s - (x + y)| := abs_sub_comm _ _
      _ ≤ |y| := herror
      _ < fmt.mantissaBound * fmt.scale ry.exponent := hy_rep_bound
  have hresrep : p12Representable fmt (y - (tr.s - x)) :=
    ⟨p12_rep_of_int_mul_scale fmt _ (mx + my - ms) ry.exponent
      ry.exponent_lower ry.exponent_upper hres_eq hres_abs⟩
  have hresrep_t : p12Representable fmt (y - tr.t) := by
    rw [ht]
    exact hresrep
  have he : tr.e = y - tr.t :=
    p12_faithful_eq_of_representable fmt run.second_sub hresrep_t
  refine ⟨ht, he, ?_, herror⟩
  rw [he, ht]
  ring

end HighamBench
