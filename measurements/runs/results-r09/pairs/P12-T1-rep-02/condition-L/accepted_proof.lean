import HighamBench.P12Definitions

namespace HighamBench

private lemma p12_betaR_pos (fmt : P12RadixFormat) : 0 < fmt.betaR := by
  unfold P12RadixFormat.betaR
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)

private lemma p12_scale_pos (fmt : P12RadixFormat) (e : ℤ) :
    0 < fmt.scale e := by
  unfold P12RadixFormat.scale
  exact zpow_pos (p12_betaR_pos fmt) _

private lemma p12_scale_mono (fmt : P12RadixFormat) {e f : ℤ}
    (hef : e ≤ f) : fmt.scale e ≤ fmt.scale f := by
  unfold P12RadixFormat.scale
  exact zpow_le_zpow_right₀ (by
    unfold P12RadixFormat.betaR
    exact_mod_cast (show 1 ≤ fmt.beta from le_trans (by norm_num) fmt.beta_ge_two)) hef

private lemma p12_scale_eq_pow_mul (fmt : P12RadixFormat) {e f : ℤ}
    (hef : e ≤ f) :
    fmt.scale f =
      ((fmt.beta ^ (f - e).toNat : ℕ) : ℝ) * fmt.scale e := by
  have hnonneg : 0 ≤ f - e := sub_nonneg.mpr hef
  have hbase : (fmt.betaR : ℝ) ≠ 0 := ne_of_gt (p12_betaR_pos fmt)
  have hp :
      fmt.betaR ^ (f - e) =
        ((fmt.beta ^ (f - e).toNat : ℕ) : ℝ) := by
    conv_lhs => rw [← Int.toNat_of_nonneg hnonneg, zpow_natCast]
    unfold P12RadixFormat.betaR
    norm_cast
  unfold P12RadixFormat.scale
  calc
    fmt.betaR ^ f = fmt.betaR ^ (f - e) * fmt.betaR ^ e := by
      rw [← zpow_add₀ hbase]
      congr 1
      omega
    _ = ((fmt.beta ^ (f - e).toNat : ℕ) : ℝ) * fmt.betaR ^ e := by
      rw [hp]

private lemma p12_scale_succ (fmt : P12RadixFormat) (e : ℤ) :
    fmt.scale (e + 1) = fmt.betaR * fmt.scale e := by
  simpa using (p12_scale_eq_pow_mul fmt (e := e) (f := e + 1) (by omega))

private lemma p12_rep_abs_lt (fmt : P12RadixFormat) {z : ℝ}
    (r : P12Representation fmt z) :
    |z| < fmt.mantissaBound * fmt.scale r.exponent := by
  have hm : |(r.mantissa : ℝ)| < fmt.mantissaBound :=
    (abs_lt).2 ⟨r.mantissa_lower, r.mantissa_upper⟩
  calc
    |z| = |(r.mantissa : ℝ) * fmt.scale r.exponent| :=
      congrArg abs r.value_eq
    _ = |(r.mantissa : ℝ)| * fmt.scale r.exponent := by
      rw [abs_mul, abs_of_pos (p12_scale_pos fmt r.exponent)]
    _ < fmt.mantissaBound * fmt.scale r.exponent :=
      mul_lt_mul_of_pos_right hm (p12_scale_pos fmt r.exponent)

private lemma p12_representable_of_scaled_int
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hm : |(m : ℝ)| < fmt.mantissaBound)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e) :
    p12Representable fmt z := by
  refine ⟨⟨m, e, ?_, ?_, hemin, hemax, hz⟩⟩
  · exact (abs_lt.mp hm).1
  · exact (abs_lt.mp hm).2

private lemma p12_scaled_int_at_lower_exponent
    (fmt : P12RadixFormat) {z : ℝ} (r : P12Representation fmt z)
    {e : ℤ} (he : e ≤ r.exponent) :
    ∃ m : ℤ, z = (m : ℝ) * fmt.scale e := by
  let q : ℕ := fmt.beta ^ (r.exponent - e).toNat
  refine ⟨r.mantissa * (q : ℤ), ?_⟩
  calc
    z = (r.mantissa : ℝ) * fmt.scale r.exponent := r.value_eq
    _ = (r.mantissa : ℝ) * (((q : ℕ) : ℝ) * fmt.scale e) := by
      rw [p12_scale_eq_pow_mul fmt he]
    _ = ((r.mantissa * (q : ℤ) : ℤ) : ℝ) * fmt.scale e := by
      push_cast
      ring

private lemma p12_representable_of_lattice_and_bound
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e)
    (hbound : |z| < fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt z := by
  have hs := p12_scale_pos fmt e
  have habs : |(m : ℝ)| * fmt.scale e = |z| := by
    rw [hz, abs_mul, abs_of_pos hs]
  apply p12_representable_of_scaled_int fmt z m e _ hemin hemax hz
  nlinarith

private lemma p12_representable_of_lattice_and_closed_bound_with_room
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e)
    (hbound : |z| ≤ fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt z := by
  by_cases hstrict : |z| < fmt.mantissaBound * fmt.scale e
  · exact p12_representable_of_lattice_and_bound fmt z m e hemin (le_of_lt hemax)
      hz hstrict
  · have heq : |z| = fmt.mantissaBound * fmt.scale e :=
      le_antisymm hbound (le_of_not_gt hstrict)
    obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt fmt.precision_pos)
    let k : ℕ := fmt.beta ^ p
    have hkpos : 0 < k := pow_pos (lt_of_lt_of_le (by omega) fmt.beta_ge_two) _
    have hklt : (k : ℝ) < fmt.mantissaBound := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      rw [hp, pow_succ]
      norm_cast
      have hbetaone : 1 < fmt.beta := lt_of_lt_of_le (by omega) fmt.beta_ge_two
      simpa [k, Nat.mul_comm] using lt_mul_of_one_lt_left hkpos hbetaone
    have hBscale :
        fmt.mantissaBound * fmt.scale e = (k : ℝ) * fmt.scale (e + 1) := by
      unfold P12RadixFormat.mantissaBound
      rw [hp, pow_succ, p12_scale_succ]
      unfold P12RadixFormat.betaR
      push_cast
      simp only [k, Nat.cast_pow]
      ring
    by_cases hznonneg : 0 ≤ z
    · have hzpos : z = (k : ℝ) * fmt.scale (e + 1) := by
        rw [abs_of_nonneg hznonneg, hBscale] at heq
        exact heq
      exact p12_representable_of_scaled_int fmt z (k : ℤ) (e + 1)
        (by simpa [abs_of_nonneg (show (0 : ℝ) ≤ k by positivity)] using hklt)
        (by omega) (by omega) (by simpa using hzpos)
    · have hzneg : z = (-(k : ℤ) : ℤ) * fmt.scale (e + 1) := by
        have hznonpos : z ≤ 0 := le_of_not_ge hznonneg
        rw [abs_of_nonpos hznonpos, hBscale] at heq
        push_cast
        nlinarith
      exact p12_representable_of_scaled_int fmt z (-(k : ℤ)) (e + 1)
        (by simpa [abs_of_nonneg (show (0 : ℝ) ≤ k by positivity)] using hklt)
        (by omega) (by omega) hzneg

private lemma p12_lattice_add
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    {e : ℤ} (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent) :
    ∃ m : ℤ, a + b = (m : ℝ) * fmt.scale e := by
  obtain ⟨ma, hma⟩ := p12_scaled_int_at_lower_exponent fmt ra hea
  obtain ⟨mb, hmb⟩ := p12_scaled_int_at_lower_exponent fmt rb heb
  refine ⟨ma + mb, ?_⟩
  rw [hma, hmb]
  push_cast
  ring

private lemma p12_lattice_sub
    (fmt : P12RadixFormat) {a b : ℝ}
    (ra : P12Representation fmt a) (rb : P12Representation fmt b)
    {e : ℤ} (hea : e ≤ ra.exponent) (heb : e ≤ rb.exponent) :
    ∃ m : ℤ, a - b = (m : ℝ) * fmt.scale e := by
  obtain ⟨ma, hma⟩ := p12_scaled_int_at_lower_exponent fmt ra hea
  obtain ⟨mb, hmb⟩ := p12_scaled_int_at_lower_exponent fmt rb heb
  refine ⟨ma - mb, ?_⟩
  rw [hma, hmb]
  push_cast
  ring

private lemma p12_beta_le_pow_precision (fmt : P12RadixFormat) :
    fmt.beta ≤ fmt.beta ^ fmt.precision := by
  obtain ⟨p, hp⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt fmt.precision_pos)
  rw [hp, pow_succ]
  exact Nat.le_mul_of_pos_left _ (pow_pos (lt_of_lt_of_le (by omega) fmt.beta_ge_two) _)

private lemma p12_half_le_bound (fmt : P12RadixFormat) :
    fmt.beta / 2 ≤ fmt.beta ^ fmt.precision :=
  le_trans (Nat.div_le_self _ _) (p12_beta_le_pow_precision fmt)

private lemma p12_half_lt_beta (fmt : P12RadixFormat) :
    fmt.beta / 2 < fmt.beta := by
  have := fmt.beta_ge_two
  omega

private lemma p12_condition7_lt_mantissaBound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  have hhalfpos : 0 < fmt.beta / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by
    simpa [Nat.mul_comm] using fmt.beta_ge_two)
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.mantissaBound
    P12RadixFormat.betaR
  norm_cast
  exact Nat.sub_lt (pow_pos (by omega) _) hhalfpos

private lemma p12_condition7_add_half (fmt : P12RadixFormat) :
    fmt.condition7Ceiling + fmt.halfRadixFloor = fmt.mantissaBound := by
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.halfRadixFloor
    P12RadixFormat.mantissaBound P12RadixFormat.betaR
  norm_cast
  exact Nat.sub_add_cancel (p12_half_le_bound fmt)

private lemma p12_twice_pred_lt_beta_mul_sub_half (fmt : P12RadixFormat) :
    2 * ((fmt.beta ^ fmt.precision : ℕ) : ℝ) - 2 <
      (fmt.beta : ℝ) * (fmt.beta ^ fmt.precision : ℕ) -
        (fmt.beta / 2 : ℕ) := by
  let B : ℝ := (fmt.beta ^ fmt.precision : ℕ)
  let b : ℝ := fmt.beta
  let q : ℝ := (fmt.beta / 2 : ℕ)
  have hb : 2 ≤ b := by dsimp [b]; exact_mod_cast fmt.beta_ge_two
  have hB : b ≤ B := by dsimp [b, B]; exact_mod_cast p12_beta_le_pow_precision fmt
  have hq : 2 * q ≤ b := by
    dsimp [q, b]
    exact_mod_cast (Nat.mul_div_le fmt.beta 2)
  have hprod : 0 ≤ (b - 2) * (B - b) := mul_nonneg (by linarith) (by linarith)
  have hsq : 0 ≤ (b - 2) ^ 2 := sq_nonneg (b - 2)
  change 2 * B - 2 < b * B - q
  nlinarith

private lemma p12_nearest_multiple_coeff
    (fmt : P12RadixFormat) (m : ℤ)
    (hm : |m| ≤ 2 * (fmt.beta ^ fmt.precision : ℕ) - 2) :
    ∃ k r : ℤ,
      m = (fmt.beta : ℤ) * k + r ∧
      |r| ≤ (fmt.beta / 2 : ℕ) ∧
      |k| < (fmt.beta ^ fmt.precision : ℕ) := by
  let b : ℤ := fmt.beta
  let q : ℤ := (fmt.beta / 2 : ℕ)
  let k : ℤ := (m + q) / b
  let r : ℤ := (m + q) % b - q
  have hbpos : 0 < b := by
    dsimp [b]
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) fmt.beta_ge_two)
  have hrem0 : 0 ≤ (m + q) % b := Int.emod_nonneg _ (ne_of_gt hbpos)
  have hremlt : (m + q) % b < b := Int.emod_lt_of_pos _ hbpos
  have htwoq_nat : 2 * (fmt.beta / 2) ≤ fmt.beta := Nat.mul_div_le _ _
  have hbq_nat : fmt.beta ≤ 2 * (fmt.beta / 2) + 1 := by omega
  have htwoq : 2 * q ≤ b := by dsimp [q, b]; exact_mod_cast htwoq_nat
  have hbq : b ≤ 2 * q + 1 := by dsimp [q, b]; exact_mod_cast hbq_nat
  have hrlo : -q ≤ r := by dsimp [r]; omega
  have hrhi : r ≤ q := by dsimp [r]; omega
  have hdecomp : m = b * k + r := by
    have hd := Int.emod_add_mul_ediv (m + q) b
    dsimp [k, r]
    omega
  have hgapR := p12_twice_pred_lt_beta_mul_sub_half fmt
  have hgap :
      2 * (fmt.beta ^ fmt.precision : ℕ) - 2 <
        (fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) -
          (fmt.beta / 2 : ℕ) := by
    exact_mod_cast hgapR
  have hmlow : -(2 * (fmt.beta ^ fmt.precision : ℕ) - 2) ≤ m :=
    (abs_le.mp hm).1
  have hmhigh : m ≤ 2 * (fmt.beta ^ fmt.precision : ℕ) - 2 :=
    (abs_le.mp hm).2
  have hkhi : k < (fmt.beta ^ fmt.precision : ℕ) := by
    by_contra hnot
    have hkge : (fmt.beta ^ fmt.precision : ℕ) ≤ k := le_of_not_gt hnot
    have hmul :
        (fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) ≤ b * k := by
      have hb0 : 0 ≤ b := le_of_lt hbpos
      dsimp [b]
      nlinarith
    have hmge :
        (fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) -
            (fmt.beta / 2 : ℕ) ≤ m := by
      calc
        (fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) -
              (fmt.beta / 2 : ℕ) ≤ b * k - (fmt.beta / 2 : ℕ) :=
          sub_le_sub_right hmul _
        _ ≤ b * k + r := by dsimp [q] at hrlo; omega
        _ = m := hdecomp.symm
    exact (not_lt_of_ge hmhigh) (lt_of_lt_of_le hgap hmge)
  have hklo : -(fmt.beta ^ fmt.precision : ℕ) < k := by
    by_contra hnot
    have hkle : k ≤ -(fmt.beta ^ fmt.precision : ℕ) := le_of_not_gt hnot
    have hmul :
        b * k ≤ -(fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) := by
      have hb0 : 0 ≤ b := le_of_lt hbpos
      dsimp [b]
      nlinarith
    have hmle :
        m ≤ -(fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) +
            (fmt.beta / 2 : ℕ) := by
      calc
        m = b * k + r := hdecomp
        _ ≤ b * k + (fmt.beta / 2 : ℕ) := by dsimp [q] at hrhi; omega
        _ ≤ -(fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) +
              (fmt.beta / 2 : ℕ) := by nlinarith [hmul]
    have hneg :
        -(fmt.beta : ℤ) * (fmt.beta ^ fmt.precision : ℕ) +
            (fmt.beta / 2 : ℕ) <
          -(2 * (fmt.beta ^ fmt.precision : ℕ) - 2) := by
      ring_nf at hgap ⊢
      linarith
    exact (not_lt_of_ge hmlow) (lt_of_le_of_lt hmle hneg)
  refine ⟨k, r, ?_, (abs_le.mpr ⟨hrlo, hrhi⟩), (abs_lt.mpr ⟨hklo, hkhi⟩)⟩
  simpa [b] using hdecomp

private lemma p12_close_representable_at_next
    (fmt : P12RadixFormat) (z : ℝ) (m : ℤ) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hz : z = (m : ℝ) * fmt.scale e)
    (hm : |m| ≤ 2 * (fmt.beta ^ fmt.precision : ℕ) - 2) :
    ∃ f : ℝ, p12Representable fmt f ∧
      |z - f| ≤ fmt.halfRadixFloor * fmt.scale e := by
  obtain ⟨k, r, hdecomp, hr, hk⟩ := p12_nearest_multiple_coeff fmt m hm
  let f : ℝ := (k : ℝ) * fmt.scale (e + 1)
  have hkR : |(k : ℝ)| < fmt.mantissaBound := by
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
    rw [← Int.cast_abs]
    exact_mod_cast hk
  have hf : p12Representable fmt f :=
    p12_representable_of_scaled_int fmt f k (e + 1) hkR (by omega) (by omega) rfl
  refine ⟨f, hf, ?_⟩
  have herr : z - f = (r : ℝ) * fmt.scale e := by
    rw [hz]
    dsimp [f]
    rw [p12_scale_succ]
    unfold P12RadixFormat.betaR
    push_cast
    have hdR : (m : ℝ) = (fmt.beta : ℝ) * (k : ℝ) + (r : ℝ) := by
      exact_mod_cast hdecomp
    rw [hdR]
    ring
  rw [herr, abs_mul, abs_of_pos (p12_scale_pos fmt e)]
  have hrR : |(r : ℝ)| ≤ fmt.halfRadixFloor := by
    unfold P12RadixFormat.halfRadixFloor
    let qN : ℕ := fmt.beta / 2
    change |(r : ℝ)| ≤ (qN : ℝ)
    apply abs_le.mpr
    constructor
    · have hlo :
          ((-(qN : ℤ) : ℤ) : ℝ) ≤ (r : ℝ) := by
          apply (Int.cast_le).mpr
          simpa [qN] using (abs_le.mp hr).1
      calc
        -(qN : ℝ) = ((-(qN : ℤ) : ℤ) : ℝ) := by norm_num
        _ ≤ (r : ℝ) := hlo
    · have hhi :
          (r : ℝ) ≤ ((qN : ℤ) : ℝ) := by
          apply (Int.cast_le).mpr
          simpa [qN] using (abs_le.mp hr).2
      calc
        (r : ℝ) ≤ ((qN : ℤ) : ℝ) := hhi
        _ = (qN : ℝ) := by norm_num
  exact mul_le_mul_of_nonneg_right hrR (le_of_lt (p12_scale_pos fmt e))

private lemma p12_choose_y_not_above_x
    (fmt : P12RadixFormat) {x y : ℝ}
    (rx : P12Representation fmt x) (hy : p12Representable fmt y)
    (hcondition : |y| ≤ fmt.condition7Ceiling * fmt.scale rx.exponent) :
    ∃ ry : P12Representation fmt y, ry.exponent ≤ rx.exponent := by
  let ry₀ := Classical.choice hy
  by_cases h : ry₀.exponent ≤ rx.exponent
  · exact ⟨ry₀, h⟩
  · have hex : rx.exponent ≤ ry₀.exponent := le_of_lt (lt_of_not_ge h)
    obtain ⟨m, hm⟩ := p12_scaled_int_at_lower_exponent fmt ry₀ hex
    have hstrict : |y| < fmt.mantissaBound * fmt.scale rx.exponent := by
      have hs := p12_scale_pos fmt rx.exponent
      have hc := p12_condition7_lt_mantissaBound fmt
      nlinarith
    have hmabs : |(m : ℝ)| < fmt.mantissaBound := by
      have hs := p12_scale_pos fmt rx.exponent
      have habs : |(m : ℝ)| * fmt.scale rx.exponent = |y| := by
        rw [hm, abs_mul, abs_of_pos hs]
      nlinarith
    let ry : P12Representation fmt y :=
      ⟨m, rx.exponent, (abs_lt.mp hmabs).1, (abs_lt.mp hmabs).2,
        rx.exponent_lower, rx.exponent_upper, hm⟩
    exact ⟨ry, le_rfl⟩

private lemma p12_mantissa_int_bounds
    (fmt : P12RadixFormat) {z : ℝ} (r : P12Representation fmt z) :
    -(fmt.beta ^ fmt.precision : ℕ) < r.mantissa ∧
      r.mantissa < (fmt.beta ^ fmt.precision : ℕ) := by
  constructor
  · have h := r.mantissa_lower
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at h
    exact_mod_cast h
  · have h := r.mantissa_upper
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at h
    exact_mod_cast h

private lemma p12_nearest_eq_of_representable
    (fmt : P12RadixFormat) (exact rounded : ℝ)
    (hnearest : p12NearestInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) :
    rounded = exact := by
  have h := hnearest.2 exact hexact
  have : |exact - rounded| = 0 := le_antisymm (by simpa using h) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp this) |>.symm

private lemma p12_boundary_representable
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax) (negative : Bool) :
    p12Representable fmt
      (if negative then -(fmt.mantissaBound * fmt.scale e)
       else fmt.mantissaBound * fmt.scale e) := by
  let m : ℤ := if negative then -(fmt.beta ^ fmt.precision : ℕ)
    else (fmt.beta ^ fmt.precision : ℕ)
  have hz :
      (if negative then -(fmt.mantissaBound * fmt.scale e)
       else fmt.mantissaBound * fmt.scale e) = (m : ℝ) * fmt.scale e := by
    cases negative <;>
      simp [m, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
  apply p12_representable_of_lattice_and_closed_bound_with_room fmt _ m e
    hemin hemax hz
  have hB : 0 ≤ fmt.mantissaBound := by
    unfold P12RadixFormat.mantissaBound
    exact pow_nonneg (le_of_lt (p12_betaR_pos fmt)) _
  cases negative <;>
    simp [abs_mul, abs_of_pos (p12_scale_pos fmt e), abs_of_nonneg hB]

private lemma p12_zero_representable (fmt : P12RadixFormat) :
    p12Representable fmt 0 := by
  apply p12_representable_of_scaled_int fmt 0 0 fmt.emin
  · unfold P12RadixFormat.mantissaBound
    simpa using pow_pos (p12_betaR_pos fmt) fmt.precision
  · exact le_rfl
  · exact fmt.emin_le_emax
  · ring

private lemma p12_sub_and_error_representable_of_exponent_lt
    (fmt : P12RadixFormat) (x y s : ℝ)
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (rs : P12Representation fmt s)
    (hnearest : p12NearestInFormat fmt (x + y) s)
    (heyx : ry.exponent < rx.exponent) :
    p12Representable fmt (s - x) ∧ p12Representable fmt (x + y - s) := by
  let B : ℝ := fmt.mantissaBound
  let S : ℝ := fmt.scale ry.exponent
  have hBpos : 0 < B := by
    dsimp [B]
    unfold P12RadixFormat.mantissaBound
    exact pow_pos (p12_betaR_pos fmt) _
  have hSpos : 0 < S := by exact p12_scale_pos fmt _
  have hye : ry.exponent ≤ rx.exponent := le_of_lt heyx
  obtain ⟨m, hm⟩ := p12_lattice_add fmt rx ry hye le_rfl
  by_cases hsmall : |x + y| ≤ B * S
  · have hsumrep : p12Representable fmt (x + y) :=
      p12_representable_of_lattice_and_closed_bound_with_room fmt (x + y) m
        ry.exponent ry.exponent_lower (lt_of_lt_of_le heyx rx.exponent_upper)
        (by simpa [S] using hm) (by simpa [B, S] using hsmall)
    have hs : s = x + y := p12_nearest_eq_of_representable fmt _ _ hnearest hsumrep
    constructor
    · have : s - x = y := by rw [hs]; ring
      rw [this]
      exact ⟨ry⟩
    · have : x + y - s = 0 := by rw [hs]; ring
      rw [this]
      exact p12_zero_representable fmt
  · have hlarge : B * S < |x + y| := lt_of_not_ge hsmall
    have hroom : ry.exponent < fmt.emax :=
      lt_of_lt_of_le heyx rx.exponent_upper
    have hsabs : B * S ≤ |s| := by
      by_cases hz : 0 ≤ x + y
      · have hzbig : B * S < x + y := by
          simpa [abs_of_nonneg hz] using hlarge
        have hboundary := p12_boundary_representable fmt ry.exponent
          ry.exponent_lower hroom false
        have hn := hnearest.2 (B * S) (by simpa [B, S] using hboundary)
        have hdist : |(x + y) - B * S| = (x + y) - B * S := by
          rw [abs_of_nonneg (le_of_lt (sub_pos.mpr hzbig))]
        rw [hdist] at hn
        have hu := (abs_le.mp hn).2
        have hslo : B * S ≤ s := by linarith
        exact le_trans hslo (le_abs_self s)
      · have hzneg : x + y < 0 := lt_of_not_ge hz
        have hzbig : x + y < -(B * S) := by
          rw [abs_of_neg hzneg] at hlarge
          linarith
        have hboundary := p12_boundary_representable fmt ry.exponent
          ry.exponent_lower hroom true
        have hn := hnearest.2 (-(B * S)) (by simpa [B, S] using hboundary)
        have hdist : |(x + y) - (-(B * S))| = -((x + y) + B * S) := by
          rw [show (x + y) - (-(B * S)) = (x + y) + B * S by ring,
            abs_of_neg (by linarith)]
        rw [hdist] at hn
        have hl := (abs_le.mp hn).1
        have hshi : s ≤ -(B * S) := by linarith
        have : B * S ≤ -s := by linarith
        exact le_trans this (le_abs_self (-s) |>.trans_eq (abs_neg s))
    have hrsy : ry.exponent < rs.exponent := by
      by_contra hnot
      have hrsle : rs.exponent ≤ ry.exponent := le_of_not_gt hnot
      have hslt := p12_rep_abs_lt fmt rs
      have hscale := p12_scale_mono fmt hrsle
      have : |s| < B * S := by
        dsimp [B, S] at ⊢
        exact lt_of_lt_of_le hslt (mul_le_mul_of_nonneg_left hscale (le_of_lt hBpos))
      linarith
    let e₀ : ℤ := min rs.exponent rx.exponent
    have he0y : ry.exponent < e₀ := by
      dsimp [e₀]
      omega
    have he0min : fmt.emin ≤ e₀ := by
      dsimp [e₀]
      exact le_min rs.exponent_lower rx.exponent_lower
    have he0max : e₀ ≤ fmt.emax := by
      dsimp [e₀]
      exact (min_le_right _ _).trans rx.exponent_upper
    obtain ⟨md, hmd⟩ := p12_lattice_sub fmt rs rx (min_le_left _ _) (min_le_right _ _)
    have hylt : |y| < B * S := by
      simpa [B, S] using p12_rep_abs_lt fmt ry
    have herr : |s - (x + y)| ≤ |y| := by
      have hn := hnearest.2 x ⟨rx⟩
      simpa [abs_sub_comm, add_sub_cancel_left] using hn
    have hdtri : |s - x| ≤ |s - (x + y)| + |y| := by
      calc
        |s - x| = |(s - (x + y)) + y| := by ring_nf
        _ ≤ |s - (x + y)| + |y| := abs_add_le _ _
    have hscaleStep : fmt.betaR * S ≤ fmt.scale e₀ := by
      rw [← p12_scale_succ]
      exact p12_scale_mono fmt (by omega : ry.exponent + 1 ≤ e₀)
    have hbetaR : (2 : ℝ) ≤ fmt.betaR := by
      unfold P12RadixFormat.betaR
      exact_mod_cast fmt.beta_ge_two
    have htwoScale : 2 * S ≤ fmt.scale e₀ := by
      calc
        2 * S ≤ fmt.betaR * S :=
          mul_le_mul_of_nonneg_right hbetaR (le_of_lt hSpos)
        _ ≤ fmt.scale e₀ := hscaleStep
    have hdlt : |s - x| < B * fmt.scale e₀ := by
      have hsumlt : |s - (x + y)| + |y| < 2 * (B * S) := by linarith
      have hBS : 2 * (B * S) ≤ B * fmt.scale e₀ := by
        nlinarith
      exact lt_of_le_of_lt hdtri (lt_of_lt_of_le hsumlt hBS)
    have hdrep : p12Representable fmt (s - x) :=
      p12_representable_of_lattice_and_bound fmt (s - x) md e₀ he0min he0max
        (by simpa [e₀] using hmd) hdlt
    have hrslower : ry.exponent ≤ rs.exponent := le_of_lt hrsy
    obtain ⟨ms, hms⟩ := p12_scaled_int_at_lower_exponent fmt rs hrslower
    have herrLat : x + y - s = ((m - ms : ℤ) : ℝ) * fmt.scale ry.exponent := by
      rw [hm, hms]
      push_cast
      ring
    have herrlt : |x + y - s| < B * S := by
      rw [abs_sub_comm]
      exact lt_of_le_of_lt herr hylt
    have herrep : p12Representable fmt (x + y - s) :=
      p12_representable_of_lattice_and_bound fmt _ (m - ms) ry.exponent
        ry.exponent_lower ry.exponent_upper herrLat (by simpa [B, S] using herrlt)
    exact ⟨hdrep, herrep⟩

private lemma p12_beta_mul_bound_pred_ge_bound (fmt : P12RadixFormat) :
    fmt.mantissaBound ≤ fmt.betaR * (fmt.mantissaBound - 1) := by
  have hB2 : 2 ≤ fmt.beta ^ fmt.precision :=
    le_trans fmt.beta_ge_two (p12_beta_le_pow_precision fmt)
  have hnat :
      fmt.beta ^ fmt.precision ≤
        fmt.beta * (fmt.beta ^ fmt.precision - 1) := by
    calc
      fmt.beta ^ fmt.precision ≤ 2 * (fmt.beta ^ fmt.precision - 1) := by omega
      _ ≤ fmt.beta * (fmt.beta ^ fmt.precision - 1) := by
        exact Nat.mul_le_mul_right _ fmt.beta_ge_two
  unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
  have hBone : 1 ≤ fmt.beta ^ fmt.precision := by omega
  have hnatR :
      ((fmt.beta ^ fmt.precision : ℕ) : ℝ) ≤
        ((fmt.beta * (fmt.beta ^ fmt.precision - 1) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hnatR
  simpa [Nat.cast_sub hBone] using hnatR

private lemma p12_sub_and_error_representable_of_same_exponent
    (fmt : P12RadixFormat) (x y s : ℝ)
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (rs : P12Representation fmt s)
    (hnearest : p12NearestInFormat fmt (x + y) s)
    (heq : ry.exponent = rx.exponent)
    (hycond : |y| ≤
      fmt.condition7Ceiling * fmt.scale rx.exponent) :
    p12Representable fmt (s - x) ∧ p12Representable fmt (x + y - s) := by
  let e : ℤ := rx.exponent
  let S : ℝ := fmt.scale e
  let Bn : ℕ := fmt.beta ^ fmt.precision
  let n : ℤ := rx.mantissa + ry.mantissa
  have hSpos : 0 < S := by exact p12_scale_pos fmt _
  have hBpos : 0 < fmt.mantissaBound := by
    unfold P12RadixFormat.mantissaBound
    exact pow_pos (p12_betaR_pos fmt) _
  have hsum : x + y = (n : ℝ) * S := by
    rw [rx.value_eq, ry.value_eq]
    dsimp [e, S, n]
    rw [heq]
    push_cast
    ring
  have hmx := p12_mantissa_int_bounds fmt rx
  have hmy := p12_mantissa_int_bounds fmt ry
  have hnabs : |n| ≤ 2 * (Bn : ℤ) - 2 := by
    have hmx' : -(Bn : ℤ) < rx.mantissa ∧ rx.mantissa < (Bn : ℤ) := by
      simpa [Bn] using hmx
    have hmy' : -(Bn : ℤ) < ry.mantissa ∧ ry.mantissa < (Bn : ℤ) := by
      simpa [Bn] using hmy
    dsimp [n]
    rw [abs_le]
    constructor <;> omega
  by_cases hnsmall : |n| < (Bn : ℤ)
  · have hnR : |(n : ℝ)| < fmt.mantissaBound := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      rw [← Int.cast_abs]
      exact_mod_cast hnsmall
    have hsumrep : p12Representable fmt (x + y) :=
      p12_representable_of_scaled_int fmt _ n e hnR rx.exponent_lower
        rx.exponent_upper (by simpa [e, S] using hsum)
    have hs : s = x + y := p12_nearest_eq_of_representable fmt _ _ hnearest hsumrep
    constructor
    · have hval : s - x = y := by rw [hs]; ring
      rw [hval]
      exact ⟨ry⟩
    · rw [hs]
      convert p12_zero_representable fmt using 1 <;> ring
  · have hnlarge : (Bn : ℤ) ≤ |n| := le_of_not_gt hnsmall
    rcases lt_or_eq_of_le rx.exponent_upper with hemaxlt | hemaxeq
    · have hemaxlt' : e < fmt.emax := by simpa [e] using hemaxlt
      obtain ⟨f, hf, hfclose⟩ := p12_close_representable_at_next fmt
        (x + y) n e rx.exponent_lower hemaxlt'
        (by simpa [e, S] using hsum) (by simpa [Bn] using hnabs)
      have herr : |s - (x + y)| ≤ fmt.halfRadixFloor * S := by
        have hnf := hnearest.2 f hf
        rw [abs_sub_comm] at hnf
        exact hnf.trans (by simpa [S] using hfclose)
      have hsumabs : fmt.mantissaBound * S ≤ |x + y| := by
        have hnR : fmt.mantissaBound ≤ |(n : ℝ)| := by
          unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
          rw [← Int.cast_abs]
          exact_mod_cast hnlarge
        rw [hsum, abs_mul, abs_of_pos hSpos]
        exact mul_le_mul_of_nonneg_right hnR (le_of_lt hSpos)
      have hsabs : fmt.mantissaBound * S ≤ |s| := by
        by_cases hz : 0 ≤ x + y
        · have hzB : fmt.mantissaBound * S ≤ x + y := by
            simpa [abs_of_nonneg hz] using hsumabs
          have hb := p12_boundary_representable fmt e rx.exponent_lower hemaxlt' false
          have hn' := hnearest.2 (fmt.mantissaBound * S) (by simpa [e, S] using hb)
          have hd : |(x + y) - fmt.mantissaBound * S| =
              (x + y) - fmt.mantissaBound * S := by
            rw [abs_of_nonneg (sub_nonneg.mpr hzB)]
          rw [hd] at hn'
          have := (abs_le.mp hn').2
          have : fmt.mantissaBound * S ≤ s := by linarith
          exact this.trans (le_abs_self s)
        · have hzneg : x + y < 0 := lt_of_not_ge hz
          have hzB : x + y ≤ -(fmt.mantissaBound * S) := by
            rw [abs_of_neg hzneg] at hsumabs
            linarith
          have hb := p12_boundary_representable fmt e rx.exponent_lower hemaxlt' true
          have hn' := hnearest.2 (-(fmt.mantissaBound * S)) (by simpa [e, S] using hb)
          have hd : |(x + y) - (-(fmt.mantissaBound * S))| =
              -((x + y) + fmt.mantissaBound * S) := by
            rw [show (x + y) - (-(fmt.mantissaBound * S)) =
                (x + y) + fmt.mantissaBound * S by ring,
              abs_of_nonpos (by linarith)]
          rw [hd] at hn'
          have := (abs_le.mp hn').1
          have hsle : s ≤ -(fmt.mantissaBound * S) := by linarith
          have : fmt.mantissaBound * S ≤ -s := by linarith
          simpa using this.trans (le_abs_self (-s))
      have hrse : e < rs.exponent := by
        by_contra hnot
        have hrsle : rs.exponent ≤ e := le_of_not_gt hnot
        have hslt := p12_rep_abs_lt fmt rs
        have hscale := p12_scale_mono fmt hrsle
        have : |s| < fmt.mantissaBound * S := by
          dsimp [S]
          exact hslt.trans_le
            (mul_le_mul_of_nonneg_left hscale (le_of_lt hBpos))
        linarith
      obtain ⟨md, hmd⟩ := p12_lattice_sub fmt rs rx (le_of_lt hrse) le_rfl
      have hdtri : |s - x| ≤ |s - (x + y)| + |y| := by
        calc
          |s - x| = |(s - (x + y)) + y| := by ring_nf
          _ ≤ |s - (x + y)| + |y| := abs_add_le _ _
      have hdclosed : |s - x| ≤ fmt.mantissaBound * S := by
        have hident := p12_condition7_add_half fmt
        have hs0 : 0 ≤ S := le_of_lt hSpos
        calc
          |s - x| ≤ |s - (x + y)| + |y| := hdtri
          _ ≤ fmt.halfRadixFloor * S + fmt.condition7Ceiling * S :=
            add_le_add herr (by simpa [S] using hycond)
          _ = fmt.mantissaBound * S := by
            rw [← add_mul, add_comm, hident]
      have hdrep : p12Representable fmt (s - x) :=
        p12_representable_of_lattice_and_closed_bound_with_room fmt _ md e
          rx.exponent_lower hemaxlt' (by simpa [e, S] using hmd)
          (by simpa [S] using hdclosed)
      obtain ⟨ms, hms⟩ := p12_scaled_int_at_lower_exponent fmt rs (le_of_lt hrse)
      have herrorLat : x + y - s = ((n - ms : ℤ) : ℝ) * S := by
        rw [hsum, hms]
        dsimp [S, e] at ⊢
        push_cast
        ring
      have hhalf_lt : fmt.halfRadixFloor < fmt.mantissaBound := by
        unfold P12RadixFormat.halfRadixFloor P12RadixFormat.mantissaBound
          P12RadixFormat.betaR
        norm_cast
        exact (p12_half_lt_beta fmt).trans_le
          (p12_beta_le_pow_precision fmt)
      have herrlt : |x + y - s| < fmt.mantissaBound * S := by
        rw [abs_sub_comm]
        exact herr.trans_lt (mul_lt_mul_of_pos_right hhalf_lt hSpos)
      have herrep := p12_representable_of_lattice_and_bound fmt _ (n - ms) e
        rx.exponent_lower rx.exponent_upper (by simpa [S] using herrorLat)
        (by simpa [S] using herrlt)
      exact ⟨hdrep, herrep⟩
    · have hemax : e = fmt.emax := by simpa [e] using hemaxeq
      -- At the largest exponent, nearest rounding saturates at the signed endpoint.
      have hBn2 : 2 ≤ Bn := by
        dsimp [Bn]
        exact le_trans fmt.beta_ge_two (p12_beta_le_pow_precision fmt)
      have hendpointAbs :
          |((Bn : ℝ) - 1) * S| = (fmt.mantissaBound - 1) * S := by
        have hcastB : (Bn : ℝ) = fmt.mantissaBound := by
          simp [Bn, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
        rw [abs_mul, abs_of_pos hSpos, abs_of_nonneg (by
          rw [hcastB]
          have hBnR : (1 : ℝ) < (Bn : ℝ) := by exact_mod_cast hBn2
          have : (1 : ℝ) < fmt.mantissaBound := by simpa [hcastB] using hBnR
          linarith), hcastB]
      rcases le_total 0 n with hnpos | hnneg
      · have hnB : (Bn : ℤ) ≤ n := by
          rw [abs_of_nonneg hnpos] at hnlarge
          exact hnlarge
        let ep : ℝ := ((Bn : ℕ) : ℝ) - 1
        have hepR : p12Representable fmt (ep * S) := by
          have hmR : |((Bn : ℤ) - 1 : ℤ)| < fmt.mantissaBound := by
            have hcastB : (Bn : ℝ) = fmt.mantissaBound := by
              simp [Bn, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
            rw [abs_of_nonneg (by omega)]
            push_cast
            rw [hcastB]
            linarith
          apply p12_representable_of_scaled_int fmt (ep * S) ((Bn : ℤ) - 1) e
            (by simpa only [Int.cast_abs] using hmR) rx.exponent_lower (by simpa [hemax])
          dsimp [ep, S]
          push_cast
          ring
        have hnnear := hnearest.2 (ep * S) hepR
        have hsumLower : ep * S ≤ x + y := by
          rw [hsum]
          have : (ep : ℝ) ≤ (n : ℝ) := by
            dsimp [ep]
            exact_mod_cast (show (Bn : ℤ) - 1 ≤ n by omega)
          exact mul_le_mul_of_nonneg_right this (le_of_lt hSpos)
        have hdist : |(x + y) - ep * S| = (x + y) - ep * S :=
          abs_of_nonneg (sub_nonneg.mpr hsumLower)
        rw [hdist] at hnnear
        have hsLower : ep * S ≤ s := by
          have := (abs_le.mp hnnear).2
          linarith
        have hrseq : rs.exponent = e := by
          have hrsle : rs.exponent ≤ e := by rw [hemax]; exact rs.exponent_upper
          apply le_antisymm hrsle
          by_contra hnot
          have hrslt : rs.exponent < e := lt_of_not_ge hnot
          have hslt := p12_rep_abs_lt fmt rs
          have hstep : fmt.betaR * fmt.scale rs.exponent ≤ S := by
            dsimp [S]
            rw [← p12_scale_succ]
            exact p12_scale_mono fmt (by omega)
          have hmulUpper : fmt.betaR * |s| < fmt.mantissaBound * S := by
            have h1 : fmt.betaR * |s| < fmt.betaR *
                (fmt.mantissaBound * fmt.scale rs.exponent) :=
              mul_lt_mul_of_pos_left hslt (p12_betaR_pos fmt)
            have h2 : fmt.betaR * (fmt.mantissaBound * fmt.scale rs.exponent) ≤
                fmt.mantissaBound * S := by nlinarith
            exact h1.trans_le h2
          have hsabsLower : (fmt.mantissaBound - 1) * S ≤ |s| := by
            have hep : ep = fmt.mantissaBound - 1 := by
              simp [ep, Bn, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
            rw [hep] at hsLower
            exact hsLower.trans (le_abs_self s)
          have hmulLower : fmt.mantissaBound * S ≤ fmt.betaR * |s| := by
            have hbpred := p12_beta_mul_bound_pred_ge_bound fmt
            calc
              fmt.mantissaBound * S ≤
                  (fmt.betaR * (fmt.mantissaBound - 1)) * S :=
                mul_le_mul_of_nonneg_right hbpred (le_of_lt hSpos)
              _ = fmt.betaR * ((fmt.mantissaBound - 1) * S) := by ring
              _ ≤ fmt.betaR * |s| :=
                mul_le_mul_of_nonneg_left hsabsLower (le_of_lt (p12_betaR_pos fmt))
          exact (not_lt_of_ge hmulLower) hmulUpper
        have hsMantLower : (Bn : ℤ) - 1 ≤ rs.mantissa := by
          have hv := rs.value_eq
          rw [hrseq] at hv
          have hcast : (ep : ℝ) = ((Bn : ℤ) - 1 : ℤ) := by
            dsimp [ep]
            norm_cast
          rw [hv] at hsLower
          dsimp [S, e] at hsLower
          have : ((Bn : ℤ) - 1 : ℤ) ≤ rs.mantissa := by
            exact_mod_cast (by nlinarith [p12_scale_pos fmt rx.exponent] :
              (((Bn : ℤ) - 1 : ℤ) : ℝ) ≤ (rs.mantissa : ℝ))
          exact this
        have hrsBounds := p12_mantissa_int_bounds fmt rs
        have hsMant : rs.mantissa = (Bn : ℤ) - 1 := by
          have hrsBounds' : -(Bn : ℤ) < rs.mantissa ∧
              rs.mantissa < (Bn : ℤ) := by simpa [Bn] using hrsBounds
          omega
        have hmxpos : 1 ≤ rx.mantissa := by
          have hmy' : ry.mantissa < (Bn : ℤ) := by simpa [Bn] using hmy.2
          dsimp [n] at hnB
          omega
        have hdcoef : |rs.mantissa - rx.mantissa| < (Bn : ℤ) := by
          have hmx' : rx.mantissa < (Bn : ℤ) := by simpa [Bn] using hmx.2
          rw [hsMant, abs_of_nonneg (by omega)]
          omega
        have hercoef : |n - rs.mantissa| < (Bn : ℤ) := by
          have hmx' : rx.mantissa < (Bn : ℤ) := by simpa [Bn] using hmx.2
          have hmy' : ry.mantissa < (Bn : ℤ) := by simpa [Bn] using hmy.2
          dsimp [n]
          rw [hsMant, abs_of_nonneg (by omega)]
          omega
        constructor
        · have hdlat : s - x = ((rs.mantissa - rx.mantissa : ℤ) : ℝ) * S := by
            calc
              s - x = (rs.mantissa : ℝ) * fmt.scale rs.exponent - x :=
                congrArg (fun q : ℝ => q - x) rs.value_eq
              _ = (rs.mantissa : ℝ) * fmt.scale rs.exponent -
                    (rx.mantissa : ℝ) * fmt.scale rx.exponent :=
                congrArg (fun q : ℝ =>
                  (rs.mantissa : ℝ) * fmt.scale rs.exponent - q) rx.value_eq
              _ = ((rs.mantissa - rx.mantissa : ℤ) : ℝ) * S := by
                rw [hrseq]
                dsimp [S, e]
                push_cast
                ring
          apply p12_representable_of_scaled_int fmt _ (rs.mantissa - rx.mantissa) e
          · unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
            rw [← Int.cast_abs]
            exact_mod_cast hdcoef
          · exact rx.exponent_lower
          · simpa [hemax]
          · simpa [S] using hdlat
        · have hrlat : x + y - s = ((n - rs.mantissa : ℤ) : ℝ) * S := by
            calc
              x + y - s = (n : ℝ) * S - s := congrArg (fun q : ℝ => q - s) hsum
              _ = (n : ℝ) * S -
                    (rs.mantissa : ℝ) * fmt.scale rs.exponent :=
                congrArg (fun q : ℝ => (n : ℝ) * S - q) rs.value_eq
              _ = ((n - rs.mantissa : ℤ) : ℝ) * S := by
                rw [hrseq]
                dsimp [S, e]
                push_cast
                ring
          apply p12_representable_of_scaled_int fmt _ (n - rs.mantissa) e
          · unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
            rw [← Int.cast_abs]
            exact_mod_cast hercoef
          · exact rx.exponent_lower
          · simpa [hemax]
          · simpa [S] using hrlat
      · have hnB : n ≤ -(Bn : ℤ) := by
          rw [abs_of_nonpos hnneg] at hnlarge
          omega
        let ep : ℝ := -(((Bn : ℕ) : ℝ) - 1)
        have hepR : p12Representable fmt (ep * S) := by
          have hmR : |(-((Bn : ℤ) - 1) : ℤ)| < fmt.mantissaBound := by
            have hcastB : (Bn : ℝ) = fmt.mantissaBound := by
              simp [Bn, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
            rw [abs_neg, abs_of_nonneg (by omega)]
            push_cast
            rw [hcastB]
            have hBnR : (1 : ℝ) < (Bn : ℝ) := by exact_mod_cast hBn2
            have : (1 : ℝ) < fmt.mantissaBound := by simpa [hcastB] using hBnR
            linarith
          apply p12_representable_of_scaled_int fmt (ep * S) (-((Bn : ℤ) - 1)) e
            (by simpa only [Int.cast_abs] using hmR) rx.exponent_lower (by simpa [hemax])
          dsimp [ep, S]
          push_cast
          ring
        have hnnear := hnearest.2 (ep * S) hepR
        have hsumUpper : x + y ≤ ep * S := by
          rw [hsum]
          have : (n : ℝ) ≤ ep := by
            dsimp [ep]
            exact_mod_cast (show n ≤ -((Bn : ℤ) - 1) by omega)
          exact mul_le_mul_of_nonneg_right this (le_of_lt hSpos)
        have hdist : |(x + y) - ep * S| = -(x + y - ep * S) :=
          abs_of_nonpos (sub_nonpos.mpr hsumUpper)
        rw [hdist] at hnnear
        have hsUpper : s ≤ ep * S := by
          have := (abs_le.mp hnnear).1
          linarith
        have hrseq : rs.exponent = e := by
          have hrsle : rs.exponent ≤ e := by rw [hemax]; exact rs.exponent_upper
          apply le_antisymm hrsle
          by_contra hnot
          have hrslt : rs.exponent < e := lt_of_not_ge hnot
          have hslt := p12_rep_abs_lt fmt rs
          have hstep : fmt.betaR * fmt.scale rs.exponent ≤ S := by
            dsimp [S]
            rw [← p12_scale_succ]
            exact p12_scale_mono fmt (by omega)
          have hmulUpper : fmt.betaR * |s| < fmt.mantissaBound * S := by
            have h1 := mul_lt_mul_of_pos_left hslt (p12_betaR_pos fmt)
            have h2 : fmt.betaR * (fmt.mantissaBound * fmt.scale rs.exponent) ≤
                fmt.mantissaBound * S := by nlinarith
            exact h1.trans_le h2
          have hsabsLower : (fmt.mantissaBound - 1) * S ≤ |s| := by
            have hep : ep = -(fmt.mantissaBound - 1) := by
              simp [ep, Bn, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
            rw [hep] at hsUpper
            have : (fmt.mantissaBound - 1) * S ≤ -s := by nlinarith
            simpa using this.trans (le_abs_self (-s))
          have hmulLower : fmt.mantissaBound * S ≤ fmt.betaR * |s| := by
            have hbpred := p12_beta_mul_bound_pred_ge_bound fmt
            calc
              fmt.mantissaBound * S ≤
                  (fmt.betaR * (fmt.mantissaBound - 1)) * S :=
                mul_le_mul_of_nonneg_right hbpred (le_of_lt hSpos)
              _ = fmt.betaR * ((fmt.mantissaBound - 1) * S) := by ring
              _ ≤ fmt.betaR * |s| :=
                mul_le_mul_of_nonneg_left hsabsLower (le_of_lt (p12_betaR_pos fmt))
          exact (not_lt_of_ge hmulLower) hmulUpper
        have hsMantUpper : rs.mantissa ≤ -((Bn : ℤ) - 1) := by
          have hv := rs.value_eq
          rw [hrseq] at hv
          rw [hv] at hsUpper
          dsimp [ep, S, e] at hsUpper
          have : (rs.mantissa : ℝ) ≤ (-((Bn : ℤ) - 1) : ℤ) := by
            push_cast
            nlinarith [p12_scale_pos fmt rx.exponent]
          exact_mod_cast this
        have hrsBounds := p12_mantissa_int_bounds fmt rs
        have hsMant : rs.mantissa = -((Bn : ℤ) - 1) := by
          have hrsBounds' : -(Bn : ℤ) < rs.mantissa ∧
              rs.mantissa < (Bn : ℤ) := by simpa [Bn] using hrsBounds
          omega
        have hmxneg : rx.mantissa ≤ -1 := by
          have hmy' : -(Bn : ℤ) < ry.mantissa := by simpa [Bn] using hmy.1
          dsimp [n] at hnB
          omega
        have hdcoef : |rs.mantissa - rx.mantissa| < (Bn : ℤ) := by
          have hmx' : -(Bn : ℤ) < rx.mantissa := by simpa [Bn] using hmx.1
          rw [hsMant, abs_of_nonpos (by omega)]
          omega
        have hercoef : |n - rs.mantissa| < (Bn : ℤ) := by
          have hmx' : -(Bn : ℤ) < rx.mantissa := by simpa [Bn] using hmx.1
          have hmy' : -(Bn : ℤ) < ry.mantissa := by simpa [Bn] using hmy.1
          dsimp [n]
          rw [hsMant, abs_of_nonpos (by omega)]
          omega
        constructor
        · have hdlat : s - x = ((rs.mantissa - rx.mantissa : ℤ) : ℝ) * S := by
            calc
              s - x = (rs.mantissa : ℝ) * fmt.scale rs.exponent - x :=
                congrArg (fun q : ℝ => q - x) rs.value_eq
              _ = (rs.mantissa : ℝ) * fmt.scale rs.exponent -
                    (rx.mantissa : ℝ) * fmt.scale rx.exponent :=
                congrArg (fun q : ℝ =>
                  (rs.mantissa : ℝ) * fmt.scale rs.exponent - q) rx.value_eq
              _ = ((rs.mantissa - rx.mantissa : ℤ) : ℝ) * S := by
                rw [hrseq]
                dsimp [S, e]
                push_cast
                ring
          apply p12_representable_of_scaled_int fmt _ (rs.mantissa - rx.mantissa) e
          · unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
            rw [← Int.cast_abs]
            exact_mod_cast hdcoef
          · exact rx.exponent_lower
          · simpa [hemax]
          · simpa [S] using hdlat
        · have hrlat : x + y - s = ((n - rs.mantissa : ℤ) : ℝ) * S := by
            calc
              x + y - s = (n : ℝ) * S - s := congrArg (fun q : ℝ => q - s) hsum
              _ = (n : ℝ) * S -
                    (rs.mantissa : ℝ) * fmt.scale rs.exponent :=
                congrArg (fun q : ℝ => (n : ℝ) * S - q) rs.value_eq
              _ = ((n - rs.mantissa : ℤ) : ℝ) * S := by
                rw [hrseq]
                dsimp [S, e]
                push_cast
                ring
          apply p12_representable_of_scaled_int fmt _ (n - rs.mantissa) e
          · unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
            rw [← Int.cast_abs]
            exact_mod_cast hercoef
          · exact rx.exponent_lower
          · simpa [hemax]
          · simpa [S] using hrlat

private lemma p12_faithful_eq_of_representable
    (fmt : P12RadixFormat) (exact rounded : ℝ)
    (hfaithful : p12FaithfulInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) :
    rounded = exact := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfaithful.2 exact hexact (Or.inl ⟨hlt, le_rfl⟩)
  · exact hfaithful.2 exact hexact (Or.inr ⟨le_rfl, hgt⟩)

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
  obtain ⟨rx, hycond⟩ := hcondition7
  obtain ⟨ry, hryx⟩ := p12_choose_y_not_above_x fmt rx hy hycond
  have hsrep : p12Representable fmt tr.s := run.add.1
  let rs : P12Representation fmt tr.s := Classical.choice hsrep
  have hpair :
      p12Representable fmt (tr.s - x) ∧
        p12Representable fmt (x + y - tr.s) := by
    rcases lt_or_eq_of_le hryx with hlt | heq
    · exact p12_sub_and_error_representable_of_exponent_lt
        fmt x y tr.s rx ry rs run.add hlt
    · exact p12_sub_and_error_representable_of_same_exponent
        fmt x y tr.s rx ry rs run.add heq hycond
  have ht : tr.t = tr.s - x :=
    p12_faithful_eq_of_representable fmt _ _ run.first_sub hpair.1
  have hytrep : p12Representable fmt (y - tr.t) := by
    have hval : y - tr.t = x + y - tr.s := by rw [ht]; ring
    rw [hval]
    exact hpair.2
  have he : tr.e = y - tr.t :=
    p12_faithful_eq_of_representable fmt _ _ run.second_sub hytrep
  have hsum : tr.s + tr.e = x + y := by
    rw [he, ht]
    ring
  have herr : |tr.s - (x + y)| ≤ |y| := by
    have hn := run.add.2 x hx
    simpa [abs_sub_comm, add_sub_cancel_left] using hn
  exact ⟨ht, he, hsum, herr⟩

end HighamBench
