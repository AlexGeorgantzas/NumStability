import HighamBench.P12Definitions

set_option maxHeartbeats 1000000

namespace HighamBench

private lemma p12_beta_pos (fmt : P12RadixFormat) : (0 : ℝ) < fmt.beta := by
  exact_mod_cast (lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) fmt.beta_ge_two)

private lemma p12_scale_pos (fmt : P12RadixFormat) (e : ℤ) :
    0 < fmt.scale e := by
  exact zpow_pos (p12_beta_pos fmt) e

private lemma p12_bound_pos (fmt : P12RadixFormat) :
    0 < fmt.mantissaBound := by
  unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
  exact pow_pos (p12_beta_pos fmt) _

private lemma p12_rep_value_at_lower
    {fmt : P12RadixFormat} {v : ℝ} (r : P12Representation fmt v)
    {e : ℤ} (he : e ≤ r.exponent) :
    ∃ m : ℤ, v = (m : ℝ) * fmt.scale e := by
  let n : ℕ := (r.exponent - e).toNat
  refine ⟨r.mantissa * (fmt.beta : ℤ) ^ n, ?_⟩
  have hexp : r.exponent = e + (n : ℤ) := by
    dsimp [n]
    omega
  calc
    v = (r.mantissa : ℝ) * fmt.scale r.exponent := r.value_eq
    _ = (r.mantissa : ℝ) * fmt.scale (e + (n : ℤ)) := by rw [hexp]
    _ = ((r.mantissa * (fmt.beta : ℤ) ^ n : ℤ) : ℝ) * fmt.scale e := by
      unfold P12RadixFormat.scale P12RadixFormat.betaR
      rw [zpow_add₀ (ne_of_gt (p12_beta_pos fmt))]
      simp only [zpow_natCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      ring

private lemma p12_representable_of_int_scale
    {fmt : P12RadixFormat} {v : ℝ} {m : ℤ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (hv : v = (m : ℝ) * fmt.scale e)
    (hm : |(m : ℝ)| < fmt.mantissaBound) :
    p12Representable fmt v := by
  refine ⟨⟨m, e, ?_, ?_, hemin, hemax, hv⟩⟩
  · exact (abs_lt.mp hm).1
  · exact (abs_lt.mp hm).2

private lemma p12_scale_mono (fmt : P12RadixFormat) {e₁ e₂ : ℤ}
    (h : e₁ ≤ e₂) : fmt.scale e₁ ≤ fmt.scale e₂ := by
  unfold P12RadixFormat.scale P12RadixFormat.betaR
  have hbN : 1 ≤ fmt.beta := le_trans (by decide) fmt.beta_ge_two
  have hb : (1 : ℝ) ≤ fmt.beta := by exact_mod_cast hbN
  exact zpow_le_zpow_right₀ hb h

private lemma p12_representable_of_int_scale_le
    {fmt : P12RadixFormat} {v : ℝ} {m : ℤ} {e : ℤ}
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (hv : v = (m : ℝ) * fmt.scale e)
    (hm : |(m : ℝ)| ≤ fmt.mantissaBound) :
    p12Representable fmt v := by
  rcases lt_or_eq_of_le hm with hmlt | hmeq
  · exact p12_representable_of_int_scale hemin (by omega) hv hmlt
  · have hp := fmt.precision_pos
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : fmt.precision ≠ 0)
    have hbg := fmt.beta_ge_two
    have hb : 0 < fmt.beta := by omega
    have hpowlt : fmt.beta ^ k < fmt.beta ^ fmt.precision := by
      rw [hk, pow_succ]
      have hpk : 0 < fmt.beta ^ k := pow_pos hb k
      calc
        fmt.beta ^ k = fmt.beta ^ k * 1 := by simp
        _ < fmt.beta ^ k * fmt.beta := Nat.mul_lt_mul_of_pos_left (by omega) hpk
    have hsmall : ((fmt.beta ^ k : ℕ) : ℝ) < fmt.mantissaBound := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      exact_mod_cast hpowlt
    have hscale : fmt.scale (e + 1) = fmt.scale e * (fmt.beta : ℝ) := by
      unfold P12RadixFormat.scale P12RadixFormat.betaR
      rw [zpow_add_one₀ (ne_of_gt (p12_beta_pos fmt))]
    by_cases hnonneg : 0 ≤ m
    · have hmcast : (m : ℝ) = (fmt.beta ^ fmt.precision : ℕ) := by
        have hmnonneg : (0 : ℝ) ≤ m := by exact_mod_cast hnonneg
        rw [abs_of_nonneg hmnonneg] at hmeq
        simpa [P12RadixFormat.mantissaBound, P12RadixFormat.betaR] using hmeq
      have hmint : m = (fmt.beta ^ fmt.precision : ℕ) := by exact_mod_cast hmcast
      refine p12_representable_of_int_scale (e := e + 1) (m := (fmt.beta ^ k : ℕ))
        (by omega) (by omega) ?_ ?_
      · rw [hv, hmint, hk, hscale, pow_succ]
        push_cast
        ring
      · simpa [abs_of_nonneg (show (0 : ℝ) ≤ (fmt.beta ^ k : ℕ) by positivity)]
          using hsmall
    · have hmneg : (m : ℝ) < 0 := by exact_mod_cast (show m < 0 by omega)
      have hmcast : -(m : ℝ) = (fmt.beta ^ fmt.precision : ℕ) := by
        rw [abs_of_neg hmneg] at hmeq
        simpa [P12RadixFormat.mantissaBound, P12RadixFormat.betaR] using hmeq
      have hmint : m = -((fmt.beta ^ fmt.precision : ℕ) : ℤ) := by
        have hh : -m = ((fmt.beta ^ fmt.precision : ℕ) : ℤ) := by
          exact_mod_cast hmcast
        omega
      refine p12_representable_of_int_scale (e := e + 1)
        (m := -((fmt.beta ^ k : ℕ) : ℤ)) (by omega) (by omega) ?_ ?_
      · rw [hv, hmint, hk, hscale, pow_succ]
        push_cast
        ring
      · rw [Int.cast_neg, abs_neg]
        simpa [abs_of_nonneg (show (0 : ℝ) ≤ (fmt.beta ^ k : ℕ) by positivity)]
          using hsmall

private lemma p12_rep_abs_le_pred_bound
    {fmt : P12RadixFormat} {v : ℝ} (r : P12Representation fmt v)
    {e : ℤ} (he : r.exponent ≤ e) :
    |v| ≤ ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e := by
  have hB : 0 < fmt.beta ^ fmt.precision := by
    have hbg := fmt.beta_ge_two
    have hb : 0 < fmt.beta := by omega
    exact pow_pos hb _
  have hmreal : |(r.mantissa : ℝ)| < (fmt.beta ^ fmt.precision : ℕ) := by
    simpa [P12RadixFormat.mantissaBound, P12RadixFormat.betaR] using
      (abs_lt.mpr ⟨r.mantissa_lower, r.mantissa_upper⟩)
  have hmnat : r.mantissa.natAbs < fmt.beta ^ fmt.precision := by
    have hmInt : |r.mantissa| < ((fmt.beta ^ fmt.precision : ℕ) : ℤ) := by
      exact_mod_cast hmreal
    have hmNatInt : (r.mantissa.natAbs : ℤ) < ((fmt.beta ^ fmt.precision : ℕ) : ℤ) := by
      simpa using hmInt
    exact_mod_cast hmNatInt
  have hmle : |(r.mantissa : ℝ)| ≤ ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) := by
    have hh : ((r.mantissa.natAbs : ℕ) : ℝ) ≤
        ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show r.mantissa.natAbs ≤ fmt.beta ^ fmt.precision - 1 by omega)
    simpa using hh
  have hsmono := p12_scale_mono fmt he
  have hsnonneg : 0 ≤ fmt.scale r.exponent := le_of_lt (p12_scale_pos fmt _)
  have he_nonneg : 0 ≤ fmt.scale e := le_of_lt (p12_scale_pos fmt _)
  rw [r.value_eq, abs_mul, abs_of_pos (p12_scale_pos fmt _)]
  calc
    |(r.mantissa : ℝ)| * fmt.scale r.exponent ≤
        ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale r.exponent :=
      mul_le_mul_of_nonneg_right hmle hsnonneg
    _ ≤ ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) * fmt.scale e := by
      exact mul_le_mul_of_nonneg_left hsmono (by positivity)

private lemma p12_faithful_exact
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (h : p12FaithfulInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  rcases h with ⟨_, hgap⟩
  have hn := hgap exact hexact
  rcases lt_trichotomy rounded exact with hlt | heq | hgt
  · exact False.elim (hn (Or.inl ⟨hlt, le_rfl⟩))
  · exact heq
  · exact False.elim (hn (Or.inr ⟨le_rfl, hgt⟩))

private lemma p12_nearest_exact
    {fmt : P12RadixFormat} {exact rounded : ℝ}
    (h : p12NearestInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  have hz := h.2 exact hexact
  simp only [sub_self, abs_zero] at hz
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))) |>.symm

private lemma p12_condition7_lt_bound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  have hbg := fmt.beta_ge_two
  have hb : 0 < fmt.beta := by omega
  have hbpos : 0 < fmt.beta ^ fmt.precision := pow_pos hb _
  have hhpos : 0 < fmt.beta / 2 := by omega
  have hn : fmt.beta ^ fmt.precision - fmt.beta / 2 < fmt.beta ^ fmt.precision :=
    Nat.sub_lt hbpos hhpos
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.mantissaBound
    P12RadixFormat.betaR
  norm_cast

private lemma p12_half_le_bound_nat (fmt : P12RadixFormat) :
    fmt.beta / 2 ≤ fmt.beta ^ fmt.precision := by
  have hbpow : fmt.beta ≤ fmt.beta ^ fmt.precision := Nat.le_pow fmt.precision_pos
  exact le_trans (Nat.div_le_self _ _) hbpow

private lemma p12_condition_add_half (fmt : P12RadixFormat) :
    fmt.condition7Ceiling + fmt.halfRadixFloor = fmt.mantissaBound := by
  unfold P12RadixFormat.condition7Ceiling P12RadixFormat.halfRadixFloor
    P12RadixFormat.mantissaBound P12RadixFormat.betaR
  rw [← Nat.cast_add, Nat.sub_add_cancel (p12_half_le_bound_nat fmt)]
  norm_cast

private lemma p12_half_lt_bound (fmt : P12RadixFormat) :
    fmt.halfRadixFloor < fmt.mantissaBound := by
  have hbg := fmt.beta_ge_two
  have hh : fmt.beta / 2 < fmt.beta := Nat.div_lt_self (by omega) (by omega)
  have hbpow : fmt.beta ≤ fmt.beta ^ fmt.precision := Nat.le_pow fmt.precision_pos
  unfold P12RadixFormat.halfRadixFloor P12RadixFormat.mantissaBound
    P12RadixFormat.betaR
  exact_mod_cast (lt_of_lt_of_le hh hbpow)

private lemma p12_nat_nearby_multiple (b n : ℕ) (hb : 2 ≤ b) :
    ∃ k : ℕ, b ∣ k ∧ k ≤ n + b / 2 ∧ n ≤ k + b / 2 := by
  let q := n / b
  let r := n % b
  have hbpos : 0 < b := by omega
  have hrlt : r < b := by simpa [r] using Nat.mod_lt n hbpos
  have hn : n = q * b + r := by
    simpa [q, r, Nat.mul_comm] using (Nat.div_add_mod n b).symm
  by_cases hr : r ≤ b / 2
  · refine ⟨q * b, ⟨q, Nat.mul_comm _ _⟩, ?_, ?_⟩
    · rw [hn]
      omega
    · rw [hn]
      omega
  · have hkexp : (q + 1) * b = q * b + b := by ring
    refine ⟨(q + 1) * b, ⟨q + 1, Nat.mul_comm _ _⟩, ?_, ?_⟩
    · rw [hn, hkexp]
      omega
    · rw [hn, hkexp]
      omega

private lemma p12_rounding_candidate
    {fmt : P12RadixFormat} {e : ℤ} (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (Z : ℤ)
    (hZ : |(Z : ℝ)| < fmt.mantissaBound + fmt.condition7Ceiling) :
    ∃ f : ℝ, p12Representable fmt f ∧
      |(Z : ℝ) * fmt.scale e - f| ≤ fmt.halfRadixFloor * fmt.scale e := by
  let n := Z.natAbs
  obtain ⟨k, hbk, hkupper, hklower⟩ := p12_nat_nearby_multiple fmt.beta n fmt.beta_ge_two
  rcases hbk with ⟨km, hkm⟩
  have hnreal : ((n : ℕ) : ℝ) = |(Z : ℝ)| := by simp [n]
  have hnltR : (n : ℝ) < fmt.mantissaBound + fmt.condition7Ceiling := by
    rwa [hnreal]
  have hnlt : n < fmt.beta ^ fmt.precision +
      (fmt.beta ^ fmt.precision - fmt.beta / 2) := by
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      P12RadixFormat.condition7Ceiling at hnltR
    exact_mod_cast hnltR
  have hhalf := p12_half_le_bound_nat fmt
  have hklt2 : k < 2 * fmt.beta ^ fmt.precision := by
    have hsum : (fmt.beta ^ fmt.precision - fmt.beta / 2) + fmt.beta / 2 =
        fmt.beta ^ fmt.precision := Nat.sub_add_cancel hhalf
    omega
  have hkltmul : k < fmt.beta * fmt.beta ^ fmt.precision := by
    have hmul := Nat.mul_le_mul_right (fmt.beta ^ fmt.precision) fmt.beta_ge_two
    rw [Nat.mul_comm] at hmul
    omega
  have hbg := fmt.beta_ge_two
  have hbpos : 0 < fmt.beta := by omega
  have hkmlt : km < fmt.beta ^ fmt.precision := by
    have : fmt.beta * km < fmt.beta * fmt.beta ^ fmt.precision := by
      rwa [← hkm]
    exact (Nat.mul_lt_mul_left hbpos).mp this
  have hkmmant : |((km : ℕ) : ℝ)| < fmt.mantissaBound := by
    simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (km : ℕ))]
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
    exact_mod_cast hkmlt
  have hscale : fmt.scale (e + 1) = fmt.scale e * (fmt.beta : ℝ) := by
    unfold P12RadixFormat.scale P12RadixFormat.betaR
    rw [zpow_add_one₀ (ne_of_gt (p12_beta_pos fmt))]
  have hq := p12_scale_pos fmt e
  by_cases hnonneg : 0 ≤ Z
  · have hZn : Z = (n : ℕ) := by
      have hh : ((n : ℕ) : ℝ) = (Z : ℝ) := by
        rw [hnreal, abs_of_nonneg (by exact_mod_cast hnonneg)]
      have hi : (n : ℤ) = Z := by exact_mod_cast hh
      exact hi.symm
    let f : ℝ := (k : ℝ) * fmt.scale e
    have hfval : f = (km : ℝ) * fmt.scale (e + 1) := by
      dsimp [f]
      rw [hkm, hscale]
      push_cast
      ring
    have hfrep := p12_representable_of_int_scale (fmt := fmt)
      (m := (km : ℕ)) (e := e + 1)
      (show fmt.emin ≤ e + 1 by omega) (show e + 1 ≤ fmt.emax by omega) hfval hkmmant
    refine ⟨f, hfrep, ?_⟩
    have hdist : |((n : ℕ) : ℝ) - (k : ℝ)| ≤ (fmt.beta / 2 : ℕ) := by
      have hkR : (k : ℝ) ≤ (n : ℝ) + (fmt.beta / 2 : ℕ) := by exact_mod_cast hkupper
      have hnR : (n : ℝ) ≤ (k : ℝ) + (fmt.beta / 2 : ℕ) := by exact_mod_cast hklower
      rw [abs_le]
      constructor <;> linarith
    rw [hZn]
    dsimp [f, P12RadixFormat.halfRadixFloor]
    rw [← sub_mul, abs_mul, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_right hdist (le_of_lt hq)
  · have hZneg : Z < 0 := by omega
    have hZn : Z = -(n : ℕ) := by
      have hh : ((n : ℕ) : ℝ) = -(Z : ℝ) := by
        rw [hnreal, abs_of_neg (by exact_mod_cast hZneg)]
      have hi : (n : ℤ) = -Z := by exact_mod_cast hh
      omega
    let f : ℝ := -(k : ℝ) * fmt.scale e
    have hfval : f = (-((km : ℕ) : ℤ) : ℝ) * fmt.scale (e + 1) := by
      dsimp [f]
      rw [hkm, hscale]
      push_cast
      ring
    have hfrep := p12_representable_of_int_scale (fmt := fmt)
      (m := -((km : ℕ) : ℤ)) (e := e + 1)
      (show fmt.emin ≤ e + 1 by omega) (show e + 1 ≤ fmt.emax by omega)
      (by simpa using hfval) (by
        rw [Int.cast_neg, abs_neg]
        exact hkmmant)
    refine ⟨f, hfrep, ?_⟩
    have hdist : |((n : ℕ) : ℝ) - (k : ℝ)| ≤ (fmt.beta / 2 : ℕ) := by
      have hkR : (k : ℝ) ≤ (n : ℝ) + (fmt.beta / 2 : ℕ) := by exact_mod_cast hkupper
      have hnR : (n : ℝ) ≤ (k : ℝ) + (fmt.beta / 2 : ℕ) := by exact_mod_cast hklower
      rw [abs_le]
      constructor <;> linarith
    rw [hZn]
    dsimp [f, P12RadixFormat.halfRadixFloor]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [show -((n : ℕ) : ℝ) * fmt.scale e - -(k : ℝ) * fmt.scale e =
      -(((n : ℕ) : ℝ) - (k : ℝ)) * fmt.scale e by ring,
      abs_mul, abs_neg, abs_of_pos hq]
    exact mul_le_mul_of_nonneg_right hdist (le_of_lt hq)

private lemma p12_y_representation_below_x
    {fmt : P12RadixFormat} {x y : ℝ}
    (rx : P12Representation fmt x) (hy : p12Representable fmt y)
    (hcondition : |y| ≤ fmt.condition7Ceiling * fmt.scale rx.exponent) :
    ∃ ry : P12Representation fmt y, ry.exponent ≤ rx.exponent := by
  let ry₀ := Classical.choice hy
  by_cases hle : ry₀.exponent ≤ rx.exponent
  · exact ⟨ry₀, hle⟩
  · have hxe : rx.exponent ≤ ry₀.exponent := by omega
    obtain ⟨m, hmval⟩ := p12_rep_value_at_lower ry₀ hxe
    have hq : 0 < fmt.scale rx.exponent := p12_scale_pos fmt _
    have habsy : |y| = |(m : ℝ)| * fmt.scale rx.exponent := by
      rw [hmval, abs_mul, abs_of_pos hq]
    have hmle : |(m : ℝ)| ≤ fmt.condition7Ceiling := by
      rw [habsy] at hcondition
      nlinarith
    have hmlt : |(m : ℝ)| < fmt.mantissaBound :=
      lt_of_le_of_lt hmle (p12_condition7_lt_bound fmt)
    refine ⟨⟨m, rx.exponent, (abs_lt.mp hmlt).1, (abs_lt.mp hmlt).2,
      rx.exponent_lower, rx.exponent_upper, hmval⟩, le_rfl⟩

private lemma p12_zero_representable
    {fmt : P12RadixFormat} {e : ℤ} (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax) :
    p12Representable fmt (0 : ℝ) := by
  exact p12_representable_of_int_scale (m := 0) hemin hemax (by simp)
    (by simpa using p12_bound_pos fmt)

private lemma p12_differences_of_exponent_lt
    {fmt : P12RadixFormat} {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (heyx : ry.exponent < rx.exponent)
    (hnear : p12NearestInFormat fmt (x + y) s) :
    p12Representable fmt (s - x) ∧ p12Representable fmt (x + y - s) := by
  let q := fmt.scale ry.exponent
  have hq : 0 < q := p12_scale_pos fmt _
  have hB : 0 < fmt.mantissaBound := p12_bound_pos fmt
  have hymant : |(ry.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨ry.mantissa_lower, ry.mantissa_upper⟩
  have hymag : |y| < fmt.mantissaBound * q := by
    rw [ry.value_eq, abs_mul, abs_of_pos hq]
    exact mul_lt_mul_of_pos_right hymant hq
  obtain ⟨X, hxval⟩ := p12_rep_value_at_lower rx (le_of_lt heyx)
  let Z : ℤ := X + ry.mantissa
  have hzval : x + y = (Z : ℝ) * q := by
    calc
      x + y = (X : ℝ) * fmt.scale ry.exponent +
          (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
            exact congrArg₂ (fun a b : ℝ => a + b) hxval ry.value_eq
      _ = (Z : ℝ) * q := by
        dsimp [Z, q]
        push_cast
        ring
  by_cases hzsmall : |(Z : ℝ)| < fmt.mantissaBound
  · have hzrep : p12Representable fmt (x + y) :=
      p12_representable_of_int_scale ry.exponent_lower ry.exponent_upper hzval hzsmall
    have hsexact := p12_nearest_exact hnear hzrep
    subst s
    constructor
    · simpa using (show p12Representable fmt y from ⟨ry⟩)
    · convert p12_zero_representable ry.exponent_lower ry.exponent_upper using 1 <;> ring
  · have hzlarge : fmt.mantissaBound ≤ |(Z : ℝ)| := le_of_not_gt hzsmall
    let rs := Classical.choice hnear.1
    have hrsexp : ry.exponent < rs.exponent := by
      by_contra hn
      have hrsle : rs.exponent ≤ ry.exponent := by omega
      have hsmag := p12_rep_abs_le_pred_bound rs hrsle
      have hpredlt : ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) <
          fmt.mantissaBound := by
        unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
        have hbp : 0 < fmt.beta ^ fmt.precision := by
          have hbg := fmt.beta_ge_two
          have hb : 0 < fmt.beta := by omega
          exact pow_pos hb _
        exact_mod_cast (show fmt.beta ^ fmt.precision - 1 < fmt.beta ^ fmt.precision by omega)
      have hsstrict : |s| < fmt.mantissaBound * q := by
        exact lt_of_le_of_lt hsmag (mul_lt_mul_of_pos_right hpredlt hq)
      have heymax : ry.exponent < fmt.emax := lt_of_lt_of_le heyx rx.exponent_upper
      rcases le_total 0 Z with hZpos | hZneg
      · have hZB : fmt.mantissaBound ≤ (Z : ℝ) := by
          rw [abs_of_nonneg (by exact_mod_cast hZpos)] at hzlarge
          exact hzlarge
        let f : ℝ := fmt.mantissaBound * q
        have hfval : f = (((fmt.beta ^ fmt.precision : ℕ) : ℤ) : ℝ) *
            fmt.scale ry.exponent := by
          simp [f, q, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
        have hfrep : p12Representable fmt f := by
          apply p12_representable_of_int_scale_le (m := ((fmt.beta ^ fmt.precision : ℕ) : ℤ))
            ry.exponent_lower heymax hfval
          simp [P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
        have hsf : s < f := lt_of_le_of_lt (le_abs_self s) hsstrict
        have hfz : f ≤ x + y := by rw [hzval]; dsimp [f, q]; nlinarith
        have hsz : s ≤ x + y := le_trans (le_of_lt hsf) hfz
        have hn := hnear.2 f hfrep
        rw [abs_of_nonneg (sub_nonneg.mpr hsz), abs_of_nonneg (sub_nonneg.mpr hfz)] at hn
        linarith
      · have hZB : (Z : ℝ) ≤ -fmt.mantissaBound := by
          have hzr : (Z : ℝ) ≤ 0 := by exact_mod_cast hZneg
          rw [abs_of_nonpos hzr] at hzlarge
          linarith
        let f : ℝ := -fmt.mantissaBound * q
        have hfval : f = ((-((fmt.beta ^ fmt.precision : ℕ) : ℤ)) : ℝ) *
            fmt.scale ry.exponent := by
          simp [f, q, P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
        have hfrep : p12Representable fmt f := by
          apply p12_representable_of_int_scale_le (m := -((fmt.beta ^ fmt.precision : ℕ) : ℤ))
            ry.exponent_lower heymax (by simpa using hfval)
          simp [P12RadixFormat.mantissaBound, P12RadixFormat.betaR]
        have hfs : f < s := by
          have := neg_lt_of_abs_lt hsstrict
          dsimp [f]
          linarith
        have hzf : x + y ≤ f := by rw [hzval]; dsimp [f, q]; nlinarith
        have hzs : x + y ≤ s := le_trans hzf (le_of_lt hfs)
        have hn := hnear.2 f hfrep
        rw [abs_of_nonpos (sub_nonpos.mpr hzs), abs_of_nonpos (sub_nonpos.mpr hzf)] at hn
        linarith
    let e := min rx.exponent rs.exponent
    have hex : e ≤ rx.exponent := min_le_left _ _
    have hes : e ≤ rs.exponent := min_le_right _ _
    have hegt : ry.exponent < e := lt_min heyx hrsexp
    obtain ⟨Xm, hxmval⟩ := p12_rep_value_at_lower rx hex
    obtain ⟨Sm, hsmval⟩ := p12_rep_value_at_lower rs hes
    have hdval : s - x = ((Sm - Xm : ℤ) : ℝ) * fmt.scale e := by
      rw [hsmval, hxmval]
      push_cast
      ring
    have herr : |s - (x + y)| ≤ |y| := by
      simpa [abs_sub_comm] using hnear.2 x (show p12Representable fmt x from ⟨rx⟩)
    have hdabs : |s - x| < fmt.mantissaBound * fmt.scale e := by
      have htri : |s - x| ≤ |s - (x + y)| + |y| := by
        calc
          |s - x| = |(s - (x + y)) + y| := by ring_nf
          _ ≤ |s - (x + y)| + |y| := abs_add_le _ _
      have hscale1 : q * (fmt.beta : ℝ) ≤ fmt.scale e := by
        have hm := p12_scale_mono fmt (show ry.exponent + 1 ≤ e by omega)
        have hs : fmt.scale (ry.exponent + 1) = q * (fmt.beta : ℝ) := by
          dsimp [q]
          unfold P12RadixFormat.scale P12RadixFormat.betaR
          rw [zpow_add_one₀ (ne_of_gt (p12_beta_pos fmt))]
        rwa [hs] at hm
      have hb2 : (2 : ℝ) ≤ fmt.beta := by exact_mod_cast fmt.beta_ge_two
      have hsumlt : |s - (x + y)| + |y| < 2 * (fmt.mantissaBound * q) := by
        linarith
      have htwo : 2 * (fmt.mantissaBound * q) ≤
          fmt.mantissaBound * (q * (fmt.beta : ℝ)) := by
        calc
          2 * (fmt.mantissaBound * q) ≤
              (fmt.beta : ℝ) * (fmt.mantissaBound * q) :=
            mul_le_mul_of_nonneg_right hb2 (by positivity)
          _ = fmt.mantissaBound * (q * (fmt.beta : ℝ)) := by ring
      have hlast : fmt.mantissaBound * (q * (fmt.beta : ℝ)) ≤
          fmt.mantissaBound * fmt.scale e :=
        mul_le_mul_of_nonneg_left hscale1 (le_of_lt hB)
      exact lt_of_le_of_lt htri (lt_of_lt_of_le hsumlt (le_trans htwo hlast))
    have hdmant : |(((Sm - Xm : ℤ) : ℝ))| < fmt.mantissaBound := by
      rw [hdval, abs_mul, abs_of_pos (p12_scale_pos fmt _)] at hdabs
      nlinarith [p12_scale_pos fmt e]
    have hdrep : p12Representable fmt (s - x) :=
      p12_representable_of_int_scale (le_trans ry.exponent_lower (le_of_lt hegt))
        (le_trans hex rx.exponent_upper) hdval hdmant
    obtain ⟨S₀, hs₀val⟩ := p12_rep_value_at_lower rs (le_of_lt hrsexp)
    have hrval : x + y - s = (((X + ry.mantissa - S₀ : ℤ)) : ℝ) * q := by
      calc
        x + y - s = (Z : ℝ) * q - (S₀ : ℝ) * fmt.scale ry.exponent := by
          rw [hzval, hs₀val]
        _ = (((X + ry.mantissa - S₀ : ℤ)) : ℝ) * q := by
          dsimp [Z, q]
          push_cast
          ring
    have hrabs : |x + y - s| < fmt.mantissaBound * q :=
      lt_of_le_of_lt (by simpa [abs_sub_comm] using herr) hymag
    have hrmant : |(((X + ry.mantissa - S₀ : ℤ) : ℝ))| < fmt.mantissaBound := by
      rw [hrval, abs_mul, abs_of_pos hq] at hrabs
      nlinarith
    exact ⟨hdrep, p12_representable_of_int_scale ry.exponent_lower ry.exponent_upper
      hrval hrmant⟩

private lemma p12_differences_of_exponent_eq
    {fmt : P12RadixFormat} {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (heyx : ry.exponent = rx.exponent)
    (hcondition : |y| ≤ fmt.condition7Ceiling * fmt.scale rx.exponent)
    (hnear : p12NearestInFormat fmt (x + y) s) :
    p12Representable fmt (s - x) ∧ p12Representable fmt (x + y - s) := by
  let e := rx.exponent
  let q := fmt.scale e
  have hq : 0 < q := p12_scale_pos fmt _
  have hB : 0 < fmt.mantissaBound := p12_bound_pos fmt
  have hxmant : |(rx.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨rx.mantissa_lower, rx.mantissa_upper⟩
  have hymant : |(ry.mantissa : ℝ)| ≤ fmt.condition7Ceiling := by
    have hyval : y = (ry.mantissa : ℝ) * q := by
      calc
        y = (ry.mantissa : ℝ) * fmt.scale ry.exponent := ry.value_eq
        _ = (ry.mantissa : ℝ) * q := by simp [q, e, heyx]
    have habsy : |y| = |(ry.mantissa : ℝ)| * q := by
      calc
        |y| = |(ry.mantissa : ℝ) * q| := congrArg abs hyval
        _ = |(ry.mantissa : ℝ)| * q := by rw [abs_mul, abs_of_pos hq]
    rw [habsy] at hcondition
    dsimp [q, e] at hcondition
    nlinarith
  have hymag : |y| < fmt.mantissaBound * q := by
    have hmylt := lt_of_le_of_lt hymant (p12_condition7_lt_bound fmt)
    have hyval : y = (ry.mantissa : ℝ) * q := by
      calc
        y = (ry.mantissa : ℝ) * fmt.scale ry.exponent := ry.value_eq
        _ = (ry.mantissa : ℝ) * q := by simp [q, e, heyx]
    calc
      |y| = |(ry.mantissa : ℝ) * q| := congrArg abs hyval
      _ = |(ry.mantissa : ℝ)| * q := by rw [abs_mul, abs_of_pos hq]
      _ < fmt.mantissaBound * q := mul_lt_mul_of_pos_right hmylt hq
  let Z : ℤ := rx.mantissa + ry.mantissa
  have hzval : x + y = (Z : ℝ) * q := by
    calc
      x + y = (rx.mantissa : ℝ) * fmt.scale rx.exponent +
          (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
            exact congrArg₂ (fun a b : ℝ => a + b) rx.value_eq ry.value_eq
      _ = (Z : ℝ) * q := by
        dsimp [Z, q, e]
        rw [heyx]
        push_cast
        ring
  have hzbound : |(Z : ℝ)| < fmt.mantissaBound + fmt.condition7Ceiling := by
    have htri : |(Z : ℝ)| ≤ |(rx.mantissa : ℝ)| + |(ry.mantissa : ℝ)| := by
      dsimp [Z]
      push_cast
      exact abs_add_le _ _
    linarith
  by_cases hzsmall : |(Z : ℝ)| < fmt.mantissaBound
  · have hzrep : p12Representable fmt (x + y) :=
      p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper hzval hzsmall
    have hsexact := p12_nearest_exact hnear hzrep
    subst s
    constructor
    · simpa using (show p12Representable fmt y from ⟨ry⟩)
    · convert p12_zero_representable rx.exponent_lower rx.exponent_upper using 1 <;> ring
  · have hzlarge : fmt.mantissaBound ≤ |(Z : ℝ)| := le_of_not_gt hzsmall
    have herr : |s - (x + y)| ≤ |y| := by
      simpa [abs_sub_comm] using hnear.2 x (show p12Representable fmt x from ⟨rx⟩)
    let rs := Classical.choice hnear.1
    by_cases hemaxeq : e = fmt.emax
    · have hrsle : rs.exponent ≤ e := by
        rw [hemaxeq]
        exact rs.exponent_upper
      have hsmag := p12_rep_abs_le_pred_bound rs hrsle
      let A : ℝ := ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ)
      have hAq : |s| ≤ A * q := by simpa [A, q] using hsmag
      have hAltB : A < fmt.mantissaBound := by
        dsimp [A]
        unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
        have hbp : 0 < fmt.beta ^ fmt.precision := by
          have hbg := fmt.beta_ge_two
          have hb : 0 < fmt.beta := by omega
          exact pow_pos hb _
        exact_mod_cast (show fmt.beta ^ fmt.precision - 1 < fmt.beta ^ fmt.precision by omega)
      have hBnat1 : 1 ≤ fmt.beta ^ fmt.precision := by
        have hbg := fmt.beta_ge_two
        have hb : 0 < fmt.beta := by omega
        exact Nat.one_le_pow _ _ hb
      have hAeq : A = fmt.mantissaBound - 1 := by
        dsimp [A]
        unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
        rw [Nat.cast_sub hBnat1]
        norm_num
      have hBtwo : (2 : ℝ) ≤ fmt.mantissaBound := by
        unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
        exact_mod_cast (le_trans fmt.beta_ge_two (Nat.le_pow fmt.precision_pos))
      rcases le_total 0 Z with hZpos | hZneg
      · have hZB : fmt.mantissaBound ≤ (Z : ℝ) := by
          rw [abs_of_nonneg (by exact_mod_cast hZpos)] at hzlarge
          exact hzlarge
        let f : ℝ := A * q
        have hfval : f = (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ) : ℝ) *
            fmt.scale e := by simp [f, A, q]
        have hfrep : p12Representable fmt f := by
          apply p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper hfval
          simpa [A] using hAltB
        have hsf : s ≤ f := le_trans (le_abs_self s) hAq
        have hfz : f ≤ x + y := by rw [hzval]; dsimp [f, A]; nlinarith
        have hn := hnear.2 f hfrep
        rw [abs_of_nonneg (sub_nonneg.mpr (le_trans hsf hfz)),
          abs_of_nonneg (sub_nonneg.mpr hfz)] at hn
        have hse : s = f := by linarith
        have hXpos : 0 < (rx.mantissa : ℝ) := by
          have hc := p12_condition7_lt_bound fmt
          dsimp [Z] at hZB
          push_cast at hZB
          have hyupper := le_trans (le_abs_self (ry.mantissa : ℝ)) hymant
          linarith
        let D : ℤ := (fmt.beta ^ fmt.precision - 1 : ℕ) - rx.mantissa
        have hdval : s - x = (D : ℝ) * q := by
          rw [hse, rx.value_eq]
          dsimp [D, f, A, q, e]
          push_cast
          ring
        have hD : |(D : ℝ)| < fmt.mantissaBound := by
          have hAE : (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ)) =
              fmt.mantissaBound - 1 := by simpa [A] using hAeq
          have hxhi := (abs_lt.mp hxmant).2
          dsimp [D]
          push_cast
          rw [abs_lt]
          constructor <;> nlinarith
        have hdrep := p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper
          hdval hD
        let R : ℤ := Z - (fmt.beta ^ fmt.precision - 1 : ℕ)
        have hrval : x + y - s = (R : ℝ) * q := by
          rw [hzval, hse]
          dsimp [R, f, A]
          push_cast
          ring
        have hrabs : |x + y - s| < fmt.mantissaBound * q :=
          lt_of_le_of_lt (by simpa [abs_sub_comm] using herr) hymag
        have hR : |(R : ℝ)| < fmt.mantissaBound := by
          rw [hrval, abs_mul, abs_of_pos hq] at hrabs
          nlinarith
        exact ⟨hdrep, p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper
          hrval hR⟩
      · have hZB : (Z : ℝ) ≤ -fmt.mantissaBound := by
          have hz0 : (Z : ℝ) ≤ 0 := by exact_mod_cast hZneg
          rw [abs_of_nonpos hz0] at hzlarge
          linarith
        let f : ℝ := -A * q
        have hfval : f = ((-((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ)) : ℝ) *
            fmt.scale e := by simp [f, A, q]
        have hfrep : p12Representable fmt f := by
          apply p12_representable_of_int_scale (m := -((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ))
            rx.exponent_lower rx.exponent_upper (by simpa using hfval)
          simpa [A] using hAltB
        have hfs : f ≤ s := by
          have := neg_le_of_abs_le hAq
          dsimp [f]
          linarith
        have hzf : x + y ≤ f := by rw [hzval]; dsimp [f, A]; nlinarith
        have hn := hnear.2 f hfrep
        rw [abs_of_nonpos (sub_nonpos.mpr (le_trans hzf hfs)),
          abs_of_nonpos (sub_nonpos.mpr hzf)] at hn
        have hse : s = f := by linarith
        have hXneg : (rx.mantissa : ℝ) < 0 := by
          have hc := p12_condition7_lt_bound fmt
          dsimp [Z] at hZB
          push_cast at hZB
          have hylower := neg_le_of_abs_le hymant
          linarith
        let D : ℤ := -((fmt.beta ^ fmt.precision - 1 : ℕ) : ℤ) - rx.mantissa
        have hdval : s - x = (D : ℝ) * q := by
          rw [hse, rx.value_eq]
          dsimp [D, f, A, q, e]
          push_cast
          ring
        have hD : |(D : ℝ)| < fmt.mantissaBound := by
          have hAE : (((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ)) =
              fmt.mantissaBound - 1 := by simpa [A] using hAeq
          have hxlo := (abs_lt.mp hxmant).1
          dsimp [D]
          push_cast
          rw [abs_lt]
          constructor <;> nlinarith
        have hdrep := p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper
          hdval hD
        let R : ℤ := Z + (fmt.beta ^ fmt.precision - 1 : ℕ)
        have hrval : x + y - s = (R : ℝ) * q := by
          rw [hzval, hse]
          dsimp [R, f, A]
          push_cast
          ring
        have hrabs : |x + y - s| < fmt.mantissaBound * q :=
          lt_of_le_of_lt (by simpa [abs_sub_comm] using herr) hymag
        have hR : |(R : ℝ)| < fmt.mantissaBound := by
          rw [hrval, abs_mul, abs_of_pos hq] at hrabs
          nlinarith
        exact ⟨hdrep, p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper
          hrval hR⟩
    · have hemaxlt : e < fmt.emax := lt_of_le_of_ne rx.exponent_upper hemaxeq
      have hrsexp : e ≤ rs.exponent := by
        by_contra hn
        have hrslt : rs.exponent < e := by omega
        have hsmag := p12_rep_abs_le_pred_bound rs (le_of_lt hrslt)
        have hpredlt : ((fmt.beta ^ fmt.precision - 1 : ℕ) : ℝ) <
            fmt.mantissaBound := by
          unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
          have hbp : 0 < fmt.beta ^ fmt.precision := by
            have hbg := fmt.beta_ge_two
            have hb : 0 < fmt.beta := by omega
            exact pow_pos hb _
          exact_mod_cast (show fmt.beta ^ fmt.precision - 1 < fmt.beta ^ fmt.precision by omega)
        have hsstrict : |s| < fmt.mantissaBound * q :=
          lt_of_le_of_lt hsmag (mul_lt_mul_of_pos_right hpredlt hq)
        rcases le_total 0 Z with hZpos | hZneg
        · have hZB : fmt.mantissaBound ≤ (Z : ℝ) := by
            rw [abs_of_nonneg (by exact_mod_cast hZpos)] at hzlarge
            exact hzlarge
          let f : ℝ := fmt.mantissaBound * q
          have hfval : f = (((fmt.beta ^ fmt.precision : ℕ) : ℤ) : ℝ) *
              fmt.scale e := by simp [f, q, P12RadixFormat.mantissaBound,
                P12RadixFormat.betaR]
          have hfrep := p12_representable_of_int_scale_le rx.exponent_lower hemaxlt
            hfval (show |((((fmt.beta ^ fmt.precision : ℕ) : ℤ) : ℝ))| ≤
              fmt.mantissaBound by simp [P12RadixFormat.mantissaBound,
                P12RadixFormat.betaR])
          have hsf : s < f := lt_of_le_of_lt (le_abs_self s) hsstrict
          have hfz : f ≤ x + y := by rw [hzval]; dsimp [f]; nlinarith
          have hn := hnear.2 f hfrep
          rw [abs_of_nonneg (sub_nonneg.mpr (le_trans (le_of_lt hsf) hfz)),
            abs_of_nonneg (sub_nonneg.mpr hfz)] at hn
          linarith
        · have hZB : (Z : ℝ) ≤ -fmt.mantissaBound := by
            have hz0 : (Z : ℝ) ≤ 0 := by exact_mod_cast hZneg
            rw [abs_of_nonpos hz0] at hzlarge
            linarith
          let f : ℝ := -fmt.mantissaBound * q
          have hfval : f = ((-((fmt.beta ^ fmt.precision : ℕ) : ℤ)) : ℝ) *
              fmt.scale e := by simp [f, q, P12RadixFormat.mantissaBound,
                P12RadixFormat.betaR]
          have hfrep := p12_representable_of_int_scale_le
            (m := -((fmt.beta ^ fmt.precision : ℕ) : ℤ)) rx.exponent_lower hemaxlt
            (by simpa using hfval) (by
              simp [P12RadixFormat.mantissaBound, P12RadixFormat.betaR])
          have hfs : f < s := by
            have := neg_lt_of_abs_lt hsstrict
            dsimp [f]
            linarith
          have hzf : x + y ≤ f := by rw [hzval]; dsimp [f]; nlinarith
          have hn := hnear.2 f hfrep
          rw [abs_of_nonpos (sub_nonpos.mpr (le_trans hzf (le_of_lt hfs))),
            abs_of_nonpos (sub_nonpos.mpr hzf)] at hn
          linarith
      obtain ⟨S, hsval⟩ := p12_rep_value_at_lower rs hrsexp
      have hdval : s - x = ((S - rx.mantissa : ℤ) : ℝ) * q := by
        calc
          s - x = (S : ℝ) * fmt.scale e -
              (rx.mantissa : ℝ) * fmt.scale rx.exponent := by
                exact congrArg₂ (fun a b : ℝ => a - b) hsval rx.value_eq
          _ = ((S - rx.mantissa : ℤ) : ℝ) * q := by
            dsimp [q, e]
            push_cast
            ring
      have hrval : x + y - s = ((Z - S : ℤ) : ℝ) * q := by
        rw [hzval, hsval]
        dsimp [q, e]
        push_cast
        ring
      obtain ⟨f, hfrep, hferr⟩ := p12_rounding_candidate rx.exponent_lower hemaxlt Z hzbound
      have herrhalf : |s - (x + y)| ≤ fmt.halfRadixFloor * q := by
        have hn := hnear.2 f hfrep
        have hn' : |s - (x + y)| ≤ |(Z : ℝ) * fmt.scale e - f| := by
          simpa [hzval, q, abs_sub_comm] using hn
        exact le_trans hn' hferr
      have hdabs : |s - x| ≤ fmt.mantissaBound * q := by
        have htri : |s - x| ≤ |s - (x + y)| + |y| := by
          calc
            |s - x| = |(s - (x + y)) + y| := by ring_nf
            _ ≤ |s - (x + y)| + |y| := abs_add_le _ _
        have hadd := p12_condition_add_half fmt
        have hyweak : |y| ≤ fmt.condition7Ceiling * q := by
          simpa [q, e] using hcondition
        nlinarith
      have hD : |((S - rx.mantissa : ℤ) : ℝ)| ≤ fmt.mantissaBound := by
        rw [hdval, abs_mul, abs_of_pos hq] at hdabs
        nlinarith
      have hdrep := p12_representable_of_int_scale_le rx.exponent_lower hemaxlt hdval hD
      have hrabs : |x + y - s| < fmt.mantissaBound * q :=
        lt_of_le_of_lt (by simpa [abs_sub_comm] using herrhalf)
          (mul_lt_mul_of_pos_right (p12_half_lt_bound fmt) hq)
      have hR : |((Z - S : ℤ) : ℝ)| < fmt.mantissaBound := by
        rw [hrval, abs_mul, abs_of_pos hq] at hrabs
        nlinarith
      exact ⟨hdrep, p12_representable_of_int_scale rx.exponent_lower rx.exponent_upper
        hrval hR⟩

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
  obtain ⟨ry, hryx⟩ := p12_y_representation_below_x rx hy hcondition
  have hdiffs : p12Representable fmt (tr.s - x) ∧
      p12Representable fmt (x + y - tr.s) := by
    rcases lt_or_eq_of_le hryx with hryxlt | hryxeq
    · exact p12_differences_of_exponent_lt rx ry hryxlt run.add
    · exact p12_differences_of_exponent_eq rx ry hryxeq hcondition run.add
  have ht : tr.t = tr.s - x := p12_faithful_exact run.first_sub hdiffs.1
  have hsecond : p12Representable fmt (y - tr.t) := by
    rw [ht]
    convert hdiffs.2 using 1 <;> ring
  have he : tr.e = y - tr.t := p12_faithful_exact run.second_sub hsecond
  have hsum : tr.s + tr.e = x + y := by
    rw [he, ht]
    ring
  have herr : |tr.s - (x + y)| ≤ |y| := by
    simpa [abs_sub_comm] using run.add.2 x hx
  exact ⟨ht, he, hsum, herr⟩

end HighamBench
