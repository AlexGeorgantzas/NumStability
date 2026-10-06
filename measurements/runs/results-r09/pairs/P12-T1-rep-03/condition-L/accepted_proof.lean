import HighamBench.P12Definitions

namespace HighamBench

private lemma p12_scale_pos (fmt : P12RadixFormat) (e : ℤ) :
    0 < fmt.scale e := by
  change 0 < (fmt.beta : ℝ) ^ e
  apply zpow_pos
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)

private lemma p12_value_integer_at_lower_exponent
    (fmt : P12RadixFormat) {a : ℝ} (ra : P12Representation fmt a)
    (e : ℤ) (he : e ≤ ra.exponent) :
    ∃ k : ℤ, a = (k : ℝ) * fmt.scale e := by
  let n : ℕ := (ra.exponent - e).toNat
  have hn : (n : ℤ) = ra.exponent - e := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr he)
  refine ⟨ra.mantissa * (fmt.beta ^ n : ℕ), ?_⟩
  have hexp : ra.exponent = e + (n : ℤ) := by omega
  calc
    a = (ra.mantissa : ℝ) * fmt.scale ra.exponent := ra.value_eq
    _ = (ra.mantissa : ℝ) * fmt.scale (e + (n : ℤ)) := by rw [hexp]
    _ = (ra.mantissa * (fmt.beta ^ n : ℕ) : ℤ) * fmt.scale e := by
      simp only [P12RadixFormat.scale, P12RadixFormat.betaR]
      rw [zpow_add₀ (ne_of_gt (by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)))]
      · rw [zpow_natCast]
        push_cast
        ring

private lemma p12_representable_of_integer_multiple_lt
    (fmt : P12RadixFormat) {a : ℝ} (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (k : ℤ) (ha : a = (k : ℝ) * fmt.scale e)
    (hab : |a| < fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt a := by
  have hspos := p12_scale_pos fmt e
  have habk : |(k : ℝ)| < fmt.mantissaBound := by
    rw [ha, abs_mul, abs_of_pos hspos] at hab
    nlinarith
  refine ⟨⟨k, e, ?_, ?_, hemin, hemax, ha⟩⟩
  · exact (abs_lt.mp habk).1
  · exact (abs_lt.mp habk).2

private lemma p12_boundary_representable
    (fmt : P12RadixFormat) (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax) (sgn : ℤ)
    (hsgn : sgn = 1 ∨ sgn = -1) :
    ∃ r : P12Representation fmt
        ((sgn : ℝ) * fmt.mantissaBound * fmt.scale e),
      e ≤ r.exponent := by
  obtain ⟨q, hp⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fmt.precision_pos)
  let m : ℤ := sgn * (fmt.beta ^ q : ℕ)
  have hbeta_gt_one : 1 < fmt.beta := fmt.beta_ge_two
  have hpow_lt : fmt.beta ^ q < fmt.beta ^ fmt.precision := by
    rw [hp, pow_succ]
    nlinarith [pow_pos (show 0 < fmt.beta by omega) q]
  have hmabs : |(m : ℝ)| < fmt.mantissaBound := by
    rcases hsgn with rfl | rfl <;>
      simp [m, P12RadixFormat.mantissaBound, P12RadixFormat.betaR,
        Nat.cast_pow] <;> exact_mod_cast hpow_lt
  refine ⟨⟨m, e + 1, (abs_lt.mp hmabs).1, (abs_lt.mp hmabs).2,
    ?_, ?_, ?_⟩, ?_⟩
  · exact Int.le_add_one hemin
  · exact Int.add_one_le_of_lt hemax
  · rcases hsgn with rfl | rfl <;>
      simp only [m, P12RadixFormat.mantissaBound,
        P12RadixFormat.scale, P12RadixFormat.betaR]
    all_goals
      rw [hp, pow_succ, zpow_add_one₀]
      · push_cast
        ring
      · exact_mod_cast (show fmt.beta ≠ 0 by omega)
  · simpa using (show e ≤ e + 1 by omega)

private lemma p12_representable_of_integer_multiple_le
    (fmt : P12RadixFormat) {a : ℝ} (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (k : ℤ) (ha : a = (k : ℝ) * fmt.scale e)
    (hab : |a| ≤ fmt.mantissaBound * fmt.scale e) :
    p12Representable fmt a := by
  have hspos := p12_scale_pos fmt e
  have habk : |(k : ℝ)| ≤ fmt.mantissaBound := by
    rw [ha, abs_mul, abs_of_pos hspos] at hab
    nlinarith
  rcases lt_or_eq_of_le habk with hlt | heq
  · exact p12_representable_of_integer_multiple_lt fmt e hemin (le_of_lt hemax)
      k ha (by rw [ha, abs_mul, abs_of_pos hspos]; nlinarith)
  · have hBnonneg : 0 ≤ fmt.mantissaBound := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      positivity
    rcases (abs_eq hBnonneg).mp heq with hk | hk
    · have ha' : a = ((1 : ℤ) : ℝ) * fmt.mantissaBound * fmt.scale e := by
        rw [ha, hk]
        ring
      rw [ha']
      rcases p12_boundary_representable fmt e hemin hemax 1 (Or.inl rfl) with
        ⟨r, _⟩
      exact ⟨by simpa using r⟩
    · have ha' : a = ((-1 : ℤ) : ℝ) * fmt.mantissaBound * fmt.scale e := by
        rw [ha, hk]
        ring
      rw [ha']
      rcases p12_boundary_representable fmt e hemin hemax (-1) (Or.inr rfl) with
        ⟨r, _⟩
      exact ⟨r⟩

private lemma p12_representation_of_integer_multiple_le
    (fmt : P12RadixFormat) {a : ℝ} (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e < fmt.emax)
    (k : ℤ) (ha : a = (k : ℝ) * fmt.scale e)
    (hab : |a| ≤ fmt.mantissaBound * fmt.scale e) :
    ∃ r : P12Representation fmt a, e ≤ r.exponent := by
  have hspos := p12_scale_pos fmt e
  have habk : |(k : ℝ)| ≤ fmt.mantissaBound := by
    rw [ha, abs_mul, abs_of_pos hspos] at hab
    nlinarith
  rcases lt_or_eq_of_le habk with hlt | heq
  · refine ⟨⟨k, e, (abs_lt.mp hlt).1, (abs_lt.mp hlt).2,
      hemin, le_of_lt hemax, ha⟩, le_rfl⟩
  · have hBnonneg : 0 ≤ fmt.mantissaBound := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      positivity
    rcases (abs_eq hBnonneg).mp heq with hk | hk
    · have ha' : a = ((1 : ℤ) : ℝ) * fmt.mantissaBound * fmt.scale e := by
        rw [ha, hk]
        ring
      rw [ha']
      simpa using p12_boundary_representable fmt e hemin hemax 1 (Or.inl rfl)
    · have ha' : a = ((-1 : ℤ) : ℝ) * fmt.mantissaBound * fmt.scale e := by
        rw [ha, hk]
        ring
      rw [ha']
      exact p12_boundary_representable fmt e hemin hemax (-1) (Or.inr rfl)

private lemma p12_representation_of_integer_multiple_lt
    (fmt : P12RadixFormat) {a : ℝ} (e : ℤ)
    (hemin : fmt.emin ≤ e) (hemax : e ≤ fmt.emax)
    (k : ℤ) (ha : a = (k : ℝ) * fmt.scale e)
    (hab : |a| < fmt.mantissaBound * fmt.scale e) :
    ∃ r : P12Representation fmt a, r.exponent = e := by
  have hspos := p12_scale_pos fmt e
  have habk : |(k : ℝ)| < fmt.mantissaBound := by
    rw [ha, abs_mul, abs_of_pos hspos] at hab
    nlinarith
  exact ⟨⟨k, e, (abs_lt.mp habk).1, (abs_lt.mp habk).2,
    hemin, hemax, ha⟩, rfl⟩

private lemma p12_faithful_eq_of_representable
    (fmt : P12RadixFormat) {exact rounded : ℝ}
    (hfaithful : p12FaithfulInFormat fmt exact rounded)
    (hexact : p12Representable fmt exact) : rounded = exact := by
  have hnone := hfaithful.2 exact hexact
  rcases lt_trichotomy rounded exact with hlt | heq | hgt
  · exact False.elim (hnone (Or.inl ⟨hlt, le_rfl⟩))
  · exact heq
  · exact False.elim (hnone (Or.inr ⟨le_rfl, hgt⟩))

private lemma p12_int_near_radix_multiple (n : ℤ) (b : ℕ) (hb : 2 ≤ b) :
    ∃ q : ℤ, |n - q * (b : ℤ)| ≤ (b / 2 : ℕ) := by
  let r : ℤ := n % (b : ℤ)
  have hb0 : (b : ℤ) ≠ 0 := by omega
  have hr0 : 0 ≤ r := Int.emod_nonneg n hb0
  have hrb : r < (b : ℤ) := by
    simpa [r] using Int.emod_lt n hb0
  have hdiv : (b : ℤ) * (n / (b : ℤ)) + r = n := by
    simpa [r] using Int.ediv_add_emod n (b : ℤ)
  rw [mul_comm (b : ℤ) (n / (b : ℤ))] at hdiv
  by_cases hhalf : 2 * r ≤ (b : ℤ)
  · refine ⟨n / (b : ℤ), ?_⟩
    have heq : n - n / (b : ℤ) * (b : ℤ) = r := by omega
    rw [heq, abs_of_nonneg hr0]
    omega
  · refine ⟨n / (b : ℤ) + 1, ?_⟩
    have heq : n - (n / (b : ℤ) + 1) * (b : ℤ) = r - b := by
      calc
        n - (n / (b : ℤ) + 1) * (b : ℤ) =
            n - n / (b : ℤ) * (b : ℤ) - b := by ring
        _ = r - b := by omega
    rw [heq, abs_of_nonpos (by omega)]
    omega

private lemma p12_scale_mono (fmt : P12RadixFormat) {e f : ℤ} (hef : e ≤ f) :
    fmt.scale e ≤ fmt.scale f := by
  apply zpow_le_zpow_right₀
  · change (1 : ℝ) ≤ fmt.beta
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) fmt.beta_ge_two)
  · exact hef

private lemma p12_scale_succ (fmt : P12RadixFormat) (e : ℤ) :
    fmt.scale (e + 1) = fmt.scale e * fmt.betaR := by
  unfold P12RadixFormat.scale
  rw [zpow_add_one₀]
  exact ne_of_gt (by
    change (0 : ℝ) < (fmt.beta : ℝ)
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two))

private lemma p12_rep_abs_lt_bound_scale
    (fmt : P12RadixFormat) {a : ℝ} (ra : P12Representation fmt a) :
    |a| < fmt.mantissaBound * fmt.scale ra.exponent := by
  have hm : |(ra.mantissa : ℝ)| < fmt.mantissaBound :=
    abs_lt.mpr ⟨ra.mantissa_lower, ra.mantissa_upper⟩
  calc
    |a| = |(ra.mantissa : ℝ) * fmt.scale ra.exponent| :=
      congrArg abs ra.value_eq
    _ = |(ra.mantissa : ℝ)| * fmt.scale ra.exponent := by
      rw [abs_mul, abs_of_pos (p12_scale_pos fmt ra.exponent)]
    _ < fmt.mantissaBound * fmt.scale ra.exponent :=
      mul_lt_mul_of_pos_right hm (p12_scale_pos fmt ra.exponent)

private lemma p12_bound_pos (fmt : P12RadixFormat) :
    (0 : ℝ) < fmt.mantissaBound := by
  change (0 : ℝ) < (fmt.beta : ℝ) ^ fmt.precision
  exact pow_pos (by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)) _

private lemma p12_bound_ge_radix_nat (fmt : P12RadixFormat) :
    fmt.beta ≤ fmt.beta ^ fmt.precision := by
  obtain ⟨q, hp⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt fmt.precision_pos)
  rw [hp, pow_succ]
  have hge := fmt.beta_ge_two
  have hpow : 1 ≤ fmt.beta ^ q := one_le_pow₀ (by omega)
  nlinarith

private lemma p12_bound_ge_radix (fmt : P12RadixFormat) :
    fmt.betaR ≤ fmt.mantissaBound := by
  change ((fmt.beta : ℝ) ≤ (fmt.beta : ℝ) ^ fmt.precision)
  exact_mod_cast p12_bound_ge_radix_nat fmt

private lemma p12_half_add_ceiling (fmt : P12RadixFormat) :
    fmt.halfRadixFloor + fmt.condition7Ceiling = fmt.mantissaBound := by
  have hhalf : fmt.beta / 2 ≤ fmt.beta ^ fmt.precision :=
    le_trans (Nat.div_le_self _ _) (p12_bound_ge_radix_nat fmt)
  unfold P12RadixFormat.halfRadixFloor
    P12RadixFormat.condition7Ceiling P12RadixFormat.mantissaBound
    P12RadixFormat.betaR
  norm_cast
  exact Nat.add_sub_of_le hhalf

private lemma p12_two_mul_half_le_radix (fmt : P12RadixFormat) :
    2 * fmt.halfRadixFloor ≤ fmt.betaR := by
  unfold P12RadixFormat.halfRadixFloor P12RadixFormat.betaR
  norm_cast
  omega

private lemma p12_bound_le_radix_mul_ceiling (fmt : P12RadixFormat) :
    fmt.mantissaBound ≤ fmt.betaR * fmt.condition7Ceiling := by
  have hb := p12_bound_ge_radix fmt
  have hh := p12_two_mul_half_le_radix fmt
  have hsum := p12_half_add_ceiling fmt
  have hbeta : (2 : ℝ) ≤ fmt.betaR := by
    unfold P12RadixFormat.betaR
    exact_mod_cast fmt.beta_ge_two
  have hhalf_nonneg : 0 ≤ fmt.halfRadixFloor := by
    unfold P12RadixFormat.halfRadixFloor
    positivity
  have hceil_nonneg : 0 ≤ fmt.condition7Ceiling := by
    unfold P12RadixFormat.condition7Ceiling
    positivity
  nlinarith [mul_nonneg (sub_nonneg.mpr hbeta) (sub_nonneg.mpr hb)]

private lemma p12_ceiling_lt_bound (fmt : P12RadixFormat) :
    fmt.condition7Ceiling < fmt.mantissaBound := by
  have hsum := p12_half_add_ceiling fmt
  have hhalf : (0 : ℝ) < fmt.halfRadixFloor := by
    unfold P12RadixFormat.halfRadixFloor
    norm_cast
    have hge := fmt.beta_ge_two
    omega
  linarith

private lemma p12_bound_le_radix_mul_bound_pred (fmt : P12RadixFormat) :
    fmt.mantissaBound ≤ fmt.betaR * (fmt.mantissaBound - 1) := by
  have hb := p12_bound_ge_radix fmt
  have hbeta : (2 : ℝ) ≤ fmt.betaR := by
    unfold P12RadixFormat.betaR
    exact_mod_cast fmt.beta_ge_two
  nlinarith [mul_nonneg (sub_nonneg.mpr hbeta) (sub_nonneg.mpr hb)]

private lemma p12_rep_abs_le_global_top
    (fmt : P12RadixFormat) {a : ℝ} (ra : P12Representation fmt a) :
    |a| ≤ (fmt.mantissaBound - 1) * fmt.scale fmt.emax := by
  by_cases heq : ra.exponent = fmt.emax
  · have hmInt : |ra.mantissa| ≤ (fmt.beta ^ fmt.precision : ℕ) - 1 := by
      have hmReal : |(ra.mantissa : ℝ)| < fmt.mantissaBound :=
        abs_lt.mpr ⟨ra.mantissa_lower, ra.mantissa_upper⟩
      have hmCast : (|ra.mantissa| : ℤ) < (fmt.beta ^ fmt.precision : ℕ) := by
        unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at hmReal
        rw [← Int.cast_abs] at hmReal
        exact_mod_cast hmReal
      omega
    have hmReal : |(ra.mantissa : ℝ)| ≤ fmt.mantissaBound - 1 := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      rw [← Int.cast_abs]
      exact_mod_cast hmInt
    calc
      |a| = |(ra.mantissa : ℝ)| * fmt.scale ra.exponent := by
        calc
          |a| = |(ra.mantissa : ℝ) * fmt.scale ra.exponent| :=
            congrArg abs ra.value_eq
          _ = |(ra.mantissa : ℝ)| * fmt.scale ra.exponent := by
            rw [abs_mul, abs_of_pos (p12_scale_pos fmt ra.exponent)]
      _ ≤ (fmt.mantissaBound - 1) * fmt.scale ra.exponent :=
        mul_le_mul_of_nonneg_right hmReal (le_of_lt (p12_scale_pos fmt ra.exponent))
      _ = (fmt.mantissaBound - 1) * fmt.scale fmt.emax := by rw [heq]
  · have helt : ra.exponent < fmt.emax := lt_of_le_of_ne ra.exponent_upper heq
    have hscale : fmt.betaR * fmt.scale ra.exponent ≤ fmt.scale fmt.emax := by
      have hm := p12_scale_mono fmt (Int.add_one_le_of_lt helt)
      rw [p12_scale_succ] at hm
      nlinarith
    have hab := p12_rep_abs_lt_bound_scale fmt ra
    have hbound := p12_bound_le_radix_mul_bound_pred fmt
    have hpred_nonneg : 0 ≤ fmt.mantissaBound - 1 := by
      have hb := p12_bound_ge_radix fmt
      have hbeta : (2 : ℝ) ≤ fmt.betaR := by
        unfold P12RadixFormat.betaR
        exact_mod_cast fmt.beta_ge_two
      linarith
    calc
      |a| ≤ fmt.mantissaBound * fmt.scale ra.exponent := le_of_lt hab
      _ ≤ (fmt.betaR * (fmt.mantissaBound - 1)) *
          fmt.scale ra.exponent :=
        mul_le_mul_of_nonneg_right hbound (le_of_lt (p12_scale_pos fmt ra.exponent))
      _ = (fmt.mantissaBound - 1) *
          (fmt.betaR * fmt.scale ra.exponent) := by ring
      _ ≤ (fmt.mantissaBound - 1) * fmt.scale fmt.emax :=
        mul_le_mul_of_nonneg_left hscale hpred_nonneg

private lemma p12_choose_lower_input_representation
    (fmt : P12RadixFormat) {x y : ℝ}
    (rx : P12Representation fmt x) (hy : p12Representable fmt y)
    (hcond : |y| ≤ fmt.condition7Ceiling * fmt.scale rx.exponent) :
    ∃ ry : P12Representation fmt y, ry.exponent ≤ rx.exponent := by
  rcases hy with ⟨ry⟩
  by_cases hey : ry.exponent ≤ rx.exponent
  · exact ⟨ry, hey⟩
  · have her : rx.exponent ≤ ry.exponent := by omega
    obtain ⟨k, hk⟩ :=
      p12_value_integer_at_lower_exponent fmt ry rx.exponent her
    have hylt : |y| < fmt.mantissaBound * fmt.scale rx.exponent := by
      have hs := p12_scale_pos fmt rx.exponent
      have hc := p12_ceiling_lt_bound fmt
      nlinarith
    have hspos := p12_scale_pos fmt rx.exponent
    have hkabs : |(k : ℝ)| < fmt.mantissaBound := by
      rw [hk, abs_mul, abs_of_pos hspos] at hylt
      nlinarith
    refine ⟨⟨k, rx.exponent, (abs_lt.mp hkabs).1, (abs_lt.mp hkabs).2,
      rx.exponent_lower, rx.exponent_upper, hk⟩, le_rfl⟩

private lemma p12_zero_representable (fmt : P12RadixFormat) :
    p12Representable fmt 0 := by
  refine ⟨⟨0, fmt.emin, ?_, ?_, le_rfl, fmt.emin_le_emax, ?_⟩⟩
  · have hBpos : (0 : ℝ) < fmt.mantissaBound := by
      have hb := p12_bound_ge_radix fmt
      have hbeta : (0 : ℝ) < fmt.betaR := by
        unfold P12RadixFormat.betaR
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)
      linarith
    simpa using (neg_lt_zero.mpr hBpos)
  · have hBpos : (0 : ℝ) < fmt.mantissaBound := by
      have hb := p12_bound_ge_radix fmt
      have hbeta : (0 : ℝ) < fmt.betaR := by
        unfold P12RadixFormat.betaR
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)
      linarith
    simpa using hBpos
  · simp

private lemma p12_sum_representable_of_bound
    (fmt : P12RadixFormat) {x y : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (heyx : ry.exponent ≤ rx.exponent) (heymax : ry.exponent < fmt.emax)
    (hsum : |x + y| ≤ fmt.mantissaBound * fmt.scale ry.exponent) :
    p12Representable fmt (x + y) := by
  obtain ⟨kx, hkx⟩ := p12_value_integer_at_lower_exponent fmt rx
    ry.exponent heyx
  have hxy : x + y = (kx + ry.mantissa : ℤ) * fmt.scale ry.exponent := by
    calc
      x + y = (kx : ℝ) * fmt.scale ry.exponent + y := by rw [hkx]
      _ = (kx : ℝ) * fmt.scale ry.exponent +
          (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
            exact congrArg ((kx : ℝ) * fmt.scale ry.exponent + ·) ry.value_eq
      _ = (kx + ry.mantissa : ℤ) * fmt.scale ry.exponent := by
        push_cast
        ring
  exact p12_representable_of_integer_multiple_le fmt ry.exponent
    ry.exponent_lower heymax (kx + ry.mantissa) hxy hsum

private lemma p12_near_multiple_mantissa_lt
    (b p : ℕ) (hp : 0 < p) (hb : 2 ≤ b)
    (mx my q : ℤ)
    (hmxlo : -(b ^ p : ℕ) < mx) (hmxhi : mx < (b ^ p : ℕ))
    (hmylo : -(b ^ p : ℕ) < my) (hmyhi : my < (b ^ p : ℕ))
    (hnear : |mx + my - q * (b : ℤ)| ≤ (b / 2 : ℕ)) :
    |q| < (b ^ p : ℕ) := by
  let B : ℤ := (b ^ p : ℕ)
  let H : ℤ := (b / 2 : ℕ)
  have hBge : (b : ℤ) ≤ B := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hp)
    simp only [B, pow_succ]
    norm_cast
    have hbpos : 0 < b := by omega
    nlinarith [pow_pos hbpos j, show 1 ≤ b ^ j by exact one_le_pow₀ (by omega)]
  have hH : 2 * H ≤ (b : ℤ) := by
    dsimp [H]
    omega
  have hmxlo' : -B + 1 ≤ mx := by simpa [B] using hmxlo
  have hmxhi' : mx ≤ B - 1 := by simpa [B] using hmxhi
  have hmylo' : -B + 1 ≤ my := by simpa [B] using hmylo
  have hmyhi' : my ≤ B - 1 := by simpa [B] using hmyhi
  have hnlo : -2 * B + 2 ≤ mx + my := by omega
  have hnhi : mx + my ≤ 2 * B - 2 := by omega
  have hnear' : -H ≤ mx + my - q * (b : ℤ) ∧
      mx + my - q * (b : ℤ) ≤ H := by
    simpa [H] using (abs_le.mp hnear)
  rw [abs_lt]
  constructor
  · by_contra hq
    have hq' : q ≤ -B := by omega
    have hmul : q * (b : ℤ) ≤ (-B) * b := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ (-B) - q by omega)
        (show (0 : ℤ) ≤ b by omega)]
    have hgap : H < (b : ℤ) * B - 2 * B + 2 := by
      have hbm2 : 0 ≤ (b : ℤ) - 2 := by omega
      have hprod : ((b : ℤ) - 2) * b ≤ ((b : ℤ) - 2) * B := by
        exact mul_le_mul_of_nonneg_left hBge hbm2
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ b by omega)
        (show (0 : ℤ) ≤ (b : ℤ) - 2 by omega)]
    nlinarith
  · by_contra hq
    have hq' : B ≤ q := by omega
    have hmul : B * (b : ℤ) ≤ q * b := by
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ q - B by omega)
        (show (0 : ℤ) ≤ b by omega)]
    have hgap : H < (b : ℤ) * B - 2 * B + 2 := by
      have hbm2 : 0 ≤ (b : ℤ) - 2 := by omega
      have hprod : ((b : ℤ) - 2) * b ≤ ((b : ℤ) - 2) * B := by
        exact mul_le_mul_of_nonneg_left hBge hbm2
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ b by omega)
        (show (0 : ℤ) ≤ (b : ℤ) - 2 by omega)]
    nlinarith

private lemma p12_same_exponent_nearest_error
    (fmt : P12RadixFormat) {x y s : ℝ}
    (rx : P12Representation fmt x) (ry : P12Representation fmt y)
    (hexp : ry.exponent = rx.exponent) (hemax : rx.exponent < fmt.emax)
    (hnearest : p12NearestInFormat fmt (x + y) s) :
    |s - (x + y)| ≤ fmt.halfRadixFloor * fmt.scale rx.exponent := by
  let n : ℤ := rx.mantissa + ry.mantissa
  obtain ⟨q, hqnear⟩ := p12_int_near_radix_multiple n fmt.beta fmt.beta_ge_two
  have hmxlo : -(fmt.beta ^ fmt.precision : ℕ) < rx.mantissa := by
    have := rx.mantissa_lower
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at this
    exact_mod_cast this
  have hmxhi : rx.mantissa < (fmt.beta ^ fmt.precision : ℕ) := by
    have := rx.mantissa_upper
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at this
    exact_mod_cast this
  have hmylo : -(fmt.beta ^ fmt.precision : ℕ) < ry.mantissa := by
    have := ry.mantissa_lower
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at this
    exact_mod_cast this
  have hmyhi : ry.mantissa < (fmt.beta ^ fmt.precision : ℕ) := by
    have := ry.mantissa_upper
    unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR at this
    exact_mod_cast this
  have hqmant : |q| < (fmt.beta ^ fmt.precision : ℕ) :=
    p12_near_multiple_mantissa_lt fmt.beta fmt.precision fmt.precision_pos
      fmt.beta_ge_two rx.mantissa ry.mantissa q hmxlo hmxhi hmylo hmyhi
      (by simpa [n] using hqnear)
  let f : ℝ := (q : ℝ) * fmt.scale (rx.exponent + 1)
  have hfmag : |f| < fmt.mantissaBound * fmt.scale (rx.exponent + 1) := by
    have hqmantR : |(q : ℝ)| < fmt.mantissaBound := by
      unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
      rw [← Int.cast_abs]
      exact_mod_cast hqmant
    dsimp [f]
    rw [abs_mul, abs_of_pos (p12_scale_pos fmt (rx.exponent + 1))]
    exact mul_lt_mul_of_pos_right hqmantR
      (p12_scale_pos fmt (rx.exponent + 1))
  have hfrep : p12Representable fmt f :=
    p12_representable_of_integer_multiple_lt fmt (rx.exponent + 1)
      (Int.le_add_one rx.exponent_lower) (Int.add_one_le_of_lt hemax) q rfl hfmag
  have hxy : x + y = (n : ℝ) * fmt.scale rx.exponent := by
    calc
      x + y = (rx.mantissa : ℝ) * fmt.scale rx.exponent +
          (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
            calc
              x + y = (rx.mantissa : ℝ) * fmt.scale rx.exponent + y := by
                exact congrArg (· + y) rx.value_eq
              _ = (rx.mantissa : ℝ) * fmt.scale rx.exponent +
                  (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
                    exact congrArg
                      ((rx.mantissa : ℝ) * fmt.scale rx.exponent + ·) ry.value_eq
      _ = (n : ℝ) * fmt.scale rx.exponent := by
        rw [hexp]
        simp only [n]
        push_cast
        ring
  have hzf : |(x + y) - f| ≤
      fmt.halfRadixFloor * fmt.scale rx.exponent := by
    have hqnearR : |((n - q * (fmt.beta : ℤ) : ℤ) : ℝ)| ≤
        fmt.halfRadixFloor := by
      unfold P12RadixFormat.halfRadixFloor
      rw [← Int.cast_abs]
      exact Int.cast_le.mpr hqnear
    have hfeq : f = ((q * (fmt.beta : ℤ) : ℤ) : ℝ) *
        fmt.scale rx.exponent := by
      dsimp [f]
      rw [p12_scale_succ]
      unfold P12RadixFormat.betaR
      push_cast
      ring
    rw [hxy, hfeq]
    have hspos := p12_scale_pos fmt rx.exponent
    rw [← sub_mul, ← Int.cast_sub, abs_mul, abs_of_pos hspos]
    exact mul_le_mul_of_nonneg_right hqnearR (le_of_lt hspos)
  calc
    |s - (x + y)| = |(x + y) - s| := abs_sub_comm _ _
    _ ≤ |(x + y) - f| := hnearest.2 f hfrep
    _ ≤ fmt.halfRadixFloor * fmt.scale rx.exponent := hzf

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
  rcases hcondition7 with ⟨rx, hcond⟩
  obtain ⟨ry, heyx⟩ :=
    p12_choose_lower_input_representation fmt rx hy hcond
  rcases run.add.1 with ⟨rs⟩
  have herr : |tr.s - (x + y)| ≤ |y| := by
    calc
      |tr.s - (x + y)| = |(x + y) - tr.s| := abs_sub_comm _ _
      _ ≤ |(x + y) - x| := run.add.2 x hx
      _ = |y| := by congr 1 <;> ring
  have hdiff : ∃ rd : P12Representation fmt (tr.s - x),
      ry.exponent ≤ rd.exponent := by
    by_cases hsumrep : p12Representable fmt (x + y)
    · have hzero : |(x + y) - tr.s| ≤ 0 := by
        simpa using run.add.2 (x + y) hsumrep
      have hs : tr.s = x + y := by
        have : (x + y) - tr.s = 0 := abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
        linarith
      have hd : tr.s - x = y := by rw [hs]; ring
      rw [hd]
      exact ⟨ry, le_rfl⟩
    · by_cases heq : ry.exponent = rx.exponent
      · by_cases hemax : rx.exponent < fmt.emax
        · have hsumlarge : fmt.mantissaBound * fmt.scale rx.exponent <
              |x + y| := by
            by_contra hn
            have hle : |x + y| ≤ fmt.mantissaBound *
                fmt.scale ry.exponent := by simpa [heq] using le_of_not_gt hn
            exact hsumrep (p12_sum_representable_of_bound fmt rx ry heyx
              (by omega) hle)
          have herrHalf := p12_same_exponent_nearest_error fmt rx ry heq hemax run.add
          have hsLower : fmt.condition7Ceiling * fmt.scale rx.exponent < |tr.s| := by
            have htri : |x + y| ≤ |tr.s| + |tr.s - (x + y)| := by
              calc
                |x + y| = |tr.s + ((x + y) - tr.s)| := by congr 1 <;> ring
                _ ≤ |tr.s| + |(x + y) - tr.s| := abs_add_le _ _
                _ = |tr.s| + |tr.s - (x + y)| := by
                  rw [abs_sub_comm (x + y) tr.s]
            have hsumHC := p12_half_add_ceiling fmt
            have hmul : fmt.halfRadixFloor * fmt.scale rx.exponent +
                fmt.condition7Ceiling * fmt.scale rx.exponent =
                fmt.mantissaBound * fmt.scale rx.exponent := by
              rw [← add_mul, hsumHC]
            linarith
          have hes : rx.exponent ≤ rs.exponent := by
            by_contra hn
            have heslt : rs.exponent < rx.exponent := by omega
            have hscale : fmt.betaR * fmt.scale rs.exponent ≤
                fmt.scale rx.exponent := by
              have hm := p12_scale_mono fmt (Int.add_one_le_of_lt heslt)
              rw [p12_scale_succ] at hm
              nlinarith
            have hbound := p12_bound_le_radix_mul_ceiling fmt
            have hceilnonneg : 0 ≤ fmt.condition7Ceiling := by
              unfold P12RadixFormat.condition7Ceiling
              positivity
            have hcompare : fmt.mantissaBound * fmt.scale rs.exponent ≤
                fmt.condition7Ceiling * fmt.scale rx.exponent := by
              calc
                fmt.mantissaBound * fmt.scale rs.exponent ≤
                    (fmt.betaR * fmt.condition7Ceiling) *
                      fmt.scale rs.exponent :=
                  mul_le_mul_of_nonneg_right hbound
                    (le_of_lt (p12_scale_pos fmt rs.exponent))
                _ = fmt.condition7Ceiling *
                    (fmt.betaR * fmt.scale rs.exponent) := by ring
                _ ≤ fmt.condition7Ceiling * fmt.scale rx.exponent :=
                  mul_le_mul_of_nonneg_left hscale hceilnonneg
            have hsbound := p12_rep_abs_lt_bound_scale fmt rs
            linarith
          obtain ⟨ks, hks⟩ :=
            p12_value_integer_at_lower_exponent fmt rs rx.exponent hes
          have hdval : tr.s - x = (ks - rx.mantissa : ℤ) *
              fmt.scale rx.exponent := by
            calc
              tr.s - x = (ks : ℝ) * fmt.scale rx.exponent - x := by rw [hks]
              _ = (ks : ℝ) * fmt.scale rx.exponent -
                  (rx.mantissa : ℝ) * fmt.scale rx.exponent := by
                    exact congrArg ((ks : ℝ) * fmt.scale rx.exponent - ·)
                      rx.value_eq
              _ = (ks - rx.mantissa : ℤ) * fmt.scale rx.exponent := by
                push_cast
                ring
          have hdmag : |tr.s - x| ≤
              fmt.mantissaBound * fmt.scale rx.exponent := by
            have htri : |tr.s - x| ≤ |tr.s - (x + y)| + |y| := by
              calc
                |tr.s - x| = |(tr.s - (x + y)) + y| := by congr 1 <;> ring
                _ ≤ |tr.s - (x + y)| + |y| := abs_add_le _ _
            have hsumHC := p12_half_add_ceiling fmt
            have hmul : fmt.halfRadixFloor * fmt.scale rx.exponent +
                fmt.condition7Ceiling * fmt.scale rx.exponent =
                fmt.mantissaBound * fmt.scale rx.exponent := by
              rw [← add_mul, hsumHC]
            linarith
          obtain ⟨rd, hrd⟩ := p12_representation_of_integer_multiple_le fmt
            rx.exponent rx.exponent_lower hemax (ks - rx.mantissa) hdval hdmag
          exact ⟨rd, by omega⟩
        · have hexmax : rx.exponent = fmt.emax :=
            le_antisymm rx.exponent_upper (le_of_not_gt hemax)
          have hxy : x + y = (rx.mantissa + ry.mantissa : ℤ) *
              fmt.scale rx.exponent := by
            calc
              x + y = (rx.mantissa : ℝ) * fmt.scale rx.exponent + y :=
                congrArg (· + y) rx.value_eq
              _ = (rx.mantissa : ℝ) * fmt.scale rx.exponent +
                  (ry.mantissa : ℝ) * fmt.scale ry.exponent := by
                    exact congrArg
                      ((rx.mantissa : ℝ) * fmt.scale rx.exponent + ·)
                      ry.value_eq
              _ = (rx.mantissa + ry.mantissa : ℤ) *
                  fmt.scale rx.exponent := by
                    rw [heq]
                    push_cast
                    ring
          have hsumlarge : fmt.mantissaBound * fmt.scale rx.exponent ≤
              |x + y| := by
            by_contra hn
            have hlt : |x + y| < fmt.mantissaBound *
                fmt.scale rx.exponent := lt_of_not_ge hn
            have hr := p12_representable_of_integer_multiple_lt fmt rx.exponent
              rx.exponent_lower rx.exponent_upper
              (rx.mantissa + ry.mantissa) hxy hlt
            exact hsumrep hr
          let Bn : ℕ := fmt.beta ^ fmt.precision
          have hBnpos : 0 < Bn := by
            dsimp [Bn]
            exact pow_pos (lt_of_lt_of_le (by norm_num) fmt.beta_ge_two) _
          let mt : ℤ := (Bn - 1 : ℕ)
          have hmtcast : (mt : ℝ) = fmt.mantissaBound - 1 := by
            simp only [mt]
            rw [Nat.cast_sub (by omega)]
            dsimp [Bn]
            unfold P12RadixFormat.mantissaBound P12RadixFormat.betaR
            norm_cast
          let top : ℝ := (fmt.mantissaBound - 1) * fmt.scale fmt.emax
          have htoppos : 0 < top := by
            have hB := p12_bound_ge_radix fmt
            have hb : (2 : ℝ) ≤ fmt.betaR := by
              unfold P12RadixFormat.betaR
              exact_mod_cast fmt.beta_ge_two
            dsimp [top]
            exact mul_pos (by linarith) (p12_scale_pos fmt fmt.emax)
          have htoplt : top < fmt.mantissaBound * fmt.scale fmt.emax := by
            dsimp [top]
            have hs := p12_scale_pos fmt fmt.emax
            nlinarith
          have rtop : P12Representation fmt top := by
            refine ⟨mt, fmt.emax, ?_, ?_, fmt.emin_le_emax, le_rfl, ?_⟩
            · rw [hmtcast]
              have hB := p12_bound_ge_radix fmt
              have hb : (2 : ℝ) ≤ fmt.betaR := by
                unfold P12RadixFormat.betaR
                exact_mod_cast fmt.beta_ge_two
              linarith
            · rw [hmtcast]
              linarith [p12_bound_pos fmt]
            · dsimp [top]
              rw [hmtcast]
          have rbot : P12Representation fmt (-top) := by
            refine ⟨-mt, fmt.emax, ?_, ?_, fmt.emin_le_emax, le_rfl, ?_⟩
            · rw [Int.cast_neg, hmtcast]
              linarith [p12_bound_pos fmt]
            · rw [Int.cast_neg, hmtcast]
              have hB := p12_bound_ge_radix fmt
              have hb : (2 : ℝ) ≤ fmt.betaR := by
                unfold P12RadixFormat.betaR
                exact_mod_cast fmt.beta_ge_two
              linarith
            · dsimp [top]
              rw [Int.cast_neg, hmtcast]
              ring
          have hsform : tr.s = top ∨ tr.s = -top := by
            have hsGlobal := p12_rep_abs_le_global_top fmt rs
            by_cases hz : 0 ≤ x + y
            · left
              have hzB : fmt.mantissaBound * fmt.scale rx.exponent ≤
                  x + y := by simpa [abs_of_nonneg hz] using hsumlarge
              have htopExp : top = (fmt.mantissaBound - 1) *
                  fmt.scale rx.exponent := by simp [top, hexmax]
              have hsle : tr.s ≤ top :=
                le_trans (le_abs_self tr.s) (by simpa [top] using hsGlobal)
              have hztop : top < x + y := by
                rw [htopExp]
                have hs := p12_scale_pos fmt rx.exponent
                nlinarith
              have hnround := run.add.2 top ⟨rtop⟩
              have hleft : |(x + y) - tr.s| = (x + y) - tr.s := by
                rw [abs_of_nonneg (by linarith)]
              have hright : |(x + y) - top| = (x + y) - top := by
                rw [abs_of_nonneg (by linarith)]
              rw [hleft, hright] at hnround
              linarith
            · right
              have hzneg : x + y < 0 := lt_of_not_ge hz
              have hzB : x + y ≤
                  -(fmt.mantissaBound * fmt.scale rx.exponent) := by
                rw [abs_of_neg hzneg] at hsumlarge
                linarith
              have hbotExp : -top = -(fmt.mantissaBound - 1) *
                  fmt.scale rx.exponent := by simp [top, hexmax]; ring
              have hsge : -top ≤ tr.s := by
                have := neg_le_of_abs_le hsGlobal
                simpa [top] using this
              have hzbot : x + y < -top := by
                rw [hbotExp]
                have hs := p12_scale_pos fmt rx.exponent
                nlinarith
              have hnround := run.add.2 (-top) ⟨rbot⟩
              have hleft : |(x + y) - tr.s| = tr.s - (x + y) := by
                rw [abs_of_nonpos (by linarith)]
                ring
              have hright : |(x + y) - (-top)| = -top - (x + y) := by
                rw [abs_of_nonpos (by linarith)]
                ring
              rw [hleft, hright] at hnround
              linarith
          rcases hsform with hs | hs
          · have hzB : fmt.mantissaBound * fmt.scale rx.exponent ≤
                x + y := by
              by_contra hn
              have hzneg : x + y < 0 := by
                by_contra hz
                rw [abs_of_nonneg (le_of_not_gt hz)] at hsumlarge
                linarith
              rw [abs_of_neg hzneg] at hsumlarge
              have hnround := run.add.2 (-top) ⟨rbot⟩
              rw [hs] at hnround
              have hztop : x + y ≤ -(fmt.mantissaBound *
                  fmt.scale rx.exponent) := by linarith
              have htopE : top < fmt.mantissaBound * fmt.scale rx.exponent := by
                simpa [hexmax] using htoplt
              have hl : |(x + y) - top| = top - (x + y) := by
                rw [abs_of_nonpos (by linarith)]
                ring
              have hr : |(x + y) - (-top)| = -top - (x + y) := by
                rw [abs_of_nonpos (by linarith)]
                ring
              rw [hl, hr] at hnround
              linarith
            have hceil : fmt.condition7Ceiling < fmt.mantissaBound :=
              p12_ceiling_lt_bound fmt
            have hxnonneg : 0 ≤ x := by
              have hyupper : y ≤ fmt.condition7Ceiling *
                  fmt.scale rx.exponent := le_trans (le_abs_self y) hcond
              have hspos := p12_scale_pos fmt rx.exponent
              nlinarith
            have hxabs := p12_rep_abs_lt_bound_scale fmt rx
            have hxupper : x < fmt.mantissaBound * fmt.scale rx.exponent := by
              exact lt_of_le_of_lt (le_abs_self x) hxabs
            have hstop : 0 ≤ tr.s := by rw [hs]; exact le_of_lt htoppos
            have hsupper : tr.s < fmt.mantissaBound * fmt.scale rx.exponent := by
              rw [hs]
              simpa [hexmax] using htoplt
            have hdmag : |tr.s - x| < fmt.mantissaBound *
                fmt.scale rx.exponent := by
              rw [abs_lt]
              constructor <;> linarith
            have hdval : tr.s - x = (mt - rx.mantissa : ℤ) *
                fmt.scale rx.exponent := by
              rw [hs]
              calc
                top - x = (mt : ℝ) * fmt.scale rx.exponent - x := by
                  dsimp [top]
                  rw [hexmax, hmtcast]
                _ = (mt : ℝ) * fmt.scale rx.exponent -
                    (rx.mantissa : ℝ) * fmt.scale rx.exponent := by
                      exact congrArg ((mt : ℝ) * fmt.scale rx.exponent - ·)
                        rx.value_eq
                _ = (mt - rx.mantissa : ℤ) * fmt.scale rx.exponent := by
                  push_cast
                  ring
            obtain ⟨rd, hrdeq⟩ := p12_representation_of_integer_multiple_lt fmt
              rx.exponent rx.exponent_lower rx.exponent_upper
              (mt - rx.mantissa) hdval hdmag
            exact ⟨rd, by omega⟩
          · have hzB : x + y ≤
                -(fmt.mantissaBound * fmt.scale rx.exponent) := by
              by_contra hn
              have hzpos : 0 ≤ x + y := by
                by_contra hz
                rw [abs_of_neg (lt_of_not_ge hz)] at hsumlarge
                linarith
              rw [abs_of_nonneg hzpos] at hsumlarge
              have hnround := run.add.2 top ⟨rtop⟩
              rw [hs] at hnround
              have htopE : top < fmt.mantissaBound * fmt.scale rx.exponent := by
                simpa [hexmax] using htoplt
              have hl : |(x + y) - (-top)| = (x + y) + top := by
                rw [abs_of_nonneg (by linarith)]
                ring
              have hr : |(x + y) - top| = (x + y) - top := by
                rw [abs_of_nonneg (by linarith)]
              rw [hl, hr] at hnround
              linarith
            have hceil : fmt.condition7Ceiling < fmt.mantissaBound :=
              p12_ceiling_lt_bound fmt
            have hxnonpos : x ≤ 0 := by
              have hylower : -(fmt.condition7Ceiling * fmt.scale rx.exponent) ≤ y := by
                have := neg_le_of_abs_le hcond
                simpa [abs_of_pos (p12_scale_pos fmt rx.exponent)] using this
              have hspos := p12_scale_pos fmt rx.exponent
              nlinarith
            have hxabs := p12_rep_abs_lt_bound_scale fmt rx
            have hxlower : -(fmt.mantissaBound * fmt.scale rx.exponent) < x :=
              neg_lt_of_abs_lt hxabs
            have hsnonpos : tr.s ≤ 0 := by rw [hs]; linarith [htoppos]
            have hslower : -(fmt.mantissaBound * fmt.scale rx.exponent) <
                tr.s := by
              rw [hs]
              have htopE : top < fmt.mantissaBound * fmt.scale rx.exponent := by
                simpa [hexmax] using htoplt
              linarith
            have hdmag : |tr.s - x| < fmt.mantissaBound *
                fmt.scale rx.exponent := by
              rw [abs_lt]
              constructor <;> linarith
            have hdval : tr.s - x = (-mt - rx.mantissa : ℤ) *
                fmt.scale rx.exponent := by
              rw [hs]
              calc
                -top - x = ((-mt : ℤ) : ℝ) * fmt.scale rx.exponent - x := by
                  dsimp [top]
                  rw [Int.cast_neg, hexmax, hmtcast]
                  ring
                _ = ((-mt : ℤ) : ℝ) * fmt.scale rx.exponent -
                    (rx.mantissa : ℝ) * fmt.scale rx.exponent := by
                      exact congrArg
                        (((-mt : ℤ) : ℝ) * fmt.scale rx.exponent - ·)
                        rx.value_eq
                _ = (-mt - rx.mantissa : ℤ) * fmt.scale rx.exponent := by
                  push_cast
                  ring
            obtain ⟨rd, hrdeq⟩ := p12_representation_of_integer_multiple_lt fmt
              rx.exponent rx.exponent_lower rx.exponent_upper
              (-mt - rx.mantissa) hdval hdmag
            exact ⟨rd, by omega⟩
      · have heylt : ry.exponent < rx.exponent := by omega
        have heymax : ry.exponent < fmt.emax :=
          lt_of_lt_of_le heylt rx.exponent_upper
        have hsumlarge : fmt.mantissaBound * fmt.scale ry.exponent <
            |x + y| := by
          by_contra hn
          exact hsumrep (p12_sum_representable_of_bound fmt rx ry heyx heymax
            (le_of_not_gt hn))
        have hes : ry.exponent < rs.exponent := by
          by_contra hn
          have hesle : rs.exponent ≤ ry.exponent := by omega
          have hsabs : |tr.s| < fmt.mantissaBound * fmt.scale ry.exponent := by
            have hrs := p12_rep_abs_lt_bound_scale fmt rs
            have hscale := p12_scale_mono fmt hesle
            have hBnonneg : 0 ≤ fmt.mantissaBound :=
              le_of_lt (p12_bound_pos fmt)
            exact lt_of_lt_of_le hrs
              (mul_le_mul_of_nonneg_left hscale hBnonneg)
          by_cases hz : 0 ≤ x + y
          · have hzlarge : fmt.mantissaBound * fmt.scale ry.exponent < x + y := by
              rw [abs_of_nonneg hz] at hsumlarge
              exact hsumlarge
            rcases p12_boundary_representable fmt ry.exponent
                ry.exponent_lower heymax 1 (Or.inl rfl) with ⟨rf, _⟩
            have hf : p12Representable fmt
                (fmt.mantissaBound * fmt.scale ry.exponent) := by
              exact ⟨by simpa using rf⟩
            have hnround := run.add.2
              (fmt.mantissaBound * fmt.scale ry.exponent) hf
            have hslt : tr.s < fmt.mantissaBound * fmt.scale ry.exponent :=
              lt_of_le_of_lt (le_abs_self tr.s) hsabs
            have hleft : |(x + y) - tr.s| = (x + y) - tr.s :=
              abs_of_nonneg (by linarith)
            have hright : |(x + y) -
                fmt.mantissaBound * fmt.scale ry.exponent| =
                (x + y) - fmt.mantissaBound * fmt.scale ry.exponent :=
              abs_of_nonneg (by linarith)
            rw [hleft, hright] at hnround
            linarith
          · have hzneg : x + y < 0 := lt_of_not_ge hz
            have hzlarge : x + y <
                -(fmt.mantissaBound * fmt.scale ry.exponent) := by
              rw [abs_of_neg hzneg] at hsumlarge
              linarith
            rcases p12_boundary_representable fmt ry.exponent
                ry.exponent_lower heymax (-1) (Or.inr rfl) with ⟨rf, _⟩
            have hf : p12Representable fmt
                (-(fmt.mantissaBound * fmt.scale ry.exponent)) := by
              refine ⟨?_⟩
              simpa only [Int.cast_neg, Int.cast_one, neg_mul, one_mul] using rf
            have hnround := run.add.2
              (-(fmt.mantissaBound * fmt.scale ry.exponent)) hf
            have hsneg : -(fmt.mantissaBound * fmt.scale ry.exponent) < tr.s := by
              have := neg_lt_of_abs_lt hsabs
              exact this
            have hleft : |(x + y) - tr.s| = tr.s - (x + y) := by
              rw [abs_of_nonpos (by linarith [lt_trans hzlarge hsneg])]
              ring
            have hright : |(x + y) -
                (-(fmt.mantissaBound * fmt.scale ry.exponent))| =
                -(fmt.mantissaBound * fmt.scale ry.exponent) - (x + y) := by
              rw [abs_of_nonpos (by linarith)]
              ring
            rw [hleft, hright] at hnround
            linarith
        let qexp : ℤ := min rs.exponent rx.exponent
        have heyq : ry.exponent < qexp := by
          exact lt_min hes heylt
        have hqrs : qexp ≤ rs.exponent := min_le_left _ _
        have hqrx : qexp ≤ rx.exponent := min_le_right _ _
        obtain ⟨ks, hks⟩ :=
          p12_value_integer_at_lower_exponent fmt rs qexp hqrs
        obtain ⟨kx, hkx⟩ :=
          p12_value_integer_at_lower_exponent fmt rx qexp hqrx
        have hdval : tr.s - x = (ks - kx : ℤ) * fmt.scale qexp := by
          rw [hks, hkx]
          push_cast
          ring
        have hdtri : |tr.s - x| ≤ |tr.s - (x + y)| + |y| := by
          calc
            |tr.s - x| = |(tr.s - (x + y)) + y| := by congr 1 <;> ring
            _ ≤ |tr.s - (x + y)| + |y| := abs_add_le _ _
        have hybound := p12_rep_abs_lt_bound_scale fmt ry
        have hdsmall : |tr.s - x| <
            2 * (fmt.mantissaBound * fmt.scale ry.exponent) := by
          linarith
        have hscale : fmt.betaR * fmt.scale ry.exponent ≤
            fmt.scale qexp := by
          have hm := p12_scale_mono fmt (Int.add_one_le_of_lt heyq)
          rw [p12_scale_succ] at hm
          nlinarith
        have hbeta : (2 : ℝ) ≤ fmt.betaR := by
          unfold P12RadixFormat.betaR
          exact_mod_cast fmt.beta_ge_two
        have hBsnonneg : 0 ≤ fmt.mantissaBound *
            fmt.scale ry.exponent :=
          mul_nonneg (le_of_lt (p12_bound_pos fmt))
            (le_of_lt (p12_scale_pos fmt ry.exponent))
        have hcompare : 2 * (fmt.mantissaBound * fmt.scale ry.exponent) ≤
            fmt.mantissaBound * fmt.scale qexp := by
          calc
            2 * (fmt.mantissaBound * fmt.scale ry.exponent) ≤
                fmt.betaR * (fmt.mantissaBound * fmt.scale ry.exponent) :=
              mul_le_mul_of_nonneg_right hbeta hBsnonneg
            _ = fmt.mantissaBound *
                (fmt.betaR * fmt.scale ry.exponent) := by ring
            _ ≤ fmt.mantissaBound * fmt.scale qexp :=
              mul_le_mul_of_nonneg_left hscale (le_of_lt (p12_bound_pos fmt))
        have hdmag : |tr.s - x| < fmt.mantissaBound * fmt.scale qexp :=
          lt_of_lt_of_le hdsmall hcompare
        obtain ⟨rd, hrdeq⟩ := p12_representation_of_integer_multiple_lt fmt
          qexp (le_trans ry.exponent_lower (le_of_lt heyq))
          (le_trans hqrx rx.exponent_upper) (ks - kx) hdval hdmag
        exact ⟨rd, by omega⟩
  obtain ⟨rd, hryrd⟩ := hdiff
  have ht : tr.t = tr.s - x :=
    p12_faithful_eq_of_representable fmt run.first_sub ⟨rd⟩
  have herrRep : p12Representable fmt (y - (tr.s - x)) := by
    obtain ⟨ky, hky⟩ := p12_value_integer_at_lower_exponent fmt ry
      ry.exponent le_rfl
    obtain ⟨kd, hkd⟩ := p12_value_integer_at_lower_exponent fmt rd
      ry.exponent hryrd
    have hval : y - (tr.s - x) = (ky - kd : ℤ) *
        fmt.scale ry.exponent := by
      calc
        y - (tr.s - x) = (ky : ℝ) * fmt.scale ry.exponent -
            (tr.s - x) := congrArg (· - (tr.s - x)) hky
        _ = (ky : ℝ) * fmt.scale ry.exponent -
            (kd : ℝ) * fmt.scale ry.exponent := by
              exact congrArg ((ky : ℝ) * fmt.scale ry.exponent - ·) hkd
        _ = (ky - kd : ℤ) * fmt.scale ry.exponent := by
          push_cast
          ring
    have hmag : |y - (tr.s - x)| <
        fmt.mantissaBound * fmt.scale ry.exponent := by
      have hybound := p12_rep_abs_lt_bound_scale fmt ry
      have heqerr : y - (tr.s - x) = (x + y) - tr.s := by ring
      rw [heqerr, abs_sub_comm]
      exact lt_of_le_of_lt herr hybound
    exact p12_representable_of_integer_multiple_lt fmt ry.exponent
      ry.exponent_lower ry.exponent_upper (ky - kd) hval hmag
  have he : tr.e = y - tr.t := by
    rw [ht]
    apply p12_faithful_eq_of_representable fmt
    · simpa [ht] using run.second_sub
    · exact herrRep
  refine ⟨ht, he, ?_, herr⟩
  rw [he, ht]
  ring

end HighamBench
