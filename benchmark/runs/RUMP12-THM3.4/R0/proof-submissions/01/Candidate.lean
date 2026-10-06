import Mathlib

namespace HighamBenchCandidate

/-- A binary floating-point format with unbounded upper exponent (the paper's
no-overflow setting). `minExponent` is the exponent of the least positive
subnormal, and `precision` is the number of significand bits. -/
structure BinaryFormat where
  precision : ℕ
  precision_pos : 0 < precision
  minExponent : ℤ
  one_in_normal_range : minExponent ≤ -(precision : ℤ)

/-- Finite values in the binary format, including zero and subnormals. -/
def BinaryFormat.representable (F : BinaryFormat) (x : ℝ) : Prop :=
  ∃ (m : ℤ) (e : ℤ),
    F.minExponent ≤ e ∧ m.natAbs < 2 ^ F.precision ∧
      x = (m : ℝ) * (2 : ℝ) ^ e

/-- Any choice of a closest representable value is a rounding to nearest;
ties may be resolved either way. -/
def BinaryFormat.roundsToNearest (F : BinaryFormat) (x y : ℝ) : Prop :=
  F.representable y ∧
    ∀ z : ℝ, F.representable z → |y - x| ≤ |z - x|

/-- Relative rounding error unit, the gap from 1 to its predecessor. -/
noncomputable def BinaryFormat.unitRoundoff (F : BinaryFormat) : ℝ :=
  (2 : ℝ) ^ (-(F.precision : ℤ))

/-- The successive computed sums of Algorithm 3.1 for a vector of length
`n + 1`. The first sum is the first input; every later addition is rounded. -/
def BinaryFormat.recursiveSum
    (F : BinaryFormat) {n : ℕ} (p s : Fin (n + 1) → ℝ) : Prop :=
  s 0 = p 0 ∧
    ∀ i : Fin n,
      F.roundsToNearest (s (Fin.castSucc i) + p (Fin.succ i))
        (s (Fin.succ i))

private lemma BinaryFormat.rounding_le_abs_addend
    (F : BinaryFormat) {a b y : ℝ}
    (ha : F.representable a) (hy : F.roundsToNearest (a + b) y) :
    |y - (a + b)| ≤ |b| := by
  have h := hy.2 a ha
  have heq : a - (a + b) = -b := by ring
  simpa [heq, abs_neg] using h

private lemma BinaryFormat.representable_pos_nat
    (F : BinaryFormat) {x : ℝ} (hx : 0 < x)
    (hF : F.representable x) :
    ∃ (m : ℕ) (e : ℤ), F.minExponent ≤ e ∧
      0 < m ∧ m < 2 ^ F.precision ∧
      x = (m : ℝ) * (2 : ℝ) ^ e := by
  obtain ⟨m, e, he, hm, rfl⟩ := hF
  have hpow : 0 < (2 : ℝ) ^ e := zpow_pos (by norm_num) _
  have hmposR : (0 : ℝ) < m := (mul_pos_iff_of_pos_right hpow).mp hx
  have hmpos : 0 < m := by exact_mod_cast hmposR
  have hm_nat : m.toNat = m.natAbs := by omega
  refine ⟨m.toNat, e, he, ?_, ?_, ?_⟩
  · omega
  · simpa [hm_nat] using hm
  · have hcast : (m.toNat : ℝ) = m := by exact_mod_cast (Int.toNat_of_nonneg hmpos.le)
    rw [hcast]

private lemma BinaryFormat.normal_rep
    (F : BinaryFormat) {x : ℝ} (hx : 0 < x)
    (hF : F.representable x) :
    ∃ (m : ℕ) (e : ℤ), F.minExponent ≤ e ∧
      0 < m ∧ m < 2 ^ F.precision ∧
      x = (m : ℝ) * (2 : ℝ) ^ e ∧
      (e = F.minExponent ∨ 2 ^ (F.precision - 1) ≤ m) := by
  classical
  obtain ⟨m₀, e₀, he₀, hm₀, hmp₀, hx₀⟩ := F.representable_pos_nat hx hF
  let P : ℕ → Prop := fun d => ∃ m : ℕ,
    0 < m ∧ m < 2 ^ F.precision ∧
      x = (m : ℝ) * (2 : ℝ) ^ (F.minExponent + (d : ℤ))
  have hP : ∃ d, P d := by
    refine ⟨(e₀ - F.minExponent).toNat, m₀, hm₀, hmp₀, ?_⟩
    have heq : F.minExponent + ((e₀ - F.minExponent).toNat : ℤ) = e₀ := by omega
    change x = (m₀ : ℝ) * (2 : ℝ) ^
      (F.minExponent + (((e₀ - F.minExponent).toNat : ℕ) : ℤ))
    rw [heq]
    exact hx₀
  let d := Nat.find hP
  obtain ⟨m, hmpos, hmlt, hmx⟩ := Nat.find_spec hP
  have he : F.minExponent ≤ F.minExponent + (d : ℤ) := by omega
  refine ⟨m, F.minExponent + (d : ℤ), he, hmpos, hmlt, hmx, ?_⟩
  by_cases hd : d = 0
  · left
    simp [hd]
  · right
    by_contra hsmall
    have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    have hhalf : m < 2 ^ (F.precision - 1) := by omega
    have hpow : 2 ^ F.precision = 2 * 2 ^ (F.precision - 1) := by
      conv_lhs => rw [show F.precision = F.precision - 1 + 1 by
        have := F.precision_pos
        omega, pow_succ]
      ring
    have hm2 : 2 * m < 2 ^ F.precision := by omega
    have hbase : F.minExponent + (d : ℤ) =
        F.minExponent + ((d - 1 : ℕ) : ℤ) + 1 := by omega
    have hmx2 : x = ((2 * m : ℕ) : ℝ) *
        (2 : ℝ) ^ (F.minExponent + ((d - 1 : ℕ) : ℤ)) := by
      rw [hbase, zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at hmx
      norm_num at hmx
      push_cast
      nlinarith [hmx]
    have hP2 : P (d - 1) := ⟨2 * m, by omega, hm2, hmx2⟩
    have hmin := Nat.find_min' hP hP2
    omega

private lemma BinaryFormat.representable_nat
    (F : BinaryFormat) (m : ℕ) (e : ℤ)
    (he : F.minExponent ≤ e) (hm : m < 2 ^ F.precision) :
    F.representable ((m : ℝ) * (2 : ℝ) ^ e) := by
  refine ⟨(m : ℤ), e, he, ?_, rfl⟩
  simpa using hm

private lemma BinaryFormat.representable_int
    (F : BinaryFormat) (m : ℤ) (e : ℤ)
    (he : F.minExponent ≤ e) (hm : m.natAbs < 2 ^ F.precision) :
    F.representable ((m : ℝ) * (2 : ℝ) ^ e) :=
  ⟨m, e, he, hm, rfl⟩

private lemma BinaryFormat.neighbors
    (F : BinaryFormat) {y : ℝ} (hypos : 0 < y)
    (hy : F.representable y) :
    ∃ (m : ℕ) (e : ℤ) (h : ℝ),
      F.minExponent ≤ e ∧ 0 < h ∧ h = (2 : ℝ) ^ e ∧ y = (m : ℝ) * h ∧
      F.representable (y - h) ∧ F.representable (y + h) ∧
      (e = F.minExponent ∨ 2 ^ (F.precision - 1) ≤ m) ∧
      (e = F.minExponent ∨ h ≤ 2 * F.unitRoundoff * y) := by
  obtain ⟨m, e, he, hmpos, hmlt, rfl, hnorm⟩ := F.normal_rep hypos hy
  let h : ℝ := (2 : ℝ) ^ e
  have hh : 0 < h := zpow_pos (by norm_num) _
  have hdown : F.representable ((m : ℝ) * h - h) := by
    have hm_sub : m - 1 < 2 ^ F.precision := by omega
    have hrep := F.representable_nat (m - 1) e he hm_sub
    convert hrep using 1
    · have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        have hs : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
          exact_mod_cast (Nat.sub_add_cancel hmpos)
        linarith
      rw [hcast]
      dsimp [h]
      ring
  have hup : F.representable ((m : ℝ) * h + h) := by
    by_cases hlt : m + 1 < 2 ^ F.precision
    · have hrep := F.representable_nat (m + 1) e he hlt
      convert hrep using 1
      · push_cast
        dsimp [h]
        ring
    · have htop : m + 1 = 2 ^ F.precision := by omega
      have he' : F.minExponent ≤ e + (F.precision : ℤ) := by
        have := F.precision_pos
        omega
      have hrep := F.representable_nat 1 (e + (F.precision : ℤ)) he'
        (Nat.one_lt_two_pow (Nat.ne_of_gt F.precision_pos))
      convert hrep using 1
      · have hcast : ((m + 1 : ℕ) : ℝ) = (2 : ℝ) ^ F.precision := by
          exact_mod_cast htop
        rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        norm_num
        dsimp [h]
        rw [← hcast]
        push_cast
        ring
  refine ⟨m, e, h, he, hh, rfl, rfl, hdown, hup, hnorm, ?_⟩
  rcases hnorm with hemin | hnormal
  · left
    exact hemin
  · right
    have hp : (2 : ℝ) ^ F.precision ≤ 2 * (m : ℝ) := by
      have hpow : 2 ^ F.precision = 2 * 2 ^ (F.precision - 1) := by
        conv_lhs => rw [show F.precision = F.precision - 1 + 1 by
          have := F.precision_pos
          omega, pow_succ]
        ring
      have hpowR : (2 : ℝ) ^ F.precision =
          2 * (2 : ℝ) ^ (F.precision - 1) := by exact_mod_cast hpow
      rw [hpowR]
      exact_mod_cast Nat.mul_le_mul_left 2 hnormal
    have hp_pos : 0 < (2 : ℝ) ^ F.precision := pow_pos (by norm_num) _
    have hu : F.unitRoundoff = 1 / (2 : ℝ) ^ F.precision := by
      simp [BinaryFormat.unitRoundoff, zpow_neg, zpow_natCast]
    rw [hu]
    dsimp [h]
    have hcoef : (1 : ℝ) ≤ 2 * (m : ℝ) / 2 ^ F.precision := by
      apply (le_div_iff₀ hp_pos).mpr
      nlinarith [hp]
    convert mul_le_mul_of_nonneg_right hcoef hh.le using 1 <;> ring

private lemma BinaryFormat.representable_grid
    (F : BinaryFormat) {x : ℝ} (hx : F.representable x) :
    ∃ k : ℤ, x = (k : ℝ) * (2 : ℝ) ^ F.minExponent := by
  obtain ⟨m, e, he, -, rfl⟩ := hx
  let d : ℕ := (e - F.minExponent).toNat
  have heq : e = F.minExponent + (d : ℤ) := by
    dsimp [d]
    omega
  refine ⟨m * (2 : ℤ) ^ d, ?_⟩
  rw [heq, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  simp only [zpow_natCast]
  push_cast
  ring

private lemma nearest_half_step {x y h : ℝ} (hh : 0 < h)
    (hlo : |y - x| ≤ |y - h - x|)
    (hhi : |y - x| ≤ |y + h - x|) :
    |y - x| ≤ h / 2 := by
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonneg (by linarith : 0 ≤ y - x)] at *
    rcases le_total x (y - h) with hc | hc
    · rw [abs_of_nonneg (by linarith : 0 ≤ y - h - x)] at hlo
      linarith
    · rw [abs_of_nonpos (by linarith : y - h - x ≤ 0)] at hlo
      linarith
  · rw [abs_of_nonpos (by linarith : y - x ≤ 0)] at *
    rcases le_total x (y + h) with hc | hc
    · rw [abs_of_nonneg (by linarith : 0 ≤ y + h - x)] at hhi
      linarith
    · rw [abs_of_nonpos (by linarith : y + h - x ≤ 0)] at hhi
      linarith

private lemma nearest_lower_half {x y h : ℝ} (hh : 0 < h)
    (hxy : x ≤ y) (hlo : |y - x| ≤ |y - h - x|) :
    y - x ≤ h / 2 := by
  rw [abs_of_nonneg (by linarith : 0 ≤ y - x)] at hlo
  rcases le_total x (y - h) with hc | hc
  · rw [abs_of_nonneg (by linarith : 0 ≤ y - h - x)] at hlo
    linarith
  · rw [abs_of_nonpos (by linarith : y - h - x ≤ 0)] at hlo
    linarith

private lemma nearest_grid_exact {x y h : ℝ} (hh : 0 < h)
    (hlo : |y - x| ≤ |y - h - x|)
    (hhi : |y - x| ≤ |y + h - x|)
    (hx : ∃ k : ℤ, x = (k : ℝ) * h)
    (hy : ∃ k : ℤ, y = (k : ℝ) * h) :
    y = x := by
  obtain ⟨k, rfl⟩ := hx
  obtain ⟨l, rfl⟩ := hy
  by_contra hne
  have hneInt : l - k ≠ 0 := by
    intro hzero
    have : l = k := by omega
    subst l
    exact hne rfl
  have hAbs : (1 : ℝ) ≤ |((l - k : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hneInt
  have hdist : h ≤ |(l : ℝ) * h - (k : ℝ) * h| := by
    have heq : (l : ℝ) * h - (k : ℝ) * h = ((l - k : ℤ) : ℝ) * h := by
      push_cast
      ring
    rw [heq, abs_mul, abs_of_pos hh]
    nlinarith
  have hhalf := nearest_half_step hh hlo hhi
  linarith

private lemma BinaryFormat.rounding_pos_grid
    (F : BinaryFormat) {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) * (2 : ℝ) ^ F.minExponent)
    (hypos : 0 < y) (hy : F.roundsToNearest x y) :
    |y - x| ≤ F.unitRoundoff * y := by
  obtain ⟨m, e, h, he, hh, heh, hey, hbelow, habove, -, hcase⟩ :=
    F.neighbors hypos hy.1
  have hlo := hy.2 (y - h) hbelow
  have hhi := hy.2 (y + h) habove
  rcases hcase with he | hbound
  · subst e
    subst h
    have hygrid := F.representable_grid hy.1
    have hEq := nearest_grid_exact hh hlo hhi hx hygrid
    rw [hEq] at hypos ⊢
    have hu : 0 ≤ F.unitRoundoff := by
      unfold BinaryFormat.unitRoundoff
      positivity
    simpa using mul_nonneg hu hypos.le
  · have hhalf := nearest_half_step hh hlo hhi
    nlinarith

private lemma BinaryFormat.representable_neg
    (F : BinaryFormat) {x : ℝ} (hx : F.representable x) :
    F.representable (-x) := by
  obtain ⟨m, e, he, hm, rfl⟩ := hx
  refine ⟨-m, e, he, ?_, ?_⟩
  · simpa using hm
  · push_cast
    ring

private lemma BinaryFormat.roundsToNearest_neg
    (F : BinaryFormat) {x y : ℝ} (hy : F.roundsToNearest x y) :
    F.roundsToNearest (-x) (-y) := by
  refine ⟨F.representable_neg hy.1, ?_⟩
  intro z hz
  have h := hy.2 (-z) (F.representable_neg hz)
  have hleft : |-y - -x| = |y - x| := by
    have he : -y - -x = -(y - x) := by ring
    rw [he, abs_neg]
  have hright : |-z - x| = |z - -x| := by
    have he : -z - x = -(z - -x) := by ring
    rw [he, abs_neg]
  rw [hleft, ← hright]
  exact h

private lemma BinaryFormat.rounding_add_le_u_abs
    (F : BinaryFormat) {a b y : ℝ}
    (ha : F.representable a) (hb : F.representable b)
    (hy : F.roundsToNearest (a + b) y) :
    |y - (a + b)| ≤ F.unitRoundoff * |y| := by
  obtain ⟨ka, hka⟩ := F.representable_grid ha
  obtain ⟨kb, hkb⟩ := F.representable_grid hb
  have hxgrid : ∃ k : ℤ,
      a + b = (k : ℝ) * (2 : ℝ) ^ F.minExponent := by
    refine ⟨ka + kb, ?_⟩
    rw [hka, hkb]
    push_cast
    ring
  rcases lt_trichotomy y 0 with hneg | hzero | hpos
  · obtain ⟨k, hk⟩ := hxgrid
    have hxneg : ∃ k : ℤ,
        -(a + b) = (k : ℝ) * (2 : ℝ) ^ F.minExponent := by
      refine ⟨-k, ?_⟩
      rw [hk]
      push_cast
      ring
    have h := F.rounding_pos_grid hxneg (by linarith : 0 < -y)
      (F.roundsToNearest_neg hy)
    have he : -y - -(a + b) = -(y - (a + b)) := by ring
    rw [he, abs_neg] at h
    simpa [abs_of_neg hneg] using h
  · subst y
    have hygrid := F.representable_grid hy.1
    have h0 : F.representable (0 : ℝ) := by
      refine ⟨0, F.minExponent, le_rfl, ?_, ?_⟩
      · simpa using Nat.two_pow_pos F.precision
      · simp
    have hstep : F.representable ((2 : ℝ) ^ F.minExponent) := by
      convert F.representable_nat 1 F.minExponent le_rfl
        (Nat.one_lt_two_pow (Nat.ne_of_gt F.precision_pos)) using 1 <;> ring
    have hstep_neg := F.representable_neg hstep
    have hh : 0 < (2 : ℝ) ^ F.minExponent := zpow_pos (by norm_num) _
    have hlo := hy.2 (-(2 : ℝ) ^ F.minExponent) hstep_neg
    have hhi := hy.2 ((2 : ℝ) ^ F.minExponent) hstep
    have heq := nearest_grid_exact hh (by simpa using hlo)
      (by simpa using hhi) hxgrid hygrid
    rw [← heq]
    simp
  · have h := F.rounding_pos_grid hxgrid hpos hy
    simpa [abs_of_pos hpos] using h

private lemma BinaryFormat.power_lower_neighbor
    (F : BinaryFormat) (e : ℤ)
    (he : F.minExponent < e) :
    F.representable
      (((2 : ℝ) ^ (F.precision - 1)) * (2 : ℝ) ^ e -
        (2 : ℝ) ^ (e - 1)) := by
  have he' : F.minExponent ≤ e - 1 := by omega
  have hm : 2 ^ F.precision - 1 < 2 ^ F.precision := by
    have := Nat.two_pow_pos F.precision
    omega
  have hrep := F.representable_nat (2 ^ F.precision - 1) (e - 1) he' hm
  convert hrep using 1
  have hp : 2 ^ F.precision = 2 * 2 ^ (F.precision - 1) := by
    conv_lhs => rw [show F.precision = F.precision - 1 + 1 by
      have := F.precision_pos
      omega, pow_succ]
    ring
  have hpR : (2 : ℝ) ^ F.precision =
      2 * (2 : ℝ) ^ (F.precision - 1) := by exact_mod_cast hp
  have hcast : ((2 ^ F.precision - 1 : ℕ) : ℝ) =
      (2 : ℝ) ^ F.precision - 1 := by
    have hp0 := Nat.two_pow_pos F.precision
    have hs : ((2 ^ F.precision - 1 : ℕ) : ℝ) + 1 =
        (2 : ℝ) ^ F.precision := by
      exact_mod_cast Nat.sub_add_cancel hp0
    linarith
  have hpow : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - 1) * 2 := by
    conv_lhs => rw [show e = e - 1 + 1 by omega,
      zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hcast, hpow, hpR]
  ring

private lemma BinaryFormat.rounding_pos_grid_input
    (F : BinaryFormat) {x y : ℝ}
    (hx : ∃ k : ℤ, x = (k : ℝ) * (2 : ℝ) ^ F.minExponent)
    (hypos : 0 < y) (hy : F.roundsToNearest x y) :
    |y - x| ≤ F.unitRoundoff * |x| := by
  obtain ⟨m, e, h, he, hh, heh, hey, hbelow, habove, hnorm, hcase⟩ :=
    F.neighbors hypos hy.1
  have hlo := hy.2 (y - h) hbelow
  have hhi := hy.2 (y + h) habove
  have hu : 0 ≤ F.unitRoundoff := by
    unfold BinaryFormat.unitRoundoff
    positivity
  rcases hcase with hemin | hbound
  · have heq : h = (2 : ℝ) ^ F.minExponent := by simpa [hemin] using heh
    rw [heq] at hlo hhi hh
    have hEq := nearest_grid_exact hh hlo hhi hx
      (F.representable_grid hy.1)
    rw [hEq]
    simp [mul_nonneg hu]
  · rcases le_total y x with hyx | hxy
    · have hposx : 0 < x := lt_of_lt_of_le hypos hyx
      have hbound' := F.rounding_pos_grid hx hypos hy
      rw [abs_of_pos hposx]
      nlinarith [mul_nonneg hu (sub_nonneg.mpr hyx)]
    · have hhalf := nearest_lower_half hh hxy hlo
      have hdist : |y - x| = y - x := abs_of_nonneg (sub_nonneg.mpr hxy)
      have hp_pos : 0 < (2 : ℝ) ^ F.precision := pow_pos (by norm_num) _
      have hu_eq : F.unitRoundoff = 1 / (2 : ℝ) ^ F.precision := by
        simp [BinaryFormat.unitRoundoff, zpow_neg, zpow_natCast]
      have hpow : 2 ^ F.precision = 2 * 2 ^ (F.precision - 1) := by
        conv_lhs => rw [show F.precision = F.precision - 1 + 1 by
          have := F.precision_pos
          omega, pow_succ]
        ring
      have hpowR : (2 : ℝ) ^ F.precision =
          2 * (2 : ℝ) ^ (F.precision - 1) := by exact_mod_cast hpow
      have hmposR : (0 : ℝ) < m := by
        apply (mul_pos_iff_of_pos_right hh).mp
        simpa [← hey] using hypos
      have hmOne : (1 : ℝ) ≤ m := by
        have hnat : 0 < m := by exact_mod_cast hmposR
        exact_mod_cast hnat
      have hyge : h ≤ y := by
        rw [hey]
        nlinarith [mul_nonneg (sub_nonneg.mpr hmOne) hh.le]
      have hxnonneg : 0 ≤ x := by linarith
      rcases hnorm with hemin | hnormal
      · have heq : h = (2 : ℝ) ^ F.minExponent := by simpa [hemin] using heh
        rw [heq] at hlo hhi hh
        have hEq := nearest_grid_exact hh hlo hhi hx
          (F.representable_grid hy.1)
        rw [hEq]
        simp [mul_nonneg hu]
      · by_cases hmEq : m = 2 ^ (F.precision - 1)
        · by_cases hemin : e = F.minExponent
          · have heq : h = (2 : ℝ) ^ F.minExponent := by simpa [hemin] using heh
            rw [heq] at hlo hhi hh
            have hEq := nearest_grid_exact hh hlo hhi hx
              (F.representable_grid hy.1)
            rw [hEq]
            simp [mul_nonneg hu]
          have hegt : F.minExponent < e := by omega
          have hlower := F.power_lower_neighbor e hegt
          have hhalf_pow : (2 : ℝ) ^ (e - 1) = h / 2 := by
            have heqpow : (2 : ℝ) ^ e = (2 : ℝ) ^ (e - 1) * 2 := by
              conv_lhs => rw [show e = e - 1 + 1 by omega,
                zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
            rw [heh] at *
            linarith
          have hmEqR : (m : ℝ) = (2 : ℝ) ^ (F.precision - 1) := by
            exact_mod_cast hmEq
          rw [← hmEqR, ← heh, ← hey, hhalf_pow] at hlower
          have hlo2 := hy.2 (y - h / 2) hlower
          have hquarter := nearest_lower_half (by linarith : 0 < h / 2) hxy hlo2
          have hP : (2 : ℝ) ^ F.precision = 2 * (m : ℝ) := by
            rw [hpowR, hmEqR]
          have hUy : F.unitRoundoff * y = h / 2 := by
            rw [hu_eq, hey, hP]
            field_simp
          have hu_le : F.unitRoundoff ≤ 1 := by
            rw [hu_eq]
            apply (div_le_iff₀ hp_pos).mpr
            have hpp : (1 : ℝ) ≤ (2 : ℝ) ^ F.precision := by
              exact_mod_cast (Nat.one_lt_two_pow (Nat.ne_of_gt F.precision_pos)).le
            nlinarith
          rw [hdist]
          have hmul := mul_nonneg hu (by linarith : 0 ≤ x - (y - h / 4))
          have hgap := mul_nonneg (by linarith : 0 ≤ 1 - F.unitRoundoff) hh.le
          rw [abs_of_nonneg hxnonneg]
          nlinarith [hmul, hgap, hUy]
        · have hmStr : 2 ^ (F.precision - 1) + 1 ≤ m := by omega
          have hpStr : (2 : ℝ) ^ F.precision ≤ 2 * (m : ℝ) - 1 := by
            have hmStrR : (2 : ℝ) ^ (F.precision - 1) + 1 ≤ (m : ℝ) := by
              exact_mod_cast hmStr
            rw [hpowR]
            linarith
          have hcoef : (1 / 2 : ℝ) ≤
              ((m : ℝ) - 1 / 2) / (2 : ℝ) ^ F.precision := by
            apply (le_div_iff₀ hp_pos).mpr
            nlinarith [hpStr]
          have hmain : h / 2 ≤ F.unitRoundoff * (y - h / 2) := by
            rw [hu_eq, hey]
            convert mul_le_mul_of_nonneg_right hcoef hh.le using 1 <;> ring
          rw [hdist, abs_of_nonneg hxnonneg]
          have hmul := mul_nonneg hu (by linarith : 0 ≤ x - (y - h / 2))
          nlinarith [hmul, hmain]

private lemma BinaryFormat.rounding_add_le_u_abs_input
    (F : BinaryFormat) {a b y : ℝ}
    (ha : F.representable a) (hb : F.representable b)
    (hy : F.roundsToNearest (a + b) y) :
    |y - (a + b)| ≤ F.unitRoundoff * |a + b| := by
  obtain ⟨ka, hka⟩ := F.representable_grid ha
  obtain ⟨kb, hkb⟩ := F.representable_grid hb
  have hxgrid : ∃ k : ℤ,
      a + b = (k : ℝ) * (2 : ℝ) ^ F.minExponent := by
    refine ⟨ka + kb, ?_⟩
    rw [hka, hkb]
    push_cast
    ring
  rcases lt_trichotomy y 0 with hneg | hzero | hpos
  · obtain ⟨k, hk⟩ := hxgrid
    have hxneg : ∃ k : ℤ,
        -(a + b) = (k : ℝ) * (2 : ℝ) ^ F.minExponent := by
      refine ⟨-k, ?_⟩
      rw [hk]
      push_cast
      ring
    have h := F.rounding_pos_grid_input hxneg (by linarith : 0 < -y)
      (F.roundsToNearest_neg hy)
    have he : -y - -(a + b) = -(y - (a + b)) := by ring
    rw [he, abs_neg] at h
    simpa only [abs_neg] using h
  · have h := F.rounding_add_le_u_abs ha hb hy
    rw [hzero] at h
    simp only [abs_zero, mul_zero] at h
    have habs : |0 - (a + b)| = 0 := le_antisymm h (abs_nonneg _)
    have he : a + b = 0 := by
      have h' : -b + -a = 0 := by simpa using habs
      linarith
    rw [hzero, he]
    simp
  · exact F.rounding_pos_grid_input hxgrid hpos hy

/-- Rump, Theorem 3.4, equation (3.5), with `n + 1` inputs. -/
theorem target :
    ∀ (F : BinaryFormat) (n : ℕ)
      (p s : Fin (n + 1) → ℝ),
      (∀ i, F.representable (p i)) →
      F.recursiveSum p s →
      |s (Fin.last n) - ∑ i, p i| ≤
        (n : ℝ) * F.unitRoundoff * ∑ i, |p i| := by
  intro F n
  induction n with
  | zero =>
      intro p s hp hs
      have hsum : (∑ i : Fin 1, p i) = p 0 := by simp
      have hlast : (Fin.last 0 : Fin 1) = 0 := rfl
      rw [hlast, hsum, hs.1]
      simp
  | succ n ih =>
      intro p s hp hs
      let p' : Fin (n + 1) → ℝ := fun i => p (Fin.castSucc i)
      let s' : Fin (n + 1) → ℝ := fun i => s (Fin.castSucc i)
      have hp' : ∀ i, F.representable (p' i) := by
        intro i
        exact hp (Fin.castSucc i)
      have hs' : F.recursiveSum p' s' := by
        constructor
        · exact hs.1
        · intro i
          change F.roundsToNearest
            (s (Fin.castSucc (Fin.castSucc i)) +
              p (Fin.castSucc (Fin.succ i)))
            (s (Fin.castSucc (Fin.succ i)))
          have heq1 : Fin.castSucc (Fin.castSucc i) =
              Fin.castSucc (Fin.castSucc i) := rfl
          have heq2 : Fin.castSucc (Fin.succ i) =
              Fin.succ (Fin.castSucc i) := by ext; rfl
          rw [heq2]
          exact hs.2 (Fin.castSucc i)
      have ih' := ih p' s' hp' hs'
      let a : ℝ := s (Fin.castSucc (Fin.last n))
      let b : ℝ := p (Fin.last (n + 1))
      let y : ℝ := s (Fin.last (n + 1))
      let T : ℝ := ∑ i : Fin (n + 1), p (Fin.castSucc i)
      let A : ℝ := ∑ i : Fin (n + 1), |p (Fin.castSucc i)|
      have ha : F.representable a := by
        cases n with
        | zero => simpa [a, hs.1] using hp (0 : Fin 2)
        | succ k =>
            have hi := hs.2 (Fin.castSucc (Fin.last k))
            simpa [a] using hi.1
      have hb : F.representable b := hp _
      have hround : F.roundsToNearest (a + b) y := by
        simpa [a, b, y] using hs.2 (Fin.last n)
      have hsmall := F.rounding_le_abs_addend ha hround
      have hrel := F.rounding_add_le_u_abs_input ha hb hround
      have hT : (∑ i : Fin (n + 2), p i) = T + b := by
        simpa [T, b] using (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => p i))
      have hA : (∑ i : Fin (n + 2), |p i|) = A + |b| := by
        simpa [A, b] using (Fin.sum_univ_castSucc (fun i : Fin (n + 2) => |p i|))
      have hprev : |a - T| ≤ (n : ℝ) * F.unitRoundoff * A := by
        simpa [a, T, A, p', s'] using ih'
      have hAnonneg : 0 ≤ A := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hunonneg : 0 ≤ F.unitRoundoff := by
        unfold BinaryFormat.unitRoundoff
        positivity
      have hnnonneg : (0 : ℝ) ≤ n := by positivity
      have hsplit : |y - (T + b)| ≤ |y - (a + b)| + |a - T| := by
        have he : y - (T + b) = (y - (a + b)) + (a - T) := by ring
        rw [he]
        exact abs_add_le _ _
      rw [hT, hA]
      change |y - (T + b)| ≤
        ((n + 1 : ℕ) : ℝ) * F.unitRoundoff * (A + |b|)
      by_cases hcase : |b| ≤ F.unitRoundoff * A
      · calc
          |y - (T + b)| ≤ |y - (a + b)| + |a - T| := hsplit
          _ ≤ |b| + (n : ℝ) * F.unitRoundoff * A := add_le_add hsmall hprev
          _ ≤ ((n + 1 : ℕ) : ℝ) * F.unitRoundoff * (A + |b|) := by
            push_cast
            have hcoef : 0 ≤ ((n : ℝ) + 1) * F.unitRoundoff := by positivity
            have hprod := mul_nonneg hcoef (abs_nonneg b)
            nlinarith [hcase, hprod]
      · have hlarge : F.unitRoundoff * A < |b| := lt_of_not_ge hcase
        have habs : |a + b| ≤ |a - T| + (A + |b|) := by
          have he : a + b = (a - T) + (T + b) := by ring
          rw [he]
          have hsumabs : |T| ≤ A := by
            simpa [T, A] using
              (Finset.abs_sum_le_sum_abs (s := Finset.univ)
                (f := fun i : Fin (n + 1) => p (Fin.castSucc i)))
          calc
            |(a - T) + (T + b)| ≤ |a - T| + |T + b| := abs_add_le _ _
            _ ≤ |a - T| + (|T| + |b|) := by gcongr; exact abs_add_le _ _
            _ ≤ |a - T| + (A + |b|) := by gcongr
        calc
          |y - (T + b)| ≤ |y - (a + b)| + |a - T| := hsplit
          _ ≤ F.unitRoundoff * |a + b| + |a - T| := by gcongr
          _ ≤ F.unitRoundoff * (|a - T| + (A + |b|)) + |a - T| := by
            gcongr
          _ ≤ ((n + 1 : ℕ) : ℝ) * F.unitRoundoff * (A + |b|) := by
            push_cast
            have hDmul := mul_le_mul_of_nonneg_left hprev hunonneg
            have hgap := mul_le_mul_of_nonneg_left hlarge.le
              (mul_nonneg hnnonneg hunonneg)
            nlinarith [hDmul, hgap, hprev]

end HighamBenchCandidate
