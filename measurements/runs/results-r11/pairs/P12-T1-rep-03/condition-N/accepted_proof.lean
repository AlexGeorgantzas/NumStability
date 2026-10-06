import HighamBench.P12Definitions
import Mathlib

namespace HighamBench

private lemma p12_betaR_ne_zero (fmt : P12RadixFormat) : fmt.betaR ≠ 0 := by
  unfold P12RadixFormat.betaR
  apply Nat.cast_ne_zero.mpr
  have hb := fmt.beta_ge_two
  omega

private lemma p12_normalizedValue_succ
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m (e + 1) =
      fmt.normalizedValue negative (m * fmt.beta) e := by
  rw [P12RadixFormat.normalizedValue, P12RadixFormat.normalizedValue]
  rw [show e + 1 - (fmt.precision : ℤ) =
      (e - (fmt.precision : ℤ)) + 1 by omega]
  rw [zpow_add₀ (p12_betaR_ne_zero fmt)]
  simp [P12RadixFormat.betaR]
  ring

private lemma p12_normalizedValue_at_emin
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) :
    fmt.normalizedValue negative m fmt.normalEmin =
      fmt.subnormalValue negative m := by
  simp [P12RadixFormat.normalizedValue, P12RadixFormat.subnormalValue,
    P12RadixFormat.normalEmin]

private lemma p12_finite_normalize_aux
    (fmt : P12RadixFormat) (negative : Bool) :
    ∀ (d m : ℕ),
      fmt.normalEmin + (d : ℤ) < fmt.normalEmax →
      m ≤ fmt.beta ^ fmt.precision →
      p12FiniteSystem fmt
        (fmt.normalizedValue negative m (fmt.normalEmin + (d : ℤ))) := by
  intro d
  induction d with
  | zero =>
      intro m hmax hm
      norm_num at hmax ⊢
      by_cases hmzero : m = 0
      · left
        simp [hmzero, P12RadixFormat.normalizedValue]
      by_cases hsmall : m < fmt.minNormalMantissa
      · right; right
        refine ⟨negative, m, ⟨Nat.pos_of_ne_zero hmzero, hsmall⟩, ?_⟩
        simpa using p12_normalizedValue_at_emin fmt negative m
      · by_cases htop : m < fmt.beta ^ fmt.precision
        · right; left
          refine ⟨negative, m, fmt.normalEmin, ⟨Nat.le_of_not_gt hsmall, htop⟩, ?_, ?_⟩
          · exact ⟨le_rfl, Int.le_of_lt hmax⟩
          · simp
        · have hmeq : m = fmt.beta ^ fmt.precision :=
            Nat.le_antisymm hm (Nat.le_of_not_gt htop)
          right; left
          refine ⟨negative, fmt.beta ^ (fmt.precision - 1), fmt.normalEmin + 1, ?_, ?_, ?_⟩
          · refine ⟨le_rfl, ?_⟩
            apply Nat.pow_lt_pow_right fmt.beta_ge_two
            have hp := fmt.precision_pos
            omega
          · refine ⟨by omega, ?_⟩
            exact Int.add_one_le_iff.mpr hmax
          · rw [hmeq]
            have hp : fmt.precision - 1 + 1 = fmt.precision := by
              have := fmt.precision_pos
              omega
            have hpow : fmt.beta ^ (fmt.precision - 1) * fmt.beta =
                fmt.beta ^ fmt.precision := by
              conv_rhs => rw [← hp]
              rw [pow_succ]
            rw [← hpow]
            exact (p12_normalizedValue_succ fmt negative
              (fmt.beta ^ (fmt.precision - 1)) fmt.normalEmin).symm
  | succ d ih =>
      intro m hmax hm
      norm_num at hmax ⊢
      by_cases hmzero : m = 0
      · left
        simp [hmzero, P12RadixFormat.normalizedValue]
      by_cases hsmall : m < fmt.minNormalMantissa
      · have hmul : m * fmt.beta ≤ fmt.beta ^ fmt.precision := by
          calc
            m * fmt.beta ≤ fmt.minNormalMantissa * fmt.beta :=
              Nat.mul_le_mul_right _ (Nat.le_of_lt hsmall)
            _ = fmt.beta ^ fmt.precision := by
              simp [P12RadixFormat.minNormalMantissa, ← pow_succ]
              congr 1
              have hp := fmt.precision_pos
              omega
        have hprev : fmt.normalEmin + (d : ℤ) < fmt.normalEmax := by omega
        rw [show fmt.normalEmin + ((d : ℤ) + 1) =
          (fmt.normalEmin + (d : ℤ)) + 1 by omega]
        rw [p12_normalizedValue_succ]
        exact ih (m * fmt.beta) hprev hmul
      · by_cases htop : m < fmt.beta ^ fmt.precision
        · right; left
          refine ⟨negative, m, fmt.normalEmin + ((d + 1 : ℕ) : ℤ),
            ⟨Nat.le_of_not_gt hsmall, htop⟩, ?_, rfl⟩
          exact ⟨by omega, Int.le_of_lt hmax⟩
        · have hmeq : m = fmt.beta ^ fmt.precision :=
            Nat.le_antisymm hm (Nat.le_of_not_gt htop)
          right; left
          refine ⟨negative, fmt.beta ^ (fmt.precision - 1),
            fmt.normalEmin + ((d + 1 : ℕ) : ℤ) + 1, ?_, ?_, ?_⟩
          · refine ⟨le_rfl, ?_⟩
            apply Nat.pow_lt_pow_right fmt.beta_ge_two
            have hp := fmt.precision_pos
            omega
          · refine ⟨by omega, ?_⟩
            apply Int.add_one_le_iff.mpr
            simpa using hmax
          · rw [hmeq]
            have hp : fmt.precision - 1 + 1 = fmt.precision := by
              have := fmt.precision_pos
              omega
            have hpow : fmt.beta ^ (fmt.precision - 1) * fmt.beta =
                fmt.beta ^ fmt.precision := by
              conv_rhs => rw [← hp]
              rw [pow_succ]
            rw [← hpow]
            exact (p12_normalizedValue_succ fmt negative
              (fmt.beta ^ (fmt.precision - 1))
              (fmt.normalEmin + ((d + 1 : ℕ) : ℤ))).symm

private lemma p12_finite_normalize
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ)
    (hemin : fmt.normalEmin ≤ e) (hemax : e < fmt.normalEmax)
    (hm : m ≤ fmt.beta ^ fmt.precision) :
    p12FiniteSystem fmt (fmt.normalizedValue negative m e) := by
  let d : ℕ := (e - fmt.normalEmin).toNat
  have hdnonneg : 0 ≤ e - fmt.normalEmin := sub_nonneg.mpr hemin
  have hd : (d : ℤ) = e - fmt.normalEmin := by
    exact Int.toNat_of_nonneg hdnonneg
  have he : fmt.normalEmin + (d : ℤ) = e := by omega
  rw [← he]
  exact p12_finite_normalize_aux fmt negative d m (by simpa [he] using hemax) hm

private def p12_signedNat (negative : Bool) (m : ℕ) : ℤ :=
  if negative then -(m : ℤ) else (m : ℤ)

private lemma p12_normalizedValue_lattice
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e k : ℤ)
    (hk : k ≤ e) :
    fmt.normalizedValue negative m e =
      ((p12_signedNat negative m * fmt.beta ^ (e - k).toNat : ℤ) : ℝ) *
        fmt.betaR ^ (k - (fmt.precision : ℤ)) := by
  have hnonneg : 0 ≤ e - k := sub_nonneg.mpr hk
  have hcast : (((e - k).toNat : ℕ) : ℤ) = e - k :=
    Int.toNat_of_nonneg hnonneg
  have hpow : (((fmt.beta : ℤ) ^ (e - k).toNat : ℤ) : ℝ) =
      fmt.betaR ^ (e - k) := by
    conv_rhs => rw [← hcast, zpow_natCast]
    simp [P12RadixFormat.betaR]
  have hsign : ((p12_signedNat negative m : ℤ) : ℝ) =
      fmt.signValue negative * (m : ℝ) := by
    cases negative <;>
      simp [p12_signedNat, P12RadixFormat.signValue]
  rw [P12RadixFormat.normalizedValue]
  rw [show e - (fmt.precision : ℤ) =
    (e - k) + (k - (fmt.precision : ℤ)) by omega]
  rw [zpow_add₀ (p12_betaR_ne_zero fmt)]
  rw [Int.cast_mul, hsign, hpow]
  ring

private lemma p12_beta_power_split (fmt : P12RadixFormat) (e : ℤ) :
    fmt.betaR ^ e =
      ((fmt.beta ^ fmt.precision : ℕ) : ℝ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
  rw [show e = (fmt.precision : ℤ) +
    (e - (fmt.precision : ℤ)) by omega]
  rw [zpow_add₀ (p12_betaR_ne_zero fmt)]
  simp [P12RadixFormat.betaR]

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  rcases hx with ⟨negativeX, mx, hmx, hex, hxval⟩
  rcases hy with ⟨negativeY, my, hmy, hey, hyval⟩
  let e : ℤ := min ex ey
  have heX : e ≤ ex := min_le_left ex ey
  have heY : e ≤ ey := min_le_right ex ey
  let ax : ℤ :=
    p12_signedNat negativeX mx * (fmt.beta : ℤ) ^ (ex - e).toNat
  let ay : ℤ :=
    p12_signedNat negativeY my * (fmt.beta : ℤ) ^ (ey - e).toNat
  let z : ℤ := ax - ay
  have hxLattice : x = (ax : ℝ) *
      fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    rw [hxval]
    simpa [ax] using
      p12_normalizedValue_lattice fmt negativeX mx ex e heX
  have hyLattice : y = (ay : ℝ) *
      fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    rw [hyval]
    simpa [ay] using
      p12_normalizedValue_lattice fmt negativeY my ey e heY
  have hxy : x - y = (z : ℝ) *
      fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
    rw [hxLattice, hyLattice]
    simp only [z, Int.cast_sub]
    ring
  have hbetaPos : (0 : ℝ) < fmt.betaR := by
    unfold P12RadixFormat.betaR
    exact_mod_cast (show 0 < fmt.beta by
      have hb := fmt.beta_ge_two
      omega)
  have hscalePos : (0 : ℝ) <
      fmt.betaR ^ (e - (fmt.precision : ℤ)) :=
    zpow_pos hbetaPos _
  have hcoeffReal : |(z : ℝ)| ≤
      ((fmt.beta ^ fmt.precision : ℕ) : ℝ) := by
    have hmagnitude := hmag
    rw [show min ex ey = e by rfl] at hmagnitude
    rw [hxy, abs_mul, abs_of_pos hscalePos,
      p12_beta_power_split fmt e] at hmagnitude
    nlinarith
  have hnatAbsReal : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    norm_num [Int.cast_natAbs]
  have hcoeff : z.natAbs ≤ fmt.beta ^ fmt.precision := by
    exact_mod_cast (show ((z.natAbs : ℕ) : ℝ) ≤
      ((fmt.beta ^ fmt.precision : ℕ) : ℝ) by
        simpa [hnatAbsReal] using hcoeffReal)
  have heLower : fmt.normalEmin ≤ e := by
    exact le_min hex.1 hey.1
  have heUpper : e < fmt.normalEmax := by
    simpa [e] using hnoOverflow
  have hexact : p12FiniteSystem fmt (x - y) := by
    by_cases hz : 0 ≤ z
    · have hzReal : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hz
      have hvalue : fmt.normalizedValue false z.natAbs e = x - y := by
        rw [hxy]
        simp [P12RadixFormat.normalizedValue,
          P12RadixFormat.signValue, hnatAbsReal, abs_of_nonneg hzReal]
      have hfinite := p12_finite_normalize fmt false z.natAbs e
        heLower heUpper hcoeff
      rwa [hvalue] at hfinite
    · have hzInt : z < 0 := lt_of_not_ge hz
      have hzReal : (z : ℝ) < 0 := by exact_mod_cast hzInt
      have hvalue : fmt.normalizedValue true z.natAbs e = x - y := by
        rw [hxy]
        simp [P12RadixFormat.normalizedValue,
          P12RadixFormat.signValue, hnatAbsReal, abs_of_neg hzReal]
      have hfinite := p12_finite_normalize fmt true z.natAbs e
        heLower heUpper hcoeff
      rwa [hvalue] at hfinite
  refine ⟨hexact, ?_⟩
  rcases hround with ⟨_hrounded, hfaithful⟩
  rcases lt_trichotomy rounded (x - y) with hlt | heq | hgt
  · exact False.elim (hfaithful (x - y) hexact
      (Or.inl ⟨hlt, le_rfl⟩))
  · exact heq
  · exact False.elim (hfaithful (x - y) hexact
      (Or.inr ⟨le_rfl, hgt⟩))

end HighamBench
