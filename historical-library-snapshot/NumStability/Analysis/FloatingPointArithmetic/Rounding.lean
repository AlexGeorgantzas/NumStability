import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.FloatingPointArithmetic.Format

namespace NumStability

/-!
# Rounding

Extracted without change from FloatingPointArithmetic.
-/

noncomputable section

namespace FloatingPointFormat

theorem normalizedValue_sub_sameSign_sameExponent_eq_aligned
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m e - fmt.normalizedValue negative n e =
      fmt.alignedSameExponentSubtractionValue negative m n e := by
  cases negative <;>
    simp [alignedSameExponentSubtractionValue, normalizedValue, signValue] <;>
    ring
/-- Integer coefficient for same-exponent aligned subtraction. -/
def sameExponentMantissaDiffInt
    (_fmt : FloatingPointFormat) (m n : ℕ) : ℤ :=
  (m : ℤ) - (n : ℤ)
theorem sameExponentMantissaDiffInt_cast
    (fmt : FloatingPointFormat) (m n : ℕ) :
    ((fmt.sameExponentMantissaDiffInt m n : ℤ) : ℝ) =
      (m : ℝ) - (n : ℝ) := by
  simp [sameExponentMantissaDiffInt]
theorem sameExponentMantissaDiffInt_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ}
    (hm : fmt.mantissaInRange m) (hn : fmt.mantissaInRange n) :
    (fmt.sameExponentMantissaDiffInt m n).natAbs < fmt.beta ^ fmt.t := by
  have hmInt : (m : ℤ) < (fmt.beta ^ fmt.t : ℤ) := by
    exact_mod_cast hm
  have hnInt : (n : ℤ) < (fmt.beta ^ fmt.t : ℤ) := by
    exact_mod_cast hn
  have habs :
      |(m : ℤ) - (n : ℤ)| < (fmt.beta ^ fmt.t : ℤ) := by
    rw [abs_lt]
    constructor <;> omega
  have hnatInt :
      (((((m : ℤ) - (n : ℤ)).natAbs : ℕ) : ℤ) <
        (fmt.beta ^ fmt.t : ℤ)) := by
    simpa [Int.natCast_natAbs] using habs
  have hnat : (((m : ℤ) - (n : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
    exact_mod_cast hnatInt
  simpa [sameExponentMantissaDiffInt] using hnat
/-- A selector witness for direct same-exponent renormalization: after shifting
some finite number of base digits from the exponent into the exact integer
mantissa difference, the shifted mantissa is normalized and the shifted exponent
remains inside the finite exponent range. -/
def sameExponentRenormalizationWitness
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) : Prop :=
  ∃ shift : ℕ,
    fmt.exponentInRange (e - (shift : ℤ)) ∧
      fmt.normalizedMantissa
        ((fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift)
/-- A selector witness for the same-exponent branch whose exact difference
shifts all the way down to `emin` and lands in the subnormal interval. -/
def sameExponentSubnormalEndpointWitness
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) : Prop :=
  ∃ shift : ℕ,
    e - (shift : ℤ) = fmt.emin ∧
      (fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift <
        fmt.minNormalMantissa
/-- Finite radix-shift search for a same-exponent integer coefficient.  Within
`q` shifts, a `t`-digit coefficient is either zero, becomes normalized, or is
still below the normalized leading-digit threshold at the endpoint. -/
theorem sameExponent_shift_search
    {fmt : FloatingPointFormat} {a q : ℕ}
    (ha : a < fmt.beta ^ fmt.t) :
    a = 0 ∨
      (∃ shift : ℕ, shift ≤ q ∧
        fmt.normalizedMantissa (a * fmt.beta ^ shift)) ∨
      a * fmt.beta ^ q < fmt.minNormalMantissa := by
  induction q with
  | zero =>
      by_cases ha0 : a = 0
      · exact Or.inl ha0
      · by_cases hmin : fmt.minNormalMantissa ≤ a
        · exact Or.inr (Or.inl ⟨0, le_rfl, by
            simpa [normalizedMantissa] using
              (⟨hmin, ha⟩ : fmt.normalizedMantissa a)⟩)
        · exact Or.inr (Or.inr (by
            simpa using (Nat.lt_of_not_ge hmin)))
  | succ q ih =>
      rcases ih with hzero | hrest
      · exact Or.inl hzero
      rcases hrest with hnorm | hprev_lt
      · rcases hnorm with ⟨shift, hle, hnorm⟩
        exact Or.inr (Or.inl ⟨shift, Nat.le_succ_of_le hle, hnorm⟩)
      · by_cases hnext_lt :
          a * fmt.beta ^ (q + 1) < fmt.minNormalMantissa
        · exact Or.inr (Or.inr hnext_lt)
        · have hnext_ge :
            fmt.minNormalMantissa ≤ a * fmt.beta ^ (q + 1) :=
            Nat.le_of_not_gt hnext_lt
          have hstep :
              a * fmt.beta ^ (q + 1) =
                (a * fmt.beta ^ q) * fmt.beta := by
            rw [pow_succ]
            ring
          have hnext_lt_bound :
              a * fmt.beta ^ (q + 1) < fmt.beta ^ fmt.t := by
            calc
              a * fmt.beta ^ (q + 1) =
                  (a * fmt.beta ^ q) * fmt.beta := hstep
              _ < fmt.minNormalMantissa * fmt.beta :=
                  Nat.mul_lt_mul_of_pos_right hprev_lt
                    (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two)
              _ = fmt.beta ^ fmt.t :=
                  fmt.minNormalMantissa_mul_beta_eq_mantissaBound
          exact Or.inr (Or.inl
            ⟨q + 1, le_rfl, ⟨hnext_ge, hnext_lt_bound⟩⟩)
/-- Generic finite-system theorem for an exact signed integer coefficient with
fewer than `t` radix digits at exponent `e`.  The coefficient either is zero,
renormalizes before leaving the exponent interval, or lands in the shifted
`emin` subnormal endpoint. -/
theorem scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {k : ℤ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hk : k.natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.signValue negative * (k : ℝ) *
        fmt.betaR ^ (e - (fmt.t : ℤ))) := by
  by_cases hkzero : k = 0
  · left
    simp [hkzero]
  let a := k.natAbs
  let q := Int.toNat (e - fmt.emin)
  have ha_pos : 0 < a := by
    exact Nat.pos_of_ne_zero (mt Int.natAbs_eq_zero.mp hkzero)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have ha_lt : a < fmt.beta ^ fmt.t := by
    simpa [a] using hk
  rcases fmt.sameExponent_shift_search (a := a) (q := q) ha_lt with
    hazero | hrest
  · exact False.elim (by
      have : k.natAbs = 0 := by simpa [a] using hazero
      exact hkzero (Int.natAbs_eq_zero.mp this))
  rcases hrest with hnorm | hend
  · rcases hnorm with ⟨shift, hle, hnorm⟩
    have hle_int : (shift : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast hle
    have hex : fmt.exponentInRange (e - (shift : ℤ)) := by
      constructor
      · omega
      · have hshift_nonneg : (0 : ℤ) ≤ (shift : ℤ) := by
          exact_mod_cast Nat.zero_le shift
        have hle_e : e - (shift : ℤ) ≤ e := by omega
        exact le_trans hle_e he.2
    by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inl
          ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inl
          ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inl
          ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inl
          ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
            by simpa [a] using hnorm, hex, by
            rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
  · have hscale_pos :
        0 < k.natAbs * fmt.beta ^ q := by
      exact Nat.mul_pos ha_pos
        (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two))
    have hsub :
        fmt.subnormalMantissa (k.natAbs * fmt.beta ^ q) :=
      ⟨hscale_pos, by simpa [a] using hend⟩
    by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ q, hsub, by
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := q)
              (e := e) hq_endpoint]
            simp [normalizedValue, signValue, hk_abs_real]⟩)
/-- If two normalized-value expressions are aligned on the lower exponent
lattice and their exact difference has magnitude below the next binade, then
the difference is finite representable.  The proof derives the signed integer
coefficient bound from the real magnitude bound and invokes the generic finite
lattice selector; it does not assume any representation of the difference. -/
theorem normalizedValue_sub_orderedExponent_finiteSystem_of_abs_lt_beta_pow
    {fmt : FloatingPointFormat} {negativeX negativeY : Bool}
    {mx my : ℕ} {ex ey : ℤ}
    (hey : fmt.exponentInRange ey)
    (hle : ey ≤ ex)
    (hmag :
      |fmt.normalizedValue negativeX mx ex -
        fmt.normalizedValue negativeY my ey| < fmt.betaR ^ ey) :
    fmt.finiteSystem
      (fmt.normalizedValue negativeX mx ex -
        fmt.normalizedValue negativeY my ey) := by
  let q : ℕ := Int.toNat (ex - ey)
  have hq_cast : ((q : ℕ) : ℤ) = ex - ey := by
    have hnonneg : 0 ≤ ex - ey := sub_nonneg.mpr hle
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : ex - (q : ℤ) = ey := by
    omega
  have hshift :
      fmt.normalizedValue negativeX (mx * fmt.beta ^ q) ey =
        fmt.normalizedValue negativeX mx ex := by
    have h := fmt.normalizedValue_mul_beta_pow_subExponent_eq
      (negative := negativeX) (m := mx) (shift := q) (e := ex)
    rw [hq_endpoint] at h
    exact h
  let k : ℤ :=
    fmt.signedMantissaCoeff negativeX (mx * fmt.beta ^ q) -
      fmt.signedMantissaCoeff negativeY my
  have hrepr :
      fmt.normalizedValue negativeX mx ex -
          fmt.normalizedValue negativeY my ey =
        (k : ℝ) * fmt.betaR ^ (ey - (fmt.t : ℤ)) := by
    rw [← hshift,
      fmt.normalizedValue_eq_signedMantissaCoeff,
      fmt.normalizedValue_eq_signedMantissaCoeff]
    simp [k]
    ring
  let s : ℝ := fmt.betaR ^ (ey - (fmt.t : ℤ))
  have hs : 0 < s := fmt.betaR_zpow_pos _
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ ey = fmt.betaR ^ (fmt.t : ℤ) * s := by
    dsimp [s]
    rw [← zpow_add₀ hbase]
    congr 1
    ring
  have hk_real : |(k : ℝ)| < fmt.betaR ^ (fmt.t : ℤ) := by
    rw [hrepr, abs_mul, abs_of_pos hs, hpow] at hmag
    exact lt_of_mul_lt_mul_right hmag (le_of_lt hs)
  have hk_natabs_cast : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    norm_num [Int.cast_abs]
  have hbeta_cast :
      ((fmt.beta ^ fmt.t : ℕ) : ℝ) = fmt.betaR ^ (fmt.t : ℤ) := by
    simp [betaR]
  have hk_natabs_real :
      ((k.natAbs : ℕ) : ℝ) < ((fmt.beta ^ fmt.t : ℕ) : ℝ) := by
    rw [hk_natabs_cast, hbeta_cast]
    exact hk_real
  have hk : k.natAbs < fmt.beta ^ fmt.t := by
    exact_mod_cast hk_natabs_real
  have hfin := fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
    (negative := false) (k := k) (e := ey) hey hk
  simpa [signValue, hrepr] using hfin
/-- Same-lattice signed scaled-integer subtraction is finite when the integer
coefficient difference has fewer than `t` radix digits.

This is the coefficient-level bridge needed by binary addition roundoff-error
representability proofs: once an exact source value and its rounded endpoint
are represented on the same exponent lattice, the real difference is finite
provided the coefficient gap fits in the finite mantissa range. -/
theorem signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {k l : ℤ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hdiff : (k - l).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.signValue negative * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) -
        fmt.signValue negative * (l : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) := by
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative * ((k - l : ℤ) : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative) (k := k - l) (e := e) he hdiff
  convert hfin using 1
  norm_num
  ring
/-- Same-sign, same-exponent normalized addition stays on the same scaled
integer lattice with coefficient `m+n`.

This is the source-side operand-grid representation needed by the C4.4
roundoff-error proof: before the rounded endpoint is compared to `a+b`, the
exact sum of two aligned same-sign normalized operands has an explicit integer
coefficient on the common exponent lattice. -/
theorem normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m n : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m e +
        fmt.normalizedValue negative n e =
      fmt.signValue negative * ((m + n : ℕ) : ℝ) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_add] <;> ring
/-- The same-sign, same-exponent normalized addition coefficient has at most
one guard digit: `m+n < 2*beta^t`. -/
theorem normalizedMantissa_add_lt_two_mul_mantissaBound
    {fmt : FloatingPointFormat} {m n : ℕ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    m + n < 2 * fmt.beta ^ fmt.t := by
  have hsum : m + n < fmt.beta ^ fmt.t + fmt.beta ^ fmt.t :=
    Nat.add_lt_add hm.2 hn.2
  simpa [two_mul] using hsum
/-- Packaged source-grid form for aligned same-sign normalized addition: the
exact source sum has an explicit signed integer coefficient on the same exponent
lattice, and that coefficient is bounded by the two-operand guard word
`2*beta^t`. -/
theorem normalizedValue_add_sameSign_sameExponent_exists_scaledIntegerCoeff
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    ∃ k : ℤ,
      k.natAbs < 2 * fmt.beta ^ fmt.t ∧
        fmt.normalizedValue negative m e +
            fmt.normalizedValue negative n e =
          fmt.signValue negative * (k : ℝ) *
            fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  refine ⟨((m + n : ℕ) : ℤ), ?_, ?_⟩
  · simpa using
      normalizedMantissa_add_lt_two_mul_mantissaBound
        (fmt := fmt) hm hn
  · exact fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger
      negative m n e
/-- If the aligned same-sign normalized addition coefficient already fits in
`t` digits, the exact source sum is finite representable. -/
theorem normalizedValue_add_sameSign_sameExponent_finiteSystem_of_add_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (he : fmt.exponentInRange e)
    (hadd : m + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e +
        fmt.normalizedValue negative n e) := by
  rw [fmt.normalizedValue_add_sameSign_sameExponent_eq_scaledInteger]
  exact
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative) (k := ((m + n : ℕ) : ℤ)) (e := e) he
      (by simpa using hadd)
/-- Same-sign normalized operands with ordered exponents add exactly when the
higher-exponent operand is shifted onto the lower exponent lattice and the
resulting coefficient still fits in `t` radix digits. -/
theorem normalizedValue_add_sameSign_orderedExponent_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool}
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (_hmHigh : fmt.normalizedMantissa mHigh)
    (_hmLow : fmt.normalizedMantissa mLow)
    (_heHigh : fmt.exponentInRange eHigh)
    (heLow : fmt.exponentInRange eLow)
    (hle : eLow ≤ eHigh)
    (hcoeff :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative mHigh eHigh +
        fmt.normalizedValue negative mLow eLow) := by
  let q := Int.toNat (eHigh - eLow)
  have hq_cast : ((q : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : eHigh - (q : ℤ) = eLow := by
    omega
  have hshift :
      fmt.normalizedValue negative (mHigh * fmt.beta ^ q) eLow =
        fmt.normalizedValue negative mHigh eHigh := by
    have h :=
      fmt.normalizedValue_mul_beta_pow_subExponent_eq
        (negative := negative) (m := mHigh) (shift := q) (e := eHigh)
    rw [hq_endpoint] at h
    exact h
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative *
          ((((mHigh * fmt.beta ^ q + mLow : ℕ) : ℤ) : ℝ)) *
          fmt.betaR ^ (eLow - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := ((mHigh * fmt.beta ^ q + mLow : ℕ) : ℤ))
      (e := eLow)
      heLow
      (by simpa [q] using hcoeff)
  convert hfin using 1
  rw [← hshift]
  simp [normalizedValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring
/-- Raising the normalized exponent by one shifts one base digit into the
integer coefficient on the original exponent lattice. -/
theorem normalizedValue_succExponent_eq_beta_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m (e + 1) =
      fmt.signValue negative * (((fmt.beta * m : ℕ) : ℝ)) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  have hpow :
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
        fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    calc
      fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ ((e - (fmt.t : ℤ)) + 1) := by
        congr 1
        ring
      _ = fmt.betaR ^ (e - (fmt.t : ℤ)) * fmt.betaR ^ (1 : ℤ) := by
        rw [zpow_add₀ hbase]
      _ = fmt.betaR * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
        rw [zpow_one]
        ring
  cases negative <;>
    simp [normalizedValue, signValue, Nat.cast_mul, hpow] <;>
    rw [show ((fmt.beta : ℝ) = fmt.betaR) by rfl] <;> ring
/-- Raising the normalized exponent by two shifts two base digits into the
integer coefficient on the original exponent lattice. -/
theorem normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m (e + 2) =
      fmt.signValue negative * (((m * fmt.beta ^ 2 : ℕ) : ℝ)) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have h := fmt.normalizedValue_mul_beta_pow_subExponent_eq
    (negative := negative) (m := m) (shift := 2) (e := e + 2)
  have hexp : (e + 2 - (2 : ℤ)) = e := by ring
  have hleft :
      fmt.normalizedValue negative (m * fmt.beta ^ 2) e =
        fmt.normalizedValue negative m (e + 2) := by
    simpa [hexp] using h
  rw [← hleft]
  rfl
/-- Raising the normalized exponent by `d` shifts `d` base digits into the
integer coefficient on the original exponent lattice. -/
theorem normalizedValue_add_natExponent_eq_beta_pow_scaledInteger
    (fmt : FloatingPointFormat) (negative : Bool) (m d : ℕ) (e : ℤ) :
    fmt.normalizedValue negative m (e + (d : ℤ)) =
      fmt.signValue negative * (((fmt.beta ^ d * m : ℕ) : ℝ)) *
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have h := fmt.normalizedValue_mul_beta_pow_subExponent_eq
    (negative := negative) (m := m) (shift := d) (e := e + (d : ℤ))
  have hexp : e + (d : ℤ) - (d : ℤ) = e := by
    ring
  have hcomm : m * fmt.beta ^ d = fmt.beta ^ d * m := by
    exact Nat.mul_comm m (fmt.beta ^ d)
  have hleft :
      fmt.normalizedValue negative (fmt.beta ^ d * m) e =
        fmt.normalizedValue negative m (e + (d : ℤ)) := by
    simpa [hexp, hcomm] using h
  rw [← hleft]
  rfl
/-- Positive binary guard-word source coefficients lie between the quotient
endpoints at the next exponent.

If `k = beta*q+r` with `r < beta`, then the source value
`k*beta^(e-t)` is between the normalized values with mantissas `q` and
`q+1` at exponent `e+1`.  This is the concrete bracket-construction step for
the aligned positive C4.4 guard-word branch. -/
theorem binaryGuardSource_between_sameExponentEndpoints_positive
    {fmt : FloatingPointFormat} {k q r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue false q (e + 1) ≤
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue false (q + 1) (e + 1) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * q ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hk_upper_nat : k ≤ fmt.beta * (q + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.le_of_lt hr) (fmt.beta * q)
  have hk_lower_real : (((fmt.beta * q : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤ (((fmt.beta * (q + 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' : (fmt.beta : ℝ) * (q : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' : (k : ℝ) ≤ (fmt.beta : ℝ) * ((q : ℝ) + 1) := by
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
/-- Positive multi-guard source coefficients lie between quotient endpoints at
the shifted exponent.

If `k = beta^d*q+r` with `r < beta^d`, then the source value
`k*beta^(e-t)` is between normalized values with mantissas `q` and `q+1` at
exponent `e+d`. -/
theorem multiGuardSource_between_sameExponentEndpoints_positive
    {fmt : FloatingPointFormat} {k q r d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d) :
    fmt.normalizedValue false q (e + (d : ℤ)) ≤
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue false (q + 1) (e + (d : ℤ)) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta ^ d * q ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hk_upper_nat : k ≤ fmt.beta ^ d * (q + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.le_of_lt hr) (fmt.beta ^ d * q)
  have hk_lower_real : (((fmt.beta ^ d * q : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤ (((fmt.beta ^ d * (q + 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' : (fmt.beta ^ d : ℝ) * (q : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.beta ^ d : ℝ) * ((q : ℝ) + 1) := by
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
/-- Negative binary guard-word source coefficients lie between the reversed
quotient endpoints at the next exponent.

For negative values the real-order bracket is reversed: the left endpoint has
mantissa `q+1`, and the right endpoint has mantissa `q`. -/
theorem binaryGuardSource_between_sameExponentEndpoints_negative
    {fmt : FloatingPointFormat} {k q r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue true (q + 1) (e + 1) ≤
        fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue true q (e + 1) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * q ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hk_upper_nat : k ≤ fmt.beta * (q + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.le_of_lt hr) (fmt.beta * q)
  have hk_lower_real : (((fmt.beta * q : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤ (((fmt.beta * (q + 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' : (fmt.beta : ℝ) * (q : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' : (k : ℝ) ≤ (fmt.beta : ℝ) * ((q : ℝ) + 1) := by
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
/-- Negative multi-guard source coefficients lie between the reversed quotient
endpoints at the shifted exponent.

For negative values the real-order bracket is reversed: the left endpoint has
mantissa `q+1`, and the right endpoint has mantissa `q`. -/
theorem multiGuardSource_between_sameExponentEndpoints_negative
    {fmt : FloatingPointFormat} {k q r d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d) :
    fmt.normalizedValue true (q + 1) (e + (d : ℤ)) ≤
        fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue true q (e + (d : ℤ)) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta ^ d * q ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hk_upper_nat : k ≤ fmt.beta ^ d * (q + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_le_add_left (Nat.le_of_lt hr) (fmt.beta ^ d * q)
  have hk_lower_real : (((fmt.beta ^ d * q : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤ (((fmt.beta ^ d * (q + 1) : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' : (fmt.beta ^ d : ℝ) * (q : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.beta ^ d : ℝ) * ((q : ℝ) + 1) := by
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
      using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
/-- Positive binary guard-word source coefficients at the mantissa ceiling lie
between the exponent-boundary endpoints.

This is the boundary counterpart of
`binaryGuardSource_between_sameExponentEndpoints_positive`: when the lower
quotient is `maxNormalMantissa`, the upper endpoint is the smallest mantissa at
the next exponent. -/
theorem binaryGuardSource_between_boundaryEndpoints_positive
    {fmt : FloatingPointFormat} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue false fmt.maxNormalMantissa (e + 1) ≤
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue false fmt.minNormalMantissa (e + 2) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * fmt.maxNormalMantissa ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta * (fmt.maxNormalMantissa + 1) =
        fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [hmaxsucc_eq]
    ring
  have hk_upper_lt : k < fmt.beta * (fmt.maxNormalMantissa + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_lt_add_left hr (fmt.beta * fmt.maxNormalMantissa)
  have hk_upper_nat : k ≤ fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [← hupper_coeff]
    exact Nat.le_of_lt hk_upper_lt
  have hk_lower_real : (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) ≤
      (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤
      (((fmt.minNormalMantissa * fmt.beta ^ 2 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' :
      (fmt.beta : ℝ) * (fmt.maxNormalMantissa : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.minNormalMantissa : ℝ) * (fmt.beta : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
  · rw [fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
/-- Negative binary guard-word source coefficients at the mantissa ceiling lie
between the reversed exponent-boundary endpoints. -/
theorem binaryGuardSource_between_boundaryEndpoints_negative
    {fmt : FloatingPointFormat} {k r : ℕ} {e : ℤ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta) :
    fmt.normalizedValue true fmt.minNormalMantissa (e + 2) ≤
        fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue true fmt.maxNormalMantissa (e + 1) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta * fmt.maxNormalMantissa ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta * (fmt.maxNormalMantissa + 1) =
        fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [hmaxsucc_eq]
    ring
  have hk_upper_lt : k < fmt.beta * (fmt.maxNormalMantissa + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_lt_add_left hr (fmt.beta * fmt.maxNormalMantissa)
  have hk_upper_nat : k ≤ fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [← hupper_coeff]
    exact Nat.le_of_lt hk_upper_lt
  have hk_lower_real : (((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℝ)) ≤
      (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real : (k : ℝ) ≤
      (((fmt.minNormalMantissa * fmt.beta ^ 2 : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' :
      (fmt.beta : ℝ) * (fmt.maxNormalMantissa : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.minNormalMantissa : ℝ) * (fmt.beta : ℝ) ^ 2 := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_add_twoExponent_eq_beta_sq_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
  · rw [fmt.normalizedValue_succExponent_eq_beta_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
/-- Positive multi-guard source coefficients at the mantissa ceiling lie between
the shifted exponent-boundary endpoints.

This generalizes the binary boundary bracket from one guard digit to an
arbitrary shift `d`: if `k = beta^d * maxNormalMantissa + r` with
`r < beta^d`, then `k*beta^(e-t)` lies between the largest mantissa at
exponent `e+d` and the smallest mantissa at exponent `e+d+1`. -/
theorem multiGuardSource_between_boundaryEndpoints_positive
    {fmt : FloatingPointFormat} {k r d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d) :
    fmt.normalizedValue false fmt.maxNormalMantissa (e + (d : ℤ)) ≤
        (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      (k : ℝ) * fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue false fmt.minNormalMantissa
          (e + ((d + 1 : ℕ) : ℤ)) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta ^ d * fmt.maxNormalMantissa ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta ^ d * (fmt.maxNormalMantissa + 1) =
        fmt.beta ^ (d + 1) * fmt.minNormalMantissa := by
    rw [hmaxsucc_eq]
    ring
  have hk_upper_lt :
      k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_lt_add_left hr (fmt.beta ^ d * fmt.maxNormalMantissa)
  have hk_upper_nat :
      k ≤ fmt.beta ^ (d + 1) * fmt.minNormalMantissa := by
    rw [← hupper_coeff]
    exact Nat.le_of_lt hk_upper_lt
  have hk_lower_real :
      (((fmt.beta ^ d * fmt.maxNormalMantissa : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real :
      (k : ℝ) ≤
        (((fmt.beta ^ (d + 1) * fmt.minNormalMantissa : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' :
      (fmt.beta ^ d : ℝ) * (fmt.maxNormalMantissa : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.beta ^ (d + 1) : ℝ) *
        (fmt.minNormalMantissa : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
/-- Negative multi-guard source coefficients at the mantissa ceiling lie between
the reversed shifted exponent-boundary endpoints. -/
theorem multiGuardSource_between_boundaryEndpoints_negative
    {fmt : FloatingPointFormat} {k r d : ℕ} {e : ℤ}
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d) :
    fmt.normalizedValue true fmt.minNormalMantissa
        (e + ((d + 1 : ℕ) : ℤ)) ≤
        fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
      fmt.signValue true * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
        fmt.normalizedValue true fmt.maxNormalMantissa (e + (d : ℤ)) := by
  have hs_nonneg : 0 ≤ fmt.betaR ^ (e - (fmt.t : ℤ)) :=
    fmt.betaR_zpow_nonneg (e - (fmt.t : ℤ))
  have hk_lower_nat : fmt.beta ^ d * fmt.maxNormalMantissa ≤ k := by
    rw [hk]
    exact Nat.le_add_right _ _
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta ^ d * (fmt.maxNormalMantissa + 1) =
        fmt.beta ^ (d + 1) * fmt.minNormalMantissa := by
    rw [hmaxsucc_eq]
    ring
  have hk_upper_lt :
      k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
    rw [hk, Nat.mul_succ]
    exact Nat.add_lt_add_left hr (fmt.beta ^ d * fmt.maxNormalMantissa)
  have hk_upper_nat :
      k ≤ fmt.beta ^ (d + 1) * fmt.minNormalMantissa := by
    rw [← hupper_coeff]
    exact Nat.le_of_lt hk_upper_lt
  have hk_lower_real :
      (((fmt.beta ^ d * fmt.maxNormalMantissa : ℕ) : ℝ)) ≤ (k : ℝ) :=
    Nat.cast_le.mpr hk_lower_nat
  have hk_upper_real :
      (k : ℝ) ≤
        (((fmt.beta ^ (d + 1) * fmt.minNormalMantissa : ℕ) : ℝ)) :=
    Nat.cast_le.mpr hk_upper_nat
  have hk_lower_real' :
      (fmt.beta ^ d : ℝ) * (fmt.maxNormalMantissa : ℝ) ≤ (k : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_lower_real
  have hk_upper_real' :
      (k : ℝ) ≤ (fmt.beta ^ (d + 1) : ℝ) *
        (fmt.minNormalMantissa : ℝ) := by
    simpa [Nat.cast_mul, Nat.cast_pow] using hk_upper_real
  constructor
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_upper_real' hs_nonneg
  · rw [fmt.normalizedValue_add_natExponent_eq_beta_pow_scaledInteger]
    simp [signValue]
    exact mul_le_mul_of_nonneg_right hk_lower_real' hs_nonneg
/-- Binary guard-word quotient dispatcher for aligned addition.

If a one-guard-digit source coefficient `k` lies in
`[beta^t, 2*beta^t)` and is decomposed as `k = 2*q+r`, then the quotient
endpoint is either an ordinary normalized same-exponent bracket (`q` and
`q+1` are both normalized mantissas) or the lower endpoint is exactly
`maxNormalMantissa`, which is the exponent-boundary guard-word case. -/
theorem binaryGuardQuotient_normalized_or_max_of_mantissaBound_le_of_lt_two_mul
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k q r : ℕ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hlo : fmt.beta ^ fmt.t ≤ k)
    (hhi : k < 2 * fmt.beta ^ fmt.t) :
    (fmt.normalizedMantissa q ∧ fmt.normalizedMantissa (q + 1)) ∨
      q = fmt.maxNormalMantissa := by
  have hk2 : k = 2 * q + r := by
    simpa [hbeta] using hk
  have hr2 : r < 2 := by
    simpa [hbeta] using hr
  have hB_eq : fmt.beta ^ fmt.t = 2 * fmt.minNormalMantissa := by
    rw [← fmt.minNormalMantissa_mul_beta_eq_mantissaBound, hbeta]
    ring
  have hq_ge_min : fmt.minNormalMantissa ≤ q := by
    omega
  have hq_lt_B : q < fmt.beta ^ fmt.t := by
    omega
  by_cases hqsucc_lt_B : q + 1 < fmt.beta ^ fmt.t
  · exact Or.inl
      ⟨⟨hq_ge_min, hq_lt_B⟩,
        ⟨Nat.le_trans hq_ge_min (Nat.le_succ q), hqsucc_lt_B⟩⟩
  · have hqsucc_eq_B : q + 1 = fmt.beta ^ fmt.t := by
      omega
    have hqmax : q = fmt.maxNormalMantissa := by
      rw [← fmt.maxNormalMantissa_add_one] at hqsucc_eq_B
      omega
    exact Or.inr hqmax
/-- Binary one-guard-digit endpoint comparison for aligned addition.

If a source coefficient `k` is decomposed as `k = beta*q + r` in base two, and
the rounded endpoint coefficient is either `q` or the non-exact upper endpoint
`q+1`, then the scaled coefficient difference `k - beta*l` has fewer than `t`
base-`beta` digits.  This is the integer arithmetic core of the aligned
inexact-add branch for C4.4/FastTwoSum. -/
theorem binaryGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k q r l : ℕ}
    (hk : k = fmt.beta * q + r)
    (hr : r < fmt.beta)
    (hl : l = q ∨ (l = q + 1 ∧ r ≠ 0)) :
    (((k : ℤ) - ((fmt.beta * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hbeta_le_B : fmt.beta ≤ fmt.beta ^ fmt.t :=
    Nat.le_self_pow (Nat.ne_of_gt fmt.t_pos) fmt.beta
  have hBgt1 : 1 < fmt.beta ^ fmt.t :=
    Nat.one_lt_pow (Nat.ne_of_gt fmt.t_pos) fmt.one_lt_beta
  have hk2 : k = 2 * q + r := by
    simpa [hbeta] using hk
  have hr2 : r < 2 := by
    simpa [hbeta] using hr
  rcases hl with hl | hceil
  · subst l
    have hdiff : ((k : ℤ) - ((fmt.beta * q : ℕ) : ℤ)) = (r : ℤ) := by
      rw [hbeta]
      omega
    rw [hdiff]
    have habs : ((r : ℤ).natAbs) = r := by
      simp
    rw [habs]
    exact lt_of_lt_of_le hr hbeta_le_B
  · rcases hceil with ⟨hl, hrne⟩
    subst l
    have hr_eq : r = 1 := by
      omega
    have hdiff :
        ((k : ℤ) - ((fmt.beta * (q + 1) : ℕ) : ℤ)) = (-1 : ℤ) := by
      rw [hbeta]
      omega
    rw [hdiff]
    norm_num
    exact hBgt1
/-- Multi-guard endpoint comparison for aligned addition.

If a source coefficient `k` is decomposed as `k = beta^d*q+r`, the endpoint
coefficient is either the lower quotient `q` or the non-exact upper quotient
`q+1`, and the shift `d` fits within the format precision, then the scaled
coefficient difference `k - beta^d*l` has fewer than `t` radix digits.  This is
the coefficient arithmetic core for the remaining ordered-exponent C4.4 branch
where the lower operand lies inside the high operand's precision window but is
not a one-guard-digit alignment. -/
theorem multiGuardCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_ceil
    {fmt : FloatingPointFormat} {k q r l d : ℕ}
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hl : l = q ∨ (l = q + 1 ∧ r ≠ 0)) :
    (((k : ℤ) - (((fmt.beta ^ d) * l : ℕ) : ℤ)).natAbs <
      fmt.beta ^ fmt.t) := by
  have hbeta_pos : 0 < fmt.beta := by
    exact Nat.zero_lt_of_lt fmt.one_lt_beta
  have hpow_pos : 0 < fmt.beta ^ d := Nat.pow_pos hbeta_pos
  have hpow_le_B : fmt.beta ^ d ≤ fmt.beta ^ fmt.t :=
    Nat.pow_le_pow_right hbeta_pos hdle
  rcases hl with hl | hceil
  · subst l
    have hdiff :
        ((k : ℤ) - (((fmt.beta ^ d) * q : ℕ) : ℤ)) = (r : ℤ) := by
      rw [hk]
      omega
    rw [hdiff]
    have habs : ((r : ℤ).natAbs) = r := by
      simp
    rw [habs]
    exact lt_of_lt_of_le hr hpow_le_B
  · rcases hceil with ⟨hl, hrne⟩
    subst l
    have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
    have hle_r : r ≤ fmt.beta ^ d := Nat.le_of_lt hr
    have hsub_cast :
        (((fmt.beta ^ d - r : ℕ) : ℤ)) =
          (fmt.beta ^ d : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hle_r]
      rfl
    have hdiff :
        ((k : ℤ) - (((fmt.beta ^ d) * (q + 1) : ℕ) : ℤ)) =
          -((fmt.beta ^ d - r : ℕ) : ℤ) := by
      rw [hk, Nat.mul_succ, hsub_cast]
      norm_num [Nat.cast_add, Nat.cast_mul]
    rw [hdiff]
    have habs :
        ((-((fmt.beta ^ d - r : ℕ) : ℤ)).natAbs) =
          fmt.beta ^ d - r := by
      simp
    rw [habs]
    have hsub_lt : fmt.beta ^ d - r < fmt.beta ^ d :=
      Nat.sub_lt hpow_pos hrpos
    exact lt_of_lt_of_le hsub_lt hpow_le_B
/-- Binary one-guard-digit coefficient comparison at the exponent boundary.

The lower endpoint is `beta * maxNormalMantissa` on the original exponent
lattice.  The upper boundary endpoint is `minNormalMantissa * beta^2` on that
same lattice, and it can only be selected in the non-exact remainder case. -/
theorem binaryGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k r c : ℕ}
    (hk : k = fmt.beta * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta)
    (hc : c = fmt.beta * fmt.maxNormalMantissa ∨
      (c = fmt.minNormalMantissa * fmt.beta ^ 2 ∧ r ≠ 0)) :
    (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  have hbeta_le_B : fmt.beta ≤ fmt.beta ^ fmt.t :=
    Nat.le_self_pow (Nat.ne_of_gt fmt.t_pos) fmt.beta
  have hBgt1 : 1 < fmt.beta ^ fmt.t :=
    Nat.one_lt_pow (Nat.ne_of_gt fmt.t_pos) fmt.one_lt_beta
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta * (fmt.maxNormalMantissa + 1) =
        fmt.minNormalMantissa * fmt.beta ^ 2 := by
    rw [hmaxsucc_eq]
    ring
  rcases hc with hc | hc
  · subst c
    have hdiff :
        ((k : ℤ) - ((fmt.beta * fmt.maxNormalMantissa : ℕ) : ℤ)) =
          (r : ℤ) := by
      rw [hk]
      omega
    rw [hdiff]
    have habs : ((r : ℤ).natAbs) = r := by simp
    rw [habs]
    exact lt_of_lt_of_le hr hbeta_le_B
  · rcases hc with ⟨hc, hrne⟩
    subst c
    have hr_eq : r = 1 := by
      omega
    have hdiff :
        ((k : ℤ) - ((fmt.minNormalMantissa * fmt.beta ^ 2 : ℕ) : ℤ)) =
          (-1 : ℤ) := by
      rw [hk, ← hupper_coeff, hbeta, hr_eq]
      omega
    rw [hdiff]
    simpa using hBgt1
/-- Multi-guard coefficient comparison at the exponent boundary.

The lower endpoint is `beta^d * maxNormalMantissa` on the original exponent
lattice.  The upper boundary endpoint is `beta^(d+1) * minNormalMantissa` on
that same lattice, and it can only be selected in the non-exact remainder case.
-/
theorem multiGuardBoundaryCoeffDiff_natAbs_lt_mantissaBound_of_floor_or_boundary
    {fmt : FloatingPointFormat} {k r c d : ℕ}
    (hdle : d ≤ fmt.t)
    (hk : k = fmt.beta ^ d * fmt.maxNormalMantissa + r)
    (hr : r < fmt.beta ^ d)
    (hc : c = fmt.beta ^ d * fmt.maxNormalMantissa ∨
      (c = fmt.beta ^ (d + 1) * fmt.minNormalMantissa ∧ r ≠ 0)) :
    (((k : ℤ) - (c : ℤ)).natAbs < fmt.beta ^ fmt.t) := by
  have hbeta_pos : 0 < fmt.beta := by
    exact Nat.zero_lt_of_lt fmt.one_lt_beta
  have hpow_pos : 0 < fmt.beta ^ d := Nat.pow_pos hbeta_pos
  have hpow_le_B : fmt.beta ^ d ≤ fmt.beta ^ fmt.t :=
    Nat.pow_le_pow_right hbeta_pos hdle
  have hmaxsucc_eq :
      fmt.maxNormalMantissa + 1 = fmt.minNormalMantissa * fmt.beta := by
    rw [fmt.maxNormalMantissa_add_one,
      fmt.minNormalMantissa_mul_beta_eq_mantissaBound]
  have hupper_coeff :
      fmt.beta ^ d * (fmt.maxNormalMantissa + 1) =
        fmt.beta ^ (d + 1) * fmt.minNormalMantissa := by
    rw [hmaxsucc_eq]
    ring
  rcases hc with hc | hc
  · subst c
    have hdiff :
        ((k : ℤ) - (((fmt.beta ^ d) * fmt.maxNormalMantissa : ℕ) : ℤ)) =
          (r : ℤ) := by
      rw [hk]
      omega
    rw [hdiff]
    have habs : ((r : ℤ).natAbs) = r := by simp
    rw [habs]
    exact lt_of_lt_of_le hr hpow_le_B
  · rcases hc with ⟨hc, hrne⟩
    subst c
    have hrpos : 0 < r := Nat.pos_of_ne_zero hrne
    have hle_r : r ≤ fmt.beta ^ d := Nat.le_of_lt hr
    have hsub_cast :
        (((fmt.beta ^ d - r : ℕ) : ℤ)) =
          (fmt.beta ^ d : ℤ) - (r : ℤ) := by
      rw [Nat.cast_sub hle_r]
      rfl
    have hdiff :
        ((k : ℤ) -
            (((fmt.beta ^ (d + 1)) * fmt.minNormalMantissa : ℕ) : ℤ)) =
          -((fmt.beta ^ d - r : ℕ) : ℤ) := by
      rw [hk, ← hupper_coeff, Nat.mul_succ, hsub_cast]
      norm_num [Nat.cast_add, Nat.cast_mul]
    rw [hdiff]
    have habs :
        ((-((fmt.beta ^ d - r : ℕ) : ℤ)).natAbs) =
          fmt.beta ^ d - r := by
      simp
    rw [habs]
    have hsub_lt : fmt.beta ^ d - r < fmt.beta ^ d :=
      Nat.sub_lt hpow_pos hrpos
    exact lt_of_lt_of_le hsub_lt hpow_le_B
/-- Multi-guard quotient dispatcher on a supplied scaled mantissa range.

If `k = beta^d*q+r` with `r < beta^d` and `k` lies between the scaled minimum
mantissa and the scaled next-binade boundary, then either the ordinary endpoint
mantissas `q,q+1` are normalized or `q` is exactly `maxNormalMantissa`, the
shifted exponent-boundary case. -/
theorem multiGuardQuotient_normalized_or_max_of_scaledMantissaRange
    {fmt : FloatingPointFormat} {k q r d : ℕ}
    (hk : k = fmt.beta ^ d * q + r)
    (hr : r < fmt.beta ^ d)
    (hlo : fmt.beta ^ d * fmt.minNormalMantissa ≤ k)
    (hhi : k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1)) :
    (fmt.normalizedMantissa q ∧ fmt.normalizedMantissa (q + 1)) ∨
      q = fmt.maxNormalMantissa := by
  have hq_ge_min : fmt.minNormalMantissa ≤ q := by
    by_contra hnot
    have hq_lt_min : q < fmt.minNormalMantissa := lt_of_not_ge hnot
    have hqsucc_le_min : q + 1 ≤ fmt.minNormalMantissa :=
      Nat.succ_le_of_lt hq_lt_min
    have hk_lt_min : k < fmt.beta ^ d * fmt.minNormalMantissa := by
      calc
        k = fmt.beta ^ d * q + r := hk
        _ < fmt.beta ^ d * q + fmt.beta ^ d :=
          Nat.add_lt_add_left hr (fmt.beta ^ d * q)
        _ = fmt.beta ^ d * (q + 1) := by rw [Nat.mul_succ]
        _ ≤ fmt.beta ^ d * fmt.minNormalMantissa :=
          Nat.mul_le_mul_left (fmt.beta ^ d) hqsucc_le_min
    exact (not_lt_of_ge hlo) hk_lt_min
  have hq_lt_B : q < fmt.beta ^ fmt.t := by
    by_contra hnot
    have hq_ge_B : fmt.beta ^ fmt.t ≤ q := le_of_not_gt hnot
    have hboundary_le_q :
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1) ≤
          fmt.beta ^ d * q := by
      rw [fmt.maxNormalMantissa_add_one]
      exact Nat.mul_le_mul_left (fmt.beta ^ d) hq_ge_B
    have hq_le_k : fmt.beta ^ d * q ≤ k := by
      rw [hk]
      exact Nat.le_add_right _ _
    exact (not_le_of_gt hhi) (le_trans hboundary_le_q hq_le_k)
  by_cases hqsucc_lt_B : q + 1 < fmt.beta ^ fmt.t
  · exact Or.inl
      ⟨⟨hq_ge_min, hq_lt_B⟩,
        ⟨Nat.le_trans hq_ge_min (Nat.le_succ q), hqsucc_lt_B⟩⟩
  · have hqsucc_eq_B : q + 1 = fmt.beta ^ fmt.t := by
      omega
    have hqmax : q = fmt.maxNormalMantissa := by
      rw [← fmt.maxNormalMantissa_add_one] at hqsucc_eq_B
      omega
    exact Or.inr hqmax
/-- Base-two binade selector for the multi-guard complementary coefficient.

If a positive aligned coefficient `k` is at least two precision units and is
still below the two-precision bound, then its radix-2 logarithmic binade selects
a shift `d <= t` for which `k` lies in the scaled normalized mantissa range.
This is the scale/range dependency consumed by the quotient-free multi-guard
C4.4 wrappers. -/
theorem multiGuardScaleRange_exists_of_baseTwo_bounds
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {k : ℕ}
    (hlo : 2 * fmt.beta ^ fmt.t ≤ k)
    (hhi : k < fmt.beta ^ (2 * fmt.t)) :
    ∃ d, d ≤ fmt.t ∧
      fmt.beta ^ d * fmt.minNormalMantissa ≤ k ∧
      k < fmt.beta ^ d * (fmt.maxNormalMantissa + 1) := by
  have hk_pos : 0 < k :=
    lt_of_lt_of_le
      (Nat.mul_pos (by decide : 0 < 2) fmt.mantissaBound_pos) hlo
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk_pos
  let L : ℕ := Nat.log fmt.beta k
  have hpow_succ_eq :
      fmt.beta ^ (fmt.t + 1) = 2 * fmt.beta ^ fmt.t := by
    rw [pow_succ, hbeta]
    ring
  have hpow_succ_le : fmt.beta ^ (fmt.t + 1) ≤ k := by
    rw [hpow_succ_eq]
    exact hlo
  have hL_ge : fmt.t + 1 ≤ L := by
    dsimp [L]
    exact Nat.le_log_of_pow_le fmt.one_lt_beta hpow_succ_le
  have hL_lt : L < 2 * fmt.t := by
    dsimp [L]
    exact Nat.log_lt_of_lt_pow hk_ne hhi
  let d : ℕ := L + 1 - fmt.t
  have hdle : d ≤ fmt.t := by
    dsimp [d]
    omega
  have hd_add_pred : d + (fmt.t - 1) = L := by
    dsimp [d]
    omega
  have hd_add : d + fmt.t = L + 1 := by
    dsimp [d]
    omega
  refine ⟨d, hdle, ?_, ?_⟩
  · have hmul_min :
        fmt.beta ^ d * fmt.minNormalMantissa = fmt.beta ^ L := by
      unfold minNormalMantissa
      rw [← pow_add, hd_add_pred]
    rw [hmul_min]
    exact Nat.pow_log_le_self fmt.beta hk_ne
  · have hmul_max :
        fmt.beta ^ d * (fmt.maxNormalMantissa + 1) =
          fmt.beta ^ (L + 1) := by
      rw [fmt.maxNormalMantissa_add_one, ← pow_add, hd_add]
    rw [hmul_max]
    simpa [L, Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self fmt.one_lt_beta k
/-- Base-two upper bound for the complementary ordered-exponent coefficient.

If the lower exponent is still inside the high operand's precision window, the
aligned coefficient
`mHigh * beta^(eHigh-eLow) + mLow` is strictly below `beta^(2*t)`.
This is the raw upper-bound dependency needed by the multi-guard C4.4 branch. -/
theorem alignedCoeff_lt_two_precision_bound_of_normalizedMantissas_window
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (hle : eLow ≤ eHigh)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh) :
    mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
      fmt.beta ^ (2 * fmt.t) := by
  let shift : ℕ := Int.toNat (eHigh - eLow)
  have hshift_cast : ((shift : ℕ) : ℤ) = eHigh - eLow := by
    have hnonneg : 0 ≤ eHigh - eLow := sub_nonneg.mpr hle
    simpa [shift] using Int.toNat_of_nonneg hnonneg
  have hshift_lt : shift < fmt.t := by
    have hshift_lt_int : (shift : ℤ) < (fmt.t : ℤ) := by
      rw [hshift_cast]
      omega
    exact Int.ofNat_lt.mp hshift_lt_int
  let B : ℕ := fmt.beta ^ fmt.t
  let S : ℕ := fmt.beta ^ shift
  let P : ℕ := fmt.beta ^ (fmt.t - 1)
  have hbeta_pos : 0 < fmt.beta := Nat.zero_lt_of_lt fmt.one_lt_beta
  have hS_pos : 0 < S := by
    dsimp [S]
    exact Nat.pow_pos hbeta_pos
  have hP_pos : 0 < P := by
    dsimp [P]
    exact Nat.pow_pos hbeta_pos
  have hshift_le_pred : shift ≤ fmt.t - 1 := by
    omega
  have hS_le_P : S ≤ P := by
    dsimp [S, P]
    exact Nat.pow_le_pow_right hbeta_pos hshift_le_pred
  have hhigh_lt_BP : mHigh * S < B * P := by
    have hhigh_lt_BS : mHigh * S < B * S := by
      exact Nat.mul_lt_mul_of_pos_right hmHigh.2 hS_pos
    have hBS_le_BP : B * S ≤ B * P := by
      exact Nat.mul_le_mul_left B hS_le_P
    exact lt_of_lt_of_le hhigh_lt_BS hBS_le_BP
  have hlow_lt_BP : mLow < B * P := by
    have hB_le_BP : B ≤ B * P := by
      calc
        B = B * 1 := by ring
        _ ≤ B * P := Nat.mul_le_mul_left B (Nat.succ_le_of_lt hP_pos)
    exact lt_of_lt_of_le hmLow.2 hB_le_BP
  have hP_mul_beta : P * fmt.beta = fmt.beta ^ fmt.t := by
    dsimp [P]
    rw [← pow_succ]
    congr 1
    exact Nat.sub_one_add_one_eq_of_pos fmt.t_pos
  have hBP_sum :
      B * P + B * P = fmt.beta ^ (2 * fmt.t) := by
    calc
      B * P + B * P = 2 * (B * P) := by ring
      _ = fmt.beta * (B * P) := by rw [hbeta]
      _ = B * (P * fmt.beta) := by ring
      _ = B * fmt.beta ^ fmt.t := by rw [hP_mul_beta]
      _ = fmt.beta ^ (fmt.t + fmt.t) := by
        dsimp [B]
        rw [← pow_add]
      _ = fmt.beta ^ (2 * fmt.t) := by
        congr 1
        omega
  have hsum :
      mHigh * S + mLow < B * P + B * P :=
    Nat.add_lt_add hhigh_lt_BP hlow_lt_BP
  rw [hBP_sum] at hsum
  simpa [S, B] using hsum
/-- Base-two upper bound for the complementary ordered-exponent difference
coefficient.

Inside the high operand's precision window, the subtraction coefficient
`mHigh * beta^(eHigh-eLow) - mLow` is bounded above by the already-closed
same-sign aligned coefficient bound. -/
theorem alignedDiffCoeff_lt_two_precision_bound_of_normalizedMantissas_window
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2)
    {mHigh mLow : ℕ} {eHigh eLow : ℤ}
    (hmHigh : fmt.normalizedMantissa mHigh)
    (hmLow : fmt.normalizedMantissa mLow)
    (hle : eLow ≤ eHigh)
    (hwindow : eLow + (fmt.t : ℤ) > eHigh) :
    mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow <
      fmt.beta ^ (2 * fmt.t) := by
  have hplus :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow <
        fmt.beta ^ (2 * fmt.t) :=
    fmt.alignedCoeff_lt_two_precision_bound_of_normalizedMantissas_window
      hbeta hmHigh hmLow hle hwindow
  have hdiff_le :
      mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) - mLow ≤
        mHigh * fmt.beta ^ Int.toNat (eHigh - eLow) + mLow := by
    exact le_trans (Nat.sub_le _ _) (Nat.le_add_right _ _)
  exact lt_of_le_of_lt hdiff_le hplus
/-- The currently closed same-exponent finite-difference cases for direct
Sterbenz-style representability: exact zero, a normalized finite shift, or the
shifted `emin` subnormal endpoint.  Proving this witness from Sterbenz's source
hypotheses is the remaining direct same-exponent selector obligation. -/
def sameExponentFiniteDifferenceWitness
    (fmt : FloatingPointFormat) (m n : ℕ) (e : ℤ) : Prop :=
  (fmt.sameExponentMantissaDiffInt m n).natAbs = 0 ∨
    fmt.sameExponentRenormalizationWitness m n e ∨
      fmt.sameExponentSubnormalEndpointWitness m n e
/-- Same-exponent finite-difference selector derived from ordinary finite
same-exponent operand facts.  The exact integer mantissa difference has fewer
than `t` digits; shifting it down from exponent `e` either normalizes before
leaving the finite exponent interval or reaches the shifted `emin` subnormal
endpoint. -/
theorem sameExponentFiniteDifferenceWitness_of_normalizedMantissas
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.sameExponentFiniteDifferenceWitness m n e := by
  let a := (fmt.sameExponentMantissaDiffInt m n).natAbs
  let q := Int.toNat (e - fmt.emin)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have ha_lt : a < fmt.beta ^ fmt.t := by
    simpa [a] using
      fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound hm.2 hn.2
  rcases fmt.sameExponent_shift_search (a := a) (q := q) ha_lt with
    hzero | hrest
  · exact Or.inl (by simpa [a] using hzero)
  rcases hrest with hnorm | hend
  · rcases hnorm with ⟨shift, hle, hnorm⟩
    have hle_int : (shift : ℤ) ≤ (q : ℤ) := by
      exact_mod_cast hle
    have hex : fmt.exponentInRange (e - (shift : ℤ)) := by
      constructor
      · omega
      · have hshift_nonneg : (0 : ℤ) ≤ (shift : ℤ) := by
          exact_mod_cast Nat.zero_le shift
        have hle_e : e - (shift : ℤ) ≤ e := by omega
        exact le_trans hle_e he.2
    exact Or.inr (Or.inl ⟨shift, hex, by simpa [a] using hnorm⟩)
  · exact Or.inr (Or.inr ⟨q, hq_endpoint, by simpa [a] using hend⟩)
/-- Exact zero same-exponent subtraction is finite for every exponent. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hdiff : (fmt.sameExponentMantissaDiffInt m n).natAbs = 0) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  have hkzero : k = 0 := by
    exact Int.natAbs_eq_zero.mp (by simpa [k] using hdiff)
  left
  rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
  simp [alignedSameExponentSubtractionValue, signValue, hk_cast.symm, hkzero]
/-- Direct representability subcase for Sterbenz-style exact subtraction:
when the same-exponent mantissa difference is already a normalized mantissa, the
exact subtraction result is a finite normalized floating-point value.  The
remaining direct Sterbenz work is the non-`emin` renormalization case when this
coefficient has too few leading digits. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedDiff
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hex : fmt.exponentInRange e)
    (hdiff : fmt.normalizedMantissa
      (fmt.sameExponentMantissaDiffInt m n).natAbs) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkneg : k < 0
  · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
      simp [abs_of_neg hkneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
  · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
    have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
      simp [abs_of_nonneg hknonneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs, e, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
/-- Direct one-step renormalization subcase for Sterbenz-style exact
subtraction: if shifting one base digit from the exponent into the exact
same-exponent mantissa difference gives a normalized mantissa, then the exact
subtraction result is a finite normalized floating-point value at exponent
`e - 1`. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_mul_normalizedDiff
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hex : fmt.exponentInRange (e - 1))
    (hdiff : fmt.normalizedMantissa
      ((fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta)) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkneg : k < 0
  · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
      simp [abs_of_neg hkneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
  · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
    have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
      simp [abs_of_nonneg hknonneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta, e - 1, by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_predExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
/-- Direct arbitrary-shift renormalization subcase for Sterbenz-style exact
subtraction: if shifting any finite number of base digits from the exponent
into the exact same-exponent mantissa difference gives a normalized mantissa,
then the exact subtraction result is a finite normalized floating-point value
at the shifted exponent. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff
    {fmt : FloatingPointFormat} {negative : Bool} {m n shift : ℕ} {e : ℤ}
    (hex : fmt.exponentInRange (e - (shift : ℤ)))
    (hdiff : fmt.normalizedMantissa
      ((fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift)) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkneg : k < 0
  · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
      simp [abs_of_neg hkneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
  · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
    have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
      simp [abs_of_nonneg hknonneg]
    have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
      have hcast :
          ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
        congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
      simpa using hcast
    cases negative
    · exact Or.inr (Or.inl
        ⟨false, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
    · exact Or.inr (Or.inl
        ⟨true, k.natAbs * fmt.beta ^ shift, e - (shift : ℤ),
          by simpa [k] using hdiff, hex, by
          rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
          rw [fmt.normalizedValue_mul_beta_pow_subExponent_eq]
          simp [alignedSameExponentSubtractionValue, normalizedValue,
            signValue, hk_cast.symm, hk_abs_real]⟩)
/-- A renormalization selector witness is enough to prove same-exponent exact
subtraction is finite. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hw : fmt.sameExponentRenormalizationWitness m n e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  rcases hw with ⟨shift, hex, hdiff⟩
  exact
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_beta_pow_mul_normalizedDiff
      (negative := negative) (m := m) (n := n) (e := e)
      (shift := shift) hex hdiff
/-- Direct subnormal endpoint for Sterbenz-style exact subtraction: at the
smallest normal exponent, a same-exponent exact mantissa difference below the
normal leading-digit threshold is either zero or a finite subnormal value. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_emin_of_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs < fmt.minNormalMantissa) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m fmt.emin -
        fmt.normalizedValue negative n fmt.emin) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkzero : k = 0
  · left
    rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
    simp [alignedSameExponentSubtractionValue, signValue, hk_cast.symm, hkzero]
  · by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      have hpos_int : (0 : ℤ) < ((k.natAbs : ℕ) : ℤ) := by
        rw [hk_abs_int]
        exact neg_pos.mpr hkneg
      have hpos : 0 < k.natAbs := by
        exact_mod_cast hpos_int
      have hsub : fmt.subnormalMantissa k.natAbs :=
        ⟨hpos, by simpa [k] using hdiff⟩
      cases negative
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hkpos_int : (0 : ℤ) < k := by
        exact lt_of_le_of_ne hknonneg (fun h => hkzero h.symm)
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      have hpos_int : (0 : ℤ) < ((k.natAbs : ℕ) : ℤ) := by
        rw [hk_abs_int]
        exact hkpos_int
      have hpos : 0 < k.natAbs := by
        exact_mod_cast hpos_int
      have hsub : fmt.subnormalMantissa k.natAbs :=
        ⟨hpos, by simpa [k] using hdiff⟩
      cases negative
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            simp [alignedSameExponentSubtractionValue, subnormalValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
/-- Shifted direct subnormal endpoint for Sterbenz-style exact subtraction:
after shifting some finite number of base digits from the exponent into the
same-exponent exact mantissa difference, if the shifted exponent is `emin` and
the shifted coefficient is below the normalized leading-digit threshold, then
the exact subtraction result is finite. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {negative : Bool} {m n shift : ℕ} {e : ℤ}
    (he : e - (shift : ℤ) = fmt.emin)
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs * fmt.beta ^ shift <
        fmt.minNormalMantissa) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  let k := fmt.sameExponentMantissaDiffInt m n
  have hk_cast : (k : ℝ) = (m : ℝ) - (n : ℝ) := by
    simpa [k] using fmt.sameExponentMantissaDiffInt_cast m n
  by_cases hkzero : k = 0
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero
        (negative := negative) (m := m) (n := n) (e := e)
        (by simp [k, hkzero])
  · have hkabs_pos : 0 < k.natAbs := by
      exact Nat.pos_of_ne_zero (mt Int.natAbs_eq_zero.mp hkzero)
    have hscale_pos :
        0 < k.natAbs * fmt.beta ^ shift := by
      exact Nat.mul_pos hkabs_pos
        (Nat.pow_pos (lt_of_lt_of_le (by decide : 0 < 2) fmt.beta_ge_two))
    have hsub :
        fmt.subnormalMantissa (k.natAbs * fmt.beta ^ shift) :=
      ⟨hscale_pos, by simpa [k] using hdiff⟩
    by_cases hkneg : k < 0
    · have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = -k := by
        simp [abs_of_neg hkneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = -(k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = (((-k : ℤ) : ℝ)) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
    · have hknonneg : 0 ≤ k := le_of_not_gt hkneg
      have hk_abs_int : (((k.natAbs : ℕ) : ℤ)) = k := by
        simp [abs_of_nonneg hknonneg]
      have hk_abs_real : ((k.natAbs : ℕ) : ℝ) = (k : ℝ) := by
        have hcast :
            ((((k.natAbs : ℕ) : ℤ) : ℝ)) = ((k : ℤ) : ℝ) :=
          congrArg (fun z : ℤ => (z : ℝ)) hk_abs_int
        simpa using hcast
      cases negative
      · exact Or.inr (Or.inr
          ⟨false, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := false) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
      · exact Or.inr (Or.inr
          ⟨true, k.natAbs * fmt.beta ^ shift, hsub, by
            rw [fmt.normalizedValue_sub_sameSign_sameExponent_eq_aligned]
            rw [← fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
              (negative := true) (m := k.natAbs) (shift := shift)
              (e := e) he]
            simp [alignedSameExponentSubtractionValue, normalizedValue,
              signValue, hk_cast.symm, hk_abs_real]⟩)
/-- A shifted subnormal endpoint selector witness is enough to prove
same-exponent exact subtraction is finite. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hw : fmt.sameExponentSubnormalEndpointWitness m n e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  rcases hw with ⟨shift, he, hdiff⟩
  exact
    fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_at_shifted_emin_of_natAbs_mul_beta_pow_lt_minNormalMantissa
      (negative := negative) (m := m) (n := n) (e := e)
      (shift := shift) he hdiff
/-- The closed same-exponent finite-difference witness packages the direct
Sterbenz-style finite representability cases currently proved in Lean: exact
zero, normalized finite renormalization shift, or the shifted `emin` subnormal
endpoint. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hw : fmt.sameExponentFiniteDifferenceWitness m n e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) := by
  rcases hw with hzero | hrenorm | hemin
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_natAbs_eq_zero
        (negative := negative) (m := m) (n := n) (e := e) hzero
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_renormalizationWitness
        (negative := negative) (m := m) (n := n) (e := e) hrenorm
  · exact
      fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_subnormalEndpointWitness
        (negative := negative) (m := m) (n := n) (e := e) hemin
/-- Source-facing same-exponent finite-subtraction theorem: for two finite
normalized operands with the same exponent and sign, the exact difference is a
finite floating-point number.  The proof derives the finite-difference selector
from the operand mantissas and exponent range. -/
theorem normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_normalizedMantissas
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : fmt.exponentInRange e) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e -
        fmt.normalizedValue negative n e) :=
  fmt.normalizedValue_sub_sameSign_sameExponent_finiteSystem_of_finiteDifferenceWitness
    (negative := negative) (m := m) (n := n) (e := e)
    (fmt.sameExponentFiniteDifferenceWitness_of_normalizedMantissas hm hn he)
/-- Same-sign subnormal subtraction is finite: both operands lie on the common
subnormal lattice, so the exact integer coefficient still has fewer than `t`
radix digits. -/
theorem subnormalValue_sub_sameSign_finiteSystem_of_subnormalMantissas
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      (fmt.subnormalValue negative m -
        fmt.subnormalValue negative n) := by
  have hmrange : fmt.mantissaInRange m :=
    fmt.subnormalMantissa_inRange hm
  have hnrange : fmt.mantissaInRange n :=
    fmt.subnormalMantissa_inRange hn
  have hcoeff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs < fmt.beta ^ fmt.t :=
    fmt.sameExponentMantissaDiffInt_natAbs_lt_mantissaBound hmrange hnrange
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative *
          ((fmt.sameExponentMantissaDiffInt m n : ℤ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := fmt.sameExponentMantissaDiffInt m n)
      (e := fmt.emin) ⟨le_rfl, fmt.emin_le_emax⟩ hcoeff
  convert hfin using 1
  rw [fmt.sameExponentMantissaDiffInt_cast m n]
  simp [subnormalValue]
  ring
/-- Same-sign subnormal addition is finite: both operands share the minimum
subnormal lattice spacing, and the sum coefficient stays below the normalized
mantissa bound. -/
theorem subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ}
    (hm : fmt.subnormalMantissa m)
    (hn : fmt.subnormalMantissa n) :
    fmt.finiteSystem
      (fmt.subnormalValue negative m + fmt.subnormalValue negative n) := by
  have hsum_lt_min_sum :
      m + n < fmt.minNormalMantissa + fmt.minNormalMantissa :=
    Nat.add_lt_add hm.2 hn.2
  have hsum_lt_bound : m + n < fmt.beta ^ fmt.t := by
    have hle_two :
        fmt.minNormalMantissa + fmt.minNormalMantissa ≤
          fmt.minNormalMantissa * fmt.beta := by
      calc
        fmt.minNormalMantissa + fmt.minNormalMantissa =
            fmt.minNormalMantissa * 2 := by omega
        _ ≤ fmt.minNormalMantissa * fmt.beta :=
            Nat.mul_le_mul_left fmt.minNormalMantissa fmt.beta_ge_two
    exact lt_of_lt_of_le hsum_lt_min_sum
      (by simpa [fmt.minNormalMantissa_mul_beta_eq_mantissaBound] using hle_two)
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative * (((m + n : ℕ) : ℤ) : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := ((m + n : ℕ) : ℤ))
      (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩
      (by simpa using hsum_lt_bound)
  convert hfin using 1
  simp [subnormalValue, Nat.cast_add]
  ring
/-- In base `2`, doubling a finite value is finite whenever the doubled
magnitude stays below the largest finite magnitude.

The normalized branch shifts the exponent by one in the unbounded system and
then uses the finite-normal-range bridge; the subnormal branch is just
same-sign subnormal addition. -/
theorem finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2)
    {a : ℝ}
    (ha : fmt.finiteSystem a)
    (habs : |2 * a| ≤ fmt.maxFiniteMagnitude) :
    fmt.finiteSystem (2 * a) := by
  rcases ha with ha0 | hnorm | hsub
  · subst a
    exact Or.inl (by ring)
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    have htwo_betaR : (2 : ℝ) = fmt.betaR := by
      simp [betaR, hbeta]
    have hunbounded :
        fmt.unboundedNormalizedSystem
          (2 * fmt.normalizedValue negative m e) := by
      refine ⟨negative, m, e + 1, hm, ?_⟩
      rw [htwo_betaR]
      exact fmt.betaR_mul_normalizedValue_eq_succExponent negative m e
    have hnorm2 :
        fmt.normalizedSystem (2 * fmt.normalizedValue negative m e) := by
      apply fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      · exact hunbounded
      · constructor
        · have hmin :=
            (fmt.normalizedSystem_abs_bounds
              ⟨negative, m, e, hm, he, rfl⟩).1
          have hle_abs :
              |fmt.normalizedValue negative m e| ≤
                |2 * fmt.normalizedValue negative m e| := by
            rw [abs_mul]
            have hge : (1 : ℝ) ≤ |(2 : ℝ)| := by norm_num
            nlinarith [abs_nonneg (fmt.normalizedValue negative m e)]
          exact le_trans hmin hle_abs
        · exact habs
    exact Or.inr (Or.inl hnorm2)
  · rcases hsub with ⟨negative, m, hm, rfl⟩
    have hfin :
        fmt.finiteSystem
          (fmt.subnormalValue negative m + fmt.subnormalValue negative m) :=
      fmt.subnormalValue_add_sameSign_finiteSystem_of_subnormalMantissas
        (negative := negative) hm hm
    simpa [two_mul] using hfin
/-- Same-sign mixed normal/subnormal addition is finite when the normalized
operand, shifted onto the subnormal lattice, plus the subnormal coefficient
still fits in `t` radix digits. -/
theorem normalizedValue_add_sameSign_subnormal_finiteSystem_of_alignedCoeff_lt_mantissaBound
    {fmt : FloatingPointFormat} {negative : Bool} {m n : ℕ} {e : ℤ}
    (_hm : fmt.normalizedMantissa m)
    (_hn : fmt.subnormalMantissa n)
    (he : fmt.exponentInRange e)
    (hcoeff :
      m * fmt.beta ^ Int.toNat (e - fmt.emin) + n < fmt.beta ^ fmt.t) :
    fmt.finiteSystem
      (fmt.normalizedValue negative m e + fmt.subnormalValue negative n) := by
  let q := Int.toNat (e - fmt.emin)
  have hq_cast : ((q : ℕ) : ℤ) = e - fmt.emin := by
    have hnonneg : 0 ≤ e - fmt.emin := sub_nonneg.mpr he.1
    simpa [q] using Int.toNat_of_nonneg hnonneg
  have hq_endpoint : e - (q : ℤ) = fmt.emin := by
    omega
  have hshift :
      fmt.normalizedValue negative m e =
        fmt.subnormalValue negative (m * fmt.beta ^ q) :=
    fmt.normalizedValue_eq_subnormalValue_mul_beta_pow_of_subExponent_eq_emin
      (negative := negative) (m := m) (shift := q) (e := e) hq_endpoint
  have hfin :
      fmt.finiteSystem
        (fmt.signValue negative *
          ((((m * fmt.beta ^ q + n : ℕ) : ℤ) : ℝ)) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) :=
    fmt.scaledIntegerValue_finiteSystem_of_natAbs_lt_mantissaBound
      (negative := negative)
      (k := ((m * fmt.beta ^ q + n : ℕ) : ℤ))
      (e := fmt.emin)
      ⟨le_rfl, fmt.emin_le_emax⟩
      (by simpa [q] using hcoeff)
  convert hfin using 1
  rw [hshift]
  simp [subnormalValue, Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
  ring
/-- The unshifted `emin` endpoint remains available as a constructor for the
new shifted subnormal endpoint witness. -/
theorem sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (he : e = fmt.emin)
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs <
        fmt.minNormalMantissa) :
    fmt.sameExponentSubnormalEndpointWitness m n e := by
  refine ⟨0, ?_, ?_⟩
  · simp [he]
  · simpa using hdiff
/-- The old unshifted `emin` endpoint is a special case of the packaged
finite-difference witness. -/
theorem sameExponentFiniteDifferenceWitness_of_emin_natAbs_lt_minNormalMantissa
    {fmt : FloatingPointFormat} {m n : ℕ} {e : ℤ}
    (he : e = fmt.emin)
    (hdiff :
      (fmt.sameExponentMantissaDiffInt m n).natAbs <
        fmt.minNormalMantissa) :
    fmt.sameExponentFiniteDifferenceWitness m n e := by
    exact
      Or.inr (Or.inr
        (fmt.sameExponentSubnormalEndpointWitness_of_emin_natAbs_lt_minNormalMantissa
          (m := m) (n := n) (e := e) he hdiff))
theorem subnormalValue_abs_lt_min_normal {fmt : FloatingPointFormat}
    {negative : Bool} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    |fmt.subnormalValue negative m| < fmt.betaR ^ (fmt.emin - 1) := by
  rw [fmt.subnormalValue_abs negative m,
    ← fmt.minNormalMantissa_scale_eq fmt.emin]
  exact mul_lt_mul_of_pos_right
    (Nat.cast_lt.mpr hm.2)
    (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
/-- Subnormal finite values lie below the smallest positive normal magnitude. -/
theorem subnormalSystem_finiteUnderflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    fmt.finiteUnderflowRange y := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  simpa [finiteUnderflowRange, minNormalMagnitude] using
    fmt.subnormalValue_abs_lt_min_normal (negative := negative) hm
/-- Subnormal values are no larger than the positive smallest normal
magnitude. -/
theorem subnormalSystem_le_minNormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    y ≤ fmt.minNormalMagnitude := by
  have hunder := fmt.subnormalSystem_finiteUnderflowRange hy
  exact le_trans (le_abs_self y) (le_of_lt hunder)
/-- Subnormal values are no smaller than the negative smallest normal
endpoint. -/
theorem neg_minNormalMagnitude_le_subnormalSystem
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    -fmt.minNormalMagnitude ≤ y := by
  have hunder := fmt.subnormalSystem_finiteUnderflowRange hy
  have hneg : -fmt.minNormalMagnitude < -|y| := neg_lt_neg hunder
  exact le_of_lt (lt_of_lt_of_le hneg (neg_abs_le y))
/-- In a binary finite system, a nonnegative finite value either has a finite
half or is already within twice the smallest normal magnitude.

The disjunction is intentional: at the bottom binade, and in the subnormal
region, halving a finite value need not stay in the finite system. -/
theorem finiteSystem_half_or_le_two_minNormalMagnitude_of_nonneg_baseTwo
    {fmt : FloatingPointFormat} (hbeta : fmt.beta = 2) {a : ℝ}
    (ha : fmt.finiteSystem a) (ha_nonneg : 0 ≤ a) :
    fmt.finiteSystem (a / 2) ∨ a ≤ 2 * fmt.minNormalMagnitude := by
  rcases ha with ha0 | hanorm | hasub
  · subst a
    left
    simp [finiteSystem]
  · rcases hanorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · by_cases hemin : e = fmt.emin
      · subst e
        right
        have hval_nonneg :
            0 ≤ fmt.normalizedValue false m fmt.emin :=
          le_of_lt (fmt.normalizedValue_false_pos (m := m) (e := fmt.emin) hm)
        have habs :
            |fmt.normalizedValue false m fmt.emin| =
              fmt.normalizedValue false m fmt.emin :=
          abs_of_nonneg hval_nonneg
        have hlt_abs :
            |fmt.normalizedValue false m fmt.emin| < fmt.betaR ^ fmt.emin :=
          fmt.normalizedValue_abs_lt_beta_pow
            (negative := false) (m := m) (e := fmt.emin) hm
        have hlt :
            fmt.normalizedValue false m fmt.emin < fmt.betaR ^ fmt.emin := by
          simpa [habs] using hlt_abs
        have hpow :
            fmt.betaR ^ fmt.emin = 2 * fmt.minNormalMagnitude := by
          have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
          calc
            fmt.betaR ^ fmt.emin =
                fmt.betaR ^ ((1 : ℤ) + (fmt.emin - 1)) := by
              congr 1
              ring
            _ = fmt.betaR ^ (1 : ℤ) *
                fmt.betaR ^ (fmt.emin - 1) := by
              rw [zpow_add₀ hbase]
            _ = 2 * fmt.minNormalMagnitude := by
              simp [minNormalMagnitude, betaR, hbeta]
        exact le_of_lt (by simpa [hpow] using hlt)
      · left
        have hegt : fmt.emin < e :=
          lt_of_le_of_ne he.1 (fun h => hemin h.symm)
        have hepred : fmt.exponentInRange (e - 1) := by
          constructor
          · omega
          · linarith [he.2]
        have hshift :
            2 * fmt.normalizedValue false m (e - 1) =
              fmt.normalizedValue false m e := by
          have h :=
            fmt.betaR_mul_normalizedValue_eq_succExponent false m (e - 1)
          simpa [betaR, hbeta] using h
        have hdiv :
            fmt.normalizedValue false m e / 2 =
              fmt.normalizedValue false m (e - 1) := by
          nlinarith
        rw [hdiv]
        exact Or.inr (Or.inl ⟨false, m, e - 1, hm, hepred, rfl⟩)
    · exfalso
      exact (not_lt_of_ge ha_nonneg)
        (fmt.normalizedValue_true_neg (m := m) (e := e) hm)
  · right
    have hle : a ≤ fmt.minNormalMagnitude :=
      fmt.subnormalSystem_le_minNormalMagnitude hasub
    have hmin_pos : 0 < fmt.minNormalMagnitude :=
      fmt.minNormalMagnitude_pos
    nlinarith
/-- Subnormal finite values have magnitude at least the smallest subnormal. -/
theorem subnormalSystem_abs_ge_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    fmt.minSubnormalMagnitude ≤ |y| := by
  rcases hy with ⟨negative, m, hm, rfl⟩
  have hm_one : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt hm.1)
  rw [fmt.subnormalValue_abs negative m]
  simpa [minSubnormalMagnitude] using
    mul_le_mul_of_nonneg_right hm_one
      (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
/-- Subnormal finite values are not in the source-facing overflow range. -/
theorem subnormalSystem_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.subnormalSystem y) :
    ¬ fmt.finiteOverflowRange y := by
  have hunder := fmt.subnormalSystem_finiteUnderflowRange hy
  exact not_lt_of_ge
    (le_trans (le_of_lt hunder)
      fmt.minNormalMagnitude_le_maxFiniteMagnitude)
/-- Every finite-system value is either zero, in the finite normal range, or in
the source-facing underflow range. -/
theorem finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    y = 0 ∨ fmt.finiteNormalRange y ∨ fmt.finiteUnderflowRange y := by
  rcases hy with hzero | hnorm | hsub
  · exact Or.inl hzero
  · exact Or.inr (Or.inl (fmt.normalizedSystem_finiteNormalRange hnorm))
  · exact Or.inr (Or.inr (fmt.subnormalSystem_finiteUnderflowRange hsub))
/-- Inside the finite system, the source-facing underflow range contains only
zero and subnormal values. -/
theorem finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem
    {fmt : FloatingPointFormat} {y : ℝ} :
    (fmt.finiteSystem y ∧ fmt.finiteUnderflowRange y) ↔
      y = 0 ∨ fmt.subnormalSystem y := by
  constructor
  · rintro ⟨hy, hunder⟩
    rcases hy with hzero | hnorm | hsub
    · exact Or.inl hzero
    · exact False.elim
        ((fmt.normalizedSystem_not_finiteUnderflowRange hnorm) hunder)
    · exact Or.inr hsub
  · intro h
    rcases h with hzero | hsub
    · subst y
      constructor
      · exact Or.inl rfl
      · simpa [finiteUnderflowRange] using fmt.minNormalMagnitude_pos
    · exact ⟨Or.inr (Or.inr hsub),
        fmt.subnormalSystem_finiteUnderflowRange hsub⟩
/-- A finite value is a nonzero underflow-range value exactly when it is
subnormal. -/
theorem finiteSystem_finiteUnderflowRange_ne_zero_iff_subnormalSystem
    {fmt : FloatingPointFormat} {y : ℝ} :
    (fmt.finiteSystem y ∧ fmt.finiteUnderflowRange y ∧ y ≠ 0) ↔
      fmt.subnormalSystem y := by
  constructor
  · rintro ⟨hy, hunder, hy_ne⟩
    rcases
      (fmt.finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem).mp
        ⟨hy, hunder⟩ with hzero | hsub
    · exact False.elim (hy_ne hzero)
    · exact hsub
  · intro hsub
    exact
      ⟨Or.inr (Or.inr hsub),
        fmt.subnormalSystem_finiteUnderflowRange hsub,
        fmt.subnormalSystem_ne_zero hsub⟩
/-- No finite-system value lies in the source-facing overflow range. -/
theorem finiteSystem_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    ¬ fmt.finiteOverflowRange y := by
  rcases hy with hzero | hnorm | hsub
  · subst y
    rw [finiteOverflowRange, abs_zero]
    exact not_lt_of_ge fmt.maxFiniteMagnitude_nonneg
  · exact fmt.normalizedSystem_not_finiteOverflowRange hnorm
  · exact fmt.subnormalSystem_not_finiteOverflowRange hsub
/-- Every finite-system value has magnitude at most the largest finite
normalized magnitude. -/
theorem finiteSystem_abs_le_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) :
    |y| ≤ fmt.maxFiniteMagnitude := by
  have hnot := fmt.finiteSystem_not_finiteOverflowRange hy
  rw [finiteOverflowRange] at hnot
  exact le_of_not_gt hnot
/-- Every nonzero finite-system value has magnitude at least the smallest
positive subnormal magnitude. -/
theorem finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {y : ℝ}
    (hy : fmt.finiteSystem y) (hzero : y ≠ 0) :
    fmt.minSubnormalMagnitude ≤ |y| := by
  rcases hy with hzero' | hnorm | hsub
  · exact False.elim (hzero hzero')
  · exact fmt.normalizedSystem_abs_ge_minSubnormalMagnitude hnorm
  · exact fmt.subnormalSystem_abs_ge_minSubnormalMagnitude hsub
theorem subnormalValue_false_one_eq (fmt : FloatingPointFormat) :
    fmt.subnormalValue false 1 =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  simp [subnormalValue, signValue]
theorem subnormalValue_one_abs_eq
    (fmt : FloatingPointFormat) (negative : Bool) :
    |fmt.subnormalValue negative 1| =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  rw [fmt.subnormalValue_abs negative 1]
  ring
/-- If mantissa `1` is an admissible subnormal mantissa, then the smallest
positive subnormal magnitude is a finite subnormal value. -/
theorem minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one
    {fmt : FloatingPointFormat} (h : fmt.subnormalMantissa 1) :
    fmt.subnormalSystem fmt.minSubnormalMagnitude := by
  refine ⟨false, 1, h, ?_⟩
  exact Eq.symm (fmt.subnormalValue_false_one_eq)
/-- If the first subnormal mantissa exists, the smallest normal is at least two
subnormal spacings from zero. -/
theorem two_mul_minSubnormalMagnitude_le_minNormalMagnitude_of_subnormalMantissa_one
    {fmt : FloatingPointFormat} (h : fmt.subnormalMantissa 1) :
    2 * fmt.minSubnormalMagnitude ≤ fmt.minNormalMagnitude := by
  have htwo_le_mantissa : (2 : ℝ) ≤ (fmt.minNormalMantissa : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt h.2)
  have hscale :
      2 * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≤
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
    mul_le_mul_of_nonneg_right htwo_le_mantissa
      (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
  rw [fmt.minNormalMantissa_scale_eq fmt.emin] at hscale
  simpa [minSubnormalMagnitude, minNormalMagnitude] using hscale
theorem subnormalValue_false_one_le_of_subnormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ} (hm : fmt.subnormalMantissa m) :
    fmt.subnormalValue false 1 ≤ fmt.subnormalValue false m := by
  have hle : (1 : ℕ) ≤ m := Nat.succ_le_of_lt hm.1
  have hleR : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hle
  simpa [subnormalValue, signValue] using
    mul_le_mul_of_nonneg_right
      hleR
      (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
theorem subnormalValue_succ_sub
    (fmt : FloatingPointFormat) (m : ℕ) :
    fmt.subnormalValue false (m + 1) - fmt.subnormalValue false m =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  simp [subnormalValue, signValue]
  ring
theorem subnormalValue_succ_spacing
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) :
    |fmt.subnormalValue negative (m + 1) -
        fmt.subnormalValue negative m| =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  cases negative
  · rw [fmt.subnormalValue_succ_sub m]
    exact abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
  · have hsub :
        fmt.subnormalValue true (m + 1) - fmt.subnormalValue true m =
          -fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
      simp [subnormalValue, signValue]
      ring
    rw [hsub, abs_neg]
    exact abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
theorem subnormalValue_boundary_sub
    (fmt : FloatingPointFormat) :
    fmt.normalizedValue false fmt.minNormalMantissa fmt.emin -
        fmt.subnormalValue false (fmt.minNormalMantissa - 1) =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  have hcast :
      ((fmt.minNormalMantissa - 1 : ℕ) : ℝ) =
        (fmt.minNormalMantissa : ℝ) - 1 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt fmt.minNormalMantissa_pos),
      Nat.cast_one]
  simp [normalizedValue, subnormalValue, signValue, hcast]
  ring
theorem subnormalValue_boundary_spacing
    (fmt : FloatingPointFormat) :
    |fmt.normalizedValue false fmt.minNormalMantissa fmt.emin -
        fmt.subnormalValue false (fmt.minNormalMantissa - 1)| =
      fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) := by
  rw [fmt.subnormalValue_boundary_sub]
  exact abs_of_pos (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
theorem normalizedValue_false_lower_power {fmt : FloatingPointFormat}
    {m : ℕ} {e : ℤ} (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (e - 1) ≤ fmt.normalizedValue false m e := by
  have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
  simpa [abs_of_pos hpos] using
    (fmt.normalizedValue_abs_lower_power (negative := false) (m := m) (e := e) hm)
theorem normalizedValue_false_lt_beta_pow {fmt : FloatingPointFormat}
    {m : ℕ} {e : ℤ} (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue false m e < fmt.betaR ^ e := by
  have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
  simpa [abs_of_pos hpos] using
    (fmt.normalizedValue_abs_lt_beta_pow (negative := false) (m := m) (e := e) hm)
theorem normalizedValue_false_lt_of_exp_lt {fmt : FloatingPointFormat}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : e < e') :
    fmt.normalizedValue false m e < fmt.normalizedValue false n e' := by
  have hone : (1 : ℝ) ≤ fmt.betaR := by
    unfold betaR
    exact_mod_cast (le_trans (by decide : 1 ≤ 2) fmt.beta_ge_two)
  have hexp_le : e ≤ e' - 1 := by
    omega
  calc
    fmt.normalizedValue false m e < fmt.betaR ^ e :=
      fmt.normalizedValue_false_lt_beta_pow hm
    _ ≤ fmt.betaR ^ (e' - 1) :=
      zpow_le_zpow_right₀ hone hexp_le
    _ ≤ fmt.normalizedValue false n e' :=
      fmt.normalizedValue_false_lower_power hn
theorem normalizedValue_true_lt_of_exp_lt {fmt : FloatingPointFormat}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (he : e < e') :
    fmt.normalizedValue true n e' < fmt.normalizedValue true m e := by
  have hpos :=
    fmt.normalizedValue_false_lt_of_exp_lt
      (m := m) (n := n) (e := e) (e' := e') hm hn he
  rw [fmt.normalizedValue_true_eq_neg_false n e',
    fmt.normalizedValue_true_eq_neg_false m e]
  exact neg_lt_neg hpos
theorem normalizedValue_false_eq_iff
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue false m e = fmt.normalizedValue false n e' ↔
      e = e' ∧ m = n := by
  constructor
  · intro h
    have heq : e = e' := by
      rcases lt_trichotomy e e' with hlt | heq | hgt
      · exact False.elim
          ((ne_of_lt (fmt.normalizedValue_false_lt_of_exp_lt hm hn hlt)) h)
      · exact heq
      · exact False.elim
          ((ne_of_gt (fmt.normalizedValue_false_lt_of_exp_lt hn hm hgt)) h)
    subst e'
    have hmn : m = n := by
      rcases lt_trichotomy m n with hlt | heq | hgt
      · exact False.elim
          ((ne_of_lt
            ((fmt.normalizedValue_sameExponent_lt_iff_false m n e).2 hlt)) h)
      · exact heq
      · exact False.elim
          ((ne_of_gt
            ((fmt.normalizedValue_sameExponent_lt_iff_false n m e).2 hgt)) h)
    exact ⟨rfl, hmn⟩
  · rintro ⟨rfl, rfl⟩
    rfl
theorem normalizedValue_true_eq_iff
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue true m e = fmt.normalizedValue true n e' ↔
      e = e' ∧ m = n := by
  constructor
  · intro h
    have hfalse :
        fmt.normalizedValue false m e =
          fmt.normalizedValue false n e' := by
      rw [fmt.normalizedValue_true_eq_neg_false m e,
        fmt.normalizedValue_true_eq_neg_false n e'] at h
      exact neg_inj.mp h
    exact (fmt.normalizedValue_false_eq_iff hm hn).1 hfalse
  · rintro ⟨rfl, rfl⟩
    rfl
theorem normalizedValue_false_ne_true
    {fmt : FloatingPointFormat} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue false m e ≠ fmt.normalizedValue true n e' := by
  intro h
  have hpos : 0 < fmt.normalizedValue true n e' := by
    simpa [h] using fmt.normalizedValue_false_pos (m := m) (e := e) hm
  exact (not_lt_of_ge (le_of_lt (fmt.normalizedValue_true_neg hn))) hpos
theorem normalizedValue_eq_sign_exp_mantissa
    {fmt : FloatingPointFormat} {negative negative' : Bool}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (h :
      fmt.normalizedValue negative m e =
        fmt.normalizedValue negative' n e') :
    negative = negative' ∧ e = e' ∧ m = n := by
  cases negative <;> cases negative'
  · rcases (fmt.normalizedValue_false_eq_iff hm hn).1 h with ⟨he, hmne⟩
    exact ⟨rfl, he, hmne⟩
  · exact False.elim ((fmt.normalizedValue_false_ne_true hm hn) h)
  · exact False.elim ((fmt.normalizedValue_false_ne_true hn hm) h.symm)
  · rcases (fmt.normalizedValue_true_eq_iff hm hn).1 h with ⟨he, hmne⟩
    exact ⟨rfl, he, hmne⟩
theorem normalizedValue_eq_iff_sign_exp_mantissa
    {fmt : FloatingPointFormat} {negative negative' : Bool}
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n) :
    fmt.normalizedValue negative m e =
        fmt.normalizedValue negative' n e' ↔
      negative = negative' ∧ e = e' ∧ m = n := by
  constructor
  · exact fmt.normalizedValue_eq_sign_exp_mantissa hm hn
  · rintro ⟨rfl, rfl, rfl⟩
    rfl
theorem normalizedValue_false_le_of_mantissa_le
    (fmt : FloatingPointFormat) {m n : ℕ} (e : ℤ) (hmn : m ≤ n) :
    fmt.normalizedValue false m e ≤ fmt.normalizedValue false n e := by
  rcases lt_or_eq_of_le hmn with hlt | heq
  · exact le_of_lt ((fmt.normalizedValue_sameExponent_lt_iff_false m n e).2 hlt)
  · subst n
    rfl
theorem normalizedValue_false_le_maxNormalMantissa
    {fmt : FloatingPointFormat} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue false m e ≤
      fmt.normalizedValue false fmt.maxNormalMantissa e := by
  have hle : m ≤ fmt.maxNormalMantissa := by
    unfold maxNormalMantissa
    exact Nat.le_sub_one_of_lt hm.2
  exact fmt.normalizedValue_false_le_of_mantissa_le e hle
theorem normalizedValue_false_minNormalMantissa_le
    {fmt : FloatingPointFormat} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.normalizedValue false fmt.minNormalMantissa e ≤
      fmt.normalizedValue false m e :=
  fmt.normalizedValue_false_le_of_mantissa_le e hm.1
theorem normalizedValue_false_minNormalMantissa_succ_eq_beta_pow
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.normalizedValue false fmt.minNormalMantissa (e + 1) =
      fmt.betaR ^ e := by
  calc
    fmt.normalizedValue false fmt.minNormalMantissa (e + 1) =
        (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
      simp [normalizedValue, signValue]
    _ = fmt.betaR ^ ((e + 1) - 1) :=
      fmt.minNormalMantissa_scale_eq (e + 1)
    _ = fmt.betaR ^ e := by
      congr 1
      ring
theorem normalizedValue_false_le_maxNormalMantissa_of_exp_le
    {fmt : FloatingPointFormat} {m : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (he : e' ≤ e) :
    fmt.normalizedValue false m e' ≤
      fmt.normalizedValue false fmt.maxNormalMantissa e := by
  by_cases hlt : e' < e
  · exact le_of_lt
      (fmt.normalizedValue_false_lt_of_exp_lt
        hm fmt.maxNormalMantissa_normalized hlt)
  · have heq : e' = e := by
      omega
    subst e'
    exact fmt.normalizedValue_false_le_maxNormalMantissa hm
theorem normalizedValue_false_minNormalMantissa_le_of_exp_le
    {fmt : FloatingPointFormat} {m : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (he : e + 1 ≤ e') :
    fmt.normalizedValue false fmt.minNormalMantissa (e + 1) ≤
      fmt.normalizedValue false m e' := by
  by_cases hlt : e + 1 < e'
  · exact le_of_lt
      (fmt.normalizedValue_false_lt_of_exp_lt
        fmt.minNormalMantissa_normalized hm hlt)
  · have heq : e' = e + 1 := by
      omega
    subst e'
    exact fmt.normalizedValue_false_minNormalMantissa_le hm
theorem normalizedValue_sameSign_no_between_succ
    (fmt : FloatingPointFormat) (negative : Bool) {m k : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmnext : fmt.normalizedMantissa (m + 1))
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue negative k e' ∧
        fmt.normalizedValue negative k e' <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue negative k e' ∧
        fmt.normalizedValue negative k e' <
          fmt.normalizedValue negative m e)) := by
  by_cases heq : e' = e
  · subst e'
    exact fmt.normalizedValue_sameExponent_no_between_succ negative m k e
  · have horder : e' < e ∨ e < e' := lt_or_gt_of_ne heq
    cases negative
    · intro hbetween
      rcases horder with hlt | hlt
      · have hk_lt_m :
            fmt.normalizedValue false k e' <
              fmt.normalizedValue false m e :=
          fmt.normalizedValue_false_lt_of_exp_lt hk hm hlt
        have hk_lt_mnext :
            fmt.normalizedValue false k e' <
              fmt.normalizedValue false (m + 1) e :=
          fmt.normalizedValue_false_lt_of_exp_lt hk hmnext hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hk_lt_m)) hbetween.1
        · exact (not_lt_of_ge (le_of_lt hk_lt_mnext)) hbetween.1
      · have hm_lt_k :
            fmt.normalizedValue false m e <
              fmt.normalizedValue false k e' :=
          fmt.normalizedValue_false_lt_of_exp_lt hm hk hlt
        have hmnext_lt_k :
            fmt.normalizedValue false (m + 1) e <
              fmt.normalizedValue false k e' :=
          fmt.normalizedValue_false_lt_of_exp_lt hmnext hk hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hmnext_lt_k)) hbetween.2
        · exact (not_lt_of_ge (le_of_lt hm_lt_k)) hbetween.2
    · intro hbetween
      rcases horder with hlt | hlt
      · have hm_lt_k :
            fmt.normalizedValue true m e <
              fmt.normalizedValue true k e' :=
          fmt.normalizedValue_true_lt_of_exp_lt hk hm hlt
        have hmnext_lt_k :
            fmt.normalizedValue true (m + 1) e <
              fmt.normalizedValue true k e' :=
          fmt.normalizedValue_true_lt_of_exp_lt hk hmnext hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hmnext_lt_k)) hbetween.2
        · exact (not_lt_of_ge (le_of_lt hm_lt_k)) hbetween.2
      · have hk_lt_m :
            fmt.normalizedValue true k e' <
              fmt.normalizedValue true m e :=
          fmt.normalizedValue_true_lt_of_exp_lt hm hk hlt
        have hk_lt_mnext :
            fmt.normalizedValue true k e' <
              fmt.normalizedValue true (m + 1) e :=
          fmt.normalizedValue_true_lt_of_exp_lt hmnext hk hlt
        rcases hbetween with hbetween | hbetween
        · exact (not_lt_of_ge (le_of_lt hk_lt_m)) hbetween.1
        · exact (not_lt_of_ge (le_of_lt hk_lt_mnext)) hbetween.1
theorem normalizedValue_oppositeSign_no_between_succ
    (fmt : FloatingPointFormat) (negative : Bool) {m k : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmnext : fmt.normalizedMantissa (m + 1))
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue (!negative) k e' ∧
        fmt.normalizedValue (!negative) k e' <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue (!negative) k e' ∧
        fmt.normalizedValue (!negative) k e' <
          fmt.normalizedValue negative m e)) := by
  cases negative
  · have hm_pos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
    have hmnext_pos :=
      fmt.normalizedValue_false_pos (m := m + 1) (e := e) hmnext
    have hk_neg := fmt.normalizedValue_true_neg (m := k) (e := e') hk
    have hk_lt_m :
        fmt.normalizedValue true k e' < fmt.normalizedValue false m e :=
      lt_trans hk_neg hm_pos
    have hk_lt_mnext :
        fmt.normalizedValue true k e' <
          fmt.normalizedValue false (m + 1) e :=
      lt_trans hk_neg hmnext_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hk_lt_m)) hbetween.1
    · exact (not_lt_of_ge (le_of_lt hk_lt_mnext)) hbetween.1
  · have hm_neg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
    have hmnext_neg :=
      fmt.normalizedValue_true_neg (m := m + 1) (e := e) hmnext
    have hk_pos := fmt.normalizedValue_false_pos (m := k) (e := e') hk
    have hm_lt_k :
        fmt.normalizedValue true m e < fmt.normalizedValue false k e' :=
      lt_trans hm_neg hk_pos
    have hmnext_lt_k :
        fmt.normalizedValue true (m + 1) e <
          fmt.normalizedValue false k e' :=
      lt_trans hmnext_neg hk_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hmnext_lt_k)) hbetween.2
    · exact (not_lt_of_ge (le_of_lt hm_lt_k)) hbetween.2
theorem normalizedValue_no_between_succ
    (fmt : FloatingPointFormat) (negative znegative : Bool)
    {m k : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m)
    (hmnext : fmt.normalizedMantissa (m + 1))
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative m e <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative (m + 1) e) ∨
      (fmt.normalizedValue negative (m + 1) e <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative m e)) := by
  cases negative <;> cases znegative
  · exact fmt.normalizedValue_sameSign_no_between_succ false hm hmnext hk
  · exact fmt.normalizedValue_oppositeSign_no_between_succ false hm hmnext hk
  · exact fmt.normalizedValue_oppositeSign_no_between_succ true hm hmnext hk
  · exact fmt.normalizedValue_sameSign_no_between_succ true hm hmnext hk
theorem normalizedValue_boundary_no_between
    (fmt : FloatingPointFormat) (negative znegative : Bool)
    {k : ℕ} {e e' : ℤ}
    (hk : fmt.normalizedMantissa k) :
    ¬ ((fmt.normalizedValue negative fmt.maxNormalMantissa e <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)) ∨
      (fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) <
          fmt.normalizedValue znegative k e' ∧
        fmt.normalizedValue znegative k e' <
          fmt.normalizedValue negative fmt.maxNormalMantissa e)) := by
  have hmax_lt_min_false :
      fmt.normalizedValue false fmt.maxNormalMantissa e <
        fmt.normalizedValue false fmt.minNormalMantissa (e + 1) :=
    fmt.normalizedValue_false_lt_of_exp_lt
      fmt.maxNormalMantissa_normalized fmt.minNormalMantissa_normalized
      (by omega)
  cases negative <;> cases znegative
  · by_cases hle : e' ≤ e
    · have hz_le_max :
          fmt.normalizedValue false k e' ≤
            fmt.normalizedValue false fmt.maxNormalMantissa e :=
        fmt.normalizedValue_false_le_maxNormalMantissa_of_exp_le hk hle
      have hz_lt_min :
          fmt.normalizedValue false k e' <
            fmt.normalizedValue false fmt.minNormalMantissa (e + 1) :=
        lt_of_le_of_lt hz_le_max hmax_lt_min_false
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge hz_le_max) hbetween.1
      · exact (not_lt_of_ge (le_of_lt hz_lt_min)) hbetween.1
    · have he_ge : e + 1 ≤ e' := by
        omega
      have hmin_le_z :
          fmt.normalizedValue false fmt.minNormalMantissa (e + 1) ≤
            fmt.normalizedValue false k e' :=
        fmt.normalizedValue_false_minNormalMantissa_le_of_exp_le hk he_ge
      have hmax_lt_z :
          fmt.normalizedValue false fmt.maxNormalMantissa e <
            fmt.normalizedValue false k e' :=
        lt_of_lt_of_le hmax_lt_min_false hmin_le_z
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge hmin_le_z) hbetween.2
      · exact (not_lt_of_ge (le_of_lt hmax_lt_z)) hbetween.2
  · have hz_neg := fmt.normalizedValue_true_neg (m := k) (e := e') hk
    have hmax_pos :=
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e) fmt.maxNormalMantissa_normalized
    have hmin_pos :=
      fmt.normalizedValue_false_pos
        (m := fmt.minNormalMantissa) (e := e + 1) fmt.minNormalMantissa_normalized
    have hz_lt_max :
        fmt.normalizedValue true k e' <
          fmt.normalizedValue false fmt.maxNormalMantissa e :=
      lt_trans hz_neg hmax_pos
    have hz_lt_min :
        fmt.normalizedValue true k e' <
          fmt.normalizedValue false fmt.minNormalMantissa (e + 1) :=
      lt_trans hz_neg hmin_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hz_lt_max)) hbetween.1
    · exact (not_lt_of_ge (le_of_lt hz_lt_min)) hbetween.1
  · have hmax_neg :=
      fmt.normalizedValue_true_neg
        (m := fmt.maxNormalMantissa) (e := e) fmt.maxNormalMantissa_normalized
    have hmin_neg :=
      fmt.normalizedValue_true_neg
        (m := fmt.minNormalMantissa) (e := e + 1) fmt.minNormalMantissa_normalized
    have hz_pos := fmt.normalizedValue_false_pos (m := k) (e := e') hk
    have hmax_lt_z :
        fmt.normalizedValue true fmt.maxNormalMantissa e <
          fmt.normalizedValue false k e' :=
      lt_trans hmax_neg hz_pos
    have hmin_lt_z :
        fmt.normalizedValue true fmt.minNormalMantissa (e + 1) <
          fmt.normalizedValue false k e' :=
      lt_trans hmin_neg hz_pos
    intro hbetween
    rcases hbetween with hbetween | hbetween
    · exact (not_lt_of_ge (le_of_lt hmin_lt_z)) hbetween.2
    · exact (not_lt_of_ge (le_of_lt hmax_lt_z)) hbetween.2
  · have hmin_true_lt_max_true :
        fmt.normalizedValue true fmt.minNormalMantissa (e + 1) <
          fmt.normalizedValue true fmt.maxNormalMantissa e := by
      rw [fmt.normalizedValue_true_eq_neg_false fmt.minNormalMantissa (e + 1),
        fmt.normalizedValue_true_eq_neg_false fmt.maxNormalMantissa e]
      exact neg_lt_neg hmax_lt_min_false
    by_cases hle : e' ≤ e
    · have hz_le_max_false :
          fmt.normalizedValue false k e' ≤
            fmt.normalizedValue false fmt.maxNormalMantissa e :=
        fmt.normalizedValue_false_le_maxNormalMantissa_of_exp_le hk hle
      have hmax_true_le_z :
          fmt.normalizedValue true fmt.maxNormalMantissa e ≤
            fmt.normalizedValue true k e' := by
        rw [fmt.normalizedValue_true_eq_neg_false fmt.maxNormalMantissa e,
          fmt.normalizedValue_true_eq_neg_false k e']
        exact neg_le_neg hz_le_max_false
      have hmin_true_lt_z :
          fmt.normalizedValue true fmt.minNormalMantissa (e + 1) <
            fmt.normalizedValue true k e' :=
        lt_of_lt_of_le hmin_true_lt_max_true hmax_true_le_z
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge (le_of_lt hmin_true_lt_z)) hbetween.2
      · exact (not_lt_of_ge hmax_true_le_z) hbetween.2
    · have he_ge : e + 1 ≤ e' := by
        omega
      have hmin_le_z_false :
          fmt.normalizedValue false fmt.minNormalMantissa (e + 1) ≤
            fmt.normalizedValue false k e' :=
        fmt.normalizedValue_false_minNormalMantissa_le_of_exp_le hk he_ge
      have hz_true_le_min :
          fmt.normalizedValue true k e' ≤
            fmt.normalizedValue true fmt.minNormalMantissa (e + 1) := by
        rw [fmt.normalizedValue_true_eq_neg_false k e',
          fmt.normalizedValue_true_eq_neg_false fmt.minNormalMantissa (e + 1)]
        exact neg_le_neg hmin_le_z_false
      have hz_true_lt_max :
          fmt.normalizedValue true k e' <
            fmt.normalizedValue true fmt.maxNormalMantissa e :=
        lt_of_le_of_lt hz_true_le_min hmin_true_lt_max_true
      intro hbetween
      rcases hbetween with hbetween | hbetween
      · exact (not_lt_of_ge (le_of_lt hz_true_lt_max)) hbetween.1
      · exact (not_lt_of_ge hz_true_le_min) hbetween.1
theorem machineEpsilon_mul_lower_power_eq (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.machineEpsilon * fmt.betaR ^ (e - 1) =
      fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  unfold machineEpsilon
  calc
    fmt.betaR ^ (1 - (fmt.t : ℤ)) * fmt.betaR ^ (e - 1) =
        fmt.betaR ^ ((1 - (fmt.t : ℤ)) + (e - 1)) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      congr 1
      ring
theorem beta_inv_machineEpsilon_mul_upper_power_eq
    (fmt : FloatingPointFormat) (e : ℤ) :
    (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) * fmt.betaR ^ e =
      fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hbase : fmt.betaR ≠ 0 := ne_of_gt fmt.betaR_pos
  unfold machineEpsilon
  calc
    (fmt.betaR ^ (-1 : ℤ) * fmt.betaR ^ (1 - (fmt.t : ℤ))) *
        fmt.betaR ^ e =
        fmt.betaR ^ ((-1 : ℤ) + (1 - (fmt.t : ℤ))) * fmt.betaR ^ e := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (((-1 : ℤ) + (1 - (fmt.t : ℤ))) + e) := by
      rw [← zpow_add₀ hbase]
    _ = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      congr 1
      ring
theorem ulpAtExponent_eq_machineEpsilon_mul_lower_power
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.ulpAtExponent e = fmt.machineEpsilon * fmt.betaR ^ (e - 1) := by
  simpa [ulpAtExponent] using
    (fmt.machineEpsilon_mul_lower_power_eq e).symm
theorem ulpAtExponent_eq_beta_inv_machineEpsilon_mul_upper_power
    (fmt : FloatingPointFormat) (e : ℤ) :
    fmt.ulpAtExponent e =
      (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) * fmt.betaR ^ e := by
  simpa [ulpAtExponent] using
    (fmt.beta_inv_machineEpsilon_mul_upper_power_eq e).symm
theorem normalizedValue_spacing_bounds
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon *
        |fmt.normalizedValue negative m e| ≤
      fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
    fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
      fmt.machineEpsilon * |fmt.normalizedValue negative m e| := by
  have hmag :=
    fmt.normalizedValue_abs_between_beta_powers
      (negative := negative) (m := m) (e := e) hm
  constructor
  · have hfactor_pos :
        0 < fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon := by
      unfold machineEpsilon
      exact mul_pos (fmt.betaR_zpow_pos (-1 : ℤ))
        (fmt.betaR_zpow_pos (1 - (fmt.t : ℤ)))
    have hlt :
        (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) *
            |fmt.normalizedValue negative m e| <
          (fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon) *
            fmt.betaR ^ e :=
      mul_lt_mul_of_pos_left hmag.2 hfactor_pos
    have hscale :
        fmt.betaR⁻¹ * fmt.machineEpsilon * fmt.betaR ^ e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simpa using fmt.beta_inv_machineEpsilon_mul_upper_power_eq e
    exact le_of_lt (by simpa [hscale] using hlt)
  · have heps_nonneg : 0 ≤ fmt.machineEpsilon := by
      unfold machineEpsilon
      exact fmt.betaR_zpow_nonneg (1 - (fmt.t : ℤ))
    have hle :
        fmt.machineEpsilon * fmt.betaR ^ (e - 1) ≤
          fmt.machineEpsilon * |fmt.normalizedValue negative m e| :=
      mul_le_mul_of_nonneg_left hmag.1 heps_nonneg
    have hscale := fmt.machineEpsilon_mul_lower_power_eq e
    simpa [hscale] using hle
theorem normalizedValue_wobblingPrecision_bounds
    {fmt : FloatingPointFormat} {negative : Bool} {m : ℕ} {e : ℤ}
    (hm : fmt.normalizedMantissa m) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon *
        |fmt.normalizedValue negative m e| ≤ fmt.ulpAtExponent e ∧
    fmt.ulpAtExponent e ≤
      fmt.machineEpsilon * |fmt.normalizedValue negative m e| := by
  simpa [ulpAtExponent] using
    (fmt.normalizedValue_spacing_bounds (negative := negative) (m := m)
      (e := e) hm)
theorem normalizedValue_succ_sub_sameExponent (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.normalizedValue negative (m + 1) e -
      fmt.normalizedValue negative m e =
        fmt.signValue negative * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  unfold normalizedValue
  norm_num
  ring
theorem normalizedValue_succ_spacing (fmt : FloatingPointFormat)
    (negative : Bool) (m : ℕ) (e : ℤ) :
    |fmt.normalizedValue negative (m + 1) e -
      fmt.normalizedValue negative m e| =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_succ_sub_sameExponent negative m e, abs_mul,
    fmt.signValue_abs negative,
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring
theorem normalizedValue_succ_spacing_eq_ulpAtExponent
    (fmt : FloatingPointFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    |fmt.normalizedValue negative (m + 1) e -
      fmt.normalizedValue negative m e| = fmt.ulpAtExponent e := by
  simpa [ulpAtExponent] using
    fmt.normalizedValue_succ_spacing negative m e
theorem normalizedValue_boundary_sub (fmt : FloatingPointFormat)
    (negative : Bool) (e : ℤ) :
    fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) -
      fmt.normalizedValue negative fmt.maxNormalMantissa e =
        fmt.signValue negative * fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  have hmin :
      (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) = fmt.betaR ^ e := by
    calc
      (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
            fmt.betaR ^ ((e + 1) - 1) := by
        exact fmt.minNormalMantissa_scale_eq (e + 1)
      _ = fmt.betaR ^ e := by
        congr 1
        ring
  have hmax := fmt.maxNormalMantissa_scale_eq e
  unfold normalizedValue
  calc
    fmt.signValue negative * ↑fmt.minNormalMantissa *
          fmt.betaR ^ ((e + 1) - ↑fmt.t) -
        fmt.signValue negative * ↑fmt.maxNormalMantissa *
          fmt.betaR ^ (e - ↑fmt.t) =
        fmt.signValue negative *
          (↑fmt.minNormalMantissa * fmt.betaR ^ ((e + 1) - ↑fmt.t) -
            ↑fmt.maxNormalMantissa * fmt.betaR ^ (e - ↑fmt.t)) := by
      ring
    _ = fmt.signValue negative *
        (fmt.betaR ^ e - (fmt.betaR ^ e - fmt.betaR ^ (e - ↑fmt.t))) := by
      rw [hmin, hmax]
    _ = fmt.signValue negative * fmt.betaR ^ (e - ↑fmt.t) := by
      ring
theorem normalizedValue_boundary_spacing (fmt : FloatingPointFormat)
    (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) -
      fmt.normalizedValue negative fmt.maxNormalMantissa e| =
        fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rw [fmt.normalizedValue_boundary_sub negative e, abs_mul,
    fmt.signValue_abs negative,
    abs_of_pos (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))]
  ring
theorem normalizedValue_boundary_spacing_eq_ulpAtExponent
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1) -
      fmt.normalizedValue negative fmt.maxNormalMantissa e| =
        fmt.ulpAtExponent e := by
  simpa [ulpAtExponent] using
    fmt.normalizedValue_boundary_spacing negative e
theorem normalizedValue_boundary_min_spacing_bounds
    (fmt : FloatingPointFormat) (negative : Bool) (e : ℤ) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon *
        |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| ≤
      fmt.betaR ^ (e - (fmt.t : ℤ)) ∧
    fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
      fmt.machineEpsilon *
        |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| := by
  have habs :
      |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
        fmt.betaR ^ e := by
    rw [fmt.normalizedValue_abs negative fmt.minNormalMantissa (e + 1)]
    calc
      (fmt.minNormalMantissa : ℝ) *
          fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) =
          fmt.betaR ^ ((e + 1) - 1) := by
        exact fmt.minNormalMantissa_scale_eq (e + 1)
      _ = fmt.betaR ^ e := by
        congr 1
        ring
  constructor
  · have hscale :
        fmt.betaR⁻¹ * fmt.machineEpsilon * fmt.betaR ^ e =
          fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      simpa using fmt.beta_inv_machineEpsilon_mul_upper_power_eq e
    simp [habs, hscale]
  · have hone : (1 : ℝ) ≤ fmt.betaR := by
      unfold betaR
      exact_mod_cast (le_trans (by decide : 1 ≤ 2) fmt.beta_ge_two)
    have hexp_le : e - (fmt.t : ℤ) ≤ e + 1 - (fmt.t : ℤ) := by
      exact sub_le_sub_right
        (le_add_of_nonneg_right (by decide : (0 : ℤ) ≤ 1)) (fmt.t : ℤ)
    have hpow_le :
        fmt.betaR ^ (e - (fmt.t : ℤ)) ≤
          fmt.betaR ^ (e + 1 - (fmt.t : ℤ)) :=
      zpow_le_zpow_right₀ hone hexp_le
    have hscale :
        fmt.machineEpsilon *
            |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
          fmt.betaR ^ (e + 1 - (fmt.t : ℤ)) := by
      calc
        fmt.machineEpsilon *
            |fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
            fmt.machineEpsilon * fmt.betaR ^ e := by
          rw [habs]
        _ = fmt.machineEpsilon * fmt.betaR ^ ((e + 1) - 1) := by
          congr 1
          congr 1
          ring
        _ = fmt.betaR ^ ((e + 1) - (fmt.t : ℤ)) := by
          exact fmt.machineEpsilon_mul_lower_power_eq (e + 1)
    simpa [hscale] using hpow_le
theorem sameExponentAdjacentNormalized_abs_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rcases h with ⟨negative, m, e, _hm, _hmnext, hxy⟩
  refine ⟨e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    rw [abs_sub_comm]
    exact fmt.normalizedValue_succ_spacing negative m e
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_succ_spacing negative m e
theorem sameExponentAdjacentNormalized_abs_sub_eq_ulpAtExponent
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.ulpAtExponent e := by
  rcases fmt.sameExponentAdjacentNormalized_abs_sub h with ⟨e, hspace⟩
  exact ⟨e, by simpa [ulpAtExponent] using hspace⟩
theorem boundaryAdjacentNormalized_abs_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rcases h with ⟨negative, e, hxy⟩
  refine ⟨e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    rw [abs_sub_comm]
    exact fmt.normalizedValue_boundary_spacing negative e
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_boundary_spacing negative e
theorem boundaryAdjacentNormalized_abs_sub_eq_ulpAtExponent
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.ulpAtExponent e := by
  rcases fmt.boundaryAdjacentNormalized_abs_sub h with ⟨e, hspace⟩
  exact ⟨e, by simpa [ulpAtExponent] using hspace⟩
theorem adjacentNormalized_abs_sub
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_abs_sub hsame
  · exact boundaryAdjacentNormalized_abs_sub hboundary
theorem adjacentNormalized_abs_sub_eq_ulpAtExponent
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    ∃ e : ℤ, |x - y| = fmt.ulpAtExponent e := by
  rcases h with hsame | hboundary
  · exact fmt.sameExponentAdjacentNormalized_abs_sub_eq_ulpAtExponent hsame
  · exact fmt.boundaryAdjacentNormalized_abs_sub_eq_ulpAtExponent hboundary
theorem sameExponentAdjacentNormalized_left_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, m, e, hm, rfl⟩
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, m + 1, e, hmnext, rfl⟩
theorem sameExponentAdjacentNormalized_right_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, m + 1, e, hmnext, rfl⟩
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, m, e, hm, rfl⟩
theorem boundaryAdjacentNormalized_left_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x := by
  rcases h with ⟨negative, e, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, fmt.maxNormalMantissa, e,
      fmt.maxNormalMantissa_normalized, rfl⟩
  · rcases hxy with ⟨rfl, _⟩
    exact ⟨negative, fmt.minNormalMantissa, e + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
theorem boundaryAdjacentNormalized_right_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases h with ⟨negative, e, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, fmt.minNormalMantissa, e + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
  · rcases hxy with ⟨_, rfl⟩
    exact ⟨negative, fmt.maxNormalMantissa, e,
      fmt.maxNormalMantissa_normalized, rfl⟩
theorem adjacentNormalized_left_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_left_mem hsame
  · exact boundaryAdjacentNormalized_left_mem hboundary
theorem adjacentNormalized_right_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.unboundedNormalizedSystem y := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_right_mem hsame
  · exact boundaryAdjacentNormalized_right_mem hboundary
theorem adjacentNormalized_ne
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    x ≠ y := by
  intro hxy
  rcases adjacentNormalized_abs_sub h with ⟨e, hspace⟩
  have hzero : (0 : ℝ) = fmt.betaR ^ (e - (fmt.t : ℤ)) := by
    simpa [hxy] using hspace
  exact (ne_of_gt (fmt.betaR_zpow_pos (e - (fmt.t : ℤ)))) hzero.symm
theorem adjacentNormalized_endpoint_data
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.unboundedNormalizedSystem x ∧
      fmt.unboundedNormalizedSystem y ∧ x ≠ y :=
  ⟨adjacentNormalized_left_mem h,
    adjacentNormalized_right_mem h,
    adjacentNormalized_ne h⟩
theorem realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y)
    (hbetween : ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x))) :
    fmt.realOrderAdjacentNormalized x y := by
  exact ⟨adjacentNormalized_left_mem h,
    adjacentNormalized_right_mem h,
    adjacentNormalized_ne h,
    hbetween⟩
theorem realOrderAdjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized y x := by
  refine ⟨h.2.1, h.1, h.2.2.1.symm, ?_⟩
  intro z hz hbetween
  apply h.2.2.2 z hz
  rcases hbetween with hbetween | hbetween
  · exact Or.inr hbetween
  · exact Or.inl hbetween
theorem realOrderAdjacentNormalized_neg_ordered
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized (-y) (-x) := by
  refine
    ⟨fmt.unboundedNormalizedSystem_neg h.2.1,
      fmt.unboundedNormalizedSystem_neg h.1, ?_, ?_⟩
  · intro hneg_eq
    apply h.2.2.1
    linarith
  · intro z hz hbetween
    have hzneg : fmt.unboundedNormalizedSystem (-z) :=
      fmt.unboundedNormalizedSystem_neg hz
    apply h.2.2.2 (-z) hzneg
    rcases hbetween with hbetween | hbetween
    · rcases hbetween with ⟨hyz, hzx⟩
      exact Or.inl ⟨by linarith, by linarith⟩
    · rcases hbetween with ⟨hxz, hzy⟩
      exact Or.inr ⟨by linarith, by linarith⟩
theorem sameExponentAdjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.sameExponentAdjacentNormalized y x := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  refine ⟨negative, m, e, hm, hmnext, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl⟩
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
theorem boundaryAdjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.boundaryAdjacentNormalized y x := by
  rcases h with ⟨negative, e, hxy⟩
  refine ⟨negative, e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inr ⟨rfl, rfl⟩
  · rcases hxy with ⟨rfl, rfl⟩
    exact Or.inl ⟨rfl, rfl⟩
theorem adjacentNormalized_symm
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.adjacentNormalized y x := by
  rcases h with hsame | hboundary
  · exact Or.inl (fmt.sameExponentAdjacentNormalized_symm hsame)
  · exact Or.inr (fmt.boundaryAdjacentNormalized_symm hboundary)
theorem sameExponentAdjacentNormalized_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.sameExponentAdjacentNormalized (-x) (-y) := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  refine ⟨!negative, m, e, hm, hmnext, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) m e := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative m e]
    have hyneg :
        -y = fmt.normalizedValue (!negative) (m + 1) e := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative (m + 1) e]
    exact Or.inl ⟨hxneg, hyneg⟩
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) (m + 1) e := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative (m + 1) e]
    have hyneg :
        -y = fmt.normalizedValue (!negative) m e := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative m e]
    exact Or.inr ⟨hxneg, hyneg⟩
theorem boundaryAdjacentNormalized_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.boundaryAdjacentNormalized (-x) (-y) := by
  rcases h with ⟨negative, e, hxy⟩
  refine ⟨!negative, e, ?_⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) fmt.maxNormalMantissa e := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative fmt.maxNormalMantissa e]
    have hyneg :
        -y = fmt.normalizedValue (!negative) fmt.minNormalMantissa (e + 1) := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative fmt.minNormalMantissa (e + 1)]
    exact Or.inl ⟨hxneg, hyneg⟩
  · rcases hxy with ⟨hx, hy⟩
    have hxneg :
        -x = fmt.normalizedValue (!negative) fmt.minNormalMantissa (e + 1) := by
      rw [hx, ← fmt.normalizedValue_not_eq_neg negative fmt.minNormalMantissa (e + 1)]
    have hyneg :
        -y = fmt.normalizedValue (!negative) fmt.maxNormalMantissa e := by
      rw [hy, ← fmt.normalizedValue_not_eq_neg negative fmt.maxNormalMantissa e]
    exact Or.inr ⟨hxneg, hyneg⟩
theorem adjacentNormalized_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.adjacentNormalized (-x) (-y) := by
  rcases h with hsame | hboundary
  · exact Or.inl (fmt.sameExponentAdjacentNormalized_neg hsame)
  · exact Or.inr (fmt.boundaryAdjacentNormalized_neg hboundary)
theorem sameExponentAdjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  intro z hz
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hz with ⟨znegative, k, e', hk, rfl⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_no_between_succ negative znegative hm hmnext hk
  · rcases hxy with ⟨rfl, rfl⟩
    have hnb :=
      fmt.normalizedValue_no_between_succ
        negative znegative (e := e) (e' := e') hm hmnext hk
    intro hbetween
    apply hnb
    rcases hbetween with hbetween | hbetween
    · exact Or.inr hbetween
    · exact Or.inl hbetween
theorem realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y :=
  fmt.realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    (Or.inl h) (fmt.sameExponentAdjacentNormalized_no_between h)
theorem boundaryAdjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  intro z hz
  rcases h with ⟨negative, e, hxy⟩
  rcases hz with ⟨znegative, k, e', hk, rfl⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    exact fmt.normalizedValue_boundary_no_between negative znegative hk
  · rcases hxy with ⟨rfl, rfl⟩
    have hnb :=
      fmt.normalizedValue_boundary_no_between
        negative znegative (e := e) (e' := e') hk
    intro hbetween
    apply hnb
    rcases hbetween with hbetween | hbetween
    · exact Or.inr hbetween
    · exact Or.inl hbetween
theorem realOrderAdjacentNormalized_of_boundaryAdjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y :=
  fmt.realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    (Or.inr h) (fmt.boundaryAdjacentNormalized_no_between h)
theorem adjacentNormalized_no_between
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    ∀ z, fmt.unboundedNormalizedSystem z →
      ¬ ((x < z ∧ z < y) ∨ (y < z ∧ z < x)) := by
  rcases h with hsame | hboundary
  · exact fmt.sameExponentAdjacentNormalized_no_between hsame
  · exact fmt.boundaryAdjacentNormalized_no_between hboundary
theorem realOrderAdjacentNormalized_of_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y :=
  fmt.realOrderAdjacentNormalized_of_adjacentNormalized_no_between
    h (fmt.adjacentNormalized_no_between h)
theorem realOrderAdjacentNormalized_same_sign_of_representations
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {negative znegative : Bool} {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue negative m e)
    (hy : y = fmt.normalizedValue znegative n e') :
    negative = znegative := by
  cases negative <;> cases znegative
  · rfl
  · exfalso
    let z := fmt.normalizedValue false fmt.maxNormalMantissa (e - 1)
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, fmt.maxNormalMantissa, e - 1,
        fmt.maxNormalMantissa_normalized, rfl⟩
    have hz_pos :
        0 < z :=
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e - 1)
        fmt.maxNormalMantissa_normalized
    have hy_neg : y < 0 := by
      rw [hy]
      exact fmt.normalizedValue_true_neg (m := n) (e := e') hn
    have hz_lt_x : z < x := by
      rw [hx]
      exact fmt.normalizedValue_false_lt_of_exp_lt
        fmt.maxNormalMantissa_normalized hm (by omega)
    exact (h.2.2.2 z hz_mem) (Or.inr ⟨lt_trans hy_neg hz_pos, hz_lt_x⟩)
  · exfalso
    let z := fmt.normalizedValue false fmt.maxNormalMantissa (e' - 1)
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, fmt.maxNormalMantissa, e' - 1,
        fmt.maxNormalMantissa_normalized, rfl⟩
    have hz_pos :
        0 < z :=
      fmt.normalizedValue_false_pos
        (m := fmt.maxNormalMantissa) (e := e' - 1)
        fmt.maxNormalMantissa_normalized
    have hx_neg : x < 0 := by
      rw [hx]
      exact fmt.normalizedValue_true_neg (m := m) (e := e) hm
    have hz_lt_y : z < y := by
      rw [hy]
      exact fmt.normalizedValue_false_lt_of_exp_lt
        fmt.maxNormalMantissa_normalized hn (by omega)
    exact (h.2.2.2 z hz_mem) (Or.inl ⟨lt_trans hx_neg hz_pos, hz_lt_y⟩)
  · rfl
theorem realOrderAdjacentNormalized_false_ordered_exp_ge
    {fmt : FloatingPointFormat} {x y : ℝ}
    (_h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) :
    e ≤ e' := by
  by_contra hnot
  have hlt : e' < e := by
    omega
  have hy_lt_x : y < x := by
    rw [hx, hy]
    exact fmt.normalizedValue_false_lt_of_exp_lt hn hm hlt
  exact (not_lt_of_ge (le_of_lt hy_lt_x)) hxy
theorem realOrderAdjacentNormalized_false_ordered_exp_le_succ
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (_hxy : x < y) :
    e' ≤ e + 1 := by
  by_contra hnot
  have hgap : e + 1 < e' := by
    omega
  let z := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
  have hz_mem : fmt.unboundedNormalizedSystem z :=
    ⟨false, fmt.minNormalMantissa, e + 1,
      fmt.minNormalMantissa_normalized, rfl⟩
  have hx_lt_z : x < z := by
    rw [hx]
    change fmt.normalizedValue false m e <
      fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
    rw [fmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow e]
    exact fmt.normalizedValue_false_lt_beta_pow hm
  have hz_lt_y : z < y := by
    rw [hy]
    exact fmt.normalizedValue_false_lt_of_exp_lt
      fmt.minNormalMantissa_normalized hn hgap
  exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)
theorem realOrderAdjacentNormalized_false_ordered_exp_eq_or_succ
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) :
    e' = e ∨ e' = e + 1 := by
  have hge :=
    fmt.realOrderAdjacentNormalized_false_ordered_exp_ge h hm hn hx hy hxy
  have hle :=
    fmt.realOrderAdjacentNormalized_false_ordered_exp_le_succ h hm hn hx hy hxy
  omega
theorem realOrderAdjacentNormalized_false_ordered_same_exp_mantissa_succ
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) (he : e' = e) :
    n = m + 1 := by
  subst e'
  have hval : fmt.normalizedValue false m e <
      fmt.normalizedValue false n e := by
    simpa [hx, hy] using hxy
  have hmn : m < n :=
    (fmt.normalizedValue_sameExponent_lt_iff_false m n e).mp hval
  by_contra hne
  have hgap : m + 1 < n := by
    omega
  have hmnext : fmt.normalizedMantissa (m + 1) :=
    ⟨le_trans hm.1 (Nat.le_succ m), lt_trans hgap hn.2⟩
  let z := fmt.normalizedValue false (m + 1) e
  have hz_mem : fmt.unboundedNormalizedSystem z :=
    ⟨false, m + 1, e, hmnext, rfl⟩
  have hx_lt_z : x < z := by
    rw [hx]
    exact (fmt.normalizedValue_sameExponent_lt_iff_false m (m + 1) e).2
      (Nat.lt_succ_self m)
  have hz_lt_y : z < y := by
    rw [hy]
    exact (fmt.normalizedValue_sameExponent_lt_iff_false (m + 1) n e).2 hgap
  exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)
theorem realOrderAdjacentNormalized_false_ordered_succ_exp_mantissa_boundary
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (he : e' = e + 1) :
    m = fmt.maxNormalMantissa ∧ n = fmt.minNormalMantissa := by
  subst e'
  constructor
  · by_contra hmmax
    have hm_le_max : m ≤ fmt.maxNormalMantissa := by
      unfold maxNormalMantissa
      exact Nat.le_sub_one_of_lt hm.2
    have hm_lt_max : m < fmt.maxNormalMantissa :=
      lt_of_le_of_ne hm_le_max hmmax
    have hmnext : fmt.normalizedMantissa (m + 1) :=
      ⟨le_trans hm.1 (Nat.le_succ m),
        lt_of_le_of_lt (Nat.succ_le_of_lt hm_lt_max)
          fmt.maxNormalMantissa_lt_mantissaBound⟩
    let z := fmt.normalizedValue false (m + 1) e
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, m + 1, e, hmnext, rfl⟩
    have hx_lt_z : x < z := by
      rw [hx]
      exact (fmt.normalizedValue_sameExponent_lt_iff_false m (m + 1) e).2
        (Nat.lt_succ_self m)
    have hz_lt_y : z < y := by
      rw [hy]
      exact fmt.normalizedValue_false_lt_of_exp_lt hmnext hn (by omega)
    exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)
  · by_contra hnmin
    have hmin_ne_n : fmt.minNormalMantissa ≠ n := by
      intro hmin_eq_n
      exact hnmin hmin_eq_n.symm
    have hmin_lt_n : fmt.minNormalMantissa < n :=
      lt_of_le_of_ne hn.1 hmin_ne_n
    let z := fmt.normalizedValue false fmt.minNormalMantissa (e + 1)
    have hz_mem : fmt.unboundedNormalizedSystem z :=
      ⟨false, fmt.minNormalMantissa, e + 1,
        fmt.minNormalMantissa_normalized, rfl⟩
    have hx_lt_z : x < z := by
      rw [hx]
      exact fmt.normalizedValue_false_lt_of_exp_lt
        hm fmt.minNormalMantissa_normalized (by omega)
    have hz_lt_y : z < y := by
      rw [hy]
      exact (fmt.normalizedValue_sameExponent_lt_iff_false
        fmt.minNormalMantissa n (e + 1)).2 hmin_lt_n
    exact (h.2.2.2 z hz_mem) (Or.inl ⟨hx_lt_z, hz_lt_y⟩)
theorem realOrderAdjacentNormalized_false_ordered_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e')
    (hxy : x < y) :
    fmt.adjacentNormalized x y := by
  rcases fmt.realOrderAdjacentNormalized_false_ordered_exp_eq_or_succ
      h hm hn hx hy hxy with he | hsucc
  · have hn_succ :=
      fmt.realOrderAdjacentNormalized_false_ordered_same_exp_mantissa_succ
        h hm hn hx hy hxy he
    have hmnext : fmt.normalizedMantissa (m + 1) := by
      simpa [hn_succ] using hn
    have hy_succ : y = fmt.normalizedValue false (m + 1) e := by
      simpa [hn_succ, he] using hy
    exact Or.inl
      ⟨false, m, e, hm, hmnext, Or.inl ⟨hx, hy_succ⟩⟩
  · have hboundary :=
      fmt.realOrderAdjacentNormalized_false_ordered_succ_exp_mantissa_boundary
        h hm hn hx hy hsucc
    rcases hboundary with ⟨hmmax, hnmin⟩
    have hx_max : x = fmt.normalizedValue false fmt.maxNormalMantissa e := by
      simpa [hmmax] using hx
    have hy_min :
        y = fmt.normalizedValue false fmt.minNormalMantissa (e + 1) := by
      simpa [hnmin, hsucc] using hy
    exact Or.inr ⟨false, e, Or.inl ⟨hx_max, hy_min⟩⟩
theorem realOrderAdjacentNormalized_false_representations_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue false m e)
    (hy : y = fmt.normalizedValue false n e') :
    fmt.adjacentNormalized x y := by
  rcases lt_or_gt_of_ne h.2.2.1 with hxy | hyx
  · exact fmt.realOrderAdjacentNormalized_false_ordered_adjacentNormalized
      h hm hn hx hy hxy
  · exact fmt.adjacentNormalized_symm
      (fmt.realOrderAdjacentNormalized_false_ordered_adjacentNormalized
        (fmt.realOrderAdjacentNormalized_symm h) hn hm hy hx hyx)
theorem realOrderAdjacentNormalized_false_of_true_representations
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue true m e)
    (hy : y = fmt.normalizedValue true n e') :
    fmt.realOrderAdjacentNormalized
      (fmt.normalizedValue false m e)
      (fmt.normalizedValue false n e') := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false n e'
  have hx_neg : x = -a := by
    dsimp [a]
    rw [hx, fmt.normalizedValue_true_eq_neg_false m e]
  have hy_neg : y = -b := by
    dsimp [b]
    rw [hy, fmt.normalizedValue_true_eq_neg_false n e']
  refine ⟨⟨false, m, e, hm, rfl⟩, ⟨false, n, e', hn, rfl⟩, ?_, ?_⟩
  · intro hab
    have hab_ab : a = b := by
      simpa [a, b] using hab
    apply h.2.2.1
    rw [hx_neg, hy_neg, hab_ab]
  · intro z hz hbetween
    rcases hz with ⟨negative, k, ez, hk, rfl⟩
    let zneg := fmt.normalizedValue (!negative) k ez
    have hzneg_mem : fmt.unboundedNormalizedSystem zneg :=
      ⟨!negative, k, ez, hk, rfl⟩
    have hzneg_eq :
        zneg = -fmt.normalizedValue negative k ez :=
      fmt.normalizedValue_not_eq_neg negative k ez
    apply h.2.2.2 zneg hzneg_mem
    rcases hbetween with hbetween | hbetween
    · rcases hbetween with ⟨haz, hzb⟩
      have hy_lt_zneg : y < zneg := by
        rw [hy_neg, hzneg_eq]
        exact neg_lt_neg hzb
      have zneg_lt_x : zneg < x := by
        rw [hx_neg, hzneg_eq]
        exact neg_lt_neg haz
      exact Or.inr ⟨hy_lt_zneg, zneg_lt_x⟩
    · rcases hbetween with ⟨hbz, hza⟩
      have hx_lt_zneg : x < zneg := by
        rw [hx_neg, hzneg_eq]
        exact neg_lt_neg hza
      have zneg_lt_y : zneg < y := by
        rw [hy_neg, hzneg_eq]
        exact neg_lt_neg hbz
      exact Or.inl ⟨hx_lt_zneg, zneg_lt_y⟩
theorem realOrderAdjacentNormalized_true_representations_adjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y)
    {m n : ℕ} {e e' : ℤ}
    (hm : fmt.normalizedMantissa m) (hn : fmt.normalizedMantissa n)
    (hx : x = fmt.normalizedValue true m e)
    (hy : y = fmt.normalizedValue true n e') :
    fmt.adjacentNormalized x y := by
  let a := fmt.normalizedValue false m e
  let b := fmt.normalizedValue false n e'
  have hx_neg : x = -a := by
    dsimp [a]
    rw [hx, fmt.normalizedValue_true_eq_neg_false m e]
  have hy_neg : y = -b := by
    dsimp [b]
    rw [hy, fmt.normalizedValue_true_eq_neg_false n e']
  have hpos :=
    fmt.realOrderAdjacentNormalized_false_of_true_representations h hm hn hx hy
  have hpos_adj :
      fmt.adjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_false_representations_adjacentNormalized
      hpos hm hn rfl rfl
  have hneg_adj : fmt.adjacentNormalized (-a) (-b) :=
    fmt.adjacentNormalized_neg hpos_adj
  rw [hx_neg, hy_neg]
  exact hneg_adj
theorem adjacentNormalized_of_realOrderAdjacentNormalized
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.adjacentNormalized x y := by
  rcases h.1 with ⟨negative, m, e, hm, hx⟩
  rcases h.2.1 with ⟨znegative, n, e', hn, hy⟩
  have hsign :=
    fmt.realOrderAdjacentNormalized_same_sign_of_representations
      h hm hn hx hy
  subst znegative
  cases negative
  · exact fmt.realOrderAdjacentNormalized_false_representations_adjacentNormalized
      h hm hn hx hy
  · exact fmt.realOrderAdjacentNormalized_true_representations_adjacentNormalized
      h hm hn hx hy
theorem sameExponentAdjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.sameExponentAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| := by
  rcases h with ⟨negative, m, e, hm, hmnext, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    have hb :=
      fmt.normalizedValue_spacing_bounds
        (negative := negative) (m := m) (e := e) hm
    have hspace :
        |fmt.normalizedValue negative m e -
          fmt.normalizedValue negative (m + 1) e| =
            fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [abs_sub_comm]
      exact fmt.normalizedValue_succ_spacing negative m e
    constructor
    · simpa [hspace] using hb.1
    · simpa [hspace] using hb.2
  · rcases hxy with ⟨rfl, rfl⟩
    have hb :=
      fmt.normalizedValue_spacing_bounds
        (negative := negative) (m := m + 1) (e := e) hmnext
    constructor
    · simpa [fmt.normalizedValue_succ_spacing negative m e] using hb.1
    · simpa [fmt.normalizedValue_succ_spacing negative m e] using hb.2
theorem boundaryAdjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.boundaryAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| := by
  rcases h with ⟨negative, e, hxy⟩
  rcases hxy with hxy | hxy
  · rcases hxy with ⟨rfl, rfl⟩
    have hb :=
      fmt.normalizedValue_spacing_bounds
        (negative := negative) (m := fmt.maxNormalMantissa) (e := e)
        fmt.maxNormalMantissa_normalized
    have hspace :
        |fmt.normalizedValue negative fmt.maxNormalMantissa e -
          fmt.normalizedValue negative fmt.minNormalMantissa (e + 1)| =
            fmt.betaR ^ (e - (fmt.t : ℤ)) := by
      rw [abs_sub_comm]
      exact fmt.normalizedValue_boundary_spacing negative e
    constructor
    · simpa [hspace] using hb.1
    · simpa [hspace] using hb.2
  · rcases hxy with ⟨rfl, rfl⟩
    have hb := fmt.normalizedValue_boundary_min_spacing_bounds negative e
    constructor
    · simpa [fmt.normalizedValue_boundary_spacing negative e] using hb.1
    · simpa [fmt.normalizedValue_boundary_spacing negative e] using hb.2
theorem adjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| := by
  rcases h with hsame | hboundary
  · exact sameExponentAdjacentNormalized_spacing_bounds_left hsame
  · exact boundaryAdjacentNormalized_spacing_bounds_left hboundary
theorem realOrderAdjacentNormalized_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
      |x - y| ≤ fmt.machineEpsilon * |x| :=
  fmt.adjacentNormalized_spacing_bounds_left
    (fmt.adjacentNormalized_of_realOrderAdjacentNormalized h)
theorem realOrderAdjacentNormalized_relativeSpacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.realOrderAdjacentNormalized x y) :
    fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon ≤ |x - y| / |x| ∧
      |x - y| / |x| ≤ fmt.machineEpsilon := by
  have hb := fmt.realOrderAdjacentNormalized_spacing_bounds_left h
  have hxpos : 0 < |x| :=
    abs_pos.mpr (fmt.unboundedNormalizedSystem_ne_zero h.1)
  constructor
  · have hdiv := div_le_div_of_nonneg_right hb.1 hxpos.le
    have hcancel :
        fmt.betaR⁻¹ * fmt.machineEpsilon * |x| / |x| =
          fmt.betaR⁻¹ * fmt.machineEpsilon := by
      field_simp [ne_of_gt hxpos]
    simpa [hcancel] using hdiv
  · have hdiv := div_le_div_of_nonneg_right hb.2 hxpos.le
    have hcancel :
        (fmt.machineEpsilon * |x|) / |x| = fmt.machineEpsilon := by
      field_simp [ne_of_gt hxpos]
    simpa [hcancel] using hdiv
theorem ieeeSingleFormat_realOrderAdjacentNormalized_relativeSpacing_bounds_left
    {x y : ℝ}
    (h : ieeeSingleFormat.realOrderAdjacentNormalized x y) :
    (2 : ℝ) ^ (-24 : ℤ) ≤ |x - y| / |x| ∧
      |x - y| / |x| ≤ (2 : ℝ) ^ (-23 : ℤ) := by
  have hb := ieeeSingleFormat.realOrderAdjacentNormalized_relativeSpacing_bounds_left h
  have hleft :
      ieeeSingleFormat.betaR⁻¹ *
          ieeeSingleFormat.machineEpsilon =
        (2 : ℝ) ^ (-24 : ℤ) := by
    rw [ieeeSingleFormat_machineEpsilon]
    norm_num [ieeeSingleFormat, betaR, zpow_neg]
  constructor
  · simpa [hleft, zpow_neg] using hb.1
  · simpa [ieeeSingleFormat_machineEpsilon] using hb.2
theorem adjacentNormalized_realOrder_spacing_bounds_left
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.adjacentNormalized x y) :
    fmt.realOrderAdjacentNormalized x y ∧
      fmt.betaR ^ (-1 : ℤ) * fmt.machineEpsilon * |x| ≤ |x - y| ∧
        |x - y| ≤ fmt.machineEpsilon * |x| :=
  ⟨fmt.realOrderAdjacentNormalized_of_adjacentNormalized h,
    fmt.adjacentNormalized_spacing_bounds_left h⟩
theorem unitRoundoff_eq_half_machineEpsilon (fmt : FloatingPointFormat) :
    fmt.unitRoundoff = (1 / 2 : ℝ) * fmt.machineEpsilon :=
  rfl
theorem nearestRoundingIn_mem {S : ℝ → Prop} {x y : ℝ}
    (h : nearestRoundingIn S x y) :
    S y :=
  h.1
theorem nearestRoundingIn_minimal {S : ℝ → Prop} {x y z : ℝ}
    (h : nearestRoundingIn S x y) (hz : S z) :
    |x - y| ≤ |x - z| :=
  h.2 z hz
/-- Nearest rounding is symmetric under negation when the target set is closed
under negation. -/
theorem nearestRoundingIn_neg {S : ℝ → Prop} {x y : ℝ}
    (hSneg : ∀ {z : ℝ}, S z → S (-z))
    (h : nearestRoundingIn S x y) :
    nearestRoundingIn S (-x) (-y) := by
  refine ⟨hSneg (nearestRoundingIn_mem h), ?_⟩
  intro z hz
  have hmin := nearestRoundingIn_minimal h (hSneg hz)
  rw [show (-x) - (-y) = -(x - y) by ring,
    show (-x) - z = -(x - (-z)) by ring, abs_neg, abs_neg]
  exact hmin
/-- Finite nearest rounding is symmetric under negation. -/
theorem nearestRoundingToFinite_neg
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    fmt.nearestRoundingToFinite (-x) (-y) :=
  nearestRoundingIn_neg (fun hz => fmt.finiteSystem_neg hz) h
/-- Floor-based mantissa bracketing.  If a nonnegative real mantissa coordinate
lies in a natural interval, it is either exactly an integer mantissa or lies
strictly between two consecutive mantissas still inside the interval. -/
theorem nat_floor_exact_or_successor_bracket
    {lo hi : ℕ} {q : ℝ}
    (hloq : (lo : ℝ) ≤ q) (hqhi : q ≤ (hi : ℝ)) :
    ∃ m : ℕ,
      lo ≤ m ∧ m ≤ hi ∧
        (q = (m : ℝ) ∨
          (m + 1 ≤ hi ∧ (m : ℝ) < q ∧ q < (m + 1 : ℝ))) := by
  let m := Nat.floor q
  have hq_nonneg : 0 ≤ q := le_trans (Nat.cast_nonneg lo) hloq
  have hlo_m : lo ≤ m := Nat.le_floor hloq
  have hm_hi : m ≤ hi := Nat.floor_le_of_le hqhi
  refine ⟨m, hlo_m, hm_hi, ?_⟩
  by_cases hq_eq : q = (m : ℝ)
  · exact Or.inl hq_eq
  · have hm_le_q : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
    have hm_lt_q : (m : ℝ) < q :=
      lt_of_le_of_ne hm_le_q (by
        intro hmq
        exact hq_eq hmq.symm)
    have hq_lt_msucc : q < (m + 1 : ℝ) := by
      simpa using Nat.lt_floor_add_one q
    have hm_lt_hi : m < hi :=
      Nat.cast_lt.mp (lt_of_lt_of_le hm_lt_q hqhi)
    exact Or.inr ⟨Nat.succ_le_iff.mpr hm_lt_hi, hm_lt_q, hq_lt_msucc⟩
/-- Half-cell natural index selection.  If a real coordinate lies strictly
between the zero/first-cell boundary and the last-subnormal/normal boundary,
then some natural index `m` with `0 < m < M` is within half a unit of it. -/
theorem exists_nat_half_cell_of_half_lt_of_lt_sub_half
    {M : ℕ} {q : ℝ}
    (hlo : (1 / 2 : ℝ) < q)
    (hhi : q < (M : ℝ) - (1 / 2 : ℝ)) :
    ∃ m : ℕ,
      0 < m ∧ m < M ∧
        (m : ℝ) - (1 / 2 : ℝ) ≤ q ∧
          q ≤ (m : ℝ) + (1 / 2 : ℝ) := by
  let r : ℝ := q + (1 / 2 : ℝ)
  let m : ℕ := Nat.floor r
  have hr_ge_one : (1 : ℝ) ≤ r := by
    dsimp [r]
    linarith
  have hr_nonneg : 0 ≤ r := by linarith
  have hm_ge_one : 1 ≤ m :=
    Nat.le_floor (show ((1 : ℕ) : ℝ) ≤ r by simpa using hr_ge_one)
  have hm_pos : 0 < m := hm_ge_one
  have hfloor_le : (m : ℝ) ≤ r := Nat.floor_le hr_nonneg
  have hr_lt_M : r < (M : ℝ) := by
    dsimp [r]
    linarith
  have hm_lt_M : m < M :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hr_lt_M)
  have hr_lt_msucc : r < (m + 1 : ℝ) := by
    simpa [m, r] using Nat.lt_floor_add_one r
  refine ⟨m, hm_pos, hm_lt_M, ?_, ?_⟩
  · dsimp [r] at hfloor_le
    linarith
  · dsimp [r] at hr_lt_msucc
    linarith
/-- Same-exponent positive bracketing from a scaled mantissa interval.  For a
positive real input between the smallest and largest normalized values at a
fixed exponent, `Nat.floor (x / beta^(e-t))` either gives an exact normalized
representation or two adjacent normalized endpoints bracketing `x`. -/
theorem exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hmin : fmt.normalizedValue false fmt.minNormalMantissa e ≤ x)
    (hmax : x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e) :
    (∃ m : ℕ,
      fmt.normalizedMantissa m ∧ x = fmt.normalizedValue false m e) ∨
      ∃ a b : ℝ,
        fmt.realOrderAdjacentNormalized a b ∧
          0 ≤ a ∧ a ≤ x ∧ x ≤ b := by
  let s : ℝ := fmt.betaR ^ (e - (fmt.t : ℤ))
  have hs_pos : 0 < s := by
    dsimp [s]
    exact fmt.betaR_zpow_pos (e - (fmt.t : ℤ))
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have hmin_scaled : (fmt.minNormalMantissa : ℝ) * s ≤ x := by
    simpa [normalizedValue, signValue, s] using hmin
  have hmax_scaled : x ≤ (fmt.maxNormalMantissa : ℝ) * s := by
    simpa [normalizedValue, signValue, s] using hmax
  have hq_min : (fmt.minNormalMantissa : ℝ) ≤ x / s :=
    (le_div_iff₀ hs_pos).2 hmin_scaled
  have hq_max : x / s ≤ (fmt.maxNormalMantissa : ℝ) :=
    (div_le_iff₀ hs_pos).2 hmax_scaled
  rcases nat_floor_exact_or_successor_bracket hq_min hq_max with
    ⟨m, hm_min, hm_max, hcase⟩
  have hm_range : fmt.mantissaInRange m :=
    lt_of_le_of_lt hm_max fmt.maxNormalMantissa_lt_mantissaBound
  have hm_norm : fmt.normalizedMantissa m := ⟨hm_min, hm_range⟩
  rcases hcase with hq_eq | hbetween
  · have hx_eq_scaled : x = (m : ℝ) * s :=
      (div_eq_iff hs_ne).mp hq_eq
    exact Or.inl
      ⟨m, hm_norm, by
        simpa [normalizedValue, signValue, s] using hx_eq_scaled⟩
  · rcases hbetween with ⟨hm_succ_max, hm_lt_q, hq_lt_succ⟩
    have hm_succ_min : fmt.minNormalMantissa ≤ m + 1 :=
      le_trans hm_min (Nat.le_succ m)
    have hm_succ_range : fmt.mantissaInRange (m + 1) :=
      lt_of_le_of_lt hm_succ_max fmt.maxNormalMantissa_lt_mantissaBound
    have hm_succ_norm : fmt.normalizedMantissa (m + 1) :=
      ⟨hm_succ_min, hm_succ_range⟩
    let a := fmt.normalizedValue false m e
    let b := fmt.normalizedValue false (m + 1) e
    have hstruct : fmt.sameExponentAdjacentNormalized a b := by
      refine ⟨false, m, e, hm_norm, hm_succ_norm, Or.inl ?_⟩
      exact ⟨rfl, rfl⟩
    have hadj : fmt.realOrderAdjacentNormalized a b :=
      fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
    have ha_nonneg : 0 ≤ a :=
      le_of_lt (fmt.normalizedValue_false_pos hm_norm)
    have ha_le_x : a ≤ x := by
      have hlt : (m : ℝ) * s < x := by
        have hmul := mul_lt_mul_of_pos_right hm_lt_q hs_pos
        simpa [s, div_mul_cancel₀ x hs_ne] using hmul
      exact le_of_lt (by
        simpa [a, normalizedValue, signValue, s] using hlt)
    have hx_le_b : x ≤ b := by
      have hlt : x < ((m + 1 : ℕ) : ℝ) * s := by
        have hmul := mul_lt_mul_of_pos_right hq_lt_succ hs_pos
        simpa [s, div_mul_cancel₀ x hs_ne] using hmul
      exact le_of_lt (by
        simpa [b, normalizedValue, signValue, s] using hlt)
    exact Or.inr ⟨a, b, hadj, ha_nonneg, ha_le_x, hx_le_b⟩
/-- Same-exponent negative bracketing, obtained from the positive floor
construction by sign symmetry.  If a negative input lies in one exponent bin,
it is either exactly represented by a negative normalized mantissa or bracketed
by adjacent negative normalized endpoints. -/
theorem exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent_negative
    {fmt : FloatingPointFormat} {x : ℝ} {e : ℤ}
    (hlo : fmt.normalizedValue true fmt.maxNormalMantissa e ≤ x)
    (hhi : x ≤ fmt.normalizedValue true fmt.minNormalMantissa e) :
    (∃ m : ℕ,
      fmt.normalizedMantissa m ∧ x = fmt.normalizedValue true m e) ∨
      ∃ a b : ℝ,
        fmt.realOrderAdjacentNormalized a b ∧
          b ≤ 0 ∧ a ≤ x ∧ x ≤ b := by
  have hpos_min : fmt.normalizedValue false fmt.minNormalMantissa e ≤ -x := by
    have h := neg_le_neg hhi
    simpa [fmt.normalizedValue_true_eq_neg_false] using h
  have hpos_max : -x ≤ fmt.normalizedValue false fmt.maxNormalMantissa e := by
    have h := neg_le_neg hlo
    simpa [fmt.normalizedValue_true_eq_neg_false] using h
  rcases fmt.exists_unboundedNormalized_or_realOrderAdjacent_bracket_sameExponent
      hpos_min hpos_max with hrepr | hbracket
  · rcases hrepr with ⟨m, hm, hxneg_eq⟩
    have hx_eq : x = fmt.normalizedValue true m e := by
      calc
        x = -(-x) := by simp
        _ = -fmt.normalizedValue false m e := by rw [hxneg_eq]
        _ = fmt.normalizedValue true m e := by
          rw [fmt.normalizedValue_true_eq_neg_false]
    exact Or.inl ⟨m, hm, hx_eq⟩
  · rcases hbracket with ⟨a, b, hadj, ha_nonneg, ha_le_negx, hnegx_le_b⟩
    have hneg_adj_ab : fmt.realOrderAdjacentNormalized (-a) (-b) :=
      fmt.realOrderAdjacentNormalized_of_adjacentNormalized
        (fmt.adjacentNormalized_neg
          (fmt.adjacentNormalized_of_realOrderAdjacentNormalized hadj))
    have hneg_adj : fmt.realOrderAdjacentNormalized (-b) (-a) :=
      fmt.realOrderAdjacentNormalized_symm hneg_adj_ab
    have hleft : -b ≤ x := by
      have h := neg_le_neg hnegx_le_b
      simpa using h
    have hright : x ≤ -a := by
      have h := neg_le_neg ha_le_negx
      simpa using h
    have hright_nonpos : -a ≤ 0 := by
      simpa using (neg_nonpos.mpr ha_nonneg)
    exact Or.inr ⟨-b, -a, hneg_adj, hright_nonpos, hleft, hright⟩
theorem nearestRoundingIn_self {S : ℝ → Prop} {x : ℝ}
    (hx : S x) :
    nearestRoundingIn S x x := by
  refine ⟨hx, ?_⟩
  intro z _hz
  simp
/-- If the source value is already in the target set, every nearest-rounded
output is equal to the source value. -/
theorem nearestRoundingIn_eq_self_of_mem {S : ℝ → Prop} {x y : ℝ}
    (hx : S x) (h : nearestRoundingIn S x y) :
    y = x := by
  have hdist : |x - y| ≤ 0 := by
    simpa using nearestRoundingIn_minimal h hx
  have hdist_nonneg : 0 ≤ |x - y| := abs_nonneg _
  have habs : |x - y| = 0 := le_antisymm hdist hdist_nonneg
  have hsub : x - y = 0 := abs_eq_zero.mp habs
  linarith
theorem nearestRoundingToUnbounded_self
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.unboundedNormalizedSystem x) :
    fmt.nearestRoundingToUnbounded x x :=
  nearestRoundingIn_self hx
theorem nearestRoundingToUnbounded_eq_self_of_mem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.unboundedNormalizedSystem x)
    (h : fmt.nearestRoundingToUnbounded x y) :
    y = x :=
  nearestRoundingIn_eq_self_of_mem hx h
theorem nearestRoundingToFinite_self
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    fmt.nearestRoundingToFinite x x :=
  nearestRoundingIn_self hx
theorem nearestRoundingToFinite_eq_self_of_finiteSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hx : fmt.finiteSystem x)
    (h : fmt.nearestRoundingToFinite x y) :
    y = x :=
  nearestRoundingIn_eq_self_of_mem hx h
/-- Zero is part of the finite floating-point system. -/
theorem finiteSystem_zero (fmt : FloatingPointFormat) :
    fmt.finiteSystem 0 :=
  Or.inl rfl
/-- Finite-format nearest rounding sends zero to itself under the relation. -/
theorem nearestRoundingToFinite_zero (fmt : FloatingPointFormat) :
    fmt.nearestRoundingToFinite 0 0 :=
  fmt.nearestRoundingToFinite_self fmt.finiteSystem_zero
/-- Positive normal-range bridge from the unbounded nearest-rounding relation
to the finite nearest-rounding relation.  If `x` is at or above the smallest
normal magnitude and an unbounded nearest-rounded value `y` is finite, then
zero and subnormal finite candidates are no closer than the smallest normal,
while normalized finite candidates are already candidates in `G`. -/
theorem nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hyfin : fmt.finiteSystem y)
    (hxlo : fmt.minNormalMagnitude ≤ x) :
    fmt.nearestRoundingToFinite x y := by
  refine ⟨hyfin, ?_⟩
  intro z hz
  rcases hz with hz0 | hznorm | hzsub
  · subst z
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.minNormalMagnitude_mem_unboundedNormalizedSystem
    have hmin_nonneg : 0 ≤ fmt.minNormalMagnitude :=
      le_of_lt fmt.minNormalMagnitude_pos
    have hx_min_nonneg : 0 ≤ x - fmt.minNormalMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_zero_nonneg : 0 ≤ x - 0 := by
      linarith
    have hdist : |x - fmt.minNormalMagnitude| ≤ |x - 0| := by
      rw [abs_of_nonneg hx_min_nonneg, abs_of_nonneg hx_zero_nonneg]
      linarith
    exact le_trans hmin hdist
  · exact
      nearestRoundingIn_minimal hround
        (fmt.normalizedSystem_unboundedNormalizedSystem hznorm)
  · have hmin :=
      nearestRoundingIn_minimal hround
        fmt.minNormalMagnitude_mem_unboundedNormalizedSystem
    have hz_le_min : z ≤ fmt.minNormalMagnitude :=
      fmt.subnormalSystem_le_minNormalMagnitude hzsub
    have hx_min_nonneg : 0 ≤ x - fmt.minNormalMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_z_nonneg : 0 ≤ x - z :=
      sub_nonneg.mpr (le_trans hz_le_min hxlo)
    have hdist : |x - fmt.minNormalMagnitude| ≤ |x - z| := by
      rw [abs_of_nonneg hx_min_nonneg, abs_of_nonneg hx_z_nonneg]
      linarith
    exact le_trans hmin hdist
/-- Negative normal-range bridge from the unbounded nearest-rounding relation
to the finite nearest-rounding relation.  This is the sign mirror of
`nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_minNormalMagnitude_le`. -/
theorem nearestRoundingToFinite_of_nearestRoundingToUnbounded_of_finite_of_le_neg_minNormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hyfin : fmt.finiteSystem y)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    fmt.nearestRoundingToFinite x y := by
  refine ⟨hyfin, ?_⟩
  intro z hz
  rcases hz with hz0 | hznorm | hzsub
  · subst z
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    have hmin_nonneg : 0 ≤ fmt.minNormalMagnitude :=
      le_of_lt fmt.minNormalMagnitude_pos
    have hx_min_nonpos : x - -fmt.minNormalMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_zero_nonpos : x - 0 ≤ 0 := by
      linarith
    have hdist : |x - -fmt.minNormalMagnitude| ≤ |x - 0| := by
      rw [abs_of_nonpos hx_min_nonpos, abs_of_nonpos hx_zero_nonpos]
      linarith
    exact le_trans hmin hdist
  · exact
      nearestRoundingIn_minimal hround
        (fmt.normalizedSystem_unboundedNormalizedSystem hznorm)
  · have hmin :=
      nearestRoundingIn_minimal hround
        fmt.neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    have hneg_min_le_z : -fmt.minNormalMagnitude ≤ z :=
      fmt.neg_minNormalMagnitude_le_subnormalSystem hzsub
    have hx_min_nonpos : x - -fmt.minNormalMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_z_nonpos : x - z ≤ 0 :=
      sub_nonpos.mpr (le_trans hxhi hneg_min_le_z)
    have hdist : |x - -fmt.minNormalMagnitude| ≤ |x - z| := by
      rw [abs_of_nonpos hx_min_nonpos, abs_of_nonpos hx_z_nonpos]
      linarith
    exact le_trans hmin hdist
/-- A nearest-rounded value in the unbounded system is finite whenever the
positive input lies in the finite normal interval. -/
theorem nearestRoundingToUnbounded_output_finite_of_minNormalMagnitude_le_of_le_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hxlo : fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.maxFiniteMagnitude) :
    fmt.finiteSystem y := by
  have hmin_le_y : fmt.minNormalMagnitude ≤ y := by
    by_contra hnot
    have hy_lt : y < fmt.minNormalMagnitude := lt_of_not_ge hnot
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.minNormalMagnitude_mem_unboundedNormalizedSystem
    have hx_min_nonneg : 0 ≤ x - fmt.minNormalMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_y_nonneg : 0 ≤ x - y :=
      sub_nonneg.mpr (le_trans (le_of_lt hy_lt) hxlo)
    have hdist : |x - fmt.minNormalMagnitude| < |x - y| := by
      rw [abs_of_nonneg hx_min_nonneg, abs_of_nonneg hx_y_nonneg]
      linarith
    exact not_lt_of_ge hmin hdist
  have hy_le_max : y ≤ fmt.maxFiniteMagnitude := by
    by_contra hnot
    have hmax_lt : fmt.maxFiniteMagnitude < y := lt_of_not_ge hnot
    have hmax :=
      nearestRoundingIn_minimal hround
        fmt.maxFiniteMagnitude_mem_unboundedNormalizedSystem
    have hx_max_nonpos : x - fmt.maxFiniteMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_y_nonpos : x - y ≤ 0 :=
      sub_nonpos.mpr (le_trans hxhi (le_of_lt hmax_lt))
    have hdist : |x - fmt.maxFiniteMagnitude| < |x - y| := by
      rw [abs_of_nonpos hx_max_nonpos, abs_of_nonpos hx_y_nonpos]
      linarith
    exact not_lt_of_ge hmax hdist
  have hy_nonneg : 0 ≤ y :=
    le_trans (le_of_lt fmt.minNormalMagnitude_pos) hmin_le_y
  have hyrange : fmt.finiteNormalRange y := by
    constructor
    · simpa [abs_of_nonneg hy_nonneg] using hmin_le_y
    · simpa [abs_of_nonneg hy_nonneg] using hy_le_max
  exact Or.inr (Or.inl
    (fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      (nearestRoundingIn_mem hround) hyrange))
/-- A nearest-rounded value in the unbounded system is finite whenever the
negative input lies in the finite normal interval. -/
theorem nearestRoundingToUnbounded_output_finite_of_neg_maxFiniteMagnitude_le_of_le_neg_minNormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (hround : fmt.nearestRoundingToUnbounded x y)
    (hxlo : -fmt.maxFiniteMagnitude ≤ x)
    (hxhi : x ≤ -fmt.minNormalMagnitude) :
    fmt.finiteSystem y := by
  have hnegmax_le_y : -fmt.maxFiniteMagnitude ≤ y := by
    by_contra hnot
    have hy_lt : y < -fmt.maxFiniteMagnitude := lt_of_not_ge hnot
    have hmax :=
      nearestRoundingIn_minimal hround
        fmt.neg_maxFiniteMagnitude_mem_unboundedNormalizedSystem
    have hx_max_nonneg : 0 ≤ x - -fmt.maxFiniteMagnitude :=
      sub_nonneg.mpr hxlo
    have hx_y_nonneg : 0 ≤ x - y :=
      sub_nonneg.mpr (le_trans (le_of_lt hy_lt) hxlo)
    have hdist : |x - -fmt.maxFiniteMagnitude| < |x - y| := by
      rw [abs_of_nonneg hx_max_nonneg, abs_of_nonneg hx_y_nonneg]
      linarith
    exact not_lt_of_ge hmax hdist
  have hy_le_negmin : y ≤ -fmt.minNormalMagnitude := by
    by_contra hnot
    have hmin_lt : -fmt.minNormalMagnitude < y := lt_of_not_ge hnot
    have hmin :=
      nearestRoundingIn_minimal hround
        fmt.neg_minNormalMagnitude_mem_unboundedNormalizedSystem
    have hx_min_nonpos : x - -fmt.minNormalMagnitude ≤ 0 :=
      sub_nonpos.mpr hxhi
    have hx_y_nonpos : x - y ≤ 0 :=
      sub_nonpos.mpr (le_trans hxhi (le_of_lt hmin_lt))
    have hdist : |x - -fmt.minNormalMagnitude| < |x - y| := by
      rw [abs_of_nonpos hx_min_nonpos, abs_of_nonpos hx_y_nonpos]
      linarith
    exact not_lt_of_ge hmin hdist
  have hy_nonpos : y ≤ 0 := by
    have hmin_pos := fmt.minNormalMagnitude_pos
    linarith
  have hyrange : fmt.finiteNormalRange y := by
    constructor
    · rw [abs_of_nonpos hy_nonpos]
      linarith
    · rw [abs_of_nonpos hy_nonpos]
      linarith
  exact Or.inr (Or.inl
    (fmt.unboundedNormalizedSystem_normalizedSystem_of_finiteNormalRange
      (nearestRoundingIn_mem hround) hyrange))
/-- Outputs of the finite nearest-rounding relation are finite values, hence
zero, finite-normal by magnitude, or in the source-facing underflow range. -/
theorem nearestRoundingToFinite_output_zero_or_finiteNormalRange_or_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    y = 0 ∨ fmt.finiteNormalRange y ∨ fmt.finiteUnderflowRange y :=
  fmt.finiteSystem_zero_or_finiteNormalRange_or_finiteUnderflowRange
    (nearestRoundingIn_mem h)
/-- A finite nearest-rounded output that lies in the source-facing underflow
range is either zero or subnormal. -/
theorem nearestRoundingToFinite_output_underflow_zero_or_subnormalSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange y) :
    y = 0 ∨ fmt.subnormalSystem y :=
  (fmt.finiteSystem_finiteUnderflowRange_iff_zero_or_subnormalSystem).mp
    ⟨nearestRoundingIn_mem h, hunder⟩
/-- A nonzero finite nearest-rounded output in the source-facing underflow
range is subnormal. -/
theorem nearestRoundingToFinite_output_underflow_ne_zero_subnormalSystem
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hunder : fmt.finiteUnderflowRange y)
    (hy_ne : y ≠ 0) :
    fmt.subnormalSystem y :=
  (fmt.finiteSystem_finiteUnderflowRange_ne_zero_iff_subnormalSystem).mp
    ⟨nearestRoundingIn_mem h, hunder, hy_ne⟩
/-- Outputs of the finite nearest-rounding relation cannot be in the
source-facing overflow range. -/
theorem nearestRoundingToFinite_output_not_finiteOverflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    ¬ fmt.finiteOverflowRange y :=
  fmt.finiteSystem_not_finiteOverflowRange (nearestRoundingIn_mem h)
/-- Outputs of the finite nearest-rounding relation have magnitude bounded by
the largest finite normalized magnitude. -/
theorem nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y) :
    |y| ≤ fmt.maxFiniteMagnitude :=
  fmt.finiteSystem_abs_le_maxFiniteMagnitude (nearestRoundingIn_mem h)
/-- Positive overflow-range inputs round, under the finite nearest-rounding
relation, to the positive largest finite endpoint.  This is the constructive
existence direction for relation-level saturation. -/
theorem nearestRoundingToFinite_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.maxFiniteMagnitude < x) :
    fmt.nearestRoundingToFinite x fmt.maxFiniteMagnitude := by
  refine ⟨fmt.maxFiniteMagnitude_mem_finiteSystem, ?_⟩
  intro z hz
  have hz_abs_le := fmt.finiteSystem_abs_le_maxFiniteMagnitude hz
  have hz_le : z ≤ fmt.maxFiniteMagnitude :=
    le_trans (le_abs_self z) hz_abs_le
  have hx_z : z ≤ x := le_trans hz_le (le_of_lt hx)
  have hxz_nonneg : 0 ≤ x - z := sub_nonneg.mpr hx_z
  have hxM_nonneg : 0 ≤ x - fmt.maxFiniteMagnitude :=
    sub_nonneg.mpr (le_of_lt hx)
  rw [abs_of_nonneg hxM_nonneg, abs_of_nonneg hxz_nonneg]
  linarith
/-- Negative overflow-range inputs round, under the finite nearest-rounding
relation, to the negative largest finite endpoint.  This is the constructive
existence direction for relation-level saturation. -/
theorem nearestRoundingToFinite_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < -fmt.maxFiniteMagnitude) :
    fmt.nearestRoundingToFinite x (-fmt.maxFiniteMagnitude) := by
  refine ⟨fmt.neg_maxFiniteMagnitude_mem_finiteSystem, ?_⟩
  intro z hz
  have hz_abs_le := fmt.finiteSystem_abs_le_maxFiniteMagnitude hz
  have hnegM_le_z : -fmt.maxFiniteMagnitude ≤ z :=
    le_trans (neg_le_neg hz_abs_le) (neg_abs_le z)
  have hx_z : x ≤ z := le_trans (le_of_lt hx) hnegM_le_z
  have hxz_nonpos : x - z ≤ 0 := sub_nonpos.mpr hx_z
  have hxM_nonpos : x - -fmt.maxFiniteMagnitude ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx)
  rw [abs_of_nonpos hxM_nonpos, abs_of_nonpos hxz_nonpos]
  linarith
/-- Source-facing finite overflow saturation map.  It picks the signed largest
finite endpoint for inputs whose magnitude exceeds the finite range.  This is
not an IEEE exception model. -/
def finiteOverflowSaturation (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if x < 0 then -fmt.maxFiniteMagnitude else fmt.maxFiniteMagnitude
/-- Positive overflow inputs saturate to the positive largest finite endpoint
under the source-facing saturation map. -/
theorem finiteOverflowSaturation_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.maxFiniteMagnitude < x) :
    fmt.finiteOverflowSaturation x = fmt.maxFiniteMagnitude := by
  have hx_nonneg : ¬ x < 0 := by
    have hM_nonneg := fmt.maxFiniteMagnitude_nonneg
    linarith
  simp [finiteOverflowSaturation, hx_nonneg]
/-- Negative overflow inputs saturate to the negative largest finite endpoint
under the source-facing saturation map. -/
theorem finiteOverflowSaturation_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : x < -fmt.maxFiniteMagnitude) :
    fmt.finiteOverflowSaturation x = -fmt.maxFiniteMagnitude := by
  have hx_neg : x < 0 := by
    have hM_nonneg := fmt.maxFiniteMagnitude_nonneg
    linarith
  simp [finiteOverflowSaturation, hx_neg]
/-- For every source-facing overflow-range input, the saturation map is a
finite nearest-rounded value. -/
theorem finiteOverflowSaturation_nearestRoundingToFinite_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteOverflowSaturation x) := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · have hxneg : x < -fmt.maxFiniteMagnitude := by
      rw [finiteOverflowRange, abs_of_neg hneg] at hx
      linarith
    simpa [finiteOverflowSaturation, hneg] using
      fmt.nearestRoundingToFinite_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
        hxneg
  · have hxpos : fmt.maxFiniteMagnitude < x := by
      rw [finiteOverflowRange, abs_of_nonneg hnonneg] at hx
      exact hx
    have hx_not_neg : ¬ x < 0 := not_lt.mpr hnonneg
    simpa [finiteOverflowSaturation, hx_not_neg] using
      fmt.nearestRoundingToFinite_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
        hxpos
/-- Source-facing overflow saturation never increases magnitude on overflow
inputs.  This is the finite-value counterpart of directed toward-zero overflow:
IEEE directed modes that overflow toward infinity are modeled separately by
`ieeeOverflowValue`. -/
theorem finiteOverflowSaturation_abs_le_abs_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    |fmt.finiteOverflowSaturation x| ≤ |x| := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · have hxneg : x < -fmt.maxFiniteMagnitude := by
      rw [finiteOverflowRange, abs_of_neg hneg] at hx
      linarith
    have hMnonneg := fmt.maxFiniteMagnitude_nonneg
    simp [finiteOverflowSaturation, hneg, abs_of_nonneg hMnonneg,
      abs_of_neg hneg]
    linarith
  · have hxpos : fmt.maxFiniteMagnitude < x := by
      rw [finiteOverflowRange, abs_of_nonneg hnonneg] at hx
      exact hx
    have hx_not_neg : ¬ x < 0 := not_lt.mpr hnonneg
    have hMnonneg := fmt.maxFiniteMagnitude_nonneg
    simp [finiteOverflowSaturation, hx_not_neg, abs_of_nonneg hMnonneg,
      abs_of_nonneg hnonneg]
    exact le_of_lt hxpos
theorem finiteOverflowSaturation_neg_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteOverflowRange x) :
    fmt.finiteOverflowSaturation (-x) =
      -fmt.finiteOverflowSaturation x := by
  unfold finiteOverflowSaturation
  by_cases hxneg : x < 0
  · have hnegx_nonneg : ¬ -x < 0 := by linarith
    simp [hxneg, hnegx_nonneg]
  · have hxnonneg : 0 ≤ x := le_of_not_gt hxneg
    have hxpos : 0 < x := by
      have hMnonneg := fmt.maxFiniteMagnitude_nonneg
      have hx' := hx
      rw [finiteOverflowRange, abs_of_nonneg hxnonneg] at hx'
      linarith
    have hnegx_neg : -x < 0 := by linarith
    simp [hxneg, hnegx_neg]
/-- Positive overflow-range inputs round, under the finite nearest-rounding
relation, to the positive largest finite endpoint.  This is relation-level
saturation behavior, not yet a total `fl` function or IEEE exception model. -/
theorem nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : fmt.maxFiniteMagnitude < x) :
    y = fmt.maxFiniteMagnitude := by
  have hy_abs_le :=
    fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude h
  have hy_le : y ≤ fmt.maxFiniteMagnitude :=
    le_trans (le_abs_self y) hy_abs_le
  have hx_y : y ≤ x := le_trans hy_le (le_of_lt hx)
  have hxy_nonneg : 0 ≤ x - y := sub_nonneg.mpr hx_y
  have hxM_nonneg : 0 ≤ x - fmt.maxFiniteMagnitude :=
    sub_nonneg.mpr (le_of_lt hx)
  have hmin :=
    nearestRoundingIn_minimal h fmt.maxFiniteMagnitude_mem_finiteSystem
  rw [abs_of_nonneg hxy_nonneg, abs_of_nonneg hxM_nonneg] at hmin
  have hM_le_y : fmt.maxFiniteMagnitude ≤ y := by
    linarith
  exact le_antisymm hy_le hM_le_y
/-- Negative overflow-range inputs round, under the finite nearest-rounding
relation, to the negative largest finite endpoint.  This is relation-level
saturation behavior, not yet a total `fl` function or IEEE exception model. -/
theorem nearestRoundingToFinite_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : x < -fmt.maxFiniteMagnitude) :
    y = -fmt.maxFiniteMagnitude := by
  have hy_abs_le :=
    fmt.nearestRoundingToFinite_output_abs_le_maxFiniteMagnitude h
  have hnegM_le_y : -fmt.maxFiniteMagnitude ≤ y := by
    exact le_trans (neg_le_neg hy_abs_le) (neg_abs_le y)
  have hx_y : x ≤ y := le_trans (le_of_lt hx) hnegM_le_y
  have hxy_nonpos : x - y ≤ 0 := sub_nonpos.mpr hx_y
  have hxM_nonpos : x - -fmt.maxFiniteMagnitude ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hx)
  have hmin :=
    nearestRoundingIn_minimal h fmt.neg_maxFiniteMagnitude_mem_finiteSystem
  rw [abs_of_nonpos hxy_nonpos, abs_of_nonpos hxM_nonpos] at hmin
  have hy_le_negM : y ≤ -fmt.maxFiniteMagnitude := by
    linarith
  exact le_antisymm hy_le_negM hnegM_le_y
/-- In the source-facing overflow range, every finite nearest-rounded value is
the saturation-map value.  Ties do not matter outside the finite interval. -/
theorem nearestRoundingToFinite_eq_finiteOverflowSaturation_of_finiteOverflowRange
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : fmt.finiteOverflowRange x) :
    y = fmt.finiteOverflowSaturation x := by
  rcases lt_or_ge x 0 with hneg | hnonneg
  · have hxneg : x < -fmt.maxFiniteMagnitude := by
      rw [finiteOverflowRange, abs_of_neg hneg] at hx
      linarith
    rw [fmt.nearestRoundingToFinite_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
      h hxneg]
    exact Eq.symm
      (fmt.finiteOverflowSaturation_eq_neg_maxFiniteMagnitude_of_lt_neg_maxFiniteMagnitude
        hxneg)
  · have hxpos : fmt.maxFiniteMagnitude < x := by
      rw [finiteOverflowRange, abs_of_nonneg hnonneg] at hx
      exact hx
    rw [fmt.nearestRoundingToFinite_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
      h hxpos]
    exact Eq.symm
      (fmt.finiteOverflowSaturation_eq_maxFiniteMagnitude_of_gt_maxFiniteMagnitude
        hxpos)
/-- If the input is within half the smallest subnormal magnitude of zero, then
zero is a finite nearest-rounded value.  Ties at exactly half spacing remain
relation-valued. -/
theorem nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : |x| ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x 0 := by
  refine ⟨fmt.finiteSystem_zero, ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    simp
  · have hz_lb :=
      fmt.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude hz hz0
    have htri0 : |z| ≤ |z - x| + |x| := by
      have h := abs_add_le (z - x) x
      have hzx : z - x + x = z := by ring
      simpa [hzx] using h
    have htri : |z| ≤ |x - z| + |x| := by
      simpa [abs_sub_comm] using htri0
    have hdist : |x| ≤ |x - z| := by
      nlinarith
    simpa using hdist
/-- If the input is strictly within half the smallest subnormal magnitude of
zero, every finite nearest-rounded value is zero. -/
theorem nearestRoundingToFinite_eq_zero_of_abs_lt_half_minSubnormalMagnitude
    {fmt : FloatingPointFormat} {x y : ℝ}
    (h : fmt.nearestRoundingToFinite x y)
    (hx : |x| < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    y = 0 := by
  by_contra hy0
  have hy_lb :=
    fmt.finiteSystem_ne_zero_abs_ge_minSubnormalMagnitude
      (nearestRoundingIn_mem h) hy0
  have htri0 : |y| ≤ |y - x| + |x| := by
    have htri := abs_add_le (y - x) x
    have hyx : y - x + x = y := by ring
    simpa [hyx] using htri
  have htri : |y| ≤ |x - y| + |x| := by
    simpa [abs_sub_comm] using htri0
  have hdist_gt : |x| < |x - y| := by
    nlinarith
  have hzero_min :=
    nearestRoundingIn_minimal h fmt.finiteSystem_zero
  have hdist_le : |x - y| ≤ |x| := by
    simpa using hzero_min
  exact not_lt_of_ge hdist_le hdist_gt
/-- First positive subnormal cell: if the first subnormal mantissa exists and
`x` lies between one half and three halves of the smallest subnormal spacing,
then the smallest positive subnormal magnitude is a finite nearest-rounded
value.  This is the first local piece of the remaining underflow selector. -/
theorem nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hxlo : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ (3 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x fmt.minSubnormalMagnitude := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hx_nonneg : 0 ≤ x := by nlinarith
  have hdist_le_x : |x - fmt.minSubnormalMagnitude| ≤ x := by
    rw [abs_le]
    constructor <;> nlinarith
  have hdist_le_half :
      |x - fmt.minSubnormalMagnitude| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [abs_le]
    constructor <;> nlinarith
  have htwo_normal :=
    fmt.two_mul_minSubnormalMagnitude_le_minNormalMagnitude_of_subnormalMantissa_one
      hsub
  refine
    ⟨Or.inr (Or.inr
        (fmt.minSubnormalMagnitude_mem_subnormalSystem_of_subnormalMantissa_one
          hsub)), ?_⟩
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    simpa [abs_of_nonneg hx_nonneg] using hdist_le_x
  rcases hz with hzero | hnorm | hsubz
  · exact False.elim (hz0 hzero)
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · have hz_abs_ge_min :
          fmt.minNormalMagnitude ≤
            |fmt.normalizedValue false m e| :=
        (fmt.normalizedSystem_finiteNormalRange
          ⟨false, m, e, hm, he, rfl⟩).1
      have hz_ge_two :
          2 * fmt.minSubnormalMagnitude ≤
            fmt.normalizedValue false m e := by
        have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        rw [abs_of_pos hpos] at hz_abs_ge_min
        exact le_trans htwo_normal hz_abs_ge_min
      have hxz_nonpos : x - fmt.normalizedValue false m e ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hxz_nonpos]
      nlinarith
    · have hz_neg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
      have hxz_nonneg : 0 ≤ x - fmt.normalizedValue true m e := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith
  · rcases hsubz with ⟨negative, m, hm, rfl⟩
    cases negative
    · by_cases hm_one : m = 1
      · subst m
        rw [fmt.subnormalValue_false_one_eq]
        rfl
      · have hm_gt_one : 1 < m :=
          lt_of_le_of_ne (Nat.succ_le_of_lt hm.1) (Ne.symm hm_one)
        have htwo_le_m : (2 : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt hm_gt_one)
        have hz_ge_two :
            2 * fmt.minSubnormalMagnitude ≤ fmt.subnormalValue false m := by
          have hmul :
              2 * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≤
                (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
            mul_le_mul_of_nonneg_right htwo_le_m
              (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
          simpa [subnormalValue, signValue, minSubnormalMagnitude] using hmul
        have hxz_nonpos : x - fmt.subnormalValue false m ≤ 0 := by
          nlinarith
        rw [abs_of_nonpos hxz_nonpos]
        nlinarith
    · have hz_nonpos : fmt.subnormalValue true m ≤ 0 := by
        have hpos :
            0 < (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_pos (Nat.cast_pos.mpr hm.1)
            (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
        have hle :
            -((m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) ≤ 0 := by
          nlinarith
        simpa [subnormalValue, signValue] using hle
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue true m := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith
/-- First negative subnormal cell: by sign symmetry, inputs between negative
three halves and negative one half of the smallest subnormal spacing have the
negative smallest subnormal magnitude as a finite nearest-rounded value. -/
theorem nearestRoundingToFinite_neg_minSubnormalMagnitude_of_neg_three_halves_le_of_le_neg_half
    {fmt : FloatingPointFormat} {x : ℝ}
    (hsub : fmt.subnormalMantissa 1)
    (hxlo : -(3 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ -(1 / 2 : ℝ) * fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x (-fmt.minSubnormalMagnitude) := by
  have hposlo : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ -x := by
    nlinarith
  have hposhi : -x ≤ (3 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    nlinarith
  have hround :=
    fmt.nearestRoundingToFinite_minSubnormalMagnitude_of_half_le_of_le_three_halves
      hsub hposlo hposhi
  simpa using fmt.nearestRoundingToFinite_neg hround
/-- Positive subnormal grid cell: if `x` lies within half a subnormal spacing
of a positive subnormal value, then that subnormal value is a finite
nearest-rounded value.  Ties at the cell endpoints remain relation-valued. -/
theorem nearestRoundingToFinite_subnormalValue_false_of_half_cell
    {fmt : FloatingPointFormat} {m : ℕ} {x : ℝ}
    (hm : fmt.subnormalMantissa m)
    (hxlo : ((m : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) :
    fmt.nearestRoundingToFinite x (fmt.subnormalValue false m) := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hm_ge_one_nat : 1 ≤ m := Nat.succ_le_of_lt hm.1
  have hm_ge_one : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_ge_one_nat
  have htarget :
      fmt.subnormalValue false m =
        (m : ℝ) * fmt.minSubnormalMagnitude := by
    simp [subnormalValue, signValue, minSubnormalMagnitude]
  have hdist_le_half :
      |x - fmt.subnormalValue false m| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [htarget, abs_le]
    constructor <;> nlinarith
  have hhalf_le_x : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x := by
    nlinarith
  have hx_nonneg : 0 ≤ x := by nlinarith
  refine ⟨Or.inr (Or.inr ⟨false, m, hm, rfl⟩), ?_⟩
  intro z hz
  rcases hz with hzero | hnorm | hsubz
  · subst z
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact le_trans hdist_le_half hhalf_le_x
  · rcases hnorm with ⟨negative, n, e, hn, he, rfl⟩
    cases negative
    · have hz_abs_ge_min :
          fmt.minNormalMagnitude ≤ |fmt.normalizedValue false n e| :=
        (fmt.normalizedSystem_finiteNormalRange
          ⟨false, n, e, hn, he, rfl⟩).1
      have hz_ge_min :
          fmt.minNormalMagnitude ≤ fmt.normalizedValue false n e := by
        have hpos := fmt.normalizedValue_false_pos (m := n) (e := e) hn
        simpa [abs_of_pos hpos] using hz_abs_ge_min
      have hm_succ_le_min : m + 1 ≤ fmt.minNormalMantissa :=
        Nat.succ_le_of_lt hm.2
      have hm_succ_le_min_real :
          ((m + 1 : ℕ) : ℝ) ≤ (fmt.minNormalMantissa : ℝ) := by
        exact_mod_cast hm_succ_le_min
      have hm_succ_cast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
        norm_num
      have hnormal_ge_next :
          ((m + 1 : ℕ) : ℝ) *
              fmt.minSubnormalMagnitude ≤ fmt.minNormalMagnitude := by
        have hmul :
            ((m + 1 : ℕ) : ℝ) *
                fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) ≤
              (fmt.minNormalMantissa : ℝ) *
                fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_le_mul_of_nonneg_right hm_succ_le_min_real
            (fmt.betaR_zpow_nonneg (fmt.emin - (fmt.t : ℤ)))
        rw [fmt.minNormalMantissa_scale_eq fmt.emin] at hmul
        simpa [minSubnormalMagnitude, minNormalMagnitude] using hmul
      have hcell_le_next :
          ((m : ℝ) + (1 / 2 : ℝ)) * fmt.minSubnormalMagnitude ≤
            ((m + 1 : ℕ) : ℝ) * fmt.minSubnormalMagnitude := by
        nlinarith
      have hxz_nonpos : x - fmt.normalizedValue false n e ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hxz_nonpos]
      have hgap :
          (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
            -(x - fmt.normalizedValue false n e) := by
        nlinarith
      exact le_trans hdist_le_half hgap
    · have hz_neg := fmt.normalizedValue_true_neg (m := n) (e := e) hn
      have hxz_nonneg : 0 ≤ x - fmt.normalizedValue true n e := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith
  · rcases hsubz with ⟨negative, n, hn, rfl⟩
    cases negative
    · by_cases hnm : n = m
      · subst n
        rfl
      · have hlt_or_gt : n < m ∨ m < n := Nat.lt_or_gt_of_ne hnm
        rcases hlt_or_gt with hnm_lt | hm_lt_n
        · have hn_succ_le_m : n + 1 ≤ m := Nat.succ_le_of_lt hnm_lt
          have hn_succ_le_m_real :
              ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
            exact_mod_cast hn_succ_le_m
          have hn_succ_cast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
            norm_num
          have hgap :
              (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
                x - fmt.subnormalValue false n := by
            have hval_n :
                fmt.subnormalValue false n =
                  (n : ℝ) * fmt.minSubnormalMagnitude := by
              simp [subnormalValue, signValue, minSubnormalMagnitude]
            rw [hval_n]
            nlinarith
          have hxz_nonneg : 0 ≤ x - fmt.subnormalValue false n := by
            nlinarith
          rw [abs_of_nonneg hxz_nonneg]
          exact le_trans hdist_le_half hgap
        · have hm_succ_le_n : m + 1 ≤ n := Nat.succ_le_of_lt hm_lt_n
          have hm_succ_le_n_real :
              ((m + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
            exact_mod_cast hm_succ_le_n
          have hm_succ_cast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
            norm_num
          have hgap :
              (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
                fmt.subnormalValue false n - x := by
            have hval_n :
                fmt.subnormalValue false n =
                  (n : ℝ) * fmt.minSubnormalMagnitude := by
              simp [subnormalValue, signValue, minSubnormalMagnitude]
            rw [hval_n]
            nlinarith
          have hxz_nonpos : x - fmt.subnormalValue false n ≤ 0 := by
            nlinarith
          rw [abs_of_nonpos hxz_nonpos]
          have hgap' :
              (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
                -(x - fmt.subnormalValue false n) := by
            nlinarith
          exact le_trans hdist_le_half hgap'
    · have hz_nonpos : fmt.subnormalValue true n ≤ 0 := by
        have hpos :
            0 < (n : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_pos (Nat.cast_pos.mpr hn.1)
            (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
        have hle :
            -((n : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) ≤ 0 := by
          nlinarith
        simpa [subnormalValue, signValue] using hle
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue true n := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      nlinarith
/-- Positive subnormal half-cell absolute-error bound: if `x` lies within
half a subnormal spacing of a positive subnormal value, the absolute error to
that value is at most half a subnormal spacing. -/
theorem absError_subnormalValue_false_le_half_minSubnormalMagnitude_of_half_cell
    {fmt : FloatingPointFormat} {m : ℕ} {x : ℝ}
    (_hm : fmt.subnormalMantissa m)
    (hxlo : ((m : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) :
    absError (fmt.subnormalValue false m) x ≤
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have htarget :
      fmt.subnormalValue false m =
        (m : ℝ) * fmt.minSubnormalMagnitude := by
    simp [subnormalValue, signValue, minSubnormalMagnitude]
  rw [absError, htarget]
  rw [abs_le]
  constructor <;> nlinarith
/-- Negative subnormal grid cell, obtained from the positive cell by finite
nearest-rounding sign symmetry. -/
theorem nearestRoundingToFinite_subnormalValue_true_of_half_cell
    {fmt : FloatingPointFormat} {m : ℕ} {x : ℝ}
    (hm : fmt.subnormalMantissa m)
    (hxlo : -(((m : ℝ) + (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) ≤ x)
    (hxhi : x ≤ -(((m : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude)) :
    fmt.nearestRoundingToFinite x (fmt.subnormalValue true m) := by
  have hposlo :
      ((m : ℝ) - (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude ≤ -x := by
    nlinarith
  have hposhi :
      -x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude := by
    nlinarith
  have hround :=
    fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
      hm hposlo hposhi
  have hneg := fmt.nearestRoundingToFinite_neg hround
  have hsign := fmt.subnormalValue_not_eq_neg false m
  rw [← hsign] at hneg
  simpa using hneg
/-- The smallest normal magnitude is exactly `minNormalMantissa` subnormal
spacings from zero. -/
theorem minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    (fmt : FloatingPointFormat) :
    fmt.minNormalMagnitude =
      (fmt.minNormalMantissa : ℝ) * fmt.minSubnormalMagnitude := by
  simpa [minNormalMagnitude, minSubnormalMagnitude] using
    (fmt.minNormalMantissa_scale_eq fmt.emin).symm
/-- Positive subnormal/normal boundary cell: inputs in the top half subnormal
spacing below the smallest normal magnitude have the smallest normal magnitude
as a finite nearest-rounded value.  The endpoint tie remains relation-valued. -/
theorem nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.minNormalMagnitude) :
    fmt.nearestRoundingToFinite x fmt.minNormalMagnitude := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hMpos_nat : 0 < fmt.minNormalMantissa := fmt.minNormalMantissa_pos
  have hMge_one_nat : 1 ≤ fmt.minNormalMantissa :=
    Nat.succ_le_of_lt hMpos_nat
  have hMge_one : (1 : ℝ) ≤ (fmt.minNormalMantissa : ℝ) := by
    exact_mod_cast hMge_one_nat
  have htarget :
      fmt.minNormalMagnitude =
        (fmt.minNormalMantissa : ℝ) * fmt.minSubnormalMagnitude :=
    fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
  have hhalf_le_x : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤ x := by
    rw [htarget] at hxhi
    nlinarith
  have hx_nonneg : 0 ≤ x := by nlinarith
  have hdist_le_half :
      |x - fmt.minNormalMagnitude| ≤
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
    rw [htarget, abs_le]
    constructor <;> nlinarith
  refine ⟨fmt.minNormalMagnitude_mem_finiteSystem, ?_⟩
  intro z hz
  rcases hz with hzero | hnorm | hsubz
  · subst z
    rw [sub_zero, abs_of_nonneg hx_nonneg]
    exact le_trans hdist_le_half hhalf_le_x
  · rcases hnorm with ⟨negative, m, e, hm, he, rfl⟩
    cases negative
    · have hz_abs_ge_min :
          fmt.minNormalMagnitude ≤
            |fmt.normalizedValue false m e| :=
        (fmt.normalizedSystem_finiteNormalRange
          ⟨false, m, e, hm, he, rfl⟩).1
      have hz_ge_min :
          fmt.minNormalMagnitude ≤ fmt.normalizedValue false m e := by
        have hpos := fmt.normalizedValue_false_pos (m := m) (e := e) hm
        simpa [abs_of_pos hpos] using hz_abs_ge_min
      have hxz_nonpos : x - fmt.normalizedValue false m e ≤ 0 := by
        nlinarith
      rw [abs_of_nonpos hxz_nonpos]
      have hx_target_nonpos : x - fmt.minNormalMagnitude ≤ 0 :=
        sub_nonpos.mpr hxhi
      rw [abs_of_nonpos hx_target_nonpos]
      nlinarith
    · have hz_neg := fmt.normalizedValue_true_neg (m := m) (e := e) hm
      have hxz_nonneg : 0 ≤ x - fmt.normalizedValue true m e := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      exact le_trans hdist_le_half (le_trans hhalf_le_x (by nlinarith))
  · rcases hsubz with ⟨negative, m, hm, rfl⟩
    cases negative
    · have hm_le_last : m ≤ fmt.minNormalMantissa - 1 :=
        Nat.le_sub_one_of_lt hm.2
      have hm_le_last_real :
          (m : ℝ) ≤ (fmt.minNormalMantissa - 1 : ℕ) := by
        exact_mod_cast hm_le_last
      have hlast_cast :
          ((fmt.minNormalMantissa - 1 : ℕ) : ℝ) =
            (fmt.minNormalMantissa : ℝ) - 1 := by
        rw [Nat.cast_sub hMge_one_nat, Nat.cast_one]
      have hz_le_last :
          fmt.subnormalValue false m ≤
            ((fmt.minNormalMantissa : ℝ) - 1) *
              fmt.minSubnormalMagnitude := by
        have hmul :
            (m : ℝ) * fmt.minSubnormalMagnitude ≤
              ((fmt.minNormalMantissa - 1 : ℕ) : ℝ) *
                fmt.minSubnormalMagnitude :=
          mul_le_mul_of_nonneg_right hm_le_last_real hηnonneg
        simpa [subnormalValue, signValue, minSubnormalMagnitude, hlast_cast]
          using hmul
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue false m := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      have hgap :
          (1 / 2 : ℝ) * fmt.minSubnormalMagnitude ≤
            x - fmt.subnormalValue false m := by
        nlinarith
      exact le_trans hdist_le_half hgap
    · have hz_nonpos : fmt.subnormalValue true m ≤ 0 := by
        have hpos :
            0 < (m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ)) :=
          mul_pos (Nat.cast_pos.mpr hm.1)
            (fmt.betaR_zpow_pos (fmt.emin - (fmt.t : ℤ)))
        have hle :
            -((m : ℝ) * fmt.betaR ^ (fmt.emin - (fmt.t : ℤ))) ≤ 0 := by
          nlinarith
        simpa [subnormalValue, signValue] using hle
      have hxz_nonneg : 0 ≤ x - fmt.subnormalValue true m := by
        nlinarith
      rw [abs_of_nonneg hxz_nonneg]
      exact le_trans hdist_le_half (le_trans hhalf_le_x (by nlinarith))
/-- Positive subnormal/normal boundary-cell absolute-error bound: if `x` is in
the top half subnormal spacing below the smallest normal value, the absolute
error to the smallest normal value is at most half a subnormal spacing. -/
theorem absError_minNormalMagnitude_le_half_minSubnormalMagnitude_of_boundary_half_cell
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude ≤ x)
    (hxhi : x ≤ fmt.minNormalMagnitude) :
    absError fmt.minNormalMagnitude x ≤
      (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have htarget :=
    fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
  rw [absError, htarget]
  rw [abs_le]
  constructor <;> nlinarith
/-- Negative subnormal/normal boundary cell, obtained from the positive
boundary cell by finite nearest-rounding sign symmetry. -/
theorem nearestRoundingToFinite_neg_minNormalMagnitude_of_subnormal_boundary_half_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : -fmt.minNormalMagnitude ≤ x)
    (hxhi : x ≤ -(((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude)) :
    fmt.nearestRoundingToFinite x (-fmt.minNormalMagnitude) := by
  have hposlo :
      ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude ≤ -x := by
    nlinarith
  have hposhi : -x ≤ fmt.minNormalMagnitude := by
    nlinarith
  have hround :=
    fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
      hposlo hposhi
  simpa using fmt.nearestRoundingToFinite_neg hround
/-- Positive middle subnormal underflow existence: away from the zero cell and
the smallest-normal boundary cell, a positive underflow input lies in one of
the proved positive subnormal half-cells. -/
theorem exists_nearestRoundingToFinite_positive_subnormal_middle
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxlo : (1 / 2 : ℝ) * fmt.minSubnormalMagnitude < x)
    (hxhi : x < ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
        fmt.minSubnormalMagnitude) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  let q : ℝ := x / fmt.minSubnormalMagnitude
  have hqlo : (1 / 2 : ℝ) < q := by
    dsimp [q]
    rw [lt_div_iff₀ hηpos]
    simpa [mul_comm] using hxlo
  have hqhi : q < (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) := by
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hxhi
  rcases exists_nat_half_cell_of_half_lt_of_lt_sub_half
      (M := fmt.minNormalMantissa) hqlo hqhi with
    ⟨m, hmpos, hmlt, hcelllo, hcellhi⟩
  have hq_mul : q * fmt.minSubnormalMagnitude = x := by
    dsimp [q]
    exact div_mul_cancel₀ x (ne_of_gt hηpos)
  have hxlo_cell :
      ((m : ℝ) - (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude ≤ x := by
    have hmul :=
      mul_le_mul_of_nonneg_right hcelllo hηnonneg
    rw [hq_mul] at hmul
    exact hmul
  have hxhi_cell :
      x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
          fmt.minSubnormalMagnitude := by
    have hmul :=
      mul_le_mul_of_nonneg_right hcellhi hηnonneg
    rw [hq_mul] at hmul
    exact hmul
  exact
    ⟨fmt.subnormalValue false m,
      fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
        ⟨hmpos, hmlt⟩ hxlo_cell hxhi_cell⟩
/-- Nonnegative finite-underflow inputs have at least one finite nearest-rounded
value.  The proof splits the underflow band into the zero cell, subnormal
half-cells, and the smallest-normal boundary cell. -/
theorem exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  by_cases hzero :
      x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude
  · exact
      ⟨0, fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
        (by simpa [abs_of_nonneg hxnonneg] using hzero)⟩
  · have hx_gt_half :
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude < x :=
      lt_of_not_ge hzero
    by_cases hboundary :
        ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
            fmt.minSubnormalMagnitude ≤ x
    · exact
        ⟨fmt.minNormalMagnitude,
          fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
            hboundary hx_le_min⟩
    · have hx_lt_boundary :
          x < ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude :=
        lt_of_not_ge hboundary
      exact
        fmt.exists_nearestRoundingToFinite_positive_subnormal_middle
          hx_gt_half hx_lt_boundary
/-- Nonnegative finite-underflow inputs have a finite candidate within half a
subnormal spacing.  This is the absolute-error substrate for Higham's gradual
underflow additive term. -/
theorem exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ,
      fmt.finiteSystem y ∧
        absError y x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  by_cases hzero :
      x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude
  · exact
      ⟨0, fmt.finiteSystem_zero,
        by simpa [absError, abs_of_nonneg hxnonneg] using hzero⟩
  · have hx_gt_half :
        (1 / 2 : ℝ) * fmt.minSubnormalMagnitude < x :=
      lt_of_not_ge hzero
    by_cases hboundary :
        ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
            fmt.minSubnormalMagnitude ≤ x
    · exact
        ⟨fmt.minNormalMagnitude, fmt.minNormalMagnitude_mem_finiteSystem,
          fmt.absError_minNormalMagnitude_le_half_minSubnormalMagnitude_of_boundary_half_cell
            hboundary hx_le_min⟩
    · have hx_lt_boundary :
          x < ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude :=
        lt_of_not_ge hboundary
      have hηpos := fmt.minSubnormalMagnitude_pos
      have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
      let q : ℝ := x / fmt.minSubnormalMagnitude
      have hqlo : (1 / 2 : ℝ) < q := by
        dsimp [q]
        rw [lt_div_iff₀ hηpos]
        simpa [mul_comm] using hx_gt_half
      have hqhi : q < (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) := by
        dsimp [q]
        rw [div_lt_iff₀ hηpos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hx_lt_boundary
      rcases exists_nat_half_cell_of_half_lt_of_lt_sub_half
          (M := fmt.minNormalMantissa) hqlo hqhi with
        ⟨m, hmpos, hmlt, hcelllo, hcellhi⟩
      have hq_mul : q * fmt.minSubnormalMagnitude = x := by
        dsimp [q]
        exact div_mul_cancel₀ x (ne_of_gt hηpos)
      have hxlo_cell :
          ((m : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul :=
          mul_le_mul_of_nonneg_right hcelllo hηnonneg
        rw [hq_mul] at hmul
        exact hmul
      have hxhi_cell :
          x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude := by
        have hmul :=
          mul_le_mul_of_nonneg_right hcellhi hηnonneg
        rw [hq_mul] at hmul
        exact hmul
      exact
        ⟨fmt.subnormalValue false m,
          Or.inr (Or.inr ⟨false, m, ⟨hmpos, hmlt⟩, rfl⟩),
          fmt.absError_subnormalValue_false_le_half_minSubnormalMagnitude_of_half_cell
            ⟨hmpos, hmlt⟩ hxlo_cell hxhi_cell⟩
/-- Nonpositive finite-underflow inputs have at least one finite nearest-rounded
value, by sign symmetry from the nonnegative underflow theorem. -/
theorem exists_nearestRoundingToFinite_nonpos_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonpos : x ≤ 0)
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  have hneg_nonneg : 0 ≤ -x := by linarith
  have hunder_neg : fmt.finiteUnderflowRange (-x) := by
    simpa [finiteUnderflowRange, abs_neg] using hunder
  rcases fmt.exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange
      hneg_nonneg hunder_neg with ⟨y, hround⟩
  exact ⟨-y, by simpa using fmt.nearestRoundingToFinite_neg hround⟩
/-- Every source-facing finite-underflow input has at least one finite
nearest-rounded value.  This is relation-level gradual-underflow existence; it
does not choose a unique tie result or model IEEE underflow exceptions. -/
theorem exists_nearestRoundingToFinite_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ, fmt.nearestRoundingToFinite x y := by
  by_cases hxnonneg : 0 ≤ x
  · exact
      fmt.exists_nearestRoundingToFinite_nonneg_finiteUnderflowRange
        hxnonneg hunder
  · have hxnonpos : x ≤ 0 := le_of_lt (lt_of_not_ge hxnonneg)
    exact
      fmt.exists_nearestRoundingToFinite_nonpos_finiteUnderflowRange
        hxnonpos hunder
/-- Every finite-underflow input has a finite candidate within half a subnormal
spacing. -/
theorem exists_finiteSystem_absError_le_half_minSubnormalMagnitude_finiteUnderflowRange
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    ∃ y : ℝ,
      fmt.finiteSystem y ∧
        absError y x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
  by_cases hxnonneg : 0 ≤ x
  · exact
      fmt.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange
        hxnonneg hunder
  · have hxnonpos : x ≤ 0 := le_of_lt (lt_of_not_ge hxnonneg)
    have hneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    rcases
      fmt.exists_finiteSystem_absError_le_half_minSubnormalMagnitude_nonneg_finiteUnderflowRange
        hneg_nonneg hunder_neg with
      ⟨y, hy, hdist⟩
    refine ⟨-y, fmt.finiteSystem_neg hy, ?_⟩
    have heq : absError (-y) x = absError y (-x) := by
      unfold absError
      have harg : -y - x = -(y - -x) := by ring
      rw [harg, abs_neg]
    simpa [heq] using hdist
/-- Source-style round-away selector for nonnegative finite-underflow inputs.
It rounds by the subnormal lattice coordinate `x / eta`, where
`eta = minSubnormalMagnitude`, choosing the larger-magnitude endpoint at exact
halfway ties.  This is still only a finite-value selector, not an IEEE
underflow/exception semantics. -/
def finiteUnderflowRoundAwayNonneg (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor (q + (1 / 2 : ℝ))
  if m = 0 then
    0
  else if fmt.minNormalMantissa ≤ m then
    fmt.minNormalMagnitude
  else
    fmt.subnormalValue false m
theorem finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x
      (fmt.finiteUnderflowRoundAwayNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor (q + (1 / 2 : ℝ))
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hr_nonneg : 0 ≤ q + (1 / 2 : ℝ) := by
    nlinarith
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q + (1 / 2 : ℝ) :=
    Nat.floor_le hr_nonneg
  have hfloor_succ : q + (1 / 2 : ℝ) < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one (q + (1 / 2 : ℝ))
  change
    fmt.nearestRoundingToFinite x
      (if m = 0 then 0
        else if fmt.minNormalMantissa ≤ m then fmt.minNormalMagnitude
        else fmt.subnormalValue false m)
  by_cases hm0 : m = 0
  · simp [hm0]
    have hq_lt_half : q < (1 / 2 : ℝ) := by
      have hs : q + (1 / 2 : ℝ) < (1 : ℝ) := by
        simpa [hm0] using hfloor_succ
      linarith
    have hx_lt_half : x < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
      dsimp [q] at hq_lt_half
      rw [div_lt_iff₀ hηpos] at hq_lt_half
      simpa [mul_comm] using hq_lt_half
    exact
      fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
        (by
          rw [abs_of_nonneg hxnonneg]
          exact le_of_lt hx_lt_half)
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
    by_cases htop : fmt.minNormalMantissa ≤ m
    · simp [hm0, htop]
      have hM_le_r :
          (fmt.minNormalMantissa : ℝ) ≤ q + (1 / 2 : ℝ) := by
        exact le_trans (by exact_mod_cast htop) hfloor_le
      have hqlo :
          (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) ≤ q := by
        linarith
      have hxlo :
          ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      exact
        fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
          hxlo hx_le_min
    · simp [hm0, htop]
      have hmlt : m < fmt.minNormalMantissa := lt_of_not_ge htop
      have hm : fmt.subnormalMantissa m := ⟨hmpos, hmlt⟩
      have hqlo : (m : ℝ) - (1 / 2 : ℝ) ≤ q := by
        linarith
      have hfloor_succ' : q + (1 / 2 : ℝ) < (m : ℝ) + 1 := by
        simpa [Nat.cast_add, Nat.cast_one] using hfloor_succ
      have hqhi : q ≤ (m : ℝ) + (1 / 2 : ℝ) := by
        linarith
      have hxlo :
          ((m : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      have hxhi :
          x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude := by
        have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      exact
        fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
          hm hxlo hxhi
/-- Source-style round-away selector for finite-underflow inputs, obtained from
the nonnegative selector by sign symmetry. -/
def finiteUnderflowRoundAway (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundAwayNonneg x
  else
    -fmt.finiteUnderflowRoundAwayNonneg (-x)
theorem finiteUnderflowRoundAway_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteUnderflowRoundAway x) := by
  unfold finiteUnderflowRoundAway
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    have hround :=
      fmt.finiteUnderflowRoundAwayNonneg_nearestRoundingToFinite
        hxneg_nonneg hunder_neg
    simpa using fmt.nearestRoundingToFinite_neg hround
/-- Source-style round-to-even selector for nonnegative finite-underflow
inputs.  It rounds by the subnormal lattice coordinate `x / eta`, where
`eta = minSubnormalMagnitude`, and breaks exact half-spacing ties by the lower
lattice index parity.  The index `0` denotes zero, positive indices below
`minNormalMantissa` denote subnormals, and `minNormalMantissa` denotes the
smallest normal value. -/
def finiteUnderflowRoundToEvenNonneg (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  let midpoint : ℝ := (m : ℝ) + (1 / 2 : ℝ)
  if q < midpoint then
    if m = 0 then 0 else fmt.subnormalValue false m
  else if midpoint < q then
    if fmt.minNormalMantissa ≤ m + 1 then
      fmt.minNormalMagnitude
    else
      fmt.subnormalValue false (m + 1)
  else if evenMantissa m then
    if m = 0 then 0 else fmt.subnormalValue false m
  else if fmt.minNormalMantissa ≤ m + 1 then
    fmt.minNormalMagnitude
  else
    fmt.subnormalValue false (m + 1)
theorem finiteUnderflowRoundToEvenNonneg_zero
    (fmt : FloatingPointFormat) :
    fmt.finiteUnderflowRoundToEvenNonneg 0 = 0 := by
  unfold finiteUnderflowRoundToEvenNonneg
  simp
theorem finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x)
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x
      (fmt.finiteUnderflowRoundToEvenNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  let midpoint : ℝ := (m : ℝ) + (1 / 2 : ℝ)
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hx_le_min : x ≤ fmt.minNormalMagnitude := le_of_lt hx_lt_min
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hfloor_succ : q < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  have hsucc_le_M : m + 1 ≤ fmt.minNormalMantissa :=
    Nat.succ_le_iff.mpr hm_lt_M
  change
    fmt.nearestRoundingToFinite x
      (if q < midpoint then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if midpoint < q then
        if fmt.minNormalMantissa ≤ m + 1 then
          fmt.minNormalMagnitude
        else
          fmt.subnormalValue false (m + 1)
      else if evenMantissa m then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1))
  by_cases hleft : q < midpoint
  · simp [hleft]
    by_cases hm0 : m = 0
    · simp [hm0]
      have hq_lt_half : q < (1 / 2 : ℝ) := by
        simpa [midpoint, hm0] using hleft
      have hx_lt_half : x < (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
        dsimp [q] at hq_lt_half
        rw [div_lt_iff₀ hηpos] at hq_lt_half
        simpa [mul_comm] using hq_lt_half
      exact
        fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
          (by
            rw [abs_of_nonneg hxnonneg]
            exact le_of_lt hx_lt_half)
    · simp [hm0]
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hm : fmt.subnormalMantissa m := ⟨hmpos, hm_lt_M⟩
      have hqlo : (m : ℝ) - (1 / 2 : ℝ) ≤ q := by
        linarith
      have hqhi : q ≤ (m : ℝ) + (1 / 2 : ℝ) := le_of_lt hleft
      have hxlo :
          ((m : ℝ) - (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude ≤ x := by
        have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      have hxhi :
          x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
              fmt.minSubnormalMagnitude := by
        have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
        dsimp [q] at hmul
        rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
        exact hmul
      exact
        fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
          hm hxlo hxhi
  · simp [hleft]
    by_cases hright : midpoint < q
    · simp [hright]
      by_cases htop : fmt.minNormalMantissa ≤ m + 1
      · simp [htop]
        have hM_le_succ :
            (fmt.minNormalMantissa : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
          exact_mod_cast htop
        have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
          dsimp [midpoint]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hqlo :
            (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) ≤ q := by
          rw [hmid_eq] at hright
          linarith
        have hxlo :
            ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
                fmt.minSubnormalMagnitude ≤ x := by
          have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
          dsimp [q] at hmul
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
          exact hmul
        exact
          fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
            hxlo hx_le_min
      · simp [htop]
        have hsucc_lt_M : m + 1 < fmt.minNormalMantissa :=
          lt_of_not_ge htop
        have hm : fmt.subnormalMantissa (m + 1) :=
          ⟨Nat.succ_pos m, hsucc_lt_M⟩
        have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
          dsimp [midpoint]
          rw [Nat.cast_add, Nat.cast_one]
          ring
        have hqlo : ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) ≤ q := by
          rw [← hmid_eq]
          exact le_of_lt hright
        have hqhi : q ≤ ((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ) := by
          have hsucc' : q < ((m + 1 : ℕ) : ℝ) := by
            simpa using hfloor_succ
          linarith
        have hxlo :
            (((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ)) *
                fmt.minSubnormalMagnitude ≤ x := by
          have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
          dsimp [q] at hmul
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
          exact hmul
        have hxhi :
            x ≤ (((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ)) *
                fmt.minSubnormalMagnitude := by
          have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
          dsimp [q] at hmul
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
          exact hmul
        exact
          fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
            hm hxlo hxhi
    · simp [hright]
      have htie : q = midpoint :=
        le_antisymm (le_of_not_gt hright) (le_of_not_gt hleft)
      by_cases heven : evenMantissa m
      · simp [heven]
        by_cases hm0 : m = 0
        · simp [hm0]
          have hq_le_half : q ≤ (1 / 2 : ℝ) := by
            rw [htie]
            simp [midpoint, hm0]
          have hx_le_half : x ≤ (1 / 2 : ℝ) * fmt.minSubnormalMagnitude := by
            dsimp [q] at hq_le_half
            rw [div_le_iff₀ hηpos] at hq_le_half
            simpa [mul_comm] using hq_le_half
          exact
            fmt.nearestRoundingToFinite_zero_of_abs_le_half_minSubnormalMagnitude
              (by
                rw [abs_of_nonneg hxnonneg]
                exact hx_le_half)
        · simp [hm0]
          have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hm : fmt.subnormalMantissa m := ⟨hmpos, hm_lt_M⟩
          have hqlo : (m : ℝ) - (1 / 2 : ℝ) ≤ q := by
            linarith
          have hqhi : q ≤ (m : ℝ) + (1 / 2 : ℝ) := by
            simpa [midpoint] using le_of_eq htie
          have hxlo :
              ((m : ℝ) - (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude ≤ x := by
            have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          have hxhi :
              x ≤ ((m : ℝ) + (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude := by
            have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          exact
            fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
              hm hxlo hxhi
      · simp [heven]
        by_cases htop : fmt.minNormalMantissa ≤ m + 1
        · simp [htop]
          have hM_le_succ :
              (fmt.minNormalMantissa : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
            exact_mod_cast htop
          have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
            dsimp [midpoint]
            rw [Nat.cast_add, Nat.cast_one]
            ring
          have hqlo :
              (fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ) ≤ q := by
            rw [htie, hmid_eq]
            linarith
          have hxlo :
              ((fmt.minNormalMantissa : ℝ) - (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude ≤ x := by
            have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          exact
            fmt.nearestRoundingToFinite_minNormalMagnitude_of_subnormal_boundary_half_le
              hxlo hx_le_min
        · simp [htop]
          have hsucc_lt_M : m + 1 < fmt.minNormalMantissa :=
            lt_of_not_ge htop
          have hm : fmt.subnormalMantissa (m + 1) :=
            ⟨Nat.succ_pos m, hsucc_lt_M⟩
          have hmid_eq : midpoint = ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) := by
            dsimp [midpoint]
            rw [Nat.cast_add, Nat.cast_one]
            ring
          have hqlo : ((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ) ≤ q := by
            rw [htie, hmid_eq]
          have hqhi : q ≤ ((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ) := by
            have hsucc' : q < ((m + 1 : ℕ) : ℝ) := by
              simpa using hfloor_succ
            linarith
          have hxlo :
              (((m + 1 : ℕ) : ℝ) - (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude ≤ x := by
            have hmul := mul_le_mul_of_nonneg_right hqlo hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          have hxhi :
              x ≤ (((m + 1 : ℕ) : ℝ) + (1 / 2 : ℝ)) *
                  fmt.minSubnormalMagnitude := by
            have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
            dsimp [q] at hmul
            rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
            exact hmul
          exact
            fmt.nearestRoundingToFinite_subnormalValue_false_of_half_cell
              hm hxlo hxhi
/-- Source-style round-to-even selector for finite-underflow inputs, obtained
from the nonnegative selector by sign symmetry. -/
def finiteUnderflowRoundToEven (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundToEvenNonneg x
  else
    -fmt.finiteUnderflowRoundToEvenNonneg (-x)
theorem finiteUnderflowRoundToEven_neg
    (fmt : FloatingPointFormat) (x : ℝ) :
    fmt.finiteUnderflowRoundToEven (-x) =
      -fmt.finiteUnderflowRoundToEven x := by
  rcases lt_trichotomy x 0 with hxneg | hxzero | hxpos
  · have hx_nonneg : ¬ 0 ≤ x := by linarith
    have hnegx_nonneg : 0 ≤ -x := by linarith
    simp [finiteUnderflowRoundToEven, hx_nonneg, hnegx_nonneg]
  · subst x
    simp [finiteUnderflowRoundToEven, finiteUnderflowRoundToEvenNonneg_zero]
  · have hx_nonneg : 0 ≤ x := le_of_lt hxpos
    have hnegx_nonneg : ¬ 0 ≤ -x := by linarith
    simp [finiteUnderflowRoundToEven, hx_nonneg, hnegx_nonneg]
theorem finiteUnderflowRoundToEven_nearestRoundingToFinite
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.nearestRoundingToFinite x (fmt.finiteUnderflowRoundToEven x) := by
  unfold finiteUnderflowRoundToEven
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    have hround :=
      fmt.finiteUnderflowRoundToEvenNonneg_nearestRoundingToFinite
        hxneg_nonneg hunder_neg
    simpa using fmt.nearestRoundingToFinite_neg hround
/-- Source-style directed round-down selector for nonnegative finite-underflow
inputs.  It truncates the subnormal lattice coordinate `x / eta`, where
`eta = minSubnormalMagnitude`; index `0` denotes zero and positive indices below
`minNormalMantissa` denote positive subnormals. -/
def finiteUnderflowRoundTowardZeroNonneg
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  if m = 0 then 0 else fmt.subnormalValue false m
/-- Source-style directed round-up selector for nonnegative finite-underflow
inputs.  It uses the same subnormal lattice coordinate as
`finiteUnderflowRoundTowardZeroNonneg`, choosing the next lattice value unless
the coordinate is already exact.  The top lattice endpoint is the smallest
normal magnitude. -/
def finiteUnderflowRoundTowardPositiveNonneg
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  if q = (m : ℝ) then
    if m = 0 then 0 else fmt.subnormalValue false m
  else if fmt.minNormalMantissa ≤ m + 1 then
    fmt.minNormalMagnitude
  else
    fmt.subnormalValue false (m + 1)
theorem finiteUnderflowRoundTowardZeroNonneg_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardZeroNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  change fmt.finiteSystem (if m = 0 then 0 else fmt.subnormalValue false m)
  by_cases hm0 : m = 0
  · simp [hm0, fmt.finiteSystem_zero]
  · simp [hm0]
    exact Or.inr (Or.inr
      ⟨false, m, ⟨Nat.pos_of_ne_zero hm0, hm_lt_M⟩, rfl⟩)
theorem finiteUnderflowRoundTowardPositiveNonneg_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardPositiveNonneg x) := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  change
    fmt.finiteSystem
      (if q = (m : ℝ) then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1))
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    by_cases hm0 : m = 0
    · simp [hm0, fmt.finiteSystem_zero]
    · simp [hm0]
      exact Or.inr (Or.inr
        ⟨false, m, ⟨Nat.pos_of_ne_zero hm0, hm_lt_M⟩, rfl⟩)
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop]
      exact fmt.minNormalMagnitude_mem_finiteSystem
    · simp [htop]
      have hsucc_lt_M : m + 1 < fmt.minNormalMantissa := lt_of_not_ge htop
      exact Or.inr (Or.inr
        ⟨false, m + 1, ⟨Nat.succ_pos m, hsucc_lt_M⟩, rfl⟩)
theorem finiteUnderflowRoundTowardZeroNonneg_nonneg
    (fmt : FloatingPointFormat) (x : ℝ) :
    0 ≤ fmt.finiteUnderflowRoundTowardZeroNonneg x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  change 0 ≤ if m = 0 then 0 else fmt.subnormalValue false m
  by_cases hm0 : m = 0
  · simp [hm0]
  · simp [hm0, subnormalValue, signValue]
    exact mul_nonneg (Nat.cast_nonneg m) hηnonneg
theorem finiteUnderflowRoundTowardPositiveNonneg_nonneg
    (fmt : FloatingPointFormat) (x : ℝ) :
    0 ≤ fmt.finiteUnderflowRoundTowardPositiveNonneg x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude :=
    le_of_lt fmt.minSubnormalMagnitude_pos
  have hmin_nonneg : 0 ≤ fmt.minNormalMagnitude :=
    le_of_lt fmt.minNormalMagnitude_pos
  change
    0 ≤
      if q = (m : ℝ) then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1)
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    by_cases hm0 : m = 0
    · simp [hm0]
    · simp [hm0, subnormalValue, signValue]
      exact mul_nonneg (Nat.cast_nonneg m) hηnonneg
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop, hmin_nonneg]
    · simp [htop, subnormalValue, signValue]
      have hsucc_nonneg : 0 ≤ (m : ℝ) + 1 := by positivity
      exact mul_nonneg hsucc_nonneg hηnonneg
theorem finiteUnderflowRoundTowardZeroNonneg_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) :
    fmt.finiteUnderflowRoundTowardZeroNonneg x ≤ x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  change (if m = 0 then 0 else fmt.subnormalValue false m) ≤ x
  by_cases hm0 : m = 0
  · simp [hm0, hxnonneg]
  · simp [hm0, subnormalValue, signValue]
    have hmul := mul_le_mul_of_nonneg_right hfloor_le hηnonneg
    dsimp [q] at hmul
    rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
    simpa [mul_assoc] using hmul
theorem le_finiteUnderflowRoundTowardPositiveNonneg
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    x ≤ fmt.finiteUnderflowRoundTowardPositiveNonneg x := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hfloor_succ : q < (m + 1 : ℕ) := by
    simpa [m] using Nat.lt_floor_add_one q
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  change
    x ≤
      if q = (m : ℝ) then
        if m = 0 then 0 else fmt.subnormalValue false m
      else if fmt.minNormalMantissa ≤ m + 1 then
        fmt.minNormalMagnitude
      else
        fmt.subnormalValue false (m + 1)
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    have hx_div : x / fmt.minSubnormalMagnitude = (m : ℝ) := by
      simpa [q] using hqeq
    have hx_eq : x = (m : ℝ) * fmt.minSubnormalMagnitude := by
      calc
        x = x / fmt.minSubnormalMagnitude *
            fmt.minSubnormalMagnitude := by
          rw [div_mul_cancel₀ x (ne_of_gt hηpos)]
        _ = (m : ℝ) * fmt.minSubnormalMagnitude := by
          rw [hx_div]
    by_cases hm0 : m = 0
    · simp [hm0] at hx_eq
      simp [hm0, hx_eq]
    · simp [hm0, subnormalValue, signValue, minSubnormalMagnitude, hx_eq]
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop]
      exact le_of_lt hx_lt_min
    · simp [htop, subnormalValue, signValue]
      have hqhi : q ≤ ((m + 1 : ℕ) : ℝ) := le_of_lt hfloor_succ
      have hmul := mul_le_mul_of_nonneg_right hqhi hηnonneg
      dsimp [q] at hmul
      rw [div_mul_cancel₀ x (ne_of_gt hηpos)] at hmul
      simpa [Nat.cast_add, Nat.cast_one, mul_assoc] using hmul
/-- The nonnegative round-up underflow selector never exceeds the smallest
normal magnitude. -/
theorem finiteUnderflowRoundTowardPositiveNonneg_le_minNormalMagnitude
    {fmt : FloatingPointFormat} {x : ℝ}
    (hxnonneg : 0 ≤ x) (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteUnderflowRoundTowardPositiveNonneg x ≤
      fmt.minNormalMagnitude := by
  let q : ℝ := x / fmt.minSubnormalMagnitude
  let m : ℕ := Nat.floor q
  have hηpos := fmt.minSubnormalMagnitude_pos
  have hηnonneg : 0 ≤ fmt.minSubnormalMagnitude := le_of_lt hηpos
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact div_nonneg hxnonneg hηnonneg
  have hx_lt_min : x < fmt.minNormalMagnitude := by
    simpa [finiteUnderflowRange, abs_of_nonneg hxnonneg] using hunder
  have hq_lt_M : q < (fmt.minNormalMantissa : ℝ) := by
    have htarget :=
      fmt.minNormalMagnitude_eq_minNormalMantissa_mul_minSubnormalMagnitude
    dsimp [q]
    rw [div_lt_iff₀ hηpos]
    simpa [htarget, mul_comm] using hx_lt_min
  have hfloor_le : (m : ℝ) ≤ q := Nat.floor_le hq_nonneg
  have hm_lt_M : m < fmt.minNormalMantissa :=
    Nat.cast_lt.mp (lt_of_le_of_lt hfloor_le hq_lt_M)
  change
    (if q = (m : ℝ) then
      if m = 0 then 0 else fmt.subnormalValue false m
    else if fmt.minNormalMantissa ≤ m + 1 then
      fmt.minNormalMagnitude
    else
      fmt.subnormalValue false (m + 1)) ≤ fmt.minNormalMagnitude
  by_cases hqeq : q = (m : ℝ)
  · simp [hqeq]
    by_cases hm0 : m = 0
    · simp [hm0, le_of_lt fmt.minNormalMagnitude_pos]
    · simp [hm0]
      have hsubmant : fmt.subnormalMantissa m :=
        ⟨Nat.pos_of_ne_zero hm0, hm_lt_M⟩
      have hlt :=
        fmt.subnormalValue_abs_lt_min_normal
          (negative := false) hsubmant
      have hnonneg : 0 ≤ fmt.subnormalValue false m := by
        simp [subnormalValue, signValue]
        exact mul_nonneg (Nat.cast_nonneg m) hηnonneg
      exact le_of_lt (by
        simpa [minNormalMagnitude, abs_of_nonneg hnonneg] using hlt)
  · simp [hqeq]
    by_cases htop : fmt.minNormalMantissa ≤ m + 1
    · simp [htop]
    · simp [htop]
      have hsucc_lt_M : m + 1 < fmt.minNormalMantissa := lt_of_not_ge htop
      have hsubmant : fmt.subnormalMantissa (m + 1) :=
        ⟨Nat.succ_pos m, hsucc_lt_M⟩
      have hlt :=
        fmt.subnormalValue_abs_lt_min_normal
          (negative := false) hsubmant
      have hnonneg : 0 ≤ fmt.subnormalValue false (m + 1) := by
        simp [subnormalValue, signValue]
        exact mul_nonneg (by positivity : 0 ≤ (m : ℝ) + 1) hηnonneg
      exact le_of_lt (by
        simpa [minNormalMagnitude, abs_of_nonneg hnonneg] using hlt)
/-- Negating both sides inside `absError` preserves the absolute distance. -/
theorem absError_neg_left_eq_neg_exact (computed exact : ℝ) :
    absError (-computed) exact = absError computed (-exact) := by
  unfold absError
  rw [show -computed - exact = -(computed - -exact) by ring, abs_neg]
/-- Source-style finite-underflow selector for rounding toward zero, obtained
from the nonnegative round-down selector by sign symmetry. -/
def finiteUnderflowRoundTowardZero
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundTowardZeroNonneg x
  else
    -fmt.finiteUnderflowRoundTowardZeroNonneg (-x)
/-- Source-style finite-underflow selector for rounding toward positive
infinity, using round-up on nonnegative inputs and round-down after sign
symmetry on negative inputs. -/
def finiteUnderflowRoundTowardPositive
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundTowardPositiveNonneg x
  else
    -fmt.finiteUnderflowRoundTowardZeroNonneg (-x)
/-- Source-style finite-underflow selector for rounding toward negative
infinity, using round-down on nonnegative inputs and round-up after sign
symmetry on negative inputs. -/
def finiteUnderflowRoundTowardNegative
    (fmt : FloatingPointFormat) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    fmt.finiteUnderflowRoundTowardZeroNonneg x
  else
    -fmt.finiteUnderflowRoundTowardPositiveNonneg (-x)
theorem finiteUnderflowRoundTowardZero_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardZero x) := by
  unfold finiteUnderflowRoundTowardZero
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    exact fmt.finiteSystem_neg
      (fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxneg_nonneg hunder_neg)
theorem finiteUnderflowRoundTowardPositive_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardPositive x) := by
  unfold finiteUnderflowRoundTowardPositive
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardPositiveNonneg_finiteSystem
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    exact fmt.finiteSystem_neg
      (fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxneg_nonneg hunder_neg)
theorem finiteUnderflowRoundTowardNegative_finiteSystem
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteSystem (fmt.finiteUnderflowRoundTowardNegative x) := by
  unfold finiteUnderflowRoundTowardNegative
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.finiteUnderflowRoundTowardZeroNonneg_finiteSystem
        hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    exact fmt.finiteSystem_neg
      (fmt.finiteUnderflowRoundTowardPositiveNonneg_finiteSystem
        hxneg_nonneg hunder_neg)
theorem finiteUnderflowRoundTowardZero_abs_le_abs
    {fmt : FloatingPointFormat} {x : ℝ}
    (_hunder : fmt.finiteUnderflowRange x) :
    |fmt.finiteUnderflowRoundTowardZero x| ≤ |x| := by
  unfold finiteUnderflowRoundTowardZero
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    have hout_nonneg :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg x
    have hout_le :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_le hxnonneg
    rw [abs_of_nonneg hxnonneg, abs_of_nonneg hout_nonneg]
    exact hout_le
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hout_nonneg :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_nonneg (-x)
    have hout_le :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_le hxneg_nonneg
    have hxneg : x < 0 := lt_of_not_ge hxnonneg
    rw [abs_of_neg hxneg, abs_of_nonneg hout_nonneg]
    exact hout_le
theorem le_finiteUnderflowRoundTowardPositive
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    x ≤ fmt.finiteUnderflowRoundTowardPositive x := by
  unfold finiteUnderflowRoundTowardPositive
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact
      fmt.le_finiteUnderflowRoundTowardPositiveNonneg hxnonneg hunder
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hout_le :=
      fmt.finiteUnderflowRoundTowardZeroNonneg_le hxneg_nonneg
    linarith
theorem finiteUnderflowRoundTowardNegative_le
    {fmt : FloatingPointFormat} {x : ℝ}
    (hunder : fmt.finiteUnderflowRange x) :
    fmt.finiteUnderflowRoundTowardNegative x ≤ x := by
  unfold finiteUnderflowRoundTowardNegative
  by_cases hxnonneg : 0 ≤ x
  · simp [hxnonneg]
    exact fmt.finiteUnderflowRoundTowardZeroNonneg_le hxnonneg
  · simp [hxnonneg]
    have hxneg_nonneg : 0 ≤ -x := by linarith
    have hunder_neg : fmt.finiteUnderflowRange (-x) := by
      simpa [finiteUnderflowRange, abs_neg] using hunder
    have hle :=
      fmt.le_finiteUnderflowRoundTowardPositiveNonneg
        hxneg_nonneg hunder_neg
    linarith
/-- Exact finite representable inputs round to themselves with signed relative
error witness `delta = 0`.  This includes zero, normalized values, and
subnormals. -/
theorem nearestRoundingToFinite_exact_signedRelErrorWitness
    {fmt : FloatingPointFormat} {x : ℝ}
    (hx : fmt.finiteSystem x) :
    ∃ δ : ℝ,
      |δ| ≤ fmt.unitRoundoff ∧
        signedRelErrorWitness x x δ ∧
          fmt.nearestRoundingToFinite x x := by
  refine ⟨0, ?_, ?_, fmt.nearestRoundingToFinite_self hx⟩
  · simpa using fmt.unitRoundoff_nonneg
  · unfold signedRelErrorWitness
    ring

end FloatingPointFormat

end

end NumStability
