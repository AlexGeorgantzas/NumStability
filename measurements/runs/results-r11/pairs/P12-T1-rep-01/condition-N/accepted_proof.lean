import HighamBench.P12Definitions
import Mathlib

namespace HighamBench

private lemma p12_betaR_pos (fmt : P12RadixFormat) : 0 < fmt.betaR := by
  unfold P12RadixFormat.betaR
  exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) fmt.beta_ge_two)

private lemma p12_scale_shift_down
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    fmt.signValue negative * (m : ℝ) *
        fmt.betaR ^ (e + 1 - (fmt.precision : ℤ)) =
      fmt.signValue negative * (m * fmt.beta : ℕ) *
        fmt.betaR ^ (e - (fmt.precision : ℤ)) := by
  have hb : fmt.betaR ≠ 0 := ne_of_gt (p12_betaR_pos fmt)
  have he : e + 1 - (fmt.precision : ℤ) =
      1 + (e - (fmt.precision : ℤ)) := by omega
  rw [he, zpow_add₀ hb]
  simp [P12RadixFormat.betaR]
  ring

private lemma p12_minMantissa_mul_beta (fmt : P12RadixFormat) :
    fmt.minNormalMantissa * fmt.beta = fmt.beta ^ fmt.precision := by
  unfold P12RadixFormat.minNormalMantissa
  rw [← pow_succ]
  congr 1
  have hp := fmt.precision_pos
  omega

private lemma p12_finite_scaled
    (fmt : P12RadixFormat) (d : ℕ) (negative : Bool) (m : ℕ)
    (hm : m ≤ fmt.beta ^ fmt.precision)
    (hmax : fmt.normalEmin + (d : ℤ) < fmt.normalEmax) :
    p12FiniteSystem fmt
      (fmt.signValue negative * (m : ℝ) *
        fmt.betaR ^
          (fmt.normalEmin + (d : ℤ) - (fmt.precision : ℤ))) := by
  induction d generalizing m negative with
  | zero =>
      by_cases hm0 : m = 0
      · left
        simp [hm0]
      by_cases hsmall : m < fmt.minNormalMantissa
      · right
        right
        refine ⟨negative, m, ⟨Nat.pos_of_ne_zero hm0, hsmall⟩, ?_⟩
        simp [P12RadixFormat.normalEmin,
          P12RadixFormat.subnormalValue]
      · have hmin : fmt.minNormalMantissa ≤ m := by omega
        by_cases htop : m < fmt.beta ^ fmt.precision
        · right
          left
          refine ⟨negative, m, fmt.normalEmin, ⟨hmin, htop⟩,
            ⟨le_rfl, ?_⟩, ?_⟩
          · exact le_of_lt (by simpa using hmax)
          · simp [P12RadixFormat.normalizedValue]
        · have hmeq : m = fmt.beta ^ fmt.precision := by omega
          right
          left
          refine ⟨negative, fmt.minNormalMantissa, fmt.normalEmin + 1,
            ?_, ?_, ?_⟩
          · constructor
            · exact le_rfl
            · rw [← p12_minMantissa_mul_beta fmt]
              have hminpos : 0 < fmt.minNormalMantissa := by
                unfold P12RadixFormat.minNormalMantissa
                exact pow_pos (Nat.zero_lt_of_lt fmt.beta_ge_two) _
              nlinarith [fmt.beta_ge_two]
          · constructor
            · omega
            · omega
          · rw [hmeq]
            unfold P12RadixFormat.normalizedValue
            have hshift := (p12_scale_shift_down fmt negative
              fmt.minNormalMantissa fmt.normalEmin).symm
            rw [p12_minMantissa_mul_beta fmt] at hshift
            simpa using hshift
  | succ d ih =>
      by_cases hm0 : m = 0
      · left
        simp [hm0]
      by_cases hsmall : m < fmt.minNormalMantissa
      · have hmul : m * fmt.beta ≤ fmt.beta ^ fmt.precision := by
          rw [← p12_minMantissa_mul_beta fmt]
          exact Nat.mul_le_mul_right fmt.beta (Nat.le_of_lt hsmall)
        have hrec := ih negative (m * fmt.beta) hmul (by omega)
        rw [show fmt.normalEmin + ((d + 1 : ℕ) : ℤ) =
          (fmt.normalEmin + (d : ℤ)) + 1 by push_cast; ring]
        rw [p12_scale_shift_down]
        exact hrec
      · have hmin : fmt.minNormalMantissa ≤ m := by omega
        by_cases htop : m < fmt.beta ^ fmt.precision
        · right
          left
          refine ⟨negative, m, fmt.normalEmin + ((d + 1 : ℕ) : ℤ),
            ⟨hmin, htop⟩, ⟨?_, ?_⟩, rfl⟩
          · omega
          · exact le_of_lt hmax
        · have hmeq : m = fmt.beta ^ fmt.precision := by omega
          right
          left
          refine ⟨negative, fmt.minNormalMantissa,
            fmt.normalEmin + ((d + 1 : ℕ) : ℤ) + 1, ?_, ?_, ?_⟩
          · constructor
            · exact le_rfl
            · rw [← p12_minMantissa_mul_beta fmt]
              have hminpos : 0 < fmt.minNormalMantissa := by
                unfold P12RadixFormat.minNormalMantissa
                exact pow_pos (Nat.zero_lt_of_lt fmt.beta_ge_two) _
              nlinarith [fmt.beta_ge_two]
          · constructor <;> omega
          · rw [hmeq]
            unfold P12RadixFormat.normalizedValue
            have hshift := (p12_scale_shift_down fmt negative
              fmt.minNormalMantissa
              (fmt.normalEmin + ((d + 1 : ℕ) : ℤ))).symm
            rw [p12_minMantissa_mul_beta fmt] at hshift
            exact hshift

private lemma p12_factor_at_smaller_exponent
    (fmt : P12RadixFormat) (a k : ℤ) (hk : k ≤ a) :
    ((fmt.beta ^ (a - k).toNat : ℕ) : ℝ) *
        fmt.betaR ^ (k - (fmt.precision : ℤ)) =
      fmt.betaR ^ (a - (fmt.precision : ℤ)) := by
  have hb : fmt.betaR ≠ 0 := ne_of_gt (p12_betaR_pos fmt)
  have hto : ((a - k).toNat : ℤ) = a - k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  rw [show ((fmt.beta ^ (a - k).toNat : ℕ) : ℝ) =
    fmt.betaR ^ (a - k).toNat by
      simp [P12RadixFormat.betaR]]
  rw [← zpow_natCast, hto, ← zpow_add₀ hb]
  congr 1
  omega

private lemma p12_power_split (fmt : P12RadixFormat) (k : ℤ) :
    fmt.betaR ^ k =
      ((fmt.beta ^ fmt.precision : ℕ) : ℝ) *
        fmt.betaR ^ (k - (fmt.precision : ℤ)) := by
  have hb : fmt.betaR ≠ 0 := ne_of_gt (p12_betaR_pos fmt)
  rw [show ((fmt.beta ^ fmt.precision : ℕ) : ℝ) =
    fmt.betaR ^ fmt.precision by simp [P12RadixFormat.betaR]]
  rw [← zpow_natCast, ← zpow_add₀ hb]
  congr 1
  omega

private lemma p12_finite_scaled_at_exponent
    (fmt : P12RadixFormat) (k : ℤ) (negative : Bool) (m : ℕ)
    (hm : m ≤ fmt.beta ^ fmt.precision)
    (hmin : fmt.normalEmin ≤ k) (hmax : k < fmt.normalEmax) :
    p12FiniteSystem fmt
      (fmt.signValue negative * (m : ℝ) *
        fmt.betaR ^ (k - (fmt.precision : ℤ))) := by
  let d := (k - fmt.normalEmin).toNat
  have hdcast : (d : ℤ) = k - fmt.normalEmin := by
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hmin)
  have heq : fmt.normalEmin + (d : ℤ) = k := by omega
  simpa [heq] using
    (p12_finite_scaled fmt d negative m hm (by simpa [heq] using hmax))

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  rcases hx with ⟨nx, mx, hmx, hex, hxeq⟩
  rcases hy with ⟨ny, my, hmy, hey, hyeq⟩
  let k : ℤ := min ex ey
  have hkx : k ≤ ex := min_le_left ex ey
  have hky : k ≤ ey := min_le_right ex ey
  have hkmin : fmt.normalEmin ≤ k := le_min hex.1 hey.1
  have hkmax : k < fmt.normalEmax := hnoOverflow
  let z : ℤ :=
    (if nx then -1 else 1) * (mx : ℤ) *
        (fmt.beta : ℤ) ^ (ex - k).toNat -
      (if ny then -1 else 1) * (my : ℤ) *
        (fmt.beta : ℤ) ^ (ey - k).toNat
  have hxy : x - y = (z : ℝ) *
      fmt.betaR ^ (k - (fmt.precision : ℤ)) := by
    rw [hxeq, hyeq]
    unfold P12RadixFormat.normalizedValue
    rw [← p12_factor_at_smaller_exponent fmt ex k hkx,
      ← p12_factor_at_smaller_exponent fmt ey k hky]
    simp only [z]
    push_cast
    cases nx <;> cases ny <;>
      simp [P12RadixFormat.signValue] <;> ring
  have hscale : 0 < fmt.betaR ^ (k - (fmt.precision : ℤ)) :=
    zpow_pos (p12_betaR_pos fmt) _
  have hfinite : p12FiniteSystem fmt (x - y) := by
    cases hz : z with
    | ofNat n =>
        have hmag' := hmag
        rw [show min ex ey = k by rfl, hxy, hz,
          p12_power_split fmt k] at hmag'
        have habs : |((Int.ofNat n : ℤ) : ℝ)| = (n : ℝ) := by
          rw [Int.ofNat_eq_natCast, Int.cast_natCast, abs_of_nonneg]
          positivity
        rw [abs_mul, habs, abs_of_pos hscale] at hmag'
        have hnR : (n : ℝ) ≤ ((fmt.beta ^ fmt.precision : ℕ) : ℝ) := by
          nlinarith
        have hn : n ≤ fmt.beta ^ fmt.precision := by exact_mod_cast hnR
        have hf := p12_finite_scaled_at_exponent fmt k false n hn hkmin hkmax
        rw [hxy, hz]
        simpa [P12RadixFormat.signValue] using hf
    | negSucc n =>
        have hmag' := hmag
        rw [show min ex ey = k by rfl, hxy, hz,
          p12_power_split fmt k] at hmag'
        have habs : |((Int.negSucc n : ℤ) : ℝ)| = ((n + 1 : ℕ) : ℝ) := by
          rw [Int.cast_negSucc, abs_neg, abs_of_nonneg]
          positivity
        rw [abs_mul, habs, abs_of_pos hscale] at hmag'
        have hnR : ((n + 1 : ℕ) : ℝ) ≤
            ((fmt.beta ^ fmt.precision : ℕ) : ℝ) := by
          nlinarith
        have hn : n + 1 ≤ fmt.beta ^ fmt.precision := by exact_mod_cast hnR
        have hf := p12_finite_scaled_at_exponent fmt k true (n + 1) hn hkmin hkmax
        rw [hxy, hz]
        simpa [P12RadixFormat.signValue] using hf
  refine ⟨hfinite, ?_⟩
  unfold p12FaithfulInFormat p12Faithful at hround
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hround.2 (x - y) hfinite (Or.inl ⟨hlt, le_rfl⟩)
  · exact hround.2 (x - y) hfinite (Or.inr ⟨le_rfl, hgt⟩)

end HighamBench
