import HighamBench.P12Definitions
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

namespace HighamBench

noncomputable def p12NumStabilityFormat
    (fmt : P12RadixFormat) : NumStability.FloatingPointFormat where
  beta := fmt.beta
  t := fmt.precision
  emin := fmt.normalEmin
  emax := fmt.normalEmax
  beta_ge_two := fmt.beta_ge_two
  t_pos := fmt.precision_pos
  emin_le_emax := by
    unfold P12RadixFormat.normalEmin P12RadixFormat.normalEmax
    simpa [add_comm] using
      (add_le_add_right fmt.emin_le_emax (fmt.precision : ℤ))

private theorem p12_normalizedValue_eq
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) (e : ℤ) :
    (p12NumStabilityFormat fmt).normalizedValue negative m e =
      fmt.normalizedValue negative m e := by
  rfl

private theorem p12_subnormalValue_eq
    (fmt : P12RadixFormat) (negative : Bool) (m : ℕ) :
    (p12NumStabilityFormat fmt).subnormalValue negative m =
      fmt.subnormalValue negative m := by
  simp [p12NumStabilityFormat, NumStability.FloatingPointFormat.subnormalValue,
    P12RadixFormat.subnormalValue, NumStability.FloatingPointFormat.signValue,
    P12RadixFormat.signValue, NumStability.FloatingPointFormat.betaR,
    P12RadixFormat.betaR, P12RadixFormat.normalEmin]

private theorem p12_normalizedRepresentation_to_numStability
    {fmt : P12RadixFormat} {x : ℝ} {e : ℤ}
    (h : P12NormalizedExponentRepresentation fmt x e) :
    (p12NumStabilityFormat fmt).normalizedExponentRepresentation x e := by
  rcases h with ⟨negative, m, hm, he, hx⟩
  refine ⟨negative, m, ?_, ?_, ?_⟩
  · simpa [p12NumStabilityFormat,
      NumStability.FloatingPointFormat.normalizedMantissa,
      NumStability.FloatingPointFormat.mantissaInRange,
      NumStability.FloatingPointFormat.minNormalMantissa,
      P12RadixFormat.normalizedMantissa,
      P12RadixFormat.minNormalMantissa] using hm
  · simpa [p12NumStabilityFormat,
      NumStability.FloatingPointFormat.exponentInRange,
      P12RadixFormat.normalizedExponentInRange] using he
  · simpa [p12_normalizedValue_eq] using hx

private theorem p12_finiteSystem_of_numStability
    {fmt : P12RadixFormat} {x : ℝ}
    (h : (p12NumStabilityFormat fmt).finiteSystem x) :
    p12FiniteSystem fmt x := by
  rcases h with hzero | hnormal | hsubnormal
  · exact Or.inl hzero
  · rcases hnormal with ⟨negative, m, e, hm, he, hx⟩
    exact Or.inr (Or.inl ⟨negative, m, e, by
      simpa [p12NumStabilityFormat,
        NumStability.FloatingPointFormat.normalizedMantissa,
        NumStability.FloatingPointFormat.mantissaInRange,
        NumStability.FloatingPointFormat.minNormalMantissa,
        P12RadixFormat.normalizedMantissa,
        P12RadixFormat.minNormalMantissa] using hm, by
      simpa [p12NumStabilityFormat,
        NumStability.FloatingPointFormat.exponentInRange,
        P12RadixFormat.normalizedExponentInRange] using he, by
      simpa [p12_normalizedValue_eq] using hx⟩)
  · rcases hsubnormal with ⟨negative, m, hm, hx⟩
    exact Or.inr (Or.inr ⟨negative, m, by
      simpa [p12NumStabilityFormat,
        NumStability.FloatingPointFormat.subnormalMantissa,
        NumStability.FloatingPointFormat.minNormalMantissa,
        P12RadixFormat.subnormalMantissa,
        P12RadixFormat.minNormalMantissa] using hm, by
      simpa [p12_subnormalValue_eq] using hx⟩)

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  let nfmt := p12NumStabilityFormat fmt
  have hx' : nfmt.normalizedExponentRepresentation x ex := by
    simpa [nfmt] using p12_normalizedRepresentation_to_numStability hx
  have hy' : nfmt.normalizedExponentRepresentation y ey := by
    simpa [nfmt] using p12_normalizedRepresentation_to_numStability hy
  have hfinite : p12FiniteSystem fmt (x - y) := by
    apply p12_finiteSystem_of_numStability
    by_cases hstrict : |x - y| < fmt.betaR ^ min ex ey
    · apply nfmt.fergusonMagnitudeExponentConditionLe_sub_finiteSystem
      exact ⟨ex, ey, hx', hy', by simpa [nfmt, p12NumStabilityFormat,
        NumStability.FloatingPointFormat.betaR] using hstrict⟩
    · have habs : |x - y| = fmt.betaR ^ min ex ey :=
        le_antisymm hmag (le_of_not_gt hstrict)
      have hex : nfmt.exponentInRange ex := by
        rcases hx' with ⟨negative, m, hm, he, hxval⟩
        exact he
      have hey : nfmt.exponentInRange ey := by
        rcases hy' with ⟨negative, m, hm, he, hyval⟩
        exact he
      have hk_lower : nfmt.emin ≤ min ex ey := le_min hex.1 hey.1
      have hk_upper : min ex ey < nfmt.emax := by
        simpa [nfmt, p12NumStabilityFormat] using hnoOverflow
      have hk_succ_range : nfmt.exponentInRange (min ex ey + 1) := by
        constructor
        · omega
        · omega
      by_cases hnonneg : 0 ≤ x - y
      · refine Or.inr (Or.inl ⟨false, nfmt.minNormalMantissa,
          min ex ey + 1, nfmt.minNormalMantissa_normalized,
          hk_succ_range, ?_⟩)
        have hvalue : x - y = fmt.betaR ^ min ex ey := by
          simpa [abs_of_nonneg hnonneg] using habs
        calc
          x - y = fmt.betaR ^ min ex ey := hvalue
          _ = nfmt.betaR ^ min ex ey := by
            rfl
          _ = nfmt.normalizedValue false nfmt.minNormalMantissa
                (min ex ey + 1) :=
            (nfmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow
              (min ex ey)).symm
      · have hneg : x - y < 0 := lt_of_not_ge hnonneg
        refine Or.inr (Or.inl ⟨true, nfmt.minNormalMantissa,
          min ex ey + 1, nfmt.minNormalMantissa_normalized,
          hk_succ_range, ?_⟩)
        have hvalue : x - y = -(fmt.betaR ^ min ex ey) := by
          rw [abs_of_neg hneg] at habs
          linarith
        calc
          x - y = -(fmt.betaR ^ min ex ey) := hvalue
          _ = -(nfmt.betaR ^ min ex ey) := by
            rfl
          _ = -nfmt.normalizedValue false nfmt.minNormalMantissa
                (min ex ey + 1) := by
            rw [nfmt.normalizedValue_false_minNormalMantissa_succ_eq_beta_pow]
          _ = nfmt.normalizedValue true nfmt.minNormalMantissa
                (min ex ey + 1) :=
            (nfmt.normalizedValue_true_eq_neg_false _ _).symm
  refine ⟨hfinite, ?_⟩
  rcases hround with ⟨hrounded, hfaithful⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfaithful (x - y) hfinite (by exact Or.inl ⟨hlt, le_rfl⟩)
  · exact hfaithful (x - y) hfinite (by exact Or.inr ⟨le_rfl, hgt⟩)

end HighamBench
