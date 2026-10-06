import HighamBench.P12Definitions
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

namespace HighamBench

noncomputable def p12AssociatedFormat (fmt : P12RadixFormat) :
    NumStability.FloatingPointFormat where
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

private theorem p12_normalized_representation_to_associated
    {fmt : P12RadixFormat} {x : ℝ} {e : ℤ}
    (h : P12NormalizedExponentRepresentation fmt x e) :
    (p12AssociatedFormat fmt).normalizedExponentRepresentation x e := by
  simpa [P12NormalizedExponentRepresentation, p12AssociatedFormat,
    P12RadixFormat.normalizedMantissa,
    P12RadixFormat.minNormalMantissa,
    P12RadixFormat.normalizedExponentInRange,
    NumStability.FloatingPointFormat.normalizedExponentRepresentation,
    NumStability.FloatingPointFormat.normalizedMantissa,
    NumStability.FloatingPointFormat.mantissaInRange,
    NumStability.FloatingPointFormat.minNormalMantissa,
    NumStability.FloatingPointFormat.exponentInRange,
    P12RadixFormat.normalizedValue,
    NumStability.FloatingPointFormat.normalizedValue,
    P12RadixFormat.signValue,
    NumStability.FloatingPointFormat.signValue,
    P12RadixFormat.betaR,
    NumStability.FloatingPointFormat.betaR] using h

private theorem p12_finite_of_associated_finite
    {fmt : P12RadixFormat} {x : ℝ}
    (h : (p12AssociatedFormat fmt).finiteSystem x) :
    p12FiniteSystem fmt x := by
  simpa [p12FiniteSystem, p12AssociatedFormat,
    NumStability.FloatingPointFormat.finiteSystem,
    NumStability.FloatingPointFormat.normalizedSystem,
    NumStability.FloatingPointFormat.subnormalSystem,
    P12RadixFormat.normalizedMantissa,
    P12RadixFormat.subnormalMantissa,
    P12RadixFormat.minNormalMantissa,
    P12RadixFormat.normalizedExponentInRange,
    NumStability.FloatingPointFormat.normalizedMantissa,
    NumStability.FloatingPointFormat.subnormalMantissa,
    NumStability.FloatingPointFormat.mantissaInRange,
    NumStability.FloatingPointFormat.minNormalMantissa,
    NumStability.FloatingPointFormat.exponentInRange,
    P12RadixFormat.normalizedValue,
    P12RadixFormat.subnormalValue,
    NumStability.FloatingPointFormat.normalizedValue,
    NumStability.FloatingPointFormat.subnormalValue,
    P12RadixFormat.signValue,
    NumStability.FloatingPointFormat.signValue,
    P12RadixFormat.betaR,
    NumStability.FloatingPointFormat.betaR,
    P12RadixFormat.normalEmin] using h

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  let nfmt := p12AssociatedFormat fmt
  have hx' : nfmt.normalizedExponentRepresentation x ex :=
    p12_normalized_representation_to_associated hx
  have hy' : nfmt.normalizedExponentRepresentation y ey :=
    p12_normalized_representation_to_associated hy
  have hexRange : nfmt.exponentInRange ex := by
    rcases hx' with ⟨_negative, _m, _hm, he, _hx⟩
    exact he
  have heyRange : nfmt.exponentInRange ey := by
    rcases hy' with ⟨_negative, _m, _hm, he, _hy⟩
    exact he
  have hfin' : nfmt.finiteSystem (x - y) := by
    rcases lt_or_eq_of_le hmag with hmaglt | hmageq
    · apply nfmt.fergusonMagnitudeExponentConditionLe_sub_finiteSystem
      exact ⟨ex, ey, hx', hy', hmaglt⟩
    · have hminLower : nfmt.emin ≤ min ex ey :=
        le_min hexRange.1 heyRange.1
      have hsuccRange : nfmt.exponentInRange (min ex ey + 1) := by
        constructor
        · omega
        · change min ex ey + 1 ≤ fmt.normalEmax
          omega
      have hpowFinite : nfmt.finiteSystem (nfmt.betaR ^ min ex ey) := by
        right
        left
        refine ⟨false, nfmt.minNormalMantissa, min ex ey + 1,
          nfmt.minNormalMantissa_normalized, hsuccRange, ?_⟩
        simpa only [add_sub_cancel_right] using
          (nfmt.normalizedValue_false_minNormalMantissa_eq
            (min ex ey + 1)).symm
      by_cases hnonneg : 0 ≤ x - y
      · have heq : x - y = nfmt.betaR ^ min ex ey := by
          rw [abs_of_nonneg hnonneg] at hmageq
          simpa [nfmt, p12AssociatedFormat, P12RadixFormat.betaR,
            NumStability.FloatingPointFormat.betaR] using hmageq
        simpa [heq] using hpowFinite
      · have hneg : x - y < 0 := lt_of_not_ge hnonneg
        have heq : x - y = -(nfmt.betaR ^ min ex ey) := by
          rw [abs_of_neg hneg] at hmageq
          have hnegEq : -(x - y) = nfmt.betaR ^ min ex ey := by
            simpa [nfmt, p12AssociatedFormat, P12RadixFormat.betaR,
              NumStability.FloatingPointFormat.betaR] using hmageq
          linarith
        simpa [heq] using nfmt.finiteSystem_neg hpowFinite
  have hfin : p12FiniteSystem fmt (x - y) :=
    p12_finite_of_associated_finite hfin'
  refine ⟨hfin, ?_⟩
  rcases hround with ⟨_roundedFinite, hfaithful⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact hfaithful (x - y) hfin (Or.inl ⟨hlt, le_rfl⟩)
  · exact hfaithful (x - y) hfin (Or.inr ⟨le_rfl, hgt⟩)

end HighamBench
