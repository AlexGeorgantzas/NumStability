import HighamBench.P12Definitions
import NumStability.Analysis.FloatingPointArithmetic.ExactSubtraction

namespace HighamBench

private def p12AsFloatingPointFormat (fmt : P12RadixFormat) :
    NumStability.FloatingPointFormat where
  beta := fmt.beta
  t := fmt.precision
  emin := fmt.normalEmin
  emax := fmt.normalEmax
  beta_ge_two := fmt.beta_ge_two
  t_pos := fmt.precision_pos
  emin_le_emax := by
    simpa [P12RadixFormat.normalEmin, P12RadixFormat.normalEmax] using
      add_le_add_right fmt.emin_le_emax (fmt.precision : ℤ)

private theorem p12_normalizedRepresentation_iff
    (fmt : P12RadixFormat) (z : ℝ) (e : ℤ) :
    P12NormalizedExponentRepresentation fmt z e ↔
      (p12AsFloatingPointFormat fmt).normalizedExponentRepresentation z e := by
  rfl

private theorem p12_finiteSystem_iff
    (fmt : P12RadixFormat) (z : ℝ) :
    p12FiniteSystem fmt z ↔
      (p12AsFloatingPointFormat fmt).finiteSystem z := by
  simp only [p12FiniteSystem, NumStability.FloatingPointFormat.finiteSystem,
    NumStability.FloatingPointFormat.normalizedSystem,
    NumStability.FloatingPointFormat.subnormalSystem]
  constructor
  · rintro (rfl | ⟨negative, m, e, hm, he, rfl⟩ | ⟨negative, m, hm, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)
    · exact Or.inr (Or.inr ⟨negative, m, hm, by
        simp [p12AsFloatingPointFormat, P12RadixFormat.subnormalValue,
          NumStability.FloatingPointFormat.subnormalValue,
          P12RadixFormat.signValue, NumStability.FloatingPointFormat.signValue,
          P12RadixFormat.betaR, NumStability.FloatingPointFormat.betaR,
          P12RadixFormat.normalEmin]⟩)
  · rintro (rfl | ⟨negative, m, e, hm, he, rfl⟩ | ⟨negative, m, hm, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨negative, m, e, hm, he, rfl⟩)
    · exact Or.inr (Or.inr ⟨negative, m, hm, by
        simp [p12AsFloatingPointFormat, P12RadixFormat.subnormalValue,
          NumStability.FloatingPointFormat.subnormalValue,
          P12RadixFormat.signValue, NumStability.FloatingPointFormat.signValue,
          P12RadixFormat.betaR, NumStability.FloatingPointFormat.betaR,
          P12RadixFormat.normalEmin]⟩)

theorem p12_t1_exact_subtraction
    (fmt : P12RadixFormat) (x y rounded : ℝ) (ex ey : ℤ)
    (hx : P12NormalizedExponentRepresentation fmt x ex)
    (hy : P12NormalizedExponentRepresentation fmt y ey)
    (hmag : |x - y| ≤ fmt.betaR ^ min ex ey)
    (hnoOverflow : min ex ey < fmt.normalEmax)
    (hround : p12FaithfulInFormat fmt (x - y) rounded) :
    p12FiniteSystem fmt (x - y) ∧ rounded = x - y := by
  -- PROOF_START P12-T1-H001
  let nfmt := p12AsFloatingPointFormat fmt
  have hx' : nfmt.normalizedExponentRepresentation x ex := by
    exact (p12_normalizedRepresentation_iff fmt x ex).mp hx
  have hy' : nfmt.normalizedExponentRepresentation y ey := by
    exact (p12_normalizedRepresentation_iff fmt y ey).mp hy
  have hex' : nfmt.exponentInRange ex := by
    rcases hx' with ⟨_negative, _m, _hm, he, _hx⟩
    exact he
  have hey' : nfmt.exponentInRange ey := by
    rcases hy' with ⟨_negative, _m, _hm, he, _hy⟩
    exact he
  have hfinite' : nfmt.finiteSystem (x - y) := by
    by_cases hstrict : |x - y| < fmt.betaR ^ min ex ey
    · apply nfmt.fergusonMagnitudeExponentConditionLe_sub_finiteSystem
      refine ⟨ex, ey, hx', hy', ?_⟩
      simpa [nfmt, p12AsFloatingPointFormat, P12RadixFormat.betaR,
        NumStability.FloatingPointFormat.betaR] using hstrict
    · have heq : |x - y| = fmt.betaR ^ min ex ey :=
        le_antisymm hmag (le_of_not_gt hstrict)
      have hemin : nfmt.emin ≤ min ex ey + 1 := by
        have : nfmt.emin ≤ min ex ey := le_min hex'.1 hey'.1
        omega
      have hemax : min ex ey + 1 ≤ nfmt.emax := by
        change min ex ey + 1 ≤ fmt.normalEmax
        omega
      have hendpoint : nfmt.finiteSystem (nfmt.betaR ^ min ex ey) := by
        exact Or.inr (Or.inl
          ⟨false, nfmt.minNormalMantissa, min ex ey + 1,
            nfmt.minNormalMantissa_normalized, ⟨hemin, hemax⟩, by
              simpa using
                (nfmt.normalizedValue_false_minNormalMantissa_eq
                  (min ex ey + 1)).symm⟩)
      have heq' : |x - y| = nfmt.betaR ^ min ex ey := by
        simpa [nfmt, p12AsFloatingPointFormat, P12RadixFormat.betaR,
          NumStability.FloatingPointFormat.betaR] using heq
      rcases eq_or_eq_neg_of_abs_eq heq' with hpos | hneg
      · simpa [hpos] using hendpoint
      · have := nfmt.finiteSystem_neg hendpoint
        simpa [hneg] using this
  have hfinite : p12FiniteSystem fmt (x - y) :=
    (p12_finiteSystem_iff fmt (x - y)).mpr hfinite'
  refine ⟨hfinite, ?_⟩
  rcases hround with ⟨_hrounded, hfaithful⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (hfaithful (x - y) hfinite) (Or.inl ⟨hlt, le_rfl⟩)
  · exact (hfaithful (x - y) hfinite) (Or.inr ⟨le_rfl, hgt⟩)

end HighamBench
