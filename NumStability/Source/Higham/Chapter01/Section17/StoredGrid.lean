import NumStability.Source.Higham.Chapter01.Section17.GridVariation

namespace NumStability

/-!
# Concrete IEEE-double stored-grid certificate

Exact round-to-even input and output certificates for the stored source grid
in Kahan's Higham Section 1.17 example. The module defines the stored-grid
evaluation and proves its concrete values at the diagnostic indices 175 and
289.
-/

/-- Stored IEEE-double version of the source grid point.  This makes the input
rounding in the plotted Horner path explicit instead of silently feeding the
exact real grid point to the first primitive operation. -/
noncomputable def ieeeDoubleKahanStoredGridPoint (k : ℕ) : ℝ :=
  FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven (kahanHornerGridPoint k)

/-- IEEE-double Horner path evaluated at the stored source-grid input. -/
noncomputable def ieeeDoubleKahanStoredGridRationalFunction (k : ℕ) : ℝ :=
  ieeeDoubleKahanRationalFunction (ieeeDoubleKahanStoredGridPoint k)

private theorem ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent
    {x a b : ℝ} {leftMantissa : ℕ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hsliceLo :
      FloatingPointFormat.ieeeDoubleFormat.betaR ^ ((1 : ℤ) - 1) ≤ x)
    (hsliceHi : x ≤ FloatingPointFormat.ieeeDoubleFormat.betaR ^ (1 : ℤ))
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa (1 : ℤ))
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) (1 : ℤ))
    (ha_nonneg : 0 ≤ a)
    (hax : a ≤ x) (hxb : x ≤ b)
    (hcloser : |x - b| < |x - a|) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = b := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hfinite :
      fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine
      ⟨false, leftMantissa, (1 : ℤ), hleftMantissa, hrightMantissa,
        Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hnearest :
      FloatingPointFormat.nearestAdjacentRoundToEven x a b leftMantissa = b :=
    FloatingPointFormat.nearestAdjacentRoundToEven_eq_right_of_right_closer
      hcloser
  have hcert : fmt.sourceRoundToEvenEvidence x b := by
    refine Or.inl ?_
    refine ⟨(1 : ℤ), hsliceLo, hsliceHi, Or.inr ?_⟩
    refine
      ⟨a, b, leftMantissa, hadj, ?_, ha_nonneg, hax, hxb, hnearest.symm⟩
    exact ⟨false, (1 : ℤ), hleftMantissa, hleft⟩
  exact FloatingPointFormat.sourceRoundToEvenEvidence_unique hfinite hcert

/-- The selected `k=175` source grid point rounds upward to this IEEE-double
stored input. -/
theorem ieeeDoubleKahanStoredGridPoint_175_eq :
    ieeeDoubleKahanStoredGridPoint 175 =
      (7232781001557191 : ℝ) / 4503599627370496 := by
  unfold ieeeDoubleKahanStoredGridPoint
  apply
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent
      (a := (7232781001557190 : ℝ) / 4503599627370496)
      (leftMantissa := 7232781001557190)
  · apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [kahanHornerGridPoint]
    · norm_num [kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]

/-- The selected `k=289` source grid point rounds upward to this IEEE-double
stored input. -/
theorem ieeeDoubleKahanStoredGridPoint_289_eq :
    ieeeDoubleKahanStoredGridPoint 289 =
      (7232781001557305 : ℝ) / 4503599627370496 := by
  unfold ieeeDoubleKahanStoredGridPoint
  apply
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_one_adjacent
      (a := (7232781001557304 : ℝ) / 4503599627370496)
      (leftMantissa := 7232781001557304)
  · apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [kahanHornerGridPoint]
    · norm_num [kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.ieeeDoubleFormat,
      FloatingPointFormat.betaR, kahanHornerGridPoint]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num [FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  · norm_num
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]
  · norm_num [kahanHornerGridPoint]

/-- First numerator Horner primitive at the selected stored input `k=175`.
The product `4*xstored` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_m0_175_eq :
    ieeeDoubleKahanNumerator_m0 (ieeeDoubleKahanStoredGridPoint 175) =
      (7232781001557191 : ℝ) / 1125899906842624 := by
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  unfold ieeeDoubleKahanNumerator_m0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 7232781001557191, (3 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- First numerator Horner primitive at the selected stored input `k=289`.
The product `4*xstored` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_m0_289_eq :
    ieeeDoubleKahanNumerator_m0 (ieeeDoubleKahanStoredGridPoint 289) =
      (7232781001557305 : ℝ) / 1125899906842624 := by
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  unfold ieeeDoubleKahanNumerator_m0
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 7232781001557305, (3 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Second numerator Horner primitive at the selected stored input `k=175`.
The exact subtraction `59 - m0` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_s0_175_eq :
    ieeeDoubleKahanNumerator_s0 (ieeeDoubleKahanStoredGridPoint 175) =
      (7399414187769703 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanNumerator_s0
  rw [ieeeDoubleKahanStoredGridNumerator_m0_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 59
      ((7232781001557191 : ℝ) / 1125899906842624)
  let a : ℝ := (7399414187769703 : ℝ) / 140737488355328
  let b : ℝ := (7399414187769704 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7399414187769703 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7399414187769703 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 7399414187769703, (6 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 59
          ((7232781001557191 : ℝ) / 1125899906842624)) =
      (7399414187769703 : ℝ) / 140737488355328
  simpa [fmt, exact, a] using hround

/-- Second numerator Horner primitive at the selected stored input `k=289`.
The exact subtraction `59 - m0` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_s0_289_eq :
    ieeeDoubleKahanNumerator_s0 (ieeeDoubleKahanStoredGridPoint 289) =
      (7399414187769689 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanNumerator_s0
  rw [ieeeDoubleKahanStoredGridNumerator_m0_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 59
      ((7232781001557305 : ℝ) / 1125899906842624)
  let a : ℝ := (7399414187769688 : ℝ) / 140737488355328
  let b : ℝ := (7399414187769689 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7399414187769688 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7399414187769688 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 7399414187769688, (6 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 59
          ((7232781001557305 : ℝ) / 1125899906842624)) =
      (7399414187769689 : ℝ) / 140737488355328
  simpa [fmt, exact, b] using hround

/-- Third numerator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s0` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m1_175_eq :
    ieeeDoubleKahanNumerator_m1 (ieeeDoubleKahanStoredGridPoint 175) =
      (5941729592779215 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanNumerator_m1
  rw [ieeeDoubleKahanStoredGridNumerator_s0_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((7399414187769703 : ℝ) / 140737488355328)
  let a : ℝ := (5941729592779214 : ℝ) / 70368744177664
  let b : ℝ := (5941729592779215 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5941729592779214 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5941729592779214 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5941729592779214, (7 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((7399414187769703 : ℝ) / 140737488355328)) =
      (5941729592779215 : ℝ) / 70368744177664
  simpa [fmt, exact, b] using hround

/-- Third numerator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s0` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m1_289_eq :
    ieeeDoubleKahanNumerator_m1 (ieeeDoubleKahanStoredGridPoint 289) =
      (5941729592779297 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanNumerator_m1
  rw [ieeeDoubleKahanStoredGridNumerator_s0_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((7399414187769689 : ℝ) / 140737488355328)
  let a : ℝ := (5941729592779297 : ℝ) / 70368744177664
  let b : ℝ := (5941729592779298 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5941729592779297 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5941729592779297 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5941729592779297, (7 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((7399414187769689 : ℝ) / 140737488355328)) =
      (5941729592779297 : ℝ) / 70368744177664
  simpa [fmt, exact, a] using hround

/-- Fourth numerator Horner primitive at the selected stored input `k=175`.
The exact subtraction `324 - m1` is exactly halfway between adjacent
IEEE-double endpoints, and the left mantissa is even. -/
theorem ieeeDoubleKahanStoredGridNumerator_s1_175_eq :
    ieeeDoubleKahanNumerator_s1 (ieeeDoubleKahanStoredGridPoint 175) =
      (8428871760391960 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanNumerator_s1
  rw [ieeeDoubleKahanStoredGridNumerator_m1_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 324
      ((5941729592779215 : ℝ) / 70368744177664)
  let a : ℝ := (8428871760391960 : ℝ) / 35184372088832
  let b : ℝ := (8428871760391961 : ℝ) / 35184372088832
  have hm : fmt.normalizedMantissa 8428871760391960 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (8428871760391960 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 8428871760391960 (8 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (8428871760391960 + 1) (8 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 8428871760391960, (8 : ℤ), hm, hmnext, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have heven : FloatingPointFormat.evenMantissa 8428871760391960 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hm hleft htie heven
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 324
          ((5941729592779215 : ℝ) / 70368744177664)) =
      (8428871760391960 : ℝ) / 35184372088832
  simpa [fmt, exact, a] using hround

/-- Fourth numerator Horner primitive at the selected stored input `k=289`.
The exact subtraction `324 - m1` is exactly halfway between adjacent
IEEE-double endpoints, and the left mantissa is odd, so the right endpoint is
chosen. -/
theorem ieeeDoubleKahanStoredGridNumerator_s1_289_eq :
    ieeeDoubleKahanNumerator_s1 (ieeeDoubleKahanStoredGridPoint 289) =
      (8428871760391920 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanNumerator_s1
  rw [ieeeDoubleKahanStoredGridNumerator_m1_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 324
      ((5941729592779297 : ℝ) / 70368744177664)
  let a : ℝ := (8428871760391919 : ℝ) / 35184372088832
  let b : ℝ := (8428871760391920 : ℝ) / 35184372088832
  have hm : fmt.normalizedMantissa 8428871760391919 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (8428871760391919 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 8428871760391919 (8 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (8428871760391919 + 1) (8 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 8428871760391919, (8 : ℤ), hm, hmnext, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hodd : ¬ FloatingPointFormat.evenMantissa 8428871760391919 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hm hleft htie hodd
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 324
          ((5941729592779297 : ℝ) / 70368744177664)) =
      (8428871760391920 : ℝ) / 35184372088832
  simpa [fmt, exact, b] using hround

/-- Fifth numerator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s1` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m2_175_eq :
    ieeeDoubleKahanNumerator_m2 (ieeeDoubleKahanStoredGridPoint 175) =
      (6768384023594907 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_m2
  rw [ieeeDoubleKahanStoredGridNumerator_s1_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((8428871760391960 : ℝ) / 35184372088832)
  let a : ℝ := (6768384023594907 : ℝ) / 17592186044416
  let b : ℝ := (6768384023594908 : ℝ) / 17592186044416
  have hm : fmt.normalizedMantissa 6768384023594907 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6768384023594907 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 6768384023594907, (9 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((8428871760391960 : ℝ) / 35184372088832)) =
      (6768384023594907 : ℝ) / 17592186044416
  simpa [fmt, exact, a] using hround

/-- Fifth numerator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s1` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m2_289_eq :
    ieeeDoubleKahanNumerator_m2 (ieeeDoubleKahanStoredGridPoint 289) =
      (6768384023594982 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_m2
  rw [ieeeDoubleKahanStoredGridNumerator_s1_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((8428871760391920 : ℝ) / 35184372088832)
  let a : ℝ := (6768384023594981 : ℝ) / 17592186044416
  let b : ℝ := (6768384023594982 : ℝ) / 17592186044416
  have hm : fmt.normalizedMantissa 6768384023594981 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6768384023594981 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 6768384023594981, (9 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((8428871760391920 : ℝ) / 35184372088832)) =
      (6768384023594982 : ℝ) / 17592186044416
  simpa [fmt, exact, b] using hround

/-- Sixth numerator Horner primitive at the selected stored input `k=175`.
The subtraction `751 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_s2_175_eq :
    ieeeDoubleKahanNumerator_s2 (ieeeDoubleKahanStoredGridPoint 175) =
      (6443347695761509 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_s2
  rw [ieeeDoubleKahanStoredGridNumerator_m2_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 6443347695761509, (9 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Sixth numerator Horner primitive at the selected stored input `k=289`.
The subtraction `751 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridNumerator_s2_289_eq :
    ieeeDoubleKahanNumerator_s2 (ieeeDoubleKahanStoredGridPoint 289) =
      (6443347695761434 : ℝ) / 17592186044416 := by
  unfold ieeeDoubleKahanNumerator_s2
  rw [ieeeDoubleKahanStoredGridNumerator_m2_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 6443347695761434, (9 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Seventh numerator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s2` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m3_175_eq :
    ieeeDoubleKahanNumerator_m3 (ieeeDoubleKahanStoredGridPoint 175) =
      (5174008199696617 : ℝ) / 8796093022208 := by
  unfold ieeeDoubleKahanNumerator_m3
  rw [ieeeDoubleKahanStoredGridNumerator_s2_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((6443347695761509 : ℝ) / 17592186044416)
  let a : ℝ := (5174008199696616 : ℝ) / 8796093022208
  let b : ℝ := (5174008199696617 : ℝ) / 8796093022208
  have hm : fmt.normalizedMantissa 5174008199696616 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5174008199696616 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5174008199696616, (10 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((6443347695761509 : ℝ) / 17592186044416)) =
      (5174008199696617 : ℝ) / 8796093022208
  simpa [fmt, exact, b] using hround

/-- Seventh numerator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s2` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridNumerator_m3_289_eq :
    ieeeDoubleKahanNumerator_m3 (ieeeDoubleKahanStoredGridPoint 289) =
      (5174008199696638 : ℝ) / 8796093022208 := by
  unfold ieeeDoubleKahanNumerator_m3
  rw [ieeeDoubleKahanStoredGridNumerator_s2_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((6443347695761434 : ℝ) / 17592186044416)
  let a : ℝ := (5174008199696637 : ℝ) / 8796093022208
  let b : ℝ := (5174008199696638 : ℝ) / 8796093022208
  have hm : fmt.normalizedMantissa 5174008199696637 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5174008199696637 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, 5174008199696637, (10 : ℤ), hm, hmnext, Or.inl ?_⟩
    constructor
    · norm_num [fmt, a, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
    · norm_num [fmt, b, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hpolicy : fmt.sourceRoundToEvenEvidence exact (fmt.finiteRoundToEven exact) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hexactNormal
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((6443347695761434 : ℝ) / 17592186044416)) =
      (5174008199696638 : ℝ) / 8796093022208
  simpa [fmt, exact, b] using hround

/-- Final rounded numerator Horner value at the selected stored input `k=175`.
The subtraction `622 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerNumerator_175_eq :
    ieeeDoubleKahanHornerNumerator (ieeeDoubleKahanStoredGridPoint 175) =
      (4754586561868144 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanHornerNumerator
  rw [ieeeDoubleKahanStoredGridNumerator_m3_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4754586561868144, (6 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Final rounded numerator Horner value at the selected stored input `k=289`.
The subtraction `622 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerNumerator_289_eq :
    ieeeDoubleKahanHornerNumerator (ieeeDoubleKahanStoredGridPoint 289) =
      (4754586561867808 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanHornerNumerator
  rw [ieeeDoubleKahanStoredGridNumerator_m3_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4754586561867808, (6 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

private theorem ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (hcloser : |x - a| < |x - b|) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = a := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_left_closer
      hpolicy hadj hstrict hcloser

private theorem ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (hcloser : |x - b| < |x - a|) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = b := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_right_closer
      hpolicy hadj hstrict hcloser

private theorem ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_tie_even
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (htie : |x - a| = |x - b|)
    (heven : FloatingPointFormat.evenMantissa leftMantissa) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = a := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_left_of_realOrderAdjacent_strict_between_tie_even
      hpolicy hadj hstrict hleftMantissa hleft htie heven

private theorem ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
    {x a b : ℝ} {leftMantissa : ℕ} {e : ℤ}
    (hxnormal :
      FloatingPointFormat.ieeeDoubleFormat.finiteNormalRange x)
    (hleftMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa leftMantissa)
    (hrightMantissa :
      FloatingPointFormat.ieeeDoubleFormat.normalizedMantissa
        (leftMantissa + 1))
    (hleft :
      a =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          leftMantissa e)
    (hright :
      b =
        FloatingPointFormat.ieeeDoubleFormat.normalizedValue false
          (leftMantissa + 1) e)
    (hstrict : a < x ∧ x < b)
    (htie : |x - a| = |x - b|)
    (hodd : ¬ FloatingPointFormat.evenMantissa leftMantissa) :
    FloatingPointFormat.ieeeDoubleFormat.finiteRoundToEven x = b := by
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  have hpolicy : fmt.sourceRoundToEvenEvidence x (fmt.finiteRoundToEven x) :=
    fmt.finiteRoundToEven_sourceRoundToEvenEvidence_of_finiteNormalRange
      hxnormal
  have hstruct : fmt.sameExponentAdjacentNormalized a b := by
    refine ⟨false, leftMantissa, e, hleftMantissa, hrightMantissa, Or.inl ?_⟩
    exact ⟨hleft, hright⟩
  have hadj : fmt.realOrderAdjacentNormalized a b :=
    fmt.realOrderAdjacentNormalized_of_sameExponentAdjacentNormalized hstruct
  exact
    fmt.sourceRoundToEvenEvidence_eq_right_of_realOrderAdjacent_strict_between_tie_odd
      hpolicy hadj hstrict hleftMantissa hleft htie hodd

/-- First denominator Horner primitive at the selected stored input `k=175`.
The exact subtraction `14 - xstored` lies closer to the left adjacent
IEEE-double endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s0_175_eq :
    ieeeDoubleKahanDenominator_s0 (ieeeDoubleKahanStoredGridPoint 175) =
      (6977201722703719 : ℝ) / 562949953421312 := by
  unfold ieeeDoubleKahanDenominator_s0
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 14
      ((7232781001557191 : ℝ) / 4503599627370496)
  let a : ℝ := (6977201722703719 : ℝ) / 562949953421312
  let b : ℝ := (6977201722703720 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 6977201722703719 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6977201722703719 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 6977201722703719 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (6977201722703719 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 14
          ((7232781001557191 : ℝ) / 4503599627370496)) =
      (6977201722703719 : ℝ) / 562949953421312
  simpa [fmt, exact, a] using hround

/-- First denominator Horner primitive at the selected stored input `k=289`.
The exact subtraction `14 - xstored` lies closer to the right adjacent
IEEE-double endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s0_289_eq :
    ieeeDoubleKahanDenominator_s0 (ieeeDoubleKahanStoredGridPoint 289) =
      (6977201722703705 : ℝ) / 562949953421312 := by
  unfold ieeeDoubleKahanDenominator_s0
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 14
      ((7232781001557305 : ℝ) / 4503599627370496)
  let a : ℝ := (6977201722703704 : ℝ) / 562949953421312
  let b : ℝ := (6977201722703705 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 6977201722703704 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (6977201722703704 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 6977201722703704 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (6977201722703704 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 14
          ((7232781001557305 : ℝ) / 4503599627370496)) =
      (6977201722703705 : ℝ) / 562949953421312
  simpa [fmt, exact, b] using hround

/-- Second denominator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s0` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m1_175_eq :
    ieeeDoubleKahanDenominator_m1 (ieeeDoubleKahanStoredGridPoint 175) =
      (5602692983331221 : ℝ) / 281474976710656 := by
  unfold ieeeDoubleKahanDenominator_m1
  rw [ieeeDoubleKahanStoredGridDenominator_s0_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((6977201722703719 : ℝ) / 562949953421312)
  let a : ℝ := (5602692983331221 : ℝ) / 281474976710656
  let b : ℝ := (5602692983331222 : ℝ) / 281474976710656
  have hm : fmt.normalizedMantissa 5602692983331221 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5602692983331221 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5602692983331221 (5 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5602692983331221 + 1) (5 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((6977201722703719 : ℝ) / 562949953421312)) =
      (5602692983331221 : ℝ) / 281474976710656
  simpa [fmt, exact, a] using hround

/-- Second denominator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s0` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m1_289_eq :
    ieeeDoubleKahanDenominator_m1 (ieeeDoubleKahanStoredGridPoint 289) =
      (5602692983331299 : ℝ) / 281474976710656 := by
  unfold ieeeDoubleKahanDenominator_m1
  rw [ieeeDoubleKahanStoredGridDenominator_s0_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((6977201722703705 : ℝ) / 562949953421312)
  let a : ℝ := (5602692983331298 : ℝ) / 281474976710656
  let b : ℝ := (5602692983331299 : ℝ) / 281474976710656
  have hm : fmt.normalizedMantissa 5602692983331298 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5602692983331298 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5602692983331298 (5 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5602692983331298 + 1) (5 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((6977201722703705 : ℝ) / 562949953421312)) =
      (5602692983331299 : ℝ) / 281474976710656
  simpa [fmt, exact, b] using hround

/-- Third denominator Horner primitive at the selected stored input `k=175`.
The exact subtraction `72 - m1` is a midpoint case and rounds to the even
right endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s1_175_eq :
    ieeeDoubleKahanDenominator_s1 (ieeeDoubleKahanStoredGridPoint 175) =
      (7331752669918006 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanDenominator_s1
  rw [ieeeDoubleKahanStoredGridDenominator_m1_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 72
      ((5602692983331221 : ℝ) / 281474976710656)
  let a : ℝ := (7331752669918005 : ℝ) / 140737488355328
  let b : ℝ := (7331752669918006 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7331752669918005 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7331752669918005 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7331752669918005 (6 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7331752669918005 + 1) (6 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hodd : ¬ FloatingPointFormat.evenMantissa 7331752669918005 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_tie_odd
      hexactNormal hm hmnext hleft hright hstrict htie hodd
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 72
          ((5602692983331221 : ℝ) / 281474976710656)) =
      (7331752669918006 : ℝ) / 140737488355328
  simpa [fmt, exact, b] using hround

/-- Third denominator Horner primitive at the selected stored input `k=289`.
The exact subtraction `72 - m1` is a midpoint case and rounds to the even left
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_s1_289_eq :
    ieeeDoubleKahanDenominator_s1 (ieeeDoubleKahanStoredGridPoint 289) =
      (7331752669917966 : ℝ) / 140737488355328 := by
  unfold ieeeDoubleKahanDenominator_s1
  rw [ieeeDoubleKahanStoredGridDenominator_m1_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.sub 72
      ((5602692983331299 : ℝ) / 281474976710656)
  let a : ℝ := (7331752669917966 : ℝ) / 140737488355328
  let b : ℝ := (7331752669917967 : ℝ) / 140737488355328
  have hm : fmt.normalizedMantissa 7331752669917966 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7331752669917966 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7331752669917966 (6 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7331752669917966 + 1) (6 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have htie : |exact - a| = |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have heven : FloatingPointFormat.evenMantissa 7331752669917966 := by
    norm_num [FloatingPointFormat.evenMantissa]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_tie_even
      hexactNormal hm hmnext hleft hright hstrict htie heven
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.sub 72
          ((5602692983331299 : ℝ) / 281474976710656)) =
      (7331752669917966 : ℝ) / 140737488355328
  simpa [fmt, exact, a] using hround

/-- Fourth denominator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s1` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m2_175_eq :
    ieeeDoubleKahanDenominator_m2 (ieeeDoubleKahanStoredGridPoint 175) =
      (5887397393944301 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m2
  rw [ieeeDoubleKahanStoredGridDenominator_s1_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((7331752669918006 : ℝ) / 140737488355328)
  let a : ℝ := (5887397393944300 : ℝ) / 70368744177664
  let b : ℝ := (5887397393944301 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5887397393944300 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5887397393944300 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5887397393944300 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5887397393944300 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((7331752669918006 : ℝ) / 140737488355328)) =
      (5887397393944301 : ℝ) / 70368744177664
  simpa [fmt, exact, b] using hround

/-- Fourth denominator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s1` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m2_289_eq :
    ieeeDoubleKahanDenominator_m2 (ieeeDoubleKahanStoredGridPoint 289) =
      (5887397393944361 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m2
  rw [ieeeDoubleKahanStoredGridDenominator_s1_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((7331752669917966 : ℝ) / 140737488355328)
  let a : ℝ := (5887397393944361 : ℝ) / 70368744177664
  let b : ℝ := (5887397393944362 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 5887397393944361 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (5887397393944361 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 5887397393944361 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (5887397393944361 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((7331752669917966 : ℝ) / 140737488355328)) =
      (5887397393944361 : ℝ) / 70368744177664
  simpa [fmt, exact, a] using hround

/-- Fifth denominator Horner primitive at the selected stored input `k=175`.
The subtraction `151 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridDenominator_s2_175_eq :
    ieeeDoubleKahanDenominator_s2 (ieeeDoubleKahanStoredGridPoint 175) =
      (4738282976882963 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_s2
  rw [ieeeDoubleKahanStoredGridDenominator_m2_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4738282976882963, (7 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Fifth denominator Horner primitive at the selected stored input `k=289`.
The subtraction `151 - m2` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridDenominator_s2_289_eq :
    ieeeDoubleKahanDenominator_s2 (ieeeDoubleKahanStoredGridPoint 289) =
      (4738282976882903 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_s2
  rw [ieeeDoubleKahanStoredGridDenominator_m2_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 4738282976882903, (7 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Sixth denominator Horner primitive at the selected stored input `k=175`.
The exact product `xstored*s2` lies closer to the left adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m3_175_eq :
    ieeeDoubleKahanDenominator_m3 (ieeeDoubleKahanStoredGridPoint 175) =
      (7609682460874222 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m3
  rw [ieeeDoubleKahanStoredGridDenominator_s2_175_eq]
  rw [ieeeDoubleKahanStoredGridPoint_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557191 : ℝ) / 4503599627370496)
      ((4738282976882963 : ℝ) / 70368744177664)
  let a : ℝ := (7609682460874222 : ℝ) / 70368744177664
  let b : ℝ := (7609682460874223 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 7609682460874222 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7609682460874222 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7609682460874222 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7609682460874222 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hleftCloser : |exact - a| < |exact - b| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = a :=
    ieeeDouble_finiteRoundToEven_eq_left_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hleftCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557191 : ℝ) / 4503599627370496)
          ((4738282976882963 : ℝ) / 70368744177664)) =
      (7609682460874222 : ℝ) / 70368744177664
  simpa [fmt, exact, a] using hround

/-- Sixth denominator Horner primitive at the selected stored input `k=289`.
The exact product `xstored*s2` lies closer to the right adjacent IEEE-double
endpoint. -/
theorem ieeeDoubleKahanStoredGridDenominator_m3_289_eq :
    ieeeDoubleKahanDenominator_m3 (ieeeDoubleKahanStoredGridPoint 289) =
      (7609682460874246 : ℝ) / 70368744177664 := by
  unfold ieeeDoubleKahanDenominator_m3
  rw [ieeeDoubleKahanStoredGridDenominator_s2_289_eq]
  rw [ieeeDoubleKahanStoredGridPoint_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.mul
      ((7232781001557305 : ℝ) / 4503599627370496)
      ((4738282976882903 : ℝ) / 70368744177664)
  let a : ℝ := (7609682460874245 : ℝ) / 70368744177664
  let b : ℝ := (7609682460874246 : ℝ) / 70368744177664
  have hm : fmt.normalizedMantissa 7609682460874245 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (7609682460874245 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 7609682460874245 (7 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (7609682460874245 + 1) (7 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.mul
          ((7232781001557305 : ℝ) / 4503599627370496)
          ((4738282976882903 : ℝ) / 70368744177664)) =
      (7609682460874246 : ℝ) / 70368744177664
  simpa [fmt, exact, b] using hround

/-- Final rounded denominator Horner value at the selected stored input
`k=175`. The subtraction `112 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerDenominator_175_eq :
    ieeeDoubleKahanHornerDenominator (ieeeDoubleKahanStoredGridPoint 175) =
      (135808443512073 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanHornerDenominator
  rw [ieeeDoubleKahanStoredGridDenominator_m3_175_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 8691740384772672, (2 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Final rounded denominator Horner value at the selected stored input
`k=289`. The subtraction `112 - m3` is exactly representable in IEEE double. -/
theorem ieeeDoubleKahanStoredGridHornerDenominator_289_eq :
    ieeeDoubleKahanHornerDenominator (ieeeDoubleKahanStoredGridPoint 289) =
      (135808443512061 : ℝ) / 35184372088832 := by
  unfold ieeeDoubleKahanHornerDenominator
  rw [ieeeDoubleKahanStoredGridDenominator_m3_289_eq]
  rw [FloatingPointFormat.finiteRoundToEvenOp_eq_exact_of_finiteSystem]
  · norm_num [BasicOp.exact]
  · refine Or.inr (Or.inl ?_)
    refine ⟨false, 8691740384771904, (2 : ℤ), ?_, ?_, ?_⟩
    · norm_num [FloatingPointFormat.normalizedMantissa,
        FloatingPointFormat.mantissaInRange,
        FloatingPointFormat.minNormalMantissa,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [FloatingPointFormat.exponentInRange,
        FloatingPointFormat.ieeeDoubleFormat]
    · norm_num [BasicOp.exact, FloatingPointFormat.normalizedValue,
        FloatingPointFormat.signValue,
        FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]

/-- Final stored-input IEEE-double Horner quotient at selected input `k=175`. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_175_eq :
    ieeeDoubleKahanStoredGridRationalFunction 175 =
      (4927149988474991 : ℝ) / 562949953421312 := by
  unfold ieeeDoubleKahanStoredGridRationalFunction
  unfold ieeeDoubleKahanRationalFunction
  rw [ieeeDoubleKahanStoredGridHornerNumerator_175_eq]
  rw [ieeeDoubleKahanStoredGridHornerDenominator_175_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.div
      ((4754586561868144 : ℝ) / 140737488355328)
      ((135808443512073 : ℝ) / 35184372088832)
  let a : ℝ := (4927149988474990 : ℝ) / 562949953421312
  let b : ℝ := (4927149988474991 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 4927149988474990 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (4927149988474990 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 4927149988474990 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (4927149988474990 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.div
          ((4754586561868144 : ℝ) / 140737488355328)
          ((135808443512073 : ℝ) / 35184372088832)) =
      (4927149988474991 : ℝ) / 562949953421312
  simpa [fmt, exact, b] using hround

/-- Final stored-input IEEE-double Horner quotient at selected input `k=289`. -/
theorem ieeeDoubleKahanStoredGridRationalFunction_289_eq :
    ieeeDoubleKahanStoredGridRationalFunction 289 =
      (2463574994237539 : ℝ) / 281474976710656 := by
  unfold ieeeDoubleKahanStoredGridRationalFunction
  unfold ieeeDoubleKahanRationalFunction
  rw [ieeeDoubleKahanStoredGridHornerNumerator_289_eq]
  rw [ieeeDoubleKahanStoredGridHornerDenominator_289_eq]
  let fmt := FloatingPointFormat.ieeeDoubleFormat
  let exact : ℝ :=
    BasicOp.exact BasicOp.div
      ((4754586561867808 : ℝ) / 140737488355328)
      ((135808443512061 : ℝ) / 35184372088832)
  let a : ℝ := (4927149988475077 : ℝ) / 562949953421312
  let b : ℝ := (4927149988475078 : ℝ) / 562949953421312
  have hm : fmt.normalizedMantissa 4927149988475077 := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hmnext : fmt.normalizedMantissa (4927149988475077 + 1) := by
    norm_num [fmt, FloatingPointFormat.normalizedMantissa,
      FloatingPointFormat.mantissaInRange,
      FloatingPointFormat.minNormalMantissa,
      FloatingPointFormat.ieeeDoubleFormat]
  have hleft :
      a =
        fmt.normalizedValue false 4927149988475077 (4 : ℤ) := by
    norm_num [fmt, a, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hright :
      b =
        fmt.normalizedValue false (4927149988475077 + 1) (4 : ℤ) := by
    norm_num [fmt, b, FloatingPointFormat.normalizedValue,
      FloatingPointFormat.signValue,
      FloatingPointFormat.ieeeDoubleFormat, FloatingPointFormat.betaR]
  have hexactNormal : fmt.finiteNormalRange exact := by
    apply ieeeDouble_finiteNormalRange_of_abs_between_one_thousand
    · norm_num [exact, BasicOp.exact]
    · norm_num [exact, BasicOp.exact]
  have hstrict : a < exact ∧ exact < b := by
    norm_num [exact, a, b, BasicOp.exact]
  have hrightCloser : |exact - b| < |exact - a| := by
    norm_num [exact, a, b, BasicOp.exact]
  have hround : fmt.finiteRoundToEven exact = b :=
    ieeeDouble_finiteRoundToEven_eq_right_of_pos_same_exp_adjacent
      hexactNormal hm hmnext hleft hright hstrict hrightCloser
  change
    fmt.finiteRoundToEven
        (BasicOp.exact BasicOp.div
          ((4754586561867808 : ℝ) / 140737488355328)
          ((135808443512061 : ℝ) / 35184372088832)) =
      (2463574994237539 : ℝ) / 281474976710656
  have hb : b = (2463574994237539 : ℝ) / 281474976710656 := by
    norm_num [b]
  rw [← hb]
  simpa [fmt, exact] using hround

end NumStability
