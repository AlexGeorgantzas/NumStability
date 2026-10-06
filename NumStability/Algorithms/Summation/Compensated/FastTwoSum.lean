import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Algorithms.Summation.Compensated.CorrectionFormula

namespace NumStability

/-!
# Finite FastTwoSum and correction-formula exactness

Reusable finite round-to-even certificates and exactness theorems for the
two-operation correction formula. Source-specific failed proof routes and
counterexamples live under `NumStability.Source.Higham.Chapter04`.
-/

/-! ### Finite round-to-even bridge for equation (4.7) -/

/-- Concrete finite round-to-even trace for Higham equation (4.7):
`s = round(a+b)` and `e = round(round(a-s)+b)`. -/
noncomputable def finiteCorrectionFormulaTrace
    (fmt : FloatingPointFormat) (a b : ℝ) : CorrectionFormulaTrace :=
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  let e := fmt.finiteRoundToEvenOp BasicOp.add
    (fmt.finiteRoundToEvenOp BasicOp.sub a s) b
  { s := s, e := e }

/-- The rounded `s = fl(a+b)` assignment for the finite round-to-even trace. -/
theorem finiteCorrectionFormulaTrace_s
    (fmt : FloatingPointFormat) (a b : ℝ) :
    (finiteCorrectionFormulaTrace fmt a b).s =
      fmt.finiteRoundToEvenOp BasicOp.add a b := by
  rfl

/-- The rounded `e = fl((a-s)+b)` assignment for the finite round-to-even trace. -/
theorem finiteCorrectionFormulaTrace_e
    (fmt : FloatingPointFormat) (a b : ℝ) :
    (finiteCorrectionFormulaTrace fmt a b).e =
      fmt.finiteRoundToEvenOp BasicOp.add
        (fmt.finiteRoundToEvenOp BasicOp.sub a
          (finiteCorrectionFormulaTrace fmt a b).s) b := by
  rfl

/-- If the intermediate subtraction `a-s` and the final addition `(a-s)+b`
are exact in the concrete finite round-to-even format, then Higham equation
(4.7)'s exactness conclusion holds. -/
theorem finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b)
    (hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  dsimp [CorrectionFormulaTrace.exact, finiteCorrectionFormulaTrace]
  rw [hsub]
  have hadd_exact :
      fmt.finiteRoundToEvenOp BasicOp.add
          (a - fmt.finiteRoundToEvenOp BasicOp.add a b) b =
        (a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b := by
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.add)
        (x := a - fmt.finiteRoundToEvenOp BasicOp.add a b)
        (y := b) hadd)
  rw [hadd_exact]
  ring

/-- Finite-format Sterbenz bridge for Higham equation (4.7).

If `a` and the rounded sum `s = round(a+b)` are finite representable, satisfy
the positive Sterbenz ratio condition, and the final exact error term
`(a-s)+b` is finite representable, then the finite round-to-even correction
trace satisfies `a+b = s+e`.  This is an intermediate finite-format route to
the full Dekker/Knuth/Linnainmaa base-2 theorem, not yet the full all-signs
FastTwoSum result. -/
theorem finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hsterbenz :
      fmt.sterbenzRatioCondition a
        (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b :=
    fmt.finiteRoundToEvenOp_sub_finiteSystem_eq_exact_of_sterbenzRatioCondition
      ha hs hsterbenz
  exact finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    fmt a b hsub hadd

/-- Signed finite-format Sterbenz bridge for Higham equation (4.7).

This extends `finiteCorrectionFormulaTrace_exact_of_sterbenz_and_finite_error_add`
from the positive Sterbenz branch to the same-sign negative branch: if either
`a` and `s = round(a+b)` satisfy the positive Sterbenz ratio condition, or
their sign-flipped values `-a` and `-s` do, then the intermediate subtraction
`a-s` is finite representable and therefore rounded exactly.  The final
error-add representability assumption is still explicit; deriving it from the
printed Dekker/Knuth/Linnainmaa hypotheses remains the full FastTwoSum proof
target. -/
theorem finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hsterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b)))
    (hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs' : fmt.finiteSystem s := by
    simpa [s] using hs
  have hsub_finite : fmt.finiteSystem (a - s) := by
    rcases hsterbenz with hpos | hneg
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := a) (y := s) ha hs' (by simpa [s] using hpos)
    · have hneg_a : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
      have hfin_neg :
          fmt.finiteSystem ((-a) - (-s)) :=
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := -a) (y := -s) hneg_a hneg_s (by simpa [s] using hneg)
      have hrewrite : a - s = -((-a) - (-s)) := by ring
      rw [hrewrite]
      exact fmt.finiteSystem_neg hfin_neg
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b := by
    have hsub_finite' :
        fmt.finiteSystem
          (BasicOp.exact BasicOp.sub a
            (fmt.finiteRoundToEvenOp BasicOp.add a b)) := by
      simpa [BasicOp.exact, s] using hsub_finite
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := a)
        (y := fmt.finiteRoundToEvenOp BasicOp.add a b) hsub_finite')
  exact finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    fmt a b hsub hadd

/-- Two-stage signed finite-format Sterbenz bridge for Higham equation (4.7).

The first signed Sterbenz condition proves that the intermediate subtraction
`a-s` is exact.  The second signed Sterbenz condition proves that the final
exact error term is finite representable via
`(a-s)+b = (a+b)-s`, so the final rounded add is exact as well.  This removes
the explicit final-add finite-system assumption from
`finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add`,
but still leaves the source-level task of deriving these certificates from the
printed FastTwoSum hypotheses. -/
theorem finiteCorrectionFormulaTrace_exact_of_two_signed_sterbenz
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hexact : fmt.finiteSystem (a + b))
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b)))
    (herr_sterbenz :
      fmt.sterbenzRatioCondition (a + b)
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-(a + b))
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs' : fmt.finiteSystem s := by
    simpa [s] using hs
  have herror_finite : fmt.finiteSystem ((a + b) - s) := by
    rcases herr_sterbenz with hpos | hneg
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := a + b) (y := s) hexact hs' (by simpa [s] using hpos)
    · have hneg_exact : fmt.finiteSystem (-(a + b)) :=
        fmt.finiteSystem_neg hexact
      have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
      have hfin_neg :
          fmt.finiteSystem (-(a + b) - (-s)) :=
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := -(a + b)) (y := -s) hneg_exact hneg_s
          (by simpa [s] using hneg)
      have hrewrite : (a + b) - s = -( -(a + b) - (-s)) := by ring
      rw [hrewrite]
      exact fmt.finiteSystem_neg hfin_neg
  have hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b) := by
    have hrewrite :
        (a - s) + b = (a + b) - s := by ring
    simpa [s, hrewrite] using herror_finite
  exact finiteCorrectionFormulaTrace_exact_of_signed_sterbenz_and_finite_error_add
    fmt a b ha hs hsub_sterbenz hadd

/-- Representability certificate for the finite FastTwoSum/correction-formula
bridge behind Higham equation (4.7).

This is not the full Dekker/Knuth/Linnainmaa theorem: it records the exact
finite-format obligations that the all-signs base-2 proof must derive from
the printed assumptions. -/
structure FastTwoSumFiniteCertificate
    (fmt : FloatingPointFormat) (a b : ℝ) : Prop where
  /-- The rounded sum produced by the first operation. -/
  finite_s : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b)
  /-- The intermediate subtraction `a - s` is representable, so it rounds
  exactly. -/
  finite_a_sub_s :
    fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b)
  /-- The true local error `(a+b)-s` is representable, so the final error add
  can round exactly. -/
  finite_error :
    fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b)

/-- The first rounded addition in the finite real-valued selector always
returns a finite-format value.  Future FastTwoSum proofs therefore need not
carry `s`-finite as a source hypothesis; only the two local-error
representability obligations are genuine. -/
theorem FastTwoSumFiniteCertificate.finite_s_unconditional
    (fmt : FloatingPointFormat) (a b : ℝ) :
    fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b) :=
  fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add a b

/-- Build the finite FastTwoSum certificate from exactly the two nontrivial
representability obligations: `a-s` and the true local error `(a+b)-s`. -/
theorem FastTwoSumFiniteCertificate.of_error_obligations
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hsub :
      fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b))
    (herr :
      fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b)) :
    FastTwoSumFiniteCertificate fmt a b :=
  { finite_s := FastTwoSumFiniteCertificate.finite_s_unconditional fmt a b
    finite_a_sub_s := hsub
    finite_error := herr }

/-- Same-lattice coefficient bridge for the true FastTwoSum local error.

If the exact source `a+b` and rounded endpoint `s = fl(a+b)` have already
been placed on the same signed scaled-integer exponent lattice, and their
integer coefficient gap has fewer than `t` radix digits, then the true local
error `(a+b)-s` is finite representable.  This is the direct certificate-field
handoff needed by the remaining finite binary operand-grid proof. -/
theorem FastTwoSumFiniteCertificate.finite_error_of_sameExponentScaledInteger
    (fmt : FloatingPointFormat) (a b : ℝ)
    {negative : Bool} {k l : ℤ} {e : ℤ}
    (hsource :
      a + b =
        fmt.signValue negative * (k : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)))
    (hround :
      fmt.finiteRoundToEvenOp BasicOp.add a b =
        fmt.signValue negative * (l : ℝ) *
          fmt.betaR ^ (e - (fmt.t : ℤ)))
    (he : fmt.exponentInRange e)
    (hdiff : (k - l).natAbs < fmt.beta ^ fmt.t) :
    fmt.finiteSystem ((a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  rw [hsource, hround]
  exact
    fmt.signedScaledIntegerValue_sub_sameExponent_finiteSystem_of_natAbs_diff_lt_mantissaBound
      (negative := negative) (k := k) (l := l) (e := e) he hdiff

/-- The current finite-format two-Sterbenz route packaged as a
`FastTwoSumFiniteCertificate`.

The first signed Sterbenz certificate proves representability of `a-s`; the
second proves representability of the true local error `(a+b)-s`.  The
remaining C4.4 source-level gap is deriving these signed Sterbenz certificates
from the printed base-2 `|a| > |b|` hypotheses. -/
theorem FastTwoSumFiniteCertificate.of_two_signed_sterbenz
    (fmt : FloatingPointFormat) (a b : ℝ)
    (ha : fmt.finiteSystem a)
    (hs : fmt.finiteSystem (fmt.finiteRoundToEvenOp BasicOp.add a b))
    (hexact : fmt.finiteSystem (a + b))
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b)))
    (herr_sterbenz :
      fmt.sterbenzRatioCondition (a + b)
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-(a + b))
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    FastTwoSumFiniteCertificate fmt a b := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs' : fmt.finiteSystem s := by
    simpa [s] using hs
  refine
    { finite_s := hs
      finite_a_sub_s := ?_
      finite_error := ?_ }
  · have hsub_finite : fmt.finiteSystem (a - s) := by
      rcases hsub_sterbenz with hpos | hneg
      · exact
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := a) (y := s) ha hs' (by simpa [s] using hpos)
      · have hneg_a : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
        have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
        have hfin_neg :
            fmt.finiteSystem ((-a) - (-s)) :=
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := -a) (y := -s) hneg_a hneg_s (by simpa [s] using hneg)
        have hrewrite : a - s = -((-a) - (-s)) := by ring
        rw [hrewrite]
        exact fmt.finiteSystem_neg hfin_neg
    simpa [s] using hsub_finite
  · have herror_finite : fmt.finiteSystem ((a + b) - s) := by
      rcases herr_sterbenz with hpos | hneg
      · exact
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := a + b) (y := s) hexact hs' (by simpa [s] using hpos)
      · have hneg_exact : fmt.finiteSystem (-(a + b)) :=
          fmt.finiteSystem_neg hexact
        have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs'
        have hfin_neg :
            fmt.finiteSystem (-(a + b) - (-s)) :=
          fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
            (x := -(a + b)) (y := -s) hneg_exact hneg_s
            (by simpa [s] using hneg)
        have hrewrite : (a + b) - s = -( -(a + b) - (-s)) := by ring
        rw [hrewrite]
        exact fmt.finiteSystem_neg hfin_neg
    simpa [s] using herror_finite

/-- Exact-first-add branch for the finite FastTwoSum/correction-formula
certificate.

If the first rounded addition already returns the exact real sum, then the
intermediate subtraction is `-b` and the true local error is zero.  This closes
one concrete split case of the full base-2 proof of Higham equation (4.7). -/
theorem FastTwoSumFiniteCertificate.of_exact_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hb : fmt.finiteSystem b)
    (hadd :
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b) :
    FastTwoSumFiniteCertificate fmt a b := by
  refine
    { finite_s := fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add a b
      finite_a_sub_s := ?_
      finite_error := ?_ }
  · have hrewrite :
        a - fmt.finiteRoundToEvenOp BasicOp.add a b = -b := by
      rw [hadd]
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg hb
  · have hrewrite :
        (a + b) - fmt.finiteRoundToEvenOp BasicOp.add a b = 0 := by
      rw [hadd]
      ring
    rw [hrewrite]
    exact Or.inl rfl

/-- Base-2 absolute-order FastTwoSum certificate once the remaining
intermediate-subtraction representability field is supplied.

The rounded-add local-error field is no longer a C4.4 obstruction: under the
source finite binary operand hypotheses and finite-normal-range condition it
follows from
`finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange`.
The remaining source-level FastTwoSum/Dekker-Knuth step is exactly the
representability of `a - fl(a+b)`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsub :
      fmt.finiteSystem (a - fmt.finiteRoundToEvenOp BasicOp.add a b)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_error_obligations fmt a b hsub
    (fmt.finiteRoundToEvenOp_add_error_finite_of_base2_abs_order_of_finiteNormalRange
      hbeta ht ha hb hab habRange)

/-- Signed Sterbenz line-2 branch for the finite FastTwoSum certificate.

If `a` and the rounded first sum `s = fl(a+b)` satisfy Sterbenz after a
possible simultaneous sign flip, then the intermediate subtraction `a-s` is
finite representable. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hs : fmt.finiteSystem s :=
    FastTwoSumFiniteCertificate.finite_s_unconditional fmt a b
  have hsub : fmt.finiteSystem (a - s) := by
    rcases hsub_sterbenz with hpos | hneg
    · exact
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := a) (y := s) ha hs (by simpa [s] using hpos)
    · have hneg_a : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_s : fmt.finiteSystem (-s) := fmt.finiteSystem_neg hs
      have hfin_neg :
          fmt.finiteSystem ((-a) - (-s)) :=
        fmt.finiteSystem_sub_finiteSystem_of_sterbenzRatioCondition
          (x := -a) (y := -s) hneg_a hneg_s (by simpa [s] using hneg)
      have hrewrite : a - s = -((-a) - (-s)) := by ring
      rw [hrewrite]
      exact fmt.finiteSystem_neg hfin_neg
  simpa [s] using hsub

/-- Endpoint-inclusive line-2 branch for the finite FastTwoSum certificate.

The strict signed-Sterbenz branch proves representability of `a-s` away from
the endpoints.  If strict Sterbenz fails only because `s = 2*a`, then
`a-s = -a`; if it fails because `a = 2*s`, then `a-s = s`.  Both values are
finite representable from the source finite operand and the rounded sum's
unconditional finite-system certificate. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hsub :
      (fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = 2 * a ∨
      a = 2 * fmt.finiteRoundToEvenOp BasicOp.add a b) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  rcases hsub with hsterbenz | hendpoint
  · exact
      FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz
        fmt ha hsterbenz
  rcases hendpoint with hs_double | ha_double
  · have hs_double' : s = 2 * a := by
      simpa [s] using hs_double
    have hrewrite : a - s = -a := by
      rw [hs_double']
      ring
    rw [hrewrite]
    exact fmt.finiteSystem_neg ha
  · have hs : fmt.finiteSystem s :=
      FastTwoSumFiniteCertificate.finite_s_unconditional fmt a b
    have ha_double' : a = 2 * s := by
      simpa [s] using ha_double
    have hrewrite : a - s = s := by
      rw [ha_double']
      ring
    rw [hrewrite]
    exact hs

/-- Non-strict signed ratio bounds imply the endpoint-inclusive line-2 branch
for the finite FastTwoSum certificate.

This is the next local form needed for the Dekker/Knuth split: if the rounded
first sum `s = fl(a+b)` and `a` satisfy the non-strict Sterbenz bounds after a
possible simultaneous sign flip, then either strict signed Sterbenz holds or
one of the two endpoint equalities `s = 2*a`, `a = 2*s` holds. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s))) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbounds' :
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
    simpa [s] using hbounds
  rcases hbounds' with hpos | hneg
  · rcases hpos with ⟨hs_le, ha_le⟩
    by_cases hs_double : s = 2 * a
    · exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inl (by simpa [s] using hs_double)))
    by_cases ha_double : a = 2 * s
    · exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inr (by simpa [s] using ha_double)))
    have hs_lt : s < 2 * a := lt_of_le_of_ne hs_le hs_double
    have ha_lt : a < 2 * s := lt_of_le_of_ne ha_le ha_double
    have hsterbenz : fmt.sterbenzRatioCondition a s := by
      unfold FloatingPointFormat.sterbenzRatioCondition
      constructor
      · linarith
      · exact ha_lt
    exact
      FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
        fmt ha (Or.inl (Or.inl (by simpa [s] using hsterbenz)))
  · rcases hneg with ⟨hns_le, hna_le⟩
    by_cases hns_double : -s = 2 * (-a)
    · have hs_double : s = 2 * a := by linarith
      exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inl (by simpa [s] using hs_double)))
    by_cases hna_double : -a = 2 * (-s)
    · have ha_double : a = 2 * s := by linarith
      exact
        FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
          fmt ha (Or.inr (Or.inr (by simpa [s] using ha_double)))
    have hns_lt : -s < 2 * (-a) := lt_of_le_of_ne hns_le hns_double
    have hna_lt : -a < 2 * (-s) := lt_of_le_of_ne hna_le hna_double
    have hsterbenz : fmt.sterbenzRatioCondition (-a) (-s) := by
      unfold FloatingPointFormat.sterbenzRatioCondition
      constructor
      · linarith
      · exact hna_lt
    exact
      FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
        fmt ha (Or.inl (Or.inr (by simpa [s] using hsterbenz)))

/-- Positive/negative far-magnitude source split for the signed-ratio
FastTwoSum route.

If the first rounded add is inexact, the already-closed near-magnitude branch
rules out `a < 2*(-b)`.  The exact sum is then bracketed above by the finite
candidate `a` and below either by the finite half `a/2` or, at the bottom
binade, by `minNormalMagnitude`.  The rounded-add interval theorem transfers
that exact-sum bracket to the rounded first sum `s`. -/
theorem FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (ha_nonneg : 0 ≤ a) (hb_nonpos : b ≤ 0)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    s ≤ 2 * a ∧ a ≤ 2 * s := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hmag : -b < a := by
    simpa [abs_of_nonpos hb_nonpos, abs_of_nonneg ha_nonneg] using hab
  have hnot_lt :
      ¬ a < 2 * (-b) :=
    fmt.finiteRoundToEvenOp_add_pos_neg_finiteSystem_not_lt_two_of_ne_exact
      ha hb ha_nonneg hb_nonpos hinexact hmag
  have hfar : 2 * (-b) ≤ a := le_of_not_gt hnot_lt
  have hsum_lower_half : a / 2 ≤ a + b := by
    nlinarith
  have hsum_le_a : a + b ≤ a := by
    linarith
  have hs_le_a : s ≤ a := by
    simpa [s] using
      fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
        ha hsum_le_a
  have hs_le_two_a : s ≤ 2 * a := by
    nlinarith
  have ha_le_two_s : a ≤ 2 * s := by
    rcases
      fmt.finiteSystem_half_or_le_two_minNormalMagnitude_of_nonneg_baseTwo
        hbeta ha ha_nonneg with hhalf_fin | ha_small
    · have hhalf_le_s : a / 2 ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact
            hhalf_fin hsum_lower_half
      nlinarith
    · have hsum_pos : 0 < a + b := by
        nlinarith
      have hsum_abs : |a + b| = a + b :=
        abs_of_nonneg (le_of_lt hsum_pos)
      have hmin_le_sum : fmt.minNormalMagnitude ≤ a + b := by
        simpa [hsum_abs] using habRange.1
      have hmin_le_s : fmt.minNormalMagnitude ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_of_finiteSystem_le_exact
            fmt.minNormalMagnitude_mem_finiteSystem hmin_le_sum
      nlinarith
  exact ⟨hs_le_two_a, ha_le_two_s⟩

/-- Sign-symmetric negative/positive far-magnitude source split for the
signed-ratio FastTwoSum route. -/
theorem FastTwoSumFiniteCertificate.signed_ratio_bounds_of_neg_pos_abs_order_inexact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (ha_nonpos : a ≤ 0) (hb_nonneg : 0 ≤ b)
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  let sp := fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b)
  have hbeta_even : FloatingPointFormat.evenMantissa fmt.beta := by
    unfold FloatingPointFormat.evenMantissa
    omega
  have hs_eq_neg_sp : s = -sp := by
    dsimp [s, sp, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
    have hsum : a + b = -((-a) + (-b)) := by ring
    rw [hsum]
    simpa using
      fmt.finiteRoundToEven_neg hbeta_even ht ((-a) + (-b))
  have hinexact_neg :
      fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b) ≠ (-a) + (-b) := by
    intro hexact_neg
    exact hinexact (by
      change s = a + b
      rw [hs_eq_neg_sp]
      have hsp_exact : sp = (-a) + (-b) := by
        simpa [sp] using hexact_neg
      rw [hsp_exact]
      ring)
  have hneg_range : fmt.finiteNormalRange ((-a) + (-b)) := by
    have h := (fmt.finiteNormalRange_neg_iff (a + b)).mpr habRange
    simpa [add_comm, add_left_comm, add_assoc] using h
  have hpos_bounds :
      sp ≤ 2 * (-a) ∧ -a ≤ 2 * sp := by
    simpa [sp] using
      FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact
        fmt hbeta
        (a := -a) (b := -b)
        (fmt.finiteSystem_neg ha) (fmt.finiteSystem_neg hb)
        (by simpa [abs_neg] using hab)
        hneg_range
        (by linarith) (by linarith)
        hinexact_neg
  have hneg_s_eq_sp : -s = sp := by
    rw [hs_eq_neg_sp]
    ring
  constructor
  · rw [hneg_s_eq_sp]
    exact hpos_bounds.1
  · rw [hneg_s_eq_sp]
    exact hpos_bounds.2

/-- Opposite-sign inexact source split for the signed-ratio FastTwoSum route. -/
theorem FastTwoSumFiniteCertificate.signed_ratio_bounds_of_opposite_sign_abs_order_inexact
    (fmt : FloatingPointFormat) (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsign : (0 ≤ a ∧ b ≤ 0) ∨ (a ≤ 0 ∧ 0 ≤ b))
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    let s := fmt.finiteRoundToEvenOp BasicOp.add a b
    (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
  rcases hsign with hposneg | hnegpos
  · exact Or.inl
      (by
        simpa using
          FastTwoSumFiniteCertificate.signed_ratio_bounds_of_pos_neg_abs_order_inexact
            fmt hbeta ha hb hab habRange hposneg.1 hposneg.2 hinexact)
  · exact Or.inr
      (by
        simpa using
          FastTwoSumFiniteCertificate.signed_ratio_bounds_of_neg_pos_abs_order_inexact
            fmt hbeta ht ha hb hab habRange hnegpos.1 hnegpos.2 hinexact)

/-- Same-sign absolute ratio bounds imply the signed ratio-bound line-2 branch
for the finite FastTwoSum certificate.

This is a source-facing adapter: once the operand split proves that `a` and the
rounded first sum `s = fl(a+b)` have the same sign, ordinary absolute bounds
`|s| <= 2|a|` and `|a| <= 2|s|` are enough to reuse the signed-ratio
certificate field. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s|)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbounds' :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    simpa [s] using hbounds
  rcases hbounds' with ⟨hsign, hs_abs, ha_abs⟩
  have hsigned :
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s)) := by
    rcases hsign with hnonneg | hnonpos
    · rcases hnonneg with ⟨ha_nonneg, hs_nonneg⟩
      left
      constructor
      · simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using hs_abs
      · simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using ha_abs
    · rcases hnonpos with ⟨ha_nonpos, hs_nonpos⟩
      right
      constructor
      · simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using hs_abs
      · simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using ha_abs
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds
      fmt ha (by simpa [s] using hsigned)

/-- Same-sign interval control for the first rounded sum implies the absolute
ratio bounds needed for the finite FastTwoSum line-2 field.

For nonnegative inputs the interval is `a <= s <= a+b`; for nonpositive inputs
it is `a+b <= s <= a`.  The remaining proof work is to obtain that interval
fact from the concrete base-2 rounder. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_first_sum_interval
    (fmt : FloatingPointFormat) {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hinterval :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (0 ≤ a ∧ 0 ≤ b ∧ |b| < |a| ∧ a ≤ s ∧ s ≤ a + b) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ |b| < |a| ∧ a + b ≤ s ∧ s ≤ a)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hinterval' :
      (0 ≤ a ∧ 0 ≤ b ∧ |b| < |a| ∧ a ≤ s ∧ s ≤ a + b) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ |b| < |a| ∧ a + b ≤ s ∧ s ≤ a) := by
    simpa [s] using hinterval
  have hbounds :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    rcases hinterval' with hpos | hneg
    · rcases hpos with ⟨ha_nonneg, hb_nonneg, hab_abs, has, hsab⟩
      have hb_lt_a : b < a := by
        simpa [abs_of_nonneg hb_nonneg, abs_of_nonneg ha_nonneg] using hab_abs
      have hs_nonneg : 0 ≤ s := le_trans ha_nonneg has
      refine ⟨Or.inl ⟨ha_nonneg, hs_nonneg⟩, ?_, ?_⟩
      · have hs_le_two_a : s ≤ 2 * a := by
          linarith
        simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using hs_le_two_a
      · have ha_le_two_s : a ≤ 2 * s := by
          linarith
        simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using ha_le_two_s
    · rcases hneg with ⟨ha_nonpos, hb_nonpos, hab_abs, habs, hsa⟩
      have hneg_b_lt_neg_a : -b < -a := by
        simpa [abs_of_nonpos hb_nonpos, abs_of_nonpos ha_nonpos] using hab_abs
      have hs_nonpos : s ≤ 0 := le_trans hsa ha_nonpos
      refine ⟨Or.inr ⟨ha_nonpos, hs_nonpos⟩, ?_, ?_⟩
      · have hneg_s_le_two_neg_a : -s ≤ 2 * (-a) := by
          linarith
        simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using
          hneg_s_le_two_neg_a
      · have hneg_a_le_two_neg_s : -a ≤ 2 * (-s) := by
          linarith
        simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using
          hneg_a_le_two_neg_s
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha (by simpa [s] using hbounds)

/-- A small same-sign addend gives the absolute ratio bounds needed for the
finite FastTwoSum line-2 field.

This closes the easy same-sign branch: if the smaller same-sign operand has
magnitude at most one half of the larger operand, nearestness gives `s >= a`
and `s <= a + 2*b` in the nonnegative branch, hence `s <= 2*a`.  The
nonpositive branch follows by round-to-even oddness in base `2`. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_small_addend
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hsmall :
      (0 ≤ a ∧ 0 ≤ b ∧ b ≤ a / 2) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ -b ≤ (-a) / 2)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbeta_even : FloatingPointFormat.evenMantissa fmt.beta := by
    unfold FloatingPointFormat.evenMantissa
    omega
  have hbounds :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    rcases hsmall with hpos | hneg
    · rcases hpos with ⟨ha_nonneg, hb_nonneg, hb_half⟩
      have has : a ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            ha hb_nonneg
      have hs_le : s ≤ a + 2 * b := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg
            ha hb_nonneg
      have hs_nonneg : 0 ≤ s := le_trans ha_nonneg has
      refine ⟨Or.inl ⟨ha_nonneg, hs_nonneg⟩, ?_, ?_⟩
      · have hs_le_two_a : s ≤ 2 * a := by
          linarith
        simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using hs_le_two_a
      · have ha_le_two_s : a ≤ 2 * s := by
          linarith
        simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using ha_le_two_s
    · rcases hneg with ⟨ha_nonpos, hb_nonpos, hb_half⟩
      let sp := fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b)
      have hneg_a_fin : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_b_nonneg : 0 ≤ -b := by linarith
      have hsp_ge : -a ≤ sp := by
        simpa [sp] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            hneg_a_fin hneg_b_nonneg
      have hsp_le : sp ≤ -a + 2 * (-b) := by
        simpa [sp] using
          fmt.finiteRoundToEvenOp_add_le_left_add_two_mul_right_of_finiteSystem_of_nonneg
            hneg_a_fin hneg_b_nonneg
      have hsp_nonneg : 0 ≤ sp := le_trans (by linarith) hsp_ge
      have hs_eq_neg_sp : s = -sp := by
        dsimp [s, sp, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
        have hsum : a + b = -((-a) + (-b)) := by ring
        rw [hsum]
        simpa using
          fmt.finiteRoundToEven_neg hbeta_even ht ((-a) + (-b))
      have hs_nonpos : s ≤ 0 := by
        rw [hs_eq_neg_sp]
        linarith
      refine ⟨Or.inr ⟨ha_nonpos, hs_nonpos⟩, ?_, ?_⟩
      · have hneg_s_le_two_neg_a : -s ≤ 2 * (-a) := by
          rw [hs_eq_neg_sp]
          linarith
        simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using
          hneg_s_le_two_neg_a
      · have hneg_a_le_two_neg_s : -a ≤ 2 * (-s) := by
          rw [hs_eq_neg_sp]
          linarith
        simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using
          hneg_a_le_two_neg_s
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha (by simpa [s] using hbounds)

/-- Same-sign source operands satisfying `|b| < |a|` give the line-2
representability field for the finite FastTwoSum certificate.

For nonnegative operands, nearestness gives `a <= s`; an upper bound `s <= 2*a`
comes either from the finite candidate `2*a`, when it is in range, or from the
global finite-output bound when `2*a` is beyond the largest finite magnitude.
The nonpositive branch reduces to the nonnegative one by base-2 oddness of
round-to-even. -/
theorem FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_order
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a)
    (hab : |b| < |a|)
    (hsign : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :
    fmt.finiteSystem
      (a - fmt.finiteRoundToEvenOp BasicOp.add a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hbeta_even : FloatingPointFormat.evenMantissa fmt.beta := by
    unfold FloatingPointFormat.evenMantissa
    omega
  have hbounds :
      ((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s| := by
    rcases hsign with hpos | hneg
    · rcases hpos with ⟨ha_nonneg, hb_nonneg⟩
      have has : a ≤ s := by
        simpa [s] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            ha hb_nonneg
      have hb_le_a : b ≤ a := by
        have hlt : b < a := by
          simpa [abs_of_nonneg hb_nonneg, abs_of_nonneg ha_nonneg] using hab
        exact le_of_lt hlt
      have hs_nonneg : 0 ≤ s := le_trans ha_nonneg has
      have hs_le_two_a : s ≤ 2 * a := by
        by_cases htwo_le_max : 2 * a ≤ fmt.maxFiniteMagnitude
        · have htwo_nonneg : 0 ≤ 2 * a := by nlinarith
          have htwo_fin : fmt.finiteSystem (2 * a) :=
            fmt.finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude hbeta ha
              (by simpa [abs_of_nonneg htwo_nonneg] using htwo_le_max)
          have hsum_le : a + b ≤ 2 * a := by linarith
          simpa [s] using
            fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
              htwo_fin hsum_le
        · have hmax_lt : fmt.maxFiniteMagnitude < 2 * a :=
            lt_of_not_ge htwo_le_max
          have hs_abs_le :
              |s| ≤ fmt.maxFiniteMagnitude := by
            simpa [s] using
              fmt.finiteSystem_abs_le_maxFiniteMagnitude
                (fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add a b)
          have hs_le_max : s ≤ fmt.maxFiniteMagnitude := by
            simpa [abs_of_nonneg hs_nonneg] using hs_abs_le
          exact le_of_lt (lt_of_le_of_lt hs_le_max hmax_lt)
      refine ⟨Or.inl ⟨ha_nonneg, hs_nonneg⟩, ?_, ?_⟩
      · simpa [abs_of_nonneg hs_nonneg, abs_of_nonneg ha_nonneg] using
          hs_le_two_a
      · have ha_le_two_s : a ≤ 2 * s := by
          nlinarith
        simpa [abs_of_nonneg ha_nonneg, abs_of_nonneg hs_nonneg] using
          ha_le_two_s
    · rcases hneg with ⟨ha_nonpos, hb_nonpos⟩
      let sp := fmt.finiteRoundToEvenOp BasicOp.add (-a) (-b)
      have hneg_a_fin : fmt.finiteSystem (-a) := fmt.finiteSystem_neg ha
      have hneg_a_nonneg : 0 ≤ -a := by linarith
      have hneg_b_nonneg : 0 ≤ -b := by linarith
      have hneg_b_le_neg_a : -b ≤ -a := by
        have hlt : -b < -a := by
          simpa [abs_of_nonpos hb_nonpos, abs_of_nonpos ha_nonpos] using hab
        exact le_of_lt hlt
      have hsp_ge : -a ≤ sp := by
        simpa [sp] using
          fmt.finiteRoundToEvenOp_add_ge_left_of_finiteSystem_of_nonneg
            hneg_a_fin hneg_b_nonneg
      have hsp_nonneg : 0 ≤ sp := le_trans hneg_a_nonneg hsp_ge
      have hsp_le_two_neg_a : sp ≤ 2 * (-a) := by
        by_cases htwo_le_max : 2 * (-a) ≤ fmt.maxFiniteMagnitude
        · have htwo_nonneg : 0 ≤ 2 * (-a) := by nlinarith
          have htwo_abs_le : |2 * (-a)| ≤ fmt.maxFiniteMagnitude := by
            rw [abs_of_nonneg htwo_nonneg]
            exact htwo_le_max
          have htwo_fin : fmt.finiteSystem (2 * (-a)) :=
            fmt.finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude hbeta hneg_a_fin
              htwo_abs_le
          have hsum_le : (-a) + (-b) ≤ 2 * (-a) := by linarith
          simpa [sp] using
            fmt.finiteRoundToEvenOp_add_le_of_exact_le_finiteSystem
              htwo_fin hsum_le
        · have hmax_lt : fmt.maxFiniteMagnitude < 2 * (-a) :=
            lt_of_not_ge htwo_le_max
          have hsp_abs_le :
              |sp| ≤ fmt.maxFiniteMagnitude := by
            simpa [sp] using
              fmt.finiteSystem_abs_le_maxFiniteMagnitude
                (fmt.finiteRoundToEvenOp_finiteSystem BasicOp.add (-a) (-b))
          have hsp_le_max : sp ≤ fmt.maxFiniteMagnitude := by
            simpa [abs_of_nonneg hsp_nonneg] using hsp_abs_le
          exact le_of_lt (lt_of_le_of_lt hsp_le_max hmax_lt)
      have hs_eq_neg_sp : s = -sp := by
        dsimp [s, sp, FloatingPointFormat.finiteRoundToEvenOp, BasicOp.exact]
        have hsum : a + b = -((-a) + (-b)) := by ring
        rw [hsum]
        simpa using
          fmt.finiteRoundToEven_neg hbeta_even ht ((-a) + (-b))
      have hs_nonpos : s ≤ 0 := by
        rw [hs_eq_neg_sp]
        linarith
      refine ⟨Or.inr ⟨ha_nonpos, hs_nonpos⟩, ?_, ?_⟩
      · have hneg_s_le_two_neg_a : -s ≤ 2 * (-a) := by
          have hneg_s_eq_sp : -s = sp := by
            rw [hs_eq_neg_sp]
            ring
          simpa [hneg_s_eq_sp] using hsp_le_two_neg_a
        simpa [abs_of_nonpos hs_nonpos, abs_of_nonpos ha_nonpos] using
          hneg_s_le_two_neg_a
      · have hneg_a_le_two_neg_s : -a ≤ 2 * (-s) := by
          rw [hs_eq_neg_sp]
          nlinarith
        simpa [abs_of_nonpos ha_nonpos, abs_of_nonpos hs_nonpos] using
          hneg_a_le_two_neg_s
  exact
    FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha (by simpa [s] using hbounds)

/-- Base-2 absolute-order FastTwoSum certificate from the signed Sterbenz
line-2 branch.

This removes the old need for a second Sterbenz proof for `(a+b)-s`: the true
roundoff-error field is supplied by the base-2 rounded-add error theorem. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_sterbenz_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsub_sterbenz :
      fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz
      fmt ha hsub_sterbenz)

/-- Base-2 absolute-order FastTwoSum certificate from the strict Sterbenz or
endpoint-inclusive line-2 branch.

This is the certificate-level form of the corrected C4.4 route exposed by the
strict-Sterbenz endpoint counterexample: strict signed Sterbenz remains enough
away from the endpoints, while the two endpoint equalities close `a-s`
representability directly. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_sterbenz_or_endpoint_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsub :
      (fmt.sterbenzRatioCondition a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) ∨
        fmt.sterbenzRatioCondition (-a)
          (-(fmt.finiteRoundToEvenOp BasicOp.add a b))) ∨
      fmt.finiteRoundToEvenOp BasicOp.add a b = 2 * a ∨
      a = 2 * fmt.finiteRoundToEvenOp BasicOp.add a b) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_sterbenz_or_endpoint
      fmt ha hsub)

/-- Base-2 absolute-order FastTwoSum certificate from non-strict signed ratio
bounds on `a` and the rounded first sum.

The non-strict bounds are immediately split into strict signed Sterbenz or one
of the two endpoint equalities before reusing the closed base-2 rounded-add
error theorem. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_ratio_bounds_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (s ≤ 2 * a ∧ a ≤ 2 * s) ∨
      (-s ≤ 2 * (-a) ∧ -a ≤ 2 * (-s))) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_signed_ratio_bounds
      fmt ha hbounds)

/-- Base-2 absolute-order FastTwoSum certificate from same-sign absolute ratio
bounds on `a` and the rounded first sum.

This source-facing wrapper composes the same-sign absolute-ratio adapter with
the closed rounded-add error theorem. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_abs_ratio_bounds_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hbounds :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (((0 ≤ a ∧ 0 ≤ s) ∨ (a ≤ 0 ∧ s ≤ 0)) ∧
        |s| ≤ 2 * |a| ∧ |a| ≤ 2 * |s|)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_ratio_bounds
      fmt ha hbounds)

/-- Base-2 absolute-order FastTwoSum certificate from same-sign interval
control of the first rounded sum.

This packages a source-shaped route: once `s = fl(a+b)` is known to lie between
the larger same-sign operand `a` and the exact same-sign sum, the same-sign
absolute ratio-bound branch supplies the `a-s` certificate field. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_first_sum_interval_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hinterval :
      let s := fmt.finiteRoundToEvenOp BasicOp.add a b
      (0 ≤ a ∧ 0 ≤ b ∧ |b| < |a| ∧ a ≤ s ∧ s ≤ a + b) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ |b| < |a| ∧ a + b ≤ s ∧ s ≤ a)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_first_sum_interval
      fmt ha hinterval)

/-- Base-2 absolute-order FastTwoSum certificate for the easy same-sign
small-addend branch.

If the same-sign addend has magnitude at most one half of the larger operand,
the one-sided nearestness bounds give the signed ratio bounds for `a` and
`s = fl(a+b)`, while the closed rounded-add error theorem supplies the other
certificate field. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_small_addend_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsmall :
      (0 ≤ a ∧ 0 ≤ b ∧ b ≤ a / 2) ∨
      (a ≤ 0 ∧ b ≤ 0 ∧ -b ≤ (-a) / 2)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_small_addend
      fmt hbeta ht ha hsmall)

/-- Base-2 absolute-order FastTwoSum certificate for the full same-sign source
branch.

Under the source magnitude order `|b| < |a|`, same-sign operands already give
the ratio bounds for `a` and `s = fl(a+b)` needed by the line-2 certificate
field; the closed rounded-add error theorem supplies the other field. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsign : (0 ≤ a ∧ 0 ≤ b) ∨ (a ≤ 0 ∧ b ≤ 0)) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_finite_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.finite_a_sub_s_of_same_sign_abs_order
      fmt hbeta ht ha hab hsign)

/-- Base-2 absolute-order FastTwoSum certificate for the inexact
opposite-sign branch.

The near-magnitude exact-add branch has already been ruled out by the inexact
first sum, so the remaining opposite-sign case supplies the signed ratio bounds
needed for `a-s` representability. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hsign : (0 ≤ a ∧ b ≤ 0) ∨ (a ≤ 0 ∧ 0 ≤ b))
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    FastTwoSumFiniteCertificate fmt a b :=
  FastTwoSumFiniteCertificate.of_base2_abs_order_of_signed_ratio_bounds_a_sub_s
    fmt hbeta ht ha hb hab habRange
    (FastTwoSumFiniteCertificate.signed_ratio_bounds_of_opposite_sign_abs_order_inexact
      fmt hbeta ht ha hb hab habRange hsign hinexact)

/-- Base-2 absolute-order FastTwoSum certificate for an inexact first add.

This closes the remaining all-sign inexact branch of the correction formula:
same-sign operands use the closed same-sign source theorem, and opposite-sign
operands use the far-magnitude signed-ratio split after the near-magnitude
exact branch is excluded by `hinexact`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b))
    (hinexact : fmt.finiteRoundToEvenOp BasicOp.add a b ≠ a + b) :
    FastTwoSumFiniteCertificate fmt a b := by
  by_cases ha_nonneg : 0 ≤ a
  · by_cases hb_nonneg : 0 ≤ b
    · exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inl ⟨ha_nonneg, hb_nonneg⟩)
    · have hb_nonpos : b ≤ 0 := le_of_not_ge hb_nonneg
      exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inl ⟨ha_nonneg, hb_nonpos⟩) hinexact
  · have ha_nonpos : a ≤ 0 := le_of_not_ge ha_nonneg
    by_cases hb_nonpos : b ≤ 0
    · exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_same_sign_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inr ⟨ha_nonpos, hb_nonpos⟩)
    · have hb_nonneg : 0 ≤ b := le_of_not_ge hb_nonpos
      exact
        FastTwoSumFiniteCertificate.of_base2_abs_order_of_opposite_sign_inexact_a_sub_s
          fmt hbeta ht ha hb hab habRange
          (Or.inr ⟨ha_nonpos, hb_nonneg⟩) hinexact

/-- Base-2 absolute-order FastTwoSum finite certificate.

This is the finite-format certificate form of Higham equation (4.7)'s binary
correction-formula exactness route: the exact-first-add branch uses
`FastTwoSumFiniteCertificate.of_exact_add`, while the inexact branch uses
`FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    FastTwoSumFiniteCertificate fmt a b := by
  by_cases hadd : fmt.finiteRoundToEvenOp BasicOp.add a b = a + b
  · exact FastTwoSumFiniteCertificate.of_exact_add fmt a b hb hadd
  · exact
      FastTwoSumFiniteCertificate.of_base2_abs_gt_of_inexact_add
        fmt hbeta ht ha hb hab habRange hadd

/-- Base-2 FastTwoSum certificate with Higham's non-strict order
`|b| ≤ |a|`.  Equal magnitudes force `b = a` or `b = -a`, so the first
addition is exact (`2a` or `0`) when overflow is excluded by `habRange`. -/
theorem FastTwoSumFiniteCertificate.of_base2_abs_le
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| ≤ |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    FastTwoSumFiniteCertificate fmt a b := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · exact FastTwoSumFiniteCertificate.of_base2_abs_gt
      fmt hbeta ht ha hb hlt habRange
  · rcases abs_eq_abs.mp heq with hba | hba
    · subst b
      have hfin : fmt.finiteSystem (a + a) := by
        have htwo := fmt.finiteSystem_two_mul_of_abs_le_maxFiniteMagnitude
          hbeta ha (by simpa [two_mul] using habRange.2)
        simpa [two_mul] using htwo
      have hadd :
          fmt.finiteRoundToEvenOp BasicOp.add a a = a + a := by
        simpa [BasicOp.exact] using
          fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add) (x := a) (y := a) hfin
      exact FastTwoSumFiniteCertificate.of_exact_add fmt a a ha hadd
    · subst b
      have hfin : fmt.finiteSystem (a + -a) := by
        simpa using fmt.finiteSystem_zero
      have hadd :
          fmt.finiteRoundToEvenOp BasicOp.add a (-a) = a + -a := by
        simpa [BasicOp.exact] using
          fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
            (op := BasicOp.add) (x := a) (y := -a) hfin
      exact FastTwoSumFiniteCertificate.of_exact_add fmt a (-a)
        (fmt.finiteSystem_neg ha) hadd

/-- If the finite FastTwoSum certificate supplies representability of the
intermediate subtraction and the true local error, then Higham equation
(4.7)'s exactness conclusion follows for the finite round-to-even trace. -/
theorem finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hcert : FastTwoSumFiniteCertificate fmt a b) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) := by
  let s := fmt.finiteRoundToEvenOp BasicOp.add a b
  have hsub :
      fmt.finiteRoundToEvenOp BasicOp.sub a
          (fmt.finiteRoundToEvenOp BasicOp.add a b) =
        a - fmt.finiteRoundToEvenOp BasicOp.add a b := by
    have hsub_finite :
        fmt.finiteSystem
          (BasicOp.exact BasicOp.sub a
            (fmt.finiteRoundToEvenOp BasicOp.add a b)) := by
      simpa [BasicOp.exact, s] using hcert.finite_a_sub_s
    simpa [BasicOp.exact] using
      (fmt.finiteRoundToEvenOp_eq_exact_of_finiteSystem
        (op := BasicOp.sub) (x := a)
        (y := fmt.finiteRoundToEvenOp BasicOp.add a b) hsub_finite)
  have hadd :
      fmt.finiteSystem
        ((a - fmt.finiteRoundToEvenOp BasicOp.add a b) + b) := by
    have hrewrite :
        (a - s) + b = (a + b) - s := by ring
    simpa [s, hrewrite] using hcert.finite_error
  exact finiteCorrectionFormulaTrace_exact_of_exact_sub_and_finite_error_add
    fmt a b hsub hadd

/-- Exact-first-add branch of Higham equation (4.7)'s finite round-to-even
correction formula.

When `s = fl(a+b)` is already the exact real sum and `b` is finite
representable, the displayed correction formula recovers the local error
exactly. -/
theorem finiteCorrectionFormulaTrace_exact_of_exact_add
    (fmt : FloatingPointFormat) (a b : ℝ)
    (hb : fmt.finiteSystem b)
    (hadd :
      fmt.finiteRoundToEvenOp BasicOp.add a b = a + b) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) :=
  finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate fmt a b
    (FastTwoSumFiniteCertificate.of_exact_add fmt a b hb hadd)

/-- Higham equation (4.7) for the concrete finite binary round-to-even
correction-formula trace. -/
theorem finiteCorrectionFormulaTrace_exact_of_base2_abs_gt
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| < |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) :=
  finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate
    fmt a b
    (FastTwoSumFiniteCertificate.of_base2_abs_gt
      fmt hbeta ht ha hb hab habRange)

/-- Higham equation (4.7) with the source's non-strict magnitude hypothesis
`|a| ≥ |b|`.

The strict branch is `finiteCorrectionFormulaTrace_exact_of_base2_abs_gt`.
When the magnitudes tie, `b = a` or `b = -a`: the first sum is respectively
`2a` or `0`, hence is exactly representable (the normal-range hypothesis rules
out overflow in the doubling branch), and the exact-add certificate closes the
displayed correction trace.  This packages the equality case that was formerly
only documented as an informal side branch. -/
theorem finiteCorrectionFormulaTrace_exact_of_base2_abs_le
    (fmt : FloatingPointFormat)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    {a b : ℝ}
    (ha : fmt.finiteSystem a) (hb : fmt.finiteSystem b)
    (hab : |b| ≤ |a|)
    (habRange : fmt.finiteNormalRange (a + b)) :
    CorrectionFormulaTrace.exact a b
      (finiteCorrectionFormulaTrace fmt a b) :=
  finiteCorrectionFormulaTrace_exact_of_fastTwoSumFiniteCertificate fmt a b
    (FastTwoSumFiniteCertificate.of_base2_abs_le
      fmt hbeta ht ha hb hab habRange)

end NumStability
