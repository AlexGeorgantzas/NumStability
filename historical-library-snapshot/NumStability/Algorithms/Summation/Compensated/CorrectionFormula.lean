import NumStability.FloatingPoint.Model

namespace NumStability

/-!
# Local correction-formula trace

Reusable source-level data and identities for the rounded two-operation
correction formula used by FastTwoSum, Kahan summation, and related
compensated algorithms.
-/

/-! ## Error-correction formula trace -/

/-- Source-level trace for Higham equation (4.7)'s local correction formula:
`s = fl(a + b)` and `e = fl((a - s) + b)`. -/
structure CorrectionFormulaTrace where
  s : ℝ
  e : ℝ

/-- Predicate for the exactness conclusion of Higham equation (4.7).  The
finite base-2 theorem proving this predicate under the source assumptions is
tracked separately in the Chapter 4 ledger. -/
def CorrectionFormulaTrace.exact (a b : ℝ) (t : CorrectionFormulaTrace) : Prop :=
  a + b = t.s + t.e

/-- The rounded local correction-formula trace. -/
noncomputable def correctionFormulaTrace
    (fp : FPModel) (a b : ℝ) : CorrectionFormulaTrace :=
  let s := fp.fl_add a b
  let e := fp.fl_add (fp.fl_sub a s) b
  { s := s, e := e }

/-- The `s = fl(a + b)` assignment in the correction formula. -/
theorem correctionFormulaTrace_s (fp : FPModel) (a b : ℝ) :
    (correctionFormulaTrace fp a b).s = fp.fl_add a b := by
  rfl

/-- The `e = fl((a - s) + b)` assignment in the correction formula, in the
displayed evaluation order. -/
theorem correctionFormulaTrace_e (fp : FPModel) (a b : ℝ) :
    (correctionFormulaTrace fp a b).e =
      fp.fl_add (fp.fl_sub a (correctionFormulaTrace fp a b).s) b := by
  rfl

end NumStability
