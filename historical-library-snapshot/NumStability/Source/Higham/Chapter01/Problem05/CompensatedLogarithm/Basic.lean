import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.Error.Measures.ScalarDefinitions
import NumStability.Analysis.Error.Measures.ScalarWitnesses
import NumStability.Analysis.FloatingPointArithmetic.Format
import NumStability.Analysis.FloatingPointArithmetic.NearestRoundingError
import NumStability.Analysis.Rounding

/-!
# Chapter01 Problem05 CompensatedLogarithm Basic

Canonical destination for material split out of
`NumStability.Analysis.Accumulation` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped Topology

namespace NumStability

/-- Higham Problem 1.5 / Appendix A formula (A.1), interpreted in exact real
arithmetic.  The branch at `w = 1` removes the apparent singularity of
`x * log(w) / (w - 1)` when `w = 1 + x`. -/
noncomputable def logOnePlusCompensatedExact (x : ℝ) : ℝ :=
  let w : ℝ := 1 + x
  if w = 1 then x else x * Real.log w / (w - 1)

/-- The compensated formula returns zero at the removable singularity. -/
theorem logOnePlusCompensatedExact_zero :
    logOnePlusCompensatedExact 0 = 0 := by
  simp [logOnePlusCompensatedExact]

/-- Exact source identity for Problem 1.5's compensated logarithm formula:
with exact arithmetic, formula (A.1) computes `log(1+x)`. -/
theorem logOnePlusCompensatedExact_eq_log_one_add (x : ℝ) :
    logOnePlusCompensatedExact x = Real.log (1 + x) := by
  unfold logOnePlusCompensatedExact
  by_cases h : 1 + x = 1
  · have hx : x = 0 := by linarith
    simp [hx]
  · have hx : x ≠ 0 := by
      intro hx
      apply h
      simp [hx]
    simp [h]
    field_simp [hx]

/-- Nonbranch perturbation surface for Problem 1.5's compensated logarithm:
`wHat` is the supplied value of `1+x`, `epsLog` models the relative error in
`log wHat`, and `epsMul`/`epsDiv` model the final multiply/divide roundings. -/
noncomputable def logOnePlusCompensatedPerturbedNonbranch
    (x wHat epsLog epsMul epsDiv : ℝ) : ℝ :=
  ((x * (Real.log wHat * (1 + epsLog))) * (1 + epsMul) /
      (wHat - 1)) * (1 + epsDiv)

/-- If the addition forming `w = 1+x` is exact in the nonzero branch, the
Problem 1.5 compensated logarithm has exactly the displayed product of
relative-error factors. -/
theorem logOnePlusCompensatedPerturbedNonbranch_exact_w_signedRelErrorWitness
    {x epsLog epsMul epsDiv : ℝ} (hx : x ≠ 0) :
    signedRelErrorWitness
      (logOnePlusCompensatedPerturbedNonbranch x (1 + x) epsLog epsMul epsDiv)
      (Real.log (1 + x))
      ((1 + epsLog) * (1 + epsMul) * (1 + epsDiv) - 1) := by
  unfold signedRelErrorWitness logOnePlusCompensatedPerturbedNonbranch
  field_simp [hx]
  ring

/-- Relative-error form of the nonzero exact-`w` branch of Problem 1.5's
compensated logarithm formula. -/
theorem logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_eq
    {x epsLog epsMul epsDiv : ℝ}
    (hx : x ≠ 0) (hlog : relErrorDefined (Real.log (1 + x))) :
    relError
        (logOnePlusCompensatedPerturbedNonbranch x (1 + x) epsLog epsMul epsDiv)
        (Real.log (1 + x)) =
      |(1 + epsLog) * (1 + epsMul) * (1 + epsDiv) - 1| :=
  relError_eq_abs_of_signedRelErrorWitness hlog
    (logOnePlusCompensatedPerturbedNonbranch_exact_w_signedRelErrorWitness
      (x := x) (epsLog := epsLog) (epsMul := epsMul) (epsDiv := epsDiv) hx)

/-- Bound form of the nonzero exact-`w` branch of Problem 1.5's compensated
logarithm formula.  The caller supplies whatever gamma/theta calculus is
appropriate for the three visible relative-error factors. -/
theorem logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_le
    {x epsLog epsMul epsDiv eps : ℝ}
    (hx : x ≠ 0) (hlog : relErrorDefined (Real.log (1 + x)))
    (hfactor :
      |(1 + epsLog) * (1 + epsMul) * (1 + epsDiv) - 1| ≤ eps) :
    relError
        (logOnePlusCompensatedPerturbedNonbranch x (1 + x) epsLog epsMul epsDiv)
        (Real.log (1 + x)) ≤ eps := by
  rw [logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_eq hx hlog]
  exact hfactor

end NumStability
