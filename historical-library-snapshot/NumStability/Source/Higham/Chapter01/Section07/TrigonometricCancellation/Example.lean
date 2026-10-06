import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Source.Higham.Chapter01.Problem03.CancellationRewrites.Algebra

-- Analysis/TrigCancellation.lean
--
-- Exact trigonometric cancellation algebra for Higham Chapter 1, Section 1.7.










namespace NumStability

/-!
# Trigonometric Cancellation Algebra

Higham Chapter 1, Section 1.7 uses `1 - cos x` to illustrate cancellation and
the stable exact rewrite `2 * sin (x/2)^2`.  This file records the exact
real-arithmetic identity, the supplied-error comparison of the two evaluation
paths, and finite round-to-even wrappers for the trigonometric outputs under
finite-normal hypotheses.  It also records the exact cancellation-avoiding
rewrites from Problem 1.3.
-/














-- ============================================================
-- Higham §1.7 scaled target and cancellation-amplification bounds
-- ============================================================



























































































































































-- ============================================================
-- Higham §1.7 finite round-to-even trigonometric routine wrappers
-- ============================================================







































































































































-- ============================================================
-- Higham Problem 1.3 cancellation-avoiding rewrites
-- ============================================================


































































-- ============================================================
-- Higham §1.7 displayed ten-significant-figure example
-- ============================================================





/-- The displayed ten-significant-figure cosine approximation
`c = 0.9999999999`. -/
noncomputable def trigCancellationExampleCos10 : ℝ :=
  (9999999999 : ℝ) / 10000000000

/-- The displayed ten-significant-figure sine-half approximation
`sin(x/2) ≈ 0.0000060000`. -/
noncomputable def trigCancellationExampleSinHalf10 : ℝ :=
  (6 : ℝ) / 1000000

/-- The direct cancellation path `(1 - c) / x^2` for the displayed decimal data. -/
noncomputable def trigCancellationDirectScaled : ℝ :=
  (1 - trigCancellationExampleCos10) / trigCancellationExampleX ^ 2

/-- The rewritten path `2*s^2 / x^2` for the displayed decimal data. -/
noncomputable def trigCancellationRewriteScaled : ℝ :=
  2 * trigCancellationExampleSinHalf10 ^ 2 / trigCancellationExampleX ^ 2

/-- In the displayed example, the direct formula gives `25/36 = 0.6944...`. -/
theorem trigCancellationDirectScaled_eq :
    trigCancellationDirectScaled = (25 : ℝ) / 36 := by
  norm_num [trigCancellationDirectScaled, trigCancellationExampleCos10,
    trigCancellationExampleX]

/-- The displayed direct result is not the correct limiting value `1/2`. -/
theorem trigCancellationDirectScaled_ne_half :
    trigCancellationDirectScaled ≠ (1 : ℝ) / 2 := by
  rw [trigCancellationDirectScaled_eq]
  norm_num

/-- In the displayed example, the rewritten sine-half formula gives `1/2`. -/
theorem trigCancellationRewriteScaled_eq_half :
    trigCancellationRewriteScaled = (1 : ℝ) / 2 := by
  norm_num [trigCancellationRewriteScaled, trigCancellationExampleSinHalf10,
    trigCancellationExampleX]

end NumStability
