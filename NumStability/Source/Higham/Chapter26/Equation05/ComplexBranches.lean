/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

namespace NumStability

/-! # Higham Chapter 26, Equation 26.5: Complex Branches

Algebraic complex square roots and the complex plus and minus branches of equation (26.5).
-/

/-! ### Complex form of Cardano's branches -/

/-- A choice of square root in the algebraically closed field of complex
numbers.  Unlike `Real.sqrt`, this is defined for every radicand. -/
noncomputable def algebraicComplexSqrt (z : Complex) : Complex :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 2))

theorem algebraicComplexSqrt_sq (z : Complex) :
    algebraicComplexSqrt z ^ 2 = z :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq z (by norm_num : 0 < 2))

/-- The radicand in (26.5), now coerced to the source's complex root domain. -/
noncomputable def cubicRadicandComplex (p q : Real) : Complex :=
  (q : Complex) ^ 2 / 4 + (p : Complex) ^ 3 / 27

noncomputable def cubicWCubePlusComplex (p q : Real) : Complex :=
  -(q : Complex) / 2 + algebraicComplexSqrt (cubicRadicandComplex p q)

noncomputable def cubicWCubeMinusComplex (p q : Real) : Complex :=
  -(q : Complex) / 2 - algebraicComplexSqrt (cubicRadicandComplex p q)

/-- Both signs in (26.5) solve the quadratic for `w^3` for every real `p,q`,
including the negative-radicand case omitted by the real-only implementation. -/
theorem cubicWCubePlusComplex_quadratic (p q : Real) :
    cubicWCubePlusComplex p q ^ 2 + (q : Complex) * cubicWCubePlusComplex p q -
        (p : Complex) ^ 3 / 27 = 0 := by
  have hs := algebraicComplexSqrt_sq (cubicRadicandComplex p q)
  calc
    cubicWCubePlusComplex p q ^ 2 +
          (q : Complex) * cubicWCubePlusComplex p q -
          (p : Complex) ^ 3 / 27 =
        algebraicComplexSqrt (cubicRadicandComplex p q) ^ 2 -
          cubicRadicandComplex p q := by
            unfold cubicWCubePlusComplex cubicRadicandComplex
            ring
    _ = 0 := by rw [hs]; ring

theorem cubicWCubeMinusComplex_quadratic (p q : Real) :
    cubicWCubeMinusComplex p q ^ 2 + (q : Complex) * cubicWCubeMinusComplex p q -
        (p : Complex) ^ 3 / 27 = 0 := by
  have hs := algebraicComplexSqrt_sq (cubicRadicandComplex p q)
  calc
    cubicWCubeMinusComplex p q ^ 2 +
          (q : Complex) * cubicWCubeMinusComplex p q -
          (p : Complex) ^ 3 / 27 =
        algebraicComplexSqrt (cubicRadicandComplex p q) ^ 2 -
          cubicRadicandComplex p q := by
            unfold cubicWCubeMinusComplex cubicRadicandComplex
            ring
    _ = 0 := by rw [hs]; ring

end NumStability
