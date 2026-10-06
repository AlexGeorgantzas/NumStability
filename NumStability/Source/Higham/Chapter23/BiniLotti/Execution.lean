/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.BilinearAlgorithm
import NumStability.Source.Higham.Chapter23.BiniLotti.RecursiveAlgebra
import NumStability.Source.Higham.Chapter23.Equation11

namespace NumStability

open scoped Topology BigOperators
open Filter

/-!
# Higham Chapter 23: Bini--Lotti execution

The literal recursive evaluator and exact majorant recurrence for the Bini--Lotti bilinear algorithm.
-/

def higham23BiniFlattenBlock {h depth : ℕ}
    (A : Higham23BiniMatrix h (depth + 1)) (q : Fin (h * h)) :
    Higham23BiniMatrix h depth :=
  A (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

noncomputable def higham23BiniExactLevel {h t depth : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Higham23BiniMatrix h (depth + 1)) :
    Higham23BiniMatrix h (depth + 1) :=
  fun i j ↦ higham23BiniExactDot h t depth (alg.W i j) (fun k ↦
    higham23BiniMul h depth
      (higham23BiniExactDot h (h * h) depth (higham23MillerFlattenU alg k)
        (higham23BiniFlattenBlock A))
      (higham23BiniExactDot h (h * h) depth (higham23MillerFlattenV alg k)
        (higham23BiniFlattenBlock B)))

/-- The noncommutative correctness condition required by Theorem 23.4.  It
is solely an exact tensor identity; no numerical-error conclusion is assumed. -/
def Higham23BilinearAlgorithm.IsNoncommutativeCorrect {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) : Prop :=
  ∀ depth (A B : Higham23BiniMatrix h (depth + 1)),
    higham23BiniExactLevel alg A B = higham23BiniMul h (depth + 1) A B

noncomputable def higham23BiniFlEvaluate
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) :
    ∀ depth, Higham23BiniMatrix h depth → Higham23BiniMatrix h depth →
      Higham23BiniMatrix h depth
  | 0, A, B => fp.fl_mul A B
  | depth + 1, A, B =>
      let Xhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenU alg k)
          (higham23BiniFlattenBlock A)
      let Yhat := fun k : Fin t ↦
        higham23BiniFlDot fp h (h * h) depth (higham23MillerFlattenV alg k)
          (higham23BiniFlattenBlock B)
      let P := fun k : Fin t ↦
        higham23BiniFlEvaluate fp alg depth (Xhat k) (Yhat k)
      fun i j ↦ higham23BiniFlDot fp h t depth (alg.W i j) P

noncomputable def higham23BiniProductErrorCore (N e g : ℝ) : ℝ :=
  N * g + N * (1 + g) * g + e * (1 + g) ^ 2

noncomputable def higham23BiniProductNormCore (N e g : ℝ) : ℝ :=
  (N + e) * (1 + g) ^ 2

noncomputable def higham23BiniStepMajorant
    (K N e g gt : ℝ) : ℝ :=
  K * (higham23BiniProductErrorCore N e g +
    gt * higham23BiniProductNormCore N e g)

noncomputable def higham23BiniExactMajorant
    (fp : FPModel) {h t : ℕ} (alg : Higham23BilinearAlgorithm h t) : ℕ → ℝ
  | 0 => fp.u
  | depth + 1 =>
      higham23BiniStepMajorant (higham23MillerWeightTotal alg)
        ((h ^ depth : ℕ) : ℝ) (higham23BiniExactMajorant fp alg depth)
        (gamma fp (h * h)) (gamma fp t)

end NumStability
