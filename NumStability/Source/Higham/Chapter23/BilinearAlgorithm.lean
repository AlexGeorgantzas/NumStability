/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Analysis.Norms

namespace NumStability

open scoped BigOperators Topology
open Filter

/-!
# Higham Chapter 23: Bilinear algorithms

The abstract bilinear multiplication algorithm of equations (23.7a)--(23.7b).
-/

section BilinearAlgorithm

/-- Equations (23.7a)--(23.7b): exact data of a bilinear noncommutative
algorithm.  The scalar coefficient ring is kept separate from the block ring;
the external Bini--Lotti stability constants are not invented here. -/
structure Higham23BilinearAlgorithm (h t : ℕ) where
  U : Fin t → Fin h → Fin h → ℝ
  V : Fin t → Fin h → Fin h → ℝ
  W : Fin h → Fin h → Fin t → ℝ

/-- Equation (23.7b): the `k`th nonscalar product formed from the two
coefficient-weighted input matrices. -/
noncomputable def higham23BilinearProduct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) : ℝ :=
  (∑ i : Fin h, ∑ j : Fin h, alg.U k i j * A i j) *
    (∑ i : Fin h, ∑ j : Fin h, alg.V k i j * B i j)

/-- Equation (23.7a): reconstruct every output entry from the `t` products. -/
noncomputable def higham23BilinearEvaluate {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) : Matrix (Fin h) (Fin h) ℝ :=
  fun i j ↦ ∑ k : Fin t, alg.W i j k * higham23BilinearProduct alg A B k

/-- The source phrase "algorithm for multiplying" means that the fixed tensor
data reconstruct matrix multiplication for every pair of inputs. -/
def Higham23BilinearAlgorithm.IsCorrect {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) : Prop :=
  ∀ A B : Matrix (Fin h) (Fin h) ℝ,
    higham23BilinearEvaluate alg A B = A * B

/-- Equation (23.7b) is the executable product formula, exposed separately for
source-facing use. -/
theorem higham23_eq23_7b {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (k : Fin t) :
    higham23BilinearProduct alg A B k =
      (∑ i : Fin h, ∑ j : Fin h, alg.U k i j * A i j) *
        (∑ i : Fin h, ∑ j : Fin h, alg.V k i j * B i j) := rfl

/-- Equation (23.7a), entrywise. -/
theorem higham23_eq23_7a {h t : ℕ} (alg : Higham23BilinearAlgorithm h t)
    (A B : Matrix (Fin h) (Fin h) ℝ) (i j : Fin h) :
    higham23BilinearEvaluate alg A B i j =
      ∑ k : Fin t, alg.W i j k * higham23BilinearProduct alg A B k := rfl

/-- One-level exact reconstruction for tensors satisfying the defining
correctness condition of a bilinear multiplication algorithm. -/
theorem higham23_bilinearEvaluate_correct {h t : ℕ}
    (alg : Higham23BilinearAlgorithm h t) (halg : alg.IsCorrect)
    (A B : Matrix (Fin h) (Fin h) ℝ) :
    higham23BilinearEvaluate alg A B = A * B :=
  halg A B

/-! Miller's (23.11) and Bini--Lotti's Theorem 23.4 are cited results whose
rounded arithmetic graphs are not supplied in Chapter 23.  This foundation
does not manufacture target-bearing witnesses; the literal rounded circuits
and their error inductions are provided downstream in `Higham23Remaining`
and `Higham23Bini`. -/

end BilinearAlgorithm

end NumStability
