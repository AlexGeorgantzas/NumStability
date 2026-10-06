/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter23.Theorem02.ErrorRelations
import NumStability.Source.Higham.Chapter23.Theorem02.Execution
import NumStability.Source.Higham.Chapter23.ThreeM

namespace NumStability

open scoped Topology
open Filter

/-!
# Higham Chapter 23: combined 3M--Strassen execution

The literal combined complex evaluator and its scalar exact-majorant components.
-/

abbrev Higham23RecursiveComplex (r depth : ℕ) :=
  Higham23RecursiveMatrix r depth × Higham23RecursiveMatrix r depth

/-- Exact complex multiplication, written in the three-multiplication form. -/
noncomputable def higham23ThreeMExactRecursive (r depth : ℕ)
    (A B : Higham23RecursiveComplex r depth) : Higham23RecursiveComplex r depth :=
  higham23ThreeM A.1 A.2 B.1 B.2

/-- Literal 3M implementation whose three real products are actual recursive
Strassen calls. -/
noncomputable def higham23FlThreeMStrassen (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveComplex r depth) : Higham23RecursiveComplex r depth :=
  let As := higham23RecursiveFlAdd fp r depth A.1 A.2
  let Bs := higham23RecursiveFlAdd fp r depth B.1 B.2
  let P1 := higham23FlStrassenRecursive fp r depth A.1 B.1
  let P2 := higham23FlStrassenRecursive fp r depth A.2 B.2
  let P3 := higham23FlStrassenRecursive fp r depth As Bs
  (higham23RecursiveFlSub fp r depth P1 P2,
    higham23RecursiveFlSub fp r depth
      (higham23RecursiveFlSub fp r depth P3 P1) P2)

def Higham23RecursiveComplexErrorLe (r depth : ℕ)
    (X Y : Higham23RecursiveComplex r depth) (re im : ℝ) : Prop :=
  Higham23RecursiveErrorLe r depth X.1 Y.1 re ∧
    Higham23RecursiveErrorLe r depth X.2 Y.2 im

/-- Leafwise rounded addition can use a direct bound on the exact sum.  This
is the form needed for `|A₁|+|A₂| ≤ √2 |A₁+iA₂|`. -/
theorem higham23_recursiveFlAdd_error_of_sum_norm
    (fp : FPModel) (r : ℕ) :
    ∀ depth (A B : Higham23RecursiveMatrix r depth) (s : ℝ),
      0 ≤ s → Higham23RecursiveMaxNormLe r depth (A + B) s →
      Higham23RecursiveErrorLe r depth (A + B)
        (higham23RecursiveFlAdd fp r depth A B) (fp.u * s)
  | 0, A, B, s, hs, hSum => by
      intro i j
      obtain ⟨δ, hδ, hfl⟩ := fp.model_add (A i j) (B i j)
      change |A i j + B i j - fp.fl_add (A i j) (B i j)| ≤ fp.u * s
      rw [hfl, show A i j + B i j - (A i j + B i j) * (1 + δ) =
        -(A i j + B i j) * δ by ring, abs_mul, abs_neg]
      calc
        |A i j + B i j| * |δ| ≤ s * fp.u :=
          mul_le_mul (hSum i j) hδ (abs_nonneg _) hs
        _ = fp.u * s := by ring
  | depth + 1, A, B, s, hs, hSum => by
      rcases hSum with ⟨h11, h12, h21, h22⟩
      exact ⟨higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h11,
        higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h12,
        higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h21,
        higham23_recursiveFlAdd_error_of_sum_norm fp r depth _ _ s hs h22⟩

theorem higham23_recursiveFlAdd_norm_of_sum_norm
    (fp : FPModel) (r depth : ℕ)
    (A B : Higham23RecursiveMatrix r depth) (s : ℝ) (hs : 0 ≤ s)
    (hSum : Higham23RecursiveMaxNormLe r depth (A + B) s) :
    Higham23RecursiveMaxNormLe r depth
      (higham23RecursiveFlAdd fp r depth A B) ((1 + fp.u) * s) := by
  have hErr := higham23_recursiveFlAdd_error_of_sum_norm fp r depth A B s hs hSum
  have hNorm := higham23_recursiveMaxNormLe_of_error r depth _ _ hSum hErr
  convert hNorm using 1 <;> ring

noncomputable def higham23ThreeMStrassenP3Error (n e u : ℝ) : ℝ :=
  2 * (n * u + n * u * (1 + u) + e * (1 + u) ^ 2)

noncomputable def higham23ThreeMStrassenP1Norm (n e : ℝ) : ℝ := n + e

noncomputable def higham23ThreeMStrassenP3Norm (n e u : ℝ) : ℝ :=
  2 * (n + e) * (1 + u) ^ 2

noncomputable def higham23ThreeMStrassenRealMajorant (n e u : ℝ) : ℝ :=
  2 * e + 2 * u * higham23ThreeMStrassenP1Norm n e

noncomputable def higham23ThreeMStrassenImagMajorant (n e u : ℝ) : ℝ :=
  let n1 := higham23ThreeMStrassenP1Norm n e
  let n3 := higham23ThreeMStrassenP3Norm n e u
  higham23ThreeMStrassenP3Error n e u + 2 * e +
    u * (n3 + n1) + u * ((1 + u) * (n3 + n1) + n1)

end NumStability
