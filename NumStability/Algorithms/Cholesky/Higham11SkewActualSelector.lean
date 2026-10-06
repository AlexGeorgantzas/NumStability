/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Higham Algorithm 11.9: actual skew-pivot argmax and permutation

This module replaces the scalar-only `SkewBunchPivotChoice` interface by a
finite matrix selector.  It chooses the printed pair `(p,q)`, proves the
argmax property, and constructs the symmetric row/column permutation that
moves `q` and `p` to the first two positions.
-/

import NumStability.Algorithms.HighamChapter11

namespace NumStability

/-- Eligible score for the pair `(q,p)` in Algorithm 11.9.  The source scans
column zero below the diagonal and column one strictly below its diagonal. -/
noncomputable def higham11_9_skewPairScore {n : ℕ}
    (A : Fin n → Fin n → ℝ) (qp : Fin n × Fin n) : ℝ :=
  if qp.1.val < 2 ∧ qp.1.val < qp.2.val then |A qp.2 qp.1| else 0

/-- The deterministic finite argmax pair `(q,p)` for Algorithm 11.9. -/
noncomputable def higham11_9_skewPairArgmax {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : Fin n × Fin n :=
  (Finset.exists_max_image Finset.univ (higham11_9_skewPairScore A)
    ⟨(⟨0, lt_of_lt_of_le (by omega) hn2⟩,
       ⟨1, lt_of_lt_of_le (by omega) hn2⟩), Finset.mem_univ _⟩).choose

/-- The selected lower index `q`. -/
noncomputable def higham11_9_skewPivotQ {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : Fin n :=
  (higham11_9_skewPairArgmax hn2 A).1

/-- The selected upper index `p`. -/
noncomputable def higham11_9_skewPivotP {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : Fin n :=
  (higham11_9_skewPairArgmax hn2 A).2

/-- Magnitude of the selected skew pivot. -/
noncomputable def higham11_9_skewPivotMagnitude {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  higham11_9_skewPairScore A (higham11_9_skewPairArgmax hn2 A)

/-- The chosen pair dominates every eligible entry in the two printed
columns. -/
theorem higham11_9_skewPairArgmax_spec {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) (q p : Fin n) :
    higham11_9_skewPairScore A (q, p) ≤
      higham11_9_skewPivotMagnitude hn2 A := by
  exact ((Finset.exists_max_image Finset.univ
    (higham11_9_skewPairScore A)
    ⟨(⟨0, lt_of_lt_of_le (by omega) hn2⟩,
       ⟨1, lt_of_lt_of_le (by omega) hn2⟩), Finset.mem_univ _⟩).choose_spec.2
      (q, p) (Finset.mem_univ _))

/-- A positive selected magnitude certifies the source ordering
`q < 2` and `q < p`. -/
theorem higham11_9_skewPairArgmax_indices_of_pos {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ)
    (hpos : 0 < higham11_9_skewPivotMagnitude hn2 A) :
    (higham11_9_skewPivotQ hn2 A).val < 2 ∧
      (higham11_9_skewPivotQ hn2 A).val <
        (higham11_9_skewPivotP hn2 A).val := by
  let qp := higham11_9_skewPairArgmax hn2 A
  by_contra hbad
  have hbad' : ¬ (qp.1.val < 2 ∧ qp.1.val < qp.2.val) := by
    simpa [qp, higham11_9_skewPivotQ, higham11_9_skewPivotP] using hbad
  have hbadArg :
      ¬ ((higham11_9_skewPairArgmax hn2 A).1.val < 2 ∧
        (higham11_9_skewPairArgmax hn2 A).1.val <
          (higham11_9_skewPairArgmax hn2 A).2.val) := by
    simpa [qp] using hbad'
  have hz : higham11_9_skewPivotMagnitude hn2 A = 0 := by
    unfold higham11_9_skewPivotMagnitude higham11_9_skewPairScore
    rw [if_neg hbadArg]
  linarith

/-- The selected magnitude is exactly the magnitude of the selected entry
when it is positive. -/
theorem higham11_9_skewPivotMagnitude_eq_abs_entry_of_pos {n : ℕ}
    (hn2 : 2 ≤ n) (A : Fin n → Fin n → ℝ)
    (hpos : 0 < higham11_9_skewPivotMagnitude hn2 A) :
    higham11_9_skewPivotMagnitude hn2 A =
      |A (higham11_9_skewPivotP hn2 A)
        (higham11_9_skewPivotQ hn2 A)| := by
  have hidx := higham11_9_skewPairArgmax_indices_of_pos hn2 A hpos
  let qp := higham11_9_skewPairArgmax hn2 A
  have hidx' : qp.1.val < 2 ∧ qp.1.val < qp.2.val := by
    simpa [qp, higham11_9_skewPivotQ, higham11_9_skewPivotP] using hidx
  simp [higham11_9_skewPivotMagnitude, higham11_9_skewPivotQ,
    higham11_9_skewPivotP, higham11_9_skewPairScore, qp, hidx']

/-- Source test `||A(2:n,1)||_infinity = 0`. -/
def higham11_9_firstColumnTailZero {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ p : Fin n,
    p ≠ (⟨0, lt_of_lt_of_le (by omega) hn2⟩ : Fin n) →
      A p ⟨0, lt_of_lt_of_le (by omega) hn2⟩ = 0

/-- If the first column tail is nonzero, the actual two-column argmax has
positive magnitude. -/
theorem higham11_9_skewPivotMagnitude_pos_of_firstColumnTail_ne_zero
    {n : ℕ} (hn2 : 2 ≤ n) (A : Fin n → Fin n → ℝ)
    (hzero : ¬ higham11_9_firstColumnTailZero hn2 A) :
    0 < higham11_9_skewPivotMagnitude hn2 A := by
  classical
  simp only [higham11_9_firstColumnTailZero] at hzero
  push_neg at hzero
  obtain ⟨p, hpne, hpnz⟩ := hzero
  let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn2⟩
  have hpval : 0 < p.val := by
    have : p.val ≠ 0 := by
      intro hv
      exact hpne (Fin.ext hv)
    omega
  have hscore :
      higham11_9_skewPairScore A (i₀, p) = |A p i₀| := by
    simp [higham11_9_skewPairScore, i₀, hpval]
  have hle := higham11_9_skewPairArgmax_spec hn2 A i₀ p
  rw [hscore] at hle
  have habs : 0 < |A p i₀| := abs_pos.mpr hpnz
  exact lt_of_lt_of_le habs hle

/-- The actual pivot size returned by Algorithm 11.9. -/
noncomputable def higham11_9_skewActualPivotSize {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : PivotSize := by
  classical
  exact if higham11_9_firstColumnTailZero hn2 A then PivotSize.one
    else PivotSize.two

/-- **Algorithm 11.9 actual decision correctness.**  The finite selector
produces the existing source pivot predicate without assuming a pivot
magnitude or a branch. -/
theorem higham11_9_skewActualPivotChoice_spec {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) :
    higham11_9_SkewBunchPivotChoice
      (higham11_9_firstColumnTailZero hn2 A)
      (higham11_9_skewPivotMagnitude hn2 A)
      (higham11_9_skewActualPivotSize hn2 A) := by
  classical
  by_cases hzero : higham11_9_firstColumnTailZero hn2 A
  · exact Or.inl ⟨hzero, by simp [higham11_9_skewActualPivotSize, hzero]⟩
  · exact Or.inr ⟨hzero,
      higham11_9_skewPivotMagnitude_pos_of_firstColumnTail_ne_zero hn2 A hzero,
      by simp [higham11_9_skewActualPivotSize, hzero]⟩

/-- The actual selected pivot dominates every candidate in the first source
column. -/
theorem higham11_9_skewPivot_dominates_column_zero {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) (p : Fin n) (hp : 0 < p.val) :
    |A p ⟨0, lt_of_lt_of_le (by omega) hn2⟩| ≤
      higham11_9_skewPivotMagnitude hn2 A := by
  let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn2⟩
  have h := higham11_9_skewPairArgmax_spec hn2 A i₀ p
  simpa [higham11_9_skewPairScore, i₀, hp] using h

/-- The actual selected pivot dominates every candidate strictly below the
diagonal in the second source column. -/
theorem higham11_9_skewPivot_dominates_column_one {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) (p : Fin n) (hp : 1 < p.val) :
    |A p ⟨1, lt_of_lt_of_le (by omega) hn2⟩| ≤
      higham11_9_skewPivotMagnitude hn2 A := by
  let i₁ : Fin n := ⟨1, lt_of_lt_of_le (by omega) hn2⟩
  have h := higham11_9_skewPairArgmax_spec hn2 A i₁ p
  simpa [higham11_9_skewPairScore, i₁, hp] using h

/-- The source permutation, represented directly as a finite equivalence.
Its value at new index zero is `q`, and at new index one is `p`. -/
noncomputable def higham11_9_skewActualPerm {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : Equiv.Perm (Fin n) :=
  let i₀ : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn2⟩
  let i₁ : Fin n := ⟨1, lt_of_lt_of_le (by omega) hn2⟩
  let q := higham11_9_skewPivotQ hn2 A
  let p := higham11_9_skewPivotP hn2 A
  (Equiv.swap i₁ p).trans (Equiv.swap i₀ q)

/-- The matrix after the two symmetric interchanges in Algorithm 11.9. -/
noncomputable def higham11_9_skewActualPermutedMatrix {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => A (higham11_9_skewActualPerm hn2 A i)
    (higham11_9_skewActualPerm hn2 A j)

/-- Skew symmetry is preserved by the actual symmetric permutation. -/
theorem higham11_9_skewActualPermutedMatrix_isSkew {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) (hA : higham11_16_IsSkewSymmetric n A) :
    higham11_16_IsSkewSymmetric n
      (higham11_9_skewActualPermutedMatrix hn2 A) := by
  intro i j
  exact hA _ _

/-- The returned row/column map is a genuine permutation. -/
theorem higham11_9_skewActualPerm_injective {n : ℕ} (hn2 : 2 ≤ n)
    (A : Fin n → Fin n → ℝ) :
    Function.Injective (higham11_9_skewActualPerm hn2 A) :=
  (higham11_9_skewActualPerm hn2 A).injective

end NumStability
