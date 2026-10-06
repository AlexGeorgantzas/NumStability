/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28GinibreRoots

/-! # Higham Chapter 28: real roots and conjugate pairs

This module partitions the complex characteristic roots of a real matrix,
with algebraic multiplicity, into real roots and the two open half-planes.
Complex conjugation preserves the complete root multiset and exchanges the
upper and lower parts.  Consequently the real-root count plus twice the
upper-half-plane count is the matrix dimension.
-/

namespace NumStability

open MeasureTheory Polynomial
open scoped ComplexConjugate

noncomputable section

local instance ginibreComplexPairsMeasurableSpace (n : ℕ) :
    MeasurableSpace (GinibreRawMatrix n) :=
  MeasurableSpace.pi

/-- Number of characteristic roots in the open upper half-plane, counted
with algebraic multiplicity. -/
def complexUpperEigenvalueCount (n : ℕ) (A : GinibreRawMatrix n) : ℕ :=
  ((complexMatrixCharpoly A).roots.filter fun z => 0 < z.im).card

/-- Mapping the complex characteristic polynomial of a real matrix through
complex conjugation leaves the polynomial unchanged. -/
theorem map_complexMatrixCharpoly_conj {n : ℕ} (A : GinibreRawMatrix n) :
    (complexMatrixCharpoly A).map Complex.conjAe.toRingEquiv.toRingHom =
      complexMatrixCharpoly A := by
  rw [complexMatrixCharpoly, Polynomial.map_map]
  congr 1
  ext x
  simp [Complex.conjAe_coe]

/-- The complete complex root multiset of a real characteristic polynomial
is invariant under conjugation.  Since this is a multiset equality, it
retains algebraic multiplicities. -/
theorem roots_complexMatrixCharpoly_map_conj {n : ℕ}
    (A : GinibreRawMatrix n) :
    (complexMatrixCharpoly A).roots.map (starRingEnd ℂ) =
      (complexMatrixCharpoly A).roots := by
  have h := (IsAlgClosed.splits (complexMatrixCharpoly A)).roots_map_of_injective
    Complex.conjAe.toRingEquiv.injective
  rw [show (starRingEnd ℂ) = Complex.conjAe.toRingEquiv.toRingHom by ext; rfl,
    map_complexMatrixCharpoly_conj A] at h
  exact h.symm

/-- Conjugate roots occur with exactly equal algebraic multiplicity. -/
theorem complexMatrixCharpoly_rootMultiplicity_conj
    {n : ℕ} (A : GinibreRawMatrix n) (z : ℂ) :
    (complexMatrixCharpoly A).roots.count ((starRingEnd ℂ) z) =
      (complexMatrixCharpoly A).roots.count z := by
  classical
  have hcount := Multiset.count_map_eq_count'
    (starRingEnd ℂ) (complexMatrixCharpoly A).roots
    Complex.conjAe.toRingEquiv.injective z
  rw [roots_complexMatrixCharpoly_map_conj A] at hcount
  exact hcount

private theorem card_partition_by_im (s : Multiset ℂ) :
    s.card =
      (s.filter fun z => z.im = 0).card +
      (s.filter fun z => 0 < z.im).card +
      (s.filter fun z => z.im < 0).card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons z s ih =>
      rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
      · simp [hneg, hneg.ne, not_lt.mpr hneg.le, ih]
        omega
      · simp [hzero, ih]
        omega
      · simp [hpos, hpos.ne', not_lt.mpr hpos.le, ih]
        omega

private theorem card_filter_im_neg_eq_pos_of_map_conj
    (s : Multiset ℂ) (hs : s.map (starRingEnd ℂ) = s) :
    (s.filter fun z => z.im < 0).card =
      (s.filter fun z => 0 < z.im).card := by
  calc
    (s.filter fun z => z.im < 0).card =
        ((s.map (starRingEnd ℂ)).filter fun z => z.im < 0).card := by rw [hs]
    _ = ((s.filter fun z => ((starRingEnd ℂ) z).im < 0).map
        (starRingEnd ℂ)).card := by
      simp only [Multiset.filter_map, Function.comp_apply]
    _ = (s.filter fun z => 0 < z.im).card := by
      simp only [Multiset.card_map, Complex.conj_im, neg_lt_zero]

/-- The roots of the complexified characteristic polynomial on the real axis
are exactly the roots of the original real characteristic polynomial. -/
theorem card_filter_im_eq_zero_complexMatrixCharpoly
    {n : ℕ} (A : GinibreRawMatrix n) :
    ((complexMatrixCharpoly A).roots.filter fun z => z.im = 0).card =
      realEigenvalueCount n A := by
  classical
  have hf := Polynomial.filter_roots_map_range_eq_map_roots
    Complex.ofRealHom.injective (Matrix.charpoly (Matrix.of A))
  have hc := congrArg Multiset.card hf
  rw [show (Matrix.charpoly (Matrix.of A)).map Complex.ofRealHom =
      complexMatrixCharpoly A by rfl, Multiset.card_map] at hc
  simpa only [mem_range_complexOfReal_iff] using hc

/-- Every nonreal characteristic root belongs to one conjugate pair.  This
identity counts every root with its algebraic multiplicity. -/
theorem realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount
    (n : ℕ) (A : GinibreRawMatrix n) :
    realEigenvalueCount n A + 2 * complexUpperEigenvalueCount n A = n := by
  let s := (complexMatrixCharpoly A).roots
  have hpart := card_partition_by_im s
  have hconj : s.map (starRingEnd ℂ) = s :=
    roots_complexMatrixCharpoly_map_conj A
  have hupdown := card_filter_im_neg_eq_pos_of_map_conj s hconj
  have hcard : s.card = n := by
    dsimp [s]
    rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_complexMatrixCharpoly]
  have hreal : (s.filter fun z => z.im = 0).card =
      realEigenvalueCount n A := by
    exact card_filter_im_eq_zero_complexMatrixCharpoly A
  unfold complexUpperEigenvalueCount
  dsimp [s] at hpart hcard hreal hupdown
  omega

theorem complexUpperEigenvalueCount_eq
    (n : ℕ) (A : GinibreRawMatrix n) :
    complexUpperEigenvalueCount n A = (n - realEigenvalueCount n A) / 2 := by
  have h := realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount n A
  omega

theorem complexUpperEigenvalueCount_le
    (n : ℕ) (A : GinibreRawMatrix n) :
    complexUpperEigenvalueCount n A ≤ n := by
  have h := realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount n A
  omega

/-- The conjugate-pair count is Borel measurable in the matrix entries. -/
theorem measurable_complexUpperEigenvalueCount (n : ℕ) :
    Measurable (fun A : GinibreRawMatrix n => complexUpperEigenvalueCount n A) := by
  have hfun : (fun A : GinibreRawMatrix n => complexUpperEigenvalueCount n A) =
      fun A => (n - realEigenvalueCount n A) / 2 := by
    funext A
    exact complexUpperEigenvalueCount_eq n A
  rw [hfun]
  exact (measurable_of_countable (fun k : ℕ => (n - k) / 2)).comp
    (measurable_realEigenvalueCount n)

theorem measurable_complexUpperEigenvalueCount_real (n : ℕ) :
    Measurable
      (fun A : GinibreRawMatrix n => (complexUpperEigenvalueCount n A : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_complexUpperEigenvalueCount n)

/-- The number of nonreal conjugate pairs is integrable under the normalized
real Ginibre law. -/
theorem integrable_complexUpperEigenvalueCount (n : ℕ) :
    Integrable
      (fun A : GinibreRawMatrix n => (complexUpperEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  refine @Integrable.of_bound _ _ _ _ _ this _
    (measurable_complexUpperEigenvalueCount_real n).aestronglyMeasurable n ?_
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast complexUpperEigenvalueCount_le n A

end
end NumStability
