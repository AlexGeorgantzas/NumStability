import Mathlib.Analysis.SpecialFunctions.Stirling
import NumStability.Analysis.TestMatrices.Hilbert.Asymptotics
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.Ginibre
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreComplexPairs
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.ProbabilityLaw.ProductLaw
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Ginibre, NumStability.Algorithms.TestMatrices.Higham28GinibreComplexPairs, NumStability.Algorithms.TestMatrices.Higham28GinibreRoots under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open Filter Asymptotics Polynomial MeasureTheory

local instance instMeasurableSpaceRSqMat_2 (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Once measurability of the root count is supplied, boundedness makes its
integrability under the normalized real-Ginibre law automatic. -/
theorem integrable_realEigenvalueCount_of_aestronglyMeasurable
    (n : ℕ)
    (hmeas : AEStronglyMeasurable
      (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n)) :
    Integrable
      (fun A : RSqMat n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  apply Integrable.of_bound hmeas n
  filter_upwards with A
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast realEigenvalueCount_le n A

end NumStability

noncomputable section
namespace NumStability


open MeasureTheory Polynomial

local instance instMeasurableSpaceGinibreRawMatrix (n : ℕ) : MeasurableSpace (GinibreRawMatrix n) := MeasurableSpace.pi

local instance instOpensMeasurableSpaceGinibreRawMatrix (n : ℕ) : OpensMeasurableSpace (GinibreRawMatrix n) := Pi.opensMeasurableSpace

local instance instBorelSpaceGinibreRawMatrix (n : ℕ) : BorelSpace (GinibreRawMatrix n) := Pi.borelSpace

local instance instStandardBorelSpaceGinibreRawMatrix (n : ℕ) : StandardBorelSpace (GinibreRawMatrix n) :=
  StandardBorelSpace.pi_countable

local instance instMeasurableSpaceForallFinComplex_numStability (n : ℕ) : MeasurableSpace (Fin n → ℂ) := MeasurableSpace.pi

local instance instOpensMeasurableSpaceForallFinComplex_numStability (n : ℕ) : OpensMeasurableSpace (Fin n → ℂ) := Pi.opensMeasurableSpace

local instance instBorelSpaceForallFinComplex_numStability (n : ℕ) : BorelSpace (Fin n → ℂ) := Pi.borelSpace

local instance instStandardBorelSpaceForallFinComplex_numStability (n : ℕ) : StandardBorelSpace (Fin n → ℂ) :=
  StandardBorelSpace.pi_countable

theorem measurable_complexTupleRealCount (n : ℕ) :
    Measurable (@complexTupleRealCount n) := by
  classical
  unfold complexTupleRealCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · exact measurableSet_eq_fun
      (Complex.measurable_im.comp (measurable_pi_apply i)) measurable_const
  · exact measurable_const
  · exact measurable_const

theorem measurableSet_complexRootTupleCountSet (n k : ℕ) :
    MeasurableSet (complexRootTupleCountSet n k) := by
  apply (isClosed_complexRootTupleSet n).measurableSet.inter
  exact measurableSet_eq_fun
    ((measurable_complexTupleRealCount n).comp measurable_snd) measurable_const

theorem analyticSet_complexRootTupleCountProjection (n k : ℕ) :
    AnalyticSet (complexRootTupleCountProjection n k) := by
  exact (measurableSet_complexRootTupleCountSet n k).analyticSet.image_of_continuous
    continuous_fst

theorem measurableSet_realEigenvalueCount_level (n k : ℕ) :
    MeasurableSet {A : GinibreRawMatrix n | realEigenvalueCount n A = k} := by
  have hset : {A : GinibreRawMatrix n | realEigenvalueCount n A = k} =
      complexRootTupleCountProjection n k := by
    ext A
    exact (mem_complexRootTupleCountProjection_iff n k A).symm
  rw [hset]
  apply (analyticSet_complexRootTupleCountProjection n k).measurableSet_of_compl
  rw [compl_complexRootTupleCountProjection]
  apply AnalyticSet.iUnion
  intro j
  split
  · exact analyticSet_empty
  · exact analyticSet_complexRootTupleCountProjection n j

theorem measurable_realEigenvalueCount (n : ℕ) :
    Measurable (fun A : GinibreRawMatrix n => realEigenvalueCount n A) := by
  apply measurable_to_countable'
  intro k
  simpa only [Set.preimage, Set.mem_singleton_iff] using
    measurableSet_realEigenvalueCount_level n k

/-- The real-valued root count used in the Ginibre expectation is Borel
measurable; this is the source-facing form needed by Bochner integration. -/
theorem measurable_realEigenvalueCount_real (n : ℕ) :
    Measurable (fun A : GinibreRawMatrix n => (realEigenvalueCount n A : ℝ)) :=
  (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
    (measurable_realEigenvalueCount n)

theorem aestronglyMeasurable_realEigenvalueCount (n : ℕ) :
    AEStronglyMeasurable
      (fun A : GinibreRawMatrix n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) :=
  (measurable_realEigenvalueCount_real n).aestronglyMeasurable

/-- The real-eigenvalue count is integrable under the normalized real
Ginibre law, unconditionally. -/
theorem integrable_realEigenvalueCount (n : ℕ) :
    Integrable
      (fun A : GinibreRawMatrix n => (realEigenvalueCount n A : ℝ))
      (realGinibreMeasure n) :=
  integrable_realEigenvalueCount_of_aestronglyMeasurable n
    (aestronglyMeasurable_realEigenvalueCount n)

theorem measurable_complexTupleRealBelowCount (n : ℕ) :
    Measurable (@complexTupleRealBelowCount n) := by
  classical
  unfold complexTupleRealBelowCount
  simp_rw [Finset.card_filter]
  apply Finset.measurable_sum
  intro i hi
  apply Measurable.ite
  · apply MeasurableSet.inter
    · exact measurableSet_eq_fun
        (Complex.measurable_im.comp (measurable_pi_apply i |>.comp measurable_fst))
        measurable_const
    · exact measurableSet_lt
        (Complex.measurable_re.comp (measurable_pi_apply i |>.comp measurable_fst))
        measurable_snd
  · exact measurable_const
  · exact measurable_const

theorem measurableSet_complexRootTupleBelowCountSet (n k : ℕ) :
    MeasurableSet (complexRootTupleBelowCountSet n k) := by
  apply MeasurableSet.inter
  · exact (isClosed_complexRootTupleSet n).measurableSet.preimage
      ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  · exact measurableSet_eq_fun
      ((measurable_complexTupleRealBelowCount n).comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
      measurable_const

theorem analyticSet_complexRootTupleBelowCountProjection (n k : ℕ) :
    AnalyticSet (complexRootTupleBelowCountProjection n k) := by
  exact (measurableSet_complexRootTupleBelowCountSet n k).analyticSet.image_of_continuous
    continuous_fst

theorem measurableSet_realEigenvalueBelowCount_level (n k : ℕ) :
    MeasurableSet {p : GinibreRawMatrix n × ℝ | realEigenvalueBelowCount p = k} := by
  have hset : {p : GinibreRawMatrix n × ℝ | realEigenvalueBelowCount p = k} =
      complexRootTupleBelowCountProjection n k := by
    ext p
    exact (mem_complexRootTupleBelowCountProjection_iff n k p).symm
  rw [hset]
  apply (analyticSet_complexRootTupleBelowCountProjection n k).measurableSet_of_compl
  rw [compl_complexRootTupleBelowCountProjection]
  apply AnalyticSet.iUnion
  intro j
  split
  · exact analyticSet_empty
  · exact analyticSet_complexRootTupleBelowCountProjection n j

theorem measurable_realEigenvalueBelowCount (n : ℕ) :
    Measurable (@realEigenvalueBelowCount n) := by
  apply measurable_to_countable'
  intro k
  simpa only [Set.preimage, Set.mem_singleton_iff] using
    measurableSet_realEigenvalueBelowCount_level n k

end NumStability
end

noncomputable section

namespace NumStability

open MeasureTheory Polynomial

open scoped ComplexConjugate

local instance ginibreComplexPairsMeasurableSpace (n : ℕ) :
    MeasurableSpace (GinibreRawMatrix n) :=
  MeasurableSpace.pi

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

end NumStability

end
