import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance
import NumStability.Algorithms.Summation.Compensated.Kahan.Core
import NumStability.Algorithms.Summation.Tree.Core
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter04.Problem04
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.Ginibre
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.FiniteExpectation.GinibreSignedExpectation
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.ExpectedCountTransfer
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Incidence.GinibreTruncatedIncidence
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.InvariantPlanes.GinibreComplexPairs
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.RootMeasurability.GinibreMultiplicity

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28GinibreSignedExpectation, NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRank, NumStability.Algorithms.TestMatrices.Higham28GinibreSignedRankTransfer, NumStability.Algorithms.TestMatrices.Higham28GinibreTruncatedIncidence under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

noncomputable section
namespace NumStability


open Filter MeasureTheory ProbabilityTheory Set

open scoped BigOperators ENNReal

private theorem two_mul_alternating_range (r : ℕ) :
    2 * (∑ i ∈ Finset.range r, (-1 : ℝ) ^ i) =
      1 - (-1 : ℝ) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
      rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
      ring

private theorem one_eq_rankSign_sub_pairPrefix (j : ℕ) :
    (1 : ℝ) = (-1 : ℝ) ^ j -
      2 * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j) := by
  rw [show (∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)) =
      (-1 : ℝ) ^ j * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i by
    simp_rw [pow_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring]
  have h := two_mul_alternating_range j
  have hsign : ((-1 : ℝ) ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  symm
  calc
    (-1 : ℝ) ^ j -
        2 * ((-1 : ℝ) ^ j * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i) =
        (-1 : ℝ) ^ j -
          (-1 : ℝ) ^ j *
            (2 * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ i) := by ring
    _ = (-1 : ℝ) ^ j - (-1 : ℝ) ^ j * (1 - (-1 : ℝ) ^ j) := by
      rw [h]
    _ = ((-1 : ℝ) ^ j) ^ 2 := by ring
    _ = 1 := hsign

/-- Every finite unsigned count is a one-rank alternating sum minus twice
the corresponding alternating pair sum. -/
theorem natCast_eq_alternating_sub_two_pairs (r : ℕ) :
    (r : ℝ) =
      ginibreAlternatingCount r -
        2 * ginibreAlternatingPairCount r := by
  unfold ginibreAlternatingCount ginibreAlternatingPairCount
  calc
    (r : ℝ) = ∑ _j ∈ Finset.range r, (1 : ℝ) := by simp
    _ = ∑ j ∈ Finset.range r,
        ((-1 : ℝ) ^ j -
          2 * ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact one_eq_rankSign_sub_pairPrefix j
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]

/-- At a regular incidence point, the parity of the marked root's rank is
exactly the sign of the deflated characteristic determinant. -/
theorem neg_one_pow_rootRank_mul_abs_det
    {m : ℕ} (q : GinibreIncidenceCoordinates m)
    (hq : q ∈ ginibreIncidenceRegularSet m) :
    (-1 : ℝ) ^ ginibreIncidenceRootRank q *
        |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| =
      (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det := by
  let D : RSqMat m := ginibreIncidenceDeflatedBlock q
  let l : ℝ := ginibreIncidenceEigenvalue q
  let P : Polynomial ℝ := D.charpoly
  have hPmonic : P.Monic := Matrix.charpoly_monic D
  have hPne : P ≠ 0 := hPmonic.ne_zero
  have hx : ¬P.IsRoot l := by
    intro hroot
    have heval : P.eval l = 0 := hroot
    rw [show P = D.charpoly by rfl, Matrix.eval_charpoly] at heval
    have htangent : ginibreIncidenceTangentMatrix q =
        Matrix.scalar (Fin m) l - D := by
      ext i j
      simp [ginibreIncidenceTangentMatrix, D, l, Matrix.scalar_apply,
        Matrix.one_apply, Matrix.diagonal_apply]
    change (ginibreIncidenceTangentMatrix q).det ≠ 0 at hq
    apply hq
    rw [htangent]
    exact heval
  have hlinear :
      (Polynomial.X - Polynomial.C l : Polynomial ℝ) ≠ 0 :=
    Polynomial.X_sub_C_ne_zero l
  have hfullRoots :
      (ginibreIncidenceMatrix q).charpoly.roots = P.roots + {l} := by
    rw [ginibreIncidenceMatrix_charpoly_factor]
    change (D.charpoly * (Polynomial.X - Polynomial.C l)).roots = _
    rw [Polynomial.roots_mul (mul_ne_zero hPne hlinear),
      Polynomial.roots_X_sub_C]
  have hrank : ginibreIncidenceRootRank q =
      (P.roots.filter fun z => z < l).card := by
    unfold ginibreIncidenceRootRank realEigenvalueBelowCount
    rw [ginibreCoordinatesFinMatrix_charpoly,
      ginibreCoordinatesMatrix_chart, hfullRoots,
      Multiset.filter_add, Multiset.card_add,
      Multiset.filter_singleton, if_neg (lt_irrefl l)]
    rfl
  have hdet :
      (-1 : ℝ) ^ P.natDegree * P.eval l =
        (D - l • (1 : RSqMat m)).det := by
    have hnat : P.natDegree = m := by
      change D.charpoly.natDegree = m
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    rw [show P = D.charpoly by rfl, Matrix.eval_charpoly, hnat]
    have hneg : D - l • (1 : RSqMat m) =
        -(Matrix.scalar (Fin m) l - D) := by
      ext i j
      simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]
    rw [hneg, Matrix.det_neg, Fintype.card_fin]
  have hpoly :=
    Polynomial.negOnePow_card_roots_lt_mul_abs_eval hPmonic hx
  rw [hrank, ← hdet]
  exact hpoly

/-- Away from the existing affine-boundary and critical-value exceptional
sets, the occupied incidence rank sheets are precisely the ranks strictly
below the full real-root count. -/
theorem mem_ginibreIncidenceRankImage_iff_lt_rootCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ)
    (k : Fin (m + 2)) :
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k ↔
      k.val <
        realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) := by
  classical
  let P : Polynomial ℝ :=
    Matrix.charpoly (Matrix.of (ginibreCoordinatesFinMatrix p))
  let count : ℕ :=
    realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)
  let K : Finset (Fin (m + 2)) := Finset.univ.filter fun j =>
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m j
  have hPne : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hcountDegree : count ≤ m + 1 := by
    change P.roots.card ≤ m + 1
    exact (Polynomial.card_roots' P).trans_eq (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  let countFin : Fin (m + 2) := ⟨count, by omega⟩
  let S : Finset (Fin (m + 2)) := Finset.Iio countFin
  have hKS : K ⊆ S := by
    intro j hj
    have hjImage := (Finset.mem_filter.1 hj).2
    rcases hjImage with ⟨q, hq, hchart⟩
    have hreg : q ∈ ginibreIncidenceRegularSet m := hq.1
    have hrank : ginibreIncidenceRootRank q = j.val := hq.2
    let l : ℝ := ginibreIncidenceEigenvalue q
    have hlroot : P.IsRoot l := by
      simpa [P, l, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
    have hlmem : l ∈ P.roots :=
      (Polynomial.mem_roots hPne).2 hlroot
    have hrankCard :
        (P.roots.filter fun z => z < l).card = j.val := by
      simpa [ginibreIncidenceRootRank, realEigenvalueBelowCount, P, l,
        hchart] using hrank
    have hstrict := card_filter_lt_card_filter_of_mem P.roots hlmem
      (show l < l + 1 by linarith)
    have hfilterLe :
        (P.roots.filter fun z => z < l + 1).card ≤ P.roots.card :=
      Multiset.card_le_card (Multiset.filter_le _ _)
    have hjCount : j.val < count := by
      change j.val < P.roots.card
      rw [← hrankCard]
      exact hstrict.trans_le hfilterLe
    simpa [S, countFin] using hjCount
  have hKcard : K.card = count := by
    have hmult := ginibreRegularFiberMultiplicity_eq_realEigenvalueCount
      p hboundary hcritical
    simpa [K, count, ginibreRegularFiberMultiplicity, Finset.sum_boole]
      using hmult
  have hScard : S.card = count := by
    simp [S, countFin, Fin.card_Iio]
  have hKS_eq : K = S :=
    Finset.eq_of_subset_of_card_le hKS (by rw [hScard, hKcard])
  have hfinal : k ∈ K ↔ k.val < count := by
    rw [hKS_eq]
    simp only [S, Finset.mem_Iio]
    change k.val < count ↔ k.val < count
    rfl
  simpa [K, count] using hfinal

/-- Single-rank-sheet form of the incidence area identity.  Keeping this
identity before summing the sheets is what permits alternating signs to be
attached outside the nonnegative change-of-variables theorem. -/
theorem lintegral_ginibreIncidence_rankPiece_eq_image
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (k : Fin (m + 2))
    (g : GinibreIncidenceCoordinates m → ℝ≥0∞) :
    ∫⁻ q in ginibreIncidenceRankPiece m k,
        ENNReal.ofReal |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫⁻ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece m k,
        g p ∂μ := by
  exact (lintegral_image_eq_lintegral_abs_det_fderiv_mul
    μ (measurableSet_ginibreIncidenceRankPiece m k)
    (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
    (injOn_ginibreIncidenceChart_rankPiece m k) g).symm

end NumStability
end

noncomputable section

namespace NumStability

open MeasureTheory ProbabilityTheory

private local instance ginibreSignedExpectationMeasurableSpace (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

/-- Expected alternating one-root count. -/
def expectedGinibreAlternatingCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, ginibreAlternatingEigenvalueCount n A
    ∂realGinibreMeasure n

/-- Expected alternating ordered-pair count.  This is the `T n` quantity in
the signed two-incidence recurrence. -/
def expectedGinibreAlternatingPairCount (n : ℕ) : ℝ :=
  ∫ A : RSqMat n, ginibreAlternatingPairEigenvalueCount n A
    ∂realGinibreMeasure n

theorem measurable_ginibreAlternatingEigenvalueCount (n : ℕ) :
    Measurable (ginibreAlternatingEigenvalueCount n) := by
  exact (measurable_of_countable (fun r : ℕ => ginibreAlternatingCount r)).comp
    (measurable_realEigenvalueCount n)

theorem measurable_ginibreAlternatingPairEigenvalueCount (n : ℕ) :
    Measurable (ginibreAlternatingPairEigenvalueCount n) := by
  exact (measurable_of_countable
    (fun r : ℕ => ginibreAlternatingPairCount r)).comp
      (measurable_realEigenvalueCount n)

theorem integrable_ginibreAlternatingEigenvalueCount (n : ℕ) :
    Integrable (ginibreAlternatingEigenvalueCount n)
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  refine Integrable.of_bound
    (measurable_ginibreAlternatingEigenvalueCount n).aestronglyMeasurable n ?_
  filter_upwards with A
  rw [Real.norm_eq_abs]
  exact (abs_ginibreAlternatingCount_le _).trans (by
    exact_mod_cast realEigenvalueCount_le n A)

theorem integrable_ginibreAlternatingPairEigenvalueCount (n : ℕ) :
    Integrable (ginibreAlternatingPairEigenvalueCount n)
      (realGinibreMeasure n) := by
  letI : IsFiniteMeasure (realGinibreMeasure n) :=
    ⟨by rw [realGinibreMeasure_univ]; norm_num⟩
  refine Integrable.of_bound
    (measurable_ginibreAlternatingPairEigenvalueCount n).aestronglyMeasurable
      ((n : ℝ) ^ 2) ?_
  filter_upwards with A
  rw [Real.norm_eq_abs]
  exact (abs_ginibreAlternatingPairCount_le_sq _).trans (by
    gcongr
    exact_mod_cast realEigenvalueCount_le n A)

/-- Pointwise signed decomposition of the ordinary root count. -/
theorem realEigenvalueCount_cast_eq_alternating_sub_two_pairs
    (n : ℕ) (A : RSqMat n) :
    (realEigenvalueCount n A : ℝ) =
      ginibreAlternatingEigenvalueCount n A -
        2 * ginibreAlternatingPairEigenvalueCount n A := by
  exact natCast_eq_alternating_sub_two_pairs (realEigenvalueCount n A)

/-- Expected-count version of the signed rank/pair decomposition. -/
theorem expectedRealEigenvalueCount_eq_alternating_sub_two_pairs
    (n : ℕ) :
    expectedRealEigenvalueCount n =
      expectedGinibreAlternatingCount n -
        2 * expectedGinibreAlternatingPairCount n := by
  unfold expectedRealEigenvalueCount expectedGinibreAlternatingCount
    expectedGinibreAlternatingPairCount
  rw [show (fun A : RSqMat n => (realEigenvalueCount n A : ℝ)) =
      fun A => ginibreAlternatingEigenvalueCount n A -
        2 * ginibreAlternatingPairEigenvalueCount n A by
    funext A
    exact realEigenvalueCount_cast_eq_alternating_sub_two_pairs n A]
  rw [integral_sub
    (integrable_ginibreAlternatingEigenvalueCount n)
    ((integrable_ginibreAlternatingPairEigenvalueCount n).const_mul 2),
    integral_const_mul]

/-- Because nonreal roots occur in conjugate pairs, the alternating one-root
observable depends only on the matrix dimension. -/
theorem ginibreAlternatingEigenvalueCount_eq_dimension
    (n : ℕ) (A : RSqMat n) :
    ginibreAlternatingEigenvalueCount n A = ginibreAlternatingCount n := by
  have hpair :=
    realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount n A
  unfold ginibreAlternatingEigenvalueCount
  calc
    ginibreAlternatingCount (realEigenvalueCount n A) =
        ginibreAlternatingCount
          (realEigenvalueCount n A +
            2 * complexUpperEigenvalueCount n A) :=
      (ginibreAlternatingCount_add_two_mul
        (realEigenvalueCount n A)
        (complexUpperEigenvalueCount n A)).symm
    _ = ginibreAlternatingCount n := by rw [hpair]

theorem expectedGinibreAlternatingCount_eq_dimension (n : ℕ) :
    expectedGinibreAlternatingCount n = ginibreAlternatingCount n := by
  unfold expectedGinibreAlternatingCount
  rw [show (fun A : RSqMat n => ginibreAlternatingEigenvalueCount n A) =
      fun _A : RSqMat n => ginibreAlternatingCount n by
    funext A
    exact ginibreAlternatingEigenvalueCount_eq_dimension n A]
  rw [integral_const]
  simp only [realGinibreMeasure_univ, measureReal_def, ENNReal.toReal_one,
    one_smul]

theorem expectedGinibreAlternatingCount_add_two (m : ℕ) :
    expectedGinibreAlternatingCount (m + 2) =
      expectedGinibreAlternatingCount m := by
  rw [expectedGinibreAlternatingCount_eq_dimension,
    expectedGinibreAlternatingCount_eq_dimension,
    ginibreAlternatingCount_add_two]

theorem expectedGinibreAlternatingPairCount_one :
    expectedGinibreAlternatingPairCount 1 = 0 := by
  unfold expectedGinibreAlternatingPairCount
    ginibreAlternatingPairEigenvalueCount ginibreAlternatingPairCount
  rw [show (fun A : RSqMat 1 =>
      ∑ j ∈ Finset.range (realEigenvalueCount 1 A),
        ∑ i ∈ Finset.range j, (-1 : ℝ) ^ (i + j)) =
      fun _A : RSqMat 1 => 0 by
    funext A
    have h := realEigenvalueCount_add_two_mul_complexUpperEigenvalueCount 1 A
    have hr : realEigenvalueCount 1 A = 1 := by omega
    rw [hr]
    norm_num]
  simp

/-- Consequently, a two-dimensional shift of the genuine expected count is
exactly minus twice the corresponding shift of the signed pair expectation. -/
theorem expectedRealEigenvalueCount_shift_eq_neg_two_mul_pair_shift
    (m : ℕ) :
    expectedRealEigenvalueCount (m + 2) -
        expectedRealEigenvalueCount m =
      -2 * (expectedGinibreAlternatingPairCount (m + 2) -
        expectedGinibreAlternatingPairCount m) := by
  rw [expectedRealEigenvalueCount_eq_alternating_sub_two_pairs,
    expectedRealEigenvalueCount_eq_alternating_sub_two_pairs,
    expectedGinibreAlternatingCount_add_two]
  ring

end NumStability

end

noncomputable section

namespace NumStability

open MeasureTheory Set

open scoped BigOperators

local instance instDecidable_numStability (p : Prop) : Decidable p := Classical.propDecidable p

theorem measurableSet_ginibreIncidenceRankPieceBelow
    (m : ℕ) (k : Fin (m + 2)) (x : ℝ) :
    MeasurableSet (ginibreIncidenceRankPieceBelow m k x) := by
  exact (measurableSet_ginibreIncidenceRankPiece m k).inter
    (measurableSet_lt measurable_ginibreIncidenceEigenvalue measurable_const)

/-- Ordinary signed-integral area formula on one regular rank sheet. -/
theorem integral_ginibreIncidence_rankPiece_eq_image
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (k : Fin (m + 2))
    (g : GinibreIncidenceCoordinates m → ℝ) :
    ∫ q in ginibreIncidenceRankPiece m k,
        |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫ p in ginibreIncidenceChart '' ginibreIncidenceRankPiece m k,
        g p ∂μ := by
  have h := (integral_image_eq_integral_abs_det_fderiv_smul
    μ (measurableSet_ginibreIncidenceRankPiece m k)
    (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
    (injOn_ginibreIncidenceChart_rankPiece m k) g).symm
  simpa [smul_eq_mul] using h

/-- Ordinary signed-integral area formula on the part of one rank sheet
below an external spectral threshold. -/
theorem integral_ginibreIncidence_rankPieceBelow_eq_image
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (k : Fin (m + 2)) (x : ℝ)
    (g : GinibreIncidenceCoordinates m → ℝ) :
    ∫ q in ginibreIncidenceRankPieceBelow m k x,
        |(ginibreIncidenceDerivativeLinearMap q).det| *
          g (ginibreIncidenceChart q) ∂μ =
      ∫ p in ginibreIncidenceChart ''
          ginibreIncidenceRankPieceBelow m k x,
        g p ∂μ := by
  have hinj : Set.InjOn ginibreIncidenceChart
      (ginibreIncidenceRankPieceBelow m k x) :=
    (injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left
  have h := (integral_image_eq_integral_abs_det_fderiv_smul
    μ (measurableSet_ginibreIncidenceRankPieceBelow m k x)
    (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
    hinj g).symm
  simpa [smul_eq_mul] using h

/-- Away from the affine-boundary and critical-value sets, the truncated
`k`th rank sheet is occupied precisely when there are more than `k` real
roots below the fixed threshold. -/
theorem mem_ginibreIncidenceRankPieceBelow_image_iff_lt_belowCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ)
    (k : Fin (m + 2)) (x : ℝ) :
    p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPieceBelow m k x ↔
      k.val < realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x) := by
  classical
  let P : Polynomial ℝ :=
    Matrix.charpoly (Matrix.of (ginibreCoordinatesFinMatrix p))
  have hPne : P ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  constructor
  · rintro ⟨q, ⟨hq, hqlt⟩, hchart⟩
    have hlroot : P.IsRoot (ginibreIncidenceEigenvalue q) := by
      simpa [P, hchart] using ginibreIncidenceEigenvalue_isRoot_charpoly q
    have hlmem : ginibreIncidenceEigenvalue q ∈ P.roots :=
      (Polynomial.mem_roots hPne).2 hlroot
    have hstrict := card_filter_lt_card_filter_of_mem P.roots hlmem hqlt
    have hrank : ginibreIncidenceRootRank q = k.val := hq.2
    have hrankCard :
        (P.roots.filter fun z => z < ginibreIncidenceEigenvalue q).card =
          k.val := by
      simpa [ginibreIncidenceRootRank, realEigenvalueBelowCount, P, hchart]
        using hrank
    rw [hrankCard] at hstrict
    simpa [realEigenvalueBelowCount, P] using hstrict
  · intro hk
    have hbelowLeFull :
        realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x) ≤
          realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) := by
      unfold realEigenvalueBelowCount realEigenvalueCount
      exact Multiset.card_le_card (Multiset.filter_le _ _)
    have hkFull :
        k.val < realEigenvalueCount (m + 1)
          (ginibreCoordinatesFinMatrix p) :=
      hk.trans_le hbelowLeFull
    have himage :=
      (mem_ginibreIncidenceRankImage_iff_lt_rootCount
        p hboundary hcritical k).2 hkFull
    rcases himage with ⟨q, hq, hchart⟩
    refine ⟨q, ⟨hq, ?_⟩, hchart⟩
    by_contra hnlt
    have hxle : x ≤ ginibreIncidenceEigenvalue q := le_of_not_gt hnlt
    have hfilterLe :
        (P.roots.filter fun z => z < x).card ≤
          (P.roots.filter
            fun z => z < ginibreIncidenceEigenvalue q).card := by
      exact Multiset.card_le_card
        (Multiset.monotone_filter_right P.roots
          (fun z hz => lt_of_lt_of_le hz hxle))
    have hrank : ginibreIncidenceRootRank q = k.val := hq.2
    have hrankCard :
        (P.roots.filter fun z => z < ginibreIncidenceEigenvalue q).card =
          k.val := by
      simpa [ginibreIncidenceRootRank, realEigenvalueBelowCount, P, hchart]
        using hrank
    have hbelowLeRank :
        realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x) ≤
          k.val := by
      rw [hrankCard] at hfilterLe
      simpa [realEigenvalueBelowCount, P] using hfilterLe
    exact (Nat.not_lt_of_ge hbelowLeRank) hk

/-- Pointwise collapse of the signed regular-rank sheets above a generic
matrix to the alternating real-root count. -/
theorem sum_ginibreIncidenceRankImage_sign_eq_alternatingCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ) :
    (∑ k : Fin (m + 2),
      if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k then
        (-1 : ℝ) ^ k.val else 0) =
      ginibreAlternatingCount
        (realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)) := by
  classical
  simp_rw [mem_ginibreIncidenceRankImage_iff_lt_rootCount
    p hboundary hcritical]
  apply sum_fin_ite_lt_eq_ginibreAlternatingCount
  have hdegree :
      realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) ≤
        m + 1 := by
    unfold realEigenvalueCount
    exact (Polynomial.card_roots' _).trans_eq (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  omega

/-- Pointwise collapse of signed rank sheets with the one-root prefix weight
to the alternating ordered-pair count. -/
theorem sum_ginibreIncidenceRankImage_pairPrefix_eq_alternatingPairCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ) :
    (∑ k : Fin (m + 2),
      if p ∈ ginibreIncidenceChart '' ginibreIncidenceRankPiece m k then
        (-1 : ℝ) ^ k.val * ginibreAlternatingCount k.val else 0) =
      ginibreAlternatingPairCount
        (realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p)) := by
  classical
  simp_rw [mem_ginibreIncidenceRankImage_iff_lt_rootCount
    p hboundary hcritical]
  apply sum_fin_ite_lt_eq_ginibreAlternatingPairCount
  have hdegree :
      realEigenvalueCount (m + 1) (ginibreCoordinatesFinMatrix p) ≤
        m + 1 := by
    unfold realEigenvalueCount
    exact (Polynomial.card_roots' _).trans_eq (by
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])
  omega

/-- Pointwise collapse of the signed truncated rank sheets to the alternating
count of roots below the threshold. -/
theorem sum_ginibreIncidenceRankPieceBelow_image_sign_eq_alternatingCount
    {m : ℕ} (p : GinibreIncidenceCoordinates m)
    (hboundary : p ∉ ginibreAffineBoundaryEigenpairSet m)
    (hcritical :
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ)
    (x : ℝ) :
    (∑ k : Fin (m + 2),
      if p ∈ ginibreIncidenceChart ''
          ginibreIncidenceRankPieceBelow m k x then
        (-1 : ℝ) ^ k.val else 0) =
      ginibreAlternatingCount
        (realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x)) := by
  classical
  simp_rw [mem_ginibreIncidenceRankPieceBelow_image_iff_lt_belowCount
    p hboundary hcritical]
  apply sum_fin_ite_lt_eq_ginibreAlternatingCount
  have hle := realEigenvalueBelowCount_le
    (ginibreCoordinatesFinMatrix p, x)
  omega

end NumStability

end

noncomputable section

namespace NumStability

open Matrix MeasureTheory ProbabilityTheory Set Filter

open scoped BigOperators ENNReal RealInnerProductSpace Matrix.Norms.Frobenius

private local instance ginibreTruncatedMeasurableSpaceRSqMat (n : ℕ) :
    MeasurableSpace (RSqMat n) := MeasurableSpace.pi

private local instance ginibreTruncatedMeasureSpaceRSqMat (n : ℕ) :
    MeasureSpace (RSqMat n) := {
  toMeasurableSpace := MeasurableSpace.pi
  volume := realGinibreLebesgueMeasure n }

private local instance ginibreTruncatedStandardBorelNuisance (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceNuisance n) :=
  StandardBorelSpace.prod

private local instance ginibreTruncatedStandardBorelCoordinates (n : ℕ) :
    StandardBorelSpace (GinibreIncidenceCoordinates n) :=
  StandardBorelSpace.prod

/-- The image of a truncated regular rank sheet is measurable. -/
theorem measurableSet_ginibreIncidenceRankPieceBelow_image
    (m : ℕ) (k : Fin (m + 2)) (x : ℝ) :
    MeasurableSet (ginibreIncidenceChart ''
      ginibreIncidenceRankPieceBelow m k x) :=
  (measurableSet_ginibreIncidenceRankPieceBelow m k x).image_of_measurable_injOn
    measurable_ginibreIncidenceChart
    ((injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left)

/-- A signed truncated incidence transfer.  The alternating number of real
roots below `x` becomes the signed deflated determinant, integrated over
incidence points whose marked root lies below `x`. -/
theorem integral_ginibreAlternatingBelow_eq_signedIncidenceBelow
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (x : ℝ)
    (h : GinibreIncidenceCoordinates m → ℝ) (hh : Integrable h μ) :
    (∫ p,
      ginibreAlternatingCount
          (realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x)) *
        h p ∂μ) =
      ∫ q in {q | ginibreIncidenceEigenvalue q < x},
        (ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
          h (ginibreIncidenceChart q) ∂μ := by
  classical
  let image : Fin (m + 2) → Set (GinibreIncidenceCoordinates m) := fun k =>
    ginibreIncidenceChart '' ginibreIncidenceRankPieceBelow m k x
  let c : Fin (m + 2) → ℝ := fun k => (-1 : ℝ) ^ k.val
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      h (ginibreIncidenceChart q)
  have himageMeas (k : Fin (m + 2)) : MeasurableSet (image k) := by
    exact measurableSet_ginibreIncidenceRankPieceBelow_image m k x
  have himageInt (k : Fin (m + 2)) :
      Integrable ((image k).indicator (fun p => c k * h p)) μ :=
    (hh.const_mul (c k)).indicator (himageMeas k)
  have hsourceInt (k : Fin (m + 2)) : IntegrableOn f
      (ginibreIncidenceRankPieceBelow m k x) μ := by
    have htarget : IntegrableOn (fun p => c k * h p) (image k) μ :=
      (hh.const_mul (c k)).integrableOn
    have hsource :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        μ (measurableSet_ginibreIncidenceRankPieceBelow m k x)
        (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
        ((injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left)
        (fun p => c k * h p)).1 htarget
    refine hsource.congr_fun ?_
      (measurableSet_ginibreIncidenceRankPieceBelow m k x)
    intro q hq
    simp only [smul_eq_mul]
    change |(ginibreIncidenceDerivativeLinearMap q).det| *
        (c k * h (ginibreIncidenceChart q)) = f q
    have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1.1
    dsimp [c, f]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.1.2]
    calc
      |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            h (ginibreIncidenceChart q)) =
        ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
          |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
          h (ginibreIncidenceChart q) := by ring
      _ = _ := by rw [hsign]
  have hb : ∀ᵐ p ∂μ, p ∉ ginibreAffineBoundaryEigenpairSet m :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreAffineBoundaryEigenpairSet_eq_zero m μ)
  have hc : ∀ᵐ p ∂μ,
      p ∉ ginibreIncidenceChart '' (ginibreIncidenceRegularSet m)ᶜ :=
    measure_eq_zero_iff_ae_notMem.1
      (measure_ginibreIncidence_criticalImage_eq_zero m μ)
  have hbelowMeas : MeasurableSet
      {q : GinibreIncidenceCoordinates m | ginibreIncidenceEigenvalue q < x} :=
    measurableSet_lt measurable_ginibreIncidenceEigenvalue measurable_const
  calc
    (∫ p,
      ginibreAlternatingCount
          (realEigenvalueBelowCount (ginibreCoordinatesFinMatrix p, x)) *
        h p ∂μ) =
        ∫ p, ∑ k : Fin (m + 2),
          (image k).indicator (fun p => c k * h p) p ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb, hc] with p hbp hcp
      have hcollapse :=
        sum_ginibreIncidenceRankPieceBelow_image_sign_eq_alternatingCount
          p hbp hcp x
      dsimp [image, c]
      rw [← hcollapse, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hmem : p ∈ ginibreIncidenceChart ''
          ginibreIncidenceRankPieceBelow m k x
      · simp [hmem]
      · simp [hmem]
    _ = ∑ k : Fin (m + 2),
          ∫ p, (image k).indicator (fun p => c k * h p) p ∂μ := by
      exact integral_finset_sum Finset.univ (fun k hk => himageInt k)
    _ = ∑ k : Fin (m + 2),
          ∫ p in image k, c k * h p ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [integral_indicator (himageMeas k)]
    _ = ∑ k : Fin (m + 2),
          ∫ q in ginibreIncidenceRankPieceBelow m k x,
            |(ginibreIncidenceDerivativeLinearMap q).det| *
              (c k * h (ginibreIncidenceChart q)) ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      exact (integral_ginibreIncidence_rankPieceBelow_eq_image
        m μ k x (fun p => c k * h p)).symm
    _ = ∑ k : Fin (m + 2),
          ∫ q in ginibreIncidenceRankPieceBelow m k x, f q ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      apply setIntegral_congr_fun
        (measurableSet_ginibreIncidenceRankPieceBelow m k x)
      intro q hq
      have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1.1
      change |(ginibreIncidenceDerivativeLinearMap q).det| *
          (c k * h (ginibreIncidenceChart q)) = f q
      dsimp [c, f]
      rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.1.2]
      calc
        |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
            ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
              h (ginibreIncidenceChart q)) =
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            |(ginibreIncidenceDeflatedBlock q -
              ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
            h (ginibreIncidenceChart q) := by ring
        _ = _ := by rw [hsign]
    _ = ∫ q in ginibreIncidenceRegularSet m ∩
          {q | ginibreIncidenceEigenvalue q < x}, f q ∂μ := by
      rw [← iUnion_ginibreIncidenceRankPieceBelow]
      symm
      rw [integral_iUnion
        (fun k => measurableSet_ginibreIncidenceRankPieceBelow m k x)
        (pairwiseDisjoint_ginibreIncidenceRankPieceBelow m x)]
      · rw [tsum_fintype]
      · exact integrableOn_iUnion_of_summable_integral_norm
          hsourceInt ((hasSum_fintype (fun k : Fin (m + 2) =>
            ∫ q in ginibreIncidenceRankPieceBelow m k x, ‖f q‖ ∂μ) _).summable)
    _ = ∫ q in {q | ginibreIncidenceEigenvalue q < x}, f q ∂μ := by
      rw [← integral_indicator hbelowMeas,
        ← integral_indicator
          ((measurableSet_ginibreIncidenceRegularSet m).inter hbelowMeas)]
      apply integral_congr_ae
      filter_upwards with q
      by_cases hreg : q ∈ ginibreIncidenceRegularSet m
      · by_cases hlt : ginibreIncidenceEigenvalue q < x
        · simp [hreg, hlt]
        · simp [hreg, hlt]
      · have htan : (ginibreIncidenceTangentMatrix q).det = 0 := by
          simpa [ginibreIncidenceRegularSet] using hreg
        have hdet : (ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det = 0 := by
          have hneg : ginibreIncidenceDeflatedBlock q -
              ginibreIncidenceEigenvalue q • (1 : RSqMat m) =
              -(ginibreIncidenceTangentMatrix q) := by
            unfold ginibreIncidenceTangentMatrix
            abel
          rw [hneg, Matrix.det_neg, htan, mul_zero]
        by_cases hlt : ginibreIncidenceEigenvalue q < x
        · simp [hreg, hlt, f, hdet]
        · simp [hreg, hlt]
    _ = _ := rfl

/-- Integrability companion to the truncated signed-incidence identity. -/
theorem integrableOn_ginibreSignedIncidenceBelow
    (m : ℕ) (μ : Measure (GinibreIncidenceCoordinates m))
    [μ.IsAddHaarMeasure] (x : ℝ)
    (h : GinibreIncidenceCoordinates m → ℝ) (hh : Integrable h μ) :
    IntegrableOn (fun q : GinibreIncidenceCoordinates m =>
      (ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
        h (ginibreIncidenceChart q))
      {q | ginibreIncidenceEigenvalue q < x} μ := by
  classical
  let f : GinibreIncidenceCoordinates m → ℝ := fun q =>
    (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det *
      h (ginibreIncidenceChart q)
  have hsourceInt (k : Fin (m + 2)) : IntegrableOn f
      (ginibreIncidenceRankPieceBelow m k x) μ := by
    let c : ℝ := (-1 : ℝ) ^ k.val
    let image : Set (GinibreIncidenceCoordinates m) :=
      ginibreIncidenceChart '' ginibreIncidenceRankPieceBelow m k x
    have htarget : IntegrableOn (fun p => c * h p) image μ :=
      (hh.const_mul c).integrableOn
    have hsource :=
      (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul
        μ (measurableSet_ginibreIncidenceRankPieceBelow m k x)
        (fun q hq => (hasFDerivAt_ginibreIncidenceChart q).hasFDerivWithinAt)
        ((injOn_ginibreIncidenceChart_rankPiece m k).mono inter_subset_left)
        (fun p => c * h p)).1 htarget
    refine hsource.congr_fun ?_
      (measurableSet_ginibreIncidenceRankPieceBelow m k x)
    intro q hq
    simp only [smul_eq_mul]
    change |(ginibreIncidenceDerivativeLinearMap q).det| *
        (c * h (ginibreIncidenceChart q)) = f q
    have hsign := neg_one_pow_rootRank_mul_abs_det q hq.1.1
    dsimp [c, f]
    rw [abs_ginibreIncidenceDerivativeLinearMap_det, ← hq.1.2]
    calc
      |(ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det| *
          ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
            h (ginibreIncidenceChart q)) =
        ((-1 : ℝ) ^ ginibreIncidenceRootRank q *
          |(ginibreIncidenceDeflatedBlock q -
            ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det|) *
          h (ginibreIncidenceChart q) := by ring
      _ = _ := by rw [hsign]
  have hregBelow : IntegrableOn f
      (ginibreIncidenceRegularSet m ∩
        {q | ginibreIncidenceEigenvalue q < x}) μ := by
    rw [← iUnion_ginibreIncidenceRankPieceBelow]
    exact integrableOn_iUnion_of_summable_integral_norm
      hsourceInt ((hasSum_fintype (fun k : Fin (m + 2) =>
        ∫ q in ginibreIncidenceRankPieceBelow m k x, ‖f q‖ ∂μ) _).summable)
  have hcomp : IntegrableOn f (ginibreIncidenceRegularSet m)ᶜ μ := by
    have hz : IntegrableOn
        (fun _q : GinibreIncidenceCoordinates m => (0 : ℝ))
        (ginibreIncidenceRegularSet m)ᶜ μ :=
      (integrable_zero (GinibreIncidenceCoordinates m) ℝ μ).integrableOn
    refine hz.congr_fun ?_
      (measurableSet_ginibreIncidenceRegularSet m).compl
    intro q hq
    have htan : (ginibreIncidenceTangentMatrix q).det = 0 := by
      simpa [ginibreIncidenceRegularSet] using hq
    have hdet : (ginibreIncidenceDeflatedBlock q -
        ginibreIncidenceEigenvalue q • (1 : RSqMat m)).det = 0 := by
      have hneg : ginibreIncidenceDeflatedBlock q -
          ginibreIncidenceEigenvalue q • (1 : RSqMat m) =
          -(ginibreIncidenceTangentMatrix q) := by
        unfold ginibreIncidenceTangentMatrix
        abel
      rw [hneg, Matrix.det_neg, htan, mul_zero]
    simp [f, hdet]
  have hall := hregBelow.union hcomp
  apply hall.mono_set
  intro q hq
  by_cases hreg : q ∈ ginibreIncidenceRegularSet m
  · exact Or.inl ⟨hreg, hq⟩
  · exact Or.inr hreg

end NumStability

end
