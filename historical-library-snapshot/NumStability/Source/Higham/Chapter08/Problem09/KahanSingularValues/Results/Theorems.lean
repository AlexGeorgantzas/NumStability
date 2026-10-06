-- NumStability/Source/Higham/Chapter08/Problem09/KahanSingularValues/Results/Theorems.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Split component of a mixed/multi-destination owner.
-- Historical owner: `NumStability.Algorithms.HighamChapter8`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Order.Interval.Finset.Fin
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LinearSystems.Triangular
import NumStability.Algorithms.MMatrix
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder
import NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.All
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ConditionNumbers
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.ForwardErrorKernels
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem05
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem09Exact
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem04
import NumStability.Source.Higham.Chapter08.Equation14.FanInExecutor.Executor
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic
import NumStability.Source.Higham.Chapter08.Problem01.NoGuardSubstitution.Aliases
import NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.RatioWitness
import NumStability.Source.Higham.Chapter08.Problem03.UnitTriangularSubstitution.Bound
import NumStability.Source.Higham.Chapter08.Problem04.MMatrixSubstitution.Comparison
import NumStability.Source.Higham.Chapter08.Problem05.InverseNormBounds.ZInverse
import NumStability.Source.Higham.Chapter08.Problem06.ComparisonInverseBounds.VectorBounds
import NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Bounds
import NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.RankOne
import NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.KahanMatrix
import NumStability.Source.Higham.Chapter08.Section01.BackwardErrorAnalysis.Core
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBounds
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.ComparisonBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section02.ForwardErrorAnalysis.NormBounds
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsLower
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsPrelude
import NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseBoundsUpper
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.AllOrdersEnvelope
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.Factors
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds

/-!
# Theorems

Relocated from `NumStability.Algorithms.HighamChapter8` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Algorithms/HighamChapter8.lean
--
-- Source-facing entry points for Higham Chapter 8, "Triangular Systems".
-- The detailed proofs remain in the focused triangular-system modules; this
-- file provides stable chapter labels and light wrappers around those results.















namespace NumStability

open scoped BigOperators

/-! ## §8.1 Backward Error Analysis -/

















































































































/-! ## §8.2 Forward Error Analysis -/












































































































































































































































/-! ## §8.3 Kahan's triangular example -/






















































































































private noncomputable def higham8_problem8_9_svdTopSpan
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ
    (Set.range (fun i : {i : Fin n // i ≤ k} =>
      complexMatrixGramEigenvectorBasis A i.1))


private noncomputable def higham8_problem8_9_svdTailSpan
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin n)) :=
  Submodule.span ℂ
    (Set.range (fun i : {i : Fin n // k ≤ i} =>
      complexMatrixGramEigenvectorBasis A i.1))


private theorem higham8_problem8_9_svdTopSpan_finrank
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Module.finrank ℂ (↥(higham8_problem8_9_svdTopSpan A k)) = k.val + 1 := by
  rw [higham8_problem8_9_svdTopSpan]
  rw [finrank_span_eq_card]
  · convert (Fintype.card_Iic k).trans (Fin.card_Iic k) using 2
  · exact (complexMatrixGramEigenvectorBasis A).toBasis.linearIndependent.comp
      (fun i : {i : Fin n // i ≤ k} => (i : Fin n))
      (Subtype.val_injective)


private theorem higham8_problem8_9_svdTailSpan_finrank
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Module.finrank ℂ (↥(higham8_problem8_9_svdTailSpan A k)) = n - k.val := by
  rw [higham8_problem8_9_svdTailSpan]
  rw [finrank_span_eq_card]
  · convert (Fintype.card_Ici k).trans (Fin.card_Ici k) using 2
  · exact (complexMatrixGramEigenvectorBasis A).toBasis.linearIndependent.comp
      (fun i : {i : Fin n // k ≤ i} => (i : Fin n))
      (Subtype.val_injective)


private theorem higham8_problem8_9_svdTopSpan_repr_eq_zero_of_lt
    {n : ℕ} (A : CMatrix n n) (k j : Fin n)
    {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTopSpan A k) (hkj : k < j) :
    (complexMatrixGramEigenvectorBasis A).repr x j = 0 := by
  rw [higham8_problem8_9_svdTopSpan] at hx
  refine Submodule.span_induction
    (s := Set.range (fun i : {i : Fin n // i ≤ k} =>
      complexMatrixGramEigenvectorBasis A i.1))
    ?mem ?zero ?add ?smul hx
  · rintro y ⟨i, rfl⟩
    have hji : j ≠ (i : Fin n) := by
      intro h
      subst j
      exact not_lt_of_ge i.2 hkj
    simp [OrthonormalBasis.repr_self, hji]
  · simp
  · intro x y hx hy hx0 hy0
    simp [map_add, hx0, hy0]
  · intro a x hx hx0
    simp [map_smul, hx0]


private theorem higham8_problem8_9_svdTailSpan_repr_eq_zero_of_lt
    {n : ℕ} (A : CMatrix n n) (k j : Fin n)
    {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTailSpan A k) (hjk : j < k) :
    (complexMatrixGramEigenvectorBasis A).repr x j = 0 := by
  rw [higham8_problem8_9_svdTailSpan] at hx
  refine Submodule.span_induction
    (s := Set.range (fun i : {i : Fin n // k ≤ i} =>
      complexMatrixGramEigenvectorBasis A i.1))
    ?mem ?zero ?add ?smul hx
  · rintro y ⟨i, rfl⟩
    have hji : j ≠ (i : Fin n) := by
      intro h
      subst j
      exact not_lt_of_ge i.2 hjk
    simp [OrthonormalBasis.repr_self, hji]
  · simp
  · intro x y hx hy hx0 hy0
    simp [map_add, hx0, hy0]
  · intro a x hx hx0
    simp [map_smul, hx0]


private theorem higham8_problem8_9_matrix_toEuclideanLin_ofLp
    {m n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    WithLp.ofLp (Matrix.toEuclideanLin A x) =
      Matrix.toLin' A (WithLp.ofLp x) := by
  change WithLp.ofLp (((Matrix.toLpLin (2 : ENNReal) (2 : ENNReal)) A) x) =
    Matrix.toLin' A (WithLp.ofLp x)
  exact Matrix.ofLp_toLpLin (2 : ENNReal) (2 : ENNReal) A x


private theorem higham8_problem8_9_norm_sq_eq_sum
    {n : ℕ} (A : CMatrix n n) (z : EuclideanSpace ℂ (Fin n)) :
    ‖complexMatrixEuclideanLin A z‖ ^ 2 =
      ∑ i : Fin n,
        complexMatrixSingularValue A i ^ 2 *
          ‖(complexMatrixGramEigenvectorBasis A).repr z i‖ ^ 2 := by
  classical
  obtain ⟨b, hcontains⟩ :=
    exists_complexMatrixLeftSingularVector_fin_orthonormalBasis_extension A
  let q : Equiv.Perm (Fin n) := complexMatrixLeftSingularVectorBasisPerm A b hcontains
  let coeff : EuclideanSpace ℂ (Fin n) := (complexMatrixGramEigenvectorBasis A).repr z
  have hcoord :
      Matrix.mulVec (highamProblem65MonomialMatrix q
          (fun i => (complexMatrixSingularValue A i : ℂ))) coeff =
        b.repr (complexMatrixEuclideanLin A z) := by
    have h := complexMatrixSVDFinDiagonalCoordinateMatrix_mulVec_repr A b hcontains z
    rw [complexMatrixSVDFinDiagonalCoordinateMatrix_eq_monomial_basisPerm A b hcontains] at h
    simpa [q, coeff] using h
  have hcoord_lift :
      (WithLp.toLp (2 : ENNReal)
        (Matrix.mulVec (highamProblem65MonomialMatrix q
          (fun i => (complexMatrixSingularValue A i : ℂ)))
          (WithLp.ofLp coeff)) : EuclideanSpace ℂ (Fin n)) =
        b.repr (complexMatrixEuclideanLin A z) := by
    apply WithLp.ofLp_injective
    simpa [q, coeff] using hcoord
  have hnorm_repr :
      ‖b.repr (complexMatrixEuclideanLin A z)‖ =
        ‖complexMatrixEuclideanLin A z‖ :=
    LinearIsometryEquiv.norm_map b.repr (complexMatrixEuclideanLin A z)
  rw [← hnorm_repr, ← hcoord_lift]
  exact ch7Problem75_monomial_mulVec_norm_sq_eq_sum q
    (fun i => complexMatrixSingularValue A i) coeff


private theorem higham8_problem8_9_topSpan_sigma_mul_norm_le
    {n : ℕ} (A : CMatrix n n) (k : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTopSpan A k) :
    complexMatrixSingularValue A k * ‖x‖ ≤ ‖complexMatrixEuclideanLin A x‖ := by
  apply (sq_le_sq₀
    (mul_nonneg (complexMatrixSingularValue_nonneg A k) (norm_nonneg x))
    (norm_nonneg (complexMatrixEuclideanLin A x))).mp
  rw [mul_pow, higham8_problem8_9_norm_sq_eq_sum]
  calc
    complexMatrixSingularValue A k ^ 2 * ‖x‖ ^ 2
        = ∑ i : Fin n,
            complexMatrixSingularValue A k ^ 2 *
              ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
          rw [← ch7Problem75_orthonormalBasis_repr_norm_sq
            (complexMatrixGramEigenvectorBasis A) x]
          rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin n,
        complexMatrixSingularValue A i ^ 2 *
          ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          by_cases hki : k < i
          · have hzero :=
              higham8_problem8_9_svdTopSpan_repr_eq_zero_of_lt A k i hx hki
            simp [hzero]
          · have hik : i ≤ k := le_of_not_gt hki
            exact mul_le_mul_of_nonneg_right
              ((sq_le_sq₀ (complexMatrixSingularValue_nonneg A k)
                (complexMatrixSingularValue_nonneg A i)).mpr
                (complexMatrixSingularValue_antitone A hik))
              (sq_nonneg _)


private theorem higham8_problem8_9_tailSpan_norm_image_le_sigma_mul_norm
    {n : ℕ} (A : CMatrix n n) (k : Fin n) {x : EuclideanSpace ℂ (Fin n)}
    (hx : x ∈ higham8_problem8_9_svdTailSpan A k) :
    ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A k * ‖x‖ := by
  apply (sq_le_sq₀
    (norm_nonneg (complexMatrixEuclideanLin A x))
    (mul_nonneg (complexMatrixSingularValue_nonneg A k) (norm_nonneg x))).mp
  rw [mul_pow, higham8_problem8_9_norm_sq_eq_sum]
  calc
    (∑ i : Fin n,
        complexMatrixSingularValue A i ^ 2 *
          ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2)
        ≤ ∑ i : Fin n,
            complexMatrixSingularValue A k ^ 2 *
              ‖(complexMatrixGramEigenvectorBasis A).repr x i‖ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          by_cases hik : i < k
          · have hzero :=
              higham8_problem8_9_svdTailSpan_repr_eq_zero_of_lt A k i hx hik
            simp [hzero]
          · have hki : k ≤ i := le_of_not_gt hik
            exact mul_le_mul_of_nonneg_right
              ((sq_le_sq₀ (complexMatrixSingularValue_nonneg A i)
                (complexMatrixSingularValue_nonneg A k)).mpr
                (complexMatrixSingularValue_antitone A hki))
              (sq_nonneg _)
    _ = complexMatrixSingularValue A k ^ 2 * ‖x‖ ^ 2 := by
          rw [← Finset.mul_sum]
          rw [ch7Problem75_orthonormalBasis_repr_norm_sq]


private noncomputable def higham8_problem8_9_embedLastZero (n : ℕ) :
    EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin (n + 1)) where
  toFun x := WithLp.toLp (2 : ENNReal)
    (fun i : Fin (n + 1) => if h : i.val < n then WithLp.ofLp x ⟨i.val, h⟩ else 0)
  map_add' x y := by
    apply WithLp.ofLp_injective
    ext i
    by_cases h : i.val < n <;> simp [h]
  map_smul' a x := by
    apply WithLp.ofLp_injective
    ext i
    by_cases h : i.val < n <;> simp [h]


@[simp] private theorem higham8_problem8_9_embedLastZero_apply_castSucc
    (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) (i : Fin n) :
    higham8_problem8_9_embedLastZero n x i.castSucc = x i := by
  simp [higham8_problem8_9_embedLastZero]


@[simp] private theorem higham8_problem8_9_embedLastZero_apply_last
    (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    higham8_problem8_9_embedLastZero n x (Fin.last n) = 0 := by
  simp [higham8_problem8_9_embedLastZero]


private theorem higham8_problem8_9_embedLastZero_norm
    (n : ℕ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖higham8_problem8_9_embedLastZero n x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [Fin.sum_univ_castSucc]
  simp [higham8_problem8_9_embedLastZero]


private theorem higham8_problem8_9_embedLastZero_injective (n : ℕ) :
    Function.Injective (higham8_problem8_9_embedLastZero n) := by
  intro x y hxy
  apply WithLp.ofLp_injective
  ext i
  have hcoord :=
    congrArg (fun z : EuclideanSpace ℂ (Fin (n + 1)) => z i.castSucc) hxy
  simpa using hcoord


private theorem higham8_problem8_9_kahan_euclideanLin_embed
    (n : ℕ) (c s : ℝ) (x : EuclideanSpace ℂ (Fin n)) :
    complexMatrixEuclideanLin
        (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (higham8_problem8_9_embedLastZero n x) =
      higham8_problem8_9_embedLastZero n
        (complexMatrixEuclideanLin
          (realRectToCMatrix (higham8_11_kahanMatrix n c s)) x) := by
  apply WithLp.ofLp_injective
  ext r
  refine Fin.lastCases ?last ?cast r
  · simp only [complexMatrixEuclideanLin]
    rw [higham8_problem8_9_matrix_toEuclideanLin_ofLp]
    change Matrix.toLin' (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (WithLp.ofLp ((higham8_problem8_9_embedLastZero n) x)) (Fin.last n) =
      WithLp.ofLp ((higham8_problem8_9_embedLastZero n)
        ((complexMatrixEuclideanLin
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))) x)) (Fin.last n)
    rw [Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    rw [Fin.sum_univ_castSucc]
    simp [higham8_problem8_9_embedLastZero]
    apply Finset.sum_eq_zero
    intro j _hj
    have hne : Fin.last n ≠ j.castSucc := (Fin.castSucc_ne_last j).symm
    have hnlt : ¬ n < j.val := by omega
    simp [realRectToCMatrix, higham8_11_kahanMatrix, higham8_3_stressUpper, hne, hnlt]
  · intro i
    simp only [complexMatrixEuclideanLin]
    rw [higham8_problem8_9_matrix_toEuclideanLin_ofLp]
    change Matrix.toLin' (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (WithLp.ofLp ((higham8_problem8_9_embedLastZero n) x)) i.castSucc =
      WithLp.ofLp ((higham8_problem8_9_embedLastZero n)
        ((complexMatrixEuclideanLin
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))) x)) i.castSucc
    rw [Matrix.toLin'_apply]
    unfold Matrix.mulVec dotProduct
    rw [Fin.sum_univ_castSucc]
    simp [higham8_problem8_9_embedLastZero, realRectToCMatrix,
      higham8_11_kahanMatrix_leadingBlock_succ]
    rfl


private noncomputable def higham8_problem8_9_embeddedTopSpan
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (n + 1))) :=
  LinearMap.range
    ((higham8_problem8_9_embedLastZero n).comp
      (higham8_problem8_9_svdTopSpan A k).subtype)


private theorem higham8_problem8_9_embeddedTopSpan_finrank
    {n : ℕ} (A : CMatrix n n) (k : Fin n) :
    Module.finrank ℂ (↥(higham8_problem8_9_embeddedTopSpan A k)) = k.val + 1 := by
  rw [higham8_problem8_9_embeddedTopSpan]
  rw [LinearMap.finrank_range_of_inj]
  · exact higham8_problem8_9_svdTopSpan_finrank A k
  · intro x y hxy
    apply Subtype.ext
    exact higham8_problem8_9_embedLastZero_injective n hxy


private theorem higham8_problem8_9_subspace_intersection_nonzero
    {N dS dT : ℕ}
    (S T : Submodule ℂ (EuclideanSpace ℂ (Fin N)))
    (hS : Module.finrank ℂ (↥S) = dS)
    (hT : Module.finrank ℂ (↥T) = dT)
    (hsum : N < dS + dT) :
    ∃ x : EuclideanSpace ℂ (Fin N), x ∈ S ∧ x ∈ T ∧ x ≠ 0 := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S T
  have hsup_le : Module.finrank ℂ (↥(S ⊔ T)) ≤ N := by
    calc
      Module.finrank ℂ (↥(S ⊔ T)) ≤
          Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) :=
        Submodule.finrank_le (S ⊔ T)
      _ = N := finrank_euclideanSpace_fin
  have hinf_pos : 0 < Module.finrank ℂ (↥(S ⊓ T)) := by
    rw [hS, hT] at hdim
    omega
  have hne : S ⊓ T ≠ ⊥ := by
    intro hbot
    have hfin : Module.finrank ℂ (↥(S ⊓ T)) = 0 := by
      rw [hbot, finrank_bot]
    omega
  obtain ⟨x, hx, hxne⟩ := (Submodule.ne_bot_iff (S ⊓ T)).1 hne
  rw [Submodule.mem_inf] at hx
  exact ⟨x, hx.1, hx.2, hxne⟩


private theorem higham8_problem8_9_kahanSingularValue_interlace_succ
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) ≤
      complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega)) := by
  classical
  let B : CMatrix n n := realRectToCMatrix (higham8_11_kahanMatrix n c s)
  let A : CMatrix (n + 1) (n + 1) :=
    realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s)
  let k := higham8_problem8_9_secondSmallestIndex n h2
  let r := higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega : 3 ≤ n + 1)
  by_contra hnot
  have hlt : complexMatrixSingularValue A r < complexMatrixSingularValue B k :=
    lt_of_not_ge hnot
  let S := higham8_problem8_9_embeddedTopSpan B k
  let T := higham8_problem8_9_svdTailSpan A r
  have hSdim : Module.finrank ℂ (↥S) = n - 1 := by
    have hkval : k.val + 1 = n - 1 := by
      simp [k, higham8_problem8_9_secondSmallestIndex]
      omega
    rw [higham8_problem8_9_embeddedTopSpan_finrank B k, hkval]
  have hTdim : Module.finrank ℂ (↥T) = 3 := by
    have hrval : (n + 1) - r.val = 3 := by
      simp [r, higham8_problem8_9_thirdSmallestIndex]
      omega
    rw [higham8_problem8_9_svdTailSpan_finrank A r, hrval]
  obtain ⟨x, hxS, hxT, hxne⟩ :=
    higham8_problem8_9_subspace_intersection_nonzero S T hSdim hTdim (by omega)
  rcases hxS with ⟨yTop, hyEq⟩
  let y : EuclideanSpace ℂ (Fin n) := yTop
  have hyTop : y ∈ higham8_problem8_9_svdTopSpan B k := yTop.property
  have hxy : higham8_problem8_9_embedLastZero n y = x := by
    simpa [S, higham8_problem8_9_embeddedTopSpan, y] using hyEq
  have hyne : y ≠ 0 := by
    intro hy0
    apply hxne
    rw [← hxy, hy0]
    simp
  have hynorm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hyne
  have hlower : complexMatrixSingularValue B k * ‖y‖ ≤
      ‖complexMatrixEuclideanLin B y‖ :=
    higham8_problem8_9_topSpan_sigma_mul_norm_le B k hyTop
  have haction :
      ‖complexMatrixEuclideanLin A (higham8_problem8_9_embedLastZero n y)‖ =
        ‖complexMatrixEuclideanLin B y‖ := by
    rw [higham8_problem8_9_kahan_euclideanLin_embed]
    exact higham8_problem8_9_embedLastZero_norm n (complexMatrixEuclideanLin B y)
  have hupper_x :
      ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A r * ‖x‖ :=
    higham8_problem8_9_tailSpan_norm_image_le_sigma_mul_norm A r hxT
  have hupper :
      ‖complexMatrixEuclideanLin B y‖ ≤ complexMatrixSingularValue A r * ‖y‖ := by
    rw [← haction, hxy]
    calc
      ‖complexMatrixEuclideanLin A x‖ ≤ complexMatrixSingularValue A r * ‖x‖ :=
        hupper_x
      _ = complexMatrixSingularValue A r * ‖y‖ := by
            rw [← hxy, higham8_problem8_9_embedLastZero_norm]
  have hle_mul : complexMatrixSingularValue B k * ‖y‖ ≤
      complexMatrixSingularValue A r * ‖y‖ := hlower.trans hupper
  have hlt_mul : complexMatrixSingularValue A r * ‖y‖ <
      complexMatrixSingularValue B k * ‖y‖ :=
    mul_lt_mul_of_pos_right hlt hynorm_pos
  exact not_lt_of_ge hle_mul hlt_mul


private theorem higham8_problem8_9_kahanGram_interlace_succ
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) ≤
      complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
        (higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega)) := by
  have hsing := higham8_problem8_9_kahanSingularValue_interlace_succ n h2 c s
  have hsq := (sq_le_sq₀
    (complexMatrixSingularValue_nonneg
      (realRectToCMatrix (higham8_11_kahanMatrix n c s))
      (higham8_problem8_9_secondSmallestIndex n h2))
    (complexMatrixSingularValue_nonneg
      (realRectToCMatrix (higham8_11_kahanMatrix (n + 1) c s))
      (higham8_problem8_9_thirdSmallestIndex (n + 1) (by omega)))).mpr hsing
  rw [complexMatrixSingularValue_sq, complexMatrixSingularValue_sq] at hsq
  exact hsq


/-- **Problem 8.9**, Kahan-specific leading-block interlacing step.

This is the ordered Gram-eigenvalue inequality used by Appendix A's induction:
the previous-size second-smallest Gram eigenvalue is bounded by the current
third-smallest Gram eigenvalue.  The proof uses the right singular-vector
top span for the leading block, the tail span for the current matrix, and a
dimension-count intersection after embedding the leading block by appending
one zero coordinate. -/
theorem higham8_problem8_9_kahanGram_interlacing (c s : ℝ) :
    ∀ (m : ℕ) (hm : 3 ≤ m),
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
          (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix m c s))
          (higham8_problem8_9_thirdSmallestIndex m hm) := by
  intro m hm
  rcases m with _ | _ | _ | k
  · omega
  · omega
  · omega
  · have h := higham8_problem8_9_kahanGram_interlace_succ (k + 2) (by omega) c s
    simpa [Nat.add_assoc] using h


private theorem higham8_complexMatrixGramLin_eq_smul_id_of_conjTranspose_mul_self_scalar
    {n : ℕ} (A : CMatrix n n) (lam : ℂ)
    (hA : (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
      (lam • (1 : Matrix (Fin n) (Fin n) ℂ))) :
    complexMatrixGramLin A =
      lam •
        (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)) := by
  let b := complexEuclideanBasisFin n
  rw [← Matrix.toLin_toMatrix b b (complexMatrixGramLin A)]
  rw [← Matrix.toLin_toMatrix b b
    (lam •
      (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))]
  congr 1
  rw [complexMatrixGramLin_toMatrix, hA]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply]
  · simp [LinearMap.toMatrix_apply, hij]


private theorem higham8_complexMatrixGramEigenvalues_eq_of_gramLin_eq_smul_id
    {m n : ℕ} (A : CMatrix m n) {lam : ℝ}
    (h :
      complexMatrixGramLin A =
        ((lam : ℂ) •
          (LinearMap.id : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)))) :
    ∀ i : Fin n, complexMatrixGramEigenvalues A i = lam := by
  intro i
  let b := complexMatrixGramEigenvectorBasis A
  let v : EuclideanSpace ℂ (Fin n) := b i
  have heig := complexMatrixGramLin_apply_eigenvectorBasis A i
  have hsmul : ((lam : ℂ) • v) = (complexMatrixGramEigenvalues A i : ℂ) • v := by
    simpa [v, b, h, LinearMap.smul_apply] using heig
  have hv_ne : v ≠ 0 := by
    intro hv
    have hvn : ‖v‖ = 1 := by
      simp [v, b, complexMatrixGramEigenvectorBasis_norm A i]
    simp [hv] at hvn
  have hzero : (((lam : ℂ) - (complexMatrixGramEigenvalues A i : ℂ)) • v) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact hsmul
  have hscalar : (lam : ℂ) - (complexMatrixGramEigenvalues A i : ℂ) = 0 := by
    exact (smul_eq_zero.mp hzero).resolve_right hv_ne
  apply Complex.ofReal_injective
  exact (sub_eq_zero.mp hscalar).symm










theorem higham8_problem8_9_kahan_zero_one_gramEigenvalues_eq_one
    (n : ℕ) :
    ∀ i : Fin n,
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n 0 1)) i = 1 := by
  apply higham8_complexMatrixGramEigenvalues_eq_of_gramLin_eq_smul_id
  apply higham8_complexMatrixGramLin_eq_smul_id_of_conjTranspose_mul_self_scalar
  have hA :
      complexCMatrixAsMatrix (realRectToCMatrix (higham8_11_kahanMatrix n 0 1)) =
        (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [higham8_11_kahanMatrix_zero_one_eq_finiteId n]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [complexCMatrixAsMatrix, realRectToCMatrix, finiteIdMatrix]
    · simp [complexCMatrixAsMatrix, realRectToCMatrix, finiteIdMatrix, hij]
  rw [hA]
  simp


theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_one
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hcs : c ^ 2 + s ^ 2 = 1) (hs_one : s = 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  subst s
  have hc_sq : c ^ 2 = 0 := by nlinarith
  have hc_zero : c = 0 := sq_eq_zero_iff.mp hc_sq
  subst c
  have hgram :=
    higham8_problem8_9_kahan_zero_one_gramEigenvalues_eq_one n
      (higham8_problem8_9_secondSmallestIndex n h2)
  simpa using hgram


























theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) (hs_one : s = 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc
  · rw [hs_one]
    norm_num
  · exact
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_one
        n h2 c s hcs hs_one



































































































































































































































private theorem higham8_sum_two_support {n : ℕ}
    (p q : Fin n) (hpq : p ≠ q) (f : Fin n → ℝ) (a b : ℝ) :
    (∑ j : Fin n, f j * (if j = p then a else if j = q then b else 0)) =
      f p * a + f q * b := by
  calc
    (∑ j : Fin n, f j * (if j = p then a else if j = q then b else 0)) =
        ∑ j : Fin n,
          ((if j = p then f j * a else 0) + (if j = q then f j * b else 0)) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hjp : j = p
          · simp [hjp, hpq]
          · by_cases hjq : j = q
            · have hqp : q ≠ p := by
                intro h
                exact hpq h.symm
              simp [hjq, hqp]
            · simp [hjp, hjq]
    _ = (∑ j : Fin n, if j = p then f j * a else 0) +
          (∑ j : Fin n, if j = q then f j * b else 0) := by
          rw [Finset.sum_add_distrib]
    _ = f p * a + f q * b := by
          rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']


/-- **Problem 8.9**, Appendix A forward witness equation:
`U_n(θ) v = s^(n-2) sqrt(1+c) u`, using the scaled witness vectors above. -/
theorem higham8_problem8_9_kahan_witness_forward
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ) :
    matMulVec n (higham8_11_kahanMatrix n c s)
        (higham8_problem8_9_kahanRightWitness n h2 c) =
      fun i =>
        s ^ (n - 2) * Real.sqrt (1 + c) *
          higham8_problem8_9_kahanLeftWitness n h2 c s i := by
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    simp [p, q, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex] at hval
    omega
  have hpval : p.val = n - 2 := rfl
  have hqval : q.val = n - 1 := rfl
  have hqpow : s ^ q.val = s ^ (n - 2) * s := by
    rw [hqval]
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hpow_nm1 : s ^ (n - 1) = s ^ (n - 2) * s := by
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hnm2_ne_nm1 : n - 2 ≠ n - 1 := by omega
  have hnm1_ne_nm2 : n - 1 ≠ n - 2 := by omega
  have hnm2_lt_nm1 : n - 2 < n - 1 := by omega
  have hnot_nm1_lt_nm2 : ¬ n - 1 < n - 2 := by omega
  have hp_lt_q : p < q := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hq_ne_p : q ≠ p := hpq.symm
  have hnot_q_lt_p : ¬ q < p := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hright :
      higham8_problem8_9_kahanRightWitness n h2 c =
        fun j =>
          if j = p then Real.sqrt (1 + c)
          else if j = q then -Real.sqrt (1 + c)
          else 0 := by
    ext j
    simp [higham8_problem8_9_kahanRightWitness, p, q]
  ext i
  unfold matMulVec
  rw [hright]
  rw [higham8_sum_two_support p q hpq]
  by_cases hip : i = p
  · subst i
    simp [higham8_problem8_9_kahanLeftWitness, higham8_11_kahanMatrix,
      higham8_3_stressUpper, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex, p, q, hnm2_ne_nm1, hnm2_lt_nm1]
    ring_nf
  · by_cases hiq : i = q
    · subst i
      simp [higham8_problem8_9_kahanLeftWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, higham8_problem8_9_secondSmallestIndex,
        higham8_problem8_9_lastIndex, p, q, hnm1_ne_nm2, hnot_nm1_lt_nm2]
      rw [hpow_nm1]
      ring_nf
    · have hip_lt : i.val < p.val := by
        have hi_ne_p : i.val ≠ n - 2 := by
          intro hval
          exact hip (Fin.ext (by simpa [p, hpval] using hval))
        have hi_ne_q : i.val ≠ n - 1 := by
          intro hval
          exact hiq (Fin.ext (by simpa [q, hqval] using hval))
        have hi_bound : i.val < n := i.isLt
        omega
      have hi_ne_p : i ≠ p := hip
      have hi_ne_q : i ≠ q := hiq
      have hi_lt_q : i < q := by
        rw [Fin.lt_def]
        rw [hqval]
        omega
      simp [higham8_problem8_9_kahanLeftWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, p, q, hi_ne_p, hi_ne_q, hip_lt, hi_lt_q]


/-- **Problem 8.9**, Appendix A transpose witness equation:
`U_n(θ)^T u = s^(n-2) sqrt(1+c) v`, using the scaled witness vectors above. -/
theorem higham8_problem8_9_kahan_witness_transpose
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    matMulVec n (matTranspose (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_kahanLeftWitness n h2 c s) =
      fun i =>
        s ^ (n - 2) * Real.sqrt (1 + c) *
          higham8_problem8_9_kahanRightWitness n h2 c i := by
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  have hpq : p ≠ q := by
    intro h
    have hval := congrArg Fin.val h
    simp [p, q, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex] at hval
    omega
  have hpval : p.val = n - 2 := rfl
  have hqval : q.val = n - 1 := rfl
  have hqpow : s ^ q.val = s ^ (n - 2) * s := by
    rw [hqval]
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hpow_nm1 : s ^ (n - 1) = s ^ (n - 2) * s := by
    have hidx : n - 1 = n - 2 + 1 := by omega
    rw [hidx, pow_succ]
  have hnm2_ne_nm1 : n - 2 ≠ n - 1 := by omega
  have hnm1_ne_nm2 : n - 1 ≠ n - 2 := by omega
  have hnm2_lt_nm1 : n - 2 < n - 1 := by omega
  have hnot_nm1_lt_nm2 : ¬ n - 1 < n - 2 := by omega
  have hp_lt_q : p < q := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hq_ne_p : q ≠ p := hpq.symm
  have hnot_q_lt_p : ¬ q < p := by
    rw [Fin.lt_def, hpval, hqval]
    omega
  have hleft :
      higham8_problem8_9_kahanLeftWitness n h2 c s =
        fun j =>
          if j = p then 1 + c
          else if j = q then -s
          else 0 := by
    ext j
    simp [higham8_problem8_9_kahanLeftWitness, p, q]
  have hright :
      higham8_problem8_9_kahanRightWitness n h2 c =
        fun j =>
          if j = p then Real.sqrt (1 + c)
          else if j = q then -Real.sqrt (1 + c)
          else 0 := by
    ext j
    simp [higham8_problem8_9_kahanRightWitness, p, q]
  have hone_c_nonneg : 0 ≤ 1 + c := by linarith
  have hsqrt_sq : Real.sqrt (1 + c) * Real.sqrt (1 + c) = 1 + c := by
    simpa [sq] using Real.sq_sqrt hone_c_nonneg
  have hsqrt_prod :
      s ^ (n - 2) * Real.sqrt (1 + c) * Real.sqrt (1 + c) =
        s ^ (n - 2) * (1 + c) := by
    rw [mul_assoc, hsqrt_sq]
  ext i
  unfold matMulVec
  rw [hleft]
  rw [higham8_sum_two_support p q hpq]
  by_cases hip : i = p
  · subst i
    simp [higham8_problem8_9_kahanRightWitness, higham8_11_kahanMatrix,
      higham8_3_stressUpper, matTranspose, higham8_problem8_9_secondSmallestIndex,
      higham8_problem8_9_lastIndex, p, q, hnm1_ne_nm2, hnot_nm1_lt_nm2]
    rw [hsqrt_prod]
  · by_cases hiq : i = q
    · subst i
      simp [higham8_problem8_9_kahanRightWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, matTranspose, higham8_problem8_9_secondSmallestIndex,
        higham8_problem8_9_lastIndex, p, q, hnm2_ne_nm1, hnm1_ne_nm2,
        hnm2_lt_nm1]
      rw [hpow_nm1, hsqrt_prod]
      have hsum : c * (1 + c) + s * s = 1 + c := by
        nlinarith [hcs]
      calc
        -(s ^ (n - 2) * c * (1 + c)) + -(s ^ (n - 2) * s * s)
            = -s ^ (n - 2) * (c * (1 + c) + s * s) := by ring
        _ = -s ^ (n - 2) * (1 + c) := by rw [hsum]
        _ = -(s ^ (n - 2) * (1 + c)) := by ring
    · have hip_lt : i.val < p.val := by
        have hi_ne_p : i.val ≠ n - 2 := by
          intro hval
          exact hip (Fin.ext (by simpa [p, hpval] using hval))
        have hi_ne_q : i.val ≠ n - 1 := by
          intro hval
          exact hiq (Fin.ext (by simpa [q, hqval] using hval))
        have hi_bound : i.val < n := i.isLt
        omega
      have hp_ne_i : p ≠ i := by exact fun h => hip h.symm
      have hq_ne_i : q ≠ i := by exact fun h => hiq h.symm
      have hnot_p_lt_i : ¬ p < i := by
        rw [Fin.lt_def]
        omega
      have hnot_q_lt_i : ¬ q < i := by
        rw [Fin.lt_def]
        rw [hqval]
        omega
      simp [higham8_problem8_9_kahanRightWitness, higham8_11_kahanMatrix,
        higham8_3_stressUpper, matTranspose, p, q, hip, hiq, hp_ne_i, hq_ne_i,
        hnot_p_lt_i, hnot_q_lt_i]


private theorem higham8_realRectToCMatrix_euclideanLin_realVec {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    complexMatrixEuclideanLin (realRectToCMatrix A) (realVecToEuclidean x) =
      realVecToEuclidean (rectMatMulVec A x) := by
  apply WithLp.ofLp_injective
  ext i
  simp [realRectToCMatrix_euclideanLin_ofLp, realVecToEuclidean,
    complexMatrixVecMul, realRectToCMatrix, rectMatMulVec]


private theorem higham8_realRectToCMatrix_euclideanLin_realVec_square {n : ℕ}
    (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    complexMatrixEuclideanLin (realRectToCMatrix A) (realVecToEuclidean x) =
      realVecToEuclidean (matMulVec n A x) := by
  simpa [matMulVec, rectMatMulVec] using
    higham8_realRectToCMatrix_euclideanLin_realVec A x


/-- **Problem 8.9**, Gram-eigenpair certificate for the Appendix A Kahan
witness.  This proves that the explicit candidate has squared singular value
`(s^(n-2))^2 (1+c)`; the remaining source step is to place this eigenvalue at
the ordered index `n-2`. -/
theorem higham8_problem8_9_kahan_gram_witness
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    complexMatrixGramLin (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c)) =
      (((s ^ (n - 2)) ^ 2 * (1 + c) : ℝ) : ℂ) •
        realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c) := by
  let A : Fin n → Fin n → ℝ := higham8_11_kahanMatrix n c s
  let x : Fin n → ℝ := higham8_problem8_9_kahanRightWitness n h2 c
  let y : Fin n → ℝ := higham8_problem8_9_kahanLeftWitness n h2 c s
  let σ : ℝ := s ^ (n - 2) * Real.sqrt (1 + c)
  have hforward : matMulVec n A x = fun i => σ * y i := by
    simpa [A, x, y, σ] using
      higham8_problem8_9_kahan_witness_forward n h2 c s
  have htranspose : matMulVec n (matTranspose A) y = fun i => σ * x i := by
    simpa [A, x, y, σ] using
      higham8_problem8_9_kahan_witness_transpose n h2 c s hc hcs
  have hscale :
      matMulVec n (matTranspose A) (fun j => σ * y j) =
        fun i => σ * matMulVec n (matTranspose A) y i := by
    ext i
    unfold matMulVec
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hreal :
      matMulVec n (matMul n (matTranspose A) A) x =
        fun i => σ ^ 2 * x i := by
    ext i
    calc
      matMulVec n (matMul n (matTranspose A) A) x i =
          matMulVec n (matTranspose A) (matMulVec n A x) i :=
            matMulVec_matMul n (matTranspose A) A x i
      _ = matMulVec n (matTranspose A) (fun j => σ * y j) i := by
            rw [hforward]
      _ = σ * matMulVec n (matTranspose A) y i := by
            rw [hscale]
      _ = σ * (σ * x i) := by
            rw [htranspose]
      _ = σ ^ 2 * x i := by ring
  have hsigma_sq : σ ^ 2 = (s ^ (n - 2)) ^ 2 * (1 + c) := by
    dsimp [σ]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  rw [← complexMatrixEuclideanLin_adjoint_mul_self (realRectToCMatrix A)]
  rw [← realRectToCMatrix_matTranspose A]
  rw [← realRectToCMatrix_matMul]
  rw [higham8_realRectToCMatrix_euclideanLin_realVec_square]
  rw [hreal]
  apply WithLp.ofLp_injective
  ext i
  change ((σ ^ 2 * x i : ℝ) : ℂ) =
    (((s ^ (n - 2)) ^ 2 * (1 + c) : ℝ) : ℂ) * (x i : ℂ)
  rw [hsigma_sq]
  norm_num [Complex.ofReal_mul]


/-- **Problem 8.9** support: the Appendix A witness gives an actual Gram
eigenvalue, not only a formal action equation.  The remaining source step is
the ordered placement at index `n - 2`. -/
theorem higham8_problem8_9_kahan_candidate_hasGramEigenvalue
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    Module.End.HasEigenvalue
      (complexMatrixGramLin (realRectToCMatrix (higham8_11_kahanMatrix n c s)))
      ((((s ^ (n - 2)) ^ 2 * (1 + c) : ℝ) : ℂ)) := by
  let v := realVecToEuclidean (higham8_problem8_9_kahanRightWitness n h2 c)
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ?_
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    simpa [v] using higham8_problem8_9_kahan_gram_witness n h2 c s hc hcs
  · exact higham8_problem8_9_kahanRightWitness_euclidean_ne_zero n h2 c hc


/-- **Problem 8.9** support: the Appendix A candidate occurs somewhere in the
repository's sorted Gram-eigenvalue list.  Problem 8.9 remains open precisely
because this theorem does not identify the occurrence with index `n - 2`. -/
theorem higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) :
    ∃ i : Fin n,
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s)) i =
        (s ^ (n - 2)) ^ 2 * (1 + c) := by
  obtain ⟨i, hi⟩ :=
    (complexMatrixGramLin_isSymmetric
      (realRectToCMatrix (higham8_11_kahanMatrix n c s))).exists_eigenvalues_eq
      (finrank_euclideanSpace_fin (𝕜 := ℂ) (n := n))
      (higham8_problem8_9_kahan_candidate_hasGramEigenvalue n h2 c s hc hcs)
  exact ⟨i, Complex.ofReal_injective (by
    simpa [complexMatrixGramEigenvalues] using hi)⟩


private theorem higham8_complexMatrixRank_rankOne_standard_le_one
    {m n : ℕ} (i0 : Fin m) (y : CVec n) :
    complexMatrixRank (complexMatrixRankOne (standardBasisCVec i0) y) ≤ 1 := by
  unfold complexMatrixRank
  rw [Matrix.rank_eq_finrank_span_cols]
  have hspan_le :
      Submodule.span ℂ
          (Set.range
            (Matrix.col
              (complexMatrixRankOne (standardBasisCVec i0) y :
                Matrix (Fin m) (Fin n) ℂ))) ≤
        ℂ ∙ standardBasisCVec i0 := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    have hcol :
        Matrix.col
            (complexMatrixRankOne (standardBasisCVec i0) y : Matrix (Fin m) (Fin n) ℂ) j =
          y j • standardBasisCVec i0 := by
      ext i
      simp [complexMatrixRankOne, mul_comm]
    rw [hcol]
    exact Submodule.smul_mem (ℂ ∙ standardBasisCVec i0) (y j)
      (Submodule.mem_span_singleton_self (standardBasisCVec i0))
  calc
    Module.finrank ℂ
        (Submodule.span ℂ
          (Set.range
            (Matrix.col
              (complexMatrixRankOne (standardBasisCVec i0) y :
                Matrix (Fin m) (Fin n) ℂ)))) ≤
        Module.finrank ℂ (ℂ ∙ standardBasisCVec i0) :=
          Submodule.finrank_mono hspan_le
    _ = 1 := finrank_span_singleton (standardBasisCVec_ne_zero i0)


private theorem higham8_problem8_9_kahan_zero_eq_rankOne
    (n : ℕ) (hn : 0 < n) :
    realRectToCMatrix (higham8_11_kahanMatrix n 1 0) =
      complexMatrixRankOne (standardBasisCVec (⟨0, hn⟩ : Fin n))
        (fun j => realRectToCMatrix (higham8_11_kahanMatrix n 1 0)
          (⟨0, hn⟩ : Fin n) j) := by
  let z : Fin n := ⟨0, hn⟩
  ext i j
  by_cases hi : i = z
  · subst i
    simp [complexMatrixRankOne, standardBasisCVec, z]
  · have hi' : i ≠ (⟨0, hn⟩ : Fin n) := by simpa [z] using hi
    have hi_pos : 0 < i.val := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hzero
        exact hi' (Fin.ext (by simpa using hzero))
      omega
    have hpow : (0 : ℝ) ^ i.val = 0 := zero_pow (Nat.ne_of_gt hi_pos)
    simp [realRectToCMatrix, higham8_11_kahanMatrix, complexMatrixRankOne,
      standardBasisCVec, hi', hpow]


private theorem higham8_problem8_9_kahan_zero_rank_le_one
    (n : ℕ) (hn : 0 < n) :
    complexMatrixRank (realRectToCMatrix (higham8_11_kahanMatrix n 1 0)) ≤ 1 := by
  rw [higham8_problem8_9_kahan_zero_eq_rankOne n hn]
  exact higham8_complexMatrixRank_rankOne_standard_le_one (⟨0, hn⟩ : Fin n)
    (fun j => realRectToCMatrix (higham8_11_kahanMatrix n 1 0) (⟨0, hn⟩ : Fin n) j)


private theorem higham8_complexMatrixGramEigenvalues_eq_zero_of_rank_le_one
    {m n : ℕ} (A : CMatrix m n) (i : Fin n)
    (hi : 1 ≤ i.val) (hrank : complexMatrixRank A ≤ 1) :
    complexMatrixGramEigenvalues A i = 0 := by
  classical
  by_contra hne
  let z : Fin n := ⟨0, by omega⟩
  have hz_ne_i : z ≠ i := by
    intro h
    have hval := congrArg Fin.val h
    simp [z] at hval
    omega
  have hpos_i : 0 < complexMatrixGramEigenvalues A i := by
    exact lt_of_le_of_ne (complexMatrixGramEigenvalues_nonneg A i) (by
      intro hzero
      exact hne hzero.symm)
  have hle : complexMatrixGramEigenvalues A i ≤ complexMatrixGramEigenvalues A z := by
    exact (complexMatrixGramEigenvalues_antitone A) (by
      rw [Fin.le_iff_val_le_val]
      simp [z])
  have hz_ne_zero : complexMatrixGramEigenvalues A z ≠ 0 := by
    have hz_pos : 0 < complexMatrixGramEigenvalues A z := lt_of_lt_of_le hpos_i hle
    exact ne_of_gt hz_pos
  have hcard : Fintype.card {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} ≤ 1 := by
    have hcount := complexMatrixRank_eq_card_nonzero_gramEigenvalues (A := A)
    omega
  have hsub : Subsingleton {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} :=
    Fintype.card_le_one_iff_subsingleton.mp hcard
  let zi : {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} := ⟨z, hz_ne_zero⟩
  let ii : {j : Fin n // complexMatrixGramEigenvalues A j ≠ 0} := ⟨i, hne⟩
  have hzi : zi = ii := Subsingleton.elim zi ii
  exact hz_ne_i (Subtype.ext_iff.mp hzi)


private theorem higham8_complexMatrixGramEigenvalues_top_eq_of_rank_le_one_of_mem_nonzero
    {m n : ℕ} (A : CMatrix m n) (hn : 0 < n) {lam : ℝ}
    (hlam : lam ≠ 0) (hrank : complexMatrixRank A ≤ 1)
    (hmem : ∃ i : Fin n, complexMatrixGramEigenvalues A i = lam) :
    complexMatrixGramEigenvalues A (⟨0, hn⟩ : Fin n) = lam := by
  rcases hmem with ⟨i, hi⟩
  by_cases hiz : i = (⟨0, hn⟩ : Fin n)
  · simpa [hiz] using hi
  · have hi_pos : 1 ≤ i.val := by
      have hi_ne_zero : i.val ≠ 0 := by
        intro hzero
        exact hiz (Fin.ext (by simpa using hzero))
      omega
    have hzero := higham8_complexMatrixGramEigenvalues_eq_zero_of_rank_le_one A i hi_pos hrank
    exact False.elim (hlam (by simpa [hi] using hzero))


theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_three_le
    (n : ℕ) (h3 : 3 ≤ n) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n 1 0))
        (higham8_problem8_9_secondSmallestIndex n (by omega)) =
      (0 ^ (n - 2)) ^ 2 * (1 + (1 : ℝ)) := by
  let p := higham8_problem8_9_secondSmallestIndex n (by omega : 2 ≤ n)
  have hp_pos : 1 ≤ p.val := by
    simp [p, higham8_problem8_9_secondSmallestIndex]
    omega
  have hzero :
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n 1 0)) p = 0 :=
    higham8_complexMatrixGramEigenvalues_eq_zero_of_rank_le_one _ p hp_pos
      (higham8_problem8_9_kahan_zero_rank_le_one n (by omega))
  have hpow : (0 : ℝ) ^ (n - 2) = 0 :=
    zero_pow (by omega : n - 2 ≠ 0)
  rw [hzero, hpow]
  ring


theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_two :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix 2 1 0))
        (higham8_problem8_9_secondSmallestIndex 2 (by norm_num)) =
      (0 ^ (2 - 2)) ^ 2 * (1 + (1 : ℝ)) := by
  let A : CMatrix 2 2 := realRectToCMatrix (higham8_11_kahanMatrix 2 1 0)
  have hmem :
      ∃ i : Fin 2,
        complexMatrixGramEigenvalues A i =
          (0 ^ (2 - 2)) ^ 2 * (1 + (1 : ℝ)) := by
    simpa [A] using
      higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
        2 (by norm_num : 2 ≤ 2) 1 0 (by norm_num) (by norm_num)
  have htop :
      complexMatrixGramEigenvalues A (⟨0, by norm_num⟩ : Fin 2) =
        (0 ^ (2 - 2)) ^ 2 * (1 + (1 : ℝ)) := by
    apply higham8_complexMatrixGramEigenvalues_top_eq_of_rank_le_one_of_mem_nonzero A
      (by norm_num)
    · norm_num
    · simpa [A] using higham8_problem8_9_kahan_zero_rank_le_one 2 (by norm_num)
    · exact hmem
  have hp :
      higham8_problem8_9_secondSmallestIndex 2 (by norm_num : 2 ≤ 2) =
        (⟨0, by norm_num⟩ : Fin 2) := by
    ext
    simp [higham8_problem8_9_secondSmallestIndex]
  simpa [A, hp] using htop


theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_zero
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) (hs_zero : s = 0) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  subst s
  have hc_sq : c ^ 2 = 1 := by nlinarith
  have hc_one : c = 1 := by
    nlinarith [sq_nonneg (c - 1), sq_nonneg (c + 1)]
  subst c
  by_cases hn2 : n = 2
  · subst n
    simpa using
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_two
  · have h3 : 3 ≤ n := by omega
    simpa using
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_zero_three_le n h3


theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1) (hs_zero : s = 0) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc
  · rw [hs_zero]
  · exact
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_zero
        n h2 c s hc hcs hs_zero


/-- **Problem 8.9** support: in the source branch `0 < s < 1`, the already
proved smallest-slot exclusion and witness eigenvalue prove the easy ordered
half: the second-smallest Gram eigenvalue is no larger than the Appendix A
candidate.  The missing half is the interlacing lower bound. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) ≤
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  let A : CMatrix n n := realRectToCMatrix (higham8_11_kahanMatrix n c s)
  let p := higham8_problem8_9_secondSmallestIndex n h2
  let q := higham8_problem8_9_lastIndex n (by omega : 0 < n)
  let σ := higham8_problem8_9_kahanSecondSmallestValue n c s
  let lam : ℝ := (s ^ (n - 2)) ^ 2 * (1 + c)
  have hσ_nonneg : 0 ≤ σ := by
    exact mul_nonneg (pow_nonneg (le_of_lt hs_pos) _) (Real.sqrt_nonneg _)
  have hsmall :
      complexMatrixSingularValue A q < σ := by
    simpa [A, q, σ] using
      higham8_problem8_9_kahan_smallestSingularValue_lt_candidate
        n h2 c s hc hs_pos hs_lt
  have hlast_lt : complexMatrixGramEigenvalues A q < lam := by
    have hsq :
        complexMatrixSingularValue A q ^ 2 < σ ^ 2 :=
      (sq_lt_sq₀ (complexMatrixSingularValue_nonneg A q) hσ_nonneg).2 hsmall
    have hσ_sq : σ ^ 2 = lam := by
      simp [σ, lam, higham8_problem8_9_kahanSecondSmallestValue, mul_pow,
        Real.sq_sqrt (by linarith : 0 ≤ 1 + c)]
    rw [complexMatrixSingularValue_sq, hσ_sq] at hsq
    exact hsq
  obtain ⟨i, hi⟩ :=
    higham8_problem8_9_kahan_candidate_mem_gramEigenvalues n h2 c s hc hcs
  have hi_ne_q : i ≠ q := by
    intro hiq
    have hqeq : complexMatrixGramEigenvalues A q = lam := by
      simpa [A, q, lam, hiq] using hi
    exact (ne_of_lt hlast_lt) hqeq
  have hi_le_p : i ≤ p := by
    rw [Fin.le_iff_val_le_val]
    have hi_val_ne : i.val ≠ n - 1 := by
      intro hv
      apply hi_ne_q
      exact Fin.ext (by
        simpa [q, higham8_problem8_9_lastIndex] using hv)
    have hi_bound : i.val < n := i.isLt
    simp [p, higham8_problem8_9_secondSmallestIndex]
    omega
  have hp_le_hi : complexMatrixGramEigenvalues A p ≤ complexMatrixGramEigenvalues A i :=
    (complexMatrixGramEigenvalues_antitone A) hi_le_p
  simpa [A, p, lam, hi] using hp_le_hi


/-- **Problem 8.9** support: the exact ordered Gram-eigenvalue statement follows
from the sole missing source-side lower bound.  The lower bound is the
interlacing/min-max step from Appendix A. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hlower :
      (s ^ (n - 2)) ^ 2 * (1 + c) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2)) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  exact le_antisymm
    (higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate
      n h2 c s hc hcs hs_pos hs_lt)
    hlower


/-- **Problem 8.9** support: once the interlacing lower bound places the
candidate at the ordered Gram slot `n - 2`, the displayed singular-value
formula follows from the local SVD/Gram reduction. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hlower :
      (s ^ (n - 2)) ^ 2 * (1 + c) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc (le_of_lt hs_pos)
  exact
    higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound
      n h2 c s hc hcs hs_pos hs_lt hlower


/-- **Problem 8.9** base case: for the `2 × 2` Kahan matrix, the target
`second-smallest` slot is the top sorted Gram eigenvalue, so candidate
membership and antitonicity give the missing lower bound without interlacing. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two
    (c s : ℝ) (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix 2 c s))
        (higham8_problem8_9_secondSmallestIndex 2 (by norm_num)) =
      (s ^ (2 - 2)) ^ 2 * (1 + c) := by
  let A : CMatrix 2 2 := realRectToCMatrix (higham8_11_kahanMatrix 2 c s)
  let p := higham8_problem8_9_secondSmallestIndex 2 (by norm_num : 2 ≤ 2)
  let lam : ℝ := (s ^ (2 - 2)) ^ 2 * (1 + c)
  have hp_top : p = (⟨0, by norm_num⟩ : Fin 2) := by
    ext
    simp [p, higham8_problem8_9_secondSmallestIndex]
  have hupper : complexMatrixGramEigenvalues A p ≤ lam := by
    simpa [A, p, lam] using
      higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate
        2 (by norm_num : 2 ≤ 2) c s hc hcs hs_pos hs_lt
  have hlower : lam ≤ complexMatrixGramEigenvalues A p := by
    obtain ⟨i, hi⟩ :=
      higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
        2 (by norm_num : 2 ≤ 2) c s hc hcs
    have hp_le_i : p ≤ i := by
      rw [hp_top]
      exact Fin.zero_le i
    have hi_le_top : complexMatrixGramEigenvalues A i ≤ complexMatrixGramEigenvalues A p :=
      (complexMatrixGramEigenvalues_antitone A) hp_le_i
    simpa [A, lam, hi] using hi_le_top
  exact le_antisymm hupper hlower


/-- **Problem 8.9** base case: the displayed second-smallest singular value is
closed for `n = 2` in the source branch `0 < s < 1`. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_two
    (c s : ℝ) (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix 2 c s))
        (higham8_problem8_9_secondSmallestIndex 2 (by norm_num)) =
      higham8_problem8_9_kahanSecondSmallestValue 2 c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    2 (by norm_num : 2 ≤ 2) c s hc (le_of_lt hs_pos)
  exact higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two
    c s hc hcs hs_pos hs_lt


/-- **Problem 8.9** induction reduction: if the one-step Cauchy-interlacing
consequence holds for the leading Kahan Gram blocks, then the displayed
interior Gram eigenvalue formula follows for every size.

The required interlacing consequence is the exact source induction step: the
previous-size second-smallest Gram eigenvalue is no larger than the current
third-smallest Gram eigenvalue.  The remaining project-level spectral blocker
is proving that hypothesis from a reusable interlacing/min-max theorem. -/
theorem higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hinterlace :
      ∀ (m : ℕ) (hm : 3 ≤ m),
        complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
            (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
          complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix m c s))
            (higham8_problem8_9_thirdSmallestIndex m hm)) :
    complexMatrixGramEigenvalues
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      (s ^ (n - 2)) ^ 2 * (1 + c) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ (hk2 : 2 ≤ k),
      complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix k c s))
          (higham8_problem8_9_secondSmallestIndex k hk2) =
        (s ^ (k - 2)) ^ 2 * (1 + c)
  have hmain : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk2
        by_cases hk_two : k = 2
        · subst k
          exact
            higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two
              c s hc hcs hs_pos hs_lt
        · have hk3 : 3 ≤ k := by omega
          let A : CMatrix k k := realRectToCMatrix (higham8_11_kahanMatrix k c s)
          let p := higham8_problem8_9_secondSmallestIndex k hk2
          let q := higham8_problem8_9_lastIndex k (by omega : 0 < k)
          let r := higham8_problem8_9_thirdSmallestIndex k hk3
          let lam : ℝ := (s ^ (k - 2)) ^ 2 * (1 + c)
          let lamPrev : ℝ := (s ^ ((k - 1) - 2)) ^ 2 * (1 + c)
          have hprev2 : 2 ≤ k - 1 := by omega
          have hprev :
              complexMatrixGramEigenvalues
                  (realRectToCMatrix (higham8_11_kahanMatrix (k - 1) c s))
                  (higham8_problem8_9_secondSmallestIndex (k - 1) hprev2) =
                lamPrev := by
            simpa [P, lamPrev] using ih (k - 1) (by omega) hprev2
          have hthird_ge_prev : lamPrev ≤ complexMatrixGramEigenvalues A r := by
            calc
              lamPrev =
                  complexMatrixGramEigenvalues
                    (realRectToCMatrix (higham8_11_kahanMatrix (k - 1) c s))
                    (higham8_problem8_9_secondSmallestIndex (k - 1) (by omega)) := by
                      simpa [lamPrev] using hprev.symm
              _ ≤ complexMatrixGramEigenvalues A r := by
                      simpa [A, r] using hinterlace k hk3
          have hs_sq_lt_one : s ^ 2 < 1 := by
            nlinarith [mul_lt_mul_of_pos_right hs_lt hs_pos]
          have hprev_pos : 0 < lamPrev := by
            have hpow_pos : 0 < s ^ ((k - 1) - 2) := pow_pos hs_pos _
            have hc_pos : 0 < 1 + c := by linarith
            exact mul_pos (sq_pos_of_pos hpow_pos) hc_pos
          have hlam_lt_prev : lam < lamPrev := by
            have hkidx : k - 2 = (k - 1) - 2 + 1 := by omega
            have hrewrite :
                lam = s ^ 2 * lamPrev := by
              simp [lam, lamPrev, hkidx, pow_succ]
              ring
            rw [hrewrite]
            simpa using mul_lt_mul_of_pos_right hs_sq_lt_one hprev_pos
          have hthird_gt_lam : lam < complexMatrixGramEigenvalues A r :=
            hlam_lt_prev.trans_le hthird_ge_prev
          obtain ⟨i, hi⟩ :=
            higham8_problem8_9_kahan_candidate_mem_gramEigenvalues
              k hk2 c s hc hcs
          have hi_not_le_r : ¬ i ≤ r := by
            intro hir
            have hr_le_i :
                complexMatrixGramEigenvalues A r ≤ complexMatrixGramEigenvalues A i :=
              complexMatrixGramEigenvalues_antitone A hir
            have hr_le_lam : complexMatrixGramEigenvalues A r ≤ lam := by
              simpa [A, lam, hi] using hr_le_i
            exact (not_lt_of_ge hr_le_lam) hthird_gt_lam
          have hi_val_gt_r : r.val < i.val := by
            by_contra hle
            exact hi_not_le_r (Fin.le_iff_val_le_val.2 (by omega))
          have hi_ge_p_val : p.val ≤ i.val := by
            simp [p, higham8_problem8_9_secondSmallestIndex]
            simp [r, higham8_problem8_9_thirdSmallestIndex] at hi_val_gt_r
            omega
          have hlast_lt :
              complexMatrixGramEigenvalues A q < lam := by
            simpa [A, q, lam] using
              higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate
                k hk2 c s hc hs_pos hs_lt
          have hi_ne_q : i ≠ q := by
            intro hiq
            have hqeq : complexMatrixGramEigenvalues A q = lam := by
              simpa [A, q, lam, hiq] using hi
            exact (ne_of_lt hlast_lt) hqeq
          have hi_eq_p : i = p := by
            apply Fin.ext
            have hi_ne_last_val : i.val ≠ k - 1 := by
              intro hv
              apply hi_ne_q
              exact Fin.ext (by
                simpa [q, higham8_problem8_9_lastIndex] using hv)
            have hi_lt_last : i.val < k - 1 := by
              have hi_lt_k : i.val < k := i.isLt
              omega
            simp [p, higham8_problem8_9_secondSmallestIndex] at hi_ge_p_val ⊢
            omega
          simpa [A, p, lam, hi_eq_p] using hi
  exact hmain n h2


/-- **Problem 8.9** induction reduction, singular-value form: the source
interior formula follows from the exact one-step Cauchy-interlacing consequence
for the leading Kahan Gram blocks. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_interlacing
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hcs : c ^ 2 + s ^ 2 = 1)
    (hs_pos : 0 < s) (hs_lt : s < 1)
    (hinterlace :
      ∀ (m : ℕ) (hm : 3 ≤ m),
        complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
            (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
          complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix m c s))
            (higham8_problem8_9_thirdSmallestIndex m hm)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue
    n h2 c s hc (le_of_lt hs_pos)
  exact
    higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing
      n h2 c s hc hcs hs_pos hs_lt hinterlace


theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hlower : 3 ≤ n → 0 < s → s < 1 →
      (s ^ (n - 2)) ^ 2 * (1 + c) ≤
        complexMatrixGramEigenvalues
          (realRectToCMatrix (higham8_11_kahanMatrix n c s))
          (higham8_problem8_9_secondSmallestIndex n h2)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  by_cases hs_zero : s = 0
  · exact higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero
      n h2 c s hc hcs hs_zero
  · by_cases hs_one : s = 1
    · exact higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one
        n h2 c s hc hcs hs_one
    · have hs_pos : 0 < s := lt_of_le_of_ne hs (by
        intro hzero
        exact hs_zero hzero.symm)
      have hs_lt : s < 1 := by
        have hs_sq_le : s ^ 2 ≤ 1 := by nlinarith [sq_nonneg c]
        have hs_le : s ≤ 1 := by
          simpa using Real.le_sqrt_of_sq_le hs_sq_le
        exact lt_of_le_of_ne hs_le hs_one
      by_cases hn2 : n = 2
      · subst n
        exact higham8_problem8_9_kahan_secondSmallestSingularValue_two
          c s hc hcs hs_pos hs_lt
      · have h3 : 3 ≤ n := by omega
        exact higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound
          n h2 c s hc hcs hs_pos hs_lt (hlower h3 hs_pos hs_lt)


/-- **Problem 8.9** all-cases reduction to the Kahan Gram interlacing step.
Once the leading-principal-block Cauchy interlacing consequence is available,
this theorem closes the displayed second-smallest singular-value formula without
any separate edge-case assumptions. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1)
    (hinterlace :
      ∀ (m : ℕ) (hm : 3 ≤ m),
        complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
            (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
          complexMatrixGramEigenvalues
            (realRectToCMatrix (higham8_11_kahanMatrix m c s))
            (higham8_problem8_9_thirdSmallestIndex m hm)) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  apply
    higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound
      n h2 c s hc hs hcs
  intro h3 hs_pos hs_lt
  exact le_of_eq
    (higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing
      n h2 c s hc hcs hs_pos hs_lt hinterlace).symm


/-- **Problem 8.9**: for Kahan's matrix in (8.11), the second-smallest
singular value is `s^(n-2) * sqrt (1+c)` in the repository's descending
singular-value order. -/
theorem higham8_problem8_9_kahan_secondSmallestSingularValue
    (n : ℕ) (h2 : 2 ≤ n) (c s : ℝ)
    (hc : 0 ≤ c) (hs : 0 ≤ s) (hcs : c ^ 2 + s ^ 2 = 1) :
    complexMatrixSingularValue
        (realRectToCMatrix (higham8_11_kahanMatrix n c s))
        (higham8_problem8_9_secondSmallestIndex n h2) =
      higham8_problem8_9_kahanSecondSmallestValue n c s := by
  exact
    higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing
      n h2 c s hc hs hcs
      (higham8_problem8_9_kahanGram_interlacing c s)

end NumStability
