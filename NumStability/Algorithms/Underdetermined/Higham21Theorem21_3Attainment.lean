-- Algorithms/Underdetermined/Higham21Theorem21_3Attainment.lean
--
-- Attainment refinements for Higham, Theorem 21.3.  The source writes a
-- minimum, while the base development models the backward error as an
-- infimum.  This module identifies the exact nondegeneracy condition under
-- which the existing least-singular-vector construction attains that
-- infimum, proves closure attainment without extra assumptions, and records
-- a scalar counterexample to unconditional exact attainment.

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- The square-case singular term
-- ============================================================

/-- A square matrix with a nontrivial right kernel has zero row-side least
    singular value.  The row singular value is represented in the Chapter 21
    development as the least column singular value of the transpose. -/
theorem higham21SigmaMinRow_eq_zero_of_square_nontrivial_kernel
    {d : Nat} (M : Fin (d + 1) -> Fin (d + 1) -> Real)
    {x : Fin (d + 1) -> Real} (hx : x ≠ 0)
    (hMx : rectMatMulVec M x = 0) :
    higham21SigmaMinRow M = 0 := by
  have hsigma_nonneg : 0 <= higham21SigmaMinRow M :=
    higham21SigmaMinRow_nonneg M
  by_contra hsigma_ne
  have hsigma_pos : 0 < higham21SigmaMinRow M :=
    lt_of_le_of_ne hsigma_nonneg (Ne.symm hsigma_ne)
  have htranspose_injective : Function.Injective (rectTransposeMulVec M) := by
    intro u v huv
    let z : Fin (d + 1) -> Real := fun i => u i - v i
    have hzaction : rectTransposeMulVec M z = 0 := by
      ext j
      have hj := congrFun huv j
      dsimp [z]
      unfold rectTransposeMulVec at hj
      unfold rectTransposeMulVec
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr hj
    have hbound :=
      higham21SigmaMinRow_mul_vecNorm2_le_rectTransposeMulVec M z
    rw [hzaction] at hbound
    change higham21SigmaMinRow M * vecNorm2 z ≤
      vecNorm2 (fun _ : Fin (d + 1) => 0) at hbound
    rw [vecNorm2_zero] at hbound
    have hproduct_nonneg :
        0 <= higham21SigmaMinRow M * vecNorm2 z :=
      mul_nonneg (le_of_lt hsigma_pos) (vecNorm2_nonneg z)
    have hproduct_zero :
        higham21SigmaMinRow M * vecNorm2 z = 0 :=
      le_antisymm hbound hproduct_nonneg
    have hznorm : vecNorm2 z = 0 :=
      (mul_eq_zero.mp hproduct_zero).resolve_left (ne_of_gt hsigma_pos)
    ext i
    have hi := (vecNorm2_eq_zero_iff z).mp hznorm i
    dsimp [z] at hi
    linarith
  have hfinite_transpose_injective :
      Function.Injective (rectMatMulVec (finiteTranspose M)) := by
    intro u v huv
    apply htranspose_injective
    ext j
    have hj := congrFun huv j
    simpa [rectMatMulVec, finiteTranspose, rectTransposeMulVec] using hj
  have hdet_transpose :
      Matrix.det
          (finiteTranspose M : Matrix (Fin (d + 1)) (Fin (d + 1)) Real) ≠ 0 :=
    det_ne_zero_of_square_rectMatMulVec_injective
      hfinite_transpose_injective
  let MM : Matrix (Fin (d + 1)) (Fin (d + 1)) Real := M
  have htranspose_matrix :
      (finiteTranspose M : Matrix (Fin (d + 1)) (Fin (d + 1)) Real) =
        MM.transpose := by
    ext i j
    rfl
  have hdet : MM.det ≠ 0 := by
    rw [htranspose_matrix, Matrix.det_transpose] at hdet_transpose
    exact hdet_transpose
  have hdet_unit : IsUnit MM.det := by
    exact isUnit_iff_ne_zero.mpr hdet
  have hmatrix_unit : IsUnit MM :=
    (Matrix.isUnit_iff_isUnit_det MM).mpr hdet_unit
  have hmulVec_injective : Function.Injective MM.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hmatrix_unit
  have hxzero : x = 0 := by
    apply hmulVec_injective
    ext i
    have hi := congrFun hMx i
    simpa [MM, Matrix.mulVec, rectMatMulVec] using hi
  exact hx hxzero

/-- Higham, 2nd ed., Theorem 21.3, square-case note: for nonzero `y`, the
    source matrix `A (I - y y^+)` has zero `sigma_m` when its row and column
    dimensions agree. -/
theorem higham21_theorem21_3_square_sigma_term_eq_zero
    {d : Nat} (A : Fin (d + 1) -> Fin (d + 1) -> Real)
    (y : Fin (d + 1) -> Real) (hy : y ≠ 0) :
    higham21SigmaMinRow
        (undetNormwiseBackwardErrorFormulaMatrix A y) = 0 := by
  apply higham21SigmaMinRow_eq_zero_of_square_nontrivial_kernel
    (undetNormwiseBackwardErrorFormulaMatrix A y) hy
  exact higham21_thm21_3_formulaMatrix_mulVec_candidate_eq_zero A y
    (higham21_vecNorm2Sq_ne_zero_of_ne_zero hy)

/-- In the square case, the nonzero Sun--Sun formula reduces to its scalar
    residual branch, as stated immediately after Theorem 21.3. -/
theorem higham21_theorem21_3_square_nonzero_formula_eq_phi
    {d : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (d + 1) -> Fin (d + 1) -> Real)
    (b : Fin (d + 1) -> Real) (y : Fin (d + 1) -> Real) (hy : y ≠ 0) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
        (higham21SigmaMinRow
          (undetNormwiseBackwardErrorFormulaMatrix A y)) =
      lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y := by
  rw [higham21_theorem21_3_square_sigma_term_eq_zero A y hy]
  exact undetNormwiseBackwardErrorNonzeroFormulaRHS_eq_phi_of_sigma_zero
    htheta A b hy

/-- Source-facing square specialization of the complete nonzero formula. -/
theorem higham21_theorem21_3_square_nonzero_etaF_eq_phi
    {d : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (d + 1) -> Fin (d + 1) -> Real)
    (b : Fin (d + 1) -> Real) (y : Fin (d + 1) -> Real) (hy : y ≠ 0) :
    undetNormwiseBackwardErrorEtaF theta A b y =
      lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y := by
  calc
    undetNormwiseBackwardErrorEtaF theta A b y =
        undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix A y)) :=
      higham21_theorem21_3_nonzero_normwise_backward_error_formula
        htheta A b y hy
    _ = lsNormwiseBackwardErrorPhi theta (undetResidualHigham A b y) y :=
      higham21_theorem21_3_square_nonzero_formula_eq_phi
        htheta A b y hy

-- ============================================================
-- Exact attainment under the sharp range nondegeneracy condition
-- ============================================================

/-- The `t = 0` least-singular-vector perturbation is exactly feasible when
    its residual-corrected right-hand side has nonzero pairing with the chosen
    attaining left singular vector.  This is precisely the coefficient that
    the epsilon construction perturbs away from zero. -/
theorem higham21_theorem21_3_exists_exact_attaining_perturbation_of_pairing_ne_zero
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) (y : Fin n -> Real)
    (u : Fin (m + 1) -> Real) (hy : y ≠ 0) (hu : u ≠ 0)
    (hattain :
      vecNorm2Sq
          (rectTransposeMulVec
            (undetNormwiseBackwardErrorFormulaMatrix A y) u) =
        higham21SigmaMinRow
              (undetNormwiseBackwardErrorFormulaMatrix A y) ^ 2 *
          vecNorm2Sq u)
    (hpair :
      (∑ i : Fin (m + 1),
        u i *
          (b i + higham21Thm21_3ResidualDeltab theta A b y i)) ≠ 0) :
    ∃ (DeltaA : Fin (m + 1) -> Fin n -> Real)
        (Deltab : Fin (m + 1) -> Real),
      UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab /\
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
            (higham21SigmaMinRow
              (undetNormwiseBackwardErrorFormulaMatrix A y)) := by
  let DeltaA := higham21Thm21_3ApproxDeltaA theta A b y u 0
  let Deltab := higham21Thm21_3ApproxDeltab theta A b y u 0
  refine ⟨DeltaA, Deltab, ?_, ?_⟩
  · apply
      (undetNormwiseBackwardErrorFeasible_iff_system_eq_and_exists_transpose_witness
        A b y DeltaA Deltab).2
    have hsystem :
        rectMatMulVec (fun i j => A i j + DeltaA i j) y =
          fun i => b i + Deltab i := by
      simpa [DeltaA, Deltab] using
        higham21Thm21_3Approx_system_eq theta A b y u 0 hy
    refine ⟨hsystem, ?_⟩
    have hY : vecNorm2Sq y ≠ 0 :=
      higham21_vecNorm2Sq_ne_zero_of_ne_zero hy
    have hpair' :
        (∑ i : Fin (m + 1), u i * (b i + Deltab i)) ≠ 0 := by
      simpa [Deltab, higham21Thm21_3ApproxDeltab] using hpair
    let q : Real :=
      (∑ i : Fin (m + 1), u i * (b i + Deltab i)) / vecNorm2Sq y
    have hq : q ≠ 0 := div_ne_zero hpair' hY
    have htrans :
        rectTransposeMulVec (fun i j => A i j + DeltaA i j) u =
          fun j => q * y j := by
      simpa [DeltaA, Deltab, q] using
        higham21Thm21_3Approx_transpose_action
          theta A b y u 0 hy hu
    refine ⟨(fun i => (1 / q) * u i), ?_⟩
    ext j
    have htransj :
        (∑ i : Fin (m + 1), (A i j + DeltaA i j) * u i) = q * y j := by
      simpa [rectTransposeMulVec] using congrFun htrans j
    unfold rectTransposeMulVec
    calc
      (∑ i : Fin (m + 1),
          (A i j + DeltaA i j) * ((1 / q) * u i)) =
          (1 / q) *
            (∑ i : Fin (m + 1), (A i j + DeltaA i j) * u i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (1 / q) * (q * y j) := by rw [htransj]
      _ = y j := by field_simp [hq]
  · simpa [DeltaA, Deltab] using
      higham21Thm21_3Approx_cost_zero_eq_formulaRHS_of_attaining
        htheta A b y u hy hu hattain

/-- Under the same nonzero-pairing condition, the infimum itself belongs to
    the attainable-cost set, so the source `min` is literally realized. -/
theorem higham21_theorem21_3_etaF_is_attained_of_pairing_ne_zero
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) (y : Fin n -> Real)
    (u : Fin (m + 1) -> Real) (hy : y ≠ 0) (hu : u ≠ 0)
    (hattain :
      vecNorm2Sq
          (rectTransposeMulVec
            (undetNormwiseBackwardErrorFormulaMatrix A y) u) =
        higham21SigmaMinRow
              (undetNormwiseBackwardErrorFormulaMatrix A y) ^ 2 *
          vecNorm2Sq u)
    (hpair :
      (∑ i : Fin (m + 1),
        u i *
          (b i + higham21Thm21_3ResidualDeltab theta A b y i)) ≠ 0) :
    ∃ (DeltaA : Fin (m + 1) -> Fin n -> Real)
        (Deltab : Fin (m + 1) -> Real),
      UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab /\
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          undetNormwiseBackwardErrorEtaF theta A b y := by
  obtain ⟨DeltaA, Deltab, hfeas, hcost⟩ :=
    higham21_theorem21_3_exists_exact_attaining_perturbation_of_pairing_ne_zero
      htheta A b y u hy hu hattain hpair
  refine ⟨DeltaA, Deltab, hfeas, ?_⟩
  calc
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
        undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix A y)) := hcost
    _ = undetNormwiseBackwardErrorEtaF theta A b y :=
      (higham21_theorem21_3_nonzero_normwise_backward_error_formula
        htheta A b y hy).symm

-- ============================================================
-- Assumption-free closure attainment and exact obstruction
-- ============================================================

/-- Without a nonzero-pairing hypothesis, the displayed formula is still a
    closure point of the genuinely attainable costs.  The lower formula bound
    and the signed epsilon construction place feasible costs on its upper side
    arbitrarily closely. -/
theorem higham21_theorem21_3_nonzero_formula_mem_closure_attainable_costs
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) (y : Fin n -> Real) (hy : y ≠ 0) :
    undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
        (higham21SigmaMinRow
          (undetNormwiseBackwardErrorFormulaMatrix A y)) ∈
      closure (undetNormwiseBackwardErrorValuesF theta A b y) := by
  rw [Metric.mem_closure_iff]
  intro eps heps
  obtain ⟨DeltaA, Deltab, hfeas, hcost⟩ :=
    higham21_thm21_3_nonzero_upper_epsilon
      htheta A b y hy (eps / 2) (half_pos heps)
  let c := lsNormwiseBackwardErrorCostF theta DeltaA Deltab
  refine ⟨c, ?_, ?_⟩
  · exact ⟨DeltaA, Deltab, hfeas, rfl⟩
  · have hlower :
        undetNormwiseBackwardErrorNonzeroFormulaRHS theta A b y
            (higham21SigmaMinRow
              (undetNormwiseBackwardErrorFormulaMatrix A y)) <= c := by
      exact higham21_thm21_3_nonzeroFormulaRHS_le_costF_of_feasible
        theta A b hy DeltaA Deltab hfeas
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hlower)]
    dsimp [c]
    linarith

/-- The infimum model is always attained after closing the attainable-cost
    set.  This is the strongest unconditional replacement for the printed
    minimum supported by the present feasibility predicate. -/
theorem higham21_theorem21_3_nonzero_etaF_mem_closure_attainable_costs
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) (y : Fin n -> Real) (hy : y ≠ 0) :
    undetNormwiseBackwardErrorEtaF theta A b y ∈
      closure (undetNormwiseBackwardErrorValuesF theta A b y) := by
  rw [higham21_theorem21_3_nonzero_normwise_backward_error_formula
    htheta A b y hy]
  exact higham21_theorem21_3_nonzero_formula_mem_closure_attainable_costs
    htheta A b y hy

/-- Exhaustive least-singular-vector obstruction: either one attaining vector
    has nonzero pairing and gives an exact minimum, or every attaining vector
    lies in the orthogonal hyperplane of the residual-corrected right-hand
    side. -/
theorem higham21_theorem21_3_exact_attainment_or_pairing_obstruction
    {m n : Nat} {theta : Real} (htheta : 0 <= theta)
    (A : Fin (m + 1) -> Fin n -> Real)
    (b : Fin (m + 1) -> Real) (y : Fin n -> Real) (hy : y ≠ 0) :
    (∃ (DeltaA : Fin (m + 1) -> Fin n -> Real)
        (Deltab : Fin (m + 1) -> Real),
      UndetNormwiseBackwardErrorFeasible A b y DeltaA Deltab /\
        lsNormwiseBackwardErrorCostF theta DeltaA Deltab =
          undetNormwiseBackwardErrorEtaF theta A b y) \/
      (∀ u : Fin (m + 1) -> Real, u ≠ 0 ->
        vecNorm2Sq
            (rectTransposeMulVec
              (undetNormwiseBackwardErrorFormulaMatrix A y) u) =
          higham21SigmaMinRow
                (undetNormwiseBackwardErrorFormulaMatrix A y) ^ 2 *
            vecNorm2Sq u ->
        (∑ i : Fin (m + 1),
          u i *
            (b i + higham21Thm21_3ResidualDeltab theta A b y i)) = 0) := by
  classical
  by_cases hgood :
      ∃ u : Fin (m + 1) -> Real,
        u ≠ 0 /\
          vecNorm2Sq
              (rectTransposeMulVec
                (undetNormwiseBackwardErrorFormulaMatrix A y) u) =
            higham21SigmaMinRow
                  (undetNormwiseBackwardErrorFormulaMatrix A y) ^ 2 *
              vecNorm2Sq u /\
          (∑ i : Fin (m + 1),
            u i *
              (b i + higham21Thm21_3ResidualDeltab theta A b y i)) ≠ 0
  · left
    obtain ⟨u, hu, hattain, hpair⟩ := hgood
    exact higham21_theorem21_3_etaF_is_attained_of_pairing_ne_zero
      htheta A b y u hy hu hattain hpair
  · right
    intro u hu hattain
    by_contra hpair
    exact hgood ⟨u, hu, hattain, hpair⟩

-- ============================================================
-- A scalar nonattainment witness
-- ============================================================

/-- Scalar data for which the unconstrained optimal perturbation annihilates
    the coefficient matrix and right-hand side. -/
def higham21Thm21_3ScalarNonattainmentA : Fin 1 -> Fin 1 -> Real :=
  fun _ _ => -1

def higham21Thm21_3ScalarNonattainmentB : Fin 1 -> Real :=
  fun _ => 1

def higham21Thm21_3ScalarNonattainmentY : Fin 1 -> Real :=
  fun _ => 1

theorem higham21Thm21_3ScalarNonattainmentY_ne_zero :
    higham21Thm21_3ScalarNonattainmentY ≠ 0 := by
  intro h
  have h0 := congrFun h (0 : Fin 1)
  norm_num [higham21Thm21_3ScalarNonattainmentY] at h0

/-- In the scalar example the residual-corrected right-hand side is zero, so
    every least-singular-vector choice hits the forbidden pairing hyperplane. -/
theorem higham21_theorem21_3_scalar_pairing_obstruction
    (u : Fin 1 -> Real) :
    (∑ i : Fin 1,
      u i *
        (higham21Thm21_3ScalarNonattainmentB i +
          higham21Thm21_3ResidualDeltab 1
            higham21Thm21_3ScalarNonattainmentA
            higham21Thm21_3ScalarNonattainmentB
            higham21Thm21_3ScalarNonattainmentY i)) = 0 := by
  norm_num [higham21Thm21_3ResidualDeltab,
    higham21Thm21_3ScalarNonattainmentA,
    higham21Thm21_3ScalarNonattainmentB,
    higham21Thm21_3ScalarNonattainmentY, undetResidualHigham,
    rectMatMulVec, vecNorm2Sq, Fin.sum_univ_succ]

/-- For `A = [-1]`, `b = [1]`, `y = [1]`, and `theta = 1`, no feasible
    perturbation has exactly the Sun--Sun formula cost.  Equality in the
    scalar cost forces `Delta A = [1]` and `Delta b = [-1]`, leaving the zero
    system, whose minimum-norm solution is zero rather than `y`. -/
theorem higham21_theorem21_3_scalar_formula_is_not_exactly_attainable :
    ¬ (∃ (DeltaA : Fin 1 -> Fin 1 -> Real) (Deltab : Fin 1 -> Real),
      UndetNormwiseBackwardErrorFeasible
          higham21Thm21_3ScalarNonattainmentA
          higham21Thm21_3ScalarNonattainmentB
          higham21Thm21_3ScalarNonattainmentY DeltaA Deltab /\
        lsNormwiseBackwardErrorCostF 1 DeltaA Deltab =
          undetNormwiseBackwardErrorNonzeroFormulaRHS 1
            higham21Thm21_3ScalarNonattainmentA
            higham21Thm21_3ScalarNonattainmentB
            higham21Thm21_3ScalarNonattainmentY
            (higham21SigmaMinRow
              (undetNormwiseBackwardErrorFormulaMatrix
                higham21Thm21_3ScalarNonattainmentA
                higham21Thm21_3ScalarNonattainmentY))) := by
  rintro ⟨DeltaA, Deltab, hfeas, hcost⟩
  have hy : higham21Thm21_3ScalarNonattainmentY ≠ 0 :=
    higham21Thm21_3ScalarNonattainmentY_ne_zero
  have hsigma :
      higham21SigmaMinRow
          (undetNormwiseBackwardErrorFormulaMatrix
            higham21Thm21_3ScalarNonattainmentA
            higham21Thm21_3ScalarNonattainmentY) = 0 :=
    higham21_theorem21_3_square_sigma_term_eq_zero
      higham21Thm21_3ScalarNonattainmentA
      higham21Thm21_3ScalarNonattainmentY hy
  have hsystem := congrFun hfeas.system_eq (0 : Fin 1)
  have hsystem' :
      (-1 : Real) + DeltaA 0 0 = 1 + Deltab 0 := by
    simpa [higham21Thm21_3ScalarNonattainmentA,
      higham21Thm21_3ScalarNonattainmentB,
      higham21Thm21_3ScalarNonattainmentY, rectMatMulVec,
      Fin.sum_univ_succ] using hsystem
  have hDeltab : Deltab 0 = DeltaA 0 0 - 2 := by
    linarith
  have hcost_sq :
      lsNormwiseBackwardErrorCostF 1 DeltaA Deltab ^ 2 =
        DeltaA 0 0 ^ 2 + Deltab 0 ^ 2 := by
    rw [lsNormwiseBackwardErrorCostF_sq]
    simp [frobNormSqRect, vecNorm2Sq, Fin.sum_univ_succ]
  have hformula_sq :
      undetNormwiseBackwardErrorNonzeroFormulaRHS 1
          higham21Thm21_3ScalarNonattainmentA
          higham21Thm21_3ScalarNonattainmentB
          higham21Thm21_3ScalarNonattainmentY
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix
              higham21Thm21_3ScalarNonattainmentA
              higham21Thm21_3ScalarNonattainmentY)) ^ 2 = 2 := by
    rw [undetNormwiseBackwardErrorNonzeroFormulaRHS_sq, hsigma]
    norm_num [higham21Thm21_3ScalarNonattainmentA,
      higham21Thm21_3ScalarNonattainmentB,
      higham21Thm21_3ScalarNonattainmentY, undetResidualHigham,
      rectMatMulVec, vecNorm2Sq, Fin.sum_univ_succ] <;> rfl
  have hsq :
      lsNormwiseBackwardErrorCostF 1 DeltaA Deltab ^ 2 =
        undetNormwiseBackwardErrorNonzeroFormulaRHS 1
          higham21Thm21_3ScalarNonattainmentA
          higham21Thm21_3ScalarNonattainmentB
          higham21Thm21_3ScalarNonattainmentY
          (higham21SigmaMinRow
            (undetNormwiseBackwardErrorFormulaMatrix
              higham21Thm21_3ScalarNonattainmentA
              higham21Thm21_3ScalarNonattainmentY)) ^ 2 := by
    exact congrArg (fun z : Real => z ^ 2) hcost
  rw [hcost_sq, hformula_sq] at hsq
  have hDeltaA : DeltaA 0 0 = 1 := by
    rw [hDeltab] at hsq
    nlinarith [sq_nonneg (DeltaA 0 0 - 1)]
  have hDeltab_value : Deltab 0 = -1 := by
    rw [hDeltab, hDeltaA]
    norm_num
  have hmatrix_zero :
      (fun i j => higham21Thm21_3ScalarNonattainmentA i j + DeltaA i j) =
        (0 : Fin 1 -> Fin 1 -> Real) := by
    funext i j
    fin_cases i
    fin_cases j
    norm_num [higham21Thm21_3ScalarNonattainmentA, hDeltaA]
  have hrhs_zero :
      (fun i => higham21Thm21_3ScalarNonattainmentB i + Deltab i) =
        (0 : Fin 1 -> Real) := by
    funext i
    fin_cases i
    norm_num [higham21Thm21_3ScalarNonattainmentB, hDeltab_value]
  have hzero_solution :
      rectMatMulVec
          (fun i j =>
            higham21Thm21_3ScalarNonattainmentA i j + DeltaA i j)
          (0 : Fin 1 -> Real) =
        fun i => higham21Thm21_3ScalarNonattainmentB i + Deltab i := by
    rw [hmatrix_zero, hrhs_zero]
    ext i
    simp [rectMatMulVec]
  have hmin := hfeas.min_norm (0 : Fin 1 -> Real) hzero_solution
  have hynorm : vecNorm2 higham21Thm21_3ScalarNonattainmentY = 1 := by
    norm_num [vecNorm2, vecNorm2Sq,
      higham21Thm21_3ScalarNonattainmentY, Fin.sum_univ_succ]
  rw [hynorm] at hmin
  change 1 ≤ vecNorm2 (fun _ : Fin 1 => 0) at hmin
  rw [vecNorm2_zero] at hmin
  norm_num at hmin

/-- The formula value is a closure point but is not an attainable cost in the
    scalar example. -/
theorem higham21_theorem21_3_scalar_formula_not_mem_attainable_costs :
    undetNormwiseBackwardErrorNonzeroFormulaRHS 1
        higham21Thm21_3ScalarNonattainmentA
        higham21Thm21_3ScalarNonattainmentB
        higham21Thm21_3ScalarNonattainmentY
        (higham21SigmaMinRow
          (undetNormwiseBackwardErrorFormulaMatrix
            higham21Thm21_3ScalarNonattainmentA
            higham21Thm21_3ScalarNonattainmentY)) ∉
      undetNormwiseBackwardErrorValuesF 1
        higham21Thm21_3ScalarNonattainmentA
        higham21Thm21_3ScalarNonattainmentB
        higham21Thm21_3ScalarNonattainmentY := by
  intro hmem
  rcases hmem with ⟨DeltaA, Deltab, hfeas, hvalue⟩
  exact higham21_theorem21_3_scalar_formula_is_not_exactly_attainable
    ⟨DeltaA, Deltab, hfeas, hvalue.symm⟩

/-- Consequently, the scalar infimum is not a member of its attainable-cost
    set: the source `min` cannot be strengthened unconditionally for the
    current minimum-norm feasibility predicate. -/
theorem higham21_theorem21_3_scalar_etaF_is_not_attained :
    undetNormwiseBackwardErrorEtaF 1
        higham21Thm21_3ScalarNonattainmentA
        higham21Thm21_3ScalarNonattainmentB
        higham21Thm21_3ScalarNonattainmentY ∉
      undetNormwiseBackwardErrorValuesF 1
        higham21Thm21_3ScalarNonattainmentA
        higham21Thm21_3ScalarNonattainmentB
        higham21Thm21_3ScalarNonattainmentY := by
  rw [higham21_theorem21_3_nonzero_normwise_backward_error_formula
    (theta := (1 : Real)) (by norm_num)
    higham21Thm21_3ScalarNonattainmentA
    higham21Thm21_3ScalarNonattainmentB
    higham21Thm21_3ScalarNonattainmentY
    higham21Thm21_3ScalarNonattainmentY_ne_zero]
  exact higham21_theorem21_3_scalar_formula_not_mem_attainable_costs

/-- The attainable-cost set in the scalar example is not closed.  Thus the
    usual finite-dimensional compactness route cannot turn the proven
    infimum formula into an unconditional exact minimizer. -/
theorem higham21_theorem21_3_scalar_attainable_costs_not_closed :
    ¬ (IsClosed
      (undetNormwiseBackwardErrorValuesF 1
        higham21Thm21_3ScalarNonattainmentA
        higham21Thm21_3ScalarNonattainmentB
        higham21Thm21_3ScalarNonattainmentY)) := by
  intro hclosed
  have hclosure :=
    higham21_theorem21_3_nonzero_formula_mem_closure_attainable_costs
      (theta := (1 : Real)) (by norm_num)
      higham21Thm21_3ScalarNonattainmentA
      higham21Thm21_3ScalarNonattainmentB
      higham21Thm21_3ScalarNonattainmentY
      higham21Thm21_3ScalarNonattainmentY_ne_zero
  rw [hclosed.closure_eq] at hclosure
  exact higham21_theorem21_3_scalar_formula_not_mem_attainable_costs hclosure

end NumStability
