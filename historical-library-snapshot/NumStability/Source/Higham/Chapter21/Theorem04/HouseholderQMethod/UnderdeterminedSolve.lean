import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.BackwardError.Rowwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Specifications.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.QR.Foundations.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.RankStability.FullRowRank.UnderdeterminedSolve
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation01.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation02.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation03.UnderdeterminedSolve
import NumStability.Source.Higham.Chapter21.Equation04.UnderdeterminedSpec
import NumStability.Source.Higham.Chapter21.Equation10.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Theorem04.HouseholderQMethod.UnderdeterminedSolve

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Algorithms/Underdetermined/UnderdeterminedSolve.lean
--
-- Error analysis of solution methods for underdetermined systems
-- (Higham §21.3).
--
-- Q method (Theorem 21.4): the concrete rounded Householder-QR output is
-- row-wise backward stable under an explicit source-shaped gamma/cond2
-- smallness condition. A legacy coarse Gram predicate is retained below.
--
-- SNE method: solves RᵀRy = b by two rounded triangular solves. The
-- componentwise Gram-system envelope below is only an intermediate result;
-- the source-shaped equation (21.11) endpoint uses the signed factorwise
-- Demmel--Higham cancellation developed in the dedicated Higham21SNE modules.






















namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §21.1  QR block algebra for the Q method and SNE setup
-- ============================================================











































































































































































































































































































































































































































































-- Equation (21.7): exact one-parameter first-order expansion.



































































































































































































































































































































































































































































































































































































































































-- Equation (21.7): explicit fixed-radius quadratic remainder bounds.
section Higham21Eq21_7QuadraticRemainder

open Filter
open Asymptotics






























































































































































































































































































































































































































































































set_option maxHeartbeats 5000000























































































































































































































end Higham21Eq21_7QuadraticRemainder


-- ============================================================
-- §21.2  Lemma 21.2 projector/norm bridge
-- ============================================================






























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- §21.3  Row-wise backward error for underdetermined systems
-- ============================================================























































































































































































































































































set_option maxHeartbeats 1200000










































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- §21.2  Theorem 21.3: normwise backward-error model
-- ============================================================


































































































































































































































































































































set_option maxHeartbeats 800000














































































































set_option maxHeartbeats 2000000















































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































-- ============================================================
-- §21.3  Theorem 21.4: Q method backward stability
-- ============================================================























/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing QR dependency for the Q method.  Applying Chapter 19,
    Theorem 19.4 to `Aᵀ` gives a perturbation `DeltaA0` of the original
    underdetermined matrix whose rows satisfy the printed row-wise QR bound.

    This is only the QR factorization perturbation used in the proof of
    Theorem 21.4; the triangular-solve and final `Q`-application perturbations
    remain separate obligations before the full Q-method theorem closes. -/
theorem higham21_theorem21_4_qr_transpose_row_perturbation_bound
    {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (Q : Fin n → Fin n → ℝ)
    (R_hat : Fin n → Fin m → ℝ)
    (eta : ℝ)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError n m
      (finiteTranspose A) Q R_hat eta) :
    ∃ DeltaA0 : Fin m → Fin n → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect n n m Q R_hat j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤ eta * rectRowNorm2 A i) := by
  rcases hqr.result with ⟨DeltaAT, hrep, hcol⟩
  refine ⟨finiteTranspose DeltaAT, ?_, ?_⟩
  · intro i j
    simpa [finiteTranspose] using hrep j i
  · intro i
    have hrow :=
      higham21_row_bounds_of_transposed_qr_column_bounds
        (finiteTranspose A) DeltaAT hcol i
    simpa [finiteTranspose_finiteTranspose] using hrow

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete Householder QR instantiation of the transposed row-perturbation
    dependency for `Aᵀ`.  The dimension hypotheses are the Chapter 19 tall-panel
    side conditions for the matrix `Aᵀ : ℝ^(n×m)`. -/
theorem higham21_theorem21_4_householder_qr_transpose_row_perturbation_bound
    {m n : ℕ} (fp : FPModel)
    (A : Fin m → Fin n → ℝ)
    (hm : 0 < m) (hmn : m ≤ n)
    (hvalid :
      gammaValid fp (m * householderConstructApplyGammaIndex n)) :
    ∃ DeltaA0 : Fin m → Fin n → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect n n m
          (fl_householderQRPanel_Q fp n m (finiteTranspose A))
          (fl_householderQRPanel_R fp n m (finiteTranspose A)) j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤
          H19.Theorem19_4.gamma_tilde fp n m * rectRowNorm2 A i) := by
  exact
    higham21_theorem21_4_qr_transpose_row_perturbation_bound A
      (fl_householderQRPanel_Q fp n m (finiteTranspose A))
      (fl_householderQRPanel_R fp n m (finiteTranspose A))
      (H19.Theorem19_4.gamma_tilde fp n m)
      (H19.Theorem19_4.householder_qr_backward_error
        fp n m (finiteTranspose A) hm hmn hvalid)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular-solve dependency for the Q-method proof.  Applying the existing
    forward-substitution backward-error theorem to `R_hatᵀ` gives the printed
    perturbation form `(R_hat + DeltaR)ᵀ y_hat1 = b` with a componentwise
    `gamma_m` bound on `DeltaR`. -/
theorem higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
    (fp : FPModel) (m : ℕ)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      ∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i := by
  let L : Fin m → Fin m → ℝ := matTranspose R_hat
  have hLdiag : ∀ i : Fin m, L i i ≠ 0 := by
    intro i
    simpa [L, matTranspose] using hdiag i
  have hlower : ∀ i j : Fin m, i.val < j.val → L i j = 0 := by
    intro i j hij
    simpa [L, matTranspose] using hupper j i hij
  obtain ⟨DeltaL, hDeltaL, hsolve⟩ :=
    forwardSub_backward_error fp m L b hLdiag hlower hvalid
  let DeltaR : Fin m → Fin m → ℝ := matTranspose DeltaL
  refine ⟨DeltaR, ?_, ?_⟩
  · intro i j
    simpa [DeltaR, L, matTranspose] using hDeltaL j i
  · intro i
    simpa [DeltaR, L, matTranspose, matMulVec] using hsolve i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular perturbation nonsingularity for the rounded `R_hat^T` solve.
    If an upper-triangular factor has nonzero diagonal and the perturbation is
    entrywise relatively bounded by a factor below one, then the perturbed
    transpose factor remains nonsingular. -/
theorem higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
    {m : ℕ}
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    {eta : ℝ} (heta_lt : eta < 1)
    (hDelta : ∀ i j, |DeltaR i j| ≤ eta * |R_hat i j|) :
    Matrix.det
        (matTranspose (fun a b => R_hat a b + DeltaR a b) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let Tpert : Fin m → Fin m → ℝ :=
    matTranspose (fun a b => R_hat a b + DeltaR a b)
  have hlowerPert : ∀ i j : Fin m, i.val < j.val → Tpert i j = 0 := by
    intro i j hij
    have hR : R_hat j i = 0 := hupper j i hij
    have hbound : |DeltaR j i| ≤ 0 := by
      simpa [hR] using hDelta j i
    have hDeltaZero : DeltaR j i = 0 := by
      exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg (DeltaR j i)))
    simp [Tpert, matTranspose, hR, hDeltaZero]
  have hdiagPert : ∀ i : Fin m, Tpert i i ≠ 0 := by
    intro i hzero
    have hsum : R_hat i i + DeltaR i i = 0 := by
      simpa [Tpert, matTranspose] using hzero
    have hDelta_eq : DeltaR i i = -R_hat i i := by
      linarith
    have habs_eq : |DeltaR i i| = |R_hat i i| := by
      rw [hDelta_eq, abs_neg]
    have hle : |R_hat i i| ≤ eta * |R_hat i i| := by
      simpa [habs_eq] using hDelta i i
    have hpos : 0 < |R_hat i i| := abs_pos.mpr (hdiag i)
    nlinarith
  have hdet :
      Matrix.det (Tpert : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_lower_triangular_diag_ne_zero m
      Tpert
      hlowerPert hdiagPert
  simpa [Tpert] using hdet

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    triangular-solve handoff into the exact Q-method minimum-norm theorem.
    The rounded solve of `R_hat^T y = b` supplies a perturbation `DeltaR`;
    if the perturbed transpose factor is nonsingular, then the formed
    Q-method vector is the exact minimum-norm solution for the corresponding
    perturbed QR-coordinate system.

    This is not the full row-wise backward-stability theorem: it isolates the
    remaining nonsingularity and row-wise perturbation obligations from the
    already proved triangular-solve backward-error certificate. -/
theorem higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
    {m k : ℕ} (fp : FPModel)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      (Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 →
        RectMinNormSolution m (m + k)
          (finiteTranspose
            (matMulRectLeft Q
              (lsQRTallBlock (k := k) (fun a b => R_hat a b + DeltaR a b))))
          b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m (matTranspose R_hat) b)
              (0 : Fin k → ℝ)))) := by
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalid
  refine ⟨DeltaR, hDeltaR, hsolve, ?_⟩
  intro hdetT
  let Rpert : Fin m → Fin m → ℝ := fun a b => R_hat a b + DeltaR a b
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  have hy1 : (fun j : Fin m => ∑ i : Fin m, Rpert i j * y1 i) = b := by
    ext j
    simpa [Rpert, y1, matMulVec, matTranspose] using hsolve j
  exact
    higham21_eq21_3_q_method_min_norm_of_qr_det_ne_zero
      Q hQ Rpert b y1 hdetT hy1

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free triangular-solve handoff for the Q-method minimum-norm
    theorem.  The stronger guard `gammaValid fp (2*m)` makes `gamma_m < 1`,
    so the componentwise triangular perturbation preserves nonsingularity of
    the perturbed transpose factor. -/
theorem higham21_theorem21_4_forwardSub_q_method_min_norm_handoff_of_gammaValid2
    {m k : ℕ} (fp : FPModel)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      RectMinNormSolution m (m + k)
        (finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k) (fun a b => R_hat a b + DeltaR a b))))
        b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ))) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hminCond⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff
      fp Q hQ R_hat b hdiag hupper hvalid
  have hdet :
      Matrix.det
          (matTranspose (fun a b => R_hat a b + DeltaR a b) :
            Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_theorem21_4_perturbed_transpose_factor_det_ne_zero_of_componentwise_bound
      R_hat DeltaR hdiag hupper (gamma_lt_one fp m hvalid2) hDeltaR
  exact ⟨DeltaR, hDeltaR, hsolve, hminCond hdet⟩










































































































































































































/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    QR assembly equality for adding the triangular-solve perturbation to an
    existing QR perturbation.  If `A + DeltaA0` is represented by
    `(Q [R_hat;0])^T`, then adding the lifted block
    `(Q [DeltaR;0])^T` gives the represented system
    `(Q [R_hat + DeltaR;0])^T`. -/
theorem higham21_theorem21_4_qr_deltaR_assembly_eq
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat))) :
    (fun i j =>
        A i j +
          (DeltaA0 i j +
            finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) i j)) =
      finiteTranspose
        (matMulRectLeft Q
          (lsQRTallBlock (k := k)
            (fun i j => R_hat i j + DeltaR i j))) := by
  have hblock :
      (fun i j =>
          lsQRTallBlock (k := k) R_hat i j +
            lsQRTallBlock (k := k) DeltaR i j) =
        lsQRTallBlock (k := k)
          (fun i j => R_hat i j + DeltaR i j) :=
    lsQRTallBlock_add R_hat DeltaR
  have hmul :
      (fun i j =>
          matMulRectLeft Q (lsQRTallBlock (k := k) R_hat) i j +
            matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) i j) =
        matMulRectLeft Q
          (lsQRTallBlock (k := k)
            (fun i j => R_hat i j + DeltaR i j)) := by
    rw [← hblock]
    exact (matMulRectLeft_add_right Q
      (lsQRTallBlock (k := k) R_hat)
      (lsQRTallBlock (k := k) DeltaR)).symm
  ext i j
  have hAij := congrFun (congrFun hA i) j
  have hmulji := congrFun (congrFun hmul j) i
  simp [finiteTranspose] at hAij hmulji ⊢
  calc
    A i j + (DeltaA0 i j + matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) j i)
        = (A i j + DeltaA0 i j) +
            matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) j i := by ring
    _ = matMulRectLeft Q (lsQRTallBlock (k := k) R_hat) j i +
          matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR) j i := by
          rw [hAij]
    _ = matMulRectLeft Q
          (lsQRTallBlock (k := k)
            (fun i j => R_hat i j + DeltaR i j)) j i := hmulji

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise triangle-inequality adapter for assembling two perturbation
    bounds against the same source matrix. -/
theorem higham21_rectRowNorm2_add_le_of_row_bounds
    {m n : ℕ}
    (DeltaA DeltaB A : Fin m → Fin n → ℝ)
    {etaA etaB : ℝ}
    (hDeltaA : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤ etaA * rectRowNorm2 A i)
    (hDeltaB : ∀ i : Fin m,
      rectRowNorm2 DeltaB i ≤ etaB * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2 (fun r c => DeltaA r c + DeltaB r c) i ≤
      (etaA + etaB) * rectRowNorm2 A i := by
  calc
    rectRowNorm2 (fun r c => DeltaA r c + DeltaB r c) i
        = vecNorm2 (fun j : Fin n => DeltaA i j + DeltaB i j) := rfl
    _ ≤ vecNorm2 (fun j : Fin n => DeltaA i j) +
          vecNorm2 (fun j : Fin n => DeltaB i j) := by
          exact vecNorm2_add_le
            (fun j : Fin n => DeltaA i j)
            (fun j : Fin n => DeltaB i j)
    _ = rectRowNorm2 DeltaA i + rectRowNorm2 DeltaB i := rfl
    _ ≤ etaA * rectRowNorm2 A i + etaB * rectRowNorm2 A i := by
          exact add_le_add (hDeltaA i) (hDeltaB i)
    _ = (etaA + etaB) * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    once the QR perturbation and lifted triangular-solve perturbation are
    bounded row-wise against `A`, their assembled common perturbation satisfies
    the summed row-wise bound used by the Q-method proof. -/
theorem higham21_theorem21_4_common_perturbation_row_bound_of_qr_and_lifted_bounds
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR : ℝ}
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i : Fin m,
      rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i ≤
        etaR * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2
        (fun r c =>
          DeltaA0 r c +
            finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) r c) i ≤
      (etaQR + etaR) * rectRowNorm2 A i :=
  higham21_rectRowNorm2_add_le_of_row_bounds
    DeltaA0
    (finiteTranspose
      (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)))
    A hDeltaA0 hDeltaR i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    an orthogonal left factor preserves each column norm of a rectangular
    panel.  This is the per-column form needed for the lifted triangular
    perturbation `(Q [DeltaR;0])^T`. -/
theorem higham21_columnFrob_matMulRectLeft_orthogonal
    {m n : ℕ}
    (Q : Fin m → Fin m → ℝ)
    (B : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (j : Fin n) :
    columnFrob (matMulRectLeft Q B) j = columnFrob B j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  have hcol :
      (fun i : Fin m => matMulRectLeft Q B i j) =
        matMulVec m Q (fun i : Fin m => B i j) := by
    ext i
    rfl
  rw [hcol]
  exact vecNorm2_orthogonal Q (fun i : Fin m => B i j) hQ

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    stacking zero rows below a square triangular perturbation preserves each
    column Frobenius norm. -/
theorem higham21_columnFrob_lsQRTallBlock
    {m k : ℕ}
    (R : Fin m → Fin m → ℝ)
    (j : Fin m) :
    columnFrob (lsQRTallBlock (k := k) R) j = columnFrob R j := by
  rw [columnFrob_eq_vecNorm2, columnFrob_eq_vecNorm2]
  have hcol :
      (fun i : Fin (m + k) => lsQRTallBlock (k := k) R i j) =
        Fin.append (fun i : Fin m => R i j) (0 : Fin k → ℝ) := by
    ext i
    refine Fin.addCases
      (motive := fun i : Fin (m + k) =>
        lsQRTallBlock (k := k) R i j =
          Fin.append (fun i : Fin m => R i j) (0 : Fin k → ℝ) i)
      ?left ?right i
    · intro i
      simp [lsQRTallBlock, Fin.append_left]
    · intro i
      simp [lsQRTallBlock, Fin.append_right]
  rw [hcol]
  unfold vecNorm2
  rw [lsVecNorm2Sq_append]
  simp [vecNorm2Sq]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the lifted triangular block has row norm equal to the corresponding column
    norm of the triangular perturbation when the QR factor is orthogonal. -/
theorem higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
    {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (DeltaR : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (j : Fin m) :
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) j =
      columnFrob DeltaR j := by
  calc
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) j
        = columnFrob
            (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) j := by
          simp [rectRowNorm2, columnFrob_eq_vecNorm2, finiteTranspose]
    _ = columnFrob (lsQRTallBlock (k := k) DeltaR) j := by
          exact higham21_columnFrob_matMulRectLeft_orthogonal
            Q (lsQRTallBlock (k := k) DeltaR) hQ j
    _ = columnFrob DeltaR j := higham21_columnFrob_lsQRTallBlock DeltaR j

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    columnwise control of the triangular perturbation gives the row-wise bound
    for its lifted original-coordinate perturbation. -/
theorem higham21_theorem21_4_lifted_deltaR_row_bound_of_column_bound
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (DeltaR : Fin m → Fin m → ℝ)
    {etaR : ℝ}
    (hQ : IsOrthogonal (m + k) Q)
    (hDeltaRCol : ∀ i : Fin m,
      columnFrob DeltaR i ≤ etaR * rectRowNorm2 A i)
    (i : Fin m) :
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i ≤
      etaR * rectRowNorm2 A i := by
  rw [higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
    Q DeltaR hQ i]
  exact hDeltaRCol i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    entrywise relative bounds on the triangular perturbation imply the
    corresponding columnwise Euclidean bound. -/
theorem higham21_columnFrob_le_of_entrywise_relative_bound
    {m : ℕ}
    (R DeltaR : Fin m → Fin m → ℝ)
    {eta : ℝ} (heta : 0 ≤ eta)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ eta * |R i j|)
    (j : Fin m) :
    columnFrob DeltaR j ≤ eta * columnFrob R j := by
  calc
    columnFrob DeltaR j
        = vecNorm2 (fun i : Fin m => DeltaR i j) := by
          rw [columnFrob_eq_vecNorm2]
    _ ≤ vecNorm2 (fun i : Fin m => eta * |R i j|) := by
          exact
            vecNorm2_le_of_abs_le
              (fun i : Fin m => DeltaR i j)
              (fun i : Fin m => eta * |R i j|)
              (fun i => hDeltaR i j)
    _ = eta * columnFrob R j := by
          rw [vecNorm2_smul, abs_of_nonneg heta, vecNorm2_abs,
            columnFrob_eq_vecNorm2]

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    if `A + DeltaA0 = (Q [R_hat;0])^T`, then the row norm of the assembled
    QR side is the corresponding column norm of `R_hat`. -/
theorem higham21_theorem21_4_assembled_qr_row_norm_eq_R_columnFrob
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (j : Fin m) :
    rectRowNorm2 (fun i j => A i j + DeltaA0 i j) j =
      columnFrob R_hat j := by
  rw [hA]
  exact higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
    Q R_hat hQ j

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    componentwise triangular-solve backward error, together with the QR
    assembly and QR row perturbation bound, gives a row-wise bound for the
    lifted triangular perturbation `(Q [DeltaR;0])^T` relative to the original
    underdetermined matrix `A`. -/
theorem higham21_theorem21_4_lifted_deltaR_row_bound_of_entrywise_relative
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR : ℝ} (hetaR : 0 ≤ etaR)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (i : Fin m) :
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i ≤
      etaR * (1 + etaQR) * rectRowNorm2 A i := by
  have hcol :
      columnFrob DeltaR i ≤ etaR * columnFrob R_hat i :=
    higham21_columnFrob_le_of_entrywise_relative_bound
      R_hat DeltaR hetaR hDeltaR i
  have hassembled_eq :
      rectRowNorm2 (fun r c => A r c + DeltaA0 r c) i =
        columnFrob R_hat i :=
    higham21_theorem21_4_assembled_qr_row_norm_eq_R_columnFrob
      A DeltaA0 Q R_hat hQ hA i
  have hAself : ∀ r : Fin m,
      rectRowNorm2 A r ≤ (1 : ℝ) * rectRowNorm2 A r := by
    intro r
    rw [one_mul]
  have hassembled_bound :
      rectRowNorm2 (fun r c => A r c + DeltaA0 r c) i ≤
        (1 + etaQR) * rectRowNorm2 A i :=
    higham21_rectRowNorm2_add_le_of_row_bounds
      A DeltaA0 A hAself hDeltaA0 i
  calc
    rectRowNorm2
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR))) i
        = columnFrob DeltaR i := by
          exact higham21_theorem21_4_lifted_deltaR_row_norm_eq_columnFrob
            Q DeltaR hQ i
    _ ≤ etaR * columnFrob R_hat i := hcol
    _ = etaR * rectRowNorm2 (fun r c => A r c + DeltaA0 r c) i := by
          rw [← hassembled_eq]
    _ ≤ etaR * ((1 + etaQR) * rectRowNorm2 A i) :=
          mul_le_mul_of_nonneg_left hassembled_bound hetaR
    _ = etaR * (1 + etaQR) * rectRowNorm2 A i := by ring

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    combines the QR row perturbation and the componentwise triangular-solve
    perturbation into the row-wise bound for the common perturbation assembled
    as `DeltaA0 + (Q [DeltaR;0])^T`. -/
theorem higham21_theorem21_4_common_perturbation_row_bound_of_entrywise_deltaR
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR : ℝ} (hetaR : 0 ≤ etaR)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (i : Fin m) :
    rectRowNorm2
        (fun r c =>
          DeltaA0 r c +
            finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) r c) i ≤
      (etaQR + etaR * (1 + etaQR)) * rectRowNorm2 A i :=
  higham21_theorem21_4_common_perturbation_row_bound_of_qr_and_lifted_bounds
    A DeltaA0 Q DeltaR hDeltaA0
    (fun r =>
      higham21_theorem21_4_lifted_deltaR_row_bound_of_entrywise_relative
        A DeltaA0 Q R_hat DeltaR hetaR hQ hA hDeltaA0 hDeltaR r)
    i

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-free row-wise Q-method handoff after QR assembly.  Given the
    QR perturbation for `A`, the componentwise triangular-solve perturbation,
    and the orthogonal QR factor, the assembled perturbation
    `DeltaA0 + (Q [DeltaR;0])^T` is a row-wise backward-error witness. -/
theorem higham21_theorem21_4_rowwise_backward_error_of_qr_assembly_and_entrywise_deltaR
    {m k : ℕ} (fp : FPModel)
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R_hat : Fin m → Fin m → ℝ) (b : Fin m → ℝ)
    (hdiag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hupper : IsUpperTrapezoidal m m R_hat)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    {etaQR : ℝ} (hetaQR : 0 ≤ etaQR)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i) :
    ∃ DeltaR : Fin m → Fin m → ℝ,
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      (∀ i,
        matMulVec m (matTranspose (fun a b => R_hat a b + DeltaR a b))
          (fl_forwardSub fp m (matTranspose R_hat) b) i = b i) ∧
      UndetRowwiseBackwardErrorBounded m (m + k) A b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ)))
        (etaQR + gamma fp m * (1 + etaQR)) := by
  obtain ⟨DeltaR, hDeltaR, hsolve, hmin⟩ :=
    higham21_theorem21_4_forwardSub_q_method_min_norm_handoff_of_gammaValid2
      fp Q hQ R_hat b hdiag hupper hvalid hvalid2
  let DeltaA : Fin m → Fin (m + k) → ℝ :=
    fun i j =>
      DeltaA0 i j +
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) i j
  have hqr :
      (fun i j => A i j + DeltaA i j) =
        finiteTranspose
          (matMulRectLeft Q
            (lsQRTallBlock (k := k)
              (fun i j => R_hat i j + DeltaR i j))) := by
    simpa [DeltaA] using
      higham21_theorem21_4_qr_deltaR_assembly_eq
        A DeltaA0 Q R_hat DeltaR hA
  have hminA :
      RectMinNormSolution m (m + k)
        (fun i j => A i j + DeltaA i j) b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ))) := by
    rw [hqr]
    exact hmin
  have hgamma_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp hvalid
  have heta : 0 ≤ etaQR + gamma fp m * (1 + etaQR) := by
    have hone_eta : 0 ≤ 1 + etaQR := by linarith
    exact add_nonneg hetaQR (mul_nonneg hgamma_nonneg hone_eta)
  have hrow : ∀ i : Fin m,
      rectRowNorm2 DeltaA i ≤
        (etaQR + gamma fp m * (1 + etaQR)) * rectRowNorm2 A i := by
    intro i
    simpa [DeltaA] using
      higham21_theorem21_4_common_perturbation_row_bound_of_entrywise_deltaR
        A DeltaA0 Q R_hat DeltaR hgamma_nonneg hQ hA hDeltaA0 hDeltaR i
  exact
    ⟨DeltaR, hDeltaR, hsolve,
      higham21_rowwise_backward_error_bound_witness
        m (m + k) A DeltaA b
        (matMulVec (m + k) Q
          (Fin.append
            (fl_forwardSub fp m (matTranspose R_hat) b)
            (0 : Fin k → ℝ)))
        (etaQR + gamma fp m * (1 + etaQR))
        heta hminA hrow⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    row-wise Q-method handoff from a Chapter 19 QR certificate for `A^T`.
    The tall QR factor is reduced to its top square block using its
    upper-trapezoidal shape, then fed to the assembled row-wise handoff. -/
theorem higham21_theorem21_4_rowwise_backward_error_of_qr_transpose_certificate
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (b : Fin m → ℝ)
    {etaQR : ℝ} (hetaQR : 0 ≤ etaQR)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError (m + k) m
      (finiteTranspose A) Q R_tall etaQR)
    (hdiag : ∀ i : Fin m, R_tall (Fin.castAdd k i) i ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaA0 : Fin m → Fin (m + k) → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect (m + k) (m + k) m Q R_tall j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i) ∧
      ∃ DeltaR : Fin m → Fin m → ℝ,
        (∀ i j, |DeltaR i j| ≤
          gamma fp m * |R_tall (Fin.castAdd k i) j|) ∧
        (∀ i,
          matMulVec m
            (matTranspose
              (fun a b => R_tall (Fin.castAdd k a) b + DeltaR a b))
            (fl_forwardSub fp m
              (matTranspose (fun a b => R_tall (Fin.castAdd k a) b)) b) i =
            b i) ∧
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k) Q
            (Fin.append
              (fl_forwardSub fp m
                (matTranspose (fun a b => R_tall (Fin.castAdd k a) b)) b)
              (0 : Fin k → ℝ)))
          (etaQR + gamma fp m * (1 + etaQR)) := by
  let R_top : Fin m → Fin m → ℝ :=
    fun i j => R_tall (Fin.castAdd k i) j
  obtain ⟨DeltaA0, hDeltaA0Rep, hDeltaA0Row⟩ :=
    higham21_theorem21_4_qr_transpose_row_perturbation_bound
      A Q R_tall etaQR hqr
  have hRblock :
      R_tall = lsQRTallBlock (k := k) R_top :=
    lsQRTallBlock_of_upper_trapezoidal R_tall hqr.upper
  have hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_top)) := by
    ext i j
    calc
      A i j + DeltaA0 i j =
          matMulRect (m + k) (m + k) m Q R_tall j i := hDeltaA0Rep i j
      _ =
          finiteTranspose
            (matMulRectLeft Q (lsQRTallBlock (k := k) R_top)) i j := by
            simp [finiteTranspose, matMulRect, matMulRectLeft, hRblock]
  have hupperTop : IsUpperTrapezoidal m m R_top :=
    lsQRTallBlock_top_upper_of_upper_trapezoidal R_tall hqr.upper
  obtain ⟨DeltaR, hDeltaR, hsolve, hcert⟩ :=
    higham21_theorem21_4_rowwise_backward_error_of_qr_assembly_and_entrywise_deltaR
      fp A DeltaA0 Q hqr.orth R_top b hdiag hupperTop
      hvalid hvalid2 hetaQR hA hDeltaA0Row
  exact ⟨DeltaA0, hDeltaA0Rep, hDeltaA0Row, DeltaR,
    by simpa [R_top] using hDeltaR,
    by simpa [R_top] using hsolve,
    by simpa [R_top] using hcert⟩

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete Householder-QR specialization of the row-wise Q-method handoff
    for `A^T`.  The remaining diagonal hypothesis is the local nonbreakdown
    condition for the computed top square triangular block. -/
theorem higham21_theorem21_4_rowwise_backward_error_of_householder_qr_transpose
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : ∀ i : Fin m,
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) i ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    ∃ DeltaA0 : Fin m → Fin (m + k) → ℝ,
      (∀ i j, A i j + DeltaA0 i j =
        matMulRect (m + k) (m + k) m
          (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
          (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
          j i) ∧
      (∀ i : Fin m,
        rectRowNorm2 DeltaA0 i ≤
          H19.Theorem19_4.gamma_tilde fp (m + k) m * rectRowNorm2 A i) ∧
      ∃ DeltaR : Fin m → Fin m → ℝ,
        (∀ i j, |DeltaR i j| ≤
          gamma fp m *
            |fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
              (Fin.castAdd k i) j|) ∧
        (∀ i,
          matMulVec m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b + DeltaR a b))
            (fl_forwardSub fp m
              (matTranspose
                (fun a b =>
                  fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                    (Fin.castAdd k a) b)) b) i =
            b i) ∧
        UndetRowwiseBackwardErrorBounded m (m + k) A b
          (matMulVec (m + k)
            (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
            (Fin.append
              (fl_forwardSub fp m
                (matTranspose
                  (fun a b =>
                    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                      (Fin.castAdd k a) b)) b)
              (0 : Fin k → ℝ)))
          (H19.Theorem19_4.gamma_tilde fp (m + k) m +
            gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) := by
  exact
    higham21_theorem21_4_rowwise_backward_error_of_qr_transpose_certificate
      fp A
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
      b
      (H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR)
      (H19.Theorem19_4.householder_qr_backward_error
        fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR)
      hdiag hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    named side condition that the computed top square block of the tall
    Householder QR factor for `A^T` has no zero diagonal pivots.  The printed
    theorem assumes the Q-method triangular solve does not break down; this
    predicate records exactly the local formal obligation still exposed by
    the concrete QR path. -/
def Higham21QMethodTopBlockNonbreakdown
    (m k : ℕ) (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) : Prop :=
  lsTheorem20_4ComputedQRNonbreakdown fp (finiteTranspose A)

theorem Higham21QMethodTopBlockNonbreakdown.of_topBlock_det_ne_zero
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hdet :
      Matrix.det
        ((fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0) :
    Higham21QMethodTopBlockNonbreakdown m k fp A := by
  let R_top : Fin m → Fin m → ℝ :=
    fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal fp (m + k) m
      (finiteTranspose A)
  have hupperTop : ∀ i j : Fin m, j.val < i.val → R_top i j = 0 := by
    simpa [R_top] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, R_top i i ≠ 0 :=
    diag_ne_zero_of_upper_triangular_det_ne_zero m R_top hupperTop (by
      simpa [R_top] using hdet)
  simpa [Higham21QMethodTopBlockNonbreakdown,
    lsTheorem20_4ComputedQRNonbreakdown, R_top] using hdiag

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing concrete domain for the Q-method Householder path.  The
    printed full-row-rank condition for `A` is represented as full column rank
    of `A^T`; the current verified QR API still also exposes the computed
    top-block nonbreakdown condition needed by the triangular solve. -/
def Higham21QMethodFullRowRankComputedQRDomain
    (m k : ℕ) (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) : Prop :=
  lsTheorem20_4FullRankComputedQRDomain fp (finiteTranspose A)

theorem Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown
    {m k : ℕ} {fp : FPModel}
    {A : Fin m → Fin (m + k) → ℝ}
    (h : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    Higham21QMethodTopBlockNonbreakdown m k fp A :=
  lsTheorem20_4FullRankComputedQRDomain.computedQRNonbreakdown fp h

/-- Full row rank of the Q-method source matrix makes its Gram matrix
    A A^T nonsingular. -/
theorem higham21_qmethod_full_row_rank_gram_det_ne_zero
    {m k : ℕ} {fp : FPModel}
    {A : Fin m → Fin (m + k) → ℝ}
    (h : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  have hfull : lsRealRectColRank (finiteTranspose A) = m :=
    lsTheorem20_4FullRankComputedQRDomain.fullRank fp h
  have hinj : Function.Injective (rectMatMulVec (finiteTranspose A)) :=
    lsRealRectColRank_rectMatMulVec_injective_of_colRank_eq_card
      (finiteTranspose A) hfull
  have hdet :
      Matrix.det
        (rectLSGram (finiteTranspose A) :
          Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    rectLSGram_det_ne_zero_of_rectMatMulVec_injective
      (finiteTranspose A) hinj
  simpa [rectLSGram, rectGram, finiteTranspose] using hdet

/-- The canonical table A^T(AA^T)^{-1} is a right inverse throughout the
    source-facing full-row-rank Q-method domain. -/
theorem higham21_qmethod_full_row_rank_canonical_right_inverse
    {m k : ℕ} {fp : FPModel}
    {A : Fin m → Fin (m + k) → ℝ}
    (h : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    rectMatMul A (undetAplusOfGramNonsingInv A) = idMatrix m := by
  exact
    higham21_eq21_4_rect_pseudoinverse_right_inverse_of_gram_det_ne_zero A
      (higham21_qmethod_full_row_rank_gram_det_ne_zero h)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the concrete row-wise coefficient currently proved for the Householder
    Q-method path: the Chapter 19 QR perturbation factor plus the triangular
    solve factor and their first-order product. -/
noncomputable def Higham21QMethodRowwiseCoefficient
    (fp : FPModel) (m k : ℕ) : ℝ :=
  H19.Theorem19_4.gamma_tilde fp (m + k) m +
    gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)

theorem Higham21QMethodRowwiseCoefficient_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hvalid : gammaValid fp m) :
    0 ≤ Higham21QMethodRowwiseCoefficient fp m k := by
  have hqr_nonneg :
      0 ≤ H19.Theorem19_4.gamma_tilde fp (m + k) m :=
    H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hgamma_nonneg : 0 ≤ gamma fp m := gamma_nonneg fp hvalid
  have hone : 0 ≤ 1 + H19.Theorem19_4.gamma_tilde fp (m + k) m := by
    linarith
  simpa [Higham21QMethodRowwiseCoefficient] using
    add_nonneg hqr_nonneg (mul_nonneg hgamma_nonneg hone)








/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the proved Q-method row-wise coefficient is absorbed by one larger gamma
    term.  This is the concrete repository analogue of the printed
    dimension-dependent gamma factor in the row perturbation bound. -/
theorem Higham21QMethodRowwiseCoefficient_le_gamma_index
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    Higham21QMethodRowwiseCoefficient fp m k ≤
      gamma fp (Higham21QMethodRowwiseGammaIndex m k) := by
  let q : ℕ := m * householderConstructApplyGammaIndex (m + k)
  have hsum :
      gamma fp q + gamma fp m + gamma fp q * gamma fp m ≤
        gamma fp (q + m) :=
    gamma_sum_le fp q m (by
      simpa [Higham21QMethodRowwiseGammaIndex, q] using hvalid)
  have hcoeff :
      Higham21QMethodRowwiseCoefficient fp m k =
        gamma fp q + gamma fp m + gamma fp q * gamma fp m := by
    simp [Higham21QMethodRowwiseCoefficient, H19.Theorem19_4.gamma_tilde, q]
    ring
  calc
    Higham21QMethodRowwiseCoefficient fp m k =
        gamma fp q + gamma fp m + gamma fp q * gamma fp m := hcoeff
    _ ≤ gamma fp (q + m) := hsum
    _ = gamma fp (Higham21QMethodRowwiseGammaIndex m k) := by
      simp [Higham21QMethodRowwiseGammaIndex, q]








































/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    source-facing row-wise backward-stability wrapper for any Chapter 19 QR
    certificate of `A^T`.  This projects the detailed `DeltaA0`/`DeltaR`
    witness into the row-wise backward-error predicate used by the theorem. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_qr_transpose_certificate
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (b : Fin m → ℝ)
    {etaQR : ℝ} (hetaQR : 0 ≤ etaQR)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError (m + k) m
      (finiteTranspose A) Q R_tall etaQR)
    (hdiag : ∀ i : Fin m, R_tall (Fin.castAdd k i) i ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k) Q
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose (fun a b => R_tall (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (etaQR + gamma fp m * (1 + etaQR)) := by
  obtain ⟨_, _, _, _, _, _, hcert⟩ :=
    higham21_theorem21_4_rowwise_backward_error_of_qr_transpose_certificate
      fp A Q R_tall b hetaQR hqr hdiag hvalid hvalid2
  exact hcert

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete source-facing row-wise backward-stability theorem for the
    Householder QR panel applied to `A^T`, with the remaining nonbreakdown
    condition named explicitly by `Higham21QMethodTopBlockNonbreakdown`. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_householder_qr_transpose
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdiag : Higham21QMethodTopBlockNonbreakdown m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (H19.Theorem19_4.gamma_tilde fp (m + k) m +
        gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_qr_transpose_certificate
      fp A
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
      b
      (H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR)
      (H19.Theorem19_4.householder_qr_backward_error
        fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR)
      hdiag hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-facing nonbreakdown variant.  A nonzero determinant of the
    computed top square `R` block implies the diagonal nonbreakdown field
    consumed by the concrete Q-method row-wise theorem. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_topBlock_det_ne_zero
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdet :
      Matrix.det
        ((fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (Higham21QMethodRowwiseCoefficient fp m k) := by
  simpa [Higham21QMethodRowwiseCoefficient] using
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_householder_qr_transpose
      fp A b hm hvalidQR
      (Higham21QMethodTopBlockNonbreakdown.of_topBlock_det_ne_zero fp A hdet)
      hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    concrete row-wise backward-stability wrapper under the source-facing
    full-row-rank/computed-QR domain for the Householder QR of `A^T`. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (H19.Theorem19_4.gamma_tilde fp (m + k) m +
        gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_householder_qr_transpose
      fp A b hm hvalidQR
      (Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain)
      hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    same concrete Q-method row-wise theorem with the proved coefficient named
    explicitly for later comparison with the printed asymptotic coefficient. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_coefficient
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (Higham21QMethodRowwiseCoefficient fp m k) := by
  simpa [Higham21QMethodRowwiseCoefficient] using
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain
      fp A b hm hvalidQR hdomain hvalid hvalid2

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    conservative-coefficient handoff.  Any nonnegative source coefficient
    that dominates `Higham21QMethodRowwiseCoefficient` inherits the concrete
    row-wise backward-stability certificate. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_of_coefficient_le
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    {eta : ℝ} (heta : 0 ≤ eta)
    (hcoeff : Higham21QMethodRowwiseCoefficient fp m k ≤ eta) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      eta := by
  exact
    higham21_rowwise_backward_error_bound_mono
      (higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_coefficient
        fp A b hm hvalidQR hdomain hvalid hvalid2)
      heta hcoeff

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    single-gamma row-wise Q-method stability wrapper under the source-facing
    full-row-rank/computed-QR domain. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hvalidQR :
      gammaValid fp (m * householderConstructApplyGammaIndex (m + k)))
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp m)
    (hvalid2 : gammaValid fp (2 * m))
    (hvalidCoeff : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (gamma fp (Higham21QMethodRowwiseGammaIndex m k)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_of_coefficient_le
      fp A b hm hvalidQR hdomain hvalid hvalid2
      (gamma_nonneg fp hvalidCoeff)
      (Higham21QMethodRowwiseCoefficient_le_gamma_index fp m k hvalidCoeff)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    single-gamma row-wise Q-method stability under the source-facing
    full-row-rank/computed-QR domain.  Validity of the displayed combined
    gamma index discharges every smaller QR and triangular-solve validity
    condition. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma_single_valid
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (gamma fp (Higham21QMethodRowwiseGammaIndex m k)) := by
  exact
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma
      fp A b hm
      (Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalid)
      hdomain
      (Higham21QMethodRowwiseGammaIndex.validM fp m k hvalid)
      (Higham21QMethodRowwiseGammaIndex.valid2M fp m k hvalid)
      hvalid

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    determinant-facing single-gamma Q-method stability theorem.  A single
    validity assumption at the combined index supplies all validity conditions
    used by the QR and triangular-solve certificates. -/
theorem higham21_theorem21_4_q_method_rowwise_backward_stable_of_topBlock_det_ne_zero_gamma_single_valid
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdet :
      Matrix.det
        ((fun i j =>
          fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
            (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hvalid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k)) :
    UndetRowwiseBackwardErrorBounded m (m + k) A b
      (matMulVec (m + k)
        (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
        (Fin.append
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)
          (0 : Fin k → ℝ)))
      (gamma fp (Higham21QMethodRowwiseGammaIndex m k)) := by
  have hcert :=
    higham21_theorem21_4_q_method_rowwise_backward_stable_of_topBlock_det_ne_zero
      fp A b hm
      (Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalid)
      hdet
      (Higham21QMethodRowwiseGammaIndex.validM fp m k hvalid)
      (Higham21QMethodRowwiseGammaIndex.valid2M fp m k hvalid)
  exact
    higham21_rowwise_backward_error_bound_mono hcert
      (gamma_nonneg fp hvalid)
      (Higham21QMethodRowwiseCoefficient_le_gamma_index fp m k hvalid)


























































































































































































































































































































































































































































/-- A sufficiently small accumulated `Q_hat` perturbation has a concrete
    left inverse.  The witness is the Chapter 7 Neumann inverse candidate;
    its infinity-norm bound is retained for the later perturbation estimate. -/
theorem higham21_qhat_left_inverse_of_fixed_accum_error
    {n : ℕ}
    (Q Q_hat : Fin n → Fin n → ℝ) (eta : ℝ)
    (hn : 0 < n)
    (hQerr : HouseholderQRPanelQhatFixedAccumError n Q Q_hat eta)
    (hsmall : (n : ℝ) * eta < 1) :
    ∃ Q_inv : Fin n → Fin n → ℝ,
      matMul n Q_inv Q_hat = idMatrix n ∧
      infNorm Q_inv ≤
        ((n : ℝ) * (1 / (1 - (n : ℝ) * eta))) *
          infNorm (matTranspose Q) := by
  obtain ⟨DeltaQ, hQhat, hDeltaQ⟩ := hQerr.result
  have heta : 0 ≤ eta := le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hscale : 0 ≤ (n : ℝ) * eta :=
    mul_nonneg (Nat.cast_nonneg n) heta
  have hbound :
      infNormBound n
        (absMatrix n (matMul n (matTranspose Q) DeltaQ))
        ((n : ℝ) * eta) :=
    higham21_infNormBound_abs_orthogonal_transpose_mul
      Q DeltaQ eta hn hQerr.orth hDeltaQ
  let Q_inv : Fin n → Fin n → ℝ :=
    ch7Problem711PerturbedInverseCandidate n (matTranspose Q) DeltaQ
  have hRightRaw :
      IsRightInverse n (fun i j => Q i j + DeltaQ i j) Q_inv := by
    dsimp [Q_inv]
    exact
      problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound
        n hn Q (matTranspose Q) DeltaQ ((n : ℝ) * eta)
        hscale hsmall hQerr.orth.left_inv hbound
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhat i j
  have hRight : IsRightInverse n Q_hat Q_inv := by
    rw [hQhatEq]
    exact hRightRaw
  have hLeft : IsLeftInverse n Q_hat Q_inv :=
    isLeftInverse_of_isRightInverse Q_hat Q_inv hRight
  have hmul : matMul n Q_inv Q_hat = idMatrix n := by
    ext i j
    exact hLeft i j
  have hInvBound :
      infNorm Q_inv ≤
        ((n : ℝ) * (1 / (1 - (n : ℝ) * eta))) *
          infNorm (matTranspose Q) := by
    dsimp [Q_inv]
    exact
      problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound
        n hn (matTranspose Q) DeltaQ ((n : ℝ) * eta)
        hscale hsmall hbound
  exact ⟨Q_inv, hmul, hInvBound⟩








































































































































/-- The concrete rounded Householder factor in the computed Q method has a
    left inverse whenever its combined-index equation-(21.10) radius is less
    than one. -/
theorem higham21_theorem21_4_qhat_exists_left_inverse_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) := by
  dsimp only
  exact
    higham21_qhat_exists_left_inverse_of_fixed_accum_error_lt_one
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)
      hsmall

/-- The concrete rounded Householder factor has a left inverse with the sharp
    operator bound associated with its combined equation-(21.10) radius. -/
theorem higham21_theorem21_4_qhat_exists_left_inverse_with_opNorm2Le_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) ∧
      opNorm2Le Q_inv
        (1 / (1 - Higham21QMethodQhatRadius fp m k)) := by
  dsimp only
  exact
    higham21_qhat_exists_left_inverse_with_opNorm2Le_of_fixed_accum_error_lt_one
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)
      hsmall

/-- The concrete accumulated Householder factor used by the Q method has a
    certified left inverse under the displayed combined-index smallness
    condition. -/
theorem higham21_theorem21_4_qhat_left_inverse_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall :
      ((m + k : ℕ) : ℝ) * Higham21QMethodQhatRadius fp m k < 1) :
    let Q := fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) ∧
      infNorm Q_inv ≤
        (((m + k : ℕ) : ℝ) *
          (1 / (1 - ((m + k : ℕ) : ℝ) *
            Higham21QMethodQhatRadius fp m k))) *
          infNorm (matTranspose Q) := by
  dsimp only
  exact
    higham21_qhat_left_inverse_of_fixed_accum_error
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (Higham21QMethodQhatRadius fp m k)
      (by omega)
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)
      hsmall

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4 and equation
    (21.10): computed-Q-method package under one validity condition.  The
    ideal action by the computed orthogonal `Q` has the proved row-wise
    certificate, while the rounded accumulated `Q_hat` action is within the
    displayed equation-(21.10) vector radius.  This keeps the remaining
    row-wise transfer to `Q_hat` explicit rather than assuming it. -/
theorem higham21_theorem21_4_q_method_rowwise_and_qhat_action_of_full_row_rank_computed_qr_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    let Q := fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let y1 :=
      fl_forwardSub fp m
        (matTranspose
          (fun a b =>
            fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
              (Fin.castAdd k a) b)) b
    let z := Fin.append y1 (0 : Fin k → ℝ)
    let x := matMulVec (m + k) Q z
    let x_hat := matMulVec (m + k) Q_hat z
    UndetRowwiseBackwardErrorBounded m (m + k) A b x
        (gamma fp (Higham21QMethodComputedGammaIndex m k)) ∧
      vecNorm2 (fun i : Fin (m + k) => x_hat i - x i) ≤
        (gamma fp (Higham21QMethodComputedGammaIndex m k) *
          Real.sqrt ((m + k : ℕ) : ℝ)) * vecNorm2 y1 := by
  dsimp only
  constructor
  · have hrow :=
      higham21_theorem21_4_q_method_rowwise_backward_stable_of_full_row_rank_computed_qr_domain_gamma_single_valid
        fp A b hm hdomain
        (Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid)
    exact
      higham21_rowwise_backward_error_bound_mono hrow
        (gamma_nonneg fp hvalid)
        (Higham21QMethodComputedGammaIndex.rowwiseGamma_le fp m k hvalid)
  · have hNpos : 0 < m + k := by omega
    have haction :=
      higham21_eq21_10_q_action_vec_error_bound_of_householder_qr_panel_qhat_gamma
        fp A
        (fl_forwardSub fp m
          (matTranspose
            (fun a b =>
              fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                (Fin.castAdd k a) b)) b)
        (matMulVec (m + k)
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
          (Fin.append
            (fl_forwardSub fp m
              (matTranspose
                (fun a b =>
                  fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                    (Fin.castAdd k a) b)) b)
            (0 : Fin k → ℝ)))
        hNpos
        (Higham21QMethodComputedGammaIndex.validQAction fp m k hvalid)
        rfl
    have hcoeff :
        gamma fp ((m + k) * householderConstructApplyGammaIndex (m + k)) *
            Real.sqrt ((m + k : ℕ) : ℝ) ≤
          gamma fp (Higham21QMethodComputedGammaIndex m k) *
            Real.sqrt ((m + k : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right
        (Higham21QMethodComputedGammaIndex.qActionGamma_le fp m k hvalid)
        (Real.sqrt_nonneg _)
    exact le_trans haction
      (mul_le_mul_of_nonneg_right hcoeff
        (vecNorm2_nonneg
          (fl_forwardSub fp m
            (matTranspose
              (fun a b =>
                fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                  (Fin.castAdd k a) b)) b)))



























































/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    block-coordinate specialization of the left-inverse transpose action.
    It reduces the first perturbed system to the triangular equation
    `(R_plus)^T y1 = b`. -/
theorem higham21_theorem21_4_qhat_first_system_block_action
    {m k : ℕ}
    (Q_inv Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ)
    (y1 : Fin m → ℝ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k)) :
    rectMatMulVec
        (finiteTranspose
          (matMulRectLeft (matTranspose Q_inv)
            (lsQRTallBlock (k := k) R_plus)))
        (matMulVec (m + k) Q_hat
          (Fin.append y1 (0 : Fin k → ℝ))) =
      fun j : Fin m => ∑ i : Fin m, R_plus i j * y1 i := by
  calc
    rectMatMulVec
        (finiteTranspose
          (matMulRectLeft (matTranspose Q_inv)
            (lsQRTallBlock (k := k) R_plus)))
        (matMulVec (m + k) Q_hat
          (Fin.append y1 (0 : Fin k → ℝ))) =
      (fun j : Fin m =>
        ∑ i : Fin (m + k),
          lsQRTallBlock (k := k) R_plus i j *
            Fin.append y1 (0 : Fin k → ℝ) i) :=
      higham21_matMulRectLeft_transpose_action_of_left_inverse
        Q_inv Q_hat (lsQRTallBlock (k := k) R_plus)
        (Fin.append y1 (0 : Fin k → ℝ)) hleft
    _ = fun j : Fin m => ∑ i : Fin m, R_plus i j * y1 i :=
      higham21_eq21_2_qr_block_transpose_coordinates
        R_plus y1 (0 : Fin k → ℝ)

/-- The first source perturbation in Higham's Theorem 21.4 proof.  Its
    perturbed matrix is `[R_plus^T,0] Q_hat^{-1}`, represented by transposing
    `(Q_hat^{-1})^T [R_plus;0]`. -/
noncomputable def Higham21QMethodDeltaA1
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ) :
    Fin m → Fin (m + k) → ℝ :=
  fun i j =>
    finiteTranspose
        (matMulRectLeft (matTranspose Q_inv)
          (lsQRTallBlock (k := k) R_plus)) i j - A i j

theorem Higham21QMethodDeltaA1.add_eq
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ) :
    (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j) =
      finiteTranspose
        (matMulRectLeft (matTranspose Q_inv)
          (lsQRTallBlock (k := k) R_plus)) := by
  ext i j
  simp [Higham21QMethodDeltaA1]

/-- The constructed `DeltaA1` makes the rounded `Q_hat` action solve the
    first perturbed system whenever `Q_inv` is a left inverse and the
    perturbed triangular equation holds. -/
theorem Higham21QMethodDeltaA1.system_eq
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k))
    (htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j)
    (hx : x_hat = matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))) :
    rectMatMulVec
        (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
        x_hat = b := by
  rw [Higham21QMethodDeltaA1.add_eq A Q_inv R_plus, hx]
  exact
    (higham21_theorem21_4_qhat_first_system_block_action
      Q_inv Q_hat R_plus y1 hleft).trans (funext htri)

set_option maxHeartbeats 800000
/-- The first perturbation in Higham's rounded-`Q` proof is bounded by the
    ideal QR-plus-triangular perturbation and the defect between
    `(Q_hat^{-1})^T` and the exact orthogonal factor. -/
theorem Higham21QMethodDeltaA1.row_bound_of_inverse_defect
    {m k : ℕ}
    (A DeltaA0 : Fin m → Fin (m + k) → ℝ)
    (Q Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR etaInv : ℝ}
    (hetaR : 0 ≤ etaR)
    (hetaInv : 0 ≤ etaInv)
    (hQ : IsOrthogonal (m + k) Q)
    (hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)))
    (hDeltaA0 : ∀ i : Fin m,
      rectRowNorm2 DeltaA0 i ≤ etaQR * rectRowNorm2 A i)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (hDefect :
      opNorm2Le (fun a b => Q_inv b a - Q a b) etaInv) :
    ∀ i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA1 A Q_inv
            (fun a b => R_hat a b + DeltaR a b)) i ≤
        ((etaQR + etaR * (1 + etaQR)) +
          etaInv * (1 + (etaQR + etaR * (1 + etaQR)))) *
          rectRowNorm2 A i := by
  let etaBase : ℝ := etaQR + etaR * (1 + etaQR)
  let R_plus : Fin m → Fin m → ℝ :=
    fun i j => R_hat i j + DeltaR i j
  let DeltaBase : Fin m → Fin (m + k) → ℝ :=
    fun i j =>
      DeltaA0 i j +
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) DeltaR)) i j
  let Defect : Fin (m + k) → Fin (m + k) → ℝ :=
    fun a b => Q_inv b a - Q a b
  let Correction : Fin m → Fin (m + k) → ℝ :=
    finiteTranspose
      (matMulRectLeft Defect (lsQRTallBlock (k := k) R_plus))
  have hBase : ∀ i : Fin m,
      rectRowNorm2 DeltaBase i ≤ etaBase * rectRowNorm2 A i := by
    intro i
    simpa [DeltaBase, etaBase] using
      higham21_theorem21_4_common_perturbation_row_bound_of_entrywise_deltaR
        A DeltaA0 Q R_hat DeltaR hetaR hQ hA hDeltaA0 hDeltaR i
  have hAssembly :
      (fun i j => A i j + DeltaBase i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_plus)) := by
    simpa [DeltaBase, R_plus] using
      higham21_theorem21_4_qr_deltaR_assembly_eq
        A DeltaA0 Q R_hat DeltaR hA
  have hAself : ∀ i : Fin m,
      rectRowNorm2 A i ≤ (1 : ℝ) * rectRowNorm2 A i := by
    intro i
    rw [one_mul]
  have hAssembledBound : ∀ i : Fin m,
      rectRowNorm2 (fun r c => A r c + DeltaBase r c) i ≤
        (1 + etaBase) * rectRowNorm2 A i := by
    intro i
    exact higham21_rectRowNorm2_add_le_of_row_bounds
      A DeltaBase A hAself hBase i
  have hRplusColumn : ∀ i : Fin m,
      columnFrob R_plus i ≤ (1 + etaBase) * rectRowNorm2 A i := by
    intro i
    have hnorm :=
      higham21_theorem21_4_assembled_qr_row_norm_eq_R_columnFrob
        A DeltaBase Q R_plus hQ hAssembly i
    rw [← hnorm]
    exact hAssembledBound i
  have hDefect' : opNorm2Le Defect etaInv := by
    simpa [Defect] using hDefect
  have hDefectRect : rectOpNorm2Le Defect etaInv :=
    rectOpNorm2Le_of_opNorm2Le_square Defect hDefect'
  have hCorrectionTranspose :
      finiteTranspose Correction =
        matMulRectLeft Defect (lsQRTallBlock (k := k) R_plus) := by
    ext i j
    rfl
  have hCorrection : ∀ i : Fin m,
      rectRowNorm2 Correction i ≤
        (etaInv * (1 + etaBase)) * rectRowNorm2 A i := by
    intro i
    calc
      rectRowNorm2 Correction i = columnFrob (finiteTranspose Correction) i :=
        higham21_rectRowNorm2_eq_columnFrob_finiteTranspose Correction i
      _ = columnFrob
          (matMulRectLeft Defect (lsQRTallBlock (k := k) R_plus)) i := by
        rw [hCorrectionTranspose]
      _ ≤ etaInv * columnFrob (lsQRTallBlock (k := k) R_plus) i := by
        exact
          columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob
            Defect (lsQRTallBlock (k := k) R_plus) hDefectRect i
      _ = etaInv * columnFrob R_plus i := by
        rw [higham21_columnFrob_lsQRTallBlock]
      _ ≤ etaInv * ((1 + etaBase) * rectRowNorm2 A i) :=
        mul_le_mul_of_nonneg_left (hRplusColumn i) hetaInv
      _ = (etaInv * (1 + etaBase)) * rectRowNorm2 A i := by ring
  have hTransposeQinv :
      matTranspose Q_inv = fun a b => Q a b + Defect a b := by
    ext a b
    dsimp [Defect, matTranspose]
    ring
  have hDeltaA1Rep :
      Higham21QMethodDeltaA1 A Q_inv R_plus =
        fun i j => DeltaBase i j + Correction i j := by
    ext i j
    change
      finiteTranspose
          (matMulRectLeft (matTranspose Q_inv)
            (lsQRTallBlock (k := k) R_plus)) i j - A i j =
        DeltaBase i j + Correction i j
    rw [hTransposeQinv, matMulRectLeft_add_left]
    have hAssemblyEntry := congrFun (congrFun hAssembly i) j
    dsimp [Correction, finiteTranspose] at hAssemblyEntry ⊢
    linarith
  intro i
  rw [hDeltaA1Rep]
  simpa [etaBase] using
    higham21_rectRowNorm2_add_le_of_row_bounds
      DeltaBase Correction A hBase hCorrection i

/-- The inverse-transpose defect in Higham's first perturbed system is the
    product of the exact inverse, the accumulated `Q_hat` perturbation, and
    the orthogonal reference factor. -/
theorem higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
    {n : ℕ}
    (Q Q_hat Q_inv DeltaQ : Fin n → Fin n → ℝ)
    (etaQ qinv : ℝ)
    (hQ : IsOrthogonal n Q)
    (hQhat : Q_hat = fun i j => Q i j + DeltaQ i j)
    (hDeltaQ : frobNorm DeltaQ ≤ etaQ)
    (hleft : matMul n Q_inv Q_hat = idMatrix n)
    (hqinv : 0 ≤ qinv)
    (hQinvOp : opNorm2Le Q_inv qinv) :
    opNorm2Le (fun a b => Q_inv b a - Q a b) (qinv * etaQ) := by
  have hetaQ : 0 ≤ etaQ :=
    le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hPertLeft :
      IsLeftInverse n (fun i j => Q i j + DeltaQ i j) Q_inv := by
    intro i j
    have hij := congrFun (congrFun hleft i) j
    rw [hQhat] at hij
    simpa only [matMul, idMatrix] using hij
  have hPertRight :
      IsRightInverse n (fun i j => Q i j + DeltaQ i j) Q_inv :=
    ch7_isRightInverse_of_isLeftInverse hPertLeft
  have hDefectEq :
      (fun a b => Q_inv a b - Q b a) =
        (fun a b =>
          -matMul n (matMul n (matTranspose Q) DeltaQ) Q_inv a b) := by
    ext a b
    have hab :=
      ch7_inversePerturbation_decomposition
        n Q (matTranspose Q) DeltaQ Q_inv
        hQ.left_inv hPertRight a b
    change
      Q_inv a b +
          matMul n (matMul n (matTranspose Q) DeltaQ) Q_inv a b =
        Q b a at hab
    linarith
  have hDeltaQOp : opNorm2Le DeltaQ etaQ :=
    opNorm2Le_of_frobNorm_le DeltaQ hDeltaQ
  have hQtDeltaQProduct :
      opNorm2Le (matMul n (matTranspose Q) DeltaQ) ((1 : ℝ) * etaQ) :=
    opNorm2Le_matMul_square_of_bounds
      (matTranspose Q) DeltaQ (by norm_num)
      hQ.transpose_opNorm2Le_one hDeltaQOp
  have hQtDeltaQ :
      opNorm2Le (matMul n (matTranspose Q) DeltaQ) etaQ := by
    simpa only [one_mul] using hQtDeltaQProduct
  have hProduct :
      opNorm2Le
        (matMul n (matMul n (matTranspose Q) DeltaQ) Q_inv)
        (etaQ * qinv) :=
    opNorm2Le_matMul_square_of_bounds
      (matMul n (matTranspose Q) DeltaQ) Q_inv
      hetaQ hQtDeltaQ hQinvOp
  have hRaw :
      opNorm2Le (fun a b => Q_inv a b - Q b a) (qinv * etaQ) := by
    rw [hDefectEq]
    simpa only [mul_comm] using (opNorm2Le_neg hProduct)
  have hRawTranspose :
      opNorm2Le
        (matTranspose (fun a b => Q_inv a b - Q b a))
        (qinv * etaQ) :=
    opNorm2Le_transpose
      (fun a b => Q_inv a b - Q b a)
      (mul_nonneg hqinv hetaQ) hRaw
  simpa only [matTranspose] using hRawTranspose

/-- Frobenius-norm specialization of the inverse-transpose defect bound. -/
theorem higham21_qhat_inverse_transpose_defect_opNorm2Le
    {n : ℕ}
    (Q Q_hat Q_inv DeltaQ : Fin n → Fin n → ℝ)
    (etaQ qinv : ℝ)
    (hQ : IsOrthogonal n Q)
    (hQhat : Q_hat = fun i j => Q i j + DeltaQ i j)
    (hDeltaQ : frobNorm DeltaQ ≤ etaQ)
    (hleft : matMul n Q_inv Q_hat = idMatrix n)
    (hQinv : frobNorm Q_inv ≤ qinv) :
    opNorm2Le (fun a b => Q_inv b a - Q a b) (qinv * etaQ) :=
  higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
    Q Q_hat Q_inv DeltaQ etaQ qinv hQ hQhat hDeltaQ hleft
    (le_trans (frobNorm_nonneg Q_inv) hQinv)
    (opNorm2Le_of_frobNorm_le Q_inv hQinv)

/-- QR, triangular-solve, accumulated-`Q`, and inverse certificates combine
    into the row-relative bound for Higham's first perturbed system. -/
theorem Higham21QMethodDeltaA1.row_bound_of_qr_transpose_certificate
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q Q_hat Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (R_hat DeltaR : Fin m → Fin m → ℝ)
    {etaQR etaR etaQ qinv : ℝ}
    (hRblock : R_tall = lsQRTallBlock (k := k) R_hat)
    (hetaR : 0 ≤ etaR)
    (hqinv : 0 ≤ qinv)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hDeltaR : ∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k))
    (hQinvOp : opNorm2Le Q_inv qinv) :
    ∀ i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA1 A Q_inv
            (fun a b => R_hat a b + DeltaR a b)) i ≤
        ((etaQR + etaR * (1 + etaQR)) +
          (qinv * etaQ) *
            (1 + (etaQR + etaR * (1 + etaQR)))) *
          rectRowNorm2 A i := by
  subst R_tall
  obtain ⟨DeltaA0, hA0, hDeltaA0⟩ :=
    higham21_theorem21_4_qr_transpose_row_perturbation_bound
      A Q (lsQRTallBlock (k := k) R_hat) etaQR hqr
  have hA :
      (fun i j => A i j + DeltaA0 i j) =
        finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R_hat)) := by
    ext i j
    simpa [finiteTranspose, matMulRectLeft, matMulRect] using hA0 i j
  rcases hQerr.result with ⟨DeltaQ, hQhatRep, hDeltaQ⟩
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhatRep i j
  have hetaQ : 0 ≤ etaQ :=
    le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hDefect :
      opNorm2Le (fun a b => Q_inv b a - Q a b) (qinv * etaQ) :=
    higham21_qhat_inverse_transpose_defect_opNorm2Le_of_inverse_bound
      Q Q_hat Q_inv DeltaQ etaQ qinv hqr.orth hQhatEq hDeltaQ hleft
      hqinv hQinvOp
  exact
    Higham21QMethodDeltaA1.row_bound_of_inverse_defect
      A DeltaA0 Q Q_inv R_hat DeltaR hetaR
      (mul_nonneg hqinv hetaQ) hqr.orth hA hDeltaA0 hDeltaR hDefect

/-- Transposing a rectangular product and applying it to a vector is the
    same as applying the square left factor after the rectangular action. -/
theorem higham21_rectTransposeMulVec_finiteTranspose_matMulRectLeft
    {m n : ℕ}
    (Q : Fin n → Fin n → ℝ)
    (B : Fin n → Fin m → ℝ)
    (y : Fin m → ℝ) :
    rectTransposeMulVec (finiteTranspose (matMulRectLeft Q B)) y =
      matMulVec n Q (rectMatMulVec B y) := by
  ext j
  have h := congrFun (rectMatMulVec_matMulRectLeft Q B y) j
  simpa [rectTransposeMulVec, finiteTranspose] using h

/-- Block specialization of the transpose-range identity for the concrete
    rounded `Q_hat` factor. -/
theorem higham21_theorem21_4_qhat_tall_block_transpose_action
    {m k : ℕ}
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (y : Fin m → ℝ) :
    rectTransposeMulVec
        (finiteTranspose
          (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat))) y =
      matMulVec (m + k) Q_hat
        (Fin.append (rectMatMulVec R_hat y) (0 : Fin k → ℝ)) := by
  rw [higham21_rectTransposeMulVec_finiteTranspose_matMulRectLeft]
  rw [higham21_eq21_1_qr_transpose_block_mulVec]

/-- The second source perturbation in Higham's Theorem 21.4 proof, defined
    by the concrete rounded product `Q_hat [R_hat;0]`. -/
noncomputable def Higham21QMethodDeltaA2
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ) :
    Fin m → Fin (m + k) → ℝ :=
  fun i j =>
    finiteTranspose
        (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat)) i j - A i j

theorem Higham21QMethodDeltaA2.add_eq
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ) :
    (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) =
      finiteTranspose
        (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat)) := by
  ext i j
  simp [Higham21QMethodDeltaA2]

/-- If `R_hat y = y1`, the concrete rounded action `Q_hat [y1;0]` lies in
    the transpose range of `A + DeltaA2`, exactly as required by the second
    perturbed system in Higham's proof. -/
theorem Higham21QMethodDeltaA2.transpose_representation
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    (y y1 : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hRy : rectMatMulVec R_hat y = y1)
    (hx : x_hat = matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))) :
    x_hat =
      rectTransposeMulVec
        (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) y := by
  rw [Higham21QMethodDeltaA2.add_eq A Q_hat R_hat]
  calc
    x_hat = matMulVec (m + k) Q_hat
        (Fin.append y1 (0 : Fin k → ℝ)) := hx
    _ = matMulVec (m + k) Q_hat
        (Fin.append (rectMatMulVec R_hat y) (0 : Fin k → ℝ)) := by rw [hRy]
    _ = rectTransposeMulVec
        (finiteTranspose
          (matMulRectLeft Q_hat (lsQRTallBlock (k := k) R_hat))) y :=
      (higham21_theorem21_4_qhat_tall_block_transpose_action
        Q_hat R_hat y).symm

set_option maxHeartbeats 800000
/-- The second perturbation in Higham's rounded-`Q` proof inherits a
    row-relative bound from the QR residual and the accumulated `Q_hat`
    perturbation. -/
theorem Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_tall : Fin (m + k) → Fin m → ℝ)
    (R_hat : Fin m → Fin m → ℝ)
    {etaQR etaQ : ℝ}
    (hRblock : R_tall = lsQRTallBlock (k := k) R_hat)
    (hqr : H19.Theorem19_4.HouseholderQRBackwardError
      (m + k) m (finiteTranspose A) Q R_tall etaQR)
    (hQerr : HouseholderQRPanelQhatFixedAccumError
      (m + k) Q Q_hat etaQ) :
    ∀ i : Fin m,
      rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
        (etaQR + etaQ * (1 + etaQR)) * rectRowNorm2 A i := by
  subst R_tall
  rcases hqr.result with ⟨DeltaAT, hQR, hDeltaAT⟩
  rcases hQerr.result with ⟨DeltaQ, hQhatRep, hDeltaQ⟩
  let B : Fin (m + k) → Fin m → ℝ := lsQRTallBlock (k := k) R_hat
  let E : Fin (m + k) → Fin m → ℝ := matMulRectLeft DeltaQ B
  have hQhatEq : Q_hat = fun i j => Q i j + DeltaQ i j := by
    ext i j
    exact hQhatRep i j
  have hQRfun :
      (fun i j => finiteTranspose A i j + DeltaAT i j) =
        matMulRectLeft Q B := by
    ext i j
    simpa [B, matMulRectLeft, matMulRect] using hQR i j
  have hetaQ : 0 ≤ etaQ :=
    le_trans (frobNorm_nonneg DeltaQ) hDeltaQ
  have hRcol : ∀ i : Fin m,
      columnFrob B i ≤
        (1 + etaQR) * columnFrob (finiteTranspose A) i := by
    intro i
    calc
      columnFrob B i = columnFrob (matMulRectLeft Q B) i :=
        (higham21_columnFrob_matMulRectLeft_orthogonal
          Q B hqr.orth i).symm
      _ ≤ columnFrob (finiteTranspose A) i + columnFrob DeltaAT i := by
        rw [← hQRfun]
        exact columnFrob_add_le _ _ i
      _ ≤ columnFrob (finiteTranspose A) i +
          etaQR * columnFrob (finiteTranspose A) i :=
        add_le_add (le_refl (columnFrob (finiteTranspose A) i))
          (hDeltaAT i)
      _ = (1 + etaQR) * columnFrob (finiteTranspose A) i := by ring
  have hEcol : ∀ i : Fin m,
      columnFrob E i ≤
        etaQ * (1 + etaQR) * columnFrob (finiteTranspose A) i := by
    intro i
    calc
      columnFrob E i ≤ frobNorm DeltaQ * columnFrob B i :=
        columnFrob_matMulVec_le_frobNorm_mul_columnFrob
          E B DeltaQ i (fun _ => rfl)
      _ ≤ etaQ * columnFrob B i :=
        mul_le_mul_of_nonneg_right hDeltaQ (columnFrob_nonneg B i)
      _ ≤ etaQ * ((1 + etaQR) *
          columnFrob (finiteTranspose A) i) :=
        mul_le_mul_of_nonneg_left (hRcol i) hetaQ
      _ = etaQ * (1 + etaQR) *
          columnFrob (finiteTranspose A) i := by ring
  have hResidual :
      finiteTranspose (Higham21QMethodDeltaA2 A Q_hat R_hat) =
        fun i j => DeltaAT i j + E i j := by
    ext i j
    change matMulRectLeft Q_hat B i j - finiteTranspose A i j =
      DeltaAT i j + E i j
    rw [hQhatEq, matMulRectLeft_add_left]
    have hQRentry := congrFun (congrFun hQRfun i) j
    dsimp [E]
    linarith
  intro i
  calc
    rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i =
        columnFrob
          (finiteTranspose (Higham21QMethodDeltaA2 A Q_hat R_hat)) i :=
      higham21_rectRowNorm2_eq_columnFrob_finiteTranspose _ i
    _ ≤ columnFrob DeltaAT i + columnFrob E i := by
      rw [hResidual]
      exact columnFrob_add_le _ _ i
    _ ≤ etaQR * columnFrob (finiteTranspose A) i +
        etaQ * (1 + etaQR) * columnFrob (finiteTranspose A) i :=
      add_le_add (hDeltaAT i) (hEcol i)
    _ = (etaQR + etaQ * (1 + etaQR)) * rectRowNorm2 A i := by
      rw [higham21_rectRowNorm2_eq_columnFrob_finiteTranspose A i]
      ring

/-- Concrete Householder specialization of the second rounded-`Q`
    perturbation bound under the single computed Q-method gamma validity
    condition. -/
theorem Higham21QMethodDeltaA2.row_bound_of_computed_gamma
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    ∀ i : Fin m,
      rectRowNorm2
          (Higham21QMethodDeltaA2 A
            (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
            (fun a b =>
              fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
                (Fin.castAdd k a) b)) i ≤
        (H19.Theorem19_4.gamma_tilde fp (m + k) m +
          Higham21QMethodQhatRadius fp m k *
            (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)) *
          rectRowNorm2 A i := by
  have hvalidQR :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k
      (Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid)
  have hqr :=
    H19.Theorem19_4.householder_qr_backward_error
      fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR
  have hRblock :=
    lsQRTallBlock_of_upper_trapezoidal
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) hqr.upper
  exact
    Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
      A
      (fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
      (fun a b =>
        fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
          (Fin.castAdd k a) b)
      hRblock hqr
      (higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid)

/-- Higham, 2nd ed., Chapter 21, Section 21.3, Theorem 21.4:
    the two exact perturbed-system equations for the rounded `Q_hat` output.
    This is the algebraic input to Lemma 21.2; perturbation-size and
    smallness bounds remain separate obligations. -/
theorem higham21_theorem21_4_qhat_two_perturbed_systems
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q_inv Q_hat : Fin (m + k) → Fin (m + k) → ℝ)
    (R_plus R_hat : Fin m → Fin m → ℝ)
    (b y1 y : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hleft : matMul (m + k) Q_inv Q_hat = idMatrix (m + k))
    (htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j)
    (hRy : rectMatMulVec R_hat y = y1)
    (hx : x_hat = matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))) :
    rectMatMulVec
        (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
        x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) y := by
  constructor
  · exact Higham21QMethodDeltaA1.system_eq
      A Q_inv Q_hat R_plus b y1 x_hat hleft htri hx
  · exact Higham21QMethodDeltaA2.transpose_representation
      A Q_hat R_hat y y1 x_hat hRy hx

/-- Theorem 21.4's two perturbed systems for the concrete rounded
    Householder `Q_hat`.  Equation (21.10) and the single combined gamma
    condition now construct the inverse internally. -/
theorem higham21_theorem21_4_computed_qhat_two_perturbed_systems
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (R_plus R_hat : Fin m → Fin m → ℝ)
    (b y1 y : Fin m → ℝ)
    (x_hat : Fin (m + k) → ℝ)
    (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1)
    (htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j)
    (hRy : rectMatMulVec R_hat y = y1)
    (hx : x_hat = matMulVec (m + k)
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      (Fin.append y1 (0 : Fin k → ℝ))) :
    ∃ Q_inv : Fin (m + k) → Fin (m + k) → ℝ,
      rectMatMulVec
          (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
          x_hat = b ∧
        x_hat =
          rectTransposeMulVec
            (fun i j => A i j +
              Higham21QMethodDeltaA2 A
                (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
                R_hat i j) y := by
  obtain ⟨Q_inv, hleft⟩ :=
    higham21_theorem21_4_qhat_exists_left_inverse_of_computed_gamma
      fp A hm hvalid hsmall
  exact ⟨Q_inv,
    higham21_theorem21_4_qhat_two_perturbed_systems
      A Q_inv
      (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A))
      R_plus R_hat b y1 y x_hat hleft htri hRy hx⟩

/-- Full-row-rank computed-QR data makes the computed top `R` block
    surjective.  This supplies the exact coordinate used in the second
    perturbed system of Theorem 21.4. -/
theorem higham21_computed_top_block_exists_exact_preimage
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (y1 : Fin m → ℝ) :
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    ∃ y : Fin m → ℝ, rectMatMulVec R_hat y = y1 := by
  dsimp only
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal
      fp (m + k) m (finiteTranspose A)
  have hupper : IsUpperTrapezoidal m m R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, R_hat i i ≠ 0 := by
    simpa [R_hat, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  have hdet : Matrix.det (R_hat : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    det_ne_zero_of_upper_triangular_diag_ne_zero m R_hat hupper hdiag
  have hInverse : IsInverse m R_hat (nonsingInv m R_hat) :=
    isInverse_nonsingInv_of_det_ne_zero m R_hat hdet
  refine ⟨matMulVec m (nonsingInv m R_hat) y1, ?_⟩
  change matMulVec m R_hat (matMulVec m (nonsingInv m R_hat) y1) = y1
  exact matMulVec_of_isRightInverse R_hat (nonsingInv m R_hat) hInverse.2 y1

/-- The concrete rounded Q-method output satisfies both perturbed systems in
    Higham's Theorem 21.4 with every algebraic witness constructed from the
    implementation-backed QR domain and the single combined gamma validity
    condition. -/
theorem higham21_theorem21_4_computed_qhat_two_perturbed_systems_of_full_row_rank_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    ∃ (DeltaR : Fin m → Fin m → ℝ)
        (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
        (y : Fin m → ℝ),
      (∀ i j, |DeltaR i j| ≤ gamma fp m * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y := by
  dsimp only
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal
      fp (m + k) m (finiteTranspose A)
  have hupper : IsUpperTrapezoidal m m R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, R_hat i i ≠ 0 := by
    simpa [R_hat, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  have hvalidRowwise :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid
  have hvalidM :=
    Higham21QMethodRowwiseGammaIndex.validM fp m k hvalidRowwise
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalidM
  let R_plus : Fin m → Fin m → ℝ :=
    fun i j => R_hat i j + DeltaR i j
  have htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j := by
    intro j
    simpa [R_plus, y1, matMulVec, matTranspose] using hsolve j
  obtain ⟨y, hRyRaw⟩ :=
    higham21_computed_top_block_exists_exact_preimage fp A hdomain y1
  have hRy : rectMatMulVec R_hat y = y1 := by
    simpa [R_hat] using hRyRaw
  obtain ⟨Q_inv, hfirst, hsecond⟩ :=
    higham21_theorem21_4_computed_qhat_two_perturbed_systems
      fp A R_plus R_hat b y1 y x_hat hm hvalid hsmall htri hRy (by
        rfl)
  refine ⟨DeltaR, Q_inv, y, ?_, ?_, ?_⟩
  · simpa [R_hat] using hDeltaR
  · simpa [R_hat, R_plus, Q_hat, y1, x_hat] using hfirst
  · simpa [R_hat, Q_hat, y1, x_hat] using hsecond

/-- Implementation-backed rounded-Q witness package with a supplied inverse
    operator bound.  The same `DeltaR`, inverse, and range coordinate satisfy
    both exact systems and both row-relative perturbation estimates. -/
theorem higham21_theorem21_4_computed_qhat_perturbations_of_inverse_bound
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (qinv : ℝ) (hqinv : 0 ≤ qinv)
    (hleft :
      matMul (m + k) Q_inv
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)) =
        idMatrix (m + k))
    (hQinvOp : opNorm2Le Q_inv qinv) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
    let etaR := gamma fp m
    let etaQ := Higham21QMethodQhatRadius fp m k
    ∃ (DeltaR : Fin m → Fin m → ℝ) (y : Fin m → ℝ),
      (∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y ∧
      (∀ i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i ≤
          ((etaQR + etaR * (1 + etaQR)) +
            (qinv * etaQ) *
              (1 + (etaQR + etaR * (1 + etaQR)))) *
            rectRowNorm2 A i) ∧
      (∀ i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
          (etaQR + etaQ * (1 + etaQR)) * rectRowNorm2 A i) := by
  dsimp only
  let Q : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Q fp (m + k) m (finiteTranspose A)
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_tall : Fin (m + k) → Fin m → ℝ :=
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    R_tall (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let etaQR : ℝ := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaR : ℝ := gamma fp m
  let etaQ : ℝ := Higham21QMethodQhatRadius fp m k
  have hvalidRowwise :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid
  have hvalidQR :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalidRowwise
  have hvalidM :=
    Higham21QMethodRowwiseGammaIndex.validM fp m k hvalidRowwise
  have hqr :
      H19.Theorem19_4.HouseholderQRBackwardError
        (m + k) m (finiteTranspose A) Q R_tall etaQR := by
    simpa [Q, R_tall, etaQR] using
      H19.Theorem19_4.householder_qr_backward_error
        fp (m + k) m (finiteTranspose A) hm (Nat.le_add_right m k) hvalidQR
  have hRblock : R_tall = lsQRTallBlock (k := k) R_hat := by
    simpa [R_hat] using
      lsQRTallBlock_of_upper_trapezoidal R_tall hqr.upper
  have hupper : IsUpperTrapezoidal m m R_hat :=
    lsQRTallBlock_top_upper_of_upper_trapezoidal R_tall hqr.upper
  have hdiag : ∀ i : Fin m, R_hat i i ≠ 0 := by
    simpa [R_hat, R_tall, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  obtain ⟨DeltaR, hDeltaR, hsolve⟩ :=
    higham21_theorem21_4_forwardSub_transpose_triangular_solve_backward_error
      fp m R_hat b hdiag hupper hvalidM
  let R_plus : Fin m → Fin m → ℝ :=
    fun i j => R_hat i j + DeltaR i j
  have htri : ∀ j : Fin m, ∑ i : Fin m, R_plus i j * y1 i = b j := by
    intro j
    simpa [R_plus, y1, matMulVec, matTranspose] using hsolve j
  obtain ⟨y, hRyRaw⟩ :=
    higham21_computed_top_block_exists_exact_preimage fp A hdomain y1
  have hRy : rectMatMulVec R_hat y = y1 := by
    simpa [R_hat, R_tall] using hRyRaw
  have hleft' : matMul (m + k) Q_inv Q_hat = idMatrix (m + k) := by
    simpa [Q_hat] using hleft
  have hQerr :
      HouseholderQRPanelQhatFixedAccumError (m + k) Q Q_hat etaQ := by
    simpa [Q, Q_hat, etaQ] using
      higham21_eq21_10_qhat_fixed_accum_error_of_computed_gamma_index
        fp A hm hvalid
  have hfirst :
      rectMatMulVec
          (fun i j => A i j + Higham21QMethodDeltaA1 A Q_inv R_plus i j)
          x_hat = b :=
    Higham21QMethodDeltaA1.system_eq
      A Q_inv Q_hat R_plus b y1 x_hat hleft' htri rfl
  have hsecond :
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j + Higham21QMethodDeltaA2 A Q_hat R_hat i j) y :=
    Higham21QMethodDeltaA2.transpose_representation
      A Q_hat R_hat y y1 x_hat hRy rfl
  have hrow1 :=
    Higham21QMethodDeltaA1.row_bound_of_qr_transpose_certificate
      A Q Q_hat Q_inv R_tall R_hat DeltaR hRblock
      (gamma_nonneg fp hvalidM) hqinv hqr hDeltaR hQerr hleft' hQinvOp
  have hrow2 :=
    Higham21QMethodDeltaA2.row_bound_of_qr_transpose_certificate
      A Q Q_hat R_tall R_hat hRblock hqr hQerr
  refine ⟨DeltaR, y, ?_, hfirst, hsecond, hrow1, hrow2⟩
  simpa [etaR] using hDeltaR

/-- A common row-wise radius for the two rounded-`Q_hat` perturbations when
    an operator bound on the supplied inverse is available. -/
noncomputable def Higham21QMethodRoundedRowwiseCoefficientOfInverseBound
    (fp : FPModel) (m k : ℕ) (qinv : ℝ) : ℝ :=
  let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaR := gamma fp m
  let etaQ := Higham21QMethodQhatRadius fp m k
  max
    ((etaQR + etaR * (1 + etaQR)) +
      (qinv * etaQ) * (1 + (etaQR + etaR * (1 + etaQR))))
    (etaQR + etaQ * (1 + etaQR))

/-- The source-shaped rounded-`Q_hat` row radius, using the inverse estimate
    `||Q_hat^{-1}||_2 <= 1 / (1 - etaQ)`. -/
noncomputable def Higham21QMethodRoundedRowwiseCoefficient
    (fp : FPModel) (m k : ℕ) : ℝ :=
  Higham21QMethodRoundedRowwiseCoefficientOfInverseBound fp m k
    (1 / (1 - Higham21QMethodQhatRadius fp m k))

theorem Higham21QMethodQhatRadius_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    0 ≤ Higham21QMethodQhatRadius fp m k := by
  exact mul_nonneg (gamma_nonneg fp hvalid) (Real.sqrt_nonneg _)

theorem Higham21QMethodRoundedRowwiseCoefficientOfInverseBound_nonneg
    (fp : FPModel) (m k : ℕ) (qinv : ℝ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    0 ≤ Higham21QMethodRoundedRowwiseCoefficientOfInverseBound fp m k qinv := by
  have hvalidRowwise :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k hvalid
  have hvalidQR :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hvalidRowwise
  have hetaQR : 0 ≤ H19.Theorem19_4.gamma_tilde fp (m + k) m :=
    H19.Theorem19_4.gamma_tilde_nonneg fp hvalidQR
  have hetaQ : 0 ≤ Higham21QMethodQhatRadius fp m k :=
    Higham21QMethodQhatRadius_nonneg fp m k hvalid
  have heta2 :
      0 ≤ H19.Theorem19_4.gamma_tilde fp (m + k) m +
        Higham21QMethodQhatRadius fp m k *
          (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m) := by
    exact add_nonneg hetaQR (mul_nonneg hetaQ (by linarith))
  exact heta2.trans (by
    unfold Higham21QMethodRoundedRowwiseCoefficientOfInverseBound
    exact le_max_right _ _)

theorem Higham21QMethodRoundedRowwiseCoefficient_nonneg
    (fp : FPModel) (m k : ℕ)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k)) :
    0 ≤ Higham21QMethodRoundedRowwiseCoefficient fp m k := by
  exact
    Higham21QMethodRoundedRowwiseCoefficientOfInverseBound_nonneg
      fp m k _ hvalid

/-- The base operation-count index used to absorb the rounded-`Q_hat`
    inverse, QR, and triangular-solve radii into one gamma term. -/
def Higham21QMethodRoundedGammaBaseIndex (m k : ℕ) : ℕ :=
  Higham21QMethodComputedGammaIndex m k +
    2 * ((m + k) * Higham21QMethodComputedGammaIndex m k)

/-- Higham, 2nd ed., Chapter 21, Theorem 21.4: a concrete realization of
    the printed `gamma_tilde_{mn}`.  The leading `3 * n` also absorbs the
    Lemma 21.2 smallness factor and the row-to-operator `sqrt n` estimate. -/
def Higham21QMethodRoundedGammaIndex (m k : ℕ) : ℕ :=
  (3 * (m + k)) * Higham21QMethodRoundedGammaBaseIndex m k

theorem Higham21QMethodRoundedGammaBaseIndex_le_index
    (m k : ℕ) (hm : 0 < m) :
    Higham21QMethodRoundedGammaBaseIndex m k ≤
      Higham21QMethodRoundedGammaIndex m k := by
  have hfactor : 0 < 3 * (m + k) := by omega
  exact Nat.le_mul_of_pos_left _ hfactor

theorem Higham21QMethodComputedGammaIndex_le_roundedGammaIndex
    (m k : ℕ) (hm : 0 < m) :
    Higham21QMethodComputedGammaIndex m k ≤
      Higham21QMethodRoundedGammaIndex m k := by
  calc
    Higham21QMethodComputedGammaIndex m k ≤
        Higham21QMethodRoundedGammaBaseIndex m k := by
      dsimp [Higham21QMethodRoundedGammaBaseIndex]
      exact Nat.le_add_right _ _
    _ ≤ Higham21QMethodRoundedGammaIndex m k :=
      Higham21QMethodRoundedGammaBaseIndex_le_index m k hm

theorem Higham21QMethodRoundedGammaIndex.validComputed
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    gammaValid fp (Higham21QMethodComputedGammaIndex m k) :=
  gammaValid_mono fp
    (Higham21QMethodComputedGammaIndex_le_roundedGammaIndex m k hm) hvalid

theorem Higham21QMethodQhatRadius_le_gamma_n_mul_computed
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Higham21QMethodQhatRadius fp m k ≤
      gamma fp ((m + k) * Higham21QMethodComputedGammaIndex m k) := by
  let N := m + k
  let G := Higham21QMethodComputedGammaIndex m k
  have hN : 1 ≤ N := by simp [N]; omega
  have hGvalid : gammaValid fp G := by
    simpa [G] using
      Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hNG_le_base : N * G ≤ Higham21QMethodRoundedGammaBaseIndex m k := by
    have hK2 : N * G ≤ 2 * (N * G) :=
      Nat.le_mul_of_pos_left _ (by norm_num)
    exact hK2.trans (by
      dsimp [Higham21QMethodRoundedGammaBaseIndex, N, G]
      exact Nat.le_add_left _ _)
  have hNGvalid : gammaValid fp (N * G) :=
    gammaValid_mono fp
      (hNG_le_base.trans
        (Higham21QMethodRoundedGammaBaseIndex_le_index m k hm)) hvalid
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) :=
    higham21_sqrt_nat_le_nat N
  calc
    Higham21QMethodQhatRadius fp m k =
        gamma fp G * Real.sqrt (N : ℝ) := by
      simp [Higham21QMethodQhatRadius, N, G]
    _ ≤ gamma fp G * (N : ℝ) :=
      mul_le_mul_of_nonneg_left hsqrt (gamma_nonneg fp hGvalid)
    _ = (N : ℝ) * gamma fp G := by ring
    _ ≤ gamma fp (N * G) :=
      gamma_nsmul_le fp N G hN hNGvalid
    _ = gamma fp ((m + k) * Higham21QMethodComputedGammaIndex m k) := by
      simp [N, G]

theorem Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Higham21QMethodQhatRadius fp m k < 1 := by
  let N := m + k
  let G := Higham21QMethodComputedGammaIndex m k
  let K := N * G
  have h2K_le_base : 2 * K ≤ Higham21QMethodRoundedGammaBaseIndex m k := by
    dsimp [Higham21QMethodRoundedGammaBaseIndex, K, N, G]
    exact Nat.le_add_left _ _
  have h2Kvalid : gammaValid fp (2 * K) :=
    gammaValid_mono fp
      (h2K_le_base.trans
        (Higham21QMethodRoundedGammaBaseIndex_le_index m k hm)) hvalid
  have hq : Higham21QMethodQhatRadius fp m k ≤ gamma fp K := by
    simpa [K, N, G] using
      Higham21QMethodQhatRadius_le_gamma_n_mul_computed fp m k hm hvalid
  exact hq.trans_lt (gamma_lt_one fp K h2Kvalid)

/-- The exact rounded-Q coefficient is bounded by one gamma term before the
    final Lemma 21.2 dimension factor is absorbed. -/
theorem Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Higham21QMethodRoundedRowwiseCoefficient fp m k ≤
      gamma fp (Higham21QMethodRoundedGammaBaseIndex m k) := by
  let N := m + k
  let G := Higham21QMethodComputedGammaIndex m k
  let K := N * G
  let H := G + 2 * K
  let etaQR := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaQ := Higham21QMethodQhatRadius fp m k
  let eta0 := Higham21QMethodRowwiseCoefficient fp m k
  let invQ := (1 / (1 - etaQ)) * etaQ
  have hH_eq : H = Higham21QMethodRoundedGammaBaseIndex m k := by
    simp [H, K, N, G, Higham21QMethodRoundedGammaBaseIndex]
  have hHvalid : gammaValid fp H := by
    apply gammaValid_mono fp
      (show H ≤ Higham21QMethodRoundedGammaIndex m k from ?_) hvalid
    rw [hH_eq]
    exact Higham21QMethodRoundedGammaBaseIndex_le_index m k hm
  have hGvalid : gammaValid fp G := by
    simpa [G] using
      Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have hRowValid : gammaValid fp (Higham21QMethodRowwiseGammaIndex m k) :=
    Higham21QMethodComputedGammaIndex.validRowwise fp m k (by simpa [G] using hGvalid)
  have hQRValid :=
    Higham21QMethodRowwiseGammaIndex.validQR fp m k hRowValid
  have hMValid :=
    Higham21QMethodRowwiseGammaIndex.validM fp m k hRowValid
  have hetaQR0 : 0 ≤ etaQR := by
    exact H19.Theorem19_4.gamma_tilde_nonneg fp hQRValid
  have heta00 : 0 ≤ eta0 := by
    exact Higham21QMethodRowwiseCoefficient_nonneg fp m k hQRValid hMValid
  have hetaQ0 : 0 ≤ etaQ := by
    exact Higham21QMethodQhatRadius_nonneg fp m k (by simpa [G] using hGvalid)
  have hetaQ_lt : etaQ < 1 := by
    exact Higham21QMethodQhatRadius_lt_one_of_roundedGamma_valid fp m k hm hvalid
  have hK_le_base : K ≤ H := by
    have hK2 : K ≤ 2 * K := Nat.le_mul_of_pos_left _ (by norm_num)
    exact hK2.trans (Nat.le_add_left _ _)
  have h2K_le_base : 2 * K ≤ H := Nat.le_add_left _ _
  have hKvalid : gammaValid fp K := gammaValid_mono fp hK_le_base hHvalid
  have h2Kvalid : gammaValid fp (2 * K) :=
    gammaValid_mono fp h2K_le_base hHvalid
  have hetaQ_le : etaQ ≤ gamma fp K := by
    simpa [etaQ, K, N, G] using
      Higham21QMethodQhatRadius_le_gamma_n_mul_computed fp m k hm hvalid
  have hgammaK0 : 0 ≤ gamma fp K := gamma_nonneg fp hKvalid
  have hgammaK_lt : gamma fp K < 1 := gamma_lt_one fp K h2Kvalid
  have hinvQ0 : 0 ≤ invQ := by
    exact mul_nonneg (one_div_pos.mpr (sub_pos.mpr hetaQ_lt)).le hetaQ0
  have hinvQ_le : invQ ≤ gamma fp (2 * K) := by
    have hfrac : etaQ / (1 - etaQ) ≤ gamma fp K / (1 - gamma fp K) :=
      div_le_div₀ hgammaK0 hetaQ_le (sub_pos.mpr hgammaK_lt) (by linarith)
    have hdouble :
        gamma fp K / (1 - gamma fp K) ≤
          (gamma fp K + gamma fp K) / (1 - gamma fp K) := by
      rw [div_le_div_iff₀ (sub_pos.mpr hgammaK_lt) (sub_pos.mpr hgammaK_lt)]
      nlinarith
    have habsorb :=
      gamma_add_div_one_sub_gamma_le_of_le fp K K (le_refl K) (by
        simpa [two_mul] using h2Kvalid)
    calc
      invQ = etaQ / (1 - etaQ) := by
        simp [invQ, div_eq_mul_inv, mul_comm]
      _ ≤ gamma fp K / (1 - gamma fp K) := hfrac
      _ ≤ (gamma fp K + gamma fp K) / (1 - gamma fp K) := hdouble
      _ ≤ gamma fp (2 * K) := by simpa [two_mul] using habsorb
  have heta0_le_G : eta0 ≤ gamma fp G := by
    calc
      eta0 ≤ gamma fp (Higham21QMethodRowwiseGammaIndex m k) := by
        exact Higham21QMethodRowwiseCoefficient_le_gamma_index fp m k hRowValid
      _ ≤ gamma fp G := by
        simpa [G] using
          Higham21QMethodComputedGammaIndex.rowwiseGamma_le fp m k
            (by simpa [G] using hGvalid)
  have hetaQR_le_eta0 : etaQR ≤ eta0 := by
    have hterm :
        0 ≤ gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m) :=
      mul_nonneg (gamma_nonneg fp hMValid) (by linarith)
    change H19.Theorem19_4.gamma_tilde fp (m + k) m ≤
      H19.Theorem19_4.gamma_tilde fp (m + k) m +
        gamma fp m * (1 + H19.Theorem19_4.gamma_tilde fp (m + k) m)
    exact le_add_of_nonneg_right hterm
  have hetaQR_le_G : etaQR ≤ gamma fp G := hetaQR_le_eta0.trans heta0_le_G
  have hgammaG0 : 0 ≤ gamma fp G := gamma_nonneg fp hGvalid
  have hgamma2K0 : 0 ≤ gamma fp (2 * K) := gamma_nonneg fp h2Kvalid
  have hsum1 :
      gamma fp G + gamma fp (2 * K) +
          gamma fp G * gamma fp (2 * K) ≤ gamma fp H := by
    simpa [H] using gamma_sum_le fp G (2 * K) hHvalid
  have hmul1 :
      invQ * (1 + eta0) ≤
        gamma fp (2 * K) * (1 + gamma fp G) := by
    calc
      invQ * (1 + eta0) ≤ gamma fp (2 * K) * (1 + eta0) :=
        mul_le_mul_of_nonneg_right hinvQ_le (by linarith)
      _ ≤ gamma fp (2 * K) * (1 + gamma fp G) :=
        mul_le_mul_of_nonneg_left (by linarith) hgamma2K0
  have heta1 : eta0 + invQ * (1 + eta0) ≤ gamma fp H := by
    calc
      eta0 + invQ * (1 + eta0) ≤
          gamma fp G + gamma fp (2 * K) * (1 + gamma fp G) :=
        add_le_add heta0_le_G hmul1
      _ = gamma fp G + gamma fp (2 * K) +
          gamma fp G * gamma fp (2 * K) := by ring
      _ ≤ gamma fp H := hsum1
  have hGK_le_H : G + K ≤ H := by
    dsimp [H]
    exact Nat.add_le_add_left
      (Nat.le_mul_of_pos_left K (by norm_num)) G
  have hGKvalid : gammaValid fp (G + K) := gammaValid_mono fp hGK_le_H hHvalid
  have hsum2 :
      gamma fp G + gamma fp K + gamma fp G * gamma fp K ≤
        gamma fp (G + K) := gamma_sum_le fp G K hGKvalid
  have hmul2 :
      etaQ * (1 + etaQR) ≤ gamma fp K * (1 + gamma fp G) := by
    calc
      etaQ * (1 + etaQR) ≤ gamma fp K * (1 + etaQR) :=
        mul_le_mul_of_nonneg_right hetaQ_le (by linarith)
      _ ≤ gamma fp K * (1 + gamma fp G) :=
        mul_le_mul_of_nonneg_left (by linarith) hgammaK0
  have heta2 : etaQR + etaQ * (1 + etaQR) ≤ gamma fp H := by
    calc
      etaQR + etaQ * (1 + etaQR) ≤
          gamma fp G + gamma fp K * (1 + gamma fp G) :=
        add_le_add hetaQR_le_G hmul2
      _ = gamma fp G + gamma fp K + gamma fp G * gamma fp K := by ring
      _ ≤ gamma fp (G + K) := hsum2
      _ ≤ gamma fp H := gamma_mono fp hGK_le_H hHvalid
  have hmax :
      max (eta0 + invQ * (1 + eta0))
          (etaQR + etaQ * (1 + etaQR)) ≤ gamma fp H :=
    max_le heta1 heta2
  simpa [Higham21QMethodRoundedRowwiseCoefficient,
    Higham21QMethodRoundedRowwiseCoefficientOfInverseBound,
    Higham21QMethodRowwiseCoefficient, eta0, invQ, etaQR, etaQ,
    Higham21QMethodQhatRadius, hH_eq] using hmax

/-- The actual row-relative factor returned after Lemma 21.2 is bounded by
    the concrete `gamma_tilde_{mn}` used in the source-facing theorem. -/
theorem Higham21QMethodRoundedOutputCoefficient_le_gamma_index
    (fp : FPModel) (m k : ℕ) (hm : 0 < m)
    (hvalid : gammaValid fp (Higham21QMethodRoundedGammaIndex m k)) :
    Real.sqrt 2 * Higham21QMethodRoundedRowwiseCoefficient fp m k ≤
      gamma fp (Higham21QMethodRoundedGammaIndex m k) := by
  let H := Higham21QMethodRoundedGammaBaseIndex m k
  have hComputed :=
    Higham21QMethodRoundedGammaIndex.validComputed fp m k hm hvalid
  have heta0 :=
    Higham21QMethodRoundedRowwiseCoefficient_nonneg fp m k hComputed
  have heta :=
    Higham21QMethodRoundedRowwiseCoefficient_le_gamma_base fp m k hm hvalid
  have hsqrt2 : Real.sqrt (2 : ℝ) ≤ 2 := by
    have hsqrt0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt (2 : ℝ)) ^ 2 = 2 :=
      Real.sq_sqrt (by norm_num)
    nlinarith
  have h2H_le : 2 * H ≤ Higham21QMethodRoundedGammaIndex m k := by
    have hN : 2 ≤ 3 * (m + k) := by omega
    simpa [Higham21QMethodRoundedGammaIndex, H] using
      Nat.mul_le_mul_right H hN
  have h2Hvalid : gammaValid fp (2 * H) :=
    gammaValid_mono fp h2H_le hvalid
  calc
    Real.sqrt 2 * Higham21QMethodRoundedRowwiseCoefficient fp m k ≤
        2 * Higham21QMethodRoundedRowwiseCoefficient fp m k :=
      mul_le_mul_of_nonneg_right hsqrt2 heta0
    _ ≤ 2 * gamma fp H :=
      mul_le_mul_of_nonneg_left (by simpa [H] using heta) (by norm_num)
    _ ≤ gamma fp (2 * H) :=
      gamma_nsmul_le fp 2 H (by norm_num) h2Hvalid
    _ ≤ gamma fp (Higham21QMethodRoundedGammaIndex m k) :=
      gamma_mono fp h2H_le hvalid

/-- The same inverse, triangular perturbation, and range coordinate satisfy
    both exact systems with one common row-wise perturbation radius. -/
theorem higham21_theorem21_4_computed_qhat_perturbations_common_row_bound_of_inverse_bound
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
    (qinv : ℝ) (hqinv : 0 ≤ qinv)
    (hleft :
      matMul (m + k) Q_inv
          (fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)) =
        idMatrix (m + k))
    (hQinvOp : opNorm2Le Q_inv qinv) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    let etaR := gamma fp m
    let eta :=
      Higham21QMethodRoundedRowwiseCoefficientOfInverseBound fp m k qinv
    ∃ (DeltaR : Fin m → Fin m → ℝ) (y : Fin m → ℝ),
      (∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y ∧
      (∀ i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i ≤
          eta * rectRowNorm2 A i) ∧
      (∀ i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
          eta * rectRowNorm2 A i) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let etaQR : ℝ := H19.Theorem19_4.gamma_tilde fp (m + k) m
  let etaR : ℝ := gamma fp m
  let etaQ : ℝ := Higham21QMethodQhatRadius fp m k
  let eta1 : ℝ :=
    (etaQR + etaR * (1 + etaQR)) +
      (qinv * etaQ) * (1 + (etaQR + etaR * (1 + etaQR)))
  let eta2 : ℝ := etaQR + etaQ * (1 + etaQR)
  let eta : ℝ := max eta1 eta2
  obtain ⟨DeltaR, y, hDeltaR, hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_theorem21_4_computed_qhat_perturbations_of_inverse_bound
      fp A b hm hdomain hvalid Q_inv qinv hqinv hleft hQinvOp
  refine ⟨DeltaR, y, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [etaR] using hDeltaR
  · simpa [Q_hat, R_hat, y1, x_hat] using hfirst
  · simpa [Q_hat, R_hat, y1, x_hat] using hsecond
  · intro i
    have hle : eta1 ≤ eta := le_max_left _ _
    exact (hrow1 i).trans (by
      apply mul_le_mul_of_nonneg_right hle
      exact rectRowNorm2_nonneg A i)
  · intro i
    have hle : eta2 ≤ eta := le_max_right _ _
    exact (hrow2 i).trans (by
      apply mul_le_mul_of_nonneg_right hle
      exact rectRowNorm2_nonneg A i)

/-- Concrete rounded-Q-method perturbation package.  Under the single
    combined gamma validity condition and `etaQ < 1`, it constructs one
    inverse, one triangular perturbation, and one range coordinate satisfying
    both exact systems and the common row-relative bound used by Lemma 21.2. -/
theorem higham21_theorem21_4_computed_qhat_perturbations_common_row_bound
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ) (b : Fin m → ℝ)
    (hm : 0 < m)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A)
    (hvalid : gammaValid fp (Higham21QMethodComputedGammaIndex m k))
    (hsmall : Higham21QMethodQhatRadius fp m k < 1) :
    let Q_hat := fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
    let R_hat : Fin m → Fin m → ℝ := fun i j =>
      fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
        (Fin.castAdd k i) j
    let y1 := fl_forwardSub fp m (matTranspose R_hat) b
    let x_hat := matMulVec (m + k) Q_hat
      (Fin.append y1 (0 : Fin k → ℝ))
    let etaR := gamma fp m
    let eta := Higham21QMethodRoundedRowwiseCoefficient fp m k
    ∃ (Q_inv : Fin (m + k) → Fin (m + k) → ℝ)
        (DeltaR : Fin m → Fin m → ℝ) (y : Fin m → ℝ),
      matMul (m + k) Q_inv Q_hat = idMatrix (m + k) ∧
      (∀ i j, |DeltaR i j| ≤ etaR * |R_hat i j|) ∧
      rectMatMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b) i j)
          x_hat = b ∧
      x_hat =
        rectTransposeMulVec
          (fun i j => A i j +
            Higham21QMethodDeltaA2 A Q_hat R_hat i j) y ∧
      (∀ i : Fin m,
        rectRowNorm2
            (Higham21QMethodDeltaA1 A Q_inv
              (fun a b => R_hat a b + DeltaR a b)) i ≤
          eta * rectRowNorm2 A i) ∧
      (∀ i : Fin m,
        rectRowNorm2 (Higham21QMethodDeltaA2 A Q_hat R_hat) i ≤
          eta * rectRowNorm2 A i) := by
  dsimp only
  let Q_hat : Fin (m + k) → Fin (m + k) → ℝ :=
    fl_householderQRPanel_Qhat fp (m + k) m (finiteTranspose A)
  let R_hat : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  let y1 : Fin m → ℝ := fl_forwardSub fp m (matTranspose R_hat) b
  let x_hat : Fin (m + k) → ℝ :=
    matMulVec (m + k) Q_hat (Fin.append y1 (0 : Fin k → ℝ))
  let etaR : ℝ := gamma fp m
  let etaQ : ℝ := Higham21QMethodQhatRadius fp m k
  let qinv : ℝ := 1 / (1 - etaQ)
  obtain ⟨Q_inv, hleft, hQinvOp⟩ :=
    higham21_theorem21_4_qhat_exists_left_inverse_with_opNorm2Le_of_computed_gamma
      fp A hm hvalid hsmall
  have hqinv : 0 ≤ qinv := by
    exact (one_div_pos.mpr (sub_pos.mpr hsmall)).le
  obtain ⟨DeltaR, y, hDeltaR, hfirst, hsecond, hrow1, hrow2⟩ :=
    higham21_theorem21_4_computed_qhat_perturbations_common_row_bound_of_inverse_bound
      fp A b hm hdomain hvalid Q_inv qinv hqinv hleft hQinvOp
  refine ⟨Q_inv, DeltaR, y, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Q_hat] using hleft
  · simpa [R_hat, etaR] using hDeltaR
  · simpa [Q_hat, R_hat, y1, x_hat] using hfirst
  · simpa [Q_hat, R_hat, y1, x_hat] using hsecond
  · simpa [Higham21QMethodRoundedRowwiseCoefficient, qinv, etaQ,
      Q_hat, R_hat] using hrow1
  · simpa [Higham21QMethodRoundedRowwiseCoefficient, qinv, etaQ,
      Q_hat, R_hat] using hrow2


































































































































































































































/-- **Theorem 21.4** (Higham): The Q method for underdetermined systems
    is row-wise backward stable.

    The Q method solves Rᵀy₁ = b and forms x = Q[y₁; 0]ᵀ using
    the QR factorization Aᵀ = Q[R; 0]. The computed x̂ is the
    minimum 2-norm solution to (A + ΔA)x = b, where:

    ‖ΔA‖_F ≤ mγ_{cn}‖A‖_F  (normwise)
    |ΔA| ≤ mnγ_{cn}|A|G, ‖G‖_F = 1  (componentwise)

    Note: b is not perturbed (unlike the least-squares QR result in
    Theorem 20.3).

    This legacy Gram-system summary is retained for compatibility.  The
    concrete rounded-output source theorem is
    `higham21_theorem21_4_computed_qhat_rowwise_backward_stable_gamma`. -/
structure QMethodBackwardStable (m : ℕ)
    (AAT : Fin m → Fin m → ℝ)
    (b y_hat : Fin m → ℝ)
    (c_bound : ℝ) : Prop where
  /-- c_bound is nonneg. -/
  bound_nonneg : 0 ≤ c_bound
  /-- The computed ŷ satisfies perturbed normal equations
      (AAᵀ + ΔG)ŷ = b with bounded ΔG.
      This captures the Q method's backward stability projected
      to the m×m Gram system AAᵀ. -/
  result : ∃ (ΔG : Fin m → Fin m → ℝ),
    (∀ i, matMulVec m (fun a b => AAT a b + ΔG a b) y_hat i = b i) ∧
    frobNorm ΔG ≤ c_bound

-- ============================================================
-- §21.3  SNE method backward error
-- ============================================================





























-- ============================================================
-- §21.3  Forward error bound (eq. 21.11)
-- ============================================================






































































































































































































































































































































































































































































































































































































































































































end NumStability
