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
import NumStability.Algorithms.LinearSystems.Underdetermined.Conditioning.Componentwise.UnderdeterminedSolve
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Algorithms.LinearSystems.Underdetermined.SeminormalEquations.QRTransfer.QRMajorant
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Theorem04.SeminormalEquations.ActualOutput

/-!
# Source.Higham.Chapter21.Theorem04.SeminormalEquations.QRMajorant

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Componentwise QR-action estimates for the signed SNE analysis.



namespace NumStability

open scoped BigOperators

/-!
# QR perturbation action without an aggregate Gram envelope

The Householder backward-error theorem supplies

`|F i p| <= rho * sum_s G p s * |A i s|`,

where `G` is nonnegative and has operator norm at most one.  The lemmas below
keep this action on the dual vector.  This is the cancellation-compatible
route used by Demmel--Higham; it does not introduce `|(A A^T)⁻¹|`.
-/






































































































































































































/-- Absorb the QR action into the nearby dual condition expression.  This is
the finite form of the first-order step
`|| |A|ᵀ |ybar| || <= cond₂(B)||xbar|| + O(rho)`.

The hypotheses are local: a componentwise QR perturbation, a norm-one
majorant, the canonical nearby dual relation, and `rho < 1`. -/
theorem higham21_sne_source_dual_action_absorbed_by_nearby_cond2
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho) (hrho_lt : rho < 1)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (Bplus : Fin n -> Fin m -> Real)
    (ybar : Fin m -> Real) (xbar : Fin n -> Real)
    (hybar : ybar = rectTransposeMulVec Bplus xbar) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      (higham21Cond2With (fun i j => A i j + F i j) Bplus *
          vecNorm2 xbar) / (1 - rho) := by
  let wA : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wB : Fin n -> Real :=
    rectTransposeMulVec
      (absMatrixRect (fun i j => A i j + F i j)) (fun i => |ybar i|)
  let q : Real :=
    higham21Cond2With (fun i j => A i j + F i j) Bplus * vecNorm2 xbar
  have hWF :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) <=
        rho * vecNorm2 wA := by
    simpa [wA] using
      higham21_sne_qr_abs_error_transpose_action_le_source
        A F G rho hrho hG hGop hF ybar
  have hAB : vecNorm2 wA <= vecNorm2 wB +
      vecNorm2
        (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) := by
    simpa [wA, wB] using
      higham21_sne_source_dual_action_le_nearby_add_error A F ybar
  have hBq : vecNorm2 wB <= q := by
    simpa [wB, q, hybar] using
      higham21_sne_dual_majorant_le_cond2
        (fun i j => A i j + F i j) Bplus xbar
  have hWA : vecNorm2 wA <= q + rho * vecNorm2 wA :=
    hAB.trans (add_le_add hBq hWF)
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hscaled : (1 - rho) * vecNorm2 wA <= q := by
    nlinarith
  have hdiv : vecNorm2 wA <= q / (1 - rho) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
  simpa [wA, q] using hdiv

theorem higham21_sne_qr_action_absorbed_by_nearby_cond2
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho) (hrho_lt : rho < 1)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (Bplus : Fin n -> Fin m -> Real)
    (ybar : Fin m -> Real) (xbar : Fin n -> Real)
    (hybar : ybar = rectTransposeMulVec Bplus xbar) :
    vecNorm2 (rectTransposeMulVec F ybar) <=
      rho / (1 - rho) *
        higham21Cond2With (fun i j => A i j + F i j) Bplus *
          vecNorm2 xbar := by
  let wA : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wB : Fin n -> Real :=
    rectTransposeMulVec
      (absMatrixRect (fun i j => A i j + F i j)) (fun i => |ybar i|)
  let q : Real :=
    higham21Cond2With (fun i j => A i j + F i j) Bplus * vecNorm2 xbar
  have hq : 0 <= q :=
    mul_nonneg (higham21Cond2With_nonneg _ _) (vecNorm2_nonneg _)
  have hFB : vecNorm2 (rectTransposeMulVec F ybar) <= rho * vecNorm2 wA := by
    simpa [wA] using
      higham21_sne_qr_error_transpose_action_le_source
        A F G rho hrho hG hGop hF ybar
  have hWF :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) <=
        rho * vecNorm2 wA := by
    simpa [wA] using
      higham21_sne_qr_abs_error_transpose_action_le_source
        A F G rho hrho hG hGop hF ybar
  have hAB : vecNorm2 wA <= vecNorm2 wB +
      vecNorm2
        (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) := by
    simpa [wA, wB] using
      higham21_sne_source_dual_action_le_nearby_add_error A F ybar
  have hBq : vecNorm2 wB <= q := by
    simpa [wB, q, hybar] using
      higham21_sne_dual_majorant_le_cond2
        (fun i j => A i j + F i j) Bplus xbar
  have hWA : vecNorm2 wA <= q + rho * vecNorm2 wA :=
    hAB.trans (add_le_add hBq hWF)
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hscaled : (1 - rho) * vecNorm2 wA <= q := by
    nlinarith
  have hWAdiv : vecNorm2 wA <= q / (1 - rho) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
  calc
    vecNorm2 (rectTransposeMulVec F ybar) <= rho * vecNorm2 wA := hFB
    _ <= rho * (q / (1 - rho)) := mul_le_mul_of_nonneg_left hWAdiv hrho
    _ = rho / (1 - rho) *
        higham21Cond2With (fun i j => A i j + F i j) Bplus *
          vecNorm2 xbar := by
      simp [q]
      ring

end NumStability
