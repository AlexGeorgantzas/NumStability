import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.MatrixInversion

/-!
# Chapter14 Section02 TriangularInversion Method2B MatrixInversion

Canonical destination for material split out of
`NumStability.Algorithms.MatrixInversion` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham equation (14.14), Method 2B block-update decomposition:
    the computed off-diagonal block is the exact block product plus an explicit
    perturbation. -/
theorem higham14_eq14_14_method2B_block_update_decomposition {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ) (i : Fin r) (j : Fin m) :
    X21_hat i j =
      higham14_method2BBlockUpdateExact X22 L21 X11 i j +
        higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j := by
  unfold higham14_method2BBlockUpdateDelta
  ring

/-- The Method 2B block-update perturbation inherits any supplied
    componentwise product-error bound for the rectangular triple product in
    equation (14.14). -/
theorem higham14_eq14_14_method2B_block_update_delta_bound {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ)
    (hBound : ∀ i : Fin r, ∀ j : Fin m,
      |X21_hat i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j| ≤
          ε * absBound i j) :
    ∀ i : Fin r, ∀ j : Fin m,
      |higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j| ≤
        ε * absBound i j := by
  intro i j
  simpa [higham14_method2BBlockUpdateDelta] using hBound i j

/-- Higham, 2nd ed., Chapter 14, equation (14.14), Method 2B:
    source-facing package for the rounded off-diagonal block update.

    The package records both the exact decomposition of the computed block into
    `-X22 * L21 * X11` plus an explicit perturbation and the componentwise
    product-error bound on that perturbation.  The instability analysis that
    uses this update certificate remains a separate source obligation. -/
structure Method2BBlockUpdateSpec {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ) : Prop where
  /-- The computed off-diagonal block is the exact Method 2B update plus
      the explicitly named perturbation. -/
  update_decomposition : ∀ i : Fin r, ∀ j : Fin m,
    X21_hat i j =
      higham14_method2BBlockUpdateExact X22 L21 X11 i j +
        higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j
  /-- The explicit perturbation obeys the supplied componentwise product-error
      envelope for the rectangular triple product. -/
  delta_bound : ∀ i : Fin r, ∀ j : Fin m,
    |higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11 i j| ≤
      ε * absBound i j

/-- Higham, 2nd ed., Chapter 14, equation (14.14), Method 2B:
    build the source-facing block-update package from a rectangular
    triple-product error certificate. -/
theorem higham14_eq14_14_method2B_block_update_spec_of_product_error {m r : ℕ}
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (X11 : Fin m → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ)
    (hBound : ∀ i : Fin r, ∀ j : Fin m,
      |X21_hat i j -
        higham14_method2BBlockUpdateExact X22 L21 X11 i j| ≤
          ε * absBound i j) :
    Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound where
  update_decomposition :=
    higham14_eq14_14_method2B_block_update_decomposition
      X21_hat X22 L21 X11
  delta_bound :=
    higham14_eq14_14_method2B_block_update_delta_bound
      X21_hat X22 L21 X11 ε absBound hBound

/-- Higham equation (14.14), Method 2B residual identity:
    the off-diagonal left-residual block
    `X21_hat * L11 + X22 * L21` is exactly the block-update perturbation
    propagated through `L11`, provided `X11 * L11 = I`.

    This isolates the algebraic hinge used by the instability discussion:
    even if the block update has a local product-error certificate, that
    perturbation is subsequently multiplied by `L11` in the residual. -/
theorem higham14_eq14_14_method2B_offdiag_residual_eq_delta_mul {m r : ℕ}
    (L11 X11 : Fin m → Fin m → ℝ)
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (ε : ℝ) (absBound : Fin r → Fin m → ℝ)
    (hSpec : Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound)
    (hX11_left : IsLeftInverse m L11 X11) :
    ∀ i : Fin r, ∀ j : Fin m,
      rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j =
        rectMatMul
          (higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11)
          L11 i j := by
  intro i j
  let Δ := higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11
  let E := higham14_method2BBlockUpdateExact X22 L21 X11
  have hX21 : X21_hat = fun a b => E a b + Δ a b := by
    ext a b
    exact hSpec.update_decomposition a b
  have hX11L11 : rectMatMul X11 L11 = idMatrix m := by
    ext a b
    exact hX11_left a b
  have hE_mul :
      rectMatMul E L11 = fun a b => -rectMatMul X22 L21 a b := by
    unfold E higham14_method2BBlockUpdateExact
    calc
      rectMatMul (fun a b => -rectMatMul (rectMatMul X22 L21) X11 a b) L11
          = fun a b =>
              -rectMatMul (rectMatMul (rectMatMul X22 L21) X11) L11 a b := by
            exact rectMatMul_neg_left (rectMatMul (rectMatMul X22 L21) X11) L11
      _ = fun a b =>
              -rectMatMul (rectMatMul X22 L21) (rectMatMul X11 L11) a b := by
            rw [rectMatMul_assoc (rectMatMul X22 L21) X11 L11]
      _ = fun a b =>
              -rectMatMul (rectMatMul X22 L21) (idMatrix m) a b := by
            rw [hX11L11]
      _ = fun a b => -rectMatMul X22 L21 a b := by
            rw [rectMatMul_id_right (rectMatMul X22 L21)]
  have hX21_mul :
      rectMatMul X21_hat L11 i j =
        rectMatMul E L11 i j + rectMatMul Δ L11 i j := by
    calc
      rectMatMul X21_hat L11 i j =
          rectMatMul (fun a b => E a b + Δ a b) L11 i j := by
            rw [hX21]
      _ = rectMatMul E L11 i j + rectMatMul Δ L11 i j := by
            rw [rectMatMul_add_left E Δ L11]
  calc
    rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j
        = (rectMatMul E L11 i j + rectMatMul Δ L11 i j) +
            rectMatMul X22 L21 i j := by rw [hX21_mul]
    _ = (-rectMatMul X22 L21 i j + rectMatMul Δ L11 i j) +
            rectMatMul X22 L21 i j := by rw [hE_mul]
    _ = rectMatMul Δ L11 i j := by ring

/-- Higham equation (14.14), Method 2B obstruction wrapper:
    if the propagated block-update perturbation is larger than a proposed
    off-diagonal residual budget in one entry, then the whole off-diagonal
    residual block cannot satisfy that budget.

    This is a source-facing obstruction hinge, not the full instability
    theorem: the large propagated-delta hypothesis still has to be established
    for a concrete Method 2B instance. -/
theorem higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta
    {m r : ℕ}
    (L11 X11 : Fin m → Fin m → ℝ)
    (X21_hat : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin m → ℝ)
    (ε : ℝ) (absBound sourceBudget : Fin r → Fin m → ℝ)
    (hSpec : Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound)
    (hX11_left : IsLeftInverse m L11 X11)
    {i0 : Fin r} {j0 : Fin m}
    (hLarge :
      sourceBudget i0 j0 <
        |rectMatMul
          (higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11)
          L11 i0 j0|) :
    ¬ (∀ i : Fin r, ∀ j : Fin m,
      |rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j| ≤
        sourceBudget i j) := by
  intro hSmall
  have hId :=
    higham14_eq14_14_method2B_offdiag_residual_eq_delta_mul
      L11 X11 X21_hat X22 L21 ε absBound hSpec hX11_left i0 j0
  have hEntry := hSmall i0 j0
  rw [hId] at hEntry
  exact not_lt_of_ge hEntry hLarge

/-- One-column diagonal-block specialization of the Method 2B residual
    obstruction.  In the scalar `L11` case, the propagated perturbation entry
    is the explicit product `Delta21 * L11`, so callers can supply a concrete
    scalar lower bound instead of a rectangular matrix product. -/
theorem higham14_eq14_14_method2B_no_small_offdiag_residual_of_scalar_propagated_delta
    {r : ℕ}
    (L11 X11 : Fin 1 → Fin 1 → ℝ)
    (X21_hat : Fin r → Fin 1 → ℝ)
    (X22 : Fin r → Fin r → ℝ) (L21 : Fin r → Fin 1 → ℝ)
    (ε : ℝ) (absBound sourceBudget : Fin r → Fin 1 → ℝ)
    (hSpec : Method2BBlockUpdateSpec X21_hat X22 L21 X11 ε absBound)
    (hX11_left : IsLeftInverse 1 L11 X11)
    {i0 : Fin r}
    (hLarge :
      sourceBudget i0 (0 : Fin 1) <
        |higham14_method2BBlockUpdateDelta X21_hat X22 L21 X11
            i0 (0 : Fin 1) * L11 (0 : Fin 1) (0 : Fin 1)|) :
    ¬ (∀ i : Fin r, ∀ j : Fin 1,
      |rectMatMul X21_hat L11 i j + rectMatMul X22 L21 i j| ≤
        sourceBudget i j) := by
  apply
    higham14_eq14_14_method2B_no_small_offdiag_residual_of_propagated_delta
      L11 X11 X21_hat X22 L21 ε absBound sourceBudget hSpec hX11_left
      (i0 := i0) (j0 := (0 : Fin 1))
  simpa [rectMatMul] using hLarge

/-- Exact Method 2B off-diagonal block formula from the block equation
    `X21 * L11 + X22 * L21 = 0` and the diagonal-block inverse certificate
    `L11 * X11 = I`.  This is the exact algebra behind equation (14.14);
    the rounded update is represented separately by
    `higham14_method2BBlockUpdateDelta`. -/
theorem higham14_eq14_14_method2B_exact_offdiag_block_update {m r : ℕ}
    (L11 X11 : Fin m → Fin m → ℝ)
    (L21 X21 : Fin r → Fin m → ℝ)
    (X22 : Fin r → Fin r → ℝ)
    (hOffdiag : ∀ i : Fin r, ∀ j : Fin m,
      rectMatMul X21 L11 i j + rectMatMul X22 L21 i j = 0)
    (hX11 : IsRightInverse m L11 X11) :
    ∀ i : Fin r, ∀ j : Fin m,
      X21 i j = higham14_method2BBlockUpdateExact X22 L21 X11 i j := by
  intro i j
  have hzero :
      rectMatMul
          (fun a b => rectMatMul X21 L11 a b + rectMatMul X22 L21 a b)
          X11 i j = 0 := by
    unfold rectMatMul
    apply Finset.sum_eq_zero
    intro x _
    have hx := hOffdiag i x
    unfold rectMatMul at hx
    change (∑ k : Fin m, X21 i k * L11 k x) +
        (∑ k : Fin r, X22 i k * L21 k x) = 0 at hx
    change ((∑ k : Fin m, X21 i k * L11 k x) +
        (∑ k : Fin r, X22 i k * L21 k x)) * X11 x j = 0
    rw [hx]
    ring
  have hsplit :
      rectMatMul (rectMatMul X21 L11) X11 i j +
        rectMatMul (rectMatMul X22 L21) X11 i j = 0 := by
    simpa [rectMatMul_add_left] using hzero
  have hassoc : rectMatMul (rectMatMul X21 L11) X11 =
      rectMatMul X21 (rectMatMul L11 X11) :=
    rectMatMul_assoc X21 L11 X11
  have hright : rectMatMul L11 X11 = idMatrix m := by
    ext a b
    exact hX11 a b
  have hleft : rectMatMul (rectMatMul X21 L11) X11 i j = X21 i j := by
    rw [hassoc, hright]
    exact congrFun (congrFun (rectMatMul_id_right X21) i) j
  rw [hleft] at hsplit
  unfold higham14_method2BBlockUpdateExact
  linarith

end NumStability
