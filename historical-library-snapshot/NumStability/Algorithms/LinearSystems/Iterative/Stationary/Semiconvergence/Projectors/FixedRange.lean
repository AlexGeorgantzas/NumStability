import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra

/-!
# Fixed and range projectors for index-one stationary iterations

Reusable algebra and matrix-power consequences for the fixed and range
projectors induced by an index-one Drazin inverse.
-/

namespace NumStability

open scoped BigOperators

/-- Multiplying two complements expands as
    `(I - A)(I - E) = I - E - A + AE`. -/
private theorem matMul_matSub_id_matSub_id (n : ℕ)
    (A E : Fin n → Fin n → ℝ) :
    matMul n (matSub_id n A) (matSub_id n E) =
      fun i j => idMatrix n i j - E i j - A i j + matMul n A E i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [sub_mul, mul_sub, Finset.sum_sub_distrib]
  have hII :
      ∑ k : Fin n, idMatrix n i k * idMatrix n k j = idMatrix n i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n (idMatrix n))
    simpa [matMul] using h
  have hIE :
      ∑ k : Fin n, idMatrix n i k * E k j = E i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n E)
    simpa [matMul] using h
  have hAI :
      ∑ k : Fin n, A i k * idMatrix n k j = A i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n A)
    simpa [matMul] using h
  rw [hII, hIE, hAI]
  ring

/-- Left multiplication by a complement expands as `(I-A)B = B - AB`. -/
private theorem matMul_matSub_id_left (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    matMul n (matSub_id n A) B =
      fun i j => B i j - matMul n A B i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  have hIB :
      ∑ k : Fin n, idMatrix n i k * B k j = B i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_left n B)
    simpa [matMul] using h
  rw [hIB]

/-- Right multiplication by a complement expands as `B(I-A) = B - BA`. -/
private theorem matMul_matSub_id_right (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    matMul n B (matSub_id n A) =
      fun i j => B i j - matMul n B A i j := by
  ext i j
  unfold matMul matSub_id
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  have hBI :
      ∑ k : Fin n, B i k * idMatrix n k j = B i j := by
    have h := congrArg (fun T : Fin n → Fin n → ℝ => T i j)
      (matMul_id_right n B)
    simpa [matMul] using h
  rw [hBI]











































/-- The Drazin range projector commutes with the stationary iteration matrix
    `G`. -/
theorem stationaryDrazinRangeProjector_commutes_with_G (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n G (stationaryDrazinRangeProjector n G D) =
      matMul n (stationaryDrazinRangeProjector n G D) G := by
  let A := matSub_id n G
  let E := stationaryDrazinRangeProjector n G D
  have hG : matSub_id n A = G := by
    ext i j
    dsimp [A, matSub_id, idMatrix]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hAE : matMul n A E = A := by
    simpa [A, E] using
      stationaryDrazinRangeProjector_matSub_id_mul_left n G D hD
  have hEA : matMul n E A = A := by
    simpa [A, E] using
      stationaryDrazinRangeProjector_matSub_id_mul_right n G D hD
  calc
    matMul n G (stationaryDrazinRangeProjector n G D) =
      matMul n (matSub_id n A) E := by
        rw [hG]
    _ = (fun i j => E i j - matMul n A E i j) :=
        matMul_matSub_id_left n A E
    _ = (fun i j => E i j - A i j) := by
        rw [hAE]
    _ = (fun i j => E i j - matMul n E A i j) := by
        rw [hEA]
    _ = matMul n E (matSub_id n A) := by
        exact (matMul_matSub_id_right n A E).symm
    _ = matMul n (stationaryDrazinRangeProjector n G D) G := by
        rw [hG]

/-- The Drazin range projector commutes with every finite power of `G`. -/
theorem stationaryDrazinRangeProjector_commutes_with_matPow (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k, matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D) =
      matMul n (stationaryDrazinRangeProjector n G D) (matPow n G k) := by
  exact matPow_comm_of_matMul_comm n G
    (stationaryDrazinRangeProjector n G D)
    (stationaryDrazinRangeProjector_commutes_with_G n G D hD)

/-- Sandwiching a powered range component by the Drazin range projector leaves
    it unchanged: `E G^k E = G^k E`. -/
theorem stationaryDrazinRangeProjector_matPow_sandwich (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k,
      matMul n (stationaryDrazinRangeProjector n G D)
        (matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D)) =
      matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D) := by
  intro k
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  have hcomm :
      matMul n (matPow n G k) E = matMul n E (matPow n G k) := by
    simpa [E] using stationaryDrazinRangeProjector_commutes_with_matPow n G D hD k
  calc
    matMul n (stationaryDrazinRangeProjector n G D)
        (matMul n (matPow n G k) (stationaryDrazinRangeProjector n G D)) =
      matMul n E (matMul n (matPow n G k) E) := rfl
    _ = matMul n (matMul n E (matPow n G k)) E := by
        rw [matMul_assoc]
    _ = matMul n (matMul n (matPow n G k) E) E := by
        rw [← hcomm]
    _ = matMul n (matPow n G k) (matMul n E E) := by
        rw [matMul_assoc]
    _ = matMul n (matPow n G k) E := by
        rw [hEid]







































































/-- The complementary Drazin fixed/null projector `I-E` is idempotent. -/
theorem stationaryDrazinFixedProjector_idempotent (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n (stationaryDrazinFixedProjector n G D)
      (stationaryDrazinFixedProjector n G D) =
    stationaryDrazinFixedProjector n G D := by
  let E := stationaryDrazinRangeProjector n G D
  have hEid : matMul n E E = E := by
    simpa [E] using stationaryDrazinRangeProjector_idempotent n G D hD
  calc
    matMul n (stationaryDrazinFixedProjector n G D)
        (stationaryDrazinFixedProjector n G D) =
      matMul n (matSub_id n E) (matSub_id n E) := rfl
    _ = (fun i j => idMatrix n i j - E i j - E i j + matMul n E E i j) :=
        matMul_matSub_id_matSub_id n E E
    _ = stationaryDrazinFixedProjector n G D := by
        ext i j
        rw [hEid]
        unfold stationaryDrazinFixedProjector matSub_id
        ring

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.25)-(17.27):
    the Drazin fixed/null projector `I - (I - G)D` is fixed by the stationary
    iteration matrix `G`.  This is the algebraic projector fact needed by the
    finite singular error split. -/
theorem stationaryDrazinFixedProjector_fixed_by_G (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    matMul n G (stationaryDrazinFixedProjector n G D) =
      stationaryDrazinFixedProjector n G D := by
  let A := matSub_id n G
  let E := stationaryDrazinRangeProjector n G D
  have hG : matSub_id n A = G := by
    ext i j
    dsimp [A, matSub_id, idMatrix]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  have hAE : matMul n A E = A := by
    dsimp [A, E, stationaryDrazinRangeProjector]
    rw [← matMul_assoc]
    exact hD.index_one
  calc
    matMul n G (stationaryDrazinFixedProjector n G D)
        = matMul n G (matSub_id n E) := rfl
    _ = matMul n (matSub_id n A) (matSub_id n E) := by
            rw [hG]
    _ = (fun i j => idMatrix n i j - E i j - A i j + matMul n A E i j) :=
            matMul_matSub_id_matSub_id n A E
    _ = matSub_id n E := by
            ext i j
            rw [hAE]
            unfold matSub_id
            ring
    _ = stationaryDrazinFixedProjector n G D := rfl

/-- Every finite power of `G` fixes the Drazin fixed/null projector.  This is
    the finite-power algebraic side of the limiting projector identity used in
    Higham's semiconvergent singular-system analysis. -/
theorem stationaryDrazinFixedProjector_matPow_fixed (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ k, matMul n (matPow n G k) (stationaryDrazinFixedProjector n G D) =
      stationaryDrazinFixedProjector n G D := by
  exact matPow_mul_fixed_of_matMul_fixed n G
    (stationaryDrazinFixedProjector n G D)
    (stationaryDrazinFixedProjector_fixed_by_G n G D hD)

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.25)-(17.27):
    finite algebraic split behind the singular-system limiting projector.
    Every powered vector decomposes into its propagated Drazin range component
    plus the fixed/null Drazin projector component. -/
theorem stationaryDrazin_matPow_vec_split (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ) (m : ℕ) :
    ∀ i, matMulVec n (matPow n G m) v i =
      matMulVec n (matMul n (matPow n G m)
        (stationaryDrazinRangeProjector n G D)) v i +
      matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
  intro i
  let E := stationaryDrazinRangeProjector n G D
  let C := stationaryDrazinFixedProjector n G D
  have hsplit : v = fun j => matMulVec n E v j + matMulVec n C v j := by
    ext j
    simpa [E, C, stationaryDrazinFixedProjector] using
      (matMulVec_add_complement_apply n E v j).symm
  have hfixedMat : matMul n (matPow n G m) C = C := by
    simpa [C] using stationaryDrazinFixedProjector_matPow_fixed n G D hD m
  calc
    matMulVec n (matPow n G m) v i =
        matMulVec n (matPow n G m)
          (fun j => matMulVec n E v j + matMulVec n C v j) i := by
          exact congrArg (fun w => matMulVec n (matPow n G m) w i) hsplit
    _ = matMulVec n (matPow n G m) (matMulVec n E v) i +
        matMulVec n (matPow n G m) (matMulVec n C v) i := by
          simpa using congrFun
            (matMulVec_add_right n (matPow n G m)
              (matMulVec n E v) (matMulVec n C v)) i
    _ = matMulVec n (matMul n (matPow n G m) E) v i +
        matMulVec n (matMul n (matPow n G m) C) v i := by
          rw [← matMulVec_matMul n (matPow n G m) E v i]
          rw [← matMulVec_matMul n (matPow n G m) C v i]
    _ = matMulVec n (matMul n (matPow n G m) E) v i +
        matMulVec n C v i := by
          rw [hfixedMat]
    _ = matMulVec n (matMul n (matPow n G m)
          (stationaryDrazinRangeProjector n G D)) v i +
        matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
          rfl

/-- Conditional limiting form of `stationaryDrazin_matPow_vec_split`: if the
    Drazin range component decays to zero, then `G^m v` tends coordinatewise
    to the fixed/null Drazin projector component.  This records the formal
    dependency used by the semiconvergent singular-system discussion without
    asserting semiconvergence or Drazin existence. -/
theorem stationaryDrazin_matPow_vec_tendsto_fixedProjector_of_range_tendsto_zero
    (n : ℕ) (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ)
    (hRange : ∀ i, Filter.Tendsto
      (fun m : ℕ => matMulVec n (matMul n (matPow n G m)
        (stationaryDrazinRangeProjector n G D)) v i)
      Filter.atTop (nhds 0)) :
    ∀ i, Filter.Tendsto
      (fun m : ℕ => matMulVec n (matPow n G m) v i)
      Filter.atTop
      (nhds (matMulVec n (stationaryDrazinFixedProjector n G D) v i)) := by
  intro i
  let E := stationaryDrazinRangeProjector n G D
  let C := stationaryDrazinFixedProjector n G D
  have hRangeE : Filter.Tendsto
      (fun m : ℕ => matMulVec n (matMul n (matPow n G m) E) v i)
      Filter.atTop (nhds 0) := by
    simpa [E] using hRange i
  have hlimSplit : Filter.Tendsto
      (fun m : ℕ =>
        matMulVec n (matMul n (matPow n G m) E) v i +
          matMulVec n C v i)
      Filter.atTop (nhds (0 + matMulVec n C v i)) := by
    exact hRangeE.add tendsto_const_nhds
  have hcongr :
      (fun m : ℕ =>
        matMulVec n (matMul n (matPow n G m) E) v i +
          matMulVec n C v i) =ᶠ[Filter.atTop]
      (fun m : ℕ => matMulVec n (matPow n G m) v i) := by
    exact Filter.Eventually.of_forall fun m => by
      have hsplit := stationaryDrazin_matPow_vec_split n G D hD v m i
      simpa [E, C] using hsplit.symm
  exact Filter.Tendsto.congr'
    (f₁ := fun m : ℕ =>
      matMulVec n (matMul n (matPow n G m) E) v i + matMulVec n C v i)
    (f₂ := fun m : ℕ => matMulVec n (matPow n G m) v i)
    hcongr
    (by simpa [C] using hlimSplit)

/-- Vector-action form of `stationaryDrazinFixedProjector_fixed_by_G`. -/
theorem stationaryDrazinFixedProjector_matMulVec_fixed (n : ℕ)
    (G D : Fin n → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D)
    (v : Fin n → ℝ) :
    ∀ i, matMulVec n G
        (matMulVec n (stationaryDrazinFixedProjector n G D) v) i =
      matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
  intro i
  calc
    matMulVec n G (matMulVec n (stationaryDrazinFixedProjector n G D) v) i
        = matMulVec n
            (matMul n G (stationaryDrazinFixedProjector n G D)) v i := by
            rw [← matMulVec_matMul]
    _ = matMulVec n (stationaryDrazinFixedProjector n G D) v i := by
            rw [stationaryDrazinFixedProjector_fixed_by_G n G D hD]

/-- The Drazin range projector supplies the fixed-null hypothesis required by
    the finite singular error split: `G` fixes `(I - E)M^{-1}xi_t`. -/
theorem stationaryDrazinRangeProjector_null_component_fixed (n : ℕ)
    (G D M_inv : Fin n → Fin n → ℝ) (xi : ℕ → Fin n → ℝ)
    (hD : IndexOneDrazinInverse n (matSub_id n G) D) :
    ∀ t i,
      matMulVec n G
        (matMulVec n (matSub_id n (stationaryDrazinRangeProjector n G D))
          (matMulVec n M_inv (xi t))) i =
      matMulVec n (matSub_id n (stationaryDrazinRangeProjector n G D))
        (matMulVec n M_inv (xi t)) i := by
  intro t i
  simpa [stationaryDrazinFixedProjector] using
    stationaryDrazinFixedProjector_matMulVec_fixed n G D hD
      (matMulVec n M_inv (xi t)) i

end NumStability
