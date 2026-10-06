import Mathlib.Analysis.CStarAlgebra.Matrix
import NumStability.Analysis.SingularValues.Basic

/-!
# Higham Chapter 6: two-sided unitary invariance

Source correspondence for the operator-2 and Frobenius two-sided
unitary-invariance prose in Section 6.2. The operator-2 adapter is also the
narrow dependency used by the condition-number and block-antidiagonal leaves.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix
open scoped Matrix.Norms.L2Operator

/-- The source-facing operator `2`-norm equals Mathlib's `l2` operator norm of
    the matrix view. -/
theorem ch6aside_op2_eq_l2 {m n : ℕ} (A : CMatrix m n) :
    complexMatrixOp2 A = ‖complexCMatrixAsMatrix A‖ := by
  rw [complexMatrixOp2]
  exact (Matrix.l2_opNorm_def (complexCMatrixAsMatrix A)).symm

/-! ### (ii) Two-sided unitary invariance of the `2`- and Frobenius norms -/

/-- The `l2` operator norm of the `m × m` identity is `1` (`m ≥ 1`). -/
private theorem ch6aside_l2_one {m : ℕ} [Nonempty (Fin m)] :
    ‖(1 : Matrix (Fin m) (Fin m) ℂ)‖ = 1 := by
  rw [show (1 : Matrix (Fin m) (Fin m) ℂ)
        = Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
      Matrix.l2_opNorm_diagonal, Pi.norm_def, Finset.sup_const Finset.univ_nonempty]
  simp

/-- The `l2` operator norm of a unitary matrix is `1` (`m ≥ 1`). -/
private theorem ch6aside_l2_unitary {m : ℕ} [Nonempty (Fin m)]
    {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) :
    ‖U‖ = 1 := by
  have h1 : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hsq : ‖Uᴴ * U‖ = ‖U‖ * ‖U‖ := Matrix.l2_opNorm_conjTranspose_mul_self U
  rw [h1, ch6aside_l2_one] at hsq
  nlinarith [norm_nonneg U]

/-- **Two-sided unitary invariance of the operator `2`-norm** (Higham §6.2,
    p. 108-109: "`‖UAV‖ = ‖A‖`" for the unitarily invariant `2`-norm).
    For unitary `U ∈ ℂ^{m×m}`, `V ∈ ℂ^{n×n}`, `‖UAV‖₂ = ‖A‖₂`. -/
theorem ch6aside_op2_two_sided_unitary_invariant {m n : ℕ}
    [Nonempty (Fin m)] [Nonempty (Fin n)]
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : CMatrix m n) :
    complexMatrixOp2
        ((U * complexCMatrixAsMatrix A * V : Matrix (Fin m) (Fin n) ℂ)) =
      complexMatrixOp2 A := by
  set Am : Matrix (Fin m) (Fin n) ℂ := complexCMatrixAsMatrix A with hAm
  have hUn : ‖U‖ = 1 := ch6aside_l2_unitary hU
  have hVn : ‖V‖ = 1 := ch6aside_l2_unitary hV
  have hUHU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hVVH : V * Vᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := V)).mp hV
    rwa [Matrix.star_eq_conjTranspose] at this
  rw [ch6aside_op2_eq_l2, ch6aside_op2_eq_l2]
  have hcast : (complexCMatrixAsMatrix
      ((U * Am * V : Matrix (Fin m) (Fin n) ℂ))) = U * Am * V := rfl
  rw [hcast, ← hAm]
  -- upper bound: ‖U Am V‖ ≤ ‖Am‖
  have hle : ‖U * Am * V‖ ≤ ‖Am‖ := by
    calc ‖U * Am * V‖ ≤ ‖U * Am‖ * ‖V‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖U‖ * ‖Am‖) * ‖V‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖Am‖ := by rw [hUn, hVn]; ring
  -- lower bound: ‖Am‖ = ‖Uᴴ (U Am V) Vᴴ‖ ≤ ‖U Am V‖
  have hUHn : ‖Uᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hUn
  have hVHn : ‖Vᴴ‖ = 1 := by rw [Matrix.l2_opNorm_conjTranspose]; exact hVn
  have hge : ‖Am‖ ≤ ‖U * Am * V‖ := by
    have hAmrw : Am = Uᴴ * (U * Am * V) * Vᴴ := by
      have : Uᴴ * (U * Am * V) * Vᴴ = (Uᴴ * U) * Am * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      rw [this, hUHU, hVVH, Matrix.one_mul, Matrix.mul_one]
    calc ‖Am‖ = ‖Uᴴ * (U * Am * V) * Vᴴ‖ := by rw [← hAmrw]
      _ ≤ ‖Uᴴ * (U * Am * V)‖ * ‖Vᴴ‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖Uᴴ‖ * ‖U * Am * V‖) * ‖Vᴴ‖ := by gcongr; exact Matrix.l2_opNorm_mul _ _
      _ = ‖U * Am * V‖ := by rw [hUHn, hVHn]; ring
  exact le_antisymm hle hge

/-- The squared Frobenius norm equals `tr(AᴴA)` (embedded in `ℂ`); the identity
    `‖A‖_F² = tr(AᴴA)` that drives Frobenius unitary invariance. -/
theorem ch6aside_frobeniusSq_eq_trace {m n : ℕ} (A : CMatrix m n) :
    (complexMatrixFrobeniusSq A : ℂ) =
      ((complexCMatrixAsMatrix A)ᴴ * complexCMatrixAsMatrix A).trace := by
  unfold complexMatrixFrobeniusSq Matrix.trace
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply]
  simp only [complexCMatrixAsMatrix, Complex.star_def]
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **Two-sided unitary invariance of the Frobenius norm** (Higham §6.2,
    p. 108-109).  For unitary `U ∈ ℂ^{m×m}`, `V ∈ ℂ^{n×n}`, `‖UAV‖_F = ‖A‖_F`. -/
theorem ch6aside_frobenius_two_sided_unitary_invariant {m n : ℕ}
    {U : Matrix (Fin m) (Fin m) ℂ} {V : Matrix (Fin n) (Fin n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin m) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (A : CMatrix m n) :
    complexMatrixFrobenius
        ((U * complexCMatrixAsMatrix A * V : Matrix (Fin m) (Fin n) ℂ)) =
      complexMatrixFrobenius A := by
  set Am : Matrix (Fin m) (Fin n) ℂ := complexCMatrixAsMatrix A with hAm
  have hUHU : Uᴴ * U = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := U)).mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hVVH : V * Vᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := V)).mp hV
    rwa [Matrix.star_eq_conjTranspose] at this
  -- FrobSq (U Am V) = FrobSq Am via trace cyclicity.
  have hsq : complexMatrixFrobeniusSq
      ((U * Am * V : Matrix (Fin m) (Fin n) ℂ)) = complexMatrixFrobeniusSq A := by
    have hcast : complexCMatrixAsMatrix
        ((U * Am * V : Matrix (Fin m) (Fin n) ℂ)) = U * Am * V := rfl
    have key :
        (((U * Am * V)ᴴ) * (U * Am * V)).trace = (Amᴴ * Am).trace := by
      have hexp : ((U * Am * V)ᴴ) * (U * Am * V) = Vᴴ * (Amᴴ * Am) * V := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Uᴴ U (Am * V), hUHU, Matrix.one_mul]
      rw [hexp, Matrix.trace_mul_cycle Vᴴ (Amᴴ * Am) V, ← Matrix.mul_assoc,
        hVVH, Matrix.one_mul]
    have hc : (complexMatrixFrobeniusSq ((U * Am * V : Matrix (Fin m) (Fin n) ℂ)) : ℂ)
        = (complexMatrixFrobeniusSq A : ℂ) := by
      rw [ch6aside_frobeniusSq_eq_trace, ch6aside_frobeniusSq_eq_trace,
        hcast, ← hAm, key]
    exact_mod_cast hc
  rw [complexMatrixFrobenius, complexMatrixFrobenius, hsq]

end NumStability
