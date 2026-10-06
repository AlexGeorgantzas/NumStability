-- Higham20Remaining.lean
--
-- Source-facing closure of the normal-equations displays (20.11)--(20.12)
-- and exact algebra for the column-pivoted constraint factorization (20.29).

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.HighamChapter10
import NumStability.Algorithms.LeastSquares.LSNormalEquations
import NumStability.Algorithms.LeastSquares.LSE

namespace NumStability

open scoped BigOperators

/-! ## Equations (20.11) and (20.12) -/

/-- Higham, 2nd ed., Chapter 20, equation (20.11), extracted from the
Cholesky backward-error interface.  The perturbation is constructed as the
actual factorization residual; it is not supplied as a hypothesis. -/
theorem higham20_eq20_11_of_cholesky_backward_error
    (fp : FPModel) (n : ℕ)
    (C_hat R_hat : Fin n → Fin n → ℝ)
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1))) :
    ∃ DeltaC2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        ∑ k : Fin n, R_hat k i * R_hat k j =
          C_hat i j + DeltaC2 i j) ∧
      (∀ i j : Fin n, |DeltaC2 i j| ≤
        gamma fp (n + 1) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j|) := by
  let DeltaC2 : Fin n → Fin n → ℝ :=
    fun i j => (∑ k : Fin n, R_hat k i * R_hat k j) - C_hat i j
  refine ⟨DeltaC2, ?_, ?_⟩
  · intro i j
    simp only [DeltaC2]
    ring
  · intro i j
    simpa only [DeltaC2] using hChol.backward_bound i j

/-- Equation (20.11) for the concrete `fl_cholesky` implementation.  The
public guards are precisely the algorithm's symmetry, gamma-validity,
nonnegative-pivot, and nonzero-diagonal domain conditions. -/
theorem higham20_eq20_11_fl_cholesky
    (fp : FPModel) (n : ℕ) (C_hat : Fin n → Fin n → ℝ)
    (hsym : ∀ i j : Fin n, C_hat i j = C_hat j i)
    (hn1 : gammaValid fp (n + 1))
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n C_hat j)
    (hdiag : ∀ j : Fin n, fl_cholesky fp n C_hat j j ≠ 0) :
    ∃ DeltaC2 : Fin n → Fin n → ℝ,
      (∀ i j : Fin n,
        ∑ k : Fin n,
            fl_cholesky fp n C_hat k i * fl_cholesky fp n C_hat k j =
          C_hat i j + DeltaC2 i j) ∧
      (∀ i j : Fin n, |DeltaC2 i j| ≤
        gamma fp (n + 1) *
          ∑ k : Fin n,
            |fl_cholesky fp n C_hat k i| *
              |fl_cholesky fp n C_hat k j|) := by
  exact higham20_eq20_11_of_cholesky_backward_error fp n C_hat
    (fl_cholesky fp n C_hat)
    (fl_cholesky_backward_error fp n C_hat hsym hn1 hpiv hdiag)

/-- The Cholesky-factorization and two triangular-solve coefficients in the
normal-equations analysis are absorbed by the printed `gamma_(3n+1)`.
This is the finite counterpart of the coefficient used in (20.12). -/
theorem higham20_cholesky_solve_coefficient_le_gamma_3n1
    (fp : FPModel) (n : ℕ) (h3n1 : gammaValid fp (3 * n + 1)) :
    gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2 ≤
      gamma fp (3 * n + 1) := by
  have hstep1 :
      gamma fp n + gamma fp n + gamma fp n * gamma fp n ≤
        gamma fp (2 * n) := by
    have h := gamma_sum_le fp n n (gammaValid_mono fp (by omega) h3n1)
    simpa [show n + n = 2 * n by omega] using h
  have hstep2 :
      gamma fp (n + 1) + gamma fp (2 * n) ≤
        gamma fp (3 * n + 1) := by
    have heq : (n + 1) + 2 * n = 3 * n + 1 := by omega
    have h := gamma_sum_le fp (n + 1) (2 * n) (heq ▸ h3n1)
    have hleft : 0 ≤ gamma fp (n + 1) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) h3n1)
    have hright : 0 ≤ gamma fp (2 * n) :=
      gamma_nonneg fp (gammaValid_mono fp (by omega) h3n1)
    rw [heq] at h
    linarith [mul_nonneg hleft hright]
  nlinarith [hstep1, hstep2]

/-- Higham, 2nd ed., Chapter 20, equation (20.12), with the printed finite
`gamma_m` and `gamma_(3n+1)` componentwise bounds.

The hypotheses are the three immediately preceding computed-stage contracts:
rounded Gram product, rounded Gram right-hand side, and Cholesky
factorization.  The total perturbations in the conclusion are constructed by
`ls_normal_equations_backward`; no normal-equations conclusion is assumed. -/
theorem higham20_eq20_12_normal_equations_gamma3n1
    (fp : FPModel) (m n : ℕ)
    (ATA : Fin n → Fin n → ℝ) (ATb : Fin n → ℝ)
    (absATA : Fin n → Fin n → ℝ) (absATb : Fin n → ℝ)
    (C_hat : Fin n → Fin n → ℝ) (c_hat : Fin n → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (hGram : GramProductError n C_hat ATA absATA (gamma fp m))
    (hGramVec : GramVecError n c_hat ATb absATb (gamma fp m))
    (hChol : CholeskyBackwardError n C_hat R_hat (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1)) :
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      (∀ i j, |DeltaA i j| ≤
        gamma fp m * absATA i j + gamma fp (3 * n + 1) *
          ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, |Deltac i| ≤ gamma fp m * absATb i) := by
  dsimp
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  obtain ⟨DeltaA, Deltac, hEq, hDeltaA, hDeltac⟩ :=
    ls_normal_equations_backward fp n ATA ATb absATA absATb C_hat c_hat
      R_hat hGram hGramVec hChol hR_diag hm hn1
  refine ⟨DeltaA, Deltac, hEq, ?_, hDeltac⟩
  intro i j
  have hcoeff :=
    higham20_cholesky_solve_coefficient_le_gamma_3n1 fp n h3n1
  have hsum_nonneg :
      0 ≤ ∑ k : Fin n, |R_hat k i| * |R_hat k j| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  exact (hDeltaA i j).trans
    (add_le_add_right (mul_le_mul_of_nonneg_right hcoeff hsum_nonneg) _)

/-- Concrete rounded-Gram specialization of (20.12).  Both `C_hat` and
`c_hat` are definitionally the repository's floating-point matrix and
matrix-vector kernels; only the downstream Cholesky certificate and its
nonzero solve domain remain as component interfaces. -/
theorem higham20_eq20_12_fl_gram_gamma3n1
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (R_hat : Fin n → Fin n → ℝ)
    (hChol : CholeskyBackwardError n
      (fl_matMul fp n m n (fun i k => A k i) A) R_hat
      (gamma fp (n + 1)))
    (hR_diag : ∀ i : Fin n, R_hat i i ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1)) :
    let ATA := fun i j : Fin n => ∑ k : Fin m, A k i * A k j
    let ATb := fun i : Fin n => ∑ k : Fin m, A k i * b k
    let c_hat := fl_matVec fp n m (fun i k => A k i) b
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      (∀ i j, |DeltaA i j| ≤
        gamma fp m * (∑ k : Fin m, |A k i| * |A k j|) +
          gamma fp (3 * n + 1) *
            ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, |Deltac i| ≤
        gamma fp m * (∑ k : Fin m, |A k i| * |b k|)) := by
  dsimp
  exact higham20_eq20_12_normal_equations_gamma3n1 fp m n
    (fun i j => ∑ k : Fin m, A k i * A k j)
    (fun i => ∑ k : Fin m, A k i * b k)
    (fun i j => ∑ k : Fin m, |A k i| * |A k j|)
    (fun i => ∑ k : Fin m, |A k i| * |b k|)
    (fl_matMul fp n m n (fun i k => A k i) A)
    (fl_matVec fp n m (fun i k => A k i) b) R_hat
    (gramProductError_from_fl_matMul fp m n A hm)
    (gramVecError_from_fl_matVec fp m n A b hm)
    hChol hR_diag hm h3n1

/-- Fully concrete normal-equations specialization of (20.12): the Gram
matrix and right-hand side use the repository's rounded kernels and the
factor is the actual `fl_cholesky` output.  The visible assumptions are exactly
the symmetry, pivot, diagonal-nonbreakdown, and gamma-validity domain of that
implementation. -/
theorem higham20_eq20_12_fl_gram_fl_cholesky_gamma3n1
    (fp : FPModel) (m n : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (hsym : ∀ i j : Fin n,
      fl_matMul fp n m n (fun i k => A k i) A i j =
        fl_matMul fp n m n (fun i k => A k i) A j i)
    (hpiv : ∀ j : Fin n, 0 ≤ fl_cholPivot fp n
      (fl_matMul fp n m n (fun i k => A k i) A) j)
    (hdiag : ∀ j : Fin n,
      fl_cholesky fp n
        (fl_matMul fp n m n (fun i k => A k i) A) j j ≠ 0)
    (hm : gammaValid fp m) (h3n1 : gammaValid fp (3 * n + 1)) :
    let ATA := fun i j : Fin n => ∑ k : Fin m, A k i * A k j
    let ATb := fun i : Fin n => ∑ k : Fin m, A k i * b k
    let C_hat := fl_matMul fp n m n (fun i k => A k i) A
    let c_hat := fl_matVec fp n m (fun i k => A k i) b
    let R_hat := fl_cholesky fp n C_hat
    let R_hatT := fun i j : Fin n => R_hat j i
    let y_hat := fl_forwardSub fp n R_hatT c_hat
    let x_hat := fl_backSub fp n R_hat y_hat
    ∃ (DeltaA : Fin n → Fin n → ℝ) (Deltac : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, (ATA i j + DeltaA i j) * x_hat j =
        ATb i + Deltac i) ∧
      (∀ i j, |DeltaA i j| ≤
        gamma fp m * (∑ k : Fin m, |A k i| * |A k j|) +
          gamma fp (3 * n + 1) *
            ∑ k : Fin n, |R_hat k i| * |R_hat k j|) ∧
      (∀ i, |Deltac i| ≤
        gamma fp m * (∑ k : Fin m, |A k i| * |b k|)) := by
  dsimp
  have hn1 : gammaValid fp (n + 1) :=
    gammaValid_mono fp (by omega) h3n1
  exact higham20_eq20_12_fl_gram_gamma3n1 fp m n A b
    (fl_cholesky fp n (fl_matMul fp n m n (fun i k => A k i) A))
    (fl_cholesky_backward_error fp n
      (fl_matMul fp n m n (fun i k => A k i) A)
      hsym hn1 hpiv hdiag)
    hdiag hm h3n1

/-! ## Equation (20.29): exact block action -/

/-- The displayed block `[R₁ R₂]` in the column-pivoted constraint QR
factorization (20.29), for `n = p + q`. -/
noncomputable def higham20Eq20_29Block {p q : ℕ}
    (R1 : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ) :
    Fin p → Fin (p + q) → ℝ :=
  fun i => Fin.append (R1 i) (R2 i)

/-- Exact row action of the block in (20.29):
`[R₁ R₂] [x₁;x₂] = R₁x₁ + R₂x₂`. -/
theorem higham20_eq20_29_block_mulVec {p q : ℕ}
    (R1 : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (x1 : Fin p → ℝ) (x2 : Fin q → ℝ) :
    rectMatMulVec (higham20Eq20_29Block R1 R2) (Fin.append x1 x2) =
      fun i : Fin p => rectMatMulVec R1 x1 i + rectMatMulVec R2 x2 i := by
  ext i
  unfold rectMatMulVec higham20Eq20_29Block
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right]

private theorem higham20_orthogonal_transpose_mulVec_mulVec {p : ℕ}
    (Q : Fin p → Fin p → ℝ) (hQ : IsOrthogonal p Q)
    (v : Fin p → ℝ) :
    matMulVec p (matTranspose Q) (matMulVec p Q v) = v := by
  ext i
  calc
    matMulVec p (matTranspose Q) (matMulVec p Q v) i =
        matMulVec p (matMul p (matTranspose Q) Q) v i :=
      (matMulVec_matMul p (matTranspose Q) Q v i).symm
    _ = matMulVec p (idMatrix p) v i := by
      congr 1
      ext a b
      exact hQ.left_inv a b
    _ = v i := congrFun (matMulVec_id p v) i

private theorem higham20_orthogonal_mulVec_transpose_mulVec {p : ℕ}
    (Q : Fin p → Fin p → ℝ) (hQ : IsOrthogonal p Q)
    (v : Fin p → ℝ) :
    matMulVec p Q (matMulVec p (matTranspose Q) v) = v := by
  ext i
  calc
    matMulVec p Q (matMulVec p (matTranspose Q) v) i =
        matMulVec p (matMul p Q (matTranspose Q)) v i :=
      (matMulVec_matMul p Q (matTranspose Q) v i).symm
    _ = matMulVec p (idMatrix p) v i := by
      congr 1
      ext a b
      exact hQ.right_inv a b
    _ = v i := congrFun (matMulVec_id p v) i

/-- Higham, 2nd ed., Chapter 20, equation (20.29), constraint-reduction
identity.  Given the exact column-pivoted QR relation
`BΠ = Q [R₁ R₂]`, the original constraint on the pulled-back vector is
equivalent to the printed triangular equation
`R₁ x̃₁ = Qᵀ d - R₂ x̃₂`.

This theorem assumes only the QR factorization relation and orthogonality;
the reduced constraint equation itself is derived in both directions. -/
theorem higham20_eq20_29_constraint_iff
    {p q : ℕ} (π : Fin (p + q) ≃ Fin (p + q))
    (B : Fin p → Fin (p + q) → ℝ)
    (Q R1 : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (d : Fin p → ℝ) (x1 : Fin p → ℝ) (x2 : Fin q → ℝ)
    (hQ : IsOrthogonal p Q)
    (hfactor : rectPermuteCols π B =
      rectMatMul Q (higham20Eq20_29Block R1 R2)) :
    LSEFeasible B d (vecPermute π.symm (Fin.append x1 x2)) ↔
      ∀ i : Fin p,
        rectMatMulVec R1 x1 i =
          matMulVec p (matTranspose Q) d i - rectMatMulVec R2 x2 i := by
  let z : Fin (p + q) → ℝ := Fin.append x1 x2
  let w : Fin p → ℝ :=
    fun i => rectMatMulVec R1 x1 i + rectMatMulVec R2 x2 i
  have hblock : rectMatMulVec (higham20Eq20_29Block R1 R2) z = w := by
    simpa [z, w] using higham20_eq20_29_block_mulVec R1 R2 x1 x2
  have hfactor_action : rectMatMulVec (rectPermuteCols π B) z =
      matMulVec p Q w := by
    rw [hfactor]
    ext i
    rw [rectMatMulVec_rectMatMul]
    rw [hblock]
    rfl
  constructor
  · intro hfeas
    have hperm : rectMatMulVec (rectPermuteCols π B) z = d := by
      rw [rectMatMulVec_permuteCols]
      exact funext hfeas
    have hQw : matMulVec p Q w = d := hfactor_action.symm.trans hperm
    have hw : w = matMulVec p (matTranspose Q) d := by
      calc
        w = matMulVec p (matTranspose Q) (matMulVec p Q w) :=
          (higham20_orthogonal_transpose_mulVec_mulVec Q hQ w).symm
        _ = matMulVec p (matTranspose Q) d := by rw [hQw]
    intro i
    have hi := congrFun hw i
    dsimp [w] at hi
    linarith
  · intro htri
    have hw : w = matMulVec p (matTranspose Q) d := by
      ext i
      dsimp [w]
      linarith [htri i]
    have hQw : matMulVec p Q w = d := by
      rw [hw]
      exact higham20_orthogonal_mulVec_transpose_mulVec Q hQ d
    intro i
    have hperm := congrFun (rectMatMulVec_permuteCols π B z) i
    calc
      rectMatMulVec B (vecPermute π.symm (Fin.append x1 x2)) i =
          rectMatMulVec (rectPermuteCols π B) z i := by
        simpa [z] using hperm.symm
      _ = matMulVec p Q w i := congrFun hfactor_action i
      _ = d i := congrFun hQw i

/-! ## Equation (20.30): Gaussian annihilation and the reduced block -/

/-- The reduced coefficient block in the penultimate transformation of
(20.30): `Ã₂ - Ã₁ R₁⁻¹ R₂`. -/
noncomputable def higham20Eq20_30ReducedBlock {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ) :
    Fin m → Fin q → ℝ :=
  fun i j => A2 i j - rectMatMul A1 (rectMatMul R1inv R2) i j

private theorem higham20_leftInverse_mulVec_mulVec {p : ℕ}
    (R Rinv : Fin p → Fin p → ℝ) (h : IsLeftInverse p R Rinv)
    (v : Fin p → ℝ) :
    matMulVec p Rinv (matMulVec p R v) = v := by
  ext i
  calc
    matMulVec p Rinv (matMulVec p R v) i =
        matMulVec p (matMul p Rinv R) v i :=
      (matMulVec_matMul p Rinv R v i).symm
    _ = matMulVec p (idMatrix p) v i := by
      congr 1
      ext a b
      exact h a b
    _ = v i := congrFun (matMulVec_id p v) i

/-- Exact action of the reduced block displayed in (20.30). -/
theorem higham20_eq20_30_reducedBlock_mulVec {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (x2 : Fin q → ℝ) :
    rectMatMulVec (higham20Eq20_30ReducedBlock A1 A2 R1inv R2) x2 =
      fun i : Fin m => rectMatMulVec A2 x2 i -
        rectMatMulVec A1 (rectMatMulVec R1inv (rectMatMulVec R2 x2)) i := by
  have hsub :
      rectMatMulVec (higham20Eq20_30ReducedBlock A1 A2 R1inv R2) x2 =
        fun i : Fin m => rectMatMulVec A2 x2 i -
          rectMatMulVec (rectMatMul A1 (rectMatMul R1inv R2)) x2 i := by
    ext i
    unfold rectMatMulVec higham20Eq20_30ReducedBlock
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsub]
  ext i
  rw [rectMatMulVec_rectMatMul, rectMatMulVec_rectMatMul]

/-- Higham, 2nd ed., Chapter 20, equation (20.30), the Gaussian-elimination
step that annihilates `Ã₁`.  Subtracting
`Ã₁ R₁⁻¹` times the constraint block from the objective block leaves
exactly `(Ã₂ - Ã₁ R₁⁻¹ R₂) x̃₂`.

The only algebraic hypothesis is that `R1inv` is a left inverse of the
nonsingular triangular `R₁`; the annihilated conclusion is derived. -/
theorem higham20_eq20_30_gaussian_annihilation {m p q : ℕ}
    (A1 : Fin m → Fin p → ℝ) (A2 : Fin m → Fin q → ℝ)
    (R1 R1inv : Fin p → Fin p → ℝ) (R2 : Fin p → Fin q → ℝ)
    (x1 : Fin p → ℝ) (x2 : Fin q → ℝ)
    (hleft : IsLeftInverse p R1 R1inv) :
    (fun i : Fin m =>
      (rectMatMulVec A1 x1 i + rectMatMulVec A2 x2 i) -
        rectMatMulVec A1
          (rectMatMulVec R1inv
            (fun j : Fin p =>
              rectMatMulVec R1 x1 j + rectMatMulVec R2 x2 j)) i) =
      rectMatMulVec (higham20Eq20_30ReducedBlock A1 A2 R1inv R2) x2 := by
  have hRinvAdd := rectMatMulVec_add R1inv
    (rectMatMulVec R1 x1) (rectMatMulVec R2 x2)
  have hRinvR := higham20_leftInverse_mulVec_mulVec R1 R1inv hleft x1
  have hinner :
      (fun i : Fin p =>
        rectMatMulVec R1inv (rectMatMulVec R1 x1) i +
          rectMatMulVec R1inv (rectMatMulVec R2 x2) i) =
        (fun i : Fin p =>
          x1 i + rectMatMulVec R1inv (rectMatMulVec R2 x2) i) := by
    ext i
    have hi : rectMatMulVec R1inv (rectMatMulVec R1 x1) i = x1 i := by
      simpa [matMulVec, rectMatMulVec] using congrFun hRinvR i
    rw [hi]
  have hA1Add := rectMatMulVec_add A1 x1
    (rectMatMulVec R1inv (rectMatMulVec R2 x2))
  have hReduced := higham20_eq20_30_reducedBlock_mulVec A1 A2 R1inv R2 x2
  rw [hRinvAdd, hinner, hA1Add, hReduced]
  ext i
  ring

end NumStability
