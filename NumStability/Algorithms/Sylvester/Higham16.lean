-- Algorithms/Sylvester/Higham16.lean
--
-- Source-facing Chapter 16 surfaces for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed.  This file complements the older square
-- Frobenius-norm Sylvester infrastructure in `SylvesterSpec`,
-- `SylvesterBackward`, and `SylvesterPerturbation`.

import NumStability.Algorithms.Sylvester.SylvesterPerturbation
import NumStability.Algorithms.Sylvester.SylvesterBackward
import Mathlib.LinearAlgebra.Matrix.Vec

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- Rectangular source equations
-- ============================================================

/-- On square matrices, the rectangular product agrees with the repository's
    legacy square `matMul`. -/
theorem matMulRect_square_eq_matMul (n : Nat) (A B : Fin n -> Fin n -> Real) :
    matMulRect n n n A B = matMul n A B := by
  rfl

/-- Higham, 2nd ed., Chapter 16, equation (16.1):
    rectangular Sylvester operator `X |-> AX - XB`. -/
noncomputable def sylvesterOpRect (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (X : RMatFn m n) : RMatFn m n :=
  fun i j => matMulRect m m n A X i j - matMulRect m n n X B i j

/-- The square source-facing Sylvester operator is the existing legacy square
    operator used by the proved Chapter 16 infrastructure. -/
theorem sylvesterOpRect_square_eq_sylvesterOp (n : Nat)
    (A B X : Fin n -> Fin n -> Real) :
    sylvesterOpRect n n A B X = sylvesterOp n A B X := by
  rfl

/-- Higham, 2nd ed., Chapter 16.1, equation (16.1):
    source-numbered alias for square/rectangular product compatibility. -/
alias H16_eq16_1_matMulRect_square_eq_matMul := matMulRect_square_eq_matMul

/-- Higham, 2nd ed., Chapter 16.1, equation (16.1):
    source-numbered alias for square/rectangular Sylvester-operator
    compatibility. -/
alias H16_eq16_1_sylvesterOpRect_square_eq_sylvesterOp :=
  sylvesterOpRect_square_eq_sylvesterOp

/-- Higham, 2nd ed., Chapter 16, equation (16.1):
    the rectangular Sylvester equation predicate `AX - XB = C`. -/
def IsSylvesterSolutionRect (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X : RMatFn m n) : Prop :=
  forall i j, sylvesterOpRect m n A B X i j = C i j

/-- Higham, 2nd ed., Chapter 16, equations (16.9), (16.11), and (16.29):
    rectangular residual `C - (AY - YB)` for an approximate Sylvester solution. -/
noncomputable def sylvesterResidualRect (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Yhat : RMatFn m n) : RMatFn m n :=
  fun i j => C i j - sylvesterOpRect m n A B Yhat i j

/-- Rectangular residual expanded:
    `R_ij = C_ij - (AY)_ij + (YB)_ij`. -/
theorem sylvesterResidualRect_eq (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Yhat : RMatFn m n) :
    sylvesterResidualRect m n A B C Yhat =
    fun i j => C i j - matMulRect m m n A Yhat i j +
      matMulRect m n n Yhat B i j := by
  ext i j
  unfold sylvesterResidualRect sylvesterOpRect
  ring

/-- Higham, 2nd ed., Chapter 16, equation (16.9):
    source-numbered alias for the expanded rectangular residual. -/
alias H16_eq16_9_sylvesterResidualRect_eq := sylvesterResidualRect_eq

-- ============================================================
-- Vec/Kronecker formulation from Chapter 16.1
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    the product-index coefficient matrix
    `I_n kron A - B^T kron I_m` for vectorized rectangular Sylvester systems.
    The product index follows Mathlib's column-stacking `Matrix.vec` convention:
    `(j,i)` denotes entry `(i,j)`. -/
noncomputable def sylvesterVecCoeff (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) Real) A -
    Matrix.kronecker (Matrix.transpose B) (1 : Matrix (Fin m) (Fin m) Real)

/-- Higham, 2nd ed., Chapter 16.1, prose following equation (16.2):
    `vec(A X B) = (B^T kron A) vec(X)` for finite matrices. -/
theorem vec_triple_product_rect (m k n p : Nat)
    (A : Matrix (Fin m) (Fin k) Real)
    (X : Matrix (Fin k) (Fin n) Real)
    (B : Matrix (Fin n) (Fin p) Real) :
    Matrix.vec (A * X * B) =
      Matrix.mulVec (Matrix.kronecker (Matrix.transpose B) A) (Matrix.vec X) := by
  simpa [Matrix.kronecker] using
    (Matrix.kronecker_mulVec_vec A X (Matrix.transpose B)).symm

/-- Left multiplication by `A` in vectorized form, the `I_n kron A` half of
    equation (16.2). -/
theorem vec_left_mul_rect (m k n : Nat)
    (A : Matrix (Fin m) (Fin k) Real)
    (X : Matrix (Fin k) (Fin n) Real) :
    Matrix.vec (A * X) =
      Matrix.mulVec
        (Matrix.kronecker (1 : Matrix (Fin n) (Fin n) Real) A)
        (Matrix.vec X) := by
  simpa [Matrix.kronecker] using Matrix.vec_mul_eq_mulVec A X

/-- Right multiplication by `B` in vectorized form, the `B^T kron I_m` half of
    equation (16.2). -/
theorem vec_right_mul_rect (m n p : Nat)
    (X : Matrix (Fin m) (Fin n) Real)
    (B : Matrix (Fin n) (Fin p) Real) :
    Matrix.vec (X * B) =
      Matrix.mulVec
        (Matrix.kronecker (Matrix.transpose B)
          (1 : Matrix (Fin m) (Fin m) Real))
        (Matrix.vec X) := by
  simpa [Matrix.kronecker] using
    (Matrix.kronecker_mulVec_vec (1 : Matrix (Fin m) (Fin m) Real)
      X (Matrix.transpose B)).symm

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered alias
    for the rectangular `vec(A * X * B)` Kronecker identity. -/
alias H16_eq16_2_vec_triple_product_rect := vec_triple_product_rect

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered alias
    for the left-multiplication half of the rectangular vec/Kronecker system. -/
alias H16_eq16_2_vec_left_mul_rect := vec_left_mul_rect

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered alias
    for the right-multiplication half of the rectangular vec/Kronecker system. -/
alias H16_eq16_2_vec_right_mul_rect := vec_right_mul_rect

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    the product-index Lyapunov coefficient `I_n kron A + A kron I_n`
    for vectorized Lyapunov systems `A X + X A^T = C`. -/
noncomputable def lyapunovVecCoeff (n : Nat)
    (A : Matrix (Fin n) (Fin n) Real) :
    Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real :=
  Matrix.kronecker (1 : Matrix (Fin n) (Fin n) Real) A +
    Matrix.kronecker A (1 : Matrix (Fin n) (Fin n) Real)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    applying `I_n kron A + A kron I_n` to `vec(X)` gives
    `vec(A X + X A^T)`. -/
theorem lyapunovVecCoeff_mulVec_vec (n : Nat)
    (A X : Matrix (Fin n) (Fin n) Real) :
    Matrix.mulVec (lyapunovVecCoeff n A) (Matrix.vec X) =
      Matrix.vec (A * X + X * Matrix.transpose A) := by
  ext p
  have hleft := congrFun (vec_left_mul_rect n n n A X) p
  have hright := congrFun (vec_right_mul_rect n n n X (Matrix.transpose A)) p
  have hright' :
      (X * Matrix.transpose A).vec p =
        (Matrix.kronecker A (1 : Matrix (Fin n) (Fin n) Real)).mulVec X.vec p := by
    simpa using hright
  simp only [lyapunovVecCoeff, Matrix.add_mulVec, Pi.add_apply]
  rw [← hleft, ← hright']
  simp [Matrix.vec]

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    vectorized first-order Lyapunov perturbation equation.  The coefficient
    `I_n kron A + A kron I_n` sends `vec(dX)` to the vectorized linearized
    right-hand side `dC - dA X - X dA^T`. -/
theorem lyapunov_perturbation_first_order_vec (n : Nat)
    (A X dA dC dX : Fin n -> Fin n -> Real)
    (hLin : forall i j, lyapunovOp n A dX i j =
      dC i j - matMul n dA X i j - matMul n X (matTranspose dA) i j) :
    Matrix.mulVec (lyapunovVecCoeff n A) (Matrix.vec dX) =
      Matrix.vec (fun i j =>
        dC i j - matMul n dA X i j - matMul n X (matTranspose dA) i j) := by
  rw [lyapunovVecCoeff_mulVec_vec]
  ext p
  simpa [lyapunovOp, matMul, matTranspose, Matrix.vec, Matrix.mul_apply]
    using hLin p.2 p.1

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    the vec-permutation matrix `Pi` in product-index form.  It swaps the
    column-stacking product index `(j,i)` to `(i,j)`. -/
noncomputable def vecTransposePermutation (n : Nat) :
    Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real :=
  fun p q => if q = (p.2, p.1) then 1 else 0

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    defining property of the vec-permutation matrix, `vec(A^T) = Pi vec(A)`. -/
theorem vecTransposePermutation_mulVec_vec (n : Nat)
    (A : Matrix (Fin n) (Fin n) Real) :
    Matrix.mulVec (vecTransposePermutation n) (Matrix.vec A) =
      Matrix.vec (Matrix.transpose A) := by
  ext p
  simp [vecTransposePermutation, Matrix.mulVec, dotProduct, Matrix.vec]

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the Lyapunov vec/Kronecker coefficient identity. -/
alias H16_eq16_27_lyapunovVecCoeff_mulVec_vec :=
  lyapunovVecCoeff_mulVec_vec

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the vectorized first-order Lyapunov perturbation
    equation. -/
alias H16_eq16_27_lyapunov_perturbation_first_order_vec :=
  lyapunov_perturbation_first_order_vec

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the vec-transpose permutation identity. -/
alias H16_eq16_27_vecTransposePermutation_mulVec_vec :=
  vecTransposePermutation_mulVec_vec

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    applying `I_n kron A - B^T kron I_m` to `vec(X)` gives
    `vec(AX - XB)`. -/
theorem sylvesterVecCoeff_mulVec_vec (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (X : RMatFn m n) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) =
      Matrix.vec (sylvesterOpRect m n A B X) := by
  ext p
  have hleft := congrFun (vec_left_mul_rect m m n A X) p
  have hright := congrFun (vec_right_mul_rect m n n X B) p
  unfold sylvesterVecCoeff
  simp only [Pi.sub_apply, Matrix.sub_mulVec, hleft.symm, hright.symm]
  simp [sylvesterOpRect, matMulRect, Matrix.vec, Matrix.mul_apply]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2):
    the vectorized linear system is equivalent to the rectangular Sylvester
    equation. -/
theorem sylvester_vec_system_iff_solution (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X : RMatFn m n) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = Matrix.vec C <->
      IsSylvesterSolutionRect m n A B C X := by
  constructor
  case mp =>
    intro h i j
    have hp := congrFun h (j, i)
    rw [sylvesterVecCoeff_mulVec_vec] at hp
    exact hp
  case mpr =>
    intro h
    rw [sylvesterVecCoeff_mulVec_vec]
    ext p
    exact h p.2 p.1

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered alias
    for applying the rectangular Sylvester vec/Kronecker coefficient to
    `vec(X)`. -/
alias H16_eq16_2_sylvesterVecCoeff_mulVec_vec := sylvesterVecCoeff_mulVec_vec

/-- Higham, 2nd ed., Chapter 16.1, equation (16.2): source-numbered alias
    for equivalence between the rectangular vec/Kronecker linear system and
    the Sylvester equation. -/
alias H16_eq16_2_sylvester_vec_system_iff_solution := sylvester_vec_system_iff_solution

/-- Higham, 2nd ed., Chapter 16, equation (16.22):
    vectorized/Kronecker form of the full perturbation identity, including the
    second-order terms. -/
theorem sylvester_perturbation_equation_vec (n : Nat)
    (A B C X dA dB dC dX : Fin n -> Fin n -> Real)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hPerturbed : forall i j, sylvesterOp n
      (fun i' j' => A i' j' + dA i' j')
      (fun i' j' => B i' j' + dB i' j')
      (fun i' j' => X i' j' + dX i' j') i j = C i j + dC i j) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) (Matrix.vec dX) =
      Matrix.vec (fun i j =>
        dC i j - matMul n dA X i j + matMul n X dB i j -
          matMul n dA dX i j + matMul n dX dB i j) := by
  rw [sylvesterVecCoeff_mulVec_vec]
  ext p
  simpa [sylvesterOpRect] using
    sylvester_perturbation_equation n A B C X dA dB dC dX
      hExact hPerturbed p.2 p.1

/-- Higham, 2nd ed., Chapter 16, equation (16.22), first-order form:
    after dropping second-order perturbation products, the vec/Kronecker
    coefficient sends `vec(dX)` to the vectorized first-order right-hand side. -/
theorem sylvester_perturbation_first_order_vec (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) (Matrix.vec dX) =
      Matrix.vec (fun i j =>
        dC i j - matMul n dA X i j + matMul n X dB i j) := by
  rw [sylvesterVecCoeff_mulVec_vec]
  ext p
  simpa [sylvesterOpRect] using
    sylvester_perturbation_first_order n A B X dA dB dC dX hLin p.2 p.1

/-- Higham, 2nd ed., Chapter 16.4, equation (16.22):
    source-numbered alias for the vectorized full perturbation identity. -/
alias H16_eq16_22_sylvester_perturbation_equation_vec :=
  sylvester_perturbation_equation_vec

/-- Higham, 2nd ed., Chapter 16.4, equation (16.22):
    source-numbered alias for the vectorized first-order perturbation
    identity. -/
alias H16_eq16_22_sylvester_perturbation_first_order_vec :=
  sylvester_perturbation_first_order_vec

-- ============================================================
-- Practical max-entry error bounds from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the vector max norm on a vectorized rectangular matrix, using Mathlib's
    finite-function sup norm. -/
noncomputable def sylvesterVecMaxNorm (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) : Real :=
  norm v

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    `||X|| := max_{i,j} |x_ij|`, represented as the vector max norm of
    `vec(X)` in column-stacking order. -/
noncomputable def sylvesterMaxEntryNormRect (m n : Nat)
    (X : RMatFn m n) : Real :=
  sylvesterVecMaxNorm m n (Matrix.vec X)

lemma sylvesterVecMaxNorm_nonneg (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) :
    0 <= sylvesterVecMaxNorm m n v := by
  unfold sylvesterVecMaxNorm
  exact norm_nonneg v

lemma abs_le_sylvesterVecMaxNorm (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) (p : Prod (Fin n) (Fin m)) :
    |v p| <= sylvesterVecMaxNorm m n v := by
  unfold sylvesterVecMaxNorm
  simpa [Real.norm_eq_abs] using norm_le_pi_norm v p

lemma sylvesterVecMaxNorm_le_of_abs_le (m n : Nat)
    (v : Prod (Fin n) (Fin m) -> Real) {c : Real}
    (h : forall p : Prod (Fin n) (Fin m), |v p| <= c) (hc : 0 <= c) :
    sylvesterVecMaxNorm m n v <= c := by
  unfold sylvesterVecMaxNorm
  rw [pi_norm_le_iff_of_nonneg hc]
  intro p
  simpa [Real.norm_eq_abs] using h p

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the practical componentwise budget vector
    `|P^{-1}| (|vec(Rhat)| + vec(Ru))`.  The matrix `PinvAbs` represents
    an entrywise nonnegative upper bound for `|P^{-1}|`, and `Ru` is the
    nonnegative residual-rounding budget. -/
noncomputable def sylvesterPracticalBudgetVec (m n : Nat)
    (PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Ru : RMatFn m n) : Prod (Fin n) (Fin m) -> Real :=
  fun p =>
    Finset.sum Finset.univ fun q : Prod (Fin n) (Fin m) =>
      PinvAbs p q * (|Matrix.vec Rhat q| + Matrix.vec Ru q)

lemma sylvesterPracticalBudgetVec_nonneg (m n : Nat)
    (PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Ru : RMatFn m n)
    (hPinvAbs : forall p q, 0 <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j) :
    forall p, 0 <= sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p := by
  intro p
  unfold sylvesterPracticalBudgetVec
  exact Finset.sum_nonneg fun q _ =>
    mul_nonneg (hPinvAbs p q)
      (add_nonneg (abs_nonneg _)
        (by simpa [Matrix.vec] using hRu q.2 q.1))

/-- If one nonnegative vector budget dominates another componentwise, it also
    dominates it in the source max-entry norm used in equation (16.29). -/
lemma sylvesterVecMaxNorm_mono_of_nonneg (m n : Nat)
    {v w : Prod (Fin n) (Fin m) -> Real}
    (hv : forall p, 0 <= v p)
    (hle : forall p, v p <= w p) :
    sylvesterVecMaxNorm m n v <= sylvesterVecMaxNorm m n w := by
  unfold sylvesterVecMaxNorm
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg w)]
  intro p
  calc
    |v p| = v p := abs_of_nonneg (hv p)
    _ <= w p := hle p
    _ <= |w p| := le_abs_self (w p)
    _ <= norm w := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm w p

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the practical budget is monotone in the inverse-entry bound, the
    absolute computed residual, and the residual-rounding budget.  This lets
    later estimator paths replace exact budgets by proved upper estimates. -/
lemma sylvesterPracticalBudgetVec_mono (m n : Nat)
    (PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Rhat' Ru Ru' : RMatFn m n)
    (hPinvAbs' : forall p q, 0 <= PinvAbs' p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu : forall i j, 0 <= Ru i j)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    forall p,
      sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <=
        sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p := by
  intro p
  unfold sylvesterPracticalBudgetVec
  apply Finset.sum_le_sum
  intro q _
  have hterm :
      |Matrix.vec Rhat q| + Matrix.vec Ru q <=
        |Matrix.vec Rhat' q| + Matrix.vec Ru' q := by
    simpa [Matrix.vec] using
      add_le_add (hRhat q.2 q.1) (hRu_le q.2 q.1)
  have hterm_nonneg :
      0 <= |Matrix.vec Rhat q| + Matrix.vec Ru q := by
    exact add_nonneg (abs_nonneg _)
      (by simpa [Matrix.vec] using hRu q.2 q.1)
  exact mul_le_mul (hPinvAbs_le p q) hterm hterm_nonneg (hPinvAbs' p q)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    max-norm form of monotonicity for the practical budget vector. -/
lemma sylvesterPracticalBudgetVec_maxNorm_mono (m n : Nat)
    (PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Rhat' Ru Ru' : RMatFn m n)
    (hPinvAbs : forall p q, 0 <= PinvAbs p q)
    (hPinvAbs' : forall p q, 0 <= PinvAbs' p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu : forall i j, 0 <= Ru i j)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  apply sylvesterVecMaxNorm_mono_of_nonneg
  · exact sylvesterPracticalBudgetVec_nonneg m n PinvAbs Rhat Ru hPinvAbs hRu
  · exact sylvesterPracticalBudgetVec_mono m n
      PinvAbs PinvAbs' Rhat Rhat' Ru Ru' hPinvAbs' hPinvAbs_le
      hRhat hRu hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    scalar cap form of the practical budget vector.  If every component of
    the practical `|P^{-1}| (|vec(Rhat)| + vec(Ru))` budget is bounded by
    `eta`, then its source max-entry norm is bounded by `eta`. -/
lemma sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le (m n : Nat)
    (PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (Rhat Ru : RMatFn m n) {eta : Real}
    (hPinvAbs : forall p q, 0 <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <= eta := by
  apply sylvesterVecMaxNorm_le_of_abs_le
  · intro p
    rw [abs_of_nonneg
      (sylvesterPracticalBudgetVec_nonneg m n PinvAbs Rhat Ru
        hPinvAbs hRu p)]
    exact hcomponent p
  · exact heta

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    the entrywise absolute-value matrix `|P^{-1}|` for the vec/Kronecker
    Sylvester coefficient `P = I_n kron A - B^T kron I_m`.  The inverse is
    Mathlib's nonsingular matrix inverse; source-facing theorems using this
    definition separately prove the required left-inverse hypothesis. -/
noncomputable def sylvesterVecCoeffNonsingInvAbs (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real :=
  fun p q => |((sylvesterVecCoeff m n A B)⁻¹) p q|

/-- The absolute-value matrix `sylvesterVecCoeffNonsingInvAbs` bounds the
    nonsingular inverse entries componentwise, exactly as required by the
    practical error-budget theorem. -/
lemma sylvesterVecCoeffNonsingInv_abs_le_invAbs (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) :
    forall p q,
      |((sylvesterVecCoeff m n A B)⁻¹) p q| <=
        sylvesterVecCoeffNonsingInvAbs m n A B p q := by
  intro p q
  rfl

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute max-entry
    bridge: a nonnegative componentwise budget for `X - Xhat` bounds the
    practical max-entry forward error before any relative normalization. -/
theorem sylvester_practical_abs_error_bound_of_componentwise_budget (m n : Nat)
    (X Xhat : RMatFn m n) (budget : Prod (Fin n) (Fin m) -> Real)
    (hbudget : forall p, 0 <= budget p)
    (hcert : forall i j, |X i j - Xhat i j| <= budget (j, i)) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n budget := by
  unfold sylvesterMaxEntryNormRect
  apply sylvesterVecMaxNorm_le_of_abs_le
  · intro p
    calc
      |Matrix.vec (fun i j => X i j - Xhat i j) p|
          = |X p.2 p.1 - Xhat p.2 p.1| := by
            simp [Matrix.vec]
      _ <= budget p := hcert p.2 p.1
      _ = |budget p| := (abs_of_nonneg (hbudget p)).symm
      _ <= sylvesterVecMaxNorm m n budget :=
        abs_le_sylvesterVecMaxNorm m n budget p
  · exact sylvesterVecMaxNorm_nonneg m n budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), max-entry norm bridge:
    a nonnegative componentwise budget for `X - Xhat` bounds the relative
    max-entry forward error in the source norm `||X|| := max_{i,j} |x_ij|`. -/
theorem sylvester_practical_error_bound_of_componentwise_budget (m n : Nat)
    (X Xhat : RMatFn m n) (budget : Prod (Fin n) (Fin m) -> Real)
    (hbudget : forall p, 0 <= budget p)
    (hcert : forall i j, |X i j - Xhat i j| <= budget (j, i))
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n budget / sylvesterMaxEntryNormRect m n Xhat := by
  have hnorm :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n budget := by
    exact
      sylvester_practical_abs_error_bound_of_componentwise_budget m n
        X Xhat budget hbudget hcert
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hXhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute certificate
    form: if the vectorized error is `P^{-1} r`, the inverse entries are bounded
    componentwise by `PinvAbs`, and the residual vector satisfies
    `|r| <= |vec(Rhat)| + vec(Ru)`, then the practical budget bounds the
    unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_inverse_residual_budget (m n : Nat)
    (X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (r : Prod (Fin n) (Fin m) -> Real)
    (hErr : Matrix.vec (fun i j => X i j - Xhat i j) =
      Matrix.mulVec Pinv r)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hr : forall q, |r q| <= |Matrix.vec Rhat q| + Matrix.vec Ru q) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  apply sylvester_practical_abs_error_bound_of_componentwise_budget
  · exact sylvesterPracticalBudgetVec_nonneg m n PinvAbs Rhat Ru hPinvAbs_nonneg hRu
  · intro i j
    let p : Prod (Fin n) (Fin m) := (j, i)
    have hp := congrFun hErr p
    have herr :
        X i j - Xhat i j = Matrix.mulVec Pinv r p := by
      simpa [p, Matrix.vec] using hp
    rw [herr]
    calc
      |Matrix.mulVec Pinv r p|
          = |Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) => Pinv p q * r q)| := by
            simp [Matrix.mulVec, dotProduct]
      _ <= Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) => |Pinv p q * r q|) :=
            Finset.abs_sum_le_sum_abs _ _
      _ = Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) => |Pinv p q| * |r q|) := by
            apply Finset.sum_congr rfl
            intro q _
            rw [abs_mul]
      _ <= Finset.sum Finset.univ
              (fun q : Prod (Fin n) (Fin m) =>
                PinvAbs p q * (|Matrix.vec Rhat q| + Matrix.vec Ru q)) := by
            apply Finset.sum_le_sum
            intro q _
            exact mul_le_mul (hPinvAbs p q) (hr q)
              (abs_nonneg (r q)) (hPinvAbs_nonneg p q)
      _ = sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p := by
            rfl

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), certificate form:
    if the vectorized error is `P^{-1} r`, the inverse entries are bounded
    componentwise by `PinvAbs`, and the residual vector satisfies
    `|r| <= |vec(Rhat)| + vec(Ru)`, then the practical `|P^{-1}|` budget
    gives the relative max-entry forward-error bound. -/
theorem sylvester_practical_error_bound_of_inverse_residual_budget (m n : Nat)
    (X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (r : Prod (Fin n) (Fin m) -> Real)
    (hErr : Matrix.vec (fun i j => X i j - Xhat i j) =
      Matrix.mulVec Pinv r)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hr : forall q, |r q| <= |Matrix.vec Rhat q| + Matrix.vec Ru q)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hnorm :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) :=
    sylvester_practical_abs_error_bound_of_inverse_residual_budget m n
      X Xhat Rhat Ru Pinv PinvAbs r hErr hPinvAbs hRu hr
  exact div_le_div_of_nonneg_right hnorm (le_of_lt hXhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact residual identity:
    if `X` solves the Sylvester equation, then the exact residual of `Xhat`
    is the Sylvester operator applied to the forward error `X - Xhat`. -/
theorem sylvesterResidualRect_eq_sylvesterOpRect_error (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (hX : IsSylvesterSolutionRect m n A B C X) :
    sylvesterResidualRect m n A B C Xhat =
      sylvesterOpRect m n A B (fun i j => X i j - Xhat i j) := by
  ext i j
  have h := hX i j
  unfold sylvesterResidualRect sylvesterOpRect matMulRect at h ⊢
  rw [← h]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the exact residual/error identity underlying the
    practical componentwise bound. -/
alias H16_eq16_29_sylvesterResidualRect_eq_sylvesterOpRect_error :=
  sylvesterResidualRect_eq_sylvesterOpRect_error

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), inverse-residual bridge:
    if `Pinv` is a left inverse for the vec/Kronecker Sylvester coefficient,
    then the vectorized forward error is `Pinv` applied to the exact residual. -/
theorem sylvester_vec_error_eq_inverse_residual_of_left_inverse (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat : RMatFn m n)
    (Pinv :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1) :
    Matrix.vec (fun i j => X i j - Xhat i j) =
      Matrix.mulVec Pinv (Matrix.vec (sylvesterResidualRect m n A B C Xhat)) := by
  let P := sylvesterVecCoeff m n A B
  let E : RMatFn m n := fun i j => X i j - Xhat i j
  change Matrix.vec E =
    Matrix.mulVec Pinv (Matrix.vec (sylvesterResidualRect m n A B C Xhat))
  have hLeftP : Pinv * P = 1 := by
    simpa [P] using hLeft
  have hres : Matrix.mulVec P (Matrix.vec E) =
      Matrix.vec (sylvesterResidualRect m n A B C Xhat) := by
    rw [show P = sylvesterVecCoeff m n A B by rfl]
    rw [sylvesterVecCoeff_mulVec_vec]
    rw [sylvesterResidualRect_eq_sylvesterOpRect_error m n A B C X Xhat hX]
  calc
    Matrix.vec E =
        Matrix.mulVec (1 :
          Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
          (Matrix.vec E) := by
            simp
    _ = Matrix.mulVec (Pinv * P) (Matrix.vec E) := by
          rw [hLeftP]
    _ = Matrix.mulVec Pinv (Matrix.mulVec P (Matrix.vec E)) := by
          rw [Matrix.mulVec_mulVec]
    _ = Matrix.mulVec Pinv (Matrix.vec (sylvesterResidualRect m n A B C Xhat)) := by
          rw [hres]

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for the left-inverse residual-to-error bridge. -/
alias H16_eq16_29_sylvester_vec_error_eq_inverse_residual_of_left_inverse :=
  sylvester_vec_error_eq_inverse_residual_of_left_inverse

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    if a computed residual `Rhat` differs from the exact residual `R` by
    the nonnegative componentwise budget `Ru`, then
    `|vec(R)| <= |vec(Rhat)| + vec(Ru)`. -/
theorem sylvester_exact_residual_vec_abs_le_computed_residual_budget (m n : Nat)
    (R Rhat Ru : RMatFn m n)
    (hRhat : forall i j, |R i j - Rhat i j| <= Ru i j) :
    forall q : Prod (Fin n) (Fin m),
      |Matrix.vec R q| <= |Matrix.vec Rhat q| + Matrix.vec Ru q := by
  intro q
  calc
    |Matrix.vec R q| = |R q.2 q.1| := by
        simp [Matrix.vec]
    _ = |Rhat q.2 q.1 + (R q.2 q.1 - Rhat q.2 q.1)| := by
        congr 1
        ring
    _ <= |Rhat q.2 q.1| + |R q.2 q.1 - Rhat q.2 q.1| :=
        abs_add_le _ _
    _ <= |Rhat q.2 q.1| + Ru q.2 q.1 := by
        exact add_le_add (le_refl |Rhat q.2 q.1|) (hRhat q.2 q.1)
    _ = |Matrix.vec Rhat q| + Matrix.vec Ru q := by
        simp [Matrix.vec]

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), computed-residual
    budget certificate: `Rhat` approximates the exact residual with
    nonnegative componentwise error budget `Ru`. -/
def IsSylvesterComputedResidualBudget (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat Rhat Ru : RMatFn m n) :
    Prop :=
  (forall i j, 0 <= Ru i j) /\
    forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    an explicit residual error matrix `dR` with
    `Rhat = R(Xhat) + dR` and `|dR| <= Ru` yields the computed-residual
    budget certificate used by the practical bound. -/
theorem sylvesterComputedResidualBudget_of_error_model (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat Rhat Ru dR : RMatFn m n)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j) :
    IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru := by
  constructor
  · exact hRu
  · intro i j
    rw [hRhat i j]
    have hsub :
        sylvesterResidualRect m n A B C Xhat i j -
            (sylvesterResidualRect m n A B C Xhat i j + dR i j) =
          -dR i j := by
      ring
    rw [hsub, abs_neg]
    exact hdR i j

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for deriving a computed-residual budget from an
    explicit residual error model. -/
alias H16_eq16_29_sylvesterComputedResidualBudget_of_error_model :=
  sylvesterComputedResidualBudget_of_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    a Frobenius residual-arithmetic certificate `||dR||_F <= rho` supplies
    the componentwise computed-residual budget with the uniform budget
    `Ru i j = rho`. -/
theorem sylvesterComputedResidualBudget_of_frobenius_error_model (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C Xhat Rhat dR : RMatFn m n)
    (rho : Real)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho) :
    IsSylvesterComputedResidualBudget m n A B C Xhat Rhat (fun _ _ => rho) := by
  exact
    sylvesterComputedResidualBudget_of_error_model m n
      A B C Xhat Rhat (fun _ _ => rho) dR hRhat
      (fun _ _ => hrho)
      (fun i j => (abs_entry_le_frobNorm dR i j).trans hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    source-numbered alias for turning a Frobenius residual-error certificate
    into a uniform computed-residual budget. -/
alias H16_eq16_29_sylvesterComputedResidualBudget_of_frobenius_error_model :=
  sylvesterComputedResidualBudget_of_frobenius_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), computed-residual
    certificate form: a left inverse for the vec/Kronecker coefficient,
    an entrywise inverse bound, and a computed-residual budget instantiate
    the practical relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_inverse_residual_budget m n
      X Xhat Rhat Ru Pinv PinvAbs
      (Matrix.vec (sylvesterResidualRect m n A B C Xhat))
      (sylvester_vec_error_eq_inverse_residual_of_left_inverse
        m n A B C X Xhat Pinv hX hLeft)
      hPinvAbs hRu
      (sylvester_exact_residual_vec_abs_le_computed_residual_budget
        m n (sylvesterResidualRect m n A B C Xhat) Rhat Ru hRhat)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), certificate-packaged
    form of the practical componentwise error bound. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_budget m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      hBudget.1 hBudget.2 hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute
    computed-residual certificate endpoint: the same practical budget bounds
    the unnormalized max-entry forward error, so no positive `||Xhat||`
    denominator assumption is needed. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_inverse_residual_budget m n
      X Xhat Rhat Ru Pinv PinvAbs
      (Matrix.vec (sylvesterResidualRect m n A B C Xhat))
      (sylvester_vec_error_eq_inverse_residual_of_left_inverse
        m n A B C X Xhat Pinv hX hLeft)
      hPinvAbs hBudget.1
      (sylvester_exact_residual_vec_abs_le_computed_residual_budget
        m n (sylvesterResidualRect m n A B C Xhat) Rhat Ru hBudget.2)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute scalar
    computed-residual certificate endpoint: a scalar cap on every practical
    budget component bounds the unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  have hbase :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) :=
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs Rhat Ru hPinvAbs_nonneg hBudget.1 heta hcomponent
  exact le_trans hbase hnorm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint: the residual budget hypotheses directly
    bound the unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      (And.intro hRu hRhat)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint with a scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      (And.intro hRu hRhat) heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint: an explicit residual perturbation model
    supplies the practical budget without requiring a positive denominator. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint with a scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute Frobenius
    residual-arithmetic endpoint: a Frobenius residual perturbation certificate
    supplies the componentwise residual budget with uniform radius `rho`,
    giving an unnormalized max-entry forward-error bound. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_frobenius_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat dR : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_frobenius_error_model m n
        A B C Xhat Rhat dR rho hRhat hrho hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute Frobenius
    residual-arithmetic endpoint with a scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_frobenius_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat dR : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs Rhat (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat (fun _ _ => rho) Pinv PinvAbs eta
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_frobenius_error_model m n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute
    estimator-ready form: once the exact practical certificate has been proved,
    any componentwise larger inverse/residual budget also gives a valid
    unnormalized max-entry forward-error bound. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  have hbase :=
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') :=
    sylvesterPracticalBudgetVec_maxNorm_mono m n
      PinvAbs PinvAbs' Rhat Rhat' Ru Ru'
      hPinvAbs_nonneg hPinvAbs'_nonneg hPinvAbs_le hRhat hBudget.1 hRu_le
  exact hbase.trans hnorm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute monotone
    scalar endpoint: after replacing the inverse and residual budgets by
    componentwise larger estimates, a scalar cap on the estimated practical
    budget bounds the unnormalized max-entry forward error. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  have hbase :
      sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') :=
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hBudget hRhat hRu_le
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hRu'_nonneg : forall i j, 0 <= Ru' i j := by
    intro i j
    exact (hBudget.1 i j).trans (hRu_le i j)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs' Rhat' Ru' hPinvAbs'_nonneg hRu'_nonneg heta hcomponent
  exact le_trans hbase hnorm

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint with monotone supplied inverse and
    residual estimates. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le (And.intro hRu hRhat)
      hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute raw
    computed-residual budget endpoint with monotone supplied estimates and a
    scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_budget_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le (And.intro hRu hRhat)
      hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint with monotone supplied inverse and residual
    estimates. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), absolute explicit
    residual error-model endpoint with monotone supplied estimates and a
    scalar practical-budget cap. -/
theorem sylvester_practical_abs_error_bound_of_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29):
    practical residual bound from a Frobenius residual-arithmetic model.
    The bound `||dR||_F <= rho` derives the raw componentwise residual-budget
    hypothesis with `Ru i j = rho`, then feeds the existing practical
    computed-residual certificate endpoint. -/
theorem sylvester_practical_error_bound_of_computed_residual_frobenius_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat dR : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_frobenius_error_model m n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), estimator-ready form:
    once the exact practical certificate has been proved, any componentwise
    larger inverse/residual budget also gives a valid relative max-entry error
    bound.  This is a monotone wrapper for later LAPACK-style estimator
    instantiations; it does not prove the estimator itself. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget hXhat
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <=
        sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') :=
    sylvesterPracticalBudgetVec_maxNorm_mono m n
      PinvAbs PinvAbs' Rhat Rhat' Ru Ru'
      hPinvAbs_nonneg hPinvAbs'_nonneg hPinvAbs_le hRhat hBudget.1 hRu_le
  exact hbase.trans
    (div_le_div_of_nonneg_right hnorm (le_of_lt hXhat))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), scalar estimator-ready
    form: a scalar cap on every practical-budget component gives the same
    relative max-entry forward-error bound with right-hand side
    `eta / ||Xhat||`. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget hXhat
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs Rhat Ru hPinvAbs_nonneg hBudget.1 heta hcomponent
  exact hbase.trans
    (div_le_div_of_nonneg_right hnorm (le_of_lt hXhat))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), monotone scalar
    estimator-ready form: after replacing the inverse and residual budgets by
    componentwise larger estimated quantities, a scalar cap on the estimated
    practical budget gives the final relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  have hbase :=
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hBudget hRhat hRu_le hXhat
  have hPinvAbs_nonneg : forall p q, 0 <= PinvAbs p q := by
    intro p q
    exact (abs_nonneg (Pinv p q)).trans (hPinvAbs p q)
  have hPinvAbs'_nonneg : forall p q, 0 <= PinvAbs' p q := by
    intro p q
    exact (hPinvAbs_nonneg p q).trans (hPinvAbs_le p q)
  have hRu'_nonneg : forall i j, 0 <= Ru' i j := by
    intro i j
    exact (hBudget.1 i j).trans (hRu_le i j)
  have hnorm :
      sylvesterVecMaxNorm m n
          (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') <= eta :=
    sylvesterPracticalBudgetVec_maxNorm_le_of_componentwise_le m n
      PinvAbs' Rhat' Ru' hPinvAbs'_nonneg hRu'_nonneg heta hcomponent
  exact hbase.trans
    (div_le_div_of_nonneg_right hnorm (le_of_lt hXhat))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), raw computed-residual
    budget form with monotone supplied inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le ⟨hRu, hRhat⟩
      hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), raw computed-residual
    budget form with a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      ⟨hRu, hRhat⟩ heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), raw computed-residual
    budget form with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_computed_residual_budget_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le ⟨hRu, hRhat⟩
      hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form of the practical componentwise error bound.  An explicit
    residual perturbation `dR` with `Rhat = R(Xhat) + dR` and `|dR| <= Ru`
    supplies the computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form with monotone supplied inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form with a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), explicit residual
    error-model form with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the generic computed-residual certificate endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_certificate
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar computed-residual certificate endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_certificate_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone computed-residual certificate endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_certificate_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar computed-residual certificate endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the generic raw computed-residual budget endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_budget
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_budget m n
      A B C X Xhat Rhat Ru Pinv PinvAbs hX hLeft hPinvAbs hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar raw computed-residual budget endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_budget_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_scalar m n
      A B C X Xhat Rhat Ru Pinv PinvAbs eta hX hLeft hPinvAbs
      hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone raw computed-residual budget endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_budget_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hRu hRhat hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar raw computed-residual budget endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_budget_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_budget_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le hRu hRhat hRhat_le hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the generic explicit residual-error model endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_error_model
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model m n
      A B C X Xhat Rhat Ru dR Pinv PinvAbs hX hLeft hPinvAbs
      hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the scalar explicit residual-error model endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_error_model_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model_scalar m n
      A B C X Xhat Rhat Ru dR Pinv PinvAbs eta hX hLeft hPinvAbs
      hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone explicit residual-error model endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_error_model_mono
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model_mono m n
      A B C X Xhat Rhat Rhat' Ru Ru' dR Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le hRhat hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the monotone scalar explicit residual-error model endpoint. -/
theorem H16_eq16_29_sylvester_practical_error_bound_of_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model_mono_scalar m n
      A B C X Xhat Rhat Rhat' Ru Ru' dR Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le hRhat hRu hdR hRhat_le hRu_le
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    endpoint: nonsingularity of the rectangular vec/Kronecker Sylvester
    coefficient supplies the actual inverse and its absolute-value budget for
    the practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    absolute endpoint: the determinant certificate supplies the actual inverse
    budget, giving an unnormalized practical error bound. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    raw computed-residual budget endpoint. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect
      m n A B C X Xhat Rhat Ru hdet hX (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), rectangular determinant
    explicit residual-error-model endpoint. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_rect
    (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hdet : Matrix.det (sylvesterVecCoeff m n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model m n
      A B C X Xhat Rhat Ru dR
      (Inv.inv (sylvesterVecCoeff m n A B))
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    endpoint: nonsingularity of the vec/Kronecker Sylvester coefficient
    supplies the actual inverse and its absolute-value budget for the exact
    computed-residual certificate.  This is a practical residual certificate,
    not an automatic estimator or rounded Schur-solve theorem. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute endpoint: nonsingularity of the vec/Kronecker coefficient supplies
    the actual inverse budget, giving an unnormalized practical error bound
    without a positive `||Xhat||` assumption. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute scalar endpoint: nonsingularity of the vec/Kronecker coefficient
    supplies the actual inverse budget, and a scalar cap on that budget bounds
    the unnormalized max-entry error. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute monotone endpoint: after determinant nonsingularity supplies the
    exact inverse budget, componentwise larger inverse and residual estimates
    preserve the unnormalized practical error bound. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute raw-budget monotone endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hdet hX (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute raw-budget monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hdet hX (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute explicit-error-model monotone endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model n n A B C Xhat Rhat Ru dR
        hRhat_eq hRu hdR)
      hPinvAbs_le hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute explicit-error-model monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hdet hX
      (sylvesterComputedResidualBudget_of_error_model n n A B C Xhat Rhat Ru dR
        hRhat_eq hRu hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    scalar endpoint: the nonsingular vec/Kronecker coefficient supplies the
    exact inverse budget, and a scalar cap on that practical budget gives the
    relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar n n
      A B C X Xhat Rhat Ru
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    monotone endpoint: after the determinant proof supplies the exact inverse
    budget, componentwise larger inverse and residual inputs preserve the
    practical computed-residual bound.  This is estimator-ready infrastructure,
    not a proof of any particular estimator. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    monotone scalar endpoint: a scalar cap on a componentwise larger practical
    budget gives the same relative max-entry error bound after nonsingularity
    supplies the exact inverse certificate. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar n n
      A B C X Xhat Rhat Rhat' Ru Ru'
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint: a determinant-nonzero vec/Kronecker
    coefficient supplies the nonsingular inverse, while the caller supplies a
    direct absolute residual budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru hdet hX (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint with monotone supplied inverse and
    residual estimates.  The determinant certificate still provides the exact
    inverse; the primed inputs are any componentwise larger practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hdet hX (And.intro hRu hRhat_budget)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint with a scalar cap on the practical
    budget induced by the nonsingular vec/Kronecker inverse. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta hdet hX
      (And.intro hRu hRhat) heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    raw computed-residual budget endpoint with monotone supplied estimates and
    a scalar cap on the enlarged practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hdet hX
      (And.intro hRu hRhat_budget)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model endpoint.  An explicit residual perturbation
    supplies the computed-residual certificate; determinant nonsingularity
    supplies the exact inverse budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model n n
      A B C X Xhat Rhat Ru dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model with a scalar cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model_scalar n n
      A B C X Xhat Rhat Ru dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model with monotone supplied inverse and residual
    estimates.  The monotone inputs may be estimator outputs, but no estimator
    correctness is asserted here. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model_mono n n
      A B C X Xhat Rhat Rhat' Ru Ru' dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    explicit residual-error model with monotone estimates and a scalar cap on
    the enlarged practical budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_error_model_mono_scalar n n
      A B C X Xhat Rhat Rhat' Ru Ru' dR
      (Inv.inv (sylvesterVecCoeff n n A B))
      (sylvesterVecCoeffNonsingInvAbs n n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff n n A B)
        (isUnit_iff_ne_zero.mpr hdet))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs n n A B)
      hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error endpoint.  A Frobenius residual-arithmetic
    certificate supplies the uniform residual budget `rho`; determinant
    nonsingularity supplies the nonsingular inverse budget. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat (fun _ _ => rho) hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error endpoint.  A Frobenius residual-arithmetic
    certificate supplies the uniform residual budget `rho`; determinant
    nonsingularity supplies the nonsingular inverse budget. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat (fun _ _ => rho) hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat (fun _ _ => rho) eta hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error monotone endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs'
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    absolute Frobenius residual-error monotone scalar endpoint. -/
theorem sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Not (Matrix.det (sylvesterVecCoeff n n A B) = 0))
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs' eta
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error scalar endpoint.  The scalar cap is taken over
    the determinant-supplied inverse budget and the uniform residual budget
    `rho`. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat dR : RMatFn n n) (rho eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat (fun _ _ => rho) eta hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat hrho hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error monotone endpoint.  Componentwise larger inverse
    and residual estimates may replace the determinant-supplied practical
    budget after the Frobenius certificate supplies `Ru i j = rho`. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs'
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square determinant
    Frobenius residual-error monotone scalar endpoint. -/
theorem sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru' dR : RMatFn n n)
    (rho : Real)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hdet : Matrix.det (sylvesterVecCoeff n n A B) ≠ 0)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' (fun _ _ => rho) Ru' PinvAbs' eta
      hdet hX
      (sylvesterComputedResidualBudget_of_frobenius_error_model n n
        A B C Xhat Rhat dR rho hRhat_eq hrho hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    if `A` and `B` are diagonal in the chosen bases, the vec/Kronecker
    Sylvester coefficient is diagonal with entries `a_i - b_j`.
    This is the algebraic finite-index core of the general eigenvalue
    difference formula. -/
theorem sylvesterVecCoeff_diagonal (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (fun p : Prod (Fin n) (Fin m) => a p.2 - b p.1) := by
  ext p q
  by_cases h1 : p.1 = q.1
  case pos =>
    by_cases h2 : p.2 = q.2
    case pos =>
      cases p
      cases q
      simp_all [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal]
    case neg =>
      have hpq : Not (p = q) := by
        intro hpq
        exact h2 (congrArg Prod.snd hpq)
      simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal, h1, h2, hpq]
  case neg =>
    have h1' : Not (q.1 = p.1) := by
      intro h
      exact h1 h.symm
    have hpq : Not (p = q) := by
      intro hpq
      exact h1 (congrArg Prod.fst hpq)
    by_cases h2 : p.2 = q.2
    case pos =>
      simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal, h1, h1', h2, hpq]
    case neg =>
      simp [sylvesterVecCoeff, Matrix.kronecker, Matrix.diagonal, h1, h1', h2, hpq]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    determinant of the diagonal-basis vec/Kronecker coefficient. -/
theorem sylvesterVecCoeff_diagonal_det (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b)).det =
      Finset.prod Finset.univ (fun p : Prod (Fin n) (Fin m) => a p.2 - b p.1) := by
  rw [sylvesterVecCoeff_diagonal, Matrix.det_diagonal]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    the diagonal-basis vec/Kronecker coefficient is nonsingular exactly when
    no diagonal entry of `A` equals a diagonal entry of `B`. -/
theorem sylvesterVecCoeff_diagonal_det_ne_zero_iff (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    Not ((sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b)).det = 0) <->
      forall i j, Not (a i - b j = 0) := by
  rw [sylvesterVecCoeff_diagonal_det]
  constructor
  case mp =>
    intro h i j
    have hall := Finset.prod_ne_zero_iff.mp h
    exact hall (j, i) (by simp)
  case mpr =>
    intro h
    exact Finset.prod_ne_zero_iff.mpr (by
      intro p _hp
      exact h p.2 p.1)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    a common diagonal entry makes the diagonal-basis vec/Kronecker Sylvester
    coefficient singular. -/
theorem sylvesterVecCoeff_diagonal_det_eq_zero_of_common_entry (n : Nat)
    (a b : Fin n -> Real) (i j : Fin n) (hij : a i = b j) :
    (sylvesterVecCoeff n n (Matrix.diagonal a) (Matrix.diagonal b)).det = 0 := by
  by_contra hdet
  have hsep := (sylvesterVecCoeff_diagonal_det_ne_zero_iff n n a b).mp hdet
  exact hsep i j (by rw [hij, sub_self])

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3):
    source-numbered alias for the diagonal vec/Kronecker Sylvester coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal :=
  sylvesterVecCoeff_diagonal

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3):
    source-numbered alias for the diagonal-basis determinant product. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_det :=
  sylvesterVecCoeff_diagonal_det

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3):
    source-numbered alias for diagonal nonsingularity by separated entries. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_det_ne_zero_iff :=
  sylvesterVecCoeff_diagonal_det_ne_zero_iff

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3):
    source-numbered alias for singularity from a common diagonal entry. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_det_eq_zero_of_common_entry :=
  sylvesterVecCoeff_diagonal_det_eq_zero_of_common_entry

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    explicit inverse for the diagonal-basis vec/Kronecker coefficient with
    diagonal entries `(a_i - b_j)^{-1}`. -/
noncomputable def sylvesterDiagonalVecCoeffInv (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real :=
  Matrix.diagonal
    (fun p : Prod (Fin n) (Fin m) => Ring.inverse (a p.2 - b p.1))

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal case:
    entrywise absolute-value bound for the explicit diagonal inverse of the
    vec/Kronecker Sylvester coefficient. -/
noncomputable def sylvesterDiagonalVecCoeffInvAbs (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real :=
  fun p q => |sylvesterDiagonalVecCoeffInv m n a b p q|

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    the explicit diagonal inverse is a left inverse for the separated
    vec/Kronecker Sylvester coefficient. -/
theorem sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hsep : forall i j, Not (a i - b j = 0)) :
    sylvesterDiagonalVecCoeffInv m n a b *
        sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b) = 1 := by
  rw [sylvesterVecCoeff_diagonal, sylvesterDiagonalVecCoeffInv,
    Matrix.diagonal_mul_diagonal]
  ext p q
  by_cases hpq : p = q
  case pos =>
    subst q
    simp [Matrix.diagonal, hsep p.2 p.1]
  case neg =>
    simp [Matrix.diagonal, hpq]

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    the separated diagonal-basis vec/Kronecker Sylvester coefficient is also a
    right inverse for the explicit diagonal inverse. -/
theorem sylvesterVecCoeff_diagonal_mul_sylvesterDiagonalVecCoeffInv (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hsep : forall i j, Not (a i - b j = 0)) :
    sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b) *
        sylvesterDiagonalVecCoeffInv m n a b = 1 := by
  rw [sylvesterVecCoeff_diagonal, sylvesterDiagonalVecCoeffInv,
    Matrix.diagonal_mul_diagonal]
  ext p q
  by_cases hpq : p = q
  case pos =>
    subst q
    simp [Matrix.diagonal, hsep p.2 p.1]
  case neg =>
    simp [Matrix.diagonal, hpq]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    in diagonal coordinates, the Sylvester operator acts entrywise as
    multiplication by `a_i - b_j`. -/
theorem sylvesterOpRect_diagonal_apply (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (X : RMatFn m n)
    (i : Fin m) (j : Fin n) :
    sylvesterOpRect m n (Matrix.diagonal a) (Matrix.diagonal b) X i j =
      (a i - b j) * X i j := by
  have h :=
    congrFun
      (sylvesterVecCoeff_mulVec_vec m n
        (Matrix.diagonal a) (Matrix.diagonal b) X) (j, i)
  rw [sylvesterVecCoeff_diagonal] at h
  simpa [Matrix.vec, Matrix.mulVec_diagonal] using h.symm

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    the entrywise solution obtained by dividing each right-hand side entry by
    the separated scalar coefficient `a_i - b_j`. -/
noncomputable def sylvesterDiagonalSolution (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n) : RMatFn m n :=
  fun i j => Ring.inverse (a i - b j) * C i j

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    the explicit diagonal solution of the homogeneous equation is zero. -/
theorem sylvesterDiagonalSolution_zero (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    sylvesterDiagonalSolution m n a b (0 : RMatFn m n) = 0 := by
  ext i j
  simp [sylvesterDiagonalSolution]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), diagonal case:
    vectorizing the explicit diagonal solution is the same as applying the
    explicit inverse diagonal vec/Kronecker coefficient. -/
theorem vec_sylvesterDiagonalSolution_eq_mulVec_inv (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n) :
    Matrix.vec (sylvesterDiagonalSolution m n a b C) =
      Matrix.mulVec (sylvesterDiagonalVecCoeffInv m n a b) (Matrix.vec C) := by
  ext p
  simp [sylvesterDiagonalSolution, sylvesterDiagonalVecCoeffInv, Matrix.vec,
    Matrix.mulVec_diagonal]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    the explicit entrywise formula solves the vectorized Sylvester system when
    the diagonal entries are pairwise separated. -/
theorem sylvesterVecCoeff_mulVec_vec_sylvesterDiagonalSolution (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0)) :
    Matrix.mulVec (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))
        (Matrix.vec (sylvesterDiagonalSolution m n a b C)) =
      Matrix.vec C := by
  rw [vec_sylvesterDiagonalSolution_eq_mulVec_inv, Matrix.mulVec_mulVec,
    sylvesterVecCoeff_diagonal_mul_sylvesterDiagonalVecCoeffInv m n a b hsep,
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    componentwise form of the exact diagonal solve. -/
theorem sylvesterOpRect_diagonal_sylvesterDiagonalSolution (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0)) :
    sylvesterOpRect m n (Matrix.diagonal a) (Matrix.diagonal b)
        (sylvesterDiagonalSolution m n a b C) =
      C := by
  ext i j
  rw [sylvesterOpRect_diagonal_apply]
  rw [sylvesterDiagonalSolution, ← mul_assoc]
  simp [hsep i j]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    the explicit entrywise formula is a Sylvester solution under separation. -/
theorem isSylvesterSolutionRect_sylvesterDiagonalSolution (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0)) :
    IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C
      (sylvesterDiagonalSolution m n a b C) := by
  exact
    (sylvester_vec_system_iff_solution m n
      (Matrix.diagonal a) (Matrix.diagonal b) C
      (sylvesterDiagonalSolution m n a b C)).mp
      (sylvesterVecCoeff_mulVec_vec_sylvesterDiagonalSolution m n a b C hsep)

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3), diagonal case:
    under separation, any Sylvester solution equals the explicit entrywise
    diagonal solution. -/
theorem sylvesterDiagonalSolution_unique (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X) :
    X = sylvesterDiagonalSolution m n a b C := by
  apply Matrix.vec_inj.mp
  have hvecX :
      Matrix.mulVec (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))
          (Matrix.vec X) =
        Matrix.vec C :=
    (sylvester_vec_system_iff_solution m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X).mpr hX
  rw [vec_sylvesterDiagonalSolution_eq_mulVec_inv, ← hvecX]
  rw [Matrix.mulVec_mulVec,
    sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal m n a b hsep,
    Matrix.one_mulVec]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3), diagonal case:
    separated diagonal Sylvester equations have exactly one solution, given by
    the explicit entrywise formula. -/
theorem existsUnique_isSylvesterSolutionRect_diagonal (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0)) :
    ExistsUnique
      (IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C) := by
  refine ⟨sylvesterDiagonalSolution m n a b C,
    isSylvesterSolutionRect_sylvesterDiagonalSolution m n a b C hsep, ?_⟩
  intro X hX
  exact sylvesterDiagonalSolution_unique m n a b C X hsep hX

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), diagonal case:
    under separated diagonal entries, the vectorized diagonal Sylvester
    coefficient has trivial kernel. -/
theorem sylvesterVecCoeff_diagonal_mulVec_eq_zero_iff (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) (X : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0)) :
    Matrix.mulVec (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))
        (Matrix.vec X) = 0 <->
      X = 0 := by
  constructor
  case mp =>
    intro h
    have hpinv :
        Matrix.mulVec (sylvesterDiagonalVecCoeffInv m n a b)
            (Matrix.mulVec
              (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))
              (Matrix.vec X)) =
          Matrix.mulVec (sylvesterDiagonalVecCoeffInv m n a b) 0 := by
      rw [h]
    rw [Matrix.mulVec_mulVec,
      sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal m n a b hsep,
      Matrix.one_mulVec, Matrix.mulVec_zero] at hpinv
    exact Matrix.vec_eq_zero_iff.mp hpinv
  case mpr =>
    intro hX
    rw [hX]
    change Matrix.mulVec
        (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))
        (0 : Prod (Fin n) (Fin m) -> Real) = 0
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), diagonal case:
    under separated diagonal entries, the vectorized diagonal Sylvester
    coefficient acts injectively on vectorized unknowns. -/
theorem sylvesterVecCoeff_diagonal_mulVec_injective (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Injective
      (Matrix.mulVec
        (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))) := by
  intro x y hxy
  let Pinv := sylvesterDiagonalVecCoeffInv m n a b
  let P := sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b)
  have hx : Matrix.mulVec Pinv (Matrix.mulVec P x) = x := by
    dsimp [Pinv, P]
    rw [Matrix.mulVec_mulVec,
      sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal m n a b hsep,
      Matrix.one_mulVec]
  have hy : Matrix.mulVec Pinv (Matrix.mulVec P y) = y := by
    dsimp [Pinv, P]
    rw [Matrix.mulVec_mulVec,
      sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal m n a b hsep,
      Matrix.one_mulVec]
  calc
    x = Matrix.mulVec Pinv (Matrix.mulVec P x) := hx.symm
    _ = Matrix.mulVec Pinv (Matrix.mulVec P y) := by rw [hxy]
    _ = y := hy

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), diagonal case:
    under separated diagonal entries, the vectorized diagonal Sylvester
    coefficient reaches every right-hand side by the explicit entrywise solve. -/
theorem sylvesterVecCoeff_diagonal_mulVec_surjective (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Surjective
      (Matrix.mulVec
        (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))) := by
  intro y
  obtain ⟨C, hC⟩ := Matrix.vec_bijective.surjective y
  refine ⟨Matrix.vec (sylvesterDiagonalSolution m n a b C), ?_⟩
  rw [← hC]
  exact sylvesterVecCoeff_mulVec_vec_sylvesterDiagonalSolution m n a b C hsep

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), diagonal case:
    separated diagonal entries make the vectorized diagonal Sylvester
    coefficient a bijection on vectorized unknowns. -/
theorem sylvesterVecCoeff_diagonal_mulVec_bijective (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Bijective
      (Matrix.mulVec
        (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b))) :=
  ⟨sylvesterVecCoeff_diagonal_mulVec_injective m n a b hsep,
    sylvesterVecCoeff_diagonal_mulVec_surjective m n a b hsep⟩

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), diagonal case:
    the separated diagonal vectorized Sylvester linear system has a unique
    solution for every vectorized right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_diagonal_mulVec (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec
        (sylvesterVecCoeff m n (Matrix.diagonal a) (Matrix.diagonal b)) x = c := by
  have hinj :=
    sylvesterVecCoeff_diagonal_mulVec_injective m n a b hsep
  have hsurj :=
    sylvesterVecCoeff_diagonal_mulVec_surjective m n a b hsep
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    abbreviation for the separated diagonal vec/Kronecker inverse. -/
noncomputable abbrev H16_eq16_3_sylvesterDiagonalVecCoeffInv :=
  sylvesterDiagonalVecCoeffInv

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    alias for the left-inverse property of the separated diagonal coefficient. -/
alias H16_eq16_3_sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal :=
  sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    alias for the right-inverse property of the separated diagonal coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_mul_sylvesterDiagonalVecCoeffInv :=
  sylvesterVecCoeff_diagonal_mul_sylvesterDiagonalVecCoeffInv

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3): source-numbered
    alias for the entrywise diagonal Sylvester operator action. -/
alias H16_eq16_3_sylvesterOpRect_diagonal_apply :=
  sylvesterOpRect_diagonal_apply

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    abbreviation for the explicit separated diagonal Sylvester solution. -/
noncomputable abbrev H16_eq16_3_sylvesterDiagonalSolution :=
  sylvesterDiagonalSolution

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    alias for the homogeneous explicit diagonal solution. -/
alias H16_eq16_3_sylvesterDiagonalSolution_zero :=
  sylvesterDiagonalSolution_zero

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias identifying the vectorized explicit solution with the inverse action. -/
alias H16_eq16_3_vec_sylvesterDiagonalSolution_eq_mulVec_inv :=
  vec_sylvesterDiagonalSolution_eq_mulVec_inv

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias for the vectorized diagonal solve. -/
alias H16_eq16_3_sylvesterVecCoeff_mulVec_vec_sylvesterDiagonalSolution :=
  sylvesterVecCoeff_mulVec_vec_sylvesterDiagonalSolution

/-- Higham, 2nd ed., Chapter 16.1, equations (16.1)-(16.3): source-numbered
    alias for the componentwise exact diagonal solve. -/
alias H16_eq16_3_sylvesterOpRect_diagonal_sylvesterDiagonalSolution :=
  sylvesterOpRect_diagonal_sylvesterDiagonalSolution

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    alias for the explicit diagonal Sylvester solution predicate. -/
alias H16_eq16_3_isSylvesterSolutionRect_sylvesterDiagonalSolution :=
  isSylvesterSolutionRect_sylvesterDiagonalSolution

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    alias for uniqueness of the explicit diagonal Sylvester solution. -/
alias H16_eq16_3_sylvesterDiagonalSolution_unique :=
  sylvesterDiagonalSolution_unique

/-- Higham, 2nd ed., Chapter 16.1, equation (16.3): source-numbered
    alias for unique solvability of separated diagonal Sylvester equations. -/
alias H16_eq16_3_existsUnique_isSylvesterSolutionRect_diagonal :=
  existsUnique_isSylvesterSolutionRect_diagonal

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias for the trivial-kernel form of the separated diagonal coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_mulVec_eq_zero_iff :=
  sylvesterVecCoeff_diagonal_mulVec_eq_zero_iff

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias for injectivity of the separated diagonal vec/Kronecker coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_mulVec_injective :=
  sylvesterVecCoeff_diagonal_mulVec_injective

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias for surjectivity of the separated diagonal vec/Kronecker coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_mulVec_surjective :=
  sylvesterVecCoeff_diagonal_mulVec_surjective

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias for bijectivity of the separated diagonal vec/Kronecker coefficient. -/
alias H16_eq16_3_sylvesterVecCoeff_diagonal_mulVec_bijective :=
  sylvesterVecCoeff_diagonal_mulVec_bijective

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3): source-numbered
    alias for unique vectorized solves by the separated diagonal coefficient. -/
alias H16_eq16_3_existsUnique_sylvesterVecCoeff_diagonal_mulVec :=
  existsUnique_sylvesterVecCoeff_diagonal_mulVec

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal case:
    the absolute-value matrix exactly bounds the explicit diagonal inverse
    componentwise. -/
lemma sylvesterDiagonalVecCoeffInv_abs_le_invAbs (m n : Nat)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    forall p q,
      |sylvesterDiagonalVecCoeffInv m n a b p q| <=
        sylvesterDiagonalVecCoeffInvAbs m n a b p q := by
  intro p q
  rfl

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    with `A` and `B` diagonal and `a_i != b_j`, the practical componentwise
    error bound is instantiated with the explicit diagonal inverse of the
    vec/Kronecker Sylvester coefficient. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Ru
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    after replacing the explicit diagonal inverse and computed-residual budget
    by componentwise larger supplied estimates, the enlarged practical budget
    gives the relative max-entry error bound.  This is an exact
    diagonal-inverse specialization; it does not prove any estimator such as a
    LAPACK condition estimator. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Rhat' Ru Ru'
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      PinvAbs' hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    a scalar cap on the explicit diagonal-inverse practical budget gives the
    final practical relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Ru
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      eta hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    after replacing the explicit diagonal inverse and computed-residual budget
    by componentwise larger supplied estimates, a scalar cap on the estimated
    practical budget gives the relative max-entry error bound.  This is an
    exact diagonal-inverse specialization; it does not prove any estimator such
    as a LAPACK condition estimator. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hBudget :
      IsSylvesterComputedResidualBudget m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat Rhat Rhat' Ru Ru'
      (sylvesterDiagonalVecCoeffInv m n a b)
      (sylvesterDiagonalVecCoeffInvAbs m n a b)
      PinvAbs' eta hX
      (sylvesterDiagonalVecCoeffInv_mul_sylvesterVecCoeff_diagonal
        m n a b hsep)
      (sylvesterDiagonalVecCoeffInv_abs_le_invAbs m n a b)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form of the practical componentwise error
    bound using the explicit diagonal inverse of the vec/Kronecker Sylvester
    coefficient. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
      m n a b C X Xhat Rhat Ru hsep hX
      (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form with componentwise larger supplied
    inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hsep hX
      (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form with a scalar cap on the practical
    budget. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
      m n a b C X Xhat Rhat Ru eta hsep hX
      (And.intro hRu hRhat) heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    raw computed-residual budget form with monotone supplied estimates and a
    scalar cap on the estimated practical budget. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j -
          Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hsep hX
      (And.intro hRu hRhat) hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case:
    if the computed residual has an explicit error model
    `Rhat = R(Xhat) + dR` with `|dR| <= Ru`, then the practical
    componentwise error bound follows using the explicit diagonal inverse of
    the vec/Kronecker Sylvester coefficient. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate
      m n a b C X Xhat Rhat Ru hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case
    with an explicit residual error model: after replacing the exact diagonal
    inverse and residual budget by componentwise larger supplied estimates, the
    enlarged practical budget gives the final relative max-entry error bound.
    This remains an exact diagonal-inverse wrapper, not a rounded residual or
    estimator proof. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat_model : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case
    with an explicit residual error model and a scalar cap on the practical
    budget. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterDiagonalVecCoeffInvAbs m n a b) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar
      m n a b C X Xhat Rhat Ru eta hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), diagonal separated case
    with an explicit residual error model: after replacing the exact diagonal
    inverse and computed-residual budget by componentwise larger supplied
    estimates, a scalar cap on the estimated practical budget gives the final
    relative max-entry error bound.  This is an exact diagonal-inverse
    specialization; it does not prove any estimator such as a LAPACK condition
    estimator. -/
theorem sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono_scalar
    (m n : Nat) (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b) C X)
    (hRhat_eq : forall i j,
      Rhat i j =
        sylvesterResidualRect m n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat i j +
          dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterDiagonalVecCoeffInvAbs m n a b p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar
      m n a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n
        (Matrix.diagonal a) (Matrix.diagonal b) C Xhat Rhat Ru dR
        hRhat_eq hRu hdR)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

-- ============================================================
-- Exact Schur-coordinate algebra from Chapter 16.1
-- ============================================================

private theorem rectMatMul_left_right_sub {m n p q : Nat}
    (A : Fin m -> Fin n -> Real) (B C : Fin n -> Fin p -> Real)
    (D : Fin p -> Fin q -> Real) :
    rectMatMul A (rectMatMul (fun i j => B i j - C i j) D) =
      fun i j => rectMatMul A (rectMatMul B D) i j -
        rectMatMul A (rectMatMul C D) i j := by
  ext i j
  unfold rectMatMul
  rw [(Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun k : Fin n => A i k * Finset.sum Finset.univ (fun k1 : Fin p =>
      B k k1 * D k1 j))
    (g := fun k : Fin n => A i k * Finset.sum Finset.univ (fun k1 : Fin p =>
      C k k1 * D k1 j))).symm]
  apply Finset.sum_congr rfl
  intro k _
  rw [(mul_sub (A i k)
    (Finset.sum Finset.univ (fun k1 : Fin p => B k k1 * D k1 j))
    (Finset.sum Finset.univ (fun k1 : Fin p => C k k1 * D k1 j))).symm]
  apply congrArg (fun z => A i k * z)
  rw [(Finset.sum_sub_distrib (s := Finset.univ)
    (f := fun k1 : Fin p => B k k1 * D k1 j)
    (g := fun k1 : Fin p => C k k1 * D k1 j)).symm]
  apply Finset.sum_congr rfl
  intro k1 _
  ring

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    exact Sylvester-operator algebra in supplied Schur coordinates.  If
    `A = U R U^T`, `B = V S V^T`, and `U,V` are orthogonal, then
    substituting `X = U Y V^T` transforms `AX - XB` into
    `U (RY - YS) V^T`.  This conditional wrapper does not assert existence
    of Schur decompositions or any triangular/quasi-triangular structure. -/
theorem sylvester_schur_transform_identity (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    sylvesterOpRect m n A B (rectMatMul U (rectMatMul Y (matTranspose V))) =
      rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) := by
  subst A
  subst B
  have hUtU : rectMatMul (matTranspose U) U = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hVtV : rectMatMul (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.left_inv i j
  have hleft :
      rectMatMul (rectMatMul U (rectMatMul R (matTranspose U)))
          (rectMatMul U (rectMatMul Y (matTranspose V))) =
        rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) := by
    calc
      rectMatMul (rectMatMul U (rectMatMul R (matTranspose U)))
          (rectMatMul U (rectMatMul Y (matTranspose V)))
          = rectMatMul U (rectMatMul (rectMatMul R (matTranspose U))
              (rectMatMul U (rectMatMul Y (matTranspose V)))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (matTranspose U) (rectMatMul U (rectMatMul Y (matTranspose V))))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (rectMatMul (matTranspose U) U) (rectMatMul Y (matTranspose V)))) := by
              exact congrArg (fun Z => rectMatMul U (rectMatMul R Z))
                (rectMatMul_assoc (matTranspose U) U (rectMatMul Y (matTranspose V))).symm
      _ = rectMatMul U (rectMatMul R
              (rectMatMul (idMatrix m) (rectMatMul Y (matTranspose V)))) := by
              rw [hUtU]
      _ = rectMatMul U (rectMatMul R (rectMatMul Y (matTranspose V))) := by
              rw [rectMatMul_id_left]
      _ = rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) := by
              exact congrArg (rectMatMul U) (rectMatMul_assoc R Y (matTranspose V)).symm
  have hright :
      rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
          (rectMatMul V (rectMatMul S (matTranspose V))) =
        rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) := by
    calc
      rectMatMul (rectMatMul U (rectMatMul Y (matTranspose V)))
          (rectMatMul V (rectMatMul S (matTranspose V)))
          = rectMatMul U (rectMatMul (rectMatMul Y (matTranspose V))
              (rectMatMul V (rectMatMul S (matTranspose V)))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (matTranspose V) (rectMatMul V (rectMatMul S (matTranspose V))))) := by
              rw [rectMatMul_assoc]
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (rectMatMul (matTranspose V) V) (rectMatMul S (matTranspose V)))) := by
              exact congrArg (fun Z => rectMatMul U (rectMatMul Y Z))
                (rectMatMul_assoc (matTranspose V) V (rectMatMul S (matTranspose V))).symm
      _ = rectMatMul U (rectMatMul Y
              (rectMatMul (idMatrix n) (rectMatMul S (matTranspose V)))) := by
              rw [hVtV]
      _ = rectMatMul U (rectMatMul Y (rectMatMul S (matTranspose V))) := by
              rw [rectMatMul_id_left]
      _ = rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) := by
              exact congrArg (rectMatMul U) (rectMatMul_assoc Y S (matTranspose V)).symm
  have hcombine :
      rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) =
        fun i j => rectMatMul U (rectMatMul (rectMatMul R Y) (matTranspose V)) i j -
          rectMatMul U (rectMatMul (rectMatMul Y S) (matTranspose V)) i j := by
    simpa [sylvesterOpRect, matMulRect_eq_rectMatMul] using
      (rectMatMul_left_right_sub U (rectMatMul R Y) (rectMatMul Y S) (matTranspose V))
  unfold sylvesterOpRect
  simp only [matMulRect_eq_rectMatMul]
  rw [hleft, hright]
  exact hcombine.symm

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    source-numbered alias for the supplied Schur-coordinate Sylvester
    operator identity. -/
alias H16_eq16_4_5_sylvester_schur_transform_identity :=
  sylvester_schur_transform_identity

theorem rectMatMul_schur_coords_cancel {m n : Nat}
    (U : RMatFn m m) (V : RMatFn n n) (M : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    rectMatMul (matTranspose U)
      (rectMatMul (rectMatMul U (rectMatMul M (matTranspose V))) V) = M := by
  have hUtU : rectMatMul (matTranspose U) U = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.left_inv i j
  have hVtV : rectMatMul (matTranspose V) V = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.left_inv i j
  calc
    rectMatMul (matTranspose U)
        (rectMatMul (rectMatMul U (rectMatMul M (matTranspose V))) V)
        = rectMatMul (rectMatMul (matTranspose U)
            (rectMatMul U (rectMatMul M (matTranspose V)))) V := by
            exact (rectMatMul_assoc (matTranspose U)
              (rectMatMul U (rectMatMul M (matTranspose V))) V).symm
    _ = rectMatMul (rectMatMul (rectMatMul (matTranspose U) U)
            (rectMatMul M (matTranspose V))) V := by
            exact congrArg (fun Z => rectMatMul Z V)
              (rectMatMul_assoc (matTranspose U) U (rectMatMul M (matTranspose V))).symm
    _ = rectMatMul (rectMatMul (idMatrix m) (rectMatMul M (matTranspose V))) V := by
            rw [hUtU]
    _ = rectMatMul (rectMatMul M (matTranspose V)) V := by
            rw [rectMatMul_id_left]
    _ = rectMatMul M (rectMatMul (matTranspose V) V) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul M (idMatrix n) := by
            rw [hVtV]
    _ = M := by
            rw [rectMatMul_id_right]

theorem rectMatMul_schur_coords_expand {m n : Nat}
    (U : RMatFn m m) (V : RMatFn n n) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V) :
    rectMatMul U
      (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)) = C := by
  have hUUt : rectMatMul U (matTranspose U) = idMatrix m := by
    ext i j
    simpa [rectMatMul, idMatrix] using hU.right_inv i j
  have hVVt : rectMatMul V (matTranspose V) = idMatrix n := by
    ext i j
    simpa [rectMatMul, idMatrix] using hV.right_inv i j
  calc
    rectMatMul U
        (rectMatMul (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V))
        = rectMatMul (rectMatMul U
            (rectMatMul (matTranspose U) (rectMatMul C V))) (matTranspose V) := by
            exact (rectMatMul_assoc U
              (rectMatMul (matTranspose U) (rectMatMul C V)) (matTranspose V)).symm
    _ = rectMatMul (rectMatMul (rectMatMul U (matTranspose U))
            (rectMatMul C V)) (matTranspose V) := by
            exact congrArg (fun Z => rectMatMul Z (matTranspose V))
              (rectMatMul_assoc U (matTranspose U) (rectMatMul C V)).symm
    _ = rectMatMul (rectMatMul (idMatrix m) (rectMatMul C V)) (matTranspose V) := by
            rw [hUUt]
    _ = rectMatMul (rectMatMul C V) (matTranspose V) := by
            rw [rectMatMul_id_left]
    _ = rectMatMul C (rectMatMul V (matTranspose V)) := by
            rw [rectMatMul_assoc]
    _ = rectMatMul C (idMatrix n) := by
            rw [hVVt]
    _ = C := by
            rw [rectMatMul_id_right]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.5) and (16.9):
    exact residual transport under supplied orthogonal Schur coordinates.
    If `A = U R U^T`, `B = V S V^T`, and `Xhat = U Y V^T`, then the original
    residual is `U` times the Schur-coordinate residual times `V^T`. -/
theorem sylvesterResidualRect_schur_transform_identity (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    sylvesterResidualRect m n A B C
        (rectMatMul U (rectMatMul Y (matTranspose V))) =
      rectMatMul U
        (rectMatMul
          (sylvesterResidualRect m n R S
            (rectMatMul (matTranspose U) (rectMatMul C V)) Y)
          (matTranspose V)) := by
  let Cs : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul C V)
  have hCexpand : rectMatMul U (rectMatMul Cs (matTranspose V)) = C := by
    simpa [Cs] using rectMatMul_schur_coords_expand U V C hU hV
  have hop :=
    sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
  have hsub :=
    rectMatMul_left_right_sub U Cs (sylvesterOpRect m n R S Y) (matTranspose V)
  ext i j
  unfold sylvesterResidualRect
  rw [hop]
  have hCij := congrFun (congrFun hCexpand i) j
  have hsubij := congrFun (congrFun hsub i) j
  rw [← hCij, ← hsubij]

/-- Higham, 2nd ed., Chapter 16.1-16.2, equations (16.5) and (16.9):
    source-numbered alias for exact residual transport under supplied
    orthogonal Schur coordinates. -/
alias H16_eq16_5_9_sylvesterResidualRect_schur_transform_identity :=
  sylvesterResidualRect_schur_transform_identity

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), exact residual norm
    transport for supplied orthogonal Schur coordinates.  This is the
    exact-arithmetic norm bridge used before any rounded Schur-solve residual
    model is introduced. -/
theorem frobNormRect_sylvesterResidualRect_schur_transform (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) =
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) := by
  let Rs : RMatFn m n :=
    sylvesterResidualRect m n R S
      (rectMatMul (matTranspose U) (rectMatMul C V)) Y
  rw [sylvesterResidualRect_schur_transform_identity m n U R A V S B C Y
    hU hV hA hB]
  calc
    frobNormRect (rectMatMul U (rectMatMul Rs (matTranspose V))) =
        frobNormRect (rectMatMul Rs (matTranspose V)) := by
          simpa [Rs, matMulRectLeft] using
            frobNormRect_orthogonal_left U
              (rectMatMul Rs (matTranspose V)) hU
    _ = frobNormRect Rs := by
          simpa [Rs, matMulRectRight] using
            frobNormRect_orthogonal_right Rs (matTranspose V) hV.transpose

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9): source-numbered alias
    for exact Frobenius residual norm transport under supplied orthogonal
    Schur coordinates. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_schur_transform :=
  frobNormRect_sylvesterResidualRect_schur_transform

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9), conditional exact
    residual-bound transport.  Any Schur-coordinate Frobenius residual bound
    transfers unchanged to the reconstructed original-coordinate iterate. -/
theorem frobNormRect_sylvesterResidualRect_le_of_schur_transform (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    frobNormRect
        (sylvesterResidualRect m n A B C
          (rectMatMul U (rectMatMul Y (matTranspose V)))) <= rho := by
  rw [frobNormRect_sylvesterResidualRect_schur_transform m n U R A V S B C Y
    hU hV hA hB]
  exact hres

/-- Higham, 2nd ed., Chapter 16.2, equation (16.9): source-numbered
    alias for exact residual-bound transport from Schur coordinates. -/
alias H16_eq16_9_frobNormRect_sylvesterResidualRect_le_of_schur_transform :=
  frobNormRect_sylvesterResidualRect_le_of_schur_transform

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    a Frobenius residual-error model in Schur coordinates transfers to the
    original-coordinate computed-residual budget after orthogonal
    reconstruction. -/
theorem sylvesterComputedResidualBudget_of_schur_frobenius_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Y RhatS dRs : RMatFn m n) (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hRhatS : forall i j,
      RhatS i j =
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) i j + dRs i j)
    (hrho : 0 <= rho)
    (hdRs : frobNorm dRs <= rho) :
    IsSylvesterComputedResidualBudget m n A B C
      (rectMatMul U (rectMatMul Y (matTranspose V)))
      (rectMatMul U (rectMatMul RhatS (matTranspose V)))
      (fun _ _ => rho) := by
  let Cs : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul C V)
  let Rs : RMatFn m n := sylvesterResidualRect m n R S Cs Y
  let Xhat : RMatFn m n := rectMatMul U (rectMatMul Y (matTranspose V))
  let Rhat : RMatFn m n := rectMatMul U (rectMatMul RhatS (matTranspose V))
  let dR : RMatFn m n := rectMatMul U (rectMatMul dRs (matTranspose V))
  have hRhatS_fun : RhatS = fun i j => Rs i j + dRs i j := by
    ext i j
    simpa [Rs, Cs] using hRhatS i j
  have hinner :
      rectMatMul RhatS (matTranspose V) =
        fun i j =>
          rectMatMul Rs (matTranspose V) i j +
            rectMatMul dRs (matTranspose V) i j := by
    rw [hRhatS_fun]
    exact rectMatMul_add_left Rs dRs (matTranspose V)
  have houter :
      Rhat =
        fun i j =>
          rectMatMul U (rectMatMul Rs (matTranspose V)) i j + dR i j := by
    unfold Rhat dR
    rw [hinner]
    exact rectMatMul_add_right U
      (rectMatMul Rs (matTranspose V)) (rectMatMul dRs (matTranspose V))
  have horig :
      sylvesterResidualRect m n A B C Xhat =
        rectMatMul U (rectMatMul Rs (matTranspose V)) := by
    simpa [Xhat, Rs, Cs] using
      sylvesterResidualRect_schur_transform_identity
        m n U R A V S B C Y hU hV hA hB
  have hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j := by
    intro i j
    have houterij := congrFun (congrFun houter i) j
    have horigij := congrFun (congrFun horig i) j
    calc
      Rhat i j =
          rectMatMul U (rectMatMul Rs (matTranspose V)) i j + dR i j := houterij
      _ = sylvesterResidualRect m n A B C Xhat i j + dR i j := by
          rw [← horigij]
  have hdR : frobNorm dR <= rho := by
    have hrect : frobNormRect dR = frobNormRect dRs := by
      calc
        frobNormRect dR =
            frobNormRect (rectMatMul dRs (matTranspose V)) := by
            simpa [dR, matMulRectLeft] using
              frobNormRect_orthogonal_left U
                (rectMatMul dRs (matTranspose V)) hU
        _ = frobNormRect dRs := by
            simpa [matMulRectRight] using
              frobNormRect_orthogonal_right dRs (matTranspose V) hV.transpose
    have hnorm : frobNorm dR = frobNorm dRs := by
      rw [← frobNormRect_eq_frobNormFn dR, hrect,
        frobNormRect_eq_frobNormFn dRs]
    simpa [hnorm] using hdRs
  simpa [Xhat, Rhat] using
    sylvesterComputedResidualBudget_of_frobenius_error_model m n
      A B C Xhat Rhat dR rho hRhat hrho hdR

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the Schur-coordinate Frobenius residual-error budget transfer. -/
alias H16_eq16_29_sylvesterComputedResidualBudget_of_schur_frobenius_error_model :=
  sylvesterComputedResidualBudget_of_schur_frobenius_error_model

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    a Schur-coordinate Frobenius residual bound gives an original-coordinate
    computed-residual budget with `Rhat = 0` and uniform radius `rho`. -/
theorem sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C Y : RMatFn m n) (rho : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    IsSylvesterComputedResidualBudget m n A B C
      (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) := by
  let Xhat : RMatFn m n := rectMatMul U (rectMatMul Y (matTranspose V))
  let Rorig : RMatFn m n := sylvesterResidualRect m n A B C Xhat
  have hres_orig : frobNormRect Rorig <= rho := by
    simpa [Xhat, Rorig] using
      frobNormRect_sylvesterResidualRect_le_of_schur_transform
        m n U R A V S B C Y rho hU hV hA hB hres
  have hrho : 0 <= rho := (frobNormRect_nonneg Rorig).trans hres_orig
  constructor
  · intro _ _
    exact hrho
  · intro i j
    have hentry : |Rorig i j| <= rho :=
      (abs_entry_le_frobNormRect Rorig i j).trans hres_orig
    simpa [Xhat, Rorig] using hentry

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    conservative practical max-entry bound from a Schur-coordinate Frobenius
    residual bound, using `Rhat = 0` and a uniform residual budget `rho`. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (fun _ _ => 0) (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    scalar-cap conservative practical max-entry bound from a Schur-coordinate
    Frobenius residual bound. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (heta : 0 <= eta)
    (hcomponent :
      forall p,
        sylvesterPracticalBudgetVec m n PinvAbs
            (fun _ _ => 0) (fun _ _ => rho) p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      eta /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs eta
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    monotone conservative practical max-entry bound from a Schur-coordinate
    Frobenius residual bound.  This estimator-facing wrapper permits a larger
    supplied inverse/residual budget without proving the estimator itself. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound_mono
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho : Real)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru'
      Pinv PinvAbs PinvAbs'
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    monotone scalar-cap conservative practical max-entry bound from a
    Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_error_bound_of_schur_transform_residual_bound_mono_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y Rhat' Ru' : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hPinvAbs_le : forall p q, PinvAbs p q <= PinvAbs' p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (hRhat : forall i j, |(0 : Real)| <= |Rhat' i j|)
    (hRu_le : forall i j, rho <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      eta /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) Rhat' (fun _ _ => rho) Ru'
      Pinv PinvAbs PinvAbs' eta
      hX hLeft hPinvAbs hPinvAbs_le
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    practical max-entry bound from a Schur-coordinate Frobenius residual-error
    model.  This wrapper consumes the exact residual-arithmetic certificate and
    does not prove rounded Bartels-Stewart arithmetic. -/
theorem sylvester_practical_error_bound_of_schur_frobenius_error_model
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y RhatS dR : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hRhatS : forall i j,
      RhatS i j = sylvesterResidualRect m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) Y i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n
      (rectMatMul U (rectMatMul Y (matTranspose V)))) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (rectMatMul U (rectMatMul RhatS (matTranspose V)))
          (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect m n
          (rectMatMul U (rectMatMul Y (matTranspose V))) := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (rectMatMul U (rectMatMul RhatS (matTranspose V)))
      (fun _ _ => rho) Pinv PinvAbs hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_of_schur_frobenius_error_model
        m n U R A V S B C Y RhatS dR rho
        hU hV hA hB hRhatS hrho hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    denominator-free conservative practical max-entry bound from a
    Schur-coordinate Frobenius residual bound. -/
theorem sylvester_practical_abs_error_bound_of_schur_transform_residual_bound
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs
          (fun _ _ => 0) (fun _ _ => rho)) := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate m n
      A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)

/-- Higham, 2nd ed., Chapter 16.2 and 16.4, equations (16.9) and (16.29):
    scalar-cap form of the denominator-free conservative Schur residual
    practical max-entry bound. -/
theorem sylvester_practical_abs_error_bound_of_schur_transform_residual_bound_scalar
    (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n)
    (C X Y : RMatFn m n) (rho eta : Real)
    (Pinv PinvAbs :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V)))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hLeft : Pinv * sylvesterVecCoeff m n A B = 1)
    (hPinvAbs : forall p q, |Pinv p q| <= PinvAbs p q)
    (hres :
      frobNormRect
        (sylvesterResidualRect m n R S
          (rectMatMul (matTranspose U) (rectMatMul C V)) Y) <= rho)
    (heta : 0 <= eta)
    (hcomponent :
      forall p,
        sylvesterPracticalBudgetVec m n PinvAbs
            (fun _ _ => 0) (fun _ _ => rho) p <= eta) :
    sylvesterMaxEntryNormRect m n
        (fun i j =>
          X i j - rectMatMul U (rectMatMul Y (matTranspose V)) i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_computed_residual_certificate_scalar
      m n A B C X (rectMatMul U (rectMatMul Y (matTranspose V)))
      (fun _ _ => 0) (fun _ _ => rho) Pinv PinvAbs eta
      hX hLeft hPinvAbs
      (sylvesterComputedResidualBudget_zero_of_schur_transform_residual_bound
        m n U R A V S B C Y rho hU hV hA hB hres)
      heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the conservative practical wrapper from a Schur residual bound. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the scalar-cap conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound_scalar :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the monotone conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound_mono :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the monotone scalar-cap conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_transform_residual_bound_mono_scalar :=
  sylvester_practical_error_bound_of_schur_transform_residual_bound_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the Schur-coordinate Frobenius residual-error practical wrapper. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schur_frobenius_error_model :=
  sylvester_practical_error_bound_of_schur_frobenius_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the denominator-free conservative Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_schur_transform_residual_bound :=
  sylvester_practical_abs_error_bound_of_schur_transform_residual_bound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered alias
    for the denominator-free scalar-cap Schur residual practical wrapper. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_schur_transform_residual_bound_scalar :=
  sylvester_practical_abs_error_bound_of_schur_transform_residual_bound_scalar

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    equation-level Schur-coordinate form.  Under supplied orthogonal
    factorizations `A = U R U^T` and `B = V S V^T`, the substitution
    `X = U Y V^T` solves `AX - XB = C` exactly when `Y` solves
    `RY - YS = U^T C V`. -/
theorem sylvester_schur_transform_solution_iff (m n : Nat)
    (U R A : RMatFn m m) (V S B : RMatFn n n) (C Y : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul R (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul S (matTranspose V))) :
    IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul Y (matTranspose V))) <->
      IsSylvesterSolutionRect m n R S
        (rectMatMul (matTranspose U) (rectMatMul C V)) Y := by
  constructor
  case mp =>
    intro h
    have htrans := sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
    have hUMVt :
        rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) = C := by
      rw [htrans.symm]
      ext i j
      exact h i j
    have hM :
        sylvesterOpRect m n R S Y =
          rectMatMul (matTranspose U) (rectMatMul C V) := by
      calc
        sylvesterOpRect m n R S Y =
            rectMatMul (matTranspose U)
              (rectMatMul (rectMatMul U
                (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V))) V) := by
                exact (rectMatMul_schur_coords_cancel U V
                  (sylvesterOpRect m n R S Y) hU hV).symm
        _ = rectMatMul (matTranspose U) (rectMatMul C V) := by
                rw [hUMVt]
    intro i j
    exact congrFun (congrFun hM i) j
  case mpr =>
    intro h
    have hM :
        sylvesterOpRect m n R S Y =
          rectMatMul (matTranspose U) (rectMatMul C V) := by
      ext i j
      exact h i j
    have hUMVt :
        rectMatMul U (rectMatMul (sylvesterOpRect m n R S Y) (matTranspose V)) = C := by
      rw [hM]
      exact rectMatMul_schur_coords_expand U V C hU hV
    have htrans := sylvester_schur_transform_identity m n U R A V S B Y hU hV hA hB
    have hsol :
        sylvesterOpRect m n A B (rectMatMul U (rectMatMul Y (matTranspose V))) = C := by
      rw [htrans]
      exact hUMVt
    intro i j
    exact congrFun (congrFun hsol i) j

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5):
    source-numbered alias for the supplied Schur-coordinate equation-level
    solution equivalence. -/
alias H16_eq16_4_5_sylvester_schur_transform_solution_iff :=
  sylvester_schur_transform_solution_iff

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5), diagonal
    Schur-coordinate case: reconstruct the original-coordinate solution from
    supplied orthogonal diagonal factors and the explicit diagonal solve. -/
noncomputable def sylvesterSchurDiagonalSolution (m n : Nat)
    (U : RMatFn m m) (V : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n) : RMatFn m n :=
  rectMatMul U
    (rectMatMul
      (sylvesterDiagonalSolution m n a b
        (rectMatMul (matTranspose U) (rectMatMul C V)))
      (matTranspose V))

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), diagonal
    Schur-coordinate case: the reconstructed solution for zero right-hand side
    is zero. -/
theorem sylvesterSchurDiagonalSolution_zero (m n : Nat)
    (U : RMatFn m m) (V : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) :
    sylvesterSchurDiagonalSolution m n U V a b (0 : RMatFn m n) = 0 := by
  unfold sylvesterSchurDiagonalSolution
  have hcoord :
      rectMatMul (matTranspose U) (rectMatMul (0 : RMatFn m n) V) =
        (0 : RMatFn m n) := by
    ext i j
    simp [rectMatMul]
  rw [hcoord]
  rw [sylvesterDiagonalSolution_zero]
  ext i j
  simp [rectMatMul]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.4)-(16.5), diagonal
    Schur-coordinate case: if supplied orthogonal factors diagonalize `A` and
    `B`, the reconstructed explicit diagonal-coordinate solution solves the
    original Sylvester equation.  This remains an exact-arithmetic conditional
    wrapper; it does not assert Schur existence or floating-point stability. -/
theorem isSylvesterSolutionRect_schurDiagonalSolution (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    IsSylvesterSolutionRect m n A B C
      (sylvesterSchurDiagonalSolution m n U V a b C) := by
  unfold sylvesterSchurDiagonalSolution
  exact
    (sylvester_schur_transform_solution_iff m n
      U (Matrix.diagonal a) A V (Matrix.diagonal b) B C
      (sylvesterDiagonalSolution m n a b
        (rectMatMul (matTranspose U) (rectMatMul C V)))
      hU hV hA hB).mpr
      (isSylvesterSolutionRect_sylvesterDiagonalSolution m n a b
        (rectMatMul (matTranspose U) (rectMatMul C V)) hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), diagonal
    Schur-coordinate case: under supplied orthogonal diagonal factors and
    separated diagonal entries, every original-coordinate solution is the
    reconstructed explicit diagonal-coordinate solution. -/
theorem sylvesterSchurDiagonalSolution_unique (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C X : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X) :
    X = sylvesterSchurDiagonalSolution m n U V a b C := by
  let YX : RMatFn m n := rectMatMul (matTranspose U) (rectMatMul X V)
  have hXrecon :
      IsSylvesterSolutionRect m n A B C
        (rectMatMul U (rectMatMul YX (matTranspose V))) := by
    dsimp [YX]
    rw [rectMatMul_schur_coords_expand U V X hU hV]
    exact hX
  have hYsol :
      IsSylvesterSolutionRect m n (Matrix.diagonal a) (Matrix.diagonal b)
        (rectMatMul (matTranspose U) (rectMatMul C V)) YX :=
    (sylvester_schur_transform_solution_iff m n
      U (Matrix.diagonal a) A V (Matrix.diagonal b) B C YX
      hU hV hA hB).mp hXrecon
  have hYeq :
      YX =
        sylvesterDiagonalSolution m n a b
          (rectMatMul (matTranspose U) (rectMatMul C V)) :=
    sylvesterDiagonalSolution_unique m n a b
      (rectMatMul (matTranspose U) (rectMatMul C V)) YX hsep hYsol
  calc
    X = rectMatMul U (rectMatMul YX (matTranspose V)) := by
        dsimp [YX]
        exact (rectMatMul_schur_coords_expand U V X hU hV).symm
    _ = sylvesterSchurDiagonalSolution m n U V a b C := by
        unfold sylvesterSchurDiagonalSolution
        rw [hYeq]

/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries give a unique exact Sylvester solution. -/
theorem existsUnique_isSylvesterSolutionRect_schurDiagonal (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (C : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    ExistsUnique (IsSylvesterSolutionRect m n A B C) := by
  refine ⟨sylvesterSchurDiagonalSolution m n U V a b C,
    isSylvesterSolutionRect_schurDiagonalSolution m n U A V B a b C
      hU hV hA hB hsep, ?_⟩
  intro X hX
  exact sylvesterSchurDiagonalSolution_unique m n U A V B a b C X
    hU hV hA hB hsep hX

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient have trivial
    kernel. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_eq_zero_iff (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real) (X : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 <->
      X = 0 := by
  constructor
  case mp =>
    intro h
    have hsol : IsSylvesterSolutionRect m n A B (0 : RMatFn m n) X :=
      (sylvester_vec_system_iff_solution m n A B (0 : RMatFn m n) X).mp
        (by simpa using h)
    have hX :
        X = sylvesterSchurDiagonalSolution m n U V a b (0 : RMatFn m n) :=
      sylvesterSchurDiagonalSolution_unique m n U A V B a b
        (0 : RMatFn m n) X hU hV hA hB hsep hsol
    rw [hX, sylvesterSchurDiagonalSolution_zero]
  case mpr =>
    intro hX
    rw [hX]
    change Matrix.mulVec (sylvesterVecCoeff m n A B)
        (0 : Prod (Fin n) (Fin m) -> Real) = 0
    exact Matrix.mulVec_zero _

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient injective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_injective (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro x y hxy
  let P := sylvesterVecCoeff m n A B
  have hker : Matrix.mulVec P (x - y) = 0 := by
    dsimp [P]
    rw [Matrix.mulVec_sub, hxy, sub_self]
  obtain ⟨X, hXvec⟩ :=
    Matrix.vec_bijective.surjective (x - y : Prod (Fin n) (Fin m) -> Real)
  have hkerX :
      Matrix.mulVec (sylvesterVecCoeff m n A B) (Matrix.vec X) = 0 := by
    dsimp [P] at hker
    rw [hXvec]
    exact hker
  have hXzero : X = 0 :=
    (sylvesterVecCoeff_schurDiagonal_mulVec_eq_zero_iff
      m n U A V B a b X hU hV hA hB hsep).mp hkerX
  have hsub : x - y = 0 := by
    rw [← hXvec, hXzero]
    rfl
  exact sub_eq_zero.mp hsub

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient surjective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_surjective (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff m n A B)) := by
  intro y
  obtain ⟨C, hC⟩ := Matrix.vec_bijective.surjective y
  refine ⟨Matrix.vec (sylvesterSchurDiagonalSolution m n U V a b C), ?_⟩
  rw [← hC]
  exact
    (sylvester_vec_system_iff_solution m n A B C
      (sylvesterSchurDiagonalSolution m n U V a b C)).mpr
      (isSylvesterSolutionRect_schurDiagonalSolution
        m n U A V B a b C hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vectorized Sylvester coefficient bijective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_bijective (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff m n A B)) :=
  ⟨sylvesterVecCoeff_schurDiagonal_mulVec_injective
      m n U A V B a b hU hV hA hB hsep,
    sylvesterVecCoeff_schurDiagonal_mulVec_surjective
      m n U A V B a b hU hV hA hB hsep⟩

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: supplied orthogonal diagonal factors with separated
    diagonal entries make the vec/Kronecker Sylvester coefficient
    nonsingular. This is the determinant form of the vectorized solve theorem;
    it is a supplied-factor result, not a proof of Schur existence. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0)) :
    Not (Matrix.det (sylvesterVecCoeff m n A B) = 0) := by
  intro hdet
  obtain ⟨x, hxne, hxzero⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hinj :=
    sylvesterVecCoeff_schurDiagonal_mulVec_injective
      m n U A V B a b hU hV hA hB hsep
  have hxzero' : x = 0 := by
    apply hinj
    rw [hxzero, Matrix.mulVec_zero]
  exact hxne hxzero'

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), diagonal
    Schur-coordinate case: the supplied-factor vectorized Sylvester linear
    system has a unique solution for every vectorized right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_schurDiagonal_mulVec (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (c : Prod (Fin n) (Fin m) -> Real) :
    ∃! x : Prod (Fin n) (Fin m) -> Real,
      Matrix.mulVec (sylvesterVecCoeff m n A B) x = c := by
  have hinj :=
    sylvesterVecCoeff_schurDiagonal_mulVec_injective
      m n U A V B a b hU hV hA hB hsep
  have hsurj :=
    sylvesterVecCoeff_schurDiagonal_mulVec_surjective
      m n U A V B a b hU hV hA hB hsep
  obtain ⟨x, hx⟩ := hsurj c
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact hinj (by rw [hy, hx])

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: the practical componentwise error bound can use
    the actual nonsingular inverse of the vec/Kronecker Sylvester coefficient.
    This is an exact supplied-factor subcase; it does not assert Schur
    existence or a floating-point residual computation. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with a monotone estimated practical budget.  The
    exact inverse bound comes from the supplied Schur-diagonal certificate,
    while `PinvAbs'`, `Rhat'`, and `Ru'` may be any componentwise larger
    estimator inputs.  Scope: exact supplied factors only; this does not assert
    Schur existence, rounded residual arithmetic, or a LAPACK estimator. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: a scalar cap on the nonsingular-inverse practical
    budget gives the final practical relative max-entry error bound. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_scalar m n
      A B C X Xhat Rhat Ru
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with a monotone scalar cap on an estimated practical
    budget.  The exact nonsingular inverse is supplied by the Schur-diagonal
    certificate, while `PinvAbs'`, `Rhat'`, and `Ru'` may be any componentwise
    larger estimator inputs.  Scope: exact supplied factors only; this does not
    assert Schur existence, rounded residual arithmetic, or a LAPACK estimator. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget m n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_computed_residual_certificate_mono_scalar
      m n A B C X Xhat Rhat Rhat' Ru Ru'
      ((sylvesterVecCoeff m n A B)⁻¹)
      (sylvesterVecCoeffNonsingInvAbs m n A B)
      PinvAbs' eta hX
      (Matrix.nonsing_inv_mul (sylvesterVecCoeff m n A B)
        (isUnit_iff_ne_zero.mpr
          (sylvesterVecCoeff_schurDiagonal_det_ne_zero
            m n U A V B a b hU hV hA hB hsep)))
      (sylvesterVecCoeffNonsingInv_abs_le_invAbs m n A B)
      hPinvAbs_le hBudget hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form of the practical
    componentwise error bound.  Scope: exact supplied factors only; this does
    not assert Schur existence or a floating-point residual computation. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
      m n U A V B a b C X Xhat Rhat Ru hU hV hA hB hsep hX
      (And.intro hRu hRhat) hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form with a monotone
    estimated practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hsep hX (And.intro hRu hRhat)
      hPinvAbs_le hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form with a scalar cap
    on the practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
      m n U A V B a b C X Xhat Rhat Ru eta hU hV hA hB hsep hX
      (And.intro hRu hRhat) heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case: raw computed-residual budget form with monotone
    supplied estimates and a scalar cap on the estimated practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect m n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hsep hX (And.intro hRu hRhat)
      hPinvAbs_le hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model:
    if `Rhat = R(Xhat) + dR` and `|dR| <= Ru`, then the practical
    componentwise error bound follows using the nonsingular inverse of the
    supplied Schur-diagonal vec/Kronecker coefficient. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate
      m n U A V B a b C X Xhat Rhat Ru hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model and a monotone
    estimated practical budget.  This is an exact supplied-factor wrapper: no
    Schur existence, rounded residual arithmetic, or estimator proof is
    asserted. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      sylvesterVecMaxNorm m n
        (sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model and a scalar
    cap on the practical budget. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Ru dR : RMatFn m n) (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n
          (sylvesterVecCoeffNonsingInvAbs m n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar
      m n U A V B a b C X Xhat Rhat Ru eta hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat hRu hdR)
      heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), supplied diagonal
    Schur-coordinate case with an explicit residual error model and a monotone
    scalar cap on an estimated practical budget.  This remains an exact
    supplied-factor wrapper: no Schur existence, rounded residual arithmetic,
    or estimator proof is asserted. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono_scalar
    (m n : Nat)
    (U A : RMatFn m m) (V B : RMatFn n n)
    (a : Fin m -> Real) (b : Fin n -> Real)
    (C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn m n)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin m)) (Prod (Fin n) (Fin m)) Real)
    (eta : Real)
    (hU : IsOrthogonal m U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, Not (a i - b j = 0))
    (hX : IsSylvesterSolutionRect m n A B C X)
    (hRhat_model : forall i j,
      Rhat i j = sylvesterResidualRect m n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs m n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec m n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect m n Xhat) :
    sylvesterMaxEntryNormRect m n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect m n Xhat <=
      eta / sylvesterMaxEntryNormRect m n Xhat := by
  exact
    sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar
      m n U A V B a b C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      hU hV hA hB hsep hX
      (sylvesterComputedResidualBudget_of_error_model m n A B C Xhat Rhat Ru dR
        hRhat_model hRu hdR)
      hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), square supplied
    diagonal Schur-coordinate case: pairwise spectral-coordinate exclusion
    makes the vec/Kronecker Sylvester coefficient nonsingular.  The positive
    dimension hypothesis keeps this wrapper aligned with the square
    spectral-exclusion endpoints; the proof only needs the equivalent
    subtraction form used by the supplied-factor certificate above. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne_square
    (n : Nat)
    (U A : RMatFn n n) (V B : RMatFn n n)
    (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Matrix.det (sylvesterVecCoeff n n A B) ≠ 0 := by
  have _hn : 0 < n := hn
  have hsep_sub : forall i j, Not (a i - b j = 0) := by
    intro i j hzero
    exact hsep i j (sub_eq_zero.mp hzero)
  exact
    sylvesterVecCoeff_schurDiagonal_det_ne_zero
      n n U A V B a b hU hV hA hB hsep_sub

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square supplied diagonal
    Schur-coordinate case under pairwise spectral-coordinate exclusion:
    the raw computed-residual budget endpoint no longer needs a separately
    supplied determinant or gap certificate.  Scope: exact supplied factors
    only; this does not assert Schur existence or rounded residual arithmetic. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_entrywise_ne_computed_residual_budget
    (n : Nat)
    (U A : RMatFn n n) (V B : RMatFn n n)
    (a b : Fin n -> Real)
    (C X Xhat Rhat Ru : RMatFn n n)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne_square
        n U A V B a b hn hU hV hA hB hsep)
      hX hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square supplied diagonal
    Schur-coordinate case under pairwise spectral-coordinate exclusion:
    a Frobenius residual-error model supplies the uniform practical residual
    budget, while the spectral exclusion discharges nonsingularity.  Scope:
    exact supplied factors only; this does not assert Schur existence,
    rounded Schur arithmetic, or estimator production. -/
theorem sylvester_practical_error_bound_of_schurDiagonal_entrywise_ne_computed_residual_frobenius_error_model
    (n : Nat)
    (U A : RMatFn n n) (V B : RMatFn n n)
    (a b : Fin n -> Real)
    (C X Xhat Rhat dR : RMatFn n n) (rho : Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hrho : 0 <= rho)
    (hdR : frobNorm dR <= rho)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat
          (fun _ _ => rho)) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model
      n A B C X Xhat Rhat dR rho
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne_square
        n U A V B a b hn hU hV hA hB hsep)
      hX hRhat hrho hdR hXhat

-- ============================================================
-- Lyapunov specialization from Chapter 16.3
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.3:
    the Lyapunov equation is the Sylvester equation with `B = -A^T`. -/
theorem lyapunov_solution_iff_sylvester_special (n : Nat)
    (A C X : Fin n -> Fin n -> Real) :
    (forall i j, lyapunovOp n A X i j = C i j) <->
      (forall i j,
        sylvesterOp n A (fun i j => -matTranspose A i j) X i j = C i j) := by
  constructor
  case mp =>
    intro h i j
    have hij := h i j
    rw [lyapunovOp_eq_sylvesterOp] at hij
    exact hij
  case mpr =>
    intro h i j
    have hij := h i j
    rw [(lyapunovOp_eq_sylvesterOp n A X).symm] at hij
    exact hij

/-- Higham, 2nd ed., Chapter 16.3:
    positive separation for `sep(A,-A^T)` gives uniqueness for the Lyapunov
    equation. -/
theorem lyapunov_unique_solution_of_sep (n : Nat)
    (A : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (C X1 X2 : Fin n -> Fin n -> Real)
    (hX1 : forall i j, lyapunovOp n A X1 i j = C i j)
    (hX2 : forall i j, lyapunovOp n A X2 i j = C i j) :
    forall i j, X1 i j = X2 i j :=
  sep_implies_unique_solution n A (fun i j => -matTranspose A i j) sigma hSep
    C X1 X2
    ((lyapunov_solution_iff_sylvester_special n A C X1).mp hX1)
    ((lyapunov_solution_iff_sylvester_special n A C X2).mp hX2)

/-- If `X` solves a Lyapunov equation with a symmetric right-hand side, then
    `X^T` solves the same Lyapunov equation. -/
theorem lyapunov_transpose_solution_of_symmetric_rhs (n : Nat)
    (A C X : Fin n -> Fin n -> Real)
    (hC : IsSymmetric n C)
    (hX : forall i j, lyapunovOp n A X i j = C i j) :
    forall i j, lyapunovOp n A (matTranspose X) i j = C i j := by
  intro i j
  have hji := hX j i
  unfold lyapunovOp matMul matTranspose at hji
  unfold lyapunovOp matMul matTranspose
  calc
    (Finset.sum Finset.univ (fun k : Fin n => A i k * X j k)) +
        (Finset.sum Finset.univ (fun k : Fin n => X k i * A j k))
        = (Finset.sum Finset.univ (fun k : Fin n => X j k * A i k)) +
            (Finset.sum Finset.univ (fun k : Fin n => A j k * X k i)) := by
          have hleft :
              Finset.sum Finset.univ (fun k : Fin n => A i k * X j k) =
                Finset.sum Finset.univ (fun k : Fin n => X j k * A i k) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          have hright :
              Finset.sum Finset.univ (fun k : Fin n => X k i * A j k) =
                Finset.sum Finset.univ (fun k : Fin n => A j k * X k i) := by
            apply Finset.sum_congr rfl
            intro k _
            ring
          rw [hleft, hright]
    _ = (Finset.sum Finset.univ (fun k : Fin n => A j k * X k i)) +
          (Finset.sum Finset.univ (fun k : Fin n => X j k * A i k)) := by
          ring
    _ = C j i := hji
    _ = C i j := hC j i

/-- Higham, 2nd ed., Chapter 16.3:
    for a symmetric right-hand side, positive `sep(A,-A^T)` makes any
    Lyapunov solution symmetric, hence the solution is unique in the symmetric
    class. -/
theorem lyapunov_solution_symmetric_of_symmetric_rhs (n : Nat)
    (A C X : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A (fun i j => -matTranspose A i j) sigma)
    (hC : IsSymmetric n C)
    (hX : forall i j, lyapunovOp n A X i j = C i j) :
    IsSymmetric n X := by
  have hXT : forall i j, lyapunovOp n A (matTranspose X) i j = C i j :=
    lyapunov_transpose_solution_of_symmetric_rhs n A C X hC hX
  have huniq :=
    lyapunov_unique_solution_of_sep n A sigma hSep C X (matTranspose X) hX hXT
  intro i j
  exact huniq i j

/-- Higham, 2nd ed., Chapter 16.3: source-facing alias for the Lyapunov
    equation as the Sylvester special case `B = -A^T`. -/
alias H16_Lyapunov_solution_iff_sylvester_special :=
  lyapunov_solution_iff_sylvester_special

/-- Higham, 2nd ed., Chapter 16.3: source-facing alias for uniqueness of the
    Lyapunov equation from a `sep(A,-A^T)` lower-bound certificate. -/
alias H16_Lyapunov_unique_solution_of_sep :=
  lyapunov_unique_solution_of_sep

/-- Higham, 2nd ed., Chapter 16.3: source-facing alias for transposing a
    Lyapunov solution when the right-hand side is symmetric. -/
alias H16_Lyapunov_transpose_solution_of_symmetric_rhs :=
  lyapunov_transpose_solution_of_symmetric_rhs

/-- Higham, 2nd ed., Chapter 16.3: source-facing alias for symmetry of the
    unique Lyapunov solution with symmetric right-hand side. -/
alias H16_Lyapunov_solution_symmetric_of_symmetric_rhs :=
  lyapunov_solution_symmetric_of_symmetric_rhs

-- ============================================================
-- Separation infimum from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    feasible Frobenius ratios for `sep(A,B)`.  The nonzero condition is
    represented by `frobNormSq X` to match the existing square infrastructure. -/
def sylvesterSepRatios (n : Nat) (A B : Fin n -> Fin n -> Real) : Set Real :=
  {rho | exists X : Fin n -> Fin n -> Real,
    Not (frobNormSq X = 0) /\
      rho = frobNorm (sylvesterOp n A B X) / frobNorm X}

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    `sep(A,B)` modeled as the infimum of the nonzero Frobenius ratios.
    This records the exact source object without asserting that the infimum is
    attained by a minimizing matrix. -/
noncomputable def sylvesterSepInf (n : Nat) (A B : Fin n -> Fin n -> Real) : Real :=
  sInf (sylvesterSepRatios n A B)

/-- The exact `sep(A,B)` ratio set is bounded below by zero. -/
theorem sylvesterSepRatios_bddBelow (n : Nat) (A B : Fin n -> Fin n -> Real) :
    BddBelow (sylvesterSepRatios n A B) := by
  refine Exists.intro 0 ?_
  intro rho hrho
  cases hrho with
  | intro X hrest =>
      cases hrest with
      | intro _hX hrho_eq =>
          rw [hrho_eq]
          exact div_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- The exact infimum model of `sep(A,B)` from equation (16.26) is
    nonnegative, since every feasible Frobenius ratio is nonnegative. -/
theorem sylvesterSepInf_nonneg (n : Nat) (A B : Fin n -> Fin n -> Real) :
    0 <= sylvesterSepInf n A B := by
  unfold sylvesterSepInf
  apply Real.sInf_nonneg
  intro rho hrho
  rcases hrho with ⟨X, _hX, hrho_eq⟩
  rw [hrho_eq]
  exact div_nonneg (frobNorm_nonneg _) (frobNorm_nonneg _)

/-- Every nonzero Frobenius ratio is above the infimum model of `sep(A,B)`. -/
theorem sylvesterSepInf_le_ratio (n : Nat) (A B X : Fin n -> Fin n -> Real)
    (hX : Not (frobNormSq X = 0)) :
    sylvesterSepInf n A B <= frobNorm (sylvesterOp n A B X) / frobNorm X := by
  unfold sylvesterSepInf
  exact csInf_le (sylvesterSepRatios_bddBelow n A B)
    (Exists.intro X (And.intro hX rfl))

/-- In positive dimension, the feasible ratio set in the infimum model of
    `sep(A,B)` is nonempty: a single-entry test matrix is a nonzero witness. -/
theorem sylvesterSepRatios_nonempty_of_pos_dim (n : Nat)
    (A B : Fin n -> Fin n -> Real) (hn : 0 < n) :
    (sylvesterSepRatios n A B).Nonempty := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let E : Fin n -> Fin n -> Real :=
    fun r c => if i = r /\ i = c then (1 : Real) else 0
  refine ⟨frobNorm (sylvesterOp n A B E) / frobNorm E, ?_⟩
  refine ⟨E, ?_, rfl⟩
  have hrect : frobNormSqRect E = (1 : Real) ^ 2 := by
    simpa [E] using frobNormSqRect_single_left i i (1 : Real)
  rw [frobNormSqRect_eq_frobNormSq] at hrect
  norm_num at hrect
  intro hzero
  rw [hzero] at hrect
  norm_num at hrect

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered abbreviation for the feasible Frobenius-ratio set in the
    exact `sep(A,B)` infimum model. -/
abbrev H16_eq16_26_sylvesterSepRatios := sylvesterSepRatios

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered abbreviation for the exact `sep(A,B)` infimum model. -/
noncomputable abbrev H16_eq16_26_sylvesterSepInf := sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for lower-boundedness of the feasible ratio set. -/
alias H16_eq16_26_sylvesterSepRatios_bddBelow :=
  sylvesterSepRatios_bddBelow

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for nonnegativity of the exact `sep(A,B)` infimum
    model. -/
alias H16_eq16_26_sylvesterSepInf_nonneg :=
  sylvesterSepInf_nonneg

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias saying the exact `sep(A,B)` infimum is below every
    feasible nonzero Frobenius ratio. -/
alias H16_eq16_26_sylvesterSepInf_le_ratio :=
  sylvesterSepInf_le_ratio

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for nonemptiness of the feasible ratio set in
    positive dimension. -/
alias H16_eq16_26_sylvesterSepRatios_nonempty_of_pos_dim :=
  sylvesterSepRatios_nonempty_of_pos_dim

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), diagonal case:
    a uniform lower bound on all diagonal differences gives a Frobenius
    `SepLowerBound` certificate for the diagonal Sylvester operator. -/
theorem SepLowerBound_diagonal_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    SepLowerBound n (Matrix.diagonal a) (Matrix.diagonal b) sigma := by
  refine ⟨hsigma, ?_⟩
  intro X _hX
  have hop :
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X =
        fun i j => (a i - b j) * X i j := by
    rw [← sylvesterOpRect_square_eq_sylvesterOp]
    ext i j
    exact sylvesterOpRect_diagonal_apply n n a b X i j
  rw [hop]
  unfold frobNormSq
  calc
    sigma ^ 2 * (∑ i : Fin n, ∑ j : Fin n, X i j ^ 2)
        = ∑ i : Fin n, ∑ j : Fin n, sigma ^ 2 * X i j ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ <= ∑ i : Fin n, ∑ j : Fin n, ((a i - b j) * X i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      have hleft : -|a i - b j| <= sigma := by
        linarith [abs_nonneg (a i - b j), le_of_lt hsigma]
      have hsq_abs : sigma ^ 2 <= |a i - b j| ^ 2 :=
        sq_le_sq' hleft (hgap i j)
      have hsq : sigma ^ 2 <= (a i - b j) ^ 2 := by
        simpa [sq_abs] using hsq_abs
      have hterm :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg (X i j))
      simpa [mul_pow] using hterm

/-- Higham, 2nd ed., Chapter 16.1 and equation (16.3), diagonal case:
    a common diagonal entry gives a nonzero element of the diagonal Sylvester
    operator kernel. -/
theorem exists_nonzero_sylvesterOp_diagonal_kernel_of_common_entry (n : Nat)
    (a b : Fin n -> Real) (i j : Fin n) (hij : a i = b j) :
    exists X : Fin n -> Fin n -> Real,
      Not (frobNormSq X = 0) /\
        sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X = 0 := by
  classical
  let E : Fin n -> Fin n -> Real :=
    fun r c => if i = r /\ j = c then (1 : Real) else 0
  refine ⟨E, ?_, ?_⟩
  · have hrect : frobNormSqRect E = (1 : Real) ^ 2 :=
      frobNormSqRect_single_left i j (1 : Real)
    rw [frobNormSqRect_eq_frobNormSq] at hrect
    norm_num at hrect
    intro hzero
    rw [hzero] at hrect
    norm_num at hrect
  · have hrect :
        sylvesterOpRect n n (Matrix.diagonal a) (Matrix.diagonal b) E = 0 := by
      ext r c
      rw [sylvesterOpRect_diagonal_apply]
      by_cases hrc : i = r /\ j = c
      · rcases hrc with ⟨hir, hjc⟩
        subst r
        subst c
        simp [E, hij]
      · simp [E, hrc]
    simpa [sylvesterOpRect_square_eq_sylvesterOp] using hrect

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), diagonal case:
    a common diagonal entry forces the exact infimum model of `sep(A,B)` to
    vanish. -/
theorem sylvesterSepInf_diagonal_eq_zero_of_common_entry (n : Nat)
    (a b : Fin n -> Real) (i j : Fin n) (hij : a i = b j) :
    sylvesterSepInf n (Matrix.diagonal a) (Matrix.diagonal b) = 0 := by
  obtain ⟨X, hXne, hker⟩ :=
    exists_nonzero_sylvesterOp_diagonal_kernel_of_common_entry n a b i j hij
  have hle :=
    sylvesterSepInf_le_ratio n (Matrix.diagonal a) (Matrix.diagonal b) X hXne
  have hratio :
      frobNorm (sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X) /
          frobNorm X = 0 := by
    rw [hker]
    simp [frobNorm]
  exact le_antisymm (by simpa [hratio] using hle)
    (sylvesterSepInf_nonneg n (Matrix.diagonal a) (Matrix.diagonal b))

/-- A positive `SepLowerBound` certificate is below the exact infimum model,
    whenever the feasible ratio set is nonempty. -/
theorem SepLowerBound_le_sylvesterSepInf_of_nonempty (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    sigma <= sylvesterSepInf n A B := by
  unfold sylvesterSepInf
  apply le_csInf hne
  intro rho hrho
  cases hrho with
  | intro X hrest =>
      cases hrest with
      | intro hX hrho_eq =>
          rw [hrho_eq]
          have hXsq_pos : 0 < frobNormSq X :=
            lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hX)
          have hXnorm_pos : 0 < frobNorm X := by
            have hs : 0 < frobNorm X ^ 2 := by
              rw [frobNorm_sq]
              exact hXsq_pos
            have hne_norm : Not (frobNorm X = 0) := sq_pos_iff.mp hs
            exact lt_of_le_of_ne (frobNorm_nonneg X) (Ne.symm hne_norm)
          have hsq := hSep.2 X hX
          have hsq_norms : (sigma * frobNorm X) ^ 2 <=
              frobNorm (sylvesterOp n A B X) ^ 2 := by
            rw [mul_pow, frobNorm_sq, frobNorm_sq]
            exact hsq
          have hleft_nonneg : 0 <= sigma * frobNorm X :=
            mul_nonneg (le_of_lt hSep.1) (frobNorm_nonneg X)
          have hright_nonneg : 0 <= frobNorm (sylvesterOp n A B X) :=
            frobNorm_nonneg _
          have hnorm_le :
              sigma * frobNorm X <= frobNorm (sylvesterOp n A B X) := by
            nlinarith [sq_nonneg
              (frobNorm (sylvesterOp n A B X) - sigma * frobNorm X)]
          have hXnorm_ne : Not (frobNorm X = 0) := ne_of_gt hXnorm_pos
          calc
            sigma = sigma * frobNorm X / frobNorm X := by
              field_simp [hXnorm_ne]
            _ <= frobNorm (sylvesterOp n A B X) / frobNorm X := by
              exact div_le_div_of_nonneg_right hnorm_le (le_of_lt hXnorm_pos)

/-- In positive dimension, a positive `SepLowerBound` certificate is below the
    exact infimum model of `sep(A,B)`. -/
theorem SepLowerBound_le_sylvesterSepInf_of_pos_dim (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) (hn : 0 < n) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A B sigma hSep
      (sylvesterSepRatios_nonempty_of_pos_dim n A B hn)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), diagonal case:
    a uniform diagonal-difference gap is below the exact infimum model of
    `sep(A,B)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_diagonal_ge_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hne : (sylvesterSepRatios n (Matrix.diagonal a)
      (Matrix.diagonal b)).Nonempty) :
    sigma <= sylvesterSepInf n (Matrix.diagonal a) (Matrix.diagonal b) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n
      (Matrix.diagonal a) (Matrix.diagonal b) sigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), diagonal case:
    in positive dimension, a uniform diagonal-difference gap is below the exact
    infimum model of `sep(A,B)`. -/
theorem sylvesterSepInf_diagonal_ge_of_entrywise_abs_ge_of_pos_dim (n : Nat)
    (a b : Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n (Matrix.diagonal a) (Matrix.diagonal b) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n
      (Matrix.diagonal a) (Matrix.diagonal b) sigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hsigma hgap) hn

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the diagonal uniform-gap `SepLowerBound` certificate. -/
alias H16_eq16_26_SepLowerBound_diagonal_of_entrywise_abs_ge :=
  SepLowerBound_diagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for a common diagonal entry giving a nonzero diagonal-operator
    kernel witness. -/
alias H16_eq16_26_exists_nonzero_sylvesterOp_diagonal_kernel_of_common_entry :=
  exists_nonzero_sylvesterOp_diagonal_kernel_of_common_entry

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for common diagonal entries forcing exact `sep` to vanish. -/
alias H16_eq16_26_sylvesterSepInf_diagonal_eq_zero_of_common_entry :=
  sylvesterSepInf_diagonal_eq_zero_of_common_entry

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the diagonal uniform-gap exact-infimum lower-bound route from
    nonempty feasible ratios. -/
alias H16_eq16_26_sylvesterSepInf_diagonal_ge_of_entrywise_abs_ge :=
  sylvesterSepInf_diagonal_ge_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the positive-dimensional diagonal uniform-gap exact-infimum
    lower-bound route. -/
alias H16_eq16_26_sylvesterSepInf_diagonal_ge_of_entrywise_abs_ge_of_pos_dim :=
  sylvesterSepInf_diagonal_ge_of_entrywise_abs_ge_of_pos_dim

/-- Any positive number below the exact infimum model of `sep(A,B)` is a valid
    `SepLowerBound` certificate for the existing perturbation infrastructure. -/
theorem SepLowerBound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    SepLowerBound n A B sigma := by
  refine And.intro hsigma ?_
  intro X hX
  have hXsq_pos : 0 < frobNormSq X :=
    lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hX)
  have hXnorm_pos : 0 < frobNorm X := by
    have hs : 0 < frobNorm X ^ 2 := by
      rw [frobNorm_sq]
      exact hXsq_pos
    have hne_norm : Not (frobNorm X = 0) := sq_pos_iff.mp hs
    exact lt_of_le_of_ne (frobNorm_nonneg X) (Ne.symm hne_norm)
  have hratio :
      sigma <= frobNorm (sylvesterOp n A B X) / frobNorm X :=
    le_trans hle (sylvesterSepInf_le_ratio n A B X hX)
  have hnorm_le :
      sigma * frobNorm X <= frobNorm (sylvesterOp n A B X) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hratio (le_of_lt hXnorm_pos)
    have hXnorm_ne : Not (frobNorm X = 0) := ne_of_gt hXnorm_pos
    have hcancel :
        frobNorm (sylvesterOp n A B X) / frobNorm X * frobNorm X =
          frobNorm (sylvesterOp n A B X) := by
      field_simp [hXnorm_ne]
    simpa [hcancel] using hmul
  have hleft_nonneg : 0 <= sigma * frobNorm X :=
    mul_nonneg (le_of_lt hsigma) (frobNorm_nonneg X)
  have hright_nonneg : 0 <= frobNorm (sylvesterOp n A B X) :=
    frobNorm_nonneg _
  have hsq_norms : (sigma * frobNorm X) ^ 2 <=
      frobNorm (sylvesterOp n A B X) ^ 2 := by
    nlinarith [sq_nonneg
      (frobNorm (sylvesterOp n A B X) - sigma * frobNorm X)]
  rw [mul_pow, frobNorm_sq, frobNorm_sq] at hsq_norms
  exact hsq_norms

/-- For a nonempty feasible ratio set, the existing positive lower-bound
    predicate is equivalent to being a positive lower bound of the exact
    infimum model.  This is an infimum bridge, not an attained-minimum claim. -/
theorem SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    SepLowerBound n A B sigma <->
      0 < sigma /\ sigma <= sylvesterSepInf n A B := by
  constructor
  · intro hSep
    exact And.intro hSep.1
      (SepLowerBound_le_sylvesterSepInf_of_nonempty n A B sigma hSep hne)
  · intro h
    exact SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma h.1 h.2

/-- In positive dimension, the existing positive lower-bound predicate is
    equivalent to being a positive lower bound of the exact infimum model. -/
theorem SepLowerBound_iff_pos_le_sylvesterSepInf_of_pos_dim (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real) (hn : 0 < n) :
    SepLowerBound n A B sigma <->
      0 < sigma /\ sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty n A B sigma
      (sylvesterSepRatios_nonempty_of_pos_dim n A B hn)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for transferring a `SepLowerBound` certificate to
    the exact `sep(A,B)` infimum model when the feasible ratio set is
    nonempty. -/
alias H16_eq16_26_SepLowerBound_le_sylvesterSepInf_of_nonempty :=
  SepLowerBound_le_sylvesterSepInf_of_nonempty

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for transferring a `SepLowerBound` certificate to
    the exact `sep(A,B)` infimum model in positive dimension. -/
alias H16_eq16_26_SepLowerBound_le_sylvesterSepInf_of_pos_dim :=
  SepLowerBound_le_sylvesterSepInf_of_pos_dim

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias turning a positive lower bound on the exact
    `sep(A,B)` infimum into the theorem-facing `SepLowerBound` certificate. -/
alias H16_eq16_26_SepLowerBound_of_pos_le_sylvesterSepInf :=
  SepLowerBound_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for the nonempty-set equivalence between
    `SepLowerBound` and a positive lower bound on the exact infimum model. -/
alias H16_eq16_26_SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty :=
  SepLowerBound_iff_pos_le_sylvesterSepInf_of_nonempty

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26):
    source-numbered alias for the positive-dimensional equivalence between
    `SepLowerBound` and a positive lower bound on the exact infimum model. -/
alias H16_eq16_26_SepLowerBound_iff_pos_le_sylvesterSepInf_of_pos_dim :=
  SepLowerBound_iff_pos_le_sylvesterSepInf_of_pos_dim

private theorem sylvesterVecCoeff_det_ne_zero_of_sepLowerBound (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hSep : SepLowerBound n A B sigma) :
    Not ((sylvesterVecCoeff n n A B).det = 0) := by
  classical
  intro hdet
  have hker :=
    (Matrix.exists_mulVec_eq_zero_iff
      (M := sylvesterVecCoeff n n A B)).mpr hdet
  cases hker with
  | intro x hx =>
      have hxne := hx.1
      have hxzero := hx.2
      let X : RMatFn n n := fun i j => x (j, i)
      have hvecX : Matrix.vec X = x := by
        ext p
        rfl
      have hXne : Not (frobNormSq X = 0) := by
        intro hsq
        apply hxne
        ext p
        have hfrob0 : frobNorm X = 0 := by
          rw [frobNorm_eq_sqrt_frobNormSq,
            Real.sqrt_eq_zero (frobNormSq_nonneg X)]
          exact hsq
        have hentries := (frobNorm_eq_zero_iff X).mp hfrob0
        cases p with
        | mk j i =>
            simpa [X] using hentries i j
      have hOpZero : sylvesterOp n A B X = 0 := by
        have hxzero' :
            Matrix.mulVec (sylvesterVecCoeff n n A B) (Matrix.vec X) = 0 := by
          simpa [hvecX] using hxzero
        have hsyl : IsSylvesterSolutionRect n n A B (0 : RMatFn n n) X :=
          (sylvester_vec_system_iff_solution n n A B (0 : RMatFn n n) X).mp
            (by simpa using hxzero')
        ext i j
        have hrect := hsyl i j
        simpa [sylvesterOpRect_square_eq_sylvesterOp n A B X] using hrect
      have hle := hSep.2 X hXne
      rw [hOpZero] at hle
      have hzero : frobNormSq (0 : RMatFn n n) = 0 := by
        unfold frobNormSq
        simp
      rw [hzero] at hle
      have hXpos : 0 < frobNormSq X :=
        lt_of_le_of_ne (frobNormSq_nonneg X) (Ne.symm hXne)
      have hsig2pos : 0 < sigma ^ 2 := sq_pos_of_pos hSep.1
      exact (not_le_of_gt (mul_pos hsig2pos hXpos)) hle

private theorem sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf (n : Nat)
    (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B) :
    Not ((sylvesterVecCoeff n n A B).det = 0) := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hsigma hle)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), square arbitrary-
    coefficient endpoint: a supplied positive `SepLowerBound` certificate
    discharges vec/Kronecker nonsingularity for the practical computed-residual
    certificate. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate scalar endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute endpoint for a practical computed-residual
    certificate.  The source separation certificate discharges vec/Kronecker
    nonsingularity, and no positive `||Xhat||` denominator is needed. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute scalar endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute monotone certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), source
    `SepLowerBound` absolute monotone scalar certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint with monotone supplied inverse and residual
    estimates. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate raw budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate scalar endpoint for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate raw budget endpoint with monotone supplied estimates and a
    scalar cap. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute raw-budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute raw-budget endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate endpoint for an explicit computed-residual error model. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate scalar endpoint for an explicit computed-residual error
    model. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hSep : SepLowerBound n A B sigma)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    certificate error-model endpoint with monotone supplied estimates and a
    scalar cap. -/
theorem sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute residual error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), `SepLowerBound`
    absolute residual error-model endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real} (hSep : SepLowerBound n A B sigma)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_sepLowerBound n A B sigma hSep)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum lower-bound
    endpoint for the practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum scalar
    endpoint for a practical computed-residual certificate. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute scalar endpoint for a practical computed-residual
    certificate. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute monotone certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    lower-bound absolute monotone scalar certificate endpoint. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    with monotone supplied inverse and residual estimates. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hBudget : IsSylvesterComputedResidualBudget n n A B C Xhat Rhat Ru)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hBudget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget
      n A B C X Xhat Rhat Ru
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum raw
    budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum scalar
    endpoint for the raw computed-residual budget form. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar
      n A B C X Xhat Rhat Ru eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum raw budget
    endpoint with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRu hRhat_budget hPinvAbs_le hRhat hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    raw-budget endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    raw-budget endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRu : forall i j, 0 <= Ru i j)
    (hRhat_budget : forall i j,
      |sylvesterResidualRect n n A B C Xhat i j - Rhat i j| <= Ru i j)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRu hRhat_budget hRhat hRu_le heta hcomponent

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum endpoint
    for an explicit computed-residual error model. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru) /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model
      n A B C X Xhat Rhat Ru dR
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRhat hRu hdR hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum scalar
    endpoint for an explicit computed-residual error model. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar
    (n : Nat)
    (A B C X Xhat Rhat Ru dR : RMatFn n n) {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hRhat : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (heta : 0 <= eta)
    (hcomponent : forall p,
      sylvesterPracticalBudgetVec n n
          (sylvesterVecCoeffNonsingInvAbs n n A B) Rhat Ru p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar
      n A B C X Xhat Rhat Ru dR eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hRhat hRu hdR heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') /
        sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum
    error-model endpoint with monotone supplied estimates and a scalar cap. -/
theorem sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta)
    (hXhat : 0 < sylvesterMaxEntryNormRect n n Xhat) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) /
        sylvesterMaxEntryNormRect n n Xhat <=
      eta / sylvesterMaxEntryNormRect n n Xhat := by
  exact
    sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent hXhat

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    residual error-model endpoint with monotone supplied estimates. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <=
      sylvesterVecMaxNorm n n
        (sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru') := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs'
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29), exact-infimum absolute
    residual error-model endpoint with monotone estimates and a scalar cap. -/
theorem sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar
    (n : Nat)
    (A B C X Xhat Rhat Rhat' Ru Ru' dR : RMatFn n n)
    {sigma : Real}
    (hsigma : 0 < sigma) (hle : sigma <= sylvesterSepInf n A B)
    (PinvAbs' :
      Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (eta : Real)
    (hX : IsSylvesterSolutionRect n n A B C X)
    (hPinvAbs_le : forall p q,
      sylvesterVecCoeffNonsingInvAbs n n A B p q <= PinvAbs' p q)
    (hRhat_eq : forall i j,
      Rhat i j = sylvesterResidualRect n n A B C Xhat i j + dR i j)
    (hRu : forall i j, 0 <= Ru i j)
    (hdR : forall i j, |dR i j| <= Ru i j)
    (hRhat_le : forall i j, |Rhat i j| <= |Rhat' i j|)
    (hRu_le : forall i j, Ru i j <= Ru' i j)
    (heta : 0 <= eta)
    (hcomponent :
      forall p, sylvesterPracticalBudgetVec n n PinvAbs' Rhat' Ru' p <= eta) :
    sylvesterMaxEntryNormRect n n (fun i j => X i j - Xhat i j) <= eta := by
  exact
    sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar
      n A B C X Xhat Rhat Rhat' Ru Ru' dR PinvAbs' eta
      (sylvesterVecCoeff_det_ne_zero_of_pos_le_sylvesterSepInf
        n A B sigma hsigma hle)
      hX hPinvAbs_le hRhat_eq hRu hdR hRhat_le hRu_le heta hcomponent

-- ============================================================
-- Equation (16.29) source-numbered practical endpoint aliases
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the rectangular determinant-nonzero practical certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the rectangular determinant-nonzero denominator-free absolute
    practical certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect :=
  sylvester_practical_abs_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_rect

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the rectangular determinant-nonzero raw residual-budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_rect :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_rect

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the rectangular determinant-nonzero residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_rect :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_rect

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero practical certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero scalar residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero Frobenius residual-error endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero scalar Frobenius residual-error endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone Frobenius residual-error endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the determinant-nonzero monotone scalar Frobenius residual-error
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_vecCoeff_det_ne_zero_computed_residual_frobenius_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal practical certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_certificate :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal monotone scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_budget :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal monotone scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_error_model :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal scalar residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal monotone residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the diagonal monotone scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_diagonal_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal scalar residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the supplied Schur-diagonal monotone scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_schurDiagonal_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_scalar :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` absolute monotone scalar certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar :=
  sylvester_practical_abs_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` scalar residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the `SepLowerBound` monotone scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_sepLowerBound_computed_residual_error_model_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` scalar certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute scalar certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute monotone
    certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` absolute monotone scalar
    certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar :=
  sylvester_practical_abs_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone certificate endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone scalar certificate
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_certificate_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` scalar raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone raw budget endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone scalar raw budget
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_budget_mono_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` residual error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` scalar error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_scalar

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone error-model endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono

/-- Higham, 2nd ed., Chapter 16.4, equation (16.29): source-numbered
    alias for the positive exact-`sylvesterSepInf` monotone scalar error-model
    endpoint. -/
alias H16_eq16_29_sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar :=
  sylvester_practical_error_bound_of_pos_le_sylvesterSepInf_computed_residual_error_model_mono_scalar

-- ============================================================
-- Perturbation source wrappers from Chapter 16.3
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    a supplied exact `SepLowerBound` certificate instantiates the Frobenius
    first-order Sylvester perturbation bound. -/
theorem sylvester_perturbation_bound_of_sepLowerBound (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound n A B X dA dB dC dX sigma hSep.1 hSep
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    the relative Sylvester perturbation bound follows from a supplied exact
    `SepLowerBound` certificate. -/
theorem sylvester_relative_perturbation_of_sepLowerBound (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation n A B X dA dB dC dX sigma hSep.1 hSep
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    total Frobenius first-order Sylvester perturbation bound from a supplied
    exact `SepLowerBound` certificate.

    This version removes the nonzero perturbation side condition by proving
    the zero-perturbation case directly. -/
theorem sylvester_perturbation_bound_of_sepLowerBound_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  by_cases hdX_sq : frobNormSq dX = 0
  · have hdX : frobNorm dX = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hdX_sq]
    have hSigma : 0 < sigma := hSep.1
    have hInv : 0 <= (1 / sigma) := by positivity
    have hAlphaBeta : 0 <= alpha + beta := add_nonneg hAlpha hBeta
    have hScale : 0 <= (alpha + beta) * frobNorm X :=
      mul_nonneg hAlphaBeta (frobNorm_nonneg X)
    have hBudget : 0 <= (alpha + beta) * frobNorm X + gamma :=
      add_nonneg hScale hGamma
    rw [hdX]
    exact mul_nonneg (mul_nonneg hInv hBudget) hEps
  · exact
      sylvester_perturbation_bound_of_sepLowerBound n A B X dA dB dC dX sigma
        hSep alpha beta gamma eps hAlpha hBeta hGamma hEps
        hdA hdB hdC hLin hdX_sq

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    total relative Sylvester perturbation bound from a supplied exact
    `SepLowerBound` certificate.

    The absolute total theorem handles zero perturbation; this wrapper divides
    by the positive Frobenius norm of the exact solution. -/
theorem sylvester_relative_perturbation_of_sepLowerBound_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  have hAbs :=
    sylvester_perturbation_bound_of_sepLowerBound_total n A B X dA dB dC dX
      sigma hSep alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin
  unfold condSylvester
  rw [div_le_iff₀ hX_pos]
  calc
    frobNorm dX <=
        (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := hAbs
    _ = ((alpha + beta) * frobNorm X + gamma) /
          (sigma * frobNorm X) * eps * frobNorm X := by
        field_simp [ne_of_gt hSep.1, ne_of_gt hX_pos]

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    an exact-infimum lower bound on `sep(A,B)` instantiates the Frobenius
    first-order Sylvester perturbation bound. -/
theorem sylvester_perturbation_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sepLowerBound n A B X dA dB dC dX sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    the relative Sylvester perturbation bound follows from an exact-infimum
    lower bound on `sep(A,B)`. -/
theorem sylvester_relative_perturbation_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sepLowerBound n A B X dA dB dC dX sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    total Frobenius first-order Sylvester perturbation bound from a positive
    lower bound on the exact infimum model of `sep(A,B)`. -/
theorem sylvester_perturbation_bound_of_pos_le_sylvesterSepInf_total (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sepLowerBound_total n A B X dA dB dC dX
      sigma (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26):
    total relative Sylvester perturbation bound from a positive lower bound on
    the exact infimum model of `sep(A,B)`. -/
theorem sylvester_relative_perturbation_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sepLowerBound_total n
      A B X dA dB dC dX sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26),
    diagonal case: a uniform diagonal-difference gap instantiates the
    Frobenius first-order Sylvester perturbation bound. -/
theorem sylvester_perturbation_bound_diagonal_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound n
      (Matrix.diagonal a) (Matrix.diagonal b) X dA dB dC dX sigma hSigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26),
    diagonal case: the relative Sylvester perturbation bound follows from a
    uniform lower bound on all diagonal differences. -/
theorem sylvester_relative_perturbation_diagonal_of_entrywise_abs_ge
    (n : Nat)
    (a b : Fin n -> Real) (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b) X
        alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation n
      (Matrix.diagonal a) (Matrix.diagonal b) X dA dB dC dX sigma hSigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26),
    diagonal case: total Frobenius first-order perturbation bound from a
    uniform lower bound on all diagonal differences. -/
theorem sylvester_perturbation_bound_diagonal_of_entrywise_abs_ge_total (n : Nat)
    (a b : Fin n -> Real) (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_sepLowerBound_total n
      (Matrix.diagonal a) (Matrix.diagonal b) X dA dB dC dX sigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25) and (16.26),
    diagonal case: total relative perturbation bound from a uniform lower
    bound on all diagonal differences. -/
theorem sylvester_relative_perturbation_diagonal_of_entrywise_abs_ge_total
    (n : Nat)
    (a b : Fin n -> Real) (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b) X
        alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_sepLowerBound_total n
      (Matrix.diagonal a) (Matrix.diagonal b) X dA dB dC dX sigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for the total exact-infimum Sylvester perturbation
    bound. -/
alias H16_eq16_25_sylvester_perturbation_bound_of_pos_le_sylvesterSepInf_total :=
  sylvester_perturbation_bound_of_pos_le_sylvesterSepInf_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for the total relative exact-infimum Sylvester
    perturbation bound. -/
alias H16_eq16_25_sylvester_relative_perturbation_of_pos_le_sylvesterSepInf_total :=
  sylvester_relative_perturbation_of_pos_le_sylvesterSepInf_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for the total diagonal-gap Sylvester perturbation
    bound. -/
alias H16_eq16_25_sylvester_perturbation_bound_diagonal_of_entrywise_abs_ge_total :=
  sylvester_perturbation_bound_diagonal_of_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for the total relative diagonal-gap Sylvester
    perturbation bound. -/
alias H16_eq16_25_sylvester_relative_perturbation_diagonal_of_entrywise_abs_ge_total :=
  sylvester_relative_perturbation_diagonal_of_entrywise_abs_ge_total

-- ============================================================
-- A posteriori source wrapper from Chapter 16.4
-- ============================================================

/-- Higham, 2nd ed., Chapter 16, equation (16.28), relative source form:
    divide the existing Frobenius residual-error bound by the norm of the
    exact solution. -/
theorem sylvester_relative_aposteriori_bound (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X :=
  div_le_div_of_nonneg_right
    (sylvester_aposteriori_bound n A B C X Xhat sigma hSigma hSep hExact hE_ne)
    (le_of_lt hX_pos)

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    a supplied exact `SepLowerBound` certificate instantiates the Frobenius
    a posteriori error-residual bound. -/
theorem sylvester_aposteriori_bound_of_sepLowerBound (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound n A B C X Xhat sigma hSep.1 hSep hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    the source-shaped relative a posteriori bound follows from a supplied
    exact `SepLowerBound` certificate. -/
theorem sylvester_relative_aposteriori_bound_of_sepLowerBound (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound n A B C X Xhat sigma hSep.1 hSep
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    an exact-infimum lower bound on `sep(A,B)` instantiates the Frobenius
    a posteriori error-residual bound. -/
theorem sylvester_aposteriori_bound_of_pos_le_sylvesterSepInf (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sepLowerBound n A B C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    the source-shaped relative a posteriori bound follows from an
    exact-infimum lower bound on `sep(A,B)`. -/
theorem sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sepLowerBound n A B C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered alias
    for the supplied `SepLowerBound` a posteriori residual-error endpoint. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_sepLowerBound :=
  sylvester_aposteriori_bound_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered alias
    for the relative supplied `SepLowerBound` a posteriori endpoint. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_sepLowerBound :=
  sylvester_relative_aposteriori_bound_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the exact-infimum a posteriori endpoint. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_pos_le_sylvesterSepInf :=
  sylvester_aposteriori_bound_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the relative exact-infimum a posteriori endpoint. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf :=
  sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total source-facing Sylvester a posteriori error-residual bound from a
    supplied exact `SepLowerBound` certificate.

    This version removes the nonzero error side condition by proving the
    zero-error case directly. -/
theorem sylvester_aposteriori_bound_of_sepLowerBound_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  by_cases hE_ne :
      Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)
  case pos =>
    exact
      sylvester_aposteriori_bound_of_sepLowerBound n A B C X Xhat sigma
        hSep hExact hE_ne
  case neg =>
    have hE_sq :
        frobNormSq (fun i j => X i j - Xhat i j) = 0 :=
      Classical.not_not.mp hE_ne
    have hE :
        frobNorm (fun i j => X i j - Xhat i j) = 0 := by
      simp [frobNorm_eq_sqrt_frobNormSq, hE_sq]
    have hsigma : 0 < sigma := hSep.1
    rw [hE]
    exact mul_nonneg (by positivity) (frobNorm_nonneg _)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28):
    total relative Sylvester a posteriori error-residual bound from a supplied
    exact `SepLowerBound` certificate.

    The absolute total theorem handles zero error; this wrapper divides by
    the positive Frobenius norm of the exact solution. -/
theorem sylvester_relative_aposteriori_bound_of_sepLowerBound_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSep : SepLowerBound n A B sigma)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  have hAbs :=
    sylvester_aposteriori_bound_of_sepLowerBound_total n A B C X Xhat sigma
      hSep hExact
  exact div_le_div_of_nonneg_right hAbs (le_of_lt hX_pos)

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total Sylvester a posteriori error-residual bound from a positive lower
    bound on the exact infimum model of `sep(A,B)`.

    This routes through the total `SepLowerBound` wrapper. -/
theorem sylvester_aposteriori_bound_of_pos_le_sylvesterSepInf_total (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sepLowerBound_total n A B C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    total relative Sylvester a posteriori error-residual bound from a positive
    lower bound on the exact infimum model of `sep(A,B)`.

    This routes through the total `SepLowerBound` wrapper and divides by
    `||X||_F`. -/
theorem sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total
    (n : Nat)
    (A B C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hle : sigma <= sylvesterSepInf n A B)
    (hExact : forall i j, sylvesterOp n A B X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) * frobNorm (sylvesterResidual n A B C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sepLowerBound_total n
      A B C X Xhat sigma
      (SepLowerBound_of_pos_le_sylvesterSepInf n A B sigma hSigma hle)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total `SepLowerBound` a posteriori residual-error endpoint. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_sepLowerBound_total :=
  sylvester_aposteriori_bound_of_sepLowerBound_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative `SepLowerBound` a posteriori residual-error endpoint. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_sepLowerBound_total :=
  sylvester_relative_aposteriori_bound_of_sepLowerBound_total

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the total exact-infimum a posteriori endpoint. -/
alias H16_eq16_28_sylvester_aposteriori_bound_of_pos_le_sylvesterSepInf_total :=
  sylvester_aposteriori_bound_of_pos_le_sylvesterSepInf_total

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28):
    source-numbered alias for the total relative exact-infimum a posteriori endpoint. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total :=
  sylvester_relative_aposteriori_bound_of_pos_le_sylvesterSepInf_total

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: a uniform diagonal-difference gap instantiates the
    Frobenius a posteriori error-residual bound. -/
theorem sylvester_aposteriori_bound_diagonal_of_entrywise_abs_ge (n : Nat)
    (a b : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0)) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) := by
  exact
    sylvester_aposteriori_bound n (Matrix.diagonal a) (Matrix.diagonal b)
      C X Xhat sigma hSigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      hExact hE_ne

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: the source-shaped relative a posteriori bound follows from
    a uniform lower bound on all diagonal differences. -/
theorem sylvester_relative_aposteriori_bound_diagonal_of_entrywise_abs_ge
    (n : Nat)
    (a b : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hE_ne : Not (frobNormSq (fun i j => X i j - Xhat i j) = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
          frobNorm
            (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat sigma hSigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      hExact hE_ne hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered alias
    for the diagonal entrywise-gap a posteriori endpoint. -/
alias H16_eq16_28_sylvester_aposteriori_bound_diagonal_of_entrywise_abs_ge :=
  sylvester_aposteriori_bound_diagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered alias
    for the relative diagonal entrywise-gap a posteriori endpoint. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_diagonal_of_entrywise_abs_ge :=
  sylvester_relative_aposteriori_bound_diagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: the total Frobenius a posteriori error-residual bound
    follows from a uniform lower bound on all diagonal differences. -/
theorem sylvester_aposteriori_bound_diagonal_of_entrywise_abs_ge_total
    (n : Nat)
    (a b : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j) :
    frobNorm (fun i j => X i j - Xhat i j) <=
      (1 / sigma) *
        frobNorm
          (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat) := by
  exact
    sylvester_aposteriori_bound_of_sepLowerBound_total n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat sigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      hExact

/-- Higham, 2nd ed., Chapter 16.4, equations (16.26) and (16.28),
    diagonal case: the total relative a posteriori error-residual bound
    follows from a uniform lower bound on all diagonal differences. -/
theorem sylvester_relative_aposteriori_bound_diagonal_of_entrywise_abs_ge_total
    (n : Nat)
    (a b : Fin n -> Real) (C X Xhat : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hExact : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) X i j = C i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm (fun i j => X i j - Xhat i j) / frobNorm X <=
      ((1 / sigma) *
          frobNorm
            (sylvesterResidual n (Matrix.diagonal a) (Matrix.diagonal b) C Xhat)) /
        frobNorm X := by
  exact
    sylvester_relative_aposteriori_bound_of_sepLowerBound_total n
      (Matrix.diagonal a) (Matrix.diagonal b) C X Xhat sigma
      (SepLowerBound_diagonal_of_entrywise_abs_ge n a b sigma hSigma hgap)
      hExact hX_pos

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total diagonal entrywise-gap a posteriori endpoint. -/
alias H16_eq16_28_sylvester_aposteriori_bound_diagonal_of_entrywise_abs_ge_total :=
  sylvester_aposteriori_bound_diagonal_of_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.4, equation (16.28): source-numbered
    alias for the total relative diagonal entrywise-gap a posteriori endpoint. -/
alias H16_eq16_28_sylvester_relative_aposteriori_bound_diagonal_of_entrywise_abs_ge_total :=
  sylvester_relative_aposteriori_bound_diagonal_of_entrywise_abs_ge_total

-- ============================================================
-- Generalized equations from Chapter 16.5
-- ============================================================

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30):
    residual for the generalized Sylvester form `A X B + C X D = E`. -/
noncomputable def generalizedSylvesterAXB_CXD_residual (m n : Nat)
    (A C : RMatFn m m) (B D : RMatFn n n) (E X : RMatFn m n) : RMatFn m n :=
  fun i j =>
    matMulRect m n n (matMulRect m m n A X) B i j +
      matMulRect m n n (matMulRect m m n C X) D i j - E i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30):
    source-numbered abbreviation for the generalized Sylvester residual
    `A X B + C X D - E`. The local API groups the left matrices as `(A,C)`
    and the right matrices as `(B,D)`. -/
noncomputable abbrev H16_eq16_30_generalizedSylvesterAXB_CXD_residual :=
  generalizedSylvesterAXB_CXD_residual

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30):
    source equation predicate for `A X B + C X D = E`. -/
def IsGeneralizedSylvesterAXB_CXD_Solution (m n : Nat)
    (A C : RMatFn m m) (B D : RMatFn n n) (E X : RMatFn m n) : Prop :=
  forall i j,
    matMulRect m n n (matMulRect m m n A X) B i j +
      matMulRect m n n (matMulRect m m n C X) D i j = E i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30):
    source-numbered abbreviation for the generalized Sylvester equation
    predicate `A X B + C X D = E`. -/
abbrev H16_eq16_30_IsGeneralizedSylvesterAXB_CXD_Solution :=
  IsGeneralizedSylvesterAXB_CXD_Solution

/-- The residual for equation (16.30) is zero exactly when the generalized
    Sylvester equation holds. -/
theorem generalizedSylvesterAXB_CXD_residual_zero_iff_solution (m n : Nat)
    (A C : RMatFn m m) (B D : RMatFn n n) (E X : RMatFn m n) :
    (forall i j, generalizedSylvesterAXB_CXD_residual m n A C B D E X i j = 0) <->
      IsGeneralizedSylvesterAXB_CXD_Solution m n A C B D E X := by
  constructor
  case mp =>
    intro h i j
    have hij := h i j
    unfold generalizedSylvesterAXB_CXD_residual at hij
    linarith
  case mpr =>
    intro h i j
    have hij := h i j
    unfold IsGeneralizedSylvesterAXB_CXD_Solution at h
    unfold generalizedSylvesterAXB_CXD_residual
    linarith

/-- Higham, 2nd ed., Chapter 16.5, equation (16.30): source-numbered alias
    for the zero-residual characterization of `A X B + C X D = E`. -/
alias H16_eq16_30_generalizedSylvesterAXB_CXD_residual_zero_iff_solution :=
  generalizedSylvesterAXB_CXD_residual_zero_iff_solution

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    coupled generalized Sylvester equation predicate
    `AX - YB = C` and `DX - YE = F`. -/
def IsGeneralizedSylvesterPairSolution (m n : Nat)
    (A D : RMatFn m m) (B E : RMatFn n n)
    (C F0 X Y : RMatFn m n) : Prop :=
  And
    (forall i j, matMulRect m m n A X i j - matMulRect m n n Y B i j = C i j)
    (forall i j, matMulRect m m n D X i j - matMulRect m n n Y E i j = F0 i j)

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    source-numbered abbreviation for the coupled generalized Sylvester
    equation predicate `AX - YB = C` and `DX - YE = F`. -/
abbrev H16_eq16_31_IsGeneralizedSylvesterPairSolution :=
  IsGeneralizedSylvesterPairSolution

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    first residual for the coupled generalized Sylvester equations
    `AX - YB = C` and `DX - YE = F`. -/
noncomputable def generalizedSylvesterPairResidualLeft (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n)
    (C X Y : RMatFn m n) : RMatFn m n :=
  fun i j => matMulRect m m n A X i j - matMulRect m n n Y B i j - C i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    source-numbered abbreviation for the left residual `AX - YB - C`. -/
noncomputable abbrev H16_eq16_31_generalizedSylvesterPairResidualLeft :=
  generalizedSylvesterPairResidualLeft

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    second residual for the coupled generalized Sylvester equations
    `AX - YB = C` and `DX - YE = F`. -/
noncomputable def generalizedSylvesterPairResidualRight (m n : Nat)
    (D : RMatFn m m) (E : RMatFn n n)
    (F0 X Y : RMatFn m n) : RMatFn m n :=
  fun i j => matMulRect m m n D X i j - matMulRect m n n Y E i j - F0 i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31):
    source-numbered abbreviation for the right residual `DX - YE - F`. -/
noncomputable abbrev H16_eq16_31_generalizedSylvesterPairResidualRight :=
  generalizedSylvesterPairResidualRight

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31): the two residuals vanish
    exactly when the coupled generalized Sylvester equations hold. -/
theorem generalizedSylvesterPair_residual_zero_iff_solution (m n : Nat)
    (A D : RMatFn m m) (B E : RMatFn n n)
    (C F0 X Y : RMatFn m n) :
    ((forall i j,
        generalizedSylvesterPairResidualLeft m n A B C X Y i j = 0) ∧
      (forall i j,
        generalizedSylvesterPairResidualRight m n D E F0 X Y i j = 0)) <->
      IsGeneralizedSylvesterPairSolution m n A D B E C F0 X Y := by
  constructor
  · intro h
    constructor
    · intro i j
      have hij := h.1 i j
      unfold generalizedSylvesterPairResidualLeft at hij
      linarith
    · intro i j
      have hij := h.2 i j
      unfold generalizedSylvesterPairResidualRight at hij
      linarith
  · intro h
    constructor
    · intro i j
      have hij := h.1 i j
      unfold generalizedSylvesterPairResidualLeft
      linarith
    · intro i j
      have hij := h.2 i j
      unfold generalizedSylvesterPairResidualRight
      linarith

/-- Higham, 2nd ed., Chapter 16.5, equation (16.31): source-numbered alias
    for the residual characterization of the coupled generalized Sylvester
    equations. -/
alias H16_eq16_31_generalizedSylvesterPair_residual_zero_iff_solution :=
  generalizedSylvesterPair_residual_zero_iff_solution

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32):
    residual for the algebraic Riccati form `AX + XB - XFX + G = 0`. -/
noncomputable def riccatiResidual (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (F : RMatFn n m)
    (G X : RMatFn m n) : RMatFn m n :=
  fun i j =>
    matMulRect m m n A X i j +
      matMulRect m n n X B i j -
      matMulRect m m n (matMulRect m n m X F) X i j +
      G i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32):
    source-numbered abbreviation for the rectangular-compatible Riccati
    residual `AX + XB - XFX + G`. -/
noncomputable abbrev H16_eq16_32_riccatiResidual :=
  riccatiResidual

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32):
    source equation predicate for `A X + X B - X F X + G = 0`. -/
def IsRiccatiSolution (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (F : RMatFn n m)
    (G X : RMatFn m n) : Prop :=
  forall i j,
    matMulRect m m n A X i j +
      matMulRect m n n X B i j -
      matMulRect m m n (matMulRect m n m X F) X i j +
      G i j = 0

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32):
    source-numbered abbreviation for the rectangular-compatible Riccati
    equation predicate `AX + XB - XFX + G = 0`. -/
abbrev H16_eq16_32_IsRiccatiSolution :=
  IsRiccatiSolution

/-- The residual for equation (16.32) is zero exactly when the Riccati source
    equation holds. -/
theorem riccatiResidual_zero_iff_solution (m n : Nat)
    (A : RMatFn m m) (B : RMatFn n n) (F : RMatFn n m)
    (G X : RMatFn m n) :
    (forall i j, riccatiResidual m n A B F G X i j = 0) <->
      IsRiccatiSolution m n A B F G X := by
  constructor
  case mp =>
    intro h i j
    exact h i j
  case mpr =>
    intro h i j
    exact h i j

/-- Higham, 2nd ed., Chapter 16.5, equation (16.32): source-numbered alias
    for the zero-residual characterization of the algebraic Riccati form. -/
alias H16_eq16_32_riccatiResidual_zero_iff_solution :=
  riccatiResidual_zero_iff_solution

end NumStability
