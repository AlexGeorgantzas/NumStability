-- Algorithms/MatSeqProduct.lean
--
-- Higham Chapter 3, Problem 3.10.

import Mathlib.Tactic
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# Sequential Matrix-Product Error Accumulation

Higham Chapter 3, Problem 3.10 asks for the standard first-order estimate

`||A_1 ... A_k - fl(A_1 ... A_k)||_F <= (k n^2 u + O(u^2))
  ||A_1||_2 ... ||A_k||_2`.

The theorem below is the exact finite-budget accumulation statement behind
that displayed formula.  It works with the repository's predicate-style
operator-2 certificates: if the local error at the `j`th matrix multiplication
is bounded by `eps_j` times the product of the spectral-norm certificates so
far, then the final Frobenius error is bounded by the sum of the local budgets
times the product of all certificates.  Instantiating `eps_j` with the local
matrix-multiply first-order budget `n^2 u + O(u^2)` gives the source formula.
-/

/-- Scalar prefix product `a_0 * ... * a_{k-1}`. -/
noncomputable def scalarPrefixProd : ℕ → (ℕ → ℝ) → ℝ
  | 0, _a => 1
  | k + 1, a => scalarPrefixProd k a * a k

/-- A prefix product of nonnegative scalars is nonnegative. -/
theorem scalarPrefixProd_nonneg (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) :
    ∀ k, 0 ≤ scalarPrefixProd k a
  | 0 => by simp [scalarPrefixProd]
  | k + 1 => by
      exact mul_nonneg (scalarPrefixProd_nonneg a ha k) (ha k)

/-- Left-to-right prefix product `A_0 * ... * A_{k-1}`. -/
noncomputable def matPrefixProd (n : ℕ) :
    ℕ → (ℕ → Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | 0, _A => idMatrix n
  | k + 1, A => matMul n (matPrefixProd n k A) (A k)

/-- Error matrix between a computed prefix and the exact prefix. -/
noncomputable def matPrefixProdError (n : ℕ)
    (A Phat : ℕ → Fin n → Fin n → ℝ) (k : ℕ) :
    Fin n → Fin n → ℝ :=
  fun i j => Phat k i j - matPrefixProd n k A i j

/-- **Problem 3.10 accumulation theorem.**

Assume the computed prefix products satisfy

`Phat_{j+1} = Phat_j A_j + E_j`,

and each local matrix-multiply error has Frobenius norm at most

`eps_j * (alpha_0 * ... * alpha_j)`,

where `alpha_j` is an operator-2 certificate for right multiplication by
`A_j`.  Then

`||Phat_k - A_0...A_{k-1}||_F
 <= (sum_{j<k} eps_j) * alpha_0...alpha_{k-1}`.

This is the source's `k n^2 u + O(u^2)` result with a concrete finite budget
in place of asymptotic notation. -/
theorem matPrefixProd_error_bound_from_local_errors
    (n : ℕ) (A Phat E : ℕ → Fin n → Fin n → ℝ)
    (eps alpha : ℕ → ℝ)
    (halpha_nonneg : ∀ j, 0 ≤ alpha j)
    (hAop : ∀ j, rectOpNorm2Le (finiteTranspose (A j)) (alpha j))
    (hinit : Phat 0 = idMatrix n)
    (hstep :
      ∀ j, Phat (j + 1) =
        fun i l => matMul n (Phat j) (A j) i l + E j i l)
    (hlocal :
      ∀ j, frobNorm (E j) ≤
        eps j * scalarPrefixProd (j + 1) alpha) :
    ∀ k,
      frobNorm (matPrefixProdError n A Phat k) ≤
        Finset.sum (Finset.range k) eps * scalarPrefixProd k alpha := by
  intro k
  induction k with
  | zero =>
      have herr_zero : matPrefixProdError n A Phat 0 = fun _i _j => 0 := by
        ext i j
        simp [matPrefixProdError, matPrefixProd, hinit]
      rw [herr_zero]
      rw [(frobNorm_eq_zero_iff (fun _i _j => 0)).mpr (by intro i j; rfl)]
      simp [scalarPrefixProd]
  | succ k ih =>
      let Err : Fin n → Fin n → ℝ := matPrefixProdError n A Phat k
      let PropErr : Fin n → Fin n → ℝ := matMul n Err (A k)
      have hmul_bound :
          frobNorm PropErr ≤ alpha k * frobNorm Err := by
        have hrect :
            frobNormRect (matMulRectLeft Err (A k)) ≤ alpha k * frobNorm Err :=
          frobNormRect_matMulRectLeft_le_of_transpose_rectOpNorm2Le
            Err (A k) (halpha_nonneg k) (hAop k)
        simpa [PropErr, matMulRectLeft, frobNormRect_eq_frobNorm] using hrect
      have herr_eq :
          matPrefixProdError n A Phat (k + 1) =
            fun i j => PropErr i j + E k i j := by
        ext i j
        simp [matPrefixProdError, matPrefixProd, PropErr, Err, hstep k, matMul]
        have hsum :
            (∑ x : Fin n,
                (Phat k i x - matPrefixProd n k A i x) * A k x j) =
              (∑ x : Fin n, Phat k i x * A k x j) -
                ∑ x : Fin n, matPrefixProd n k A i x * A k x j := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring
        rw [hsum]
        ring
      have htri :
          frobNorm (matPrefixProdError n A Phat (k + 1)) ≤
            frobNorm PropErr + frobNorm (E k) := by
        rw [herr_eq]
        exact frobNorm_add_le PropErr (E k)
      have hlocal_k :
          frobNorm (E k) ≤ eps k * (scalarPrefixProd k alpha * alpha k) := by
        simpa [scalarPrefixProd] using hlocal k
      calc
        frobNorm (matPrefixProdError n A Phat (k + 1))
            ≤ frobNorm PropErr + frobNorm (E k) := htri
        _ ≤ alpha k * frobNorm Err +
              eps k * (scalarPrefixProd k alpha * alpha k) := by
              exact add_le_add hmul_bound hlocal_k
        _ ≤ alpha k *
              (Finset.sum (Finset.range k) eps * scalarPrefixProd k alpha) +
              eps k * (scalarPrefixProd k alpha * alpha k) := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left ih (halpha_nonneg k))
                (le_refl _)
        _ =
            (Finset.sum (Finset.range k) eps + eps k) *
              (scalarPrefixProd k alpha * alpha k) := by
              ring
        _ =
            Finset.sum (Finset.range (k + 1)) eps *
              scalarPrefixProd (k + 1) alpha := by
              simp [scalarPrefixProd, Finset.sum_range_succ, add_comm]

/-- Uniform-budget corollary of the Problem 3.10 accumulation theorem. -/
theorem matPrefixProd_error_bound_uniform
    (n : ℕ) (A Phat E : ℕ → Fin n → Fin n → ℝ)
    (beta : ℝ) (alpha : ℕ → ℝ)
    (halpha_nonneg : ∀ j, 0 ≤ alpha j)
    (hAop : ∀ j, rectOpNorm2Le (finiteTranspose (A j)) (alpha j))
    (hinit : Phat 0 = idMatrix n)
    (hstep :
      ∀ j, Phat (j + 1) =
        fun i l => matMul n (Phat j) (A j) i l + E j i l)
    (hlocal :
      ∀ j, frobNorm (E j) ≤
        beta * scalarPrefixProd (j + 1) alpha) :
    ∀ k,
      frobNorm (matPrefixProdError n A Phat k) ≤
        (k : ℝ) * beta * scalarPrefixProd k alpha := by
  intro k
  have h :=
    matPrefixProd_error_bound_from_local_errors n A Phat E
      (fun _j => beta) alpha halpha_nonneg hAop hinit hstep hlocal k
  simpa [Finset.sum_const, nsmul_eq_mul] using h

end NumStability
