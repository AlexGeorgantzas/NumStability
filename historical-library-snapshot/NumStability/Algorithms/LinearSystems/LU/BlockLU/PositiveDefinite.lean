import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic.Push
import NumStability.Algorithms.LinearSystems.LU.BlockLU.Factorization
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Analysis.MatrixAlgebra

/-!
# Positive-definite block LU foundations

Reusable bridges from the repository's symmetric positive-definite predicate
to Mathlib positive-definite matrices, nonsingularity, finite positive
semidefiniteness, and positive-definite principal submatrices.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

/-- Higham, 2nd ed., Chapter 13, §13.3.2:
    positive definiteness of the flattened block matrix gives block-matrix
    nonsingularity.  This is the determinant bridge needed on the route from
    SPD leading principal submatrices to the Theorem 13.2 block-LU existence
    condition. -/
theorem blockMatrixNonsingular_of_posDef_flat {m r : ℕ}
    (A : Fin m → Fin m → (Fin r → Fin r → ℝ))
    (hPos : Matrix.PosDef (blockMatrixFlat A)) :
    BlockMatrixNonsingular A := by
  exact blockMatrixNonsingular_of_det_ne_zero_flat A
    (ne_of_gt (Matrix.PosDef.det_pos hPos))

/-- A positive-definite matrix remains positive definite after taking an
    injective principal submatrix.  This local wrapper exposes the exact
    submatrix fact needed for Chapter 13 leading block prefixes. -/
theorem matrix_posDef_submatrix_of_injective {ι κ : Type*} [Fintype ι] [Fintype κ]
    {M : Matrix ι ι ℝ}
    (hM : Matrix.PosDef M) (e : κ → ι) (he : Function.Injective e) :
    Matrix.PosDef (M.submatrix e e) := by
  refine ⟨hM.1.submatrix e, fun x hx => ?_⟩
  have hxmap : Finsupp.mapDomain e x ≠ 0 := by
    intro hzero
    apply hx
    have hz :
        Finsupp.mapDomain e x =
          Finsupp.mapDomain e (0 : κ →₀ ℝ) := by
      simpa [Finsupp.mapDomain_zero] using hzero
    exact Finsupp.mapDomain_injective he hz
  simpa [Finsupp.sum_mapDomain_index, add_mul, mul_add] using hM.2 hxmap

/-- The repository SPD predicate contains exactly the symmetry certificate
    required by the finite-matrix PSD/Loewner API. -/
theorem isSymPosDef_to_IsSymmetricFiniteMatrix {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    IsSymmetricFiniteMatrix A := hSPD.1

/-- The repository SPD predicate gives Mathlib's matrix positive-definiteness
    predicate for the same finite real matrix. -/
theorem isSymPosDef_to_matrix_posDef {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    Matrix.PosDef (A : Matrix (Fin n) (Fin n) ℝ) := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.IsHermitian.ext_iff]
    intro i j
    simp [hSPD.1 j i]
  · intro x hx
    have hx_exists : ∃ i : Fin n, x i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hx
      funext i
      exact h i
    have hquad := hSPD.2 x hx_exists
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hquad

/-- A repository SPD matrix has nonzero determinant. -/
theorem isSymPosDef_det_ne_zero {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 :=
  ne_of_gt (Matrix.PosDef.det_pos (isSymPosDef_to_matrix_posDef A hSPD))

/-- The canonical repository `nonsingInv` is a right inverse of an SPD matrix. -/
theorem isRightInverse_nonsingInv_of_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    IsRightInverse n A (nonsingInv n A) :=
  (isInverse_nonsingInv_of_det_ne_zero n A
    (isSymPosDef_det_ne_zero A hSPD)).2

/-- A repository symmetric positive-definite matrix is positive semidefinite
    in the local finite quadratic-form sense. -/
theorem finitePSD_of_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hSPD : IsSymPosDef n A) :
    finitePSD A := by
  intro x
  rw [finiteQuadraticForm_eq_sum_sum]
  by_cases hx : ∃ i : Fin n, x i ≠ 0
  · exact le_of_lt (hSPD.2 x hx)
  · push_neg at hx
    simp [hx]

/-- Mathlib positive definiteness implies the repository's finite real SPD
    predicate. -/
theorem matrix_posDef_to_isSymPosDef {n : ℕ}
    (A : Fin n → Fin n → ℝ)
    (hA : Matrix.PosDef (A : Matrix (Fin n) (Fin n) ℝ)) :
    IsSymPosDef n A := by
  constructor
  · intro i j
    have hherm := hA.1.eq
    have hij := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) hherm
    simpa using hij.symm
  · intro x hx
    have hxne : x ≠ 0 := by
      intro hzero
      obtain ⟨i, hi⟩ := hx
      exact hi (congr_fun hzero i)
    have hpos := hA.dotProduct_mulVec_pos hxne
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum,
      Finset.sum_mul, mul_assoc] using hpos

end NumStability
