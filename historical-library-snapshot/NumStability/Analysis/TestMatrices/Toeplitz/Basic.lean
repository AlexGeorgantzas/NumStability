import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Hilbert.Basic

/-!
# NumStability Analysis TestMatrices Toeplitz Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.5, p. 521: the tridiagonal Toeplitz matrix
`T_n(c,d,e)`. -/
noncomputable def tridiagonalToeplitz (n : ℕ) (c d e : ℝ) : RSqMat n :=
  fun i j =>
    if i = j then d
    else if i.val + 1 = j.val then e
    else if j.val + 1 = i.val then c
    else 0

@[simp] theorem tridiagonalToeplitz_diag {n : ℕ} (c d e : ℝ) (i : Fin n) :
    tridiagonalToeplitz n c d e i i = d := by
  simp [tridiagonalToeplitz]

/-- Transposition interchanges the sub- and superdiagonal parameters. -/
theorem tridiagonalToeplitz_transpose (n : ℕ) (c d e : ℝ) :
    (tridiagonalToeplitz n c d e).transpose =
      tridiagonalToeplitz n e d c := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [tridiagonalToeplitz]
  · by_cases hij1 : i.val + 1 = j.val
    · have hji1 : ¬j.val + 1 = i.val := by omega
      have hji : j ≠ i := Ne.symm hij
      simp [Matrix.transpose_apply, tridiagonalToeplitz, hij, hji, hij1, hji1]
    · by_cases hji1 : j.val + 1 = i.val
      · have hji : j ≠ i := Ne.symm hij
        simp [Matrix.transpose_apply, tridiagonalToeplitz, hij, hji, hij1, hji1]
      · have hji : j ≠ i := Ne.symm hij
        simp [Matrix.transpose_apply, tridiagonalToeplitz, hij, hji, hij1, hji1]

/-- Multiplication on the right by a tridiagonal Toeplitz matrix reduces to
the diagonal and its at most two neighboring rows. -/
theorem tridiagonalToeplitz_mul_apply_right
    (n : ℕ) (c d e : ℝ) (A : RSqMat n) (i j : Fin n) :
    (tridiagonalToeplitz n c d e * A) i j =
      d * A i j +
        (if h : i.val + 1 < n then e * A ⟨i.val + 1, h⟩ j else 0) +
        (if h : 0 < i.val then c * A ⟨i.val - 1, by omega⟩ j else 0) := by
  simp only [Matrix.mul_apply]
  calc
    (∑ x, tridiagonalToeplitz n c d e i x * A x j) =
        ∑ x, ((if i = x then d else 0) +
          (if i.val + 1 = x.val then e else 0) +
          (if x.val + 1 = i.val then c else 0)) * A x j := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hix : i = x
      · subst x
        simp [tridiagonalToeplitz]
      · by_cases hs : i.val + 1 = x.val
        · have hb : ¬x.val + 1 = i.val := by omega
          simp [tridiagonalToeplitz, hix, hs, hb]
        · by_cases hp : x.val + 1 = i.val
          · simp [tridiagonalToeplitz, hix, hs, hp]
          · simp [tridiagonalToeplitz, hix, hs, hp]
    _ = (∑ x, (if i = x then d else 0) * A x j) +
          (∑ x, (if i.val + 1 = x.val then e else 0) * A x j) +
          (∑ x, (if x.val + 1 = i.val then c else 0) * A x j) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = d * A i j +
        (if h : i.val + 1 < n then e * A ⟨i.val + 1, h⟩ j else 0) +
        (if h : 0 < i.val then c * A ⟨i.val - 1, by omega⟩ j else 0) := by
      simp only [ite_mul, zero_mul]
      have hdiag : (∑ x : Fin n, if i = x then d * A x j else 0) =
          d * A i j := by simp
      rw [hdiag]
      by_cases hs : i.val + 1 < n
      · let ip : Fin n := ⟨i.val + 1, hs⟩
        have hsUnique : ∀ x : Fin n, i.val + 1 = x.val ↔ x = ip := by
          intro x
          constructor
          · intro h
            apply Fin.ext
            simpa [ip] using h.symm
          · intro h
            subst x
            simp [ip]
        simp_rw [hsUnique]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ x : Fin n, x.val + 1 = i.val ↔ x = im := by
            intro x
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst x
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, ip, im]
        · have hpNone : ∀ x : Fin n, ¬x.val + 1 = i.val := by
            intro x h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp, ip]
      · have hsNone : ∀ x : Fin n, ¬i.val + 1 = x.val := by
          intro x h
          omega
        simp_rw [if_neg (hsNone _)]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ x : Fin n, x.val + 1 = i.val ↔ x = im := by
            intro x
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst x
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, im]
        · have hpNone : ∀ x : Fin n, ¬x.val + 1 = i.val := by
            intro x h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp]

/-- The p. 522 Green matrix is a right inverse of `Tₙ(-1,2,-1)`. -/
theorem tridiagonalToeplitz_mul_secondDifferenceInverse (n : ℕ) :
    tridiagonalToeplitz n (-1) 2 (-1) * secondDifferenceInverse n = 1 := by
  ext i j
  rw [tridiagonalToeplitz_mul_apply_right]
  have hrec := secondDifferenceGreenNum_recurrence n i.val j.val i.isLt j.isLt
  have hrecR := congrArg (fun z : ℤ => (z : ℝ)) hrec
  norm_num at hrecR
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp] using hrecR
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp] using hrecR
  · have hsz := secondDifferenceGreenNum_succ_zero n i.val j.val i.isLt j.isLt hs
    by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp, hsz] using hrecR
    · simp only [hs, hp, ↓reduceDIte, secondDifferenceInverse]
      field_simp
      simpa [Matrix.one_apply, Fin.ext_iff, hp, hsz] using hrecR

/-- The Green matrix is also a left inverse; finite square matrices over `ℝ`
are Dedekind-finite. -/
theorem secondDifferenceInverse_mul_tridiagonalToeplitz (n : ℕ) :
    secondDifferenceInverse n * tridiagonalToeplitz n (-1) 2 (-1) = 1 := by
  exact mul_eq_one_comm.mp (tridiagonalToeplitz_mul_secondDifferenceInverse n)

end NumStability
