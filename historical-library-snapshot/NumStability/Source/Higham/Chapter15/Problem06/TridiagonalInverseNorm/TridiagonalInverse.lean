import Mathlib.Tactic
import NumStability.Algorithms.LU.TridiagonalCond

/-!
# Chapter15 Problem06 TridiagonalInverseNorm TridiagonalInverse

Canonical destination for material split out of
`NumStability.Algorithms.LU.Higham15Problem15_6` by wave W10 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

noncomputable section

namespace NumStability

namespace Higham15Problem15_6

open scoped BigOperators

open NumStability

/-- Stored tridiagonal data for the transpose. -/
def transposeData {n : ℕ} (T : TridiagData n) : TridiagData n where
  a := fun i => if h : 0 < i.val then
    T.c ⟨i.val - 1, by omega⟩ else 0
  d := T.d
  c := fun i => if h : i.val + 1 < n then
    T.a ⟨i.val + 1, h⟩ else 0

theorem transposeData_matrix {n : ℕ} (T : TridiagData n)
    (i j : Fin n) :
    tridiag_to_matrix (transposeData T) i j =
      tridiag_to_matrix T j i := by
  by_cases hdiag : j.val = i.val
  · have hij : j = i := Fin.ext hdiag
    subst j
    simp [tridiag_to_matrix, transposeData]
  · by_cases hsub : j.val + 1 = i.val
    · have hi : 0 < i.val := by omega
      have hnotrev : i.val + 1 ≠ j.val := by omega
      simp only [tridiag_to_matrix]
      rw [if_neg hdiag, if_pos hsub]
      have hdiag' : i.val ≠ j.val := Ne.symm hdiag
      rw [if_neg hdiag', if_neg hnotrev, if_pos hsub]
      simp only [transposeData, hi, dif_pos]
      congr 1
      apply Fin.ext
      simp
      omega
    · by_cases hsuper : i.val + 1 = j.val
      · have hnext : i.val + 1 < n := by omega
        have hnotrev : j.val + 1 ≠ i.val := by omega
        simp only [tridiag_to_matrix]
        rw [if_neg hdiag, if_neg hsub, if_pos hsuper]
        have hdiag' : i.val ≠ j.val := Ne.symm hdiag
        rw [if_neg hdiag', if_pos hsuper]
        simp only [transposeData, hnext, dif_pos]
        congr 1
        apply Fin.ext
        exact hsuper
      · have hdiag' : i.val ≠ j.val := Ne.symm hdiag
        simp [tridiag_to_matrix, transposeData, hdiag, hdiag', hsub,
          hsuper]

/-- Totalized accessors let the scalar recurrences be ordinary structurally
recursive functions on `ℕ`; every correctness theorem below only evaluates
them at source-valid indices. -/
def diagAt {n : ℕ} (T : TridiagData n) (k : ℕ) : ℝ :=
  if h : k < n then T.d ⟨k, h⟩ else 0

def subAt {n : ℕ} (T : TridiagData n) (k : ℕ) : ℝ :=
  if h : k < n then T.a ⟨k, h⟩ else 0

def superAt {n : ℕ} (T : TridiagData n) (k : ℕ) : ℝ :=
  if h : k < n then T.c ⟨k, h⟩ else 0

@[simp] theorem diagAt_of_lt {n : ℕ} (T : TridiagData n) (k : ℕ)
    (hk : k < n) : diagAt T k = T.d ⟨k, hk⟩ := by
  simp [diagAt, hk]

@[simp] theorem subAt_of_lt {n : ℕ} (T : TridiagData n) (k : ℕ)
    (hk : k < n) : subAt T k = T.a ⟨k, hk⟩ := by
  simp [subAt, hk]

@[simp] theorem superAt_of_lt {n : ℕ} (T : TridiagData n) (k : ℕ)
    (hk : k < n) : superAt T k = T.c ⟨k, hk⟩ := by
  simp [superAt, hk]

/-- Forward homogeneous recurrence from the last column of `A A⁻¹ = I`,
normalized by `x₀=1`:

`x₁=-d₀/c₀`,
`x_{i+1}=-(aᵢx_{i-1}+dᵢxᵢ)/cᵢ`. -/
def forwardColumnNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T 0 / superAt T 0
  | k + 2 =>
      -(subAt T (k + 1) * forwardColumnNat T k +
          diagAt T (k + 1) * forwardColumnNat T (k + 1)) /
        superAt T (k + 1)

/-- Backward homogeneous recurrence for the first row of `A⁻¹ A = I`.
The argument is distance from the last index, so `0` stores the last entry. -/
def backwardRowNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T (n - 1) / superAt T (n - 2)
  | k + 2 =>
      let i := n - (k + 2);
      -(diagAt T i * backwardRowNat T (k + 1) +
          subAt T (i + 1) * backwardRowNat T k) /
        superAt T (i - 1)

/-- Backward homogeneous recurrence from the first column of `A A⁻¹ = I`,
again indexed by distance from the last entry. -/
def backwardColumnNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T (n - 1) / subAt T (n - 1)
  | k + 2 =>
      let i := n - (k + 2);
      -(diagAt T i * backwardColumnNat T (k + 1) +
          superAt T i * backwardColumnNat T k) /
        subAt T i

/-- Forward homogeneous recurrence for the last row of `A⁻¹ A = I`. -/
def forwardRowNat {n : ℕ} (T : TridiagData n) : ℕ → ℝ
  | 0 => 1
  | 1 => -diagAt T 0 / subAt T 1
  | k + 2 =>
      -(superAt T k * forwardRowNat T k +
          diagAt T (k + 1) * forwardRowNat T (k + 1)) /
        subAt T (k + 2)

/-- The forward `x` vector requested explicitly in Problem 15.6. -/
def problem15_6_x {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => forwardColumnNat T i.val

/-- Unnormalized backward first-row solution. -/
def problem15_6_yBar {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => backwardRowNat T (n - 1 - i.val)

/-- Its first-column residual.  Dividing by this scalar changes the
homogeneous row equations into `y A = e₀ᵀ`. -/
def problem15_6_yResidual {n : ℕ} (T : TridiagData n) : ℝ :=
  if hn : n = 0 then 1
  else if hn1 : n = 1 then diagAt T 0
  else diagAt T 0 * backwardRowNat T (n - 1) +
    subAt T 1 * backwardRowNat T (n - 2)

/-- The normalized backward `y` vector requested in Problem 15.6. -/
def problem15_6_y {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => problem15_6_yBar T i / problem15_6_yResidual T

/-- The analogous backward factor for the lower inverse triangle. -/
def problem15_6_p {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => backwardColumnNat T (n - 1 - i.val)

/-- Unnormalized forward last-row solution. -/
def problem15_6_qBar {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => forwardRowNat T i.val

/-- Last-column residual used to normalize the last inverse row. -/
def problem15_6_qResidual {n : ℕ} (T : TridiagData n) : ℝ :=
  if hn : n = 0 then 1
  else if hn1 : n = 1 then diagAt T 0
  else superAt T (n - 2) * forwardRowNat T (n - 2) +
    diagAt T (n - 1) * forwardRowNat T (n - 1)

/-- The normalized lower-triangle row factor. -/
def problem15_6_q {n : ℕ} (T : TridiagData n) : Fin n → ℝ :=
  fun i => problem15_6_qBar T i / problem15_6_qResidual T

/-- The four recurrences are a concrete producer depending only on the
`3n-2` stored tridiagonal entries. -/
structure Problem15_6Factors (n : ℕ) where
  x : Fin n → ℝ
  y : Fin n → ℝ
  p : Fin n → ℝ
  q : Fin n → ℝ

def problem15_6_factors {n : ℕ} (T : TridiagData n) :
    Problem15_6Factors n :=
  ⟨problem15_6_x T, problem15_6_y T,
    problem15_6_p T, problem15_6_q T⟩

end Higham15Problem15_6
end NumStability

end
