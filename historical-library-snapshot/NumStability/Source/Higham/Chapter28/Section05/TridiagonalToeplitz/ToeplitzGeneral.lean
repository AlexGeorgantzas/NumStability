import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Toeplitz.Basic
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter28 Section05 TridiagonalToeplitz ToeplitzGeneral

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28ToeplitzGeneral` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

noncomputable def toeplitzScaledVector {n : ℕ}
    (q : ℝ) (x : RVec n) : RVec n := fun i => q ^ i.val * x i

theorem tridiagonalToeplitz_mulVec_scaled_similarity {n : ℕ}
    (c d e q s : ℝ) (x : RVec n)
    (heq : e * q = s) (hcq : c = q * s) :
    Matrix.mulVec (tridiagonalToeplitz n c d e) (toeplitzScaledVector q x) =
      toeplitzScaledVector q
        (Matrix.mulVec (tridiagonalToeplitz n s d s) x) := by
  funext i
  rw [tridiagonalToeplitz_mulVec_apply]
  unfold toeplitzScaledVector
  rw [tridiagonalToeplitz_mulVec_apply]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      rw [pow_succ]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * q * x ⟨i.val + 1, hs⟩) * heq +
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      let j : Fin n := ⟨i.val + 1, hs⟩
      change
        d * (q ^ i.val * x i) + e * (q ^ (i.val + 1) * x j) + 0 =
          q ^ i.val * (d * x i + s * x j + 0)
      simp only [hi0, pow_zero, zero_add, pow_one, one_mul]
      linear_combination x j * heq
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · simp only [hs, hp, ↓reduceDIte]
      ring

noncomputable def generalToeplitzSineVector {n : ℕ}
    (c e : ℝ) (k : Fin n) : RVec n :=
  toeplitzScaledVector (Real.sqrt c / Real.sqrt e) (toeplitzSineVector n k)

noncomputable def generalToeplitzEigenvalue
    (n : ℕ) (c d e : ℝ) (k : Fin n) : ℝ :=
  d + 2 * Real.sqrt (c * e) *
    Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℕ))

/-- The tridiagonal Toeplitz matrix over `ℂ`.  For real parameters this is
entrywise the complexification of `tridiagonalToeplitz`. -/
noncomputable def complexTridiagonalToeplitz
    (n : ℕ) (c d e : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    if i = j then d
    else if i.val + 1 = j.val then e
    else if j.val + 1 = i.val then c
    else 0

theorem complexTridiagonalToeplitz_ofReal
    (n : ℕ) (c d e : ℝ) :
    complexTridiagonalToeplitz n c d e =
      (tridiagonalToeplitz n c d e).map Complex.ofReal := by
  ext i j
  simp only [complexTridiagonalToeplitz, tridiagonalToeplitz,
    Matrix.map_apply]
  split_ifs <;> simp

/-- Complex Toeplitz multiplication has the same three-term recurrence as
the real matrix. -/
theorem complexTridiagonalToeplitz_mulVec_apply
    {n : ℕ} (c d e : ℂ) (x : Fin n → ℂ) (i : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n c d e) x i =
      d * x i +
        (if h : i.val + 1 < n then e * x ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then c * x ⟨i.val - 1, by omega⟩ else 0) := by
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ j, complexTridiagonalToeplitz n c d e i j * x j) =
        ∑ j, ((if i = j then d else 0) +
          (if i.val + 1 = j.val then e else 0) +
          (if j.val + 1 = i.val then c else 0)) * x j := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hij : i = j
      · subst j
        simp [complexTridiagonalToeplitz]
      · by_cases hs : i.val + 1 = j.val
        · have hb : ¬j.val + 1 = i.val := by omega
          simp [complexTridiagonalToeplitz, hij, hs, hb]
        · by_cases hp : j.val + 1 = i.val
          · simp [complexTridiagonalToeplitz, hij, hs, hp]
          · simp [complexTridiagonalToeplitz, hij, hs, hp]
    _ = (∑ j, (if i = j then d else 0) * x j) +
          (∑ j, (if i.val + 1 = j.val then e else 0) * x j) +
          (∑ j, (if j.val + 1 = i.val then c else 0) * x j) := by
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = d * x i +
        (if h : i.val + 1 < n then e * x ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then c * x ⟨i.val - 1, by omega⟩ else 0) := by
      simp only [ite_mul, zero_mul]
      have hdiag : (∑ j : Fin n, if i = j then d * x j else 0) =
          d * x i := by simp
      rw [hdiag]
      by_cases hs : i.val + 1 < n
      · let ip : Fin n := ⟨i.val + 1, hs⟩
        have hsUnique : ∀ j : Fin n, i.val + 1 = j.val ↔ j = ip := by
          intro j
          constructor
          · intro h
            apply Fin.ext
            simpa [ip] using h.symm
          · intro h
            subst j
            simp [ip]
        simp_rw [hsUnique]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ j : Fin n, j.val + 1 = i.val ↔ j = im := by
            intro j
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst j
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, ip, im]
        · have hpNone : ∀ j : Fin n, ¬j.val + 1 = i.val := by
            intro j h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp, ip]
      · have hsNone : ∀ j : Fin n, ¬i.val + 1 = j.val := by
          intro j h
          omega
        simp_rw [if_neg (hsNone _)]
        by_cases hp : 0 < i.val
        · let im : Fin n := ⟨i.val - 1, by omega⟩
          have hpUnique : ∀ j : Fin n, j.val + 1 = i.val ↔ j = im := by
            intro j
            constructor
            · intro h
              apply Fin.ext
              simp [im]
              omega
            · intro h
              subst j
              simp [im]
              omega
          simp_rw [hpUnique]
          simp [hs, hp, im]
        · have hpNone : ∀ j : Fin n, ¬j.val + 1 = i.val := by
            intro j h
            omega
          simp_rw [if_neg (hpNone _)]
          simp [hs, hp]

noncomputable def complexToeplitzScaledVector {n : ℕ}
    (q : ℂ) (x : Fin n → ℂ) : Fin n → ℂ := fun i => q ^ i.val * x i

theorem complexTridiagonalToeplitz_mulVec_scaled_similarity {n : ℕ}
    (c d e q s : ℂ) (x : Fin n → ℂ)
    (heq : e * q = s) (hcq : c = q * s) :
    Matrix.mulVec (complexTridiagonalToeplitz n c d e)
        (complexToeplitzScaledVector q x) =
      complexToeplitzScaledVector q
        (Matrix.mulVec (complexTridiagonalToeplitz n s d s) x) := by
  funext i
  rw [complexTridiagonalToeplitz_mulVec_apply]
  unfold complexToeplitzScaledVector
  rw [complexTridiagonalToeplitz_mulVec_apply]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      rw [pow_succ]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * q * x ⟨i.val + 1, hs⟩) * heq +
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      let j : Fin n := ⟨i.val + 1, hs⟩
      change
        d * (q ^ i.val * x i) + e * (q ^ (i.val + 1) * x j) + 0 =
          q ^ i.val * (d * x i + s * x j + 0)
      simp only [hi0, pow_zero, zero_add, pow_one, one_mul]
      linear_combination x j * heq
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hpred : q ^ i.val = q ^ (i.val - 1) * q := by
        conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega]
        rw [pow_succ]
      rw [hpred]
      linear_combination
        (q ^ (i.val - 1) * x ⟨i.val - 1, by omega⟩) * hcq
    · simp only [hs, hp, ↓reduceDIte]
      ring

/-- A concrete complex square root of a real product. -/
noncomputable def realProductComplexSqrt (c e : ℝ) : ℂ :=
  if 0 ≤ c * e then (Real.sqrt (c * e) : ℂ)
  else Complex.I * (Real.sqrt (-(c * e)) : ℂ)

theorem realProductComplexSqrt_sq (c e : ℝ) :
    realProductComplexSqrt c e * realProductComplexSqrt c e =
      ((c * e : ℝ) : ℂ) := by
  by_cases h : 0 ≤ c * e
  · simp only [realProductComplexSqrt, if_pos h, ← Complex.ofReal_mul]
    rw [Real.mul_self_sqrt h]
  · have hn : 0 ≤ -(c * e) := le_of_lt (neg_pos.2 (lt_of_not_ge h))
    simp only [realProductComplexSqrt, if_neg h]
    rw [mul_mul_mul_comm, Complex.I_mul_I, neg_one_mul,
      ← Complex.ofReal_mul, Real.mul_self_sqrt hn, Complex.ofReal_neg]
    simp

noncomputable def complexToeplitzSineVector {n : ℕ}
    (q : ℂ) (k : Fin n) : Fin n → ℂ :=
  complexToeplitzScaledVector q (fun i => (toeplitzSineVector n k i : ℂ))

noncomputable def generalToeplitzComplexEigenvalue
    (n : ℕ) (c d e : ℝ) (k : Fin n) : ℂ :=
  (d : ℂ) + 2 * realProductComplexSqrt c e *
    (Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi / (n + 1 : ℕ)) : ℂ)

/-- The unrestricted sine vector above is nonzero for every scale, including
`q = 0`: its zeroth component is unchanged by scaling. -/
theorem complexToeplitzSineVector_ne_zero {n : ℕ}
    (q : ℂ) (k : Fin n) :
    complexToeplitzSineVector q k ≠ 0 := by
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hratio : ((k.val + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ k.isLt
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  intro hzero
  have hi := congrFun hzero i0
  simp only [complexToeplitzSineVector, complexToeplitzScaledVector,
    Pi.zero_apply] at hi
  have hentry : toeplitzSineVector n k i0 = Real.sin θ := by
    simp [toeplitzSineVector, i0, θ]
  rw [hentry] at hi
  norm_num at hi
  have hi' : (Real.sin θ : ℂ) = 0 := by simpa using hi
  exact (ne_of_gt hsin) (Complex.ofReal_eq_zero.mp hi')

def complexToeplitzLastIndex {n : ℕ} (k : Fin n) : Fin n :=
  ⟨n - 1, Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one⟩

def complexToeplitzLastVector {n : ℕ} (k : Fin n) : Fin n → ℂ :=
  Pi.single (complexToeplitzLastIndex k) 1

/-- When the superdiagonal vanishes, the last coordinate vector is an
eigenvector with eigenvalue `d`. -/
theorem complexTridiagonalToeplitz_last_eigenpair {n : ℕ}
    (c d : ℂ) (k : Fin n) :
    Matrix.mulVec (complexTridiagonalToeplitz n c d 0)
        (complexToeplitzLastVector k) =
      d • complexToeplitzLastVector k := by
  rw [complexToeplitzLastVector]
  rw [Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases hi : i = complexToeplitzLastIndex k
  · subst i
    simp [complexTridiagonalToeplitz, complexToeplitzLastIndex]
  · have hiLast : i ≠ (⟨n - 1,
        Nat.sub_lt (Nat.zero_lt_of_lt k.isLt) Nat.zero_lt_one⟩ : Fin n) := by
      simpa [complexToeplitzLastIndex] using hi
    have hbottom : n - 1 + 1 ≠ i.val := by omega
    simp [complexTridiagonalToeplitz, complexToeplitzLastIndex,
      hiLast, hbottom]

theorem complexTridiagonalToeplitz_lastVector_ne_zero {n : ℕ}
    (k : Fin n) :
    complexToeplitzLastVector k ≠ 0 := by
  intro h
  have hi := congrFun h (complexToeplitzLastIndex k)
  simp [complexToeplitzLastVector] at hi

/-- One explicit eigenvector used for the unrestricted p. 522 formula. -/
noncomputable def generalToeplitzComplexEigenvector {n : ℕ}
    (c e : ℝ) (k : Fin n) : Fin n → ℂ :=
  if e ≠ 0 then
    let s := realProductComplexSqrt c e
    complexToeplitzSineVector (s / (e : ℂ)) k
  else
    complexToeplitzLastVector k

end NumStability
