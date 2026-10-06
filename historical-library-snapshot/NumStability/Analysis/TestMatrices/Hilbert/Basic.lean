import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import NumStability.Analysis.MatrixAlgebra

/-!
# NumStability Analysis TestMatrices Hilbert Basic

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Section 28.1, p. 512: the `n × n` Hilbert matrix.  Source
indices `i,j = 1,...,n` become `Fin n` indices and the denominator is
`i.val + j.val + 1`. -/
noncomputable def hilbertMatrix (n : ℕ) : RSqMat n :=
  fun i j => 1 / (i.val + j.val + 1 : ℕ)

@[simp] theorem hilbertMatrix_apply {n : ℕ} (i j : Fin n) :
    hilbertMatrix n i j = 1 / (i.val + j.val + 1 : ℕ) := rfl

/-- The Hilbert matrix is symmetric, as stated at the start of Section 28.1. -/
theorem hilbertMatrix_transpose (n : ℕ) :
    (hilbertMatrix n).transpose = hilbertMatrix n := by
  ext i j
  simp only [Matrix.transpose_apply, hilbertMatrix_apply]
  rw [add_comm i.val j.val]

/-- Product `0! 1! ... (n-1)!`; the extra `0! = 1` gives exactly the printed
`1! 2! ... (n-1)!` product. -/
noncomputable def factorialProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (Nat.factorial k : ℝ)

/-- Higham, 2nd ed., Section 28.1, p. 513, equation (28.2): the closed-form
candidate for `det(H_n)`. -/
noncomputable def hilbertDetFormula (n : ℕ) : ℝ :=
  factorialProduct n ^ 4 / factorialProduct (2 * n)

/-- Alternating shifted-binomial sum used to verify the printed triangular
inverse. -/
def altChooseShift (N A r : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N + 1),
    (-1 : ℤ) ^ m * Nat.choose N m * Nat.choose (A + m) r

theorem altChooseShift_succ_recurrence (N A r : ℕ) :
    altChooseShift (N + 1) A r =
      altChooseShift N A r - altChooseShift N (A + 1) r := by
  have hfirst :
      (Nat.choose A r : ℤ) +
          (∑ m ∈ Finset.range (N + 1),
            (-1 : ℤ) ^ (m + 1) * Nat.choose N (m + 1) *
              Nat.choose (A + (m + 1)) r) =
        altChooseShift N A r := by
    unfold altChooseShift
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.choose_zero_right, pow_zero, Int.ofNat_one, one_mul,
      Nat.add_zero]
    conv_lhs => rw [Finset.sum_range_succ]
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)]
    simp only [Int.ofNat_zero, mul_zero, zero_mul, add_zero]
    rw [add_comm]
  have hsecond :
      (∑ m ∈ Finset.range (N + 1),
        (-1 : ℤ) ^ (m + 1) * Nat.choose N m *
          Nat.choose (A + (m + 1)) r) =
        -altChooseShift N (A + 1) r := by
    unfold altChooseShift
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [pow_succ]
    ring_nf
  unfold altChooseShift
  rw [show N + 1 + 1 = (N + 1) + 1 by omega, Finset.sum_range_succ']
  simp only [Nat.choose_zero_right, pow_zero, Int.ofNat_one, one_mul,
    Nat.add_zero]
  rw [add_comm]
  calc
    (Nat.choose A r : ℤ) +
        ∑ m ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (m + 1) * Nat.choose (N + 1) (m + 1) *
            Nat.choose (A + (m + 1)) r =
      ((Nat.choose A r : ℤ) +
        ∑ m ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (m + 1) * Nat.choose N (m + 1) *
            Nat.choose (A + (m + 1)) r) +
        ∑ m ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (m + 1) * Nat.choose N m *
            Nat.choose (A + (m + 1)) r := by
              rw [add_assoc]
              apply congrArg (fun z : ℤ => (Nat.choose A r : ℤ) + z)
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro m hm
              rw [Nat.choose_succ_succ]
              push_cast
              ring
    _ = altChooseShift N A r - altChooseShift N (A + 1) r := by
      rw [hfirst, hsecond]
      ring

theorem altChooseShift_eq (N A r : ℕ) :
    altChooseShift N A r =
      if r < N then 0 else (-1 : ℤ) ^ N * Nat.choose A (r - N) := by
  induction N generalizing A r with
  | zero => simp [altChooseShift]
  | succ N ih =>
      rw [altChooseShift_succ_recurrence, ih, ih]
      by_cases hrN : r < N
      · have hrs : r < N + 1 := by omega
        simp [hrN, hrs]
      · by_cases hrEq : r = N
        · subst r
          simp
        · have hNs : N + 1 ≤ r := by omega
          have hnot : ¬ r < N + 1 := by omega
          have hsub : r - N = (r - (N + 1)) + 1 := by omega
          simp [hrN, hnot, hsub, Nat.choose_succ_succ]
          rw [pow_succ]
          ring

theorem altChooseShift_pred_eq_zero (N A : ℕ) (hN : 0 < N) :
    altChooseShift N A (N - 1) = 0 := by
  rw [altChooseShift_eq]
  simp [show N - 1 < N by omega]

/-- Factorial part of the upper-triangular entry in (28.3). -/
noncomputable def hilbertRCore (i k : ℕ) : ℝ :=
  (Nat.factorial k : ℝ) ^ 2 /
    ((Nat.factorial (i + k + 1) : ℝ) * Nat.factorial (k - i))

/-- Signed binomial part of the inverse entry in (28.4). -/
noncomputable def hilbertRInvCore (k j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (k + j) * Nat.choose (k + j) k * Nat.choose j k

/-- One off-diagonal summand in the product of (28.3) and (28.4), reduced to
an alternating shifted-binomial summand. -/
theorem hilbert_core_product_eq_alt
    (i k j : ℕ) (hik : i ≤ k) (hkj : k ≤ j) (hij : i < j) :
    hilbertRCore i k * hilbertRInvCore k j =
      ((-1 : ℝ) ^ (i + j) / (j - i : ℝ)) *
        (((-1 : ℝ) ^ (k - i) * Nat.choose (j - i) (k - i)) *
          Nat.choose (i + j + (k - i)) (j - i - 1)) := by
  have hN : j - i ≠ 0 := by omega
  have hkm : k - i ≤ j - i := Nat.sub_le_sub_right hkj i
  have hchoose1 := Nat.cast_choose ℝ (show k ≤ k + j by omega)
  have hchoose2 := Nat.cast_choose ℝ hkj
  have hchoose3 := Nat.cast_choose ℝ hkm
  have hchoose4 := Nat.cast_choose ℝ
    (show j - i - 1 ≤ i + j + (k - i) by omega)
  unfold hilbertRCore hilbertRInvCore
  rw [hchoose1, hchoose2, hchoose3, hchoose4]
  have hfact : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  have hsign : (-1 : ℝ) ^ (k + j) =
      (-1 : ℝ) ^ (i + j) * (-1 : ℝ) ^ (k - i) := by
    rw [show k + j = (i + j) + (k - i) by omega, pow_add]
  rw [hsign]
  have hdiffne : (j : ℝ) - (i : ℝ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Nat.ne_of_gt hij))
  field_simp [hfact, hN, hdiffne]
  rw [show k + j - k = j by omega]
  rw [show j - i - (k - i) = j - k by omega]
  rw [show i + j + (k - i) = k + j by omega]
  rw [show k + j - (j - i - 1) = i + k + 1 by omega]
  have hfacN : Nat.factorial (j - i) =
      (j - i) * Nat.factorial (j - i - 1) := by
    conv_lhs => rw [show j - i = (j - i - 1) + 1 by omega,
      Nat.factorial_succ]
    rw [show j - i - 1 + 1 = j - i by omega]
  rw [hfacN]
  push_cast
  rw [Nat.cast_sub (le_of_lt hij)]
  ring

theorem hilbert_core_sum_Icc_eq_zero (i j : ℕ) (hij : i < j) :
    (∑ k ∈ Finset.Icc i j, hilbertRCore i k * hilbertRInvCore k j) = 0 := by
  have hIcc : Finset.Icc i j = Finset.Ico i (j + 1) := by
    ext k
    simp
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  rw [show j + 1 - i = (j - i) + 1 by omega]
  calc
    (∑ m ∈ Finset.range (j - i + 1),
        hilbertRCore i (i + m) * hilbertRInvCore (i + m) j) =
      ((-1 : ℝ) ^ (i + j) / (j - i : ℝ)) *
        ∑ m ∈ Finset.range (j - i + 1),
          (((-1 : ℝ) ^ m * Nat.choose (j - i) m) *
            Nat.choose (i + j + m) (j - i - 1)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      have hmN : m ≤ j - i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
      simpa [Nat.add_sub_cancel_left] using
        hilbert_core_product_eq_alt i (i + m) j
          (Nat.le_add_right i m) (by omega) hij
    _ = 0 := by
      have halt :
          (∑ m ∈ Finset.range (j - i + 1),
            (((-1 : ℝ) ^ m * Nat.choose (j - i) m) *
              Nat.choose (i + j + m) (j - i - 1))) = 0 := by
        exact_mod_cast altChooseShift_pred_eq_zero (j - i) (i + j) (by omega)
      rw [halt, mul_zero]

/-- Natural-index form of the displayed upper-triangular factor (28.3). -/
noncomputable def hilbertRNat (i j : ℕ) : ℝ :=
  if i ≤ j then Real.sqrt (2 * i + 1 : ℕ) * hilbertRCore i j else 0

/-- Natural-index form of the displayed inverse factor (28.4). -/
noncomputable def hilbertRInvNat (i j : ℕ) : ℝ :=
  if i ≤ j then Real.sqrt (2 * j + 1 : ℕ) * hilbertRInvCore i j else 0

theorem hilbert_R_diag_product (i : ℕ) :
    hilbertRNat i i * hilbertRInvNat i i = 1 := by
  simp only [hilbertRNat, hilbertRInvNat, le_refl, ↓reduceIte]
  unfold hilbertRCore hilbertRInvCore
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, mul_one,
    Nat.choose_self, Even.neg_one_pow (Even.add_self i)]
  rw [Nat.cast_choose ℝ (show i ≤ i + i by omega)]
  have hfact : ∀ n : ℕ, (Nat.factorial n : ℝ) ≠ 0 := by
    intro n
    exact_mod_cast Nat.factorial_ne_zero n
  have hsqrt : Real.sqrt (2 * i + 1 : ℕ) ^ 2 = (2 * i + 1 : ℕ) := by
    rw [Real.sq_sqrt]
    positivity
  rw [show i + i - i = i by omega]
  have hfac : Nat.factorial (i + i + 1) =
      (i + i + 1) * Nat.factorial (i + i) := by
    rw [Nat.factorial_succ]
  rw [hfac]
  push_cast
  field_simp [hfact]
  push_cast at hsqrt
  nlinarith [hsqrt]

/-- A rectangular diagonal matrix, with a source-indexed singular-value
function.  Entries outside the common diagonal are zero. -/
noncomputable def rectangularDiagonal {m n : ℕ} (σ : ℕ → ℝ) : RMat m n :=
  fun i j => if i.val = j.val then σ i.val else 0

/-- One-large-singular-value distribution from Section 28.3. -/
noncomputable def oneLargeSingularValues (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | _ + 1 => α⁻¹

/-- One-small-singular-value distribution, parameterized by the matrix order. -/
noncomputable def oneSmallSingularValues (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  if i + 1 = n then α⁻¹ else 1

/-- Geometrically distributed singular values from Section 28.3.  The source
parameter is `β = α^(1/(n-1))`, and zero-based index `i` has value `β⁻ⁱ`. -/
noncomputable def geometricSingularValues (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  let β := α ^ (1 / (n - 1 : ℝ))
  (β⁻¹) ^ i

/-- Arithmetically distributed singular values from Section 28.3, translated
to zero-based index `i`. -/
noncomputable def arithmeticSingularValues (n : ℕ) (α : ℝ) (i : ℕ) : ℝ :=
  1 - (1 - α⁻¹) * i / (n - 1 : ℝ)

/-- Product of a list of square matrices, in source order. -/
noncomputable def matrixListProduct {n : ℕ} :
    List (Fin n → Fin n → ℝ) → Fin n → Fin n → ℝ
  | [] => idMatrix n
  | A :: As => matMul n A (matrixListProduct As)

/-- The numerator in Higham's p. 522 Green-function inverse of
`Tₙ(-1,2,-1)`, expressed with zero-based indices. -/
def secondDifferenceGreenNum (n i j : ℕ) : ℕ :=
  Nat.min (i + 1) (j + 1) * (n - Nat.max i j)

/-- Higham, 2nd ed., Section 28.5, p. 522: the entrywise inverse candidate
`min(i,j) * (n - max(i,j) + 1) / (n + 1)`, translated to zero-based indices. -/
noncomputable def secondDifferenceInverse (n : ℕ) : RSqMat n :=
  fun i j => (secondDifferenceGreenNum n i.val j.val : ℝ) / (n + 1 : ℕ)

theorem secondDifferenceGreenNum_of_le (n i j : ℕ) (hij : i ≤ j) :
    secondDifferenceGreenNum n i j = (i + 1) * (n - j) := by
  have hmin : Nat.min (i + 1) (j + 1) = i + 1 := Nat.min_eq_left (by omega)
  have hmax : Nat.max i j = j := Nat.max_eq_right hij
  simp only [secondDifferenceGreenNum, hmin, hmax]

theorem secondDifferenceGreenNum_of_ge (n i j : ℕ) (hji : j ≤ i) :
    secondDifferenceGreenNum n i j = (j + 1) * (n - i) := by
  have hmin : Nat.min (i + 1) (j + 1) = j + 1 := Nat.min_eq_right (by omega)
  have hmax : Nat.max i j = i := Nat.max_eq_left hji
  simp only [secondDifferenceGreenNum, hmin, hmax]

/-- The discrete second difference of the Green numerator is `(n + 1)δᵢⱼ`.
This is the arithmetic core of the inverse verification. -/
theorem secondDifferenceGreenNum_recurrence
    (n i j : ℕ) (hi : i < n) (hj : j < n) :
    (2 : ℤ) * secondDifferenceGreenNum n i j -
        secondDifferenceGreenNum n (i + 1) j -
        (if 0 < i then (secondDifferenceGreenNum n (i - 1) j : ℤ) else 0) =
      if i = j then (n + 1 : ℕ) else 0 := by
  by_cases hi0 : i = 0
  · subst i
    by_cases hj0 : j = 0
    · subst j
      rw [secondDifferenceGreenNum_of_le n 0 0 (by omega)]
      rw [secondDifferenceGreenNum_of_ge n 1 0 (by omega)]
      simp
      push_cast [Nat.cast_sub (by omega : 1 ≤ n)]
      ring
    · rw [secondDifferenceGreenNum_of_le n 0 j (by omega)]
      rw [secondDifferenceGreenNum_of_le n 1 j (by omega)]
      have h0j : (0 : ℕ) ≠ j := by omega
      simp [h0j]
  · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
    rcases lt_trichotomy i j with hij | hij | hji
    · rw [secondDifferenceGreenNum_of_le n i j (by omega)]
      rw [secondDifferenceGreenNum_of_le n (i + 1) j (by omega)]
      rw [secondDifferenceGreenNum_of_le n (i - 1) j (by omega)]
      simp [hipos, hij.ne]
      ring
    · subst j
      rw [secondDifferenceGreenNum_of_le n i i (by omega)]
      rw [secondDifferenceGreenNum_of_ge n (i + 1) i (by omega)]
      rw [secondDifferenceGreenNum_of_le n (i - 1) i (by omega)]
      simp [hipos]
      push_cast [Nat.cast_sub (by omega : i + 1 ≤ n),
        Nat.cast_sub (by omega : i ≤ n)]
      ring
    · rw [secondDifferenceGreenNum_of_ge n i j (by omega)]
      rw [secondDifferenceGreenNum_of_ge n (i + 1) j (by omega)]
      rw [secondDifferenceGreenNum_of_ge n (i - 1) j (by omega)]
      have hijne : i ≠ j := by omega
      simp [hipos, hijne]
      push_cast [Nat.cast_sub (by omega : i + 1 ≤ n),
        Nat.cast_sub (by omega : i ≤ n),
        Nat.cast_sub (by omega : i - 1 ≤ n)]
      have himCast : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by omega
      rw [himCast]
      ring

theorem secondDifferenceGreenNum_succ_zero
    (n i j : ℕ) (hi : i < n) (hj : j < n) (hs : ¬i + 1 < n) :
    secondDifferenceGreenNum n (i + 1) j = 0 := by
  rw [secondDifferenceGreenNum_of_ge n (i + 1) j (by omega)]
  simp [show n - (i + 1) = 0 by omega]

end NumStability
