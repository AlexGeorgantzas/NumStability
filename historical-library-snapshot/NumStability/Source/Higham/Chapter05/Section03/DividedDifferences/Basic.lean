import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Chapter05 Section03 DividedDifferences Basic

Canonical destination for material split out of
`NumStability.Algorithms.Horner` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- Higham, 2nd ed., Chapter 5, Section 5.3:
one exact divided-difference sweep at level `k`.

For entries `j <= k`, the source recurrence leaves the entry fixed.  For
`j > k`, it applies
`(c_j^(k) - c_{j-1}^(k)) / (alpha_j - alpha_{j-k-1})`.  The functions are
indexed by natural numbers so later finite-vector and matrix adapters can
restrict them to `0:n`. -/
noncomputable def dividedDifferenceStep
    (nodes coeffs : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun j =>
    if j ≤ k then
      coeffs j
    else
      (coeffs j - coeffs (j - 1)) /
        (nodes j - nodes (j - k - 1))

theorem dividedDifferenceStep_of_le
    (nodes coeffs : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    dividedDifferenceStep nodes coeffs k j = coeffs j := by
  simp [dividedDifferenceStep, hj]

theorem dividedDifferenceStep_of_gt
    (nodes coeffs : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceStep nodes coeffs k j =
      (coeffs j - coeffs (j - 1)) /
        (nodes j - nodes (j - k - 1)) := by
  have hnot : ¬j ≤ k := Nat.not_le_of_gt hj
  simp [dividedDifferenceStep, hnot]

/-- Embed a finite vector on `0:n` into a natural-number-indexed vector,
padding with zero outside the source range. -/
noncomputable def dividedDifferenceFinToNat {n : ℕ}
    (v : Fin (n + 1) → ℝ) : ℕ → ℝ :=
  fun j => if h : j < n + 1 then v ⟨j, h⟩ else 0

/-- The predecessor index used by the finite divided-difference row. -/
def dividedDifferenceFinPred {n : ℕ} (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨i.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩

/-- Higham (5.9): the finite lower-bidiagonal `L_k` action for divided
differences on the vector indexed by `0:n`.

Rows `0:k` are copied.  Later rows contain the two nonzero coefficients
`1/(alpha_j-alpha_{j-k-1})` and `-1/(alpha_j-alpha_{j-k-1})`, multiplying
entries `j` and `j-1` respectively. -/
noncomputable def dividedDifferenceLMatrix
    (nodes : ℕ → ℝ) (n k : ℕ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j =>
    if _hi : i.val ≤ k then
      if j = i then 1 else 0
    else
      let den := nodes i.val - nodes (i.val - k - 1)
      (if j = i then 1 / den else 0) +
        (if j = dividedDifferenceFinPred i then -(1 / den) else 0)

/-- Matrix-vector action of Higham's finite `L_k`. -/
noncomputable def dividedDifferenceLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∑ j : Fin (n + 1), dividedDifferenceLMatrix nodes n k i j * v j

theorem dividedDifferenceLMatrixAction_of_le
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceLMatrixAction nodes n k v i = v i := by
  simp [dividedDifferenceLMatrixAction, dividedDifferenceLMatrix, hi,
    Finset.mem_univ]

theorem dividedDifferenceLMatrixAction_of_gt
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceLMatrixAction nodes n k v i =
      (v i - v (dividedDifferenceFinPred i)) /
        (nodes i.val - nodes (i.val - k - 1)) := by
  have hnot : ¬i.val ≤ k := Nat.not_le_of_gt hi
  simp [dividedDifferenceLMatrixAction, dividedDifferenceLMatrix, hnot,
    Finset.sum_add_distrib, Finset.mem_univ, add_mul]
  ring

/-- The finite `L_k` matrix action is exactly the scalar divided-difference
recurrence on indices `0:n`. -/
theorem dividedDifferenceLMatrixAction_eq_step
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    dividedDifferenceLMatrixAction nodes n k v i =
      dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val := by
  by_cases hi : i.val ≤ k
  · rw [dividedDifferenceLMatrixAction_of_le nodes v hi,
      dividedDifferenceStep_of_le nodes (dividedDifferenceFinToNat v) hi]
    simp [dividedDifferenceFinToNat, i.isLt]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [dividedDifferenceLMatrixAction_of_gt nodes v hgt,
      dividedDifferenceStep_of_gt nodes (dividedDifferenceFinToNat v) hgt]
    have hpred : i.val - 1 < n + 1 :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    simp [dividedDifferenceFinToNat, dividedDifferenceFinPred, i.isLt, hpred]

/-- Absolute-value action `|L_k| v` for the finite divided-difference matrix. -/
noncomputable def dividedDifferenceAbsLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∑ j : Fin (n + 1),
    |dividedDifferenceLMatrix nodes n k i j| * v j

theorem dividedDifferenceAbsLMatrixAction_nonneg
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLMatrixAction nodes n k v i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg (abs_nonneg _) (hv j))

/-- Componentwise absolute-value domination for one exact `L_k` action:
`|L_k v| <= |L_k| |v|`. -/
theorem abs_dividedDifferenceLMatrixAction_le_absLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLMatrixAction nodes n k v i| ≤
        dividedDifferenceAbsLMatrixAction nodes n k
          (fun j => |v j|) i := by
  intro i
  unfold dividedDifferenceLMatrixAction dividedDifferenceAbsLMatrixAction
  calc
    |∑ j : Fin (n + 1), dividedDifferenceLMatrix nodes n k i j * v j|
        ≤ ∑ j : Fin (n + 1),
            |dividedDifferenceLMatrix nodes n k i j * v j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin (n + 1),
          |dividedDifferenceLMatrix nodes n k i j| * |v j| := by
          apply Finset.sum_congr rfl
          intro j _
          exact abs_mul (dividedDifferenceLMatrix nodes n k i j) (v j)

/-- Monotonicity of the absolute `|L_k|` action. -/
theorem dividedDifferenceAbsLMatrixAction_mono
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ)
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, dividedDifferenceAbsLMatrixAction nodes n k v i ≤
      dividedDifferenceAbsLMatrixAction nodes n k w i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  exact Finset.sum_le_sum (fun j _ =>
    mul_le_mul_of_nonneg_left (hvw j) (abs_nonneg _))

/-- Linearity of the absolute `|L_k|` action with respect to subtraction in
the vector argument. -/
theorem dividedDifferenceAbsLMatrixAction_sub
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLMatrixAction nodes n k
        (fun j => v j - w j) i =
      dividedDifferenceAbsLMatrixAction nodes n k v i -
        dividedDifferenceAbsLMatrixAction nodes n k w i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Linearity of the absolute `|L_k|` action with respect to scalar
multiplication in the vector argument. -/
theorem dividedDifferenceAbsLMatrixAction_smul
    (nodes : ℕ → ℝ) (n k : ℕ) (a : ℝ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLMatrixAction nodes n k
        (fun j => a * v j) i =
      a * dividedDifferenceAbsLMatrixAction nodes n k v i := by
  intro i
  unfold dividedDifferenceAbsLMatrixAction
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Componentwise absolute-value domination for the difference of two exact
`L_k` actions. -/
theorem abs_dividedDifferenceLMatrixAction_sub_le_absLMatrixAction
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLMatrixAction nodes n k v i -
          dividedDifferenceLMatrixAction nodes n k w i| ≤
        dividedDifferenceAbsLMatrixAction nodes n k
          (fun j => |v j - w j|) i := by
  intro i
  unfold dividedDifferenceLMatrixAction dividedDifferenceAbsLMatrixAction
  have hsum :
      (∑ j : Fin (n + 1),
          dividedDifferenceLMatrix nodes n k i j * v j) -
        (∑ j : Fin (n + 1),
          dividedDifferenceLMatrix nodes n k i j * w j) =
        ∑ j : Fin (n + 1),
          dividedDifferenceLMatrix nodes n k i j * (v j - w j) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  calc
    |(∑ j : Fin (n + 1),
        dividedDifferenceLMatrix nodes n k i j * v j) -
      (∑ j : Fin (n + 1),
        dividedDifferenceLMatrix nodes n k i j * w j)|
        = |∑ j : Fin (n + 1),
            dividedDifferenceLMatrix nodes n k i j * (v j - w j)| := by
          rw [hsum]
    _ ≤ ∑ j : Fin (n + 1),
          |dividedDifferenceLMatrix nodes n k i j * (v j - w j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin (n + 1),
          |dividedDifferenceLMatrix nodes n k i j| * |v j - w j| := by
        apply Finset.sum_congr rfl
        intro j _
        exact abs_mul (dividedDifferenceLMatrix nodes n k i j) (v j - w j)

/-- Recursive absolute product majorant
`(1+gamma)|L_{m-1}| ... (1+gamma)|L_0| v` for divided differences. -/
noncomputable def dividedDifferenceAbsLProductAction
    (nodes : ℕ → ℝ) (gamma : ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v => fun i =>
      (1 + gamma) *
        dividedDifferenceAbsLMatrixAction nodes n k
          (dividedDifferenceAbsLProductAction nodes gamma n k v) i

theorem dividedDifferenceAbsLProductAction_nonneg
    (nodes : ℕ → ℝ) {gamma : ℝ} (hgamma : 0 ≤ gamma)
    (n m : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLProductAction nodes gamma n m v i := by
  induction m with
  | zero =>
      intro i
      exact hv i
  | succ m ih =>
      intro i
      unfold dividedDifferenceAbsLProductAction
      exact mul_nonneg (by linarith)
        (dividedDifferenceAbsLMatrixAction_nonneg nodes n m
          (dividedDifferenceAbsLProductAction nodes gamma n m v) ih i)

/-- Pull the repeated scalar factor in
`(1+gamma)|L_{m-1}| ... (1+gamma)|L_0| v` to the front. -/
theorem dividedDifferenceAbsLProductAction_const_gamma
    (nodes : ℕ → ℝ) (gamma : ℝ) (n m : ℕ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLProductAction nodes gamma n m v i =
      (1 + gamma) ^ m *
        dividedDifferenceAbsLProductAction nodes 0 n m v i := by
  induction m with
  | zero =>
      intro i
      simp [dividedDifferenceAbsLProductAction]
  | succ m ih =>
      intro i
      have hih :
          dividedDifferenceAbsLProductAction nodes gamma n m v =
            fun i => (1 + gamma) ^ m *
              dividedDifferenceAbsLProductAction nodes 0 n m v i := by
        funext j
        exact ih j
      calc
        dividedDifferenceAbsLProductAction nodes gamma n (m + 1) v i =
            (1 + gamma) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (dividedDifferenceAbsLProductAction nodes gamma n m v) i := rfl
        _ = (1 + gamma) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (fun j => (1 + gamma) ^ m *
                  dividedDifferenceAbsLProductAction nodes 0 n m v j) i := by
              rw [hih]
        _ = (1 + gamma) *
              ((1 + gamma) ^ m *
                dividedDifferenceAbsLMatrixAction nodes n m
                  (dividedDifferenceAbsLProductAction nodes 0 n m v) i) := by
              rw [dividedDifferenceAbsLMatrixAction_smul]
        _ = (1 + gamma) ^ (m + 1) *
              dividedDifferenceAbsLProductAction nodes 0 n (m + 1) v i := by
              simp [dividedDifferenceAbsLProductAction, pow_succ]
              ring

/-- Exact divided-difference columns `c^(k)` generated by the standard source
recurrence, with `c^(0) = f`. -/
noncomputable def dividedDifferenceCoeffs
    (nodes f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => f
  | k + 1 => dividedDifferenceStep nodes (dividedDifferenceCoeffs nodes f k) k

theorem dividedDifferenceCoeffs_zero
    (nodes f : ℕ → ℝ) :
    dividedDifferenceCoeffs nodes f 0 = f := rfl

theorem dividedDifferenceCoeffs_succ_entry_of_le
    (nodes f : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    dividedDifferenceCoeffs nodes f (k + 1) j =
      dividedDifferenceCoeffs nodes f k j := by
  simp [dividedDifferenceCoeffs, dividedDifferenceStep_of_le nodes
    (dividedDifferenceCoeffs nodes f k) hj]

theorem dividedDifferenceCoeffs_succ_entry_of_gt
    (nodes f : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceCoeffs nodes f (k + 1) j =
      (dividedDifferenceCoeffs nodes f k j -
          dividedDifferenceCoeffs nodes f k (j - 1)) /
        (nodes j - nodes (j - k - 1)) := by
  simp [dividedDifferenceCoeffs, dividedDifferenceStep_of_gt nodes
    (dividedDifferenceCoeffs nodes f k) hj]

/-- Finite divided-difference coefficient columns `c^(k)` over the source
index set `0:n`.  The successor column is the finite `L_k` action from
Higham (5.9). -/
noncomputable def dividedDifferenceFiniteCoeffs
    (nodes f : ℕ → ℝ) (n : ℕ) : ℕ → Fin (n + 1) → ℝ
  | 0 => fun i => f i.val
  | k + 1 =>
      dividedDifferenceLMatrixAction nodes n k
        (dividedDifferenceFiniteCoeffs nodes f n k)

theorem dividedDifferenceFiniteCoeffs_zero
    (nodes f : ℕ → ℝ) (n : ℕ) :
    dividedDifferenceFiniteCoeffs nodes f n 0 =
      fun i : Fin (n + 1) => f i.val := rfl

theorem dividedDifferenceFiniteCoeffs_succ
    (nodes f : ℕ → ℝ) (n k : ℕ) :
    dividedDifferenceFiniteCoeffs nodes f n (k + 1) =
      dividedDifferenceLMatrixAction nodes n k
        (dividedDifferenceFiniteCoeffs nodes f n k) := rfl

/-- Exact finite product action `L_{m-1} ... L_0 v` for divided differences. -/
noncomputable def dividedDifferenceLProductAction
    (nodes : ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceLMatrixAction nodes n k
        (dividedDifferenceLProductAction nodes n k v)

theorem dividedDifferenceLProductAction_zero
    (nodes : ℕ → ℝ) (n : ℕ) :
    dividedDifferenceLProductAction nodes n 0 =
      fun v : Fin (n + 1) → ℝ => v := rfl

theorem dividedDifferenceLProductAction_succ
    (nodes : ℕ → ℝ) (n k : ℕ) :
    dividedDifferenceLProductAction nodes n (k + 1) =
      fun v : Fin (n + 1) → ℝ =>
        dividedDifferenceLMatrixAction nodes n k
          (dividedDifferenceLProductAction nodes n k v) := rfl

/-- The exact finite divided-difference columns are the product
`L_{m-1} ... L_0 f`. -/
theorem dividedDifferenceFiniteCoeffs_eq_LProductAction
    (nodes f : ℕ → ℝ) (n m : ℕ) :
    ∀ i : Fin (n + 1),
      dividedDifferenceFiniteCoeffs nodes f n m i =
        dividedDifferenceLProductAction nodes n m
          (fun i : Fin (n + 1) => f i.val) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hprev :
          dividedDifferenceFiniteCoeffs nodes f n m =
            dividedDifferenceLProductAction nodes n m
              (fun i : Fin (n + 1) => f i.val) := by
        funext j
        exact ih j
      rw [dividedDifferenceFiniteCoeffs_succ,
        dividedDifferenceLProductAction_succ, hprev]

/-- Absolute-product majorant for the exact finite divided-difference
columns. -/
theorem dividedDifferenceFiniteCoeffs_abs_le_absLProduct_zero
    (nodes f : ℕ → ℝ) (n m : ℕ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        dividedDifferenceAbsLProductAction nodes 0 n m
          (fun i : Fin (n + 1) => |f i.val|) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have habs :=
        abs_dividedDifferenceLMatrixAction_le_absLMatrixAction nodes n m
          (dividedDifferenceFiniteCoeffs nodes f n m) i
      have hmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |dividedDifferenceFiniteCoeffs nodes f n m j|)
          (dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|))
          ih i
      calc
        |dividedDifferenceFiniteCoeffs nodes f n (m + 1) i|
            = |dividedDifferenceLMatrixAction nodes n m
                (dividedDifferenceFiniteCoeffs nodes f n m) i| := rfl
        _ ≤ dividedDifferenceAbsLMatrixAction nodes n m
              (fun j => |dividedDifferenceFiniteCoeffs nodes f n m j|) i := habs
        _ ≤ dividedDifferenceAbsLMatrixAction nodes n m
              (dividedDifferenceAbsLProductAction nodes 0 n m
                (fun i : Fin (n + 1) => |f i.val|)) i := hmono
        _ = dividedDifferenceAbsLProductAction nodes 0 n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i := by
              simp [dividedDifferenceAbsLProductAction]

/-- The finite `L_k` coefficient columns agree entrywise with the
natural-number recurrence used for the source scalar divided differences. -/
theorem dividedDifferenceFiniteCoeffs_eq_nat
    (nodes f : ℕ → ℝ) (n k : ℕ) (i : Fin (n + 1)) :
    dividedDifferenceFiniteCoeffs nodes f n k i =
      dividedDifferenceCoeffs nodes f k i.val := by
  induction k generalizing i with
  | zero =>
      rfl
  | succ k ih =>
      by_cases hi : i.val ≤ k
      · rw [dividedDifferenceFiniteCoeffs_succ,
          dividedDifferenceLMatrixAction_of_le nodes
            (dividedDifferenceFiniteCoeffs nodes f n k) hi,
          dividedDifferenceCoeffs_succ_entry_of_le nodes f hi]
        exact ih i
      · have hgt : k < i.val := Nat.lt_of_not_ge hi
        rw [dividedDifferenceFiniteCoeffs_succ,
          dividedDifferenceLMatrixAction_of_gt nodes
            (dividedDifferenceFiniteCoeffs nodes f n k) hgt,
          dividedDifferenceCoeffs_succ_entry_of_gt nodes f hgt,
          ih i, ih (dividedDifferenceFinPred i)]
        simp [dividedDifferenceFinPred]

/-- Diagonal row-scaling action `G_k` from Higham (5.9): rows `0:k` are
unchanged, while later rows are multiplied by a supplied local factor. -/
noncomputable def dividedDifferenceGAction
    (eta : ℕ → ℝ) (k : ℕ) (v : ℕ → ℝ) : ℕ → ℝ :=
  fun j => if j ≤ k then v j else eta j * v j

theorem dividedDifferenceGAction_of_le
    (eta : ℕ → ℝ) (v : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    dividedDifferenceGAction eta k v j = v j := by
  simp [dividedDifferenceGAction, hj]

theorem dividedDifferenceGAction_of_gt
    (eta : ℕ → ℝ) (v : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceGAction eta k v j = eta j * v j := by
  have hnot : ¬j ≤ k := Nat.not_le_of_gt hj
  simp [dividedDifferenceGAction, hnot]

theorem dividedDifferenceGAction_step_of_gt
    (nodes coeffs eta : ℕ → ℝ) {k j : ℕ} (hj : k < j) :
    dividedDifferenceGAction eta k (dividedDifferenceStep nodes coeffs k) j =
      eta j *
        ((coeffs j - coeffs (j - 1)) /
          (nodes j - nodes (j - k - 1))) := by
  simp [dividedDifferenceGAction_of_gt eta
    (dividedDifferenceStep nodes coeffs k) hj,
    dividedDifferenceStep_of_gt nodes coeffs hj]

/-- Higham (5.9): the finite diagonal `G_k` scaling matrix. -/
noncomputable def dividedDifferenceGMatrix
    (eta : ℕ → ℝ) (n k : ℕ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => if j = i then if i.val ≤ k then 1 else eta i.val else 0

/-- Matrix-vector action of Higham's finite diagonal `G_k`. -/
noncomputable def dividedDifferenceGMatrixAction
    (eta : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => ∑ j : Fin (n + 1), dividedDifferenceGMatrix eta n k i j * v j

theorem dividedDifferenceGMatrixAction_of_le
    (eta : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceGMatrixAction eta n k v i = v i := by
  simp [dividedDifferenceGMatrixAction, dividedDifferenceGMatrix, hi,
    Finset.mem_univ]

theorem dividedDifferenceGMatrixAction_of_gt
    (eta : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceGMatrixAction eta n k v i = eta i.val * v i := by
  have hnot : ¬i.val ≤ k := Nat.not_le_of_gt hi
  simp [dividedDifferenceGMatrixAction, dividedDifferenceGMatrix, hnot,
    Finset.mem_univ]

/-- The finite diagonal `G_k` action agrees with the natural-number-indexed
row-scaling action on indices `0:n`. -/
theorem dividedDifferenceGMatrixAction_eq_GAction
    (eta : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    dividedDifferenceGMatrixAction eta n k v i =
      dividedDifferenceGAction eta k (dividedDifferenceFinToNat v) i.val := by
  by_cases hi : i.val ≤ k
  · rw [dividedDifferenceGMatrixAction_of_le eta v hi,
      dividedDifferenceGAction_of_le eta (dividedDifferenceFinToNat v) hi]
    simp [dividedDifferenceFinToNat, i.isLt]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [dividedDifferenceGMatrixAction_of_gt eta v hgt,
      dividedDifferenceGAction_of_gt eta (dividedDifferenceFinToNat v) hgt]
    simp [dividedDifferenceFinToNat, i.isLt]

/-- Finite-matrix form of Higham (5.9): applying `G_k L_k` to a finite vector
agrees rowwise with the scalar `G_k` action applied to the exact
divided-difference step. -/
theorem dividedDifferenceGMatrixAction_LMatrixAction_eq
    (eta nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (i : Fin (n + 1)) :
    dividedDifferenceGMatrixAction eta n k
        (dividedDifferenceLMatrixAction nodes n k v) i =
      dividedDifferenceGAction eta k
        (dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k)
        i.val := by
  by_cases hi : i.val ≤ k
  · rw [dividedDifferenceGMatrixAction_of_le eta
      (dividedDifferenceLMatrixAction nodes n k v) hi,
      dividedDifferenceGAction_of_le eta
        (dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k) hi,
      dividedDifferenceLMatrixAction_eq_step nodes v i]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [dividedDifferenceGMatrixAction_of_gt eta
      (dividedDifferenceLMatrixAction nodes n k v) hgt,
      dividedDifferenceGAction_of_gt eta
        (dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k) hgt,
      dividedDifferenceLMatrixAction_eq_step nodes v i]

/-- Iterated finite product action
`G_{m-1} L_{m-1} ... G_0 L_0 v` for the divided-difference matrix factors in
Higham (5.10).  The function `eta k` supplies the diagonal entries for `G_k`. -/
noncomputable def dividedDifferenceGLProductAction
    (nodes : ℕ → ℝ) (eta : ℕ → ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceGMatrixAction (eta k) n k
        (dividedDifferenceLMatrixAction nodes n k
          (dividedDifferenceGLProductAction nodes eta n k v))

/-- Rounded primitive divided-difference sweep.  Entries `j <= k` are copied,
and entries `j > k` are computed with one rounded subtraction for the numerator,
one rounded subtraction for the node gap, and one rounded division. -/
noncomputable def fl_dividedDifferenceStep
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) (k : ℕ) : ℕ → ℝ :=
  fun j =>
    if j ≤ k then
      coeffs j
    else
      fp.fl_div
        (fp.fl_sub (coeffs j) (coeffs (j - 1)))
        (fp.fl_sub (nodes j) (nodes (j - k - 1)))

theorem fl_dividedDifferenceStep_of_le
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ} (hj : j ≤ k) :
    fl_dividedDifferenceStep fp nodes coeffs k j = coeffs j := by
  simp [fl_dividedDifferenceStep, hj]

/-- Finite rounded divided-difference coefficient columns over `0:n`.  The
successor column applies the rounded primitive sweep to the previous finite
column. -/
noncomputable def fl_dividedDifferenceFiniteCoeffs
    (fp : FPModel) (nodes f : ℕ → ℝ) (n : ℕ) :
    ℕ → Fin (n + 1) → ℝ
  | 0 => fun i => f i.val
  | k + 1 => fun i =>
      fl_dividedDifferenceStep fp nodes
        (dividedDifferenceFinToNat
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val

theorem fl_dividedDifferenceFiniteCoeffs_zero
    (fp : FPModel) (nodes f : ℕ → ℝ) (n : ℕ) :
    fl_dividedDifferenceFiniteCoeffs fp nodes f n 0 =
      fun i : Fin (n + 1) => f i.val := rfl

theorem fl_dividedDifferenceFiniteCoeffs_succ
    (fp : FPModel) (nodes f : ℕ → ℝ) (n k : ℕ) :
    fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) =
      fun i : Fin (n + 1) =>
        fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val := rfl

/-- Finite rounded matrix adapter for Higham (5.9): if the active rows of the
rounded divided-difference sweep are supplied as multiplicative perturbations
of the exact scalar row update, then the finite rounded sweep is the rowwise
`G_k L_k` matrix action. -/
theorem fl_dividedDifferenceStep_eq_GMatrixAction_of_row_factors
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ) (eta : ℕ → ℝ)
    (hrow : ∀ i : Fin (n + 1), k < i.val →
      fl_dividedDifferenceStep fp nodes (dividedDifferenceFinToNat v) k i.val =
        eta i.val *
          dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val) :
    ∀ i : Fin (n + 1),
      fl_dividedDifferenceStep fp nodes (dividedDifferenceFinToNat v) k i.val =
        dividedDifferenceGMatrixAction eta n k
          (dividedDifferenceLMatrixAction nodes n k v) i := by
  intro i
  by_cases hi : i.val ≤ k
  · rw [fl_dividedDifferenceStep_of_le fp nodes
      (dividedDifferenceFinToNat v) hi,
      dividedDifferenceGMatrixAction_of_le eta
        (dividedDifferenceLMatrixAction nodes n k v) hi,
      dividedDifferenceLMatrixAction_eq_step nodes v i,
      dividedDifferenceStep_of_le nodes (dividedDifferenceFinToNat v) hi]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rw [hrow i hgt,
      dividedDifferenceGMatrixAction_of_gt eta
        (dividedDifferenceLMatrixAction nodes n k v) hgt,
      dividedDifferenceLMatrixAction_eq_step nodes v i]

/-- Scalar row version of Higham (5.9): one rounded divided-difference entry
is the exact `L_k` row update multiplied by the local error factors from the
two subtractions and the division.  The denominator of the rounded division is
kept as an explicit nonzero hypothesis, matching `FPModel.model_div`. -/
theorem fl_dividedDifferenceStep_entry_error_factors
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat :
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0) :
    ∃ δnum δden δdiv : ℝ,
      |δnum| ≤ fp.u ∧ |δden| ≤ fp.u ∧ |δdiv| ≤ fp.u ∧
        fl_dividedDifferenceStep fp nodes coeffs k j =
          dividedDifferenceStep nodes coeffs k j *
            ((1 + δnum) / (1 + δden)) * (1 + δdiv) := by
  obtain ⟨δnum, hδnum, hnum⟩ :=
    fp.model_sub (coeffs j) (coeffs (j - 1))
  obtain ⟨δden, hδden, hdenEq⟩ :=
    fp.model_sub (nodes j) (nodes (j - k - 1))
  obtain ⟨δdiv, hδdiv, hdiv⟩ :=
    fp.model_div
      (fp.fl_sub (coeffs j) (coeffs (j - 1)))
      (fp.fl_sub (nodes j) (nodes (j - k - 1))) hdenHat
  refine ⟨δnum, δden, δdiv, hδnum, hδden, hδdiv, ?_⟩
  set num := coeffs j - coeffs (j - 1)
  set den := nodes j - nodes (j - k - 1)
  have hden' : den ≠ 0 := by
    simpa [den] using hden
  have hdenProduct : den * (1 + δden) ≠ 0 := by
    intro hzero
    apply hdenHat
    rw [hdenEq]
    simpa [den] using hzero
  have hdenFactor : 1 + δden ≠ 0 :=
    (mul_ne_zero_iff.mp hdenProduct).2
  have halg :
      ((num * (1 + δnum)) / (den * (1 + δden))) *
          (1 + δdiv) =
        (num / den) * ((1 + δnum) / (1 + δden)) *
          (1 + δdiv) := by
    field_simp [hden', hdenFactor]
  calc
    fl_dividedDifferenceStep fp nodes coeffs k j
        = fp.fl_div
            (fp.fl_sub (coeffs j) (coeffs (j - 1)))
            (fp.fl_sub (nodes j) (nodes (j - k - 1))) := by
          simp [fl_dividedDifferenceStep, Nat.not_le_of_gt hj]
    _ = ((num * (1 + δnum)) / (den * (1 + δden))) *
          (1 + δdiv) := by
          rw [hdiv, hnum, hdenEq]
    _ = (num / den) * ((1 + δnum) / (1 + δden)) *
          (1 + δdiv) := halg
    _ = dividedDifferenceStep nodes coeffs k j *
          ((1 + δnum) / (1 + δden)) * (1 + δdiv) := by
          rw [dividedDifferenceStep_of_gt nodes coeffs hj]

/-- Gamma-three version of the scalar row bridge for Higham (5.9).  The
denominator subtraction appears inverted in the exact algebra; the existing
signed product-error lemma packages the two subtraction errors and final
division error into one `theta_3`. -/
theorem fl_dividedDifferenceStep_entry_gamma3
    (fp : FPModel) (nodes coeffs : ℕ → ℝ) {k j : ℕ}
    (hj : k < j)
    (hden : nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat :
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 3 ∧
        fl_dividedDifferenceStep fp nodes coeffs k j =
          dividedDifferenceStep nodes coeffs k j * (1 + θ) := by
  rcases fl_dividedDifferenceStep_entry_error_factors
      fp nodes coeffs hj hden hdenHat with
    ⟨δnum, δden, δdiv, hδnum, hδden, hδdiv, hstep⟩
  let δ : Fin 3 → ℝ := fun i =>
    if i = 0 then δnum else if i = 1 then δden else δdiv
  let neg : Fin 3 → Bool := fun i => if i = 1 then true else false
  have hδ : ∀ i : Fin 3, |δ i| ≤ fp.u := by
    intro i
    fin_cases i <;> simp [δ, hδnum, hδden, hδdiv]
  rcases prod_signed_error_bound fp 3 δ neg hδ hγ with
    ⟨θ, hθ, hprod⟩
  refine ⟨θ, hθ, ?_⟩
  have hprodEval :
      (∏ i : Fin 3,
          if neg i = true then 1 / (1 + δ i) else 1 + δ i) =
        (1 + δnum) * (1 / (1 + δden)) * (1 + δdiv) := by
    rw [Fin.prod_univ_three]
    simp [δ, neg]
  have hfactor :
      ((1 + δnum) / (1 + δden)) * (1 + δdiv) = 1 + θ := by
    calc
      ((1 + δnum) / (1 + δden)) * (1 + δdiv)
          = (1 + δnum) * (1 / (1 + δden)) * (1 + δdiv) := by
            simp [div_eq_mul_inv]
      _ = 1 + θ := by
            rw [← hprod, hprodEval]
  calc
    fl_dividedDifferenceStep fp nodes coeffs k j
        = dividedDifferenceStep nodes coeffs k j *
            (((1 + δnum) / (1 + δden)) * (1 + δdiv)) := by
          rw [hstep]
          ring
    _ = dividedDifferenceStep nodes coeffs k j * (1 + θ) := by
          rw [hfactor]

/-- Finite `gamma_3` adapter for Higham (5.9): under the active-row
nonzero-denominator hypotheses, the rounded finite divided-difference sweep is
represented rowwise by a finite `G_k L_k` action whose active diagonal factors
are all within `gamma fp 3` of one. -/
theorem fl_dividedDifferenceStep_exists_GMatrixAction_gamma3
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ)
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta : ℕ → ℝ,
      (∀ i : Fin (n + 1), k < i.val →
        |eta i.val - 1| ≤ gamma fp 3) ∧
      ∀ i : Fin (n + 1),
        fl_dividedDifferenceStep fp nodes
            (dividedDifferenceFinToNat v) k i.val =
          dividedDifferenceGMatrixAction eta n k
            (dividedDifferenceLMatrixAction nodes n k v) i := by
  classical
  let theta : ℕ → ℝ := fun j =>
    if hjk : k < j then
      if hjn : j < n + 1 then
        Classical.choose
          (fl_dividedDifferenceStep_entry_gamma3 fp nodes
            (dividedDifferenceFinToNat v) hjk
            (hden j hjk hjn) (hdenHat j hjk hjn) hγ)
      else
        0
    else
      0
  let eta : ℕ → ℝ := fun j => 1 + theta j
  refine ⟨eta, ?_, ?_⟩
  · intro i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hi
        (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)
    have htheta :
        theta i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat v) hi
              (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have hetaDiff : eta i.val - 1 = theta i.val := by
      simp [eta]
    rw [hetaDiff, htheta]
    exact hspec.1
  · apply fl_dividedDifferenceStep_eq_GMatrixAction_of_row_factors
    intro i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hi
        (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)
    have htheta :
        theta i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat v) hi
              (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have heta :
        eta i.val =
          1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat v) hi
                (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ) := by
      simp [eta, htheta]
    calc
      fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat v) k i.val =
        dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val *
          (1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat v) hi
                (hden i.val hi i.isLt) (hdenHat i.val hi i.isLt) hγ)) := hspec.2
      _ = eta i.val *
          dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val := by
            rw [heta]
            ring

/-- Componentwise finite-row error consequence of the `gamma_3` divided
difference model.  This is the rowwise absolute-error bridge used before
assembling the product/residual bounds (5.10)-(5.12). -/
theorem fl_dividedDifferenceStep_finite_abs_error_gamma3
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ)
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat v) k i.val -
        dividedDifferenceLMatrixAction nodes n k v i| ≤
        gamma fp 3 *
          |dividedDifferenceLMatrixAction nodes n k v i| := by
  intro i
  by_cases hi : i.val ≤ k
  · rw [fl_dividedDifferenceStep_of_le fp nodes
      (dividedDifferenceFinToNat v) hi,
      dividedDifferenceLMatrixAction_of_le nodes v hi]
    simp [dividedDifferenceFinToNat, i.isLt,
      mul_nonneg (gamma_nonneg fp hγ) (abs_nonneg (v i))]
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rcases fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hgt
        (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ with
      ⟨θ, hθ, hfl⟩
    rw [dividedDifferenceLMatrixAction_eq_step nodes v i, hfl]
    set exactRow :=
      dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val
    have hdiff : exactRow * (1 + θ) - exactRow = exactRow * θ := by
      ring
    calc
      |exactRow * (1 + θ) - exactRow|
          = |exactRow * θ| := by rw [hdiff]
      _ = |exactRow| * |θ| := abs_mul exactRow θ
      _ ≤ |exactRow| * gamma fp 3 :=
            mul_le_mul_of_nonneg_left hθ (abs_nonneg exactRow)
      _ = gamma fp 3 * |exactRow| := by ring

/-- One-sweep magnitude consequence of the finite `gamma_3` divided-difference
model.  This packages the local row factors in the `|computed| <=
(1+gamma_3)|exact L_k row|` form used by product-style bounds. -/
theorem fl_dividedDifferenceStep_finite_abs_le_one_plus_gamma3
    (fp : FPModel) (nodes : ℕ → ℝ) {n k : ℕ}
    (v : Fin (n + 1) → ℝ)
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceStep fp nodes
          (dividedDifferenceFinToNat v) k i.val| ≤
        (1 + gamma fp 3) *
          |dividedDifferenceLMatrixAction nodes n k v i| := by
  intro i
  by_cases hi : i.val ≤ k
  · rw [fl_dividedDifferenceStep_of_le fp nodes
      (dividedDifferenceFinToNat v) hi,
      dividedDifferenceLMatrixAction_of_le nodes v hi]
    simp [dividedDifferenceFinToNat, i.isLt]
    have hcoef : (1 : ℝ) ≤ 1 + gamma fp 3 := by
      linarith [gamma_nonneg fp hγ]
    calc
      |v i| = (1 : ℝ) * |v i| := by ring
      _ ≤ (1 + gamma fp 3) * |v i| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg (v i))
  · have hgt : k < i.val := Nat.lt_of_not_ge hi
    rcases fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat v) hgt
        (hden i.val hgt i.isLt) (hdenHat i.val hgt i.isLt) hγ with
      ⟨θ, hθ, hfl⟩
    rw [dividedDifferenceLMatrixAction_eq_step nodes v i, hfl]
    set exactRow :=
      dividedDifferenceStep nodes (dividedDifferenceFinToNat v) k i.val
    have htheta :
        |1 + θ| ≤ 1 + gamma fp 3 := by
      calc
        |1 + θ| ≤ |(1 : ℝ)| + |θ| := abs_add_le 1 θ
        _ ≤ 1 + gamma fp 3 := by
              simpa using add_le_add_left hθ (1 : ℝ)
    calc
      |exactRow * (1 + θ)| = |exactRow| * |1 + θ| :=
        abs_mul exactRow (1 + θ)
      _ ≤ |exactRow| * (1 + gamma fp 3) :=
            mul_le_mul_of_nonneg_left htheta (abs_nonneg exactRow)
      _ = (1 + gamma fp 3) * |exactRow| := by ring

/-- Rounded finite-column form of Higham (5.9): the computed successor column
is a finite `G_k L_k` action on the previous computed column, with active
diagonal factors within `gamma fp 3` of one. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_exists_GMatrixAction_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta : ℕ → ℝ,
      (∀ i : Fin (n + 1), k < i.val →
        |eta i.val - 1| ≤ gamma fp 3) ∧
      ∀ i : Fin (n + 1),
        fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
          dividedDifferenceGMatrixAction eta n k
            (dividedDifferenceLMatrixAction nodes n k
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) i := by
  simpa [fl_dividedDifferenceFiniteCoeffs] using
    (fl_dividedDifferenceStep_exists_GMatrixAction_gamma3 fp nodes
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)
      hden hdenHat hγ)

/-- Componentwise one-step error for the rounded finite divided-difference
coefficient columns. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_abs_error_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i -
        dividedDifferenceLMatrixAction nodes n k
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| ≤
        gamma fp 3 *
          |dividedDifferenceLMatrixAction nodes n k
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| := by
  simpa [fl_dividedDifferenceFiniteCoeffs] using
    (fl_dividedDifferenceStep_finite_abs_error_gamma3 fp nodes
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)
      hden hdenHat hγ)

/-- One-step magnitude bound for the rounded finite divided-difference
coefficient columns. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_abs_le_one_plus_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i| ≤
        (1 + gamma fp 3) *
          |dividedDifferenceLMatrixAction nodes n k
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| := by
  simpa [fl_dividedDifferenceFiniteCoeffs] using
    (fl_dividedDifferenceStep_finite_abs_le_one_plus_gamma3 fp nodes
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)
      hden hdenHat hγ)

/-- Absolute-matrix one-step majorant for the rounded finite divided-difference
coefficient columns: `|computed c^(k+1)| <= (1+gamma_3)|L_k| |computed c^k|`. -/
theorem fl_dividedDifferenceFiniteCoeffs_succ_abs_le_absL_one_plus_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n k : ℕ}
    (hden : ∀ j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i| ≤
        (1 + gamma fp 3) *
          dividedDifferenceAbsLMatrixAction nodes n k
            (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n k j|) i := by
  intro i
  have hstep :=
    fl_dividedDifferenceFiniteCoeffs_succ_abs_le_one_plus_gamma3
      fp nodes f hden hdenHat hγ i
  have habs :=
    abs_dividedDifferenceLMatrixAction_le_absLMatrixAction nodes n k
      (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i
  have hscale_nonneg : 0 ≤ 1 + gamma fp 3 := by
    linarith [gamma_nonneg fp hγ]
  calc
    |fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i|
        ≤ (1 + gamma fp 3) *
          |dividedDifferenceLMatrixAction nodes n k
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n k) i| := hstep
    _ ≤ (1 + gamma fp 3) *
          dividedDifferenceAbsLMatrixAction nodes n k
            (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n k j|) i :=
          mul_le_mul_of_nonneg_left habs hscale_nonneg

/-- Multi-step absolute product majorant for the rounded finite
divided-difference coefficient columns. -/
theorem fl_dividedDifferenceFiniteCoeffs_abs_le_absLProduct_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i| ≤
        dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
          (fun i : Fin (n + 1) => |f i.val|) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hstep :=
        fl_dividedDifferenceFiniteCoeffs_succ_abs_le_absL_one_plus_gamma3
          fp nodes f
          (fun j hjk hjn => hden m j hjk hjn)
          (fun j hjk hjn => hdenHat m j hjk hjn)
          hγ i
      have hmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n m j|)
          (dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
            (fun i : Fin (n + 1) => |f i.val|))
          ih i
      have hscale_nonneg : 0 ≤ 1 + gamma fp 3 := by
        linarith [gamma_nonneg fp hγ]
      calc
        |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i|
            ≤ (1 + gamma fp 3) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (fun j => |fl_dividedDifferenceFiniteCoeffs fp nodes f n m j|)
                i := hstep
        _ ≤ (1 + gamma fp 3) *
              dividedDifferenceAbsLMatrixAction nodes n m
                (dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
                  (fun i : Fin (n + 1) => |f i.val|)) i :=
              mul_le_mul_of_nonneg_left hmono hscale_nonneg
        _ = dividedDifferenceAbsLProductAction nodes (gamma fp 3) n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i := rfl

/-- Componentwise product perturbation bound for computed divided-difference
columns.  This is the finite-vector form of Higham (5.10)-(5.11): the
computed column differs from the exact `L_{m-1} ... L_0 f` column by the gap
between the rounded absolute product majorant and the exact absolute product
majorant. -/
theorem fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_absLProduct_gap_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
        dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
          (fun i : Fin (n + 1) => |f i.val|) i -
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
  induction m with
  | zero =>
      intro i
      simp [fl_dividedDifferenceFiniteCoeffs, dividedDifferenceFiniteCoeffs,
        dividedDifferenceAbsLProductAction]
  | succ m ih =>
      intro i
      let γ := gamma fp 3
      let flm : Fin (n + 1) → ℝ :=
        fl_dividedDifferenceFiniteCoeffs fp nodes f n m
      let exactm : Fin (n + 1) → ℝ :=
        dividedDifferenceFiniteCoeffs nodes f n m
      let pg : Fin (n + 1) → ℝ :=
        dividedDifferenceAbsLProductAction nodes γ n m
          (fun i : Fin (n + 1) => |f i.val|)
      let p0 : Fin (n + 1) → ℝ :=
        dividedDifferenceAbsLProductAction nodes 0 n m
          (fun i : Fin (n + 1) => |f i.val|)
      have hγ_nonneg : 0 ≤ γ := by
        exact gamma_nonneg fp hγ
      have hlocal :=
        fl_dividedDifferenceFiniteCoeffs_succ_abs_error_gamma3
          fp nodes f
          (fun j hjk hjn => hden m j hjk hjn)
          (fun j hjk hjn => hdenHat m j hjk hjn)
          hγ i
      have hrowabs :=
        abs_dividedDifferenceLMatrixAction_le_absLMatrixAction nodes n m
          flm i
      have hflabs :
          ∀ j : Fin (n + 1), |flm j| ≤ pg j := by
        intro j
        exact
          fl_dividedDifferenceFiniteCoeffs_abs_le_absLProduct_gamma3
            fp nodes f m hden hdenHat hγ j
      have hflmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |flm j|) pg hflabs i
      have hlocal_pg :
          |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
            dividedDifferenceLMatrixAction nodes n m flm i| ≤
            γ * dividedDifferenceAbsLMatrixAction nodes n m pg i := by
        calc
          |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
            dividedDifferenceLMatrixAction nodes n m flm i|
              ≤ γ * |dividedDifferenceLMatrixAction nodes n m flm i| := by
                simpa [γ, flm] using hlocal
          _ ≤ γ *
              dividedDifferenceAbsLMatrixAction nodes n m
                (fun j => |flm j|) i :=
                mul_le_mul_of_nonneg_left hrowabs hγ_nonneg
          _ ≤ γ * dividedDifferenceAbsLMatrixAction nodes n m pg i :=
                mul_le_mul_of_nonneg_left hflmono hγ_nonneg
      have hprop0 :=
        abs_dividedDifferenceLMatrixAction_sub_le_absLMatrixAction nodes n m
          flm exactm i
      have hgap_prev :
          ∀ j : Fin (n + 1), |flm j - exactm j| ≤ pg j - p0 j := by
        intro j
        simpa [flm, exactm, pg, p0, γ] using ih j
      have hpropmono :=
        dividedDifferenceAbsLMatrixAction_mono nodes n m
          (fun j => |flm j - exactm j|)
          (fun j => pg j - p0 j) hgap_prev i
      have hprop_gap :
          |dividedDifferenceLMatrixAction nodes n m flm i -
            dividedDifferenceLMatrixAction nodes n m exactm i| ≤
            dividedDifferenceAbsLMatrixAction nodes n m
              (fun j => pg j - p0 j) i := by
        exact le_trans hprop0 hpropmono
      have htri :
          |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
            dividedDifferenceFiniteCoeffs nodes f n (m + 1) i| ≤
            |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceLMatrixAction nodes n m flm i| +
            |dividedDifferenceLMatrixAction nodes n m flm i -
              dividedDifferenceLMatrixAction nodes n m exactm i| := by
        have hsplit :
            fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceFiniteCoeffs nodes f n (m + 1) i =
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceLMatrixAction nodes n m flm i) +
            (dividedDifferenceLMatrixAction nodes n m flm i -
              dividedDifferenceLMatrixAction nodes n m exactm i) := by
          simp [exactm, dividedDifferenceFiniteCoeffs_succ]
        rw [hsplit]
        exact abs_add_le _ _
      have hAbsSub :
          dividedDifferenceAbsLMatrixAction nodes n m
            (fun j => pg j - p0 j) i =
          dividedDifferenceAbsLMatrixAction nodes n m pg i -
            dividedDifferenceAbsLMatrixAction nodes n m p0 i :=
        dividedDifferenceAbsLMatrixAction_sub nodes n m pg p0 i
      calc
        |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
          dividedDifferenceFiniteCoeffs nodes f n (m + 1) i|
            ≤
            |fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i -
              dividedDifferenceLMatrixAction nodes n m flm i| +
            |dividedDifferenceLMatrixAction nodes n m flm i -
              dividedDifferenceLMatrixAction nodes n m exactm i| := htri
        _ ≤ γ * dividedDifferenceAbsLMatrixAction nodes n m pg i +
            dividedDifferenceAbsLMatrixAction nodes n m
              (fun j => pg j - p0 j) i :=
              add_le_add hlocal_pg hprop_gap
        _ = dividedDifferenceAbsLProductAction nodes (gamma fp 3) n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i -
            dividedDifferenceAbsLProductAction nodes 0 n (m + 1)
              (fun i : Fin (n + 1) => |f i.val|) i := by
              simp [dividedDifferenceAbsLProductAction, pg, p0, γ, hAbsSub]
              ring

/-- Source-shaped scalar form of the divided-difference product perturbation
bound.  Since the same `gamma_3` factor is used at every step, the absolute
product gap equals `((1+gamma_3)^m - 1) |L_{m-1}| ... |L_0| |f|`. -/
theorem fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_scalar_absLProduct_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∀ i : Fin (n + 1),
      |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
        dividedDifferenceFiniteCoeffs nodes f n m i| ≤
        ((1 + gamma fp 3) ^ m - 1) *
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
  intro i
  have hgap :=
    fl_dividedDifferenceFiniteCoeffs_abs_sub_exact_le_absLProduct_gap_gamma3
      fp nodes f m hden hdenHat hγ i
  have hconst :=
    dividedDifferenceAbsLProductAction_const_gamma nodes (gamma fp 3) n m
      (fun i : Fin (n + 1) => |f i.val|) i
  calc
    |fl_dividedDifferenceFiniteCoeffs fp nodes f n m i -
      dividedDifferenceFiniteCoeffs nodes f n m i|
        ≤ dividedDifferenceAbsLProductAction nodes (gamma fp 3) n m
            (fun i : Fin (n + 1) => |f i.val|) i -
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := hgap
    _ = ((1 + gamma fp 3) ^ m - 1) *
          dividedDifferenceAbsLProductAction nodes 0 n m
            (fun i : Fin (n + 1) => |f i.val|) i := by
          rw [hconst]
          ring

/-- Natural-index helper for the inverse of Higham's divided-difference
matrix `L_k`. Rows `0:k` are copied; later rows reconstruct by the recurrence
`z_j = z_{j-1} + (alpha_j - alpha_{j-k-1}) w_j`. -/
noncomputable def dividedDifferenceLInvActionNat
    (nodes : ℕ → ℝ) (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => w 0
  | j + 1 =>
      if j + 1 ≤ k then
        w (j + 1)
      else
        dividedDifferenceLInvActionNat nodes k w j +
          (nodes (j + 1) - nodes (j + 1 - k - 1)) * w (j + 1)

/-- Finite inverse action `L_k^{-1}` for the divided-difference matrix. -/
noncomputable def dividedDifferenceLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ) (w : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i =>
    dividedDifferenceLInvActionNat nodes k (dividedDifferenceFinToNat w) i.val

/-- Natural-index helper for the absolute inverse action `|L_k^{-1}|`. -/
noncomputable def dividedDifferenceAbsLInvActionNat
    (nodes : ℕ → ℝ) (k : ℕ) (w : ℕ → ℝ) : ℕ → ℝ
  | 0 => w 0
  | j + 1 =>
      if j + 1 ≤ k then
        w (j + 1)
      else
        dividedDifferenceAbsLInvActionNat nodes k w j +
          |nodes (j + 1) - nodes (j + 1 - k - 1)| * w (j + 1)

/-- Absolute majorant action `|L_k^{-1}| v`. -/
noncomputable def dividedDifferenceAbsLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ) (w : Fin (n + 1) → ℝ) :
    Fin (n + 1) → ℝ :=
  fun i =>
    dividedDifferenceAbsLInvActionNat nodes k (dividedDifferenceFinToNat w) i.val

theorem dividedDifferenceLInvAction_of_le
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceLInvAction nodes n k w i = w i := by
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i _ =>
      simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat, hi,
        dividedDifferenceFinToNat, hi_lt]

theorem dividedDifferenceLInvAction_of_gt
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceLInvAction nodes n k w i =
      dividedDifferenceLInvAction nodes n k w (dividedDifferenceFinPred i) +
        (nodes i.val - nodes (i.val - k - 1)) * w i := by
  rcases i with ⟨i, hi_lt⟩
  cases i with
  | zero =>
      exact (Nat.not_lt_zero k hi).elim
  | succ i =>
      have hnot : ¬ i + 1 ≤ k := Nat.not_le_of_gt hi
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      have hi_lt_n : i < n := Nat.succ_lt_succ_iff.mp hi_lt
      simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat, hnot,
        dividedDifferenceFinToNat, dividedDifferenceFinPred, hi_lt_n]

theorem dividedDifferenceAbsLInvAction_of_le
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : i.val ≤ k) :
    dividedDifferenceAbsLInvAction nodes n k w i = w i := by
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i _ =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        hi, dividedDifferenceFinToNat, hi_lt]

theorem dividedDifferenceAbsLInvAction_of_gt
    (nodes : ℕ → ℝ) {n k : ℕ} (w : Fin (n + 1) → ℝ)
    {i : Fin (n + 1)} (hi : k < i.val) :
    dividedDifferenceAbsLInvAction nodes n k w i =
      dividedDifferenceAbsLInvAction nodes n k w (dividedDifferenceFinPred i) +
        |nodes i.val - nodes (i.val - k - 1)| * w i := by
  rcases i with ⟨i, hi_lt⟩
  cases i with
  | zero =>
      exact (Nat.not_lt_zero k hi).elim
  | succ i =>
      have hnot : ¬ i + 1 ≤ k := Nat.not_le_of_gt hi
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      have hi_lt_n : i < n := Nat.succ_lt_succ_iff.mp hi_lt
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        hnot, dividedDifferenceFinToNat, dividedDifferenceFinPred, hi_lt_n]

/-- Componentwise absolute-value domination for one exact inverse action:
`|L_k^{-1} v| <= |L_k^{-1}| |v|`. -/
theorem abs_dividedDifferenceLInvAction_le_absLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLInvAction nodes n k v i| ≤
        dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
        dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
          dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hstep :
            |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i| ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j|)) i := by
          simpa [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction]
            using ih hpred_lt
        have hmul :
            |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat v (i + 1)| =
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1)| := by
          rw [abs_mul]
        calc
          |dividedDifferenceLInvAction nodes n k v ⟨i + 1, hi_lt⟩|
              =
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  dividedDifferenceFinToNat v (i + 1)| := by
                simp [dividedDifferenceLInvAction, dividedDifferenceLInvActionNat,
                  hle]
          _ ≤
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i| +
              |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat v (i + 1)| :=
                abs_add_le _ _
          _ =
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i| +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1)| := by rw [hmul]
          _ ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j|)) i +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1)| :=
                add_le_add hstep (le_refl _)
          _ =
              dividedDifferenceAbsLInvAction nodes n k
                (fun j : Fin (n + 1) => |v j|) ⟨i + 1, hi_lt⟩ := by
                simp [dividedDifferenceAbsLInvAction,
                  dividedDifferenceAbsLInvActionNat, hle,
                  dividedDifferenceFinToNat, hi_lt]

theorem dividedDifferenceAbsLInvAction_nonneg
    (nodes : ℕ → ℝ) (n k : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLInvAction nodes n k v i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt] using hv ⟨0, hi_lt⟩
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt] using hv ⟨i + 1, hi_lt⟩
      · have hprev :
            0 ≤ dividedDifferenceAbsLInvActionNat nodes k
              (dividedDifferenceFinToNat v) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        have hterm :
            0 ≤ |nodes (i + 1) - nodes (i + 1 - k - 1)| *
              dividedDifferenceFinToNat v (i + 1) := by
          exact mul_nonneg (abs_nonneg _)
            (by simpa [dividedDifferenceFinToNat, hi_lt] using
              hv ⟨i + 1, hi_lt⟩)
        simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle] using add_nonneg hprev hterm

/-- Monotonicity of the absolute inverse action. -/
theorem dividedDifferenceAbsLInvAction_mono
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ)
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, dividedDifferenceAbsLInvAction nodes n k v i ≤
      dividedDifferenceAbsLInvAction nodes n k w i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt] using hvw ⟨0, hi_lt⟩
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt] using hvw ⟨i + 1, hi_lt⟩
      · have hprev :
            dividedDifferenceAbsLInvActionNat nodes k
              (dividedDifferenceFinToNat v) i ≤
            dividedDifferenceAbsLInvActionNat nodes k
              (dividedDifferenceFinToNat w) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        have hterm :
            |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                dividedDifferenceFinToNat v (i + 1) ≤
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                dividedDifferenceFinToNat w (i + 1) := by
          exact mul_le_mul_of_nonneg_left
            (by simpa [dividedDifferenceFinToNat, hi_lt] using
              hvw ⟨i + 1, hi_lt⟩)
            (abs_nonneg _)
        simpa [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle] using add_le_add hprev hterm

/-- Linearity of `|L_k^{-1}|` with respect to subtraction in the vector
argument. -/
theorem dividedDifferenceAbsLInvAction_sub
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLInvAction nodes n k
        (fun j => v j - w j) i =
      dividedDifferenceAbsLInvAction nodes n k v i -
        dividedDifferenceAbsLInvAction nodes n k w i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hih :
            dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => v j - w j)) i =
              dividedDifferenceAbsLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i -
                dividedDifferenceAbsLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt, hih]
        ring

/-- Linearity of `|L_k^{-1}|` with respect to scalar multiplication in the
vector argument. -/
theorem dividedDifferenceAbsLInvAction_smul
    (nodes : ℕ → ℝ) (n k : ℕ) (a : ℝ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLInvAction nodes n k
        (fun j => a * v j) i =
      a * dividedDifferenceAbsLInvAction nodes n k v i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hih :
            dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => a * v j)) i =
              a * dividedDifferenceAbsLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i := by
          simpa [dividedDifferenceAbsLInvAction] using ih hpred_lt
        simp [dividedDifferenceAbsLInvAction, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt, hih]
        ring

theorem abs_dividedDifferenceLInvAction_sub_le_absLInvAction
    (nodes : ℕ → ℝ) (n k : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLInvAction nodes n k v i -
          dividedDifferenceLInvAction nodes n k w i| ≤
        dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j - w j|) i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
        dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
        dividedDifferenceFinToNat, hi_lt]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · simp [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction,
          dividedDifferenceLInvActionNat, dividedDifferenceAbsLInvActionNat,
          hle, dividedDifferenceFinToNat, hi_lt]
      · have hih :
            |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
              dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat w) i| ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j - w j|)) i := by
          simpa [dividedDifferenceLInvAction, dividedDifferenceAbsLInvAction]
            using ih hpred_lt
        have hmul :
            |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                (dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1))| =
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1)| := by
          rw [abs_mul]
        have htri :
            |(dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat v (i + 1)) -
              (dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat w) i +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceFinToNat w (i + 1))| ≤
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
                dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i| +
              |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                (dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1))| := by
          have hsplit :
              (dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  dividedDifferenceFinToNat v (i + 1)) -
                (dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  dividedDifferenceFinToNat w (i + 1)) =
                (dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat v) i -
                  dividedDifferenceLInvActionNat nodes k
                    (dividedDifferenceFinToNat w) i) +
                (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                  (dividedDifferenceFinToNat v (i + 1) -
                    dividedDifferenceFinToNat w (i + 1)) := by
            ring
          rw [hsplit]
          exact abs_add_le _ _
        calc
          |dividedDifferenceLInvAction nodes n k v ⟨i + 1, hi_lt⟩ -
            dividedDifferenceLInvAction nodes n k w ⟨i + 1, hi_lt⟩|
              ≤
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
                dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i| +
              |(nodes (i + 1) - nodes (i + 1 - k - 1)) *
                (dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1))| := by
                simpa [dividedDifferenceLInvAction,
                  dividedDifferenceLInvActionNat, hle] using htri
          _ =
              |dividedDifferenceLInvActionNat nodes k
                (dividedDifferenceFinToNat v) i -
                dividedDifferenceLInvActionNat nodes k
                  (dividedDifferenceFinToNat w) i| +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1)| := by rw [hmul]
          _ ≤
              dividedDifferenceAbsLInvActionNat nodes k
                (dividedDifferenceFinToNat
                  (fun j : Fin (n + 1) => |v j - w j|)) i +
              |nodes (i + 1) - nodes (i + 1 - k - 1)| *
                |dividedDifferenceFinToNat v (i + 1) -
                  dividedDifferenceFinToNat w (i + 1)| :=
                add_le_add hih (le_refl _)
          _ =
              dividedDifferenceAbsLInvAction nodes n k
                (fun j : Fin (n + 1) => |v j - w j|)
                ⟨i + 1, hi_lt⟩ := by
                simp [dividedDifferenceAbsLInvAction,
                  dividedDifferenceAbsLInvActionNat, hle,
                  dividedDifferenceFinToNat, hi_lt]

/-- The recursive inverse action is a left inverse of the finite
divided-difference action. -/
theorem dividedDifferenceLInvAction_LMatrixAction_eq
    (nodes : ℕ → ℝ) {n k : ℕ} (v : Fin (n + 1) → ℝ)
    (hden : ∀ i : Fin (n + 1), k < i.val →
      nodes i.val - nodes (i.val - k - 1) ≠ 0) :
    ∀ i : Fin (n + 1),
      dividedDifferenceLInvAction nodes n k
        (dividedDifferenceLMatrixAction nodes n k v) i = v i := by
  intro i
  rcases i with ⟨i, hi_lt⟩
  induction i with
  | zero =>
      have hle : (0 : ℕ) ≤ k := Nat.zero_le k
      rw [dividedDifferenceLInvAction_of_le
        (i := ⟨0, hi_lt⟩) nodes
        (dividedDifferenceLMatrixAction nodes n k v) hle,
        dividedDifferenceLMatrixAction_of_le
          (i := ⟨0, hi_lt⟩) nodes v hle]
  | succ i ih =>
      have hpred_lt : i < n + 1 :=
        Nat.lt_trans (Nat.lt_succ_self i) hi_lt
      by_cases hle : i + 1 ≤ k
      · have hrow : (⟨i + 1, hi_lt⟩ : Fin (n + 1)).val ≤ k := hle
        rw [dividedDifferenceLInvAction_of_le
          (i := ⟨i + 1, hi_lt⟩) nodes
          (dividedDifferenceLMatrixAction nodes n k v) hrow,
          dividedDifferenceLMatrixAction_of_le
            (i := ⟨i + 1, hi_lt⟩) nodes v hrow]
      · have hgt : k < i + 1 := Nat.lt_of_not_ge hle
        have hrow :
            dividedDifferenceLMatrixAction nodes n k v ⟨i + 1, hi_lt⟩ =
              (v ⟨i + 1, hi_lt⟩ - v (dividedDifferenceFinPred ⟨i + 1, hi_lt⟩)) /
                (nodes (i + 1) - nodes (i + 1 - k - 1)) :=
          dividedDifferenceLMatrixAction_of_gt nodes v hgt
        have hpred :
            dividedDifferenceFinPred (⟨i + 1, hi_lt⟩ : Fin (n + 1)) =
              ⟨i, hpred_lt⟩ := by
          simp [dividedDifferenceFinPred]
        have hprev :
            dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              (dividedDifferenceFinPred ⟨i + 1, hi_lt⟩) =
              v ⟨i, hpred_lt⟩ := by
          rw [hpred]
          exact ih hpred_lt
        have hprev' :
            dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              ⟨i, hpred_lt⟩ =
              v ⟨i, hpred_lt⟩ :=
          ih hpred_lt
        have hden' :
            nodes (i + 1) - nodes (i + 1 - k - 1) ≠ 0 :=
          hden ⟨i + 1, hi_lt⟩ hgt
        calc
          dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              ⟨i + 1, hi_lt⟩ =
            dividedDifferenceLInvAction nodes n k
              (dividedDifferenceLMatrixAction nodes n k v)
              (dividedDifferenceFinPred ⟨i + 1, hi_lt⟩) +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                dividedDifferenceLMatrixAction nodes n k v ⟨i + 1, hi_lt⟩ := by
              rw [dividedDifferenceLInvAction_of_gt
                (i := ⟨i + 1, hi_lt⟩) nodes
                (dividedDifferenceLMatrixAction nodes n k v) hgt]
          _ =
            v ⟨i, hpred_lt⟩ +
              (nodes (i + 1) - nodes (i + 1 - k - 1)) *
                ((v ⟨i + 1, hi_lt⟩ - v ⟨i, hpred_lt⟩) /
                  (nodes (i + 1) - nodes (i + 1 - k - 1))) := by
              simp [hprev', hrow, hpred]
          _ = v ⟨i + 1, hi_lt⟩ := by
              field_simp [hden']
              ring

/-- Exact inverse product `L_0^{-1} ... L_{m-1}^{-1}`. -/
noncomputable def dividedDifferenceLInvProductAction
    (nodes : ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceLInvProductAction nodes n k
        (dividedDifferenceLInvAction nodes n k v)

/-- Absolute inverse product `|L_0^{-1}| ... |L_{m-1}^{-1}|`. -/
noncomputable def dividedDifferenceAbsLInvProductAction
    (nodes : ℕ → ℝ) (n : ℕ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferenceAbsLInvProductAction nodes n k
        (dividedDifferenceAbsLInvAction nodes n k v)

theorem dividedDifferenceAbsLInvProductAction_nonneg
    (nodes : ℕ → ℝ) (n m : ℕ) (v : Fin (n + 1) → ℝ)
    (hv : ∀ i, 0 ≤ v i) :
    ∀ i, 0 ≤ dividedDifferenceAbsLInvProductAction nodes n m v i := by
  induction m generalizing v with
  | zero =>
      intro i
      exact hv i
  | succ m ih =>
      exact ih
        (dividedDifferenceAbsLInvAction nodes n m v)
        (dividedDifferenceAbsLInvAction_nonneg nodes n m v hv)

theorem dividedDifferenceAbsLInvProductAction_mono
    (nodes : ℕ → ℝ) (n m : ℕ)
    (v w : Fin (n + 1) → ℝ)
    (hvw : ∀ i, v i ≤ w i) :
    ∀ i, dividedDifferenceAbsLInvProductAction nodes n m v i ≤
      dividedDifferenceAbsLInvProductAction nodes n m w i := by
  induction m generalizing v w with
  | zero =>
      intro i
      exact hvw i
  | succ m ih =>
      exact ih
        (dividedDifferenceAbsLInvAction nodes n m v)
        (dividedDifferenceAbsLInvAction nodes n m w)
        (dividedDifferenceAbsLInvAction_mono nodes n m v w hvw)

theorem dividedDifferenceAbsLInvProductAction_smul
    (nodes : ℕ → ℝ) (n m : ℕ) (a : ℝ)
    (v : Fin (n + 1) → ℝ) :
    ∀ i, dividedDifferenceAbsLInvProductAction nodes n m
        (fun j => a * v j) i =
      a * dividedDifferenceAbsLInvProductAction nodes n m v i := by
  induction m generalizing v with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hstep :=
        dividedDifferenceAbsLInvAction_smul nodes n m a v
      have hfun :
          dividedDifferenceAbsLInvAction nodes n m
              (fun j : Fin (n + 1) => a * v j) =
            fun j =>
              a * dividedDifferenceAbsLInvAction nodes n m v j := by
        funext j
        exact hstep j
      simp [dividedDifferenceAbsLInvProductAction, hfun, ih]

theorem abs_dividedDifferenceLInvProductAction_sub_le_absLInvProductAction
    (nodes : ℕ → ℝ) (n m : ℕ)
    (v w : Fin (n + 1) → ℝ) :
    ∀ i : Fin (n + 1),
      |dividedDifferenceLInvProductAction nodes n m v i -
          dividedDifferenceLInvProductAction nodes n m w i| ≤
        dividedDifferenceAbsLInvProductAction nodes n m
          (fun j => |v j - w j|) i := by
  induction m generalizing v w with
  | zero =>
      intro i
      simp [dividedDifferenceLInvProductAction,
        dividedDifferenceAbsLInvProductAction]
  | succ m ih =>
      intro i
      have hlocal :=
        abs_dividedDifferenceLInvAction_sub_le_absLInvAction nodes n m v w
      have hmono :=
        dividedDifferenceAbsLInvProductAction_mono nodes n m
          (fun j =>
            |dividedDifferenceLInvAction nodes n m v j -
              dividedDifferenceLInvAction nodes n m w j|)
          (dividedDifferenceAbsLInvAction nodes n m
            (fun j => |v j - w j|)) hlocal
      calc
        |dividedDifferenceLInvProductAction nodes n (m + 1) v i -
          dividedDifferenceLInvProductAction nodes n (m + 1) w i|
            ≤ dividedDifferenceAbsLInvProductAction nodes n m
                (fun j =>
                  |dividedDifferenceLInvAction nodes n m v j -
                    dividedDifferenceLInvAction nodes n m w j|) i :=
              ih
                (dividedDifferenceLInvAction nodes n m v)
                (dividedDifferenceLInvAction nodes n m w) i
        _ ≤ dividedDifferenceAbsLInvProductAction nodes n m
                (dividedDifferenceAbsLInvAction nodes n m
                  (fun j => |v j - w j|)) i :=
              hmono i
        _ = dividedDifferenceAbsLInvProductAction nodes n (m + 1)
                (fun j => |v j - w j|) i := rfl

/-- The inverse product reconstructs the original data from exact
divided-difference columns. -/
theorem dividedDifferenceLInvProductAction_finiteCoeffs_eq_data
    (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0) :
    ∀ i : Fin (n + 1),
      dividedDifferenceLInvProductAction nodes n m
        (dividedDifferenceFiniteCoeffs nodes f n m) i = f i.val := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hleft :
          dividedDifferenceLInvAction nodes n m
            (dividedDifferenceFiniteCoeffs nodes f n (m + 1)) =
          dividedDifferenceFiniteCoeffs nodes f n m := by
        funext j
        have hden_m :
            ∀ i : Fin (n + 1), m < i.val →
              nodes i.val - nodes (i.val - m - 1) ≠ 0 := by
          intro i hi
          exact hden m i.val hi i.isLt
        simpa [dividedDifferenceFiniteCoeffs_succ] using
          dividedDifferenceLInvAction_LMatrixAction_eq
            nodes (dividedDifferenceFiniteCoeffs nodes f n m) hden_m j
      simpa [dividedDifferenceLInvProductAction, hleft] using ih i

/-- A generic perturbed inverse product used for the residual unwind in
Higham (5.12). The step argument represents
`L_k^{-1} + Delta L_k^{-1}`. -/
noncomputable def dividedDifferencePerturbedLInvProductAction
    {n : ℕ}
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) :
    ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ
  | 0, v => v
  | k + 1, v =>
      dividedDifferencePerturbedLInvProductAction step k (step k v)

theorem dividedDifferencePerturbedLInvProduct_abs_le
    (nodes : ℕ → ℝ) {n : ℕ} (m : ℕ) {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hstep : ∀ k v i,
      |step k v i - dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i) :
    ∀ (v : Fin (n + 1) → ℝ) (i : Fin (n + 1)),
      |dividedDifferencePerturbedLInvProductAction step m v i -
          dividedDifferenceLInvProductAction nodes n m v i| ≤
        ((1 + gamma) ^ m - 1) *
          dividedDifferenceAbsLInvProductAction nodes n m
            (fun j => |v j|) i := by
  induction m with
  | zero =>
      intro v i
      simp [dividedDifferencePerturbedLInvProductAction,
        dividedDifferenceLInvProductAction]
  | succ m ih =>
      intro v i
      let pstep := step m v
      let estep := dividedDifferenceLInvAction nodes n m v
      let avec : Fin (n + 1) → ℝ :=
        dividedDifferenceAbsLInvAction nodes n m (fun j => |v j|)
      have habs_estep :
          ∀ j, |estep j| ≤ avec j := by
        intro j
        simpa [estep, avec] using
          abs_dividedDifferenceLInvAction_le_absLInvAction nodes n m v j
      have hprop_local :
          ∀ j, |pstep j - estep j| ≤ gamma * avec j := by
        intro j
        simpa [pstep, estep, avec] using hstep m v j
      have hlocal_abs :
          ∀ j, |pstep j| ≤ (1 + gamma) * avec j := by
        intro j
        have htri :
            |pstep j| ≤ |pstep j - estep j| + |estep j| := by
          have hsplit : pstep j = (pstep j - estep j) + estep j := by ring
          calc
            |pstep j| = |(pstep j - estep j) + estep j| := by
              exact congrArg abs hsplit
            _ ≤ |pstep j - estep j| + |estep j| :=
              abs_add_le (pstep j - estep j) (estep j)
        calc
          |pstep j| ≤ |pstep j - estep j| + |estep j| := htri
          _ ≤ gamma * avec j + avec j :=
                add_le_add (hprop_local j) (habs_estep j)
          _ = (1 + gamma) * avec j := by ring
      have hscale_nonneg : 0 ≤ 1 + gamma := by linarith
      have hcoef_nonneg : 0 ≤ (1 + gamma) ^ m - 1 := by
        have hpow : 1 ≤ (1 + gamma) ^ m :=
          one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + gamma)
        linarith
      have hpart_pert_bound :
          |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i| ≤
            ((1 + gamma) ^ m - 1) *
              ((1 + gamma) *
                dividedDifferenceAbsLInvProductAction nodes n m avec i) := by
        have hpert_mono :
            ∀ j,
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => |pstep r|) j ≤
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => (1 + gamma) * avec r) j :=
          dividedDifferenceAbsLInvProductAction_mono nodes n m
            (fun r => |pstep r|) (fun r => (1 + gamma) * avec r)
            hlocal_abs
        have hpert_smul :
            dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => (1 + gamma) * avec r) i =
              (1 + gamma) *
                dividedDifferenceAbsLInvProductAction nodes n m avec i :=
          dividedDifferenceAbsLInvProductAction_smul nodes n m
            (1 + gamma) avec i
        calc
          |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i|
              ≤ ((1 + gamma) ^ m - 1) *
                  dividedDifferenceAbsLInvProductAction nodes n m
                    (fun j => |pstep j|) i := ih pstep i
          _ ≤ ((1 + gamma) ^ m - 1) *
                  dividedDifferenceAbsLInvProductAction nodes n m
                    (fun r => (1 + gamma) * avec r) i :=
                mul_le_mul_of_nonneg_left (hpert_mono i) hcoef_nonneg
          _ = ((1 + gamma) ^ m - 1) *
                  ((1 + gamma) *
                    dividedDifferenceAbsLInvProductAction nodes n m avec i) := by
                rw [hpert_smul]
      have hpart_exact_bound :
          |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i| ≤
            gamma * dividedDifferenceAbsLInvProductAction nodes n m avec i := by
        have hprop_mono :
            ∀ j,
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => |pstep r - estep r|) j ≤
              dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => gamma * avec r) j :=
          dividedDifferenceAbsLInvProductAction_mono nodes n m
            (fun r => |pstep r - estep r|)
            (fun r => gamma * avec r) hprop_local
        have hprop_smul :
            dividedDifferenceAbsLInvProductAction nodes n m
                (fun r => gamma * avec r) i =
              gamma *
                dividedDifferenceAbsLInvProductAction nodes n m avec i :=
          dividedDifferenceAbsLInvProductAction_smul nodes n m gamma avec i
        calc
          |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i|
              ≤ dividedDifferenceAbsLInvProductAction nodes n m
                  (fun j => |pstep j - estep j|) i :=
                abs_dividedDifferenceLInvProductAction_sub_le_absLInvProductAction
                  nodes n m pstep estep i
          _ ≤ dividedDifferenceAbsLInvProductAction nodes n m
                  (fun r => gamma * avec r) i := hprop_mono i
          _ = gamma * dividedDifferenceAbsLInvProductAction nodes n m avec i :=
                hprop_smul
      have htri :
          |dividedDifferencePerturbedLInvProductAction step (m + 1) v i -
              dividedDifferenceLInvProductAction nodes n (m + 1) v i| ≤
            |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i| +
            |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i| := by
        have hsplit :
            dividedDifferencePerturbedLInvProductAction step (m + 1) v i -
              dividedDifferenceLInvProductAction nodes n (m + 1) v i =
            (dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i) +
            (dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i) := by
          simp [dividedDifferencePerturbedLInvProductAction,
            dividedDifferenceLInvProductAction, pstep, estep]
        rw [hsplit]
        exact abs_add_le _ _
      calc
        |dividedDifferencePerturbedLInvProductAction step (m + 1) v i -
          dividedDifferenceLInvProductAction nodes n (m + 1) v i|
            ≤
            |dividedDifferencePerturbedLInvProductAction step m pstep i -
              dividedDifferenceLInvProductAction nodes n m pstep i| +
            |dividedDifferenceLInvProductAction nodes n m pstep i -
              dividedDifferenceLInvProductAction nodes n m estep i| := htri
        _ ≤ ((1 + gamma) ^ m - 1) *
              ((1 + gamma) *
                dividedDifferenceAbsLInvProductAction nodes n m avec i) +
            gamma * dividedDifferenceAbsLInvProductAction nodes n m avec i :=
              add_le_add hpart_pert_bound hpart_exact_bound
        _ = ((1 + gamma) ^ (m + 1) - 1) *
              dividedDifferenceAbsLInvProductAction nodes n (m + 1)
                (fun j => |v j|) i := by
              simp [dividedDifferenceAbsLInvProductAction, avec, pow_succ]
              ring

/-- Higham (5.12), finite residual form. If the original data vector is
obtained by unwinding the computed divided differences with inverse steps
`L_k^{-1} + Delta L_k^{-1}`, and each such step has componentwise relative
majorant `gamma`, then exact Newton reconstruction with
`L_0^{-1}...L_{m-1}^{-1}` has the source residual bound. -/
theorem dividedDifferenceResidual_error_bound
    (nodes : ℕ → ℝ) {n : ℕ} (m : ℕ) {gamma : ℝ}
    (hgamma : 0 ≤ gamma)
    (step : ℕ → (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hstep : ∀ k v i,
      |step k v i - dividedDifferenceLInvAction nodes n k v i| ≤
        gamma * dividedDifferenceAbsLInvAction nodes n k
          (fun j => |v j|) i)
    (f chat : Fin (n + 1) → ℝ)
    (hf : f = dividedDifferencePerturbedLInvProductAction step m chat) :
    ∀ i : Fin (n + 1),
      |f i - dividedDifferenceLInvProductAction nodes n m chat i| ≤
        ((1 + gamma) ^ m - 1) *
          dividedDifferenceAbsLInvProductAction nodes n m
            (fun j => |chat j|) i := by
  intro i
  subst f
  exact dividedDifferencePerturbedLInvProduct_abs_le
    nodes m hgamma step hstep chat i

/-- Product-form adapter for Higham (5.10): if every active rounded row update
has the supplied multiplicative factor `eta k j`, then the `m`th computed
finite divided-difference column is the iterated product
`G_{m-1} L_{m-1} ... G_0 L_0` applied to the initial data. -/
theorem fl_dividedDifferenceFiniteCoeffs_eq_GLProductAction_of_row_factors
    (fp : FPModel) (nodes f : ℕ → ℝ) (eta : ℕ → ℕ → ℝ) (n m : ℕ)
    (hrow : ∀ k, k < m → ∀ i : Fin (n + 1), k < i.val →
      fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
        eta k i.val *
          dividedDifferenceStep nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val) :
    ∀ i : Fin (n + 1),
      fl_dividedDifferenceFiniteCoeffs fp nodes f n m i =
        dividedDifferenceGLProductAction nodes eta n m
          (fun i : Fin (n + 1) => f i.val) i := by
  induction m with
  | zero =>
      intro i
      rfl
  | succ m ih =>
      intro i
      have hrowPrev :
          ∀ k, k < m → ∀ i : Fin (n + 1), k < i.val →
            fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
              eta k i.val *
                dividedDifferenceStep nodes
                  (dividedDifferenceFinToNat
                    (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
                  k i.val := by
        intro k hk
        exact hrow k (Nat.lt_trans hk (Nat.lt_succ_self m))
      have hprev :
          fl_dividedDifferenceFiniteCoeffs fp nodes f n m =
            dividedDifferenceGLProductAction nodes eta n m
              (fun i : Fin (n + 1) => f i.val) := by
        funext i
        exact ih hrowPrev i
      have hstep :
          fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i =
            dividedDifferenceGMatrixAction (eta m) n m
              (dividedDifferenceLMatrixAction nodes n m
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)) i := by
        have hrowStep :
            ∀ i : Fin (n + 1), m < i.val →
              fl_dividedDifferenceStep fp nodes
                  (dividedDifferenceFinToNat
                    (fl_dividedDifferenceFiniteCoeffs fp nodes f n m))
                  m i.val =
                eta m i.val *
                  dividedDifferenceStep nodes
                    (dividedDifferenceFinToNat
                      (fl_dividedDifferenceFiniteCoeffs fp nodes f n m))
                    m i.val := by
          intro i hi
          simpa [fl_dividedDifferenceFiniteCoeffs] using
            hrow m (Nat.lt_succ_self m) i hi
        simpa [fl_dividedDifferenceFiniteCoeffs] using
          (fl_dividedDifferenceStep_eq_GMatrixAction_of_row_factors
            fp nodes
            (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)
            (eta m) hrowStep i)
      calc
        fl_dividedDifferenceFiniteCoeffs fp nodes f n (m + 1) i =
            dividedDifferenceGMatrixAction (eta m) n m
              (dividedDifferenceLMatrixAction nodes n m
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n m)) i := hstep
        _ = dividedDifferenceGMatrixAction (eta m) n m
              (dividedDifferenceLMatrixAction nodes n m
                (dividedDifferenceGLProductAction nodes eta n m
                  (fun i : Fin (n + 1) => f i.val))) i := by
              rw [hprev]
        _ = dividedDifferenceGLProductAction nodes eta n (m + 1)
              (fun i : Fin (n + 1) => f i.val) i := rfl

/-- Gamma-three product representation for the rounded finite
divided-difference columns.  This is the finite product-form foundation for
Higham (5.10); turning it into the printed normwise/product perturbation bound
is a separate matrix-product estimate. -/
theorem fl_dividedDifferenceFiniteCoeffs_exists_GLProductAction_gamma3
    (fp : FPModel) (nodes f : ℕ → ℝ) {n : ℕ} (m : ℕ)
    (hden : ∀ k j, k < j → j < n + 1 →
      nodes j - nodes (j - k - 1) ≠ 0)
    (hdenHat : ∀ k j, k < j → j < n + 1 →
      fp.fl_sub (nodes j) (nodes (j - k - 1)) ≠ 0)
    (hγ : gammaValid fp 3) :
    ∃ eta : ℕ → ℕ → ℝ,
      (∀ k, k < m → ∀ i : Fin (n + 1), k < i.val →
        |eta k i.val - 1| ≤ gamma fp 3) ∧
      ∀ i : Fin (n + 1),
        fl_dividedDifferenceFiniteCoeffs fp nodes f n m i =
          dividedDifferenceGLProductAction nodes eta n m
            (fun i : Fin (n + 1) => f i.val) i := by
  classical
  let theta : ℕ → ℕ → ℝ := fun k j =>
    if hjk : k < j then
      if hjn : j < n + 1 then
        Classical.choose
          (fl_dividedDifferenceStep_entry_gamma3 fp nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
            hjk (hden k j hjk hjn) (hdenHat k j hjk hjn) hγ)
      else
        0
    else
      0
  let eta : ℕ → ℕ → ℝ := fun k j => 1 + theta k j
  refine ⟨eta, ?_, ?_⟩
  · intro k hk i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
        hi (hden k i.val hi i.isLt) (hdenHat k i.val hi i.isLt) hγ)
    have htheta :
        theta k i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
              hi (hden k i.val hi i.isLt)
              (hdenHat k i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have hetaDiff : eta k i.val - 1 = theta k i.val := by
      simp [eta]
    rw [hetaDiff, htheta]
    exact hspec.1
  · apply fl_dividedDifferenceFiniteCoeffs_eq_GLProductAction_of_row_factors
    intro k hk i hi
    have hspec := Classical.choose_spec
      (fl_dividedDifferenceStep_entry_gamma3 fp nodes
        (dividedDifferenceFinToNat
          (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
        hi (hden k i.val hi i.isLt) (hdenHat k i.val hi i.isLt) hγ)
    have htheta :
        theta k i.val =
          Classical.choose
            (fl_dividedDifferenceStep_entry_gamma3 fp nodes
              (dividedDifferenceFinToNat
                (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
              hi (hden k i.val hi i.isLt)
              (hdenHat k i.val hi i.isLt) hγ) := by
      have hile : i.val ≤ n := Nat.lt_succ_iff.mp i.isLt
      simp [theta, hi, hile]
    have heta :
        eta k i.val =
          1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat
                  (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
                hi (hden k i.val hi i.isLt)
                (hdenHat k i.val hi i.isLt) hγ) := by
      simp [eta, htheta]
    calc
      fl_dividedDifferenceFiniteCoeffs fp nodes f n (k + 1) i =
          fl_dividedDifferenceStep fp nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val := by
            rfl
      _ = dividedDifferenceStep nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val *
          (1 +
            Classical.choose
              (fl_dividedDifferenceStep_entry_gamma3 fp nodes
                (dividedDifferenceFinToNat
                  (fl_dividedDifferenceFiniteCoeffs fp nodes f n k))
                hi (hden k i.val hi i.isLt)
                (hdenHat k i.val hi i.isLt) hγ)) := hspec.2
      _ = eta k i.val *
          dividedDifferenceStep nodes
            (dividedDifferenceFinToNat
              (fl_dividedDifferenceFiniteCoeffs fp nodes f n k)) k i.val := by
            rw [heta]
            ring

end NumStability
