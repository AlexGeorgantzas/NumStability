import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
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
# Chapter14 Problem02 TriangularInversion Basic

Canonical destination for material split out of
`NumStability.Algorithms.Ch14Problem142` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

/-- Triangle inequality for the Chapter 13 rectangular max-entry norm. -/
theorem higham14_problem14_2_maxEntryNormRect_add_le {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (A B : Fin m → Fin n → ℝ) :
    maxEntryNormRect hm hn (A + B) ≤
      maxEntryNormRect hm hn A + maxEntryNormRect hm hn B := by
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  calc
    |(A + B) i j| ≤ |A i j| + |B i j| := abs_add_le _ _
    _ ≤ maxEntryNormRect hm hn A + maxEntryNormRect hm hn B :=
      add_le_add (entry_le_maxEntryNormRect hm hn A i j)
        (entry_le_maxEntryNormRect hm hn B i j)

/-- Negation preserves the Chapter 13 rectangular max-entry norm. -/
theorem higham14_problem14_2_maxEntryNormRect_neg {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (A : Fin m → Fin n → ℝ) :
    maxEntryNormRect hm hn (-A) = maxEntryNormRect hm hn A := by
  apply le_antisymm
  · apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    simpa using entry_le_maxEntryNormRect hm hn A i j
  · apply maxEntryNormRect_le_of_entry_abs_le
    intro i j
    have h := entry_le_maxEntryNormRect hm hn (-A) i j
    simpa using h

/-- The norm of `-A + B` is bounded by the sum of the two error norms. -/
theorem higham14_problem14_2_maxEntryNormRect_neg_add_le {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (A B : Fin m → Fin n → ℝ) :
    maxEntryNormRect hm hn (-A + B) ≤
      maxEntryNormRect hm hn A + maxEntryNormRect hm hn B := by
  calc
    maxEntryNormRect hm hn (-A + B)
        ≤ maxEntryNormRect hm hn (-A) + maxEntryNormRect hm hn B :=
      higham14_problem14_2_maxEntryNormRect_add_le hm hn (-A) B
    _ = maxEntryNormRect hm hn A + maxEntryNormRect hm hn B := by
      rw [higham14_problem14_2_maxEntryNormRect_neg]

/-- A lower two-by-two block matrix on `Fin (r + m)`. -/
def higham14_problem14_2_lowerBlock {r m : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin m → Fin r → ℝ)
    (A22 : Fin m → Fin m → ℝ) : Matrix (Fin (r + m)) (Fin (r + m)) ℝ :=
  fun i j =>
    Fin.addCases
      (fun a : Fin r =>
        Fin.addCases (fun b : Fin r => A11 a b) (fun _ : Fin m => 0) j)
      (fun c : Fin m =>
        Fin.addCases (fun b : Fin r => A21 c b) (fun d : Fin m => A22 c d) j)
      i

@[simp] theorem higham14_problem14_2_lowerBlock_bb {r m : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin m → Fin r → ℝ)
    (A22 : Fin m → Fin m → ℝ) (i j : Fin r) :
    higham14_problem14_2_lowerBlock A11 A21 A22
      (Fin.castAdd m i) (Fin.castAdd m j) = A11 i j := by
  simp [higham14_problem14_2_lowerBlock]

@[simp] theorem higham14_problem14_2_lowerBlock_bd {r m : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin m → Fin r → ℝ)
    (A22 : Fin m → Fin m → ℝ) (i : Fin r) (j : Fin m) :
    higham14_problem14_2_lowerBlock A11 A21 A22
      (Fin.castAdd m i) (Fin.natAdd r j) = 0 := by
  simp [higham14_problem14_2_lowerBlock]

@[simp] theorem higham14_problem14_2_lowerBlock_cb {r m : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin m → Fin r → ℝ)
    (A22 : Fin m → Fin m → ℝ) (i : Fin m) (j : Fin r) :
    higham14_problem14_2_lowerBlock A11 A21 A22
      (Fin.natAdd r i) (Fin.castAdd m j) = A21 i j := by
  simp [higham14_problem14_2_lowerBlock]

@[simp] theorem higham14_problem14_2_lowerBlock_cd {r m : ℕ}
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin m → Fin r → ℝ)
    (A22 : Fin m → Fin m → ℝ) (i j : Fin m) :
    higham14_problem14_2_lowerBlock A11 A21 A22
      (Fin.natAdd r i) (Fin.natAdd r j) = A22 i j := by
  simp [higham14_problem14_2_lowerBlock]

/-- Multiplication of compatible lower two-by-two block matrices. -/
theorem higham14_problem14_2_lowerBlock_mul {r m : ℕ}
    (A11 B11 : Matrix (Fin r) (Fin r) ℝ)
    (A21 B21 : Matrix (Fin m) (Fin r) ℝ)
    (A22 B22 : Matrix (Fin m) (Fin m) ℝ) :
    (higham14_problem14_2_lowerBlock A11 A21 A22 :
        Matrix (Fin (r + m)) (Fin (r + m)) ℝ) *
      higham14_problem14_2_lowerBlock B11 B21 B22 =
        higham14_problem14_2_lowerBlock
          (A11 * B11) (A21 * B11 + A22 * B21) (A22 * B22) := by
  ext i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp only [Matrix.mul_apply, higham14_problem14_2_lowerBlock_bb]
      rw [Fin.sum_univ_add]
      simp
    · intro d
      simp only [Matrix.mul_apply, higham14_problem14_2_lowerBlock_bd]
      rw [Fin.sum_univ_add]
      simp
  · intro c
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp only [Matrix.mul_apply, higham14_problem14_2_lowerBlock_cb]
      rw [Fin.sum_univ_add]
      simp [Matrix.mul_apply]
    · intro d
      simp only [Matrix.mul_apply, higham14_problem14_2_lowerBlock_cd]
      rw [Fin.sum_univ_add]
      simp

/-- Subtraction is componentwise through the lower-block constructor. -/
theorem higham14_problem14_2_lowerBlock_sub {r m : ℕ}
    (A11 B11 : Matrix (Fin r) (Fin r) ℝ)
    (A21 B21 : Matrix (Fin m) (Fin r) ℝ)
    (A22 B22 : Matrix (Fin m) (Fin m) ℝ) :
    higham14_problem14_2_lowerBlock A11 A21 A22 -
        higham14_problem14_2_lowerBlock B11 B21 B22 =
      higham14_problem14_2_lowerBlock
        (A11 - B11) (A21 - B21) (A22 - B22) := by
  ext i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    refine Fin.addCases ?_ ?_ j <;> intro d <;> simp
  · intro c
    refine Fin.addCases ?_ ?_ j <;> intro d <;> simp

/-- The full max-entry norm of a lower block matrix is controlled by the
    maximum of its three nonzero block norms. -/
theorem higham14_problem14_2_lowerBlock_maxEntryNorm_le {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m)
    (A11 : Fin r → Fin r → ℝ) (A21 : Fin m → Fin r → ℝ)
    (A22 : Fin m → Fin m → ℝ) :
    maxEntryNormRect (Nat.add_pos_left hr m) (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock A11 A21 A22) ≤
      max (maxEntryNormRect hr hr A11)
        (max (maxEntryNormRect hm hr A21) (maxEntryNormRect hm hm A22)) := by
  apply maxEntryNormRect_le_of_entry_abs_le
  intro i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simpa using le_trans (entry_le_maxEntryNormRect hr hr A11 a b)
        (le_max_left (maxEntryNormRect hr hr A11)
          (max (maxEntryNormRect hm hr A21) (maxEntryNormRect hm hm A22)))
    · intro d
      simp only [higham14_problem14_2_lowerBlock_bd, abs_zero]
      exact le_trans (maxEntryNormRect_nonneg hr hr A11) (le_max_left _ _)
  · intro c
    refine Fin.addCases ?_ ?_ j
    · intro b
      simpa using le_trans (entry_le_maxEntryNormRect hm hr A21 c b)
        (le_trans (le_max_left _ _) (le_max_right _ _))
    · intro d
      simpa using le_trans (entry_le_maxEntryNormRect hm hm A22 c d)
        (le_trans (le_max_right _ _) (le_max_right _ _))

/-- A recursion-ready first-order composer.  It combines proved leading-block,
    off-diagonal, and trailing-block residual estimates; it does not assume a
    whole-matrix residual estimate. -/
theorem higham14_problem14_2_lowerBlock_residual_firstOrder {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (u leading11 leading21 leading22 : ℝ)
    (R11 : Fin r → Fin r → ℝ) (R21 : Fin m → Fin r → ℝ)
    (R22 : Fin m → Fin m → ℝ)
    (h11 : FirstOrderLe u leading11 (maxEntryNormRect hr hr R11))
    (h21 : FirstOrderLe u leading21 (maxEntryNormRect hm hr R21))
    (h22 : FirstOrderLe u leading22 (maxEntryNormRect hm hm R22)) :
    FirstOrderLe u (max leading11 (max leading21 leading22))
      (maxEntryNormRect (Nat.add_pos_left hr m) (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock R11 R21 R22)) := by
  have hblocks : FirstOrderLe u (max leading11 (max leading21 leading22))
      (max (maxEntryNormRect hr hr R11)
        (max (maxEntryNormRect hm hr R21) (maxEntryNormRect hm hm R22))) :=
    FirstOrderLe.max h11 (FirstOrderLe.max h21 h22)
  exact hblocks.mono_value
    (higham14_problem14_2_lowerBlock_maxEntryNorm_le hr hm R11 R21 R22)

/-- Method 1B at one arbitrary block split, expressed only through the
    Chapter 13 assumptions (13.4) and (13.5).  It forms
    `That = fl(L₂₁ X₁₁)` and solves `L₂₂ X₂₁ = -That`. -/
structure Higham14Problem142Method1BStepSpec {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (u cMul cSolve : ℝ)
    (L21 : Matrix (Fin m) (Fin r) ℝ)
    (L22 : Matrix (Fin m) (Fin m) ℝ)
    (X11 : Matrix (Fin r) (Fin r) ℝ)
    (X21 That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ) : Prop where
  product : MatMulFirstOrderSpec u cMul
    (maxEntryNormRect hm hr L21) (maxEntryNormRect hr hr X11)
    (maxEntryNormRect hm hr DeltaMul)
    L21 X11 That DeltaMul
  solve : TriangularSolveFirstOrderSpec u cSolve
    (maxEntryNormRect hm hm L22) (maxEntryNormRect hm hr X21)
    (maxEntryNormRect hm hr DeltaSolve)
    L22 (-That) DeltaSolve X21

/-- The Method 1B off-diagonal residual equation is a consequence of the two
    operation equations, rather than an input assumption. -/
theorem Higham14Problem142Method1BStepSpec.offdiag_equation {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cMul cSolve : ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {L22 : Matrix (Fin m) (Fin m) ℝ}
    {X11 : Matrix (Fin r) (Fin r) ℝ}
    {X21 That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method1BStepSpec hr hm u cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) :
    L21 * X11 + L22 * X21 = -DeltaMul + DeltaSolve := by
  rw [h.solve.equation, h.product.equation]
  abel

/-- Problem 14.2, Method 1B off-diagonal conclusion: norms replace absolute
    values and the two Chapter 13 constants contribute additively, with the
    second-order remainder retained by `FirstOrderLe`. -/
theorem Higham14Problem142Method1BStepSpec.offdiag_firstOrder {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cMul cSolve : ℝ}
    {L21 : Matrix (Fin m) (Fin r) ℝ}
    {L22 : Matrix (Fin m) (Fin m) ℝ}
    {X11 : Matrix (Fin r) (Fin r) ℝ}
    {X21 That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method1BStepSpec hr hm u cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) :
    FirstOrderLe u
      (cMul * u * maxEntryNormRect hm hr L21 * maxEntryNormRect hr hr X11 +
        cSolve * u * maxEntryNormRect hm hm L22 * maxEntryNormRect hm hr X21)
      (maxEntryNormRect hm hr (L21 * X11 + L22 * X21)) := by
  apply FirstOrderLe.add h.product.norm_bound h.solve.norm_bound
  rw [h.offdiag_equation]
  exact higham14_problem14_2_maxEntryNormRect_neg_add_le hm hr DeltaMul DeltaSolve

/-- Method 2C at one arbitrary block split under (13.4) and the right-solve
    orientation of (13.5). -/
structure Higham14Problem142Method2CStepSpec {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (u cMul cSolve : ℝ)
    (L11 : Matrix (Fin r) (Fin r) ℝ)
    (L21 : Matrix (Fin m) (Fin r) ℝ)
    (X21 : Matrix (Fin m) (Fin r) ℝ)
    (X22 : Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ) : Prop where
  product : MatMulFirstOrderSpec u cMul
    (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
    (maxEntryNormRect hm hr DeltaMul)
    X22 L21 That DeltaMul
  solve : RightTriangularSolveFirstOrderSpec u cSolve
    (maxEntryNormRect hr hr L11) (maxEntryNormRect hm hr X21)
    (maxEntryNormRect hm hr DeltaSolve)
    L11 (-That) DeltaSolve X21

/-- The Method 2C off-diagonal left residual follows from the arbitrary
    product and right-triangular-solve equations. -/
theorem Higham14Problem142Method2CStepSpec.offdiag_equation {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cMul cSolve : ℝ}
    {L11 : Matrix (Fin r) (Fin r) ℝ}
    {L21 X21 : Matrix (Fin m) (Fin r) ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2CStepSpec hr hm u cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) :
    X21 * L11 + X22 * L21 = -DeltaMul + DeltaSolve := by
  rw [h.solve.equation, h.product.equation]
  abel

/-- Problem 14.2, Method 2C off-diagonal normwise conclusion with an explicit
    first-order matrix-product term, triangular-solve term, and `O(u²)`
    remainder. -/
theorem Higham14Problem142Method2CStepSpec.offdiag_firstOrder {r m : ℕ}
    {hr : 0 < r} {hm : 0 < m} {u cMul cSolve : ℝ}
    {L11 : Matrix (Fin r) (Fin r) ℝ}
    {L21 X21 : Matrix (Fin m) (Fin r) ℝ}
    {X22 : Matrix (Fin m) (Fin m) ℝ}
    {That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ}
    (h : Higham14Problem142Method2CStepSpec hr hm u cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) :
    FirstOrderLe u
      (cMul * u * maxEntryNormRect hm hm X22 * maxEntryNormRect hm hr L21 +
        cSolve * u * maxEntryNormRect hr hr L11 * maxEntryNormRect hm hr X21)
      (maxEntryNormRect hm hr (X21 * L11 + X22 * L21)) := by
  apply FirstOrderLe.add h.product.norm_bound h.solve.norm_bound
  rw [h.offdiag_equation]
  exact higham14_problem14_2_maxEntryNormRect_neg_add_le hm hr DeltaMul DeltaSolve

/-- An operation-level derivation for Method 1B on an arbitrary finite binary
    block partition.  Leaves are identity triangular solves governed by
    (13.5); every internal node is a Method 1B product/solve step governed by
    (13.4)/(13.5).  Consequently no residual estimate occurs as a constructor
    hypothesis. -/
inductive Higham14Problem142Method1BDerivation (u : ℝ) :
    {n : ℕ} → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ → ℝ → Prop where
  | leaf {n : ℕ} (hn : 0 < n) (cSolve : ℝ)
      (L X Delta : Matrix (Fin n) (Fin n) ℝ)
      (solve : TriangularSolveFirstOrderSpec u cSolve
        (maxEntryNormRect hn hn L) (maxEntryNormRect hn hn X)
        (maxEntryNormRect hn hn Delta)
        L (1 : Matrix (Fin n) (Fin n) ℝ) Delta X) :
      Higham14Problem142Method1BDerivation u L X
        (cSolve * u * maxEntryNormRect hn hn L * maxEntryNormRect hn hn X)
  | split {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
      (cMul cSolve leading11 leading22 : ℝ)
      (L11 X11 : Matrix (Fin r) (Fin r) ℝ)
      (L21 X21 : Matrix (Fin m) (Fin r) ℝ)
      (L22 X22 : Matrix (Fin m) (Fin m) ℝ)
      (That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ)
      (head : Higham14Problem142Method1BDerivation u L11 X11 leading11)
      (tail : Higham14Problem142Method1BDerivation u L22 X22 leading22)
      (step : Higham14Problem142Method1BStepSpec hr hm u cMul cSolve
        L21 L22 X11 X21 That DeltaMul DeltaSolve) :
      Higham14Problem142Method1BDerivation u
        (higham14_problem14_2_lowerBlock L11 L21 L22)
        (higham14_problem14_2_lowerBlock X11 X21 X22)
        (max leading11
          (max
            (cMul * u * maxEntryNormRect hm hr L21 * maxEntryNormRect hr hr X11 +
              cSolve * u * maxEntryNormRect hm hm L22 * maxEntryNormRect hm hr X21)
            leading22))

/-- The corresponding operation-level derivation for Method 2C.  Leaves use
    right triangular identity solves and internal nodes use arbitrary (13.4)
    products followed by arbitrary right-oriented (13.5) solves. -/
inductive Higham14Problem142Method2CDerivation (u : ℝ) :
    {n : ℕ} → Matrix (Fin n) (Fin n) ℝ →
      Matrix (Fin n) (Fin n) ℝ → ℝ → Prop where
  | leaf {n : ℕ} (hn : 0 < n) (cSolve : ℝ)
      (L X Delta : Matrix (Fin n) (Fin n) ℝ)
      (solve : RightTriangularSolveFirstOrderSpec u cSolve
        (maxEntryNormRect hn hn L) (maxEntryNormRect hn hn X)
        (maxEntryNormRect hn hn Delta)
        L (1 : Matrix (Fin n) (Fin n) ℝ) Delta X) :
      Higham14Problem142Method2CDerivation u L X
        (cSolve * u * maxEntryNormRect hn hn L * maxEntryNormRect hn hn X)
  | split {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
      (cMul cSolve leading11 leading22 : ℝ)
      (L11 X11 : Matrix (Fin r) (Fin r) ℝ)
      (L21 X21 : Matrix (Fin m) (Fin r) ℝ)
      (L22 X22 : Matrix (Fin m) (Fin m) ℝ)
      (That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ)
      (head : Higham14Problem142Method2CDerivation u L11 X11 leading11)
      (tail : Higham14Problem142Method2CDerivation u L22 X22 leading22)
      (step : Higham14Problem142Method2CStepSpec hr hm u cMul cSolve
        L11 L21 X21 X22 That DeltaMul DeltaSolve) :
      Higham14Problem142Method2CDerivation u
        (higham14_problem14_2_lowerBlock L11 L21 L22)
        (higham14_problem14_2_lowerBlock X11 X21 X22)
        (max leading11
          (max
            (cMul * u * maxEntryNormRect hm hm X22 * maxEntryNormRect hm hr L21 +
              cSolve * u * maxEntryNormRect hr hr L11 * maxEntryNormRect hm hr X21)
            leading22))

end Ch14Ext
end NumStability
