import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Basis.Flag
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Cauchy.Basic

/-!
# NumStability Analysis TestMatrices Cauchy Contracts

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Contracts` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

/-- Strict total positivity, stated on every square submatrix selected by
strictly increasing row and column embeddings. -/
def IsStrictlyTotallyPositive {m n : ℕ} (A : RMat m n) : Prop :=
  ∀ (k : ℕ) (_hk : 0 < k) (r : Fin k → Fin m) (c : Fin k → Fin n),
    StrictMono r → StrictMono c →
      0 < Matrix.det (fun i j => A (r i) (c j))

/-- Numerator of the square Cauchy determinant product. -/
noncomputable def cauchyDetNumerator (n : ℕ) (x y : RVec n) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) * (y j - y i)

/-- Denominator of the square Cauchy determinant product. -/
noncomputable def cauchyDetDenominator (n : ℕ) (x y : RVec n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, (x i + y j)

theorem cauchyDetFormula_eq_num_div_den (n : ℕ) (x y : RVec n) :
    cauchyDetFormula n x y =
      cauchyDetNumerator n x y / cauchyDetDenominator n x y := rfl

/-- Source-only regularity assumptions for the printed square Cauchy
formulas.  These hypotheses say that the two node families have no repeats
and that every matrix denominator is nonzero; they contain none of the
determinant, inverse, LU, or total-positivity conclusions. -/
structure CauchyAdmissible {n : ℕ} (x y : RVec n) : Prop where
  x_injective : Function.Injective x
  y_injective : Function.Injective y
  sum_ne_zero : ∀ i j, x i + y j ≠ 0

theorem cauchyAdmissible_of_strictMono_of_pos
    {n : ℕ} (x y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j) :
    CauchyAdmissible x y where
  x_injective := hx.injective
  y_injective := hy.injective
  sum_ne_zero := fun i j ↦ ne_of_gt (hsum i j)

/-- Under the actual source regularity assumptions, the denominator in the
printed Cauchy determinant product is nonzero. -/
theorem cauchyDetDenominator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyDetDenominator n x y ≠ 0 := by
  unfold cauchyDetDenominator
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j _
  exact h.sum_ne_zero i j

/-- Distinct source nodes also make every Vandermonde factor in the numerator
nonzero. -/
theorem cauchyDetNumerator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyDetNumerator n x y ≠ 0 := by
  unfold cauchyDetNumerator
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  apply mul_ne_zero
  · exact sub_ne_zero.mpr fun heq ↦
      (ne_of_gt hij) (h.x_injective heq)
  · exact sub_ne_zero.mpr fun heq ↦
      (ne_of_gt hij) (h.y_injective heq)

/-- Consequently the right-hand side of Cauchy's printed determinant formula
is itself nonzero.  The remaining open step is proving that it equals the
matrix determinant. -/
theorem cauchyDetFormula_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyDetFormula n x y ≠ 0 := by
  rw [cauchyDetFormula_eq_num_div_den]
  exact div_ne_zero (cauchyDetNumerator_ne_zero h)
    (cauchyDetDenominator_ne_zero h)

/-- The paired numerator exactly as printed in the inverse-entry formula. -/
noncomputable def cauchyInverseNumerator
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  ∏ k : Fin n, (x j + y k) * (x k + y i)

/-- The three denominator factors exactly as printed in the inverse-entry
formula. -/
noncomputable def cauchyInverseDenominator
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  (x j + y i) *
    (∏ k ∈ Finset.univ.erase j, (x j - x k)) *
    (∏ k ∈ Finset.univ.erase i, (y i - y k))

theorem cauchyInverseEntry_eq_num_div_den
    (n : ℕ) (x y : RVec n) (i j : Fin n) :
    cauchyInverseEntry n x y i j =
      cauchyInverseNumerator n x y i j /
        cauchyInverseDenominator n x y i j := rfl

theorem cauchyInverseNumerator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseNumerator n x y i j ≠ 0 := by
  unfold cauchyInverseNumerator
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro k _
  exact mul_ne_zero (h.sum_ne_zero j k) (h.sum_ne_zero k i)

theorem cauchyInverseDenominator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseDenominator n x y i j ≠ 0 := by
  unfold cauchyInverseDenominator
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact h.sum_ne_zero j i
    · refine Finset.prod_ne_zero_iff.mpr ?_
      intro k hk
      rcases Finset.mem_erase.mp hk with ⟨hkj, _⟩
      exact sub_ne_zero.mpr fun heq ↦
        hkj (h.x_injective heq).symm
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro k hk
    rcases Finset.mem_erase.mp hk with ⟨hki, _⟩
    exact sub_ne_zero.mpr fun heq ↦
      hki (h.y_injective heq).symm

/-- Every displayed candidate inverse entry is well-defined and nonzero on
the genuine source domain.  This is a precursor, not the missing matrix
inverse theorem. -/
theorem cauchyInverseEntry_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseEntry n x y i j ≠ 0 := by
  rw [cauchyInverseEntry_eq_num_div_den]
  exact div_ne_zero (cauchyInverseNumerator_ne_zero h i j)
    (cauchyInverseDenominator_ne_zero h i j)

/-- Higham's unit-lower Cauchy `L` formula, translated from
`1 ≤ j < i ≤ n` to zero-based `Fin n` indices. -/
noncomputable def cauchyLowerEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  if j < i then
    ((x j + y j) / (x i + y j)) *
      (∏ k ∈ Finset.Iio j,
        ((x j + y k) * (x i - x k)) /
          ((x i + y k) * (x j - x k)))
  else if i = j then 1 else 0

/-- Higham's upper Cauchy `U` formula on the source range
`1 ≤ i ≤ j ≤ n`. -/
noncomputable def cauchyUpperEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  if i ≤ j then
    ((∏ k ∈ Finset.Iio i, (x i - x k) * (y j - y k)) /
      ((x i + y j) *
        (∏ k ∈ Finset.Iio i, (x i + y k) * (x k + y j))))
  else 0

noncomputable def cauchyLower
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j ↦ cauchyLowerEntry n x y i j

noncomputable def cauchyUpper
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j ↦ cauchyUpperEntry n x y i j

@[simp]
theorem cauchyLower_diagonal
    {n : ℕ} (x y : RVec n) (i : Fin n) :
    cauchyLower n x y i i = 1 := by
  simp [cauchyLower, cauchyLowerEntry]

theorem cauchyLower_entry_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hji : j < i) :
    cauchyLower n x y i j =
      ((x j + y j) / (x i + y j)) *
        (∏ k ∈ Finset.Iio j,
          ((x j + y k) * (x i - x k)) /
            ((x i + y k) * (x j - x k))) := by
  simp [cauchyLower, cauchyLowerEntry, hji]

theorem cauchyUpper_entry_of_le
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hij : i ≤ j) :
    cauchyUpper n x y i j =
      (∏ k ∈ Finset.Iio i, (x i - x k) * (y j - y k)) /
        ((x i + y j) *
          (∏ k ∈ Finset.Iio i, (x i + y k) * (x k + y j))) := by
  simp [cauchyUpper, cauchyUpperEntry, hij]

theorem cauchyLower_zero_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hij : i < j) :
    cauchyLower n x y i j = 0 := by
  simp [cauchyLower, cauchyLowerEntry, hij.asymm, hij.ne]

theorem cauchyUpper_zero_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hji : j < i) :
    cauchyUpper n x y i j = 0 := by
  simp [cauchyUpper, cauchyUpperEntry, show ¬i ≤ j by omega]

/-- The exact scalar Schur-complement identity for the first Cauchy pivot.
It is the local algebra needed by a genuine induction for the determinant and
Cho LU formulas. -/
theorem cauchy_firstPivot_schur_entry
    (xi x0 yj y0 : ℝ)
    (hij : xi + yj ≠ 0) (hi0 : xi + y0 ≠ 0)
    (h0j : x0 + yj ≠ 0) :
    1 / (xi + yj) -
        ((x0 + y0) / (xi + y0)) * (1 / (x0 + yj)) =
      ((xi - x0) * (yj - y0)) /
        ((xi + yj) * (xi + y0) * (x0 + yj)) := by
  field_simp
  ring

/-- Ordered positive Cauchy nodes make the printed determinant product
strictly positive. -/
theorem cauchyDetFormula_pos_of_strictMono_of_pos
    {n : ℕ} (x y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j) :
    0 < cauchyDetFormula n x y := by
  rw [cauchyDetFormula_eq_num_div_den]
  apply div_pos
  · unfold cauchyDetNumerator
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact mul_pos (sub_pos.mpr (hx hij)) (sub_pos.mpr (hy hij))
  · unfold cauchyDetDenominator
    exact Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ hsum i j

/-- The determinant-product side of every ordered Cauchy minor is positive.
The still-open foundation is the equality between this product and the
minor's matrix determinant. -/
theorem cauchyMinorDetFormula_pos
    {m n k : ℕ} (x : RVec m) (y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j)
    (r : Fin k → Fin m) (c : Fin k → Fin n)
    (hr : StrictMono r) (hc : StrictMono c) :
    0 < cauchyDetFormula k (fun i ↦ x (r i)) (fun j ↦ y (c j)) := by
  apply cauchyDetFormula_pos_of_strictMono_of_pos
  · exact hx.comp hr
  · exact hy.comp hc
  · exact fun i j ↦ hsum (r i) (c j)

/-- A concrete coordinate certificate for a singular rank-one perturbation.
The cancellation premise is the upstream entrywise arithmetic calculation,
not a matrix-singularity assumption. -/
theorem singular_rankOne_perturbation_of_coordinate_cancellation
    {n : ℕ} (A : RSqMat n) (u v z : RVec n)
    (hz : z ≠ 0)
    (hcancel : ∀ i : Fin n,
      (∑ j : Fin n, (A i j + u i * v j) * z j) = 0) :
    ∃ E : RSqMat n, (∀ i j, E i j = u i * v j) ∧
      ∃ z ≠ 0, Matrix.mulVec (A + E) z = 0 := by
  refine ⟨fun i j => u i * v j, fun _ _ => rfl, z, hz, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hcancel i

/-- Left cyclicity: the transpose Krylov family generated by `v` is a basis.
This is the algebraic precursor used in the standard proof that a companion
matrix is nonderogatory. -/
def IsLeftCyclicFor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : Prop :=
  LinearIndependent ℂ
    (fun k : Fin n => Matrix.mulVec (A.transpose ^ k.val) v)

def HasLeftCyclicVector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ v, IsLeftCyclicFor A v

end NumStability
