import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

-- Analysis/CramersRule.lean
--
-- Exact 2-by-2 Cramer's-rule algebra for Higham Chapter 1, Section 1.10.1.










namespace NumStability

/-!
# Cramer's Rule, 2 by 2

Higham Chapter 1, Section 1.10.1 contrasts GEPP with Cramer's rule.  This
file records the exact real-arithmetic 2-by-2 Cramer formula.  The floating-
point residual and forward-stability comparisons from the text and Problem 1.9
remain separate obligations.
-/

/-- Determinant of a `2 × 2` scalar matrix
`[[a11, a12], [a21, a22]]`. -/
noncomputable def det2x2 (a11 a12 a21 a22 : ℝ) : ℝ :=
  a11 * a22 - a21 * a12

/-- Sum of magnitudes of the two products in a `2 × 2` determinant.
This is the natural local error scale for a rounded computation of
`a11*a22 - a21*a12`. -/
noncomputable def det2x2AbsTerms (a11 a12 a21 a22 : ℝ) : ℝ :=
  |a11 * a22| + |a21 * a12|

/-- Floating-point evaluation of a `2 × 2` determinant by two rounded
multiplications followed by one rounded subtraction. -/
noncomputable def flDet2x2 (fp : FPModel) (a11 a12 a21 a22 : ℝ) : ℝ :=
  fp.fl_sub (fp.fl_mul a11 a22) (fp.fl_mul a21 a12)

/-- First Cramer component for a `2 × 2` system. -/
noncomputable def cramer2x2X1
    (a11 a12 a21 a22 b1 b2 : ℝ) : ℝ :=
  det2x2 b1 a12 b2 a22 / det2x2 a11 a12 a21 a22

/-- Second Cramer component for a `2 × 2` system. -/
noncomputable def cramer2x2X2
    (a11 a12 a21 a22 b1 b2 : ℝ) : ℝ :=
  det2x2 a11 b1 a21 b2 / det2x2 a11 a12 a21 a22

/-- The first equation is satisfied by the exact 2-by-2 Cramer formula. -/
theorem cramer2x2_first_eq
    (a11 a12 a21 a22 b1 b2 : ℝ)
    (hdet : det2x2 a11 a12 a21 a22 ≠ 0) :
    a11 * cramer2x2X1 a11 a12 a21 a22 b1 b2 +
      a12 * cramer2x2X2 a11 a12 a21 a22 b1 b2 = b1 := by
  have hden : a11 * a22 - a12 * a21 ≠ 0 := by
    intro h
    apply hdet
    rw [← h]
    unfold det2x2
    ring
  unfold cramer2x2X1 cramer2x2X2 det2x2
  field_simp [hden]
  ring

/-- The second equation is satisfied by the exact 2-by-2 Cramer formula. -/
theorem cramer2x2_second_eq
    (a11 a12 a21 a22 b1 b2 : ℝ)
    (hdet : det2x2 a11 a12 a21 a22 ≠ 0) :
    a21 * cramer2x2X1 a11 a12 a21 a22 b1 b2 +
      a22 * cramer2x2X2 a11 a12 a21 a22 b1 b2 = b2 := by
  have hden : -(a21 * a12) + a22 * a11 ≠ 0 := by
    intro h
    apply hdet
    rw [← h]
    unfold det2x2
    ring
  unfold cramer2x2X1 cramer2x2X2 det2x2
  rw [show a11 * a22 - a21 * a12 = -(a21 * a12) + a22 * a11 by ring]
  field_simp [hden]
  ring

/-- Determinant of a finite `2 × 2` matrix. -/
noncomputable def det2x2Matrix (A : Fin 2 → Fin 2 → ℝ) : ℝ :=
  det2x2 (A 0 0) (A 0 1) (A 1 0) (A 1 1)

/-- Replace one column of a finite `2 × 2` matrix by the right-hand side. -/
noncomputable def replaceCol2x2
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) (col : Fin 2) :
    Fin 2 → Fin 2 → ℝ :=
  fun i j => if j = col then b i else A i j

/-- Cramer's-rule solution vector for a finite `2 × 2` system. -/
noncomputable def cramer2x2Solution
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => det2x2Matrix (replaceCol2x2 A b i) / det2x2Matrix A

/-- Numerator determinant for the `i`th component of the finite `2 × 2`
Cramer solution. -/
noncomputable def cramer2x2Numerator
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  det2x2Matrix (replaceCol2x2 A b i)

/-- Product-magnitude scale for a rounded computation of the `i`th Cramer
numerator determinant. -/
noncomputable def cramer2x2NumeratorAbsTerms
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  det2x2AbsTerms
    (replaceCol2x2 A b i 0 0) (replaceCol2x2 A b i 0 1)
    (replaceCol2x2 A b i 1 0) (replaceCol2x2 A b i 1 1)

/-- Cramer's rule when the denominator determinant is exact but the two
numerator determinants are supplied as computed values.  This is the
intermediate surface used in Higham Problem 1.9. -/
noncomputable def cramer2x2ComputedFromNumerators
    (A : Fin 2 → Fin 2 → ℝ) (numHat : Fin 2 → ℝ) : Fin 2 → ℝ :=
  fun i => numHat i / det2x2Matrix A

/-- Floating-point Cramer numerator determinant for component `i`, evaluated
by two rounded multiplications followed by one rounded subtraction. -/
noncomputable def flCramer2x2Numerator
    (fp : FPModel) (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) (i : Fin 2) : ℝ :=
  flDet2x2 fp
    (replaceCol2x2 A b i 0 0) (replaceCol2x2 A b i 0 1)
    (replaceCol2x2 A b i 1 0) (replaceCol2x2 A b i 1 1)

/-! ## Displayed MATLAB data in §1.10.1 -/



































































































































































































































































/-- The finite-vector Cramer solution specializes to the displayed scalar
formula for the first component. -/
theorem cramer2x2Solution_zero
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    cramer2x2Solution A b 0 =
      cramer2x2X1 (A 0 0) (A 0 1) (A 1 0) (A 1 1) (b 0) (b 1) := by
  unfold cramer2x2Solution cramer2x2X1 det2x2Matrix replaceCol2x2
  simp [det2x2]

/-- The finite-vector Cramer solution specializes to the displayed scalar
formula for the second component. -/
theorem cramer2x2Solution_one
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    cramer2x2Solution A b 1 =
      cramer2x2X2 (A 0 0) (A 0 1) (A 1 0) (A 1 1) (b 0) (b 1) := by
  unfold cramer2x2Solution cramer2x2X2 det2x2Matrix replaceCol2x2
  simp [det2x2]

/-- The exact finite-vector 2-by-2 Cramer solution solves `A*x=b` whenever
`det(A) ≠ 0`. -/
theorem cramer2x2Solution_solves
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    ∀ i : Fin 2, ∑ j : Fin 2, A i j * cramer2x2Solution A b j = b i := by
  intro i
  fin_cases i
  · rw [Fin.sum_univ_two, cramer2x2Solution_zero, cramer2x2Solution_one]
    exact cramer2x2_first_eq (A 0 0) (A 0 1) (A 1 0) (A 1 1) (b 0) (b 1) hdet
  · rw [Fin.sum_univ_two, cramer2x2Solution_zero, cramer2x2Solution_one]
    exact cramer2x2_second_eq (A 0 0) (A 0 1) (A 1 0) (A 1 1) (b 0) (b 1) hdet



























































































































































































































































































-- ============================================================
-- Problem 1.9 forward-error bridge
-- ============================================================



















































































































































































































































































































































end NumStability
