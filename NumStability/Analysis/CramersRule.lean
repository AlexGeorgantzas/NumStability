-- Analysis/CramersRule.lean
--
-- Exact 2-by-2 Cramer's-rule algebra for Higham Chapter 1, Section 1.10.1.

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding

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

/-- The printed Cramer's-rule solution vector in Higham §1.10.1's MATLAB
comparison, encoded as exact rationals.  This records the displayed decimal
rows; it is not a reconstruction of the hidden MATLAB system. -/
noncomputable def cramerGeppExampleCramerSolution (i : Fin 2) : ℝ :=
  if i = 0 then 10000 / (10 : ℝ)^4 else 20001 / (10 : ℝ)^4

/-- Legacy name for the printed Cramer's-rule scaled-residual vector in Higham
§1.10.1's MATLAB comparison, encoded as exact rationals.  The source table
header is `r/(||A||_2 ||xhat||_2)`, so these entries are not raw residuals. -/
noncomputable def cramerGeppExampleCramerResidual (i : Fin 2) : ℝ :=
  if i = 0 then 15075 / (10 : ℝ)^11 else 19285 / (10 : ℝ)^11

/-- The printed GEPP solution vector in Higham §1.10.1's MATLAB comparison,
encoded as exact rationals. -/
noncomputable def cramerGeppExampleGeppSolution (i : Fin 2) : ℝ :=
  if i = 0 then 10002 / (10 : ℝ)^4 else 20004 / (10 : ℝ)^4

/-- Legacy name for the printed GEPP scaled-residual vector in Higham
§1.10.1's MATLAB comparison, encoded as exact rationals.  The source table
header is `r/(||A||_2 ||xhat||_2)`, so these entries are not raw residuals. -/
noncomputable def cramerGeppExampleGeppResidual (i : Fin 2) : ℝ :=
  if i = 0 then -(45689 / (10 : ℝ)^21) else -(21931 / (10 : ℝ)^21)

/-- Source-facing alias for the printed Cramer's-rule scaled-residual vector. -/
noncomputable abbrev cramerGeppExampleCramerScaledResidual (i : Fin 2) : ℝ :=
  cramerGeppExampleCramerResidual i

/-- Source-facing alias for the printed GEPP scaled-residual vector. -/
noncomputable abbrev cramerGeppExampleGeppScaledResidual (i : Fin 2) : ℝ :=
  cramerGeppExampleGeppResidual i

/-- The comparison vector `[1.0006, 2.0012]` from Higham §1.10.1, encoded as
exact rationals. -/
noncomputable def cramerGeppExampleAccurateVector (i : Fin 2) : ℝ :=
  if i = 0 then 10006 / (10 : ℝ)^4 else 20012 / (10 : ℝ)^4

/-- The two displayed Cramer's-rule solution rows. -/
theorem cramerGeppExample_cramerSolution_rows :
    cramerGeppExampleCramerSolution 0 = 10000 / (10 : ℝ)^4 ∧
    cramerGeppExampleCramerSolution 1 = 20001 / (10 : ℝ)^4 := by
  norm_num [cramerGeppExampleCramerSolution]

/-- The two displayed Cramer's-rule scaled-residual rows, under their legacy
residual-vector name. -/
theorem cramerGeppExample_cramerResidual_rows :
    cramerGeppExampleCramerResidual 0 = 15075 / (10 : ℝ)^11 ∧
    cramerGeppExampleCramerResidual 1 = 19285 / (10 : ℝ)^11 := by
  norm_num [cramerGeppExampleCramerResidual]

/-- The two displayed Cramer's-rule scaled-residual rows. -/
theorem cramerGeppExample_cramerScaledResidual_rows :
    cramerGeppExampleCramerScaledResidual 0 = 15075 / (10 : ℝ)^11 ∧
    cramerGeppExampleCramerScaledResidual 1 = 19285 / (10 : ℝ)^11 := by
  simpa [cramerGeppExampleCramerScaledResidual] using
    cramerGeppExample_cramerResidual_rows

/-- The two displayed GEPP solution rows. -/
theorem cramerGeppExample_geppSolution_rows :
    cramerGeppExampleGeppSolution 0 = 10002 / (10 : ℝ)^4 ∧
    cramerGeppExampleGeppSolution 1 = 20004 / (10 : ℝ)^4 := by
  norm_num [cramerGeppExampleGeppSolution]

/-- The two displayed GEPP scaled-residual rows, under their legacy
residual-vector name. -/
theorem cramerGeppExample_geppResidual_rows :
    cramerGeppExampleGeppResidual 0 = -(45689 / (10 : ℝ)^21) ∧
    cramerGeppExampleGeppResidual 1 = -(21931 / (10 : ℝ)^21) := by
  norm_num [cramerGeppExampleGeppResidual]

/-- The two displayed GEPP scaled-residual rows. -/
theorem cramerGeppExample_geppScaledResidual_rows :
    cramerGeppExampleGeppScaledResidual 0 = -(45689 / (10 : ℝ)^21) ∧
    cramerGeppExampleGeppScaledResidual 1 = -(21931 / (10 : ℝ)^21) := by
  simpa [cramerGeppExampleGeppScaledResidual] using
    cramerGeppExample_geppResidual_rows

/-- The two displayed comparison-vector rows. -/
theorem cramerGeppExample_accurateVector_rows :
    cramerGeppExampleAccurateVector 0 = 10006 / (10 : ℝ)^4 ∧
    cramerGeppExampleAccurateVector 1 = 20012 / (10 : ℝ)^4 := by
  norm_num [cramerGeppExampleAccurateVector]

/-- The signs of the printed scaled-residual components under their legacy
residual-vector names: the displayed Cramer entries are positive, while the
displayed GEPP entries are negative. -/
theorem cramerGeppExample_residual_signs :
    (∀ i : Fin 2, 0 < cramerGeppExampleCramerResidual i) ∧
    (∀ i : Fin 2, cramerGeppExampleGeppResidual i < 0) := by
  constructor <;> intro i <;> fin_cases i <;>
    norm_num [cramerGeppExampleCramerResidual, cramerGeppExampleGeppResidual]

/-- The signs of the printed scaled-residual components. -/
theorem cramerGeppExample_scaledResidual_signs :
    (∀ i : Fin 2, 0 < cramerGeppExampleCramerScaledResidual i) ∧
    (∀ i : Fin 2, cramerGeppExampleGeppScaledResidual i < 0) := by
  simpa [cramerGeppExampleCramerScaledResidual,
    cramerGeppExampleGeppScaledResidual] using cramerGeppExample_residual_signs

/-- Componentwise magnitude gap visible directly in the printed scaled-residual
rows, under their legacy residual-vector names: each Cramer's-rule entry is
more than `10^9` times the corresponding GEPP entry in absolute value. -/
theorem cramerGeppExample_residual_component_gap :
    ∀ i : Fin 2,
      (10 : ℝ)^9 * |cramerGeppExampleGeppResidual i| <
        |cramerGeppExampleCramerResidual i| := by
  intro i
  fin_cases i <;>
    norm_num [cramerGeppExampleCramerResidual, cramerGeppExampleGeppResidual]

/-- Componentwise magnitude gap visible directly in the printed scaled-residual
rows. -/
theorem cramerGeppExample_scaledResidual_component_gap :
    ∀ i : Fin 2,
      (10 : ℝ)^9 * |cramerGeppExampleGeppScaledResidual i| <
        |cramerGeppExampleCramerScaledResidual i| := by
  simpa [cramerGeppExampleCramerScaledResidual,
    cramerGeppExampleGeppScaledResidual] using
    cramerGeppExample_residual_component_gap

/-- The infinity norm of the printed Cramer's-rule scaled-residual vector,
under its legacy residual-vector name. -/
theorem cramerGeppExample_cramerResidual_infNorm_eq :
    infNormVec cramerGeppExampleCramerResidual =
      19285 / (10 : ℝ)^11 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        norm_num [cramerGeppExampleCramerResidual]
    · norm_num
  · have hcomp :=
      abs_le_infNormVec cramerGeppExampleCramerResidual (1 : Fin 2)
    norm_num [cramerGeppExampleCramerResidual] at hcomp
    norm_num
    exact hcomp

/-- The infinity norm of the printed Cramer's-rule scaled-residual vector. -/
theorem cramerGeppExample_cramerScaledResidual_infNorm_eq :
    infNormVec cramerGeppExampleCramerScaledResidual =
      19285 / (10 : ℝ)^11 := by
  simpa [cramerGeppExampleCramerScaledResidual] using
    cramerGeppExample_cramerResidual_infNorm_eq

/-- The infinity norm of the printed GEPP scaled-residual vector, under its
legacy residual-vector name. -/
theorem cramerGeppExample_geppResidual_infNorm_eq :
    infNormVec cramerGeppExampleGeppResidual =
      45689 / (10 : ℝ)^21 := by
  apply le_antisymm
  · apply infNormVec_le_of_abs_le
    · intro i
      fin_cases i <;>
        norm_num [cramerGeppExampleGeppResidual]
    · norm_num
  · have hcomp :=
      abs_le_infNormVec cramerGeppExampleGeppResidual (0 : Fin 2)
    norm_num [cramerGeppExampleGeppResidual] at hcomp
    norm_num
    exact hcomp

/-- The infinity norm of the printed GEPP scaled-residual vector. -/
theorem cramerGeppExample_geppScaledResidual_infNorm_eq :
    infNormVec cramerGeppExampleGeppScaledResidual =
      45689 / (10 : ℝ)^21 := by
  simpa [cramerGeppExampleGeppScaledResidual] using
    cramerGeppExample_geppResidual_infNorm_eq

/-- Norm-level magnitude gap visible directly in the printed scaled-residual
rows, under their legacy residual-vector names: the Cramer's-rule scaled
residual infinity norm is more than `10^9` times the GEPP one. -/
theorem cramerGeppExample_residual_infNorm_gap :
    (10 : ℝ)^9 * infNormVec cramerGeppExampleGeppResidual <
      infNormVec cramerGeppExampleCramerResidual := by
  rw [cramerGeppExample_cramerResidual_infNorm_eq,
    cramerGeppExample_geppResidual_infNorm_eq]
  norm_num

/-- Norm-level magnitude gap visible directly in the printed scaled-residual
rows. -/
theorem cramerGeppExample_scaledResidual_infNorm_gap :
    (10 : ℝ)^9 * infNormVec cramerGeppExampleGeppScaledResidual <
      infNormVec cramerGeppExampleCramerScaledResidual := by
  simpa [cramerGeppExampleCramerScaledResidual,
    cramerGeppExampleGeppScaledResidual] using
    cramerGeppExample_residual_infNorm_gap

/-- Exact squared Euclidean norm of the printed Cramer's-rule scaled-residual
vector, under its legacy residual-vector name. -/
theorem cramerGeppExample_cramerResidual_vecNorm2Sq_eq :
    vecNorm2Sq cramerGeppExampleCramerResidual =
      ((15075 : ℝ)^2 + (19285 : ℝ)^2) / (10 : ℝ)^22 := by
  unfold vecNorm2Sq
  rw [Fin.sum_univ_two]
  norm_num [cramerGeppExampleCramerResidual]

/-- Exact squared Euclidean norm of the printed Cramer's-rule scaled-residual
vector. -/
theorem cramerGeppExample_cramerScaledResidual_vecNorm2Sq_eq :
    vecNorm2Sq cramerGeppExampleCramerScaledResidual =
      ((15075 : ℝ)^2 + (19285 : ℝ)^2) / (10 : ℝ)^22 := by
  simpa [cramerGeppExampleCramerScaledResidual] using
    cramerGeppExample_cramerResidual_vecNorm2Sq_eq

/-- Exact squared Euclidean norm of the printed GEPP scaled-residual vector,
under its legacy residual-vector name. -/
theorem cramerGeppExample_geppResidual_vecNorm2Sq_eq :
    vecNorm2Sq cramerGeppExampleGeppResidual =
      ((45689 : ℝ)^2 + (21931 : ℝ)^2) / (10 : ℝ)^42 := by
  unfold vecNorm2Sq
  rw [Fin.sum_univ_two]
  norm_num [cramerGeppExampleGeppResidual]

/-- Exact squared Euclidean norm of the printed GEPP scaled-residual vector. -/
theorem cramerGeppExample_geppScaledResidual_vecNorm2Sq_eq :
    vecNorm2Sq cramerGeppExampleGeppScaledResidual =
      ((45689 : ℝ)^2 + (21931 : ℝ)^2) / (10 : ℝ)^42 := by
  simpa [cramerGeppExampleGeppScaledResidual] using
    cramerGeppExample_geppResidual_vecNorm2Sq_eq

/-- Exact squared Euclidean norm of the printed Cramer's-rule solution vector. -/
theorem cramerGeppExample_cramerSolution_vecNorm2Sq_eq :
    vecNorm2Sq cramerGeppExampleCramerSolution =
      ((10000 : ℝ)^2 + (20001 : ℝ)^2) / (10 : ℝ)^8 := by
  simp [vecNorm2Sq, cramerGeppExampleCramerSolution, Fin.sum_univ_two]
  ring_nf

/-- Exact squared Euclidean norm of the printed GEPP solution vector. -/
theorem cramerGeppExample_geppSolution_vecNorm2Sq_eq :
    vecNorm2Sq cramerGeppExampleGeppSolution =
      ((10002 : ℝ)^2 + (20004 : ℝ)^2) / (10 : ℝ)^8 := by
  unfold vecNorm2Sq
  rw [Fin.sum_univ_two]
  norm_num [cramerGeppExampleGeppSolution]

/-- Direct squared 2-norm gap for the printed scaled-residual vectors: the
Cramer's-rule scaled residual has squared norm more than `10^18` times the
GEPP scaled residual's squared norm. -/
theorem cramerGeppExample_scaledResidual_vecNorm2Sq_gap :
    (10 : ℝ)^18 * vecNorm2Sq cramerGeppExampleGeppScaledResidual <
      vecNorm2Sq cramerGeppExampleCramerScaledResidual := by
  rw [cramerGeppExample_geppScaledResidual_vecNorm2Sq_eq,
    cramerGeppExample_cramerScaledResidual_vecNorm2Sq_eq]
  norm_num

/-- Legacy mixed comparison over the printed scaled-residual entries and the
printed solution vector norms.  The direct source-facing scaled-residual
comparison is `cramerGeppExample_scaledResidual_vecNorm2Sq_gap`. -/
theorem cramerGeppExample_printed_scaledResidual2Sq_gap :
    (10 : ℝ)^18 * vecNorm2Sq cramerGeppExampleGeppResidual *
        vecNorm2Sq cramerGeppExampleCramerSolution <
      vecNorm2Sq cramerGeppExampleCramerResidual *
        vecNorm2Sq cramerGeppExampleGeppSolution := by
  rw [cramerGeppExample_geppResidual_vecNorm2Sq_eq,
    cramerGeppExample_cramerSolution_vecNorm2Sq_eq,
    cramerGeppExample_cramerResidual_vecNorm2Sq_eq,
    cramerGeppExample_geppSolution_vecNorm2Sq_eq]
  norm_num

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

/-- Component vector in Higham Problem 1.9's condition quantity:
`|A^{-1}| |A| |x|`. -/
noncomputable def cramer2x2CondVec
    (A A_inv : Fin 2 → Fin 2 → ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  matMulVec 2 (matMul 2 (absMatrix 2 A_inv) (absMatrix 2 A)) (absVec 2 x)

/-- Higham Problem 1.9's normwise condition quantity at a vector `x`:
`‖ |A^{-1}| |A| |x| ‖∞ / ‖x‖∞`. -/
noncomputable def cramer2x2CondAt
    (A A_inv : Fin 2 → Fin 2 → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  infNormVec (cramer2x2CondVec A A_inv x) / infNormVec x

/-- Component vector `|A^{-1}| |b|`, the natural Cramer numerator-error scale
for the residual-side inequality in Problem 1.9. -/
noncomputable def cramer2x2InvAbsRhs
    (A_inv : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) : Fin 2 → ℝ :=
  matMulVec 2 (absMatrix 2 A_inv) (absVec 2 b)

/-- Component vector `|A| |A^{-1}| |b|` for the residual-side inequality in
Problem 1.9. -/
noncomputable def cramer2x2ResidualCondVec
    (A A_inv : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) : Fin 2 → ℝ :=
  matMulVec 2 (matMul 2 (absMatrix 2 A) (absMatrix 2 A_inv)) (absVec 2 b)

/-- Higham Problem 1.9's residual-side condition quantity
`cond(A^{-1}) = ‖ |A| |A^{-1}| ‖∞`. -/
noncomputable def cramer2x2ResidualCond
    (A A_inv : Fin 2 → Fin 2 → ℝ) : ℝ :=
  infNorm (matMul 2 (absMatrix 2 A) (absMatrix 2 A_inv))

/-- The explicit inverse of a nonsingular `2 × 2` matrix used in the
condition-number restatement of Problem 1.9. -/
noncomputable def cramer2x2Inverse (A : Fin 2 → Fin 2 → ℝ) :
    Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 then
      if j = 0 then A 1 1 / det2x2Matrix A else -A 0 1 / det2x2Matrix A
    else
      if j = 0 then -A 1 0 / det2x2Matrix A else A 0 0 / det2x2Matrix A

/-- The explicit 2-by-2 inverse is a left inverse when `det(A) != 0`. -/
theorem cramer2x2Inverse_isLeftInverse
    (A : Fin 2 → Fin 2 → ℝ) (hdet : det2x2Matrix A ≠ 0) :
    IsLeftInverse 2 A (cramer2x2Inverse A) := by
  have hdet_main : A 0 0 * A 1 1 - A 1 0 * A 0 1 ≠ 0 := by
    simpa [det2x2Matrix, det2x2] using hdet
  have hdet_comm : A 1 1 * A 0 0 - A 1 0 * A 0 1 ≠ 0 := by
    intro h
    apply hdet
    rw [show det2x2Matrix A = A 1 1 * A 0 0 - A 1 0 * A 0 1 by
      unfold det2x2Matrix det2x2
      ring]
    exact h
  have hdet_add : -(A 1 0 * A 0 1) + A 0 0 * A 1 1 ≠ 0 := by
    intro h
    apply hdet
    rw [show det2x2Matrix A = -(A 1 0 * A 0 1) + A 0 0 * A 1 1 by
      unfold det2x2Matrix det2x2
      ring]
    exact h
  intro i j
  fin_cases i <;> fin_cases j <;>
    unfold cramer2x2Inverse det2x2Matrix det2x2 <;>
    simp <;>
    field_simp [hdet_main, hdet_comm, hdet_add] <;>
    ring

/-- The explicit 2-by-2 inverse is a right inverse when `det(A) != 0`. -/
theorem cramer2x2Inverse_isRightInverse
    (A : Fin 2 → Fin 2 → ℝ) (hdet : det2x2Matrix A ≠ 0) :
    IsRightInverse 2 A (cramer2x2Inverse A) := by
  have hdet_main : A 0 0 * A 1 1 - A 1 0 * A 0 1 ≠ 0 := by
    simpa [det2x2Matrix, det2x2] using hdet
  intro i j
  fin_cases i <;> fin_cases j <;>
    unfold cramer2x2Inverse det2x2Matrix det2x2 <;>
    simp <;>
    field_simp [hdet_main] <;>
    ring

/-- The explicit 2-by-2 inverse is a two-sided inverse when `det(A) != 0`. -/
theorem cramer2x2Inverse_isInverse
    (A : Fin 2 → Fin 2 → ℝ) (hdet : det2x2Matrix A ≠ 0) :
    IsInverse 2 A (cramer2x2Inverse A) :=
  ⟨cramer2x2Inverse_isLeftInverse A hdet,
    cramer2x2Inverse_isRightInverse A hdet⟩

lemma cramer2x2CondVec_nonneg
    (A A_inv : Fin 2 → Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    ∀ i : Fin 2, 0 ≤ cramer2x2CondVec A A_inv x i := by
  intro i
  unfold cramer2x2CondVec matMulVec matMul absMatrix absVec
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (abs_nonneg _))

lemma cramer2x2InvAbsRhs_nonneg
    (A_inv : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    ∀ i : Fin 2, 0 ≤ cramer2x2InvAbsRhs A_inv b i := by
  intro i
  unfold cramer2x2InvAbsRhs matMulVec absMatrix absVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))

lemma cramer2x2ResidualCondVec_nonneg
    (A A_inv : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    ∀ i : Fin 2, 0 ≤ cramer2x2ResidualCondVec A A_inv b i := by
  intro i
  unfold cramer2x2ResidualCondVec matMulVec matMul absMatrix absVec
  exact Finset.sum_nonneg (fun j _ =>
    mul_nonneg
      (Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)))
      (abs_nonneg _))

lemma cramer2x2ResidualCond_nonneg
    (A A_inv : Fin 2 → Fin 2 → ℝ) :
    0 ≤ cramer2x2ResidualCond A A_inv := by
  unfold cramer2x2ResidualCond
  exact infNorm_nonneg _

/-- Problem 1.9 norm-level adapter.  If each component of a computed 2-by-2
Cramer solution has error at most `γ * (|A^{-1}| |A| |x|)_i`, then the
relative infinity-norm forward error is at most
`γ * ‖ |A^{-1}| |A| |x| ‖∞ / ‖x‖∞`. -/
theorem cramer2x2_relative_forward_error_le_gamma_condAt_of_componentwise
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A A_inv : Fin 2 → Fin 2 → ℝ) (x xHat : Fin 2 → ℝ)
    (hx : infNormVec x ≠ 0)
    (hcomp : ∀ i : Fin 2,
      |xHat i - x i| ≤ γ * cramer2x2CondVec A A_inv x i) :
    infNormVec (fun i => xHat i - x i) / infNormVec x ≤
      γ * cramer2x2CondAt A A_inv x := by
  have hx_pos : 0 < infNormVec x :=
    lt_of_le_of_ne (infNormVec_nonneg x) (Ne.symm hx)
  have hcond_component :
      ∀ i : Fin 2,
        cramer2x2CondVec A A_inv x i ≤
          infNormVec (cramer2x2CondVec A A_inv x) := by
    intro i
    have habs := abs_le_infNormVec (cramer2x2CondVec A A_inv x) i
    rwa [abs_of_nonneg (cramer2x2CondVec_nonneg A A_inv x i)] at habs
  have hcomp_norm :
      ∀ i : Fin 2,
        |xHat i - x i| ≤ γ * infNormVec (cramer2x2CondVec A A_inv x) := by
    intro i
    exact le_trans (hcomp i)
      (mul_le_mul_of_nonneg_left (hcond_component i) hγ)
  have hnorm :
      infNormVec (fun i => xHat i - x i) ≤
        γ * infNormVec (cramer2x2CondVec A A_inv x) := by
    exact infNormVec_le_of_abs_le (fun i => xHat i - x i) hcomp_norm
      (mul_nonneg hγ (infNormVec_nonneg _))
  calc
    infNormVec (fun i => xHat i - x i) / infNormVec x
        ≤ (γ * infNormVec (cramer2x2CondVec A A_inv x)) / infNormVec x :=
          div_le_div_of_nonneg_right hnorm (le_of_lt hx_pos)
    _ = γ * cramer2x2CondAt A A_inv x := by
          unfold cramer2x2CondAt
          ring

/-- The first component of `|det(A)| * |A^{-1}| |A| |x|`, expanded for the
explicit 2-by-2 inverse. -/
lemma abs_det_mul_cramer2x2CondVec_inverse_zero
    (A : Fin 2 → Fin 2 → ℝ) (x : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    |det2x2Matrix A| *
        cramer2x2CondVec A (cramer2x2Inverse A) x 0 =
      (|A 0 0| * |x 0| + |A 0 1| * |x 1|) * |A 1 1| +
        (|A 1 0| * |x 0| + |A 1 1| * |x 1|) * |A 0 1| := by
  have hdet_abs : |det2x2Matrix A| ≠ 0 := abs_ne_zero.mpr hdet
  unfold cramer2x2CondVec cramer2x2Inverse matMulVec matMul absMatrix absVec
  simp [Fin.sum_univ_two, abs_div]
  field_simp [hdet_abs]
  ring

/-- The second component of `|det(A)| * |A^{-1}| |A| |x|`, expanded for the
explicit 2-by-2 inverse. -/
lemma abs_det_mul_cramer2x2CondVec_inverse_one
    (A : Fin 2 → Fin 2 → ℝ) (x : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    |det2x2Matrix A| *
        cramer2x2CondVec A (cramer2x2Inverse A) x 1 =
      (|A 0 0| * |x 0| + |A 0 1| * |x 1|) * |A 1 0| +
        (|A 1 0| * |x 0| + |A 1 1| * |x 1|) * |A 0 0| := by
  have hdet_abs : |det2x2Matrix A| ≠ 0 := abs_ne_zero.mpr hdet
  unfold cramer2x2CondVec cramer2x2Inverse matMulVec matMul absMatrix absVec
  simp [Fin.sum_univ_two, abs_div]
  field_simp [hdet_abs]
  ring

/-- For the exact Cramer solution `x`, the two-product numerator scale from
Problem 1.9 is bounded componentwise by the displayed
`|A^{-1}| |A| |x|` vector. -/
theorem cramer2x2NumeratorAbsTerms_div_det_le_condVec_inverse_solution
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    ∀ i : Fin 2,
      cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| ≤
        cramer2x2CondVec A (cramer2x2Inverse A) (cramer2x2Solution A b) i := by
  let x := cramer2x2Solution A b
  have hdet_abs_pos : 0 < |det2x2Matrix A| := abs_pos.mpr hdet
  have hb0_eq : b 0 = A 0 0 * x 0 + A 0 1 * x 1 := by
    have h := cramer2x2Solution_solves A b hdet 0
    simpa [Fin.sum_univ_two, x] using h.symm
  have hb1_eq : b 1 = A 1 0 * x 0 + A 1 1 * x 1 := by
    have h := cramer2x2Solution_solves A b hdet 1
    simpa [Fin.sum_univ_two, x] using h.symm
  have hb0_abs :
      |b 0| ≤ |A 0 0| * |x 0| + |A 0 1| * |x 1| := by
    rw [hb0_eq]
    calc
      |A 0 0 * x 0 + A 0 1 * x 1|
          ≤ |A 0 0 * x 0| + |A 0 1 * x 1| := abs_add_le _ _
      _ = |A 0 0| * |x 0| + |A 0 1| * |x 1| := by
          rw [abs_mul, abs_mul]
  have hb1_abs :
      |b 1| ≤ |A 1 0| * |x 0| + |A 1 1| * |x 1| := by
    rw [hb1_eq]
    calc
      |A 1 0 * x 0 + A 1 1 * x 1|
          ≤ |A 1 0 * x 0| + |A 1 1 * x 1| := abs_add_le _ _
      _ = |A 1 0| * |x 0| + |A 1 1| * |x 1| := by
          rw [abs_mul, abs_mul]
  intro i
  fin_cases i
  · have hnum :
        cramer2x2NumeratorAbsTerms A b 0 ≤
          |det2x2Matrix A| * cramer2x2CondVec A (cramer2x2Inverse A) x 0 := by
      calc
        cramer2x2NumeratorAbsTerms A b 0
            = |b 0| * |A 1 1| + |b 1| * |A 0 1| := by
                unfold cramer2x2NumeratorAbsTerms det2x2AbsTerms replaceCol2x2
                simp [abs_mul]
        _ ≤ (|A 0 0| * |x 0| + |A 0 1| * |x 1|) * |A 1 1| +
              (|A 1 0| * |x 0| + |A 1 1| * |x 1|) * |A 0 1| := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hb0_abs (abs_nonneg _))
                  (mul_le_mul_of_nonneg_right hb1_abs (abs_nonneg _))
        _ = |det2x2Matrix A| *
              cramer2x2CondVec A (cramer2x2Inverse A) x 0 := by
                rw [abs_det_mul_cramer2x2CondVec_inverse_zero A x hdet]
    exact (div_le_iff₀ hdet_abs_pos).mpr (by simpa [mul_comm, x] using hnum)
  · have hnum :
        cramer2x2NumeratorAbsTerms A b 1 ≤
          |det2x2Matrix A| * cramer2x2CondVec A (cramer2x2Inverse A) x 1 := by
      calc
        cramer2x2NumeratorAbsTerms A b 1
            = |b 0| * |A 1 0| + |b 1| * |A 0 0| := by
                unfold cramer2x2NumeratorAbsTerms det2x2AbsTerms replaceCol2x2
                simp [abs_mul]
                ring
        _ ≤ (|A 0 0| * |x 0| + |A 0 1| * |x 1|) * |A 1 0| +
              (|A 1 0| * |x 0| + |A 1 1| * |x 1|) * |A 0 0| := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_right hb0_abs (abs_nonneg _))
                  (mul_le_mul_of_nonneg_right hb1_abs (abs_nonneg _))
        _ = |det2x2Matrix A| *
              cramer2x2CondVec A (cramer2x2Inverse A) x 1 := by
                rw [abs_det_mul_cramer2x2CondVec_inverse_one A x hdet]
    exact (div_le_iff₀ hdet_abs_pos).mpr (by simpa [mul_comm, x] using hnum)

/-- The Cramer numerator product scale divided by the exact denominator is
exactly `|A^{-1}| |b|` for the explicit 2-by-2 inverse. -/
theorem cramer2x2NumeratorAbsTerms_div_det_eq_invAbsRhs_inverse
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    ∀ i : Fin 2,
      cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| =
        cramer2x2InvAbsRhs (cramer2x2Inverse A) b i := by
  have hdet_abs : |det2x2Matrix A| ≠ 0 := abs_ne_zero.mpr hdet
  intro i
  fin_cases i
  · unfold cramer2x2NumeratorAbsTerms det2x2AbsTerms replaceCol2x2
    unfold cramer2x2InvAbsRhs cramer2x2Inverse matMulVec absMatrix absVec
    simp [Fin.sum_univ_two, abs_mul, abs_div]
    field_simp [hdet_abs]
  · unfold cramer2x2NumeratorAbsTerms det2x2AbsTerms replaceCol2x2
    unfold cramer2x2InvAbsRhs cramer2x2Inverse matMulVec absMatrix absVec
    simp [Fin.sum_univ_two, abs_mul, abs_div]
    field_simp [hdet_abs]
    ring

-- ============================================================
-- Problem 1.9 forward-error bridge
-- ============================================================

/-- A two-product determinant evaluated as
`fl(fl(a11*a22) - fl(a21*a12))` has absolute error bounded by
`gamma_3 * (|a11*a22| + |a21*a12|)`.  This is the concrete floating-point
kernel used by Higham Problem 1.9 for the Cramer numerator determinants. -/
theorem flDet2x2_error_le_gamma3
    (fp : FPModel) (h3 : gammaValid fp 3)
    (a11 a12 a21 a22 : ℝ) :
    |flDet2x2 fp a11 a12 a21 a22 - det2x2 a11 a12 a21 a22| ≤
      gamma fp 3 * det2x2AbsTerms a11 a12 a21 a22 := by
  let p : ℝ := a11 * a22
  let q : ℝ := a21 * a12
  obtain ⟨δp, hδp, hp⟩ := fp.model_mul a11 a22
  obtain ⟨δq, hδq, hq⟩ := fp.model_mul a21 a12
  obtain ⟨δs, hδs, hs⟩ :=
    fp.model_sub (fp.fl_mul a11 a22) (fp.fl_mul a21 a12)
  have h1 : gammaValid fp 1 := gammaValid_mono fp (by decide : 1 ≤ 3) h3
  have h2 : gammaValid fp 2 := gammaValid_mono fp (by decide : 2 ≤ 3) h3
  have hδp1 : |δp| ≤ gamma fp 1 := le_trans hδp (u_le_gamma fp (by decide) h1)
  have hδq1 : |δq| ≤ gamma fp 1 := le_trans hδq (u_le_gamma fp (by decide) h1)
  have hδs1 : |δs| ≤ gamma fp 1 := le_trans hδs (u_le_gamma fp (by decide) h1)
  obtain ⟨θp, hθp2, hθp_eq⟩ :=
    gamma_mul fp 1 1 δp δs hδp1 hδs1 (by simpa using h2)
  obtain ⟨θq, hθq2, hθq_eq⟩ :=
    gamma_mul fp 1 1 δq δs hδq1 hδs1 (by simpa using h2)
  have hθp3 : |θp| ≤ gamma fp 3 :=
    le_trans hθp2 (gamma_mono fp (by decide : 2 ≤ 3) h3)
  have hθq3 : |θq| ≤ gamma fp 3 :=
    le_trans hθq2 (gamma_mono fp (by decide : 2 ≤ 3) h3)
  have hp' : fp.fl_mul a11 a22 = p * (1 + δp) := by
    simpa [p] using hp
  have hq' : fp.fl_mul a21 a12 = q * (1 + δq) := by
    simpa [q] using hq
  have hfl :
      flDet2x2 fp a11 a12 a21 a22 =
        p * (1 + θp) - q * (1 + θq) := by
    unfold flDet2x2
    calc
      fp.fl_sub (fp.fl_mul a11 a22) (fp.fl_mul a21 a12)
          = (fp.fl_mul a11 a22 - fp.fl_mul a21 a12) * (1 + δs) := hs
      _ = (p * (1 + δp) - q * (1 + δq)) * (1 + δs) := by
            rw [hp', hq']
      _ = p * ((1 + δp) * (1 + δs)) -
            q * ((1 + δq) * (1 + δs)) := by
            ring
      _ = p * (1 + θp) - q * (1 + θq) := by
            rw [hθp_eq, hθq_eq]
  have hdet : det2x2 a11 a12 a21 a22 = p - q := by
    simp [det2x2, p, q]
  have hterms : det2x2AbsTerms a11 a12 a21 a22 = |p| + |q| := by
    simp [det2x2AbsTerms, p, q]
  calc
    |flDet2x2 fp a11 a12 a21 a22 - det2x2 a11 a12 a21 a22|
        = |(p * (1 + θp) - q * (1 + θq)) - (p - q)| := by
            rw [hfl, hdet]
    _ = |p * θp - q * θq| := by
            congr 1
            ring
    _ ≤ |p * θp| + |q * θq| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (p * θp) (-(q * θq))
    _ = |p| * |θp| + |q| * |θq| := by
            rw [abs_mul p θp, abs_mul q θq]
    _ ≤ |p| * gamma fp 3 + |q| * gamma fp 3 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hθp3 (abs_nonneg p))
              (mul_le_mul_of_nonneg_left hθq3 (abs_nonneg q))
    _ = gamma fp 3 * det2x2AbsTerms a11 a12 a21 a22 := by
            rw [hterms]
            ring

/-- The concrete rounded Cramer numerator determinant satisfies the
`gamma_3` product-magnitude error bound from Problem 1.9. -/
theorem flCramer2x2Numerator_error_le_gamma3
    (fp : FPModel) (h3 : gammaValid fp 3)
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ) :
    ∀ i : Fin 2,
      |flCramer2x2Numerator fp A b i - cramer2x2Numerator A b i| ≤
        gamma fp 3 * cramer2x2NumeratorAbsTerms A b i := by
  intro i
  simpa [flCramer2x2Numerator, cramer2x2Numerator, cramer2x2NumeratorAbsTerms,
    det2x2Matrix] using
      flDet2x2_error_le_gamma3 fp h3
        (replaceCol2x2 A b i 0 0) (replaceCol2x2 A b i 0 1)
        (replaceCol2x2 A b i 1 0) (replaceCol2x2 A b i 1 1)

/-- Dividing by the same exact nonzero denominator transports an absolute
numerator error to an absolute quotient error. -/
theorem div_same_den_abs_error_le
    (numHat num den η : ℝ) (hden : den ≠ 0)
    (hnum : |numHat - num| ≤ η) :
    |numHat / den - num / den| ≤ η / |den| := by
  have hdiff : numHat / den - num / den = (numHat - num) / den := by
    field_simp [hden]
  calc
    |numHat / den - num / den|
        = |(numHat - num) / den| := by rw [hdiff]
    _ = |numHat - num| / |den| := by rw [abs_div]
    _ ≤ η / |den| :=
        div_le_div_of_nonneg_right hnum (abs_nonneg den)

/-- Problem 1.9 denominator-exact bridge: if the computed Cramer numerator
determinants have absolute errors bounded by `η_i`, then the componentwise
forward errors of the resulting Cramer solution are bounded by
`η_i / |det(A)|`. -/
theorem cramer2x2Solution_error_from_numerator_errors
    (A : Fin 2 → Fin 2 → ℝ) (b numHat η : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0)
    (hnum : ∀ i : Fin 2,
      |numHat i - cramer2x2Numerator A b i| ≤ η i) :
    ∀ i : Fin 2,
      |cramer2x2ComputedFromNumerators A numHat i -
          cramer2x2Solution A b i| ≤ η i / |det2x2Matrix A| := by
  intro i
  unfold cramer2x2ComputedFromNumerators cramer2x2Solution
  exact div_same_den_abs_error_le
    (numHat i) (det2x2Matrix (replaceCol2x2 A b i)) (det2x2Matrix A) (η i)
    hdet (by simpa [cramer2x2Numerator] using hnum i)

/-- Product-magnitude version of the Problem 1.9 bridge.  If the rounded
numerator determinant for each component has absolute error at most
`γ * (|p_i| + |q_i|)`, where `p_i` and `q_i` are the two determinant products,
then the componentwise Cramer solution error is bounded by that quantity
divided by the exact denominator determinant. -/
theorem cramer2x2Solution_error_from_absTerm_numerator_bounds
    (A : Fin 2 → Fin 2 → ℝ) (b numHat : Fin 2 → ℝ) (γ : ℝ)
    (hdet : det2x2Matrix A ≠ 0)
    (hnum : ∀ i : Fin 2,
      |numHat i - cramer2x2Numerator A b i| ≤
        γ * cramer2x2NumeratorAbsTerms A b i) :
    ∀ i : Fin 2,
      |cramer2x2ComputedFromNumerators A numHat i -
          cramer2x2Solution A b i| ≤
        γ * cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| := by
  exact cramer2x2Solution_error_from_numerator_errors
    A b numHat (fun i => γ * cramer2x2NumeratorAbsTerms A b i) hdet hnum

/-- Problem 1.9 concrete rounded-numerator bridge under the source assumption
that the denominator determinant `d` is computed exactly.  The numerator
determinants are evaluated by `flDet2x2`, and their `gamma_3` error bounds are
propagated to componentwise forward-error bounds for Cramer's rule. -/
theorem cramer2x2Solution_error_from_flNumerators_exact_den
    (fp : FPModel) (h3 : gammaValid fp 3)
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    ∀ i : Fin 2,
      |cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b) i -
          cramer2x2Solution A b i| ≤
        gamma fp 3 * cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| := by
  exact cramer2x2Solution_error_from_absTerm_numerator_bounds
    A b (flCramer2x2Numerator fp A b) (gamma fp 3) hdet
    (flCramer2x2Numerator_error_le_gamma3 fp h3 A b)

/-- Rounded Cramer numerator determinants, with exact denominator, give a
componentwise solution-error bound in the `|A^{-1}| |b|` scale used by the
residual side of Problem 1.9. -/
theorem cramer2x2Solution_error_from_flNumerators_exact_den_invAbsRhs
    (fp : FPModel) (h3 : gammaValid fp 3)
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    ∀ i : Fin 2,
      |cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b) i -
          cramer2x2Solution A b i| ≤
        gamma fp 3 * cramer2x2InvAbsRhs (cramer2x2Inverse A) b i := by
  intro i
  have hnum :=
    cramer2x2Solution_error_from_flNumerators_exact_den fp h3 A b hdet i
  calc
    |cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b) i -
        cramer2x2Solution A b i|
        ≤ gamma fp 3 * cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| :=
          hnum
    _ = gamma fp 3 *
          (cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A|) := by
          ring
    _ = gamma fp 3 * cramer2x2InvAbsRhs (cramer2x2Inverse A) b i := by
          rw [cramer2x2NumeratorAbsTerms_div_det_eq_invAbsRhs_inverse A b hdet i]

/-- Residual-side norm adapter for Problem 1.9.  If the solution component
errors are bounded by `γ * |A^{-1}| |b|`, then the residual is bounded by
`γ * ‖ |A| |A^{-1}| |b| ‖∞`. -/
theorem cramer2x2Residual_infNorm_le_gamma_residualCondVec_of_componentwise
    (γ : ℝ) (hγ : 0 ≤ γ)
    (A A_inv : Fin 2 → Fin 2 → ℝ) (b x xHat : Fin 2 → ℝ)
    (hAx : ∀ i : Fin 2, ∑ j : Fin 2, A i j * x j = b i)
    (hcomp : ∀ i : Fin 2,
      |xHat i - x i| ≤ γ * cramer2x2InvAbsRhs A_inv b i) :
    infNormVec (fun i => b i - matMulVec 2 A xHat i) ≤
      γ * infNormVec (cramer2x2ResidualCondVec A A_inv b) := by
  have hcomponent :
      ∀ i : Fin 2,
        |b i - matMulVec 2 A xHat i| ≤
          γ * cramer2x2ResidualCondVec A A_inv b i := by
    intro i
    have hres_eq :
        b i - matMulVec 2 A xHat i =
          -matMulVec 2 A (fun j => xHat j - x j) i := by
      rw [← hAx i]
      unfold matMulVec
      simp [Fin.sum_univ_two]
      ring
    calc
      |b i - matMulVec 2 A xHat i|
          = |matMulVec 2 A (fun j => xHat j - x j) i| := by
              rw [hres_eq, abs_neg]
      _ ≤ ∑ j : Fin 2, |A i j| * |xHat j - x j| :=
          abs_matMulVec_le 2 A (fun j => xHat j - x j) i
      _ ≤ ∑ j : Fin 2, |A i j| * (γ * cramer2x2InvAbsRhs A_inv b j) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (hcomp j) (abs_nonneg _)
      _ = γ * matMulVec 2 (absMatrix 2 A) (cramer2x2InvAbsRhs A_inv b) i := by
          unfold matMulVec absMatrix
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = γ * cramer2x2ResidualCondVec A A_inv b i := by
          unfold cramer2x2ResidualCondVec cramer2x2InvAbsRhs
          rw [← matMulVec_matMul 2 (absMatrix 2 A) (absMatrix 2 A_inv) (absVec 2 b) i]
  have hcomponent_norm :
      ∀ i : Fin 2,
        |b i - matMulVec 2 A xHat i| ≤
          γ * infNormVec (cramer2x2ResidualCondVec A A_inv b) := by
    intro i
    have hcond_i :
        cramer2x2ResidualCondVec A A_inv b i ≤
          infNormVec (cramer2x2ResidualCondVec A A_inv b) := by
      have habs := abs_le_infNormVec (cramer2x2ResidualCondVec A A_inv b) i
      rwa [abs_of_nonneg (cramer2x2ResidualCondVec_nonneg A A_inv b i)] at habs
    exact le_trans (hcomponent i) (mul_le_mul_of_nonneg_left hcond_i hγ)
  exact infNormVec_le_of_abs_le
    (fun i => b i - matMulVec 2 A xHat i) hcomponent_norm
    (mul_nonneg hγ (infNormVec_nonneg _))

/-- Problem 1.9 residual-side condition-number form for the modeled Cramer
computation: with exact denominator determinant and rounded numerator
determinants evaluated as `fl(fl(a*b)-fl(c*d))`, the infinity-norm residual is
bounded by `gamma_3 * cond(A^{-1}) * ‖b‖∞`, where
`cond(A^{-1}) = ‖ |A| |A^{-1}| ‖∞` for the explicit 2-by-2 inverse. -/
theorem cramer2x2Residual_infNorm_from_flNumerators_exact_den_condInv
    (fp : FPModel) (h3 : gammaValid fp 3)
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0) :
    infNormVec (fun i =>
        b i - matMulVec 2 A
          (cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b)) i) ≤
      gamma fp 3 * cramer2x2ResidualCond A (cramer2x2Inverse A) * infNormVec b := by
  let x := cramer2x2Solution A b
  let xHat := cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b)
  have hγ : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  have hAx : ∀ i : Fin 2, ∑ j : Fin 2, A i j * x j = b i := by
    simpa [x] using cramer2x2Solution_solves A b hdet
  have hcomp : ∀ i : Fin 2,
      |xHat i - x i| ≤
        gamma fp 3 * cramer2x2InvAbsRhs (cramer2x2Inverse A) b i := by
    simpa [x, xHat] using
      cramer2x2Solution_error_from_flNumerators_exact_den_invAbsRhs fp h3 A b hdet
  have hres :=
    cramer2x2Residual_infNorm_le_gamma_residualCondVec_of_componentwise
      (gamma fp 3) hγ A (cramer2x2Inverse A) b x xHat hAx hcomp
  have hcond_vec :
      infNormVec (cramer2x2ResidualCondVec A (cramer2x2Inverse A) b) ≤
        cramer2x2ResidualCond A (cramer2x2Inverse A) * infNormVec b := by
    unfold cramer2x2ResidualCondVec cramer2x2ResidualCond
    have hmv :=
      infNormVec_matMulVec_le (by decide : 0 < 2)
        (matMul 2 (absMatrix 2 A) (absMatrix 2 (cramer2x2Inverse A)))
        (absVec 2 b)
    rwa [infNormVec_absVec (by decide : 0 < 2) b] at hmv
  calc
    infNormVec (fun i => b i - matMulVec 2 A xHat i)
        ≤ gamma fp 3 *
            infNormVec (cramer2x2ResidualCondVec A (cramer2x2Inverse A) b) :=
          hres
    _ ≤ gamma fp 3 *
          (cramer2x2ResidualCond A (cramer2x2Inverse A) * infNormVec b) :=
          mul_le_mul_of_nonneg_left hcond_vec hγ
    _ = gamma fp 3 * cramer2x2ResidualCond A (cramer2x2Inverse A) * infNormVec b := by
          ring

/-- Problem 1.9 condition-number-facing bridge for the denominator-exact
rounded-numerator Cramer computation.  The remaining algebraic side condition
is precisely the componentwise comparison that rewrites the two Cramer
numerator product magnitudes, divided by `|det(A)|`, into the displayed
`|A^{-1}| |A| |x|` vector. -/
theorem cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_of_condVec_bound
    (fp : FPModel) (h3 : gammaValid fp 3)
    (A A_inv : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0)
    (hx : infNormVec (cramer2x2Solution A b) ≠ 0)
    (hcond : ∀ i : Fin 2,
      cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| ≤
        cramer2x2CondVec A A_inv (cramer2x2Solution A b) i) :
    infNormVec (fun i =>
        cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b) i -
          cramer2x2Solution A b i) /
        infNormVec (cramer2x2Solution A b) ≤
      gamma fp 3 * cramer2x2CondAt A A_inv (cramer2x2Solution A b) := by
  have hγ : 0 ≤ gamma fp 3 := gamma_nonneg fp h3
  apply cramer2x2_relative_forward_error_le_gamma_condAt_of_componentwise
    (gamma fp 3) hγ A A_inv (cramer2x2Solution A b)
    (cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b)) hx
  intro i
  have hnum :=
    cramer2x2Solution_error_from_flNumerators_exact_den fp h3 A b hdet i
  calc
    |cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b) i -
        cramer2x2Solution A b i|
        ≤ gamma fp 3 * cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A| :=
          hnum
    _ = gamma fp 3 *
          (cramer2x2NumeratorAbsTerms A b i / |det2x2Matrix A|) := by
          ring
    _ ≤ gamma fp 3 * cramer2x2CondVec A A_inv (cramer2x2Solution A b) i :=
          mul_le_mul_of_nonneg_left (hcond i) hγ

/-- Problem 1.9 final forward condition-number form for the modeled Cramer
computation: with exact denominator determinant and rounded numerator
determinants evaluated as `fl(fl(a*b)-fl(c*d))`, the relative infinity-norm
forward error is bounded by `gamma_3 * cond(A,x)`, where
`cond(A,x) = ‖ |A^{-1}| |A| |x| ‖∞ / ‖x‖∞` and `A^{-1}` is the explicit
2-by-2 inverse. -/
theorem cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_condAt
    (fp : FPModel) (h3 : gammaValid fp 3)
    (A : Fin 2 → Fin 2 → ℝ) (b : Fin 2 → ℝ)
    (hdet : det2x2Matrix A ≠ 0)
    (hx : infNormVec (cramer2x2Solution A b) ≠ 0) :
    infNormVec (fun i =>
        cramer2x2ComputedFromNumerators A (flCramer2x2Numerator fp A b) i -
          cramer2x2Solution A b i) /
        infNormVec (cramer2x2Solution A b) ≤
      gamma fp 3 *
        cramer2x2CondAt A (cramer2x2Inverse A) (cramer2x2Solution A b) := by
  exact
    cramer2x2Solution_relative_forward_error_from_flNumerators_exact_den_of_condVec_bound
      fp h3 A (cramer2x2Inverse A) b hdet hx
      (cramer2x2NumeratorAbsTerms_div_det_le_condVec_inverse_solution A b hdet)

end NumStability
