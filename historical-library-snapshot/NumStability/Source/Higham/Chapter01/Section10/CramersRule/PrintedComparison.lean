import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding

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


























































































































































































































































































































-- ============================================================
-- Problem 1.9 forward-error bridge
-- ============================================================



















































































































































































































































































































































end NumStability
