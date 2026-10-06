import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.MatrixEquations.Sylvester.Solvers.QuasiTriangularBartelsStewart.BlockTraversal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10

/-!
# Source.Higham.Chapter16.Section02.BartelsStewart.Equations04To08.HessenbergSchur

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16HessenbergSchur.lean
--
-- Exact Hessenberg-Schur handoff for Higham, 2nd ed., Chapter 16.2.














namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    shifting the singleton Bartels-Stewart column coefficient by `t I`
    preserves the upper-Hessenberg zero pattern. -/
theorem sylvesterTriangularShiftedCoeff_isUpperHessenberg
    (m : Nat) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R) :
    IsUpperHessenberg m (sylvesterTriangularShiftedCoeff m R t) := by
  intro i j hij
  have hne : i ≠ j := by
    intro h
    subst h
    omega
  simp [sylvesterTriangularShiftedCoeff, hR i j hij, hne]

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    a nonsingular shifted singleton column coefficient with upper-Hessenberg
    structure admits the Chapter 9 exact GEPP Hessenberg `U` trace.  This is a
    structural bridge only; it does not model rounded Bartels-Stewart arithmetic
    or a LAPACK-style estimator. -/
theorem exists_HessenbergGEPPUTrace_sylvesterTriangularShiftedCoeff_of_det_ne_zero
    (m : Nat) (hm : 0 < m) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R)
    (hdet : Matrix.det (sylvesterTriangularShiftedCoeff m R t) ≠ 0) :
    exists U : Fin m -> Fin m -> Real,
      higham9_10_HessenbergGEPPUTrace
        (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t))
        1 m (sylvesterTriangularShiftedCoeff m R t) U := by
  exact
    higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero
      hm (sylvesterTriangularShiftedCoeff m R t)
      (sylvesterTriangularShiftedCoeff_isUpperHessenberg m R t hR)
      (by simpa [Matrix.of_apply] using hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    the Chapter 9 upper-Hessenberg GEPP trace for a nonsingular shifted
    singleton column coefficient also satisfies Wilkinson's exact max-entry
    growth-factor bound.  This packages the structural handoff for later
    solver-analysis use without asserting rounded Schur arithmetic. -/
theorem exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero
    (m : Nat) (hm : 0 < m) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R)
    (hdet : Matrix.det (sylvesterTriangularShiftedCoeff m R t) ≠ 0)
    (hmax : 0 < maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t)) :
    exists U : Fin m -> Fin m -> Real,
      higham9_10_HessenbergGEPPUTrace
        (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t))
        1 m (sylvesterTriangularShiftedCoeff m R t) U /\
      growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R t) U hmax <=
        (m : Real) := by
  exact
    higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero
      hm (sylvesterTriangularShiftedCoeff m R t)
      (sylvesterTriangularShiftedCoeff_isUpperHessenberg m R t hR)
      (by simpa [Matrix.of_apply] using hdet)
      hmax

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6), Hessenberg-Schur handoff:
    nonsingularity of the shifted singleton column coefficient also supplies
    the positive max-entry denominator needed for the Chapter 9 upper-Hessenberg
    growth-factor package. -/
theorem exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax
    (m : Nat) (hm : 0 < m) (R : RMatFn m m) (t : Real)
    (hR : IsUpperHessenberg m R)
    (hdet : Matrix.det (sylvesterTriangularShiftedCoeff m R t) ≠ 0) :
    exists hmax : 0 < maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t),
    exists U : Fin m -> Fin m -> Real,
      higham9_10_HessenbergGEPPUTrace
        (maxEntryNorm hm (sylvesterTriangularShiftedCoeff m R t))
        1 m (sylvesterTriangularShiftedCoeff m R t) U /\
      growthFactorEntry hm (sylvesterTriangularShiftedCoeff m R t) U hmax <=
        (m : Real) := by
  exact
    higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero_exists_hAmax
      hm (sylvesterTriangularShiftedCoeff m R t)
      (sylvesterTriangularShiftedCoeff_isUpperHessenberg m R t hR)
      (by simpa [Matrix.of_apply] using hdet)

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for preservation of upper-Hessenberg structure by the
    shifted singleton Schur-column coefficient. -/
alias H16_eq16_6_sylvesterTriangularShiftedCoeff_isUpperHessenberg :=
  sylvesterTriangularShiftedCoeff_isUpperHessenberg

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for the exact Hessenberg GEPP trace handoff for a
    nonsingular shifted singleton Schur-column coefficient. -/
alias H16_eq16_6_exists_HessenbergGEPPUTrace_sylvesterTriangularShiftedCoeff_of_det_ne_zero :=
  exists_HessenbergGEPPUTrace_sylvesterTriangularShiftedCoeff_of_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for the exact Hessenberg GEPP trace and growth bound
    for a nonsingular shifted singleton Schur-column coefficient. -/
alias H16_eq16_6_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero :=
  exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero

/-- Higham, 2nd ed., Chapter 16.2, equation (16.6):
    source-numbered alias for the denominator-free exact Hessenberg GEPP trace
    and growth-bound package for a nonsingular shifted singleton coefficient. -/
alias H16_eq16_6_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax :=
  exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_sylvesterTriangularShiftedCoeff_of_det_ne_zero_exists_hmax

































































































































































































































































































































































































































































































































































































































































































end NumStability
