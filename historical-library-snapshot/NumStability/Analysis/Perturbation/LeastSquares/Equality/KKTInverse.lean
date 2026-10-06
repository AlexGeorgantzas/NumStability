import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# KKTInverse

Canonical reusable module extracted without change from Higham20Theorem20_8.
-/

namespace Theorem20_8

/-- A conservative source-only coefficient that keeps each denominator in the
coupled KKT radius at least one half. -/
noncomputable def kktLocalSmallnessCoeff {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B) : ℝ :=
  1 +
    2 * LSEKKTInverseMultiplierStatCoeff hB hnull * frobNormRect B +
    2 * theorem20_8KKTSolutionSelfLinearCoeff hB hnull +
    8 * LSEKKTInverseSolutionStatCoeff hB hnull * frobNormRect B *
      theorem20_8KKTMultiplierSelfLinearCoeff hB hnull
/-- Reciprocal local threshold used for the uniform linear majorant of the KKT
radius. -/
noncomputable def kktLocalSmallnessThreshold {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B) : ℝ :=
  (kktLocalSmallnessCoeff hB hnull)⁻¹
/-- An `eps`-independent source coefficient for the local linear majorant of
`theorem20_8KKTSourceResidualRatioCoupledBound`.  The deliberately loose
constants make all denominator estimates explicit. -/
noncomputable def kktLocalLinearBoundCoeff {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  let residualScale := vecNorm2 (lsResidualHigham A b x) / vecNorm2 x
  let lambdaScale := LSEKKTInverseMultiplierDataCoeff hB hnull * residualScale
  let multiplierLinear :=
    LSEKKTInverseMultiplierDataCoeff hB hnull *
        (2 * frobNormRect A + residualScale) +
      LSEKKTInverseMultiplierStatCoeff hB hnull * frobNormRect A *
        (4 * frobNormRect A + 2 * residualScale) +
      2 * LSEKKTInverseMultiplierConstrCoeff hB hnull * frobNormRect B
  let multiplierCap := 2 * (lambdaScale + multiplierLinear)
  let solutionLinear :=
    LSEKKTInverseSolutionDataCoeff hB hnull *
        (2 * frobNormRect A + residualScale) +
      LSEKKTInverseSolutionStatCoeff hB hnull * frobNormRect B *
        multiplierCap +
      LSEKKTInverseSolutionStatCoeff hB hnull * frobNormRect A *
        (4 * frobNormRect A + 2 * residualScale) +
      2 * LSEKKTInverseSolutionConstrCoeff hB hnull * frobNormRect B
  4 * solutionLinear
theorem kktLocalSmallnessCoeff_ge_one {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B) :
    1 ≤ kktLocalSmallnessCoeff hB hnull := by
  have hm : 0 ≤ LSEKKTInverseMultiplierStatCoeff hB hnull :=
    LSEKKTInverseMultiplierStatCoeff_nonneg hB hnull
  have hs : 0 ≤ theorem20_8KKTSolutionSelfLinearCoeff hB hnull :=
    theorem20_8KKTSolutionSelfLinearCoeff_nonneg hB hnull
  have hc : 0 ≤ LSEKKTInverseSolutionStatCoeff hB hnull :=
    LSEKKTInverseSolutionStatCoeff_nonneg hB hnull
  have hml : 0 ≤ theorem20_8KKTMultiplierSelfLinearCoeff hB hnull :=
    theorem20_8KKTMultiplierSelfLinearCoeff_nonneg hB hnull
  have hBn : 0 ≤ frobNormRect B := frobNormRect_nonneg B
  have hmterm :
      0 ≤ 2 * LSEKKTInverseMultiplierStatCoeff hB hnull *
        frobNormRect B :=
    mul_nonneg (mul_nonneg (by norm_num) hm) hBn
  have hsterm :
      0 ≤ 2 * theorem20_8KKTSolutionSelfLinearCoeff hB hnull :=
    mul_nonneg (by norm_num) hs
  have hcterm :
      0 ≤ 8 * LSEKKTInverseSolutionStatCoeff hB hnull *
        frobNormRect B * theorem20_8KKTMultiplierSelfLinearCoeff hB hnull :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hc) hBn) hml
  dsimp [kktLocalSmallnessCoeff]
  linarith
theorem kktLocalSmallnessThreshold_pos {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B) :
    0 < kktLocalSmallnessThreshold hB hnull := by
  have hcoeff : 0 < kktLocalSmallnessCoeff hB hnull :=
    lt_of_lt_of_le zero_lt_one (kktLocalSmallnessCoeff_ge_one hB hnull)
  simpa [kktLocalSmallnessThreshold] using inv_pos.mpr hcoeff
/-- Scalar consequences of the conservative local KKT threshold. -/
theorem kktLocal_smallness_conditions {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B)
    {eps : ℝ} (heps_nonneg : 0 ≤ eps)
    (hsmall : eps < kktLocalSmallnessThreshold hB hnull) :
    eps ≤ 1 ∧
      LSEKKTInverseMultiplierStatCoeff hB hnull *
          (eps * frobNormRect B) ≤ (1 : ℝ) / 2 ∧
      theorem20_8KKTSolutionSelfCoeff hB hnull eps ≤ (1 : ℝ) / 2 ∧
      4 * eps ^ 2 *
          (LSEKKTInverseSolutionStatCoeff hB hnull * frobNormRect B *
            theorem20_8KKTMultiplierSelfLinearCoeff hB hnull) ≤
        (1 : ℝ) / 2 := by
  let mCoeff : ℝ :=
    LSEKKTInverseMultiplierStatCoeff hB hnull * frobNormRect B
  let sCoeff : ℝ := theorem20_8KKTSolutionSelfLinearCoeff hB hnull
  let cCoeff : ℝ :=
    LSEKKTInverseSolutionStatCoeff hB hnull * frobNormRect B *
      theorem20_8KKTMultiplierSelfLinearCoeff hB hnull
  let D : ℝ := kktLocalSmallnessCoeff hB hnull
  have hm : 0 ≤ mCoeff := by
    dsimp [mCoeff]
    exact mul_nonneg (LSEKKTInverseMultiplierStatCoeff_nonneg hB hnull)
      (frobNormRect_nonneg B)
  have hs : 0 ≤ sCoeff := by
    dsimp [sCoeff]
    exact theorem20_8KKTSolutionSelfLinearCoeff_nonneg hB hnull
  have hc : 0 ≤ cCoeff := by
    dsimp [cCoeff]
    exact mul_nonneg
      (mul_nonneg (LSEKKTInverseSolutionStatCoeff_nonneg hB hnull)
        (frobNormRect_nonneg B))
      (theorem20_8KKTMultiplierSelfLinearCoeff_nonneg hB hnull)
  have hD_ge_one : 1 ≤ D := by
    dsimp [D]
    exact kktLocalSmallnessCoeff_ge_one hB hnull
  have hD_pos : 0 < D := lt_of_lt_of_le zero_lt_one hD_ge_one
  have hsmall' : eps < D⁻¹ := by
    simpa [D, kktLocalSmallnessThreshold] using hsmall
  have hepsD : eps * D < 1 := by
    calc
      eps * D < D⁻¹ * D := mul_lt_mul_of_pos_right hsmall' hD_pos
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hD_pos)
  have heps_lt_one : eps < 1 := by
    calc
      eps = eps * 1 := by ring
      _ ≤ eps * D := mul_le_mul_of_nonneg_left hD_ge_one heps_nonneg
      _ < 1 := hepsD
  have heps_le_one : eps ≤ 1 := heps_lt_one.le
  have hD_eq : D = 1 + 2 * mCoeff + 2 * sCoeff + 8 * cCoeff := by
    dsimp [D, mCoeff, sCoeff, cCoeff, kktLocalSmallnessCoeff]
    ring
  have h2m_le : 2 * mCoeff ≤ D := by rw [hD_eq]; linarith
  have h2s_le : 2 * sCoeff ≤ D := by rw [hD_eq]; linarith
  have h8c_le : 8 * cCoeff ≤ D := by rw [hD_eq]; linarith
  have heps2m : eps * (2 * mCoeff) < 1 :=
    (mul_le_mul_of_nonneg_left h2m_le heps_nonneg).trans_lt hepsD
  have heps2s : eps * (2 * sCoeff) < 1 :=
    (mul_le_mul_of_nonneg_left h2s_le heps_nonneg).trans_lt hepsD
  have heps8c : eps * (8 * cCoeff) < 1 :=
    (mul_le_mul_of_nonneg_left h8c_le heps_nonneg).trans_lt hepsD
  have hmult_half :
      LSEKKTInverseMultiplierStatCoeff hB hnull *
          (eps * frobNormRect B) ≤ (1 : ℝ) / 2 := by
    have heq :
        LSEKKTInverseMultiplierStatCoeff hB hnull *
            (eps * frobNormRect B) = eps * mCoeff := by
      dsimp [mCoeff]
      ring
    rw [heq]
    nlinarith
  have hsol_linear :=
    theorem20_8KKTSolutionSelfCoeff_le_linear_of_eps_le_one
      hB hnull heps_nonneg heps_le_one
  have hsol_half :
      theorem20_8KKTSolutionSelfCoeff hB hnull eps ≤ (1 : ℝ) / 2 := by
    have hepss : eps * sCoeff < (1 : ℝ) / 2 := by nlinarith
    exact hsol_linear.trans (by simpa [sCoeff] using hepss.le)
  have heps_sq_le_eps : eps ^ 2 ≤ eps := by
    nlinarith [heps_nonneg, heps_le_one]
  have hquad : 4 * eps ^ 2 * cCoeff ≤ (1 : ℝ) / 2 := by
    have hscaled : 4 * eps ^ 2 * cCoeff ≤ 4 * eps * cCoeff := by
      calc
        4 * eps ^ 2 * cCoeff = eps ^ 2 * (4 * cCoeff) := by ring
        _ ≤ eps * (4 * cCoeff) :=
          mul_le_mul_of_nonneg_right heps_sq_le_eps (by positivity)
        _ = 4 * eps * cCoeff := by ring
    have hlin : 4 * eps * cCoeff < (1 : ℝ) / 2 := by nlinarith
    exact hscaled.trans hlin.le
  refine ⟨heps_le_one, hmult_half, hsol_half, ?_⟩
  simpa [cCoeff] using hquad
/-- On the explicit reciprocal neighborhood, the coupled KKT radius is
uniformly linear in `eps`, with a coefficient depending only on the source
problem. -/
theorem kktSourceResidualRatioCoupledBound_le_eps_mul_kktLocalLinearBoundCoeff
    {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hnull : LSENullIntersectionTrivial A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ} (heps_nonneg : 0 ≤ eps)
    (hsmall : eps < kktLocalSmallnessThreshold hB hnull) :
    theorem20_8KKTSourceResidualRatioCoupledBound hB hnull b x eps ≤
      eps * kktLocalLinearBoundCoeff hB hnull b x := by
  rcases kktLocal_smallness_conditions hB hnull heps_nonneg hsmall with
    ⟨heps_le_one, hmult_half, hsol_half, hquad⟩
  let residualScale : ℝ :=
    vecNorm2 (lsResidualHigham A b x) / vecNorm2 x
  let aNorm : ℝ := frobNormRect A
  let bNorm : ℝ := frobNormRect B
  let lambdaScale : ℝ :=
    LSEKKTInverseMultiplierDataCoeff hB hnull * residualScale
  let multiplierLinear : ℝ :=
    LSEKKTInverseMultiplierDataCoeff hB hnull *
        (2 * aNorm + residualScale) +
      LSEKKTInverseMultiplierStatCoeff hB hnull * aNorm *
        (4 * aNorm + 2 * residualScale) +
      2 * LSEKKTInverseMultiplierConstrCoeff hB hnull * bNorm
  let multiplierCap : ℝ := 2 * (lambdaScale + multiplierLinear)
  let solutionLinear : ℝ :=
    LSEKKTInverseSolutionDataCoeff hB hnull *
        (2 * aNorm + residualScale) +
      LSEKKTInverseSolutionStatCoeff hB hnull * bNorm * multiplierCap +
      LSEKKTInverseSolutionStatCoeff hB hnull * aNorm *
        (4 * aNorm + 2 * residualScale) +
      2 * LSEKKTInverseSolutionConstrCoeff hB hnull * bNorm
  let multiplierDenom : ℝ :=
    1 - LSEKKTInverseMultiplierStatCoeff hB hnull * (eps * bNorm)
  let solutionDenom : ℝ :=
    1 - theorem20_8KKTSolutionSelfCoeff hB hnull eps
  let multiplierBase : ℝ :=
    theorem20_8KKTMultiplierSmallGainScale hB hnull eps
      (aNorm + residualScale) bNorm 1 lambdaScale
  let multiplierSelf : ℝ :=
    theorem20_8KKTMultiplierSmallGainSelfCoeff hB hnull eps
  let solutionMuCoeff : ℝ :=
    LSEKKTInverseSolutionStatCoeff hB hnull * (eps * bNorm)
  let solutionBaseNumerator : ℝ :=
    LSEKKTInverseSolutionDataCoeff hB hnull *
        (eps * (aNorm + residualScale) + eps * aNorm) +
      solutionMuCoeff * multiplierBase +
      LSEKKTInverseSolutionStatCoeff hB hnull *
        ((eps * aNorm) *
          ((1 + eps) * (aNorm + residualScale) +
            (1 + eps) * aNorm)) +
      LSEKKTInverseSolutionConstrCoeff hB hnull *
        (eps * bNorm + eps * bNorm)
  let solutionBase : ℝ := solutionBaseNumerator / solutionDenom
  let solutionSelf : ℝ :=
    solutionMuCoeff * multiplierSelf / solutionDenom
  have hresidual : 0 ≤ residualScale := by
    dsimp [residualScale]
    exact div_nonneg (vecNorm2_nonneg _) hxnorm.le
  have ha : 0 ≤ aNorm := by
    dsimp [aNorm]
    exact frobNormRect_nonneg A
  have hbN : 0 ≤ bNorm := by
    dsimp [bNorm]
    exact frobNormRect_nonneg B
  have himData : 0 ≤ LSEKKTInverseMultiplierDataCoeff hB hnull :=
    LSEKKTInverseMultiplierDataCoeff_nonneg hB hnull
  have himStat : 0 ≤ LSEKKTInverseMultiplierStatCoeff hB hnull :=
    LSEKKTInverseMultiplierStatCoeff_nonneg hB hnull
  have himConstr : 0 ≤ LSEKKTInverseMultiplierConstrCoeff hB hnull :=
    LSEKKTInverseMultiplierConstrCoeff_nonneg hB hnull
  have hisData : 0 ≤ LSEKKTInverseSolutionDataCoeff hB hnull :=
    LSEKKTInverseSolutionDataCoeff_nonneg hB hnull
  have hisStat : 0 ≤ LSEKKTInverseSolutionStatCoeff hB hnull :=
    LSEKKTInverseSolutionStatCoeff_nonneg hB hnull
  have hisConstr : 0 ≤ LSEKKTInverseSolutionConstrCoeff hB hnull :=
    LSEKKTInverseSolutionConstrCoeff_nonneg hB hnull
  have hmultiplierLinear : 0 ≤ multiplierLinear := by
    dsimp [multiplierLinear]
    positivity
  have hlambda : 0 ≤ lambdaScale := by
    dsimp [lambdaScale]
    positivity
  have hmultiplierCap : 0 ≤ multiplierCap := by
    dsimp [multiplierCap]
    positivity
  have hsolutionLinear : 0 ≤ solutionLinear := by
    dsimp [solutionLinear]
    positivity
  have hbracket :
      (1 + eps) * (aNorm + residualScale) + (1 + eps) * aNorm ≤
        4 * aNorm + 2 * residualScale := by
    have hbase : 0 ≤ 2 * aNorm + residualScale := by positivity
    calc
      (1 + eps) * (aNorm + residualScale) + (1 + eps) * aNorm =
          (1 + eps) * (2 * aNorm + residualScale) := by ring
      _ ≤ 2 * (2 * aNorm + residualScale) :=
        mul_le_mul_of_nonneg_right (by linarith) hbase
      _ = 4 * aNorm + 2 * residualScale := by ring
  have hmultiplierDenom_half : (1 : ℝ) / 2 ≤ multiplierDenom := by
    dsimp [multiplierDenom, bNorm]
    linarith
  have hmultiplierDenom_pos : 0 < multiplierDenom := by linarith
  have hsolutionDenom_half : (1 : ℝ) / 2 ≤ solutionDenom := by
    dsimp [solutionDenom]
    linarith
  have hsolutionDenom_pos : 0 < solutionDenom := by linarith
  let multiplierNumerator : ℝ :=
    lambdaScale +
      LSEKKTInverseMultiplierDataCoeff hB hnull *
        (eps * (aNorm + residualScale) + (eps * aNorm) * 1) +
      LSEKKTInverseMultiplierStatCoeff hB hnull *
        ((eps * aNorm) *
          ((1 + eps) * (aNorm + residualScale) +
            ((1 + eps) * aNorm) * 1)) +
      LSEKKTInverseMultiplierConstrCoeff hB hnull *
        (eps * bNorm + (eps * bNorm) * 1)
  have hmultData :
      LSEKKTInverseMultiplierDataCoeff hB hnull *
          (eps * (aNorm + residualScale) + (eps * aNorm) * 1) =
        eps * (LSEKKTInverseMultiplierDataCoeff hB hnull *
          (2 * aNorm + residualScale)) := by ring
  have hmultStat :
      LSEKKTInverseMultiplierStatCoeff hB hnull *
          ((eps * aNorm) *
            ((1 + eps) * (aNorm + residualScale) +
              ((1 + eps) * aNorm) * 1)) ≤
        eps * (LSEKKTInverseMultiplierStatCoeff hB hnull * aNorm *
          (4 * aNorm + 2 * residualScale)) := by
    have hepsa : 0 ≤ eps * aNorm := mul_nonneg heps_nonneg ha
    calc
      LSEKKTInverseMultiplierStatCoeff hB hnull *
            ((eps * aNorm) *
              ((1 + eps) * (aNorm + residualScale) +
                ((1 + eps) * aNorm) * 1))
          ≤ LSEKKTInverseMultiplierStatCoeff hB hnull *
              ((eps * aNorm) * (4 * aNorm + 2 * residualScale)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by simpa using hbracket) hepsa)
              himStat
      _ = eps * (LSEKKTInverseMultiplierStatCoeff hB hnull * aNorm *
            (4 * aNorm + 2 * residualScale)) := by ring
  have hmultConstr :
      LSEKKTInverseMultiplierConstrCoeff hB hnull *
          (eps * bNorm + (eps * bNorm) * 1) =
        eps * (2 * LSEKKTInverseMultiplierConstrCoeff hB hnull * bNorm) := by
    ring
  have hmultNumerator_le :
      multiplierNumerator ≤ lambdaScale + eps * multiplierLinear := by
    dsimp [multiplierNumerator, multiplierLinear]
    rw [hmultData, hmultConstr]
    linarith
  have hmultNumerator_le_halfCap :
      multiplierNumerator ≤ multiplierCap / 2 := by
    have hepsLinear : eps * multiplierLinear ≤ multiplierLinear :=
      mul_le_of_le_one_left hmultiplierLinear heps_le_one
    dsimp [multiplierCap]
    nlinarith
  have hhalfCap_le : multiplierCap / 2 ≤ multiplierCap * multiplierDenom := by
    have := mul_le_mul_of_nonneg_left hmultiplierDenom_half hmultiplierCap
    nlinarith
  have hmultiplierBase_le : multiplierBase ≤ multiplierCap := by
    have hquot : multiplierNumerator / multiplierDenom ≤ multiplierCap :=
      (div_le_iff₀ hmultiplierDenom_pos).2
        (hmultNumerator_le_halfCap.trans hhalfCap_le)
    simpa [multiplierBase, multiplierNumerator, multiplierDenom,
      theorem20_8KKTMultiplierSmallGainScale] using hquot
  have hmultiplierSelf_le :
      multiplierSelf ≤
        2 * eps * theorem20_8KKTMultiplierSelfLinearCoeff hB hnull := by
    dsimp [multiplierSelf]
    exact
      theorem20_8KKTMultiplierSmallGainSelfCoeff_le_two_mul_linear_of_eps_le_one_of_gain_le_half
        hB hnull heps_nonneg heps_le_one hmult_half
  have hsolutionMu_nonneg : 0 ≤ solutionMuCoeff := by
    dsimp [solutionMuCoeff]
    positivity
  let cCoeff : ℝ :=
    LSEKKTInverseSolutionStatCoeff hB hnull * bNorm *
      theorem20_8KKTMultiplierSelfLinearCoeff hB hnull
  have hcCoeff : 0 ≤ cCoeff := by
    dsimp [cCoeff]
    exact mul_nonneg (mul_nonneg hisStat hbN)
      (theorem20_8KKTMultiplierSelfLinearCoeff_nonneg hB hnull)
  have hsolutionSelfNumerator_le :
      solutionMuCoeff * multiplierSelf ≤ 2 * eps ^ 2 * cCoeff := by
    calc
      solutionMuCoeff * multiplierSelf ≤
          solutionMuCoeff *
            (2 * eps * theorem20_8KKTMultiplierSelfLinearCoeff hB hnull) :=
        mul_le_mul_of_nonneg_left hmultiplierSelf_le hsolutionMu_nonneg
      _ = 2 * eps ^ 2 * cCoeff := by
        dsimp [solutionMuCoeff, cCoeff]
        ring
  have hsolutionSelf_le : solutionSelf ≤ 4 * eps ^ 2 * cCoeff := by
    have hscaled :
        2 * eps ^ 2 * cCoeff ≤
          (4 * eps ^ 2 * cCoeff) * solutionDenom := by
      have hnonneg : 0 ≤ 4 * eps ^ 2 * cCoeff := by positivity
      calc
        2 * eps ^ 2 * cCoeff =
            (4 * eps ^ 2 * cCoeff) * ((1 : ℝ) / 2) := by ring
        _ ≤ (4 * eps ^ 2 * cCoeff) * solutionDenom :=
          mul_le_mul_of_nonneg_left hsolutionDenom_half hnonneg
    have hquot :
        solutionMuCoeff * multiplierSelf / solutionDenom ≤
          4 * eps ^ 2 * cCoeff :=
      (div_le_iff₀ hsolutionDenom_pos).2
        (hsolutionSelfNumerator_le.trans hscaled)
    simpa only [solutionSelf] using hquot
  have hsolutionSelf_half : solutionSelf ≤ (1 : ℝ) / 2 := by
    have hquad' : 4 * eps ^ 2 * cCoeff ≤ (1 : ℝ) / 2 := by
      simpa [cCoeff, bNorm] using hquad
    exact hsolutionSelf_le.trans hquad'
  have hfinalDenom_pos : 0 < 1 - solutionSelf := by linarith
  have hsolData :
      LSEKKTInverseSolutionDataCoeff hB hnull *
          (eps * (aNorm + residualScale) + eps * aNorm) =
        eps * (LSEKKTInverseSolutionDataCoeff hB hnull *
          (2 * aNorm + residualScale)) := by ring
  have hsolMultiplier :
      solutionMuCoeff * multiplierBase ≤
        eps * (LSEKKTInverseSolutionStatCoeff hB hnull * bNorm *
          multiplierCap) := by
    calc
      solutionMuCoeff * multiplierBase ≤ solutionMuCoeff * multiplierCap :=
        mul_le_mul_of_nonneg_left hmultiplierBase_le hsolutionMu_nonneg
      _ = eps * (LSEKKTInverseSolutionStatCoeff hB hnull * bNorm *
            multiplierCap) := by
        dsimp [solutionMuCoeff]
        ring
  have hsolStat :
      LSEKKTInverseSolutionStatCoeff hB hnull *
          ((eps * aNorm) *
            ((1 + eps) * (aNorm + residualScale) +
              (1 + eps) * aNorm)) ≤
        eps * (LSEKKTInverseSolutionStatCoeff hB hnull * aNorm *
          (4 * aNorm + 2 * residualScale)) := by
    have hepsa : 0 ≤ eps * aNorm := mul_nonneg heps_nonneg ha
    calc
      LSEKKTInverseSolutionStatCoeff hB hnull *
            ((eps * aNorm) *
              ((1 + eps) * (aNorm + residualScale) +
                (1 + eps) * aNorm))
          ≤ LSEKKTInverseSolutionStatCoeff hB hnull *
              ((eps * aNorm) * (4 * aNorm + 2 * residualScale)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hbracket hepsa) hisStat
      _ = eps * (LSEKKTInverseSolutionStatCoeff hB hnull * aNorm *
            (4 * aNorm + 2 * residualScale)) := by ring
  have hsolConstr :
      LSEKKTInverseSolutionConstrCoeff hB hnull *
          (eps * bNorm + eps * bNorm) =
        eps * (2 * LSEKKTInverseSolutionConstrCoeff hB hnull * bNorm) := by
    ring
  have hsolutionBaseNumerator_le :
      solutionBaseNumerator ≤ eps * solutionLinear := by
    dsimp [solutionBaseNumerator, solutionLinear]
    rw [hsolData, hsolConstr]
    linarith
  have hsolutionBase_le : solutionBase ≤ 2 * eps * solutionLinear := by
    have hscaled :
        eps * solutionLinear ≤
          (2 * eps * solutionLinear) * solutionDenom := by
      have hnonneg : 0 ≤ 2 * eps * solutionLinear :=
        mul_nonneg (mul_nonneg (by norm_num) heps_nonneg) hsolutionLinear
      calc
        eps * solutionLinear =
            (2 * eps * solutionLinear) * ((1 : ℝ) / 2) := by ring
        _ ≤ (2 * eps * solutionLinear) * solutionDenom :=
          mul_le_mul_of_nonneg_left hsolutionDenom_half hnonneg
    dsimp [solutionBase]
    exact (div_le_iff₀ hsolutionDenom_pos).2
      (hsolutionBaseNumerator_le.trans hscaled)
  have hfinal : solutionBase / (1 - solutionSelf) ≤
      4 * eps * solutionLinear := by
    have hscaled :
        2 * eps * solutionLinear ≤
          (4 * eps * solutionLinear) * (1 - solutionSelf) := by
      have hnonneg : 0 ≤ 4 * eps * solutionLinear :=
        mul_nonneg (mul_nonneg (by norm_num) heps_nonneg) hsolutionLinear
      have hhalf : (1 : ℝ) / 2 ≤ 1 - solutionSelf := by linarith
      calc
        2 * eps * solutionLinear =
            (4 * eps * solutionLinear) * ((1 : ℝ) / 2) := by ring
        _ ≤ (4 * eps * solutionLinear) * (1 - solutionSelf) :=
          mul_le_mul_of_nonneg_left hhalf hnonneg
    exact (div_le_iff₀ hfinalDenom_pos).2 (hsolutionBase_le.trans hscaled)
  have hbound_eq :
      theorem20_8KKTSourceResidualRatioCoupledBound hB hnull b x eps =
        solutionBase / (1 - solutionSelf) := by
    rfl
  have hcoeff_eq :
      kktLocalLinearBoundCoeff hB hnull b x = 4 * solutionLinear := by
    rfl
  rw [hbound_eq]
  rw [hcoeff_eq]
  convert hfinal using 1
  ring
/-- The genuinely higher-order stationarity remainder in the exact KKT bottom
row.  It is a perturbation norm times the residual and multiplier differences,
so it has the required quadratic structure once the local KKT difference
bounds are inserted. -/
noncomputable def kktStationarityRemainderRadius {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ) (eps : ℝ)
    (dr : Fin m → ℝ) (dlambda : Fin p → ℝ) : ℝ :=
  (complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
      ((eps * frobNormRect B) * vecNorm2 dlambda +
        (eps * frobNormRect A) * vecNorm2 dr)) /
    vecNorm2 x
/-- A reusable scalar handoff: first-order residual and multiplier differences
turn the KKT stationarity remainder into an explicit `eps²` term. -/
theorem kktStationarityRemainderRadius_le_eps_sq_mul
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (x : Fin n → ℝ)
    (dr : Fin m → ℝ) (dlambda : Fin p → ℝ)
    {eps drCoeff dlambdaCoeff : ℝ}
    (heps_nonneg : 0 ≤ eps) (hxnorm : 0 < vecNorm2 x)
    (hdr : vecNorm2 dr ≤ eps * drCoeff * vecNorm2 x)
    (hdlambda : vecNorm2 dlambda ≤ eps * dlambdaCoeff * vecNorm2 x) :
    kktStationarityRemainderRadius A B APplus x eps dr dlambda ≤
      eps ^ 2 *
        (complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
          (frobNormRect B * dlambdaCoeff + frobNormRect A * drCoeff)) := by
  have hepsB : 0 ≤ eps * frobNormRect B :=
    mul_nonneg heps_nonneg (frobNormRect_nonneg B)
  have hepsA : 0 ≤ eps * frobNormRect A :=
    mul_nonneg heps_nonneg (frobNormRect_nonneg A)
  have hdlScaled := mul_le_mul_of_nonneg_left hdlambda hepsB
  have hdrScaled := mul_le_mul_of_nonneg_left hdr hepsA
  have hopSq :
      0 ≤ complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 := sq_nonneg _
  have hsum :
      complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
          ((eps * frobNormRect B) * vecNorm2 dlambda +
            (eps * frobNormRect A) * vecNorm2 dr) ≤
        (eps ^ 2 *
          (complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
            (frobNormRect B * dlambdaCoeff +
              frobNormRect A * drCoeff))) * vecNorm2 x := by
    have hinside := add_le_add hdlScaled hdrScaled
    have hscaled := mul_le_mul_of_nonneg_left hinside hopSq
    calc
      complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
          ((eps * frobNormRect B) * vecNorm2 dlambda +
            (eps * frobNormRect A) * vecNorm2 dr) ≤
          complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
            ((eps * frobNormRect B) *
                (eps * dlambdaCoeff * vecNorm2 x) +
              (eps * frobNormRect A) *
                (eps * drCoeff * vecNorm2 x)) := hscaled
      _ = (eps ^ 2 *
            (complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
              (frobNormRect B * dlambdaCoeff +
                frobNormRect A * drCoeff))) * vecNorm2 x := by ring
  dsimp [kktStationarityRemainderRadius]
  exact (div_le_iff₀ hxnorm).2 hsum

end Theorem20_8

end NumStability
