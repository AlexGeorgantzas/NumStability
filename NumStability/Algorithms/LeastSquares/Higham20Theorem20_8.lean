import NumStability.Algorithms.LeastSquares.LSE

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

namespace Theorem20_8

/-!
# Higham, Chapter 20, Theorem 20.8

This module closes the rank/KKT perturbation route to the printed first-order
bound.  The exact Cox--Higham augmented-KKT bottom row is proved directly and
specialized to source and perturbed LSE minimizers.  Its source stationarity
part is bounded sharply by Higham's residual amplifier, while the remaining
stationarity term is a product of `(ΔA,ΔB)` with first-order residual and
multiplier differences.

`source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold` is the public
source-only endpoint.  Its single reciprocal threshold derives both perturbed
rank conditions, discharges the coupled KKT gains, and turns both remainder
terms into one explicit `eps²` coefficient.  It uses no residual-gap,
same-residual, common-factor, norm-order, or conclusion-shaped premise.

The older `directDataCorrectionRadius` is retained for compatibility.  Its
reduced-data summand has the opposite sign from Cox--Higham (4.7).  New closure
theorems therefore use `highamDirectDataCorrectionRadius`, with the source sign
`(AP)⁺(Δb-ΔA y)` required by equation (20.25).
-/

/-- The source null-intersection certificate supplied by stacked full column
rank. -/
def sourceNullIntersection {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hStack : LSEStackedFullColumnRank A B) :
    LSENullIntersectionTrivial A B :=
  (LSENullIntersectionTrivial.iff_lseStackedFullColumnRank A B).2 hStack

/-- The rank-tolerant source `BA^+` expression used in Theorem 20.8. -/
noncomputable def sourceBAplus {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hB : LSEFullRowRank B) (APplus : Fin n → Fin m → ℝ) :
    Fin n → Fin p → ℝ :=
  theorem20_8BAplus A B hB.rightInverse APplus

/-- The source data coefficient multiplying the KKT radius in the explicit
remainder. -/
noncomputable def dataCoeff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hB : LSEFullRowRank B) (APplus : Fin n → Fin m → ℝ) : ℝ :=
  complexMatrixOp2 (realRectToCMatrix (sourceBAplus A B hB APplus)) *
      frobNormRect B +
    complexMatrixOp2 (realRectToCMatrix APplus) * frobNormRect A

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

/-- The exact remainder returned by the source-facing direct/data estimate.

This is an explicit finite-`eps` expression.  The theorem
`explicitRemainder_le_eps_sq_mul` below supplies a genuine local quadratic
majorant under `kktLocalSmallnessThreshold`. -/
noncomputable def explicitRemainder {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (eps : ℝ)
    (APplus : Fin n → Fin m → ℝ) : ℝ :=
  eps *
    theorem20_8KKTSourceResidualRatioCoupledBound hB
      (sourceNullIntersection hStack) b x eps *
    dataCoeff A B hB APplus

theorem dataCoeff_nonneg {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hB : LSEFullRowRank B) (APplus : Fin n → Fin m → ℝ) :
    0 ≤ dataCoeff A B hB APplus := by
  dsimp [dataCoeff]
  exact add_nonneg
    (mul_nonneg (complexMatrixOp2_nonneg _) (frobNormRect_nonneg B))
    (mul_nonneg (complexMatrixOp2_nonneg _) (frobNormRect_nonneg A))

/-- The explicit correction-radius remainder is genuinely quadratic on the
source-only reciprocal neighborhood.  Its coefficient is independent of
`eps` (but, as expected, depends on the source problem and the chosen source
Moore--Penrose candidate). -/
theorem explicitRemainder_le_eps_sq_mul {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ} (heps_nonneg : 0 ≤ eps)
    (hsmall :
      eps < kktLocalSmallnessThreshold hB (sourceNullIntersection hStack)) :
    explicitRemainder hB hStack b x eps APplus ≤
      eps ^ 2 *
        (kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x *
          dataCoeff A B hB APplus) := by
  have hkkt :=
    kktSourceResidualRatioCoupledBound_le_eps_mul_kktLocalLinearBoundCoeff
      hB (sourceNullIntersection hStack) b x hxnorm heps_nonneg hsmall
  have hdata : 0 ≤ dataCoeff A B hB APplus :=
    dataCoeff_nonneg A B hB APplus
  have hscaled :
      eps *
          theorem20_8KKTSourceResidualRatioCoupledBound hB
            (sourceNullIntersection hStack) b x eps *
          dataCoeff A B hB APplus ≤
        eps *
          (eps *
            kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x) *
          dataCoeff A B hB APplus :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hkkt heps_nonneg) hdata
  dsimp [explicitRemainder]
  calc
    eps *
          theorem20_8KKTSourceResidualRatioCoupledBound hB
            (sourceNullIntersection hStack) b x eps *
          dataCoeff A B hB APplus
        ≤ eps *
            (eps *
              kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x) *
            dataCoeff A B hB APplus := hscaled
    _ = eps ^ 2 *
          (kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x *
            dataCoeff A B hB APplus) := by ring

/-- The source normal-equation pseudoinverse block
`((AP)ᵀ(AP))⁺ = (AP)⁺((AP)⁺)ᵀ` occurring in the bottom row of the
Cox--Higham augmented KKT inverse. -/
noncomputable def sourceNormalGramPlus {m n : ℕ}
    (APplus : Fin n → Fin m → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul APplus (finiteTranspose APplus)

/-- Exact bottom-row identity for the source augmented KKT inverse.

This is the finite-dimensional algebra behind Cox--Higham equation (4.7),
whose first-order specialization is Higham's equation (20.25).  Crucially,
the identity uses only the source right inverse, the Moore--Penrose equations
for `(AP)⁺`, its source-constraint range certificate, and the exact KKT
system.  It does not assume a residual gap, a common factorization, a norm
ordering, or any conclusion-shaped estimate. -/
theorem kkt_solution_eq_source_bottom_row
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (c : Fin p → ℝ)
    (dr : Fin m → ℝ) (dx : Fin n → ℝ) (dlambda : Fin p → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B Bplus) =
        theorem20_8Projection B Bplus)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hAPrange_symmetric :
      IsSymmetricFiniteMatrix
        (rectMatMul (theorem20_8AP A B Bplus) APplus))
    (hAPreproduces :
      rectMatMul
          (rectMatMul APplus (theorem20_8AP A B Bplus)) APplus =
        APplus)
    (hsys : LSEKKTSystem A B f g c dr dx dlambda) :
    dx = fun j : Fin n =>
      rectMatMulVec (theorem20_8BAplus A B Bplus APplus) c j +
        rectMatMulVec APplus f j -
        rectMatMulVec (sourceNormalGramPlus APplus) g j := by
  let P : Fin n → Fin n → ℝ := theorem20_8Projection B Bplus
  let AP : Fin m → Fin n → ℝ := theorem20_8AP A B Bplus
  let BAplus : Fin n → Fin p → ℝ :=
    theorem20_8BAplus A B Bplus APplus
  let Gplus : Fin n → Fin n → ℝ := sourceNormalGramPlus APplus
  rcases hsys with ⟨htop, hstat, hconstr⟩
  have hPdx :
      rectMatMulVec P dx =
        fun j : Fin n => dx j - rectMatMulVec Bplus c j := by
    simpa [P] using
      theorem20_8Projection_apply_of_constraint B Bplus dx c
        (funext hconstr)
  have hPdx_AP :
      rectMatMulVec P dx =
        rectMatMulVec APplus (rectMatMulVec AP dx) := by
    calc
      rectMatMulVec P dx =
          rectMatMulVec (rectMatMul APplus AP) dx := by
            rw [hAPleft]
      _ = rectMatMulVec APplus (rectMatMulVec AP dx) := by
            exact rectMatMulVec_rectMatMul APplus AP dx
  have hAPdx :
      rectMatMulVec AP dx =
        fun i : Fin m =>
          (f i - dr i) -
            rectMatMulVec A (rectMatMulVec Bplus c) i := by
    calc
      rectMatMulVec AP dx = rectMatMulVec A (rectMatMulVec P dx) := by
        simp only [AP, P, theorem20_8AP, rectMatMulVec_rectMatMul]
      _ = rectMatMulVec A
          (fun j : Fin n => dx j - rectMatMulVec Bplus c j) := by
        rw [hPdx]
      _ = fun i : Fin m =>
          rectMatMulVec A dx i -
            rectMatMulVec A (rectMatMulVec Bplus c) i := by
        exact rectMatMulVec_sub A dx (rectMatMulVec Bplus c)
      _ = fun i : Fin m =>
          (f i - dr i) -
            rectMatMulVec A (rectMatMulVec Bplus c) i := by
        funext i
        have hi := htop i
        linarith
  have hBA :
      rectMatMulVec BAplus c =
        fun j : Fin n =>
          rectMatMulVec Bplus c j -
            rectMatMulVec APplus
              (rectMatMulVec A (rectMatMulVec Bplus c)) j := by
    simpa [BAplus] using
      theorem20_8BAplus_apply A B Bplus APplus c
  have hdx_pre :
      dx = fun j : Fin n =>
        rectMatMulVec BAplus c j + rectMatMulVec APplus f j -
          rectMatMulVec APplus dr j := by
    ext j
    have hPj := congrFun hPdx j
    have hPAPj := congrFun hPdx_AP j
    have hAPdx' := congrArg (rectMatMulVec APplus) hAPdx
    have hAPj := congrFun hAPdx' j
    have hBAj := congrFun hBA j
    rw [rectMatMulVec_sub] at hAPj
    dsimp at hAPj
    have hfdr :
        rectMatMulVec APplus (fun i : Fin m => f i - dr i) =
          fun k : Fin n =>
            rectMatMulVec APplus f k - rectMatMulVec APplus dr k :=
      rectMatMulVec_sub APplus f dr
    rw [hfdr] at hAPj
    linarith
  have hPAPplus : rectMatMul P APplus = APplus := by
    simpa [P] using
      theorem20_8_APplus_projection_range_of_constraint_annihilates
        B Bplus APplus hBAPplus
  have hAAPplus : rectMatMul A APplus = rectMatMul AP APplus := by
    calc
      rectMatMul A APplus = rectMatMul A (rectMatMul P APplus) := by
        rw [hPAPplus]
      _ = rectMatMul (rectMatMul A P) APplus := by
        rw [rectMatMul_assoc]
      _ = rectMatMul AP APplus := by rfl
  have htranspose_stat :
      rectMatMulVec (finiteTranspose APplus) g =
        rectMatMulVec (rectMatMul AP APplus) dr := by
    ext i
    simp only [rectMatMulVec, finiteTranspose]
    calc
      ∑ j : Fin n, APplus j i * g j =
          ∑ j : Fin n, APplus j i *
            ((∑ a : Fin m, A a j * dr a) -
              (∑ r : Fin p, B r j * dlambda r)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← hstat j]
      _ =
          (∑ a : Fin m, (∑ j : Fin n, A a j * APplus j i) * dr a) -
            (∑ r : Fin p, (∑ j : Fin n, B r j * APplus j i) *
              dlambda r) := by
        calc
          ∑ j : Fin n, APplus j i *
              ((∑ a : Fin m, A a j * dr a) -
                (∑ r : Fin p, B r j * dlambda r)) =
              (∑ j : Fin n,
                APplus j i * (∑ a : Fin m, A a j * dr a)) -
                (∑ j : Fin n,
                  APplus j i * (∑ r : Fin p, B r j * dlambda r)) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            ring
          _ =
              (∑ a : Fin m, (∑ j : Fin n, A a j * APplus j i) * dr a) -
                (∑ r : Fin p, (∑ j : Fin n, B r j * APplus j i) *
                  dlambda r) := by
            congr 1
            · calc
                ∑ j : Fin n,
                    APplus j i * (∑ a : Fin m, A a j * dr a) =
                    ∑ j : Fin n, ∑ a : Fin m,
                      APplus j i * (A a j * dr a) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [Finset.mul_sum]
                _ = ∑ a : Fin m, ∑ j : Fin n,
                    APplus j i * (A a j * dr a) := by
                  rw [Finset.sum_comm]
                _ = ∑ a : Fin m,
                    (∑ j : Fin n, A a j * APplus j i) * dr a := by
                  apply Finset.sum_congr rfl
                  intro a _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
            · calc
                ∑ j : Fin n,
                    APplus j i * (∑ r : Fin p, B r j * dlambda r) =
                    ∑ j : Fin n, ∑ r : Fin p,
                      APplus j i * (B r j * dlambda r) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [Finset.mul_sum]
                _ = ∑ r : Fin p, ∑ j : Fin n,
                    APplus j i * (B r j * dlambda r) := by
                  rw [Finset.sum_comm]
                _ = ∑ r : Fin p,
                    (∑ j : Fin n, B r j * APplus j i) * dlambda r := by
                  apply Finset.sum_congr rfl
                  intro r _
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
      _ = ∑ a : Fin m, (∑ j : Fin n, A a j * APplus j i) * dr a := by
        have hz :
            ∀ r : Fin p, (∑ j : Fin n, B r j * APplus j i) = 0 := by
          intro r
          have hri := congrFun (congrFun hBAPplus r) i
          simpa [rectMatMul] using hri
        simp [hz]
      _ = ∑ a : Fin m, (rectMatMul AP APplus) i a * dr a := by
        apply Finset.sum_congr rfl
        intro a _
        have hAi :
            (∑ j : Fin n, A a j * APplus j i) =
              (rectMatMul AP APplus) a i := by
          have := congrFun (congrFun hAAPplus a) i
          simpa [rectMatMul] using this
        rw [hAi]
        have hsym := hAPrange_symmetric a i
        rw [hsym]
      _ = ∑ a : Fin m, (rectMatMul AP APplus) i a * dr a := rfl
  have hGdr :
      rectMatMulVec Gplus g = rectMatMulVec APplus dr := by
    calc
      rectMatMulVec Gplus g =
          rectMatMulVec APplus
            (rectMatMulVec (finiteTranspose APplus) g) := by
        simp only [Gplus, sourceNormalGramPlus, rectMatMulVec_rectMatMul]
      _ = rectMatMulVec APplus
          (rectMatMulVec (rectMatMul AP APplus) dr) := by
        rw [htranspose_stat]
      _ = rectMatMulVec (rectMatMul APplus (rectMatMul AP APplus)) dr := by
        exact
          (rectMatMulVec_rectMatMul APplus (rectMatMul AP APplus) dr).symm
      _ = rectMatMulVec
          (rectMatMul (rectMatMul APplus AP) APplus) dr := by
        rw [rectMatMul_assoc]
      _ = rectMatMulVec APplus dr := by
        rw [hAPreproduces]
  rw [hdx_pre]
  funext j
  have hGj := congrFun hGdr j
  dsimp [Gplus] at hGj ⊢
  linarith

/-- Source-to-perturbed LSE specialization of the exact KKT bottom row.

The returned source and perturbed multipliers are the ones selected by the
normal equations, and the accompanying KKT system exposes the residual and
multiplier differences needed to bound the genuinely second-order remainder.
-/
theorem exists_lagrange_solution_difference_eq_source_bottom_row
    {m n p : ℕ}
    {A ΔA : Fin m → Fin n → ℝ} {b Δb : Fin m → ℝ}
    {B ΔB : Fin p → Fin n → ℝ} {d Δd : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + ΔB i j))
    (APplus : Fin n → Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hAPrange_symmetric :
      IsSymmetricFiniteMatrix
        (rectMatMul (theorem20_8AP A B hB.rightInverse) APplus))
    (hAPreproduces :
      rectMatMul
          (rectMatMul APplus (theorem20_8AP A B hB.rightInverse)) APplus =
        APplus) :
    ∃ lambda mu : Fin p → ℝ,
      (∀ j : Fin n,
        ∑ i : Fin m, A i j * lsResidualHigham A b x i =
          ∑ r : Fin p, B r j * lambda r) ∧
      LSEKKTSystem A B
        (fun i => Δb i - rectMatMulVec ΔA y i)
        (fun j =>
          (∑ r : Fin p, ΔB r j * mu r) -
            (∑ i : Fin m,
              ΔA i j *
                lsResidualHigham (fun i j => A i j + ΔA i j)
                  (fun i => b i + Δb i) y i))
        (fun r => Δd r - rectMatMulVec ΔB y r)
        (fun i =>
          lsResidualHigham (fun i j => A i j + ΔA i j)
              (fun i => b i + Δb i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun r => mu r - lambda r) ∧
      (fun j => y j - x j) = fun j : Fin n =>
        rectMatMulVec
            (theorem20_8BAplus A B hB.rightInverse APplus)
            (fun r => Δd r - rectMatMulVec ΔB y r) j +
          rectMatMulVec APplus
            (fun i => Δb i - rectMatMulVec ΔA y i) j -
          rectMatMulVec (sourceNormalGramPlus APplus)
            (fun k =>
              (∑ r : Fin p, ΔB r k * mu r) -
                (∑ i : Fin m,
                  ΔA i k *
                    lsResidualHigham (fun i j => A i j + ΔA i j)
                      (fun i => b i + Δb i) y i)) j := by
  rcases
      hx.exists_lagrange_kkt_difference_source_system_of_fullRowRank_sourceNormal
        hy hB hBpert with
    ⟨lambda, mu, hnormal, hsys⟩
  refine ⟨lambda, mu, hnormal, hsys, ?_⟩
  exact
    kkt_solution_eq_source_bottom_row A B hB.rightInverse APplus
      (fun i => Δb i - rectMatMulVec ΔA y i)
      (fun j =>
        (∑ r : Fin p, ΔB r j * mu r) -
          (∑ i : Fin m,
            ΔA i j *
              lsResidualHigham (fun i j => A i j + ΔA i j)
                (fun i => b i + Δb i) y i))
      (fun r => Δd r - rectMatMulVec ΔB y r)
      (fun i =>
        lsResidualHigham (fun i j => A i j + ΔA i j)
            (fun i => b i + Δb i) y i -
          lsResidualHigham A b x i)
      (fun j => y j - x j) (fun r => mu r - lambda r)
      hAPleft hBAPplus hAPrange_symmetric hAPreproduces hsys

/-- The direct correction with the sign appearing in Cox--Higham (4.7) and
Higham (20.25): `(AP)⁺(Δb - ΔA y)`.  This is kept separate from the older
legacy radius below, whose reduced-data summand has the opposite sign. -/
noncomputable def highamDirectDataCorrectionRadius {m n p : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (B ΔB : Fin p → Fin n → ℝ) (Δd : Fin p → ℝ)
    (hB : LSEFullRowRank B) (x y : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (eps : ℝ) : ℝ :=
  (vecNorm2
        (fun j : Fin n =>
          rectMatMulVec (sourceBAplus A B hB APplus)
              (fun i : Fin p => Δd i - rectMatMulVec ΔB y i) j +
            rectMatMulVec APplus
              (fun i : Fin m => Δb i - rectMatMulVec ΔA y i) j) +
      eps * theorem20_8ResidualAmplifier A B APplus
        (sourceBAplus A B hB APplus) *
        (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
    vecNorm2 x

/-- Changing the evaluation point from `x` to `y` in the correctly signed
Higham direct correction costs the same operator-norm remainder as in the
legacy sign convention. -/
theorem higham_direct_data_correction_difference_le
    {m n p : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (B ΔB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Δd : Fin p → ℝ)
    (y x : Fin n → ℝ) {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps) :
    vecNorm2
        (fun j : Fin n =>
          (rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
                (fun i : Fin p => Δd i - rectMatMulVec ΔB y i) j +
              rectMatMulVec APplus
                (fun i : Fin m => Δb i - rectMatMulVec ΔA y i) j) -
            (rectMatMulVec (theorem20_8BAplus A B Bplus APplus)
                (fun i : Fin p => Δd i - rectMatMulVec ΔB x i) j +
              rectMatMulVec APplus
                (fun i : Fin m => Δb i - rectMatMulVec ΔA x i) j)) ≤
      complexMatrixOp2
          (realRectToCMatrix (theorem20_8BAplus A B Bplus APplus)) *
        ((eps * frobNormRect B) * vecNorm2 (fun j : Fin n => y j - x j)) +
      complexMatrixOp2 (realRectToCMatrix APplus) *
        ((eps * frobNormRect A) * vecNorm2 (fun j : Fin n => y j - x j)) := by
  let BAplus : Fin n → Fin p → ℝ :=
    theorem20_8BAplus A B Bplus APplus
  let directY : Fin n → ℝ :=
    rectMatMulVec BAplus
      (fun i : Fin p => Δd i - rectMatMulVec ΔB y i)
  let directX : Fin n → ℝ :=
    rectMatMulVec BAplus
      (fun i : Fin p => Δd i - rectMatMulVec ΔB x i)
  let dataY : Fin n → ℝ :=
    rectMatMulVec APplus
      (fun i : Fin m => Δb i - rectMatMulVec ΔA y i)
  let dataX : Fin n → ℝ :=
    rectMatMulVec APplus
      (fun i : Fin m => Δb i - rectMatMulVec ΔA x i)
  have hdirect :
      vecNorm2 (fun j : Fin n => directY j - directX j) ≤
        complexMatrixOp2 (realRectToCMatrix BAplus) *
          ((eps * frobNormRect B) * vecNorm2 (fun j : Fin n => y j - x j)) := by
    dsimp [directY, directX, BAplus]
    exact
      theorem20_8_vecNorm2_BAplus_constraint_defect_difference_le_of_maxRelativePerturbation
        A ΔA b Δb B ΔB Bplus APplus d Δd y x
        hApos hbpos hBpos hdpos hmax
  have hdata :
      vecNorm2 (fun j : Fin n => dataY j - dataX j) ≤
        complexMatrixOp2 (realRectToCMatrix APplus) *
          ((eps * frobNormRect A) * vecNorm2 (fun j : Fin n => y j - x j)) := by
    have hold :=
      theorem20_8_vecNorm2_APplus_data_forcing_difference_le_of_maxRelativePerturbation
        A ΔA b Δb B ΔB d Δd APplus y x
        hApos hbpos hBpos hdpos hmax
    have hneg :
        (fun j : Fin n => dataY j - dataX j) =
          fun j : Fin n =>
            -(rectMatMulVec APplus
                (fun i : Fin m => rectMatMulVec ΔA y i - Δb i) j -
              rectMatMulVec APplus
                (fun i : Fin m => rectMatMulVec ΔA x i - Δb i) j) := by
      funext j
      dsimp [dataY, dataX]
      have hyneg :
          (fun i : Fin m => Δb i - rectMatMulVec ΔA y i) =
            fun i : Fin m => -(rectMatMulVec ΔA y i - Δb i) := by
        funext i
        ring
      have hxneg :
          (fun i : Fin m => Δb i - rectMatMulVec ΔA x i) =
            fun i : Fin m => -(rectMatMulVec ΔA x i - Δb i) := by
        funext i
        ring
      rw [hyneg, hxneg]
      simp only [rectMatMulVec, mul_neg, Finset.sum_neg_distrib]
      ring
    rw [hneg, vecNorm2_neg]
    exact hold
  have htri :=
    vecNorm2_add_le
      (fun j : Fin n => directY j - directX j)
      (fun j : Fin n => dataY j - dataX j)
  calc
    vecNorm2
        (fun j : Fin n =>
          (rectMatMulVec BAplus
                (fun i : Fin p => Δd i - rectMatMulVec ΔB y i) j +
              rectMatMulVec APplus
                (fun i : Fin m => Δb i - rectMatMulVec ΔA y i) j) -
            (rectMatMulVec BAplus
                (fun i : Fin p => Δd i - rectMatMulVec ΔB x i) j +
              rectMatMulVec APplus
                (fun i : Fin m => Δb i - rectMatMulVec ΔA x i) j)) =
        vecNorm2
          (fun j : Fin n =>
            (directY j - directX j) + (dataY j - dataX j)) := by
              congr 1
              funext j
              dsimp [directY, directX, dataY, dataX]
              ring
    _ ≤ vecNorm2 (fun j : Fin n => directY j - directX j) +
          vecNorm2 (fun j : Fin n => dataY j - dataX j) := htri
    _ ≤ complexMatrixOp2 (realRectToCMatrix BAplus) *
          ((eps * frobNormRect B) * vecNorm2 (fun j : Fin n => y j - x j)) +
        complexMatrixOp2 (realRectToCMatrix APplus) *
          ((eps * frobNormRect A) * vecNorm2 (fun j : Fin n => y j - x j)) :=
            add_le_add hdirect hdata

/-- The correctly signed direct radius has Higham's displayed first-order
coefficient, plus the quadratic-shaped evaluation-point correction supplied
by any relative solution radius. -/
theorem highamDirectDataCorrectionRadius_le_firstOrderRHS_plus_eps_radius
    {m n p : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (B ΔB : Fin p → Fin n → ℝ) (hB : LSEFullRowRank B)
    (APplus : Fin n → Fin m → ℝ) (d Δd : Fin p → ℝ)
    (y x : Fin n → ℝ) {eps relativeRadius : ℝ}
    (heps_nonneg : 0 ≤ eps)
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hxpos : 0 < vecNorm2 x)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps)
    (hyx :
      vecNorm2 (fun j : Fin n => y j - x j) / vecNorm2 x ≤
        relativeRadius) :
    highamDirectDataCorrectionRadius A ΔA b Δb B ΔB Δd hB x y APplus eps ≤
      eps * theorem20_8FirstOrderRHS A b B d x
        (lsResidualHigham A b x) APplus (sourceBAplus A B hB APplus) +
      eps * relativeRadius * dataCoeff A B hB APplus := by
  let BAplus : Fin n → Fin p → ℝ := sourceBAplus A B hB APplus
  let directY : Fin n → ℝ := fun j =>
    rectMatMulVec BAplus
        (fun i : Fin p => Δd i - rectMatMulVec ΔB y i) j +
      rectMatMulVec APplus
        (fun i : Fin m => Δb i - rectMatMulVec ΔA y i) j
  let directX : Fin n → ℝ := fun j =>
    rectMatMulVec BAplus
        (fun i : Fin p => Δd i - rectMatMulVec ΔB x i) j +
      rectMatMulVec APplus
        (fun i : Fin m => Δb i - rectMatMulVec ΔA x i) j
  let residualTerm : ℝ :=
    eps * theorem20_8ResidualAmplifier A B APplus BAplus *
      (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)
  have hsource :
      (vecNorm2 directX + residualTerm) / vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus BAplus := by
    simpa [directX, residualTerm, BAplus, sourceBAplus] using
      theorem20_8_direct_higham_data_y_correction_residual_relative_le_firstOrderRHS_of_maxRelativePerturbation
        A ΔA b Δb B ΔB hB.rightInverse APplus d Δd x x
        (lsResidualHigham A b x) heps_nonneg hApos hbpos hBpos hdpos
        hxpos (le_refl (vecNorm2 x)) hmax
  have hdiff :=
    higham_direct_data_correction_difference_le
      A ΔA b Δb B ΔB hB.rightInverse APplus d Δd y x
      hApos hbpos hBpos hdpos hmax
  have hdiffRel :
      vecNorm2 (fun j : Fin n => directY j - directX j) / vecNorm2 x ≤
        eps * relativeRadius * dataCoeff A B hB APplus := by
    have hnorm_nonneg : 0 ≤ vecNorm2 x := hxpos.le
    have hBAop :
        0 ≤ complexMatrixOp2 (realRectToCMatrix BAplus) :=
      complexMatrixOp2_nonneg _
    have hAPop :
        0 ≤ complexMatrixOp2 (realRectToCMatrix APplus) :=
      complexMatrixOp2_nonneg _
    have hepsB : 0 ≤ eps * frobNormRect B :=
      mul_nonneg heps_nonneg (frobNormRect_nonneg B)
    have hepsA : 0 ≤ eps * frobNormRect A :=
      mul_nonneg heps_nonneg (frobNormRect_nonneg A)
    have hrelmul :
        vecNorm2 (fun j : Fin n => y j - x j) ≤
          relativeRadius * vecNorm2 x :=
      (div_le_iff₀ hxpos).mp hyx
    have hscaled :
        complexMatrixOp2 (realRectToCMatrix BAplus) *
              ((eps * frobNormRect B) *
                vecNorm2 (fun j : Fin n => y j - x j)) +
            complexMatrixOp2 (realRectToCMatrix APplus) *
              ((eps * frobNormRect A) *
                vecNorm2 (fun j : Fin n => y j - x j)) ≤
          (eps * relativeRadius * dataCoeff A B hB APplus) * vecNorm2 x := by
      have hBscale := mul_le_mul_of_nonneg_left hrelmul hepsB
      have hAscale := mul_le_mul_of_nonneg_left hrelmul hepsA
      have hBscale' := mul_le_mul_of_nonneg_left hBscale hBAop
      have hAscale' := mul_le_mul_of_nonneg_left hAscale hAPop
      dsimp [dataCoeff, BAplus, sourceBAplus] at hBscale' hAscale' ⊢
      nlinarith
    have hdiff' :
        vecNorm2 (fun j : Fin n => directY j - directX j) ≤
          (eps * relativeRadius * dataCoeff A B hB APplus) * vecNorm2 x := by
      have hdiffBase :
          vecNorm2 (fun j : Fin n => directY j - directX j) ≤
            complexMatrixOp2 (realRectToCMatrix BAplus) *
                ((eps * frobNormRect B) *
                  vecNorm2 (fun j : Fin n => y j - x j)) +
              complexMatrixOp2 (realRectToCMatrix APplus) *
                ((eps * frobNormRect A) *
                  vecNorm2 (fun j : Fin n => y j - x j)) := by
        simpa [directY, directX, BAplus, sourceBAplus] using hdiff
      exact hdiffBase.trans hscaled
    exact (div_le_iff₀ hxpos).2 hdiff'
  have htri : vecNorm2 directY ≤ vecNorm2 directX +
      vecNorm2 (fun j : Fin n => directY j - directX j) := by
    have heq : directY = fun j : Fin n =>
        directX j + (directY j - directX j) := by
      funext j
      ring
    calc
      vecNorm2 directY =
          vecNorm2 (fun j : Fin n =>
            directX j + (directY j - directX j)) := congrArg vecNorm2 heq
      _ ≤ vecNorm2 directX +
          vecNorm2 (fun j : Fin n => directY j - directX j) :=
        vecNorm2_add_le _ _
  have htotal :
      (vecNorm2 directY + residualTerm) / vecNorm2 x ≤
        (vecNorm2 directX + residualTerm) / vecNorm2 x +
          vecNorm2 (fun j : Fin n => directY j - directX j) /
            vecNorm2 x := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hxpos.le
  exact htotal.trans (by linarith)

/-- The printed `B_A⁺ = (I-(AP)⁺A)B⁺` remains a right inverse of `B` whenever
the range of `(AP)⁺` lies in the nullspace of `B`. -/
theorem sourceBAplus_rightInverse_of_constraint_annihilates
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (Bplus : Fin n → Fin p → ℝ) (APplus : Fin n → Fin m → ℝ)
    (hright : rectMatMul B Bplus = idMatrix p)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0)) :
    rectMatMul B (theorem20_8BAplus A B Bplus APplus) = idMatrix p := by
  have hBAPA :
      rectMatMul B (rectMatMul APplus A) =
        (fun _i : Fin p => fun _j : Fin n => 0) := by
    rw [← rectMatMul_assoc, hBAPplus]
    ext i j
    simp [rectMatMul]
  calc
    rectMatMul B (theorem20_8BAplus A B Bplus APplus) =
        rectMatMul
          (rectMatMul B
            (fun i j => idMatrix n i j - rectMatMul APplus A i j))
          Bplus := by
            simp only [theorem20_8BAplus, rectMatMul_assoc]
    _ = rectMatMul
          (fun i j =>
            rectMatMul B (idMatrix n) i j -
              rectMatMul B (rectMatMul APplus A) i j)
          Bplus := by
            rw [rectMatMul_sub_right]
    _ = rectMatMul B Bplus := by
      rw [rectMatMul_id_right, hBAPA]
      congr 1
      funext i j
      simp
    _ = idMatrix p := hright

/-- A source LSE multiplier is recovered sharply from the residual by
`λ = (A B_A⁺)ᵀ r` once `B_A⁺` is a right inverse. -/
theorem source_lagrange_eq_transpose_A_BAplus_residual
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (BAplus : Fin n → Fin p → ℝ) (r : Fin m → ℝ)
    (lambda : Fin p → ℝ)
    (hBBA : rectMatMul B BAplus = idMatrix p)
    (hnormal : ∀ j : Fin n,
      ∑ i : Fin m, A i j * r i = ∑ q : Fin p, B q j * lambda q) :
    lambda =
      rectMatMulVec (finiteTranspose (rectMatMul A BAplus)) r := by
  funext k
  calc
    lambda k = ∑ q : Fin p, idMatrix p q k * lambda q := by
      simp [idMatrix]
    _ = ∑ q : Fin p, rectMatMul B BAplus q k * lambda q := by
      rw [hBBA]
    _ = ∑ j : Fin n, BAplus j k * (∑ q : Fin p, B q j * lambda q) := by
      simp only [rectMatMul]
      calc
        ∑ q : Fin p, (∑ j : Fin n, B q j * BAplus j k) * lambda q =
            ∑ q : Fin p, ∑ j : Fin n,
              BAplus j k * (B q j * lambda q) := by
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ j : Fin n, ∑ q : Fin p,
              BAplus j k * (B q j * lambda q) := by
          rw [Finset.sum_comm]
        _ = ∑ j : Fin n, BAplus j k *
              (∑ q : Fin p, B q j * lambda q) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
    _ = ∑ j : Fin n, BAplus j k * (∑ i : Fin m, A i j * r i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hnormal j]
    _ = ∑ i : Fin m, (∑ j : Fin n, A i j * BAplus j k) * r i := by
      calc
        ∑ j : Fin n, BAplus j k * (∑ i : Fin m, A i j * r i) =
            ∑ j : Fin n, ∑ i : Fin m,
              BAplus j k * (A i j * r i) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
        _ = ∑ i : Fin m, ∑ j : Fin n,
              BAplus j k * (A i j * r i) := by
          rw [Finset.sum_comm]
        _ = ∑ i : Fin m, (∑ j : Fin n, A i j * BAplus j k) * r i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = rectMatMulVec (finiteTranspose (rectMatMul A BAplus)) r k := by
      rfl

/-- Sharp operator-norm consequence of
`λ = (A B_A⁺)ᵀ r`. -/
theorem source_lagrange_vecNorm2_le_A_BAplus_residual
    {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (BAplus : Fin n → Fin p → ℝ) (r : Fin m → ℝ)
    (lambda : Fin p → ℝ)
    (hBBA : rectMatMul B BAplus = idMatrix p)
    (hnormal : ∀ j : Fin n,
      ∑ i : Fin m, A i j * r i = ∑ q : Fin p, B q j * lambda q) :
    vecNorm2 lambda ≤
      complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus)) *
        vecNorm2 r := by
  rw [source_lagrange_eq_transpose_A_BAplus_residual
    A B BAplus r lambda hBBA hnormal]
  have hop :
      rectOpNorm2Le (rectMatMul A BAplus)
        (complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus))) :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le _ le_rfl
  have hopT :
      rectOpNorm2Le (finiteTranspose (rectMatMul A BAplus))
        (complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus))) :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le _
      (complexMatrixOp2_nonneg _) hop
  exact hopT r

/-- The source part of the KKT stationarity forcing is exactly the residual
term in Higham's first-order coefficient.  No estimate of the perturbed
residual or multiplier is used here. -/
theorem sourceNormalGramPlus_stationarity_forcing_le_residualAmplifier
    {m n p : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (B ΔB : Fin p → Fin n → ℝ) (Bplus : Fin n → Fin p → ℝ)
    (APplus : Fin n → Fin m → ℝ) (d Δd : Fin p → ℝ)
    (r : Fin m → ℝ) (lambda : Fin p → ℝ) {eps : ℝ}
    (hright : rectMatMul B Bplus = idMatrix p)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hnormal : ∀ j : Fin n,
      ∑ i : Fin m, A i j * r i = ∑ q : Fin p, B q j * lambda q)
    (hbudget :
      theorem20_8RelativePerturbationBudget A ΔA b Δb B ΔB d Δd eps)
    (heps_nonneg : 0 ≤ eps) (hApos : 0 < frobNormRect A) :
    vecNorm2
        (rectMatMulVec (sourceNormalGramPlus APplus)
          (fun j : Fin n =>
            (∑ q : Fin p, ΔB q j * lambda q) -
              (∑ i : Fin m, ΔA i j * r i))) ≤
      eps * theorem20_8ResidualAmplifier A B APplus
          (theorem20_8BAplus A B Bplus APplus) *
        (vecNorm2 r / frobNormRect A) := by
  let BAplus : Fin n → Fin p → ℝ :=
    theorem20_8BAplus A B Bplus APplus
  let apNorm : ℝ := complexMatrixOp2 (realRectToCMatrix APplus)
  let abNorm : ℝ :=
    complexMatrixOp2 (realRectToCMatrix (rectMatMul A BAplus))
  let forcing : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * lambda q) -
      (∑ i : Fin m, ΔA i j * r i)
  have hBBA : rectMatMul B BAplus = idMatrix p := by
    dsimp [BAplus]
    exact sourceBAplus_rightInverse_of_constraint_annihilates
      A B Bplus APplus hright hBAPplus
  have hlambda : vecNorm2 lambda ≤ abNorm * vecNorm2 r := by
    dsimp [abNorm]
    exact source_lagrange_vecNorm2_le_A_BAplus_residual
      A B BAplus r lambda hBBA hnormal
  have hforcing0 :
      vecNorm2 forcing ≤
        (eps * frobNormRect B) * vecNorm2 lambda +
          (eps * frobNormRect A) * vecNorm2 r := by
    dsimp [forcing]
    exact theorem20_8_vecNorm2_stationarity_forcing_le_of_relativeBudget
      A ΔA b Δb B ΔB d Δd lambda r hbudget
  have hepsB : 0 ≤ eps * frobNormRect B :=
    mul_nonneg heps_nonneg (frobNormRect_nonneg B)
  have hapNorm : 0 ≤ apNorm := by
    dsimp [apNorm]
    exact complexMatrixOp2_nonneg _
  have habNorm : 0 ≤ abNorm := by
    dsimp [abNorm]
    exact complexMatrixOp2_nonneg _
  have hforcing :
      vecNorm2 forcing ≤
        eps * (frobNormRect B * abNorm + frobNormRect A) * vecNorm2 r := by
    have hBterm := mul_le_mul_of_nonneg_left hlambda hepsB
    calc
      vecNorm2 forcing ≤
          (eps * frobNormRect B) * vecNorm2 lambda +
            (eps * frobNormRect A) * vecNorm2 r := hforcing0
      _ ≤ (eps * frobNormRect B) * (abNorm * vecNorm2 r) +
            (eps * frobNormRect A) * vecNorm2 r :=
          add_le_add hBterm le_rfl
      _ = eps * (frobNormRect B * abNorm + frobNormRect A) *
            vecNorm2 r := by ring
  have hAP : rectOpNorm2Le APplus apNorm := by
    dsimp [apNorm]
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le _ le_rfl
  have hAPT : rectOpNorm2Le (finiteTranspose APplus) apNorm :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le APplus hapNorm hAP
  have hG :
      rectOpNorm2Le (sourceNormalGramPlus APplus) (apNorm * apNorm) := by
    dsimp [sourceNormalGramPlus]
    exact rectOpNorm2Le_rectMatMul APplus (finiteTranspose APplus)
      hapNorm hAP hAPT
  have hGnonneg : 0 ≤ apNorm * apNorm := mul_nonneg hapNorm hapNorm
  have happly := hG forcing
  have hscaled := mul_le_mul_of_nonneg_left hforcing hGnonneg
  calc
    vecNorm2 (rectMatMulVec (sourceNormalGramPlus APplus) forcing) ≤
        (apNorm * apNorm) * vecNorm2 forcing := happly
    _ ≤ (apNorm * apNorm) *
          (eps * (frobNormRect B * abNorm + frobNormRect A) *
            vecNorm2 r) := hscaled
    _ = eps * theorem20_8ResidualAmplifier A B APplus BAplus *
          (vecNorm2 r / frobNormRect A) := by
      dsimp [apNorm, abNorm, BAplus]
      unfold theorem20_8ResidualAmplifier theorem20_8KappaB
      field_simp [ne_of_gt hApos]

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

/-- Source-only linear coefficient for the KKT data-row forcing. -/
noncomputable def kktDataDifferenceLinearCoeff {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  let residualScale := vecNorm2 (lsResidualHigham A b x) / vecNorm2 x
  let solutionCoeff :=
    kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x
  2 * frobNormRect A + residualScale + frobNormRect A * solutionCoeff

/-- Source-only linear coefficient for the KKT residual difference. -/
noncomputable def kktResidualDifferenceLinearCoeff {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  kktDataDifferenceLinearCoeff hB hStack b x +
    frobNormRect A *
      kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x

/-- Source-only linear coefficient for the KKT constraint-row forcing. -/
noncomputable def kktConstraintDifferenceLinearCoeff {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ) : ℝ :=
  frobNormRect B *
    (2 + kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x)

/-- Sharp source-stationarity forcing coefficient before applying the KKT
inverse multiplier row. -/
noncomputable def kktSourceStationarityLinearCoeff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hB : LSEFullRowRank B) (b : Fin m → ℝ) (x : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) : ℝ :=
  (frobNormRect B *
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul A (sourceBAplus A B hB APplus))) +
      frobNormRect A) *
    (vecNorm2 (lsResidualHigham A b x) / vecNorm2 x)

/-- Source-only linear coefficient for the KKT multiplier difference, after
absorbing the multiplier-row self term with a one-half denominator margin. -/
noncomputable def kktMultiplierDifferenceLinearCoeff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) : ℝ :=
  let hnull := sourceNullIntersection hStack
  2 *
    (LSEKKTInverseMultiplierDataCoeff hB hnull *
        kktDataDifferenceLinearCoeff hB hStack b x +
      LSEKKTInverseMultiplierStatCoeff hB hnull *
        (kktSourceStationarityLinearCoeff A B hB b x APplus +
          frobNormRect A *
            kktResidualDifferenceLinearCoeff hB hStack b x) +
      LSEKKTInverseMultiplierConstrCoeff hB hnull *
        kktConstraintDifferenceLinearCoeff hB hStack b x)

/-- The source-only coefficient of the stationarity `eps²` remainder. -/
noncomputable def kktStationarityQuadraticCoeff {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin p → Fin n → ℝ)
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (b : Fin m → ℝ) (x : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) : ℝ :=
  complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
    (frobNormRect B *
        kktMultiplierDifferenceLinearCoeff A B hB hStack b x APplus +
      frobNormRect A *
        kktResidualDifferenceLinearCoeff hB hStack b x)

/-- On the same explicit source-only neighborhood used for the coupled KKT
solution bound, the residual and multiplier differences are uniformly first
order.  These are precisely the two estimates required by
`kktStationarityRemainderRadius_le_eps_sq_mul`. -/
theorem kkt_residual_multiplier_differences_le_local_coeffs
    {m n p : ℕ}
    {A ΔA : Fin m → Fin n → ℝ} {b Δb : Fin m → ℝ}
    {B ΔB : Fin p → Fin n → ℝ} {d Δd : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (APplus : Fin n → Fin m → ℝ)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (lambda mu : Fin p → ℝ)
    (hnormal : ∀ j : Fin n,
      ∑ i : Fin m, A i j * lsResidualHigham A b x i =
        ∑ q : Fin p, B q j * lambda q)
    (hsys :
      LSEKKTSystem A B
        (fun i => Δb i - rectMatMulVec ΔA y i)
        (fun j =>
          (∑ q : Fin p, ΔB q j * mu q) -
            (∑ i : Fin m,
              ΔA i j *
                lsResidualHigham (fun i j => A i j + ΔA i j)
                  (fun i => b i + Δb i) y i))
        (fun q => Δd q - rectMatMulVec ΔB y q)
        (fun i =>
          lsResidualHigham (fun i j => A i j + ΔA i j)
              (fun i => b i + Δb i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun q => mu q - lambda q))
    {eps : ℝ}
    (hbudget :
      theorem20_8RelativePerturbationBudget A ΔA b Δb B ΔB d Δd eps)
    (heps_nonneg : 0 ≤ eps) (hxnorm : 0 < vecNorm2 x)
    (hsolution :
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        theorem20_8KKTSourceResidualRatioCoupledBound hB
          (sourceNullIntersection hStack) b x eps)
    (hsmall :
      eps < kktLocalSmallnessThreshold hB (sourceNullIntersection hStack)) :
    vecNorm2
        (fun i =>
          lsResidualHigham (fun i j => A i j + ΔA i j)
              (fun i => b i + Δb i) y i -
            lsResidualHigham A b x i) ≤
        eps * kktResidualDifferenceLinearCoeff hB hStack b x * vecNorm2 x ∧
      vecNorm2 (fun q => mu q - lambda q) ≤
        eps *
          kktMultiplierDifferenceLinearCoeff A B hB hStack b x APplus *
          vecNorm2 x := by
  let hnull : LSENullIntersectionTrivial A B := sourceNullIntersection hStack
  let residualScale : ℝ :=
    vecNorm2 (lsResidualHigham A b x) / vecNorm2 x
  let solutionCoeff : ℝ := kktLocalLinearBoundCoeff hB hnull b x
  let dataCoeffKKT : ℝ :=
    kktDataDifferenceLinearCoeff hB hStack b x
  let residualCoeff : ℝ :=
    kktResidualDifferenceLinearCoeff hB hStack b x
  let constraintCoeff : ℝ :=
    kktConstraintDifferenceLinearCoeff hB hStack b x
  let sourceStatCoeff : ℝ :=
    kktSourceStationarityLinearCoeff A B hB b x APplus
  let multiplierCoeff : ℝ :=
    kktMultiplierDifferenceLinearCoeff A B hB hStack b x APplus
  let r : Fin m → ℝ := lsResidualHigham A b x
  let s : Fin m → ℝ :=
    lsResidualHigham (fun i j => A i j + ΔA i j)
      (fun i => b i + Δb i) y
  let dr : Fin m → ℝ := fun i => s i - r i
  let dx : Fin n → ℝ := fun j => y j - x j
  let dlambda : Fin p → ℝ := fun q => mu q - lambda q
  let f : Fin m → ℝ := fun i => Δb i - rectMatMulVec ΔA y i
  let c : Fin p → ℝ := fun q => Δd q - rectMatMulVec ΔB y q
  let g : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * mu q) -
      (∑ i : Fin m, ΔA i j * s i)
  let gSource : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * lambda q) -
      (∑ i : Fin m, ΔA i j * r i)
  let gDiff : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * dlambda q) -
      (∑ i : Fin m, ΔA i j * dr i)
  rcases kktLocal_smallness_conditions hB hnull heps_nonneg hsmall with
    ⟨heps_le_one, hgain_half, _hsol_half, _hquad⟩
  have hsolutionLinear :=
    kktSourceResidualRatioCoupledBound_le_eps_mul_kktLocalLinearBoundCoeff
      hB hnull b x hxnorm heps_nonneg hsmall
  have hdxRel :
      vecNorm2 dx / vecNorm2 x ≤ eps * solutionCoeff := by
    exact hsolution.trans (by simpa [dx, solutionCoeff, hnull] using hsolutionLinear)
  have hdx : vecNorm2 dx ≤ eps * solutionCoeff * vecNorm2 x :=
    (div_le_iff₀ hxnorm).mp hdxRel
  have hresidualScale : 0 ≤ residualScale := by
    dsimp [residualScale]
    exact div_nonneg (vecNorm2_nonneg _) hxnorm.le
  have hsolutionCoeff : 0 ≤ solutionCoeff := by
    have himData := LSEKKTInverseMultiplierDataCoeff_nonneg hB hnull
    have himStat := LSEKKTInverseMultiplierStatCoeff_nonneg hB hnull
    have himConstr := LSEKKTInverseMultiplierConstrCoeff_nonneg hB hnull
    have hisData := LSEKKTInverseSolutionDataCoeff_nonneg hB hnull
    have hisStat := LSEKKTInverseSolutionStatCoeff_nonneg hB hnull
    have hisConstr := LSEKKTInverseSolutionConstrCoeff_nonneg hB hnull
    have hA := frobNormRect_nonneg A
    have hBnorm := frobNormRect_nonneg B
    dsimp [solutionCoeff, kktLocalLinearBoundCoeff]
    positivity
  have hdataCoeff : 0 ≤ dataCoeffKKT := by
    change 0 ≤ 2 * frobNormRect A + residualScale +
      frobNormRect A * solutionCoeff
    exact add_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (frobNormRect_nonneg A))
        hresidualScale)
      (mul_nonneg (frobNormRect_nonneg A) hsolutionCoeff)
  have hresidualCoeff : 0 ≤ residualCoeff := by
    change 0 ≤ dataCoeffKKT + frobNormRect A * solutionCoeff
    exact add_nonneg hdataCoeff
      (mul_nonneg (frobNormRect_nonneg A) hsolutionCoeff)
  have hconstraintCoeff : 0 ≤ constraintCoeff := by
    change 0 ≤ frobNormRect B * (2 + solutionCoeff)
    exact mul_nonneg (frobNormRect_nonneg B)
      (add_nonneg (by norm_num) hsolutionCoeff)
  have heps_solutionCoeff_le : eps * solutionCoeff ≤ solutionCoeff :=
    mul_le_of_le_one_left hsolutionCoeff heps_le_one
  have hy0 : vecNorm2 y ≤ (1 + eps * solutionCoeff) * vecNorm2 x :=
    vecNorm2_le_one_add_eps_solutionRadius_mul_of_solution_difference_bound
      x y hxnorm hdx
  have hy : vecNorm2 y ≤ (1 + solutionCoeff) * vecNorm2 x := by
    have hscale : 1 + eps * solutionCoeff ≤ 1 + solutionCoeff := by linarith
    exact hy0.trans
      (mul_le_mul_of_nonneg_right hscale (vecNorm2_nonneg x))
  have hrScale : vecNorm2 r ≤ residualScale * vecNorm2 x := by
    dsimp [r, residualScale]
    rw [div_mul_cancel₀ _ (ne_of_gt hxnorm)]
  have hbScale :
      vecNorm2 b ≤ (frobNormRect A + residualScale) * vecNorm2 x := by
    exact theorem20_8_vecNorm2_b_le_of_sourceResidualScale A b x
      (by simpa [r] using hrScale)
  have hdScale : vecNorm2 d ≤ frobNormRect B * vecNorm2 x :=
    hx.vecNorm2_constraint_rhs_le_frobNormRect_mul
  have hf0 :=
    theorem20_8_vecNorm2_higham_data_forcing_le_of_relativeBudget_scales
      A ΔA b Δb B ΔB d Δd x y hbudget heps_nonneg hbScale hy
  have hf : vecNorm2 f ≤ eps * dataCoeffKKT * vecNorm2 x := by
    calc
      vecNorm2 f ≤
          (eps * (frobNormRect A + residualScale) +
            (eps * frobNormRect A) * (1 + solutionCoeff)) * vecNorm2 x := by
        simpa [f] using hf0
      _ = eps * dataCoeffKKT * vecNorm2 x := by
        dsimp [dataCoeffKKT, kktDataDifferenceLinearCoeff, residualScale,
          solutionCoeff, hnull]
        ring
  have hc0 :=
    theorem20_8_vecNorm2_constraint_defect_le_of_relativeBudget_scales
      A ΔA b Δb B ΔB d Δd x y hbudget heps_nonneg hdScale hy
  have hc : vecNorm2 c ≤ eps * constraintCoeff * vecNorm2 x := by
    calc
      vecNorm2 c ≤
          (eps * frobNormRect B +
            (eps * frobNormRect B) * (1 + solutionCoeff)) * vecNorm2 x := by
        simpa [c] using hc0
      _ = eps * constraintCoeff * vecNorm2 x := by
        dsimp [constraintCoeff, kktConstraintDifferenceLinearCoeff,
          solutionCoeff, hnull]
        ring
  have hdrEq : dr = fun i : Fin m => f i - rectMatMulVec A dx i := by
    funext i
    rcases hsys with ⟨htop, _hstat, _hconstr⟩
    have hi := htop i
    dsimp [dr, s, r, f, dx] at hi ⊢
    linarith
  have hAdx :
      vecNorm2 (rectMatMulVec A dx) ≤
        frobNormRect A * (eps * solutionCoeff * vecNorm2 x) := by
    have hop := vecNorm2_rectMatMulVec_le_frobNormRect_mul A dx
    exact hop.trans
      (mul_le_mul_of_nonneg_left hdx (frobNormRect_nonneg A))
  have hdr : vecNorm2 dr ≤ eps * residualCoeff * vecNorm2 x := by
    have htri := vecNorm2_add_le f (fun i : Fin m => -rectMatMulVec A dx i)
    calc
      vecNorm2 dr =
          vecNorm2 (fun i : Fin m => f i - rectMatMulVec A dx i) :=
        congrArg vecNorm2 hdrEq
      _ ≤ vecNorm2 f +
            vecNorm2 (fun i : Fin m => -rectMatMulVec A dx i) := by
          simpa [sub_eq_add_neg] using htri
      _ = vecNorm2 f + vecNorm2 (rectMatMulVec A dx) := by
          rw [vecNorm2_neg]
      _ ≤ eps * dataCoeffKKT * vecNorm2 x +
            frobNormRect A * (eps * solutionCoeff * vecNorm2 x) :=
          add_le_add hf hAdx
      _ = eps * residualCoeff * vecNorm2 x := by
          dsimp [residualCoeff, kktResidualDifferenceLinearCoeff,
            dataCoeffKKT, solutionCoeff, hnull]
          ring
  have hBBA :
      rectMatMul B (sourceBAplus A B hB APplus) = idMatrix p :=
    sourceBAplus_rightInverse_of_constraint_annihilates
      A B hB.rightInverse APplus hB.rightInverse_spec hBAPplus
  have hlambda :
      vecNorm2 lambda ≤
        complexMatrixOp2
            (realRectToCMatrix
              (rectMatMul A (sourceBAplus A B hB APplus))) * vecNorm2 r := by
    exact source_lagrange_vecNorm2_le_A_BAplus_residual
      A B (sourceBAplus A B hB APplus) r lambda hBBA
      (by simpa [r] using hnormal)
  have hgSource0 :
      vecNorm2 gSource ≤
        (eps * frobNormRect B) * vecNorm2 lambda +
          (eps * frobNormRect A) * vecNorm2 r := by
    dsimp [gSource]
    exact theorem20_8_vecNorm2_stationarity_forcing_le_of_relativeBudget
      A ΔA b Δb B ΔB d Δd lambda r hbudget
  have hepsB : 0 ≤ eps * frobNormRect B :=
    mul_nonneg heps_nonneg (frobNormRect_nonneg B)
  have hepsA : 0 ≤ eps * frobNormRect A :=
    mul_nonneg heps_nonneg (frobNormRect_nonneg A)
  have hgSource :
      vecNorm2 gSource ≤ eps * sourceStatCoeff * vecNorm2 x := by
    have hlambda' := mul_le_mul_of_nonneg_left hlambda hepsB
    have hrB := mul_le_mul_of_nonneg_left hrScale
      (mul_nonneg heps_nonneg (frobNormRect_nonneg B))
    have hrA := mul_le_mul_of_nonneg_left hrScale hepsA
    calc
      vecNorm2 gSource ≤
          (eps * frobNormRect B) * vecNorm2 lambda +
            (eps * frobNormRect A) * vecNorm2 r := hgSource0
      _ ≤ (eps * frobNormRect B) *
              (complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (sourceBAplus A B hB APplus))) * vecNorm2 r) +
            (eps * frobNormRect A) * vecNorm2 r :=
          add_le_add hlambda' le_rfl
      _ ≤ (eps * frobNormRect B) *
              (complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (sourceBAplus A B hB APplus))) *
                (residualScale * vecNorm2 x)) +
            (eps * frobNormRect A) * (residualScale * vecNorm2 x) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hrScale
                (complexMatrixOp2_nonneg _)) hepsB
          · exact hrA
      _ = eps * sourceStatCoeff * vecNorm2 x := by
          dsimp [sourceStatCoeff, kktSourceStationarityLinearCoeff,
            residualScale]
          ring
  have hgDiff :
      vecNorm2 gDiff ≤
        (eps * frobNormRect B) * vecNorm2 dlambda +
          (eps * frobNormRect A) * vecNorm2 dr := by
    dsimp [gDiff]
    exact theorem20_8_vecNorm2_stationarity_forcing_le_of_relativeBudget
      A ΔA b Δb B ΔB d Δd dlambda dr hbudget
  have hgSplit : g = fun j : Fin n => gSource j + gDiff j := by
    funext j
    dsimp [g, gSource, gDiff, dlambda, dr, s, r]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have heps_sq_le_eps : eps ^ 2 ≤ eps := by
    nlinarith [heps_nonneg, heps_le_one]
  have hAresScaled :
      (eps * frobNormRect A) * vecNorm2 dr ≤
        eps * (frobNormRect A * residualCoeff) * vecNorm2 x := by
    have h0 := mul_le_mul_of_nonneg_left hdr hepsA
    have hfactor :
        eps ^ 2 * (frobNormRect A * residualCoeff * vecNorm2 x) ≤
          eps * (frobNormRect A * residualCoeff * vecNorm2 x) :=
      mul_le_mul_of_nonneg_right heps_sq_le_eps
        (mul_nonneg
          (mul_nonneg (frobNormRect_nonneg A) hresidualCoeff)
          (vecNorm2_nonneg x))
    calc
      (eps * frobNormRect A) * vecNorm2 dr ≤
          (eps * frobNormRect A) *
            (eps * residualCoeff * vecNorm2 x) := h0
      _ = eps ^ 2 * (frobNormRect A * residualCoeff * vecNorm2 x) := by
          ring
      _ ≤ eps * (frobNormRect A * residualCoeff * vecNorm2 x) := hfactor
      _ = eps * (frobNormRect A * residualCoeff) * vecNorm2 x := by ring
  have hg :
      vecNorm2 g ≤
        eps * (sourceStatCoeff + frobNormRect A * residualCoeff) *
            vecNorm2 x +
          (eps * frobNormRect B) * vecNorm2 dlambda := by
    have htri := vecNorm2_add_le gSource gDiff
    calc
      vecNorm2 g = vecNorm2 (fun j : Fin n => gSource j + gDiff j) :=
        congrArg vecNorm2 hgSplit
      _ ≤ vecNorm2 gSource + vecNorm2 gDiff := htri
      _ ≤ eps * sourceStatCoeff * vecNorm2 x +
            ((eps * frobNormRect B) * vecNorm2 dlambda +
              (eps * frobNormRect A) * vecNorm2 dr) :=
          add_le_add hgSource hgDiff
      _ ≤ eps * sourceStatCoeff * vecNorm2 x +
            ((eps * frobNormRect B) * vecNorm2 dlambda +
              eps * (frobNormRect A * residualCoeff) * vecNorm2 x) :=
          add_le_add le_rfl (add_le_add le_rfl hAresScaled)
      _ = eps * (sourceStatCoeff + frobNormRect A * residualCoeff) *
              vecNorm2 x +
            (eps * frobNormRect B) * vecNorm2 dlambda := by ring
  have hsys' : LSEKKTSystem A B f g c dr dx dlambda := by
    simpa [f, g, c, dr, dx, dlambda, r, s] using hsys
  have hinv := LSEKKTInverseTriple_eq_of_system hB hnull hsys'
  have hdlambdaEq :
      dlambda = LSEKKTInverseMultiplierLinearMap hB hnull (f, g, c) := by
    rw [hinv.2.2]
    rw [LSEKKTInverseMultiplierLinearMap_apply]
  have hmapSplit :=
    LSEKKTInverseMultiplierLinearMap_vecNorm2_le_split hB hnull f g c
  have hdataMap :=
    LSEKKTInverseMultiplierDataLinearMap_vecNorm2_le_coeff hB hnull f
  have hstatMap :=
    LSEKKTInverseMultiplierStatLinearMap_vecNorm2_le_coeff hB hnull g
  have hconstrMap :=
    LSEKKTInverseMultiplierConstrLinearMap_vecNorm2_le_coeff hB hnull c
  have hmap :
      vecNorm2 dlambda ≤
        LSEKKTInverseMultiplierDataCoeff hB hnull * vecNorm2 f +
          LSEKKTInverseMultiplierStatCoeff hB hnull * vecNorm2 g +
          LSEKKTInverseMultiplierConstrCoeff hB hnull * vecNorm2 c := by
    rw [hdlambdaEq]
    exact hmapSplit.trans (add_le_add (add_le_add hdataMap hstatMap) hconstrMap)
  have hdataNonneg := LSEKKTInverseMultiplierDataCoeff_nonneg hB hnull
  have hstatNonneg := LSEKKTInverseMultiplierStatCoeff_nonneg hB hnull
  have hconstrNonneg := LSEKKTInverseMultiplierConstrCoeff_nonneg hB hnull
  have hpre :
      vecNorm2 dlambda ≤
        eps * (multiplierCoeff / 2) * vecNorm2 x +
          (LSEKKTInverseMultiplierStatCoeff hB hnull *
            (eps * frobNormRect B)) * vecNorm2 dlambda := by
    have hf' := mul_le_mul_of_nonneg_left hf hdataNonneg
    have hg' := mul_le_mul_of_nonneg_left hg hstatNonneg
    have hc' := mul_le_mul_of_nonneg_left hc hconstrNonneg
    calc
      vecNorm2 dlambda ≤
          LSEKKTInverseMultiplierDataCoeff hB hnull * vecNorm2 f +
            LSEKKTInverseMultiplierStatCoeff hB hnull * vecNorm2 g +
            LSEKKTInverseMultiplierConstrCoeff hB hnull * vecNorm2 c := hmap
      _ ≤ LSEKKTInverseMultiplierDataCoeff hB hnull *
              (eps * dataCoeffKKT * vecNorm2 x) +
            LSEKKTInverseMultiplierStatCoeff hB hnull *
              (eps * (sourceStatCoeff + frobNormRect A * residualCoeff) *
                  vecNorm2 x +
                (eps * frobNormRect B) * vecNorm2 dlambda) +
            LSEKKTInverseMultiplierConstrCoeff hB hnull *
              (eps * constraintCoeff * vecNorm2 x) :=
          add_le_add (add_le_add hf' hg') hc'
      _ = eps * (multiplierCoeff / 2) * vecNorm2 x +
            (LSEKKTInverseMultiplierStatCoeff hB hnull *
              (eps * frobNormRect B)) * vecNorm2 dlambda := by
          dsimp [multiplierCoeff, kktMultiplierDifferenceLinearCoeff,
            dataCoeffKKT, residualCoeff, constraintCoeff, sourceStatCoeff,
            hnull]
          ring
  have hmultiplierCoeff : 0 ≤ multiplierCoeff := by
    have hsourceStatCoeff : 0 ≤ sourceStatCoeff := by
      change 0 ≤
        (frobNormRect B *
              complexMatrixOp2
                (realRectToCMatrix
                  (rectMatMul A (sourceBAplus A B hB APplus))) +
            frobNormRect A) * residualScale
      exact mul_nonneg
        (add_nonneg
          (mul_nonneg (frobNormRect_nonneg B)
            (complexMatrixOp2_nonneg _))
          (frobNormRect_nonneg A))
        hresidualScale
    have hdataNonneg := LSEKKTInverseMultiplierDataCoeff_nonneg hB hnull
    have hstatNonneg := LSEKKTInverseMultiplierStatCoeff_nonneg hB hnull
    have hconstrNonneg := LSEKKTInverseMultiplierConstrCoeff_nonneg hB hnull
    change 0 ≤ 2 *
      (LSEKKTInverseMultiplierDataCoeff hB hnull * dataCoeffKKT +
        LSEKKTInverseMultiplierStatCoeff hB hnull *
          (sourceStatCoeff + frobNormRect A * residualCoeff) +
        LSEKKTInverseMultiplierConstrCoeff hB hnull * constraintCoeff)
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (add_nonneg
          (mul_nonneg hdataNonneg hdataCoeff)
          (mul_nonneg hstatNonneg
            (add_nonneg hsourceStatCoeff
              (mul_nonneg (frobNormRect_nonneg A) hresidualCoeff))))
        (mul_nonneg hconstrNonneg hconstraintCoeff))
  have hdlambda :
      vecNorm2 dlambda ≤ eps * multiplierCoeff * vecNorm2 x := by
    have hgainApplied :
        (LSEKKTInverseMultiplierStatCoeff hB hnull *
            (eps * frobNormRect B)) * vecNorm2 dlambda ≤
          ((1 : ℝ) / 2) * vecNorm2 dlambda :=
      mul_le_mul_of_nonneg_right hgain_half (vecNorm2_nonneg dlambda)
    have hlinear :
        vecNorm2 dlambda ≤
          eps * (multiplierCoeff / 2) * vecNorm2 x +
            ((1 : ℝ) / 2) * vecNorm2 dlambda :=
      hpre.trans (add_le_add le_rfl hgainApplied)
    have htmp :
        vecNorm2 dlambda ≤
          2 * (eps * (multiplierCoeff / 2) * vecNorm2 x) := by
      linarith
    calc
      vecNorm2 dlambda ≤
          2 * (eps * (multiplierCoeff / 2) * vecNorm2 x) := htmp
      _ = eps * multiplierCoeff * vecNorm2 x := by ring
  exact ⟨by simpa [dr, residualCoeff] using hdr,
    by simpa [dlambda, multiplierCoeff] using hdlambda⟩

/-- Unconditional source-KKT bridge from the exact minimizer displacement to
the correctly signed Higham radius.  The only term left outside that printed
radius is explicitly a product of `(ΔA,ΔB)` with the KKT residual/multiplier
differences; no residual gap, common factorization, norm ordering, or target
inequality is assumed. -/
theorem exists_lagrange_solution_difference_relative_le_highamRadius_add_kktRemainder
    {m n p : ℕ}
    {A ΔA : Fin m → Fin n → ℝ} {b Δb : Fin m → ℝ}
    {B ΔB : Fin p → Fin n → ℝ} {d Δd : Fin p → ℝ}
    {x y : Fin n → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hBpert : LSEFullRowRank (fun i j => B i j + ΔB i j))
    (APplus : Fin n → Fin m → ℝ)
    (hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse)
    (hBAPplus :
      rectMatMul B APplus = (fun _i : Fin p => fun _j : Fin m => 0))
    (hAPrange_symmetric :
      IsSymmetricFiniteMatrix
        (rectMatMul (theorem20_8AP A B hB.rightInverse) APplus))
    (hAPreproduces :
      rectMatMul
          (rectMatMul APplus (theorem20_8AP A B hB.rightInverse)) APplus =
        APplus)
    {eps : ℝ}
    (hbudget :
      theorem20_8RelativePerturbationBudget A ΔA b Δb B ΔB d Δd eps)
    (heps_nonneg : 0 ≤ eps) (hApos : 0 < frobNormRect A)
    (hxnorm : 0 < vecNorm2 x) :
    ∃ lambda mu : Fin p → ℝ,
      (∀ j : Fin n,
        ∑ i : Fin m, A i j * lsResidualHigham A b x i =
          ∑ q : Fin p, B q j * lambda q) ∧
      LSEKKTSystem A B
        (fun i => Δb i - rectMatMulVec ΔA y i)
        (fun j =>
          (∑ q : Fin p, ΔB q j * mu q) -
            (∑ i : Fin m,
              ΔA i j *
                lsResidualHigham (fun i j => A i j + ΔA i j)
                  (fun i => b i + Δb i) y i))
        (fun q => Δd q - rectMatMulVec ΔB y q)
        (fun i =>
          lsResidualHigham (fun i j => A i j + ΔA i j)
              (fun i => b i + Δb i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun q => mu q - lambda q) ∧
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        highamDirectDataCorrectionRadius
            A ΔA b Δb B ΔB Δd hB x y APplus eps +
          kktStationarityRemainderRadius A B APplus x eps
            (fun i =>
              lsResidualHigham (fun i j => A i j + ΔA i j)
                  (fun i => b i + Δb i) y i -
                lsResidualHigham A b x i)
            (fun q => mu q - lambda q) := by
  rcases exists_lagrange_solution_difference_eq_source_bottom_row
      hx hy hB hBpert APplus hAPleft hBAPplus hAPrange_symmetric
        hAPreproduces with
    ⟨lambda, mu, hnormal, hsys, hformula⟩
  refine ⟨lambda, mu, hnormal, hsys, ?_⟩
  let r : Fin m → ℝ := lsResidualHigham A b x
  let s : Fin m → ℝ :=
    lsResidualHigham (fun i j => A i j + ΔA i j)
      (fun i => b i + Δb i) y
  let dx : Fin n → ℝ := fun j => y j - x j
  let dlambda : Fin p → ℝ := fun q => mu q - lambda q
  let direct : Fin n → ℝ := fun j =>
    rectMatMulVec (sourceBAplus A B hB APplus)
        (fun q : Fin p => Δd q - rectMatMulVec ΔB y q) j +
      rectMatMulVec APplus
        (fun i : Fin m => Δb i - rectMatMulVec ΔA y i) j
  let gSource : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * lambda q) -
      (∑ i : Fin m, ΔA i j * r i)
  let gDiff : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * dlambda q) -
      (∑ i : Fin m, ΔA i j * (s i - r i))
  let gActual : Fin n → ℝ := fun j =>
    (∑ q : Fin p, ΔB q j * mu q) -
      (∑ i : Fin m, ΔA i j * s i)
  let Gplus : Fin n → Fin n → ℝ := sourceNormalGramPlus APplus
  let sourceTerm : ℝ :=
    eps * theorem20_8ResidualAmplifier A B APplus
        (sourceBAplus A B hB APplus) *
      (vecNorm2 r / frobNormRect A)
  let remainderNumerator : ℝ :=
    complexMatrixOp2 (realRectToCMatrix APplus) ^ 2 *
      ((eps * frobNormRect B) * vecNorm2 dlambda +
        (eps * frobNormRect A) * vecNorm2 (fun i => s i - r i))
  have hgSplit : gActual = fun j : Fin n => gSource j + gDiff j := by
    funext j
    dsimp [gActual, gSource, gDiff, dlambda]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  have hformula' :
      dx = fun j : Fin n => direct j - rectMatMulVec Gplus gActual j := by
    simpa [dx, direct, gActual, s, r, Gplus, sourceBAplus] using hformula
  have hdxSplit :
      dx = fun j : Fin n =>
        (direct j - rectMatMulVec Gplus gSource j) -
          rectMatMulVec Gplus gDiff j := by
    calc
      dx = fun j : Fin n => direct j - rectMatMulVec Gplus gActual j :=
        hformula'
      _ = fun j : Fin n =>
          direct j -
            (rectMatMulVec Gplus gSource j +
              rectMatMulVec Gplus gDiff j) := by
        rw [hgSplit, rectMatMulVec_add]
      _ = fun j : Fin n =>
          (direct j - rectMatMulVec Gplus gSource j) -
            rectMatMulVec Gplus gDiff j := by
        funext j
        ring
  have hsource :
      vecNorm2 (rectMatMulVec Gplus gSource) ≤ sourceTerm := by
    dsimp [Gplus, gSource, sourceTerm, r]
    exact sourceNormalGramPlus_stationarity_forcing_le_residualAmplifier
      A ΔA b Δb B ΔB hB.rightInverse APplus d Δd
      (lsResidualHigham A b x) lambda hB.rightInverse_spec hBAPplus
      hnormal hbudget heps_nonneg hApos
  have hforcingDiff :
      vecNorm2 gDiff ≤
        (eps * frobNormRect B) * vecNorm2 dlambda +
          (eps * frobNormRect A) * vecNorm2 (fun i => s i - r i) := by
    dsimp [gDiff]
    exact theorem20_8_vecNorm2_stationarity_forcing_le_of_relativeBudget
      A ΔA b Δb B ΔB d Δd dlambda (fun i => s i - r i) hbudget
  let apNorm : ℝ := complexMatrixOp2 (realRectToCMatrix APplus)
  have hapNorm : 0 ≤ apNorm := by
    dsimp [apNorm]
    exact complexMatrixOp2_nonneg _
  have hAP : rectOpNorm2Le APplus apNorm := by
    dsimp [apNorm]
    exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le _ le_rfl
  have hAPT : rectOpNorm2Le (finiteTranspose APplus) apNorm :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le APplus hapNorm hAP
  have hG : rectOpNorm2Le Gplus (apNorm * apNorm) := by
    dsimp [Gplus, sourceNormalGramPlus]
    exact rectOpNorm2Le_rectMatMul APplus (finiteTranspose APplus)
      hapNorm hAP hAPT
  have hGD :
      vecNorm2 (rectMatMulVec Gplus gDiff) ≤ remainderNumerator := by
    have happly := hG gDiff
    have hcoeff : 0 ≤ apNorm * apNorm := mul_nonneg hapNorm hapNorm
    have hscaled := mul_le_mul_of_nonneg_left hforcingDiff hcoeff
    calc
      vecNorm2 (rectMatMulVec Gplus gDiff) ≤
          (apNorm * apNorm) * vecNorm2 gDiff := happly
      _ ≤ (apNorm * apNorm) *
            ((eps * frobNormRect B) * vecNorm2 dlambda +
              (eps * frobNormRect A) * vecNorm2 (fun i => s i - r i)) :=
          hscaled
      _ = remainderNumerator := by
        dsimp [remainderNumerator, apNorm]
        ring
  have hnorm :
      vecNorm2 dx ≤ vecNorm2 direct + sourceTerm + remainderNumerator := by
    have htriOuter :=
      vecNorm2_add_le
        (fun j : Fin n => direct j - rectMatMulVec Gplus gSource j)
        (fun j : Fin n => -rectMatMulVec Gplus gDiff j)
    have htriInner :=
      vecNorm2_add_le direct
        (fun j : Fin n => -rectMatMulVec Gplus gSource j)
    have htriInner' :
        vecNorm2 (fun j : Fin n =>
            direct j - rectMatMulVec Gplus gSource j) ≤
          vecNorm2 direct +
            vecNorm2 (fun j : Fin n => -rectMatMulVec Gplus gSource j) := by
      simpa [sub_eq_add_neg] using htriInner
    calc
      vecNorm2 dx =
          vecNorm2 (fun j : Fin n =>
            (direct j - rectMatMulVec Gplus gSource j) -
              rectMatMulVec Gplus gDiff j) := congrArg vecNorm2 hdxSplit
      _ ≤ vecNorm2 (fun j : Fin n =>
              direct j - rectMatMulVec Gplus gSource j) +
            vecNorm2 (fun j : Fin n => -rectMatMulVec Gplus gDiff j) := by
          simpa [sub_eq_add_neg] using htriOuter
      _ ≤ (vecNorm2 direct +
              vecNorm2 (fun j : Fin n => -rectMatMulVec Gplus gSource j)) +
            vecNorm2 (fun j : Fin n => -rectMatMulVec Gplus gDiff j) :=
          add_le_add htriInner' le_rfl
      _ = vecNorm2 direct +
            vecNorm2 (rectMatMulVec Gplus gSource) +
              vecNorm2 (rectMatMulVec Gplus gDiff) := by
          rw [vecNorm2_neg, vecNorm2_neg]
      _ ≤ vecNorm2 direct + sourceTerm + remainderNumerator := by
          linarith
  have hdiv :
      vecNorm2 dx / vecNorm2 x ≤
        (vecNorm2 direct + sourceTerm + remainderNumerator) / vecNorm2 x :=
    div_le_div_of_nonneg_right hnorm hxnorm.le
  simpa [dx, direct, sourceTerm, remainderNumerator, r, s, dlambda,
    highamDirectDataCorrectionRadius, kktStationarityRemainderRadius,
    add_div, sourceBAplus] using hdiv

/-- Source-facing Theorem 20.8 endpoint with explicit perturbed rank
conditions.  It combines the exact KKT bottom row with the printed first-order
coefficient.  The returned remainder consists only of products of perturbation
sizes with first-order KKT differences. -/
theorem source_facing_of_rank_conditions_with_kkt_remainder
    {r p q : ℕ}
    {A ΔA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Δb : Fin (r + q) → ℝ}
    {B ΔB : Fin p → Fin (p + q) → ℝ}
    {d Δd : Fin p → ℝ} {x y : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBpert : LSEFullRowRank (fun i j => B i j + ΔB i j))
    (_hStackPert : LSEStackedFullColumnRank
      (fun i j => A i j + ΔA i j) (fun i j => B i j + ΔB i j))
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps)
    (hsmall :
      eps < theorem20_8KKTLinearizedGainSmallnessThreshold hB
        (sourceNullIntersection hStack)) :
    ∃ (APplus : Fin (p + q) → Fin (r + q) → ℝ)
        (lambda mu : Fin p → ℝ),
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
      rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
      (∀ j : Fin (p + q),
        ∑ i : Fin (r + q), A i j * lsResidualHigham A b x i =
          ∑ k : Fin p, B k j * lambda k) ∧
      LSEKKTSystem A B
        (fun i => Δb i - rectMatMulVec ΔA y i)
        (fun j =>
          (∑ k : Fin p, ΔB k j * mu k) -
            (∑ i : Fin (r + q),
              ΔA i j *
                lsResidualHigham (fun i j => A i j + ΔA i j)
                  (fun i => b i + Δb i) y i))
        (fun k => Δd k - rectMatMulVec ΔB y k)
        (fun i =>
          lsResidualHigham (fun i j => A i j + ΔA i j)
              (fun i => b i + Δb i) y i -
            lsResidualHigham A b x i)
        (fun j => y j - x j)
        (fun k => mu k - lambda k) ∧
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus
          (sourceBAplus A B hB APplus) +
        explicitRemainder hB hStack b x eps APplus +
        kktStationarityRemainderRadius A B APplus x eps
          (fun i =>
            lsResidualHigham (fun i j => A i j + ΔA i j)
                (fun i => b i + Δb i) y i -
              lsResidualHigham A b x i)
          (fun k => mu k - lambda k) := by
  have heps_nonneg : 0 ≤ eps :=
    (theorem20_8MaxRelativePerturbation_nonneg A ΔA b Δb B ΔB d Δd
      hApos).trans hmax
  have hbudget :
      theorem20_8RelativePerturbationBudget A ΔA b Δb B ΔB d Δd eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A ΔA b Δb B ΔB d Δd hApos hbpos hBpos hdpos hmax
  have hgain :
      theorem20_8KKTSourceResidualRatioGainConditions hB
        (sourceNullIntersection hStack) eps :=
    theorem20_8KKTSourceResidualRatioGainConditions_of_linearized_smallnessThreshold
      hB (sourceNullIntersection hStack) heps_nonneg hsmall
  have hsolution :
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        theorem20_8KKTSourceResidualRatioCoupledBound hB
          (sourceNullIntersection hStack) b x eps :=
    hx.kkt_solution_difference_relative_le_theorem20_8KKTSourceResidualRatioCoupledBound_of_gainConditions
      hy hB hBpert (sourceNullIntersection hStack) hxnorm hbudget heps_nonneg
      hgain
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hStack with
    ⟨h⟩
  let APplus : Fin (p + q) → Fin (r + q) → ℝ :=
    h.liftedReducedGramAPplus
  have hMP :
      RectMoorePenrosePseudoinverse (r + q) (p + q)
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus := by
    dsimp [APplus]
    exact
      h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
        hB hStack
  have hnull :
      rectMatMul B APplus =
        (fun _i : Fin p => fun _j : Fin (r + q) => 0) := by
    dsimp [APplus]
    exact h.liftedReducedGramAPplus_constraint_annihilates
  have hAPleft :
      rectMatMul APplus (theorem20_8AP A B hB.rightInverse) =
        theorem20_8Projection B hB.rightInverse := by
    dsimp [APplus]
    exact h.liftedReducedGramAPplus_AP_eq_projection hB hStack
  have hAPrange_symmetric :
      IsSymmetricFiniteMatrix
        (rectMatMul (theorem20_8AP A B hB.rightInverse) APplus) := by
    dsimp [APplus]
    exact h.liftedReducedGramAPplus_range_projection_symmetric
      hB.rightInverse hStack
  have hAPreproduces :
      rectMatMul
          (rectMatMul APplus (theorem20_8AP A B hB.rightInverse)) APplus =
        APplus := by
    dsimp [APplus]
    exact h.liftedReducedGramAPplus_reproduces_pseudoinverse_of_rightInverse
      hB hStack hB.rightInverse hB.rightInverse_spec
  rcases
      exists_lagrange_solution_difference_relative_le_highamRadius_add_kktRemainder
        hx hy hB hBpert APplus hAPleft hnull hAPrange_symmetric hAPreproduces
        hbudget heps_nonneg hApos hxnorm with
    ⟨lambda, mu, hnormal, hsys, hbridge⟩
  have hdirect :=
    highamDirectDataCorrectionRadius_le_firstOrderRHS_plus_eps_radius
      A ΔA b Δb B ΔB hB APplus d Δd y x heps_nonneg
      hApos hbpos hBpos hdpos hxnorm hmax hsolution
  have hdirect' :
      highamDirectDataCorrectionRadius
          A ΔA b Δb B ΔB Δd hB x y APplus eps ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus
          (sourceBAplus A B hB APplus) +
        explicitRemainder hB hStack b x eps APplus := by
    simpa [explicitRemainder] using hdirect
  refine ⟨APplus, lambda, mu, hMP, hnull, hnormal, hsys, ?_⟩
  linarith

/-- Full first-order form of Theorem 20.8 with an explicit source-only
`eps²` coefficient, assuming the perturbed rank conditions are supplied.
There are no residual-gap, common-factor, norm-order, or conclusion-shaped
hypotheses. -/
theorem source_facing_firstOrder_plus_eps_sq_of_rank_conditions
    {r p q : ℕ}
    {A ΔA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Δb : Fin (r + q) → ℝ}
    {B ΔB : Fin p → Fin (p + q) → ℝ}
    {d Δd : Fin p → ℝ} {x y : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBpert : LSEFullRowRank (fun i j => B i j + ΔB i j))
    (hStackPert : LSEStackedFullColumnRank
      (fun i j => A i j + ΔA i j) (fun i j => B i j + ΔB i j))
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps)
    (hsmallGain :
      eps < theorem20_8KKTLinearizedGainSmallnessThreshold hB
        (sourceNullIntersection hStack))
    (hsmallLocal :
      eps < kktLocalSmallnessThreshold hB (sourceNullIntersection hStack)) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
      rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus
          (sourceBAplus A B hB APplus) +
        eps ^ 2 *
          (kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x *
              dataCoeff A B hB APplus +
            kktStationarityQuadraticCoeff A B hB hStack b x APplus) := by
  have heps_nonneg : 0 ≤ eps :=
    (theorem20_8MaxRelativePerturbation_nonneg A ΔA b Δb B ΔB d Δd
      hApos).trans hmax
  have hbudget :
      theorem20_8RelativePerturbationBudget A ΔA b Δb B ΔB d Δd eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A ΔA b Δb B ΔB d Δd hApos hbpos hBpos hdpos hmax
  have hgain :
      theorem20_8KKTSourceResidualRatioGainConditions hB
        (sourceNullIntersection hStack) eps :=
    theorem20_8KKTSourceResidualRatioGainConditions_of_linearized_smallnessThreshold
      hB (sourceNullIntersection hStack) heps_nonneg hsmallGain
  have hsolution :
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        theorem20_8KKTSourceResidualRatioCoupledBound hB
          (sourceNullIntersection hStack) b x eps :=
    hx.kkt_solution_difference_relative_le_theorem20_8KKTSourceResidualRatioCoupledBound_of_gainConditions
      hy hB hBpert (sourceNullIntersection hStack) hxnorm hbudget heps_nonneg
      hgain
  rcases source_facing_of_rank_conditions_with_kkt_remainder
      hx hy hB hStack hBpert hStackPert hxnorm hApos hbpos hBpos hdpos hmax
      hsmallGain with
    ⟨APplus, lambda, mu, hMP, hnull, hnormal, hsys, hfirst⟩
  rcases kkt_residual_multiplier_differences_le_local_coeffs
      hx hB hStack APplus hnull lambda mu hnormal hsys hbudget heps_nonneg
      hxnorm hsolution hsmallLocal with
    ⟨hdr, hdlambda⟩
  have hstationarity :=
    kktStationarityRemainderRadius_le_eps_sq_mul
      A B APplus x
      (fun i =>
        lsResidualHigham (fun i j => A i j + ΔA i j)
            (fun i => b i + Δb i) y i -
          lsResidualHigham A b x i)
      (fun k => mu k - lambda k)
      heps_nonneg hxnorm hdr hdlambda
  have hstationarity' :
      kktStationarityRemainderRadius A B APplus x eps
          (fun i =>
            lsResidualHigham (fun i j => A i j + ΔA i j)
                (fun i => b i + Δb i) y i -
              lsResidualHigham A b x i)
          (fun k => mu k - lambda k) ≤
        eps ^ 2 * kktStationarityQuadraticCoeff
          A B hB hStack b x APplus := by
    simpa [kktStationarityQuadraticCoeff] using hstationarity
  have hexplicit :=
    explicitRemainder_le_eps_sq_mul hB hStack b x APplus hxnorm
      heps_nonneg hsmallLocal
  refine ⟨APplus, hMP, hnull, ?_⟩
  calc
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) APplus
            (sourceBAplus A B hB APplus) +
          explicitRemainder hB hStack b x eps APplus +
          kktStationarityRemainderRadius A B APplus x eps
            (fun i =>
              lsResidualHigham (fun i j => A i j + ΔA i j)
                  (fun i => b i + Δb i) y i -
                lsResidualHigham A b x i)
            (fun k => mu k - lambda k) := hfirst
    _ ≤ eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) APplus
            (sourceBAplus A B hB APplus) +
          eps ^ 2 *
            (kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x *
              dataCoeff A B hB APplus) +
          eps ^ 2 * kktStationarityQuadraticCoeff
            A B hB hStack b x APplus :=
      add_le_add (add_le_add le_rfl hexplicit) hstationarity'
    _ = eps * theorem20_8FirstOrderRHS A b B d x
            (lsResidualHigham A b x) APplus
            (sourceBAplus A B hB APplus) +
          eps ^ 2 *
            (kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x *
                dataCoeff A B hB APplus +
              kktStationarityQuadraticCoeff A B hB hStack b x APplus) := by
      ring

/-- One source-only neighborhood simultaneously guarantees the perturbed rank
conditions, the coupled KKT gain conditions, and the uniform local estimates
needed to make both remainder terms quadratic. -/
noncomputable def finalSmallnessThreshold {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  min (theorem20_8RankKKTSmallnessThreshold hB hStack)
    (kktLocalSmallnessThreshold hB (sourceNullIntersection hStack))

theorem finalSmallnessThreshold_pos {m n p : ℕ}
    {A : Fin m → Fin n → ℝ} {B : Fin p → Fin n → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B)
    (hApos : 0 < frobNormRect A) (hBpos : 0 < frobNormRect B) :
    0 < finalSmallnessThreshold hB hStack := by
  exact lt_min
    (theorem20_8RankKKTSmallnessThreshold_pos hB hStack hApos hBpos)
    (kktLocalSmallnessThreshold_pos hB (sourceNullIntersection hStack))

/-- Higham, 2nd ed., Theorem 20.8, equation (20.25), in a single
source-only reciprocal neighborhood.  The theorem derives the perturbed rank
conditions in (20.24) and proves the actual relative solution error is the
printed first-order coefficient plus an explicit `eps²` term. -/
theorem source_facing_firstOrder_plus_eps_sq_of_finalSmallnessThreshold
    {r p q : ℕ}
    {A ΔA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Δb : Fin (r + q) → ℝ}
    {B ΔB : Fin p → Fin (p + q) → ℝ}
    {d Δd : Fin p → ℝ} {x y : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps)
    (hsmall : eps < finalSmallnessThreshold hB hStack) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
      rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
      LSEFullRowRank (fun i j => B i j + ΔB i j) ∧
      LSEStackedFullColumnRank
          (fun i j => A i j + ΔA i j)
          (fun i j => B i j + ΔB i j) ∧
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus
          (sourceBAplus A B hB APplus) +
        eps ^ 2 *
          (kktLocalLinearBoundCoeff hB (sourceNullIntersection hStack) b x *
              dataCoeff A B hB APplus +
            kktStationarityQuadraticCoeff A B hB hStack b x APplus) := by
  have hsmallRank :
      eps < theorem20_8RankKKTSmallnessThreshold hB hStack :=
    hsmall.trans_le (min_le_left _ _)
  have hsmallLocal :
      eps < kktLocalSmallnessThreshold hB (sourceNullIntersection hStack) :=
    hsmall.trans_le (min_le_right _ _)
  rcases theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hB hStack hApos hBpos hsmallRank with
    ⟨hBsmall, hStackSmall, hKKTsmall⟩
  have hranks :=
    theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
      hB hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall
  rcases source_facing_firstOrder_plus_eps_sq_of_rank_conditions
      hx hy hB hStack hranks.1 hranks.2 hxnorm hApos hbpos hBpos hdpos hmax
      hKKTsmall hsmallLocal with
    ⟨APplus, hMP, hnull, hbound⟩
  exact ⟨APplus, hMP, hnull, hranks.1, hranks.2, hbound⟩

/-- The direct-data correction radius occurring before the final residual-gap
handoff in the proof of Theorem 20.8. -/
noncomputable def directDataCorrectionRadius {m n p : ℕ}
    (A ΔA : Fin m → Fin n → ℝ) (b Δb : Fin m → ℝ)
    (B ΔB : Fin p → Fin n → ℝ) (Δd : Fin p → ℝ)
    (hB : LSEFullRowRank B) (x y : Fin n → ℝ)
    (APplus : Fin n → Fin m → ℝ) (eps : ℝ) : ℝ :=
  (vecNorm2
        (fun j : Fin n =>
          rectMatMulVec (sourceBAplus A B hB APplus)
              (fun i : Fin p => Δd i - rectMatMulVec ΔB y i) j +
            rectMatMulVec APplus
              (fun i : Fin m => rectMatMulVec ΔA y i - Δb i) j) +
      eps * theorem20_8ResidualAmplifier A B APplus
        (sourceBAplus A B hB APplus) *
        (vecNorm2 (lsResidualHigham A b x) / frobNormRect A)) /
    vecNorm2 x

/-- Partial source-facing Theorem 20.8 support endpoint when the perturbed rank
conditions are supplied explicitly.  Its conjunction is intentionally weaker
than the printed theorem's actual-displacement first-order conclusion.

The actual minimizer displacement is controlled by the coupled KKT radius.
For the same exact minimizers and the source lifted reduced-Gram Moore--Penrose
candidate, the direct/data correction radius is bounded by Higham's exact
displayed first-order coefficient plus `explicitRemainder`.  No norm ordering
between `x` and `y`, residual-relative hypothesis, common GQR factor, or
conclusion-shaped premise is used. -/
theorem partial_source_facing_of_rank_conditions
    {r p q : ℕ}
    {A ΔA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Δb : Fin (r + q) → ℝ}
    {B ΔB : Fin p → Fin (p + q) → ℝ}
    {d Δd : Fin p → ℝ} {x y : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBpert : LSEFullRowRank (fun i j => B i j + ΔB i j))
    (_hStackPert : LSEStackedFullColumnRank
      (fun i j => A i j + ΔA i j) (fun i j => B i j + ΔB i j))
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps)
    (hsmall :
      eps < theorem20_8KKTLinearizedGainSmallnessThreshold hB
        (sourceNullIntersection hStack)) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
      rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
          theorem20_8KKTSourceResidualRatioCoupledBound hB
            (sourceNullIntersection hStack) b x eps ∧
      directDataCorrectionRadius A ΔA b Δb B ΔB Δd hB x y APplus eps ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus
          (sourceBAplus A B hB APplus) +
        explicitRemainder hB hStack b x eps APplus := by
  have heps_nonneg : 0 ≤ eps :=
    (theorem20_8MaxRelativePerturbation_nonneg A ΔA b Δb B ΔB d Δd
      hApos).trans hmax
  have hbudget :
      theorem20_8RelativePerturbationBudget A ΔA b Δb B ΔB d Δd eps :=
    theorem20_8RelativePerturbationBudget_of_maxRelativePerturbation_le
      A ΔA b Δb B ΔB d Δd hApos hbpos hBpos hdpos hmax
  have hgain :
      theorem20_8KKTSourceResidualRatioGainConditions hB
        (sourceNullIntersection hStack) eps :=
    theorem20_8KKTSourceResidualRatioGainConditions_of_linearized_smallnessThreshold
      hB (sourceNullIntersection hStack) heps_nonneg hsmall
  have hsolution :
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        theorem20_8KKTSourceResidualRatioCoupledBound hB
          (sourceNullIntersection hStack) b x eps :=
    hx.kkt_solution_difference_relative_le_theorem20_8KKTSourceResidualRatioCoupledBound_of_gainConditions
      hy hB hBpert (sourceNullIntersection hStack) hxnorm hbudget heps_nonneg
      hgain
  rcases GeneralizedQRFactorization.exists_of_fullRowRank_stackedFullColumnRank
      (A := A) (B := B) hB hStack with
    ⟨h⟩
  let APplus : Fin (p + q) → Fin (r + q) → ℝ :=
    h.liftedReducedGramAPplus
  have hMP :
      RectMoorePenrosePseudoinverse (r + q) (p + q)
        (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus := by
    dsimp [APplus]
    exact
      h.liftedReducedGramAPplus_rectMoorePenrosePseudoinverse_of_gram_projection
        hB hStack
  have hnull :
      rectMatMul B APplus =
        (fun _i : Fin p => fun _j : Fin (r + q) => 0) := by
    dsimp [APplus]
    exact h.liftedReducedGramAPplus_constraint_annihilates
  have hdirect :=
    theorem20_8_direct_data_correction_residual_relative_le_firstOrderRHS_plus_eps_radius_coefficient_of_solution_difference_relative_bound
      A ΔA b Δb B ΔB hB.rightInverse APplus d Δd y x
      (lsResidualHigham A b x) heps_nonneg hApos hbpos hBpos hdpos hxnorm
      hmax hsolution
  refine ⟨APplus, hMP, hnull, hsolution, ?_⟩
  simpa [directDataCorrectionRadius, sourceBAplus, explicitRemainder,
    dataCoeff] using hdirect

/-- Source-only reciprocal-threshold version of
`partial_source_facing_of_rank_conditions`.

The single strict inequality against `theorem20_8RankKKTSmallnessThreshold`
proves the two perturbed rank conditions in (20.24) and the KKT small-gain
condition before applying the explicit-rank theorem. -/
theorem partial_source_facing_of_rank_kkt_smallnessThreshold
    {r p q : ℕ}
    {A ΔA : Fin (r + q) → Fin (p + q) → ℝ}
    {b Δb : Fin (r + q) → ℝ}
    {B ΔB : Fin p → Fin (p + q) → ℝ}
    {d Δd : Fin p → ℝ} {x y : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer A b B d x)
    (hy : IsLSEMinimizer
      (fun i j => A i j + ΔA i j) (fun i => b i + Δb i)
      (fun i j => B i j + ΔB i j) (fun i => d i + Δd i) y)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hxnorm : 0 < vecNorm2 x)
    {eps : ℝ}
    (hApos : 0 < frobNormRect A) (hbpos : 0 < vecNorm2 b)
    (hBpos : 0 < frobNormRect B) (hdpos : 0 < vecNorm2 d)
    (hmax :
      theorem20_8MaxRelativePerturbation A ΔA b Δb B ΔB d Δd ≤ eps)
    (hsmall : eps < theorem20_8RankKKTSmallnessThreshold hB hStack) :
    ∃ APplus : Fin (p + q) → Fin (r + q) → ℝ,
      RectMoorePenrosePseudoinverse (r + q) (p + q)
          (theorem20_8AP A B (undetAplusOfGramNonsingInv B)) APplus ∧
      rectMatMul B APplus =
          (fun _i : Fin p => fun _j : Fin (r + q) => 0) ∧
      LSEFullRowRank (fun i j => B i j + ΔB i j) ∧
      LSEStackedFullColumnRank
          (fun i j => A i j + ΔA i j)
          (fun i j => B i j + ΔB i j) ∧
      vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
          theorem20_8KKTSourceResidualRatioCoupledBound hB
            (sourceNullIntersection hStack) b x eps ∧
      directDataCorrectionRadius A ΔA b Δb B ΔB Δd hB x y APplus eps ≤
        eps * theorem20_8FirstOrderRHS A b B d x
          (lsResidualHigham A b x) APplus
          (sourceBAplus A B hB APplus) +
        explicitRemainder hB hStack b x eps APplus := by
  rcases theorem20_8_rank_kkt_smallness_conditions_of_eps_lt_threshold
      hB hStack hApos hBpos hsmall with
    ⟨hBsmall, hStackSmall, hKKTsmall⟩
  have hranks :=
    theorem20_8_conditions20_24_of_maxRelativePerturbation_lt_margins
      hB hStack hApos hbpos hBpos hdpos hmax hBsmall hStackSmall
  rcases partial_source_facing_of_rank_conditions hx hy hB hStack hranks.1 hranks.2
      hxnorm hApos hbpos hBpos hdpos hmax hKKTsmall with
    ⟨APplus, hMP, hnull, hsolution, hdirect⟩
  exact
    ⟨APplus, hMP, hnull, hranks.1, hranks.2, hsolution, hdirect⟩

end Theorem20_8

end NumStability
