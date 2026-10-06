import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.Conditioning.LinearSystems.PerronFrobenius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Toeplitz.Contracts
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
import NumStability.Source.Higham.Chapter28.Section02.RealGinibre.Asymptotics.Asymptotics

/-!
# Chapter28 Section05 TridiagonalToeplitz ToeplitzCondition

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28ToeplitzCondition` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open Filter Asymptotics

theorem opNorm2_eq_of_orthogonal_eigenbasis_attained {n : ℕ}
    (M Q : RSqMat n) (d : Fin n → ℝ)
    (hQ : IsOrthogonal n Q)
    (heig : ∀ k : Fin n,
      Matrix.mulVec M (fun i => Q i k) = d k • (fun i => Q i k))
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ k, |d k| ≤ L)
    (kmax : Fin n) (hkmax : |d kmax| = L) :
    opNorm2 M = L := by
  have hdiag :
      M = finiteMatMul Q
        (finiteMatMul (finiteDiagonal d) (matTranspose Q)) := by
    apply finiteMatrix_eq_orthogonal_diagonalization_of_eigenvector_columns hQ
    intro k
    simpa [finiteMatVec, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul] using heig k
  apply le_antisymm
  · exact opNorm2_le_of_isOrthogonal_diagonalization hdiag hQ hL hbound
  · let x : RVec n := fun i => Q i kmax
    have hx : vecNorm2 x = 1 := by
      simpa [x] using hQ.column_vecNorm2_eq_one kmax
    have hop := opNorm2Le_opNorm2 M x
    have hMx : matMulVec n M x = d kmax • x := by
      simpa [x, matMulVec, Matrix.mulVec, dotProduct] using heig kmax
    rw [hMx] at hop
    change vecNorm2 (fun i => d kmax * x i) ≤ opNorm2 M * vecNorm2 x at hop
    rw [vecNorm2_smul] at hop
    simp only [hx, mul_one] at hop
    simpa [hkmax] using hop

noncomputable def secondDifferenceAngle (n : ℕ) (k : Fin n) : ℝ :=
  ((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)

noncomputable def secondDifferenceEigenvalue (n : ℕ) (k : Fin n) : ℝ :=
  2 - 2 * Real.cos (secondDifferenceAngle n k)

theorem symmetricToeplitzEigenvalue_secondDifference {n : ℕ} (k : Fin n) :
    symmetricToeplitzEigenvalue n (-1) 2 k = secondDifferenceEigenvalue n k := by
  simp [symmetricToeplitzEigenvalue, secondDifferenceEigenvalue,
    secondDifferenceAngle]
  ring

theorem secondDifferenceAngle_pos {n : ℕ} (k : Fin n) :
    0 < secondDifferenceAngle n k := by
  unfold secondDifferenceAngle
  positivity

theorem secondDifferenceAngle_lt_pi {n : ℕ} (k : Fin n) :
    secondDifferenceAngle n k < Real.pi := by
  unfold secondDifferenceAngle
  have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [div_lt_iff₀ hden]
  have hk : (((k.val + 1 : ℕ) : ℝ)) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ k.isLt
  nlinarith [Real.pi_pos]

theorem secondDifferenceEigenvalue_pos {n : ℕ} (k : Fin n) :
    0 < secondDifferenceEigenvalue n k := by
  have ha0 : (0 : ℝ) ≤ secondDifferenceAngle n k :=
    le_of_lt (secondDifferenceAngle_pos k)
  have hapi : secondDifferenceAngle n k ≤ Real.pi :=
    le_of_lt (secondDifferenceAngle_lt_pi k)
  have hcos : Real.cos (secondDifferenceAngle n k) < 1 := by
    have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by exact ⟨le_rfl, le_of_lt Real.pi_pos⟩)
      (show secondDifferenceAngle n k ∈ Set.Icc 0 Real.pi by exact ⟨ha0, hapi⟩)
      (secondDifferenceAngle_pos k)
    simpa using h
  unfold secondDifferenceEigenvalue
  linarith

theorem secondDifferenceEigenvalue_le_last {n : ℕ} (hn : 0 < n)
    (k : Fin n) :
    secondDifferenceEigenvalue n k ≤
      secondDifferenceEigenvalue n ⟨n - 1, by omega⟩ := by
  let klast : Fin n := ⟨n - 1, by omega⟩
  have hak : 0 ≤ secondDifferenceAngle n k :=
    le_of_lt (secondDifferenceAngle_pos k)
  have halastpi : secondDifferenceAngle n klast ≤ Real.pi :=
    le_of_lt (secondDifferenceAngle_lt_pi klast)
  have hang : secondDifferenceAngle n k ≤ secondDifferenceAngle n klast := by
    unfold secondDifferenceAngle
    have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    apply (div_le_div_iff_of_pos_right hden).2
    apply mul_le_mul_of_nonneg_right _ (le_of_lt Real.pi_pos)
    exact_mod_cast (show k.val + 1 ≤ klast.val + 1 by
      dsimp [klast]
      omega)
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hak halastpi hang
  unfold secondDifferenceEigenvalue
  linarith

theorem secondDifferenceEigenvalue_last_eq {n : ℕ} (hn : 0 < n) :
    secondDifferenceEigenvalue n ⟨n - 1, by omega⟩ =
      2 + 2 * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  unfold secondDifferenceEigenvalue secondDifferenceAngle
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hangle :
      ((((n - 1 : ℕ) + 1 : ℕ) : ℝ) * Real.pi) /
          ((n + 1 : ℕ) : ℝ) =
        Real.pi - Real.pi / ((n + 1 : ℕ) : ℝ) := by
    have hnat : n - 1 + 1 = n := by omega
    rw [hnat]
    field_simp
    push_cast
    ring
  rw [hangle, Real.cos_pi_sub]
  ring

theorem secondDifferenceEigenvalue_first_le {n : ℕ} (hn : 0 < n)
    (k : Fin n) :
    secondDifferenceEigenvalue n ⟨0, hn⟩ ≤ secondDifferenceEigenvalue n k := by
  let k0 : Fin n := ⟨0, hn⟩
  have ha0 : 0 ≤ secondDifferenceAngle n k0 :=
    le_of_lt (secondDifferenceAngle_pos k0)
  have hakpi : secondDifferenceAngle n k ≤ Real.pi :=
    le_of_lt (secondDifferenceAngle_lt_pi k)
  have hang : secondDifferenceAngle n k0 ≤ secondDifferenceAngle n k := by
    unfold secondDifferenceAngle
    have hden : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    apply (div_le_div_iff_of_pos_right hden).2
    apply mul_le_mul_of_nonneg_right _ (le_of_lt Real.pi_pos)
    norm_num [k0]
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi ha0 hakpi hang
  unfold secondDifferenceEigenvalue
  linarith

noncomputable def secondDifferenceHalfAngle (n : ℕ) : ℝ :=
  Real.pi / (2 * ((n : ℝ) + 1))

theorem tendsto_secondDifferenceHalfAngle :
    Tendsto secondDifferenceHalfAngle atTop (nhds 0) := by
  have hden : Tendsto (fun n : ℕ => (2 : ℝ) * ((n : ℝ) + 1))
      atTop atTop := by
    have hncast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hadd : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      hncast.atTop_add tendsto_const_nhds
    exact hadd.const_mul_atTop (by norm_num)
  simpa [secondDifferenceHalfAngle] using
    (tendsto_const_nhds.div_atTop hden :
      Tendsto (fun n : ℕ => Real.pi / ((2 : ℝ) * ((n : ℝ) + 1)))
        atTop (nhds 0))

theorem secondDifferenceClosedForm_halfAngle (n : ℕ) :
    secondDifferenceConditionClosedForm n =
      Real.cos (secondDifferenceHalfAngle n) ^ 2 /
        Real.sin (secondDifferenceHalfAngle n) ^ 2 := by
  let x := secondDifferenceHalfAngle n
  change secondDifferenceConditionClosedForm n =
    Real.cos x ^ 2 / Real.sin x ^ 2
  have hxpos : 0 < x := by
    dsimp [x, secondDifferenceHalfAngle]
    positivity
  have hxlt : x < Real.pi := by
    dsimp [x, secondDifferenceHalfAngle]
    have hpi := Real.pi_pos
    have hden : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
      have hn : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hdenpos : 0 < 2 * ((n : ℝ) + 1) := by positivity
    rw [div_lt_iff₀ hdenpos]
    nlinarith
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxpos hxlt)
  have htheta :
      Real.pi / ((n + 1 : ℕ) : ℝ) = 2 * x := by
    dsimp [x, secondDifferenceHalfAngle]
    push_cast
    field_simp
  unfold secondDifferenceConditionClosedForm
  dsimp
  rw [htheta, Real.cos_two_mul]
  have htrig := Real.sin_sq_add_cos_sq x
  have hnum : 2 + 2 * (2 * Real.cos x ^ 2 - 1) =
      4 * Real.cos x ^ 2 := by ring
  have hden : 2 - 2 * (2 * Real.cos x ^ 2 - 1) =
      4 * Real.sin x ^ 2 := by nlinarith [htrig]
  rw [hnum, hden]
  field_simp [hsin]

theorem secondDifferenceClosedForm_isEquivalent_invHalfAngleSq :
    IsEquivalent atTop secondDifferenceConditionClosedForm
      (fun n : ℕ => (secondDifferenceHalfAngle n ^ 2)⁻¹) := by
  have hx := tendsto_secondDifferenceHalfAngle
  have hsin : IsEquivalent atTop
      (fun n : ℕ => Real.sin (secondDifferenceHalfAngle n))
      secondDifferenceHalfAngle := by
    simpa [Function.comp_def] using Real.isEquivalent_sin.comp_tendsto hx
  have hcosT : Tendsto
      (fun n : ℕ => Real.cos (secondDifferenceHalfAngle n))
      atTop (nhds 1) := by
    simpa using Real.continuous_cos.continuousAt.tendsto.comp hx
  have hcos : IsEquivalent atTop
      (fun n : ℕ => Real.cos (secondDifferenceHalfAngle n))
      (fun _ : ℕ => (1 : ℝ)) := by
    rw [isEquivalent_iff_tendsto_one (by simp)]
    convert hcosT using 1
    funext n
    simp
  have hquot := (hcos.pow 2).div (hsin.pow 2)
  apply (hquot.congr_left ?_).congr_right ?_
  · filter_upwards with n
    exact (secondDifferenceClosedForm_halfAngle n).symm
  · filter_upwards with n
    change (1 : ℝ) ^ 2 / secondDifferenceHalfAngle n ^ 2 =
      (secondDifferenceHalfAngle n ^ 2)⁻¹
    simp [div_eq_mul_inv]

theorem invSecondDifferenceHalfAngleSq_isEquivalent_model :
    IsEquivalent atTop
      (fun n : ℕ => (secondDifferenceHalfAngle n ^ 2)⁻¹)
      (fun n : ℕ => 4 * (n : ℝ) ^ 2 / Real.pi ^ 2) := by
  have htarget : ∀ᶠ n : ℕ in atTop,
      4 * (n : ℝ) ^ 2 / Real.pi ^ 2 ≠ 0 := by
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    positivity
  rw [isEquivalent_iff_tendsto_one htarget]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hratio : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ))
      atTop (nhds 1) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) + ((n : ℝ))⁻¹)
        atTop (nhds 1) := by
      simpa using tendsto_const_nhds.add hinv
    apply hbase.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    field_simp [hn0]
  have hratioSq : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / (n : ℝ)) ^ 2)
      atTop (nhds 1) := by
    simpa using hratio.pow 2
  apply hratioSq.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun _ hn => hn⟩] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  unfold secondDifferenceHalfAngle
  simp only [Pi.div_apply]
  field_simp [hn0, hpi]
  ring

end NumStability
