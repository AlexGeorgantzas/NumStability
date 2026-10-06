import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section05.TridiagonalToeplitz.SineEigenvectors
import NumStability.Source.Higham.Chapter28.Section05.TridiagonalToeplitz.ToeplitzCondition

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28ToeplitzCondition under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open Filter Asymptotics

theorem opNorm2_secondDifference_eq {n : ℕ} (hn : 0 < n) :
    opNorm2 (tridiagonalToeplitz n (-1) 2 (-1)) =
      2 + 2 * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ)) := by
  let Q := higham9_12_sineMatrix n
  let kmax : Fin n := ⟨n - 1, by omega⟩
  have hQ : IsOrthogonal n Q := higham9_sineMatrix_isOrthogonal hn
  have heig : ∀ k : Fin n,
      Matrix.mulVec (tridiagonalToeplitz n (-1) 2 (-1)) (fun i => Q i k) =
        secondDifferenceEigenvalue n k • (fun i => Q i k) := by
    intro k
    simpa [Q, symmetricToeplitzEigenvalue_secondDifference] using
      symmetricToeplitz_scaled_sine_eigenpair (-1) 2 k
  have hlastPos : 0 < secondDifferenceEigenvalue n kmax :=
    secondDifferenceEigenvalue_pos kmax
  have hbound : ∀ k : Fin n,
      |secondDifferenceEigenvalue n k| ≤
        secondDifferenceEigenvalue n kmax := by
    intro k
    rw [abs_of_pos (secondDifferenceEigenvalue_pos k)]
    exact secondDifferenceEigenvalue_le_last hn k
  have hop := opNorm2_eq_of_orthogonal_eigenbasis_attained
    (tridiagonalToeplitz n (-1) 2 (-1)) Q
    (secondDifferenceEigenvalue n) hQ heig
    (secondDifferenceEigenvalue n kmax) (le_of_lt hlastPos) hbound kmax
    (abs_of_pos hlastPos)
  rw [hop]
  exact secondDifferenceEigenvalue_last_eq hn

theorem secondDifferenceInverse_scaled_sine_eigenpair {n : ℕ} (k : Fin n) :
    Matrix.mulVec (secondDifferenceInverse n)
        (fun i => higham9_12_sineMatrix n i k) =
      (secondDifferenceEigenvalue n k)⁻¹ •
        (fun i => higham9_12_sineMatrix n i k) := by
  let A : RSqMat n := tridiagonalToeplitz n (-1) 2 (-1)
  let B : RSqMat n := secondDifferenceInverse n
  let v : RVec n := fun i => higham9_12_sineMatrix n i k
  let lambda := secondDifferenceEigenvalue n k
  have heig : Matrix.mulVec A v = lambda • v := by
    simpa [A, v, lambda, symmetricToeplitzEigenvalue_secondDifference] using
      symmetricToeplitz_scaled_sine_eigenpair (-1) 2 k
  have hBA : B * A = (1 : RSqMat n) := by
    simpa [A, B] using secondDifferenceInverse_mul_tridiagonalToeplitz n
  have hleft : Matrix.mulVec B (Matrix.mulVec A v) = v := by
    calc
      Matrix.mulVec B (Matrix.mulVec A v) = Matrix.mulVec (B * A) v :=
        Matrix.mulVec_mulVec v B A
      _ = v := by rw [hBA, Matrix.one_mulVec]
  rw [heig, Matrix.mulVec_smul] at hleft
  have hlambda : lambda ≠ 0 :=
    ne_of_gt (secondDifferenceEigenvalue_pos k)
  funext i
  have hi := congrFun hleft i
  change lambda * Matrix.mulVec B v i = v i at hi
  change Matrix.mulVec B v i = lambda⁻¹ * v i
  field_simp [hlambda]
  simpa [mul_comm] using hi

theorem opNorm2_secondDifferenceInverse_eq {n : ℕ} (hn : 0 < n) :
    opNorm2 (secondDifferenceInverse n) =
      (2 - 2 * Real.cos (Real.pi / ((n + 1 : ℕ) : ℝ)))⁻¹ := by
  let Q := higham9_12_sineMatrix n
  let k0 : Fin n := ⟨0, hn⟩
  have hQ : IsOrthogonal n Q := higham9_sineMatrix_isOrthogonal hn
  have heig : ∀ k : Fin n,
      Matrix.mulVec (secondDifferenceInverse n) (fun i => Q i k) =
        (secondDifferenceEigenvalue n k)⁻¹ • (fun i => Q i k) := by
    intro k
    simpa [Q] using secondDifferenceInverse_scaled_sine_eigenpair k
  have hfirstPos : 0 < secondDifferenceEigenvalue n k0 :=
    secondDifferenceEigenvalue_pos k0
  have hbound : ∀ k : Fin n,
      |(secondDifferenceEigenvalue n k)⁻¹| ≤
        (secondDifferenceEigenvalue n k0)⁻¹ := by
    intro k
    rw [abs_of_pos (inv_pos.mpr (secondDifferenceEigenvalue_pos k))]
    exact inv_anti₀ hfirstPos
      (secondDifferenceEigenvalue_first_le hn k)
  have hop := opNorm2_eq_of_orthogonal_eigenbasis_attained
    (secondDifferenceInverse n) Q
    (fun k => (secondDifferenceEigenvalue n k)⁻¹) hQ heig
    (secondDifferenceEigenvalue n k0)⁻¹ (le_of_lt (inv_pos.mpr hfirstPos))
    hbound k0 (abs_of_pos (inv_pos.mpr hfirstPos))
  rw [hop]
  congr 1
  simp [secondDifferenceEigenvalue, secondDifferenceAngle, k0]

theorem secondDifferenceConditionTwo_eq_closedForm {n : ℕ} (hn : 0 < n) :
    secondDifferenceConditionTwo n = secondDifferenceConditionClosedForm n := by
  unfold secondDifferenceConditionTwo secondDifferenceConditionClosedForm
  rw [opNorm2_secondDifference_eq hn,
    opNorm2_secondDifferenceInverse_eq hn]
  rfl

theorem secondDifferenceConditionAsymptotic_proved :
    SecondDifferenceConditionAsymptotic := by
  unfold SecondDifferenceConditionAsymptotic
  have h := secondDifferenceClosedForm_isEquivalent_invHalfAngleSq.trans
    invSecondDifferenceHalfAngleSq_isEquivalent_model
  apply h.congr_left
  filter_upwards [eventually_atTop.2 ⟨(1 : ℕ), fun _ hn => hn⟩] with n hn
  exact (secondDifferenceConditionTwo_eq_closedForm
    (lt_of_lt_of_le Nat.zero_lt_one hn)).symm

end NumStability
