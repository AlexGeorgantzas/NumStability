import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section04.Pascal.PascalSpectral

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28PascalSpectral under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators Matrix.Norms.L2Operator

private theorem vecNorm2_module_smul {n : ℕ} (a : ℝ) (x : RVec n) :
    vecNorm2 (a • x) = |a| * vecNorm2 x := by
  simpa only [Pi.smul_apply, smul_eq_mul] using vecNorm2_smul a x

private theorem vecNorm2_module_neg {n : ℕ} (x : RVec n) :
    vecNorm2 (-x) = vecNorm2 x := by
  simpa only [Pi.neg_apply] using vecNorm2_neg x

/-- The smallest Pascal eigenvalue gives the exact inverse operator norm. -/
theorem opNorm2_pascalInverseMatrix_eq_inv_smallestEigenvalue (n : ℕ) :
    opNorm2 (pascalInverseMatrix (n + 1)) =
      (pascalSmallestEigenvalue n)⁻¹ := by
  let P := pascalMatrix (n + 1)
  let Pinv := pascalInverseMatrix (n + 1)
  let lam := pascalSmallestEigenvalue n
  let v := pascalSmallestEigenvector n
  have hlam : 0 < lam := pascalSmallestEigenvalue_pos n
  have hmin : ∀ i : Fin (n + 1),
      lam ≤ finiteHermitianEigenvalues P
        (pascalMatrix_isSymmetricFiniteMatrix (n + 1)) i := by
    intro i
    exact pascalSmallestEigenvalue_le n i
  have hLower : finiteLoewnerLe
      (fun i j : Fin (n + 1) => lam * finiteIdMatrix i j) P :=
    finiteLoewnerLe_smul_id_of_le_finiteHermitianEigenvalues
      P (pascalMatrix_isSymmetricFiniteMatrix (n + 1)) hmin
  have hRight : IsRightInverse (n + 1) P Pinv :=
    (pascalMatrix_pascalInverseMatrix_isInverse (n + 1)).2
  have hPinvUpper : finiteLoewnerLe Pinv
      (fun i j : Fin (n + 1) => lam⁻¹ * finiteIdMatrix i j) :=
    finiteLoewnerLe_right_inverse_upper_of_smul_id_le
      P Pinv hlam hLower hRight
  have hInvNonneg : 0 ≤ lam⁻¹ := le_of_lt (inv_pos.mpr hlam)
  have hOpLePred : finiteOpNorm2Le Pinv lam⁻¹ :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
      Pinv hInvNonneg
      (pascalInverseMatrix_isSymmetricFiniteMatrix (n + 1))
      (pascalInverseMatrix_finitePSD (n + 1)) hPinvUpper
  have hUpper : opNorm2 Pinv ≤ lam⁻¹ :=
    opNorm2_le_of_finiteOpNorm2Le Pinv hInvNonneg hOpLePred
  have hvunit : vecNorm2 v = 1 := vecNorm2_pascalSmallestEigenvector n
  have heig : Matrix.mulVec P v = lam • v :=
    pascalMatrix_mulVec_smallestEigenvector n
  have hPinvEig : Matrix.mulVec Pinv v = lam⁻¹ • v := by
    have h := congrArg (fun z => Matrix.mulVec Pinv z) heig
    change Matrix.mulVec Pinv (Matrix.mulVec P v) =
      Matrix.mulVec Pinv (lam • v) at h
    have hInvP : (Pinv : RSqMat (n + 1)) * P = 1 := by
      simpa [P, Pinv, pascalInverseMatrix] using signedGram_mul_pascalMatrix (n + 1)
    have hscaled : Matrix.mulVec Pinv (lam • v) =
        lam • Matrix.mulVec Pinv v := by
      exact Matrix.mulVec_smul _ _ _
    rw [Matrix.mulVec_mulVec, hInvP, Matrix.one_mulVec, hscaled] at h
    ext i
    have hi := congrFun h i
    simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
    calc
      Matrix.mulVec Pinv v i = lam⁻¹ * (lam * Matrix.mulVec Pinv v i) := by
        field_simp [ne_of_gt hlam]
      _ = lam⁻¹ * v i := by rw [← hi]
  have hAction := opNorm2Le_opNorm2 Pinv v
  change vecNorm2 (Matrix.mulVec Pinv v) ≤ opNorm2 Pinv * vecNorm2 v at hAction
  rw [hPinvEig, vecNorm2_module_smul, hvunit] at hAction
  have hLowerNorm : lam⁻¹ ≤ opNorm2 Pinv := by
    simpa [abs_of_pos (inv_pos.mpr hlam)] using hAction
  exact le_antisymm hUpper hLowerNorm

/-- Exact operator norm of the optimal rank-one perturbation. -/
theorem opNorm2_pascalOptimalSingularizingPerturbation (n : ℕ) :
    opNorm2 (pascalOptimalSingularizingPerturbation n) =
      pascalSmallestEigenvalue n := by
  let lam := pascalSmallestEigenvalue n
  let v := pascalSmallestEigenvector n
  have hlam : 0 ≤ lam := le_of_lt (pascalSmallestEigenvalue_pos n)
  have hv : vecNorm2 v = 1 := vecNorm2_pascalSmallestEigenvector n
  have hEq : pascalOptimalSingularizingPerturbation n =
      residualRankOnePerturbation (n + 1) (-lam • v) v := by
    have hvsq : vecNorm2Sq v = 1 := by
      rw [← vecNorm2_sq, hv]
      norm_num
    ext i j
    simp [pascalOptimalSingularizingPerturbation,
      residualRankOnePerturbation, hvsq, lam, v]
  have hPred := opNorm2Le_residualRankOnePerturbation
    (n + 1) (-lam • v) v (by simpa [hv])
  have hratio : vecNorm2 (-lam • v) / vecNorm2 v = lam := by
    rw [vecNorm2_module_smul, hv]
    simp [abs_of_nonneg hlam]
  rw [hratio] at hPred
  have hUpper : opNorm2 (pascalOptimalSingularizingPerturbation n) ≤ lam := by
    rw [hEq]
    apply opNorm2_le_of_opNorm2Le _ hlam
    exact hPred
  have hAction := opNorm2Le_opNorm2
    (pascalOptimalSingularizingPerturbation n) v
  have hmul := pascalOptimalSingularizingPerturbation_mulVec n
  change Matrix.mulVec (pascalOptimalSingularizingPerturbation n) v =
      -(lam • v) at hmul
  change vecNorm2 (Matrix.mulVec
      (pascalOptimalSingularizingPerturbation n) v) ≤
    opNorm2 (pascalOptimalSingularizingPerturbation n) * vecNorm2 v at hAction
  rw [hmul, vecNorm2_module_neg, vecNorm2_module_smul, hv] at hAction
  have hLower : lam ≤ opNorm2 (pascalOptimalSingularizingPerturbation n) := by
    simpa [abs_of_nonneg hlam] using hAction
  exact le_antisymm hUpper hLower

/-- Every perturbation that makes the Pascal matrix singular has norm at
least the reciprocal norm of its explicit inverse. -/
theorem pascal_singularizing_perturbation_norm_lower_bound
    (n : ℕ) (E : RSqMat (n + 1))
    (hsing : ∃ z : RVec (n + 1), z ≠ 0 ∧
      Matrix.mulVec (pascalMatrix (n + 1) + E) z = 0) :
    (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ ≤ opNorm2 E := by
  obtain ⟨z, hz, hkernel⟩ := hsing
  have hznorm : 0 < vecNorm2 z := by
    have hne : vecNorm2 z ≠ 0 := by
      intro hzero
      apply hz
      funext i
      exact (vecNorm2_eq_zero_iff z).mp hzero i
    exact lt_of_le_of_ne (vecNorm2_nonneg z) (Ne.symm hne)
  let y : RVec (n + 1) := fun i => (vecNorm2 z)⁻¹ * z i
  have hyunit : vecNorm2 y = 1 := vecNorm2_inv_smul_self_of_pos z hznorm
  have hcancel : Matrix.mulVec (pascalMatrix (n + 1)) y =
      -Matrix.mulVec E y := by
    have hk : Matrix.mulVec (pascalMatrix (n + 1)) z =
        -Matrix.mulVec E z := by
      rw [Matrix.add_mulVec] at hkernel
      exact eq_neg_of_add_eq_zero_left hkernel
    have hy : y = (vecNorm2 z)⁻¹ • z := by
      ext i
      simp [y]
    rw [hy, Matrix.mulVec_smul, Matrix.mulVec_smul, hk]
    simp
  have hLower := opNorm2_inv_recip_le_vecNorm2_matMulVec_of_isRightInverse
    (pascalMatrix (n + 1)) (pascalInverseMatrix (n + 1))
    (pascalMatrix_pascalInverseMatrix_isInverse (n + 1)).2 hyunit
  have hUpper := opNorm2Le_opNorm2 E y
  change (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ ≤
    vecNorm2 (Matrix.mulVec (pascalMatrix (n + 1)) y) at hLower
  change vecNorm2 (Matrix.mulVec E y) ≤ opNorm2 E * vecNorm2 y at hUpper
  rw [hcancel, vecNorm2_module_neg] at hLower
  rw [hyunit, mul_one] at hUpper
  exact hLower.trans hUpper

/-- The rank-one eigenvector perturbation attains the exact distance to
singularity in operator 2-norm. -/
theorem pascalOptimalPerturbation_is_operator2_minimal (n : ℕ) :
    opNorm2 (pascalOptimalSingularizingPerturbation n) =
        (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ ∧
      ∀ E : RSqMat (n + 1),
        (∃ z : RVec (n + 1), z ≠ 0 ∧
          Matrix.mulVec (pascalMatrix (n + 1) + E) z = 0) →
        opNorm2 (pascalOptimalSingularizingPerturbation n) ≤ opNorm2 E := by
  have hInv := opNorm2_pascalInverseMatrix_eq_inv_smallestEigenvalue n
  have hlam := pascalSmallestEigenvalue_pos n
  have hnorm := opNorm2_pascalOptimalSingularizingPerturbation n
  have hvalue : opNorm2 (pascalOptimalSingularizingPerturbation n) =
      (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ := by
    calc
      opNorm2 (pascalOptimalSingularizingPerturbation n) =
          pascalSmallestEigenvalue n := hnorm
      _ = ((pascalSmallestEigenvalue n)⁻¹)⁻¹ :=
          (inv_inv (pascalSmallestEigenvalue n)).symm
      _ = (opNorm2 (pascalInverseMatrix (n + 1)))⁻¹ := by rw [hInv]
  constructor
  · exact hvalue
  · intro E hsing
    rw [hvalue]
    exact pascal_singularizing_perturbation_norm_lower_bound n E hsing

end NumStability
