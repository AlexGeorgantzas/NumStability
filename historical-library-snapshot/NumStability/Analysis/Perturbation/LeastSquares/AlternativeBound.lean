import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.SingularValues.Realification
import NumStability.Analysis.VectorNorms.Basic

namespace NumStability

open scoped BigOperators

/-!
# AlternativeBound

Canonical reusable module extracted without change from Higham20AlternativeBound.
-/

/-- Higham, 2nd ed., Chapter 20, printed page 384, alternative-bound
denominator: a componentwise perturbation inequality

`|z| <= eps (g + M |z|)`

in any absolute vector norm yields the factor
`(1 - eps ||M||)^{-1}`.  The matrix-norm premise is the repository's genuine
subordinate-bound predicate for the same vector norm; it is not an assumed
conclusion about `z`.

This is the combined `(m+n)`-dimensional norm bridge needed before the source
block inverse and off-diagonal data matrix are instantiated. -/
theorem higham20_alternative_bound_of_componentwise_fixed_point
    {N : Nat}
    (nu : CVec N -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (M : Fin N -> Fin N -> Real) (q eps : Real)
    (hq : MixedSubordinateMatrixBound nu nu (realRectToCMatrix M) q)
    (heps : 0 <= eps) (hsmall : eps * q < 1)
    (z g : Fin N -> Real)
    (hM : forall i j, 0 <= M i j) (hg : forall i, 0 <= g i)
    (hz : forall i,
      |z i| <= eps * (g i + rectMatMulVec M (fun j => |z j|) i)) :
    nu (realVecToComplex z) <=
      (eps * nu (realVecToComplex g)) / (1 - eps * q) := by
  let az : Fin N -> Real := fun j => |z j|
  let Maz : Fin N -> Real := rectMatMulVec M az
  have hMaz : forall i, 0 <= Maz i := by
    intro i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hM i j) (abs_nonneg (z j)))
  have hmajor_nonneg : forall i, 0 <= eps * (g i + Maz i) := by
    intro i
    exact mul_nonneg heps (add_nonneg (hg i) (hMaz i))
  have hpoint : forall i, |z i| <= eps * (g i + Maz i) := by
    intro i
    simpa [Maz, az] using hz i
  have hmono :
      nu (realVecToComplex z) <=
        nu (realVecToComplex (fun i => eps * (g i + Maz i))) :=
    realVecToComplex_norm_le_of_abs_le hnu habs hmajor_nonneg hpoint
  have hscale :
      nu (realVecToComplex (fun i => eps * (g i + Maz i))) =
        eps * nu (realVecToComplex (fun i => g i + Maz i)) :=
    realVecToComplex_norm_smul_nonneg hnu eps heps _
  have htri :
      nu (realVecToComplex (fun i => g i + Maz i)) <=
        nu (realVecToComplex g) + nu (realVecToComplex Maz) :=
    realVecToComplex_norm_add_le hnu g Maz
  have hmap :
      complexMatrixVecMul (realRectToCMatrix M) (realVecToComplex az) =
        realVecToComplex Maz := by
    ext i
    simp [complexMatrixVecMul, realRectToCMatrix, realVecToComplex,
      rectMatMulVec, Maz, az]
  have habs_z : nu (realVecToComplex az) = nu (realVecToComplex z) := by
    have habsvec :
        complexAbsVec (realVecToComplex z) = realVecToComplex az := by
      ext i
      simp [complexAbsVec, realVecToComplex, az, Real.norm_eq_abs]
    exact (congrArg nu habsvec).symm.trans (habs (realVecToComplex z))
  have hmatrix :
      nu (realVecToComplex Maz) <= q * nu (realVecToComplex z) := by
    have h := hq (realVecToComplex az)
    rw [hmap, habs_z] at h
    exact h
  have hcombined :
      nu (realVecToComplex z) <=
        eps * (nu (realVecToComplex g) + q * nu (realVecToComplex z)) := by
    calc
      nu (realVecToComplex z)
          <= nu (realVecToComplex (fun i => eps * (g i + Maz i))) := hmono
      _ = eps * nu (realVecToComplex (fun i => g i + Maz i)) := hscale
      _ <= eps * (nu (realVecToComplex g) + nu (realVecToComplex Maz)) :=
        mul_le_mul_of_nonneg_left htri heps
      _ <= eps *
          (nu (realVecToComplex g) + q * nu (realVecToComplex z)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add (le_refl (nu (realVecToComplex g))) hmatrix) heps
  have hden : 0 < 1 - eps * q := by linarith
  apply (le_div_iff₀ hden).2
  have hz_nonneg : 0 <= nu (realVecToComplex z) := hnu.nonneg _
  have hg_nonneg : 0 <= nu (realVecToComplex g) := hnu.nonneg _
  nlinarith

end NumStability
