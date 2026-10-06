-- Combined absolute-norm fixed-point bridge for the alternative perturbation
-- bounds following Higham's Theorem 20.2.

import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators

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

/-- The entrywise-absolute inverse block displayed after Theorem 20.2:
`[[|I-AA^+|, |A^+|^T], [|A^+|, |(A^T A)^-1|]]`. -/
noncomputable def higham20AlternativeAbsInverseBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append
        (fun k : Fin m => |lsAugmentedProjectionBlock A Aplus i k|)
        (fun j : Fin n => |Aplus j i|))
    (fun j : Fin n =>
      Fin.append
        (fun i : Fin m => |Aplus j i|)
        (fun k : Fin n => |gramInv j k|))

/-- The off-diagonal componentwise data block
`[[0,E],[E^T,0]]` displayed after Theorem 20.2. -/
noncomputable def higham20AlternativeOffDiagonalBlock {m n : Nat}
    (E : Fin m -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  Fin.append
    (fun i : Fin m =>
      Fin.append (fun _ : Fin m => 0) (fun j : Fin n => E i j))
    (fun j : Fin n =>
      Fin.append (fun i : Fin m => E i j) (fun _ : Fin n => 0))

/-- The exact matrix product occurring inside the alternative-bound norm. -/
noncomputable def higham20AlternativeCouplingMatrix {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) (E : Fin m -> Fin n -> Real) :
    Fin (m + n) -> Fin (m + n) -> Real :=
  rectMatMul (higham20AlternativeAbsInverseBlock A Aplus gramInv)
    (higham20AlternativeOffDiagonalBlock E)

theorem higham20AlternativeAbsInverseBlock_mulVec {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real)
    (u : Fin m -> Real) (v : Fin n -> Real) :
    rectMatMulVec (higham20AlternativeAbsInverseBlock A Aplus gramInv)
        (Fin.append u v) =
      Fin.append (lsAugmentedEq20_7Majorant A Aplus u v)
        (lsAugmentedEq20_8Majorant Aplus gramInv u v) := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [higham20AlternativeAbsInverseBlock, rectMatMulVec,
      Fin.sum_univ_add, lsAugmentedEq20_7Majorant, absMatrixRect]
  · intro j
    simp [higham20AlternativeAbsInverseBlock, rectMatMulVec,
      Fin.sum_univ_add, lsAugmentedEq20_8Majorant, absMatrixRect,
      absMatrix, matMulVec]

theorem higham20AlternativeOffDiagonalBlock_mulVec {m n : Nat}
    (E : Fin m -> Fin n -> Real) (u : Fin m -> Real) (v : Fin n -> Real) :
    rectMatMulVec (higham20AlternativeOffDiagonalBlock E) (Fin.append u v) =
      Fin.append (rectMatMulVec E v)
        (fun j => Finset.univ.sum (fun i : Fin m => E i j * u i)) := by
  ext k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp [higham20AlternativeOffDiagonalBlock, rectMatMulVec,
      Fin.sum_univ_add]
  · intro j
    simp [higham20AlternativeOffDiagonalBlock, rectMatMulVec,
      Fin.sum_univ_add]

/-- The unperturbed-data vector used by the alternative estimate:
`[f + E|x|; E^T|r|]`. -/
noncomputable def higham20AlternativeSourceData {m n : Nat}
    (E : Fin m -> Fin n -> Real) (f r : Fin m -> Real)
    (x : Fin n -> Real) : Fin (m + n) -> Real :=
  Fin.append (lsComponentwiseDataMajorant E f x)
    (lsComponentwiseTransposeMajorant E r)

/-- Applying the absolute inverse block to the unperturbed-data vector gives
the numerator in the combined alternative estimate. -/
noncomputable def higham20AlternativeSourceResponse {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real)
    (E : Fin m -> Fin n -> Real) (f r : Fin m -> Real)
    (x : Fin n -> Real) : Fin (m + n) -> Real :=
  rectMatMulVec (higham20AlternativeAbsInverseBlock A Aplus gramInv)
    (higham20AlternativeSourceData E f r x)

theorem higham20AlternativeAbsInverseBlock_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real) :
    forall i j, 0 <= higham20AlternativeAbsInverseBlock A Aplus gramInv i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj <;>
      simp [higham20AlternativeAbsInverseBlock]
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj <;>
      simp [higham20AlternativeAbsInverseBlock]

theorem higham20AlternativeOffDiagonalBlock_nonneg {m n : Nat}
    {E : Fin m -> Fin n -> Real} (hE : forall i j, 0 <= E i j) :
    forall i j, 0 <= higham20AlternativeOffDiagonalBlock E i j := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simp [higham20AlternativeOffDiagonalBlock]
    · simpa [higham20AlternativeOffDiagonalBlock] using hE ii jj
  · intro ii j
    refine Fin.addCases ?_ ?_ j <;> intro jj
    · simpa [higham20AlternativeOffDiagonalBlock] using hE jj ii
    · simp [higham20AlternativeOffDiagonalBlock]

theorem higham20AlternativeCouplingMatrix_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real)
    {E : Fin m -> Fin n -> Real} (hE : forall i j, 0 <= E i j) :
    forall i j, 0 <= higham20AlternativeCouplingMatrix A Aplus gramInv E i j := by
  intro i j
  unfold higham20AlternativeCouplingMatrix rectMatMul
  exact Finset.sum_nonneg (fun k _ => mul_nonneg
    (higham20AlternativeAbsInverseBlock_nonneg A Aplus gramInv i k)
    (higham20AlternativeOffDiagonalBlock_nonneg hE k j))

theorem higham20AlternativeSourceData_nonneg {m n : Nat}
    {E : Fin m -> Fin n -> Real} {f r : Fin m -> Real}
    (x : Fin n -> Real) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i) :
    forall k, 0 <= higham20AlternativeSourceData E f r x k := by
  intro k
  refine Fin.addCases ?_ ?_ k
  · intro i
    simp only [higham20AlternativeSourceData, Fin.append_left,
      lsComponentwiseDataMajorant, rectMatMulVec, absVec]
    exact add_nonneg (hf i) (Finset.sum_nonneg (fun j _ =>
      mul_nonneg (hE i j) (abs_nonneg (x j))))
  · intro j
    simp only [higham20AlternativeSourceData, Fin.append_right,
      lsComponentwiseTransposeMajorant]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (hE i j) (abs_nonneg (r i)))

theorem higham20AlternativeSourceResponse_nonneg {m n : Nat}
    (A : Fin m -> Fin n -> Real) (Aplus : Fin n -> Fin m -> Real)
    (gramInv : Fin n -> Fin n -> Real)
    {E : Fin m -> Fin n -> Real} {f r : Fin m -> Real}
    (x : Fin n -> Real) (hE : forall i j, 0 <= E i j)
    (hf : forall i, 0 <= f i) :
    forall k,
      0 <= higham20AlternativeSourceResponse A Aplus gramInv E f r x k := by
  intro k
  unfold higham20AlternativeSourceResponse rectMatMulVec
  exact Finset.sum_nonneg (fun j _ => mul_nonneg
    (higham20AlternativeAbsInverseBlock_nonneg A Aplus gramInv k j)
    (higham20AlternativeSourceData_nonneg x hE hf j))

/-- Higham, 2nd ed., Chapter 20, printed page 384, the alternative
Theorem 20.2 estimate with `x` and `r` in place of `y` and `s`.

The scalar `q` is a genuine subordinate bound, in the same absolute norm, for
the exact displayed product
`[[|I-AA^+|,|A^+|^T],[|A^+|,|(A^T A)^-1|]] * [[0,E],[E^T,0]]`.
Thus the conclusion contains precisely the source factor `(1-eps*q)^-1`;
neither the fixed-point conclusion nor a bound on the actual displacement is
assumed. -/
theorem higham20_alternative_theorem20_2_combined_bound
    {m n : Nat}
    (nu : CVec (m + n) -> Real) (hnu : IsComplexVectorNorm nu)
    (habs : IsAbsoluteComplexVectorNorm nu)
    (A : Fin m -> Fin n -> Real)
    (DeltaA E : Fin m -> Fin n -> Real) (Deltab f b : Fin m -> Real)
    (r s : Fin m -> Real) (x y : Fin n -> Real) (eps q : Real)
    (hA : Function.Injective (rectMatMulVec A))
    (hExact : LSAugmentedSystem A b (0 : Fin n -> Real) r x)
    (hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n -> Real) s y)
    (hcomp : LSComponentwisePerturbation DeltaA E Deltab f eps)
    (hq : MixedSubordinateMatrixBound nu nu
      (realRectToCMatrix
        (higham20AlternativeCouplingMatrix A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) E)) q)
    (hsmall : eps * q < 1) :
    nu (realVecToComplex
        (Fin.append (fun i => s i - r i) (fun j => y j - x j))) <=
      (eps * nu (realVecToComplex
        (higham20AlternativeSourceResponse A (lsAplusOfGramNonsingInv A)
          (lsGramNonsingInv A) E f r x))) / (1 - eps * q) := by
  let Aplus := lsAplusOfGramNonsingInv A
  let gramInv := lsGramNonsingInv A
  let K := higham20AlternativeAbsInverseBlock A Aplus gramInv
  let D := higham20AlternativeOffDiagonalBlock E
  let M := higham20AlternativeCouplingMatrix A Aplus gramInv E
  let z : Fin (m + n) -> Real :=
    Fin.append (fun i => s i - r i) (fun j => y j - x j)
  let dzr : Fin m -> Real := fun i => |s i - r i|
  let dzx : Fin n -> Real := fun j => |y j - x j|
  let oldData := higham20AlternativeSourceData E f s y
  let sourceData := higham20AlternativeSourceData E f r x
  let sourceResponse :=
    higham20AlternativeSourceResponse A Aplus gramInv E f r x
  have hraw :=
    lsAugmentedEq20_7_8_abs_le_of_perturbed_systems_full_column_rank_of_componentwise_perturbation
      A DeltaA E Deltab f b r s x y eps hA hExact hPert hcomp
  rcases hcomp with ⟨heps, hE, hf, hDeltaA, hDeltab⟩
  have hy_abs (j : Fin n) : |y j| <= |x j| + dzx j := by
    calc
      |y j| = |x j + (y j - x j)| := by ring_nf
      _ <= |x j| + |y j - x j| := abs_add_le _ _
      _ = |x j| + dzx j := by rfl
  have hs_abs (i : Fin m) : |s i| <= |r i| + dzr i := by
    calc
      |s i| = |r i + (s i - r i)| := by ring_nf
      _ <= |r i| + |s i - r i| := abs_add_le _ _
      _ = |r i| + dzr i := by rfl
  have hdata_top (i : Fin m) :
      lsComponentwiseDataMajorant E f y i <=
        lsComponentwiseDataMajorant E f x i + rectMatMulVec E dzx i := by
    unfold lsComponentwiseDataMajorant rectMatMulVec absVec
    calc
      f i + Finset.univ.sum (fun j : Fin n => E i j * |y j|) <=
          f i + Finset.univ.sum
            (fun j : Fin n => E i j * (|x j| + dzx j)) := by
        exact add_le_add (le_refl (f i)) (Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hy_abs j) (hE i j)))
      _ = (f i + Finset.univ.sum (fun j : Fin n => E i j * |x j|)) +
          Finset.univ.sum (fun j : Fin n => E i j * dzx j) := by
        rw [show (fun j : Fin n => E i j * (|x j| + dzx j)) =
            fun j => E i j * |x j| + E i j * dzx j by
          funext j; ring]
        rw [Finset.sum_add_distrib]
        ring
  have hdata_bottom (j : Fin n) :
      lsComponentwiseTransposeMajorant E s j <=
        lsComponentwiseTransposeMajorant E r j +
          Finset.univ.sum (fun i : Fin m => E i j * dzr i) := by
    unfold lsComponentwiseTransposeMajorant
    calc
      Finset.univ.sum (fun i : Fin m => E i j * |s i|) <=
          Finset.univ.sum (fun i : Fin m => E i j * (|r i| + dzr i)) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hs_abs i) (hE i j)
      _ = Finset.univ.sum (fun i : Fin m => E i j * |r i|) +
          Finset.univ.sum (fun i : Fin m => E i j * dzr i) := by
        rw [show (fun i : Fin m => E i j * (|r i| + dzr i)) =
            fun i => E i j * |r i| + E i j * dzr i by
          funext i; ring]
        rw [Finset.sum_add_distrib]
  have haz : (fun k => |z k|) = Fin.append dzr dzx := by
    ext k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simp [z, dzr, Fin.append_left]
    · intro j
      simp [z, dzx, Fin.append_right]
  have hDaz :
      rectMatMulVec D (fun k => |z k|) =
        Fin.append (rectMatMulVec E dzx)
          (fun j => Finset.univ.sum (fun i : Fin m => E i j * dzr i)) := by
    rw [haz]
    exact higham20AlternativeOffDiagonalBlock_mulVec E dzr dzx
  have hdata : forall k,
      oldData k <= sourceData k + rectMatMulVec D (fun j => |z j|) k := by
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa [oldData, sourceData, higham20AlternativeSourceData,
        Fin.append_left, hDaz] using hdata_top i
    · intro j
      simpa [oldData, sourceData, higham20AlternativeSourceData,
        Fin.append_right, hDaz] using hdata_bottom j
  have hKold : forall k,
      rectMatMulVec K oldData k <=
        rectMatMulVec K
          (fun j => sourceData j + rectMatMulVec D (fun l => |z l|) j) k := by
    intro k
    unfold rectMatMulVec
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hdata j)
      (higham20AlternativeAbsInverseBlock_nonneg A Aplus gramInv k j)
  have hKold_source : forall k,
      rectMatMulVec K oldData k <=
        sourceResponse k + rectMatMulVec M (fun j => |z j|) k := by
    intro k
    calc
      rectMatMulVec K oldData k <=
          rectMatMulVec K
            (fun j => sourceData j + rectMatMulVec D (fun l => |z l|) j) k :=
        hKold k
      _ = rectMatMulVec K sourceData k +
          rectMatMulVec K (rectMatMulVec D (fun l => |z l|)) k := by
        exact congrFun (rectMatMulVec_add K sourceData
          (rectMatMulVec D (fun l => |z l|))) k
      _ = sourceResponse k + rectMatMulVec M (fun j => |z j|) k := by
        unfold sourceResponse higham20AlternativeSourceResponse M
        change rectMatMulVec K sourceData k +
            rectMatMulVec K (rectMatMulVec D (fun l => |z l|)) k =
          rectMatMulVec K sourceData k +
            rectMatMulVec (rectMatMul K D) (fun j => |z j|) k
        congr 1
        exact (congrFun (rectMatMulVec_rectMatMul K D (fun j => |z j|)) k).symm
  have hKold_action :
      rectMatMulVec K oldData =
        Fin.append
          (lsAugmentedEq20_7Majorant A Aplus
            (lsComponentwiseDataMajorant E f y)
            (lsComponentwiseTransposeMajorant E s))
          (lsAugmentedEq20_8Majorant Aplus gramInv
            (lsComponentwiseDataMajorant E f y)
            (lsComponentwiseTransposeMajorant E s)) := by
    exact higham20AlternativeAbsInverseBlock_mulVec A Aplus gramInv
      (lsComponentwiseDataMajorant E f y)
      (lsComponentwiseTransposeMajorant E s)
  have hz_old : forall k, |z k| <= eps * rectMatMulVec K oldData k := by
    intro k
    refine Fin.addCases ?_ ?_ k
    · intro i
      simpa [z, Fin.append_left, hKold_action] using hraw.1 i
    · intro j
      simpa [z, Fin.append_right, hKold_action] using hraw.2 j
  have hz : forall k,
      |z k| <= eps * (sourceResponse k + rectMatMulVec M
        (fun j => |z j|) k) := by
    intro k
    exact le_trans (hz_old k)
      (mul_le_mul_of_nonneg_left (hKold_source k) heps)
  have hM : forall i j, 0 <= M i j := by
    exact higham20AlternativeCouplingMatrix_nonneg A Aplus gramInv hE
  have hg : forall k, 0 <= sourceResponse k := by
    exact higham20AlternativeSourceResponse_nonneg A Aplus gramInv x hE hf
  have hbound :=
    higham20_alternative_bound_of_componentwise_fixed_point nu hnu habs
      M q eps hq heps hsmall z sourceResponse hM hg hz
  simpa [Aplus, gramInv, M, z, sourceResponse] using hbound

end NumStability
