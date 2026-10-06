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

/-!
# Chapter28 Section04 ReciprocalSpectrumSPD ReciprocalSPD

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28ReciprocalSPD` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open scoped BigOperators

noncomputable def higham28SignDiagonal {n : ℕ} (d : Fin n → ℝ) : RSqMat n :=
  Matrix.diagonal d

noncomputable def higham28ReciprocalInvolution {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) : RSqMat n :=
  Z * higham28SignDiagonal d * Z⁻¹

noncomputable def higham28ReciprocalSPD {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) : RSqMat n :=
  (higham28ReciprocalInvolution Z d).transpose *
    higham28ReciprocalInvolution Z d

theorem higham28SignDiagonal_sq {n : ℕ} (d : Fin n → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    higham28SignDiagonal d * higham28SignDiagonal d = (1 : RSqMat n) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [higham28SignDiagonal, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_single i]
    · rcases hd i with hi | hi <;> simp [hi]
    · intro b _ hbi
      simp [hbi]
    · simp
  · simp only [higham28SignDiagonal, Matrix.mul_apply, Matrix.diagonal_apply]
    rw [Finset.sum_eq_zero]
    · simp [hij]
    · intro k _
      by_cases hik : i = k
      · subst k
        simp [hij]
      · simp [hik]

theorem higham28ReciprocalInvolution_sq {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    higham28ReciprocalInvolution Z d *
        higham28ReciprocalInvolution Z d = (1 : RSqMat n) := by
  let D := higham28SignDiagonal d
  have hD : D * D = (1 : RSqMat n) := by
    simpa [D] using higham28SignDiagonal_sq d hd
  have hZiZ : Z⁻¹ * Z = (1 : RSqMat n) := Matrix.nonsing_inv_mul Z hZ
  have hZZi : Z * Z⁻¹ = (1 : RSqMat n) := Matrix.mul_nonsing_inv Z hZ
  unfold higham28ReciprocalInvolution
  change (Z * D * Z⁻¹) * (Z * D * Z⁻¹) = _
  calc
    (Z * D * Z⁻¹) * (Z * D * Z⁻¹) =
        Z * D * (Z⁻¹ * Z) * D * Z⁻¹ := by noncomm_ring
    _ = Z * D * D * Z⁻¹ := by rw [hZiZ]; simp
    _ = Z * (D * D) * Z⁻¹ := by noncomm_ring
    _ = Z * Z⁻¹ := by rw [hD]; simp
    _ = 1 := hZZi

theorem higham28ReciprocalSPD_transpose {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) :
    (higham28ReciprocalSPD Z d).transpose =
      higham28ReciprocalSPD Z d := by
  simp [higham28ReciprocalSPD, Matrix.transpose_mul]

theorem higham28ReciprocalSPD_det_one {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    Matrix.det (higham28ReciprocalSPD Z d) = 1 := by
  let X := higham28ReciprocalInvolution Z d
  have hXsq : X * X = (1 : RSqMat n) := by
    simpa [X] using higham28ReciprocalInvolution_sq Z d hZ hd
  have hdetSq : Matrix.det X * Matrix.det X = 1 := by
    have := congrArg Matrix.det hXsq
    simpa [Matrix.det_mul] using this
  simp only [higham28ReciprocalSPD, Matrix.det_mul, Matrix.det_transpose]
  exact hdetSq

theorem higham28ReciprocalSPD_quadratic_eq_sum_sq {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ) (v : RVec n) :
    (∑ i : Fin n, ∑ j : Fin n,
      v i * higham28ReciprocalSPD Z d i j * v j) =
      ∑ k : Fin n,
        (Matrix.mulVec (higham28ReciprocalInvolution Z d) v k) ^ 2 := by
  let X := higham28ReciprocalInvolution Z d
  change (∑ i : Fin n, ∑ j : Fin n,
      v i * (X.transpose * X) i j * v j) =
      ∑ k : Fin n, (Matrix.mulVec X v k) ^ 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        v i * (X k i * X k j) * v j) =
      ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n,
        v i * (X k i * X k j) * v j := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
        v i * (X k i * X k j) * v j := by
          rw [Finset.sum_comm]
    _ = ∑ k : Fin n, (∑ j : Fin n, X k j * v j) ^ 2 := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring

theorem higham28ReciprocalInvolution_mulVec_injective {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    Function.Injective (Matrix.mulVec (higham28ReciprocalInvolution Z d)) := by
  let X := higham28ReciprocalInvolution Z d
  have hXsq : X * X = (1 : RSqMat n) := by
    simpa [X] using higham28ReciprocalInvolution_sq Z d hZ hd
  intro v w hvw
  change Matrix.mulVec X v = Matrix.mulVec X w at hvw
  have := congrArg (Matrix.mulVec X) hvw
  simpa [Matrix.mulVec_mulVec, hXsq] using this

theorem higham28ReciprocalSPD_quadratic_pos {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (v : RVec n) (hv : ∃ i, v i ≠ 0) :
    0 < ∑ i : Fin n, ∑ j : Fin n,
      v i * higham28ReciprocalSPD Z d i j * v j := by
  rw [higham28ReciprocalSPD_quadratic_eq_sum_sq]
  have hv0 : v ≠ 0 := by
    intro h
    obtain ⟨i, hi⟩ := hv
    exact hi (congrFun h i)
  let X := higham28ReciprocalInvolution Z d
  have hXv0 : Matrix.mulVec X v ≠ 0 := by
    intro h
    exact hv0 ((higham28ReciprocalInvolution_mulVec_injective Z d hZ hd)
      (h.trans (Matrix.mulVec_zero X).symm))
  have hex : ∃ i, Matrix.mulVec X v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hXv0 (funext h)
  obtain ⟨i, hi⟩ := hex
  refine Finset.sum_pos' (fun k _ => sq_nonneg _) ?_
  exact ⟨i, Finset.mem_univ i,
    (sq_nonneg (Matrix.mulVec X v i)).lt_of_ne
      (Ne.symm (pow_ne_zero 2 hi))⟩

theorem higham28ReciprocalSPD_isSymPosDef_explicit {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    (∀ i j : Fin n,
      higham28ReciprocalSPD Z d i j = higham28ReciprocalSPD Z d j i) ∧
      ∀ v : RVec n, (∃ i, v i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n,
          v i * higham28ReciprocalSPD Z d i j * v j := by
  constructor
  · intro i j
    have h := congrArg (fun M : RSqMat n => M i j)
      (higham28ReciprocalSPD_transpose Z d)
    simpa [Matrix.transpose_apply] using h.symm
  · exact higham28ReciprocalSPD_quadratic_pos Z d hZ hd

/-- Corrected row-scaling identity: left multiplication by the sign diagonal
preserves the Gram matrix defining `A`.  No triangularity is needed. -/
theorem higham28ReciprocalSPD_row_sign_factorization {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    let R := higham28SignDiagonal d *
      higham28ReciprocalInvolution Z d
    R.transpose * R = higham28ReciprocalSPD Z d := by
  let D := higham28SignDiagonal d
  let X := higham28ReciprocalInvolution Z d
  have hDD : D * D = (1 : RSqMat n) := by
    simpa [D] using higham28SignDiagonal_sq d hd
  have hDt : D.transpose = D := by
    simp [D, higham28SignDiagonal]
  change (D * X).transpose * (D * X) = X.transpose * X
  rw [Matrix.transpose_mul, hDt]
  calc
    (X.transpose * D) * (D * X) = X.transpose * (D * D) * X := by
      noncomm_ring
    _ = X.transpose * X := by rw [hDD]; simp

/-- Equivalent transpose/column-scaling identity.  The valid right scaling is
of `Xᵀ`, not of `X`: `(Xᵀ D)(Xᵀ D)ᵀ = A`. -/
theorem higham28ReciprocalSPD_transpose_column_sign_factorization {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hd : ∀ i, d i = 1 ∨ d i = -1) :
    let L := (higham28ReciprocalInvolution Z d).transpose *
      higham28SignDiagonal d
    L * L.transpose = higham28ReciprocalSPD Z d := by
  let D := higham28SignDiagonal d
  let X := higham28ReciprocalInvolution Z d
  have hDD : D * D = (1 : RSqMat n) := by
    simpa [D] using higham28SignDiagonal_sq d hd
  have hDt : D.transpose = D := by
    simp [D, higham28SignDiagonal]
  change (X.transpose * D) * (X.transpose * D).transpose = X.transpose * X
  rw [Matrix.transpose_mul, hDt, Matrix.transpose_transpose]
  calc
    (X.transpose * D) * (D * X) = X.transpose * (D * D) * X := by
      noncomm_ring
    _ = X.transpose * X := by rw [hDD]; simp

noncomputable def higham28ColumnScalingCounterZ : RSqMat 2 :=
  ![![(1 : ℝ), 0], ![1, 1]]

noncomputable def higham28ColumnScalingCounterZInv : RSqMat 2 :=
  ![![(1 : ℝ), 0], ![-1, 1]]

noncomputable def higham28ColumnScalingCounterSigns : Fin 2 → ℝ :=
  ![(1 : ℝ), -1]

noncomputable def higham28ColumnScalingCounterX : RSqMat 2 :=
  ![![(1 : ℝ), 0], ![2, -1]]

theorem higham28ColumnScalingCounterZ_lower :
    ∀ i j : Fin 2, i < j → higham28ColumnScalingCounterZ i j = 0 := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [higham28ColumnScalingCounterZ]

theorem higham28ColumnScalingCounterZ_det_isUnit :
    IsUnit (Matrix.det higham28ColumnScalingCounterZ) := by
  apply isUnit_iff_ne_zero.mpr
  norm_num [higham28ColumnScalingCounterZ, Matrix.det_fin_two]

theorem higham28ColumnScalingCounterSigns_pm_one :
    ∀ i, higham28ColumnScalingCounterSigns i = 1 ∨
      higham28ColumnScalingCounterSigns i = -1 := by
  intro i
  fin_cases i <;> simp [higham28ColumnScalingCounterSigns]

theorem higham28ColumnScalingCounterZ_inv :
    higham28ColumnScalingCounterZ⁻¹ = higham28ColumnScalingCounterZInv := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham28ColumnScalingCounterZ,
      higham28ColumnScalingCounterZInv, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

theorem higham28ColumnScalingCounter_involution :
    higham28ReciprocalInvolution higham28ColumnScalingCounterZ
      higham28ColumnScalingCounterSigns = higham28ColumnScalingCounterX := by
  unfold higham28ReciprocalInvolution
  rw [higham28ColumnScalingCounterZ_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [higham28SignDiagonal,
      higham28ColumnScalingCounterZ, higham28ColumnScalingCounterSigns,
      higham28ColumnScalingCounterX, higham28ColumnScalingCounterZInv,
      Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Literal right/column scaling of `X` by the source sign diagonal changes the
off-diagonal signs of its Gram matrix in this nonsingular lower-triangular
example, so it is not a factorization of the printed `A = XᵀX`. -/
theorem higham28ColumnScalingCounter_right_scaling_fails :
    let X := higham28ReciprocalInvolution higham28ColumnScalingCounterZ
      higham28ColumnScalingCounterSigns
    let D := higham28SignDiagonal higham28ColumnScalingCounterSigns
    (X * D).transpose * (X * D) ≠
      higham28ReciprocalSPD higham28ColumnScalingCounterZ
        higham28ColumnScalingCounterSigns := by
  dsimp only
  intro h
  unfold higham28ReciprocalSPD at h
  rw [higham28ColumnScalingCounter_involution] at h
  have h01 := congrArg (fun M : RSqMat 2 => M 0 1) h
  norm_num [higham28SignDiagonal, higham28ColumnScalingCounterSigns,
    higham28ColumnScalingCounterX, Matrix.mul_apply, Fin.sum_univ_two] at h01

theorem higham28ReciprocalSPD_reciprocal_eigenpair {n : ℕ}
    (Z : RSqMat n) (d : Fin n → ℝ)
    (hZ : IsUnit (Matrix.det Z))
    (hd : ∀ i, d i = 1 ∨ d i = -1)
    (lambda : ℝ) (v : RVec n)
    (hlambda : lambda ≠ 0) (hv : v ≠ 0)
    (heigen : Matrix.mulVec (higham28ReciprocalSPD Z d) v = lambda • v) :
    let w := Matrix.mulVec (higham28ReciprocalInvolution Z d) v
    w ≠ 0 ∧
      Matrix.mulVec (higham28ReciprocalSPD Z d) w = lambda⁻¹ • w := by
  let X := higham28ReciprocalInvolution Z d
  let A := higham28ReciprocalSPD Z d
  let B := X * X.transpose
  let w := Matrix.mulVec X v
  have hXsq : X * X = (1 : RSqMat n) := by
    simpa [X] using higham28ReciprocalInvolution_sq Z d hZ hd
  have hAw : A * B = (1 : RSqMat n) := by
    change (X.transpose * X) * (X * X.transpose) = _
    calc
      (X.transpose * X) * (X * X.transpose) =
          X.transpose * (X * X) * X.transpose := by noncomm_ring
      _ = X.transpose * X.transpose := by rw [hXsq]; simp
      _ = (X * X).transpose := by rw [Matrix.transpose_mul]
      _ = 1 := by rw [hXsq]; simp
  have hsim : X * A * X = B := by
    change X * (X.transpose * X) * X = X * X.transpose
    calc
      X * (X.transpose * X) * X = X * X.transpose * (X * X) := by
        noncomm_ring
      _ = X * X.transpose := by rw [hXsq]; simp
  have hXw : Matrix.mulVec X w = v := by
    rw [show w = Matrix.mulVec X v by rfl, Matrix.mulVec_mulVec, hXsq,
      Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    rw [← hXw, hw0]
    simp
  have heigenA : Matrix.mulVec A v = lambda • v := by
    simpa [A] using heigen
  have hBw : Matrix.mulVec B w = lambda • w := by
    calc
      Matrix.mulVec B w = Matrix.mulVec (X * A * X) w := by rw [hsim]
      _ = Matrix.mulVec (X * A) (Matrix.mulVec X w) := by
        exact (Matrix.mulVec_mulVec w (X * A) X).symm
      _ = Matrix.mulVec X (Matrix.mulVec A (Matrix.mulVec X w)) := by
        exact (Matrix.mulVec_mulVec (Matrix.mulVec X w) X A).symm
      _ = Matrix.mulVec X (Matrix.mulVec A v) := by rw [hXw]
      _ = Matrix.mulVec X (lambda • v) := by rw [heigenA]
      _ = lambda • w := by rw [Matrix.mulVec_smul]
  have happly := congrArg (Matrix.mulVec A) hBw
  have hscale : w = lambda • Matrix.mulVec A w := by
    simpa [Matrix.mulVec_mulVec, hAw, Matrix.mulVec_smul] using happly
  change w ≠ 0 ∧ Matrix.mulVec A w = lambda⁻¹ • w
  refine ⟨hw, ?_⟩
  funext i
  have hi := congrFun hscale i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  calc
    Matrix.mulVec A w i = lambda⁻¹ * (lambda * Matrix.mulVec A w i) := by
      field_simp
    _ = lambda⁻¹ * w i := by rw [← hi]
    _ = (lambda⁻¹ • w) i := by simp

end NumStability
