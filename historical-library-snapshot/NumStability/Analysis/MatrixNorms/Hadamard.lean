-- Analysis/MatrixNorms/Hadamard.lean
--
-- Exact norm formulas for Hadamard and Fourier matrices.

import Mathlib.RingTheory.RootsOfUnity.Complex
import NumStability.Analysis.MatrixNorms.Comparisons

/-!
# Hadamard and Fourier matrix norms

Develops real/complex Hadamard matrices and root-of-unity Fourier matrices,
with orthogonality, unitarity, and sharp norm evaluations.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Source-facing real Hadamard matrix predicate for Higham Problem 6.13.
    The entries have absolute value `1` and the rows and columns are mutually
    orthogonal with squared norm `n`. -/
def IsRealHadamardMatrix {n : Nat}
    (H : Fin n -> Fin n -> Real) : Prop :=
  (forall i j, |H i j| = 1) /\
    (forall j k,
      (Finset.univ.sum (fun i : Fin n => H i j * H i k)) =
        if j = k then (n : Real) else 0) /\
    (forall i k,
      (Finset.univ.sum (fun j : Fin n => H i j * H k j)) =
        if i = k then (n : Real) else 0)

lemma IsRealHadamardMatrix.entry_norm_complex {n : Nat}
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H)
    (i j : Fin n) :
    ‖realRectToCMatrix H i j‖ = 1 := by
  simpa [realRectToCMatrix, complexNorm_ofReal_eq_abs] using hH.1 i j

lemma real_sqrt_nat_inv_sq_mul_self {n : Nat} (hn : 0 < n) :
    (Real.sqrt (n : Real))⁻¹ ^ 2 * (n : Real) = 1 := by
  have hsq : Real.sqrt (n : Real) ^ 2 = (n : Real) := by
    rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hne : Real.sqrt (n : Real) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  calc
    (Real.sqrt (n : Real))⁻¹ ^ 2 * (n : Real)
        = (Real.sqrt (n : Real))⁻¹ ^ 2 * Real.sqrt (n : Real) ^ 2 := by
          rw [hsq]
    _ = ((Real.sqrt (n : Real))⁻¹ * Real.sqrt (n : Real)) ^ 2 := by
          ring
    _ = 1 := by
          rw [inv_mul_cancel₀ hne]
          norm_num

noncomputable def realHadamardScaled {n : Nat}
    (H : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => (Real.sqrt (n : Real))⁻¹ * H i j

lemma IsRealHadamardMatrix.scaled_isOrthogonal {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    IsOrthogonal n (realHadamardScaled H) := by
  constructor
  · intro i j
    unfold realHadamardScaled matTranspose
    calc
      (Finset.univ.sum fun k : Fin n =>
          ((Real.sqrt (n : Real))⁻¹ * H k i) *
            ((Real.sqrt (n : Real))⁻¹ * H k j))
          = (Real.sqrt (n : Real))⁻¹ ^ 2 *
              (Finset.univ.sum fun k : Fin n => H k i * H k j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
      _ = (Real.sqrt (n : Real))⁻¹ ^ 2 *
            (if i = j then (n : Real) else 0) := by
            rw [hH.2.1 i j]
      _ = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · rw [if_pos hij, if_pos hij]
              exact real_sqrt_nat_inv_sq_mul_self hn
            · rw [if_neg hij, if_neg hij]
              ring
  · intro i j
    unfold realHadamardScaled matTranspose
    calc
      (Finset.univ.sum fun k : Fin n =>
          ((Real.sqrt (n : Real))⁻¹ * H i k) *
            ((Real.sqrt (n : Real))⁻¹ * H j k))
          = (Real.sqrt (n : Real))⁻¹ ^ 2 *
              (Finset.univ.sum fun k : Fin n => H i k * H j k) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
      _ = (Real.sqrt (n : Real))⁻¹ ^ 2 *
            (if i = j then (n : Real) else 0) := by
            rw [hH.2.2 i j]
      _ = if i = j then 1 else 0 := by
            by_cases hij : i = j
            · rw [if_pos hij, if_pos hij]
              exact real_sqrt_nat_inv_sq_mul_self hn
            · rw [if_neg hij, if_neg hij]
              ring

lemma IsRealHadamardMatrix.rectOpNorm2Le_sqrt {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    rectOpNorm2Le H (Real.sqrt (n : Real)) := by
  let U := realHadamardScaled H
  have hUorth : IsOrthogonal n U := by
    simpa [U] using hH.scaled_isOrthogonal hn
  have hUop : opNorm2Le U 1 := hUorth.opNorm2Le_one
  have hUrect : rectOpNorm2Le U 1 := opNorm2Le_to_rectOpNorm2Le hUop
  intro x
  have hsqrt_nonneg : 0 <= Real.sqrt (n : Real) := Real.sqrt_nonneg _
  have hsqrt_ne : Real.sqrt (n : Real) ≠ 0 := by
    exact ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))
  have hHx :
      rectMatMulVec H x =
        fun i : Fin n => Real.sqrt (n : Real) * rectMatMulVec U x i := by
    ext i
    unfold rectMatMulVec U realHadamardScaled
    calc
      (Finset.univ.sum fun j : Fin n => H i j * x j)
          = Finset.univ.sum
              (fun j : Fin n =>
                (Real.sqrt (n : Real) *
                  ((Real.sqrt (n : Real))⁻¹ * H i j)) * x j) := by
              apply Finset.sum_congr rfl
              intro j _hj
              have hscale :
                  Real.sqrt (n : Real) *
                      ((Real.sqrt (n : Real))⁻¹ * H i j) =
                    H i j := by
                calc
                  Real.sqrt (n : Real) *
                      ((Real.sqrt (n : Real))⁻¹ * H i j)
                      = (Real.sqrt (n : Real) *
                          (Real.sqrt (n : Real))⁻¹) * H i j := by
                        ring
                  _ = 1 * H i j := by
                        rw [mul_inv_cancel₀ hsqrt_ne]
                  _ = H i j := by ring
              rw [hscale]
      _ = Real.sqrt (n : Real) *
            (Finset.univ.sum fun j : Fin n =>
              ((Real.sqrt (n : Real))⁻¹ * H i j) * x j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _hj
              ring
  calc
    vecNorm2 (rectMatMulVec H x)
        = vecNorm2 (fun i : Fin n =>
            Real.sqrt (n : Real) * rectMatMulVec U x i) := by
          rw [hHx]
    _ = Real.sqrt (n : Real) * vecNorm2 (rectMatMulVec U x) := by
          rw [vecNorm2_smul, abs_of_nonneg hsqrt_nonneg]
    _ <= Real.sqrt (n : Real) * (1 * vecNorm2 x) := by
          exact mul_le_mul_of_nonneg_left (hUrect x) hsqrt_nonneg
    _ = Real.sqrt (n : Real) * vecNorm2 x := by ring

lemma IsRealHadamardMatrix.column_lpNorm {n : Nat}
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H)
    {p : Real} (hp : 0 < p) (j : Fin n) :
    complexVecLpNorm (n := n) (ENNReal.ofReal p)
        (fun i : Fin n => realRectToCMatrix H i j) =
      (n : Real) ^ p⁻¹ := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp]
  apply congrArg (fun r : Real => r ^ p⁻¹)
  calc
    (Finset.univ.sum fun i : Fin n => ‖realRectToCMatrix H i j‖ ^ p)
        = Finset.univ.sum (fun _i : Fin n => (1 : Real)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [hH.entry_norm_complex i j]
          simp
    _ = (n : Real) := by simp [Finset.sum_const, Fintype.card_fin]

lemma IsRealHadamardMatrix.row_lpNorm {n : Nat}
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H)
    {p : Real} (hp : 0 < p) (i : Fin n) :
    complexVecLpNorm (n := n) (ENNReal.ofReal p)
        (fun j : Fin n => realRectToCMatrix H i j) =
      (n : Real) ^ p⁻¹ := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow hp]
  apply congrArg (fun r : Real => r ^ p⁻¹)
  calc
    (Finset.univ.sum fun j : Fin n => ‖realRectToCMatrix H i j‖ ^ p)
        = Finset.univ.sum (fun _j : Fin n => (1 : Real)) := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hH.entry_norm_complex i j]
          simp
    _ = (n : Real) := by simp [Finset.sum_const, Fintype.card_fin]

lemma IsRealHadamardMatrix.complexMatrixVecMul_standardBasis
    {n : Nat} {H : Fin n -> Fin n -> Real} (j : Fin n) :
    complexMatrixVecMul (realRectToCMatrix H) (standardBasisCVec j) =
      fun i : Fin n => realRectToCMatrix H i j := by
  ext i
  unfold complexMatrixVecMul standardBasisCVec realRectToCMatrix
  simp [Finset.mem_univ]

lemma IsRealHadamardMatrix.column_lower {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H)
    {p : Real} (hp : 1 <= p) :
    (n : Real) ^ p⁻¹ <=
      complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  haveI : Fact (1 <= ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hd := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
    (m := n) (n := n) hn p hp (realRectToCMatrix H)
  have h := hd.1 (standardBasisCVec j0)
  rw [IsRealHadamardMatrix.complexMatrixVecMul_standardBasis (H := H) j0,
    hH.column_lpNorm hp_pos j0,
    complexVecLpNorm_standardBasisCVec (ENNReal.ofReal p) j0,
    mul_one] at h
  exact h

lemma IsRealHadamardMatrix.row_sign_lower {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H)
    {p : Real} (hp : 1 <= p) :
    (n : Real) ^ (1 - p⁻¹) <=
      complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hn_pos_real : 0 < (n : Real) := Nat.cast_pos.mpr hn
  haveI : Fact (1 <= ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  let i0 : Fin n := ⟨0, hn⟩
  let x : CVec n := fun j : Fin n => realRectToCMatrix H i0 j
  have hx_norm :
      complexVecLpNorm (n := n) (ENNReal.ofReal p) x =
        (n : Real) ^ p⁻¹ := by
    simpa [x] using hH.row_lpNorm hp_pos i0
  have hcoord_value :
      complexMatrixVecMul (realRectToCMatrix H) x i0 = ((n : Real) : Complex) := by
    calc
      complexMatrixVecMul (realRectToCMatrix H) x i0
          = (Finset.univ.sum fun j : Fin n =>
              ((H i0 j * H i0 j : Real) : Complex)) := by
              simp [complexMatrixVecMul, realRectToCMatrix, x]
      _ = ((n : Real) : Complex) := by
              have hsum_real :
                  (Finset.univ.sum fun j : Fin n => H i0 j * H i0 j) =
                    (n : Real) := by
                simpa using hH.2.2 i0 i0
              exact_mod_cast hsum_real
  have hcoord_norm :
      ‖complexMatrixVecMul (realRectToCMatrix H) x i0‖ = (n : Real) := by
    rw [hcoord_value]
    exact complexNorm_ofReal_of_nonneg (Nat.cast_nonneg n)
  have hcoord_le :
      (n : Real) <=
        complexVecLpNorm (n := n) (ENNReal.ofReal p)
          (complexMatrixVecMul (realRectToCMatrix H) x) := by
    have h := complexVecLpNorm_coord_le (ENNReal.ofReal p)
      (complexMatrixVecMul (realRectToCMatrix H) x) i0
    simpa [hcoord_norm] using h
  have hd := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
    (m := n) (n := n) hn p hp (realRectToCMatrix H)
  have hbound := hd.1 x
  have hmul :
      (n : Real) <=
        complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) *
          ((n : Real) ^ p⁻¹) := by
    calc
      (n : Real) <=
          complexVecLpNorm (n := n) (ENNReal.ofReal p)
            (complexMatrixVecMul (realRectToCMatrix H) x) := hcoord_le
      _ <= complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) *
            complexVecLpNorm (n := n) (ENNReal.ofReal p) x := hbound
      _ = complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) *
            ((n : Real) ^ p⁻¹) := by rw [hx_norm]
  have hpow_pos : 0 < (n : Real) ^ p⁻¹ :=
    Real.rpow_pos_of_pos hn_pos_real p⁻¹
  have hdiv :
      (n : Real) / ((n : Real) ^ p⁻¹) <=
        complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) := by
    rw [div_le_iff₀ hpow_pos]
    exact hmul
  have hdiv_eq :
      (n : Real) / ((n : Real) ^ p⁻¹) =
        (n : Real) ^ (1 - p⁻¹) := by
    calc
      (n : Real) / ((n : Real) ^ p⁻¹)
          = (n : Real) ^ (1 : Real) / ((n : Real) ^ p⁻¹) := by
              rw [Real.rpow_one]
      _ = (n : Real) ^ (1 - p⁻¹) := by
              exact (Real.rpow_sub hn_pos_real (1 : Real) p⁻¹).symm
  simpa [hdiv_eq] using hdiv

lemma real_rpow_abs_inv_sub_half_mul_sqrt_eq_left {n : Nat} (hn : 0 < n)
    {p : Real} (hp : 1 <= p) (hp2 : p <= 2) :
    (n : Real) ^ |p⁻¹ - (2 : Real)⁻¹| * Real.sqrt (n : Real) =
      (n : Real) ^ p⁻¹ := by
  have hn_pos_real : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have habs : |p⁻¹ - (2 : Real)⁻¹| = p⁻¹ - (2 : Real)⁻¹ := by
    have htwo_inv_le : (2 : Real)⁻¹ <= p⁻¹ := by
      simpa [one_div] using (one_div_le_one_div_of_le hp_pos hp2)
    exact abs_of_nonneg (sub_nonneg.mpr htwo_inv_le)
  calc
    (n : Real) ^ |p⁻¹ - (2 : Real)⁻¹| * Real.sqrt (n : Real)
        = (n : Real) ^ (p⁻¹ - (2 : Real)⁻¹) *
            (n : Real) ^ ((1 : Real) / 2) := by
            rw [habs, Real.sqrt_eq_rpow]
    _ = (n : Real) ^ ((p⁻¹ - (2 : Real)⁻¹) + (1 : Real) / 2) := by
            rw [Real.rpow_add hn_pos_real]
    _ = (n : Real) ^ p⁻¹ := by
            congr 1
            ring

lemma real_rpow_abs_inv_sub_half_mul_sqrt_eq_right {n : Nat} (hn : 0 < n)
    {p : Real} (h2p : 2 <= p) :
    (n : Real) ^ |p⁻¹ - (2 : Real)⁻¹| * Real.sqrt (n : Real) =
      (n : Real) ^ (1 - p⁻¹) := by
  have hn_pos_real : 0 < (n : Real) := Nat.cast_pos.mpr hn
  have habs : |p⁻¹ - (2 : Real)⁻¹| = (2 : Real)⁻¹ - p⁻¹ := by
    have hp_inv_le : p⁻¹ <= (2 : Real)⁻¹ := by
      have htwo_pos : (0 : Real) < 2 := by norm_num
      simpa [one_div] using (one_div_le_one_div_of_le htwo_pos h2p)
    simpa using
      (abs_of_nonpos (sub_nonpos.mpr hp_inv_le) :
        |p⁻¹ - (2 : Real)⁻¹| = -(p⁻¹ - (2 : Real)⁻¹))
  calc
    (n : Real) ^ |p⁻¹ - (2 : Real)⁻¹| * Real.sqrt (n : Real)
        = (n : Real) ^ ((2 : Real)⁻¹ - p⁻¹) *
            (n : Real) ^ ((1 : Real) / 2) := by
            rw [habs, Real.sqrt_eq_rpow]
    _ = (n : Real) ^ (((2 : Real)⁻¹ - p⁻¹) + (1 : Real) / 2) := by
            rw [Real.rpow_add hn_pos_real]
    _ = (n : Real) ^ (1 - p⁻¹) := by
            congr 1
            norm_num
            ring

/-- Higham Problem 6.13, `p = infinity` endpoint. -/
theorem IsRealHadamardMatrix.complexMatrixInfNorm_eq {n : Nat}
    (hn : 0 < n) {H : Fin n -> Fin n -> Real}
    (hH : IsRealHadamardMatrix H) :
    complexMatrixInfNorm (realRectToCMatrix H) = (n : Real) := by
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le (Nat.cast_nonneg n)
    intro i
    calc
      (Finset.univ.sum fun j : Fin n => ‖realRectToCMatrix H i j‖)
          = Finset.univ.sum (fun _j : Fin n => (1 : Real)) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [hH.entry_norm_complex i j]
      _ = (n : Real) := by simp [Finset.sum_const, Fintype.card_fin]
      _ <= (n : Real) := le_rfl
  · let i0 : Fin n := ⟨0, hn⟩
    have h := complexMatrixInfNorm_row_sum_le (realRectToCMatrix H) i0
    have hsum :
        (Finset.univ.sum fun j : Fin n => ‖realRectToCMatrix H i0 j‖) =
          (n : Real) := by
      calc
        (Finset.univ.sum fun j : Fin n => ‖realRectToCMatrix H i0 j‖)
            = Finset.univ.sum (fun _j : Fin n => (1 : Real)) := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hH.entry_norm_complex i0 j]
        _ = (n : Real) := by simp [Finset.sum_const, Fintype.card_fin]
    simpa [hsum] using h

/-- Column orthogonality of a real Hadamard matrix after complexification:
    `H^T H = n I` over `Complex`. -/
theorem IsRealHadamardMatrix.complex_transpose_mul_self {n : Nat}
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    let HC : Matrix (Fin n) (Fin n) Complex := realRectToCMatrix H
    Matrix.transpose HC * HC =
      ((n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex)) := by
  dsimp
  ext j k
  by_cases hjk : j = k
  · subst k
    have hreal := hH.2.1 j j
    simp at hreal
    simp [Matrix.mul_apply, realRectToCMatrix]
    exact_mod_cast hreal
  · have hreal := hH.2.1 j k
    simp [hjk] at hreal
    simp [Matrix.mul_apply, realRectToCMatrix, hjk]
    exact_mod_cast hreal

/-- A nonempty real Hadamard matrix has full rank after complexification. -/
theorem IsRealHadamardMatrix.complexMatrixRank_eq {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    complexMatrixRank (realRectToCMatrix H) = n := by
  let HC : Matrix (Fin n) (Fin n) Complex := realRectToCMatrix H
  have hmul :
      Matrix.transpose HC * HC =
        ((n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex)) := by
    simpa [HC] using hH.complex_transpose_mul_self
  let B : Matrix (Fin n) (Fin n) Complex := ((n : Complex)⁻¹) • Matrix.transpose HC
  have hleft : B * HC = 1 := by
    calc
      B * HC = ((n : Complex)⁻¹) • (Matrix.transpose HC * HC) := by
        ext i j
        simp [B, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
      _ = ((n : Complex)⁻¹) • (((n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex))) := by
        rw [hmul]
      _ = 1 := by
        have hnC : (n : Complex) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hn)
        ext i j
        by_cases hij : i = j
        · subst j
          simp [hnC]
        · simp [hij]
  have hdet : IsUnit HC.det := Matrix.isUnit_det_of_left_inverse (A := HC) (B := B) hleft
  unfold complexMatrixRank
  simpa [HC, Fintype.card_fin] using
    (Matrix.rank_of_isUnit HC (Matrix.isUnit_iff_isUnit_det HC |>.mpr hdet))

/-- A square real Hadamard matrix has entrywise sum norm `n^2` after
    complexification. -/
theorem IsRealHadamardMatrix.complexMatrixEntrywiseSumNorm_eq {n : Nat}
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    complexMatrixEntrywiseSumNorm (realRectToCMatrix H) =
      ((n * n : Nat) : Real) := by
  rw [complexMatrixEntrywiseSumNorm_eq_sum_sum]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ‖realRectToCMatrix H i j‖)
        = ∑ _i : Fin n, ∑ _j : Fin n, (1 : Real) := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hH.entry_norm_complex i j]
    _ = ((n * n : Nat) : Real) := by
          simp [Finset.sum_const, Fintype.card_fin, Nat.cast_mul]

/-- A real Hadamard matrix has Euclidean operator norm at most `sqrt n` after
    complexification. -/
theorem IsRealHadamardMatrix.complexMatrixOp2_le_sqrt {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    complexMatrixOp2 (realRectToCMatrix H) <= Real.sqrt (n : Real) :=
  complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le H
    (Real.sqrt_nonneg _) (hH.rectOpNorm2Le_sqrt hn)

lemma IsRealHadamardMatrix.upper_le_max {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H)
    {p : Real} (hp : 1 <= p) :
    complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) <=
      max ((n : Real) ^ p⁻¹) ((n : Real) ^ (1 - p⁻¹)) := by
  have htwo_bound :
      complexMatrixLpNormOfReal hn (2 : Real) (by norm_num) (realRectToCMatrix H) <=
        Real.sqrt (n : Real) := by
    rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2]
    exact hH.complexMatrixOp2_le_sqrt hn
  have hcomp :=
    (complexMatrixLpNormOfReal_twoNorm_equiv_bounds
      (n := n) hn (p := p) hp (realRectToCMatrix H)).2
  have hfactor_nonneg :
      0 <= (n : Real) ^ |p⁻¹ - (2 : Real)⁻¹| :=
    Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hupper_sqrt :
      complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) <=
        (n : Real) ^ |p⁻¹ - (2 : Real)⁻¹| * Real.sqrt (n : Real) :=
    hcomp.trans (mul_le_mul_of_nonneg_left htwo_bound hfactor_nonneg)
  by_cases hp2 : p <= 2
  · have hpow := real_rpow_abs_inv_sub_half_mul_sqrt_eq_left hn hp hp2
    exact hupper_sqrt.trans (by rw [hpow]; exact le_max_left _ _)
  · have h2p : 2 <= p := le_of_not_ge hp2
    have hpow := real_rpow_abs_inv_sub_half_mul_sqrt_eq_right hn h2p
    exact hupper_sqrt.trans (by rw [hpow]; exact le_max_right _ _)

/-- Higham, 2nd ed., Chapter 6, Problem 6.13, finite-real `p` form:
    a real Hadamard matrix has induced complex matrix `p`-norm
    `max(n^(1/p), n^(1-1/p))`. -/
theorem IsRealHadamardMatrix.complexMatrixLpNormOfReal_eq {n : Nat}
    (hn : 0 < n) {H : Fin n -> Fin n -> Real}
    (hH : IsRealHadamardMatrix H) {p : Real} (hp : 1 <= p) :
    complexMatrixLpNormOfReal hn p hp (realRectToCMatrix H) =
      max ((n : Real) ^ p⁻¹) ((n : Real) ^ (1 - p⁻¹)) := by
  apply le_antisymm
  · exact hH.upper_le_max hn hp
  · exact max_le (hH.column_lower hn hp) (hH.row_sign_lower hn hp)

/-- A nonempty square real Hadamard matrix has Euclidean operator norm
    exactly `sqrt n` after complexification. -/
theorem IsRealHadamardMatrix.complexMatrixOp2_eq_sqrt {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    complexMatrixOp2 (realRectToCMatrix H) = Real.sqrt (n : Real) := by
  have hupper := hH.complexMatrixOp2_le_sqrt hn
  have hlower :=
    hH.column_lower (n := n) hn (p := (2 : Real)) (by norm_num)
  rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2] at hlower
  have hp : (n : Real) ^ (2 : Real)⁻¹ = Real.sqrt (n : Real) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  exact le_antisymm hupper (by simpa [hp] using hlower)

/-- Source-facing complex Hadamard predicate for Higham Problem 6.1's
    roots-of-unity/Vandermonde equality example.  Entries have modulus `1` and
    rows/columns are orthogonal with squared norm `n`. -/
def IsComplexHadamardMatrix {n : Nat} (H : CMatrix n n) : Prop :=
  (∀ i j, ‖H i j‖ = 1) ∧
    (∀ j k,
      (Finset.univ.sum (fun i : Fin n => star (H i j) * H i k)) =
        if j = k then (n : ℂ) else 0) ∧
    (∀ i k,
      (Finset.univ.sum (fun j : Fin n => H i j * star (H k j))) =
        if i = k then (n : ℂ) else 0)

/-- Source-facing scalar-multiple complex Hadamard predicate for the full-rank
    square specialization of Higham Problem 6.1's `S/2` equality case. -/
def IsScalarMultipleComplexHadamardMatrix {n : Nat} (A : CMatrix n n) : Prop :=
  ∃ rho : Real, 0 < rho ∧ ∃ H : CMatrix n n,
    IsComplexHadamardMatrix H ∧ ∀ i j, A i j = (rho : Complex) * H i j

/-- Normalize a matrix by a positive real entry scale. -/
noncomputable def complexMatrixNormalizeByReal {n : Nat}
    (rho : Real) (A : CMatrix n n) : CMatrix n n :=
  fun i j => ((rho : Complex)⁻¹) * A i j

/-- Column orthogonality of a complex Hadamard matrix:
    `H† H = n I`. -/
theorem IsComplexHadamardMatrix.conjTranspose_mul_self {n : Nat}
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) :
    (complexCMatrixAsMatrix H).conjTranspose * complexCMatrixAsMatrix H =
      ((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  ext j k
  by_cases hjk : j = k
  · subst k
    have hcol := hH.2.1 j j
    simp at hcol
    simpa [complexCMatrixAsMatrix, Matrix.mul_apply] using hcol
  · have hcol := hH.2.1 j k
    simp [hjk] at hcol
    simpa [complexCMatrixAsMatrix, Matrix.mul_apply, hjk] using hcol

/-- A nonempty complex Hadamard matrix has full rank. -/
theorem IsComplexHadamardMatrix.complexMatrixRank_eq {n : Nat} (hn : 0 < n)
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) :
    complexMatrixRank H = n := by
  let M : Matrix (Fin n) (Fin n) ℂ := complexCMatrixAsMatrix H
  have hmul :
      M.conjTranspose * M =
        ((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    simpa [M] using hH.conjTranspose_mul_self
  let B : Matrix (Fin n) (Fin n) ℂ := ((n : ℂ)⁻¹) • M.conjTranspose
  have hleft : B * M = 1 := by
    calc
      B * M = ((n : ℂ)⁻¹) • (M.conjTranspose * M) := by
        ext i j
        simp [B, Matrix.mul_apply, Finset.mul_sum, mul_assoc]
      _ = ((n : ℂ)⁻¹) • (((n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
        rw [hmul]
      _ = 1 := by
        have hnC : (n : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.ne_of_gt hn)
        ext i j
        by_cases hij : i = j
        · subst j
          simp [hnC]
        · simp [hij]
  have hdet : IsUnit M.det := Matrix.isUnit_det_of_left_inverse (A := M) (B := B) hleft
  unfold complexMatrixRank
  simpa [M, complexCMatrixAsMatrix, Fintype.card_fin] using
    (Matrix.rank_of_isUnit M (Matrix.isUnit_iff_isUnit_det M |>.mpr hdet))

/-- A square complex Hadamard matrix has entrywise sum norm `n^2`. -/
theorem IsComplexHadamardMatrix.complexMatrixEntrywiseSumNorm_eq {n : Nat}
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) :
    complexMatrixEntrywiseSumNorm H = ((n * n : Nat) : ℝ) := by
  rw [complexMatrixEntrywiseSumNorm_eq_sum_sum]
  calc
    (∑ i : Fin n, ∑ j : Fin n, ‖H i j‖)
        = ∑ _i : Fin n, ∑ _j : Fin n, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hH.1 i j]
    _ = ((n * n : Nat) : ℝ) := by
          simp [Finset.sum_const, Fintype.card_fin, Nat.cast_mul]

/-- Each column of a complex Hadamard matrix has Euclidean norm `sqrt n`. -/
theorem IsComplexHadamardMatrix.column_l2Norm {n : Nat}
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) (j : Fin n) :
    complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ)) (fun i : Fin n => H i j) =
      Real.sqrt (n : ℝ) := by
  rw [complexVecLpNorm_ofReal_eq_sum_rpow (by norm_num)]
  have hsum :
      (∑ i : Fin n, ‖H i j‖ ^ (2 : ℝ)) = (n : ℝ) := by
    calc
      (∑ i : Fin n, ‖H i j‖ ^ (2 : ℝ))
          = ∑ _i : Fin n, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hH.1 i j]
            norm_num
      _ = (n : ℝ) := by simp [Finset.sum_const, Fintype.card_fin]
  rw [hsum]
  rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow]

/-- A complex Hadamard matrix has Euclidean operator norm at most `sqrt n`. -/
theorem IsComplexHadamardMatrix.complexMatrixOp2_le_sqrt {n : Nat}
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) :
    complexMatrixOp2 H ≤ Real.sqrt (n : ℝ) :=
  complexMatrixOp2_le_sqrt_of_conjTranspose_mul_self H hH.conjTranspose_mul_self

/-- A nonempty complex Hadamard matrix has Euclidean operator norm exactly
    `sqrt n`. -/
theorem IsComplexHadamardMatrix.complexMatrixOp2_eq_sqrt {n : Nat} (hn : 0 < n)
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) :
    complexMatrixOp2 H = Real.sqrt (n : ℝ) := by
  have hupper := hH.complexMatrixOp2_le_sqrt
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let j0 : Fin n := ⟨0, hn⟩
  have hbound :=
    hasComplexMatrixLpBound_apply (complexMatrixOp2_hasComplexMatrixLpBound H)
      (standardBasisCVec j0)
  rw [complexMatrixVecMul_standardBasisCVec,
    hH.column_l2Norm j0, complexVecLpNorm_standardBasisCVec, mul_one] at hbound
  exact le_antisymm hupper hbound

/-- Frobenius square of a flat-entry matrix in terms of its common entry scale. -/
theorem complexMatrixFrobeniusSq_eq_card_mul_flatEntryNorm_scale_sq
    {m n : Nat} (A : CMatrix m n) (hflat : ComplexMatrixFlatEntryNorm A) :
    complexMatrixFrobeniusSq A =
      ((m * n : Nat) : Real) * (Classical.choose hflat) ^ 2 := by
  let rho : Real := Classical.choose hflat
  have hrho_spec : 0 ≤ rho ∧ ∀ i j, ‖A i j‖ = rho :=
    Classical.choose_spec hflat
  rw [complexMatrixFrobeniusSq_eq_entrywise_sum]
  calc
    (∑ ij : Fin m × Fin n, ‖A ij.1 ij.2‖ ^ 2)
        = ∑ _ij : Fin m × Fin n, rho ^ 2 := by
            apply Finset.sum_congr rfl
            intro ij _hi
            rw [hrho_spec.2 ij.1 ij.2]
    _ = ((m * n : Nat) : Real) * rho ^ 2 := by
            simp [Finset.sum_const, Fintype.card_prod, Fintype.card_fin,
              nsmul_eq_mul, Nat.cast_mul]

/-- In the full-rank square structural `S/2` equality case, the common flat
    entry scale is positive and satisfies `||A||₂² = n rho²`. -/
theorem complexMatrixFullRankS2Equality_flatEntryScale_pos_and_op2_sq_eq
    {n : Nat} (hn : 0 < n) (A : CMatrix n n)
    (hrank : complexMatrixRank A = n)
    (hflat : ComplexMatrixFlatEntryNorm A)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    let rho : Real := Classical.choose hflat
    0 < rho ∧ (∀ i j, ‖A i j‖ = rho) ∧
      complexMatrixOp2 A ^ 2 = (n : Real) * rho ^ 2 := by
  classical
  let rho : Real := Classical.choose hflat
  have hrho_spec : 0 ≤ rho ∧ ∀ i j, ‖A i j‖ = rho :=
    Classical.choose_spec hflat
  have hF_flat :
      complexMatrixFrobeniusSq A = ((n * n : Nat) : Real) * rho ^ 2 := by
    simpa [rho] using
      complexMatrixFrobeniusSq_eq_card_mul_flatEntryNorm_scale_sq A hflat
  have hF_sv :
      complexMatrixFrobeniusSq A = (n : Real) * complexMatrixOp2 A ^ 2 := by
    rw [complexMatrixFrobeniusSq_eq_rank_mul_op2_sq_of_positiveSingularValuesEqualOp2
      A hsv, hrank]
  have hnR_ne : (n : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hop2_sq_eq :
      complexMatrixOp2 A ^ 2 = (n : Real) * rho ^ 2 := by
    have hEq :
        ((n * n : Nat) : Real) * rho ^ 2 =
          (n : Real) * complexMatrixOp2 A ^ 2 := by
      rw [← hF_flat, hF_sv]
    have hEq' :
        (n : Real) * ((n : Real) * rho ^ 2) =
          (n : Real) * complexMatrixOp2 A ^ 2 := by
      simpa [Nat.cast_mul, mul_assoc] using hEq
    exact (mul_left_cancel₀ hnR_ne hEq').symm
  have hop2_pos : 0 < complexMatrixOp2 A := by
    let i0 : Fin n := ⟨0, hn⟩
    have hsig_ne : complexMatrixSingularValue A i0 ≠ 0 :=
      complexMatrixSingularValue_ne_zero_of_rank_eq_card A hrank i0
    have hsig_eq : complexMatrixSingularValue A i0 = complexMatrixOp2 A :=
      hsv i0 hsig_ne
    have hop2_ne : complexMatrixOp2 A ≠ 0 := by
      intro hop2_zero
      exact hsig_ne (by simpa [hop2_zero] using hsig_eq)
    exact lt_of_le_of_ne (complexMatrixOp2_nonneg A) (Ne.symm hop2_ne)
  have hrho_ne : rho ≠ 0 := by
    intro hrho_zero
    have hop2_sq_zero : complexMatrixOp2 A ^ 2 = 0 := by
      simp [hop2_sq_eq, hrho_zero]
    exact (ne_of_gt (sq_pos_of_pos hop2_pos)) hop2_sq_zero
  exact ⟨lt_of_le_of_ne hrho_spec.1 (Ne.symm hrho_ne), hrho_spec.2, hop2_sq_eq⟩

/-- A flat square matrix with scalar Gram `A†A = n rho² I` normalizes to a
    complex Hadamard matrix. -/
theorem complexMatrixNormalizeByReal_isComplexHadamard_of_flatEntryNorm_and_conjTranspose_mul_self
    {n : Nat} (hn : 0 < n) {A : CMatrix n n} {rho : Real}
    (hrho : 0 < rho) (hentry : ∀ i j, ‖A i j‖ = rho)
    (hgram :
      (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
        ((((n : Real) * rho ^ 2 : Real) : Complex) •
          (1 : Matrix (Fin n) (Fin n) Complex))) :
    IsComplexHadamardMatrix (complexMatrixNormalizeByReal rho A) := by
  classical
  let H : CMatrix n n := complexMatrixNormalizeByReal rho A
  let M : Matrix (Fin n) (Fin n) Complex := complexCMatrixAsMatrix A
  let HM : Matrix (Fin n) (Fin n) Complex := complexCMatrixAsMatrix H
  have hHM : HM = ((rho : Complex)⁻¹) • M := by
    ext i j
    rfl
  have hnC : (n : Complex) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hrhoC : (rho : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hrho)
  have hnorm_inv : ‖((rho : Complex)⁻¹)‖ = rho⁻¹ := by
    simp [norm_inv, abs_of_pos hrho]
  have hcolMatrix : HM.conjTranspose * HM =
      ((n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex)) := by
    rw [hHM, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, hgram]
    ext j k
    by_cases hjk : j = k
    · subst k
      simp [pow_two]
      field_simp [hrhoC]
    · simp [hjk]
  have hleft :
      (((n : Complex)⁻¹) • HM.conjTranspose) * HM =
        (1 : Matrix (Fin n) (Fin n) Complex) := by
    calc
      (((n : Complex)⁻¹) • HM.conjTranspose) * HM =
          ((n : Complex)⁻¹) • (HM.conjTranspose * HM) := by
            rw [Matrix.smul_mul]
      _ = ((n : Complex)⁻¹) •
          ((n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex)) := by
            rw [hcolMatrix]
      _ = (1 : Matrix (Fin n) (Fin n) Complex) := by
            ext i j
            by_cases hij : i = j
            · subst j
              simp [hnC]
            · simp [hij]
  have hright :
      HM * (((n : Complex)⁻¹) • HM.conjTranspose) =
        (1 : Matrix (Fin n) (Fin n) Complex) :=
    (mul_eq_one_comm).mp hleft
  have hrowMatrix : HM * HM.conjTranspose =
      ((n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex)) := by
    calc
      HM * HM.conjTranspose =
          (n : Complex) •
            (((n : Complex)⁻¹) • (HM * HM.conjTranspose)) := by
              ext i j
              simp [hnC]
      _ = (n : Complex) •
            (HM * (((n : Complex)⁻¹) • HM.conjTranspose)) := by
              rw [Matrix.mul_smul]
      _ = (n : Complex) • (1 : Matrix (Fin n) (Fin n) Complex) := by
              rw [hright]
  constructor
  · intro i j
    change ‖((rho : Complex)⁻¹) * A i j‖ = 1
    rw [norm_mul, hnorm_inv, hentry i j]
    exact inv_mul_cancel₀ (ne_of_gt hrho)
  constructor
  · intro j k
    have hentry_col := congr_fun (congr_fun hcolMatrix j) k
    simpa [H, HM, complexCMatrixAsMatrix, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.one_apply] using hentry_col
  · intro i k
    have hentry_row := congr_fun (congr_fun hrowMatrix i) k
    simpa [H, HM, complexCMatrixAsMatrix, Matrix.mul_apply, Matrix.smul_apply,
      Matrix.one_apply] using hentry_row

/-- Full-rank square `S/2` equality normalizes to a scalar multiple of a complex
    Hadamard matrix.  This is the source-facing Hadamard specialization of the
    corrected structural equality characterization. -/
theorem complexMatrixFullRankS2Equality_isScalarMultipleComplexHadamard
    {n : Nat} (hn : 0 < n) (A : CMatrix n n)
    (hrank : complexMatrixRank A = n)
    (h : complexMatrixEntrywiseSumNorm A =
      Real.sqrt (((n * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A) :
    IsScalarMultipleComplexHadamardMatrix A := by
  classical
  have hmn : 0 < n * n := Nat.mul_pos hn hn
  have hstruct :=
    complexMatrixS2StructuralConditions_of_entrywiseSumNorm_eq_sqrt_card_rank_mul_op2
      hmn A h
  let rho : Real := Classical.choose hstruct.1
  have hscale :=
    complexMatrixFullRankS2Equality_flatEntryScale_pos_and_op2_sq_eq
      hn A hrank hstruct.1 hstruct.2
  have hrho_pos : 0 < rho := hscale.1
  have hentry : ∀ i j, ‖A i j‖ = rho := hscale.2.1
  have hop2_sq : complexMatrixOp2 A ^ 2 = (n : Real) * rho ^ 2 := hscale.2.2
  have hgram_op2 :
      (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
        (((complexMatrixOp2 A ^ 2 : Real) : Complex) •
          (1 : Matrix (Fin n) (Fin n) Complex)) :=
    complexMatrix_conjTranspose_mul_self_eq_op2_sq_smul_id_of_rank_eq_card_of_positiveSingularValuesEqualOp2
      A hrank hstruct.2
  have hgram_rho :
      (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
        ((((n : Real) * rho ^ 2 : Real) : Complex) •
          (1 : Matrix (Fin n) (Fin n) Complex)) := by
    simpa [hop2_sq] using hgram_op2
  refine ⟨rho, hrho_pos, complexMatrixNormalizeByReal rho A, ?_, ?_⟩
  · exact complexMatrixNormalizeByReal_isComplexHadamard_of_flatEntryNorm_and_conjTranspose_mul_self
      hn hrho_pos hentry hgram_rho
  · intro i j
    unfold complexMatrixNormalizeByReal
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hrho_pos)]

/-- The Fourier/Vandermonde matrix built from an `n`th root of unity, indexed
    from `0` to `n - 1`. -/
noncomputable def complexFourierVandermondeMatrix (n : Nat) (ζ : ℂ) : CMatrix n n :=
  fun i j => ζ ^ (i.val * j.val)

/-- A finite geometric sum over `Fin n` vanishes when the ratio is a nontrivial
    `n`th root of unity. -/
theorem complex_fin_geometric_sum_eq_zero {n : Nat} {q : ℂ}
    (hqpow : q ^ n = 1) (hqne : q = 1 -> False) :
    (Finset.univ.sum (fun i : Fin n => q ^ i.val)) = 0 := by
  have h := geom_sum_eq (x := q) hqne n
  rw [hqpow, sub_self, zero_div] at h
  simpa [Finset.sum_range] using h

/-- Unit complex numbers have conjugate equal to inverse. -/
theorem complex_star_eq_inv_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) :
    star z = z⁻¹ := by
  simpa using (Complex.inv_eq_conj hz).symm

/-- Powers of a primitive root have `conj z * z = 1`. -/
theorem complex_star_pow_mul_pow_eq_one_of_isPrimitiveRoot {n : Nat} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (a : Nat) :
    star (ζ ^ a) * ζ ^ a = 1 := by
  have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one (Nat.ne_of_gt hn)
  have hunit : IsUnit ζ := hζ.isUnit (Nat.ne_of_gt hn)
  have hunit_a : IsUnit (ζ ^ a) := hunit.pow a
  have hstar : star (ζ ^ a) = (ζ ^ a)⁻¹ := by
    have hanorm : ‖ζ ^ a‖ = 1 := by
      simp [norm_pow, hζ_norm]
    exact complex_star_eq_inv_of_norm_eq_one hanorm
  rw [hstar]
  exact hunit_a.inv_mul_cancel

/-- Column inner-product summands of a Fourier/Vandermonde matrix are powers of
    a single root-of-unity ratio. -/
theorem complexFourierVandermonde_column_term {ζ : ℂ} (i j k : Nat) :
    star (ζ ^ (i * j)) * ζ ^ (i * k) =
      (star (ζ ^ j) * ζ ^ k) ^ i := by
  rw [star_pow]
  rw [Nat.mul_comm i j, Nat.mul_comm i k]
  rw [pow_mul, pow_mul]
  simpa [star_pow] using (mul_pow (star ζ ^ j) (ζ ^ k) i).symm

/-- Row inner-product summands of a Fourier/Vandermonde matrix are powers of a
    single root-of-unity ratio. -/
theorem complexFourierVandermonde_row_term {ζ : ℂ} (j i k : Nat) :
    ζ ^ (i * j) * star (ζ ^ (k * j)) =
      (star (ζ ^ k) * ζ ^ i) ^ j := by
  rw [Nat.mul_comm i j, Nat.mul_comm k j]
  rw [mul_comm]
  exact complexFourierVandermonde_column_term j k i

/-- Any power of a primitive `n`th root is still an `n`th root. -/
theorem complex_pow_mul_order_of_isPrimitiveRoot {n : Nat} {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) (a : Nat) :
    (ζ ^ a) ^ n = 1 := by
  calc
    (ζ ^ a) ^ n = ζ ^ (a * n) := by rw [pow_mul]
    _ = ζ ^ (n * a) := by rw [Nat.mul_comm]
    _ = (ζ ^ n) ^ a := by rw [pow_mul]
    _ = 1 := by rw [hζ.pow_eq_one, one_pow]

/-- The column ratio for a Fourier/Vandermonde matrix is an `n`th root of unity. -/
theorem complexFourierVandermonde_ratio_pow_order {n : Nat} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (j k : Fin n) :
    (star (ζ ^ j.val) * ζ ^ k.val) ^ n = 1 := by
  have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one (Nat.ne_of_gt hn)
  have hstarj : star (ζ ^ j.val) = (ζ ^ j.val)⁻¹ := by
    have hjnorm : ‖ζ ^ j.val‖ = 1 := by
      simp [norm_pow, hζ_norm]
    exact complex_star_eq_inv_of_norm_eq_one hjnorm
  have hjn : (ζ ^ j.val) ^ n = 1 :=
    complex_pow_mul_order_of_isPrimitiveRoot hζ j.val
  have hkn : (ζ ^ k.val) ^ n = 1 :=
    complex_pow_mul_order_of_isPrimitiveRoot hζ k.val
  rw [hstarj, mul_pow, inv_pow, hjn, hkn]
  simp

/-- Distinct columns give a nontrivial Fourier/Vandermonde ratio. -/
theorem complexFourierVandermonde_ratio_ne_one {n : Nat} (hn : 0 < n)
    {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n)
    {j k : Fin n} (hjk : j = k -> False) :
    (star (ζ ^ j.val) * ζ ^ k.val) = 1 -> False := by
  intro hq
  have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one (Nat.ne_of_gt hn)
  have hunit : IsUnit ζ := hζ.isUnit (Nat.ne_of_gt hn)
  have hunitj : IsUnit (ζ ^ j.val) := hunit.pow j.val
  have hstarj : star (ζ ^ j.val) = (ζ ^ j.val)⁻¹ := by
    have hjnorm : ‖ζ ^ j.val‖ = 1 := by
      simp [norm_pow, hζ_norm]
    exact complex_star_eq_inv_of_norm_eq_one hjnorm
  have hq' : (ζ ^ j.val)⁻¹ * ζ ^ k.val = 1 := by
    simpa [hstarj] using hq
  have heq : ζ ^ j.val = ζ ^ k.val := by
    exact (hunitj.inv_mul_eq_one).mp hq'
  have hvals : j.val = k.val := hζ.pow_inj j.isLt k.isLt heq
  exact hjk (Fin.ext hvals)

/-- The root-of-unity Fourier/Vandermonde matrix is a complex Hadamard matrix. -/
theorem complexFourierVandermonde_isComplexHadamard_of_isPrimitiveRoot
    {n : Nat} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    IsComplexHadamardMatrix (complexFourierVandermondeMatrix n ζ) := by
  constructor
  · intro i j
    have hζ_norm : ‖ζ‖ = 1 := hζ.norm'_eq_one (Nat.ne_of_gt hn)
    simp [complexFourierVandermondeMatrix, norm_pow, hζ_norm]
  constructor
  · intro j k
    by_cases hjk : j = k
    · subst k
      calc
        Finset.univ.sum (fun i : Fin n =>
            star (complexFourierVandermondeMatrix n ζ i j) *
              complexFourierVandermondeMatrix n ζ i j)
            = Finset.univ.sum (fun _i : Fin n => (1 : ℂ)) := by
              apply Finset.sum_congr rfl
              intro i _hi
              simpa [complexFourierVandermondeMatrix] using
                complex_star_pow_mul_pow_eq_one_of_isPrimitiveRoot hn hζ (i.val * j.val)
        _ = (n : ℂ) := by simp
        _ = (if j = j then (n : ℂ) else 0) := by simp
    · have hqpow := complexFourierVandermonde_ratio_pow_order hn hζ j k
      have hqne : (star (ζ ^ j.val) * ζ ^ k.val) = 1 -> False :=
        complexFourierVandermonde_ratio_ne_one hn hζ hjk
      have hsum := complex_fin_geometric_sum_eq_zero hqpow hqne
      calc
        Finset.univ.sum (fun i : Fin n =>
            star (complexFourierVandermondeMatrix n ζ i j) *
              complexFourierVandermondeMatrix n ζ i k)
            = Finset.univ.sum
                (fun i : Fin n => (star (ζ ^ j.val) * ζ ^ k.val) ^ i.val) := by
              apply Finset.sum_congr rfl
              intro i _hi
              simpa [complexFourierVandermondeMatrix] using
                (complexFourierVandermonde_column_term (ζ := ζ) i.val j.val k.val)
        _ = 0 := hsum
        _ = (if j = k then (n : ℂ) else 0) := by simp [hjk]
  · intro i k
    by_cases hik : i = k
    · subst k
      calc
        Finset.univ.sum (fun j : Fin n =>
            complexFourierVandermondeMatrix n ζ i j *
              star (complexFourierVandermondeMatrix n ζ i j))
            = Finset.univ.sum (fun _j : Fin n => (1 : ℂ)) := by
              apply Finset.sum_congr rfl
              intro j _hj
              simpa [complexFourierVandermondeMatrix, mul_comm] using
                complex_star_pow_mul_pow_eq_one_of_isPrimitiveRoot hn hζ (i.val * j.val)
        _ = (n : ℂ) := by simp
        _ = (if i = i then (n : ℂ) else 0) := by simp
    · have hqpow := complexFourierVandermonde_ratio_pow_order hn hζ k i
      have hqne : (star (ζ ^ k.val) * ζ ^ i.val) = 1 -> False :=
        complexFourierVandermonde_ratio_ne_one hn hζ (fun hki => hik hki.symm)
      have hsum := complex_fin_geometric_sum_eq_zero hqpow hqne
      calc
        Finset.univ.sum (fun j : Fin n =>
            complexFourierVandermondeMatrix n ζ i j *
              star (complexFourierVandermondeMatrix n ζ k j))
            = Finset.univ.sum
                (fun j : Fin n => (star (ζ ^ k.val) * ζ ^ i.val) ^ j.val) := by
              apply Finset.sum_congr rfl
              intro j _hj
              simpa [complexFourierVandermondeMatrix] using
                (complexFourierVandermonde_row_term (ζ := ζ) j.val i.val k.val)
        _ = 0 := hsum
        _ = (if i = k then (n : ℂ) else 0) := by simp [hik]
end NumStability
