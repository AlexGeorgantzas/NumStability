/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Stewart

/-! # Higham Chapter 28: exact randsvd spectral norms

This module turns the deterministic Stewart/randsvd factorization into actual
singular-vector, exact operator-norm, inverse, and condition-number theorems.
-/

namespace NumStability

theorem randsvdMatrix_mulVec_rightColumn {n : ℕ}
    (U V : RSqMat n) (sigma : ℕ → ℝ)
    (hV : IsOrthogonal n V) (k : Fin n) :
    Matrix.mulVec (randsvdMatrix U sigma V) (fun i ↦ V i k) =
      sigma k.val • (fun i ↦ U i k) := by
  let D : RSqMat n := rectangularDiagonal (m := n) (n := n) sigma
  have hVtV : V.transpose * V = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hV.left_inv i j
  have hmatrix : randsvdMatrix U sigma V * V = U * D := by
    change (U * D * V.transpose) * V = U * D
    calc
      (U * D * V.transpose) * V = U * D * (V.transpose * V) := by
        noncomm_ring
      _ = U * D := by rw [hVtV, Matrix.mul_one]
  funext i
  have hentry := congrFun (congrFun hmatrix i) k
  change (randsvdMatrix U sigma V * V) i k = sigma k.val * U i k
  rw [hentry]
  simp only [Matrix.mul_apply, D, rectangularDiagonal]
  rw [Finset.sum_eq_single k]
  · simp [mul_comm]
  · intro j _ hj
    have hval : j.val ≠ k.val := fun h => hj (Fin.ext h)
    simp [hval]
  · simp

theorem opNorm2_randsvdMatrix_eq_of_attained_bound {n : ℕ}
    (U V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ i : Fin n, |sigma i.val| ≤ L)
    (k : Fin n) (hk : |sigma k.val| = L) :
    opNorm2 (randsvdMatrix U sigma V) = L := by
  apply le_antisymm
  · apply opNorm2_le_of_opNorm2Le _ hL
    intro x
    have haction :
        matMulVec n (randsvdMatrix U sigma V) x =
          matMulVec n U
            (matMulVec n (rectangularDiagonal (m := n) (n := n) sigma)
              (matMulVec n V.transpose x)) := by
      have hmat :
          randsvdMatrix U sigma V =
            matMul n
              (matMul n U (rectangularDiagonal (m := n) (n := n) sigma))
              V.transpose := by
        ext i j
        simp [randsvdMatrix, matMul, Matrix.mul_apply]
      rw [hmat]
      funext i
      rw [matMulVec_matMul, matMulVec_matMul]
    rw [haction]
    rw [vecNorm2_orthogonal U _ hU]
    have hdiag := finiteOpNorm2Le_finiteDiagonal hL hbound
      (matMulVec n V.transpose x)
    have hVnorm : vecNorm2 (matMulVec n V.transpose x) = vecNorm2 x := by
      exact vecNorm2_orthogonal V.transpose x hV.transpose
    have hdiag' :
        vecNorm2
            (matMulVec n (rectangularDiagonal (m := n) (n := n) sigma)
              (matMulVec n V.transpose x)) ≤
          L * vecNorm2 (matMulVec n V.transpose x) := by
      have hD :
          rectangularDiagonal (m := n) (n := n) sigma =
            finiteDiagonal (fun i : Fin n => sigma i.val) := by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [rectangularDiagonal, finiteDiagonal]
        · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
          simp [rectangularDiagonal, finiteDiagonal, hij, hval]
      rw [hD]
      let y := matMulVec n V.transpose x
      have hmv :
          matMulVec n (finiteDiagonal (fun i : Fin n => sigma i.val)) y =
            finiteMatVec (finiteDiagonal (fun i : Fin n => sigma i.val)) y := by
        ext i
        simp [matMulVec, finiteMatVec, finiteDiagonal]
      change
        vecNorm2
            (matMulVec n (finiteDiagonal (fun i : Fin n => sigma i.val)) y) ≤
          L * vecNorm2 y
      rw [hmv]
      simpa [finiteVecNorm2_fin] using hdiag
    simpa [hVnorm] using hdiag'
  · let x : RVec n := fun i ↦ V i k
    have hx : vecNorm2 x = 1 := by
      simpa [x] using hV.column_vecNorm2_eq_one k
    have hAx := randsvdMatrix_mulVec_rightColumn U V sigma hV k
    have hop := opNorm2Le_opNorm2 (randsvdMatrix U sigma V) x
    have hUnorm : vecNorm2 (fun i ↦ U i k) = 1 :=
      hU.column_vecNorm2_eq_one k
    have hAx' :
        matMulVec n (randsvdMatrix U sigma V) x =
          sigma k.val • (fun i ↦ U i k) := by
      simpa [x, matMulVec, Matrix.mulVec, dotProduct] using hAx
    rw [hAx'] at hop
    change
      vecNorm2 (fun i => sigma k.val * U i k) ≤
        opNorm2 (randsvdMatrix U sigma V) * vecNorm2 x at hop
    rw [vecNorm2_smul, hUnorm, mul_one, hx, mul_one, hk] at hop
    exact hop

noncomputable def randsvdInverseMatrix {n : ℕ}
    (U V : RSqMat n) (sigma : ℕ → ℝ) : RSqMat n :=
  randsvdMatrix V (fun i => (sigma i)⁻¹) U

theorem randsvdMatrix_isInverse {n : ℕ}
    (U V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hsigma : ∀ i : Fin n, sigma i.val ≠ 0) :
    IsInverse n (randsvdMatrix U sigma V)
      (randsvdInverseMatrix U V sigma) := by
  let D : RSqMat n := rectangularDiagonal (m := n) (n := n) sigma
  let Di : RSqMat n :=
    rectangularDiagonal (m := n) (n := n) (fun i => (sigma i)⁻¹)
  have hVtV : V.transpose * V = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hV.left_inv i j
  have hUtU : U.transpose * U = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hU.left_inv i j
  have hUUt : U * U.transpose = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hU.right_inv i j
  have hVVt : V * V.transpose = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      hV.right_inv i j
  have hDDi : D * Di = (1 : RSqMat n) := by
    ext i j
    simp only [Matrix.mul_apply, D, Di, rectangularDiagonal,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      have hidx : ∀ x : Fin n, x.val = i.val ↔ x = i := by
        intro x
        exact ⟨Fin.ext, congrArg Fin.val⟩
      simp_rw [hidx]
      simp [hsigma i]
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxi : x.val = i.val
      · have hxj : x.val ≠ j.val := by omega
        change
          (if i.val = x.val then sigma i.val else 0) *
              (if x.val = j.val then (sigma x.val)⁻¹ else 0) = 0
        rw [if_pos hxi.symm, if_neg hxj, mul_zero]
      · change
          (if i.val = x.val then sigma i.val else 0) *
              (if x.val = j.val then (sigma x.val)⁻¹ else 0) = 0
        rw [if_neg (Ne.symm hxi), zero_mul]
  have hDiD : Di * D = (1 : RSqMat n) := by
    ext i j
    simp only [Matrix.mul_apply, D, Di, rectangularDiagonal,
      Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      have hidx : ∀ x : Fin n, x.val = i.val ↔ x = i := by
        intro x
        exact ⟨Fin.ext, congrArg Fin.val⟩
      simp_rw [hidx]
      simp [hsigma i]
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rw [if_neg hij]
      apply Finset.sum_eq_zero
      intro x _
      by_cases hxi : x.val = i.val
      · have hxj : x.val ≠ j.val := by omega
        change
          (if i.val = x.val then (sigma i.val)⁻¹ else 0) *
              (if x.val = j.val then sigma x.val else 0) = 0
        rw [if_pos hxi.symm, if_neg hxj, mul_zero]
      · change
          (if i.val = x.val then (sigma i.val)⁻¹ else 0) *
              (if x.val = j.val then sigma x.val else 0) = 0
        rw [if_neg (Ne.symm hxi), zero_mul]
  constructor
  · intro i j
    have hmat :
        randsvdInverseMatrix U V sigma * randsvdMatrix U sigma V =
          (1 : RSqMat n) := by
      change (V * Di * U.transpose) * (U * D * V.transpose) = 1
      calc
        (V * Di * U.transpose) * (U * D * V.transpose) =
            V * Di * (U.transpose * U) * D * V.transpose := by
              noncomm_ring
        _ = V * Di * D * V.transpose := by rw [hUtU, Matrix.mul_one]
        _ = V * (Di * D) * V.transpose := by noncomm_ring
        _ = V * V.transpose := by rw [hDiD, Matrix.mul_one]
        _ = 1 := hVVt
    simpa [Matrix.mul_apply, matMul] using congrFun (congrFun hmat i) j
  · intro i j
    have hmat :
        randsvdMatrix U sigma V * randsvdInverseMatrix U V sigma =
          (1 : RSqMat n) := by
      change (U * D * V.transpose) * (V * Di * U.transpose) = 1
      calc
        (U * D * V.transpose) * (V * Di * U.transpose) =
            U * D * (V.transpose * V) * Di * U.transpose := by
              noncomm_ring
        _ = U * D * Di * U.transpose := by rw [hVtV, Matrix.mul_one]
        _ = U * (D * Di) * U.transpose := by noncomm_ring
        _ = U * U.transpose := by rw [hDDi, Matrix.mul_one]
        _ = 1 := hUUt
    simpa [Matrix.mul_apply, matMul] using congrFun (congrFun hmat i) j

theorem kappa2_randsvdMatrix_eq_of_attained_bounds {n : ℕ}
    (U V : RSqMat n) (sigma : ℕ → ℝ)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (L Linv : ℝ) (hL : 0 ≤ L) (hLinv : 0 ≤ Linv)
    (hbound : ∀ i : Fin n, |sigma i.val| ≤ L)
    (hinvBound : ∀ i : Fin n, |(sigma i.val)⁻¹| ≤ Linv)
    (kmax kmin : Fin n) (hkmax : |sigma kmax.val| = L)
    (hkmin : |(sigma kmin.val)⁻¹| = Linv) :
    kappa2 (randsvdMatrix U sigma V) (randsvdInverseMatrix U V sigma) =
      L * Linv := by
  unfold kappa2 randsvdInverseMatrix
  rw [opNorm2_randsvdMatrix_eq_of_attained_bound U V sigma hU hV
      L hL hbound kmax hkmax,
    opNorm2_randsvdMatrix_eq_of_attained_bound V U (fun i => (sigma i)⁻¹)
      hV hU Linv hLinv hinvBound kmin hkmin]

theorem oneLargeSingularValues_pos (alpha : ℝ) (ha : 0 < alpha) (i : ℕ) :
    0 < oneLargeSingularValues alpha i := by
  cases i with
  | zero => simp [oneLargeSingularValues]
  | succ i => simp [oneLargeSingularValues, inv_pos.mpr ha]

theorem randsvd_oneLarge_kappa2_eq_alpha {n : ℕ}
    (hn : 2 ≤ n) (U V : RSqMat n) (alpha : ℝ) (ha : 1 ≤ alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    kappa2
        (randsvdMatrix U (oneLargeSingularValues alpha) V)
        (randsvdInverseMatrix U V (oneLargeSingularValues alpha)) = alpha := by
  have hapos : 0 < alpha := lt_of_lt_of_le zero_lt_one ha
  let k0 : Fin n := ⟨0, by omega⟩
  let k1 : Fin n := ⟨1, by omega⟩
  have hbound : ∀ i : Fin n, |oneLargeSingularValues alpha i.val| ≤ 1 := by
    intro i
    cases hi : i.val with
    | zero => simp [oneLargeSingularValues]
    | succ j =>
        simp only [oneLargeSingularValues, abs_inv, abs_of_pos hapos]
        exact (inv_le_one₀ hapos).mpr ha
  have hinvBound :
      ∀ i : Fin n, |(oneLargeSingularValues alpha i.val)⁻¹| ≤ alpha := by
    intro i
    cases hi : i.val with
    | zero => simpa [oneLargeSingularValues] using ha
    | succ j => simp [oneLargeSingularValues, abs_of_pos hapos]
  have hk0 : |oneLargeSingularValues alpha k0.val| = 1 := by
    simp [k0, oneLargeSingularValues]
  have hk1 : |(oneLargeSingularValues alpha k1.val)⁻¹| = alpha := by
    simp [k1, oneLargeSingularValues, abs_of_pos hapos]
  simpa using
    (kappa2_randsvdMatrix_eq_of_attained_bounds U V
      (oneLargeSingularValues alpha) hU hV 1 alpha (by norm_num)
      (le_trans (by norm_num) ha) hbound hinvBound k0 k1 hk0 hk1)

/-- The displayed inverse-factor construction is genuinely the inverse for
the one-large schedule. -/
theorem randsvd_oneLarge_isInverse {n : ℕ}
    (U V : RSqMat n) (alpha : ℝ) (ha : 0 < alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    IsInverse n
      (randsvdMatrix U (oneLargeSingularValues alpha) V)
      (randsvdInverseMatrix U V (oneLargeSingularValues alpha)) := by
  exact randsvdMatrix_isInverse U V (oneLargeSingularValues alpha) hU hV
    (fun i => ne_of_gt (oneLargeSingularValues_pos alpha ha i.val))

theorem oneSmallSingularValues_pos {n : ℕ} (alpha : ℝ) (ha : 0 < alpha)
    (i : ℕ) : 0 < oneSmallSingularValues n alpha i := by
  unfold oneSmallSingularValues
  split_ifs
  · exact inv_pos.mpr ha
  · norm_num

/-- For every nontrivial order, the one-small schedule also realizes the
source parameter exactly as `κ₂(A)`. -/
theorem randsvd_oneSmall_kappa2_eq_alpha {n : ℕ}
    (hn : 2 ≤ n) (U V : RSqMat n) (alpha : ℝ) (ha : 1 ≤ alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    kappa2
        (randsvdMatrix U (oneSmallSingularValues n alpha) V)
        (randsvdInverseMatrix U V (oneSmallSingularValues n alpha)) = alpha := by
  have hapos : 0 < alpha := lt_of_lt_of_le zero_lt_one ha
  let k0 : Fin n := ⟨0, by omega⟩
  let klast : Fin n := ⟨n - 1, by omega⟩
  have hk0ne : k0.val + 1 ≠ n := by
    dsimp [k0]
    omega
  have hklast : klast.val + 1 = n := by
    dsimp [klast]
    omega
  have hbound : ∀ i : Fin n, |oneSmallSingularValues n alpha i.val| ≤ 1 := by
    intro i
    unfold oneSmallSingularValues
    split_ifs
    · simp only [abs_inv, abs_of_pos hapos]
      exact (inv_le_one₀ hapos).mpr ha
    · norm_num
  have hinvBound :
      ∀ i : Fin n, |(oneSmallSingularValues n alpha i.val)⁻¹| ≤ alpha := by
    intro i
    unfold oneSmallSingularValues
    split_ifs
    · simp [abs_of_pos hapos]
    · simpa using ha
  have hk0 : |oneSmallSingularValues n alpha k0.val| = 1 := by
    simp [oneSmallSingularValues, hk0ne]
  have hkmin : |(oneSmallSingularValues n alpha klast.val)⁻¹| = alpha := by
    simp [oneSmallSingularValues, hklast, abs_of_pos hapos]
  simpa using
    (kappa2_randsvdMatrix_eq_of_attained_bounds U V
      (oneSmallSingularValues n alpha) hU hV 1 alpha (by norm_num)
      (le_trans (by norm_num) ha) hbound hinvBound k0 klast hk0 hkmin)

theorem randsvd_oneSmall_isInverse {n : ℕ}
    (U V : RSqMat n) (alpha : ℝ) (ha : 0 < alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    IsInverse n
      (randsvdMatrix U (oneSmallSingularValues n alpha) V)
      (randsvdInverseMatrix U V (oneSmallSingularValues n alpha)) := by
  exact randsvdMatrix_isInverse U V (oneSmallSingularValues n alpha) hU hV
    (fun i => ne_of_gt (oneSmallSingularValues_pos alpha ha i.val))

theorem geometricSingularValues_pos (n : ℕ) (alpha : ℝ) (ha : 0 < alpha)
    (i : ℕ) : 0 < geometricSingularValues n alpha i := by
  unfold geometricSingularValues
  exact pow_pos (inv_pos.mpr (Real.rpow_pos_of_pos ha _)) _

/-- For the source domain `n ≥ 2` and `α ≥ 1`, the geometric schedule
attains `1` and `α⁻¹`; hence its randsvd matrix has condition number exactly
the source parameter `α`. -/
theorem randsvd_geometric_kappa2_eq_alpha {n : ℕ}
    (hn : 2 ≤ n) (U V : RSqMat n) (alpha : ℝ) (ha : 1 ≤ alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    kappa2
        (randsvdMatrix U (geometricSingularValues n alpha) V)
        (randsvdInverseMatrix U V (geometricSingularValues n alpha)) = alpha := by
  have hapos : 0 < alpha := lt_of_lt_of_le zero_lt_one ha
  let d : ℕ := n - 1
  have hdpos : 0 < d := by omega
  have hdne : d ≠ 0 := Nat.ne_of_gt hdpos
  have hcast : (d : ℝ) = (n : ℝ) - 1 := by
    dsimp [d]
    rw [Nat.cast_sub (by omega)]
    norm_num
  let beta : ℝ := alpha ^ (1 / (n - 1 : ℝ))
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenpos : 0 < (n - 1 : ℝ) := by linarith
  have hexp_nonneg : 0 ≤ (1 / (n - 1 : ℝ)) :=
    (one_div_pos.mpr hdenpos).le
  have hbeta_pos : 0 < beta :=
    Real.rpow_pos_of_pos hapos _
  have hbeta_ge_one : 1 ≤ beta := by
    dsimp [beta]
    simpa using Real.rpow_le_rpow (x := (1 : ℝ)) (y := alpha)
      zero_le_one ha hexp_nonneg
  have hbeta_pow : beta ^ d = alpha := by
    dsimp [beta]
    rw [show (n - 1 : ℝ) = (d : ℝ) by linarith [hcast]]
    simpa [one_div] using
      Real.rpow_inv_natCast_pow (x := alpha) hapos.le hdne
  let k0 : Fin n := ⟨0, by omega⟩
  let klast : Fin n := ⟨n - 1, by omega⟩
  have hbound : ∀ i : Fin n, |geometricSingularValues n alpha i.val| ≤ 1 := by
    intro i
    have hqpos : 0 < beta⁻¹ := inv_pos.mpr hbeta_pos
    have hqle : beta⁻¹ ≤ 1 := (inv_le_one₀ hbeta_pos).2 hbeta_ge_one
    rw [show geometricSingularValues n alpha i.val = (beta⁻¹) ^ i.val by rfl]
    rw [abs_of_pos (pow_pos hqpos _)]
    exact pow_le_one₀ hqpos.le hqle
  have hinvBound :
      ∀ i : Fin n, |(geometricSingularValues n alpha i.val)⁻¹| ≤ alpha := by
    intro i
    have hi : i.val ≤ d := by
      dsimp [d]
      omega
    rw [show geometricSingularValues n alpha i.val = (beta⁻¹) ^ i.val by rfl]
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hbeta_pos _)]
    calc
      beta ^ i.val ≤ beta ^ d := pow_le_pow_right₀ hbeta_ge_one hi
      _ = alpha := hbeta_pow
  have hk0 : |geometricSingularValues n alpha k0.val| = 1 := by
    simp [k0, geometricSingularValues]
  have hklast : |(geometricSingularValues n alpha klast.val)⁻¹| = alpha := by
    rw [show geometricSingularValues n alpha klast.val = (beta⁻¹) ^ d by rfl]
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hbeta_pos _), hbeta_pow]
  simpa using
    (kappa2_randsvdMatrix_eq_of_attained_bounds U V
      (geometricSingularValues n alpha) hU hV 1 alpha (by norm_num)
      (le_trans (by norm_num) ha) hbound hinvBound k0 klast hk0 hklast)

theorem randsvd_geometric_isInverse {n : ℕ}
    (U V : RSqMat n) (alpha : ℝ) (ha : 0 < alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    IsInverse n
      (randsvdMatrix U (geometricSingularValues n alpha) V)
      (randsvdInverseMatrix U V (geometricSingularValues n alpha)) := by
  exact randsvdMatrix_isInverse U V (geometricSingularValues n alpha) hU hV
    (fun i => ne_of_gt (geometricSingularValues_pos n alpha ha i.val))

/-- For the source domain `n ≥ 2` and `α ≥ 1`, the arithmetic schedule
also attains `1` and `α⁻¹`; hence its randsvd matrix has condition number
exactly `α`. -/
theorem randsvd_arithmetic_kappa2_eq_alpha {n : ℕ}
    (hn : 2 ≤ n) (U V : RSqMat n) (alpha : ℝ) (ha : 1 ≤ alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    kappa2
        (randsvdMatrix U (arithmeticSingularValues n alpha) V)
        (randsvdInverseMatrix U V (arithmeticSingularValues n alpha)) = alpha := by
  have hapos : 0 < alpha := lt_of_lt_of_le zero_lt_one ha
  have hainvpos : 0 < alpha⁻¹ := inv_pos.mpr hapos
  have hainv_le_one : alpha⁻¹ ≤ 1 := (inv_le_one₀ hapos).2 ha
  have hc0 : 0 ≤ 1 - alpha⁻¹ := sub_nonneg.mpr hainv_le_one
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenpos : 0 < (n - 1 : ℝ) := by linarith
  let k0 : Fin n := ⟨0, by omega⟩
  let klast : Fin n := ⟨n - 1, by omega⟩
  have hsigma_bounds : ∀ i : Fin n,
      alpha⁻¹ ≤ arithmeticSingularValues n alpha i.val ∧
        arithmeticSingularValues n alpha i.val ≤ 1 := by
    intro i
    have hiNat : i.val ≤ n - 1 := by omega
    have hiR : (i.val : ℝ) ≤ n - 1 := by
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [← hcast]
      exact_mod_cast hiNat
    have hi0 : (0 : ℝ) ≤ i.val := by positivity
    have hfrac0 : 0 ≤ (i.val : ℝ) / (n - 1 : ℝ) :=
      div_nonneg hi0 hdenpos.le
    have hfrac1 : (i.val : ℝ) / (n - 1 : ℝ) ≤ 1 :=
      (div_le_one hdenpos).2 hiR
    have hterm0 : 0 ≤ (1 - alpha⁻¹) * ((i.val : ℝ) / (n - 1 : ℝ)) :=
      mul_nonneg hc0 hfrac0
    have hterm1 : (1 - alpha⁻¹) * ((i.val : ℝ) / (n - 1 : ℝ)) ≤
        1 - alpha⁻¹ :=
      mul_le_of_le_one_right hc0 hfrac1
    have hsigma : arithmeticSingularValues n alpha i.val =
        1 - (1 - alpha⁻¹) * ((i.val : ℝ) / (n - 1 : ℝ)) := by
      unfold arithmeticSingularValues
      ring
    rw [hsigma]
    constructor <;> linarith
  have hbound : ∀ i : Fin n, |arithmeticSingularValues n alpha i.val| ≤ 1 := by
    intro i
    have hlo := (hsigma_bounds i).1
    have hpos : 0 < arithmeticSingularValues n alpha i.val :=
      hainvpos.trans_le hlo
    rw [abs_of_pos hpos]
    exact (hsigma_bounds i).2
  have hinvBound : ∀ i : Fin n,
      |(arithmeticSingularValues n alpha i.val)⁻¹| ≤ alpha := by
    intro i
    have hlo := (hsigma_bounds i).1
    have hpos : 0 < arithmeticSingularValues n alpha i.val :=
      hainvpos.trans_le hlo
    rw [abs_of_pos (inv_pos.mpr hpos)]
    exact (inv_le_comm₀ hpos hapos).2 hlo
  have hk0 : |arithmeticSingularValues n alpha k0.val| = 1 := by
    simp [k0, arithmeticSingularValues]
  have hklast : |(arithmeticSingularValues n alpha klast.val)⁻¹| = alpha := by
    have hdenne : (n - 1 : ℝ) ≠ 0 := ne_of_gt hdenpos
    have hcast : ((n - 1 : ℕ) : ℝ) = (n - 1 : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hsigma : arithmeticSingularValues n alpha klast.val = alpha⁻¹ := by
      unfold arithmeticSingularValues
      dsimp [klast]
      rw [hcast]
      field_simp
      ring
    rw [hsigma, inv_inv, abs_of_pos hapos]
  simpa using
    (kappa2_randsvdMatrix_eq_of_attained_bounds U V
      (arithmeticSingularValues n alpha) hU hV 1 alpha (by norm_num)
      (le_trans (by norm_num) ha) hbound hinvBound k0 klast hk0 hklast)

theorem randsvd_arithmetic_isInverse {n : ℕ}
    (hn : 2 ≤ n) (U V : RSqMat n) (alpha : ℝ) (ha : 1 ≤ alpha)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V) :
    IsInverse n
      (randsvdMatrix U (arithmeticSingularValues n alpha) V)
      (randsvdInverseMatrix U V (arithmeticSingularValues n alpha)) := by
  have hapos : 0 < alpha := lt_of_lt_of_le zero_lt_one ha
  have hainvpos : 0 < alpha⁻¹ := inv_pos.mpr hapos
  have hainv_le_one : alpha⁻¹ ≤ 1 := (inv_le_one₀ hapos).2 ha
  have hc0 : 0 ≤ 1 - alpha⁻¹ := sub_nonneg.mpr hainv_le_one
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenpos : 0 < (n - 1 : ℝ) := by linarith
  apply randsvdMatrix_isInverse U V (arithmeticSingularValues n alpha) hU hV
  intro i
  apply ne_of_gt
  have hiNat : i.val ≤ n - 1 := by omega
  have hiR : (i.val : ℝ) ≤ n - 1 := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [← hcast]
    exact_mod_cast hiNat
  have hi0 : (0 : ℝ) ≤ i.val := by positivity
  have hfrac0 : 0 ≤ (i.val : ℝ) / (n - 1 : ℝ) :=
    div_nonneg hi0 hdenpos.le
  have hfrac1 : (i.val : ℝ) / (n - 1 : ℝ) ≤ 1 :=
    (div_le_one hdenpos).2 hiR
  have hterm1 : (1 - alpha⁻¹) * ((i.val : ℝ) / (n - 1 : ℝ)) ≤
      1 - alpha⁻¹ :=
    mul_le_of_le_one_right hc0 hfrac1
  have hsigma : arithmeticSingularValues n alpha i.val =
      1 - (1 - alpha⁻¹) * ((i.val : ℝ) / (n - 1 : ℝ)) := by
    unfold arithmeticSingularValues
    ring
  rw [hsigma]
  linarith


end NumStability
