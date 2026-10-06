/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28

/-! # Higham Chapter 28: the Pascal cube root of the identity

This module formalizes the matrix returned by MATLAB's `pascal(n,2)` as the
clockwise rotation of Higham's signed Pascal involution, with the prescribed
parity sign, and proves the printed all-orders identity `T³ = I`.
-/

namespace NumStability

open scoped BigOperators
open Polynomial

/-- The polynomial form of the alternating binomial convolution needed for
the square of the rotated signed Pascal matrix. -/
private theorem pascalAlternatingPolynomial (m j : ℕ) :
    (∑ k ∈ Finset.range (m + j + 1),
      (((-1 : ℝ) ^ k * Nat.choose m k) •
        ((Polynomial.X + 1 : Polynomial ℝ) ^ (m + j - k)))) =
      Polynomial.X ^ m * (Polynomial.X + 1) ^ j := by
  let F : ℕ → Polynomial ℝ := fun k =>
    (((-1 : ℝ) ^ k * Nat.choose m k) •
      ((Polynomial.X + 1 : Polynomial ℝ) ^ (m + j - k)))
  have hsubset : Finset.range (m + 1) ⊆ Finset.range (m + j + 1) := by
    exact Finset.range_mono (by omega)
  calc
    (∑ k ∈ Finset.range (m + j + 1),
      (((-1 : ℝ) ^ k * Nat.choose m k) •
        ((Polynomial.X + 1 : Polynomial ℝ) ^ (m + j - k)))) =
        ∑ k ∈ Finset.range (m + 1), F k := by
      symm
      apply Finset.sum_subset hsubset
      intro k hkbig hk
      have hmk : m < k := by
        have : ¬ k < m + 1 := by simpa using hk
        omega
      simp [F, Nat.choose_eq_zero_of_lt hmk]
    _ = (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℝ) •
            ((Polynomial.X + 1 : Polynomial ℝ) ^ (m - k) *
              (-1 : Polynomial ℝ) ^ k)) *
          (Polynomial.X + 1) ^ j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k hk
      have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      simp only [F, smul_eq_C_mul]
      rw [show m + j - k = (m - k) + j by omega, pow_add]
      simp only [map_mul, map_pow, map_neg, map_one]
      ring
    _ = Polynomial.X ^ m * (Polynomial.X + 1) ^ j := by
      rw [show (∑ k ∈ Finset.range (m + 1),
          (Nat.choose m k : ℝ) •
            ((Polynomial.X + 1 : Polynomial ℝ) ^ (m - k) *
              (-1 : Polynomial ℝ) ^ k)) = Polynomial.X ^ m from by
        calc
          (∑ k ∈ Finset.range (m + 1),
            (Nat.choose m k : ℝ) •
              ((Polynomial.X + 1 : Polynomial ℝ) ^ (m - k) *
                (-1 : Polynomial ℝ) ^ k)) =
              ∑ k ∈ Finset.range (m + 1),
                (-1 : Polynomial ℝ) ^ k *
                  (Polynomial.X + 1) ^ (m - k) *
                    (Nat.choose m k : Polynomial ℝ) := by
            apply Finset.sum_congr rfl
            intro k hk
            simp only [smul_eq_C_mul]
            rw [Polynomial.C_eq_natCast]
            ring
          _ = ((-1 : Polynomial ℝ) + (Polynomial.X + 1)) ^ m := by
            rw [add_pow]
          _ = Polynomial.X ^ m := by ring_nf]

/-- Coefficient extraction from `pascalAlternatingPolynomial`. -/
private theorem pascalAlternatingChooseSum
    (m j i : ℕ) (hi : i ≤ m + j) :
    (∑ k ∈ Finset.range (m + j + 1),
      (-1 : ℝ) ^ k * Nat.choose m k * Nat.choose (m + j - k) i) =
      Nat.choose j (m + j - i) := by
  let coeffHom : Polynomial ℝ →+ ℝ :=
    { toFun := fun p => p.coeff i
      map_zero' := Polynomial.coeff_zero i
      map_add' := fun p q => Polynomial.coeff_add p q i }
  have hcoeff := congrArg coeffHom (pascalAlternatingPolynomial m j)
  simp only [map_sum] at hcoeff
  change (∑ k ∈ Finset.range (m + j + 1),
      (((((-1 : ℝ) ^ k * Nat.choose m k) •
        ((Polynomial.X + 1 : Polynomial ℝ) ^ (m + j - k))) :
          Polynomial ℝ).coeff i)) =
    (Polynomial.X ^ m * (Polynomial.X + 1) ^ j).coeff i at hcoeff
  simp only [Polynomial.coeff_smul, Polynomial.coeff_X_add_one_pow,
    Polynomial.coeff_X_pow_mul'] at hcoeff
  simp only [smul_eq_mul] at hcoeff
  rw [hcoeff]
  by_cases hmi : m ≤ i
  · rw [if_pos hmi]
    have hsub : i - m ≤ j := by omega
    rw [← Nat.choose_symm hsub]
    have hind : j - (i - m) = m + j - i := by omega
    rw [hind]
  · rw [if_neg hmi]
    have hjlt : j < m + j - i := by omega
    simp [Nat.choose_eq_zero_of_lt hjlt]

/-- The alternating convolution in the indexing used by a clockwise rotation
of the signed Pascal matrix. -/
private theorem rotatedPascalChooseSum
    (N i j : ℕ) (hi : i ≤ N) (hj : j ≤ N) :
    (∑ k ∈ Finset.range (N + 1),
      (-1 : ℝ) ^ k * Nat.choose (N - k) i * Nat.choose (N - j) k) =
      Nat.choose j (N - i) := by
  have h := pascalAlternatingChooseSum (N - j) j i (by omega)
  have hNj : N - j + j = N := Nat.sub_add_cancel hj
  rw [hNj] at h
  calc
    (∑ k ∈ Finset.range (N + 1),
      (-1 : ℝ) ^ k * Nat.choose (N - k) i * Nat.choose (N - j) k) =
        ∑ k ∈ Finset.range (N + 1),
          (-1 : ℝ) ^ k * Nat.choose (N - j) k * Nat.choose (N - k) i := by
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = Nat.choose j (N - i) := h

/-- The clockwise rotation of Higham's signed Pascal involution, before the
parity correction used by `pascal(n,2)`. -/
noncomputable def rotatedSignedPascal (n : ℕ) : RSqMat n :=
  fun i j => signedPascal n (Fin.rev j) i

@[simp]
theorem rotatedSignedPascal_apply {n : ℕ} (i j : Fin n) :
    rotatedSignedPascal n i j =
      (-1 : ℝ) ^ i.val * Nat.choose (n - 1 - j.val) i.val := by
  simp only [rotatedSignedPascal, signedPascal, Fin.rev]
  have hsub : n - (j.val + 1) = n - 1 - j.val := by omega
  rw [hsub]

/-- Exact entry formula for the square of the rotated signed Pascal matrix. -/
theorem rotatedSignedPascal_square_apply
    {n : ℕ} (i j : Fin n) :
    (rotatedSignedPascal n * rotatedSignedPascal n) i j =
      (-1 : ℝ) ^ i.val * Nat.choose j.val (n - 1 - i.val) := by
  rw [Matrix.mul_apply]
  simp only [rotatedSignedPascal_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ =>
      ((-1 : ℝ) ^ i.val * Nat.choose (n - 1 - k) i.val) *
        ((-1 : ℝ) ^ k * Nat.choose (n - 1 - j.val) k)) n]
  have hn : 0 < n := Nat.zero_lt_of_lt i.isLt
  have hn1 : n - 1 + 1 = n :=
    Nat.sub_add_cancel (by omega : 1 ≤ n)
  rw [show Finset.range n = Finset.range (n - 1 + 1) by rw [hn1]]
  have hsum := rotatedPascalChooseSum (n - 1) i.val j.val (by omega) (by omega)
  calc
    (∑ k ∈ Finset.range (n - 1 + 1),
      ((-1 : ℝ) ^ i.val * Nat.choose (n - 1 - k) i.val) *
        ((-1 : ℝ) ^ k * Nat.choose (n - 1 - j.val) k)) =
        (-1 : ℝ) ^ i.val *
          ∑ k ∈ Finset.range (n - 1 + 1),
            (-1 : ℝ) ^ k * Nat.choose (n - 1 - k) i.val *
              Nat.choose (n - 1 - j.val) k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ = (-1 : ℝ) ^ i.val * Nat.choose j.val (n - 1 - i.val) := by
      rw [hsum]

/-- The uncorrected clockwise rotation has cube equal to the parity sign. -/
theorem rotatedSignedPascal_cube (n : ℕ) :
    rotatedSignedPascal n * rotatedSignedPascal n * rotatedSignedPascal n =
      (-1 : ℝ) ^ (n + 1) • (1 : RSqMat n) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [rotatedSignedPascal_square_apply, rotatedSignedPascal_apply]
  have hiN : i.val ≤ n - 1 := by omega
  have hε : (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ (n - 1) := by
    calc
      (-1 : ℝ) ^ (n + 1) = (-1 : ℝ) ^ ((n - 1) + 2) := by
        congr 1
        omega
      _ = (-1 : ℝ) ^ (n - 1) := by simp [pow_add]
  have hsplit : n - 1 = i.val + (n - 1 - i.val) := by omega
  have hpowN : (-1 : ℝ) ^ (n - 1) =
      (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ (n - 1 - i.val) := by
    conv_lhs => rw [hsplit]
    rw [pow_add]
  have hsign : (-1 : ℝ) ^ i.val =
      (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n - 1 - i.val) := by
    let b : ℝ := (-1 : ℝ) ^ (n - 1 - i.val)
    calc
      (-1 : ℝ) ^ i.val = (-1 : ℝ) ^ i.val * (b * b) := by
        simp [b, ← mul_pow]
      _ = ((-1 : ℝ) ^ i.val * b) * b := by ring
      _ = (-1 : ℝ) ^ (n - 1) * b := by rw [hpowN]
      _ = (-1 : ℝ) ^ (n + 1) *
          (-1 : ℝ) ^ (n - 1 - i.val) := by rw [hε]
  calc
    (∑ k : Fin n,
      ((-1 : ℝ) ^ i.val * Nat.choose k.val (n - 1 - i.val)) *
        ((-1 : ℝ) ^ k.val * Nat.choose (n - 1 - j.val) k.val)) =
        (-1 : ℝ) ^ (n + 1) *
          ∑ k : Fin n, signedPascal n (Fin.rev j) k *
            signedPascal n k (Fin.rev i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [signedPascal, Fin.rev]
      have hsubj : n - (j.val + 1) = n - 1 - j.val := by omega
      have hsubi : n - (i.val + 1) = n - 1 - i.val := by omega
      rw [hsubj, hsubi, hsign]
      ring
    _ = (-1 : ℝ) ^ (n + 1) *
        (signedPascal n * signedPascal n) (Fin.rev j) (Fin.rev i) := by
      rw [Matrix.mul_apply]
    _ = (-1 : ℝ) ^ (n + 1) *
        (1 : RSqMat n) (Fin.rev j) (Fin.rev i) := by
      rw [signedPascal_mul_self]
    _ = ((-1 : ℝ) ^ (n + 1) • (1 : RSqMat n)) i j := by
      by_cases hij : i = j
      · subst j
        simp
      · have hrev : Fin.rev j ≠ Fin.rev i :=
          Fin.rev_injective.ne (Ne.symm hij)
        simp [hij, hrev]

/-- Higham, 2nd ed., Section 28.4, pp. 520-521: `pascal(n,2)` is obtained by
rotating the signed Pascal involution clockwise and multiplying by `-1` when
`n` is even.  The parity factor `(-1)^(n+1)` expresses exactly that rule. -/
noncomputable def pascalIdentityCubeRootCandidate (n : ℕ) : RSqMat n :=
  fun i j => (-1 : ℝ) ^ (n + 1) * signedPascal n (Fin.rev j) i

/-- Closed entry formula for the rotated signed-Pascal candidate. -/
@[simp]
theorem pascalIdentityCubeRootCandidate_apply
    {n : ℕ} (i j : Fin n) :
    pascalIdentityCubeRootCandidate n i j =
      (-1 : ℝ) ^ (n + 1 + i.val) *
        Nat.choose (n - 1 - j.val) i.val := by
  simp only [pascalIdentityCubeRootCandidate, signedPascal, Fin.rev]
  have hsub : n - (j.val + 1) = n - 1 - j.val := by omega
  rw [hsub, pow_add]
  ring

theorem pascalIdentityCubeRootCandidate_eq_smul (n : ℕ) :
    pascalIdentityCubeRootCandidate n =
      (-1 : ℝ) ^ (n + 1) • rotatedSignedPascal n := by
  ext i j
  rfl

/-- Higham's rotated signed-Pascal matrix is a cube root of the identity for
every order, including the empty order. -/
theorem pascalIdentityCubeRootCandidate_cube (n : ℕ) :
    pascalIdentityCubeRootCandidate n * pascalIdentityCubeRootCandidate n *
        pascalIdentityCubeRootCandidate n = 1 := by
  rw [pascalIdentityCubeRootCandidate_eq_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [rotatedSignedPascal_cube]
  simp only [smul_smul]
  have hsignsq : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    simp
  have hfour : (-1 : ℝ) ^ (n + 1) *
      ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) *
        (-1 : ℝ) ^ (n + 1) = 1 := by
    calc
      (-1 : ℝ) ^ (n + 1) *
          ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) *
            (-1 : ℝ) ^ (n + 1) =
        (((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) *
          ((-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1))) := by ring
      _ = 1 := by rw [hsignsq]; norm_num
  rw [hfour]
  simp

end NumStability
