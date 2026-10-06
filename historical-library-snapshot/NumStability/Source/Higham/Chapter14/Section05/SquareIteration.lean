/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Data.Real.Star
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open Filter Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder Topology

attribute [local instance] Matrix.instL2OpNormedRing Matrix.instL2OpNormedAlgebra

/-!
# Higham Chapter 14, Section 14.5: the exact square Schulz iteration

Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Section
14.5, p. 278, gives Newton's method for the inverse in the form

`X_(k+1) = X_k (2I - A X_k) = (2I - X_k A) X_k`.

This file formalizes that exact-arithmetic iteration, both residual-square
recurrences, the closed residual formula `E_k = E_0^(2^k)`, the precise
operator-norm convergence criterion, and the source initialization
`X_0 = alpha A^T`, `0 < alpha < 2 / ||A||_2^2` for nonsingular square real
matrices.  It contains no floating-point stability claim.
-/

/-- Higham, 2nd ed., Section 14.5, p. 278: one exact Schulz step
`X ↦ X(2I - AX)`. -/
noncomputable def higham14SchulzStep {n : Nat}
    (A X : RSqMat n) : RSqMat n :=
  X * ((2 : Real) • (1 : RSqMat n) - A * X)

/-- The exact Schulz sequence beginning at `X0`. -/
noncomputable def higham14SchulzIterate {n : Nat}
    (A X0 : RSqMat n) : Nat -> RSqMat n
  | 0 => X0
  | k + 1 => higham14SchulzStep A (higham14SchulzIterate A X0 k)

@[simp] theorem higham14SchulzIterate_zero {n : Nat}
    (A X0 : RSqMat n) :
    higham14SchulzIterate A X0 0 = X0 := rfl

@[simp] theorem higham14SchulzIterate_succ {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    higham14SchulzIterate A X0 (k + 1) =
      higham14SchulzStep A (higham14SchulzIterate A X0 k) := rfl

/-- The right inverse residual `I - AX`. -/
def higham14SchulzRightResidual {n : Nat}
    (A X : RSqMat n) : RSqMat n :=
  1 - A * X

/-- The left inverse residual `I - XA`. -/
def higham14SchulzLeftResidual {n : Nat}
    (A X : RSqMat n) : RSqMat n :=
  1 - X * A

/-- The two printed forms of the Schulz update are exactly equal. -/
theorem higham14SchulzStep_eq_left {n : Nat}
    (A X : RSqMat n) :
    higham14SchulzStep A X =
      ((2 : Real) • (1 : RSqMat n) - X * A) * X := by
  simp only [higham14SchulzStep, two_smul]
  noncomm_ring

/-- Higham Section 14.5 exact recurrence for `E_k = I - AX_k`:
`E_(k+1) = E_k^2`. -/
theorem higham14SchulzRightResidual_step {n : Nat}
    (A X : RSqMat n) :
    higham14SchulzRightResidual A (higham14SchulzStep A X) =
      higham14SchulzRightResidual A X ^ 2 := by
  simp only [higham14SchulzRightResidual, higham14SchulzStep, two_smul,
    pow_two]
  noncomm_ring

/-- Higham Section 14.5 exact recurrence for `E_k = I - X_kA`:
`E_(k+1) = E_k^2`. -/
theorem higham14SchulzLeftResidual_step {n : Nat}
    (A X : RSqMat n) :
    higham14SchulzLeftResidual A (higham14SchulzStep A X) =
      higham14SchulzLeftResidual A X ^ 2 := by
  rw [higham14SchulzStep_eq_left]
  simp only [higham14SchulzLeftResidual, two_smul, pow_two]
  noncomm_ring

/-- Closed exact right-residual recurrence printed on p. 278:
`E_k = E_0^(2^k)`. -/
theorem higham14SchulzRightResidual_iterate {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    higham14SchulzRightResidual A (higham14SchulzIterate A X0 k) =
      higham14SchulzRightResidual A X0 ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [higham14SchulzIterate_succ, higham14SchulzRightResidual_step, ih,
        Nat.pow_succ, pow_mul]

/-- Closed exact left-residual recurrence printed on p. 278:
`E_k = E_0^(2^k)`. -/
theorem higham14SchulzLeftResidual_iterate {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    higham14SchulzLeftResidual A (higham14SchulzIterate A X0 k) =
      higham14SchulzLeftResidual A X0 ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [higham14SchulzIterate_succ, higham14SchulzLeftResidual_step, ih,
        Nat.pow_succ, pow_mul]

/-- Literal quadratic residual contraction for the right residual. -/
theorem higham14SchulzRightResidual_norm_next_le_sq {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    ‖higham14SchulzRightResidual A (higham14SchulzIterate A X0 (k + 1))‖ <=
      ‖higham14SchulzRightResidual A (higham14SchulzIterate A X0 k)‖ ^ 2 := by
  rw [higham14SchulzIterate_succ, higham14SchulzRightResidual_step, pow_two]
  let E : RSqMat n :=
    higham14SchulzRightResidual A (higham14SchulzIterate A X0 k)
  simpa [E, pow_two] using (norm_mul_le E E)

/-- Literal quadratic residual contraction for the left residual. -/
theorem higham14SchulzLeftResidual_norm_next_le_sq {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    ‖higham14SchulzLeftResidual A (higham14SchulzIterate A X0 (k + 1))‖ <=
      ‖higham14SchulzLeftResidual A (higham14SchulzIterate A X0 k)‖ ^ 2 := by
  rw [higham14SchulzIterate_succ, higham14SchulzLeftResidual_step, pow_two]
  let E : RSqMat n :=
    higham14SchulzLeftResidual A (higham14SchulzIterate A X0 k)
  simpa [E, pow_two] using (norm_mul_le E E)

/-- Exact double-exponential right-residual bound.  This is the quantitative
form behind the source's phrase “quadratic convergence”. -/
theorem higham14SchulzRightResidual_norm_le_initial_pow {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    ‖higham14SchulzRightResidual A (higham14SchulzIterate A X0 k)‖ <=
      ‖higham14SchulzRightResidual A X0‖ ^ (2 ^ k) := by
  rw [higham14SchulzRightResidual_iterate]
  exact norm_pow_le' _ (Nat.pow_pos (by norm_num : 0 < 2))

/-- Exact double-exponential left-residual bound. -/
theorem higham14SchulzLeftResidual_norm_le_initial_pow {n : Nat}
    (A X0 : RSqMat n) (k : Nat) :
    ‖higham14SchulzLeftResidual A (higham14SchulzIterate A X0 k)‖ <=
      ‖higham14SchulzLeftResidual A X0‖ ^ (2 ^ k) := by
  rw [higham14SchulzLeftResidual_iterate]
  exact norm_pow_le' _ (Nat.pow_pos (by norm_num : 0 < 2))

/-- Precise right-residual convergence criterion: if `‖I - AX0‖₂ < 1`,
then the exact Schulz residual converges to zero. -/
theorem higham14SchulzRightResidual_tendsto_zero_of_norm_lt_one {n : Nat}
    (A X0 : RSqMat n)
    (h0 : ‖higham14SchulzRightResidual A X0‖ < 1) :
    Tendsto
      (fun k => higham14SchulzRightResidual A
        (higham14SchulzIterate A X0 k))
      atTop (nhds 0) := by
  have hpow : Tendsto
      (fun m : Nat => higham14SchulzRightResidual A X0 ^ m)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one h0
  have htwo : Tendsto (fun k : Nat => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa only [higham14SchulzRightResidual_iterate] using hpow.comp htwo

/-- Precise left-residual convergence criterion: if `‖I - X0A‖₂ < 1`,
then the exact Schulz residual converges to zero. -/
theorem higham14SchulzLeftResidual_tendsto_zero_of_norm_lt_one {n : Nat}
    (A X0 : RSqMat n)
    (h0 : ‖higham14SchulzLeftResidual A X0‖ < 1) :
    Tendsto
      (fun k => higham14SchulzLeftResidual A
        (higham14SchulzIterate A X0 k))
      atTop (nhds 0) := by
  have hpow : Tendsto
      (fun m : Nat => higham14SchulzLeftResidual A X0 ^ m)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one h0
  have htwo : Tendsto (fun k : Nat => 2 ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  simpa only [higham14SchulzLeftResidual_iterate] using hpow.comp htwo

/-- The right-residual criterion yields convergence to any supplied left
inverse.  For square matrices the inverse is unique, so this is the exact
convergence-to-`A⁻¹` statement without totalizing singular inversion. -/
theorem higham14SchulzIterate_tendsto_inverse_of_rightResidual_norm_lt_one
    {n : Nat} (A Ainv X0 : RSqMat n)
    (hInv : IsLeftInverse n A Ainv)
    (h0 : ‖higham14SchulzRightResidual A X0‖ < 1) :
    Tendsto (higham14SchulzIterate A X0) atTop (nhds Ainv) := by
  have hInvMat : Ainv * A = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply] using hInv i j
  have hrepr : higham14SchulzIterate A X0 =
      fun k => Ainv - Ainv * higham14SchulzRightResidual A
        (higham14SchulzIterate A X0 k) := by
    funext k
    let X := higham14SchulzIterate A X0 k
    calc
      X = (Ainv * A) * X := by rw [hInvMat, one_mul]
      _ = Ainv - Ainv * higham14SchulzRightResidual A X := by
        simp only [higham14SchulzRightResidual]
        noncomm_ring
  have hres :=
    higham14SchulzRightResidual_tendsto_zero_of_norm_lt_one A X0 h0
  rw [hrepr]
  simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hres)

/-- The left-residual criterion yields convergence to any supplied right
inverse. -/
theorem higham14SchulzIterate_tendsto_inverse_of_leftResidual_norm_lt_one
    {n : Nat} (A Ainv X0 : RSqMat n)
    (hInv : IsRightInverse n A Ainv)
    (h0 : ‖higham14SchulzLeftResidual A X0‖ < 1) :
    Tendsto (higham14SchulzIterate A X0) atTop (nhds Ainv) := by
  have hInvMat : A * Ainv = (1 : RSqMat n) := by
    ext i j
    simpa [Matrix.mul_apply] using hInv i j
  have hrepr : higham14SchulzIterate A X0 =
      fun k => Ainv - higham14SchulzLeftResidual A
        (higham14SchulzIterate A X0 k) * Ainv := by
    funext k
    let X := higham14SchulzIterate A X0 k
    calc
      X = X * (A * Ainv) := by rw [hInvMat, mul_one]
      _ = Ainv - higham14SchulzLeftResidual A X * Ainv := by
        simp only [higham14SchulzLeftResidual]
        noncomm_ring
  have hres :=
    higham14SchulzLeftResidual_tendsto_zero_of_norm_lt_one A X0 h0
  rw [hrepr]
  simpa using tendsto_const_nhds.sub (hres.mul tendsto_const_nhds)

/-- Higham Section 14.5's printed initialization criterion.  If `A` is
nonsingular, `X0 = alpha A^T`, and `0 < alpha < 2 / ||A||_2^2`, then the
initial right residual has operator `2`-norm strictly below one. -/
theorem higham14Schulz_source_initial_residual_norm_lt_one {n : Nat}
    (A : RSqMat n) (hdet : A.det ≠ 0)
    (alpha : Real) (halpha : 0 < alpha)
    (hbound : alpha < 2 / ‖A‖ ^ 2) :
    ‖higham14SchulzRightResidual A (alpha • A.transpose)‖ < 1 := by
  classical
  let G : RSqMat n := A * A.transpose
  have hnorm_sq_ne : ‖A‖ ^ 2 ≠ 0 := by
    intro hzero
    have : alpha < 0 := by simpa [hzero] using hbound
    exact (not_lt_of_ge (le_of_lt halpha)) this
  have hnorm_sq_pos : 0 < ‖A‖ ^ 2 :=
    lt_of_le_of_ne (sq_nonneg ‖A‖) (Ne.symm hnorm_sq_ne)
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have hAzero : A = 0 := Subsingleton.elim _ _
    simp [hAzero] at hnorm_sq_pos
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  letI : NormOneClass (RSqMat n) := ⟨by
    rw [show (1 : RSqMat n) = Matrix.diagonal (fun _ => (1 : Real)) from
        Matrix.diagonal_one.symm,
      Matrix.l2_opNorm_diagonal, Pi.norm_def,
      Finset.sup_const Finset.univ_nonempty]
    simp⟩
  have hAunit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hAtunit : IsUnit A.transpose :=
    (Matrix.isUnit_transpose (A := A)).mpr hAunit
  have hGpsd : Matrix.PosSemidef G := by
    simpa [G] using Matrix.posSemidef_conjTranspose_mul_self A.transpose
  have hGunit : IsUnit G := by
    simpa [G] using hAunit.mul hAtunit
  have hGpos : Matrix.PosDef G := hGpsd.posDef_iff_isUnit.mpr hGunit
  let hGh : G.IsHermitian := hGpos.isHermitian
  let lam : Fin n → Real := hGh.eigenvalues
  let U := hGh.eigenvectorUnitary
  let D : RSqMat n := Matrix.diagonal (fun i => 1 - alpha * lam i)
  have hGnorm : ‖G‖ = ‖A‖ ^ 2 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (A := Aᴴ)
    have hAtnorm : ‖A.transpose‖ = ‖A‖ := by
      simpa using (Matrix.l2_opNorm_conjTranspose A)
    simpa [G, pow_two, hAtnorm] using h
  have hlam_pos (i : Fin n) : 0 < lam i := by
    exact hGpos.eigenvalues_pos i
  have hlam_le (i : Fin n) : lam i ≤ ‖G‖ := by
    have hspectrum : lam i ∈ spectrum Real G := by
      exact hGh.eigenvalues_mem_spectrum_real i
    have hnorm := spectrum.norm_le_norm_of_mem hspectrum
    simpa [Real.norm_eq_abs, abs_of_pos (hlam_pos i)] using hnorm
  have halpha_norm : alpha * ‖A‖ ^ 2 < 2 :=
    (lt_div_iff₀ hnorm_sq_pos).mp hbound
  have hdiag_lt (i : Fin n) : |1 - alpha * lam i| < 1 := by
    have hprod_pos : 0 < alpha * lam i := mul_pos halpha (hlam_pos i)
    have hprod_lt : alpha * lam i < 2 := by
      calc
        alpha * lam i ≤ alpha * ‖G‖ :=
          mul_le_mul_of_nonneg_left (hlam_le i) (le_of_lt halpha)
        _ = alpha * ‖A‖ ^ 2 := by rw [hGnorm]
        _ < 2 := halpha_norm
    rw [abs_lt]
    constructor <;> linarith
  have hGspec :
      G = (U : RSqMat n) * Matrix.diagonal lam * (U : RSqMat n)ᴴ := by
    simpa [U, lam, Function.comp_def, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose] using
      hGh.spectral_theorem
  have hD : D = 1 - alpha • Matrix.diagonal lam := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, hij]
  have hresG :
      higham14SchulzRightResidual A (alpha • A.transpose) =
        1 - alpha • G := by
    simp [higham14SchulzRightResidual, G]
  have hresdiag :
      higham14SchulzRightResidual A (alpha • A.transpose) =
        (U : RSqMat n) * D * (U : RSqMat n)ᴴ := by
    rw [hresG, hD, hGspec]
    simp only [mul_sub, sub_mul, mul_one]
    have hU : (U : RSqMat n) * (U : RSqMat n)ᴴ = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Unitary.coe_mul_star_self U)
    have hUt : (U : RSqMat n) * (U : RSqMat n).transpose = 1 := by
      simpa using hU
    simp [hUt, mul_assoc]
  rw [hresdiag]
  have hUHU : (U : RSqMat n)ᴴ * (U : RSqMat n) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Unitary.coe_star_mul_self U)
  have hUnorm : ‖(U : RSqMat n)‖ = 1 := by
    have hsq := Matrix.l2_opNorm_conjTranspose_mul_self (U : RSqMat n)
    rw [hUHU, norm_one] at hsq
    nlinarith [norm_nonneg (U : RSqMat n)]
  have hUHnorm : ‖(U : RSqMat n)ᴴ‖ = 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hUnorm
  have hrecover :
      D = (U : RSqMat n)ᴴ *
        ((U : RSqMat n) * D * (U : RSqMat n)ᴴ) * (U : RSqMat n) := by
    symm
    calc
      (U : RSqMat n)ᴴ *
          ((U : RSqMat n) * D * (U : RSqMat n)ᴴ) * (U : RSqMat n) =
          (U : RSqMat n)ᴴ * ((U : RSqMat n) * D) := by
        simp only [mul_assoc, hUHU, mul_one]
      _ = ((U : RSqMat n)ᴴ * (U : RSqMat n)) * D :=
        (mul_assoc _ _ _).symm
      _ = D := by rw [hUHU, one_mul]
  have hconj_le :
      ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ ≤ ‖D‖ := by
    calc
      ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ ≤
          ‖(U : RSqMat n)‖ * ‖D‖ * ‖(U : RSqMat n)ᴴ‖ :=
        norm_mul₃_le
      _ = ‖D‖ := by rw [hUnorm, hUHnorm]; ring
  have hD_le :
      ‖D‖ ≤ ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ := by
    calc
      ‖D‖ = ‖(U : RSqMat n)ᴴ *
          ((U : RSqMat n) * D * (U : RSqMat n)ᴴ) * (U : RSqMat n)‖ :=
        congrArg norm hrecover
      _ ≤ ‖(U : RSqMat n)ᴴ‖ *
          ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ *
            ‖(U : RSqMat n)‖ := norm_mul₃_le
      _ = ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ := by
        rw [hUnorm, hUHnorm]
        ring
  have hnorm_conj :
      ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ = ‖D‖ :=
    le_antisymm hconj_le hD_le
  calc
    ‖(U : RSqMat n) * D * (U : RSqMat n)ᴴ‖ = ‖D‖ := hnorm_conj
    _ = ‖fun i => 1 - alpha * lam i‖ := Matrix.l2_opNorm_diagonal _
    _ < 1 := (pi_norm_lt_iff (by norm_num)).mpr fun i => by
      simpa [Real.norm_eq_abs] using hdiag_lt i

/-- The source initialization therefore makes the exact Schulz iterates
converge to the nonsingular inverse of `A`. -/
theorem higham14Schulz_source_initialization_tendsto_inverse {n : Nat}
    (A : RSqMat n) (hdet : A.det ≠ 0)
    (alpha : Real) (halpha : 0 < alpha)
    (hbound : alpha < 2 / ‖A‖ ^ 2) :
    Tendsto (higham14SchulzIterate A (alpha • A.transpose)) atTop
      (nhds (nonsingInv n A)) := by
  apply higham14SchulzIterate_tendsto_inverse_of_rightResidual_norm_lt_one
    A (nonsingInv n A) (alpha • A.transpose)
  · exact (isInverse_nonsingInv_of_det_ne_zero n A hdet).1
  · exact higham14Schulz_source_initial_residual_norm_lt_one
      A hdet alpha halpha hbound

end NumStability
