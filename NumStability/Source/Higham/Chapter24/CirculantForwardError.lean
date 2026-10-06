/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.StructuredMixedStability

namespace NumStability

open scoped Matrix.Norms.L2Operator

/-!
# The forward-error consequence after Higham's Theorem 24.3

The paragraph following Theorem 24.3 says that standard perturbation theory
bounds the forward error by a multiple of `kappa_2(C) * u`.  This file supplies
the missing bridge.  It first proves a finite common-radius perturbation lemma,
then converts the theorem's generator perturbation into an operator-norm
matrix perturbation, and finally instantiates the literal four-stage solver.

The multiplier below is deliberately explicit.  It depends on the fixed FFT
length and on the coefficient controlling the twiddle error, but not on the
unit roundoff.
-/

private theorem higham24_finEuclideanNorm_add_le {n : Nat}
    (x y : Fin n -> Complex) :
    higham24FinEuclideanNorm (x + y) <=
      higham24FinEuclideanNorm x + higham24FinEuclideanNorm y := by
  simpa [higham24FinEuclideanNorm] using
    norm_add_le
      (WithLp.toLp (2 : ENNReal) x : EuclideanSpace Complex (Fin n))
      (WithLp.toLp (2 : ENNReal) y : EuclideanSpace Complex (Fin n))

private theorem higham24_finEuclideanNorm_sub_le {n : Nat}
    (x y : Fin n -> Complex) :
    higham24FinEuclideanNorm (x - y) <=
      higham24FinEuclideanNorm x + higham24FinEuclideanNorm y := by
  simpa [higham24FinEuclideanNorm] using
    norm_sub_le
      (WithLp.toLp (2 : ENNReal) x : EuclideanSpace Complex (Fin n))
      (WithLp.toLp (2 : ENNReal) y : EuclideanSpace Complex (Fin n))

/-- The `2`-norm condition number represented by an explicitly supplied
inverse.  The inverse equations are hypotheses of the theorems that use it. -/
noncomputable def higham24Condition2 {n : Nat}
    (C Cinv : Matrix (Fin n) (Fin n) Complex) : Real :=
  ‖C‖ * ‖Cinv‖

/-- A two-sided inverse has condition number at least one on a nonempty
finite-dimensional space. -/
theorem higham24_one_le_condition2_of_rightInverse {n : Nat} [NeZero n]
    (C Cinv : Matrix (Fin n) (Fin n) Complex)
    (hRight : C * Cinv = 1) :
    1 <= higham24Condition2 C Cinv := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (NeZero.pos n)
  calc
    1 = ‖(1 : Matrix (Fin n) (Fin n) Complex)‖ := by
      rw [show (1 : Matrix (Fin n) (Fin n) Complex) =
          Matrix.diagonal 1 by ext i j; simp [Matrix.one_apply],
        Matrix.l2_opNorm_diagonal]
      simp
    _ = ‖C * Cinv‖ := by rw [hRight]
    _ <= ‖C‖ * ‖Cinv‖ := Matrix.l2_opNorm_mul C Cinv
    _ = higham24Condition2 C Cinv := rfl

/-- Standard finite perturbation theory in the precise form needed after
Theorem 24.3.

All three relative perturbations have common radius `r`.  If both `r` and
`kappa_2(C) r` are at most one half, the computed vector has relative forward
error at most `10 kappa_2(C) r`.  The proof includes the theorem's additional
solution perturbation `deltaX`, which is measured relative to `xHat`. -/
theorem higham24_mixed_forward_error_le_ten_condition_radius
    {n : Nat} [NeZero n]
    (C Cinv DeltaC : Matrix (Fin n) (Fin n) Complex)
    (b xHat deltaB deltaX : Fin n -> Complex) (r : Real)
    (hLeft : Cinv * C = 1) (hRight : C * Cinv = 1)
    (hEquation : (C + DeltaC).mulVec (xHat + deltaX) = b + deltaB)
    (hDeltaC : ‖DeltaC‖ <= r * ‖C‖)
    (hDeltaB : higham24FinEuclideanNorm deltaB <=
      r * higham24FinEuclideanNorm b)
    (hDeltaX : higham24FinEuclideanNorm deltaX <=
      r * higham24FinEuclideanNorm xHat)
    (hr : 0 <= r) (hrHalf : r <= 1 / 2)
    (hConditionHalf : higham24Condition2 C Cinv * r <= 1 / 2) :
    let x := Cinv.mulVec b
    higham24FinEuclideanNorm (xHat - x) <=
      10 * higham24Condition2 C Cinv * r *
        higham24FinEuclideanNorm x := by
  dsimp only
  let x : Fin n -> Complex := Cinv.mulVec b
  let y : Fin n -> Complex := xHat + deltaX
  let kappa : Real := higham24Condition2 C Cinv
  let nx : Real := higham24FinEuclideanNorm x
  let ny : Real := higham24FinEuclideanNorm y
  let d : Real := higham24FinEuclideanNorm (y - x)
  let e : Real := higham24FinEuclideanNorm (xHat - x)
  have hxEquation : C.mulVec x = b := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec, hRight, Matrix.one_mulVec]
  have hResidual : C.mulVec (y - x) = deltaB - DeltaC.mulVec y := by
    rw [Matrix.mulVec_sub, hxEquation]
    have h := hEquation
    rw [Matrix.add_mulVec] at h
    change C.mulVec y + DeltaC.mulVec y = b + deltaB at h
    exact sub_eq_iff_eq_add.mpr (by
      calc
        C.mulVec y = b + deltaB - DeltaC.mulVec y :=
          eq_sub_of_add_eq h
        _ = b + (deltaB - DeltaC.mulVec y) := by abel
        _ = (deltaB - DeltaC.mulVec y) + b := add_comm _ _)
  have hInverseResidual : y - x =
      Cinv.mulVec (deltaB - DeltaC.mulVec y) := by
    calc
      y - x = (1 : Matrix (Fin n) (Fin n) Complex).mulVec (y - x) := by simp
      _ = (Cinv * C).mulVec (y - x) := by rw [hLeft]
      _ = Cinv.mulVec (C.mulVec (y - x)) := by
        rw [Matrix.mulVec_mulVec]
      _ = Cinv.mulVec (deltaB - DeltaC.mulVec y) := by rw [hResidual]
  have hbNorm : higham24FinEuclideanNorm b <= ‖C‖ * nx := by
    simpa [nx, x, hxEquation] using higham24_l2OpNorm_mulVec_norm_le C x
  have hDeltaBNorm : higham24FinEuclideanNorm deltaB <=
      r * ‖C‖ * nx := by
    calc
      higham24FinEuclideanNorm deltaB <=
          r * higham24FinEuclideanNorm b := hDeltaB
      _ <= r * (‖C‖ * nx) := mul_le_mul_of_nonneg_left hbNorm hr
      _ = r * ‖C‖ * nx := by ring
  have hDeltaCYNorm : higham24FinEuclideanNorm (DeltaC.mulVec y) <=
      r * ‖C‖ * ny := by
    calc
      higham24FinEuclideanNorm (DeltaC.mulVec y) <=
          ‖DeltaC‖ * higham24FinEuclideanNorm y :=
        higham24_l2OpNorm_mulVec_norm_le DeltaC y
      _ <= (r * ‖C‖) * higham24FinEuclideanNorm y :=
        mul_le_mul_of_nonneg_right hDeltaC (norm_nonneg _)
      _ = r * ‖C‖ * ny := by rfl
  have hDiffNorm : higham24FinEuclideanNorm
      (deltaB - DeltaC.mulVec y) <=
        r * ‖C‖ * nx + r * ‖C‖ * ny := by
    exact (higham24_finEuclideanNorm_sub_le deltaB (DeltaC.mulVec y)).trans
      (add_le_add hDeltaBNorm hDeltaCYNorm)
  have hdMain : d <= kappa * r * (nx + ny) := by
    calc
      d = higham24FinEuclideanNorm
          (Cinv.mulVec (deltaB - DeltaC.mulVec y)) := by
        dsimp [d]
        rw [hInverseResidual]
      _ <= ‖Cinv‖ * higham24FinEuclideanNorm
          (deltaB - DeltaC.mulVec y) :=
        higham24_l2OpNorm_mulVec_norm_le Cinv _
      _ <= ‖Cinv‖ * (r * ‖C‖ * nx + r * ‖C‖ * ny) :=
        mul_le_mul_of_nonneg_left hDiffNorm (norm_nonneg _)
      _ = kappa * r * (nx + ny) := by
        dsimp [kappa, higham24Condition2]
        ring
  have hySplit : y = x + (y - x) := by abel
  have hny : ny <= nx + d := by
    dsimp [ny]
    rw [hySplit]
    simpa [nx, d] using higham24_finEuclideanNorm_add_le x (y - x)
  have hkappa0 : 0 <= kappa := by
    dsimp [kappa, higham24Condition2]
    positivity
  have hq0 : 0 <= kappa * r := mul_nonneg hkappa0 hr
  have hdPre : d <= kappa * r * (2 * nx + d) := by
    calc
      d <= kappa * r * (nx + ny) := hdMain
      _ <= kappa * r * (nx + (nx + d)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hny nx) hq0
      _ = kappa * r * (2 * nx + d) := by ring
  have hd0 : 0 <= d := by
    dsimp [d, higham24FinEuclideanNorm]
    exact norm_nonneg _
  have hqD : kappa * r * d <= (1 / 2 : Real) * d :=
    mul_le_mul_of_nonneg_right hConditionHalf hd0
  have hdFour : d <= 4 * kappa * r * nx := by
    nlinarith
  have hxHatSplit : xHat - x = (y - x) - deltaX := by
    dsimp [y]
    abel
  have heBasic : e <= d + r * higham24FinEuclideanNorm xHat := by
    calc
      e = higham24FinEuclideanNorm ((y - x) - deltaX) := by
        dsimp [e]
        rw [hxHatSplit]
      _ <= higham24FinEuclideanNorm (y - x) +
          higham24FinEuclideanNorm deltaX :=
        higham24_finEuclideanNorm_sub_le (y - x) deltaX
      _ <= d + r * higham24FinEuclideanNorm xHat :=
        add_le_add_right hDeltaX d
  have hxHatNorm : higham24FinEuclideanNorm xHat <= nx + e := by
    have hxHat : xHat = x + (xHat - x) := by abel
    rw [hxHat]
    simpa [nx, e] using higham24_finEuclideanNorm_add_le x (xHat - x)
  have hePre : e <= d + r * (nx + e) := by
    exact heBasic.trans (add_le_add_right
      (mul_le_mul_of_nonneg_left hxHatNorm hr) d)
  have he0 : 0 <= e := by
    dsimp [e, higham24FinEuclideanNorm]
    exact norm_nonneg _
  have hrE : r * e <= (1 / 2 : Real) * e :=
    mul_le_mul_of_nonneg_right hrHalf he0
  have heTwo : e <= 2 * d + 2 * r * nx := by
    nlinarith
  have hkappaOne : 1 <= kappa := by
    dsimp [kappa]
    exact higham24_one_le_condition2_of_rightInverse C Cinv hRight
  have hrNx : r * nx <= kappa * r * nx := by
    have hnx0 : 0 <= nx := by
      dsimp [nx, higham24FinEuclideanNorm]
      exact norm_nonneg _
    have hrle : r <= kappa * r := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkappaOne) hr]
    exact mul_le_mul_of_nonneg_right hrle hnx0
  change e <= 10 * kappa * r * nx
  nlinarith

/-- The spectral norm of a length-`2^t` circulant is bounded by `sqrt(2^t)`
times the Euclidean norm of its generator. -/
theorem higham24_circulant_l2OpNorm_le_sqrt_card_mul
    (t : Nat) (c : Fin (2 ^ t) -> Complex) :
    ‖higham24Circulant c‖ <=
      Real.sqrt (((2 ^ t : Nat) : Real)) * higham24FinEuclideanNorm c := by
  let s : Real := Real.sqrt (((2 ^ t : Nat) : Real))
  let v : Fin (2 ^ t) -> Complex := higham24DFTApply c
  have hs : 0 < s := by dsimp [s]; positivity
  have hpi : ‖v‖ <= higham24FinEuclideanNorm v := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2
    intro i
    dsimp [v, higham24FinEuclideanNorm]
    exact PiLp.norm_apply_le
      (WithLp.toLp (2 : ENNReal) (higham24DFTApply c)) i
  have hfac := higham24_dftInverse_diagonal_dft_eq_circulant t v
  have hinv : higham24DFTInverseApply v = c := by
    dsimp [v]
    exact higham24_inverse_after_forward c
  rw [hinv] at hfac
  rw [← hfac]
  calc
    ‖higham24DFTInverse (2 ^ t) * Matrix.diagonal v * higham24DFT (2 ^ t)‖ <=
        ‖higham24DFTInverse (2 ^ t) * Matrix.diagonal v‖ *
          ‖higham24DFT (2 ^ t)‖ :=
      Matrix.l2_opNorm_mul _ _
    _ <= (‖higham24DFTInverse (2 ^ t)‖ * ‖Matrix.diagonal v‖) *
          ‖higham24DFT (2 ^ t)‖ :=
      mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
        (norm_nonneg _)
    _ = (s⁻¹ * ‖v‖) * s := by
      rw [higham24_dftInverse_l2_opNorm, Matrix.l2_opNorm_diagonal,
        higham24_dft_l2_opNorm]
    _ = ‖v‖ := by field_simp [hs.ne']
    _ <= higham24FinEuclideanNorm v := hpi
    _ = s * higham24FinEuclideanNorm c := by
      exact higham24_dftApply_finEuclideanNorm_eq t c

/-- The generator, being the first column, has Euclidean norm at most the
circulant's spectral norm. -/
theorem higham24_generator_norm_le_circulant_l2OpNorm
    (t : Nat) (c : Fin (2 ^ t) -> Complex) :
    higham24FinEuclideanNorm c <= ‖higham24Circulant c‖ := by
  let e : Fin (2 ^ t) -> Complex := Pi.single 0 1
  have he : higham24FinEuclideanNorm e = 1 := by
    simp [e, higham24FinEuclideanNorm]
  have haction : (higham24Circulant c).mulVec e = c := by
    change (higham24Circulant c).mulVec (Pi.single 0 1) = c
    rw [Matrix.mulVec_single_one]
    funext i
    exact Matrix.circulant_col_zero_eq c i
  have h := higham24_l2OpNorm_mulVec_norm_le (higham24Circulant c) e
  simpa [haction, he] using h

/-- A relative Euclidean perturbation of a circulant generator produces a
relative spectral-norm matrix perturbation with the explicit factor
`sqrt(2^t)`. -/
theorem higham24_circulant_generator_perturbation_l2OpNorm_le
    (t : Nat) (c deltaC : Fin (2 ^ t) -> Complex) (r : Real)
    (hr : 0 <= r)
    (hdelta : higham24FinEuclideanNorm deltaC <=
      r * higham24FinEuclideanNorm c) :
    ‖higham24Circulant deltaC‖ <=
      (Real.sqrt (((2 ^ t : Nat) : Real)) * r) *
        ‖higham24Circulant c‖ := by
  let s : Real := Real.sqrt (((2 ^ t : Nat) : Real))
  have hs0 : 0 <= s := by dsimp [s]; positivity
  calc
    ‖higham24Circulant deltaC‖ <=
        s * higham24FinEuclideanNorm deltaC :=
      higham24_circulant_l2OpNorm_le_sqrt_card_mul t deltaC
    _ <= s * (r * higham24FinEuclideanNorm c) :=
      mul_le_mul_of_nonneg_left hdelta hs0
    _ <= s * (r * ‖higham24Circulant c‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (higham24_generator_norm_le_circulant_l2OpNorm t c) hr) hs0
    _ = (s * r) * ‖higham24Circulant c‖ := by ring

/-- The explicit coefficient multiplying `u` in the first-order radius used
by the forward-error theorem. -/
noncomputable def higham24ForwardRadiusLinearCoefficient
    (t : Nat) (cMu : Real) : Real :=
  (t : Real) * higham24EtaLinearCoefficient cMu + 6 +
    higham24LiteralTheorem24_3QuadraticCoefficient t cMu

theorem higham24_eta_le_linearCoefficient_mul_u
    (fp : FPModel)
    (mu cMu : Real) (hmu : 0 <= mu) (hcMu : 0 <= cMu)
    (hmuLinear : mu <= cMu * fp.u)
    (hfourHalf : (4 : Real) * fp.u <= 1 / 2) :
    higham24Eta mu (gamma fp 4) <=
      higham24EtaLinearCoefficient cMu * fp.u := by
  have hgamma8 : gamma fp 4 <= 8 * fp.u := by
    convert gamma_le_two_mul_n_u_of_nu_le_half fp 4 hfourHalf using 1 <;> ring
  have huOne : fp.u <= 1 := by linarith [fp.u_nonneg]
  have hmuC : mu <= cMu := by
    exact hmuLinear.trans (by
      nlinarith [mul_nonneg hcMu (sub_nonneg.mpr huOne)])
  have hfactor0 : 0 <= Real.sqrt 2 + mu :=
    add_nonneg (Real.sqrt_nonneg _) hmu
  calc
    higham24Eta mu (gamma fp 4) =
        mu + gamma fp 4 * (Real.sqrt 2 + mu) := rfl
    _ <= cMu * fp.u + (8 * fp.u) * (Real.sqrt 2 + cMu) := by
      exact add_le_add hmuLinear
        (mul_le_mul hgamma8 (by linarith) hfactor0
          (mul_nonneg (by norm_num) fp.u_nonneg))
    _ = higham24EtaLinearCoefficient cMu * fp.u := by
      dsimp [higham24EtaLinearCoefficient]
      ring

theorem higham24_quadraticCoefficient_nonneg
    (t : Nat) (cMu : Real) (hcMu : 0 <= cMu) :
    0 <= higham24LiteralTheorem24_3QuadraticCoefficient t cMu := by
  dsimp [higham24LiteralTheorem24_3QuadraticCoefficient,
    higham24EtaLinearCoefficient]
  positivity

/-- The explicit quadratic-radius form of Theorem 24.3 is bounded by one
fixed coefficient times `u`. -/
theorem higham24_quadraticRadius_le_forwardLinearCoefficient_mul_u
    (fp : FPModel)
    (t : Nat) (mu cMu : Real) (hmu : 0 <= mu) (hcMu : 0 <= cMu)
    (hmuLinear : mu <= cMu * fp.u)
    (hfourHalf : (4 : Real) * fp.u <= 1 / 2) :
    (t : Real) * higham24Eta mu (gamma fp 4) + 6 * fp.u +
        higham24LiteralTheorem24_3QuadraticCoefficient t cMu * fp.u ^ 2 <=
      higham24ForwardRadiusLinearCoefficient t cMu * fp.u := by
  have heta := higham24_eta_le_linearCoefficient_mul_u
    fp mu cMu hmu hcMu hmuLinear hfourHalf
  have huOne : fp.u <= 1 := by linarith [fp.u_nonneg]
  have hK0 := higham24_quadraticCoefficient_nonneg t cMu hcMu
  have hEtaTerm : (t : Real) * higham24Eta mu (gamma fp 4) <=
      (t : Real) * higham24EtaLinearCoefficient cMu * fp.u := by
    calc
      (t : Real) * higham24Eta mu (gamma fp 4) <=
          (t : Real) * (higham24EtaLinearCoefficient cMu * fp.u) :=
        mul_le_mul_of_nonneg_left heta (Nat.cast_nonneg _)
      _ = _ := by ring
  have hQuadratic :
      higham24LiteralTheorem24_3QuadraticCoefficient t cMu * fp.u ^ 2 <=
        higham24LiteralTheorem24_3QuadraticCoefficient t cMu * fp.u := by
    have huu : fp.u ^ 2 <= fp.u := by nlinarith [fp.u_nonneg]
    exact mul_le_mul_of_nonneg_left huu hK0
  dsimp [higham24ForwardRadiusLinearCoefficient]
  linarith

/-- **Forward-error paragraph after Theorem 24.3, for the literal solver.**

The exact solution is `Cinv * b`, `kappa` is the spectral condition number
`‖C(c)‖₂ ‖Cinv‖₂`, and the displayed multiplier is independent of `fp.u`.
The smallness hypotheses are the standard finite interpretation of the
source's first-order statement. -/
theorem higham24_theorem24_3_literal_forward_error_multiple_kappa_u
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : forall s, Higham24BitIndex s -> Complex)
    (mu cMu : Real) (hmu : 0 <= mu) (hcMu : 0 <= cMu)
    (hmuLinear : mu <= cMu * fp.u)
    (hw : forall s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : Nat) (c b : Fin (2 ^ t) -> Complex)
    (hfourHalf : (4 : Real) * fp.u <= 1 / 2)
    (haHalf : (t : Real) * higham24Eta mu (gamma fp 4) <= 1 / 2)
    (hsigmaHalf : Real.sqrt 2 * gamma fp 4 <= 1 / 2)
    (hrhoHalf : higham24RelativeFFTBound t
      (higham24Eta mu (gamma fp 4)) <= 1 / 2)
    (hd : forall i,
      higham24LiteralRoundedCirculantEigenvalues fp weight t c i ≠ 0)
    (Cinv : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) Complex)
    (hLeft : Cinv * higham24Circulant c = 1)
    (hRight : higham24Circulant c * Cinv = 1)
    (hRadiusHalf :
      Real.sqrt (((2 ^ t : Nat) : Real)) *
          higham24ForwardRadiusLinearCoefficient t cMu * fp.u <= 1 / 2)
    (hConditionHalf :
      higham24Condition2 (higham24Circulant c) Cinv *
        (Real.sqrt (((2 ^ t : Nat) : Real)) *
          higham24ForwardRadiusLinearCoefficient t cMu * fp.u) <= 1 / 2) :
    let x := Cinv.mulVec b
    let xHat := higham24LiteralRoundedCirculantSolve fp weight t c b
    let kappa := higham24Condition2 (higham24Circulant c) Cinv
    let multiple := 10 * Real.sqrt (((2 ^ t : Nat) : Real)) *
      higham24ForwardRadiusLinearCoefficient t cMu
    higham24FinEuclideanNorm (xHat - x) <=
      multiple * kappa * fp.u * higham24FinEuclideanNorm x := by
  dsimp only
  let radius : Real :=
    (t : Real) * higham24Eta mu (gamma fp 4) + 6 * fp.u +
      higham24LiteralTheorem24_3QuadraticCoefficient t cMu * fp.u ^ 2
  let s : Real := Real.sqrt (((2 ^ t : Nat) : Real))
  let linear : Real := higham24ForwardRadiusLinearCoefficient t cMu
  let C : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) Complex := higham24Circulant c
  let kappa : Real := higham24Condition2 C Cinv
  have hradiusLinear : radius <= linear * fp.u := by
    exact higham24_quadraticRadius_le_forwardLinearCoefficient_mul_u
      fp t mu cMu hmu hcMu hmuLinear hfourHalf
  have heta0 : 0 <= higham24Eta mu (gamma fp 4) := by
    dsimp [higham24Eta]
    exact add_nonneg hmu
      (mul_nonneg (gamma_nonneg fp hgamma4)
        (add_nonneg (Real.sqrt_nonneg _) hmu))
  have hradius0 : 0 <= radius := by
    dsimp [radius]
    exact add_nonneg
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) heta0)
        (mul_nonneg (by norm_num) fp.u_nonneg))
      (mul_nonneg (higham24_quadraticCoefficient_nonneg t cMu hcMu)
        (sq_nonneg _))
  have hsOne : 1 <= s := by
    dsimp [s]
    rw [Real.one_le_sqrt]
    exact_mod_cast (Nat.one_le_pow t 2 (by norm_num))
  have hcommon0 : 0 <= s * radius :=
    mul_nonneg (le_trans (by norm_num) hsOne) hradius0
  have hcommonHalf : s * radius <= 1 / 2 := by
    calc
      s * radius <= s * (linear * fp.u) :=
        mul_le_mul_of_nonneg_left hradiusLinear (le_trans (by norm_num) hsOne)
      _ = s * linear * fp.u := by ring
      _ <= 1 / 2 := hRadiusHalf
  have hkappa0 : 0 <= kappa := by
    dsimp [kappa, higham24Condition2]
    positivity
  have hconditionActual : kappa * (s * radius) <= 1 / 2 := by
    calc
      kappa * (s * radius) <= kappa * (s * (linear * fp.u)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hradiusLinear
            (le_trans (by norm_num) hsOne)) hkappa0
      _ = kappa * (s * linear * fp.u) := by ring
      _ <= 1 / 2 := hConditionHalf
  obtain ⟨deltaC, deltaX, deltaB, hEq, hC, hB, hX⟩ :=
    higham24_theorem24_3_literal_quadraticRemainder
      fp hgamma4 weight mu cMu hmu hcMu hmuLinear hw t c b
        hfourHalf haHalf hsigmaHalf hrhoHalf hd
  have hMatrix : ‖higham24Circulant deltaC‖ <=
      (s * radius) * ‖C‖ := by
    simpa [s, radius, C] using
      higham24_circulant_generator_perturbation_l2OpNorm_le
        t c deltaC radius hradius0 hC
  have hBCommon : higham24FinEuclideanNorm deltaB <=
      (s * radius) * higham24FinEuclideanNorm b := by
    calc
      higham24FinEuclideanNorm deltaB <=
          radius * higham24FinEuclideanNorm b := hB
      _ <= (s * radius) * higham24FinEuclideanNorm b := by
        have : radius <= s * radius := by nlinarith
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hXCommon : higham24FinEuclideanNorm deltaX <=
      (s * radius) * higham24FinEuclideanNorm
        (higham24LiteralRoundedCirculantSolve fp weight t c b) := by
    calc
      higham24FinEuclideanNorm deltaX <= radius *
          higham24FinEuclideanNorm
            (higham24LiteralRoundedCirculantSolve fp weight t c b) := hX
      _ <= (s * radius) * higham24FinEuclideanNorm
          (higham24LiteralRoundedCirculantSolve fp weight t c b) := by
        have : radius <= s * radius := by nlinarith
        exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
  have hEqMatrix : (C + higham24Circulant deltaC).mulVec
      (higham24LiteralRoundedCirculantSolve fp weight t c b + deltaX) =
        b + deltaB := by
    simpa [C, higham24_circulant_add] using hEq
  have hforward := higham24_mixed_forward_error_le_ten_condition_radius
    C Cinv (higham24Circulant deltaC) b
      (higham24LiteralRoundedCirculantSolve fp weight t c b)
      deltaB deltaX (s * radius) hLeft hRight hEqMatrix hMatrix
      hBCommon hXCommon hcommon0 hcommonHalf hconditionActual
  dsimp only at hforward
  calc
    higham24FinEuclideanNorm
        (higham24LiteralRoundedCirculantSolve fp weight t c b - Cinv.mulVec b) <=
      10 * kappa * (s * radius) * higham24FinEuclideanNorm (Cinv.mulVec b) := by
        simpa [C, kappa] using hforward
    _ <= 10 * kappa * (s * (linear * fp.u)) *
        higham24FinEuclideanNorm (Cinv.mulVec b) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hradiusLinear
            (le_trans (by norm_num) hsOne))
          (mul_nonneg (by norm_num) hkappa0))
        (norm_nonneg _)
    _ = (10 * s * linear) * kappa * fp.u *
        higham24FinEuclideanNorm (Cinv.mulVec b) := by ring

end NumStability
