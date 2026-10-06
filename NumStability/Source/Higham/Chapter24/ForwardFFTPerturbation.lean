/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.CirculantSystems
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace NumStability

open scoped Matrix.Norms.L2Operator

/-!
# Produced forward-FFT perturbations for Higham Chapter 24

This file turns the pointwise result for the literal rounded radix-2 executor
into the input-dependent matrix perturbations used in equations (24.6)--(24.7).
The rank-one construction is total: at a zero input it selects the zero matrix,
and its action theorem asks for (and the FFT proof derives) the necessary fact
that the output error is then zero.
-/

/-- A source-facing Euclidean norm for an ordinary `Fin`-indexed complex
vector. -/
noncomputable def higham24FinEuclideanNorm {n : ℕ} (x : Fin n → ℂ) : ℝ :=
  ‖(WithLp.toLp (2 : ENNReal) x : EuclideanSpace ℂ (Fin n))‖

/-- The zero-safe rank-one matrix that sends `x` to `error` when that action is
algebraically possible.  For `x ≠ 0` this is
`error * xᴴ / ‖x‖₂²`; for `x = 0` it is the zero matrix. -/
noncomputable def higham24RankOneActionPerturbation {n : ℕ}
    (error x : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  if x = 0 then 0
  else
    ((higham24FinEuclideanNorm x : ℂ) ^ 2)⁻¹ •
      Matrix.vecMulVec error (star x)

private theorem higham24_star_dot_self {n : ℕ} (x : Fin n → ℂ) :
    dotProduct (star x) x =
      (higham24FinEuclideanNorm x : ℂ) ^ 2 := by
  let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp (2 : ENNReal) x
  calc
    dotProduct (star x) x = dotProduct x (star x) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = inner ℂ xE xE := by
      exact (EuclideanSpace.inner_toLp_toLp x x).symm
    _ = (‖xE‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K xE
    _ = (higham24FinEuclideanNorm x : ℂ) ^ 2 := by
      rfl

/-- The zero-safe rank-one matrix has the requested action whenever the target
error vanishes at a zero input.  This premise is necessary: no matrix can map
the zero vector to a nonzero error. -/
theorem higham24_rankOneActionPerturbation_mulVec {n : ℕ}
    (error x : Fin n → ℂ) (hzero : x = 0 → error = 0) :
    (higham24RankOneActionPerturbation error x).mulVec x = error := by
  by_cases hx : x = 0
  · subst x
    simp [higham24RankOneActionPerturbation, hzero rfl]
  · rw [higham24RankOneActionPerturbation, if_neg hx,
      Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      higham24_star_dot_self]
    have hnorm : higham24FinEuclideanNorm x ≠ 0 := by
      intro h
      have hxE : (WithLp.toLp (2 : ENNReal) x :
          EuclideanSpace ℂ (Fin n)) = 0 := norm_eq_zero.mp h
      apply hx
      have := congrArg WithLp.ofLp hxE
      simpa using this
    have hnormC : (higham24FinEuclideanNorm x : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hnorm
    ext i
    simp only [op_smul_eq_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [hnormC]

/-- The operator `2`-norm of an unscaled complex outer product. -/
theorem higham24_vecMulVec_l2_opNorm {n : ℕ}
    (error x : Fin n → ℂ) :
    ‖(Matrix.vecMulVec error (star x) : Matrix (Fin n) (Fin n) ℂ)‖ =
      higham24FinEuclideanNorm error * higham24FinEuclideanNorm x := by
  let eE : EuclideanSpace ℂ (Fin n) := WithLp.toLp (2 : ENNReal) error
  let xE : EuclideanSpace ℂ (Fin n) := WithLp.toLp (2 : ENNReal) x
  have hrank := InnerProductSpace.symm_toEuclideanLin_rankOne eE xE
  rw [← hrank, Matrix.l2_opNorm_def]
  rw [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have hclm :
      LinearMap.toContinuousLinearMap
          (InnerProductSpace.rankOne ℂ eE xE).toLinearMap =
        InnerProductSpace.rankOne ℂ eE xE := by
    ext z
    rfl
  rw [hclm]
  simp [eE, xE, higham24FinEuclideanNorm]

/-- The zero-safe producer has the standard rank-one operator-norm bound. -/
theorem higham24_rankOneActionPerturbation_norm_le {n : ℕ}
    (error x : Fin n → ℂ) :
    ‖higham24RankOneActionPerturbation error x‖ ≤
      higham24FinEuclideanNorm error / higham24FinEuclideanNorm x := by
  by_cases hx : x = 0
  · subst x
    simp [higham24RankOneActionPerturbation, higham24FinEuclideanNorm]
  · rw [higham24RankOneActionPerturbation, if_neg hx, norm_smul,
      higham24_vecMulVec_l2_opNorm]
    have hnorm : 0 < higham24FinEuclideanNorm x := by
      apply lt_of_le_of_ne (norm_nonneg _)
      intro h
      apply hx
      have hxE : (WithLp.toLp (2 : ENNReal) x :
          EuclideanSpace ℂ (Fin n)) = 0 := norm_eq_zero.mp h.symm
      have := congrArg WithLp.ofLp hxE
      simpa using this
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hnorm]
    apply le_of_eq
    field_simp [hnorm.ne']

/-- The unnormalized Chapter 24 DFT has the standard column Gram matrix. -/
theorem higham24_dft_conjTranspose_mul_self (t : ℕ) :
    Matrix.conjTranspose (higham24DFT (2 ^ t)) * higham24DFT (2 ^ t) =
      ((2 ^ t : ℕ) : ℂ) • (1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, higham24DFT, Matrix.of_apply,
    Matrix.smul_apply, Matrix.one_apply]
  simpa [smul_eq_mul] using
    (higham9_13_fourierVandermonde_column_gram i j)

/-- The unnormalized length-`2^t` DFT has operator `2`-norm `sqrt (2^t)`. -/
theorem higham24_dft_l2_opNorm (t : ℕ) :
    ‖higham24DFT (2 ^ t)‖ = Real.sqrt (((2 ^ t : ℕ) : ℝ)) := by
  have hgram := congrArg norm (higham24_dft_conjTranspose_mul_self t)
  have hnonempty : Nonempty (Fin (2 ^ t)) := Fin.pos_iff_nonempty.mp (by positivity)
  letI : Nonempty (Fin (2 ^ t)) := hnonempty
  have hone :
      ‖(1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ)‖ = 1 := by
    rw [show (1 : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ) =
        Matrix.diagonal 1 by ext i j; simp [Matrix.one_apply]]
    rw [Matrix.l2_opNorm_diagonal]
    simp
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul, hone,
    mul_one, Complex.norm_natCast] at hgram
  calc
    ‖higham24DFT (2 ^ t)‖ = Real.sqrt (‖higham24DFT (2 ^ t)‖ ^ 2) := by
      rw [Real.sqrt_sq (norm_nonneg _)]
    _ = Real.sqrt (((2 ^ t : ℕ) : ℝ)) := by
      rw [pow_two, hgram]

/-- The ordinary input vector, reindexed into the little-endian recursive
domain consumed by the literal decimation-in-time executor. -/
def higham24Radix2BinaryInput (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    Higham24BitIndex t → ℂ :=
  fun p => x (higham24BitIndexLEEquiv t p)

/-- Literal rounded forward FFT, exposed in ordinary DFT output order. -/
noncomputable def higham24RoundedRadix2FFTFin
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  fun k => higham24RoundedRadix2FFT fp weight t
    (higham24Radix2BinaryInput t x) ((higham24BitIndexBEEquiv t).symm k)

/-- The exact literal FFT, with the same input and output reindexings, is the
canonical Chapter 24 DFT action. -/
theorem higham24_radix2FFTFin_eq_dftApply
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) (k : Fin (2 ^ t)) :
    higham24Radix2FFT t (higham24Radix2BinaryInput t x)
        ((higham24BitIndexBEEquiv t).symm k) =
      higham24DFTApply x k := by
  simpa [higham24Radix2BinaryInput] using
    (higham24Radix2FFT_eq_dftApply t
      (higham24Radix2BinaryInput t x)
      ((higham24BitIndexBEEquiv t).symm k))

/-- Pointwise output error of the literal rounded executor in ordinary DFT
order. -/
noncomputable def higham24ForwardFFTError
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) : Fin (2 ^ t) → ℂ :=
  higham24RoundedRadix2FFTFin fp weight t x - higham24DFTApply x

private theorem higham24_finEuclideanNorm_reindex_be
    (t : ℕ) (z : Higham24BitIndex t → ℂ) :
    higham24FinEuclideanNorm
        (fun k => z ((higham24BitIndexBEEquiv t).symm k)) =
      higham24BinaryEuclideanNorm t z := by
  rw [← higham24_binaryVecNorm2_eq_euclideanNorm]
  unfold higham24FinEuclideanNorm higham24BinaryVecNorm2
  rw [complexVecLpNorm_two_eq_toLp]

/-- The ordinary-index error is exactly the big-endian transport of the
literal recursive executor's error. -/
theorem higham24_forwardFFTError_apply
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) (k : Fin (2 ^ t)) :
    higham24ForwardFFTError fp weight t x k =
      (higham24RoundedRadix2FFT fp weight t
          (higham24Radix2BinaryInput t x) -
        higham24Radix2FFT t (higham24Radix2BinaryInput t x))
        ((higham24BitIndexBEEquiv t).symm k) := by
  simp only [higham24ForwardFFTError, higham24RoundedRadix2FFTFin,
    Pi.sub_apply]
  rw [higham24_radix2FFTFin_eq_dftApply]

/-- Fin-index form of the literal pointwise forward-error theorem. -/
theorem higham24_forwardFFTError_norm_le
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    higham24FinEuclideanNorm (higham24ForwardFFTError fp weight t x) ≤
      ((1 + higham24Eta mu (gamma fp 4)) ^ t - 1) *
        higham24FinEuclideanNorm (higham24DFTApply x) := by
  let binaryError :=
    higham24RoundedRadix2FFT fp weight t (higham24Radix2BinaryInput t x) -
      higham24Radix2FFT t (higham24Radix2BinaryInput t x)
  let exactBinary :=
    higham24Radix2FFT t (higham24Radix2BinaryInput t x)
  have hbound := higham24_roundedRadix2FFT_euclidean_forward_bound
    fp hgamma4 weight mu hmu hw t (higham24Radix2BinaryInput t x)
  have herror : higham24ForwardFFTError fp weight t x =
      fun k => binaryError ((higham24BitIndexBEEquiv t).symm k) := by
    funext k
    exact higham24_forwardFFTError_apply fp weight t x k
  have hexact : higham24DFTApply x =
      fun k => exactBinary ((higham24BitIndexBEEquiv t).symm k) := by
    funext k
    exact (higham24_radix2FFTFin_eq_dftApply t x k).symm
  rw [herror, hexact, higham24_finEuclideanNorm_reindex_be,
    higham24_finEuclideanNorm_reindex_be]
  exact hbound

private theorem higham24_finEuclideanNorm_eq_zero_iff {n : ℕ}
    (x : Fin n → ℂ) : higham24FinEuclideanNorm x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hxE : (WithLp.toLp (2 : ENNReal) x :
        EuclideanSpace ℂ (Fin n)) = 0 := norm_eq_zero.mp h
    have := congrArg WithLp.ofLp hxE
    simpa using this
  · intro h
    subst x
    simp [higham24FinEuclideanNorm]

/-- The DFT action is bounded by its sharp operator norm. -/
theorem higham24_dftApply_finEuclideanNorm_le
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    higham24FinEuclideanNorm (higham24DFTApply x) ≤
      Real.sqrt (((2 ^ t : ℕ) : ℝ)) * higham24FinEuclideanNorm x := by
  simpa [higham24FinEuclideanNorm, higham24DFTApply,
    higham24_dft_l2_opNorm] using
      Matrix.l2_opNorm_mulVec (higham24DFT (2 ^ t))
        (WithLp.toLp (2 : ENNReal) x : EuclideanSpace ℂ (Fin (2 ^ t)))

private theorem higham24_eta_nonneg
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (mu : ℝ) (hmu : 0 ≤ mu) :
    0 ≤ higham24Eta mu (gamma fp 4) := by
  unfold higham24Eta
  exact add_nonneg hmu
    (mul_nonneg (gamma_nonneg fp hgamma4)
      (add_nonneg (Real.sqrt_nonneg _) hmu))

/-- At a zero input the literal FFT error is zero, derived from the proved
forward-error inequality rather than assumed as an extra executor premise. -/
theorem higham24_forwardFFTError_eq_zero_of_input_eq_zero
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) (hx : x = 0) :
    higham24ForwardFFTError fp weight t x = 0 := by
  subst x
  have hbound := higham24_forwardFFTError_norm_le
    fp hgamma4 weight mu hmu hw t (0 : Fin (2 ^ t) → ℂ)
  have hle :
      higham24FinEuclideanNorm
          (higham24ForwardFFTError fp weight t (0 : Fin (2 ^ t) → ℂ)) ≤ 0 := by
    simpa [higham24DFTApply, higham24FinEuclideanNorm] using hbound
  apply (higham24_finEuclideanNorm_eq_zero_iff _).mp
  exact le_antisymm hle (norm_nonneg _)

/-- The concrete input-dependent rank-one perturbation produced for one
literal rounded forward FFT run. -/
noncomputable def higham24LiteralForwardPerturbation
    (fp : FPModel) (weight : ∀ s, Higham24BitIndex s → ℂ)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ :=
  higham24RankOneActionPerturbation
    (higham24ForwardFFTError fp weight t x) x

/-- The produced perturbation sends the input to the literal forward FFT
error, including the honestly discharged zero-input case. -/
theorem higham24_literalForwardPerturbation_mulVec
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    (higham24LiteralForwardPerturbation fp weight t x).mulVec x =
      higham24ForwardFFTError fp weight t x := by
  apply higham24_rankOneActionPerturbation_mulVec
  intro hx
  exact higham24_forwardFFTError_eq_zero_of_input_eq_zero
    fp hgamma4 weight mu hmu hw t x hx

/-- Equation (24.6), now as a produced matrix action for the literal rounded
executor rather than a postulated computed matrix. -/
theorem higham24_literalForwardFFT_representation
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ) :
    higham24RoundedRadix2FFTFin fp weight t x =
      (higham24DFT (2 ^ t) +
        higham24LiteralForwardPerturbation fp weight t x).mulVec x := by
  rw [Matrix.add_mulVec,
    higham24_literalForwardPerturbation_mulVec fp hgamma4 weight mu hmu hw]
  funext k
  simp [higham24ForwardFFTError, higham24DFTApply]

/-- The literal executor's absolute error with the printed Theorem 24.2
relative coefficient. -/
theorem higham24_forwardFFTError_norm_le_relative
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    higham24FinEuclideanNorm (higham24ForwardFFTError fp weight t x) ≤
      higham24RelativeFFTBound t (higham24Eta mu (gamma fp 4)) *
        higham24FinEuclideanNorm (higham24DFTApply x) := by
  exact (higham24_forwardFFTError_norm_le
    fp hgamma4 weight mu hmu hw t x).trans
      (mul_le_mul_of_nonneg_right
        (higham24_eq24_5_product_bound t
          (higham24Eta mu (gamma fp 4))
          (higham24_eta_nonneg fp hgamma4 mu hmu) hvalid)
        (norm_nonneg _))

/-- The produced rank-one perturbation satisfies the sharp operator-`2` norm
budget `f(n,u) = sqrt(n) * t*eta/(1-t*eta)` from equation (24.6). -/
theorem higham24_literalForwardPerturbation_norm_le
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    ‖higham24LiteralForwardPerturbation fp weight t x‖ ≤
      higham24Eq24_6Bound (2 ^ t) t (higham24Eta mu (gamma fp 4)) := by
  let eta := higham24Eta mu (gamma fp 4)
  have heta : 0 ≤ eta := higham24_eta_nonneg fp hgamma4 mu hmu
  have hrelative : 0 ≤ higham24RelativeFFTBound t eta :=
    higham24_relativeFFTBound_nonneg t eta heta hvalid
  by_cases hx : x = 0
  · subst x
    simpa [higham24LiteralForwardPerturbation,
      higham24RankOneActionPerturbation, eta] using
        (higham24_eq24_6_bound_nonneg (2 ^ t) t eta heta hvalid)
  · have hxnorm : 0 < higham24FinEuclideanNorm x := by
      apply lt_of_le_of_ne (norm_nonneg _)
      intro h
      exact hx ((higham24_finEuclideanNorm_eq_zero_iff x).mp h.symm)
    have herror := higham24_forwardFFTError_norm_le_relative
      fp hgamma4 weight mu hmu hw t x hvalid
    have hdft := higham24_dftApply_finEuclideanNorm_le t x
    calc
      ‖higham24LiteralForwardPerturbation fp weight t x‖ ≤
          higham24FinEuclideanNorm (higham24ForwardFFTError fp weight t x) /
            higham24FinEuclideanNorm x :=
        higham24_rankOneActionPerturbation_norm_le _ _
      _ ≤ (higham24RelativeFFTBound t eta *
            higham24FinEuclideanNorm (higham24DFTApply x)) /
          higham24FinEuclideanNorm x := by
        exact (div_le_div_iff_of_pos_right hxnorm).2 herror
      _ ≤ (higham24RelativeFFTBound t eta *
            (Real.sqrt (((2 ^ t : ℕ) : ℝ)) * higham24FinEuclideanNorm x)) /
          higham24FinEuclideanNorm x := by
        apply (div_le_div_iff_of_pos_right hxnorm).2
        exact mul_le_mul_of_nonneg_left hdft hrelative
      _ = Real.sqrt (((2 ^ t : ℕ) : ℝ)) *
          higham24RelativeFFTBound t eta := by
        field_simp [hxnorm.ne']
      _ = higham24Eq24_6Bound (2 ^ t) t
          (higham24Eta mu (gamma fp 4)) := by
        rfl

/-- Producer form of (24.6): an explicit perturbation, its exact action on the
given input, and its source norm budget all follow from the literal executor. -/
theorem higham24_literalForwardFFT_exists_perturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    ∃ Delta : Matrix (Fin (2 ^ t)) (Fin (2 ^ t)) ℂ,
      higham24RoundedRadix2FFTFin fp weight t x =
          (higham24DFT (2 ^ t) + Delta).mulVec x ∧
        ‖Delta‖ ≤
          higham24Eq24_6Bound (2 ^ t) t (higham24Eta mu (gamma fp 4)) := by
  exact ⟨higham24LiteralForwardPerturbation fp weight t x,
    higham24_literalForwardFFT_representation
      fp hgamma4 weight mu hmu hw t x,
    higham24_literalForwardPerturbation_norm_le
      fp hgamma4 weight mu hmu hw t x hvalid⟩

/-- Both forward FFTs in equation (24.7), instantiated by the literal rounded
radix-2 executor and its two independently produced input-dependent rank-one
perturbations. -/
noncomputable def higham24LiteralEq24_7Execution
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (c b : Fin (2 ^ t) → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    Higham24Eq24_7Execution (higham24DFT (2 ^ t)) c b
      (higham24Eq24_6Bound (2 ^ t) t
        (higham24Eta mu (gamma fp 4))) where
  delta1 := higham24LiteralForwardPerturbation fp weight t c
  delta2 := higham24LiteralForwardPerturbation fp weight t b
  dHat := higham24RoundedRadix2FFTFin fp weight t c
  gHat := higham24RoundedRadix2FFTFin fp weight t b
  d_stage := higham24_literalForwardFFT_representation
    fp hgamma4 weight mu hmu hw t c
  g_stage := higham24_literalForwardFFT_representation
    fp hgamma4 weight mu hmu hw t b
  delta1_bound := higham24_literalForwardPerturbation_norm_le
    fp hgamma4 weight mu hmu hw t c hvalid
  delta2_bound := higham24_literalForwardPerturbation_norm_le
    fp hgamma4 weight mu hmu hw t b hvalid

end NumStability
