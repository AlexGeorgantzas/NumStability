/-
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 6, p. 113, unnumbered display following equation (6.21):

  ‖[[0,A],[Aᴴ,0]]‖ₚ = max (‖A‖ₚ, ‖A‖q),   1/p + 1/q = 1.

The older `ch6aside_blockAntidiag_op2_eq` reduction in `Higham6Asides`
retained the norm of a block diagonal matrix as a caller premise.  This module
removes that premise and proves the printed finite-exponent identity.  The
block matrix is represented through the canonical `PiLp` sum/product linear
isometry: its action on `(x,y)` is exactly `(A y, Aᴴ x)`.
-/

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Operator.Basic
import NumStability.Analysis.Norms

namespace NumStability

open scoped ENNReal

noncomputable section

/-! ### The norm of an off-diagonal map on an `L^p` product -/

variable {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y]
  [NormedSpace ℂ X] [NormedSpace ℂ Y]

/-- The off-diagonal continuous linear map `(x,y) ↦ (S y,T x)` on an `L^p`
product. -/
noncomputable def ch6aside_withLpBlockSwapCLM (p : ENNReal) [Fact (1 ≤ p)]
    (S : Y →L[ℂ] X) (T : X →L[ℂ] Y) :
    WithLp p (X × Y) →L[ℂ] WithLp p (X × Y) := by
  let L0 : WithLp p (X × Y) →ₗ[ℂ] WithLp p (X × Y) :=
    { toFun := fun z => WithLp.toLp p (S z.snd, T z.fst)
      map_add' := by
        intro z w
        apply WithLp.ofLp_injective p
        ext <;> simp
      map_smul' := by
        intro c z
        apply WithLp.ofLp_injective p
        ext <;> simp }
  exact L0.mkContinuous (‖S‖ + ‖T‖) (by
    intro z
    have hdecomp :
        WithLp.toLp p (S z.snd, T z.fst) =
          WithLp.toLp p (S z.snd, 0) + WithLp.toLp p (0, T z.fst) := by
      apply WithLp.ofLp_injective p
      ext <;> simp
    rw [show L0 z = WithLp.toLp p (S z.snd, T z.fst) by rfl, hdecomp]
    calc
      ‖WithLp.toLp p (S z.snd, 0) + WithLp.toLp p (0, T z.fst)‖
          ≤ ‖WithLp.toLp p (S z.snd, 0)‖ +
              ‖WithLp.toLp p (0, T z.fst)‖ := norm_add_le _ _
      _ = ‖S z.snd‖ + ‖T z.fst‖ := by simp
      _ ≤ ‖S‖ * ‖z.snd‖ + ‖T‖ * ‖z.fst‖ :=
        add_le_add (S.le_opNorm _) (T.le_opNorm _)
      _ ≤ ‖S‖ * ‖z‖ + ‖T‖ * ‖z‖ := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (WithLp.norm_snd_le (α := X) (β := Y) (p := p) z) (norm_nonneg S))
          (mul_le_mul_of_nonneg_left
            (WithLp.norm_fst_le (α := X) (β := Y) (p := p) z) (norm_nonneg T))
      _ = (‖S‖ + ‖T‖) * ‖z‖ := by ring)

@[simp]
theorem ch6aside_withLpBlockSwapCLM_apply (p : ENNReal) [Fact (1 ≤ p)]
    (S : Y →L[ℂ] X) (T : X →L[ℂ] Y) (z : WithLp p (X × Y)) :
    ch6aside_withLpBlockSwapCLM p S T z =
      WithLp.toLp p (S z.snd, T z.fst) := rfl

private lemma ch6aside_withLpBlockSwapCLM_bound
    (p : ENNReal) [Fact (1 ≤ p)]
    (S : Y →L[ℂ] X) (T : X →L[ℂ] Y) (z : WithLp p (X × Y)) :
    ‖ch6aside_withLpBlockSwapCLM p S T z‖ ≤
      max ‖S‖ ‖T‖ * ‖z‖ := by
  let M : ℝ := max ‖S‖ ‖T‖
  have hM : 0 ≤ M := le_trans (norm_nonneg S) (le_max_left _ _)
  have hS : ‖S z.snd‖ ≤ M * ‖z.snd‖ := by
    exact (S.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hT : ‖T z.fst‖ ≤ M * ‖z.fst‖ := by
    exact (T.le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  by_cases htop : p = ⊤
  · subst p
    rw [ch6aside_withLpBlockSwapCLM_apply, WithLp.prod_norm_eq_sup,
      WithLp.prod_norm_eq_sup]
    exact max_le
      (hS.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hM))
      (hT.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hM))
  have hp : 0 < p.toReal := (ENNReal.toReal_pos_iff_ne_top p).2 htop
  rw [ch6aside_withLpBlockSwapCLM_apply, WithLp.prod_norm_eq_add hp,
    WithLp.prod_norm_eq_add hp]
  have hpowS : ‖S z.snd‖ ^ p.toReal ≤
      (M * ‖z.snd‖) ^ p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) hS (le_of_lt hp)
  have hpowT : ‖T z.fst‖ ^ p.toReal ≤
      (M * ‖z.fst‖) ^ p.toReal :=
    Real.rpow_le_rpow (norm_nonneg _) hT (le_of_lt hp)
  have hsum :
      ‖S z.snd‖ ^ p.toReal + ‖T z.fst‖ ^ p.toReal ≤
        M ^ p.toReal *
          (‖z.fst‖ ^ p.toReal + ‖z.snd‖ ^ p.toReal) := by
    calc
      _ ≤ (M * ‖z.snd‖) ^ p.toReal +
          (M * ‖z.fst‖) ^ p.toReal := add_le_add hpowS hpowT
      _ = M ^ p.toReal *
          (‖z.fst‖ ^ p.toReal + ‖z.snd‖ ^ p.toReal) := by
        rw [Real.mul_rpow hM (norm_nonneg _),
          Real.mul_rpow hM (norm_nonneg _)]
        ring
  have hroot := Real.rpow_le_rpow
    (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
    hsum (by positivity : 0 ≤ 1 / p.toReal)
  calc
    (‖S z.snd‖ ^ p.toReal + ‖T z.fst‖ ^ p.toReal) ^ (1 / p.toReal)
        ≤ (M ^ p.toReal *
          (‖z.fst‖ ^ p.toReal + ‖z.snd‖ ^ p.toReal)) ^
            (1 / p.toReal) := hroot
    _ = M *
        (‖z.fst‖ ^ p.toReal + ‖z.snd‖ ^ p.toReal) ^
          (1 / p.toReal) := by
      rw [Real.mul_rpow (Real.rpow_nonneg hM _)
        (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
          (Real.rpow_nonneg (norm_nonneg _) _))]
      have hMr : (M ^ p.toReal) ^ (1 / p.toReal) = M := by
        rw [show 1 / p.toReal = p.toReal⁻¹ by ring,
          ← Real.rpow_mul hM, mul_inv_cancel₀ hp.ne', Real.rpow_one]
      rw [hMr]

/-- The operator norm of `(x,y) ↦ (S y,T x)` on an `L^p` product is exactly
the maximum of the two component operator norms. -/
theorem ch6aside_withLpBlockSwapCLM_norm
    (p : ENNReal) [Fact (1 ≤ p)]
    (S : Y →L[ℂ] X) (T : X →L[ℂ] Y) :
    ‖ch6aside_withLpBlockSwapCLM p S T‖ = max ‖S‖ ‖T‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _
      (le_trans (norm_nonneg S) (le_max_left _ _))
    exact ch6aside_withLpBlockSwapCLM_bound p S T
  · apply max_le
    · apply ContinuousLinearMap.opNorm_le_bound S
        (norm_nonneg (ch6aside_withLpBlockSwapCLM p S T))
      intro y
      have h := (ch6aside_withLpBlockSwapCLM p S T).le_opNorm
        (WithLp.toLp p (0, y))
      simpa using h
    · apply ContinuousLinearMap.opNorm_le_bound T
        (norm_nonneg (ch6aside_withLpBlockSwapCLM p S T))
      intro x
      have h := (ch6aside_withLpBlockSwapCLM p S T).le_opNorm
        (WithLp.toLp p (x, 0))
      simpa using h

/-! ### Concrete matrix `p`-norm bridge -/

/-- A matrix as a continuous linear map between its finite `PiLp` source and
target spaces. -/
noncomputable def ch6aside_matrixLpCLM {m n : ℕ}
    (p : ENNReal) [Fact (1 ≤ p)] (A : CMatrix m n) :
    WithLp p (CVec n) →L[ℂ] WithLp p (CVec m) := by
  let L0 : WithLp p (CVec n) →ₗ[ℂ] WithLp p (CVec m) :=
    { toFun := fun x =>
        WithLp.toLp p (complexMatrixVecMul A (WithLp.ofLp x))
      map_add' := by
        intro x y
        apply WithLp.ofLp_injective p
        ext i
        simp [complexMatrixVecMul, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro c x
        apply WithLp.ofLp_injective p
        ext i
        simp [complexMatrixVecMul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring }
  exact L0.mkContinuous (complexMatrixLpColumnSumNorm p A) (by
    intro x
    change complexVecLpNorm p (complexMatrixVecMul A (WithLp.ofLp x)) ≤
      complexMatrixLpColumnSumNorm p A *
        complexVecLpNorm p (WithLp.ofLp x)
    exact complexMatrixLpColumnSumNorm_mixedSubordinateMatrixBound p A _)

@[simp]
theorem ch6aside_matrixLpCLM_apply {m n : ℕ}
    (p : ENNReal) [Fact (1 ≤ p)] (A : CMatrix m n)
    (x : WithLp p (CVec n)) :
    ch6aside_matrixLpCLM p A x =
      WithLp.toLp p (complexMatrixVecMul A (WithLp.ofLp x)) := rfl

/-- The operator norm of `ch6aside_matrixLpCLM` satisfies the repository's
least-subordinate-value specification. -/
theorem ch6aside_matrixLpCLM_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (p : ENNReal) [Fact (1 ≤ p)]
    (A : CMatrix m n) :
    IsComplexMatrixLpNormValue p A ‖ch6aside_matrixLpCLM p A‖ := by
  dsimp [IsComplexMatrixLpNormValue, IsMixedSubordinateMatrixNormValue,
    IsMixedSubordinateNormValue]
  constructor
  · intro x
    have h := (ch6aside_matrixLpCLM p A).le_opNorm (WithLp.toLp p x)
    simpa [complexVecLpNorm] using h
  · intro d hd
    have hd_nonneg : 0 ≤ d := mixedSubordinateBound_nonneg_of_nonempty hn
      (complexVecLpNorm_isComplexVectorNorm p)
      (complexVecLpNorm_isComplexVectorNorm p) hd
    apply ContinuousLinearMap.opNorm_le_bound _ hd_nonneg
    intro x
    have hx := hd (WithLp.ofLp x)
    simpa [complexVecLpNorm] using hx

/-- The continuous-linear-map operator norm is the concrete chosen matrix
`p`-norm. -/
theorem ch6aside_matrixLpCLM_norm_eq {m n : ℕ} (hn : 0 < n)
    (p : ENNReal) [Fact (1 ≤ p)] (A : CMatrix m n) :
    ‖ch6aside_matrixLpCLM p A‖ = complexMatrixLpNorm hn p A := by
  symm
  exact complexMatrixLpNorm_eq_of_isComplexMatrixLpNormValue hn p
    (ch6aside_matrixLpCLM_isComplexMatrixLpNormValue hn p A)

/-! ### Higham's block antidiagonal identity -/

/-- The canonical `PiLp` product representation of
`[[0,A],[Aᴴ,0]]`. -/
noncomputable def ch6aside_blockAntidiagLpCLM {m n : ℕ}
    (p : ENNReal) [Fact (1 ≤ p)] (A : CMatrix m n) :
    WithLp p (WithLp p (CVec m) × WithLp p (CVec n)) →L[ℂ]
      WithLp p (WithLp p (CVec m) × WithLp p (CVec n)) :=
  ch6aside_withLpBlockSwapCLM p (ch6aside_matrixLpCLM p A)
    (ch6aside_matrixLpCLM p (complexMatrixAdjoint A))

/-- Componentwise action of the block operator.  Under
`PiLp.sumPiLpEquivProdLpPiLp`, this is exactly the `Matrix.fromBlocks` action
`(x,y) ↦ (A y,Aᴴ x)`. -/
theorem ch6aside_blockAntidiagLpCLM_components {m n : ℕ}
    (p : ENNReal) [Fact (1 ≤ p)] (A : CMatrix m n)
    (z : WithLp p (WithLp p (CVec m) × WithLp p (CVec n))) :
    WithLp.ofLp (ch6aside_blockAntidiagLpCLM p A z).fst =
        complexMatrixVecMul A (WithLp.ofLp z.snd) ∧
      WithLp.ofLp (ch6aside_blockAntidiagLpCLM p A z).snd =
        complexMatrixVecMul (complexMatrixAdjoint A)
          (WithLp.ofLp z.fst) := by
  constructor <;> rfl

/-- **Higham Chapter 6 block antidiagonal identity (finite conjugate
exponents).**  This is the unnumbered display after (6.21), with no residual
block-norm or target-equivalent premise. -/
theorem ch6aside_blockAntidiag_lp_eq {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) {p q : ℝ}
    (hpq : p.HolderConjugate q) (A : CMatrix m n) :
    letI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.lt⟩
    letI hqFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
      rw [ENNReal.one_le_ofReal]
      exact le_of_lt hpq.symm.lt⟩
    ‖ch6aside_blockAntidiagLpCLM (ENNReal.ofReal p) A‖ =
      max (complexMatrixLpNorm hn (ENNReal.ofReal p) A)
        (complexMatrixLpNorm hn (ENNReal.ofReal q) A) := by
  letI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  letI hqFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.symm.lt⟩
  rw [ch6aside_blockAntidiagLpCLM,
    ch6aside_withLpBlockSwapCLM_norm,
    ch6aside_matrixLpCLM_norm_eq hn,
    ch6aside_matrixLpCLM_norm_eq hm]
  have hadj :
      complexMatrixLpNorm hm (ENNReal.ofReal p)
          (complexMatrixAdjoint A) =
        complexMatrixLpNorm hn (ENNReal.ofReal q) A :=
    complexMatrixAdjointLpNormValue_eq hn hm hpq
      (complexMatrixLpNorm_isComplexMatrixLpNormValue hn
        (ENNReal.ofReal q) A)
      (complexMatrixLpNorm_isComplexMatrixLpNormValue hm
        (ENNReal.ofReal p) (complexMatrixAdjoint A))
  rw [hadj]

end

end NumStability
