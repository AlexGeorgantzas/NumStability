import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import NumStability.Analysis.MatrixAlgebra

/-!
# Analysis.LinearOperators.MatrixPowers.ExactNormBounds.SpectralRadius

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/MatrixPowersSpectral.lean
--
-- Higham Chapter 18, eq (18.12): the literal spectral-radius sufficient
-- condition ρ(|A|) < 1/(1+γ_{n+2}) for convergence of computed matrix
-- powers, with ρ(|A|) the genuine Mathlib `spectralRadius` of the
-- complexified entrywise-absolute matrix, via Gelfand's formula.






namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The complexified entrywise-absolute matrix `|A|` as a Mathlib matrix
    over ℂ, the object whose `spectralRadius` is Higham's `ρ(|A|)` in
    eq (18.12). -/
noncomputable def absMatrixComplexified (n : ℕ) (A : Fin n → Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  (Matrix.of (absMatrix n A)).map Complex.ofReal

/-- Repo `matPow` agrees with Mathlib matrix powers. -/
theorem matPow_eq_matrix_pow (n : ℕ) (B : Fin n → Fin n → ℝ) (k : ℕ) :
    Matrix.of (matPow n B k) = (Matrix.of B) ^ k := by
  induction k with
  | zero =>
    ext i j
    show idMatrix n i j = (1 : Matrix (Fin n) (Fin n) ℝ) i j
    unfold idMatrix
    simp [Matrix.one_apply]
  | succ k ih =>
    ext i j
    show matMul n B (matPow n B k) i j = ((Matrix.of B) ^ (k + 1)) i j
    rw [pow_succ', Matrix.mul_apply]
    unfold matMul
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← ih]
    rfl

/-- The repo ∞-norm is the Mathlib `linfty` operator norm. -/
theorem infNorm_eq_linfty_opNorm (n : ℕ) (B : Fin n → Fin n → ℝ) :
    infNorm B = ‖Matrix.of B‖ := rfl

/-- Complexification preserves the `linfty` operator norm. -/
theorem linfty_opNorm_map_ofReal {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    ‖M.map Complex.ofReal‖ = ‖M‖ := by
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  congr 1
  refine congrArg _ (funext fun i => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show ‖((M i j : ℝ) : ℂ)‖₊ = ‖M i j‖₊
  ext
  simp

/-- Complexification commutes with matrix powers. -/
theorem map_ofReal_pow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) :
    (M ^ k).map Complex.ofReal = (M.map Complex.ofReal) ^ k := by
  have h := map_pow (Complex.ofRealHom.mapMatrix
    (m := Fin n)) M k
  simpa [RingHom.mapMatrix_apply] using h

/-- Norm of the complexified power of `|A|` equals the repo norm of the
    real power. -/
theorem norm_absMatrixComplexified_pow (n : ℕ) (A : Fin n → Fin n → ℝ) (k : ℕ) :
    ‖(absMatrixComplexified n A) ^ k‖ = infNorm (matPow n (absMatrix n A) k) := by
  rw [absMatrixComplexified, ← map_ofReal_pow, linfty_opNorm_map_ofReal,
    infNorm_eq_linfty_opNorm, matPow_eq_matrix_pow]

/-- **Gelfand extraction**: if `spectralRadius ℂ (absMatrixComplexified A) ≤ ρ`
    and `ρ < r`, then eventually `‖|A|ᵏ‖∞ ≤ rᵏ`. -/
theorem eventually_matPow_abs_le_of_spectralRadius_le (n : ℕ)
    (A : Fin n → Fin n → ℝ) (ρ r : ℝ) (hρ0 : 0 ≤ ρ) (hρr : ρ < r)
    (hspec : spectralRadius ℂ (absMatrixComplexified n A) ≤ ENNReal.ofReal ρ) :
    ∀ᶠ k in Filter.atTop, infNorm (matPow n (absMatrix n A) k) ≤ r ^ k := by
  haveI hfd : FiniteDimensional ℂ (Matrix (Fin n) (Fin n) ℂ) :=
    Matrix.finiteDimensional
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
    FiniteDimensional.complete ℂ _
  have hr0 : 0 < r := lt_of_le_of_lt hρ0 hρr
  have hgel := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius
    (absMatrixComplexified n A)
  have hlt : spectralRadius ℂ (absMatrixComplexified n A) < ENNReal.ofReal r :=
    lt_of_le_of_lt hspec (ENNReal.ofReal_lt_ofReal_iff hr0 |>.mpr hρr)
  have hev : ∀ᶠ (k : ℕ) in Filter.atTop,
      ENNReal.ofReal (‖(absMatrixComplexified n A) ^ k‖ ^ (1 / (k:ℝ))) <
        ENNReal.ofReal r :=
    hgel.eventually_lt_const hlt
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with k hk hk1
  have hklt : ‖(absMatrixComplexified n A) ^ k‖ ^ (1 / (k:ℝ)) < r :=
    (ENNReal.ofReal_lt_ofReal_iff hr0).mp hk
  have hknorm0 : (0:ℝ) ≤ ‖(absMatrixComplexified n A) ^ k‖ := norm_nonneg _
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk1
  -- Undo the 1/k root: x = (x^(1/k))^k for x ≥ 0, k ≠ 0.
  have hroot : ‖(absMatrixComplexified n A) ^ k‖ =
      (‖(absMatrixComplexified n A) ^ k‖ ^ (1 / (k:ℝ))) ^ (k:ℕ) := by
    rw [← Real.rpow_natCast
      (‖(absMatrixComplexified n A) ^ k‖ ^ (1 / (k:ℝ))) k,
      ← Real.rpow_mul hknorm0]
    rw [one_div, inv_mul_cancel₀ (ne_of_gt hkR), Real.rpow_one]
  have hle : ‖(absMatrixComplexified n A) ^ k‖ ≤ r ^ k := by
    rw [hroot]
    exact pow_le_pow_left₀
      (Real.rpow_nonneg hknorm0 _) (le_of_lt hklt) k
  rw [norm_absMatrixComplexified_pow] at hle
  exact hle















































































































end NumStability
