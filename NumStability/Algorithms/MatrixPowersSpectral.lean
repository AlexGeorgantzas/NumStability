-- Algorithms/MatrixPowersSpectral.lean
--
-- Higham Chapter 18, eq (18.12): the literal spectral-radius sufficient
-- condition ρ(|A|) < 1/(1+γ_{n+2}) for convergence of computed matrix
-- powers, with ρ(|A|) the genuine Mathlib `spectralRadius` of the
-- complexified entrywise-absolute matrix, via Gelfand's formula.

import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import NumStability.Algorithms.MatrixPowers

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

/-- Normwise chain: `‖v_m‖∞ ≤ (1+c)ᵐ · ‖|A|ᵐ‖∞ · ‖v₀‖∞` for any
    computed-power sequence. -/
theorem matPow_norm_chain (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c) (m : ℕ) :
    infNormVec (v m) ≤ (1 + c) ^ m *
      (infNorm (matPow n (absMatrix n A) m) * infNormVec (v 0)) := by
  apply infNormVec_le_of_abs_le
  · intro i
    have hcw := matPow_componentwise_bound n A v c hc hComp m i
    have hmv : matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i ≤
        infNorm (matPow n (absMatrix n A) m) * infNormVec (v 0) := by
      calc matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i
          ≤ |matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i| :=
            le_abs_self _
        _ ≤ infNormVec (matMulVec n (matPow n (absMatrix n A) m)
              (absVec n (v 0))) := abs_le_infNormVec _ i
        _ ≤ infNorm (matPow n (absMatrix n A) m) *
              infNormVec (absVec n (v 0)) := infNormVec_matMulVec_le hn _ _
        _ = infNorm (matPow n (absMatrix n A) m) * infNormVec (v 0) := by
            rw [infNormVec_absVec hn]
    calc |v m i|
        ≤ (1 + c) ^ m *
          matMulVec n (matPow n (absMatrix n A) m) (absVec n (v 0)) i := hcw
      _ ≤ (1 + c) ^ m *
          (infNorm (matPow n (absMatrix n A) m) * infNormVec (v 0)) :=
          mul_le_mul_of_nonneg_left hmv (pow_nonneg (by linarith) m)
  · exact mul_nonneg (pow_nonneg (by linarith) m)
      (mul_nonneg (infNorm_nonneg _) (infNormVec_nonneg _))

/-- **Eq (18.12), literal spectral form** (Higham 2nd ed., §18.2, p. 347):
    if the genuine spectral radius of `|A|` (Mathlib `spectralRadius` of the
    complexified entrywise-absolute matrix) is at most `ρ` with
    `(1+c)·ρ < 1`, then every computed-power sequence with per-step
    componentwise budget `c` satisfies `‖v_m‖∞ → 0`.  Taking `ρ` to be the
    spectral radius itself and `c = γ_{n+2}` gives the printed condition
    `ρ(|A|) < 1/(1+γ_{n+2})` exactly.  Proof: Gelfand's formula gives
    `‖|A|ᵏ‖∞ ≤ rᵏ` eventually for any `r > ρ`; compose with the
    componentwise chain and squeeze. -/
theorem matPow_convergence_spectral (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hspec : spectralRadius ℂ (absMatrixComplexified n A) ≤ ENNReal.ofReal ρ)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hq : (1 + c) * ρ < 1) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  have h1c : (0:ℝ) < 1 + c := by linarith
  -- pick r strictly between ρ and 1/(1+c)
  have hρlt : ρ < 1 / (1 + c) := by
    rw [lt_div_iff₀ h1c]
    linarith [hq]
  set r := (ρ + 1 / (1 + c)) / 2 with hr
  have hρr : ρ < r := by
    rw [hr]
    linarith
  have hrlt : r < 1 / (1 + c) := by
    rw [hr]
    linarith
  have hr0 : 0 ≤ r := le_of_lt (lt_of_le_of_lt hρ0 hρr)
  have hq' : (1 + c) * r < 1 := by
    have := (lt_div_iff₀ h1c).mp hrlt
    linarith
  have hq0' : 0 ≤ (1 + c) * r := mul_nonneg (by linarith) hr0
  -- eventual geometric matrix-power bound from Gelfand
  have hev := eventually_matPow_abs_le_of_spectralRadius_le n A ρ r hρ0
    hρr hspec
  -- eventual sequence bound
  have hseq : ∀ᶠ m in Filter.atTop,
      infNormVec (v m) ≤ infNormVec (v 0) * ((1 + c) * r) ^ m := by
    filter_upwards [hev] with m hm
    calc infNormVec (v m)
        ≤ (1 + c) ^ m *
          (infNorm (matPow n (absMatrix n A) m) * infNormVec (v 0)) :=
          matPow_norm_chain n hn A v c hc hComp m
      _ ≤ (1 + c) ^ m * (r ^ m * infNormVec (v 0)) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by linarith) m)
          exact mul_le_mul_of_nonneg_right hm (infNormVec_nonneg _)
      _ = infNormVec (v 0) * ((1 + c) * r) ^ m := by
          rw [mul_pow]
          ring
  have htop : Filter.Tendsto
      (fun m => infNormVec (v 0) * ((1 + c) * r) ^ m)
      Filter.atTop (nhds 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0' hq').const_mul
        (infNormVec (v 0))
  exact squeeze_zero'
    (Filter.Eventually.of_forall (fun m => infNormVec_nonneg _))
    hseq htop

/-- **Eq (18.12), literal spectral form, for the actual floating-point
    iteration** (Higham 2nd ed., §18.2, p. 347): if
    `ρ(|A|)·(1+γ_{n+2}) < 1` — the printed sufficient condition
    `ρ(|A|) < 1/(1+γ_{n+2})` with `ρ(|A|)` the genuine `spectralRadius` of
    the complexified `|A|` — then `‖fl(Aᵐ v₀)‖∞ → 0`. -/
theorem matPow_convergence_spectral_fl (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hspec : spectralRadius ℂ (absMatrixComplexified n A) ≤ ENNReal.ofReal ρ)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hq : (1 + gamma fp (n + 2)) * ρ < 1) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  matPow_convergence_spectral n hn A ρ hρ0 hspec
    (fl_matPowVecSeq fp n A v0) (gamma fp (n + 2))
    (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hq

end NumStability
