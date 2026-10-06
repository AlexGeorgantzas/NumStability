import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import NumStability.Algorithms.MatrixPowers.ComputedIteration.Model
import NumStability.Analysis.LinearOperators.MatrixPowers.ExactNormBounds.SpectralRadius
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Equations08To14.ComputedIteration

/-!
# Source.Higham.Chapter18.Section02.FinitePrecisionPowers.Theorems01And02.SpectralCriterion

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
