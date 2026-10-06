import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NumStability.Algorithms.CondEstimation
import NumStability.Analysis.ConditionEstimatorLowerBound
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter15.Algorithm03.OneNormPowerMethod.Basic
import NumStability.Source.Higham.Chapter15.Algorithm04.LAPACKNormEstimator.Basic
import NumStability.Source.Higham.Chapter15.Equation06.LAPACKCounterexample.Basic
import NumStability.Source.Higham.Chapter15.Section01.ConditionNumbers.ConditionEstimators

/-!
# Bounds

Canonical destination for the frozen declaration block of
`NumStability.Algorithms.Chapter15CondEst`, routed by wave R02 of the August 2026 repository reorganization
completion phase. Declaration names, kinds, visibilities, signatures and
proofs are unchanged; only the module they live in has changed. Private
declarations keep their logical names and are re-mangled against this module,
exactly as recorded in the reviewed private normalization.
-/

/-!
# Chapter15CondEst (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Chapter15CondEst`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and their users,
together with two full-graph re-entry declarations whose frozen typed edges
cross an integrator-owned accepted consumer. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

namespace NumStability

namespace Higham15

open scoped BigOperators

/-- **Algorithm 15.4 estimate is a lower bound on κ₁** (Higham §15.3 + §15.1,
    eq. (15.1)).

    Running the LAPACK 1-norm estimator on `B` and scaling by `‖A‖₁` never
    exceeds `‖A‖₁·‖B‖₁ = κ₁(A)` (when `B = A⁻¹`).  Re-export of
    `condOneNumber_ge_scaled_estimator` under a Chapter-15 label. -/
theorem H15_Algorithm15_4_scaled_le_kappaOne {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ) :
    oneNorm A * H15_Algorithm15_4_gamma hn B ≤ H15_kappaOne A B :=
  condOneNumber_ge_scaled_estimator hn A B

/-- **LAPACK estimate under-estimates the textbook κ₁(A)** (Higham §15.3 +
    §15.1, eq. (15.1)) — the headline Chapter-15 condition-estimation result.

    For invertible `A` with supplied inverse `B` (`A * B = 1`), the scaled
    LAPACK 1-norm estimate is a genuine lower bound on `‖A‖₁·‖A⁻¹‖₁`.
    Re-export of `lapack_condEstimate_le_kappaOne`. -/
theorem H15_Algorithm15_4_condEstimate_le_kappaOne {n : ℕ} (hn : 0 < n)
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    oneNorm A * H15_Algorithm15_4_gamma hn B ≤
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) :=
  lapack_condEstimate_le_kappaOne hn A B h

/-- **Algorithm 15.4 — lower-bound guarantee** (Higham §15.3, Algorithm 15.4,
    p. 293): `γ ≤ ‖A‖₁`.

    Direct re-export of `lapackNormEstimator_lower_bound` under a Chapter-15
    label; the LAPACK estimator is the maximum of the power-method estimate and
    the alternating-vector estimate `‖Ab‖₁/‖b‖₁`, each a genuine lower bound. -/
theorem H15_Algorithm15_4_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    H15_Algorithm15_4_gamma hn A ≤ oneNorm A :=
  lapackNormEstimator_lower_bound hn A

/-- **Algorithm 15.4 — exact returned-ratio guarantee** (Higham §15.3,
    Algorithm 15.4, p. 293).

    The estimator returns the maximum of its power-method estimate and the
    alternating-vector estimate.  If the power arm wins,
    `H15_Algorithm15_3_stored_gamma_realized` supplies the normalized iterate
    at which that stored estimate was computed.  If the alternating arm wins,
    take `w = lapackAltVec` directly.  Thus in either branch there are genuine
    vectors `w` and `v = A w` satisfying the printed equality
    `‖v‖₁ / ‖w‖₁ = γ`, together with `γ ≤ ‖A‖₁`. -/
theorem H15_Algorithm15_4_exact_ratio_witness {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    ∃ (w v : Fin n → ℝ),
      (∀ i, v i = ∑ j : Fin n, A i j * w j) ∧
      oneNormVec v / oneNormVec w = H15_Algorithm15_4_gamma hn A ∧
      H15_Algorithm15_4_gamma hn A ≤ oneNorm A := by
  obtain ⟨wPower, hwPower, hpower⟩ :=
    H15_Algorithm15_3_stored_gamma_realized hn A 5
  let powerEst : ℝ := (oneNormPowerMethod hn A 5).γ
  by_cases h1n : 1 < n
  · let b : Fin n → ℝ := lapackAltVec h1n
    let altEst : ℝ :=
      oneNormVec (fun i => ∑ j : Fin n, A i j * b j) / oneNormVec b
    have hgamma :
        H15_Algorithm15_4_gamma hn A = max powerEst altEst := by
      simp [H15_Algorithm15_4_gamma, lapackNormEstimator, h1n,
        powerEst, altEst, b]
    by_cases hle : powerEst ≤ altEst
    · refine ⟨b, fun i => ∑ j : Fin n, A i j * b j, fun _ => rfl, ?_,
          H15_Algorithm15_4_lower_bound hn A⟩
      rw [hgamma, max_eq_right hle]
    · have halt : altEst ≤ powerEst := (lt_of_not_ge hle).le
      refine ⟨wPower, fun i => ∑ j : Fin n, A i j * wPower j, fun _ => rfl, ?_,
          H15_Algorithm15_4_lower_bound hn A⟩
      rw [hgamma, max_eq_left halt, hwPower, div_one]
      simpa [powerEst] using hpower
  · have hgamma : H15_Algorithm15_4_gamma hn A = powerEst := by
      simp [H15_Algorithm15_4_gamma, lapackNormEstimator, h1n, powerEst]
    refine ⟨wPower, fun i => ∑ j : Fin n, A i j * wPower j, fun _ => rfl, ?_,
        H15_Algorithm15_4_lower_bound hn A⟩
    rw [hgamma, hwPower, div_one]
    simpa [powerEst] using hpower

/-- Compatibility corollary retaining the older `≤ γ` witness surface.  The
    equality is supplied by `H15_Algorithm15_4_exact_ratio_witness`. -/
theorem H15_Algorithm15_4_ratio_witness {n : ℕ} (h1n : 1 < n)
    (A : Fin n → Fin n → ℝ) :
    ∃ (w v : Fin n → ℝ),
      (∀ i, v i = ∑ j : Fin n, A i j * w j) ∧
      oneNormVec v / oneNormVec w ≤ H15_Algorithm15_4_gamma (Nat.lt_of_lt_of_le
        Nat.zero_lt_one (le_of_lt h1n)) A ∧
      H15_Algorithm15_4_gamma (Nat.lt_of_lt_of_le Nat.zero_lt_one
        (le_of_lt h1n)) A ≤ oneNorm A := by
  set hn : 0 < n := Nat.lt_of_lt_of_le Nat.zero_lt_one (le_of_lt h1n) with hhn
  obtain ⟨w, v, hv, hratio, hlower⟩ :=
    H15_Algorithm15_4_exact_ratio_witness hn A
  exact ⟨w, v, hv, hratio.le, hlower⟩

end Higham15
end NumStability
