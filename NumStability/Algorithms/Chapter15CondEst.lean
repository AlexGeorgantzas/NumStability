-- Algorithms/Chapter15CondEst.lean
--
-- Correctly Chapter-15-labeled wrappers for the LAPACK 1-norm condition
-- estimation material of Higham, *Accuracy and Stability of Numerical
-- Algorithms*, 2nd ed. (SIAM, 2002), Chapter 15 "Condition Number Estimation".
--
-- SOURCE OF TRUTH (verbatim printed statements, Chapter 15):
--   * §15.1, eq. (15.1) region, p. 306: the componentwise-to-matrix-norm
--     reduction and the 1-norm condition number κ₁(A) = ‖A‖₁·‖A⁻¹‖₁.
--   * §15.3, Algorithm 15.3 (1-norm power method), p. 292:
--       "Given A ∈ Rⁿˣⁿ this algorithm computes γ and x such that
--        γ ≤ ‖A‖₁ and ‖Ax‖₁ = γ‖x‖₁."
--   * §15.3, Algorithm 15.4 (LAPACK norm estimator), p. 293:
--       "Given A ∈ Rⁿˣⁿ this algorithm computes γ and v = Aw such that
--        γ ≤ ‖A‖₁ with ‖v‖₁/‖w‖₁ = γ (w is not returned)."
--   * §15.1 lower-bound reading: the estimator, run on A⁻¹ and scaled by ‖A‖₁,
--     under-estimates the true 1-norm condition number κ₁(A).
--
-- NOTE ON MIS-LABELING.  The MATHEMATICS for all of the above already lives in
-- the repository but is (incorrectly) labeled as "Chapter 14":
--   * `Algorithms/CondEstimation.lean` — `oneNormPowerMethod`,
--     `oneNormPowerMethod_lower_bound`, `lapackNormEstimator`,
--     `lapackNormEstimator_lower_bound`;
--   * `Analysis/ConditionEstimatorLowerBound.lean` — `condOneNumber`,
--     `lapack_condEstimate_le_kappaOne`, etc.
-- This file is IMPORT-ONLY: it does not edit those files.  It re-exposes the
-- genuine Chapter-15 guarantees under `H15_*` names, reusing the existing
-- proofs and adding ONLY the honest `‖Ax‖₁ = γ‖x‖₁` equality (Algorithm 15.3)
-- and `‖v‖₁/‖w‖₁ = γ` equality (Algorithm 15.4), which the existing
-- lower-bound lemmas do not state.
--
-- HONEST STATEMENT STRENGTH.  The existing recursion `oneNormPowerMethod`
-- reports γ from the *previous* iterate on the converged branch, so its stored
-- `.γ` field is not in general equal to `‖A·(returned x)‖₁`.  We therefore do
-- NOT claim the equality for that stored field.  Instead we report, exactly as
-- Algorithm 15.3 prescribes, γ := ‖A x‖₁ for the returned iterate `x` (the
-- final `x` produced by the method).  Because every iterate the method produces
-- has ‖x‖₁ = 1 (the start vector n⁻¹e and every basis vertex eⱼ), this γ
-- satisfies BOTH printed conclusions at full strength:
--   γ ≤ ‖A‖₁   (submultiplicativity, ‖x‖₁ = 1)   and   ‖Ax‖₁ = γ‖x‖₁.
-- No hypothesis smuggles either conclusion in.

import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.CondEstimation
import NumStability.Analysis.ConditionEstimatorLowerBound

namespace NumStability
namespace Higham15

open scoped BigOperators

-- ============================================================
-- §15.3  Algorithm 15.3 (1-norm power method)
-- ============================================================

/-- The final iterate `x` produced by the Chapter-15 1-norm power method
    (Higham §15.3, Algorithm 15.3), obtained by running the repository's
    `oneNormPowerMethod` for `fuel` iterations and reading off its iterate.

    This is exactly the vector at which the returned scalar estimate is the
    1-norm of `Ax` (see `H15_Algorithm15_3_gamma`). -/
noncomputable def H15_Algorithm15_3_x {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) : Fin n → ℝ :=
  (oneNormPowerMethod hn A fuel).x

/-- The scalar estimate γ returned by Algorithm 15.3 (Higham §15.3, p. 292):
    γ = ‖A x‖₁ for the final iterate `x`. -/
noncomputable def H15_Algorithm15_3_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) : ℝ :=
  oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j)

/-- **Exact-normalization invariant** for the iterates of Algorithm 15.3.

    Every iterate produced by `oneNormPowerMethod` has 1-norm exactly `1`:
    the start vector is `n⁻¹e` (Higham §15.3: `x = n⁻¹e`), and every subsequent
    iterate is a unit basis vector `eⱼ` (`x = eⱼ`), both of 1-norm `1`; the
    converged branch merely re-returns the previous iterate.  This upgrades the
    `≤ 1` invariant used by the existing lower-bound proof to an *equality*,
    which is what the printed `‖Ax‖₁ = γ‖x‖₁` relation needs. -/
theorem H15_Algorithm15_3_x_oneNorm_eq_one {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (H15_Algorithm15_3_x hn A fuel) = 1 := by
  unfold H15_Algorithm15_3_x
  -- One step maps a unit-1-norm iterate to a unit-1-norm iterate (start `n⁻¹e`
  -- or a basis vertex `eⱼ`; the converged branch re-returns the input).
  have hstep_eq : ∀ st : OneNormState n, oneNormVec st.x = 1 →
      oneNormVec (oneNormStep hn A st).1.x = 1 := by
    intro st hst
    simp only [oneNormStep]
    split_ifs
    · exact hst
    · exact oneNormVec_basisVec _
  induction fuel with
  | zero =>
    simp only [oneNormPowerMethod]
    exact initial_vec_oneNorm hn
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    set prev := oneNormPowerMethod hn A fuel with hprev
    -- Rewrite the `let`-bindings into a plain `if` on the step's Bool flag.
    rw [show (let prev := oneNormPowerMethod hn A fuel;
              let x := oneNormStep hn A prev;
              if x.2 = true then prev else x.1) =
             if (oneNormStep hn A prev).2 = true then prev
             else (oneNormStep hn A prev).1 from rfl]
    split_ifs with hconv
    · -- converged: returns the previous iterate, 1-norm 1 by IH
      exact ih
    · -- not converged: returns the step output, which has 1-norm 1 by hstep_eq
      exact hstep_eq prev ih

/-- **Algorithm 15.3 — lower-bound guarantee** (Higham §15.3, p. 292):
      `γ ≤ ‖A‖₁`.

    Since the reported iterate `x` has `‖x‖₁ = 1`, submultiplicativity of the
    1-norm gives `γ = ‖Ax‖₁ ≤ ‖A‖₁·‖x‖₁ = ‖A‖₁`.  (Reuses
    `oneNormVec_matVec_le` from the existing module; no reproof of the norm
    algebra.) -/
theorem H15_Algorithm15_3_lower_bound {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    H15_Algorithm15_3_gamma hn A fuel ≤ oneNorm A := by
  unfold H15_Algorithm15_3_gamma
  have hx := H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel
  calc oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j)
      ≤ oneNorm A * oneNormVec (H15_Algorithm15_3_x hn A fuel) :=
        oneNormVec_matVec_le hn A _
    _ = oneNorm A * 1 := by rw [hx]
    _ = oneNorm A := mul_one _

/-- **Algorithm 15.3 — norm-equality guarantee** (Higham §15.3, p. 292):
      `‖Ax‖₁ = γ‖x‖₁`.

    By construction `γ = ‖Ax‖₁` and `‖x‖₁ = 1`, so `γ‖x‖₁ = γ = ‖Ax‖₁`.
    This is the equality the existing "Chapter-14" lower-bound lemmas do not
    state; it is discharged here for the genuine final iterate, no hypothesis
    added. -/
theorem H15_Algorithm15_3_norm_eq {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j) =
      H15_Algorithm15_3_gamma hn A fuel *
        oneNormVec (H15_Algorithm15_3_x hn A fuel) := by
  rw [H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel, mul_one]
  rfl

/-- **Algorithm 15.3 — full printed guarantee** (Higham §15.3, Algorithm 15.3,
    p. 292), bundling both printed conclusions for the computed pair `(γ, x)`:

      `γ ≤ ‖A‖₁`   and   `‖Ax‖₁ = γ‖x‖₁`. -/
theorem H15_Algorithm15_3_spec {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    H15_Algorithm15_3_gamma hn A fuel ≤ oneNorm A ∧
    oneNormVec (fun i => ∑ j : Fin n, A i j * H15_Algorithm15_3_x hn A fuel j) =
      H15_Algorithm15_3_gamma hn A fuel *
        oneNormVec (H15_Algorithm15_3_x hn A fuel) :=
  ⟨H15_Algorithm15_3_lower_bound hn A fuel,
   H15_Algorithm15_3_norm_eq hn A fuel⟩

/-- The scalar stored by the bounded implementation of Algorithm 15.3 is
    always the 1-norm of `A w` for some normalized iterate `w`.

    On a nonconverged step the state stores the norm computed at the previous
    iterate while replacing its `x` field by a basis vector.  Consequently the
    witness need not be the final stored `x`; this theorem records exactly the
    provenance needed by Algorithm 15.4 when it selects the power-method arm. -/
theorem H15_Algorithm15_3_stored_gamma_realized {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (fuel : ℕ) :
    ∃ w : Fin n → ℝ,
      oneNormVec w = 1 ∧
      oneNormVec (fun i => ∑ j : Fin n, A i j * w j) =
        (oneNormPowerMethod hn A fuel).γ := by
  induction fuel with
  | zero =>
    refine ⟨fun _ => (1 : ℝ) / n, initial_vec_oneNorm hn, ?_⟩
    rfl
  | succ fuel ih =>
    simp only [oneNormPowerMethod]
    set prev := oneNormPowerMethod hn A fuel with hprev
    rw [show (let prev := oneNormPowerMethod hn A fuel;
              let next := oneNormStep hn A prev;
              if next.2 = true then prev else next.1) =
             if (oneNormStep hn A prev).2 = true then prev
             else (oneNormStep hn A prev).1 from rfl]
    split_ifs with hconv
    · exact ih
    · refine ⟨prev.x, ?_, ?_⟩
      · simpa [prev, H15_Algorithm15_3_x] using
          H15_Algorithm15_3_x_oneNorm_eq_one hn A fuel
      · have hstep :
            (oneNormStep hn A prev).1.γ =
              oneNormVec (fun i => ∑ j : Fin n, A i j * prev.x j) := by
          simp only [oneNormStep]
          split_ifs <;> rfl
        exact hstep.symm

-- ============================================================
-- §15.3  Algorithm 15.4 (LAPACK norm estimator)
-- ============================================================

/-- The scalar estimate γ returned by the LAPACK norm estimator (Higham §15.3,
    Algorithm 15.4, p. 293), obtained from the repository's
    `lapackNormEstimator`. -/
noncomputable def H15_Algorithm15_4_gamma {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) : ℝ :=
  lapackNormEstimator hn A

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

-- ============================================================
-- §15.1  1-norm condition number κ₁(A) = ‖A‖₁‖A⁻¹‖₁ (eq. (15.1))
-- ============================================================

/-- **1-norm condition number** (Higham §15.1, eq. (15.1) region, p. 306):
      `κ₁(A) = ‖A‖₁·‖A⁻¹‖₁`.

    Re-export of `condOneNumber` under a Chapter-15 label.  The inverse is
    supplied explicitly as `B` (the matrix the estimator actually samples,
    accessed through linear solves); `H15_kappaOne_eq_of_rightInverse` pins `B`
    to Mathlib's canonical inverse when `A * B = 1`. -/
noncomputable def H15_kappaOne {n : ℕ} (A B : Fin n → Fin n → ℝ) : ℝ :=
  condOneNumber A B

/-- `κ₁(A) ≥ 0` (Higham §15.1). -/
theorem H15_kappaOne_nonneg {n : ℕ} (A B : Fin n → Fin n → ℝ) :
    0 ≤ H15_kappaOne A B :=
  condOneNumber_nonneg A B

/-- **κ₁ at the genuine inverse** (Higham §15.1, eq. (15.1)).

    When `B` is an actual right inverse of `A` (`A * B = 1`), `H15_kappaOne A B`
    is the textbook `‖A‖₁·‖A⁻¹‖₁` with Mathlib's canonical inverse.  Re-export
    of `condOneNumber_eq_kappaOne_of_rightInverse`. -/
theorem H15_kappaOne_eq_of_rightInverse {n : ℕ}
    (A B : Fin n → Fin n → ℝ)
    (h : (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) *
         (Matrix.of B : Matrix (Fin n) (Fin n) ℝ) = 1) :
    H15_kappaOne A B =
      oneNorm A *
        oneNorm (fun i j => (Matrix.of A : Matrix (Fin n) (Fin n) ℝ)⁻¹ i j) :=
  condOneNumber_eq_kappaOne_of_rightInverse A B h

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

/-! ## Equation (15.6): an exact LAPACK-estimator counterexample -/

/-- A nonzero direction orthogonal to the three vectors sampled by the
    four-dimensional instance of Algorithm 15.4: `e`, `e₁`, and the
    alternating vector `b`. -/
def H15_eq15_6_v : Fin 4 → ℝ := fun i =>
  if i = 0 then 0 else if i = 1 then 11 else if i = 2 then -2 else -9

/-- The rank-one orthogonal projector used in the concrete instance of
    Higham's equation (15.6).  Its denominator is
    `vᵀv = 11² + 2² + 9² = 206`. -/
noncomputable def H15_eq15_6_P : Fin 4 → Fin 4 → ℝ :=
  fun i j => H15_eq15_6_v i * H15_eq15_6_v j / 206

/-- The counterexample family `A(θ) = I + θP` from equation (15.6). -/
noncomputable def H15_eq15_6_A (θ : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => (if i = j then 1 else 0) + θ * H15_eq15_6_P i j

theorem H15_eq15_6_P_symmetric :
    ∀ i j, H15_eq15_6_P i j = H15_eq15_6_P j i := by
  intro i j
  simp only [H15_eq15_6_P]
  ring

/-- `Pe = 0`, the first annihilation relation printed in (15.6). -/
theorem H15_eq15_6_P_mul_e (i : Fin 4) :
    ∑ j : Fin 4, H15_eq15_6_P i j = 0 := by
  fin_cases i <;> simp [Fin.sum_univ_four, H15_eq15_6_P, H15_eq15_6_v] <;>
    norm_num

/-- `Pe₁ = 0`, the second annihilation relation printed in (15.6). -/
theorem H15_eq15_6_P_mul_e1 (i : Fin 4) :
    ∑ j : Fin 4, H15_eq15_6_P i j * basisVec (0 : Fin 4) j = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_P, H15_eq15_6_v, basisVec] <;>
    norm_num

/-- `Pb = 0`, where `b` is Algorithm 15.4's alternating vector. -/
theorem H15_eq15_6_P_mul_b (i : Fin 4) :
    ∑ j : Fin 4, H15_eq15_6_P i j * lapackAltVec (by omega : 1 < 4) j = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_P, H15_eq15_6_v, lapackAltVec,
      even_iff_two_dvd] <;>
    norm_num

/-- The exact family fixes the uniform starting vector used by Algorithm 15.4. -/
theorem H15_eq15_6_A_mul_uniform (θ : ℝ) (i : Fin 4) :
    (∑ j : Fin 4, H15_eq15_6_A θ i j * ((1 : ℝ) / 4)) = 1 / 4 := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v] <;>
    ring

/-- Symmetry and `Pe=0` imply `A(θ)ᵀe=e`, so the first power-method
    iteration satisfies its stopping test exactly. -/
theorem H15_eq15_6_AT_mul_e (θ : ℝ) (j : Fin 4) :
    ∑ i : Fin 4, H15_eq15_6_A θ i j = 1 := by
  fin_cases j <;>
    simp [Fin.sum_univ_four, H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v] <;>
    ring

/-- The alternative vector sampled at the end of Algorithm 15.4 is also fixed. -/
theorem H15_eq15_6_A_mul_b (θ : ℝ) (i : Fin 4) :
    (∑ j : Fin 4, H15_eq15_6_A θ i j * lapackAltVec (by omega : 1 < 4) j) =
      lapackAltVec (by omega : 1 < 4) i := by
  fin_cases i <;>
    simp [Fin.sum_univ_four, H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v,
      lapackAltVec, even_iff_two_dvd] <;>
    ring

/-- Equation (15.6), executable conclusion: the repository's bounded
    Algorithm 15.4 returns the estimate `1` on every member of the family. -/
theorem H15_eq15_6_lapackNormEstimator (θ : ℝ) :
    H15_Algorithm15_4_gamma (by omega : 0 < 4) (H15_eq15_6_A θ) = 1 := by
  have hstart : oneNormPowerMethod (by omega : 0 < 4) (H15_eq15_6_A θ) 0 =
      ⟨(fun _ => (1 : ℝ) / 4), 1⟩ := by
    have hvals :
        (fun i : Fin 4 => ∑ j : Fin 4, H15_eq15_6_A θ i j * ((1 : ℝ) / 4)) =
          (fun _ => (1 : ℝ) / 4) := by
      funext i
      exact H15_eq15_6_A_mul_uniform θ i
    have hgamma : oneNormVec
        (fun i : Fin 4 => ∑ j : Fin 4,
          H15_eq15_6_A θ i j * ((1 : ℝ) / 4)) = 1 := by
      rw [hvals]
      simp [oneNormVec, Fin.sum_univ_four]
    change (⟨(fun _ : Fin 4 => (1 : ℝ) / 4),
      oneNormVec (fun i : Fin 4 => ∑ j : Fin 4,
        H15_eq15_6_A θ i j * ((1 : ℝ) / 4))⟩ : OneNormState 4) = _
    rw [hgamma]
  have hstep : oneNormStep (by omega : 0 < 4) (H15_eq15_6_A θ)
      ⟨(fun _ => (1 : ℝ) / 4), 1⟩ =
      (⟨(fun _ => (1 : ℝ) / 4), 1⟩, true) := by
    simp only [oneNormStep]
    simp_rw [H15_eq15_6_A_mul_uniform]
    simp [signVec, infNormVec, H15_eq15_6_AT_mul_e, oneNormVec]
  have hpower : oneNormPowerMethod (by omega : 0 < 4) (H15_eq15_6_A θ) 5 =
      ⟨(fun _ => (1 : ℝ) / 4), 1⟩ := by
    have hall : ∀ fuel : ℕ,
        oneNormPowerMethod (by omega : 0 < 4) (H15_eq15_6_A θ) fuel =
          ⟨(fun _ => (1 : ℝ) / 4), 1⟩ := by
      intro fuel
      induction fuel with
      | zero => exact hstart
      | succ fuel ih =>
          simp only [oneNormPowerMethod]
          rw [ih, hstep]
          rfl
    exact hall 5
  unfold H15_Algorithm15_4_gamma lapackNormEstimator
  simp only [hpower]
  have hb : oneNormVec (lapackAltVec (by omega : 1 < 4)) = 6 := by
    have hthree : (3 : ℝ)⁻¹ * 3 = 1 := inv_mul_cancel₀ (by norm_num)
    have h0 : lapackAltVec (by omega : 1 < 4) (0 : Fin 4) = 1 := by
      norm_num [lapackAltVec, even_iff_two_dvd]
    have h1 : lapackAltVec (by omega : 1 < 4) (1 : Fin 4) = -(4 / 3 : ℝ) := by
      norm_num [lapackAltVec, even_iff_two_dvd] <;>
        simp only [div_eq_mul_inv] <;> nlinarith [hthree]
    have h2 : lapackAltVec (by omega : 1 < 4) (2 : Fin 4) = 5 / 3 := by
      norm_num [lapackAltVec, even_iff_two_dvd] <;>
        simp only [div_eq_mul_inv] <;> nlinarith [hthree]
    have h3 : lapackAltVec (by omega : 1 < 4) (3 : Fin 4) = -2 := by
      norm_num [lapackAltVec, even_iff_two_dvd] <;>
        simp only [div_eq_mul_inv] <;> nlinarith [hthree]
    simp only [oneNormVec, Fin.sum_univ_four, h0, h1, h2, h3, abs_neg]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 / 3),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 5 / 3)]
    ring
  have hAb : oneNormVec (fun i => ∑ j : Fin 4,
      H15_eq15_6_A θ i j * lapackAltVec (by omega : 1 < 4) j) = 6 := by
    simp_rw [H15_eq15_6_A_mul_b]
    exact hb
  simp [hAb, hb]

/-- The true one-norm grows linearly along the counterexample family.  Thus
    the estimate-to-norm ratio can be made arbitrarily small. -/
theorem H15_eq15_6_oneNorm_lower (θ : ℝ) (hθ : 0 ≤ θ) :
    1 + (121 / 103 : ℝ) * θ ≤ oneNorm (H15_eq15_6_A θ) := by
  have hcol := col_sum_le_oneNorm (H15_eq15_6_A θ) (1 : Fin 4)
  rw [Fin.sum_univ_four] at hcol
  simp [H15_eq15_6_A, H15_eq15_6_P, H15_eq15_6_v] at hcol
  have hmain : 0 ≤ 1 + θ * ((11 : ℝ) * 11 / 206) := by positivity
  have habsθ : |θ| = θ := abs_of_nonneg hθ
  rw [abs_of_nonneg hmain, habsθ] at hcol
  norm_num at hcol ⊢
  linarith

end Higham15
end NumStability
