-- Analysis/Accumulation.lean
--
-- Exact single-rounding amplification examples for Higham Chapter 1, Section 1.11.

import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Basic
import NumStability.Analysis.Error
import NumStability.Analysis.FloatingPointArithmetic
import NumStability.Analysis.Rounding

namespace NumStability

open scoped Topology

/-!
# Accumulation Examples

Higham Chapter 1, Section 1.11 emphasizes that a computation can be dominated
by a small number of early rounding errors.  The `(1 + 1/n)^n` example is one
such case: once the base `1 + 1/n` has been rounded, even exact subsequent
exponentiation raises that initial relative error to the `n`th power.

This file records that exact mechanism and the displayed finite data in
Table 1.1.  It does not model the hidden Fortran power algorithm or concrete
libm/IEEE contracts for `exp` and `log`.
It also records the exact `exp(n log(1+1/n))` rewrite, the bounded exponent
perturbation caused by a relative error in the logarithm, the final
relative-error composition when the outer exponential has a supplied relative
error, the literal `O(u)` envelope for that bound, and a finite-normal
round-to-even wrapper for the two transcendental outputs.

For the Strassen paragraph in the same section, the file records only the
exact operation-count substrate: adding one Strassen recursion level halves the
classical leaf threshold for the same matrix dimension and reduces the dominant
leaf multiplication count.  It does not formalize the empirical error-growth
claim deferred by the source to Chapter 22.
-/

/-- Exact finite-`n` approximation `(1 + 1/n)^n` to `exp(1)`. -/
noncomputable def expOneApproxExactBase (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ n

/-- Approximation obtained by rounding only the initial base `1 + 1/n` and
then exponentiating that rounded base exactly. -/
noncomputable def expOneApproxRoundedBase (fp : FPModel) (n : ℕ) : ℝ :=
  (fp.fl_add 1 (1 / (n : ℝ))) ^ n

/-! ## Table 1.1 displayed finite data -/

/-- The `n` values displayed in Higham Table 1.1: row `i` is `10^(i+1)`. -/
def expOneApproxTable11N (i : Fin 7) : ℕ :=
  10 ^ (i.val + 1)

/-- The computed approximation column displayed in Higham Table 1.1, encoded
as exact rational decimals.  These are source-table values, not a proof of the
hidden Fortran single-precision execution path. -/
noncomputable def expOneApproxTable11Computed (i : Fin 7) : ℝ :=
  match i.val with
  | 0 => 2593743 / (10 : ℝ) ^ 6
  | 1 => 2704811 / (10 : ℝ) ^ 6
  | 2 => 2717051 / (10 : ℝ) ^ 6
  | 3 => 2718597 / (10 : ℝ) ^ 6
  | 4 => 2721962 / (10 : ℝ) ^ 6
  | 5 => 2595227 / (10 : ℝ) ^ 6
  | _ => 3293968 / (10 : ℝ) ^ 6

/-- The displayed relative-error column in Higham Table 1.1, encoded as exact
scientific-notation rationals. -/
noncomputable def expOneApproxTable11RelativeError (i : Fin 7) : ℝ :=
  match i.val with
  | 0 => 125 / (10 : ℝ) ^ 3
  | 1 => 135 / (10 : ℝ) ^ 4
  | 2 => 123 / (10 : ℝ) ^ 5
  | 3 => 315 / (10 : ℝ) ^ 6
  | 4 => 368 / (10 : ℝ) ^ 5
  | 5 => 123 / (10 : ℝ) ^ 3
  | _ => 576 / (10 : ℝ) ^ 3

/-- Exact transcription of the `n` column in Table 1.1. -/
theorem expOneApproxTable11_n_rows :
    expOneApproxTable11N ⟨0, by norm_num⟩ = 10 ^ 1 ∧
    expOneApproxTable11N ⟨1, by norm_num⟩ = 10 ^ 2 ∧
    expOneApproxTable11N ⟨2, by norm_num⟩ = 10 ^ 3 ∧
    expOneApproxTable11N ⟨3, by norm_num⟩ = 10 ^ 4 ∧
    expOneApproxTable11N ⟨4, by norm_num⟩ = 10 ^ 5 ∧
    expOneApproxTable11N ⟨5, by norm_num⟩ = 10 ^ 6 ∧
    expOneApproxTable11N ⟨6, by norm_num⟩ = 10 ^ 7 := by
  norm_num [expOneApproxTable11N]

/-- Exact rational transcription of the computed-approximation column in
Table 1.1. -/
theorem expOneApproxTable11_computed_rows :
    expOneApproxTable11Computed ⟨0, by norm_num⟩ =
        2593743 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11Computed ⟨1, by norm_num⟩ =
        2704811 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11Computed ⟨2, by norm_num⟩ =
        2717051 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11Computed ⟨3, by norm_num⟩ =
        2718597 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11Computed ⟨4, by norm_num⟩ =
        2721962 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11Computed ⟨5, by norm_num⟩ =
        2595227 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11Computed ⟨6, by norm_num⟩ =
        3293968 / (10 : ℝ) ^ 6 := by
  norm_num [expOneApproxTable11Computed]

/-- Exact rational transcription of the displayed relative-error column in
Table 1.1. -/
theorem expOneApproxTable11_relativeError_rows :
    expOneApproxTable11RelativeError ⟨0, by norm_num⟩ =
        125 / (10 : ℝ) ^ 3 ∧
    expOneApproxTable11RelativeError ⟨1, by norm_num⟩ =
        135 / (10 : ℝ) ^ 4 ∧
    expOneApproxTable11RelativeError ⟨2, by norm_num⟩ =
        123 / (10 : ℝ) ^ 5 ∧
    expOneApproxTable11RelativeError ⟨3, by norm_num⟩ =
        315 / (10 : ℝ) ^ 6 ∧
    expOneApproxTable11RelativeError ⟨4, by norm_num⟩ =
        368 / (10 : ℝ) ^ 5 ∧
    expOneApproxTable11RelativeError ⟨5, by norm_num⟩ =
        123 / (10 : ℝ) ^ 3 ∧
    expOneApproxTable11RelativeError ⟨6, by norm_num⟩ =
        576 / (10 : ℝ) ^ 3 := by
  norm_num [expOneApproxTable11RelativeError]

/-- The displayed Table 1.1 relative errors strictly increase on the large-`n`
tail approaching the reciprocal unit-roundoff scale. -/
theorem expOneApproxTable11_tail_relativeError_strictly_increases :
    expOneApproxTable11RelativeError ⟨3, by norm_num⟩ <
        expOneApproxTable11RelativeError ⟨4, by norm_num⟩ ∧
      expOneApproxTable11RelativeError ⟨4, by norm_num⟩ <
        expOneApproxTable11RelativeError ⟨5, by norm_num⟩ ∧
      expOneApproxTable11RelativeError ⟨5, by norm_num⟩ <
        expOneApproxTable11RelativeError ⟨6, by norm_num⟩ := by
  norm_num [expOneApproxTable11RelativeError]

/-- The last two displayed Table 1.1 rows have relative error larger than
`10^-1`, recording the source's "poor approximation" tail numerically. -/
theorem expOneApproxTable11_last_two_relativeError_gt_one_tenth :
    (1 / 10 : ℝ) < expOneApproxTable11RelativeError ⟨5, by norm_num⟩ ∧
      (1 / 10 : ℝ) < expOneApproxTable11RelativeError ⟨6, by norm_num⟩ := by
  norm_num [expOneApproxTable11RelativeError]

/-! ## Strassen recursion-threshold operation-count substrate -/

/-- Dominant scalar multiplication count at the classical leaves after
`depth` levels of ideal Strassen recursion, when each leaf block has size
`leaf`.  Additions, data movement, and empirical error behavior are deliberately
outside this count. -/
def strassenLeafMulCount (depth leaf : ℕ) : ℕ :=
  7 ^ depth * leaf ^ 3

/-- Matrix dimension represented by `depth` Strassen halvings followed by a
classical leaf block of size `leaf`. -/
def strassenThresholdDimension (depth leaf : ℕ) : ℕ :=
  2 ^ depth * leaf

/-- Halving the classical leaf threshold and adding one Strassen recursion
level leaves the represented matrix dimension unchanged. -/
theorem strassenThresholdDimension_halve_leaf_succ (depth leaf : ℕ) :
    strassenThresholdDimension (depth + 1) leaf =
      strassenThresholdDimension depth (2 * leaf) := by
  simp [strassenThresholdDimension, pow_succ]
  ring

/-- For the same represented matrix dimension, halving the classical leaf
threshold and adding one Strassen recursion level reduces the dominant leaf
multiplication count by the source's `7/8` factor. -/
theorem strassenLeafMulCount_threshold_halving_decreases
    (depth leaf : ℕ) (hleaf : 0 < leaf) :
    strassenLeafMulCount (depth + 1) leaf <
      strassenLeafMulCount depth (2 * leaf) := by
  have hpos : 0 < 7 ^ depth * leaf ^ 3 := by
    exact Nat.mul_pos (pow_pos (by norm_num) depth) (pow_pos hleaf 3)
  calc
    strassenLeafMulCount (depth + 1) leaf
        = 7 * (7 ^ depth * leaf ^ 3) := by
            simp [strassenLeafMulCount, pow_succ]
            ring
    _ < 8 * (7 ^ depth * leaf ^ 3) := by
            exact Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
    _ = strassenLeafMulCount depth (2 * leaf) := by
            simp [strassenLeafMulCount]
            ring

/-- Packaged form of the exact Strassen threshold-count fact used in §1.11:
one more recursion level corresponds to the same matrix dimension with half
the leaf threshold, but a strictly smaller dominant leaf multiplication count. -/
theorem strassenThresholdHalving_same_dimension_and_decreases_count
    (depth leaf : ℕ) (hleaf : 0 < leaf) :
    strassenThresholdDimension (depth + 1) leaf =
        strassenThresholdDimension depth (2 * leaf) ∧
      strassenLeafMulCount (depth + 1) leaf <
        strassenLeafMulCount depth (2 * leaf) :=
  ⟨strassenThresholdDimension_halve_leaf_succ depth leaf,
    strassenLeafMulCount_threshold_halving_decreases depth leaf hleaf⟩

/-! ## Problem 1.5 compensated `log(1+x)` route -/

/-- Higham Problem 1.5 / Appendix A formula (A.1), interpreted in exact real
arithmetic.  The branch at `w = 1` removes the apparent singularity of
`x * log(w) / (w - 1)` when `w = 1 + x`. -/
noncomputable def logOnePlusCompensatedExact (x : ℝ) : ℝ :=
  let w : ℝ := 1 + x
  if w = 1 then x else x * Real.log w / (w - 1)

/-- The compensated formula returns zero at the removable singularity. -/
theorem logOnePlusCompensatedExact_zero :
    logOnePlusCompensatedExact 0 = 0 := by
  simp [logOnePlusCompensatedExact]

/-- Exact source identity for Problem 1.5's compensated logarithm formula:
with exact arithmetic, formula (A.1) computes `log(1+x)`. -/
theorem logOnePlusCompensatedExact_eq_log_one_add (x : ℝ) :
    logOnePlusCompensatedExact x = Real.log (1 + x) := by
  unfold logOnePlusCompensatedExact
  by_cases h : 1 + x = 1
  · have hx : x = 0 := by linarith
    simp [hx]
  · have hx : x ≠ 0 := by
      intro hx
      apply h
      simp [hx]
    simp [h]
    field_simp [hx]

/-- Nonbranch perturbation surface for Problem 1.5's compensated logarithm:
`wHat` is the supplied value of `1+x`, `epsLog` models the relative error in
`log wHat`, and `epsMul`/`epsDiv` model the final multiply/divide roundings. -/
noncomputable def logOnePlusCompensatedPerturbedNonbranch
    (x wHat epsLog epsMul epsDiv : ℝ) : ℝ :=
  ((x * (Real.log wHat * (1 + epsLog))) * (1 + epsMul) /
      (wHat - 1)) * (1 + epsDiv)

/-- If the addition forming `w = 1+x` is exact in the nonzero branch, the
Problem 1.5 compensated logarithm has exactly the displayed product of
relative-error factors. -/
theorem logOnePlusCompensatedPerturbedNonbranch_exact_w_signedRelErrorWitness
    {x epsLog epsMul epsDiv : ℝ} (hx : x ≠ 0) :
    signedRelErrorWitness
      (logOnePlusCompensatedPerturbedNonbranch x (1 + x) epsLog epsMul epsDiv)
      (Real.log (1 + x))
      ((1 + epsLog) * (1 + epsMul) * (1 + epsDiv) - 1) := by
  unfold signedRelErrorWitness logOnePlusCompensatedPerturbedNonbranch
  field_simp [hx]
  ring

/-- Relative-error form of the nonzero exact-`w` branch of Problem 1.5's
compensated logarithm formula. -/
theorem logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_eq
    {x epsLog epsMul epsDiv : ℝ}
    (hx : x ≠ 0) (hlog : relErrorDefined (Real.log (1 + x))) :
    relError
        (logOnePlusCompensatedPerturbedNonbranch x (1 + x) epsLog epsMul epsDiv)
        (Real.log (1 + x)) =
      |(1 + epsLog) * (1 + epsMul) * (1 + epsDiv) - 1| :=
  relError_eq_abs_of_signedRelErrorWitness hlog
    (logOnePlusCompensatedPerturbedNonbranch_exact_w_signedRelErrorWitness
      (x := x) (epsLog := epsLog) (epsMul := epsMul) (epsDiv := epsDiv) hx)

/-- Bound form of the nonzero exact-`w` branch of Problem 1.5's compensated
logarithm formula.  The caller supplies whatever gamma/theta calculus is
appropriate for the three visible relative-error factors. -/
theorem logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_le
    {x epsLog epsMul epsDiv eps : ℝ}
    (hx : x ≠ 0) (hlog : relErrorDefined (Real.log (1 + x)))
    (hfactor :
      |(1 + epsLog) * (1 + epsMul) * (1 + epsDiv) - 1| ≤ eps) :
    relError
        (logOnePlusCompensatedPerturbedNonbranch x (1 + x) epsLog epsMul epsDiv)
        (Real.log (1 + x)) ≤ eps := by
  rw [logOnePlusCompensatedPerturbedNonbranch_exact_w_relError_eq hx hlog]
  exact hfactor

/-- Problem 1.5 exact reformulation `exp(n*log(1+1/n))`. -/
noncomputable def expOneApproxLogExpExact (n : ℕ) : ℝ :=
  Real.exp ((n : ℝ) * Real.log (1 + 1 / (n : ℝ)))

/-- Problem 1.5 model after a supplied relative error in the logarithm,
with the outer exponential still interpreted exactly. -/
noncomputable def expOneApproxLogExpWithLogRelError (n : ℕ) (epsLog : ℝ) : ℝ :=
  Real.exp ((n : ℝ) * (Real.log (1 + 1 / (n : ℝ)) * (1 + epsLog)))

/-- Problem 1.5 model after the logarithm has relative error `epsLog` and the
outer exponential is evaluated with relative error `epsExp`.  This keeps the
transcendental routine contracts explicit rather than adding a primitive
`fl_exp` field to `FPModel`. -/
noncomputable def expOneApproxLogExpRoundedOuter
    (n : ℕ) (epsLog epsExp : ℝ) : ℝ :=
  expOneApproxLogExpWithLogRelError n epsLog * (1 + epsExp)

/-- The scalar unit-roundoff envelope appearing in Problem 1.5's log-exp
relative-error theorem. -/
noncomputable def expOneApproxLogExpUnitRoundoffEnvelope (u : ℝ) : ℝ :=
  Real.exp u * (1 + u) - 1

/-- Literal Landau form of Problem 1.5's log-exp envelope: the scalar
relative-error envelope `exp(u)*(1+u)-1` is `O(u)` as `u -> 0`. -/
theorem expOneApproxLogExpUnitRoundoffEnvelope_isBigO :
    (fun u : ℝ => expOneApproxLogExpUnitRoundoffEnvelope u)
      =O[𝓝 0] (fun u : ℝ => u) := by
  have hExpSub :
      (fun u : ℝ => Real.exp u - 1) =O[𝓝 0] (fun u : ℝ => u) := by
    simpa using (Real.exp_sub_sum_range_isBigO_pow 1)
  have hId :
      (fun u : ℝ => u) =O[𝓝 0] (fun u : ℝ => u) :=
    Asymptotics.isBigO_refl (fun u : ℝ => u) (𝓝 0)
  have hExp :
      (fun u : ℝ => Real.exp u) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
    Real.continuous_exp.continuousAt.tendsto.isBigO_one ℝ
  have hMul :
      (fun u : ℝ => u * Real.exp u) =O[𝓝 0] (fun u : ℝ => u) := by
    simpa using hId.mul hExp
  exact (hExpSub.add hMul).congr_left fun u => by
    simp [expOneApproxLogExpUnitRoundoffEnvelope]
    ring

/-- Problem 1.5 model where the logarithm and the outer exponential are
evaluated by the concrete finite round-to-even selector.  The multiplication
by `n` is kept exact here, matching the existing two-transcendental routine
contract rather than claiming a full hidden Fortran execution trace. -/
noncomputable def expOneApproxLogExpFiniteRoundToEven
    (fmt : FloatingPointFormat) (n : ℕ) : ℝ :=
  fmt.finiteRoundToEven
    (Real.exp ((n : ℝ) *
      fmt.finiteRoundToEven (Real.log (1 + 1 / (n : ℝ)))))

/-- The base `1+1/n` used in the finite-`n` exponential approximation is
positive under Lean's totalized real division, including `n = 0`. -/
theorem expOneApproxBase_pos (n : ℕ) :
    0 < 1 + 1 / (n : ℝ) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hrec : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnpos
    linarith

/-- The exact finite-`n` approximation in Problem 1.5 is positive. -/
theorem expOneApproxExactBase_pos (n : ℕ) :
    0 < expOneApproxExactBase n := by
  unfold expOneApproxExactBase
  exact pow_pos (expOneApproxBase_pos n) n

/-- The exact finite-`n` sequence `(1+1/n)^n` converges to `exp(1)`. -/
theorem expOneApproxExactBase_tendsto_exp_one :
    Filter.Tendsto expOneApproxExactBase Filter.atTop (𝓝 (Real.exp 1)) := by
  change Filter.Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n)
    Filter.atTop (𝓝 (Real.exp 1))
  simpa [one_div] using
    (Real.tendsto_one_add_div_pow_exp (1 : ℝ))

/-- A single initial rounding error in `1 + 1/n` is raised to the `n`th power
when the rounded base is then exponentiated exactly. -/
theorem expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow
    (fp : FPModel) (n : ℕ) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
      expOneApproxRoundedBase fp n = expOneApproxExactBase n * (1 + δ) ^ n := by
  obtain ⟨δ, hδ, hfl⟩ := fp.model_add 1 (1 / (n : ℝ))
  refine ⟨δ, hδ, ?_⟩
  unfold expOneApproxRoundedBase expOneApproxExactBase
  rw [hfl, mul_pow]

/-- The same single initial rounding error gives an exact relative-error
formula when the rounded base is subsequently exponentiated exactly. -/
theorem expOneApproxRoundedBase_relError_eq_initial_error_pow_abs
    (fp : FPModel) (n : ℕ) :
    ∃ δ : ℝ,
      |δ| ≤ fp.u ∧
      relError (expOneApproxRoundedBase fp n) (expOneApproxExactBase n) =
        |(1 + δ) ^ n - 1| := by
  obtain ⟨δ, hδ, hpow⟩ :=
    expOneApproxRoundedBase_eq_exact_base_mul_initial_error_pow fp n
  refine ⟨δ, hδ, ?_⟩
  set E : ℝ := expOneApproxExactBase n
  have hEpos : 0 < E := by
    simpa [E] using expOneApproxExactBase_pos n
  have hEne : E ≠ 0 := ne_of_gt hEpos
  unfold relError
  rw [hpow]
  have hdiff : E * (1 + δ) ^ n - E = E * ((1 + δ) ^ n - 1) := by
    ring
  rw [hdiff, abs_mul]
  have hEabs_ne : |E| ≠ 0 := abs_ne_zero.mpr hEne
  exact mul_div_cancel_left₀ |(1 + δ) ^ n - 1| hEabs_ne

/-- Problem 1.5: the exact logarithmic-exponential rewrite equals
`(1+1/n)^n`. -/
theorem expOneApproxLogExpExact_eq_exact_base (n : ℕ) :
    expOneApproxLogExpExact n = expOneApproxExactBase n := by
  unfold expOneApproxLogExpExact expOneApproxExactBase
  rw [Real.exp_nat_mul, Real.exp_log (expOneApproxBase_pos n)]

/-- Problem 1.5 log-error core: a relative error `epsLog` in the logarithm
multiplies the exact finite-`n` approximation by
`exp((n*log(1+1/n))*epsLog)`, before any error from evaluating the outer
exponential is modeled. -/
theorem expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp
    (n : ℕ) (epsLog : ℝ) :
    expOneApproxLogExpWithLogRelError n epsLog =
      expOneApproxExactBase n *
        Real.exp (((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) * epsLog) := by
  unfold expOneApproxLogExpWithLogRelError
  have hsplit :
      (n : ℝ) * (Real.log (1 + 1 / (n : ℝ)) * (1 + epsLog)) =
        (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) +
          ((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) * epsLog := by
    ring
  rw [hsplit, Real.exp_add]
  rw [show Real.exp ((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) =
      expOneApproxExactBase n by
    exact expOneApproxLogExpExact_eq_exact_base n]

/-- Problem 1.5 rounded-outer-exp composition: the log-exp method with a
relative log error `epsLog` and a final relative exp error `epsExp` is the exact
finite-`n` value multiplied by the two visible perturbation factors. -/
theorem expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul
    (n : ℕ) (epsLog epsExp : ℝ) :
    expOneApproxLogExpRoundedOuter n epsLog epsExp =
      expOneApproxExactBase n *
        (Real.exp (((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) * epsLog) *
          (1 + epsExp)) := by
  unfold expOneApproxLogExpRoundedOuter
  rw [expOneApproxLogExpWithLogRelError_eq_exact_base_mul_exp]
  ring

/-- The coefficient `n*log(1+1/n)` in Problem 1.5 is nonnegative. -/
theorem expOneApproxLogExp_exponentCoeff_nonneg (n : ℕ) :
    0 ≤ (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnnonneg : 0 ≤ (n : ℝ) := by exact_mod_cast (Nat.zero_le n)
    have hrec_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
    have hbase_ge : 1 ≤ 1 + 1 / (n : ℝ) := by linarith
    have hlog_nonneg : 0 ≤ Real.log (1 + 1 / (n : ℝ)) :=
      Real.log_nonneg hbase_ge
    exact mul_nonneg hnnonneg hlog_nonneg

/-- The coefficient `n*log(1+1/n)` in Problem 1.5 is at most `1`. -/
theorem expOneApproxLogExp_exponentCoeff_le_one (n : ℕ) :
    (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos : 0 < (n : ℝ) := by exact_mod_cast hnposNat
    have hbase : 0 < 1 + 1 / (n : ℝ) := expOneApproxBase_pos n
    have hlogle :
        Real.log (1 + 1 / (n : ℝ)) ≤ (1 + 1 / (n : ℝ)) - 1 :=
      Real.log_le_sub_one_of_pos hbase
    have hmul := mul_le_mul_of_nonneg_left hlogle (le_of_lt hnpos)
    have hprod : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
      field_simp [ne_of_gt hnpos]
    linarith

/-- If the logarithm in Problem 1.5 has relative error at most `u`, then the
induced exponent perturbation has absolute value at most `u`. -/
theorem expOneApproxLogExp_logRelError_exponent_abs_le
    (n : ℕ) (epsLog u : ℝ) (hu : 0 ≤ u) (heps : |epsLog| ≤ u) :
    |((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) * epsLog| ≤ u := by
  set A : ℝ := (n : ℝ) * Real.log (1 + 1 / (n : ℝ))
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using expOneApproxLogExp_exponentCoeff_nonneg n
  have hA_le_one : A ≤ 1 := by
    simpa [A] using expOneApproxLogExp_exponentCoeff_le_one n
  calc
    |A * epsLog| = A * |epsLog| := by rw [abs_mul, abs_of_nonneg hA_nonneg]
    _ ≤ A * u := mul_le_mul_of_nonneg_left heps hA_nonneg
    _ ≤ 1 * u := mul_le_mul_of_nonneg_right hA_le_one hu
    _ = u := by ring

/-- Scalar exponential perturbation bound used by the rounded outer-exponential
part of Problem 1.5. -/
theorem real_abs_exp_sub_one_le_exp_abs_sub_one (z : ℝ) :
    |Real.exp z - 1| ≤ Real.exp |z| - 1 := by
  by_cases hz : 0 ≤ z
  · have hone : (1 : ℝ) ≤ Real.exp z := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hz
    have habs : |Real.exp z - 1| = Real.exp z - 1 :=
      abs_of_nonneg (sub_nonneg.mpr hone)
    rw [habs, abs_of_nonneg hz]
  · have hzle : z ≤ 0 := le_of_lt (lt_of_not_ge hz)
    have hExp_le_one : Real.exp z ≤ 1 := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hzle
    have habs : |Real.exp z - 1| = 1 - Real.exp z := by
      rw [abs_of_nonpos (sub_nonpos.mpr hExp_le_one)]
      ring
    rw [habs, abs_of_neg (lt_of_not_ge hz)]
    have hneg_nonneg : 0 ≤ -z := by linarith
    have hOne_le : (1 : ℝ) ≤ Real.exp (-z) := by
      simpa [Real.exp_zero] using Real.exp_le_exp.mpr hneg_nonneg
    have hpos : 0 < Real.exp (-z) := Real.exp_pos (-z)
    have hrec : Real.exp z = (Real.exp (-z))⁻¹ := by
      simpa using (Real.exp_neg (-z))
    rw [hrec]
    have hcalc : 1 - (Real.exp (-z))⁻¹ ≤ Real.exp (-z) - 1 := by
      rw [← sub_nonneg]
      have key :
          Real.exp (-z) - 1 - (1 - (Real.exp (-z))⁻¹) =
            (Real.exp (-z) - 1) ^ 2 / Real.exp (-z) := by
        field_simp [hpos.ne']
      rw [key]
      exact div_nonneg (sq_nonneg _) (le_of_lt hpos)
    exact hcalc

/-- If `|z| <= u`, then the relative change caused by exponentiating `z` is at
most `exp(u)-1`. -/
theorem real_abs_exp_sub_one_le_of_abs_le {z u : ℝ} (hz : |z| ≤ u) :
    |Real.exp z - 1| ≤ Real.exp u - 1 :=
  le_trans (real_abs_exp_sub_one_le_exp_abs_sub_one z)
    (sub_le_sub_right (Real.exp_le_exp.mpr hz) 1)

/-- Problem 1.5 rounded-outer-exp relative-error bound.  If the logarithm has
relative error at most `u` and the final exponential has relative error at most
`u`, then the log-exp method computes `(1+1/n)^n` with relative error bounded
by `exp(u) * (1+u) - 1`, an `O(u)` quantity for small `u`. -/
theorem expOneApproxLogExpRoundedOuter_relError_le_exp_mul
    (n : ℕ) (epsLog epsExp u : ℝ)
    (hu : 0 ≤ u) (hepsLog : |epsLog| ≤ u) (hepsExp : |epsExp| ≤ u) :
    relError (expOneApproxLogExpRoundedOuter n epsLog epsExp)
        (expOneApproxExactBase n) ≤
      Real.exp u * (1 + u) - 1 := by
  set A : ℝ := (n : ℝ) * Real.log (1 + 1 / (n : ℝ))
  set z : ℝ := A * epsLog
  set E : ℝ := expOneApproxExactBase n
  have hEpos : 0 < E := by
    simpa [E] using expOneApproxExactBase_pos n
  have hz_bound : |z| ≤ u := by
    simpa [A, z] using
      expOneApproxLogExp_logRelError_exponent_abs_le n epsLog u hu hepsLog
  have hExpz_bound : |Real.exp z - 1| ≤ Real.exp u - 1 :=
    real_abs_exp_sub_one_le_of_abs_le hz_bound
  have hExpz_le : Real.exp z ≤ Real.exp u := by
    have hz_le_u : z ≤ u := (abs_le.mp hz_bound).2
    exact Real.exp_le_exp.mpr hz_le_u
  have hExpz_nonneg : 0 ≤ Real.exp z := le_of_lt (Real.exp_pos z)
  have hmain :
      |Real.exp z * (1 + epsExp) - 1| ≤ Real.exp u * (1 + u) - 1 := by
    calc
      |Real.exp z * (1 + epsExp) - 1|
          = |(Real.exp z - 1) + Real.exp z * epsExp| := by ring_nf
      _ ≤ |Real.exp z - 1| + |Real.exp z * epsExp| := abs_add_le _ _
      _ = |Real.exp z - 1| + Real.exp z * |epsExp| := by
        rw [abs_mul, abs_of_nonneg hExpz_nonneg]
      _ ≤ (Real.exp u - 1) + Real.exp u * u := by
        gcongr
      _ = Real.exp u * (1 + u) - 1 := by ring
  have heq :
      expOneApproxLogExpRoundedOuter n epsLog epsExp =
        E * (Real.exp z * (1 + epsExp)) := by
    simpa [E, A, z] using
      expOneApproxLogExpRoundedOuter_eq_exact_base_mul_exp_mul
        n epsLog epsExp
  unfold relError
  rw [heq]
  have hnum :
      |E * (Real.exp z * (1 + epsExp)) - E| =
        E * |Real.exp z * (1 + epsExp) - 1| := by
    have hfact :
        E * (Real.exp z * (1 + epsExp)) - E =
          E * (Real.exp z * (1 + epsExp) - 1) := by ring
    rw [hfact, abs_mul, abs_of_pos hEpos]
  rw [hnum, abs_of_pos hEpos]
  rw [mul_div_cancel_left₀ _ hEpos.ne']
  exact hmain

/-- `FPModel`-unit-roundoff wrapper for Problem 1.5's rounded outer
exponential composition theorem.  The final exp routine is represented by the
visible relative-error variable `epsExp`. -/
theorem expOneApproxLogExpRoundedOuter_relError_le_fp
    (fp : FPModel) (n : ℕ) (epsLog epsExp : ℝ)
    (hepsLog : |epsLog| ≤ fp.u) (hepsExp : |epsExp| ≤ fp.u) :
    relError (expOneApproxLogExpRoundedOuter n epsLog epsExp)
        (expOneApproxExactBase n) ≤
      Real.exp fp.u * (1 + fp.u) - 1 :=
  expOneApproxLogExpRoundedOuter_relError_le_exp_mul
    n epsLog epsExp fp.u fp.u_nonneg hepsLog hepsExp

/-- Finite round-to-even routine contract for Problem 1.5's log-exp route.

If `log(1+1/n)` and the exact outer exponential formed after the rounded log
are both in the finite-normal range of a concrete format, then the concrete
finite round-to-even expression is an instance of the existing supplied
`epsLog`/`epsExp` model with both perturbations bounded by `fp.u`. -/
theorem expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange
    (fp : FPModel) (fmt : FloatingPointFormat) (n : ℕ)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hlognormal :
      fmt.finiteNormalRange (Real.log (1 + 1 / (n : ℝ))))
    (hexpnormal :
      fmt.finiteNormalRange
        (Real.exp ((n : ℝ) *
          fmt.finiteRoundToEven (Real.log (1 + 1 / (n : ℝ)))))) :
    ∃ epsLog epsExp : ℝ,
      |epsLog| ≤ fp.u ∧
        |epsExp| ≤ fp.u ∧
          expOneApproxLogExpFiniteRoundToEven fmt n =
            expOneApproxLogExpRoundedOuter n epsLog epsExp := by
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hlognormal with
    ⟨epsLog, _hlogRound, hepsLog_lt, hlogWit⟩
  rcases
    fmt.finiteRoundToEven_signedRelErrorWitness_lt_of_finiteNormalRange
      hexpnormal with
    ⟨epsExp, _hexpRound, hepsExp_lt, hexpWit⟩
  refine ⟨epsLog, epsExp, le_trans (le_of_lt hepsLog_lt) hu,
    le_trans (le_of_lt hepsExp_lt) hu, ?_⟩
  have hlogRel :
      fmt.finiteRoundToEven (Real.log (1 + 1 / (n : ℝ))) =
        Real.log (1 + 1 / (n : ℝ)) * (1 + epsLog) := by
    simpa [signedRelErrorWitness] using hlogWit
  have hexpRel :
      fmt.finiteRoundToEven
          (Real.exp ((n : ℝ) *
            fmt.finiteRoundToEven (Real.log (1 + 1 / (n : ℝ))))) =
        Real.exp ((n : ℝ) *
            fmt.finiteRoundToEven (Real.log (1 + 1 / (n : ℝ)))) *
          (1 + epsExp) := by
    simpa [signedRelErrorWitness] using hexpWit
  unfold expOneApproxLogExpFiniteRoundToEven expOneApproxLogExpRoundedOuter
    expOneApproxLogExpWithLogRelError
  rw [hexpRel, hlogRel]

/-- Finite round-to-even version of the Problem 1.5 log-exp error bound.
This discharges the previously supplied logarithm and outer-exponential
relative-error variables from finite-normal round-to-even hypotheses. -/
theorem expOneApproxLogExpFiniteRoundToEven_relError_le_fp_of_finiteNormalRange
    (fp : FPModel) (fmt : FloatingPointFormat) (n : ℕ)
    (hu : fmt.unitRoundoff ≤ fp.u)
    (hlognormal :
      fmt.finiteNormalRange (Real.log (1 + 1 / (n : ℝ))))
    (hexpnormal :
      fmt.finiteNormalRange
        (Real.exp ((n : ℝ) *
          fmt.finiteRoundToEven (Real.log (1 + 1 / (n : ℝ)))))) :
    relError (expOneApproxLogExpFiniteRoundToEven fmt n)
        (expOneApproxExactBase n) ≤
      Real.exp fp.u * (1 + fp.u) - 1 := by
  rcases
    expOneApproxLogExpFiniteRoundToEven_exists_contract_of_finiteNormalRange
      fp fmt n hu hlognormal hexpnormal with
    ⟨epsLog, epsExp, hepsLog, hepsExp, hfinite⟩
  rw [hfinite]
  exact expOneApproxLogExpRoundedOuter_relError_le_fp
    fp n epsLog epsExp hepsLog hepsExp

end NumStability
