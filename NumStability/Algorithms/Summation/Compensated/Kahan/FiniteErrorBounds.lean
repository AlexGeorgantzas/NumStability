import NumStability.Algorithms.Summation.Compensated.Kahan.ErrorBounds
import NumStability.Algorithms.Summation.Compensated.Kahan.Finite

namespace NumStability

/-!
# Finite-format Kahan error bounds

This module specializes the reusable Kahan backward-error bounds to concrete
finite round-to-even executions.  It keeps finite execution certificates
separate from source-facing audits and finite counterexamples.
-/

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from finite representability of every displayed correction
subtraction in a concrete finite round-to-even format.

This is the finite/coherence layer below the FastTwoSum route: callers may
prove `FiniteKahanPrefixCorrectionSubFinite` directly, for example from
Sterbenz or Ferguson conditions on `temp - s`, without using a magnitude-order
FastTwoSum certificate. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hfinite :
      FiniteKahanPrefixCorrectionSubFinite fmt v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_exactSubTrace
      fp n v
      (KahanPrefixCorrectionSubExact.of_finiteRoundToEven_sub_finite
        fp fmt hround v n (Nat.le_refl n) hfinite)
      huSmall hBudget

/-- Tail-direct finite-subtraction route for the ordinary returned Kahan
backward-error representation.

The initialized first correction subtraction is finite because `temp = 0`, so
callers may supply finite representability only for the nonzero prefix
indices. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sub_finite
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hfiniteTail :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.finiteSystem
          ((finiteKahanTrace fmt v i).temp -
            (finiteKahanTrace fmt v i).s))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sub_finite
        fmt v n (Nat.le_refl n)
        (fun i hi => by simpa using hfiniteTail i hi))
      huSmall hBudget

/-- Sterbenz-ratio finite/coherence route for the ordinary returned Kahan
backward-error representation. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sterbenzLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hsterbenz :
      ∀ i : Fin n,
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_sterbenzRatioConditionLe
        fmt v n (Nat.le_refl n) (fun i => by simpa using hsterbenz i))
      huSmall hBudget

/-- Ferguson-exponent finite/coherence route for the ordinary returned Kahan
backward-error representation. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fergusonLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hferguson :
      ∀ i : Fin n,
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_fergusonConditionLe
        fmt v n (Nat.le_refl n) (fun i => by simpa using hferguson i))
      huSmall hBudget

/-- Tail-only Sterbenz finite/coherence route for the ordinary returned Kahan
backward-error representation.

The initialized first correction subtraction has `temp = 0`, hence is finite
from the rounded trace itself; only indices with nonzero prefix position need
the Sterbenz condition. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_sterbenzLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hsterbenz :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.sterbenzRatioConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_sterbenzLe
        fmt v n (Nat.le_refl n)
        (fun i hi => by simpa using hsterbenz i hi))
      huSmall hBudget

/-- Tail-only Ferguson finite/coherence route for the ordinary returned Kahan
backward-error representation.

As in the Sterbenz tail route, the first correction subtraction is finite
because `temp = 0`; the Ferguson condition is required only on subsequent
trace steps. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_tail_fergusonLe
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hferguson :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.fergusonExponentConditionLe
          (finiteKahanTrace fmt v i).temp
          (finiteKahanTrace fmt v i).s)
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_sub_finite
      fp fmt hround n v
      (FiniteKahanPrefixCorrectionSubFinite.of_first_exact_and_tail_fergusonLe
        fmt v n (Nat.le_refl n)
        (fun i hi => by simpa using hferguson i hi))
      huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from concrete finite-format FastTwoSum certificates.

This is the finite-format bridge for Higham equation (4.8): once the abstract
model is identified with the finite round-to-even add/sub operations and each
Kahan correction-formula step supplies the FastTwoSum representability
certificate, the exact-subtraction witness route applies end-to-end. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (n : ℕ) (v : Fin n → ℝ)
    (hcerts :
      KahanPrefixFastTwoSumFiniteCertificates fmt v n (Nat.le_refl n))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_exactSubTrace
      fp n v
      (KahanPrefixCorrectionSubExact.of_finiteRoundToEven_fastTwoSumCertificates
        fp fmt hround v n (Nat.le_refl n) hcerts)
      huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from the base-2 absolute-order FastTwoSum hypotheses at
each finite-format Kahan correction step. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (hfiniteTemp :
      ∀ i : Fin n, fmt.finiteSystem (finiteKahanTrace fmt v i).temp)
    (hfiniteY :
      ∀ i : Fin n, fmt.finiteSystem (finiteKahanTrace fmt v i).y)
    (horder :
      ∀ i : Fin n,
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|)
    (hrange :
      ∀ i : Fin n,
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp +
            (finiteKahanTrace fmt v i).y))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  have hcerts :
      KahanPrefixFastTwoSumFiniteCertificates
        fmt v n (Nat.le_refl n) := by
    exact
      KahanPrefixFastTwoSumFiniteCertificates.of_base2_abs_gt
        fmt hbeta ht v n (Nat.le_refl n)
        (fun i => by simpa using hfiniteTemp i)
        (fun i => by simpa using hfiniteY i)
        (fun i => by simpa using horder i)
        (fun i => by simpa using hrange i)
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates
      fp fmt hround n v hcerts huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from the two remaining base-2 correction-formula
obligations at each finite-format Kahan step: magnitude order and normal
range.  Finiteness of `temp` and `y` is supplied by the finite trace itself. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt_of_order_range
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (horder :
      ∀ i : Fin n,
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|)
    (hrange :
      ∀ i : Fin n,
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp +
            (finiteKahanTrace fmt v i).y))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_abs_gt
      fp fmt hround hbeta ht n v
      (finiteKahanTrace_temp_finiteSystem fmt v)
      (finiteKahanTrace_y_finiteSystem fmt v)
      horder hrange huSmall hBudget

/-- Conditional source-shaped backward-error representation for the ordinary
returned Kahan sum from tail-only base-2 correction-formula obligations.

The first correction-formula step starts with `temp = 0`, so it is closed by
finite zero-add exactness.  Only the later steps need the usual FastTwoSum
magnitude-order and normal-range hypotheses. -/
theorem fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_base2_tail_order_range
    (fp : FPModel) (fmt : FloatingPointFormat)
    (hround : KahanAddSubFiniteRoundToEvenRealization fp fmt)
    (hbeta : fmt.beta = 2) (ht : 1 < fmt.t)
    (n : ℕ) (v : Fin n → ℝ)
    (horder :
      ∀ i : Fin n, i.val ≠ 0 →
        |(finiteKahanTrace fmt v i).y| <
          |(finiteKahanTrace fmt v i).temp|)
    (hrange :
      ∀ i : Fin n, i.val ≠ 0 →
        fmt.finiteNormalRange
          ((finiteKahanTrace fmt v i).temp +
            (finiteKahanTrace fmt v i).y))
    (huSmall : fp.u ≤ 1 / 64)
    (hBudget : (3 + 40 * (n : ℝ)) * fp.u ≤ 1) :
    ∃ μ : Fin n → ℝ,
      (∀ i, |μ i| ≤
        2 * fp.u + 2 * (3 + 40 * (n : ℝ)) * fp.u ^ 2) ∧
      fl_kahanSum fp n v = ∑ i : Fin n, v i * (1 + μ i) := by
  have hcerts :
      KahanPrefixFastTwoSumFiniteCertificates
        fmt v n (Nat.le_refl n) := by
    exact
      KahanPrefixFastTwoSumFiniteCertificates.of_first_exact_and_tail_base2_abs_gt
        fmt hbeta ht v n (Nat.le_refl n)
        (fun i hi => by simpa using horder i hi)
        (fun i hi => by simpa using hrange i hi)
  exact
    fl_kahanSum_backward_error_source_bound_of_finiteRoundToEven_fastTwoSumCertificates
      fp fmt hround n v hcerts huSmall hBudget

end NumStability
