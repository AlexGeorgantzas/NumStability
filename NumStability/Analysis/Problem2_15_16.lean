-- Analysis/Problem2_15_16.lean
--
-- Problem-specific theorem surface for Higham Chapter 2, Problems 2.15--2.16.

import NumStability.Analysis.FloatingPointArithmetic

namespace NumStability

noncomputable section

/-!
# Higham Chapter 2, Problems 2.15--2.16

Problem 2.15 asks what `0^0` is in IEEE arithmetic.  Problem 2.16 asks the
reader to evaluate several elementary-function expressions involving infinities
and NaNs, while warning that none of those Problem 2.16 results is specified by
the IEEE standard.

The repository's core IEEE-facing layer models primitive arithmetic operations,
comparisons, square root, signed zeros, infinities, NaNs, and exception flags.
It intentionally does not prescribe a total elementary-function library for
`pow`, `exp`, `log`, or `sign`.  This file therefore records the exact source
probe list, gives one explicit reference convention, and proves that the
unconstrained elementary-environment layer itself does not force a unique
answer.  Full language/library-specific behavior remains an empirical or
implementation-specific layer above this model.
-/

/-- The exact special-value probes appearing in Higham Problems 2.15--2.16. -/
inductive problem2_15_16Probe where
  | zeroPowZero
  | onePowPosInf
  | twoPowPosInf
  | expPosInf
  | expNegInf
  | signNaN
  | signNegNaN
  | nanPowZero
  | posInfPowZero
  | onePowNaN
  | logPosInf
  | logNegInf
  | logPosZero
  deriving DecidableEq, Repr

/-- The formal source list of all Problem 2.15--2.16 probes, in the order used
by this file: Problem 2.15's `0^0`, followed by the Problem 2.16 probes. -/
def problem2_15_16ProbeList : List problem2_15_16Probe :=
  [problem2_15_16Probe.zeroPowZero,
    problem2_15_16Probe.onePowPosInf,
    problem2_15_16Probe.twoPowPosInf,
    problem2_15_16Probe.expPosInf,
    problem2_15_16Probe.expNegInf,
    problem2_15_16Probe.signNaN,
    problem2_15_16Probe.signNegNaN,
    problem2_15_16Probe.nanPowZero,
    problem2_15_16Probe.posInfPowZero,
    problem2_15_16Probe.onePowNaN,
    problem2_15_16Probe.logPosInf,
    problem2_15_16Probe.logNegInf,
    problem2_15_16Probe.logPosZero]

theorem problem2_15_16ProbeList_length :
    problem2_15_16ProbeList.length = 13 := by
  rfl

theorem problem2_15_16ProbeList_nodup :
    problem2_15_16ProbeList.Nodup := by
  decide

theorem problem2_15_16Probe_mem_sourceList
    (probe : problem2_15_16Probe) :
    probe ∈ problem2_15_16ProbeList := by
  cases probe <;> simp [problem2_15_16ProbeList]

/-- An elementary-function environment for the probes in Problems 2.15--2.16.
The absence of axioms on this structure is deliberate: these probes are not
fixed by the primitive IEEE operation layer formalized in this repository. -/
structure problem2_15_16Environment where
  eval : problem2_15_16Probe -> IeeeOperationResult

/-- Evaluate one source probe in an elementary-function environment. -/
def problem2_15_16Eval
    (env : problem2_15_16Environment)
    (probe : problem2_15_16Probe) : IeeeOperationResult :=
  env.eval probe

/-- A concrete reference convention for the Problem 2.15--2.16 probes.  This
records common quiet/default choices, not a claim that the source's IEEE-1985
primitive-operation standard forced all these elementary-function results. -/
def problem2_15_16ReferenceResult :
    problem2_15_16Probe -> IeeeOperationResult
  | problem2_15_16Probe.zeroPowZero =>
      IeeeOperationResult.finiteNoFlags 1
  | problem2_15_16Probe.onePowPosInf =>
      IeeeOperationResult.finiteNoFlags 1
  | problem2_15_16Probe.twoPowPosInf =>
      IeeeOperationResult.valueNoFlags IeeeValue.posInf
  | problem2_15_16Probe.expPosInf =>
      IeeeOperationResult.valueNoFlags IeeeValue.posInf
  | problem2_15_16Probe.expNegInf =>
      IeeeOperationResult.valueNoFlags IeeeValue.posZero
  | problem2_15_16Probe.signNaN =>
      IeeeOperationResult.valueNoFlags IeeeValue.nan
  | problem2_15_16Probe.signNegNaN =>
      IeeeOperationResult.valueNoFlags IeeeValue.nan
  | problem2_15_16Probe.nanPowZero =>
      IeeeOperationResult.finiteNoFlags 1
  | problem2_15_16Probe.posInfPowZero =>
      IeeeOperationResult.finiteNoFlags 1
  | problem2_15_16Probe.onePowNaN =>
      IeeeOperationResult.finiteNoFlags 1
  | problem2_15_16Probe.logPosInf =>
      IeeeOperationResult.valueNoFlags IeeeValue.posInf
  | problem2_15_16Probe.logNegInf =>
      ieeeInvalidOperationDefaultResult
  | problem2_15_16Probe.logPosZero =>
      ieeeDivisionByZeroDefaultResult IeeeValue.negInf

/-- The reference convention as an elementary-function environment. -/
def problem2_15_16ReferenceEnvironment : problem2_15_16Environment where
  eval := problem2_15_16ReferenceResult

theorem problem2_15_16ReferenceEnvironment_eval
    (probe : problem2_15_16Probe) :
    problem2_15_16Eval problem2_15_16ReferenceEnvironment probe =
      problem2_15_16ReferenceResult probe :=
  rfl

theorem problem2_15_reference_zero_pow_zero_value :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.zeroPowZero).value = IeeeValue.finite 1 := by
  rfl

theorem problem2_15_reference_zero_pow_zero_noFlags :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.zeroPowZero).noFlags := by
  exact IeeeOperationResult.finiteNoFlags_noFlags 1

/-- Under the local reference convention, Problem 2.15's `0^0` probe returns
`1` without raising exception flags. -/
theorem problem2_15_reference_zero_pow_zero :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.zeroPowZero).value = IeeeValue.finite 1 ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.zeroPowZero).noFlags := by
  exact
    ⟨problem2_15_reference_zero_pow_zero_value,
      problem2_15_reference_zero_pow_zero_noFlags⟩

/-- The elementary-environment abstraction can realize any supplied result for
any source probe.  This is the formal under-specification hook for Problem
2.16's warning that the listed elementary-function values are not fixed by the
core IEEE primitive-operation standard modeled here. -/
theorem problem2_15_16_probe_can_return
    (probe : problem2_15_16Probe) (result : IeeeOperationResult) :
    ∃ env : problem2_15_16Environment,
      problem2_15_16Eval env probe = result := by
  exact ⟨⟨fun _ => result⟩, rfl⟩

/-- In particular, the model does not force a unique value for any one of the
Problem 2.15--2.16 elementary probes: the same probe can be assigned a quiet
finite-one result or an invalid-operation NaN result by two different
elementary environments. -/
theorem problem2_15_16_probe_not_forced_by_core_ieee_model
    (probe : problem2_15_16Probe) :
    ∃ envOne envNaN : problem2_15_16Environment,
      (problem2_15_16Eval envOne probe).value = IeeeValue.finite 1 ∧
      (problem2_15_16Eval envOne probe).noFlags ∧
      (problem2_15_16Eval envNaN probe).value = IeeeValue.nan ∧
      (problem2_15_16Eval envNaN probe).hasFlag
        IeeeExceptionFlag.invalidOperation := by
  refine
    ⟨⟨fun _ => IeeeOperationResult.finiteNoFlags 1⟩,
      ⟨fun _ => ieeeInvalidOperationDefaultResult⟩, ?_⟩
  exact
    ⟨rfl, IeeeOperationResult.finiteNoFlags_noFlags 1, rfl,
      ieeeInvalidOperationDefaultResult_hasInvalidOperationFlag⟩

theorem problem2_16_reference_one_pow_posInf :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.onePowPosInf).value = IeeeValue.finite 1 ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.onePowPosInf).noFlags := by
  exact ⟨rfl, IeeeOperationResult.finiteNoFlags_noFlags 1⟩

theorem problem2_16_reference_two_pow_posInf :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.twoPowPosInf).value = IeeeValue.posInf ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.twoPowPosInf).noFlags := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posInf⟩

theorem problem2_16_reference_exp_posInf :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.expPosInf).value = IeeeValue.posInf ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.expPosInf).noFlags := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posInf⟩

theorem problem2_16_reference_exp_negInf :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.expNegInf).value = IeeeValue.posZero ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.expNegInf).noFlags := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posZero⟩

theorem problem2_16_reference_sign_nan :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.signNaN).value = IeeeValue.nan ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.signNaN).noFlags := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩

theorem problem2_16_reference_sign_neg_nan :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.signNegNaN).value = IeeeValue.nan ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.signNegNaN).noFlags := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.nan⟩

theorem problem2_16_reference_nan_pow_zero :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.nanPowZero).value = IeeeValue.finite 1 ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.nanPowZero).noFlags := by
  exact ⟨rfl, IeeeOperationResult.finiteNoFlags_noFlags 1⟩

theorem problem2_16_reference_posInf_pow_zero :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.posInfPowZero).value = IeeeValue.finite 1 ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.posInfPowZero).noFlags := by
  exact ⟨rfl, IeeeOperationResult.finiteNoFlags_noFlags 1⟩

theorem problem2_16_reference_one_pow_nan :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.onePowNaN).value = IeeeValue.finite 1 ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.onePowNaN).noFlags := by
  exact ⟨rfl, IeeeOperationResult.finiteNoFlags_noFlags 1⟩

theorem problem2_16_reference_log_posInf :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.logPosInf).value = IeeeValue.posInf ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.logPosInf).noFlags := by
  exact ⟨rfl, IeeeOperationResult.valueNoFlags_noFlags IeeeValue.posInf⟩

theorem problem2_16_reference_log_negInf :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.logNegInf).value = IeeeValue.nan ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.logNegInf).hasFlag
        IeeeExceptionFlag.invalidOperation := by
  exact ⟨rfl, ieeeInvalidOperationDefaultResult_hasInvalidOperationFlag⟩

theorem problem2_16_reference_log_posZero :
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.logPosZero).value = IeeeValue.negInf ∧
    (problem2_15_16ReferenceResult
      problem2_15_16Probe.logPosZero).hasFlag
        IeeeExceptionFlag.divisionByZero := by
  exact
    ⟨rfl,
      ieeeDivisionByZeroDefaultResult_hasDivisionByZeroFlag IeeeValue.negInf⟩

end

end NumStability
