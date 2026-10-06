import Mathlib

open scoped BigOperators

namespace HighamBench

def p59SpectralTail {n : ℕ} (lambda : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), lambda i

noncomputable def p59LogSpectralTail {n : ℕ} (lambda : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => k ≤ i.val), Real.log (1 + lambda i)

noncomputable def p59RelativeTraceError (traceA traceT : ℝ) : ℝ :=
  (traceA - traceT) / traceA

def p59PowerGapFactor (gamma : ℝ) (q : ℕ) : ℝ :=
  gamma ^ (2 * q - 1)

end HighamBench
