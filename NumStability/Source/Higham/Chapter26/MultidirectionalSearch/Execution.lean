/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter26.Equation03
import NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Simplex

namespace NumStability

/-! # Higham Chapter 26: Multidirectional-Search Execution

Finite-fuel iteration, relational iteration specification, convergence, and execution traces.
-/

namespace MDSSimplex

private noncomputable def iterationOrdered {n : ℕ} :
    ℕ → (RVec n → ℝ) → MDSSimplex n → Option (MDSSimplex n)
  | 0, _f, _current => none
  | fuel + 1, f, current =>
      let reflected := current.reflect
      if bestValue f reflected > f current.base then
        let expanded := current.expand
        if bestValue f expanded > bestValue f reflected then
          some (reorderBest f expanded)
        else
          some (reorderBest f reflected)
      else
        let contracted := current.contract
        if bestValue f contracted > bestValue f current then
          some (reorderBest f contracted)
        else
          iterationOrdered fuel f contracted

/-- Higham, 2nd ed., Section 26.2, pp. 475-476: one multidirectional-search
iteration with at most `fuel` contraction retries.

The input is first reordered so that `v₀` is a best current vertex.  A
successful reflection is expanded when the expanded simplex has the larger
maximum; otherwise the reflected simplex is accepted.  An unsuccessful
reflection contracts the simplex.  A contraction improving on the current
simplex is accepted, while a non-improving contraction restarts the reflection
test about the same `v₀`, with one less unit of fuel.  `none` records that this
finite observation budget did not witness completion of the iteration; it
makes no termination or optimization-correctness assumption. -/
noncomputable def iteration {n : ℕ} (fuel : ℕ) (f : RVec n → ℝ)
    (input : MDSSimplex n) : Option (MDSSimplex n) :=
  iterationOrdered fuel f (reorderBest f input)

/-- Relational, unbounded specification of a completed MDS iteration: some
finite number of contraction retries reaches one of the source's accepted
reflection, expansion, or contraction branches. -/
def IterationSpec {n : ℕ} (f : RVec n → ℝ)
    (input output : MDSSimplex n) : Prop :=
  ∃ fuel, iteration fuel f input = some output

/-- The source stopping test (26.3), specialized to an MDS simplex. -/
def Converged {n : ℕ} (tol : ℝ) (s : MDSSimplex n) : Prop :=
  mdsConverged tol s.base s.other

/-- General finite execution semantics for the MDS method: stop exactly when
the printed test (26.3) holds; otherwise complete one reflection/expansion/
contraction iteration and continue.  This trace records algorithm control flow
only.  In particular it assumes neither existence of a maximizer nor
stationarity, convergence, or global correctness of the returned simplex. -/
inductive SearchTrace {n : ℕ} (tol : ℝ) (f : RVec n → ℝ) :
    MDSSimplex n → MDSSimplex n → Prop where
  | stop (s : MDSSimplex n) (hconverged : s.Converged tol) :
      SearchTrace tol f s s
  | next {s nextState output : MDSSimplex n}
      (hnotConverged : ¬ s.Converged tol)
      (hiteration : IterationSpec f s nextState)
      (htail : SearchTrace tol f nextState output) :
      SearchTrace tol f s output

end MDSSimplex


end NumStability
