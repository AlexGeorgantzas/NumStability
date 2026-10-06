import NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter10.Theorem07.Core.Results

/-!
# Chapter10 Theorem14 CompletePivotedPSD SourceError

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.Higham1014SourceError` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- The literal trailing matrix after `r` completed Cholesky stages.

Only the trailing principal block is retained.  Its entries are computed by
the same sequential rounded multiply/subtract fold as Algorithm 10.2. -/
noncomputable def higham10_14_sourceTrailing (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if r ≤ i.val ∧ r ≤ j.val then
      fl_cholSubFold fp r
        (fun k => fl_cholesky fp n A (Fin.castLE hr k) i)
        (fun k => fl_cholesky fp n A (Fin.castLE hr k) j)
        (A i j)
    else 0

/-- The actual perturbation in display (10.23), determined by the rounded
factor and literal trailing executor rather than postulated by a caller. -/
noncomputable def higham10_14_sourceError (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    (∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
      fl_choleskyTrunc fp n A r k j) +
      higham10_14_sourceTrailing fp A r hr i j - A i j

/-- The source's rectangular `r × n` computed factor, without the zero-row
square padding used by `fl_choleskyTrunc`. -/
noncomputable def higham10_14_sourceFactorRows (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin r → Fin (r + s) → ℝ :=
  fun k j => fl_cholesky fp (r + s) A (Fin.castAdd s k) j

/-- The nonzero `s × (r+s)` row block of `Ahat^(r+1)`.  Its first `r`
columns are zero, so its operator norm is exactly the norm of the trailing
`s × s` Schur block printed in Theorem 10.14. -/
noncomputable def higham10_14_sourceTrailingRows (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ) : Fin s → Fin (r + s) → ℝ :=
  fun i j => higham10_14_sourceTrailing fp A r (Nat.le_add_right r s)
    (Fin.natAdd r i) j

/-- Display (10.23): `A + E = Rhatᵀ Rhat + Ahat^(r+1)`. -/
theorem higham10_14_equation_10_23 (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr : r ≤ n) (i j : Fin n) :
    A i j + higham10_14_sourceError fp A r hr i j =
      (∑ k : Fin n, fl_choleskyTrunc fp n A r k i *
        fl_choleskyTrunc fp n A r k j) +
        higham10_14_sourceTrailing fp A r hr i j := by
  simp only [higham10_14_sourceError]
  ring

end NumStability
