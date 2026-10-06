import NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Theorem07.Core.Results

/-!
# Chapter10 Theorem14 CompletePivotedPSD SourceSuccess

Canonical destination for material split out of
`NumStability.Algorithms.Cholesky.Higham1014SourceSuccess` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

/-- **Theorem 10.14 / display (10.21), exact source success statement.**

Let `A11` be the leading `r × r` block of `A`.  If `A11` is positive definite
and the minimum eigenvalue of its diagonally scaled form exceeds
`r * gamma_(r+1) / (1 - gamma_(r+1))`, then the concrete rounded Algorithm
10.2 run on `A` has a positive raw pivot at every stage below `r`.

No pivot trace, error certificate, strengthened smallness inequality, or
no-ties hypothesis is assumed.  Positive semidefiniteness and rank of the full
matrix are not needed for this success implication, so omitting them makes the
formal theorem slightly stronger than the corresponding clause in the book. -/
theorem higham10_14_fl_cholesky_success_source (fp : FPModel) {n : ℕ}
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hr0 : 0 < r) (hrn : r ≤ n)
    (hA11 : IsSymPosDef r
      (fun i j : Fin r => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩))
    (hr1 : gammaValid fp (r + 1))
    (hγ1 : gamma fp (r + 1) < 1)
    (hH11sym : IsSymmetricFiniteMatrix (fun i j : Fin r =>
      A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ /
        (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
         Real.sqrt (A ⟨j.val, by omega⟩ ⟨j.val, by omega⟩))))
    (h1021 : (r : ℝ) *
        (gamma fp (r + 1) / (1 - gamma fp (r + 1))) <
      finiteMinEigenvalue hr0 (fun i j : Fin r =>
        A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ /
          (Real.sqrt (A ⟨i.val, by omega⟩ ⟨i.val, by omega⟩) *
           Real.sqrt (A ⟨j.val, by omega⟩ ⟨j.val, by omega⟩))) hH11sym) :
    ∀ j : Fin n, j.val < r → 0 < fl_cholPivot fp n A j := by
  let A11 : Fin r → Fin r → ℝ :=
    fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  have hdiag : ∀ i : Fin r, 0 < A11 i i := by
    intro i
    exact higham10_spd_diag_pos A11 hA11 i
  have hpiv11 := higham10_7_fl_cholesky_success_source fp r hr0 A11
    hA11.1 hdiag hr1 hγ1 hH11sym h1021
  intro j hjr
  let jr : Fin r := ⟨j.val, hjr⟩
  have hj := hpiv11 jr
  rw [fl_cholPivot_leading_principal fp hrn A jr] at hj
  simpa [jr] using hj

end NumStability
