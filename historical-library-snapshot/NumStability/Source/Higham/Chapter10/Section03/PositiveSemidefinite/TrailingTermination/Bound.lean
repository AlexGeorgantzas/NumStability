import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Bound

Canonical destination for 1 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.CholeskyPSD` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **The computed stopping test certifies the exact trailing Schur
    complement** (displays (10.23)/(10.24) for the algorithm as run):
    under the pivot-agreement hypotheses, if the computed working
    diagonal at stage `r` passes the termination test
    `max_i S̃_ii ≤ tol`, then EVERY entry of the exact stage-`r` Schur
    complement is at most `tol + h r` in absolute value — the
    `η`-reading for the Theorem 10.14 certificate: exact trailing
    smallness from a computed test plus the accumulated budget. -/
theorem fl_cp_termination_trailing_bound (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ)
    (hPSD : IsPosSemiDef n A) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h : ℕ → ℝ) (hh0 : h 0 = 0)
    (hhstep : ∀ t : ℕ, t < r →
      h t + (3 * c ^ 2 * h t + c * h t ^ 2) / (ρ / 2) ^ 2 +
        (fp.u * ((c + δ / 2) + (c + δ / 2) ^ 2 / (ρ / 2)) +
          ((c + δ / 2) ^ 2 / (ρ / 2)) * (2 * fp.u + fp.u ^ 2) *
            (1 + fp.u)) ≤ h (t + 1))
    (hhhalf : ∀ t : ℕ, t < r → h t < δ / 2)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (tol : ℝ)
    (hterm : ∀ i : Fin n, fl_cpState fp hn A r i i ≤ tol) :
    ∀ i j : Fin n, |cpState hn A r i j| ≤ tol + h r := by
  have hρ0 : (0:ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  -- the exact stage-r state is PSD
  have hSr : IsPosSemiDef n (cpState hn A r) :=
    cpState_isPosSemiDef hn A hPSD r fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s hs)
  -- the computed and exact stage-r states are h r-close
  have hagree := fl_cpPivot_sequence_agrees fp hn A r δ ρ c hδ hδρ hc
    h hh0 hhstep hhhalf hgap hfloor hcap r le_rfl
  have hdiff := hagree.1
  -- exact trailing diagonal from the computed test
  have hdiag : ∀ i : Fin n, cpState hn A r i i ≤ tol + h r := by
    intro i
    have h1 := hdiff i i
    have h2 := abs_le.mp h1
    have h3 := hterm i
    linarith [h2.2]
  exact psd_abs_entry_le_maxdiag (cpState hn A r) hSr (tol + h r)
    hdiag

end NumStability
