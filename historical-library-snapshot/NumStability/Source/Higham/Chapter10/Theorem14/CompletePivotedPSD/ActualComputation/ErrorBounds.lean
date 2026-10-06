import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.Cholesky.CholeskyDemmel
import NumStability.Algorithms.Cholesky.CholeskyFl
import NumStability.Algorithms.Cholesky.CholeskyNonsym
import NumStability.Algorithms.Cholesky.CholeskySpec
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixNorms.SpectralExtrema.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11
import NumStability.Source.Higham.Chapter10.Equation07.AbsoluteFactorNorm.Endpoints
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.Endpoints
import NumStability.Source.Higham.Chapter10.Equation30.ComplexPositiveDefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.Endpoints
import NumStability.Source.Higham.Chapter10.Lemma11.PivotSequenceStability.SourceClosure
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.EntryBounds.Results
import NumStability.Source.Higham.Chapter10.Problem04.UnpivotedGrowth.Basic
import NumStability.Source.Higham.Chapter10.Problem08.LeadingMinorsCounterexample.Basic
import NumStability.Source.Higham.Chapter10.Section01.Factorization.Basic
import NumStability.Source.Higham.Chapter10.Section02.ErrorAnalysis.Basic
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Endpoints
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Existence
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.ActualRun
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RoundedErrorAnalysis.Bounds

/-!
# ErrorBounds

Canonical destination for 6 declaration(s) relocated from
`NumStability.Algorithms.Ch10PivotedPSDSourceClosure` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

/-!
# Ch10PivotedPSDSourceClosure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Ch10PivotedPSDSourceClosure`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open scoped BigOperators

namespace NumStability

/-- Displays (10.23)--(10.25), stopping form: a scalar test on the actual
selected computed pivot controls the exact PSD Schur residual, the computed
trailing state, and the latter's operator 2-norm. -/
theorem higham10_23_25_actual_trailing_from_stop (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (r : ℕ) (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4))
    (tol : ℝ) (htol : 0 ≤ tol)
    (hstop : higham10CpStopsAt fp hn A tol r) :
    (∀ i j : Fin n, |cpState hn A r i j| ≤
      tol + higham10CpBudget fp δ ρ c r) ∧
    (∀ i j : Fin n, |higham10CpState fp hn A r i j| ≤
      tol + 2 * higham10CpBudget fp δ ρ c r) ∧
    opNorm2Le (higham10CpState fp hn A r)
      ((tol + 2 * higham10CpBudget fp δ ρ c r) * n) := by
  have hρ0 : (0 : ℝ) < ρ := lt_of_lt_of_le hδ hδρ
  obtain ⟨hclose, _⟩ := higham10CpState_close_of_smallness fp hn A r
    δ ρ c hδ hδρ hc h5 hgap hfloor hcap hsmall
  have hSr : IsPosSemiDef n (cpState hn A r) :=
    cpState_isPosSemiDef hn A hPSD r fun s hs =>
      lt_of_lt_of_le hρ0 (hfloor s hs)
  have hcomputedDiag := higham10CpStopsAt_all_diag fp hn A tol r hstop
  have hexactDiag : ∀ i : Fin n,
      cpState hn A r i i ≤ tol + higham10CpBudget fp δ ρ c r := by
    intro i
    have hab := abs_le.mp (hclose i i)
    linarith [hcomputedDiag i, hab.2]
  have hexact : ∀ i j : Fin n, |cpState hn A r i j| ≤
      tol + higham10CpBudget fp δ ρ c r :=
    psd_abs_entry_le_maxdiag (cpState hn A r) hSr
      (tol + higham10CpBudget fp δ ρ c r) hexactDiag
  have hcomputed : ∀ i j : Fin n, |higham10CpState fp hn A r i j| ≤
      tol + 2 * higham10CpBudget fp δ ρ c r := by
    intro i j
    have htri : |higham10CpState fp hn A r i j| ≤
        |cpState hn A r i j| +
          |cpState hn A r i j - higham10CpState fp hn A r i j| := by
      calc
        |higham10CpState fp hn A r i j| =
            |cpState hn A r i j +
              (higham10CpState fp hn A r i j - cpState hn A r i j)| := by
                congr 1
                ring
        _ ≤ |cpState hn A r i j| +
            |higham10CpState fp hn A r i j - cpState hn A r i j| :=
              abs_add_le _ _
        _ = |cpState hn A r i j| +
            |cpState hn A r i j - higham10CpState fp hn A r i j| := by
              rw [abs_sub_comm]
    linarith [htri, hexact i j, hclose i j]
  let i0 : Fin n := ⟨0, hn⟩
  have hg0 : 0 ≤ higham10CpBudget fp δ ρ c r :=
    le_trans (abs_nonneg _) (hclose i0 i0)
  have hb0 : 0 ≤ tol + 2 * higham10CpBudget fp δ ρ c r := by
    linarith
  exact ⟨hexact, hcomputed,
    opNorm2Le_of_uniform_abs n (higham10CpState fp hn A r)
      (tol + 2 * higham10CpBudget fp δ ρ c r) hb0 hcomputed⟩

/-- Theorem 10.14 / displays (10.21)--(10.25), actual-run componentwise
closure under one explicit smallness guard.  The error matrix is the one
computed from the executor, not a caller-supplied certificate. -/
theorem higham10_14_actual_componentwise (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    ∀ i j : Fin n, |higham10CpBackwardError fp hn A r i j| ≤
      higham10CpGramErrorBound fp r δ c := by
  obtain ⟨hg0, hgstep, hghalf, hgt4⟩ :=
    higham10CpBudget_properties fp r δ ρ c hδ hδρ hc h5 hsmall
  intro i j
  simpa [higham10CpBackwardError, higham10CpGram,
    higham10CpRow, higham10CpState, higham10CpGramErrorBound,
    higham10CpRoundUnit] using
    (higham10_14_as_run_backward_error fp hn A r δ ρ c hδ hδρ hc
      h5 hu8 hmul hPSD (higham10CpBudget fp δ ρ c) hg0
      (by simpa [higham10CpRoundUnit] using hgstep) hghalf hgt4
      hgap hfloor hcap i j)

/-- Normwise (10.25) consequence for the actual all-orders backward error. -/
theorem higham10_25_actual_backwardError_opNorm2 (fp : FPModel) {n : ℕ}
    (hn : 0 < n) (A : Fin n → Fin n → ℝ) (r : ℕ)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4)) :
    opNorm2Le (higham10CpBackwardError fp hn A r)
      (higham10CpGramErrorBound fp r δ c * n) := by
  have hE := higham10_14_actual_componentwise fp hn A r δ ρ c
    hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
  have hcd : (0 : ℝ) ≤ c + δ / 2 := by linarith
  have hB0 : 0 ≤ higham10CpGramErrorBound fp r δ c := by
    dsimp [higham10CpGramErrorBound]
    have hu0 := fp.u_nonneg
    have hcoef : (0 : ℝ) ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact mul_nonneg (Nat.cast_nonneg r)
      (add_nonneg (mul_nonneg hu0 hcd)
        (mul_nonneg hcoef (sq_nonneg _)))
  exact opNorm2Le_of_uniform_abs n (higham10CpBackwardError fp hn A r)
    (higham10CpGramErrorBound fp r δ c) hB0 hE

/-- **Theorem 10.14, actual complete-pivoted PSD source closure.**

The factor rows, trailing matrix, and error are constructed by the executor.
Under the no-tie stage data and the explicit scalar smallness guard, a scalar
computed pivot stop yields the componentwise and operator-norm forms of
(10.21)--(10.25), together with the norm of the truncated-factor residual. -/
theorem higham10_14_completePivotedPSD_actual_source_closed
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hrn : r ≤ n)
    (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4))
    (tol : ℝ) (htol : 0 ≤ tol)
    (hstop : higham10CpStopsAt fp hn A tol r) :
    Higham10CpActualCertificate fp hn A r δ ρ c tol := by
  have hE := higham10_14_actual_componentwise fp hn A r δ ρ c
    hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
  have hEnorm := higham10_25_actual_backwardError_opNorm2 fp hn A r δ ρ c
    hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
  obtain ⟨hexact, htrail, htrailNorm⟩ :=
    higham10_23_25_actual_trailing_from_stop fp hn A hPSD r δ ρ c
      hδ hδρ hc h5 hgap hfloor hcap hsmall tol htol hstop
  have hres : ∀ i j : Fin n,
      |higham10CpFactorResidual fp hn A r i j| ≤
        higham10CpGramErrorBound fp r δ c + tol +
          2 * higham10CpBudget fp δ ρ c r := by
    intro i j
    have heq : higham10CpFactorResidual fp hn A r i j =
        higham10CpBackwardError fp hn A r i j -
          higham10CpState fp hn A r i j := by
      simp only [higham10CpFactorResidual, higham10CpBackwardError]
      ring
    rw [heq]
    have htri : |higham10CpBackwardError fp hn A r i j -
        higham10CpState fp hn A r i j| ≤
        |higham10CpBackwardError fp hn A r i j| +
          |higham10CpState fp hn A r i j| := by
      have h := abs_add_le (higham10CpBackwardError fp hn A r i j)
        (-higham10CpState fp hn A r i j)
      simpa [sub_eq_add_neg] using h
    linarith [htri, hE i j, htrail i j]
  have hcd : (0 : ℝ) ≤ c + δ / 2 := by linarith
  have hB0 : 0 ≤ higham10CpGramErrorBound fp r δ c := by
    dsimp [higham10CpGramErrorBound]
    have hcoef : (0 : ℝ) ≤ 2 * fp.u + fp.u ^ 2 := by
      nlinarith [fp.u_nonneg, sq_nonneg fp.u]
    exact mul_nonneg (Nat.cast_nonneg r)
      (add_nonneg (mul_nonneg fp.u_nonneg hcd)
        (mul_nonneg hcoef (sq_nonneg _)))
  let i0 : Fin n := ⟨0, hn⟩
  have hg0 : 0 ≤ higham10CpBudget fp δ ρ c r := by
    have hclose := (higham10CpState_close_of_smallness fp hn A r δ ρ c
      hδ hδρ hc h5 hgap hfloor hcap hsmall).1 i0 i0
    exact le_trans (abs_nonneg _) hclose
  have hresB0 : 0 ≤ higham10CpGramErrorBound fp r δ c + tol +
      2 * higham10CpBudget fp δ ρ c r := by linarith
  have hresNorm := opNorm2Le_of_uniform_abs n
    (higham10CpFactorResidual fp hn A r)
    (higham10CpGramErrorBound fp r δ c + tol +
      2 * higham10CpBudget fp δ ρ c r) hresB0 hres
  refine ⟨hrn, ?_, hE, hEnorm, hexact, htrail, htrailNorm, hres, hresNorm⟩
  intro i j
  simp only [higham10CpBackwardError]
  ring

/-- **Equations (10.27)--(10.28), actual residual guarantee.**  A relative
diagonal stop on the computed executor implies the printed residual-norm
criterion with the explicit dimension cost and the honest accumulated-state
term. -/
theorem higham10_28_implies_10_27_actual_residualNorm
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (hPSD : IsPosSemiDef n A)
    (r : ℕ) (δ ρ c : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hc : 0 ≤ c)
    (h5 : gammaValid fp 5)
    (hgap : ∀ t : ℕ, t < r → ∀ i : Fin n, i ≠ cpPivot hn A t →
      cpState hn A t i i + δ ≤
        cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hfloor : ∀ t : ℕ, t < r →
      ρ ≤ cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hcap : ∀ t : ℕ, t < r → ∀ i j : Fin n,
      |cpState hn A t i j| ≤ c)
    (hsmall : higham10CpBudget fp δ ρ c r <
      min (min 1 (δ / 2)) (ρ / 4))
    (ε : ℝ) (hε : 0 ≤ ε) (hAop : 0 < opNorm2 A)
    (hstop : higham10CpStopsAt fp hn A
      (ε * higham10CpPivotValue fp hn A 0) r) :
    higham10_27_residualStopCriterion
      (opNorm2 (higham10CpState fp hn A r)) (opNorm2 A)
      ((n : ℝ) * ε +
        2 * (n : ℝ) * higham10CpBudget fp δ ρ c r / opNorm2 A) := by
  have hp0 : 0 ≤ higham10CpPivotValue fp hn A 0 := by
    dsimp [higham10CpPivotValue, higham10CpState, fl_cpStateFactor]
    exact isPosSemiDef_diag_nonneg A hPSD _
  have hp0le : higham10CpPivotValue fp hn A 0 ≤ opNorm2 A := by
    dsimp [higham10CpPivotValue, higham10CpState, fl_cpStateFactor]
    exact diag_le_opNorm2Le A (opNorm2 A) (opNorm2Le_opNorm2 A) _
  obtain ⟨_, _, htrailNorm⟩ := higham10_23_25_actual_trailing_from_stop
    fp hn A hPSD r δ ρ c hδ hδρ hc h5 hgap hfloor hcap hsmall
      (ε * higham10CpPivotValue fp hn A 0) (mul_nonneg hε hp0) hstop
  let i0 : Fin n := ⟨0, hn⟩
  have hclose := (higham10CpState_close_of_smallness fp hn A r δ ρ c
    hδ hδρ hc h5 hgap hfloor hcap hsmall).1 i0 i0
  have hg0 : 0 ≤ higham10CpBudget fp δ ρ c r :=
    le_trans (abs_nonneg _) hclose
  have hbound0 : 0 ≤
      (ε * higham10CpPivotValue fp hn A 0 +
        2 * higham10CpBudget fp δ ρ c r) * n := by positivity
  have hnorm := opNorm2_le_of_opNorm2Le
    (higham10CpState fp hn A r) hbound0 htrailNorm
  have hmono :
      (ε * higham10CpPivotValue fp hn A 0 +
          2 * higham10CpBudget fp δ ρ c r) * n ≤
        (ε * opNorm2 A + 2 * higham10CpBudget fp δ ρ c r) * n := by
    gcongr
  have heq :
      ((n : ℝ) * ε +
          2 * (n : ℝ) * higham10CpBudget fp δ ρ c r / opNorm2 A) *
          opNorm2 A =
        (ε * opNorm2 A + 2 * higham10CpBudget fp δ ρ c r) * n := by
    field_simp
  unfold higham10_27_residualStopCriterion
  rw [heq]
  exact hnorm.trans hmono

/-- Source-shaped no-ties wrapper: the auxiliary gap, pivot floor, and entry
cap are constructed from finiteness.  Thus the only quantitative premise left
for a concrete run is the displayed scalar smallness guard on the constructed
budget. -/
theorem higham10_14_completePivotedPSD_actual_of_noTies
    (fp : FPModel) {n : ℕ} (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (r : ℕ) (hrn : r ≤ n)
    (hpivot : ∀ t : ℕ, t < r →
      0 < cpState hn A t (cpPivot hn A t) (cpPivot hn A t))
    (hnoTies : Higham10_11NoTies hn A r)
    (h5 : gammaValid fp 5) (hu8 : fp.u ≤ 1 / 8)
    (hmul : ∀ x y : ℝ, fp.fl_mul x y = fp.fl_mul y x)
    (hPSD : IsPosSemiDef n A) :
    ∃ δ ρ c : ℝ,
      0 < δ ∧ δ ≤ ρ ∧ 0 ≤ c ∧
      ∀ (_hsmall : higham10CpBudget fp δ ρ c r <
          min (min 1 (δ / 2)) (ρ / 4))
        (tol : ℝ), 0 ≤ tol → higham10CpStopsAt fp hn A tol r →
          Higham10CpActualCertificate fp hn A r δ ρ c tol := by
  obtain ⟨δ, ρ, c, hδ, hδρ, hc, hgap, hfloor, hcap⟩ :=
    higham10_11_finite_noTies_gap_floor_cap hn A r hpivot hnoTies
  refine ⟨δ, ρ, c, hδ, hδρ, hc, ?_⟩
  intro hsmall tol htol hstop
  exact higham10_14_completePivotedPSD_actual_source_closed fp hn A r hrn
    δ ρ c hδ hδρ hc h5 hu8 hmul hPSD hgap hfloor hcap hsmall
      tol htol hstop

end NumStability
