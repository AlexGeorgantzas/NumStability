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
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.CompletePivotingBound
import NumStability.Source.Higham.Chapter10.Lemma13.KahanSharpness.Endpoints
import NumStability.Source.Higham.Chapter10.Problem01.PositiveSemidefiniteEntries.Basic
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
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Bounds

Canonical destination for 4 declaration(s) relocated from
`NumStability.Algorithms.HighamChapter10` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

/-- **Section 10.4 prose**: leading principal submatrices of a matrix with
positive definite symmetric part are again in that class. -/
theorem higham10_4_nonsym_pd_leading_principal (n : ℕ)
    (A : Fin n → Fin n → ℝ) (hA : higham10_4_IsNonsymPosDef n A)
    (k : ℕ) (hk : k ≤ n) :
    higham10_4_IsNonsymPosDef k
      (fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) :=
  nonsymPosDef_leading_principal hA k hk

/-- **(10.29) per-stage quadratic-form monotonicity** (Higham §10.4): the
    `hstage` hypothesis of `stage_maxEigenvalue_le`, discharged end-to-end for a
    genuine nonsymmetric-positive-definite stage `S`.  With `H = sym(S)` and
    `Ĥ = sym(Ŝ)` (`Ŝ = luFirstSchurComplement S`) and their symmetric inverses,
    the stage Gram form never exceeds the parent trailing-block Gram form:
    `(Ŝy)ᵀĤ⁻¹(Ŝy) ≤ (S·(0,y))ᵀH⁻¹(S·(0,y))`.  Threads `schur_gram_stage_le`
    through the alignment lemmas `higham10_29_luSchur_mulVec`,
    `higham10_29_S_mulVec_cons0`, `higham10_29_symPart_luSchur_eq`, and the
    positive-semidefinite inverse fact `spd_inv_quadForm_nonneg`. -/
theorem higham10_29_stage_quadForm_le {m : ℕ}
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hHinvRight : IsRightInverse (m + 1) (symmetricPart (m + 1) S) Hinv)
    (hHhatinvRight :
      IsRightInverse m (symmetricPart m (luFirstSchurComplement S)) Hhatinv)
    (y : Fin m → ℝ) :
    (∑ p : Fin m, matMulVec m (luFirstSchurComplement S) y p *
        matMulVec m Hhatinv
          (matMulVec m (luFirstSchurComplement S) y) p) ≤
      ∑ p : Fin (m + 1),
        matMulVec (m + 1) S (Fin.cons 0 y) p *
        matMulVec (m + 1) Hinv (matMulVec (m + 1) S (Fin.cons 0 y)) p := by
  set H : Fin (m + 1) → Fin (m + 1) → ℝ := symmetricPart (m + 1) S with hHdef
  set Hhat : Fin m → Fin m → ℝ :=
    symmetricPart m (luFirstSchurComplement S) with hHhatdef
  have hα : (0 : ℝ) < S 0 0 := nonsymPosDef_diag_pos hS 0
  have hsqrtα : Real.sqrt (S 0 0) * Real.sqrt (S 0 0) = S 0 0 :=
    Real.mul_self_sqrt hα.le
  have hkk : ∀ a b : ℝ,
      a / Real.sqrt (S 0 0) * (b / Real.sqrt (S 0 0)) = a * b / S 0 0 := by
    intro a b; rw [div_mul_div_comm, hsqrtα]
  have hHspd : IsSymPosDef (m + 1) H :=
    (nonsymPosDef_iff_symPartSPD (m + 1) S).mp hS
  set Z : Fin m → Fin m → ℝ :=
    fun i j => H i.succ j.succ - H 0 i.succ * H 0 j.succ / S 0 0 with hZdef
  have hZspd : IsSymPosDef m Z := by
    have h0 := spd_schur_complement_isSymPosDef H hHspd
    have heq : H 0 0 = S 0 0 := by rw [hHdef]; unfold symmetricPart; ring
    simp only [heq] at h0
    rw [hZdef]; exact h0
  obtain ⟨Zinv, hZinvSym, hZright, hZleft⟩ := spd_inverse_exists Z hZspd
  have hβv := schur_gram_stage_le (S 0 0) hα
      (fun i => H 0 i.succ)
      (fun i => (S 0 i.succ - S i.succ 0) / 2)
      (fun i j => H i.succ j.succ)
      H Hinv Z Zinv Hhat Hhatinv
      (by rw [hHdef]; unfold symmetricPart; ring)
      (fun _ => rfl)
      (fun i => by rw [hHdef]; exact symmetricPart_symmetric (m + 1) S i.succ 0)
      (fun _ _ => rfl)
      (fun _ _ => by rw [hZdef])
      hZinvSym
      (fun vv => matMulVec_of_isRightInverse Zinv Z hZleft vv)
      (spd_inv_quadForm_nonneg Z Zinv hZspd hZright
        (fun j => (S 0 j.succ - S j.succ 0) / 2 / Real.sqrt (S 0 0)))
      (fun i j => by
        rw [hHhatdef, higham10_29_symPart_luSchur_eq, hZdef, hHdef]
        simp only []
        rw [hkk, symmetricPart_symmetric (m + 1) S i.succ 0])
      (∑ j : Fin m, S 0 j.succ * y j)
      (fun i => ∑ j : Fin m, S i.succ j.succ * y j)
      (matMulVec_of_isRightInverse H Hinv hHinvRight _)
      (matMulVec_of_isRightInverse Hhat Hhatinv hHhatinvRight _)
  have hR : matMulVec (m + 1) S (Fin.cons 0 y)
      = Fin.cons (∑ j : Fin m, S 0 j.succ * y j)
          (fun i => ∑ j : Fin m, S i.succ j.succ * y j) :=
    higham10_29_S_mulVec_cons0 S y
  have hL : matMulVec m (luFirstSchurComplement S) y
      = (fun i => (∑ j : Fin m, S i.succ j.succ * y j)
          - (∑ j : Fin m, S 0 j.succ * y j) / S 0 0
            * (H 0 i.succ - (S 0 i.succ - S i.succ 0) / 2)) := by
    funext i
    rw [higham10_29_luSchur_mulVec, hHdef]
    unfold symmetricPart
    ring
  rw [hR, hL]
  exact hβv

/-- **(10.29) operator-norm single-stage decrease** (Higham §10.4): for a
    genuine nonsymmetric-positive-definite stage `S`, the maximum eigenvalue of
    the child stage Gram `Q(Ŝ) = Ŝᵀ Ĥ⁻¹ Ŝ` (`Ŝ = luFirstSchurComplement S`,
    `Ĥ = sym Ŝ`) is at most that of the parent stage Gram `Q(S) = Sᵀ H⁻¹ S`
    (`H = sym S`).  Composes the per-stage quadratic-form monotonicity
    `higham10_29_stage_quadForm_le` (as the `hstage` of `stage_maxEigenvalue_le`,
    giving `λ_max(Q(Ŝ)) ≤ λ_max(Q₂₂)`) with the trailing-block interlacing
    `finiteMaxEigenvalue_trailing_principal_le` (`λ_max(Q₂₂) ≤ λ_max(Q(S))`).
    This is the operator-norm step chained by the GE stage induction. -/
theorem higham10_29_stage_operator_le {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i)
    (hHinvRight : IsRightInverse (m + 1) (symmetricPart (m + 1) S) Hinv)
    (hHhatinvRight :
      IsRightInverse m (symmetricPart m (luFirstSchurComplement S)) Hhatinv) :
    finiteMaxEigenvalue hm
        (matMul m (matMul m (fun a b => luFirstSchurComplement S b a) Hhatinv)
          (luFirstSchurComplement S))
        (gram_conj_isSymm Hhatinv (luFirstSchurComplement S) hHhatinvSym) ≤
      finiteMaxEigenvalue (Nat.succ_pos m)
        (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
        (gram_conj_isSymm Hinv S hHinvSym) := by
  have hstep := stage_maxEigenvalue_le hm S Hinv (luFirstSchurComplement S)
      Hhatinv hHinvSym hHhatinvSym
      (fun y => higham10_29_stage_quadForm_le S hS Hinv Hhatinv
        hHinvRight hHhatinvRight y)
  have htrail := finiteMaxEigenvalue_trailing_principal_le m hm
      (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
      (gram_conj_isSymm Hinv S hHinvSym)
      (fun i j => gram_conj_isSymm Hinv S hHinvSym i.succ j.succ)
  exact le_trans hstep htrail

/-- **(10.29) self-contained operator-norm single-stage decrease** (Higham
    §10.4): the induction-ready form of `higham10_29_stage_operator_le` whose
    only hypothesis is that the stage `S` is nonsymmetric positive definite.
    The symmetric inverses `H⁻¹ = sym(S)⁻¹` and `Ĥ⁻¹ = sym(luSchur S)⁻¹` are
    produced internally by `spd_inverse_exists` (the symmetric parts are SPD via
    `nonsymPosDef_iff_symPartSPD`, and `luFirstSchurComplement S` stays nonsym-PD
    via `higham10_29_luFirstSchurComplement_isNonsymPosDef`), so a GE stage
    induction can chain the decrease `λ_max(Q(Ŝ)) ≤ λ_max(Q(S))` across the
    Schur-complement recursion without threading inverse data by hand. -/
theorem higham10_29_stage_operator_le_exists {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S) :
    ∃ (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
      (Hhatinv : Fin m → Fin m → ℝ)
      (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
      (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i),
      finiteMaxEigenvalue hm
          (matMul m
            (matMul m (fun a b => luFirstSchurComplement S b a) Hhatinv)
            (luFirstSchurComplement S))
          (gram_conj_isSymm Hhatinv (luFirstSchurComplement S) hHhatinvSym) ≤
        finiteMaxEigenvalue (Nat.succ_pos m)
          (matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S)
          (gram_conj_isSymm Hinv S hHinvSym) := by
  obtain ⟨Hinv, hHinvSym, hHinvRight, _⟩ :=
    spd_inverse_exists (symmetricPart (m + 1) S)
      ((nonsymPosDef_iff_symPartSPD (m + 1) S).mp hS)
  obtain ⟨Hhatinv, hHhatinvSym, hHhatinvRight, _⟩ :=
    spd_inverse_exists (symmetricPart m (luFirstSchurComplement S))
      ((nonsymPosDef_iff_symPartSPD m (luFirstSchurComplement S)).mp
        (higham10_29_luFirstSchurComplement_isNonsymPosDef S hS))
  exact ⟨Hinv, Hhatinv, hHinvSym, hHhatinvSym,
    higham10_29_stage_operator_le hm S hS Hinv Hhatinv hHinvSym hHhatinvSym
      hHinvRight hHhatinvRight⟩

end NumStability
