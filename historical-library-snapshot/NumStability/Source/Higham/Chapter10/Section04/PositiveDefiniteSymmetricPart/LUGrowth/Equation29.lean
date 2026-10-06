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
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Equation29
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Equation29

Canonical destination for 3 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.Higham1029Source` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

/-!
# Higham1029Source (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.Higham1029Source`
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

/-- Strong-induction engine for (10.29), with the symmetric-part inverse
threaded explicitly so the child-to-parent spectral inequality can be used. -/
theorem higham10_29_lu_growth_aux :
    ∀ (n : ℕ) (hn : 0 < n)
      (A Hinv : Fin n → Fin n → ℝ)
      (hA : higham10_4_IsNonsymPosDef n A)
      (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
      (hHinvRight : IsRightInverse n (symmetricPart n A) Hinv)
      (hHinvLeft : IsLeftInverse n (symmetricPart n A) Hinv),
      ∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n A L U ∧
        frobNorm (higham10_29_absLUProduct L U) ≤
          (n : ℝ) * finiteMaxEigenvalue hn
            (matMul n (matMul n (fun i j => A j i) Hinv) A)
            (gram_conj_isSymm Hinv A hHinvSym) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro hn A Hinv hA hHinvSym hHinvRight hHinvLeft
      cases n with
      | zero => omega
      | succ m =>
          have hpivot : A 0 0 ≠ 0 :=
            ne_of_gt (nonsymPosDef_diag_pos hA 0)
          let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
          have hS : higham10_4_IsNonsymPosDef m S := by
            simpa [S] using
              higham10_29_luFirstSchurComplement_isNonsymPosDef A hA
          by_cases hm0 : m = 0
          · subst m
            have hhn : hn = Nat.succ_pos 0 := Subsingleton.elim _ _
            subst hn
            let L₁ : Fin 0 → Fin 0 → ℝ := fun i => Fin.elim0 i
            let U₁ : Fin 0 → Fin 0 → ℝ := fun i => Fin.elim0 i
            have hLU₁ : LUFactSpec 0 S L₁ U₁ := by
              refine ⟨?_, ?_, ?_, ?_⟩
              · intro i
                exact Fin.elim0 i
              · intro i
                exact Fin.elim0 i
              · intro i
                exact Fin.elim0 i
              · intro i
                exact Fin.elim0 i
            let L := luFirstStepL A L₁
            let U := luFirstStepU A U₁
            refine ⟨L, U,
              LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁, ?_⟩
            have hstep :=
              higham10_29_absLUProduct_firstStep_frobNorm_le A hpivot L₁ U₁
            have hfirst := higham10_29_firstRank_frob_le
              (Nat.succ_pos 0) A Hinv hA hHinvSym hHinvRight hHinvLeft
            have hzero : frobNorm (higham10_29_absLUProduct L₁ U₁) = 0 := by
              rw [frobNorm_eq_sqrt_frobNormSq]
              simp [frobNormSq]
            have hbound : frobNorm (higham10_29_absLUProduct L U) ≤
                finiteMaxEigenvalue (Nat.succ_pos 0)
                  (matMul 1 (matMul 1 (fun i j => A j i) Hinv) A)
                  (gram_conj_isSymm Hinv A hHinvSym) := by
              calc
                frobNorm (higham10_29_absLUProduct L U) ≤
                    frobNorm (fun i j => |A i 0 / A 0 0| * |A 0 j|) +
                      frobNorm (higham10_29_absLUProduct L₁ U₁) := by
                        simpa [L, U] using hstep
                _ = frobNorm (fun i j => |A i 0 / A 0 0| * |A 0 j|) := by
                      rw [hzero, add_zero]
                _ ≤ finiteMaxEigenvalue (Nat.succ_pos 0)
                      (matMul 1 (matMul 1 (fun i j => A j i) Hinv) A)
                      (gram_conj_isSymm Hinv A hHinvSym) := hfirst
            simpa using hbound
          · have hm : 0 < m := Nat.pos_of_ne_zero hm0
            obtain ⟨Hhatinv, hHhatinvSym, hHhatinvRight, hHhatinvLeft⟩ :=
              spd_inverse_exists (symmetricPart m S)
                ((higham10_29_nonsymPosDef_iff_symPartSPD m S).mp hS)
            obtain ⟨L₁, U₁, hLU₁, hchild⟩ :=
              ih m (Nat.lt_succ_self m) hm S Hhatinv hS hHhatinvSym
                hHhatinvRight hHhatinvLeft
            let L := luFirstStepL A L₁
            let U := luFirstStepU A U₁
            refine ⟨L, U,
              LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁, ?_⟩
            have hstep :=
              higham10_29_absLUProduct_firstStep_frobNorm_le A hpivot L₁ U₁
            have hfirst := higham10_29_firstRank_frob_le
              (Nat.succ_pos m) A Hinv hA hHinvSym hHinvRight hHinvLeft
            have hstage := higham10_29_stage_operator_le hm A hA Hinv Hhatinv
              hHinvSym hHhatinvSym hHinvRight hHhatinvRight
            calc
              frobNorm (higham10_29_absLUProduct L U) ≤
                  frobNorm (fun i j => |A i 0 / A 0 0| * |A 0 j|) +
                    frobNorm (higham10_29_absLUProduct L₁ U₁) := by
                      simpa [L, U] using hstep
              _ ≤ finiteMaxEigenvalue (Nat.succ_pos m)
                      (matMul (m + 1)
                        (matMul (m + 1) (fun i j => A j i) Hinv) A)
                      (gram_conj_isSymm Hinv A hHinvSym) +
                    (m : ℝ) * finiteMaxEigenvalue hm
                      (matMul m
                        (matMul m (fun i j => S j i) Hhatinv) S)
                      (gram_conj_isSymm Hhatinv S hHhatinvSym) :=
                add_le_add hfirst hchild
              _ ≤ finiteMaxEigenvalue (Nat.succ_pos m)
                      (matMul (m + 1)
                        (matMul (m + 1) (fun i j => A j i) Hinv) A)
                      (gram_conj_isSymm Hinv A hHinvSym) +
                    (m : ℝ) * finiteMaxEigenvalue (Nat.succ_pos m)
                      (matMul (m + 1)
                        (matMul (m + 1) (fun i j => A j i) Hinv) A)
                      (gram_conj_isSymm Hinv A hHinvSym) := by
                gcongr
              _ = ((m + 1 : ℕ) : ℝ) *
                    finiteMaxEigenvalue (Nat.succ_pos m)
                      (matMul (m + 1)
                        (matMul (m + 1) (fun i j => A j i) Hinv) A)
                      (gram_conj_isSymm Hinv A hHinvSym) := by
                push_cast
                ring

/-- Equation (10.29) in the equivalent parent-Gram form
`Aᵀ A_S⁻¹ A`.  The inverse is constructed from nonsymmetric positive
definiteness; the estimate holds for every exact unit-lower/upper LU
certificate. -/
theorem higham10_29_lu_growth_bound_gram (n : ℕ) (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hLU : LUFactSpec n A L U) :
    ∃ (Hinv : Fin n → Fin n → ℝ)
      (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i),
      IsRightInverse n (symmetricPart n A) Hinv ∧
      IsLeftInverse n (symmetricPart n A) Hinv ∧
      frobNorm (higham10_29_absLUProduct L U) ≤
        (n : ℝ) * finiteMaxEigenvalue hn
          (matMul n (matMul n (fun i j => A j i) Hinv) A)
          (gram_conj_isSymm Hinv A hHinvSym) := by
  obtain ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft⟩ :=
    spd_inverse_exists (symmetricPart n A)
      ((higham10_29_nonsymPosDef_iff_symPartSPD n A).mp hA)
  obtain ⟨L₀, U₀, hLU₀, hbound⟩ :=
    higham10_29_lu_growth_aux n hn A Hinv hA hHinvSym
      hHinvRight hHinvLeft
  have hdet := higham10_29_nonsymPosDef_det_ne_zero A hA
  have hUdiag : ∀ k : Fin n, U k k ≠ 0 :=
    hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet
  obtain ⟨hLeq, hUeq⟩ :=
    higham9_1_lu_unique_of_pivots_ne_zero hLU hLU₀ hUdiag
  subst L₀
  subst U₀
  exact ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, hbound⟩

/-- **Higham equation (10.29), largest-eigenvalue intermediate.**

For a real matrix with positive-definite symmetric part and any exact
unit-lower/upper factorization `A = LU`, construct `A_S⁻¹` internally and prove

`‖ |L| |U| ‖_F ≤ n · λ_max(A_S + A_Kᵀ A_S⁻¹ A_K)`.

The source matrix is symmetric positive semidefinite (it is the congruence
`Aᵀ A_S⁻¹ A`).  `higham10_29_source_lu_growth_bound_opNorm2` in
`HighamMathiasSource` supplies the final equality with the operator 2-norm
printed in the book. -/
theorem higham10_29_source_lu_growth_bound (n : ℕ) (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hLU : LUFactSpec n A L U) :
    ∃ (Hinv : Fin n → Fin n → ℝ)
      (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
      (hHinvRight : IsRightInverse n (symmetricPart n A) Hinv)
      (hHinvLeft : IsLeftInverse n (symmetricPart n A) Hinv),
      frobNorm (higham10_29_absLUProduct L U) ≤
        (n : ℝ) * finiteMaxEigenvalue hn
          (higham10_29_sourceMatrix A Hinv)
          (higham10_29_sourceMatrix_isSymm A Hinv hHinvSym
            hHinvRight hHinvLeft) := by
  obtain ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, hbound⟩ :=
    higham10_29_lu_growth_bound_gram n hn A L U hA hLU
  refine ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, ?_⟩
  have hEq := higham10_29_gram_eq_sourceMatrix A Hinv
    hHinvRight hHinvLeft
  have hEig := finiteMaxEigenvalue_congr hn
    (matMul n (matMul n (fun i j => A j i) Hinv) A)
    (higham10_29_sourceMatrix A Hinv)
    (gram_conj_isSymm Hinv A hHinvSym)
    (higham10_29_sourceMatrix_isSymm A Hinv hHinvSym
      hHinvRight hHinvLeft) hEq
  exact hbound.trans_eq (congrArg (fun x => (n : ℝ) * x) hEig)

end NumStability
