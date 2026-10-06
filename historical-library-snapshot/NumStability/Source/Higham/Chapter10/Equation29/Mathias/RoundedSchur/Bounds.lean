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
import NumStability.Source.Higham.Chapter09.DoolittleClosure
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
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.FirstBreakdown
import NumStability.Source.Higham.Chapter10.Equation29.Mathias.SourceIngredients
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
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.LUGrowth.Equation29
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.SchurStages.Bounds
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis

/-!
# Bounds

Canonical destination for 5 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.HighamMathiasSource` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

/-!
# HighamMathiasSource (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.HighamMathiasSource`
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

/-- **Higham equation (10.29), literal operator-norm form.**  The source-facing
LU growth theorem constructs the symmetric-part inverse internally; positivity
of the resulting Gram/source matrix then converts its largest eigenvalue to the
printed operator `2`-norm. -/
theorem higham10_29_source_lu_growth_bound_opNorm2 (n : ℕ) (hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hLU : LUFactSpec n A L U) :
    ∃ (Hinv : Fin n → Fin n → ℝ)
      (_hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
      (_hHinvRight : IsRightInverse n (symmetricPart n A) Hinv)
      (_hHinvLeft : IsLeftInverse n (symmetricPart n A) Hinv),
      frobNorm (higham10_29_absLUProduct L U) ≤
        (n : ℝ) * opNorm2 (higham10_29_sourceMatrix A Hinv) := by
  obtain ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, hbound⟩ :=
    higham10_29_source_lu_growth_bound n hn A L U hA hLU
  refine ⟨Hinv, hHinvSym, hHinvRight, hHinvLeft, ?_⟩
  have hnorm := higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue hn
    A Hinv hA hHinvSym hHinvRight hHinvLeft
  change opNorm2 (higham10_29_sourceMatrix A Hinv) = _ at hnorm
  rw [hnorm]
  exact hbound

/-- The inverse norm of the symmetric part cannot increase at an exact
no-pivot LU Schur step.

Writing `H = sym(S)`, its SPD Schur complement as `Z`, and
`Ĥ = sym(luFirstSchurComplement S)`, one has `Z ≤ Ĥ`, hence
`Ĥ⁻¹ ≤ Z⁻¹`.  The quadratic form of `Z⁻¹` is the trailing principal
quadratic form of `H⁻¹`, so its operator norm is bounded by `‖H⁻¹‖₂`. -/
theorem higham10_mathias_luSchur_symPartInv_opNorm2_le
    {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHinvLeft : IsLeftInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i)
    (hHhatinvRight : IsRightInverse m
      (symmetricPart m (luFirstSchurComplement S)) Hhatinv) :
    opNorm2 Hhatinv ≤ opNorm2 Hinv := by
  let H : Fin (m + 1) → Fin (m + 1) → ℝ := symmetricPart (m + 1) S
  let Hhat : Fin m → Fin m → ℝ :=
    symmetricPart m (luFirstSchurComplement S)
  let α : ℝ := S 0 0
  let fvec : Fin m → ℝ := fun i => H 0 i.succ
  let G : Fin m → Fin m → ℝ := fun i j => H i.succ j.succ
  let Z : Fin m → Fin m → ℝ :=
    fun i j => G i j - fvec i * fvec j / α
  let k : Fin m → ℝ := fun i => (S 0 i.succ - S i.succ 0) / 2
  let uvec : Fin m → ℝ := fun i => k i / Real.sqrt α
  have hα : 0 < α := by
    exact nonsymPosDef_diag_pos hS 0
  have hHspd : IsSymPosDef (m + 1) H :=
    (higham10_29_nonsymPosDef_iff_symPartSPD (m + 1) S).mp hS
  have hHsym : IsSymmetricFiniteMatrix H := hHspd.1
  have hZspd : IsSymPosDef m Z := by
    have hz := spd_schur_complement_isSymPosDef H hHspd
    have h00 : H 0 0 = α := by
      dsimp [H, α]
      unfold symmetricPart
      ring
    simp only [h00] at hz
    simpa [Z, G, fvec] using hz
  obtain ⟨Zinv, hZinvSym, hZinvRight, hZinvLeft⟩ :=
    spd_inverse_exists Z hZspd
  have hsqrt : Real.sqrt α * Real.sqrt α = α :=
    Real.mul_self_sqrt hα.le
  have huProd : ∀ i j : Fin m,
      uvec i * uvec j = k i * k j / α := by
    intro i j
    dsimp [uvec]
    rw [div_mul_div_comm, hsqrt]
  have hHhatEq : Hhat = fun i j => Z i j + uvec i * uvec j := by
    funext i j
    rw [show Hhat i j = symmetricPart m (luFirstSchurComplement S) i j by rfl,
      higham10_29_symPart_luSchur_eq]
    rw [huProd]
    dsimp [Z, G, fvec, H, α, k]
    rw [symmetricPart_symmetric (m + 1) S i.succ 0]
  have hRankPSD : finitePSD (fun i j => uvec i * uvec j) := by
    intro x
    have hrank : finiteQuadraticForm (fun i j => uvec i * uvec j) x =
        (∑ i : Fin m, uvec i * x i) ^ 2 := by
      unfold finiteQuadraticForm finiteMatVec
      calc
        (∑ i : Fin m, x i * ∑ j : Fin m, (uvec i * uvec j) * x j) =
            ∑ i : Fin m, ∑ j : Fin m,
              (x i * uvec i) * (uvec j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ i : Fin m, (x i * uvec i) *
              (∑ j : Fin m, uvec j * x j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
        _ = (∑ i : Fin m, x i * uvec i) *
            (∑ j : Fin m, uvec j * x j) := by rw [Finset.sum_mul]
        _ = (∑ i : Fin m, uvec i * x i) ^ 2 := by
          have hcomm : (∑ i : Fin m, x i * uvec i) =
              ∑ i : Fin m, uvec i * x i := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [hcomm]
          ring
    rw [hrank]
    exact sq_nonneg _
  have hLower : finiteLoewnerLe Z Hhat := by
    intro x
    rw [hHhatEq, finiteQuadraticForm_add]
    exact le_add_of_nonneg_right (hRankPSD x)
  have hZinvPSD : finitePSD Zinv := by
    intro x
    simpa [finiteQuadraticForm, finiteMatVec, matMulVec] using
      spd_inv_quadForm_nonneg Z Zinv hZspd hZinvRight x
  have hZPSD : finitePSD Z := by
    intro x
    by_cases hx : ∃ i : Fin m, x i ≠ 0
    · rw [finiteQuadraticForm_eq_sum_sum]
      exact le_of_lt (hZspd.2 x hx)
    · push_neg at hx
      simp [finiteQuadraticForm, finiteMatVec, hx]
  have hInvLoewner : finiteLoewnerLe Hhatinv Zinv := by
    have h := finiteLoewnerLe_rightInverses_anti_of_smul_left
      Z Zinv Hhat Hhatinv 1 (by norm_num) hZPSD hZspd.1
      (by simpa using hLower) hZinvRight
      (by simpa [Hhat] using hHhatinvRight)
    simpa using h
  have hZupper : finiteLoewnerLe Zinv
      (fun i j => opNorm2 Hinv * finiteIdMatrix i j) := by
    intro x
    have hZinvAct : ∀ v : Fin m → ℝ,
        matMulVec m Zinv (matMulVec m Z v) = v :=
      fun v => matMulVec_of_isRightInverse Zinv Z hZinvLeft v
    have hHinvAct : matMulVec (m + 1) H
        (matMulVec (m + 1) Hinv (Fin.cons 0 x)) = Fin.cons 0 x :=
      matMulVec_of_isRightInverse H Hinv
        (by simpa [H] using hHinvRight) (Fin.cons 0 x)
    have hblock := block_quadForm_schur_eq α hα.ne' fvec G H Hinv Z Zinv
      (by dsimp [H, α]; unfold symmetricPart; ring)
      (fun _ => rfl) (fun i => hHsym i.succ 0) (fun _ _ => rfl)
      (fun _ _ => rfl) hZinvAct 0 x hHinvAct
    have hblock' : finiteQuadraticForm Hinv (Fin.cons 0 x) =
        finiteQuadraticForm Zinv x := by
      simpa [finiteQuadraticForm, finiteMatVec, matMulVec] using hblock
    have hu := finiteLoewnerLe_smul_id_of_opNorm2Le Hinv
      (opNorm2Le_opNorm2 Hinv) (Fin.cons 0 x)
    rw [finiteQuadraticForm_smul_finiteIdMatrix] at hu ⊢
    have hpad : finiteVecNorm2Sq (Fin.cons 0 x) = finiteVecNorm2Sq x := by
      unfold finiteVecNorm2Sq
      rw [Fin.sum_univ_succ]
      simp
    rw [hblock', hpad] at hu
    exact hu
  have hZcert : finiteOpNorm2Le Zinv (opNorm2 Hinv) :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_smul_id
      Zinv (opNorm2_nonneg Hinv) hZinvSym hZinvPSD hZupper
  have hChild : higham10_4_IsNonsymPosDef m (luFirstSchurComplement S) :=
    higham10_29_luFirstSchurComplement_isNonsymPosDef S hS
  have hHhatinvPSD : finitePSD Hhatinv :=
    higham10_mathias_symPartInv_finitePSD
      (luFirstSchurComplement S) Hhatinv hChild hHhatinvRight
  have hHhatCert : finiteOpNorm2Le Hhatinv (opNorm2 Hinv) :=
    finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_of_finiteOpNorm2Le
      Hhatinv Zinv (opNorm2_nonneg Hinv) hHhatinvSym hHhatinvPSD
      hInvLoewner hZcert
  exact opNorm2_le_of_finiteOpNorm2Le Hhatinv
    (opNorm2_nonneg Hinv) hHhatCert

/-- The exact LU Schur step decreases Mathias' full condition number. -/
theorem higham10_mathias_luSchur_kappaH_le
    {m : ℕ} (hm : 0 < m)
    (S : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Hhatinv : Fin m → Fin m → ℝ)
    (hS : higham10_4_IsNonsymPosDef (m + 1) S)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHinvLeft : IsLeftInverse (m + 1)
      (symmetricPart (m + 1) S) Hinv)
    (hHhatinvSym : ∀ i j, Hhatinv i j = Hhatinv j i)
    (hHhatinvRight : IsRightInverse m
      (symmetricPart m (luFirstSchurComplement S)) Hhatinv)
    (hHhatinvLeft : IsLeftInverse m
      (symmetricPart m (luFirstSchurComplement S)) Hhatinv) :
    higham10_mathias_kappaH (luFirstSchurComplement S) Hhatinv ≤
      higham10_mathias_kappaH S Hinv := by
  let Shat : Fin m → Fin m → ℝ := luFirstSchurComplement S
  have hShat : higham10_4_IsNonsymPosDef m Shat :=
    higham10_29_luFirstSchurComplement_isNonsymPosDef S hS
  have hstage := higham10_29_stage_operator_le hm S hS Hinv Hhatinv
    hHinvSym hHhatinvSym hHinvRight hHhatinvRight
  have hf : opNorm2 (higham10_mathias_f Shat Hhatinv) ≤
      opNorm2 (higham10_mathias_f S Hinv) := by
    let rawChild : Fin m → Fin m → ℝ :=
      matMul m (matMul m (fun a b => Shat b a) Hhatinv) Shat
    let rawParent : Fin (m + 1) → Fin (m + 1) → ℝ :=
      matMul (m + 1) (matMul (m + 1) (fun a b => S b a) Hinv) S
    let hRawChild : IsSymmetricFiniteMatrix rawChild :=
      gram_conj_isSymm Hhatinv Shat hHhatinvSym
    let hRawParent : IsSymmetricFiniteMatrix rawParent :=
      gram_conj_isSymm Hinv S hHinvSym
    let hFChild : IsSymmetricFiniteMatrix (higham10_mathias_f Shat Hhatinv) :=
      higham10_29_sourceMatrix_isSymm Shat Hhatinv hHhatinvSym
        hHhatinvRight hHhatinvLeft
    let hFParent : IsSymmetricFiniteMatrix (higham10_mathias_f S Hinv) :=
      higham10_29_sourceMatrix_isSymm S Hinv hHinvSym hHinvRight hHinvLeft
    have hChildEq : finiteMaxEigenvalue hm rawChild hRawChild =
        finiteMaxEigenvalue hm (higham10_mathias_f Shat Hhatinv) hFChild :=
      finiteMaxEigenvalue_congr_matrix hm rawChild
        (higham10_mathias_f Shat Hhatinv) hRawChild hFChild
        (higham10_mathias_gram_eq_f Shat Hhatinv
          hHhatinvRight hHhatinvLeft)
    have hParentEq : finiteMaxEigenvalue (Nat.succ_pos m) rawParent hRawParent =
        finiteMaxEigenvalue (Nat.succ_pos m)
          (higham10_mathias_f S Hinv) hFParent :=
      finiteMaxEigenvalue_congr_matrix (Nat.succ_pos m) rawParent
        (higham10_mathias_f S Hinv) hRawParent hFParent
        (higham10_mathias_gram_eq_f S Hinv hHinvRight hHinvLeft)
    have hstage' : finiteMaxEigenvalue hm rawChild hRawChild ≤
        finiteMaxEigenvalue (Nat.succ_pos m) rawParent hRawParent := by
      simpa [rawChild, rawParent, Shat, hRawChild, hRawParent] using hstage
    calc
      opNorm2 (higham10_mathias_f Shat Hhatinv) =
          finiteMaxEigenvalue hm (higham10_mathias_f Shat Hhatinv) hFChild :=
        higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue hm
          Shat Hhatinv hShat hHhatinvSym hHhatinvRight hHhatinvLeft
      _ = finiteMaxEigenvalue hm rawChild hRawChild := hChildEq.symm
      _ ≤ finiteMaxEigenvalue (Nat.succ_pos m) rawParent hRawParent := hstage'
      _ = finiteMaxEigenvalue (Nat.succ_pos m)
          (higham10_mathias_f S Hinv) hFParent := hParentEq
      _ = opNorm2 (higham10_mathias_f S Hinv) :=
        (higham10_mathias_opNorm2_f_eq_finiteMaxEigenvalue (Nat.succ_pos m)
          S Hinv hS hHinvSym hHinvRight hHinvLeft).symm
  have hinv : opNorm2 Hhatinv ≤ opNorm2 Hinv :=
    higham10_mathias_luSchur_symPartInv_opNorm2_le hm S Hinv Hhatinv
      hS hHinvSym hHinvRight hHinvLeft hHhatinvSym hHhatinvRight
  unfold higham10_mathias_kappaH
  exact mul_le_mul hf hinv (opNorm2_nonneg Hhatinv)
    (opNorm2_nonneg (higham10_mathias_f S Hinv))

/-- One literal rounded Schur step preserves the full Mathias source
condition, with all child inverse and positive-definiteness data constructed
from the parent source hypotheses. -/
theorem higham10_mathias_firstRoundedSchur_sourceCondition_exists
    {m : ℕ} (hm : 1 ≤ m) (fp : FPModel)
    (A Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (hA : higham10_4_IsNonsymPosDef (m + 1) A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse (m + 1)
      (symmetricPart (m + 1) A) Hinv)
    (hHinvLeft : IsLeftInverse (m + 1)
      (symmetricPart (m + 1) A) Hinv)
    (hsource : higham10_mathias_sourceCondition fp A Hinv) :
    ∃ Hchildinv : Fin m → Fin m → ℝ,
      higham10_4_IsNonsymPosDef m (flSchurCompl m fp A) ∧
      (∀ i j, Hchildinv i j = Hchildinv j i) ∧
      IsRightInverse m (symmetricPart m (flSchurCompl m fp A)) Hchildinv ∧
      IsLeftInverse m (symmetricPart m (flSchurCompl m fp A)) Hchildinv ∧
      higham10_mathias_sourceCondition fp (flSchurCompl m fp A) Hchildinv := by
  let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
  let E : Fin m → Fin m → ℝ := higham10_mathiasFirstSchurError fp A
  let B : Fin m → Fin m → ℝ := fun i j => S i j + E i j
  have hm0 : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hS : higham10_4_IsNonsymPosDef m S :=
    higham10_29_luFirstSchurComplement_isNonsymPosDef A hA
  obtain ⟨HSinv, hHSinvSym, hHSinvRight, hHSinvLeft⟩ :=
    spd_inverse_exists (symmetricPart m S)
      ((higham10_29_nonsymPosDef_iff_symPartSPD m S).mp hS)
  have hInvExact : opNorm2 HSinv ≤ opNorm2 Hinv :=
    higham10_mathias_luSchur_symPartInv_opNorm2_le hm0 A Hinv HSinv
      hA hHinvSym hHinvRight hHinvLeft hHSinvSym hHSinvRight
  have hKappaExact : higham10_mathias_kappaH S HSinv ≤
      higham10_mathias_kappaH A Hinv :=
    higham10_mathias_luSchur_kappaH_le hm0 A Hinv HSinv hA
      hHinvSym hHinvRight hHinvLeft hHSinvSym hHSinvRight hHSinvLeft
  have hEfrob : frobNorm E ≤
      4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) := by
    simpa [E] using
      higham10_mathias_firstSchurError_frob_le_four_of_sourceCondition
        hm fp A Hinv hA hHinvSym hHinvRight hHinvLeft hsource
  have hEop : opNorm2 E ≤
      4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
        opNorm2 (higham10_mathias_f A Hinv) :=
    (opNorm2_le_frobNorm E).trans hEfrob
  let κ : ℝ := higham10_mathias_kappaH A Hinv
  let t : ℝ := Real.sqrt (↑(m + 1) : ℝ) * κ * fp.u
  let a : ℝ := opNorm2 E * opNorm2 HSinv
  have hκ0 : 0 ≤ κ := higham10_mathias_kappaH_nonneg A Hinv
  have ht0 : 0 ≤ t := by
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hκ0) fp.u_nonneg
  have ha0 : 0 ≤ a :=
    mul_nonneg (opNorm2_nonneg E) (opNorm2_nonneg HSinv)
  have hparent :
      24 * (↑(m + 1) : ℝ) * Real.sqrt (↑(m + 1) : ℝ) * κ * fp.u ≤ 1 := by
    convert hsource using 1 <;>
      simp [higham10_mathias_sourceCondition,
        higham10_mathias_nThreeHalves, κ] <;> ring
  have hparentT : 24 * (↑(m + 1) : ℝ) * t ≤ 1 := by
    convert hparent using 1 <;> simp [t] <;> ring
  have h24t : 24 * t ≤ 1 := by
    have hN1 : (1 : ℝ) ≤ (↑(m + 1) : ℝ) := by
      exact_mod_cast (show 1 ≤ m + 1 by omega)
    have htN : t ≤ (↑(m + 1) : ℝ) * t := by
      simpa using mul_le_mul_of_nonneg_right hN1 ht0
    calc
      24 * t ≤ 24 * ((↑(m + 1) : ℝ) * t) :=
        mul_le_mul_of_nonneg_left htN (by norm_num)
      _ = 24 * (↑(m + 1) : ℝ) * t := by ring
      _ ≤ 1 := hparentT
  have ha4t : a ≤ 4 * t := by
    calc
      a ≤ (4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
          opNorm2 (higham10_mathias_f A Hinv)) * opNorm2 HSinv :=
        mul_le_mul_of_nonneg_right hEop (opNorm2_nonneg HSinv)
      _ ≤ (4 * fp.u * Real.sqrt (↑(m + 1) : ℝ) *
          opNorm2 (higham10_mathias_f A Hinv)) * opNorm2 Hinv :=
        mul_le_mul_of_nonneg_left hInvExact
          (mul_nonneg
            (mul_nonneg (mul_nonneg (by norm_num) fp.u_nonneg)
              (Real.sqrt_nonneg _))
            (opNorm2_nonneg _))
      _ = 4 * t := by
        simp [t, κ, higham10_mathias_kappaH]
        ring
  have h4tHalf : 4 * t ≤ (1 : ℝ) / 2 := by linarith
  have haHalf : a ≤ (1 : ℝ) / 2 := ha4t.trans h4tHalf
  have hBpos : higham10_4_IsNonsymPosDef m B :=
    higham10_mathias_perturbed_isNonsymPosDef hm0 S E HSinv hS hHSinvRight
      (by simpa [a] using haHalf)
  obtain ⟨Hchildinv, hHchildSym, hHchildRight, hHchildLeft, hKappaPert⟩ :=
    higham10_mathias_perturbed_kappaH_exists hm0 S E HSinv hS
      hHSinvSym hHSinvRight hHSinvLeft (by simpa [a] using haHalf)
  have hdenA : 0 < 1 - a := by linarith
  have hdenT : 0 < 1 - 4 * t := by linarith
  have hratio : (1 + 7 * a) / (1 - a) ≤
      (1 + 28 * t) / (1 - 4 * t) := by
    rw [div_le_div_iff₀ hdenA hdenT]
    nlinarith
  have hratioA0 : 0 ≤ (1 + 7 * a) / (1 - a) :=
    div_nonneg (by positivity) hdenA.le
  have hKappaChild : higham10_mathias_kappaH B Hchildinv ≤
      κ * ((1 + 28 * t) / (1 - 4 * t)) := by
    calc
      higham10_mathias_kappaH B Hchildinv ≤
          higham10_mathias_kappaH S HSinv * ((1 + 7 * a) / (1 - a)) := by
        simpa [B, a] using hKappaPert
      _ ≤ κ * ((1 + 7 * a) / (1 - a)) :=
        mul_le_mul_of_nonneg_right (by simpa [κ] using hKappaExact) hratioA0
      _ ≤ κ * ((1 + 28 * t) / (1 - 4 * t)) :=
        mul_le_mul_of_nonneg_left hratio hκ0
  have hchildScalar :
      24 * (m : ℝ) * Real.sqrt m *
          higham10_mathias_kappaH B Hchildinv * fp.u ≤ 1 := by
    apply higham10_mathias_child_source_scalar_seven hm κ
      (higham10_mathias_kappaH B Hchildinv) fp.u hκ0 fp.u_nonneg hparent
    simpa [t] using hKappaChild
  have hsourceB : higham10_mathias_sourceCondition fp B Hchildinv := by
    convert hchildScalar using 1 <;>
      simp [higham10_mathias_sourceCondition,
        higham10_mathias_nThreeHalves] <;> ring
  have hBEq : B = flSchurCompl m fp A := by
    funext i j
    simp [B, S, E, higham10_mathiasFirstSchurError]
  refine ⟨Hchildinv, ?_, hHchildSym, ?_, ?_, ?_⟩
  · rw [← hBEq]
    exact hBpos
  · rw [← hBEq]
    exact hHchildRight
  · rw [← hBEq]
    exact hHchildLeft
  · rw [← hBEq]
    exact hsourceB

/-- **Higham--Mathias rounded GE success theorem.**

Under the source condition `24 n^(3/2) κ_H(A) u ≤ 1`, the literal
right-looking rounded Schur executor has a positive pivot at every stage and
therefore runs to completion.  No pivot-success or child-condition hypothesis
is supplied by the caller. -/
theorem higham10_mathias_flSchur_runsToCompletion
    {n : ℕ} (fp : FPModel)
    (A Hinv : Fin n → Fin n → ℝ)
    (hA : higham10_4_IsNonsymPosDef n A)
    (hHinvSym : ∀ i j, Hinv i j = Hinv j i)
    (hHinvRight : IsRightInverse n (symmetricPart n A) Hinv)
    (hHinvLeft : IsLeftInverse n (symmetricPart n A) Hinv)
    (hsource : higham10_mathias_sourceCondition fp A Hinv) :
    higham10_mathias_flSchurPivotsPositive fp A := by
  induction n with
  | zero =>
      trivial
  | succ m ih =>
      rw [higham10_mathias_flSchurPivotsPositive]
      refine ⟨nonsymPosDef_diag_pos hA 0, ?_⟩
      by_cases hm0 : m = 0
      · subst m
        trivial
      · have hm : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
        obtain ⟨Hchildinv, hChildPos, hChildSym,
            hChildRight, hChildLeft, hChildSource⟩ :=
          higham10_mathias_firstRoundedSchur_sourceCondition_exists
            hm fp A Hinv hA hHinvSym hHinvRight hHinvLeft hsource
        exact ih (flSchurCompl m fp A) Hchildinv hChildPos hChildSym
          hChildRight hChildLeft hChildSource

end NumStability
