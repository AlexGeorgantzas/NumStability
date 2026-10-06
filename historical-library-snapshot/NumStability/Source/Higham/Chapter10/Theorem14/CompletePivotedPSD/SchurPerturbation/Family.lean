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
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Perturbation.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.Basic
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.KahanMatrix
import NumStability.Algorithms.LinearSystems.Cholesky.PositiveSemidefinite.ScaledStage
import NumStability.Algorithms.LinearSystems.Cholesky.RoundedFactorization.Basic
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
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
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.PivotingAndScaling.Results
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.SchurComplement
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.Termination
import NumStability.Source.Higham.Chapter10.Section03.PositiveSemidefinite.WNormBound
import NumStability.Source.Higham.Chapter10.Section04.PositiveDefiniteSymmetricPart.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem06.RoundedCholesky.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem07.FailureVacuity.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.ComponentwisePerturbation.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem08.NormwiseDiscrepancy.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Endpoints
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.Equation22
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.PsdErrorAnalysis
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.RankSensitiveError.Bounds
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceError
import NumStability.Source.Higham.Chapter10.Theorem14.CompletePivotedPSD.SourceSuccess

/-!
# Family

Canonical destination for 9 declaration(s) relocated from
`NumStability.Algorithms.Cholesky.Higham1014Equation1022` during wave R04. Declaration names, kinds, signatures and
visibilities are unchanged; authored-private declarations keep their
names and change only their mangled module owner, per the reviewed
B0008 private-normalization map.
-/

/-!
# Higham1014Equation1022 (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.Cholesky.Higham1014Equation1022`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace NumStability

/-- The PSD/rank hypotheses of Theorem 10.14 generate the exact zero Schur
complement; no Schur identity is accepted as an extra premise.  The proof
uses the constructive rank-truncated pivoted Cholesky factor from Theorem
10.9, undoes its permutation, and then applies
`higham10_14_gram_schur_zero`. -/
theorem higham10_14_psd_rank_schur_zero {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A)) :
    higham10_14_block22 A =
      rectMatMul
        (rectMatMul (higham10_14_block21 A)
          (nonsingInv r (higham10_14_block11 A)))
        (higham10_14_block12 A) := by
  obtain ⟨q, σ, R, hq, hspec, hqrank⟩ :=
    higham10_9_psd_pivoted_cholesky_rank (r + s) A hPSD
  have hqr : q = r := by omega
  have hspecR :
      higham10_9_PivotedCholeskySpec (r + s) A R σ r := by
    simpa [hqr] using hspec
  obtain ⟨τ, hleft, hright⟩ :=
    Function.bijective_iff_has_inverse.mp hspecR.perm
  let Z1 : Fin r → Fin r → ℝ := fun k j =>
    R (Fin.castAdd s k) (τ (Fin.castAdd s j))
  let Z2 : Fin r → Fin s → ℝ := fun k j =>
    R (Fin.castAdd s k) (τ (Fin.natAdd r j))
  have hGram : ∀ i j : Fin (r + s),
      A i j = ∑ k : Fin r,
        R (Fin.castAdd s k) (τ i) * R (Fin.castAdd s k) (τ j) := by
    intro i j
    have hp := hspecR.product_eq (τ i) (τ j)
    rw [hright i, hright j, Fin.sum_univ_add] at hp
    have htail :
        (∑ k : Fin s,
          R (Fin.natAdd r k) (τ i) * R (Fin.natAdd r k) (τ j)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      rw [hspecR.R_rank_zero (Fin.natAdd r k) (τ i) (by simp), zero_mul]
    rw [htail, add_zero] at hp
    exact hp.symm
  have h11 : higham10_14_block11 A =
      rectMatMul (finiteTranspose Z1) Z1 := by
    ext i j
    simpa [higham10_14_block11, Z1, rectMatMul, finiteTranspose] using
      hGram (Fin.castAdd s i) (Fin.castAdd s j)
  have h12 : higham10_14_block12 A =
      rectMatMul (finiteTranspose Z1) Z2 := by
    ext i j
    simpa [higham10_14_block12, Z1, Z2, rectMatMul, finiteTranspose] using
      hGram (Fin.castAdd s i) (Fin.natAdd r j)
  have h21 : higham10_14_block21 A =
      rectMatMul (finiteTranspose Z2) Z1 := by
    ext i j
    simpa [higham10_14_block21, Z1, Z2, rectMatMul, finiteTranspose] using
      hGram (Fin.natAdd r i) (Fin.castAdd s j)
  have h22 : higham10_14_block22 A =
      rectMatMul (finiteTranspose Z2) Z2 := by
    ext i j
    simpa [higham10_14_block22, Z2, rectMatMul, finiteTranspose] using
      hGram (Fin.natAdd r i) (Fin.natAdd r j)
  have hdet11 : Matrix.det
      (higham10_14_block11 A : Matrix (Fin r) (Fin r) ℝ) ≠ 0 :=
    isSymPosDef_det_ne_zero (higham10_14_block11 A) hA11
  have hdetGram : Matrix.det
      (rectMatMul (finiteTranspose Z1) Z1 : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    rw [← h11]
    exact hdet11
  rw [h11, h12, h21, h22]
  rw [rectMatMul_assoc]
  exact higham10_14_gram_schur_zero Z1 Z2 hdetGram

/-- Literal Lemma 10.10 specialized to the matrices generated in Theorem
10.14.  The unperturbed Schur term is eliminated from the PSD/rank
hypotheses, the perturbed inverse is generated from the actual computed
triangular block, and every term in the final parenthesis contains at least
two factors from the actual error `E`. -/
theorem higham10_14_actual_schur_perturbation_exact (fp : FPModel) {r s : ℕ}
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let A11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 A
    let A12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 A
    let A21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 A
    let M : Matrix (Fin r) (Fin r) ℝ :=
      nonsingInv r (higham10_14_block11 A)
    let X : Matrix (Fin r) (Fin r) ℝ :=
      nonsingInv r
        (higham10_14_block11 A + higham10_14_block11 E)
    let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
    let E12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 E
    let E21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 E
    let E22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 E
    (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
      (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
      + (-(E21 * M * E12)
          - A21 * (M * E11 * (M * E11 * X)) * A12
          + E21 * (M * E11 * X) * A12
          + A21 * (M * E11 * X) * E12
          + E21 * (M * E11 * X) * E12) := by
  dsimp only
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let A11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 A
  let A12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 A
  let A21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 A
  let A22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 A
  let M : Matrix (Fin r) (Fin r) ℝ := nonsingInv r (higham10_14_block11 A)
  let X : Matrix (Fin r) (Fin r) ℝ := nonsingInv r
    (higham10_14_block11 A + higham10_14_block11 E)
  let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
  let E12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 E
  let E21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 E
  let E22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 E
  have hSchurF := higham10_14_actualSchur_eq_perturbedSchur
    fp A hr1 hsuccess
  have hSchur : (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
      (A22 + E22) - (A21 + E21) * X * (A12 + E12) := by
    ext i j
    simpa [A11, A12, A21, A22, E, E11, E12, E21, E22, X,
      rectMatMul, Matrix.mul_apply] using congrFun (congrFun hSchurF i) j
  have hZeroF := higham10_14_psd_rank_schur_zero A hPSD hrank hA11
  have hZero : A22 - A21 * M * A12 = 0 := by
    ext i j
    have h := congrFun (congrFun hZeroF i) j
    simp only [A22, A21, A12, M]
    simpa [rectMatMul, Matrix.mul_apply] using sub_eq_zero.mpr h
  have hdetA11 : Matrix.det A11 ≠ 0 := by
    simpa [A11] using isSymPosDef_det_ne_zero
      (higham10_14_block11 A) hA11
  have hMpred : IsInverse r (higham10_14_block11 A)
      (nonsingInv r (higham10_14_block11 A)) :=
    isInverse_nonsingInv_of_det_ne_zero r _ (by simpa [A11] using hdetA11)
  have hM : M * A11 = 1 := by
    ext i j
    simpa [M, A11, Matrix.mul_apply] using hMpred.1 i j
  obtain ⟨h11F, _h12F, _h21F, _h22F⟩ :=
    higham10_14_actual_block_equations fp A
  let R11 := higham10_14_actualR11 fp A
  have hRinv := higham10_14_actualR11_isInverse fp A hr1 hsuccess
  have hdetRof : Matrix.det (Matrix.of R11) ≠ 0 := by
    have hmul : Matrix.of R11 * Matrix.of (nonsingInv r R11) = 1 := by
      ext i j
      simpa [Matrix.mul_apply, R11] using hRinv.2 i j
    intro hz
    have hd := congrArg Matrix.det hmul
    rw [Matrix.det_mul, hz, zero_mul, Matrix.det_one] at hd
    norm_num at hd
  have hdetGram : Matrix.det
      (Matrix.of (rectMatMul (finiteTranspose R11) R11)) ≠ 0 := by
    have heq : Matrix.of (rectMatMul (finiteTranspose R11) R11) =
        (Matrix.of R11).transpose * Matrix.of R11 := by ext i j; rfl
    rw [heq, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero hdetRof hdetRof
  have hdetPert : Matrix.det
      ((higham10_14_block11 A + higham10_14_block11 E :
        Fin r → Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ) ≠ 0 := by
    have hmat : Matrix.of
        (higham10_14_block11 A + higham10_14_block11 E) =
          Matrix.of (rectMatMul (finiteTranspose R11) R11) := by
      simpa [R11, E] using congrArg Matrix.of h11F
    have hdetPertOf : Matrix.det
        (Matrix.of (higham10_14_block11 A + higham10_14_block11 E)) ≠ 0 := by
      rw [hmat]
      exact hdetGram
    simpa using hdetPertOf
  have hXpred : IsInverse r
      (higham10_14_block11 A + higham10_14_block11 E)
      (nonsingInv r
        (higham10_14_block11 A + higham10_14_block11 E)) :=
    isInverse_nonsingInv_of_det_ne_zero r _ hdetPert
  have hX : (A11 + E11) * X = 1 := by
    ext i j
    simpa [A11, E11, X, Matrix.mul_apply] using hXpred.2 i j
  have hres : X = M - M * E11 * X :=
    schur_resolvent_from_inverses M X A11 E11 hM hX
  have hexact := schur_perturbation_exact A21 E21 A12 E12 A22 E22
    M X E11 hres
  calc
    (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
        (A22 + E22) - (A21 + E21) * X * (A12 + E12) := hSchur
    _ = (A22 - A21 * M * A12)
        + (E22 - E21 * M * A12 - A21 * M * E12
            + A21 * (M * E11 * M) * A12)
        + (-(E21 * M * E12)
            - A21 * (M * E11 * (M * E11 * X)) * A12
            + E21 * (M * E11 * X) * A12
            + A21 * (M * E11 * X) * E12
            + E21 * (M * E11 * X) * E12) := hexact
    _ = (E22 - E21 * M * A12 - A21 * M * E12
          + A21 * (M * E11 * M) * A12)
        + (-(E21 * M * E12)
            - A21 * (M * E11 * (M * E11 * X)) * A12
            + E21 * (M * E11 * X) * A12
            + A21 * (M * E11 * X) * E12
            + E21 * (M * E11 * X) * E12) := by rw [hZero, zero_add]

private theorem higham10_14_rectOpNorm2Le_add {m n : ℕ}
    (A B : Fin m → Fin n → ℝ) {a b : ℝ}
    (hA : rectOpNorm2Le A a) (hB : rectOpNorm2Le B b) :
    rectOpNorm2Le (fun i j => A i j + B i j) (a + b) := by
  intro x
  have haction : rectMatMulVec (fun i j => A i j + B i j) x =
      fun i => rectMatMulVec A x i + rectMatMulVec B x i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction]
  calc
    vecNorm2 (fun i => rectMatMulVec A x i + rectMatMulVec B x i)
        ≤ vecNorm2 (rectMatMulVec A x) + vecNorm2 (rectMatMulVec B x) :=
          vecNorm2_add_le _ _
    _ ≤ a * vecNorm2 x + b * vecNorm2 x := add_le_add (hA x) (hB x)
    _ = (a + b) * vecNorm2 x := by ring

private theorem higham10_14_rectOpNorm2Le_neg {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a : ℝ} (hA : rectOpNorm2Le A a) :
    rectOpNorm2Le (fun i j => -A i j) a := by
  intro x
  have haction : rectMatMulVec (fun i j => -A i j) x =
      fun i => -rectMatMulVec A x i := by
    ext i
    unfold rectMatMulVec
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [haction, vecNorm2_neg]
  exact hA x

private theorem higham10_14_abs_entry_le_of_rectOpNorm2Le {m n : ℕ}
    (A : Fin m → Fin n → ℝ) {a : ℝ} (hA : rectOpNorm2Le A a)
    (i : Fin m) (j : Fin n) : |A i j| ≤ a := by
  let x : Fin n → ℝ := finiteBasisVec j
  have hcol : rectMatMulVec A x = fun k => A k j := by
    ext k
    unfold rectMatMulVec x finiteBasisVec
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hcoord := abs_coord_le_vecNorm2 (rectMatMulVec A x) i
  have hnorm := hA x
  have hx : vecNorm2 x = 1 := by
    simpa [x] using vecNorm2_finiteBasisVec j
  rw [hcol] at hcoord
  rw [hcol, hx, mul_one] at hnorm
  exact le_trans hcoord hnorm

/-- The first-order Schur perturbation generated by an arbitrary full error
matrix has operator norm at most `‖E‖₂ (‖W‖₂ + 1)²`. -/
theorem higham10_14_linearSchur_opNorm2Le {r s : ℕ}
    (A E : Fin (r + s) → Fin (r + s) → ℝ) :
    let W := higham10_14_W A
    let e := complexMatrixOp2 (realRectToCMatrix E)
    let w := complexMatrixOp2 (realRectToCMatrix W)
    rectOpNorm2Le
      (fun i j =>
        higham10_14_block22 E i j -
          rectMatMul (higham10_14_block21 E) W i j -
          rectMatMul (finiteTranspose W) (higham10_14_block12 E) i j +
          rectMatMul
            (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) W i j)
      (e * (w + 1) ^ 2) := by
  dsimp only
  let W := higham10_14_W A
  let e := complexMatrixOp2 (realRectToCMatrix E)
  let w := complexMatrixOp2 (realRectToCMatrix W)
  have he0 : 0 ≤ e := complexMatrixOp2_nonneg _
  have hw0 : 0 ≤ w := complexMatrixOp2_nonneg _
  have hEfull : opNorm2Le E e :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix E
  obtain ⟨hE11, hE12, hE21, hE22⟩ :=
    higham10_14_blocks_opNorm2Le E hEfull
  have hE11r : rectOpNorm2Le (higham10_14_block11 E) e := by
    intro x
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hE11 x
  have hE22r : rectOpNorm2Le (higham10_14_block22 E) e := by
    intro x
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hE22 x
  have hW : rectOpNorm2Le W w :=
    rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le W le_rfl
  have hWt : rectOpNorm2Le (finiteTranspose W) w :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le W hw0 hW
  have h21W : rectOpNorm2Le
      (rectMatMul (higham10_14_block21 E) W) (e * w) :=
    rectOpNorm2Le_rectMatMul _ _ he0 hE21 hW
  have hWt12 : rectOpNorm2Le
      (rectMatMul (finiteTranspose W) (higham10_14_block12 E)) (w * e) :=
    rectOpNorm2Le_rectMatMul _ _ hw0 hWt hE12
  have hWt11 : rectOpNorm2Le
      (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) (w * e) :=
    rectOpNorm2Le_rectMatMul _ _ hw0 hWt hE11r
  have hWt11W : rectOpNorm2Le
      (rectMatMul
        (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) W)
      (w * e * w) :=
    rectOpNorm2Le_rectMatMul _ _ (mul_nonneg hw0 he0) hWt11 hW
  have hneg21 := higham10_14_rectOpNorm2Le_neg
    (rectMatMul (higham10_14_block21 E) W) h21W
  have hneg12 := higham10_14_rectOpNorm2Le_neg
    (rectMatMul (finiteTranspose W) (higham10_14_block12 E)) hWt12
  have h1 := higham10_14_rectOpNorm2Le_add
    (higham10_14_block22 E)
    (fun i j => -rectMatMul (higham10_14_block21 E) W i j)
    hE22r hneg21
  have h2 := higham10_14_rectOpNorm2Le_add
    (fun i j => higham10_14_block22 E i j -
      rectMatMul (higham10_14_block21 E) W i j)
    (fun i j => -rectMatMul (finiteTranspose W)
      (higham10_14_block12 E) i j)
    h1 hneg12
  have h3 := higham10_14_rectOpNorm2Le_add
    (fun i j => higham10_14_block22 E i j -
      rectMatMul (higham10_14_block21 E) W i j -
      rectMatMul (finiteTranspose W) (higham10_14_block12 E) i j)
    (rectMatMul
      (rectMatMul (finiteTranspose W) (higham10_14_block11 E)) W)
    h2 hWt11W
  convert h3 using 1 <;> ring

/-- Quantitative Lemma 10.10 for the literal trailing block in Theorem
10.14.  The leading term has the exact source coefficient
`(‖W‖₂+1)²‖E‖₂`; the displayed second term is a fixed multiple of `‖E‖₂²`.
The only radius assumptions control the actual perturbation and are not
bounds on the Schur complement or final residual. -/
theorem higham10_14_actualSchur_quadratic_bound {r s : ℕ}
    (fp : FPModel) (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hr1 : gammaValid fp (r + 1))
    (hsuccess : ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot fp (r + s) A q)
    (hEone : complexMatrixOp2 (realRectToCMatrix
      (higham10_14_sourceError fp A r (Nat.le_add_right r s))) ≤ 1)
    (hinvRadius :
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_sourceError fp A r (Nat.le_add_right r s))) ≤ 1 / 2) :
    let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
    let e := complexMatrixOp2 (realRectToCMatrix E)
    let a := complexMatrixOp2 (realRectToCMatrix A)
    let M := nonsingInv r (higham10_14_block11 A)
    let μ := complexMatrixOp2 (realRectToCMatrix M)
    let W := higham10_14_W A
    let w := complexMatrixOp2 (realRectToCMatrix W)
    let C := (s : ℝ) *
      ((r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
        4 * (r : ℝ) ^ 4 * a * μ ^ 2 + 2 * (r : ℝ) ^ 4 * μ ^ 2)
    complexMatrixOp2 (realRectToCMatrix (higham10_14_actualSchur fp A)) ≤
      e * (w + 1) ^ 2 + C * e ^ 2 := by
  dsimp only
  let E := higham10_14_sourceError fp A r (Nat.le_add_right r s)
  let e := complexMatrixOp2 (realRectToCMatrix E)
  let a := complexMatrixOp2 (realRectToCMatrix A)
  let A12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 A
  let A21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 A
  let M : Matrix (Fin r) (Fin r) ℝ :=
    nonsingInv r (higham10_14_block11 A)
  let μ := complexMatrixOp2 (realRectToCMatrix M)
  let W : Matrix (Fin r) (Fin s) ℝ := higham10_14_W A
  let Wt : Matrix (Fin s) (Fin r) ℝ := finiteTranspose W
  let w := complexMatrixOp2 (realRectToCMatrix W)
  let E11 : Matrix (Fin r) (Fin r) ℝ := higham10_14_block11 E
  let E12 : Matrix (Fin r) (Fin s) ℝ := higham10_14_block12 E
  let E21 : Matrix (Fin s) (Fin r) ℝ := higham10_14_block21 E
  let E22 : Matrix (Fin s) (Fin s) ℝ := higham10_14_block22 E
  let X : Matrix (Fin r) (Fin r) ℝ :=
    nonsingInv r (higham10_14_block11 A + higham10_14_block11 E)
  let R : Matrix (Fin s) (Fin s) ℝ :=
    -(E21 * M * E12)
      - A21 * (M * E11 * (M * E11 * X)) * A12
      + E21 * (M * E11 * X) * A12
      + A21 * (M * E11 * X) * E12
      + E21 * (M * E11 * X) * E12
  let C0 := (r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
    4 * (r : ℝ) ^ 4 * a * μ ^ 2 + 2 * (r : ℝ) ^ 4 * μ ^ 2
  let C := (s : ℝ) * C0
  have he0 : 0 ≤ e := complexMatrixOp2_nonneg _
  have ha0 : 0 ≤ a := complexMatrixOp2_nonneg _
  have hμ0 : 0 ≤ μ := complexMatrixOp2_nonneg _
  have hw0 : 0 ≤ w := complexMatrixOp2_nonneg _
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg s) hC0
  have hEfull : opNorm2Le E e :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix E
  obtain ⟨hE11op, hE12op, hE21op, _hE22op⟩ :=
    higham10_14_blocks_opNorm2Le E hEfull
  have hAfull : opNorm2Le A a :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix A
  obtain ⟨_hA11op, hA12op, hA21op, _hA22op⟩ :=
    higham10_14_blocks_opNorm2Le A hAfull
  have hMop : opNorm2Le M μ :=
    opNorm2Le_complexMatrixOp2_realRectToCMatrix M
  have hE11norm : complexMatrixOp2 (realRectToCMatrix E11) ≤ e :=
    complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le E11 he0 hE11op
  have hsmall11 : μ * complexMatrixOp2 (realRectToCMatrix E11) ≤ 1 / 2 := by
    exact le_trans (mul_le_mul_of_nonneg_left hE11norm hμ0)
      (by simpa [μ, e, E, M] using hinvRadius)
  have hXnorm : complexMatrixOp2 (realRectToCMatrix X) ≤ 2 * μ := by
    simpa [E, E11, X, M, μ] using
      higham10_14_actual_inverse_complexOp2_le fp A hA11 hr1 hsuccess hsmall11
  have hXop : opNorm2Le X (2 * μ) := by
    intro v
    calc
      vecNorm2 (matMulVec r X v) ≤
          complexMatrixOp2 (realRectToCMatrix X) * vecNorm2 v :=
        opNorm2Le_complexMatrixOp2_realRectToCMatrix X v
      _ ≤ (2 * μ) * vecNorm2 v :=
        mul_le_mul_of_nonneg_right hXnorm (vecNorm2_nonneg v)
  have hE11r : rectOpNorm2Le E11 e := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hE11op v
  have hMr : rectOpNorm2Le M μ := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hMop v
  have hXr : rectOpNorm2Le X (2 * μ) := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hXop v
  have hA21ent : ∀ i j, |A21 i j| ≤ a :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le A21 hA21op i j
  have hA12ent : ∀ i j, |A12 i j| ≤ a :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le A12 hA12op i j
  have hE21ent : ∀ i j, |E21 i j| ≤ e :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le E21 hE21op i j
  have hE12ent : ∀ i j, |E12 i j| ≤ e :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le E12 hE12op i j
  have hE11ent : ∀ i j, |E11 i j| ≤ e :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le E11 hE11r i j
  have hMent : ∀ i j, |M i j| ≤ μ :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le M hMr i j
  have hXent : ∀ i j, |X i j| ≤ 2 * μ :=
    fun i j => higham10_14_abs_entry_le_of_rectOpNorm2Le X hXr i j
  have hRraw := schur_perturbation_remainder_bound
    A21 E21 A12 E12 M X E11 a μ (2 * μ) e
    ha0 hμ0 (mul_nonneg (by norm_num) hμ0) he0
    hA21ent hA12ent hE21ent hE12ent hE11ent hMent hXent
  have hcoef :
      (r : ℝ) ^ 2 * μ + (r : ℝ) ^ 6 * a ^ 2 * μ ^ 2 * (2 * μ) +
          2 * ((r : ℝ) ^ 4 * a * μ * (2 * μ)) +
          (r : ℝ) ^ 4 * μ * (2 * μ) * e ≤ C0 := by
    calc
      (r : ℝ) ^ 2 * μ + (r : ℝ) ^ 6 * a ^ 2 * μ ^ 2 * (2 * μ) +
            2 * ((r : ℝ) ^ 4 * a * μ * (2 * μ)) +
            (r : ℝ) ^ 4 * μ * (2 * μ) * e =
          ((r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
            4 * (r : ℝ) ^ 4 * a * μ ^ 2) +
              (2 * (r : ℝ) ^ 4 * μ ^ 2) * e := by ring
      _ ≤ ((r : ℝ) ^ 2 * μ + 2 * (r : ℝ) ^ 6 * a ^ 2 * μ ^ 3 +
            4 * (r : ℝ) ^ 4 * a * μ ^ 2) +
              (2 * (r : ℝ) ^ 4 * μ ^ 2) * 1 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (by simpa [e, E] using hEone) (by positivity))
      _ = C0 := by ring
  have hRentry : ∀ i j, |R i j| ≤ C0 * e ^ 2 := by
    intro i j
    calc
      |R i j| ≤
          ((r : ℝ) ^ 2 * μ + (r : ℝ) ^ 6 * a ^ 2 * μ ^ 2 * (2 * μ) +
            2 * ((r : ℝ) ^ 4 * a * μ * (2 * μ)) +
            (r : ℝ) ^ 4 * μ * (2 * μ) * e) * e ^ 2 := by
        simpa [R] using hRraw i j
      _ ≤ C0 * e ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg e)
  have hscaled := opNorm2Le_smul s (fun _ _ : Fin s => (1 : ℝ))
    (s : ℝ) (C0 * e ^ 2) (mul_nonneg hC0 (sq_nonneg e))
    (higham10_7_onesMatrix_opNorm2Le s)
  have hRop : opNorm2Le R (C * e ^ 2) := by
    have hpre := opNorm2Le_of_abs_le s R (fun _ _ => C0 * e ^ 2 * 1)
      (fun i j => by rw [mul_one]; exact hRentry i j)
      (C0 * e ^ 2 * (s : ℝ)) hscaled
    convert hpre using 1 <;> simp [C] <;> ring
  let L : Matrix (Fin s) (Fin s) ℝ := fun i j =>
    E22 i j - rectMatMul E21 W i j -
      rectMatMul (finiteTranspose W) E12 i j +
      rectMatMul (rectMatMul (finiteTranspose W) E11) W i j
  have hLrect : rectOpNorm2Le L (e * (w + 1) ^ 2) := by
    simpa [L, E, E11, E12, E21, E22, W, e, w] using
      higham10_14_linearSchur_opNorm2Le A E
  have hLop : opNorm2Le L (e * (w + 1) ^ 2) := by
    intro v
    simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hLrect v
  have hMA12 : M * A12 = (W : Matrix (Fin r) (Fin s) ℝ) := by
    ext i j
    rfl
  have hA21M : A21 * M =
      Wt := by
    ext i j
    exact congrFun (congrFun
      (higham10_14_A21M_eq_Wtranspose A hPSD.1) i) j
  have hterm1 : E21 * M * A12 = E21 * (W : Matrix (Fin r) (Fin s) ℝ) := by
    rw [Matrix.mul_assoc, hMA12]
  have hterm2 : A21 * M * E12 =
      Wt * E12 := by
    rw [hA21M]
  have hterm3 : A21 * (M * E11 * M) * A12 =
      Wt * E11 * W := by
    calc
      A21 * (M * E11 * M) * A12 = (A21 * M) * E11 * (M * A12) := by
        simp only [Matrix.mul_assoc]
      _ = Wt * E11 * W := by
        rw [hA21M, hMA12]
  have hexact := higham10_14_actual_schur_perturbation_exact
    fp A hPSD hrank hA11 hr1 hsuccess
  have hEqM : (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
      (L : Matrix (Fin s) (Fin s) ℝ) + R := by
    dsimp only at hexact
    rw [hterm1, hterm2, hterm3] at hexact
    calc
      (higham10_14_actualSchur fp A : Matrix (Fin s) (Fin s) ℝ) =
          (E22 - E21 * W - Wt * E12 + Wt * E11 * W) + R := by
        simpa [E, A12, A21, M, E11, E12, E21, E22, X, R] using hexact
      _ = (L : Matrix (Fin s) (Fin s) ℝ) + R := by
        congr 1
  have hEq : higham10_14_actualSchur fp A =
      fun i j => L i j + R i j := by
    ext i j
    exact congrFun (congrFun hEqM i) j
  have hSop : opNorm2Le (higham10_14_actualSchur fp A)
      (e * (w + 1) ^ 2 + C * e ^ 2) := by
    rw [hEq]
    exact opNorm2Le_add L R _ _ hLop hRop
  have hbound := complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
    (higham10_14_actualSchur fp A)
    (add_nonneg (mul_nonneg he0 (sq_nonneg (w + 1)))
      (mul_nonneg hC (sq_nonneg e))) hSop
  simpa [E, e, a, M, μ, W, Wt, w, C, C0] using hbound

/-- **Theorem 10.14, equation (10.22), literal family form.**

For a family of floating-point models whose unit roundoff tends to zero, this
theorem bounds the operator 2-norm of the matrix produced by the literal
truncated Cholesky executor.  The leading coefficient is exactly the one in
the book, and the remainder is the uniform family-level `O(u²)` predicate.
The hypotheses below are explicit small-roundoff radii on `gamma` and the
actual source error; none assumes a bound on the final residual or trailing
Schur block. -/
theorem higham10_14_equation_10_22_family_of_success
    {ι : Type*} {l : Filter ι} {r s : ℕ}
    (F : ι → FPModel) (U : RoundoffFamily ι l)
    (hunit : ∀ t, (F t).u = U.unit t)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hr0 : 0 < r)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hsuccess : ∀ t, ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot (F t) (r + s) A q)
    (hhalf : ∀ t, ((r + 1 : ℕ) : ℝ) * U.unit t ≤ 1 / 2)
    (hgammaRadius : ∀ t,
      (r : ℝ) * gamma (F t) (r + 1) ≤ 1 / 2)
    (hlinearAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2 ≤
        1 / 4)
    (hquadraticAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) * higham10_14_schurQuadraticCoeff A *
          complexMatrixOp2 (realRectToCMatrix
            (higham10_14_sourceError (F t) A r
              (Nat.le_add_right r s))) ≤ 1 / 4)
    (hEone : ∀ t, complexMatrixOp2 (realRectToCMatrix
      (higham10_14_sourceError (F t) A r (Nat.le_add_right r s))) ≤ 1)
    (hinvRadius : ∀ t,
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_sourceError (F t) A r
            (Nat.le_add_right r s))) ≤ 1 / 2) :
    FamilyFirstOrderLe l U.unit
      (fun t =>
        2 * (r : ℝ) * gamma (F t) (r + 1) *
          complexMatrixOp2 (realRectToCMatrix A) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2)
      (fun t => complexMatrixOp2 (realRectToCMatrix
        (higham10_14_actualResidual (F t) A))) := by
  let u : ι → ℝ := U.unit
  let g : ι → ℝ := fun t => gamma (F t) (r + 1)
  let E : ι → Fin (r + s) → Fin (r + s) → ℝ := fun t =>
    higham10_14_sourceError (F t) A r (Nat.le_add_right r s)
  let e : ι → ℝ := fun t => complexMatrixOp2 (realRectToCMatrix (E t))
  let q : ι → ℝ := fun t => complexMatrixOp2
    (realRectToCMatrix (higham10_14_actualSchur (F t) A))
  let d : ι → ℝ := fun t => complexMatrixOp2
    (realRectToCMatrix (higham10_14_actualResidual (F t) A))
  let a : ℝ := complexMatrixOp2 (realRectToCMatrix A)
  let W := higham10_14_W A
  let w : ℝ := complexMatrixOp2 (realRectToCMatrix W)
  let K : ℝ := (w + 1) ^ 2
  let C : ℝ := higham10_14_schurQuadraticCoeff A
  let CG : ℝ := 2 * ((r + 1 : ℕ) : ℝ)
  have ha0 : 0 ≤ a := complexMatrixOp2_nonneg _
  have hw0 : 0 ≤ w := complexMatrixOp2_nonneg _
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [sq_nonneg w]
  have hC : 0 ≤ C := by
    unfold C higham10_14_schurQuadraticCoeff
    dsimp only
    have ha' : 0 ≤ complexMatrixOp2 (realRectToCMatrix A) :=
      complexMatrixOp2_nonneg _
    have hμ' : 0 ≤ complexMatrixOp2 (realRectToCMatrix
        (nonsingInv r (higham10_14_block11 A))) :=
      complexMatrixOp2_nonneg _
    positivity
  have hCG : 0 ≤ CG := by dsimp [CG]; positivity
  have hr1 : ∀ t, gammaValid (F t) (r + 1) := by
    intro t
    unfold gammaValid
    rw [hunit t]
    linarith [hhalf t]
  have hg0 : ∀ t, 0 ≤ g t := fun t => gamma_nonneg (F t) (hr1 t)
  have hg : ∀ t, g t ≤ CG * u t := by
    intro t
    have ht := gamma_le_two_mul_n_u_of_nu_le_half (F t) (r + 1)
      (by simpa [hunit t] using hhalf t)
    dsimp [g, CG, u]
    rw [hunit t] at ht
    convert ht using 1 <;> ring
  have he0 : ∀ t, 0 ≤ e t := fun t => complexMatrixOp2_nonneg _
  have hq0 : ∀ t, 0 ≤ q t := fun t => complexMatrixOp2_nonneg _
  have hd0 : ∀ t, 0 ≤ d t := fun t => complexMatrixOp2_nonneg _
  have hSop : ∀ t,
      opNorm2Le (higham10_14_actualSchur (F t) A) (q t) := by
    intro t
    exact opNorm2Le_complexMatrixOp2_realRectToCMatrix _
  have hrows : ∀ t,
      rectOpNorm2Le (higham10_14_sourceTrailingRows (F t) A) (q t) := by
    intro t
    exact higham10_14_trailingRows_opNorm2Le_of_actualSchur
      (F t) A (hq0 t) (hSop t)
  have hrowsNorm : ∀ t,
      complexMatrixOp2
          (realRectToCMatrix (higham10_14_sourceTrailingRows (F t) A)) ≤
        q t := by
    intro t
    exact complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le _
      (hq0 t) (hrows t)
  have htrail : ∀ t,
      opNorm2Le
        (higham10_14_sourceTrailing (F t) A r (Nat.le_add_right r s))
        (q t) := by
    intro t
    exact higham10_14_sourceTrailing_opNorm2Le_of_rows (F t) A (hrows t)
  have he : ∀ t, e t ≤
      g t / (1 - (r : ℝ) * g t) *
        ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * q t) := by
    intro t
    have hrg : (r : ℝ) * g t < 1 :=
      lt_of_le_of_lt (by simpa [g] using hgammaRadius t) (by norm_num)
    have h25 := higham10_14_equation_10_25
      (F t) A hr0 (hr1 t) hrg hPSD.1 (hsuccess t)
    let rowsNorm := complexMatrixOp2
      (realRectToCMatrix (higham10_14_sourceTrailingRows (F t) A))
    have hden : 0 < 1 - (r : ℝ) * g t := by linarith
    have hα0 : 0 ≤ g t / (1 - (r : ℝ) * g t) :=
      div_nonneg (hg0 t) hden.le
    have hbase0 : 0 ≤ (r : ℝ) * a + ((r + s : ℕ) : ℝ) * rowsNorm := by
      exact add_nonneg
        (mul_nonneg (Nat.cast_nonneg r) ha0)
        (mul_nonneg (Nat.cast_nonneg (r + s)) (complexMatrixOp2_nonneg _))
    have heRaw : e t ≤
        g t / (1 - (r : ℝ) * g t) *
          ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * rowsNorm) := by
      exact complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le (E t)
        (mul_nonneg hα0 hbase0) (by simpa [E, e, g, a, rowsNorm] using h25)
    calc
      e t ≤ g t / (1 - (r : ℝ) * g t) *
          ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * rowsNorm) := heRaw
      _ ≤ g t / (1 - (r : ℝ) * g t) *
          ((r : ℝ) * a + ((r + s : ℕ) : ℝ) * q t) := by
        apply mul_le_mul_of_nonneg_left _ hα0
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_left
            (by simpa [rowsNorm] using hrowsNorm t)
            (Nat.cast_nonneg (r + s)))
  have hq : ∀ t, q t ≤ K * e t + C * e t ^ 2 := by
    intro t
    have ht := higham10_14_actualSchur_quadratic_bound
      (F t) A hPSD hrank hA11 (hr1 t) (hsuccess t)
      (by simpa [E, e] using hEone t)
      (by simpa [E, e] using hinvRadius t)
    change q t ≤ e t * K + C * e t ^ 2 at ht
    nlinarith
  have hd : ∀ t, d t ≤ e t + q t := by
    intro t
    have hEop : opNorm2Le (E t) (e t) :=
      opNorm2Le_complexMatrixOp2_realRectToCMatrix _
    have hErect : rectOpNorm2Le (E t) (e t) := by
      intro v
      simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hEop v
    have hnegRect := higham10_14_rectOpNorm2Le_neg (E t) hErect
    have hneg : opNorm2Le (fun i j => -(E t i j)) (e t) := by
      intro v
      simpa [rectOpNorm2Le, opNorm2Le, rectMatMulVec, matMulVec] using hnegRect v
    have hadd := opNorm2Le_add
      (higham10_14_sourceTrailing (F t) A r (Nat.le_add_right r s))
      (fun i j => -(E t i j)) (q t) (e t) (htrail t) hneg
    have h23 := higham10_14_equation_10_23
      (F t) A r (Nat.le_add_right r s)
    have hres : higham10_14_actualResidual (F t) A = fun i j =>
        higham10_14_sourceTrailing (F t) A r (Nat.le_add_right r s) i j -
          E t i j := by
      ext i j
      have hij := h23 i j
      unfold higham10_14_actualResidual
      dsimp [E]
      linarith
    have hresOp : opNorm2Le (higham10_14_actualResidual (F t) A)
        (q t + e t) := by
      rw [hres]
      simpa [sub_eq_add_neg] using hadd
    have hnorm := complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le
      (higham10_14_actualResidual (F t) A)
      (add_nonneg (hq0 t) (he0 t)) hresOp
    dsimp [d]
    linarith
  apply higham10_14_scalar_absorption_family_of_error_sq
    r (r + s) u g e q d a K C CG ha0 hK hC hCG
    U.unit_nonneg U.unit_le_one hg0 he0 hq0 hd0 hg
  · intro t
    simpa [g] using hgammaRadius t
  · intro t
    simpa [g, K, W, w] using hlinearAbsorb t
  · intro t
    simpa [g, C, E, e] using hquadraticAbsorb t
  · exact he
  · exact hq
  · exact hd

/-- Source-facing form of (10.22): display (10.21) is used to derive the
positive pivots of the literal rounded executor, after which
`higham10_14_equation_10_22_family_of_success` supplies the matrix 2-norm
bound and uniform quadratic remainder. -/
theorem higham10_14_equation_10_22_family
    {ι : Type*} {l : Filter ι} {r s : ℕ}
    (F : ι → FPModel) (U : RoundoffFamily ι l)
    (hunit : ∀ t, (F t).u = U.unit t)
    (A : Fin (r + s) → Fin (r + s) → ℝ)
    (hr0 : 0 < r)
    (hPSD : IsPosSemiDef (r + s) A)
    (hrank : (Matrix.of A).rank = r)
    (hA11 : IsSymPosDef r (higham10_14_block11 A))
    (hH11sym : IsSymmetricFiniteMatrix (fun i j : Fin r =>
      A (Fin.castAdd s i) (Fin.castAdd s j) /
        (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
         Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))))
    (h1021 : ∀ t, (r : ℝ) *
        (gamma (F t) (r + 1) / (1 - gamma (F t) (r + 1))) <
      finiteMinEigenvalue hr0 (fun i j : Fin r =>
        A (Fin.castAdd s i) (Fin.castAdd s j) /
          (Real.sqrt (A (Fin.castAdd s i) (Fin.castAdd s i)) *
           Real.sqrt (A (Fin.castAdd s j) (Fin.castAdd s j)))) hH11sym)
    (hhalf : ∀ t, ((r + 1 : ℕ) : ℝ) * U.unit t ≤ 1 / 2)
    (hgammaRadius : ∀ t,
      (r : ℝ) * gamma (F t) (r + 1) ≤ 1 / 2)
    (hlinearAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2 ≤
        1 / 4)
    (hquadraticAbsorb : ∀ t,
      (gamma (F t) (r + 1) /
          (1 - (r : ℝ) * gamma (F t) (r + 1))) *
        ((r + s : ℕ) : ℝ) * higham10_14_schurQuadraticCoeff A *
          complexMatrixOp2 (realRectToCMatrix
            (higham10_14_sourceError (F t) A r
              (Nat.le_add_right r s))) ≤ 1 / 4)
    (hEone : ∀ t, complexMatrixOp2 (realRectToCMatrix
      (higham10_14_sourceError (F t) A r (Nat.le_add_right r s))) ≤ 1)
    (hinvRadius : ∀ t,
      complexMatrixOp2 (realRectToCMatrix
          (nonsingInv r (higham10_14_block11 A))) *
        complexMatrixOp2 (realRectToCMatrix
          (higham10_14_sourceError (F t) A r
            (Nat.le_add_right r s))) ≤ 1 / 2) :
    FamilyFirstOrderLe l U.unit
      (fun t =>
        2 * (r : ℝ) * gamma (F t) (r + 1) *
          complexMatrixOp2 (realRectToCMatrix A) *
          (complexMatrixOp2 (realRectToCMatrix (higham10_14_W A)) + 1) ^ 2)
      (fun t => complexMatrixOp2 (realRectToCMatrix
        (higham10_14_actualResidual (F t) A))) := by
  have hr1 : ∀ t, gammaValid (F t) (r + 1) := by
    intro t
    unfold gammaValid
    rw [hunit t]
    linarith [hhalf t]
  have hγlt : ∀ t, gamma (F t) (r + 1) < 1 := by
    intro t
    have hg0 := gamma_nonneg (F t) (hr1 t)
    have hrOne : (1 : ℝ) ≤ r := by exact_mod_cast hr0
    have hle : gamma (F t) (r + 1) ≤
        (r : ℝ) * gamma (F t) (r + 1) :=
      le_mul_of_one_le_left hg0 hrOne
    linarith [hgammaRadius t]
  have hsuccess : ∀ t, ∀ q : Fin (r + s), q.val < r →
      0 < fl_cholPivot (F t) (r + s) A q := by
    intro t
    have hs := higham10_14_fl_cholesky_success_source
      (F t) A r hr0 (Nat.le_add_right r s)
      (by simpa [higham10_14_block11, Fin.castAdd] using hA11)
      (hr1 t) (hγlt t)
      (by simpa [Fin.castAdd] using hH11sym)
      (by simpa [Fin.castAdd] using h1021 t)
    exact hs
  exact higham10_14_equation_10_22_family_of_success
    F U hunit A hr0 hPSD hrank hA11 hsuccess hhalf hgammaRadius
    hlinearAbsorb hquadraticAbsorb hEone hinvRadius

end NumStability
