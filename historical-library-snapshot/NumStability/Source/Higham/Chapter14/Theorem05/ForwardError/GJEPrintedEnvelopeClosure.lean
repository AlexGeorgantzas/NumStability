import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
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
import NumStability.Source.Higham.Chapter14.Algorithm04.Accumulation.GaussJordanAccumulation
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies

/-!
# Chapter14 Theorem05 ForwardError GJEPrintedEnvelopeClosure

Canonical destination for material split out of
`NumStability.Algorithms.Ch14GJEPrintedEnvelopeClosure` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- Structural data behind Higham's replacement of the exact GJE envelope
`|Q| Pabs` by the printed first-order envelope `|Uhat| |Uhat^-1|`.

The two proximity fields concern the factors separately.  They neither assume
the printed product envelope nor any final error inequality. -/
structure Ch14GJEPrintedEnvelopeFamily (ι : Type*) (l : Filter ι) (n : ℕ) where
  model : ι → FPModel
  U_hat : ι → Fin n → Fin n → ℝ
  Q : ι → Fin n → Fin n → ℝ
  Pabs : ι → Fin n → Fin n → ℝ
  U_inv : ι → Fin n → Fin n → ℝ
  Q_error : ι → Fin n → Fin n → ℝ
  P_error : ι → Fin n → Fin n → ℝ
  unit_tendsto_zero : Tendsto (fun t => (model t).u) l (𝓝 0)
  dimension_pos : 1 ≤ n
  valid_three : ∀ t, gammaValid (model t) 3
  inverse_certificate : ∀ t, IsRightInverse n (U_hat t) (U_inv t)
  Pabs_nonneg : ∀ t i j, 0 ≤ Pabs t i j
  Q_error_nonneg : ∀ t i j, 0 ≤ Q_error t i j
  P_error_nonneg : ∀ t i j, 0 ≤ P_error t i j
  Q_proximity : ∀ t i j,
    |Q t i j - U_hat t i j| ≤ gje_c₃ (model t) n * Q_error t i j
  P_upper : ∀ t i j,
    Pabs t i j ≤ |U_inv t i j| + gje_c₃ (model t) n * P_error t i j
  U_hat_isBigO_one : MatrixFamilyIsBigOOne l U_hat
  U_inv_isBigO_one : MatrixFamilyIsBigOOne l U_inv
  Q_error_isBigO_one : MatrixFamilyIsBigOOne l Q_error
  P_error_isBigO_one : MatrixFamilyIsBigOOne l P_error
  exact_envelope_isBigO_one : MatrixFamilyIsBigOOne l
    (fun t => matMul n (absMatrix n (Q t)) (Pabs t))

/-- The exact, pre-replacement envelope `|Q| Pabs`.  `Q` and `Pabs` remain
separate data throughout the closure. -/
noncomputable def ch14ext_gjeExactQPEnvelope
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) :
    Fin n → Fin n → ℝ :=
  matMul n (absMatrix n (F.Q t)) (F.Pabs t)

/-- Higham's printed first-order middle factor `|Uhat| |Uhat^-1|`. -/
noncomputable def ch14ext_gjePrintedUinvEnvelope
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) :
    Fin n → Fin n → ℝ :=
  matMul n (absMatrix n (F.U_hat t)) (absMatrix n (F.U_inv t))

/-- The coefficient of `c3` in the product replacement
`|Q| Pabs ≤ |Uhat| |Uhat^-1| + c3*C`.  The last summand retains the product of
the two first-order factor errors. -/
noncomputable def ch14ext_gjePrintedEnvelopeCorrection
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) :
    Fin n → Fin n → ℝ :=
  fun i j =>
      matMul n (F.Q_error t) (absMatrix n (F.U_inv t)) i j +
      matMul n (absMatrix n (F.U_hat t)) (F.P_error t) i j +
      gje_c₃ (F.model t) n * matMul n (F.Q_error t) (F.P_error t) i j

theorem ch14ext_gjePrintedEnvelopeCorrection_nonneg
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    0 ≤ ch14ext_gjePrintedEnvelopeCorrection F t i j := by
  have h₁ : 0 ≤ matMul n (F.Q_error t) (absMatrix n (F.U_inv t)) i j := by
    unfold matMul absMatrix
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (F.Q_error_nonneg t i k) (abs_nonneg _)
  have h₂ : 0 ≤ matMul n (absMatrix n (F.U_hat t)) (F.P_error t) i j := by
    unfold matMul absMatrix
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (abs_nonneg _) (F.P_error_nonneg t k j)
  have h₃ : 0 ≤ matMul n (F.Q_error t) (F.P_error t) i j := by
    unfold matMul
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (F.Q_error_nonneg t i k) (F.P_error_nonneg t k j)
  unfold ch14ext_gjePrintedEnvelopeCorrection
  exact add_nonneg (add_nonneg h₁ h₂)
    (mul_nonneg (gje_c3_nonneg (F.model t) n F.dimension_pos (F.valid_three t)) h₃)

theorem ch14ext_gjeExactQPEnvelope_nonneg
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    0 ≤ ch14ext_gjeExactQPEnvelope F t i j := by
  unfold ch14ext_gjeExactQPEnvelope matMul absMatrix
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg _) (F.Pabs_nonneg t k j)

theorem ch14ext_gjePrintedUinvEnvelope_nonneg
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) :
    0 ≤ ch14ext_gjePrintedUinvEnvelope F t i j := by
  unfold ch14ext_gjePrintedUinvEnvelope matMul absMatrix
  positivity

/-- For the actual constructed left inverse, the accumulated matrix error
proves `Q = Uhat + O(c3)` componentwise.  The proximity is derived here from
the rounded recurrence, final `D = I` normalization, and the proved identity
`Q * signedCumProd = I`. -/
theorem ch14ext_gjeConcrete_constructedQ_sub_U_bound
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start) (t : ι) (i j : Fin n) :
    |ch14ext_gjeConstructedQ n (R.V t) start i j - R.V t start i j| ≤
      gje_c₃ (R.model t) n *
        matMul n (ch14ext_gjeConcreteFamilyXabs R t)
          (absMatrix n (R.V t start)) i j := by
  let N := ch14ext_gjeSeqStages n (R.V t)
  let Q := ch14ext_gjeConstructedQ n (R.V t) start
  let P := gje_cumulative_product n N start (start + (n - 1))
  let E : Fin n → Fin n → ℝ := fun a k =>
    R.V t (start + (n - 1)) a k - matMul n P (R.V t start) a k
  have hE : ∀ a k : Fin n, |E a k| ≤
      gje_c₃ (R.model t) n *
        ch14ext_boundObj n N (R.V t start) start (n - 1) a k := by
    intro a k
    simpa [E, P, N] using
      ch14ext_gjeConcrete_matrixAccumulation (R.model t) n (R.V t) start
        R.dimension_pos (R.valid_three t) R.index_valid
        (R.matrix_recurrence t) (R.pivots_nonzero t) a k
  have hQP : matMul n Q P = idMatrix n := by
    simpa [Q, P, N] using
      ch14ext_gjeConstructedQ_isLeftInverse n (R.V t) start R.index_valid
  have hfinalQ : matMul n Q (R.V t (start + (n - 1))) = Q := by
    rw [R.final_matrix t, matMul_id_right]
  have hproductQ : matMul n Q (matMul n P (R.V t start)) = R.V t start := by
    rw [← matMul_assoc, hQP, matMul_id_left]
  have hkey : matMul n Q E = fun a k => Q a k - R.V t start a k := by
    funext a k
    have hexpand : matMul n Q E a k =
        matMul n Q (R.V t (start + (n - 1))) a k -
          matMul n Q (matMul n P (R.V t start)) a k := by
      show (∑ q : Fin n, Q a q * E q k) =
        (∑ q : Fin n, Q a q * R.V t (start + (n - 1)) q k) -
          ∑ q : Fin n, Q a q * matMul n P (R.V t start) q k
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun q _ => by
        show Q a q *
          (R.V t (start + (n - 1)) q k - matMul n P (R.V t start) q k) = _
        ring)
    rw [hexpand, hfinalQ, hproductQ]
  have hbound := ch14ext_matMul_abs_bound n Q E
    (ch14ext_boundObj n N (R.V t start) start (n - 1))
    (gje_c₃ (R.model t) n) hE i j
  have hreassoc :
      matMul n (absMatrix n Q)
          (ch14ext_boundObj n N (R.V t start) start (n - 1)) =
        matMul n (ch14ext_gjeConcreteFamilyXabs R t)
          (absMatrix n (R.V t start)) := by
    show matMul n (absMatrix n Q)
        (matMul n (ch14ext_absCumProd n N start (n - 1))
          (absMatrix n (R.V t start))) = _
    rw [← matMul_assoc]
    rfl
  rw [hreassoc, hkey] at hbound
  simpa [Q] using hbound

/-- For the actual absolute cumulative product, upper triangularity identifies
it with the absolute signed product.  The accumulated residual and a genuine
right inverse of `Uhat` then prove Higham's one-sided inverse comparison. -/
theorem ch14ext_gjeConcrete_Pabs_le_abs_Uinv_add
    {ι : Type*} {l : Filter ι} {n : ℕ}
    {A : Fin n → Fin n → ℝ} {b : Fin n → ℝ} {start : ℕ}
    (R : Ch14GJEConcreteFamily ι l n A b start)
    (U_inv : ι → Fin n → Fin n → ℝ)
    (hUinv : ∀ t, IsRightInverse n (R.V t start) (U_inv t))
    (t : ι) (i j : Fin n) :
    ch14ext_gjeConcreteFamilyPabs R t i j ≤ |U_inv t i j| +
      gje_c₃ (R.model t) n *
        matMul n
          (matMul n (ch14ext_gjeConcreteFamilyPabs R t)
            (absMatrix n (R.V t start)))
          (absMatrix n (U_inv t)) i j := by
  let X := ch14ext_gjeConcreteFamilyPabs R t
  let S := gje_cumulative_product n (ch14ext_gjeSeqStages n (R.V t))
    start (start + (n - 1))
  have hUpper : ∀ q : ℕ, q ≤ n - 1 →
      ∀ a k : Fin n, k.val < a.val → R.V t (start + q) a k = 0 :=
    ch14ext_gjeSeq_upper_triangular (R.model t) n (R.V t) start
      R.index_valid (R.lu_certificate t).U_lower_zero
      (R.matrix_recurrence t) (R.pivots_nonzero t)
  have hX : ∀ a k : Fin n, X a k = |S a k| := by
    intro a k
    simpa [X, S, ch14ext_gjeConcreteFamilyPabs] using
      ch14ext_gje_absCumProd_eq_abs_signed n (R.V t) start (n - 1)
        R.index_valid hUpper a k
  have hAccum := ch14ext_gjeConcrete_matrixAccumulation (R.model t) n
    (R.V t) start R.dimension_pos (R.valid_three t) R.index_valid
    (R.matrix_recurrence t) (R.pivots_nonzero t)
  have hResidual : ∀ a k : Fin n,
      |idMatrix n a k - matMul n S (R.V t start) a k| ≤
        gje_c₃ (R.model t) n *
          matMul n X (absMatrix n (R.V t start)) a k := by
    intro a k
    have h := hAccum a k
    rw [R.final_matrix t] at h
    simpa [S, X, ch14ext_gjeConcreteFamilyPabs, ch14ext_boundObj] using h
  simpa [X] using
    ch14ext_abs_signed_le_abs_rightInverse_add n S X (R.V t start)
      (U_inv t) (gje_c₃ (R.model t) n) hX (hUinv t) hResidual i j

/-- The explicit correction left after replacing `|Q| Pabs` in (14.30b).
Its coefficient is `c3^2`; the matrix factor contains no hidden asymptotic
notation. -/
noncomputable def ch14ext_gje1430bPrintedRemainder
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n) (t : ι) (i j : Fin n) : ℝ :=
  gje_c₃ (F.model t) n * gje_c₃ (F.model t) n *
    matMul n (ch14ext_gjePrintedEnvelopeCorrection F t)
      (absMatrix n (F.U_hat t)) i j

/-- The explicit correction left after replacing `|Q| Pabs` in (14.30c). -/
noncomputable def ch14ext_gje1430cPrintedRemainder
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (y : ι → Fin n → ℝ) (t : ι) (i : Fin n) : ℝ :=
  gje_c₃ (F.model t) n * gje_c₃ (F.model t) n *
    matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t) (absVec n (y t)) i

/-- The literal first-order object printed in (14.31):
`|Lhat| |Uhat| |Uhat^-1| |Uhat| |xhat|`. -/
noncomputable def ch14ext_gje1431PrintedLeading
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n (L t))
    (matMulVec n (absMatrix n (F.U_hat t))
      (matMulVec n (absMatrix n (F.U_inv t))
        (matMulVec n (absMatrix n (F.U_hat t))
          (absVec n (x_hat t))))) i

/-- The bounded action multiplying the extra `c3` generated by replacing
`|Q| Pabs` with `|Uhat| |Uhat^-1|` in (14.31). -/
noncomputable def ch14ext_gje1431EnvelopeCorrectionAction
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) : ℝ :=
  matMulVec n (absMatrix n (L t))
    (matMulVec n (ch14ext_gjePrintedEnvelopeCorrection F t)
      (matMulVec n (absMatrix n (F.U_hat t))
        (absVec n (x_hat t)))) i

/-- The complete explicit remainder in the printed (14.31) endpoint.  Its
first summand is the concrete accumulation theorem's higher-order term; its
second summand records exactly the envelope replacement. -/
noncomputable def ch14ext_gje1431PrintedRemainder
    {ι : Type*} {l : Filter ι} {n : ℕ}
    (F : Ch14GJEPrintedEnvelopeFamily ι l n)
    (L : ι → Fin n → Fin n → ℝ) (y x_hat : ι → Fin n → ℝ)
    (t : ι) (i : Fin n) : ℝ :=
  ch14ext_gjeResidualHigherOrder n (F.model t) (L t)
      (ch14ext_gjeExactQPEnvelope F t) (F.U_hat t) (y t) (x_hat t) i +
    8 * (n : ℝ) * (F.model t).u * gje_c₃ (F.model t) n *
      ch14ext_gje1431EnvelopeCorrectionAction F L x_hat t i

end Ch14Ext
end NumStability
