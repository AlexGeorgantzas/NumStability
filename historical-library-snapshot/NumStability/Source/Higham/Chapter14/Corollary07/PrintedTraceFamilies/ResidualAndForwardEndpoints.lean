import NumStability.Algorithms.LinearSystems.GaussJordan.ErrorAnalysis.GaussJordan
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.FirstOrder.MatrixFamilies.AsymptoticFamilies
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter14.Algorithm04.Pivoting.GaussJordanPivoting
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.SourceClosure
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily
import NumStability.Source.Higham.Chapter14.Corollary07.WeakDominanceFamilies.ResidualAndForwardBounds
import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies

/-!
# ResidualAndForwardEndpoints

Canonical destination for the Chapter14.Corollary07 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Corollary147SourceClosure` during wave R08.
Holds 18 declaration(s): 18 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

theorem ch14ext_cor147Source_residual_14_31_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b) :
    (forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        8 * (n : Real) * (F.model t).u *
          ch14ext_gjeResidualS2 n (F.L_hat t)
            (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
            (F.x_hat t) i +
        ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
          (F.initial t).rhs (F.x_hat t) i) ∧
      forall i,
        (fun t => ch14ext_gjeResidualHigherOrder n (F.model t) (F.L_hat t)
          (ch14ext_cor147SourceXabs F t) (F.initial t).matrix
          (F.initial t).rhs (F.x_hat t) i) =O[l]
            (fun t => (F.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Source_overall_residual_14_31 F
  · intro i
    exact ch14ext_gjeResidualHigherOrder_family_isBigO n F.model F.L_hat
      (ch14ext_cor147SourceXabs F) (fun t => (F.initial t).matrix)
      (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
      F.L_hat_isBigO_one (by simpa [ch14ext_cor147SourceXabs,
        ch14ext_cor147SourceQ, ch14ext_cor147SourceV] using F.X_abs_isBigO_one)
      F.U_hat_isBigO_one F.y_isBigO_one F.x_hat_isBigO_one i

theorem ch14ext_cor147Source_forward_14_32_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hAinv : IsLeftInverse n A A_inv)
    (hExact : forall i : Fin n, matMulVec n A x i = b i) :
    (forall t i,
      |x i - F.x_hat t i| <=
        2 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
        6 * (n : Real) * (F.model t).u *
          ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i +
        ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
          (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i) ∧
      forall i,
        (fun t => ch14ext_gjeForwardLiteralHigherOrder n (F.model t) A_inv
          (F.L_hat t) (F.initial t).matrix (ch14ext_cor147SourcePabs F t)
          (F.U_hat_inv t) (F.z t) (F.initial t).rhs (F.x_hat t) i) =O[l]
            (fun t => (F.model t).u ^ 2) := by
  constructor
  · intro t
    exact ch14ext_cor147Source_overall_forward_14_32 F t A_inv x hAinv hExact
  · intro i
    exact ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n F.model
      (fun _ => A_inv) F.L_hat (fun t => (F.initial t).matrix)
      (ch14ext_cor147SourcePabs F) F.U_hat_inv F.z
      (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
      (ch14ext_fixedMatrix_family_isBigOOne l A_inv) F.L_hat_isBigO_one
      F.U_hat_isBigO_one (by simpa [ch14ext_cor147SourcePabs,
        ch14ext_cor147SourceV] using F.P_abs_isBigO_one)
      F.U_hat_inv_isBigO_one F.z_isBigO_one F.y_isBigO_one
      F.x_hat_isBigO_one i

/-- The componentwise LU backward residual is `O(u)` when the computed
factors are locally bounded. -/
theorem ch14ext_luBackward_productResidual_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    (fp : ι -> FPModel) (A : Fin n -> Fin n -> Real)
    (L_hat U_hat : ι -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hLU : forall t,
      LUBackwardError n A (L_hat t) (U_hat t) (gamma (fp t) n))
    (hvalid : forall t, gammaValid (fp t) n)
    (hLone : MatrixFamilyIsBigOOne l L_hat)
    (hUone : MatrixFamilyIsBigOOne l U_hat) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => matMul n (L_hat t) (U_hat t) i j - A i j)
      (fun t => (fp t).u) := by
  intro i j
  let W : ι -> Real := fun t =>
    ∑ k : Fin n, |L_hat t i k| * |U_hat t k j|
  have hW : W =O[l] (fun _ : ι => (1 : Real)) := by
    dsimp [W]
    simpa only [one_mul, Real.norm_eq_abs] using
      (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
        (hLone i k).norm_left.mul (hUone k j).norm_left))
  have hdom :
      (fun t => matMul n (L_hat t) (U_hat t) i j - A i j) =O[l]
        (fun t => gamma (fp t) n * W t) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [] with t
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (gamma_nonneg (fp t) (hvalid t))
        (Finset.sum_nonneg (fun k _ =>
          mul_nonneg (abs_nonneg _) (abs_nonneg _))))]
    simpa [W, matMul] using (hLU t).backward_bound i j
  have hgamma := ch14ext_gamma_family_isBigO_unit n fp hu
  exact hdom.trans (by
    simpa only [mul_one] using hgamma.mul hW)

/-- Fixed-dimensional Doolittle induction turns the operational LU backward
certificate into first-order proximity to the exact no-pivot factors.  The
only divisions are by the exact pivots, whose nonvanishing is explicit. -/
theorem ch14ext_luBackward_factorProximity_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    (fp : ι -> FPModel) (A L U : Fin n -> Fin n -> Real)
    (L_hat U_hat : ι -> Fin n -> Fin n -> Real)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (hComputed : forall t,
      LUBackwardError n A (L_hat t) (U_hat t) (gamma (fp t) n))
    (hvalid : forall t, gammaValid (fp t) n)
    (hLone : MatrixFamilyIsBigOOne l L_hat)
    (hUone : MatrixFamilyIsBigOOne l U_hat)
    (hExact : LUFactSpec n A L U)
    (hpiv : forall k : Fin n, U k k ≠ 0) :
    Ch14MatrixFamilyIsBigO l
        (fun t i j => L_hat t i j - L i j) (fun t => (fp t).u) ∧
      Ch14MatrixFamilyIsBigO l
        (fun t i j => U_hat t i j - U i j) (fun t => (fp t).u) := by
  let unit : ι -> Real := fun t => (fp t).u
  have hres := ch14ext_luBackward_productResidual_isBigO fp A L_hat U_hat
    hu hComputed hvalid hLone hUone
  have hstage : forall m : Nat, m <= n ->
      (forall k : Fin n, k.val < m -> forall j : Fin n,
        (fun t => U_hat t k j - U k j) =O[l] unit) ∧
      (forall k : Fin n, k.val < m -> forall i : Fin n,
        (fun t => L_hat t i k - L i k) =O[l] unit) := by
    intro m
    induction m with
    | zero =>
        intro _
        constructor <;> intro k hk
        · exact (Nat.not_lt_zero k.val hk).elim
        · exact (Nat.not_lt_zero k.val hk).elim
    | succ m ih =>
        intro hm
        have hprev := ih (by omega)
        have hUcurrent : forall k : Fin n, k.val < m + 1 -> forall j : Fin n,
            (fun t => U_hat t k j - U k j) =O[l] unit := by
          intro k hk j
          by_cases hkm : k.val < m
          · exact hprev.1 k hkm j
          · have hk_eq : k.val = m := by omega
            by_cases hkj : k.val <= j.val
            · have hprefix := ch14ext_luPrefix_difference_isBigO L U L_hat U_hat
                unit k j k
                (fun s hs => hprev.2 s (by omega) k)
                (fun s hs => hprev.1 s (by omega) j) hUone
              have h := (hres k j).sub hprefix
              convert h using 1
              funext t
              have hhat := ch14ext_matMul_eq_prefix_add_upper
                (L_hat t) (U_hat t) (hComputed t).L_diag
                (hComputed t).L_upper_zero k j hkj
              have hexact := ch14ext_matMul_eq_prefix_add_upper L U
                hExact.L_diag hExact.L_upper_zero k j hkj
              have hA : matMul n L U k j = A k j := by
                simpa [matMul] using hExact.product_eq k j
              change U_hat t k j - U k j =
                (matMul n (L_hat t) (U_hat t) k j - A k j) -
                  (higham9_2_rectPrefixDot (L_hat t) (U_hat t) k j k -
                    higham9_2_rectPrefixDot L U k j k)
              rw [hhat, ← hA, hexact]
              ring
            · have hjk : j.val < k.val := by omega
              have heq : (fun t => U_hat t k j - U k j) =
                  (fun _ : ι => (0 : Real)) := by
                funext t
                rw [(hComputed t).U_lower_zero k j hjk,
                  hExact.U_lower_zero k j hjk]
                ring
              rw [heq]
              exact Asymptotics.isBigO_zero _ _
        have hLcurrent : forall k : Fin n, k.val < m + 1 -> forall i : Fin n,
            (fun t => L_hat t i k - L i k) =O[l] unit := by
          intro k hk i
          by_cases hkm : k.val < m
          · exact hprev.2 k hkm i
          · have hk_eq : k.val = m := by omega
            have hprefix := ch14ext_luPrefix_difference_isBigO L U L_hat U_hat
              unit i k k
              (fun s hs => hprev.2 s (by omega) i)
              (fun s hs => hprev.1 s (by omega) k) hUone
            have hUkk := hUcurrent k hk k
            have hterm :
                (fun t => L_hat t i k * (U_hat t k k - U k k)) =O[l] unit := by
              simpa only [one_mul] using (hLone i k).mul hUkk
            have hnum := ((hres i k).sub hprefix).sub hterm
            have hscaled := hnum.const_mul_left (U k k)⁻¹
            convert hscaled using 1
            funext t
            have hhat := ch14ext_matMul_eq_prefix_add_lower
              (L_hat t) (U_hat t) (hComputed t).U_lower_zero i k
            have hexact := ch14ext_matMul_eq_prefix_add_lower L U
              hExact.U_lower_zero i k
            have hA : matMul n L U i k = A i k := by
              simpa [matMul] using hExact.product_eq i k
            change L_hat t i k - L i k = (U k k)⁻¹ *
              ((matMul n (L_hat t) (U_hat t) i k - A i k) -
                (higham9_2_rectPrefixDot (L_hat t) (U_hat t) i k k -
                  higham9_2_rectPrefixDot L U i k k) -
                L_hat t i k * (U_hat t k k - U k k))
            rw [hhat, ← hA, hexact]
            field_simp [hpiv k]
            ring
        exact ⟨hUcurrent, hLcurrent⟩
  have hall := hstage n (Nat.le_refl n)
  constructor
  · intro i j
    exact hall.2 j j.isLt i
  · intro i j
    exact hall.1 i i.isLt j

/-- Specialization of the operational factor-proximity theorem to the source
family. -/
theorem ch14ext_cor147Source_factorProximity_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    Ch14MatrixFamilyIsBigO l
        (fun t i j => F.L_hat t i j - L i j) (fun t => (F.model t).u) ∧
      Ch14MatrixFamilyIsBigO l
        (fun t i j => (F.initial t).matrix i j - U i j)
          (fun t => (F.model t).u) := by
  apply ch14ext_luBackward_factorProximity_isBigO F.model A L U F.L_hat
    (fun t => (F.initial t).matrix) F.unit_tendsto_zero F.lu_certificate
    F.valid_n F.L_hat_isBigO_one F.U_hat_isBigO_one hLU
  exact (hLU.det_ne_zero_iff_U_diag_ne_zero.mp hdet)

/-- The computed printed inverse product is `O(u)` close to its exact
counterpart, with both factor and inverse proximity already derived. -/
theorem ch14ext_cor147Source_printedX_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => ch14ext_cor147SourcePrintedX F t i j -
        ch14ext_cor147WeakExactX n U U_inv i j)
      (fun t => (F.model t).u) := by
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hInv := ch14ext_cor147Source_inverseProximity_isBigO F U U_inv
    hprox.2 hUinv
  have hUabs := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hInvabs := ch14ext_matrixFamily_absDifference_isBigO U_inv hInv
  have h := ch14ext_matrixFamily_productDifference_isBigO
    (M := fun t i j => |(F.initial t).matrix i j|)
    (N := fun t i j => |F.U_hat_inv t i j|)
    (absMatrix n U) (absMatrix n U_inv)
    (by simpa only [absMatrix] using hUabs)
    (by simpa only [absMatrix] using hInvabs)
    (matrixFamily_abs_isBigOOne F.U_hat_inv_isBigO_one)
  simpa only [ch14ext_cor147SourcePrintedX, ch14ext_cor147WeakExactX,
    absMatrix] using h

/-- The residual object formed with the computed printed inverse product is
`O(u)` close to the exact row-dominant object. -/
theorem ch14ext_cor147Source_printedResidualLeading_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeResidualS2 n (F.L_hat t) (ch14ext_cor147SourcePrintedX F t)
            (F.initial t).matrix (F.x_hat t) i -
          ch14ext_gjeResidualS2 n L (ch14ext_cor147WeakExactX n U U_inv)
            U (F.x_hat t) i)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hPXdiff := ch14ext_cor147Source_printedX_difference_isBigO
    F L U U_inv hLU hdet hUinv
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.initial t).matrix a j|)
            (fun j => |F.x_hat t j|) i -
          matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.initial t).matrix i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hPXOne : MatrixFamilyIsBigOOne l
      (ch14ext_cor147SourcePrintedX F) :=
    ch14ext_matrixFamily_mul_family_isBigOOne
      (matrixFamily_abs_isBigOOne F.U_hat_isBigO_one)
      (matrixFamily_abs_isBigOOne F.U_hat_inv_isBigO_one)
  have hPXabsDiff := ch14ext_matrixFamily_absDifference_isBigO
    (ch14ext_cor147WeakExactX n U U_inv) hPXdiff
  have hPXactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n
        (fun i j => |ch14ext_cor147SourcePrintedX F t i j|)
        (matMulVec n (fun i j => |(F.initial t).matrix i j|)
          (fun i => |F.x_hat t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne
      (matrixFamily_abs_isBigOOne hPXOne) hUactionOne
  have hPXactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |ch14ext_cor147SourcePrintedX F t a j|)
            (matMulVec n (fun a j => |(F.initial t).matrix a j|)
              (fun j => |F.x_hat t j|)) i -
          matMulVec n (absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
            (matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |ch14ext_cor147SourcePrintedX F t i j|)
      (A := absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
      (x := fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|))
      (y := fun t => matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|))
      (by simpa only [absMatrix] using hPXabsDiff) hUactionDiff hUactionOne
  have hLabsDiff := ch14ext_matrixFamily_absDifference_isBigO L hprox.1
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.L_hat t i j|) (A := absMatrix n L)
    (x := fun t => matMulVec n
      (fun i j => |ch14ext_cor147SourcePrintedX F t i j|)
      (matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)))
    (y := fun t => matMulVec n
      (absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
      (matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|)))
    (by simpa only [absMatrix] using hLabsDiff) hPXactionDiff hPXactionOne
  simpa only [ch14ext_gjeResidualS2, absMatrix, absVec] using hfinal

theorem ch14ext_cor147SourceResidualLeadingCorrection_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) (i : Fin n) :
    (fun t => ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i)
      =O[l] (fun t => (F.model t).u) := by
  have hdiff := (ch14ext_cor147Source_printedResidualLeading_difference_isBigO
    F L U U_inv hLU hdet hUinv i).norm_left
  have hc3 := ch14ext_gje_c3_family_isBigO_unit n F.model F.unit_tendsto_zero
  have henv := ch14ext_cor147SourceResidualEnvelopeCorrection_isBigOOne F i
  have hcorr : (fun t => gje_c₃ (F.model t) n *
      ch14ext_cor147SourceResidualEnvelopeCorrection F t i) =O[l]
        (fun t => (F.model t).u) := by
    simpa only [mul_one] using hc3.mul henv
  simpa only [ch14ext_cor147SourceResidualLeadingCorrection,
    Real.norm_eq_abs] using hdiff.add hcorr

theorem ch14ext_cor147SourceResidualRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) (i : Fin n) :
    (fun t => ch14ext_cor147SourceResidualRemainder F L U U_inv t i)
      =O[l] (fun t => (F.model t).u ^ 2) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hlead := ch14ext_cor147SourceResidualLeadingCorrection_isBigO
    F L U U_inv hLU hdet hUinv i
  have hscaled :
      (fun t => 8 * (n : Real) * unit t *
        ch14ext_cor147SourceResidualLeadingCorrection F L U U_inv t i)
        =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu.mul hlead).const_mul_left (8 * (n : Real))
  have hhigher := ch14ext_gjeResidualHigherOrder_family_isBigO n F.model
    F.L_hat (ch14ext_cor147SourceXabs F) (fun t => (F.initial t).matrix)
    (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
    F.L_hat_isBigO_one (by simpa [ch14ext_cor147SourceXabs,
      ch14ext_cor147SourceQ, ch14ext_cor147SourceV] using F.X_abs_isBigO_one)
    F.U_hat_isBigO_one F.y_isBigO_one F.x_hat_isBigO_one i
  simpa only [ch14ext_cor147SourceResidualRemainder, unit] using
    hscaled.add hhigher

theorem ch14ext_cor147Source_residual_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hUinv : IsInverse n U U_inv) :
    (forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.x_hat t j|) +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i) ∧
      forall i,
        (fun t => ch14ext_cor147SourceResidualRemainder F L U U_inv t i)
          =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Source_residual_bound F L U U_inv
      hRow hdet hLU hUinv
  · exact ch14ext_cor147SourceResidualRemainder_isBigO
      F L U U_inv hLU hdet hUinv

theorem ch14ext_cor147Source_forwardT1_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i -
          ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.initial t).matrix a j|)
            (fun j => |F.x_hat t j|) i -
          matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.initial t).matrix i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hLabsOne := matrixFamily_abs_isBigOOne F.L_hat_isBigO_one
  have hLabsDiff := ch14ext_matrixFamily_absDifference_isBigO L hprox.1
  have hLactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.L_hat t i j|)
        (matMulVec n (fun i j => |(F.initial t).matrix i j|)
          (fun i => |F.x_hat t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hLabsOne hUactionOne
  have hLactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.L_hat t a j|)
            (matMulVec n (fun a j => |(F.initial t).matrix a j|)
              (fun j => |F.x_hat t j|)) i -
          matMulVec n (absMatrix n L)
            (matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |F.L_hat t i j|) (A := absMatrix n L)
      (x := fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|))
      (y := fun t => matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|))
      (by simpa only [absMatrix] using hLabsDiff) hUactionDiff hUactionOne
  have hfinal := ch14ext_fixedMatrix_vectorDifference_isBigO
    (absMatrix n A_inv) hLactionDiff
  simpa only [ch14ext_gjeForwardT1, absMatrix, absVec] using hfinal

theorem ch14ext_cor147Source_forwardT2_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i -
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U (F.x_hat t) i)
      (fun t => (F.model t).u) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hprox := ch14ext_cor147Source_factorProximity_isBigO F L U hLU hdet
  have hInv := ch14ext_cor147Source_inverseProximity_isBigO F U U_inv
    hprox.2 hUinv
  have hxabs := ch14ext_vectorFamily_abs_isBigOOne F.x_hat_isBigO_one
  have hUabsOne := matrixFamily_abs_isBigOOne F.U_hat_isBigO_one
  have hUabsDiff := ch14ext_matrixFamily_absDifference_isBigO U hprox.2
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
        (fun i => |F.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |(F.initial t).matrix a j|)
            (fun j => |F.x_hat t j|) i -
          matMulVec n (absMatrix n U) (fun j => |F.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |(F.initial t).matrix i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hInvAbsDiff := ch14ext_matrixFamily_absDifference_isBigO U_inv hInv
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.U_hat_inv t i j|) (A := absMatrix n U_inv)
    (x := fun t => matMulVec n (fun i j => |(F.initial t).matrix i j|)
      (fun i => |F.x_hat t i|))
    (y := fun t => matMulVec n (absMatrix n U) (fun i => |F.x_hat t i|))
    (by simpa only [absMatrix] using hInvAbsDiff) hUactionDiff hUactionOne
  simpa only [ch14ext_gjeForwardT2, absMatrix, absVec] using hfinal

theorem ch14ext_cor147Source_forwardCore_difference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        (ch14ext_gjeForwardT1 n A_inv (F.L_hat t) (F.initial t).matrix
            (F.x_hat t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.initial t).matrix (F.x_hat t) i) -
        (ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
            (F.x_hat t) i))
      (fun t => (F.model t).u) := by
  intro i
  have h1 := ch14ext_cor147Source_forwardT1_difference_isBigO
    F A_inv L U hLU hdet i
  have h2 := ch14ext_cor147Source_forwardT2_difference_isBigO
    F L U U_inv hLU hdet hUinv i
  have h := h1.add (h2.const_mul_left (3 : Real))
  convert h using 1
  funext t
  ring

theorem ch14ext_cor147SourceForwardVectorRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i => ch14ext_cor147SourceForwardVectorRemainder
        F A_inv L U U_inv t i)
      (fun t => (F.model t).u ^ 2) := by
  let unit : ι -> Real := fun t => (F.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hcore := ch14ext_cor147Source_forwardCore_difference_isBigO
    F A_inv L U U_inv hLU hdet hUinv
  intro i
  have hscaled := (hu.mul (hcore i)).const_mul_left (2 * (n : Real))
  have hlead :
      (fun t =>
        (2 * (n : Real) * unit t *
              ch14ext_gjeForwardT1 n A_inv (F.L_hat t)
                (F.initial t).matrix (F.x_hat t) i +
            6 * (n : Real) * unit t *
              ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
                (F.initial t).matrix (F.x_hat t) i) -
          (2 * (n : Real) * unit t *
              ch14ext_gjeForwardT1 n A_inv L U (F.x_hat t) i +
            6 * (n : Real) * unit t *
              ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
                (F.x_hat t) i)) =O[l] (fun t => unit t ^ 2) := by
    convert hscaled using 1 <;> funext t <;> ring
  have hhigher := ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n
    F.model (fun _ : ι => A_inv) F.L_hat (fun t => (F.initial t).matrix)
    (ch14ext_cor147SourcePabs F) F.U_hat_inv F.z
    (fun t => (F.initial t).rhs) F.x_hat F.unit_tendsto_zero
    (ch14ext_fixedMatrix_family_isBigOOne l A_inv) F.L_hat_isBigO_one
    F.U_hat_isBigO_one (by simpa [ch14ext_cor147SourcePabs,
      ch14ext_cor147SourceV] using F.P_abs_isBigO_one)
    F.U_hat_inv_isBigO_one F.z_isBigO_one F.y_isBigO_one
    F.x_hat_isBigO_one i
  simpa only [ch14ext_cor147SourceForwardVectorRemainder, unit] using
    hlead.add hhigher

theorem ch14ext_cor147SourceForwardRelativeRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (x : Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    (fun t => ch14ext_cor147SourceForwardRelativeRemainder
      F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2) := by
  have hvec := ch14ext_cor147SourceForwardVectorRemainder_isBigO
    F A_inv L U U_inv hLU hdet hUinv
  have hnorm := ch14ext_vectorFamily_infNorm_isBigO hvec
  have hscaled := hnorm.const_mul_left (infNormVec x)⁻¹
  simpa only [ch14ext_cor147SourceForwardRelativeRemainder,
    div_eq_mul_inv, mul_comm] using hscaled

theorem ch14ext_cor147SourceForwardPrintedRemainder_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real)
    (x : Fin n -> Real)
    (hLU : LUFactSpec n A L U)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hUinv : IsInverse n U U_inv) :
    (fun t => ch14ext_cor147SourceForwardPrintedRemainder
      F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2) := by
  let unit : ι -> Real := fun t => (F.model t).u
  let C : ι -> Real := ch14ext_cor147SourceForwardLeadingCoefficient F A_inv
  let rho : ι -> Real := fun t =>
    ch14ext_cor147SourceForwardRelativeRemainder F A_inv L U U_inv x t
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos) A A_inv + 3)
  have hCeq : C = fun t => K * unit t := by
    funext t
    dsimp [C, K, unit, ch14ext_cor147SourceForwardLeadingCoefficient]
    ring
  have hunit : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hC : C =O[l] unit := by
    rw [hCeq]
    exact hunit.const_mul_left K
  have hCsq : (fun t => C t ^ 2) =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two] using hC.mul hC
  have hCzero : Tendsto C l (𝓝 0) := by
    simpa only [C] using
      ch14ext_cor147SourceForwardLeadingCoefficient_tendsto_zero F A_inv
  have hden : Tendsto (fun t => 1 - C t) l (𝓝 1) := by
    simpa using hCzero.const_sub 1
  have hinvOne : (fun t => (1 - C t)⁻¹) =O[l]
      (fun _ : ι => (1 : Real)) := by
    have hinv : Tendsto (fun t => (1 - C t)⁻¹) l (𝓝 (1 : Real)) := by
      simpa using hden.inv₀ one_ne_zero
    exact hinv.isBigO_one Real
  have hterm1 : (fun t => C t ^ 2 / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hCsq.mul hinvOne
  have hrho : rho =O[l] (fun t => unit t ^ 2) := by
    simpa only [rho, unit] using
      ch14ext_cor147SourceForwardRelativeRemainder_isBigO
        F A_inv L U U_inv x hLU hdet hUinv
  have hterm2 : (fun t => rho t / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hrho.mul hinvOne
  simpa only [ch14ext_cor147SourceForwardPrintedRemainder, C, rho, unit] using
    hterm1.add hterm2

theorem ch14ext_cor147Source_forward_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    (∀ᶠ t in l,
      infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147SourceForwardPrintedRemainder
            F A_inv L U U_inv x t) ∧
      (fun t => ch14ext_cor147SourceForwardPrintedRemainder
        F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Source_forward_printed_eventually
      F A_inv L U U_inv x hRow hdet hLU hAinv hUinv hExact hxpos
  · exact ch14ext_cor147SourceForwardPrintedRemainder_isBigO
      F A_inv L U U_inv x hLU hdet hUinv

/-- **Higham Corollary 14.7, strict source-facing family endpoint.**

The source-active Algorithm 14.4 trace supplies all second-stage recurrence
bounds.  Factor proximity and the `Xabs` replacement are derived above from
the operational certificates.  The nontrivial-filter instance is explicit,
so neither eventual statement nor any `O(u^2)` claim can be vacuous. -/
theorem ch14ext_cor147Source_vanishing_family_endpoint
    {ι : Type*} {l : Filter ι} [NeBot l] {n : Nat}
    {A : Fin n -> Fin n -> Real} {b : Fin n -> Real}
    (F : Ch14Cor147SourceFamily ι l n A b)
    (A_inv L U U_inv : Fin n -> Fin n -> Real) (x : Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    ((forall t i,
      |b i - matMulVec n A (F.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.x_hat t j|) +
          ch14ext_cor147SourceResidualRemainder F L U U_inv t i) ∧
      (forall i,
        (fun t => ch14ext_cor147SourceResidualRemainder F L U U_inv t i)
          =O[l] (fun t => (F.model t).u ^ 2))) ∧
    ((∀ᶠ t in l,
      infNormVec (fun i => x i - F.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147SourceForwardPrintedRemainder
            F A_inv L U U_inv x t) ∧
      (fun t => ch14ext_cor147SourceForwardPrintedRemainder
        F A_inv L U U_inv x t) =O[l] (fun t => (F.model t).u ^ 2)) := by
  constructor
  · exact ch14ext_cor147Source_residual_vanishing_family_endpoint
      F L U U_inv hRow hdet hLU hUinv
  · exact ch14ext_cor147Source_forward_vanishing_family_endpoint
      F A_inv L U U_inv x hRow hdet hLU hAinv hUinv hExact hxpos

end Ch14Ext
end NumStability
