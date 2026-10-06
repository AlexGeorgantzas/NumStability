import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.PerturbationTheory
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter08.Lemma08.CorrectedCondition.RowDominance
import NumStability.Source.Higham.Chapter14.Algorithm04.SecondStage.GaussJordanQConstruction
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Closure
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.Concrete
import NumStability.Source.Higham.Chapter14.Corollary07.DiagonalDominance.WeakFamily
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.EliminationFamilies.CoefficientAsymptotics
import NumStability.Source.Higham.Chapter14.Theorem05.ForwardError.GJEAsymptoticFamilies

/-!
# ResidualAndForwardBounds

Canonical destination for the Chapter14.Corollary07 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Corollary147WeakFamily` during wave R08.
Holds 11 declaration(s): 11 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The complete residual correction is uniformly `O(u^2)`. -/
theorem ch14ext_cor147WeakResidualRemainder_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (i : Fin n) :
    (fun t => ch14ext_cor147WeakResidualRemainder n F t i) =O[l]
      (fun t => (F.run.model t).u ^ 2) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hdiff := ch14ext_cor147Weak_residualLeading_difference_isBigO F i
  have hlead :
      (fun t => 8 * (n : Real) * unit t *
        (ch14ext_gjeResidualS2 n (F.run.L_hat t)
            (ch14ext_gjeConcreteFamilyXabs F.run t) (F.run.V t start)
            (F.run.x_hat t) i -
          ch14ext_gjeResidualS2 n L
            (ch14ext_cor147WeakExactX n U U_inv) U (F.run.x_hat t) i))
        =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two, mul_assoc] using
      (hu.mul hdiff).const_mul_left (8 * (n : Real))
  have hhigher := ch14ext_gjeResidualHigherOrder_family_isBigO n
    F.run.model F.run.L_hat (ch14ext_gjeConcreteFamilyXabs F.run)
    (fun t => F.run.V t start) (fun t => F.run.xseq t start)
    F.run.x_hat F.run.unit_tendsto_zero F.run.L_hat_isBigO_one
    F.run.X_abs_isBigO_one F.run.U_hat_isBigO_one F.run.y_isBigO_one
    F.run.x_hat_isBigO_one i
  simpa only [ch14ext_cor147WeakResidualRemainder, unit] using
    hlead.add hhigher

/-- Pointwise Corollary 14.7 residual bound for weak row diagonal dominance.
The printed leading term is reduced with the exact no-pivot `U`; rounded row
dominance is nowhere asserted. -/
theorem ch14ext_cor147Weak_residual_bound
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A L U U_inv : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hUinv : IsInverse n U U_inv) :
    forall t i,
      |b i - matMulVec n A (F.run.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.run.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.run.x_hat t j|) +
          ch14ext_cor147WeakResidualRemainder n F t i := by
  intro t i
  have hconcrete :=
    (ch14ext_gjeConcrete_residual_14_31_vanishing_family_endpoint
      n A b start F.run).1 t i
  have hURow := ch14ext_exactNoPivotLU_upper_higham8_8 A L U hRow hdet hLU
  have hlead := ch14ext_cor147_residual_leading_object_le
    n (F.run.model t) A L U U_inv (F.run.x_hat t) hLU hURow hUinv i
  calc
    |b i - matMulVec n A (F.run.x_hat t) i| <=
        8 * (n : Real) * (F.run.model t).u *
            ch14ext_gjeResidualS2 n (F.run.L_hat t)
              (ch14ext_gjeConcreteFamilyXabs F.run t) (F.run.V t start)
              (F.run.x_hat t) i +
          ch14ext_gjeResidualHigherOrder n (F.run.model t) (F.run.L_hat t)
            (ch14ext_gjeConcreteFamilyXabs F.run t) (F.run.V t start)
            (F.run.xseq t start) (F.run.x_hat t) i := hconcrete
    _ = 8 * (n : Real) * (F.run.model t).u *
          ch14ext_gjeResidualS2 n L
            (ch14ext_cor147WeakExactX n U U_inv) U (F.run.x_hat t) i +
          ch14ext_cor147WeakResidualRemainder n F t i := by
      unfold ch14ext_cor147WeakResidualRemainder
      ring
    _ <= 32 * (n : Real) ^ 2 * (F.run.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.run.x_hat t j|) +
          ch14ext_cor147WeakResidualRemainder n F t i :=
      by
        simpa only [ch14ext_cor147WeakExactX, add_comm] using
          add_le_add_right hlead
            (ch14ext_cor147WeakResidualRemainder n F t i)

/-- Genuine family-level residual closure of Corollary 14.7. -/
theorem ch14ext_cor147Weak_residual_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A L U U_inv : Fin n -> Fin n -> Real) (b : Fin n -> Real)
    (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hUinv : IsInverse n U U_inv) :
    (forall t i,
      |b i - matMulVec n A (F.run.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.run.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.run.x_hat t j|) +
          ch14ext_cor147WeakResidualRemainder n F t i) /\
      forall i, (fun t => ch14ext_cor147WeakResidualRemainder n F t i)
        =O[l] (fun t => (F.run.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Weak_residual_bound
      n A L U U_inv b start F hRow hdet hLU hUinv
  · exact ch14ext_cor147WeakResidualRemainder_isBigO F

/-- The complete forward vector correction is componentwise `O(u^2)`. -/
theorem ch14ext_cor147WeakForwardVectorRemainder_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A L U U_inv : Fin n -> Fin n -> Real}
    (A_inv : Fin n -> Fin n -> Real) {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i => ch14ext_cor147WeakForwardVectorRemainder n A_inv F t i)
      (fun t => (F.run.model t).u ^ 2) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  have hu : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hcore := ch14ext_cor147Weak_forwardCore_difference_isBigO
    (A_inv := A_inv) F hUinv
  intro i
  have hscaled := (hu.mul (hcore i)).const_mul_left (2 * (n : Real))
  have hlead :
      (fun t =>
        (2 * (n : Real) * unit t *
              ch14ext_gjeForwardT1 n A_inv (F.run.L_hat t)
                (F.run.V t start) (F.run.x_hat t) i +
            6 * (n : Real) * unit t *
              ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
                (F.run.V t start) (F.run.x_hat t) i) -
          (2 * (n : Real) * unit t *
              ch14ext_gjeForwardT1 n A_inv L U (F.run.x_hat t) i +
            6 * (n : Real) * unit t *
              ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
                (F.run.x_hat t) i)) =O[l] (fun t => unit t ^ 2) := by
    convert hscaled using 1 <;> funext t <;> ring
  have hhigher := ch14ext_gjeForwardLiteralHigherOrder_family_isBigO n
    F.run.model (fun _ : iota => A_inv) F.run.L_hat
    (fun t => F.run.V t start) (ch14ext_gjeConcreteFamilyPabs F.run)
    F.U_hat_inv F.z (fun t => F.run.xseq t start) F.run.x_hat
    F.run.unit_tendsto_zero (ch14ext_fixedMatrix_family_isBigOOne l A_inv)
    F.run.L_hat_isBigO_one F.run.U_hat_isBigO_one F.pabs_isBigO_one
    F.U_hat_inv_isBigO_one F.z_isBigO_one F.run.y_isBigO_one
    F.run.x_hat_isBigO_one i
  simpa only [ch14ext_cor147WeakForwardVectorRemainder, unit] using
    hlead.add hhigher

/-- Multiplication by the fixed relative normalization preserves `O(u^2)`.
The source-facing bound below separately requires a positive exact-solution
norm, so its relative quotient is meaningful. -/
theorem ch14ext_cor147WeakForwardRelativeRemainder_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A L U U_inv : Fin n -> Fin n -> Real}
    (A_inv : Fin n -> Fin n -> Real) {b : Fin n -> Real} {start : Nat}
    (x : Fin n -> Real)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hUinv : IsInverse n U U_inv) :
    (fun t => ch14ext_cor147WeakForwardRelativeRemainder n A_inv x F t)
      =O[l] (fun t => (F.run.model t).u ^ 2) := by
  have hvec := ch14ext_cor147WeakForwardVectorRemainder_isBigO A_inv F hUinv
  have hnorm := ch14ext_vectorFamily_infNorm_isBigO hvec
  have hscaled := hnorm.const_mul_left (infNormVec x)⁻¹
  simpa only [ch14ext_cor147WeakForwardRelativeRemainder, div_eq_mul_inv,
    mul_comm] using hscaled

/-- The denominator-expansion correction and the rescaled literal (14.32)
remainder are together uniformly `O(u^2)`. -/
theorem ch14ext_cor147WeakForwardPrintedRemainder_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    (A A_inv : Fin n -> Fin n -> Real) {L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat} (x : Fin n -> Real)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hUinv : IsInverse n U U_inv) :
    (fun t => ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t)
      =O[l] (fun t => (F.run.model t).u ^ 2) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  let C : iota -> Real :=
    ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F
  let rho : iota -> Real := fun t =>
    ch14ext_cor147WeakForwardRelativeRemainder n A_inv x F t
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
      A A_inv + 3)
  have hCeq : C = fun t => K * unit t := by
    funext t
    dsimp [C, K, unit, ch14ext_cor147WeakForwardLeadingCoefficient]
    ring
  have hunit : unit =O[l] unit := Asymptotics.isBigO_refl _ l
  have hC : C =O[l] unit := by
    rw [hCeq]
    exact hunit.const_mul_left K
  have hCsq : (fun t => C t ^ 2) =O[l] (fun t => unit t ^ 2) := by
    simpa only [pow_two] using hC.mul hC
  have hCzero : Tendsto C l (𝓝 0) := by
    simpa only [C] using
      ch14ext_cor147WeakForwardLeadingCoefficient_tendsto_zero n A A_inv F
  have hden : Tendsto (fun t => 1 - C t) l (𝓝 1) := by
    simpa using hCzero.const_sub 1
  have hinvOne : (fun t => (1 - C t)⁻¹) =O[l]
      (fun _ : iota => (1 : Real)) := by
    have hinv : Tendsto (fun t => (1 - C t)⁻¹) l (𝓝 (1 : Real)) := by
      simpa using hden.inv₀ one_ne_zero
    exact hinv.isBigO_one Real
  have hterm1 : (fun t => C t ^ 2 / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hCsq.mul hinvOne
  have hrho : rho =O[l] (fun t => unit t ^ 2) := by
    simpa only [rho, unit] using
      ch14ext_cor147WeakForwardRelativeRemainder_isBigO A_inv x F hUinv
  have hterm2 : (fun t => rho t / (1 - C t)) =O[l]
      (fun t => unit t ^ 2) := by
    simpa only [div_eq_mul_inv, mul_one] using hrho.mul hinvOne
  simpa only [ch14ext_cor147WeakForwardPrintedRemainder, C, rho, unit] using
    hterm1.add hterm2

/-- Normwise forward Corollary 14.7 bound. The exact weakly row-dominant `U`
is used in the `4 n^3 u` reduction; no rounded dominance hypothesis appears. -/
theorem ch14ext_cor147Weak_forward_bound
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A A_inv L U U_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    forall t,
      infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.run.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
              A A_inv + 3) *
            (infNormVec (F.run.x_hat t) / infNormVec x) +
          ch14ext_cor147WeakForwardRelativeRemainder n A_inv x F t := by
  intro t
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos
  have hconcrete :=
    (ch14ext_gjeConcrete_forward_14_32_vanishing_family_endpoint
      n A A_inv b x start F.run F.U_hat_inv F.z hAinv.1
      (fun q => (F.computed_upper_inverse q).2) hExact F.upper_solve
      F.U_hat_inv_isBigO_one F.z_isBigO_one F.pabs_isBigO_one).1 t
  have hURow := ch14ext_exactNoPivotLU_upper_higham8_8 A L U hRow hdet hLU
  have hFactProduct : LUFactSpec n
      (ch14ext_cor147ComputedProduct n L U) L U := by
    exact {
      L_diag := hLU.L_diag
      L_upper_zero := hLU.L_upper_zero
      U_lower_zero := hLU.U_lower_zero
      product_eq := by intro i j; rfl
    }
  have hProductEq : ch14ext_cor147ComputedProduct n L U = A := by
    funext i j
    simpa only [ch14ext_cor147ComputedProduct, matMul] using hLU.product_eq i j
  have hProductNorm :
      infNorm (ch14ext_cor147ComputedProduct n L U) <= infNorm A / (1 : Real) := by
    rw [hProductEq, div_one]
  have hExactLead := ch14ext_cor147_forward_leading_infNorm_le
    n (F.run.model t) hn A A_inv L U U_inv (F.run.x_hat t)
    hFactProduct hURow hUinv (1 : Real) zero_lt_one hProductNorm
  let exactLead : Fin n -> Real := fun i =>
    2 * (n : Real) * (F.run.model t).u *
        ch14ext_gjeForwardT1 n A_inv L U (F.run.x_hat t) i +
      6 * (n : Real) * (F.run.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n U_inv) U (F.run.x_hat t) i
  let rem : Fin n -> Real := fun i =>
    ch14ext_cor147WeakForwardVectorRemainder n A_inv F t i
  have hpoint : forall i, |x i - F.run.x_hat t i| <= exactLead i + rem i := by
    intro i
    calc
      |x i - F.run.x_hat t i| <=
          2 * (n : Real) * (F.run.model t).u *
              ch14ext_gjeForwardT1 n A_inv (F.run.L_hat t)
                (F.run.V t start) (F.run.x_hat t) i +
            6 * (n : Real) * (F.run.model t).u *
              ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
                (F.run.V t start) (F.run.x_hat t) i +
            ch14ext_gjeForwardLiteralHigherOrder n (F.run.model t) A_inv
              (F.run.L_hat t) (F.run.V t start)
              (ch14ext_gjeConcreteFamilyPabs F.run t) (F.U_hat_inv t)
              (F.z t) (F.run.xseq t start) (F.run.x_hat t) i := hconcrete i
      _ = exactLead i + rem i := by
        dsimp [exactLead, rem]
        unfold ch14ext_cor147WeakForwardVectorRemainder
        ring
  have hnormSplit :
      infNormVec (fun i => x i - F.run.x_hat t i) <=
        infNormVec exactLead + infNormVec rem := by
    apply infNormVec_le_of_abs_le
    · intro i
      calc
        |x i - F.run.x_hat t i| <= exactLead i + rem i := hpoint i
        _ <= |exactLead i| + |rem i| :=
          add_le_add (le_abs_self _) (le_abs_self _)
        _ <= infNormVec exactLead + infNormVec rem :=
          add_le_add (abs_le_infNormVec exactLead i) (abs_le_infNormVec rem i)
    · exact add_nonneg (infNormVec_nonneg exactLead) (infNormVec_nonneg rem)
  have hlead : infNormVec exactLead <=
      4 * (n : Real) ^ 3 * (F.run.model t).u *
        (kappaInf n hn A A_inv + 3) * infNormVec (F.run.x_hat t) := by
    simpa only [exactLead, div_one] using hExactLead
  have hnorm : infNormVec (fun i => x i - F.run.x_hat t i) <=
      4 * (n : Real) ^ 3 * (F.run.model t).u *
          (kappaInf n hn A A_inv + 3) * infNormVec (F.run.x_hat t) +
        infNormVec rem :=
    le_trans hnormSplit (add_le_add hlead (le_refl _))
  calc
    infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x <=
        (4 * (n : Real) ^ 3 * (F.run.model t).u *
            (kappaInf n hn A A_inv + 3) * infNormVec (F.run.x_hat t) +
          infNormVec rem) / infNormVec x :=
      div_le_div_of_nonneg_right hnorm hxpos.le
    _ = 4 * (n : Real) ^ 3 * (F.run.model t).u *
            (kappaInf n hn A A_inv + 3) *
            (infNormVec (F.run.x_hat t) / infNormVec x) +
          ch14ext_cor147WeakForwardRelativeRemainder n A_inv x F t := by
      rw [add_div]
      unfold ch14ext_cor147WeakForwardRelativeRemainder
      dsimp [rem]
      ring

/-- Once the printed coefficient `C(u)` is below one, the computed-solution
norm ratio in the intermediate bound can be eliminated algebraically. -/
theorem ch14ext_cor147Weak_forward_printed_bound_of_coefficient_lt_one
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A A_inv L U U_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) (t : iota)
    (hsmall : ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F t < 1) :
    infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x <=
      4 * (n : Real) ^ 3 * (F.run.model t).u *
          (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
            A A_inv + 3) +
        ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t := by
  let e : Real :=
    infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x
  let ratio : Real := infNormVec (F.run.x_hat t) / infNormVec x
  let rho : Real :=
    ch14ext_cor147WeakForwardRelativeRemainder n A_inv x F t
  let C : Real := ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F t
  have hbase : e <= C * ratio + rho := by
    simpa only [e, ratio, rho, C,
      ch14ext_cor147WeakForwardLeadingCoefficient] using
      ch14ext_cor147Weak_forward_bound n A A_inv L U U_inv b x start F
        hRow hdet hLU hAinv hUinv hExact hxpos t
  have hratio : ratio <= 1 + e := by
    dsimp only [ratio, e]
    apply (div_le_iff₀ hxpos).2
    calc
      infNormVec (F.run.x_hat t) <=
          infNormVec x + infNormVec (fun i => x i - F.run.x_hat t i) :=
        ch14ext_infNormVec_approx_le_exact_add_error x (F.run.x_hat t)
      _ = (1 +
            infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x) *
          infNormVec x := by
        field_simp [hxpos.ne']
  have hCnonneg : 0 <= C := by
    exact ch14ext_cor147WeakForwardLeadingCoefficient_nonneg n A A_inv F t
  have hraw : e <= C * (1 + e) + rho := by
    exact le_trans hbase
      (add_le_add
        (mul_le_mul_of_nonneg_left hratio hCnonneg) (le_refl rho))
  have hdenpos : 0 < 1 - C := sub_pos.mpr hsmall
  have hmult : e * (1 - C) <= C + rho := by
    nlinarith [hraw]
  have hdiv : e <= (C + rho) / (1 - C) :=
    (le_div_iff₀ hdenpos).2 hmult
  have hdecomp : (C + rho) / (1 - C) =
      C + (C ^ 2 / (1 - C) + rho / (1 - C)) := by
    field_simp [ne_of_gt hdenpos]
    ring
  calc
    infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x = e := rfl
    _ <= (C + rho) / (1 - C) := hdiv
    _ = C + (C ^ 2 / (1 - C) + rho / (1 - C)) := hdecomp
    _ = 4 * (n : Real) ^ 3 * (F.run.model t).u *
          (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
            A A_inv + 3) +
        ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t := by
      rfl

/-- Source-literal forward Corollary 14.7 bound along the vanishing-roundoff
family. The inequality is eventual because `C(u)<1` is obtained from `u->0`,
not imposed as a global execution contract. -/
theorem ch14ext_cor147Weak_forward_printed_eventually
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A A_inv L U U_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    ∀ᶠ t in l,
      infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.run.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t := by
  have hzero :=
    ch14ext_cor147WeakForwardLeadingCoefficient_tendsto_zero n A A_inv F
  have hsmall : ∀ᶠ t in l,
      ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F t < 1 :=
    (tendsto_order.1 hzero).2 1 zero_lt_one
  filter_upwards [hsmall] with t ht
  exact ch14ext_cor147Weak_forward_printed_bound_of_coefficient_lt_one
    n A A_inv L U U_inv b x start F hRow hdet hLU hAinv hUinv hExact
    hxpos t ht

/-- Genuine source-literal family-level forward closure of Corollary 14.7. -/
theorem ch14ext_cor147Weak_forward_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A A_inv L U U_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    (∀ᶠ t in l,
      infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.run.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t) /\
      (fun t => ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t)
        =O[l] (fun t => (F.run.model t).u ^ 2) := by
  constructor
  · exact ch14ext_cor147Weak_forward_printed_eventually
      n A A_inv L U U_inv b x start F
      hRow hdet hLU hAinv hUinv hExact hxpos
  · exact ch14ext_cor147WeakForwardPrintedRemainder_isBigO
      A A_inv x F hUinv

/-- Source-facing family closure of Corollary 14.7 for the printed weak
row-diagonal-dominance case. Both exact explicit remainders are primary, and
both are proved uniformly `O(u^2)` along the same successful-run family. -/
theorem ch14ext_cor147Weak_vanishing_family_endpoint
    {iota : Type*} {l : Filter iota} [NeBot l] (n : Nat)
    (A A_inv L U U_inv : Fin n -> Fin n -> Real)
    (b x : Fin n -> Real) (start : Nat)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) ≠ 0)
    (hLU : LUFactSpec n A L U) (hAinv : IsInverse n A A_inv)
    (hUinv : IsInverse n U U_inv)
    (hExact : forall i, matMulVec n A x i = b i)
    (hxpos : 0 < infNormVec x) :
    ((forall t i,
      |b i - matMulVec n A (F.run.x_hat t) i| <=
        32 * (n : Real) ^ 2 * (F.run.model t).u *
            Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |F.run.x_hat t j|) +
          ch14ext_cor147WeakResidualRemainder n F t i) /\
      (forall i, (fun t => ch14ext_cor147WeakResidualRemainder n F t i)
        =O[l] (fun t => (F.run.model t).u ^ 2))) /\
    ((∀ᶠ t in l,
      infNormVec (fun i => x i - F.run.x_hat t i) / infNormVec x <=
        4 * (n : Real) ^ 3 * (F.run.model t).u *
            (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
              A A_inv + 3) +
          ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t) /\
      (fun t => ch14ext_cor147WeakForwardPrintedRemainder n A A_inv x F t)
        =O[l] (fun t => (F.run.model t).u ^ 2)) := by
  constructor
  · exact ch14ext_cor147Weak_residual_vanishing_family_endpoint
      n A L U U_inv b start F hRow hdet hLU hUinv
  · exact ch14ext_cor147Weak_forward_vanishing_family_endpoint
      n A A_inv L U U_inv b x start F hRow hdet hLU hAinv hUinv hExact hxpos

end Ch14Ext
end NumStability
