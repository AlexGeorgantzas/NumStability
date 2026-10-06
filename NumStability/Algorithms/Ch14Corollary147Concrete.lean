/-
Copyright (c) 2026 NumStability contributors. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
-/
import NumStability.Algorithms.Ch14GaussJordanQConstruction
import NumStability.Algorithms.Ch14Corollary147
import NumStability.Algorithms.Ch14Corollary147Closure

/-!
# Corollary 14.7 from the concrete Gauss-Jordan computation

This module composes the concrete equations (14.31) and (14.32) with the
row-diagonal-dominance reductions used in Corollary 14.7. It deliberately
keeps every finite-precision correction visible.

Weak row diagonal dominance is not open. Accordingly, row dominance of the
rounded upper factor is obtained only from an entrywise perturbation envelope
that fits strictly inside the margins of the exact no-pivot upper factor. The
residual also retains the explicit inverse-envelope bridge correction. No
residual or forward-error conclusion is accepted as a hypothesis.
-/

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

/-- The exact matrix represented by the computed triangular factors. -/
noncomputable def ch14ext_cor147ComputedProduct (n : Nat)
    (L_hat U_hat : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  matMul n L_hat U_hat

/-- A backward-error certificate induces an exact LU specification for the
computed product `L_hat * U_hat`. -/
theorem ch14ext_cor147_computedProduct_luFact (n : Nat)
    (A L_hat U_hat : Fin n -> Fin n -> Real) (eps : Real)
    (hLU : LUBackwardError n A L_hat U_hat eps) :
    LUFactSpec n (ch14ext_cor147ComputedProduct n L_hat U_hat) L_hat U_hat := by
  refine {
    L_diag := hLU.L_diag
    L_upper_zero := hLU.L_upper_zero
    U_lower_zero := hLU.U_lower_zero
    product_eq := ?_
  }
  intro i j
  rfl

/-- Exact no-pivot row dominance and its honest rounded transfer.

The first conjunct is Higham's exact elimination fact. The second conjunct
uses a strict row-margin budget; no unconditional preservation of weak
dominance under rounding is asserted. -/
theorem ch14ext_cor147_concrete_upper_factors_row_dominant {n : Nat}
    (fp : FPModel)
    (A L U L_hat U_hat E : Fin n -> Fin n -> Real)
    (hRow : IsRowDiagDominant n A)
    (hdet : Not (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) = 0))
    (hExactLU : LUFactSpec n A L U)
    (hRoundedLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hUpperErr : forall i j : Fin n,
      |U_hat i j - U i j| <= fp.u * E i j)
    (hMargin : forall i : Fin n,
      fp.u *
          (E i i +
            Finset.sum (Finset.univ.filter (fun j : Fin n => i.val < j.val))
              (fun j => E i j)) <
        ch14ext_upperRowDiagMargin n U i) :
    higham8_8_rowDiagDominantUpper n U /\
      higham8_8_rowDiagDominantUpper n U_hat := by
  constructor
  · exact ch14ext_exactNoPivotLU_upper_higham8_8 A L U hRow hdet hExactLU
  · exact ch14ext_roundedUpper_higham8_8_of_entrywiseEnvelope
      U U_hat E fp.u hRoundedLU.U_lower_zero hUpperErr hMargin

/-- Nonnegativity of the absolute triangular product used below. -/
theorem ch14ext_cor147_absProduct_nonneg (n : Nat)
    (L U : Fin n -> Fin n -> Real) (i j : Fin n) :
    0 <= matMul n (absMatrix n L) (absMatrix n U) i j := by
  unfold matMul absMatrix
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (abs_nonneg (L i k)) (abs_nonneg (U k j))

/-- The computed product is controlled rowwise by the source matrix.

The denominator is the exact finite-precision correction produced by solving
the backward-error self-bound. It tends to one in a genuine vanishing-unit-
roundoff family, but no asymptotic claim is needed here. -/
theorem ch14ext_cor147_computedProduct_rowSum_le_source
    (n : Nat) (fp : FPModel) (hn : 0 < n)
    (A L_hat U_hat U_inv : Fin n -> Fin n -> Real)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hgammaValid : gammaValid fp n)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hguard : 0 < 1 - (2 * (n : Real) - 1) * gamma fp n)
    (i : Fin n) :
    Finset.sum Finset.univ
        (fun j : Fin n =>
          |ch14ext_cor147ComputedProduct n L_hat U_hat i j|) <=
      (Finset.sum Finset.univ (fun j : Fin n => |A i j|)) /
        (1 - (2 * (n : Real) - 1) * gamma fp n) := by
  let A_hat := ch14ext_cor147ComputedProduct n L_hat U_hat
  let MLU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let c : Real := 2 * (n : Real) - 1
  let delta : Real := 1 - c * gamma fp n
  have hgamma : 0 <= gamma fp n := gamma_nonneg fp hgammaValid
  have hFact : LUFactSpec n A_hat L_hat U_hat := by
    simpa [A_hat] using
      ch14ext_cor147_computedProduct_luFact n A L_hat U_hat (gamma fp n) hLU
  have hMLUrowAbs :
      Finset.sum Finset.univ (fun j : Fin n => |MLU i j|) <=
        c * Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) := by
    simpa [MLU, c] using
      ch14ext_cor147_absLU_rowSum_le n hn A_hat L_hat U_hat U_inv
        hFact hURow hUinv i
  have hMLUnonneg : forall a j : Fin n, 0 <= MLU a j := by
    intro a j
    exact ch14ext_cor147_absProduct_nonneg n L_hat U_hat a j
  have hentry : forall j : Fin n,
      |A_hat i j| <= |A i j| + gamma fp n * MLU i j := by
    intro j
    have hback : |A_hat i j - A i j| <= gamma fp n * MLU i j := by
      simpa [A_hat, MLU, ch14ext_cor147ComputedProduct, matMul, absMatrix] using
        hLU.backward_bound i j
    calc
      |A_hat i j| = |A i j + (A_hat i j - A i j)| := by ring_nf
      _ <= |A i j| + |A_hat i j - A i j| := abs_add_le _ _
      _ <= |A i j| + gamma fp n * MLU i j := add_le_add_right hback _
  have hsum :
      Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) <=
        Finset.sum Finset.univ (fun j : Fin n => |A i j|) +
          gamma fp n * Finset.sum Finset.univ (fun j : Fin n => MLU i j) := by
    calc
      Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) <=
          Finset.sum Finset.univ
            (fun j : Fin n => |A i j| + gamma fp n * MLU i j) :=
        Finset.sum_le_sum fun j _ => hentry j
      _ = Finset.sum Finset.univ (fun j : Fin n => |A i j|) +
          gamma fp n * Finset.sum Finset.univ (fun j : Fin n => MLU i j) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hMLUrow :
      Finset.sum Finset.univ (fun j : Fin n => MLU i j) <=
        c * Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) := by
    calc
      Finset.sum Finset.univ (fun j : Fin n => MLU i j) =
          Finset.sum Finset.univ (fun j : Fin n => |MLU i j|) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_of_nonneg (hMLUnonneg i j)]
      _ <= c * Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) :=
        hMLUrowAbs
  have hself :
      Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) <=
        Finset.sum Finset.univ (fun j : Fin n => |A i j|) +
          gamma fp n *
            (c * Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|)) := by
    have hmul := mul_le_mul_of_nonneg_left hMLUrow hgamma
    linarith
  have hdelta : 0 < delta := by simpa [delta, c] using hguard
  apply (le_div_iff₀ hdelta).2
  dsimp [delta, c]
  dsimp [A_hat] at hself
  nlinarith

/-- Infinity-norm form of the computed-product inflation bound. -/
theorem ch14ext_cor147_computedProduct_infNorm_le_source
    (n : Nat) (fp : FPModel) (hn : 0 < n)
    (A L_hat U_hat U_inv : Fin n -> Fin n -> Real)
    (hLU : LUBackwardError n A L_hat U_hat (gamma fp n))
    (hgammaValid : gammaValid fp n)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hguard : 0 < 1 - (2 * (n : Real) - 1) * gamma fp n) :
    infNorm (ch14ext_cor147ComputedProduct n L_hat U_hat) <=
      infNorm A / (1 - (2 * (n : Real) - 1) * gamma fp n) := by
  apply infNorm_le_of_row_sum_le
  · intro i
    calc
      Finset.sum Finset.univ
          (fun j : Fin n =>
            |ch14ext_cor147ComputedProduct n L_hat U_hat i j|) <=
          (Finset.sum Finset.univ (fun j : Fin n => |A i j|)) /
            (1 - (2 * (n : Real) - 1) * gamma fp n) :=
        ch14ext_cor147_computedProduct_rowSum_le_source
          n fp hn A L_hat U_hat U_inv hLU hgammaValid hURow hUinv hguard i
      _ <= infNorm A /
            (1 - (2 * (n : Real) - 1) * gamma fp n) := by
        exact div_le_div_of_nonneg_right (row_sum_le_infNorm A i) hguard.le
  · exact div_nonneg (infNorm_nonneg A) hguard.le

/-- The explicit correction generated when the concrete residual envelope
`X_abs` is replaced by `|U_hat| |U_hat_inv|`. -/
noncomputable def ch14ext_cor147ResidualBridgeTerm (n : Nat)
    (L_hat R U_hat : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real) (i : Fin n) : Real :=
  matMulVec n (absMatrix n L_hat)
    (matMulVec n R
      (matMulVec n (absMatrix n U_hat) (absVec n x_hat))) i

theorem ch14ext_cor147ResidualBridgeTerm_nonneg (n : Nat)
    (L_hat R U_hat : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real)
    (hR : forall i j : Fin n, 0 <= R i j) (i : Fin n) :
    0 <= ch14ext_cor147ResidualBridgeTerm n L_hat R U_hat x_hat i := by
  have hw : forall j : Fin n,
      0 <= matMulVec n (absMatrix n U_hat) (absVec n x_hat) j := by
    intro j
    exact ch14ext_absMatrix_action_nonneg n U_hat (absVec n x_hat)
      (fun k => abs_nonneg (x_hat k)) j
  have hRw : forall a : Fin n,
      0 <= matMulVec n R
        (matMulVec n (absMatrix n U_hat) (absVec n x_hat)) a := by
    intro a
    unfold matMulVec
    exact Finset.sum_nonneg fun j _ => mul_nonneg (hR a j) (hw j)
  exact ch14ext_absMatrix_action_nonneg n L_hat _ hRw i

/-- A left inverse converts a concrete product residual into a bound for that
left inverse. This is the algebraic step needed to compare the constructed
`Q` with the rounded upper factor; it assumes no comparison envelope. -/
theorem ch14ext_abs_leftInverse_le_abs_factor_add (n : Nat)
    (Q P P_abs U : Fin n -> Fin n -> Real) (c : Real)
    (hQP : matMul n Q P = idMatrix n)
    (hResidual : forall i j : Fin n,
      |idMatrix n i j - matMul n P U i j| <=
        c * matMul n P_abs (absMatrix n U) i j)
    (i j : Fin n) :
    |Q i j| <= |U i j| +
      c * matMul n
        (matMul n (absMatrix n Q) P_abs) (absMatrix n U) i j := by
  let D : Fin n -> Fin n -> Real := fun a b =>
    idMatrix n a b - matMul n P U a b
  have hQD : matMul n Q D i j = Q i j - U i j := by
    unfold D matMul
    simp only [mul_sub, Finset.sum_sub_distrib]
    change matMul n Q (idMatrix n) i j -
      matMul n Q (matMul n P U) i j = Q i j - U i j
    rw [matMul_id_right, ← matMul_assoc n Q P U, hQP, matMul_id_left]
  have hrepr : Q i j = U i j + matMul n Q D i j := by linarith
  rw [hrepr]
  calc
    |U i j + matMul n Q D i j| <=
        |U i j| + |matMul n Q D i j| := abs_add_le _ _
    _ <= |U i j| +
        Finset.sum Finset.univ (fun a : Fin n => |Q i a| * |D a j|) := by
      have hsum : |matMul n Q D i j| <=
          Finset.sum Finset.univ (fun a : Fin n => |Q i a| * |D a j|) := by
        calc
        |matMul n Q D i j| <=
            Finset.sum Finset.univ (fun a : Fin n => |Q i a * D a j|) :=
          Finset.abs_sum_le_sum_abs _ _
        _ = Finset.sum Finset.univ
            (fun a : Fin n => |Q i a| * |D a j|) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [abs_mul]
      linarith
    _ <= |U i j| +
        Finset.sum Finset.univ
          (fun a : Fin n =>
            |Q i a| * (c * matMul n P_abs (absMatrix n U) a j)) := by
      have hsum :
          Finset.sum Finset.univ (fun a : Fin n => |Q i a| * |D a j|) <=
            Finset.sum Finset.univ
              (fun a : Fin n =>
                |Q i a| * (c * matMul n P_abs (absMatrix n U) a j)) := by
        apply Finset.sum_le_sum
        intro a _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg (Q i a))
        simpa [D] using hResidual a j
      linarith
    _ = |U i j| +
        c * matMul n (absMatrix n Q)
          (matMul n P_abs (absMatrix n U)) i j := by
      congr 1
      unfold matMul absMatrix
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = |U i j| +
        c * matMul n
          (matMul n (absMatrix n Q) P_abs) (absMatrix n U) i j := by
      rw [matMul_assoc]

/-- The fully concrete correction in the residual identification
`X_abs = |U_hat| |U_hat_inv| + correction`.

Both summands are generated by the actual matrix-accumulation residual: the
first corrects the signed cumulative product and the second corrects the
constructed left inverse. -/
noncomputable def ch14ext_cor147ConcreteXResidualCorrection (n : Nat)
    (V : Nat -> Fin n -> Fin n -> Real) (start : Nat)
    (U_inv : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  let P_abs := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  let X_abs := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  let AU := absMatrix n (V start)
  let AU_inv := absMatrix n U_inv
  fun i j =>
    matMul n AU (matMul n (matMul n P_abs AU) AU_inv) i j +
      matMul n (matMul n X_abs AU) P_abs i j

theorem ch14ext_cor147ConcreteXResidualCorrection_nonneg (n : Nat)
    (V : Nat -> Fin n -> Fin n -> Real) (start : Nat)
    (U_inv : Fin n -> Fin n -> Real) (i j : Fin n) :
    0 <= ch14ext_cor147ConcreteXResidualCorrection n V start U_inv i j := by
  unfold ch14ext_cor147ConcreteXResidualCorrection
  have hP : forall a b : Fin n,
      0 <= ch14ext_absCumProd n (ch14ext_gjeSeqStages n V)
        start (n - 1) a b := by
    intro a b
    exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n V)
      start (start + (n - 1)) a b
  have hX : forall a b : Fin n,
      0 <= ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
        (ch14ext_gjeConstructedQ n V start) start (n - 1) a b := by
    intro a b
    exact ch14ext_gjeXabs_nonneg n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1) a b
  have hmm : forall (M N : Fin n -> Fin n -> Real),
      (forall a b : Fin n, 0 <= M a b) ->
      (forall a b : Fin n, 0 <= N a b) ->
      forall a b : Fin n, 0 <= matMul n M N a b := by
    intro M N hM hN a b
    unfold matMul
    exact Finset.sum_nonneg fun k _ => mul_nonneg (hM a k) (hN k b)
  have hAU : forall a b : Fin n, 0 <= absMatrix n (V start) a b :=
    fun a b => abs_nonneg (V start a b)
  have hAUi : forall a b : Fin n, 0 <= absMatrix n U_inv a b :=
    fun a b => abs_nonneg (U_inv a b)
  exact add_nonneg
    (hmm _ _ hAU (hmm _ _ (hmm _ _ hP hAU) hAUi) i j)
    (hmm _ _ (hmm _ _ hX hAU) hP i j)

/-- Concrete, derived replacement of `X_abs` by the printed inverse-factor
object. No target-shaped bridge is assumed. -/
theorem ch14ext_cor147_gjeXabs_le_printed_add_correction
    (n : Nat) (fp : FPModel)
    (V : Nat -> Fin n -> Fin n -> Real) (start : Nat)
    (U_inv : Fin n -> Fin n -> Real)
    (hLUlower : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0))
    (hUinv : IsRightInverse n (V start) U_inv)
    (i j : Fin n) :
    ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
        (ch14ext_gjeConstructedQ n V start) start (n - 1) i j <=
      matMul n (absMatrix n (V start)) (absMatrix n U_inv) i j +
        gje_c₃ fp n *
          ch14ext_cor147ConcreteXResidualCorrection n V start U_inv i j := by
  let P := gje_cumulative_product n (ch14ext_gjeSeqStages n V)
    start (start + (n - 1))
  let P_abs := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  let Q := ch14ext_gjeConstructedQ n V start
  let X_abs := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V) Q start (n - 1)
  let AU := absMatrix n (V start)
  let AU_inv := absMatrix n U_inv
  let c := gje_c₃ fp n
  have hc : 0 <= c := by
    exact gje_c3_nonneg fp n hnpos h3
  have hUpper : forall t : Nat, t <= n - 1 ->
      forall a b : Fin n, b.val < a.val -> V (start + t) a b = 0 :=
    ch14ext_gjeSeq_upper_triangular fp n V start hidx hLUlower hVrec hpiv
  have hPeq : forall a b : Fin n, P_abs a b = |P a b| := by
    intro a b
    simpa [P_abs, P] using
      ch14ext_gje_absCumProd_eq_abs_signed n V start (n - 1) hidx hUpper a b
  have hAccum := ch14ext_gjeConcrete_matrixAccumulation fp n V start
    hnpos h3 hidx hVrec hpiv
  have hResidual : forall a b : Fin n,
      |idMatrix n a b - matMul n P (V start) a b| <=
        c * matMul n P_abs AU a b := by
    intro a b
    have h := hAccum a b
    rw [hVfinal] at h
    simpa [P, P_abs, AU, c, ch14ext_boundObj] using h
  have hPcompare : forall a b : Fin n,
      P_abs a b <= AU_inv a b +
        c * matMul n (matMul n P_abs AU) AU_inv a b := by
    intro a b
    simpa [AU_inv] using
      ch14ext_abs_signed_le_abs_rightInverse_add n P P_abs (V start) U_inv c
        hPeq hUinv hResidual a b
  have hQP : matMul n Q P = idMatrix n := by
    simpa [Q, P] using ch14ext_gjeConstructedQ_isLeftInverse n V start hidx
  have hQcompare : forall a b : Fin n,
      |Q a b| <= AU a b + c * matMul n X_abs AU a b := by
    intro a b
    have h := ch14ext_abs_leftInverse_le_abs_factor_add
      n Q P P_abs (V start) c hQP hResidual a b
    simpa [AU, X_abs, Q, ch14ext_gjeXabs] using h
  have hXfirst :
      X_abs i j <= matMul n AU P_abs i j +
        c * matMul n (matMul n X_abs AU) P_abs i j := by
    unfold X_abs ch14ext_gjeXabs matMul absMatrix
    calc
      Finset.sum Finset.univ
          (fun k : Fin n => |Q i k| * P_abs k j) <=
          Finset.sum Finset.univ
            (fun k : Fin n =>
              (AU i k + c * matMul n X_abs AU i k) * P_abs k j) := by
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_right (hQcompare i k)
        exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n V)
          start (start + (n - 1)) k j
      _ = matMul n AU P_abs i j +
          c * matMul n (matMul n X_abs AU) P_abs i j := by
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        unfold matMul
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  have hAU_P : matMul n AU P_abs i j <=
      matMul n AU AU_inv i j +
        c * matMul n AU (matMul n (matMul n P_abs AU) AU_inv) i j := by
    unfold matMul
    calc
      Finset.sum Finset.univ (fun k : Fin n => AU i k * P_abs k j) <=
          Finset.sum Finset.univ
            (fun k : Fin n =>
              AU i k * (AU_inv k j +
                c * matMul n (matMul n P_abs AU) AU_inv k j)) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hPcompare k j) (abs_nonneg _)
      _ = Finset.sum Finset.univ (fun k : Fin n => AU i k * AU_inv k j) +
          c * Finset.sum Finset.univ
            (fun k : Fin n =>
              AU i k * matMul n (matMul n P_abs AU) AU_inv k j) := by
        simp only [mul_add, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
  unfold ch14ext_cor147ConcreteXResidualCorrection
  change X_abs i j <= matMul n AU AU_inv i j +
    c * (matMul n AU (matMul n (matMul n P_abs AU) AU_inv) i j +
      matMul n (matMul n X_abs AU) P_abs i j)
  nlinarith [hXfirst, hAU_P]

/-- The concrete residual source object is the printed inverse-factor object
plus a correction derived from the actual GJE accumulation identities. -/
theorem ch14ext_cor147_gjeResidualS2_le_printed_add_concrete
    (n : Nat) (fp : FPModel)
    (L_hat U_inv : Fin n -> Fin n -> Real) (x_hat : Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real) (start : Nat)
    (hLUlower : forall i j : Fin n, j.val < i.val -> V start i j = 0)
    (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0))
    (hUinv : IsRightInverse n (V start) U_inv)
    (i : Fin n) :
    ch14ext_gjeResidualS2 n L_hat
        (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
          (ch14ext_gjeConstructedQ n V start) start (n - 1))
        (V start) x_hat i <=
      ch14ext_gjeResidualS2 n L_hat
          (matMul n (absMatrix n (V start)) (absMatrix n U_inv))
          (V start) x_hat i +
        gje_c₃ fp n * ch14ext_cor147ResidualBridgeTerm n L_hat
          (ch14ext_cor147ConcreteXResidualCorrection n V start U_inv)
          (V start) x_hat i := by
  let U_hat := V start
  let X := ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
    (ch14ext_gjeConstructedQ n V start) start (n - 1)
  let B := matMul n (absMatrix n U_hat) (absMatrix n U_inv)
  let R := ch14ext_cor147ConcreteXResidualCorrection n V start U_inv
  let c := gje_c₃ fp n
  let w := matMulVec n (absMatrix n U_hat) (absVec n x_hat)
  have hX : forall a j : Fin n, 0 <= X a j := by
    intro a j
    exact ch14ext_gjeXabs_nonneg n (ch14ext_gjeSeqStages n V)
      (ch14ext_gjeConstructedQ n V start) start (n - 1) a j
  have hB : forall a j : Fin n, 0 <= B a j := by
    intro a j
    exact ch14ext_cor147_absProduct_nonneg n U_hat U_inv a j
  have hR : forall a j : Fin n, 0 <= R a j := by
    intro a j
    exact ch14ext_cor147ConcreteXResidualCorrection_nonneg
      n V start U_inv a j
  have hw : forall j : Fin n, 0 <= w j := by
    intro j
    exact ch14ext_absMatrix_action_nonneg n U_hat (absVec n x_hat)
      (fun k => abs_nonneg (x_hat k)) j
  have hXabs : absMatrix n X = X := by
    funext a j
    exact abs_of_nonneg (hX a j)
  have hBabs : absMatrix n B = B := by
    funext a j
    exact abs_of_nonneg (hB a j)
  have hinner : forall a : Fin n,
      matMulVec n X w a <=
        matMulVec n B w a + c * matMulVec n R w a := by
    intro a
    calc
      matMulVec n X w a <=
          matMulVec n (fun p q => B p q + c * R p q) w a := by
        unfold matMulVec
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (hw j)
        simpa [X, B, R, U_hat, c] using
          ch14ext_cor147_gjeXabs_le_printed_add_correction
            n fp V start U_inv hLUlower hnpos h3 hidx hVfinal hVrec hpiv
              hUinv a j
      _ = matMulVec n B w a + c * matMulVec n R w a := by
        unfold matMulVec
        simp only [add_mul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have houter := ch14ext_matMulVec_mono_nonneg n (absMatrix n L_hat)
    (matMulVec n X w)
    (fun a => matMulVec n B w a + c * matMulVec n R w a)
    (fun a j => abs_nonneg (L_hat a j)) hinner i
  have hlinear :
      matMulVec n (absMatrix n L_hat)
          (fun a => matMulVec n B w a + c * matMulVec n R w a) i =
        matMulVec n (absMatrix n L_hat) (matMulVec n B w) i +
          c * matMulVec n (absMatrix n L_hat) (matMulVec n R w) i := by
    unfold matMulVec
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  unfold ch14ext_gjeResidualS2
  change matMulVec n (absMatrix n L_hat)
      (matMulVec n (absMatrix n X) w) i <= _
  rw [hXabs, hBabs]
  unfold ch14ext_cor147ResidualBridgeTerm
  change matMulVec n (absMatrix n L_hat) (matMulVec n X w) i <=
    matMulVec n (absMatrix n L_hat) (matMulVec n B w) i +
      c * matMulVec n (absMatrix n L_hat) (matMulVec n R w) i
  rw [hlinear] at houter
  exact houter

/-- Algebraic identification of the printed residual comparison object. -/
theorem ch14ext_cor147_residualS2_printed_eq (n : Nat)
    (L_hat U_hat U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real) (i : Fin n) :
    ch14ext_gjeResidualS2 n L_hat
        (matMul n (absMatrix n U_hat) (absMatrix n U_inv))
        U_hat x_hat i =
      matMulVec n
        (matMul n
          (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
          (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
        (absVec n x_hat) i := by
  let B := matMul n (absMatrix n U_hat) (absMatrix n U_inv)
  have hB : forall a j : Fin n, 0 <= B a j := by
    intro a j
    exact ch14ext_cor147_absProduct_nonneg n U_hat U_inv a j
  have hBabs : absMatrix n B = B := by
    funext a j
    exact abs_of_nonneg (hB a j)
  unfold ch14ext_gjeResidualS2
  change matMulVec n (absMatrix n L_hat)
      (matMulVec n (absMatrix n B)
        (matMulVec n (absMatrix n U_hat) (absVec n x_hat))) i = _
  rw [hBabs]
  dsimp [B]
  have hleft :
      matMulVec n (matMul n (absMatrix n U_hat) (absMatrix n U_inv))
          (matMulVec n (absMatrix n U_hat) (absVec n x_hat)) =
        matMulVec n (absMatrix n U_hat)
          (matMulVec n (absMatrix n U_inv)
            (matMulVec n (absMatrix n U_hat) (absVec n x_hat))) := by
    funext a
    exact matMulVec_matMul n (absMatrix n U_hat) (absMatrix n U_inv)
      (matMulVec n (absMatrix n U_hat) (absVec n x_hat)) a
  have hright :
      matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
          (absVec n x_hat) =
        matMulVec n (absMatrix n U_inv)
          (matMulVec n (absMatrix n U_hat) (absVec n x_hat)) := by
    funext a
    exact matMulVec_matMul n (absMatrix n U_inv) (absMatrix n U_hat)
      (absVec n x_hat) a
  rw [hleft]
  simp only [matMulVec_matMul]
  rw [hright]

/-- The Corollary 14.7 reducer applied to the pure leading residual object.
This is a reusable algebraic consequence, not a residual hypothesis. -/
theorem ch14ext_cor147_residual_leading_object_le
    (n : Nat) (fp : FPModel)
    (A L_hat U_hat U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real)
    (hFact : LUFactSpec n A L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (i : Fin n) :
    8 * (n : Real) * fp.u *
        ch14ext_gjeResidualS2 n L_hat
          (matMul n (absMatrix n U_hat) (absMatrix n U_inv))
          U_hat x_hat i <=
      32 * (n : Real) ^ 2 * fp.u *
        Finset.sum Finset.univ (fun j : Fin n => |A i j|) *
        Finset.sum Finset.univ (fun j : Fin n => |x_hat j|) := by
  let S : Fin n -> Real := fun a =>
    ch14ext_gjeResidualS2 n L_hat
      (matMul n (absMatrix n U_hat) (absMatrix n U_inv))
      U_hat x_hat a
  let bTest : Fin n -> Real := fun a =>
    matMulVec n A x_hat a + 8 * (n : Real) * fp.u * S a
  have hS : forall a : Fin n, 0 <= S a := by
    intro a
    exact ch14ext_gjeResidualS2_nonneg n L_hat
      (matMul n (absMatrix n U_hat) (absMatrix n U_inv))
      U_hat x_hat a
  have hlead : forall a : Fin n,
      0 <= 8 * (n : Real) * fp.u * S a := by
    intro a
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg)
      (hS a)
  have hRes : forall a : Fin n,
      |bTest a - Finset.sum Finset.univ (fun j : Fin n => A a j * x_hat j)| <=
        8 * (n : Real) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) a := by
    intro a
    have hEq := ch14ext_cor147_residualS2_printed_eq
      n L_hat U_hat U_inv x_hat a
    change |bTest a - matMulVec n A x_hat a| <= _
    have hb : bTest a - matMulVec n A x_hat a =
        8 * (n : Real) * fp.u * S a := by
      dsimp [bTest]
      ring
    rw [hb]
    rw [abs_of_nonneg (hlead a)]
    dsimp [S]
    rw [hEq]
  have hBound := ch14ext_cor147_rowwise_residual_printed_of_rowDiagDominantUpper
    n fp A L_hat U_hat U_inv bTest x_hat hFact hURow hUinv hRes i
  change |bTest i - matMulVec n A x_hat i| <= _ at hBound
  have hb : bTest i - matMulVec n A x_hat i =
      8 * (n : Real) * fp.u * S i := by
    dsimp [bTest]
    ring
  rw [hb] at hBound
  rw [abs_of_nonneg (hlead i)] at hBound
  simpa [S] using hBound

/-- Concrete Corollary 14.7 residual endpoint.

The first term is Higham's printed `32 n^2 u` rowwise bound, with the exact
finite-precision LU inflation denominator retained. The next term is the
explicit `X_abs` inverse-envelope correction, and the last term is the
concrete nonnegative remainder from (14.31). This is an exact finite-precision
endpoint, not a claim that the displayed corrections are uniformly `O(u^2)`
along a varying-unit-roundoff family. -/
theorem ch14ext_cor147_concrete_residual
    (n : Nat) (fp : FPModel)
    (A L U L_hat U_inv E : Fin n -> Fin n -> Real)
    (b x_hat : Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (start : Nat)
    (hRow : IsRowDiagDominant n A)
    (hdet : Not (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) = 0))
    (hExactLU : LUFactSpec n A L U)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t))
          ⟨start + t, hidx t ht⟩ (xseq (start + t)))
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0))
    (hUpperErr : forall i j : Fin n,
      |V start i j - U i j| <= fp.u * E i j)
    (hMargin : forall i : Fin n,
      fp.u *
          (E i i +
            Finset.sum (Finset.univ.filter (fun j : Fin n => i.val < j.val))
              (fun j => E i j)) <
        ch14ext_upperRowDiagMargin n U i)
    (hUinv : IsInverse n (V start) U_inv)
    (hguard : 0 < 1 - (2 * (n : Real) - 1) * gamma fp n)
    (i : Fin n) :
    |b i - matMulVec n A x_hat i| <=
      32 * (n : Real) ^ 2 * fp.u *
          ((Finset.sum Finset.univ (fun j : Fin n => |A i j|)) /
            (1 - (2 * (n : Real) - 1) * gamma fp n)) *
          Finset.sum Finset.univ (fun j : Fin n => |x_hat j|) +
        8 * (n : Real) * fp.u * gje_c₃ fp n *
          ch14ext_cor147ResidualBridgeTerm n L_hat
            (ch14ext_cor147ConcreteXResidualCorrection n V start U_inv)
            (V start) x_hat i +
        ch14ext_gjeResidualHigherOrder n fp L_hat
          (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
            (ch14ext_gjeConstructedQ n V start) start (n - 1))
          (V start) (xseq start) x_hat i := by
  have hnDim : 0 < n := Nat.zero_lt_of_lt hnpos
  have hUpper := ch14ext_cor147_concrete_upper_factors_row_dominant
    fp A L U L_hat (V start) E hRow hdet hExactLU hLU hUpperErr hMargin
  have hURow : higham8_8_rowDiagDominantUpper n (V start) := hUpper.2
  let A_hat := ch14ext_cor147ComputedProduct n L_hat (V start)
  have hFact : LUFactSpec n A_hat L_hat (V start) := by
    simpa [A_hat] using
      ch14ext_cor147_computedProduct_luFact n A L_hat (V start)
        (gamma fp n) hLU
  have hLeadAhat := ch14ext_cor147_residual_leading_object_le
    n fp A_hat L_hat (V start) U_inv x_hat hFact hURow hUinv i
  have hAhatRow := ch14ext_cor147_computedProduct_rowSum_le_source
    n fp hnDim A L_hat (V start) U_inv hLU hn hURow hUinv hguard i
  have hsx : 0 <= Finset.sum Finset.univ
      (fun j : Fin n => |x_hat j|) := by positivity
  have hcoef : 0 <= 32 * (n : Real) ^ 2 * fp.u := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (sq_nonneg (n : Real))) fp.u_nonneg
  have hrowScaled := mul_le_mul_of_nonneg_right hAhatRow hsx
  have hLeadSource := mul_le_mul_of_nonneg_left hrowScaled hcoef
  have hSbridge := ch14ext_cor147_gjeResidualS2_le_printed_add_concrete
    n fp L_hat U_inv x_hat V start hLU.U_lower_zero hnpos h3 hidx hVfinal
      hVrec hpiv hUinv.2 i
  have h8nu : 0 <= 8 * (n : Real) * fp.u := by
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
  have hSscaled := mul_le_mul_of_nonneg_left hSbridge h8nu
  have hConcrete := ch14ext_gjeConcrete_overall_residual_14_31
    n fp A L_hat b x_hat V xseq start hLU hn hnpos h3 hidx hVfinal
      hxfinal hyStart hVrec hxrec hpiv i
  calc
    |b i - matMulVec n A x_hat i| <=
        8 * (n : Real) * fp.u *
            ch14ext_gjeResidualS2 n L_hat
              (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
                (ch14ext_gjeConstructedQ n V start) start (n - 1))
              (V start) x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) (xseq start) x_hat i := hConcrete
    _ <= 8 * (n : Real) * fp.u *
            (ch14ext_gjeResidualS2 n L_hat
                (matMul n (absMatrix n (V start)) (absMatrix n U_inv))
                (V start) x_hat i +
              gje_c₃ fp n * ch14ext_cor147ResidualBridgeTerm n L_hat
                (ch14ext_cor147ConcreteXResidualCorrection n V start U_inv)
                (V start) x_hat i) +
          ch14ext_gjeResidualHigherOrder n fp L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) (xseq start) x_hat i := by
      linarith
    _ = 8 * (n : Real) * fp.u *
            ch14ext_gjeResidualS2 n L_hat
              (matMul n (absMatrix n (V start)) (absMatrix n U_inv))
              (V start) x_hat i +
          8 * (n : Real) * fp.u * gje_c₃ fp n *
            ch14ext_cor147ResidualBridgeTerm n L_hat
              (ch14ext_cor147ConcreteXResidualCorrection n V start U_inv)
              (V start) x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) (xseq start) x_hat i := by ring
    _ <= 32 * (n : Real) ^ 2 * fp.u *
            Finset.sum Finset.univ (fun j : Fin n => |A_hat i j|) *
            Finset.sum Finset.univ (fun j : Fin n => |x_hat j|) +
          8 * (n : Real) * fp.u * gje_c₃ fp n *
            ch14ext_cor147ResidualBridgeTerm n L_hat
              (ch14ext_cor147ConcreteXResidualCorrection n V start U_inv)
              (V start) x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) (xseq start) x_hat i := by
      linarith
    _ <= 32 * (n : Real) ^ 2 * fp.u *
            ((Finset.sum Finset.univ (fun j : Fin n => |A i j|)) /
              (1 - (2 * (n : Real) - 1) * gamma fp n)) *
            Finset.sum Finset.univ (fun j : Fin n => |x_hat j|) +
          8 * (n : Real) * fp.u * gje_c₃ fp n *
            ch14ext_cor147ResidualBridgeTerm n L_hat
              (ch14ext_cor147ConcreteXResidualCorrection n V start U_inv)
              (V start) x_hat i +
          ch14ext_gjeResidualHigherOrder n fp L_hat
            (ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
              (ch14ext_gjeConstructedQ n V start) start (n - 1))
            (V start) (xseq start) x_hat i := by
      linarith

/-- Norm bound for the two printed first-order objects in (14.32).

This isolates only the leading algebra. The concrete (14.32) remainder is
added by the endpoint theorem below. -/
theorem ch14ext_cor147_forward_leading_infNorm_le
    (n : Nat) (fp : FPModel) (hnDim : 0 < n)
    (A A_inv L_hat U_hat U_inv : Fin n -> Fin n -> Real)
    (x_hat : Fin n -> Real)
    (hFact : LUFactSpec n
      (ch14ext_cor147ComputedProduct n L_hat U_hat) L_hat U_hat)
    (hURow : higham8_8_rowDiagDominantUpper n U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (delta : Real) (hdelta : 0 < delta)
    (hAhatNorm :
      infNorm (ch14ext_cor147ComputedProduct n L_hat U_hat) <=
        infNorm A / delta) :
    infNormVec (fun i : Fin n =>
      2 * (n : Real) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat U_hat x_hat i +
        6 * (n : Real) * fp.u *
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U_hat x_hat i) <=
      4 * (n : Real) ^ 3 * fp.u *
        (kappaInf n hnDim A A_inv / delta + 3) * infNormVec x_hat := by
  let A_hat := ch14ext_cor147ComputedProduct n L_hat U_hat
  let MLU := matMul n (absMatrix n L_hat) (absMatrix n U_hat)
  let M1 := matMul n (absMatrix n A_inv) MLU
  let M2 := matMul n (absMatrix n U_inv) (absMatrix n U_hat)
  let s := infNormVec x_hat
  let kap := kappaInf n hnDim A A_inv
  let c : Real := 2 * (n : Real) - 1
  have hnOne : (1 : Real) <= (n : Real) := Nat.one_le_cast.mpr hnDim
  have hc : 0 <= c := by dsimp [c]; linarith
  have hs : 0 <= s := infNormVec_nonneg x_hat
  have hkap : 0 <= kap := kappaInf_nonneg n hnDim A A_inv
  have hkapEq : kap = infNorm A * infNorm A_inv :=
    kappaInf_eq_infNorm_mul_infNorm n hnDim A A_inv
  have hM2 : infNorm M2 <= c := by
    simpa [M2, c] using
      ch14ext_cor147_condU_infNorm_le n hnDim U_hat U_inv hURow hUinv
  have hMLU0 : infNorm MLU <= c * infNorm A_hat := by
    simpa [MLU, A_hat, c] using
      ch14ext_cor147_absLU_infNorm_le n hnDim A_hat L_hat U_hat hFact hURow
  have hMLU : infNorm MLU <= c * (infNorm A / delta) :=
    le_trans hMLU0 (mul_le_mul_of_nonneg_left hAhatNorm hc)
  have hM1 : infNorm M1 <= c * (kap / delta) := by
    calc
      infNorm M1 <= infNorm (absMatrix n A_inv) * infNorm MLU :=
        infNorm_matMul_le hnDim _ _
      _ = infNorm A_inv * infNorm MLU := by
        rw [infNorm_absMatrix hnDim A_inv]
      _ <= infNorm A_inv * (c * (infNorm A / delta)) :=
        mul_le_mul_of_nonneg_left hMLU (infNorm_nonneg A_inv)
      _ = c * (kap / delta) := by
        rw [hkapEq]
        field_simp [ne_of_gt hdelta]
  have hMV : forall (M : Fin n -> Fin n -> Real) (i : Fin n),
      matMulVec n M (absVec n x_hat) i <= infNorm M * s := by
    intro M i
    calc
      matMulVec n M (absVec n x_hat) i <=
          |matMulVec n M (absVec n x_hat) i| := le_abs_self _
      _ <= infNormVec (matMulVec n M (absVec n x_hat)) :=
        abs_le_infNormVec _ i
      _ <= infNorm M * infNormVec (absVec n x_hat) :=
        infNormVec_matMulVec_le hnDim M _
      _ = infNorm M * s := by rw [infNormVec_absVec hnDim x_hat]
  have hT1 : forall i : Fin n,
      ch14ext_gjeForwardT1 n A_inv L_hat U_hat x_hat i =
        matMulVec n M1 (absVec n x_hat) i := by
    intro i
    calc
      ch14ext_gjeForwardT1 n A_inv L_hat U_hat x_hat i =
          matMulVec n (absMatrix n A_inv)
            (matMulVec n (absMatrix n L_hat)
              (matMulVec n (absMatrix n U_hat) (absVec n x_hat))) i := rfl
      _ = matMulVec n (absMatrix n A_inv)
          (matMulVec n MLU (absVec n x_hat)) i := by
        congr 1
        funext a
        exact (matMulVec_matMul n (absMatrix n L_hat) (absMatrix n U_hat)
          (absVec n x_hat) a).symm
      _ = matMulVec n M1 (absVec n x_hat) i := by
        exact (matMulVec_matMul n (absMatrix n A_inv) MLU
          (absVec n x_hat) i).symm
  have hT2 : forall i : Fin n,
      ch14ext_gjeForwardT2 n (absMatrix n U_inv) U_hat x_hat i =
        matMulVec n M2 (absVec n x_hat) i := by
    intro i
    unfold ch14ext_gjeForwardT2
    dsimp [M2]
    rw [matMulVec_matMul]
  have hlead : forall i : Fin n,
      2 * (n : Real) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat U_hat x_hat i +
        6 * (n : Real) * fp.u *
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U_hat x_hat i <=
        2 * (n : Real) * fp.u * c * (kap / delta + 3) * s := by
    intro i
    have hm1 : matMulVec n M1 (absVec n x_hat) i <=
        c * (kap / delta) * s := by
      exact le_trans (hMV M1 i) (mul_le_mul_of_nonneg_right hM1 hs)
    have hm2 : matMulVec n M2 (absVec n x_hat) i <= c * s := by
      exact le_trans (hMV M2 i) (mul_le_mul_of_nonneg_right hM2 hs)
    have h2nu : 0 <= 2 * (n : Real) * fp.u := by
      exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
    rw [hT1 i, hT2 i]
    nlinarith
  have hpoly : 2 * (n : Real) * c <= 4 * (n : Real) ^ 3 := by
    dsimp [c]
    nlinarith [mul_nonneg (show (0 : Real) <= (n : Real) by positivity)
        (sq_nonneg ((n : Real) - 1)),
      mul_nonneg (show (0 : Real) <= (n : Real) by positivity) hc]
  have hscale : 0 <= fp.u * (kap / delta + 3) * s := by
    have hkdiv : 0 <= kap / delta := div_nonneg hkap hdelta.le
    exact mul_nonneg (mul_nonneg fp.u_nonneg (by linarith)) hs
  have hweak :
      2 * (n : Real) * fp.u * c * (kap / delta + 3) * s <=
        4 * (n : Real) ^ 3 * fp.u * (kap / delta + 3) * s := by
    have hL :
        2 * (n : Real) * fp.u * c * (kap / delta + 3) * s =
          (2 * (n : Real) * c) * (fp.u * (kap / delta + 3) * s) := by ring
    have hR :
        4 * (n : Real) ^ 3 * fp.u * (kap / delta + 3) * s =
          (4 * (n : Real) ^ 3) * (fp.u * (kap / delta + 3) * s) := by ring
    rw [hL, hR]
    exact mul_le_mul_of_nonneg_right hpoly hscale
  have htarget : forall i : Fin n,
      2 * (n : Real) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat U_hat x_hat i +
        6 * (n : Real) * fp.u *
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U_hat x_hat i <=
        4 * (n : Real) ^ 3 * fp.u * (kap / delta + 3) * s := by
    intro i
    exact le_trans (hlead i) hweak
  have hleadNonneg : forall i : Fin n,
      0 <= 2 * (n : Real) * fp.u *
          ch14ext_gjeForwardT1 n A_inv L_hat U_hat x_hat i +
        6 * (n : Real) * fp.u *
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U_hat x_hat i := by
    intro i
    have ht1 := ch14ext_gjeForwardT1_nonneg n A_inv L_hat U_hat x_hat i
    have ht2 := ch14ext_gjeForwardT2_nonneg n (absMatrix n U_inv)
      U_hat x_hat i (fun a b => abs_nonneg (U_inv a b))
    have h2nu : 0 <= 2 * (n : Real) * fp.u :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
    have h6nu : 0 <= 6 * (n : Real) * fp.u :=
      mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) fp.u_nonneg
    exact add_nonneg (mul_nonneg h2nu ht1) (mul_nonneg h6nu ht2)
  have htargetNonneg :
      0 <= 4 * (n : Real) ^ 3 * fp.u * (kap / delta + 3) * s := by
    have hkdiv : 0 <= kap / delta := div_nonneg hkap hdelta.le
    have h4n : 0 <= 4 * (n : Real) ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg n) 3)
    have hk3 : 0 <= kap / delta + 3 := by linarith
    exact mul_nonneg (mul_nonneg (mul_nonneg h4n fp.u_nonneg) hk3) hs
  apply infNormVec_le_of_abs_le
  · intro i
    rw [abs_of_nonneg (hleadNonneg i)]
    simpa [kap, s] using htarget i
  · simpa [kap, s] using htargetNonneg

/-- Concrete Corollary 14.7 forward endpoint.

The first numerator term is the printed leading norm reduction with the
finite LU inflation denominator retained. The second is exactly the infinity
norm of the literal (14.32) remainder. This theorem does not call that term
`O(u^2)`; such a label requires a separate, uniform vanishing-roundoff family
argument. -/
theorem ch14ext_cor147_concrete_forward
    (n : Nat) (fp : FPModel)
    (A A_inv L U L_hat U_inv E : Fin n -> Fin n -> Real)
    (b x z x_hat : Fin n -> Real)
    (V : Nat -> Fin n -> Fin n -> Real)
    (xseq : Nat -> Fin n -> Real) (start : Nat)
    (hRow : IsRowDiagDominant n A)
    (hdet : Not (Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) Real) = 0))
    (hExactLU : LUFactSpec n A L U)
    (hLU : LUBackwardError n A L_hat (V start) (gamma fp n))
    (hAinv : IsLeftInverse n A A_inv)
    (hUinv : IsInverse n (V start) U_inv)
    (hn : gammaValid fp n) (hnpos : 1 <= n) (h3 : gammaValid fp 3)
    (hidx : forall t : Nat, t < n - 1 -> start + t < n)
    (hVfinal : V (start + (n - 1)) = idMatrix n)
    (hxfinal : forall i : Fin n, x_hat i = xseq (start + (n - 1)) i)
    (hyStart : xseq start = fl_forwardSub fp n L_hat b)
    (hExact : forall i : Fin n, matMulVec n A x i = b i)
    (hUz : forall i : Fin n, matMulVec n (V start) z i = xseq start i)
    (hVrec : forall t : Nat, (ht : t < n - 1) ->
      V (start + (t + 1)) =
        ch14ext_gjeStepMatrix fp n (V (start + t))
          ⟨start + t, hidx t ht⟩)
    (hxrec : forall t : Nat, (ht : t < n - 1) ->
      xseq (start + (t + 1)) =
        ch14ext_gjeStepVec fp n (V (start + t))
          ⟨start + t, hidx t ht⟩ (xseq (start + t)))
    (hpiv : forall t : Nat, (ht : t < n - 1) ->
      Not (V (start + t) ⟨start + t, hidx t ht⟩
        ⟨start + t, hidx t ht⟩ = 0))
    (hUpperErr : forall i j : Fin n,
      |V start i j - U i j| <= fp.u * E i j)
    (hMargin : forall i : Fin n,
      fp.u *
          (E i i +
            Finset.sum (Finset.univ.filter (fun j : Fin n => i.val < j.val))
              (fun j => E i j)) <
        ch14ext_upperRowDiagMargin n U i)
    (hguard : 0 < 1 - (2 * (n : Real) - 1) * gamma fp n)
    (hxpos : 0 < infNormVec x) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x <=
      (4 * (n : Real) ^ 3 * fp.u *
          (kappaInf n (Nat.zero_lt_of_lt hnpos) A A_inv /
              (1 - (2 * (n : Real) - 1) * gamma fp n) + 3) *
          infNormVec x_hat +
        infNormVec (fun i : Fin n =>
          ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L_hat (V start)
            (ch14ext_absCumProd n (ch14ext_gjeSeqStages n V)
              start (n - 1))
            U_inv z (xseq start) x_hat i)) /
        infNormVec x := by
  have hnDim : 0 < n := Nat.zero_lt_of_lt hnpos
  let delta : Real := 1 - (2 * (n : Real) - 1) * gamma fp n
  have hdelta : 0 < delta := by simpa [delta] using hguard
  have hUpper := ch14ext_cor147_concrete_upper_factors_row_dominant
    fp A L U L_hat (V start) E hRow hdet hExactLU hLU hUpperErr hMargin
  have hURow : higham8_8_rowDiagDominantUpper n (V start) := hUpper.2
  have hFact : LUFactSpec n
      (ch14ext_cor147ComputedProduct n L_hat (V start)) L_hat (V start) :=
    ch14ext_cor147_computedProduct_luFact n A L_hat (V start) (gamma fp n) hLU
  have hAhatNorm := ch14ext_cor147_computedProduct_infNorm_le_source
    n fp hnDim A L_hat (V start) U_inv hLU hn hURow hUinv hguard
  have hLeadNorm := ch14ext_cor147_forward_leading_infNorm_le
    n fp hnDim A A_inv L_hat (V start) U_inv x_hat hFact hURow hUinv
      delta hdelta (by simpa [delta] using hAhatNorm)
  let X := ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1)
  let Lead : Fin n -> Real := fun i =>
    2 * (n : Real) * fp.u *
        ch14ext_gjeForwardT1 n A_inv L_hat (V start) x_hat i +
      6 * (n : Real) * fp.u *
        ch14ext_gjeForwardT2 n (absMatrix n U_inv) (V start) x_hat i
  let Rem : Fin n -> Real := fun i =>
    ch14ext_gjeForwardLiteralHigherOrder n fp A_inv L_hat (V start)
      X U_inv z (xseq start) x_hat i
  have hX : forall a j : Fin n, 0 <= X a j := by
    intro a j
    exact gje_cumulative_product_abs_nonneg n (ch14ext_gjeSeqStages n V)
      start (start + (n - 1)) a j
  have hRem : forall i : Fin n, 0 <= Rem i := by
    intro i
    exact ch14ext_gjeForwardLiteralHigherOrder_nonneg n fp A_inv L_hat
      (V start) X U_inv z (xseq start) x_hat i hX hn hnpos h3
  have hConcrete : forall i : Fin n,
      |x i - x_hat i| <= Lead i + Rem i := by
    intro i
    simpa [Lead, Rem, X] using
      ch14ext_gjeConcrete_overall_forward_error_14_32
        n fp A A_inv L_hat U_inv b x z x_hat V xseq start hLU hAinv hUinv.2
          hn hnpos h3 hidx hVfinal hxfinal hyStart hExact hUz hVrec hxrec hpiv i
  have hLeadNorm' : infNormVec Lead <=
      4 * (n : Real) ^ 3 * fp.u *
        (kappaInf n hnDim A A_inv / delta + 3) * infNormVec x_hat := by
    simpa [Lead] using hLeadNorm
  have hstep : forall i : Fin n,
      |x i - x_hat i| <=
        4 * (n : Real) ^ 3 * fp.u *
            (kappaInf n hnDim A A_inv / delta + 3) * infNormVec x_hat +
          infNormVec Rem := by
    intro i
    have hLeadCoord : Lead i <=
        4 * (n : Real) ^ 3 * fp.u *
          (kappaInf n hnDim A A_inv / delta + 3) * infNormVec x_hat := by
      exact le_trans (le_trans (le_abs_self (Lead i)) (abs_le_infNormVec Lead i))
        hLeadNorm'
    have hRemCoord : Rem i <= infNormVec Rem := by
      rw [← abs_of_nonneg (hRem i)]
      exact abs_le_infNormVec Rem i
    linarith [hConcrete i]
  have hkap : 0 <= kappaInf n hnDim A A_inv :=
    kappaInf_nonneg n hnDim A A_inv
  have hLeadRhs : 0 <=
      4 * (n : Real) ^ 3 * fp.u *
        (kappaInf n hnDim A A_inv / delta + 3) * infNormVec x_hat := by
    have hkdiv : 0 <= kappaInf n hnDim A A_inv / delta :=
      div_nonneg hkap hdelta.le
    have h4n : 0 <= 4 * (n : Real) ^ 3 :=
      mul_nonneg (by norm_num) (pow_nonneg (Nat.cast_nonneg n) 3)
    have hk3 : 0 <= kappaInf n hnDim A A_inv / delta + 3 := by linarith
    exact mul_nonneg
      (mul_nonneg (mul_nonneg h4n fp.u_nonneg) hk3)
      (infNormVec_nonneg x_hat)
  have hnorm : infNormVec (fun i : Fin n => x i - x_hat i) <=
      4 * (n : Real) ^ 3 * fp.u *
          (kappaInf n hnDim A A_inv / delta + 3) * infNormVec x_hat +
        infNormVec Rem := by
    apply infNormVec_le_of_abs_le
    · exact hstep
    · exact add_nonneg hLeadRhs (infNormVec_nonneg Rem)
  have hdiv := div_le_div_of_nonneg_right hnorm hxpos.le
  simpa [Rem, X, delta] using hdiv

end NumStability.Ch14Ext
