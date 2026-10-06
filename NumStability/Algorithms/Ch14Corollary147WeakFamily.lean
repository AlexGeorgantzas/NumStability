/-
Copyright (c) 2026 NumStability contributors. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
-/
import NumStability.Algorithms.Ch14Corollary147Concrete
import NumStability.Algorithms.Ch14AsymptoticFamilies
import NumStability.Algorithms.Ch14Corollary147Closure
import NumStability.Algorithms.Ch14GJEAsymptoticFamilies

/-!
# Corollary 14.7 for weak row dominance along a precision family

Weak row diagonal dominance is not open, so this file never claims that every
rounded upper factor is row diagonally dominant. Instead, the printed leading
bounds are reduced with the exact row-dominant upper factor supplied by exact
no-pivot LU. A successful-run family contract records `O(u)` consistency of
the computed factors and of the accumulated `X_abs` state. Those are state
properties, not residual or forward-error conclusions.

The exact inverse identity derives the computed-inverse proximity; it is not a
separate contract field. Finite-dimensional product calculus then proves that
the computed and exact leading objects differ by `O(u)`. Multiplication by the
leading unit-roundoff factor makes this contribution `O(u^2)`.
-/

namespace NumStability.Ch14Ext

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

/-! ## Varying finite-dimensional product calculus -/

/-- Entrywise `O(g)` control of a matrix family. -/
def Ch14MatrixFamilyIsBigO {ι : Type*} (l : Filter ι) {m n : Nat}
    (M : ι -> Fin m -> Fin n -> Real) (g : ι -> Real) : Prop :=
  forall i j, (fun t => M t i j) =O[l] g

/-- Componentwise `O(g)` control of a vector family. -/
def Ch14VectorFamilyIsBigO {ι : Type*} (l : Filter ι) {n : Nat}
    (v : ι -> Fin n -> Real) (g : ι -> Real) : Prop :=
  forall i, (fun t => v t i) =O[l] g

theorem ch14ext_fixedMatrix_isBigOOne {ι : Type*} {l : Filter ι}
    {m n : Nat} (A : Fin m -> Fin n -> Real) :
    MatrixFamilyIsBigOOne l (fun _ : ι => A) := by
  intro i j
  exact Asymptotics.isBigO_const_const (A i j) one_ne_zero l

theorem ch14ext_fixedVector_isBigOOne {ι : Type*} {l : Filter ι}
    {n : Nat} (x : Fin n -> Real) :
    VectorFamilyIsBigOOne l (fun _ : ι => x) := by
  intro i
  exact Asymptotics.isBigO_const_const (x i) one_ne_zero l

theorem ch14ext_matrixFamily_mul_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M N : ι -> Fin n -> Fin n -> Real} {f g : ι -> Real}
    (hM : Ch14MatrixFamilyIsBigO l M f)
    (hN : Ch14MatrixFamilyIsBigO l N g) :
    Ch14MatrixFamilyIsBigO l (fun t => matMul n (M t) (N t))
      (fun t => f t * g t) := by
  intro i j
  simpa only [matMul] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM i k).mul (hN k j)))

theorem ch14ext_matrixFamily_mul_isBigOOne
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M N : ι -> Fin n -> Fin n -> Real}
    (hM : MatrixFamilyIsBigOOne l M)
    (hN : MatrixFamilyIsBigOOne l N) :
    MatrixFamilyIsBigOOne l (fun t => matMul n (M t) (N t)) := by
  intro i j
  simpa only [matMul, mul_one] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM i k).mul (hN k j)))

theorem ch14ext_matrixVectorFamily_mul_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M : ι -> Fin n -> Fin n -> Real} {x : ι -> Fin n -> Real}
    {f g : ι -> Real}
    (hM : Ch14MatrixFamilyIsBigO l M f)
    (hx : Ch14VectorFamilyIsBigO l x g) :
    Ch14VectorFamilyIsBigO l (fun t => matMulVec n (M t) (x t))
      (fun t => f t * g t) := by
  intro i
  simpa only [matMulVec] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM i k).mul (hx k)))

theorem ch14ext_matrixVectorFamily_mul_isBigOOne
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M : ι -> Fin n -> Fin n -> Real} {x : ι -> Fin n -> Real}
    (hM : MatrixFamilyIsBigOOne l M)
    (hx : VectorFamilyIsBigOOne l x) :
    VectorFamilyIsBigOOne l (fun t => matMulVec n (M t) (x t)) := by
  intro i
  simpa only [matMulVec, mul_one] using
    (Asymptotics.IsBigO.sum (s := Finset.univ) (fun k _ =>
      (hM i k).mul (hx k)))

theorem ch14ext_matrixFamily_absDifference_isBigO
    {ι : Type*} {l : Filter ι} {m n : Nat}
    {M : ι -> Fin m -> Fin n -> Real} (A : Fin m -> Fin n -> Real)
    {u : ι -> Real}
    (hM : Ch14MatrixFamilyIsBigO l (fun t i j => M t i j - A i j) u) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => |M t i j| - |A i j|) u := by
  intro i j
  have hdom : (fun t => |M t i j| - |A i j|) =O[l]
      (fun t => M t i j - A i j) := by
    apply Asymptotics.IsBigO.of_bound'
    filter_upwards [] with t
    simpa only [Real.norm_eq_abs] using
      abs_abs_sub_abs_le_abs_sub (M t i j) (A i j)
  exact hdom.trans (hM i j)

theorem ch14ext_matrixFamily_productDifference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M N : ι -> Fin n -> Fin n -> Real}
    (A B : Fin n -> Fin n -> Real) {u : ι -> Real}
    (hMdiff : Ch14MatrixFamilyIsBigO l (fun t i j => M t i j - A i j) u)
    (hNdiff : Ch14MatrixFamilyIsBigO l (fun t i j => N t i j - B i j) u)
    (hN : MatrixFamilyIsBigOOne l N) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => matMul n (M t) (N t) i j - matMul n A B i j) u := by
  intro i j
  have hsum :
      (fun t => Finset.sum Finset.univ (fun k : Fin n =>
        (M t i k - A i k) * N t k j + A i k * (N t k j - B k j)))
        =O[l] u := by
    apply Asymptotics.IsBigO.sum
    intro k _
    have h1 : (fun t => (M t i k - A i k) * N t k j) =O[l] u := by
      simpa only [mul_one] using (hMdiff i k).mul (hN k j)
    have h2 : (fun t => A i k * (N t k j - B k j)) =O[l] u :=
      (hNdiff k j).const_mul_left (A i k)
    exact h1.add h2
  convert hsum using 1
  funext t
  unfold matMul
  change (∑ k : Fin n, M t i k * N t k j) -
      (∑ k : Fin n, A i k * B k j) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ch14ext_matrixVectorFamily_actionDifference_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {M : ι -> Fin n -> Fin n -> Real} (A : Fin n -> Fin n -> Real)
    {x : ι -> Fin n -> Real} {u : ι -> Real}
    (hMdiff : Ch14MatrixFamilyIsBigO l (fun t i j => M t i j - A i j) u)
    (hx : VectorFamilyIsBigOOne l x) :
    Ch14VectorFamilyIsBigO l
      (fun t i => matMulVec n (M t) (x t) i - matMulVec n A (x t) i) u := by
  intro i
  have hsum :
      (fun t => Finset.sum Finset.univ
        (fun k : Fin n => (M t i k - A i k) * x t k)) =O[l] u := by
    apply Asymptotics.IsBigO.sum
    intro k _
    simpa only [mul_one] using (hMdiff i k).mul (hx k)
  convert hsum using 1
  funext t
  unfold matMulVec
  change (∑ k : Fin n, M t i k * x t k) -
      (∑ k : Fin n, A i k * x t k) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem ch14ext_vectorFamily_infNorm_isBigO
    {ι : Type*} {l : Filter ι} {n : Nat}
    {v : ι -> Fin n -> Real} {g : ι -> Real}
    (hv : Ch14VectorFamilyIsBigO l v g) :
    (fun t => infNormVec (v t)) =O[l] g := by
  let total : ι -> Real := fun t => Finset.sum Finset.univ (fun i : Fin n => |v t i|)
  have htotal : total =O[l] g := by
    dsimp [total]
    apply Asymptotics.IsBigO.sum
    intro i _
    simpa only [Real.norm_eq_abs] using (hv i).norm_left
  have hnorm : (fun t => infNormVec (v t)) =O[l] total := by
    apply Asymptotics.IsBigO.of_norm_le
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (infNormVec_nonneg (v t))]
    apply infNormVec_le_of_abs_le
    · intro i
      exact Finset.single_le_sum
        (fun j _ => abs_nonneg (v t j)) (Finset.mem_univ i)
    · exact Finset.sum_nonneg (fun i _ => abs_nonneg (v t i))
  exact hnorm.trans htotal

/-- Simultaneous first-order changes in a matrix and a vector give a
first-order change in their action. The computed vector is assumed locally
bounded; the comparison matrix and vector are fixed. -/
theorem ch14ext_matrixVectorFamily_productDifference_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {M : iota -> Fin n -> Fin n -> Real} (A : Fin n -> Fin n -> Real)
    {x y : iota -> Fin n -> Real} {u : iota -> Real}
    (hMdiff : Ch14MatrixFamilyIsBigO l (fun t i j => M t i j - A i j) u)
    (hxdiff : Ch14VectorFamilyIsBigO l (fun t i => x t i - y t i) u)
    (hx : VectorFamilyIsBigOOne l x) :
    Ch14VectorFamilyIsBigO l
      (fun t i => matMulVec n (M t) (x t) i - matMulVec n A (y t) i) u := by
  intro i
  have hsum :
      (fun t => Finset.sum Finset.univ (fun k : Fin n =>
        (M t i k - A i k) * x t k + A i k * (x t k - y t k))) =O[l] u := by
    apply Asymptotics.IsBigO.sum
    intro k _
    have h1 : (fun t => (M t i k - A i k) * x t k) =O[l] u := by
      simpa only [mul_one] using (hMdiff i k).mul (hx k)
    have h2 : (fun t => A i k * (x t k - y t k)) =O[l] u :=
      (hxdiff k).const_mul_left (A i k)
    exact h1.add h2
  convert hsum using 1
  funext t
  unfold matMulVec
  change (∑ k : Fin n, M t i k * x t k) -
      (∑ k : Fin n, A i k * y t k) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix multiplication distributes over pointwise subtraction in its left
argument. -/
theorem ch14ext_matMul_sub_left (n : Nat)
    (A B C : Fin n -> Fin n -> Real) :
    matMul n (fun i j => A i j - B i j) C =
      fun i j => matMul n A C i j - matMul n B C i j := by
  ext i j
  unfold matMul
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Matrix multiplication distributes over pointwise subtraction in its right
argument. -/
theorem ch14ext_matMul_sub_right (n : Nat)
    (A B C : Fin n -> Fin n -> Real) :
    matMul n A (fun i j => B i j - C i j) =
      fun i j => matMul n A B i j - matMul n A C i j := by
  ext i j
  unfold matMul
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Exact inverse perturbation identity
`Uhat_inv - U_inv = -Uhat_inv (Uhat - U) U_inv`.

Only a left-inverse certificate for the computed pair and a right-inverse
certificate for the exact pair are used. -/
theorem ch14ext_inverseDifference_identity (n : Nat)
    (U_hat U U_hat_inv U_inv : Fin n -> Fin n -> Real)
    (hUhat : IsLeftInverse n U_hat U_hat_inv)
    (hU : IsRightInverse n U U_inv) :
    (fun i j => U_hat_inv i j - U_inv i j) =
      (fun i j => -matMul n
        (matMul n U_hat_inv (fun a b => U_hat a b - U a b)) U_inv i j) := by
  have hleft : matMul n U_hat_inv U_hat = idMatrix n := by
    ext i j
    simpa only [matMul, idMatrix] using hUhat i j
  have hright : matMul n U U_inv = idMatrix n := by
    ext i j
    simpa only [matMul, idMatrix] using hU i j
  have hproduct :
      matMul n (matMul n U_hat_inv (fun a b => U_hat a b - U a b)) U_inv =
        (fun i j => U_inv i j - U_hat_inv i j) := by
    calc
      matMul n (matMul n U_hat_inv (fun a b => U_hat a b - U a b)) U_inv =
          matMul n
            (fun i j => matMul n U_hat_inv U_hat i j -
              matMul n U_hat_inv U i j) U_inv := by
            rw [ch14ext_matMul_sub_right]
      _ = fun i j =>
          matMul n (matMul n U_hat_inv U_hat) U_inv i j -
            matMul n (matMul n U_hat_inv U) U_inv i j :=
        ch14ext_matMul_sub_left n _ _ _
      _ = fun i j =>
          matMul n (matMul n U_hat_inv U_hat) U_inv i j -
            matMul n U_hat_inv (matMul n U U_inv) i j := by
        funext i j
        rw [congrFun (congrFun (matMul_assoc n U_hat_inv U U_inv) i) j]
      _ = fun i j => U_inv i j - U_hat_inv i j := by
        rw [hleft, hright, matMul_id_left, matMul_id_right]
  rw [hproduct]
  funext i j
  ring

/-! ## Successful-run weak-dominance family contract -/

/-- A family of successful concrete GJE executions approaching an exact
no-pivot factorization `A = L U`.

The `X_abs` field is the one transparent consistency contract not presently
derived from the full rounded recurrence: it says that the internal absolute
accumulation state approaches the exact inverse product `|U||U^-1|`. It names
an algorithm state, contains no residual or forward-error expression, and is
therefore not target-shaped. Computed inverse proximity is not assumed; it is
derived below from `upper_proximity` and the exact inverse identity. -/
structure Ch14Cor147WeakFamily
    (iota : Type*) (l : Filter iota) (n : Nat)
    (A L U U_inv : Fin n -> Fin n -> Real)
    (b : Fin n -> Real) (start : Nat) where
  run : Ch14GJEConcreteFamily iota l n A b start
  U_hat_inv : iota -> Fin n -> Fin n -> Real
  z : iota -> Fin n -> Real
  computed_upper_inverse : forall t,
    IsInverse n (run.V t start) (U_hat_inv t)
  exact_lower_proximity : Ch14MatrixFamilyIsBigO l
    (fun t i j => run.L_hat t i j - L i j) (fun t => (run.model t).u)
  exact_upper_proximity : Ch14MatrixFamilyIsBigO l
    (fun t i j => run.V t start i j - U i j) (fun t => (run.model t).u)
  xabs_consistency : Ch14MatrixFamilyIsBigO l
    (fun t i j => ch14ext_gjeConcreteFamilyXabs run t i j -
      matMul n (absMatrix n U) (absMatrix n U_inv) i j)
    (fun t => (run.model t).u)
  U_hat_inv_isBigO_one : MatrixFamilyIsBigOOne l U_hat_inv
  z_isBigO_one : VectorFamilyIsBigOOne l z
  upper_solve : forall t i,
    matMulVec n (run.V t start) (z t) i = run.xseq t start i
  pabs_isBigO_one : MatrixFamilyIsBigOOne l
    (ch14ext_gjeConcreteFamilyPabs run)

/-- The exact inverse identity turns `Uhat-U = O(u)` into
`Uhat^-1-U^-1 = O(u)`. This is why inverse proximity is absent from the family
contract. -/
theorem ch14ext_cor147Weak_inverse_proximity_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hUinv : IsInverse n U U_inv) :
    Ch14MatrixFamilyIsBigO l
      (fun t i j => F.U_hat_inv t i j - U_inv i j)
      (fun t => (F.run.model t).u) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  have hfirst : Ch14MatrixFamilyIsBigO l
      (fun t => matMul n (F.U_hat_inv t)
        (fun i j => F.run.V t start i j - U i j)) unit := by
    have h := ch14ext_matrixFamily_mul_isBigO
      (M := F.U_hat_inv)
      (N := fun t i j => F.run.V t start i j - U i j)
      (f := fun _ : iota => (1 : Real)) (g := unit)
      F.U_hat_inv_isBigO_one F.exact_upper_proximity
    simpa only [one_mul] using h
  have htriple : Ch14MatrixFamilyIsBigO l
      (fun t => matMul n
        (matMul n (F.U_hat_inv t)
          (fun i j => F.run.V t start i j - U i j)) U_inv) unit := by
    have hfixed : Ch14MatrixFamilyIsBigO l
        (fun _ : iota => U_inv) (fun _ : iota => (1 : Real)) :=
      ch14ext_fixedMatrix_isBigOOne U_inv
    have h := ch14ext_matrixFamily_mul_isBigO
      (M := fun t => matMul n (F.U_hat_inv t)
        (fun i j => F.run.V t start i j - U i j))
      (N := fun _ : iota => U_inv) (f := unit)
      (g := fun _ : iota => (1 : Real)) hfirst hfixed
    simpa only [mul_one] using h
  intro i j
  have hneg := (htriple i j).neg_left
  convert hneg using 1
  funext t
  exact congrFun (congrFun
    (ch14ext_inverseDifference_identity n (F.run.V t start) U
      (F.U_hat_inv t) U_inv (F.computed_upper_inverse t).1 hUinv.2) i) j

/-! ## Computed versus exact leading objects -/

/-- Exact absolute inverse product used in the printed residual object. -/
noncomputable def ch14ext_cor147WeakExactX (n : Nat)
    (U U_inv : Fin n -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  matMul n (absMatrix n U) (absMatrix n U_inv)

/-- The concrete residual leading object differs from the exact
row-dominant leading object by `O(u)`. -/
theorem ch14ext_cor147Weak_residualLeading_difference_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeResidualS2 n (F.run.L_hat t)
            (ch14ext_gjeConcreteFamilyXabs F.run t) (F.run.V t start)
            (F.run.x_hat t) i -
          ch14ext_gjeResidualS2 n L
            (ch14ext_cor147WeakExactX n U U_inv) U (F.run.x_hat t) i)
      (fun t => (F.run.model t).u) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  have hxabs : VectorFamilyIsBigOOne l
      (fun t i => |F.run.x_hat t i|) :=
    ch14ext_vectorFamily_abs_isBigOOne F.run.x_hat_isBigO_one
  have hUabsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |F.run.V t start i j|) :=
    matrixFamily_abs_isBigOOne F.run.U_hat_isBigO_one
  have hUabsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j => |F.run.V t start i j| - |U i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO U F.exact_upper_proximity
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.run.V t start i j|)
        (fun i => |F.run.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.run.V t start a j|)
            (fun j => |F.run.x_hat t j|) i -
          matMulVec n (absMatrix n U)
            (fun j => |F.run.x_hat t j|) i) unit := by
    exact ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |F.run.V t start i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hXabsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |ch14ext_gjeConcreteFamilyXabs F.run t i j|) :=
    matrixFamily_abs_isBigOOne F.run.X_abs_isBigO_one
  have hXabsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j =>
        |ch14ext_gjeConcreteFamilyXabs F.run t i j| -
          |ch14ext_cor147WeakExactX n U U_inv i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO
      (ch14ext_cor147WeakExactX n U U_inv) F.xabs_consistency
  have hXactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n
        (fun i j => |ch14ext_gjeConcreteFamilyXabs F.run t i j|)
        (matMulVec n (fun i j => |F.run.V t start i j|)
          (fun i => |F.run.x_hat t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hXabsOne hUactionOne
  have hXactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n
            (fun a j => |ch14ext_gjeConcreteFamilyXabs F.run t a j|)
            (matMulVec n (fun a j => |F.run.V t start a j|)
              (fun j => |F.run.x_hat t j|)) i -
          matMulVec n (absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
            (matMulVec n (absMatrix n U)
              (fun j => |F.run.x_hat t j|)) i) unit := by
    exact ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |ch14ext_gjeConcreteFamilyXabs F.run t i j|)
      (A := absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
      (x := fun t => matMulVec n (fun i j => |F.run.V t start i j|)
        (fun i => |F.run.x_hat t i|))
      (y := fun t => matMulVec n (absMatrix n U)
        (fun i => |F.run.x_hat t i|))
      (by simpa only [absMatrix] using hXabsDiff) hUactionDiff hUactionOne
  have hLabsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |F.run.L_hat t i j|) :=
    matrixFamily_abs_isBigOOne F.run.L_hat_isBigO_one
  have hLabsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j => |F.run.L_hat t i j| - |L i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO L F.exact_lower_proximity
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.run.L_hat t i j|) (A := absMatrix n L)
    (x := fun t => matMulVec n
      (fun i j => |ch14ext_gjeConcreteFamilyXabs F.run t i j|)
      (matMulVec n (fun i j => |F.run.V t start i j|)
        (fun i => |F.run.x_hat t i|)))
    (y := fun t => matMulVec n
      (absMatrix n (ch14ext_cor147WeakExactX n U U_inv))
      (matMulVec n (absMatrix n U) (fun i => |F.run.x_hat t i|)))
    (by simpa only [absMatrix] using hLabsDiff) hXactionDiff hXactionOne
  simpa only [ch14ext_gjeResidualS2, absMatrix, absVec] using hfinal

/-- A fixed matrix preserves a componentwise asymptotic difference between
two vector families. -/
theorem ch14ext_fixedMatrix_vectorDifference_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    (A : Fin n -> Fin n -> Real) {x y : iota -> Fin n -> Real}
    {u : iota -> Real}
    (hxy : Ch14VectorFamilyIsBigO l (fun t i => x t i - y t i) u) :
    Ch14VectorFamilyIsBigO l
      (fun t i => matMulVec n A (x t) i - matMulVec n A (y t) i) u := by
  intro i
  have hsum :
      (fun t => Finset.sum Finset.univ
        (fun k : Fin n => A i k * (x t k - y t k))) =O[l] u := by
    apply Asymptotics.IsBigO.sum
    intro k _
    exact (hxy k).const_mul_left (A i k)
  convert hsum using 1
  funext t
  unfold matMulVec
  change (∑ k : Fin n, A i k * x t k) -
      (∑ k : Fin n, A i k * y t k) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The first forward leading object `T1` changes by `O(u)`. -/
theorem ch14ext_cor147Weak_forwardT1_difference_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A A_inv L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT1 n A_inv (F.run.L_hat t) (F.run.V t start)
            (F.run.x_hat t) i -
          ch14ext_gjeForwardT1 n A_inv L U (F.run.x_hat t) i)
      (fun t => (F.run.model t).u) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  have hxabs : VectorFamilyIsBigOOne l
      (fun t i => |F.run.x_hat t i|) :=
    ch14ext_vectorFamily_abs_isBigOOne F.run.x_hat_isBigO_one
  have hUabsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |F.run.V t start i j|) :=
    matrixFamily_abs_isBigOOne F.run.U_hat_isBigO_one
  have hUabsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j => |F.run.V t start i j| - |U i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO U F.exact_upper_proximity
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.run.V t start i j|)
        (fun i => |F.run.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.run.V t start a j|)
            (fun j => |F.run.x_hat t j|) i -
          matMulVec n (absMatrix n U)
            (fun j => |F.run.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |F.run.V t start i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hLabsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |F.run.L_hat t i j|) :=
    matrixFamily_abs_isBigOOne F.run.L_hat_isBigO_one
  have hLabsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j => |F.run.L_hat t i j| - |L i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO L F.exact_lower_proximity
  have hLactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.run.L_hat t i j|)
        (matMulVec n (fun i j => |F.run.V t start i j|)
          (fun i => |F.run.x_hat t i|))) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hLabsOne hUactionOne
  have hLactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.run.L_hat t a j|)
            (matMulVec n (fun a j => |F.run.V t start a j|)
              (fun j => |F.run.x_hat t j|)) i -
          matMulVec n (absMatrix n L)
            (matMulVec n (absMatrix n U)
              (fun j => |F.run.x_hat t j|)) i) unit :=
    ch14ext_matrixVectorFamily_productDifference_isBigO
      (M := fun t i j => |F.run.L_hat t i j|) (A := absMatrix n L)
      (x := fun t => matMulVec n (fun i j => |F.run.V t start i j|)
        (fun i => |F.run.x_hat t i|))
      (y := fun t => matMulVec n (absMatrix n U)
        (fun i => |F.run.x_hat t i|))
      (by simpa only [absMatrix] using hLabsDiff) hUactionDiff hUactionOne
  have hfinal := ch14ext_fixedMatrix_vectorDifference_isBigO
    (absMatrix n A_inv) hLactionDiff
  simpa only [ch14ext_gjeForwardT1, absMatrix, absVec] using hfinal

/-- The inverse-based forward leading object `T2` changes by `O(u)`. -/
theorem ch14ext_cor147Weak_forwardT2_difference_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.run.V t start) (F.run.x_hat t) i -
          ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
            (F.run.x_hat t) i)
      (fun t => (F.run.model t).u) := by
  let unit : iota -> Real := fun t => (F.run.model t).u
  have hxabs : VectorFamilyIsBigOOne l
      (fun t i => |F.run.x_hat t i|) :=
    ch14ext_vectorFamily_abs_isBigOOne F.run.x_hat_isBigO_one
  have hUabsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |F.run.V t start i j|) :=
    matrixFamily_abs_isBigOOne F.run.U_hat_isBigO_one
  have hUabsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j => |F.run.V t start i j| - |U i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO U F.exact_upper_proximity
  have hUactionOne : VectorFamilyIsBigOOne l
      (fun t => matMulVec n (fun i j => |F.run.V t start i j|)
        (fun i => |F.run.x_hat t i|)) :=
    ch14ext_matrixVectorFamily_mul_isBigOOne hUabsOne hxabs
  have hUactionDiff : Ch14VectorFamilyIsBigO l
      (fun t i =>
        matMulVec n (fun a j => |F.run.V t start a j|)
            (fun j => |F.run.x_hat t j|) i -
          matMulVec n (absMatrix n U)
            (fun j => |F.run.x_hat t j|) i) unit :=
    ch14ext_matrixVectorFamily_actionDifference_isBigO
      (M := fun t i j => |F.run.V t start i j|) (absMatrix n U)
      (by simpa only [absMatrix] using hUabsDiff) hxabs
  have hInvDiff := ch14ext_cor147Weak_inverse_proximity_isBigO F hUinv
  have hInvAbsDiff : Ch14MatrixFamilyIsBigO l
      (fun t i j => |F.U_hat_inv t i j| - |U_inv i j|) unit :=
    ch14ext_matrixFamily_absDifference_isBigO U_inv hInvDiff
  have hInvAbsOne : MatrixFamilyIsBigOOne l
      (fun t i j => |F.U_hat_inv t i j|) :=
    matrixFamily_abs_isBigOOne F.U_hat_inv_isBigO_one
  have hfinal := ch14ext_matrixVectorFamily_productDifference_isBigO
    (M := fun t i j => |F.U_hat_inv t i j|) (A := absMatrix n U_inv)
    (x := fun t => matMulVec n (fun i j => |F.run.V t start i j|)
      (fun i => |F.run.x_hat t i|))
    (y := fun t => matMulVec n (absMatrix n U)
      (fun i => |F.run.x_hat t i|))
    (by simpa only [absMatrix] using hInvAbsDiff) hUactionDiff hUactionOne
  simpa only [ch14ext_gjeForwardT2, absMatrix, absVec] using hfinal

/-- The combined forward core `T1 + 3*T2` changes by `O(u)`. -/
theorem ch14ext_cor147Weak_forwardCore_difference_isBigO
    {iota : Type*} {l : Filter iota} {n : Nat}
    {A A_inv L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (hUinv : IsInverse n U U_inv) :
    Ch14VectorFamilyIsBigO l
      (fun t i =>
        (ch14ext_gjeForwardT1 n A_inv (F.run.L_hat t) (F.run.V t start)
            (F.run.x_hat t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
            (F.run.V t start) (F.run.x_hat t) i) -
        (ch14ext_gjeForwardT1 n A_inv L U (F.run.x_hat t) i +
          3 * ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
            (F.run.x_hat t) i))
      (fun t => (F.run.model t).u) := by
  intro i
  have h1 := ch14ext_cor147Weak_forwardT1_difference_isBigO
    (A_inv := A_inv) F i
  have h2 := ch14ext_cor147Weak_forwardT2_difference_isBigO F hUinv i
  have h := h1.add (h2.const_mul_left (3 : Real))
  convert h using 1
  funext t
  ring

/-! ## Residual endpoint with a genuine quadratic family remainder -/

/-- Exact residual correction after replacing the computed leading object by
the exact row-dominant one. The second summand is the full explicit (14.31)
higher-order expression. -/
noncomputable def ch14ext_cor147WeakResidualRemainder
    {iota : Type*} {l : Filter iota} (n : Nat)
    {A L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (t : iota) (i : Fin n) : Real :=
  8 * (n : Real) * (F.run.model t).u *
      (ch14ext_gjeResidualS2 n (F.run.L_hat t)
          (ch14ext_gjeConcreteFamilyXabs F.run t) (F.run.V t start)
          (F.run.x_hat t) i -
        ch14ext_gjeResidualS2 n L
          (ch14ext_cor147WeakExactX n U U_inv) U (F.run.x_hat t) i) +
    ch14ext_gjeResidualHigherOrder n (F.run.model t) (F.run.L_hat t)
      (ch14ext_gjeConcreteFamilyXabs F.run t) (F.run.V t start)
      (F.run.xseq t start) (F.run.x_hat t) i

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

/-! ## Forward endpoint with a genuine quadratic family remainder -/

/-- Exact vector correction after replacing both computed first-order forward
objects by the corresponding objects formed from the exact factors. -/
noncomputable def ch14ext_cor147WeakForwardVectorRemainder
    {iota : Type*} {l : Filter iota} (n : Nat)
    {A L U U_inv : Fin n -> Fin n -> Real}
    (A_inv : Fin n -> Fin n -> Real) {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (t : iota) (i : Fin n) : Real :=
  (2 * (n : Real) * (F.run.model t).u *
        ch14ext_gjeForwardT1 n A_inv (F.run.L_hat t) (F.run.V t start)
          (F.run.x_hat t) i +
      6 * (n : Real) * (F.run.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n (F.U_hat_inv t))
          (F.run.V t start) (F.run.x_hat t) i) -
    (2 * (n : Real) * (F.run.model t).u *
        ch14ext_gjeForwardT1 n A_inv L U (F.run.x_hat t) i +
      6 * (n : Real) * (F.run.model t).u *
        ch14ext_gjeForwardT2 n (absMatrix n U_inv) U
          (F.run.x_hat t) i) +
    ch14ext_gjeForwardLiteralHigherOrder n (F.run.model t) A_inv
      (F.run.L_hat t) (F.run.V t start)
      (ch14ext_gjeConcreteFamilyPabs F.run t) (F.U_hat_inv t)
      (F.z t) (F.run.xseq t start) (F.run.x_hat t) i

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

/-- Relative infinity-norm form of the explicit forward remainder. -/
noncomputable def ch14ext_cor147WeakForwardRelativeRemainder
    {iota : Type*} {l : Filter iota} (n : Nat)
    {A L U U_inv : Fin n -> Fin n -> Real}
    (A_inv : Fin n -> Fin n -> Real) {b : Fin n -> Real} {start : Nat}
    (x : Fin n -> Real)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (t : iota) : Real :=
  infNormVec (fun i =>
    ch14ext_cor147WeakForwardVectorRemainder n A_inv F t i) / infNormVec x

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

/-! ## Removing the computed-solution norm ratio -/

/-- Triangle inequality in the precise orientation needed to replace
`||x_hat|| / ||x||` by `1 + ||x-x_hat|| / ||x||`. -/
theorem ch14ext_infNormVec_approx_le_exact_add_error {n : Nat}
    (x x_hat : Fin n -> Real) :
    infNormVec x_hat <=
      infNormVec x + infNormVec (fun i => x i - x_hat i) := by
  apply infNormVec_le_of_abs_le
  · intro i
    calc
      |x_hat i| = |x i - (x i - x_hat i)| :=
        congrArg abs (sub_sub_cancel (x i) (x_hat i)).symm
      _ <= |x i| + |x i - x_hat i| := abs_sub _ _
      _ <= infNormVec x + infNormVec (fun j => x j - x_hat j) :=
        add_le_add (abs_le_infNormVec x i)
          (abs_le_infNormVec (fun j => x j - x_hat j) i)
  · exact add_nonneg (infNormVec_nonneg x)
      (infNormVec_nonneg (fun i => x i - x_hat i))

/-- The printed first-order forward coefficient in Corollary 14.7. -/
noncomputable def ch14ext_cor147WeakForwardLeadingCoefficient
    {iota : Type*} {l : Filter iota} (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real) {L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (t : iota) : Real :=
  4 * (n : Real) ^ 3 * (F.run.model t).u *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
      A A_inv + 3)

theorem ch14ext_cor147WeakForwardLeadingCoefficient_tendsto_zero
    {iota : Type*} {l : Filter iota} (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real) {L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start) :
    Tendsto (ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F) l
      (𝓝 0) := by
  let K : Real := 4 * (n : Real) ^ 3 *
    (kappaInf n (lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos)
      A A_inv + 3)
  have h := F.run.unit_tendsto_zero.const_mul K
  convert h using 1
  · funext t
    dsimp [ch14ext_cor147WeakForwardLeadingCoefficient, K]
    ring
  · simp

theorem ch14ext_cor147WeakForwardLeadingCoefficient_nonneg
    {iota : Type*} {l : Filter iota} (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real) {L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat}
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (t : iota) :
    0 <= ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F t := by
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one F.run.dimension_pos
  have hk := kappaInf_nonneg n hn A A_inv
  have hu := (F.run.model t).u_nonneg
  unfold ch14ext_cor147WeakForwardLeadingCoefficient
  positivity

/-- The exact correction that removes the computed-solution norm ratio.

Writing `C` for the printed coefficient and `rho` for the already established
relative remainder, solving `e <= C(1+e)+rho` gives
`e <= C + C^2/(1-C) + rho/(1-C)`. -/
noncomputable def ch14ext_cor147WeakForwardPrintedRemainder
    {iota : Type*} {l : Filter iota} (n : Nat)
    (A A_inv : Fin n -> Fin n -> Real) {L U U_inv : Fin n -> Fin n -> Real}
    {b : Fin n -> Real} {start : Nat} (x : Fin n -> Real)
    (F : Ch14Cor147WeakFamily iota l n A L U U_inv b start)
    (t : iota) : Real :=
  let C := ch14ext_cor147WeakForwardLeadingCoefficient n A A_inv F t
  C ^ 2 / (1 - C) +
    ch14ext_cor147WeakForwardRelativeRemainder n A_inv x F t / (1 - C)

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

end NumStability.Ch14Ext
