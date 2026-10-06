/-
  Algorithms/QR/Higham19WYApplicationClosure.lean

  Source-facing closure of Higham section 19.5, equations (19.17)--(19.22).

  The important cross-chapter bridge is explicit here: the two rounded
  matrix products used to apply the WY factor are instances of the general
  Chapter 13 equation (13.4), specialized to the operator 2-norm.  Their
  family-level contracts have one filter-uniform O(u^2) remainder.  The
  polar/Problem 19.14 bridge derives (19.21) from (19.19), and the final
  theorem derives (19.22); neither bound is a premise.
-/

import NumStability.Algorithms.LU.BlockLUFirstOrderFamilies
import NumStability.Algorithms.QR.GramSchmidtPolar

namespace NumStability

open Filter Asymptotics
open scoped Topology

noncomputable section

/-! ## Exact WY algebra: (19.17) and (19.18) -/

/-- Append one column on the right of a finite matrix. -/
def ch19ext_appendColumn {m r : Nat}
    (A : Fin m -> Fin r -> Real) (a : Fin m -> Real) :
    Fin m -> Fin (r + 1) -> Real :=
  fun i => Fin.lastCases (a i) (fun j => A i j)

@[simp] theorem ch19ext_appendColumn_castSucc {m r : Nat}
    (A : Fin m -> Fin r -> Real) (a : Fin m -> Real)
    (i : Fin m) (j : Fin r) :
    ch19ext_appendColumn A a i j.castSucc = A i j := by
  simp [ch19ext_appendColumn]

@[simp] theorem ch19ext_appendColumn_last {m r : Nat}
    (A : Fin m -> Fin r -> Real) (a : Fin m -> Real) (i : Fin m) :
    ch19ext_appendColumn A a i (Fin.last r) = a i := by
  simp [ch19ext_appendColumn]

/-- The compact WY matrix `I + W Y^T`. -/
def ch19ext_wyMatrix {m r : Nat}
    (W Y : Fin m -> Fin r -> Real) : Fin m -> Fin m -> Real :=
  fun i j => idMatrix m i j + rectMatMul W (finiteTranspose Y) i j

/-- A Householder factor in the normalization used in section 19.5. -/
def ch19ext_householderFactor {m : Nat} (v : Fin m -> Real) :
    Fin m -> Fin m -> Real :=
  fun i j => idMatrix m i j - v i * v j

/-- The initial columns in (19.17): `W_1 = -v_1`, `Y_1 = v_1`. -/
def ch19ext_wyWOne {m : Nat} (v : Fin m -> Real) :
    Fin m -> Fin 1 -> Real := fun i _ => -v i

def ch19ext_wyYOne {m : Nat} (v : Fin m -> Real) :
    Fin m -> Fin 1 -> Real := fun i _ => v i

theorem ch19ext_eq19_17_base {m : Nat} (v : Fin m -> Real) :
    ch19ext_wyMatrix (ch19ext_wyWOne v) (ch19ext_wyYOne v) =
      ch19ext_householderFactor v := by
  ext i j
  simp [ch19ext_wyMatrix, ch19ext_wyWOne, ch19ext_wyYOne,
    ch19ext_householderFactor, rectMatMul, finiteTranspose]
  ring

/-- The two column recurrences in (19.17).  The new `Y` column is
`Q_{i-1}^T v_i`, with `Q_{i-1} = I + W_{i-1}Y_{i-1}^T`. -/
def ch19ext_wyWNext {m r : Nat}
    (W : Fin m -> Fin r -> Real) (v : Fin m -> Real) :
    Fin m -> Fin (r + 1) -> Real :=
  ch19ext_appendColumn W (fun i => -v i)

def ch19ext_wyYNext {m r : Nat}
    (W Y : Fin m -> Fin r -> Real) (v : Fin m -> Real) :
    Fin m -> Fin (r + 1) -> Real :=
  ch19ext_appendColumn Y
    (rectMatMulVec (finiteTranspose (ch19ext_wyMatrix W Y)) v)

@[simp] theorem ch19ext_eq19_17_W_old {m r : Nat}
    (W : Fin m -> Fin r -> Real) (v : Fin m -> Real)
    (i : Fin m) (j : Fin r) :
    ch19ext_wyWNext W v i j.castSucc = W i j := by
  simp [ch19ext_wyWNext]

@[simp] theorem ch19ext_eq19_17_W_new {m r : Nat}
    (W : Fin m -> Fin r -> Real) (v : Fin m -> Real) (i : Fin m) :
    ch19ext_wyWNext W v i (Fin.last r) = -v i := by
  simp [ch19ext_wyWNext]

@[simp] theorem ch19ext_eq19_17_Y_old {m r : Nat}
    (W Y : Fin m -> Fin r -> Real) (v : Fin m -> Real)
    (i : Fin m) (j : Fin r) :
    ch19ext_wyYNext W Y v i j.castSucc = Y i j := by
  simp [ch19ext_wyYNext]

@[simp] theorem ch19ext_eq19_17_Y_new {m r : Nat}
    (W Y : Fin m -> Fin r -> Real) (v : Fin m -> Real) (i : Fin m) :
    ch19ext_wyYNext W Y v i (Fin.last r) =
      rectMatMulVec (finiteTranspose (ch19ext_wyMatrix W Y)) v i := by
  simp [ch19ext_wyYNext]

/-- Correctness of the recurrence (19.17).  Appending the displayed columns
updates the compact WY matrix by left multiplication with the next
Householder factor, exactly in the source orientation
`Q_i = P_i Q_{i-1}`. -/
theorem ch19ext_eq19_17_recurrence {m r : Nat}
    (W Y : Fin m -> Fin r -> Real) (v : Fin m -> Real) :
    ch19ext_wyMatrix (ch19ext_wyWNext W v) (ch19ext_wyYNext W Y v) =
      rectMatMul (ch19ext_householderFactor v) (ch19ext_wyMatrix W Y) := by
  classical
  let Q := ch19ext_wyMatrix W Y
  have hnext :
      ch19ext_wyMatrix (ch19ext_wyWNext W v) (ch19ext_wyYNext W Y v) =
        fun i j => Q i j -
          v i * rectMatMulVec (finiteTranspose Q) v j := by
    ext i j
    unfold ch19ext_wyMatrix rectMatMul finiteTranspose
    rw [Fin.sum_univ_castSucc]
    simp only [ch19ext_eq19_17_W_old, ch19ext_eq19_17_Y_old,
      ch19ext_eq19_17_W_new, ch19ext_eq19_17_Y_new]
    simp only [Q, ch19ext_wyMatrix, rectMatMul, finiteTranspose,
      rectMatMulVec]
    ring
  rw [hnext]
  ext i j
  unfold ch19ext_householderFactor rectMatMul
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  have hid :
      (∑ k : Fin m, idMatrix m i k * Q k j) = Q i j := by
    have h := congrFun (congrFun (rectMatMul_id_left Q) i) j
    simpa [rectMatMul] using h
  have hv :
      (∑ k : Fin m, (v i * v k) * Q k j) =
        v i * rectMatMulVec (finiteTranspose Q) v j := by
    unfold rectMatMulVec finiteTranspose
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hid, hv]

/-- The column partition `A = [A_1 B]` from (19.18). -/
def ch19ext_columnPartition {m r p : Nat}
    (A1 : Fin m -> Fin r -> Real) (B : Fin m -> Fin p -> Real) :
    Fin m -> Fin (r + p) -> Real :=
  fun i => Fin.addCases (fun j => A1 i j) (fun j => B i j)

@[simp] theorem ch19ext_eq19_18_left {m r p : Nat}
    (A1 : Fin m -> Fin r -> Real) (B : Fin m -> Fin p -> Real)
    (i : Fin m) (j : Fin r) :
    ch19ext_columnPartition A1 B i (Fin.castAdd p j) = A1 i j := by
  simp [ch19ext_columnPartition]

@[simp] theorem ch19ext_eq19_18_right {m r p : Nat}
    (A1 : Fin m -> Fin r -> Real) (B : Fin m -> Fin p -> Real)
    (i : Fin m) (j : Fin p) :
    ch19ext_columnPartition A1 B i (Fin.natAdd r j) = B i j := by
  simp [ch19ext_columnPartition]

/-- Exact block application preceding (19.19):
`(I + WY^T)B = B + W(Y^T B)`. -/
theorem ch19ext_wyMatrix_apply {m r p : Nat}
    (W Y : Fin m -> Fin r -> Real) (B : Fin m -> Fin p -> Real) :
    rectMatMul (ch19ext_wyMatrix W Y) B =
      fun i j => B i j +
        rectMatMul W (rectMatMul (finiteTranspose Y) B) i j := by
  calc
    rectMatMul (ch19ext_wyMatrix W Y) B =
        rectMatMul (fun i j => idMatrix m i j +
          rectMatMul W (finiteTranspose Y) i j) B := rfl
    _ = fun i j => rectMatMul (idMatrix m) B i j +
        rectMatMul (rectMatMul W (finiteTranspose Y)) B i j :=
      rectMatMul_add_left _ _ _
    _ = fun i j => B i j +
        rectMatMul W (rectMatMul (finiteTranspose Y) B) i j := by
      rw [rectMatMul_id_left, rectMatMul_assoc]

/-! ## Exact operator-2 norm utilities -/

theorem ch19ext_rectOpNorm2_add_le {m n : Nat}
    (A B : Fin m -> Fin n -> Real) :
    rectOpNorm2 (fun i j => A i j + B i j) <=
      rectOpNorm2 A + rectOpNorm2 B := by
  unfold rectOpNorm2
  simpa only [Matrix.add_apply] using
    (@norm_add_le
      (Matrix (Fin m) (Fin n) Real)
      (@SeminormedAddCommGroup.toSeminormedAddGroup
        (Matrix (Fin m) (Fin n) Real)
        (@NormedAddCommGroup.toSeminormedAddCommGroup
          (Matrix (Fin m) (Fin n) Real)
          (Matrix.instL2OpNormedAddCommGroup
            (m := Fin m) (n := Fin n) (𝕜 := Real))))
      (A : Matrix (Fin m) (Fin n) Real)
      (B : Matrix (Fin m) (Fin n) Real))

theorem ch19ext_rectOpNorm2_rectMatMul_le {m n p : Nat}
    (A : Fin m -> Fin n -> Real) (B : Fin n -> Fin p -> Real) :
    rectOpNorm2 (rectMatMul A B) <= rectOpNorm2 A * rectOpNorm2 B := by
  simpa [rectOpNorm2, rectMatMul, Matrix.mul_apply] using
    (Matrix.l2_opNorm_mul
      (A := (A : Matrix (Fin m) (Fin n) Real))
      (B := (B : Matrix (Fin n) (Fin p) Real)))

@[simp] theorem ch19ext_rectOpNorm2_transpose {m n : Nat}
    (A : Matrix (Fin m) (Fin n) Real) :
    rectOpNorm2 A.transpose = rectOpNorm2 A := by
  simpa [finiteTranspose] using
    (rectOpNorm2_finiteTranspose (M := (A : Fin m -> Fin n -> Real)))

/-! ## Problem 19.14: the polar bridge from (19.19) to (19.21) -/

/-- For a square matrix, the repository's orthonormal-column predicate is
the bundled two-sided orthogonality predicate.  The reverse product follows
from Dedekind finiteness of finite square matrices; it is not an additional
rank hypothesis. -/
theorem ch19ext_isOrthogonal_of_square_orthonormalColumns {n : Nat}
    (Q : Fin n -> Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    IsOrthogonal n Q := by
  have hleft : IsLeftInverse n Q (matTranspose Q) := by
    intro i j
    simpa [rectangularGram, matMulRect, finiteTranspose, matTranspose,
      idMatrix] using hQ i j
  have hswapRight : IsRightInverse n (matTranspose Q) Q := hleft
  have hswapLeft : IsLeftInverse n (matTranspose Q) Q :=
    isLeftInverse_of_isRightInverse (matTranspose Q) Q hswapRight
  have hright : IsRightInverse n Q (matTranspose Q) := hswapLeft
  exact And.intro hleft hright

/-- The upper inequality of Problem 19.14, in the left-Gram orientation used
by (19.19).  Applying the repository's completed right polar decomposition to
`A^T` produces an exactly orthogonal `U`; the spectral resolvent
`(I+H)^{-1}` proves

`||A-U||_2 <= ||A A^T-I||_2`.

This is the precise implication needed by the prose between (19.19) and
(19.21).  It needs no smallness or nonsingularity assumption, including for a
rank-deficient square matrix, because the polar isometry is orthogonally
completed on its nullspace. -/
theorem ch19ext_problem19_14_leftPolar_repair {n : Nat}
    (A : Matrix (Fin n) (Fin n) Real) :
    exists U DeltaU : Matrix (Fin n) (Fin n) Real,
      A = U + DeltaU /\
      IsOrthogonal n U /\
      rectOpNorm2 DeltaU <= rectOpNorm2 (A * A.transpose - 1) := by
  let At : Fin n -> Fin n -> Real := finiteTranspose A
  obtain ⟨Q, hfactor, hQcols⟩ :=
    exists_rectRightGramPolarCompletion_of_tall At (le_refl n)
  let H : Fin n -> Fin n -> Real := rectRightGramPolarH At
  let U : Fin n -> Fin n -> Real := finiteTranspose Q
  let DeltaU : Fin n -> Fin n -> Real := fun i j => A i j - U i j
  have hQorth : IsOrthogonal n Q :=
    ch19ext_isOrthogonal_of_square_orthonormalColumns Q hQcols
  have hUorth : IsOrthogonal n U := by
    simpa [U, finiteTranspose, matTranspose] using hQorth.transpose
  have hHsym : finiteTranspose H = H := by
    simpa [H] using rectRightGramPolarH_symmetric At
  have hA_factor :
      A = rectMatMul H U := by
    ext i j
    have hf := congrFun (congrFun hfactor j) i
    calc
      A i j = At j i := by rfl
      _ = matMulRect n n n Q H j i := hf
      _ = Finset.univ.sum (fun k : Fin n => Q j k * H k i) := by rfl
      _ = Finset.univ.sum (fun k : Fin n => H i k * Q j k) := by
        apply Finset.sum_congr rfl
        intro k _
        have hs := congrFun (congrFun hHsym k) i
        simp only [finiteTranspose] at hs
        rw [hs]
        ring
      _ = rectMatMul H U i j := by rfl
  have hDelta_factor :
      DeltaU = rectMatMul (fun i j => H i j - idMatrix n i j) U := by
    have hsub := matMul_sub_left n H (idMatrix n) U
    ext i j
    have hsubij := congrFun (congrFun hsub i) j
    calc
      DeltaU i j = A i j - U i j := by rfl
      _ = rectMatMul H U i j - U i j := by rw [hA_factor]
      _ = matMul n H U i j - matMul n (idMatrix n) U i j := by
        rw [matMul_id_left]
        rfl
      _ = matMul n (fun a b => H a b - idMatrix n a b) U i j :=
        hsubij.symm
      _ = rectMatMul (fun a b => H a b - idMatrix n a b) U i j := by
        rfl
  let sourceDefect : Fin n -> Fin n -> Real :=
    fun i j => rectMatMul A (finiteTranspose A) i j - idMatrix n i j
  let polarDefect : Fin n -> Fin n -> Real :=
    fun i j => idMatrix n i j - rectMatMul H H i j
  have hHsq : rectMatMul H H = rectMatMul A (finiteTranspose A) := by
    simpa [H, At, rectangularGram, matMul, matMulRect, rectMatMul] using
      rectRightGramPolarH_sq_eq_rectangularGram At
  have hDefectNeg :
      polarDefect = fun i j => -sourceDefect i j := by
    ext i j
    simp only [polarDefect, sourceDefect]
    rw [hHsq]
    ring
  let d : Real := rectOpNorm2 sourceDefect
  have hd : 0 <= d := rectOpNorm2_nonneg sourceDefect
  have hsource : rectOpNorm2Le sourceDefect d :=
    rectOpNorm2Le_rectOpNorm2 sourceDefect
  have hpolarRect : rectOpNorm2Le polarDefect d := by
    rw [hDefectNeg]
    exact rectOpNorm2Le_neg hsource
  have hpolar : opNorm2Le polarDefect d :=
    opNorm2Le_of_rectOpNorm2Le_square polarDefect hpolarRect
  let R : Fin n -> Fin n -> Real := rectRightGramPolarResolvent At
  have hR : opNorm2Le R 1 := by
    simpa [R] using rectRightGramPolarResolvent_opNorm2Le_one At
  have hresolvent :
      rectMatMul R polarDefect =
        fun i j => idMatrix n i j - H i j := by
    simpa [R, polarDefect, H, rectMatMul, matMul] using
      rectRightGramPolarResolvent_mul_id_sub_polarH_sq At
  have hIH : opNorm2Le (fun i j => idMatrix n i j - H i j) d := by
    have hprod := opNorm2Le_matMul_square_of_bounds
      R polarDefect (by norm_num) hR hpolar
    change opNorm2Le (rectMatMul R polarDefect) (1 * d) at hprod
    rw [hresolvent] at hprod
    simpa using hprod
  have hHIrect :
      rectOpNorm2Le (fun i j => H i j - idMatrix n i j) d := by
    have hIHrect := rectOpNorm2Le_of_opNorm2Le_square
      (fun i j => idMatrix n i j - H i j) hIH
    have hneg := rectOpNorm2Le_neg hIHrect
    simpa only [neg_sub] using hneg
  have hUrect : rectOpNorm2Le U 1 :=
    rectOpNorm2Le_of_opNorm2Le_square U hUorth.opNorm2Le_one
  have hDeltaRect : rectOpNorm2Le DeltaU d := by
    have hprod := rectOpNorm2Le_rectMatMul
      (fun i j => H i j - idMatrix n i j) U hd hHIrect hUrect
    rw [← hDelta_factor] at hprod
    simpa using hprod
  have hDeltaOp : opNorm2Le DeltaU d :=
    opNorm2Le_of_rectOpNorm2Le_square DeltaU hDeltaRect
  have hDeltaNorm : rectOpNorm2 DeltaU <= d := by
    have h := opNorm2_le_of_opNorm2Le DeltaU hd hDeltaOp
    simpa [opNorm2, rectOpNorm2] using h
  refine ⟨U, DeltaU, ?_, hUorth, ?_⟩
  · ext i j
    simp [DeltaU]
  · simpa [d, sourceDefect, rectMatMul, Matrix.mul_apply,
      Matrix.sub_apply, finiteTranspose, idMatrix] using hDeltaNorm

/-- A first-order family with a genuinely first-order leading term has value
`O(u)`.  This helper is what makes the nested level-3 product errors in
(19.22) contribute only to the uniform quadratic remainder. -/
theorem ch19ext_familyFirstOrder_value_isBigO_unit
    {ι : Type*} {l : Filter ι} (Uround : RoundoffFamily ι l)
    {leading value : ι -> Real}
    (hleading_nonneg : forall t, 0 <= leading t)
    (hvalue_nonneg : forall t, 0 <= value t)
    (hleadingO : leading =O[l] Uround.unit)
    (h : FamilyFirstOrderLe l Uround.unit leading value) :
    value =O[l] Uround.unit := by
  rcases h with ⟨remainder, hremainder, hbound, hremO⟩
  have hremUnit : remainder =O[l] Uround.unit :=
    hremO.trans Uround.unit_sq_isBigO_unit
  have hsumO :
      (fun t => leading t + remainder t) =O[l] Uround.unit :=
    hleadingO.add hremUnit
  exact
    (scalarFamily_isBigO_of_nonneg_le hvalue_nonneg
      (fun t => add_nonneg (hleading_nonneg t) (hremainder t)) hbound).trans
      hsumO

/-- Pure scalar bookkeeping behind the coefficient in (19.22).  Each
hypothesis is one norm inequality supplied by the exact matrix equation or
by an operation contract; the desired bound itself is not assumed. -/
theorem ch19ext_eq19_22_scalar_bound
    (u b w y du that phat eInner eOuter eAdd delta
      remInner remOuter remAdd d1 d2 d3 cInner cOuter : Real)
    (hu : 0 <= u) (hb : 0 <= b) (hw0 : 0 <= w) (hy0 : 0 <= y)
    (hd20 : 0 <= d2)
    (hcInner0 : 0 <= cInner) (hcOuter0 : 0 <= cOuter)
    (hdu : du <= d1 * u) (hw : w <= d2) (hy : y <= d3)
    (hthat : that <= y * b + eInner)
    (hphat : phat <= w * that + eOuter)
    (heInner : eInner <= cInner * u * y * b + remInner)
    (heOuter : eOuter <= cOuter * u * w * that + remOuter)
    (heAdd : eAdd <= u * (b + phat) + remAdd)
    (hdelta : delta <= du * b + w * eInner + eOuter + eAdd) :
    delta <=
      (1 + d1 + d2 * d3 * (1 + cInner + cOuter)) * u * b +
        (w * remInner + remOuter + remAdd +
          cOuter * u * w * eInner + u * w * eInner + u * eOuter) := by
  have hduB := mul_le_mul_of_nonneg_right hdu hb
  have hInnerW := mul_le_mul_of_nonneg_left heInner hw0
  have hThatScaled := mul_le_mul_of_nonneg_left hthat
    (mul_nonneg (mul_nonneg hcOuter0 hu) hw0)
  have hThatUW := mul_le_mul_of_nonneg_left hthat (mul_nonneg hu hw0)
  have hPhatU := mul_le_mul_of_nonneg_left hphat hu
  have hwy : w * y <= d2 * d3 := by
    calc
      w * y <= d2 * y := mul_le_mul_of_nonneg_right hw hy0
      _ <= d2 * d3 := mul_le_mul_of_nonneg_left hy hd20
  have hwyInner := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwy (mul_nonneg hcInner0 hu)) hb
  have hwyOuter := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwy (mul_nonneg hcOuter0 hu)) hb
  have hwyAdd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwy hu) hb
  nlinarith

/-! ## Family-level Chapter 13 operation contracts in the 2-norm -/

/-- Equation (13.4), specialized to the general operator 2-norm requested
explicitly in the derivation of (19.22). -/
structure Higham13Op2MatMulFamilySpec {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m n p : Nat} (c1 : Real)
    (A : ι -> Matrix (Fin m) (Fin n) Real)
    (B : ι -> Matrix (Fin n) (Fin p) Real)
    (Chat Delta : ι -> Matrix (Fin m) (Fin p) Real) where
  coefficient_nonneg : 0 <= c1
  equation : forall t, Chat t = A t * B t + Delta t
  left_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => rectOpNorm2 (A t))
  right_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => rectOpNorm2 (B t))
  norm_bound : FamilyFirstOrderLe l Uround.unit
    (fun t => c1 * Uround.unit t * rectOpNorm2 (A t) * rectOpNorm2 (B t))
    (fun t => rectOpNorm2 (Delta t))

/-- Normwise rounded matrix addition used in
`fl(B + fl(W fl(Y^T B)))`. -/
structure Ch19Op2AdditionFamilySpec {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m p : Nat}
    (A B Chat Delta : ι -> Matrix (Fin m) (Fin p) Real) where
  equation : forall t, Chat t = A t + B t + Delta t
  left_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => rectOpNorm2 (A t))
  right_norm_isBigO_one : ScalarFamilyIsBigOOne l
    (fun t => rectOpNorm2 (B t))
  norm_bound : FamilyFirstOrderLe l Uround.unit
    (fun t => Uround.unit t *
      (rectOpNorm2 (A t) + rectOpNorm2 (B t)))
    (fun t => rectOpNorm2 (Delta t))

/-! ## The printed construction bounds (19.19)--(19.21) -/

/-- The genuinely prior construction data in (19.19)--(19.20).  In
particular, this structure has no orthogonal matrix, perturbation, or (19.21)
field: those are consequences of `eq19_19` through Problem 19.14 below. -/
structure Ch19WYConstructionEq19_19FamilySpec {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m r : Nat}
    (d1 d2 d3 : Real)
    (Qhat : ι -> Matrix (Fin m) (Fin m) Real)
    (What Yhat : ι -> Matrix (Fin m) (Fin r) Real) where
  d1_nonneg : 0 <= d1
  d2_nonneg : 0 <= d2
  d3_nonneg : 0 <= d3
  wy_equation : forall t,
    Qhat t = 1 + What t * (Yhat t).transpose
  eq19_19 : forall t,
    rectOpNorm2 (Qhat t * (Qhat t).transpose - 1) <= d1 * Uround.unit t
  eq19_20_W : forall t, rectOpNorm2 (What t) <= d2
  eq19_20_Y : forall t, rectOpNorm2 (Yhat t) <= d3

/-- The assembled construction payload used internally by the (19.22)
derivation.  Public callers need not assume this structure: theorem
`ch19ext_eq19_19_implies_eq19_21_family` constructs it from the preceding
(19.19)--(19.20) specification. -/
structure Ch19WYConstructionFamilySpec {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m r : Nat}
    (d1 d2 d3 : Real)
    (Qhat : ι -> Matrix (Fin m) (Fin m) Real)
    (What Yhat : ι -> Matrix (Fin m) (Fin r) Real)
    (U DeltaU : ι -> Matrix (Fin m) (Fin m) Real) where
  d1_nonneg : 0 <= d1
  d2_nonneg : 0 <= d2
  d3_nonneg : 0 <= d3
  wy_equation : forall t,
    Qhat t = 1 + What t * (Yhat t).transpose
  eq19_19 : forall t,
    rectOpNorm2 (Qhat t * (Qhat t).transpose - 1) <= d1 * Uround.unit t
  eq19_20_W : forall t, rectOpNorm2 (What t) <= d2
  eq19_20_Y : forall t, rectOpNorm2 (Yhat t) <= d3
  eq19_21_equation : forall t, Qhat t = U t + DeltaU t
  eq19_21_orthogonal : forall t, IsOrthogonal m (U t)
  eq19_21_bound : forall t,
    rectOpNorm2 (DeltaU t) <= d1 * Uround.unit t

/-- Family form of the exact source implication `(19.19) => (19.21)`.
The matrices `U` and `DeltaU` are constructed pointwise by the completed
polar decomposition of `Qhat^T`; neither is supplied by the caller. -/
theorem ch19ext_eq19_19_implies_eq19_21_family
    {ι : Type*} {l : Filter ι} {Uround : RoundoffFamily ι l}
    {m r : Nat} {d1 d2 d3 : Real}
    {Qhat : ι -> Matrix (Fin m) (Fin m) Real}
    {What Yhat : ι -> Matrix (Fin m) (Fin r) Real}
    (hWY : Ch19WYConstructionEq19_19FamilySpec Uround d1 d2 d3
      Qhat What Yhat) :
    exists U DeltaU : ι -> Matrix (Fin m) (Fin m) Real,
      Ch19WYConstructionFamilySpec Uround d1 d2 d3
        Qhat What Yhat U DeltaU := by
  have hrepair : forall t : ι,
      exists U DeltaU : Matrix (Fin m) (Fin m) Real,
        Qhat t = U + DeltaU /\
        IsOrthogonal m U /\
        rectOpNorm2 DeltaU <= d1 * Uround.unit t := by
    intro t
    obtain ⟨U, DeltaU, heq, horth, hpolar⟩ :=
      ch19ext_problem19_14_leftPolar_repair (Qhat t)
    exact ⟨U, DeltaU, heq, horth, hpolar.trans (hWY.eq19_19 t)⟩
  choose U DeltaU heq horth hbound using hrepair
  refine ⟨U, DeltaU, ?_⟩
  exact
    { d1_nonneg := hWY.d1_nonneg
      d2_nonneg := hWY.d2_nonneg
      d3_nonneg := hWY.d3_nonneg
      wy_equation := hWY.wy_equation
      eq19_19 := hWY.eq19_19
      eq19_20_W := hWY.eq19_20_W
      eq19_20_Y := hWY.eq19_20_Y
      eq19_21_equation := heq
      eq19_21_orthogonal := horth
      eq19_21_bound := hbound }

/-- The actual two level-3 products and final rounded addition in section
19.5.  The product fields are precisely two uses of Chapter 13 (13.4). -/
structure Ch19WYApplicationFamilySpec {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m r p : Nat}
    (cInner cOuter : Real)
    (B : ι -> Matrix (Fin m) (Fin p) Real)
    (What Yhat : ι -> Matrix (Fin m) (Fin r) Real)
    (That DeltaInner : ι -> Matrix (Fin r) (Fin p) Real)
    (Phat DeltaOuter Chat DeltaAdd :
      ι -> Matrix (Fin m) (Fin p) Real) where
  inner_product : Higham13Op2MatMulFamilySpec Uround cInner
    (fun t => (Yhat t).transpose) B That DeltaInner
  outer_product : Higham13Op2MatMulFamilySpec Uround cOuter
    What That Phat DeltaOuter
  final_addition : Ch19Op2AdditionFamilySpec Uround
    B Phat Chat DeltaAdd

/-! ## Exact error equation and the family-level (19.22) conclusion -/

/-- The explicit accumulated application perturbation. -/
def ch19ext_wyApplicationDelta {ι : Type*} {m r p : Nat}
    (B : ι -> Matrix (Fin m) (Fin p) Real)
    (What : ι -> Matrix (Fin m) (Fin r) Real)
    (DeltaU : ι -> Matrix (Fin m) (Fin m) Real)
    (DeltaInner : ι -> Matrix (Fin r) (Fin p) Real)
    (DeltaOuter DeltaAdd : ι -> Matrix (Fin m) (Fin p) Real) :
    ι -> Matrix (Fin m) (Fin p) Real :=
  fun t => DeltaU t * B t + What t * DeltaInner t +
    DeltaOuter t + DeltaAdd t

theorem ch19ext_computed_product_rectOpNorm2_le {m n p : Nat}
    (A : Matrix (Fin m) (Fin n) Real)
    (B : Matrix (Fin n) (Fin p) Real)
    (Chat Delta : Matrix (Fin m) (Fin p) Real)
    (hequation : Chat = A * B + Delta) :
    rectOpNorm2 Chat <=
      rectOpNorm2 A * rectOpNorm2 B + rectOpNorm2 Delta := by
  rw [hequation]
  calc
    rectOpNorm2 (A * B + Delta) <=
        rectOpNorm2 (A * B) + rectOpNorm2 Delta :=
      ch19ext_rectOpNorm2_add_le _ _
    _ <= rectOpNorm2 A * rectOpNorm2 B + rectOpNorm2 Delta := by
      gcongr
      simpa [rectMatMul, Matrix.mul_apply] using
        ch19ext_rectOpNorm2_rectMatMul_le
          (A : Fin m -> Fin n -> Real) (B : Fin n -> Fin p -> Real)

theorem ch19ext_wyApplicationDelta_rectOpNorm2_le
    {ι : Type*} {m r p : Nat}
    (B : ι -> Matrix (Fin m) (Fin p) Real)
    (What : ι -> Matrix (Fin m) (Fin r) Real)
    (DeltaU : ι -> Matrix (Fin m) (Fin m) Real)
    (DeltaInner : ι -> Matrix (Fin r) (Fin p) Real)
    (DeltaOuter DeltaAdd : ι -> Matrix (Fin m) (Fin p) Real)
    (t : ι) :
    rectOpNorm2 (ch19ext_wyApplicationDelta B What DeltaU
      DeltaInner DeltaOuter DeltaAdd t) <=
      rectOpNorm2 (DeltaU t) * rectOpNorm2 (B t) +
        rectOpNorm2 (What t) * rectOpNorm2 (DeltaInner t) +
        rectOpNorm2 (DeltaOuter t) + rectOpNorm2 (DeltaAdd t) := by
  have hDU := ch19ext_rectOpNorm2_rectMatMul_le
    (DeltaU t : Fin m -> Fin m -> Real) (B t : Fin m -> Fin p -> Real)
  have hInner := ch19ext_rectOpNorm2_rectMatMul_le
    (What t : Fin m -> Fin r -> Real)
    (DeltaInner t : Fin r -> Fin p -> Real)
  have hAdd1 := ch19ext_rectOpNorm2_add_le
    (DeltaU t * B t) (What t * DeltaInner t)
  have hAdd2 := ch19ext_rectOpNorm2_add_le
    (DeltaU t * B t + What t * DeltaInner t) (DeltaOuter t)
  have hAdd3 := ch19ext_rectOpNorm2_add_le
    (DeltaU t * B t + What t * DeltaInner t + DeltaOuter t) (DeltaAdd t)
  have hDU' : rectOpNorm2 (DeltaU t * B t) <=
      rectOpNorm2 (DeltaU t) * rectOpNorm2 (B t) := by
    simpa [rectMatMul, Matrix.mul_apply] using hDU
  have hInner' : rectOpNorm2 (What t * DeltaInner t) <=
      rectOpNorm2 (What t) * rectOpNorm2 (DeltaInner t) := by
    simpa [rectMatMul, Matrix.mul_apply] using hInner
  have hAdd1' : rectOpNorm2 (DeltaU t * B t + What t * DeltaInner t) <=
      rectOpNorm2 (DeltaU t * B t) +
        rectOpNorm2 (What t * DeltaInner t) := by
    simpa only [Matrix.add_apply] using hAdd1
  have hAdd2' :
      rectOpNorm2 (DeltaU t * B t + What t * DeltaInner t + DeltaOuter t) <=
        rectOpNorm2 (DeltaU t * B t + What t * DeltaInner t) +
          rectOpNorm2 (DeltaOuter t) := by
    simpa only [Matrix.add_apply] using hAdd2
  have hAdd3' :
      rectOpNorm2 (DeltaU t * B t + What t * DeltaInner t +
          DeltaOuter t + DeltaAdd t) <=
        rectOpNorm2 (DeltaU t * B t + What t * DeltaInner t + DeltaOuter t) +
          rectOpNorm2 (DeltaAdd t) := by
    simpa only [Matrix.add_apply] using hAdd3
  simp only [ch19ext_wyApplicationDelta]
  nlinarith

theorem ch19ext_wyApplication_exact_error_equation
    {ι : Type*} {l : Filter ι} {Uround : RoundoffFamily ι l}
    {m r p : Nat} {d1 d2 d3 cInner cOuter : Real}
    {Qhat : ι -> Matrix (Fin m) (Fin m) Real}
    {What Yhat : ι -> Matrix (Fin m) (Fin r) Real}
    {U DeltaU : ι -> Matrix (Fin m) (Fin m) Real}
    {B : ι -> Matrix (Fin m) (Fin p) Real}
    {That DeltaInner : ι -> Matrix (Fin r) (Fin p) Real}
    {Phat DeltaOuter Chat DeltaAdd :
      ι -> Matrix (Fin m) (Fin p) Real}
    (hWY : Ch19WYConstructionFamilySpec Uround d1 d2 d3
      Qhat What Yhat U DeltaU)
    (happ : Ch19WYApplicationFamilySpec Uround cInner cOuter
      B What Yhat That DeltaInner Phat DeltaOuter Chat DeltaAdd)
    (t : ι) :
    Chat t = U t * B t +
      ch19ext_wyApplicationDelta B What DeltaU
        DeltaInner DeltaOuter DeltaAdd t := by
  rw [happ.final_addition.equation t, happ.outer_product.equation t,
    happ.inner_product.equation t]
  have hq :
      (1 + What t * (Yhat t).transpose) * B t =
        (U t + DeltaU t) * B t := by
    rw [← hWY.wy_equation t, hWY.eq19_21_equation t]
  calc
    B t + (What t * ((Yhat t).transpose * B t + DeltaInner t) +
          DeltaOuter t) + DeltaAdd t =
        (1 + What t * (Yhat t).transpose) * B t +
          (What t * DeltaInner t + DeltaOuter t + DeltaAdd t) := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
      abel
    _ = (U t + DeltaU t) * B t +
          (What t * DeltaInner t + DeltaOuter t + DeltaAdd t) := by
      rw [hq]
    _ = U t * B t +
          ch19ext_wyApplicationDelta B What DeltaU
            DeltaInner DeltaOuter DeltaAdd t := by
      rw [Matrix.add_mul]
      simp only [ch19ext_wyApplicationDelta]
      abel

/-- Orthogonality turns the forward perturbation equation into the second
literal equality printed in (19.22). -/
theorem ch19ext_orthogonal_backward_rewrite {m p : Nat}
    (U : Matrix (Fin m) (Fin m) Real)
    (B Delta : Matrix (Fin m) (Fin p) Real)
    (hU : IsOrthogonal m U) :
    U * B + Delta = U * (B + U.transpose * Delta) := by
  have hright : U * U.transpose = (1 : Matrix (Fin m) (Fin m) Real) := by
    ext i j
    simpa [Matrix.mul_apply, IsOrthogonal, finiteTranspose, matTranspose,
      idMatrix] using hU.right_inv i j
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hright, Matrix.one_mul]

/-- The conclusion of (19.22), keeping its actual perturbation witness. -/
def Ch19WYApplicationConclusion {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m p : Nat}
    (coefficient : Real)
    (U : ι -> Matrix (Fin m) (Fin m) Real)
    (B Chat : ι -> Matrix (Fin m) (Fin p) Real) : Prop :=
  exists DeltaC : ι -> Matrix (Fin m) (Fin p) Real,
    (forall t, Chat t = U t * B t + DeltaC t) /\
    (forall t, Chat t = U t * (B t + (U t).transpose * DeltaC t)) /\
    FamilyFirstOrderLe l Uround.unit
      (fun t => coefficient * Uround.unit t * rectOpNorm2 (B t))
      (fun t => rectOpNorm2 (DeltaC t))

/-- Equation (19.22), including both literal equalities and the exact printed
leading coefficient.  Its only numerical-computation assumptions are two
instances of the source's generic (13.4) matrix-product contract and the
displayed rounded addition.  In particular, no premise states or implies the
conclusion by merely renaming `DeltaC`. -/
theorem ch19ext_eq19_22_family
    {ι : Type*} {l : Filter ι} {Uround : RoundoffFamily ι l}
    {m r p : Nat} {d1 d2 d3 cInner cOuter : Real}
    {Qhat : ι -> Matrix (Fin m) (Fin m) Real}
    {What Yhat : ι -> Matrix (Fin m) (Fin r) Real}
    {U DeltaU : ι -> Matrix (Fin m) (Fin m) Real}
    {B : ι -> Matrix (Fin m) (Fin p) Real}
    {That DeltaInner : ι -> Matrix (Fin r) (Fin p) Real}
    {Phat DeltaOuter Chat DeltaAdd :
      ι -> Matrix (Fin m) (Fin p) Real}
    (hWY : Ch19WYConstructionFamilySpec Uround d1 d2 d3
      Qhat What Yhat U DeltaU)
    (happ : Ch19WYApplicationFamilySpec Uround cInner cOuter
      B What Yhat That DeltaInner Phat DeltaOuter Chat DeltaAdd) :
    Ch19WYApplicationConclusion Uround
      (1 + d1 + d2 * d3 * (1 + cInner + cOuter)) U B Chat := by
  let DeltaC := ch19ext_wyApplicationDelta B What DeltaU
    DeltaInner DeltaOuter DeltaAdd
  have hforward : forall t,
      Chat t = U t * B t + DeltaC t := by
    intro t
    exact ch19ext_wyApplication_exact_error_equation hWY happ t
  have hbackward : forall t,
      Chat t = U t * (B t + (U t).transpose * DeltaC t) := by
    intro t
    calc
      Chat t = U t * B t + DeltaC t := hforward t
      _ = U t * (B t + (U t).transpose * DeltaC t) :=
        ch19ext_orthogonal_backward_rewrite
          (U t) (B t) (DeltaC t) (hWY.eq19_21_orthogonal t)

  have hInnerLeadingO :
      (fun t => cInner * Uround.unit t *
        rectOpNorm2 ((Yhat t).transpose) * rectOpNorm2 (B t)) =O[l]
        Uround.unit := by
    have hcu : (fun t => cInner * Uround.unit t) =O[l] Uround.unit :=
      (Asymptotics.isBigO_refl Uround.unit l).const_mul_left cInner
    have hop := happ.inner_product.left_norm_isBigO_one.mul
      happ.inner_product.right_norm_isBigO_one
    simpa [ScalarFamilyIsBigOOne, mul_assoc] using hcu.mul hop
  have hInnerErrorO :
      (fun t => rectOpNorm2 (DeltaInner t)) =O[l] Uround.unit :=
    ch19ext_familyFirstOrder_value_isBigO_unit Uround
      (fun t => mul_nonneg
        (mul_nonneg
          (mul_nonneg happ.inner_product.coefficient_nonneg
            (Uround.unit_nonneg t))
          (rectOpNorm2_nonneg ((Yhat t).transpose)))
        (rectOpNorm2_nonneg (B t)))
      (fun t => rectOpNorm2_nonneg (DeltaInner t))
      hInnerLeadingO happ.inner_product.norm_bound

  have hOuterLeadingO :
      (fun t => cOuter * Uround.unit t * rectOpNorm2 (What t) *
        rectOpNorm2 (That t)) =O[l] Uround.unit := by
    have hcu : (fun t => cOuter * Uround.unit t) =O[l] Uround.unit :=
      (Asymptotics.isBigO_refl Uround.unit l).const_mul_left cOuter
    have hop := happ.outer_product.left_norm_isBigO_one.mul
      happ.outer_product.right_norm_isBigO_one
    simpa [ScalarFamilyIsBigOOne, mul_assoc] using hcu.mul hop
  have hOuterErrorO :
      (fun t => rectOpNorm2 (DeltaOuter t)) =O[l] Uround.unit :=
    ch19ext_familyFirstOrder_value_isBigO_unit Uround
      (fun t => mul_nonneg
        (mul_nonneg
          (mul_nonneg happ.outer_product.coefficient_nonneg
            (Uround.unit_nonneg t))
          (rectOpNorm2_nonneg (What t)))
        (rectOpNorm2_nonneg (That t)))
      (fun t => rectOpNorm2_nonneg (DeltaOuter t))
      hOuterLeadingO happ.outer_product.norm_bound

  rcases happ.inner_product.norm_bound with
    ⟨remInner, hremInner0, hInnerBound, hremInnerO⟩
  rcases happ.outer_product.norm_bound with
    ⟨remOuter, hremOuter0, hOuterBound, hremOuterO⟩
  rcases happ.final_addition.norm_bound with
    ⟨remAdd, hremAdd0, hAddBound, hremAddO⟩

  let remainder : ι -> Real := fun t =>
    rectOpNorm2 (What t) * remInner t + remOuter t + remAdd t +
      cOuter * Uround.unit t * rectOpNorm2 (What t) *
        rectOpNorm2 (DeltaInner t) +
      Uround.unit t * rectOpNorm2 (What t) *
        rectOpNorm2 (DeltaInner t) +
      Uround.unit t * rectOpNorm2 (DeltaOuter t)
  have hremainder0 : forall t, 0 <= remainder t := by
    intro t
    dsimp [remainder]
    exact add_nonneg
      (add_nonneg
        (add_nonneg
          (add_nonneg
            (add_nonneg
              (mul_nonneg (rectOpNorm2_nonneg (What t)) (hremInner0 t))
              (hremOuter0 t))
            (hremAdd0 t))
          (mul_nonneg
            (mul_nonneg
              (mul_nonneg happ.outer_product.coefficient_nonneg
                (Uround.unit_nonneg t))
              (rectOpNorm2_nonneg (What t)))
            (rectOpNorm2_nonneg (DeltaInner t))))
        (mul_nonneg
          (mul_nonneg (Uround.unit_nonneg t) (rectOpNorm2_nonneg (What t)))
          (rectOpNorm2_nonneg (DeltaInner t))))
      (mul_nonneg (Uround.unit_nonneg t)
        (rectOpNorm2_nonneg (DeltaOuter t)))

  have hWRemInner :
      (fun t => rectOpNorm2 (What t) * remInner t) =O[l]
        (fun t => Uround.unit t ^ 2) := by
    simpa [ScalarFamilyIsBigOOne] using
      Asymptotics.IsBigO.mul
        happ.outer_product.left_norm_isBigO_one hremInnerO
  have hOuterCross :
      (fun t => cOuter * Uround.unit t * rectOpNorm2 (What t) *
        rectOpNorm2 (DeltaInner t)) =O[l]
        (fun t => Uround.unit t ^ 2) := by
    have hcu : (fun t => cOuter * Uround.unit t) =O[l] Uround.unit :=
      (Asymptotics.isBigO_refl Uround.unit l).const_mul_left cOuter
    have h := (hcu.mul happ.outer_product.left_norm_isBigO_one).mul
      hInnerErrorO
    simpa [ScalarFamilyIsBigOOne, pow_two, mul_assoc] using h
  have hInnerCross :
      (fun t => Uround.unit t * rectOpNorm2 (What t) *
        rectOpNorm2 (DeltaInner t)) =O[l]
        (fun t => Uround.unit t ^ 2) := by
    have h := ((Asymptotics.isBigO_refl Uround.unit l).mul
      happ.outer_product.left_norm_isBigO_one).mul hInnerErrorO
    simpa [ScalarFamilyIsBigOOne, pow_two, mul_assoc] using h
  have hOuterCross2 :
      (fun t => Uround.unit t * rectOpNorm2 (DeltaOuter t)) =O[l]
        (fun t => Uround.unit t ^ 2) := by
    simpa [pow_two] using
      (Asymptotics.isBigO_refl Uround.unit l).mul hOuterErrorO
  have hremainderO : remainder =O[l] (fun t => Uround.unit t ^ 2) := by
    have hsum :=
      ((((hWRemInner.add hremOuterO).add hremAddO).add hOuterCross).add
        hInnerCross).add hOuterCross2
    simpa [remainder, add_assoc] using hsum

  refine ⟨DeltaC, hforward, hbackward,
    ⟨remainder, hremainder0, ?_, hremainderO⟩⟩
  intro t
  have hThat := ch19ext_computed_product_rectOpNorm2_le
    ((Yhat t).transpose) (B t) (That t) (DeltaInner t)
    (happ.inner_product.equation t)
  have hThat' : rectOpNorm2 (That t) <=
      rectOpNorm2 (Yhat t) * rectOpNorm2 (B t) +
        rectOpNorm2 (DeltaInner t) := by
    simpa only [ch19ext_rectOpNorm2_transpose] using hThat
  have hPhat := ch19ext_computed_product_rectOpNorm2_le
    (What t) (That t) (Phat t) (DeltaOuter t)
    (happ.outer_product.equation t)
  have hDelta := ch19ext_wyApplicationDelta_rectOpNorm2_le
    B What DeltaU DeltaInner DeltaOuter DeltaAdd t
  have hInnerBound' : rectOpNorm2 (DeltaInner t) <=
      cInner * Uround.unit t * rectOpNorm2 (Yhat t) *
        rectOpNorm2 (B t) + remInner t := by
    simpa only [ch19ext_rectOpNorm2_transpose] using hInnerBound t
  exact ch19ext_eq19_22_scalar_bound
    (u := Uround.unit t)
    (b := rectOpNorm2 (B t))
    (w := rectOpNorm2 (What t))
    (y := rectOpNorm2 (Yhat t))
    (du := rectOpNorm2 (DeltaU t))
    (that := rectOpNorm2 (That t))
    (phat := rectOpNorm2 (Phat t))
    (eInner := rectOpNorm2 (DeltaInner t))
    (eOuter := rectOpNorm2 (DeltaOuter t))
    (eAdd := rectOpNorm2 (DeltaAdd t))
    (delta := rectOpNorm2 (DeltaC t))
    (remInner := remInner t) (remOuter := remOuter t) (remAdd := remAdd t)
    (d1 := d1) (d2 := d2) (d3 := d3)
    (cInner := cInner) (cOuter := cOuter)
    (Uround.unit_nonneg t) (rectOpNorm2_nonneg (B t))
    (rectOpNorm2_nonneg (What t)) (rectOpNorm2_nonneg (Yhat t))
    hWY.d2_nonneg
    happ.inner_product.coefficient_nonneg
    happ.outer_product.coefficient_nonneg
    (hWY.eq19_21_bound t) (hWY.eq19_20_W t) (hWY.eq19_20_Y t)
    hThat' hPhat hInnerBound' (hOuterBound t) (hAddBound t) hDelta

/-- Source-facing existential form of (19.22): the orthogonal factor is the
analysis object whose existence follows from (19.19), rather than an input to
the application theorem. -/
def Ch19WYApplicationPolarConclusion {ι : Type*} {l : Filter ι}
    (Uround : RoundoffFamily ι l) {m p : Nat}
    (coefficient : Real)
    (B Chat : ι -> Matrix (Fin m) (Fin p) Real) : Prop :=
  exists U : ι -> Matrix (Fin m) (Fin m) Real,
    Ch19WYApplicationConclusion Uround coefficient U B Chat

/-- Fully bridged equations (19.19)--(19.22).  The only WY-construction
premise is the actual near-orthogonality/bounded-factor specification
(19.19)--(19.20).  Problem 19.14 constructs `U` and `DeltaU`, and the existing
application derivation then proves the exact coefficient in (19.22). -/
theorem ch19ext_eq19_22_family_from_eq19_19
    {ι : Type*} {l : Filter ι} {Uround : RoundoffFamily ι l}
    {m r p : Nat} {d1 d2 d3 cInner cOuter : Real}
    {Qhat : ι -> Matrix (Fin m) (Fin m) Real}
    {What Yhat : ι -> Matrix (Fin m) (Fin r) Real}
    {B : ι -> Matrix (Fin m) (Fin p) Real}
    {That DeltaInner : ι -> Matrix (Fin r) (Fin p) Real}
    {Phat DeltaOuter Chat DeltaAdd :
      ι -> Matrix (Fin m) (Fin p) Real}
    (hWY : Ch19WYConstructionEq19_19FamilySpec Uround d1 d2 d3
      Qhat What Yhat)
    (happ : Ch19WYApplicationFamilySpec Uround cInner cOuter
      B What Yhat That DeltaInner Phat DeltaOuter Chat DeltaAdd) :
    Ch19WYApplicationPolarConclusion Uround
      (1 + d1 + d2 * d3 * (1 + cInner + cOuter)) B Chat := by
  obtain ⟨U, DeltaU, hfull⟩ :=
    ch19ext_eq19_19_implies_eq19_21_family hWY
  exact ⟨U, ch19ext_eq19_22_family hfull happ⟩

end

end NumStability
