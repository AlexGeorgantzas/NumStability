import NumStability.Algorithms.QR.HouseholderQR

namespace NumStability

open scoped BigOperators

noncomputable section

/-!
Gram-Schmidt QR infrastructure for Higham Chapter 19.

This file records exact algebraic objects and source-facing specification
shapes for Algorithms 19.11 and 19.12 and Theorem 19.13.  The stability
theorem itself is left to the floating-point development that builds on these
definitions.
-/

/-- Extract column `j` from a rectangular matrix. -/
def gsColumn {m n : Nat} (A : Fin m -> Fin n -> Real) (j : Fin n) :
    Fin m -> Real :=
  fun i => A i j

/-- Euclidean dot product for Gram-Schmidt columns. -/
def gsDot {m : Nat} (x y : Fin m -> Real) : Real :=
  Finset.univ.sum fun i : Fin m => x i * y i

/-- The Gram-Schmidt dot product is symmetric. -/
theorem gsDot_comm {m : Nat} (x y : Fin m -> Real) :
    gsDot x y = gsDot y x := by
  unfold gsDot
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scale a column vector. -/
def gsScale {m : Nat} (alpha : Real) (x : Fin m -> Real) : Fin m -> Real :=
  fun i => alpha * x i

/-- Subtract one column vector from another. -/
def gsSub {m : Nat} (x y : Fin m -> Real) : Fin m -> Real :=
  fun i => x i - y i

/-- Remove the projection of `x` in the direction `q`. -/
def gsProjectAway {m : Nat} (x q : Fin m -> Real) : Fin m -> Real :=
  fun i => x i - gsDot q x * q i

/-- The Gram-Schmidt dot product of a vector with itself is its finite squared
Euclidean norm. -/
theorem gsDot_self_eq_finiteVecNorm2Sq {m : Nat} (x : Fin m -> Real) :
    gsDot x x = finiteVecNorm2Sq x := by
  simp [gsDot, finiteVecNorm2Sq, pow_two]

/-- Dot-product expansion after removing the projection of `x` along `q`. -/
theorem gsDot_projectAway_self {m : Nat} (q x : Fin m -> Real) :
    gsDot q (gsProjectAway x q) = gsDot q x - gsDot q x * gsDot q q := by
  unfold gsDot gsProjectAway
  calc
    (Finset.univ.sum fun i : Fin m => q i * (x i - gsDot q x * q i))
        =
      Finset.univ.sum fun i : Fin m =>
        q i * x i - q i * (gsDot q x * q i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ =
      (Finset.univ.sum fun i : Fin m => q i * x i) -
        (Finset.univ.sum fun i : Fin m => q i * (gsDot q x * q i)) := by
        rw [Finset.sum_sub_distrib]
    _ =
      (Finset.univ.sum fun i : Fin m => q i * x i) -
        gsDot q x * (Finset.univ.sum fun i : Fin m => q i * q i) := by
        congr 1
        calc
          (Finset.univ.sum fun i : Fin m => q i * (gsDot q x * q i))
              = Finset.univ.sum fun i : Fin m =>
                  gsDot q x * (q i * q i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = gsDot q x * Finset.univ.sum fun i : Fin m => q i * q i := by
              rw [Finset.mul_sum]
    _ =
      (Finset.univ.sum fun i : Fin m => q i * x i) -
        (Finset.univ.sum fun i : Fin m => q i * x i) *
          (Finset.univ.sum fun i : Fin m => q i * q i) := by
        rfl

/-- Dot-product expansion after removing the projection of `x` along `q`,
tested against a possibly different vector `u`. -/
theorem gsDot_projectAway_left {m : Nat}
    (u q x : Fin m -> Real) :
    gsDot u (gsProjectAway x q) = gsDot u x - gsDot q x * gsDot u q := by
  unfold gsDot gsProjectAway
  calc
    (Finset.univ.sum fun i : Fin m => u i * (x i - gsDot q x * q i))
        =
      Finset.univ.sum fun i : Fin m =>
        u i * x i - u i * (gsDot q x * q i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ =
      (Finset.univ.sum fun i : Fin m => u i * x i) -
        (Finset.univ.sum fun i : Fin m => u i * (gsDot q x * q i)) := by
        rw [Finset.sum_sub_distrib]
    _ =
      (Finset.univ.sum fun i : Fin m => u i * x i) -
        gsDot q x * (Finset.univ.sum fun i : Fin m => u i * q i) := by
        congr 1
        calc
          (Finset.univ.sum fun i : Fin m => u i * (gsDot q x * q i))
              = Finset.univ.sum fun i : Fin m =>
                  gsDot q x * (u i * q i) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
          _ = gsDot q x * Finset.univ.sum fun i : Fin m => u i * q i := by
              rw [Finset.mul_sum]
    _ =
      (Finset.univ.sum fun i : Fin m => u i * x i) -
        gsDot q x * (Finset.univ.sum fun i : Fin m => u i * q i) := rfl

/-- Removing the projection along a unit vector leaves a vector orthogonal to
that unit vector. -/
theorem gsDot_projectAway_eq_zero_of_unit {m : Nat} (q x : Fin m -> Real)
    (hunit : gsDot q q = 1) :
    gsDot q (gsProjectAway x q) = 0 := by
  rw [gsDot_projectAway_self, hunit]
  ring

/-- Projection removal preserves a prior orthogonality relation when the prior
vector is orthogonal to the projection direction. -/
theorem gsDot_projectAway_eq_zero_of_left_orthogonal {m : Nat}
    (u q x : Fin m -> Real)
    (hux : gsDot u x = 0) (huq : gsDot u q = 0) :
    gsDot u (gsProjectAway x q) = 0 := by
  rw [gsDot_projectAway_left, hux, huq]
  ring

/-- Normalize a column vector by a supplied scalar. -/
def gsNormalize {m : Nat} (x : Fin m -> Real) (r : Real) : Fin m -> Real :=
  fun i => x i / r

/-- Dot product against a normalized right argument factors out the scalar
normalizer. -/
theorem gsDot_normalize_right {m : Nat} (u x : Fin m -> Real) (r : Real) :
    gsDot u (gsNormalize x r) = gsDot u x / r := by
  unfold gsDot gsNormalize
  calc
    (Finset.univ.sum fun i : Fin m => u i * (x i / r))
        = Finset.univ.sum fun i : Fin m => (u i * x i) / r := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (Finset.univ.sum fun i : Fin m => u i * x i) / r := by
            rw [Finset.sum_div]

/-- Euclidean column norm used by the Gram-Schmidt algorithms. -/
def gsColumnNorm2 {m : Nat} (x : Fin m -> Real) : Real :=
  vecNorm2 x

/-- A normalized vector has self-dot equal to the normalizing norm, when the
normalizer is the Euclidean norm and is nonzero. -/
theorem gsDot_normalize_self {m : Nat} (x : Fin m -> Real)
    (hx : Ne (gsColumnNorm2 x) 0) :
    gsDot (gsNormalize x (gsColumnNorm2 x)) x = gsColumnNorm2 x := by
  unfold gsDot gsNormalize gsColumnNorm2
  have hsum :
      (Finset.univ.sum fun i : Fin m => x i / vecNorm2 x * x i) =
        (Finset.univ.sum fun i : Fin m => x i * x i) / vecNorm2 x := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    ring
  rw [hsum]
  have hsq :
      (Finset.univ.sum fun i : Fin m => x i * x i) = vecNorm2 x ^ 2 := by
    simpa [vecNorm2Sq, pow_two] using (vecNorm2_sq x).symm
  rw [hsq]
  have hx' : Ne (vecNorm2 x) 0 := by
    simpa [gsColumnNorm2] using hx
  by_cases hzero : vecNorm2 x = 0
  case pos =>
    exact False.elim (hx' hzero)
  case neg =>
    simp [pow_two, mul_self_div_self]

/-- Normalizing a nonzero vector by its Euclidean norm gives unit squared
norm. -/
theorem gsNormalize_norm_sq {m : Nat} (x : Fin m -> Real)
    (hx : Ne (gsColumnNorm2 x) 0) :
    finiteVecNorm2Sq (gsNormalize x (gsColumnNorm2 x)) = 1 := by
  have hxpos : 0 < vecNorm2 x := by
    exact lt_of_le_of_ne (vecNorm2_nonneg x) (Ne.symm (by
      simpa [gsColumnNorm2] using hx))
  have hnorm :
      vecNorm2 (gsNormalize x (gsColumnNorm2 x)) = 1 := by
    calc
      vecNorm2 (gsNormalize x (gsColumnNorm2 x))
          = vecNorm2 (fun i => (1 / vecNorm2 x) * x i) := by
              congr
              ext i
              simp [gsNormalize, gsColumnNorm2, div_eq_mul_inv, mul_comm]
      _ = |1 / vecNorm2 x| * vecNorm2 x := by
              rw [vecNorm2_smul]
      _ = 1 := by
              have hden : Ne (vecNorm2 x) 0 := ne_of_gt hxpos
              have hdiv_pos : 0 < 1 / vecNorm2 x := by
                positivity
              rw [abs_of_pos hdiv_pos]
              field_simp [hden]
  have hsq :
      vecNorm2Sq (gsNormalize x (gsColumnNorm2 x)) = 1 := by
    rw [<- vecNorm2_sq, hnorm]
    norm_num
  simpa [finiteVecNorm2Sq_fin] using hsq

/-- Reconstruct an `m x n` matrix from its column family. -/
def gsColumnsToMatrix {m n : Nat} (cols : Fin n -> Fin m -> Real) :
    Fin m -> Fin n -> Real :=
  fun i j => cols j i

/-- Classical Gram-Schmidt residual for column `j`, relative to already chosen
columns and coefficients.  This is the source formula
`a_j - sum_{k<j} r_kj q_k` from Algorithm 19.11. -/
def classicalGramSchmidtResidual {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real)
    (j : Fin n) : Fin m -> Real :=
  fun i => A i j -
    Finset.univ.sum
      (fun k : Fin n => if k.val < j.val then R k j * Q i k else 0)

/-- Source-facing state equations for Algorithm 19.11, classical
Gram-Schmidt.  The fields mirror the printed loop: previous projections,
residual norm, normalization, and the upper-triangular shape of `R`. -/
structure ClassicalGramSchmidtState {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real) : Prop where
  upper : IsUpperTrapezoidal n n R
  projection :
    forall i j : Fin n, i.val < j.val ->
      R i j = gsDot (gsColumn Q i) (gsColumn A j)
  diagonal :
    forall j : Fin n,
      R j j = gsColumnNorm2 (classicalGramSchmidtResidual A Q R j)
  normalized :
    forall j : Fin n,
      gsColumn Q j =
        gsNormalize (classicalGramSchmidtResidual A Q R j) (R j j)

/-- One MGS inner-loop update at outer index `k`: later columns have their
projection along the current normalized column removed, while previous/current
columns are left unchanged. -/
def modifiedGramSchmidtStep {m n : Nat}
    (V : Fin n -> Fin m -> Real) (k : Fin n) :
    Fin n -> Fin m -> Real :=
  let qk := gsNormalize (V k) (gsColumnNorm2 (V k))
  fun j => if _h : k < j then gsProjectAway (V j) qk else V j

/-- Exact MGS stage vectors.  Stage `t` stores the columns after applying
outer steps `0, ..., t-1` that exist for the `n`-column input. -/
def modifiedGramSchmidtVectors {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Nat -> Fin n -> Fin m -> Real
  | 0 => fun j => gsColumn A j
  | t + 1 =>
      if ht : t < n then
        modifiedGramSchmidtStep (modifiedGramSchmidtVectors A t) (Fin.mk t ht)
      else
        modifiedGramSchmidtVectors A t

/-- Rectangular multiplication by a standard basis vector selects the
corresponding column. -/
theorem rectMatMulVec_finiteBasisVec_gsColumn {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    rectMatMulVec A (finiteBasisVec j) = gsColumn A j := by
  ext i
  unfold rectMatMulVec finiteBasisVec gsColumn
  simp [Finset.mem_univ]

/-- Rank-to-MGS nonbreakdown base step: if the rectangular column map for `A`
is injective, then no input column has zero norm, so the stage-0 MGS
normalizer is nonzero. -/
theorem modifiedGramSchmidtVectors_zero_norm_ne_zero_of_rectMatMulVec_injective
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hinj : Function.Injective (rectMatMulVec A)) (j : Fin n) :
    gsColumnNorm2 (modifiedGramSchmidtVectors A 0 j) ≠ 0 := by
  intro hnorm
  have hvecnorm : vecNorm2 (gsColumn A j) = 0 := by
    simpa [modifiedGramSchmidtVectors, gsColumnNorm2] using hnorm
  have hcol_zero : gsColumn A j = 0 := by
    ext i
    exact (vecNorm2_eq_zero_iff (gsColumn A j)).mp hvecnorm i
  let e : Fin n -> Real := finiteBasisVec j
  have hAe_zero : rectMatMulVec A e = 0 := by
    rw [rectMatMulVec_finiteBasisVec_gsColumn]
    exact hcol_zero
  have hA0_zero : rectMatMulVec A (0 : Fin n -> Real) = 0 := by
    ext i
    unfold rectMatMulVec
    simp
  have heq : e = (0 : Fin n -> Real) := by
    apply hinj
    rw [hAe_zero, hA0_zero]
  have hone : e j = 1 := by
    simp [e, finiteBasisVec]
  have hzero : e j = 0 := by
    simpa using congrFun heq j
  linarith

/-- Computed MGS `q_j` column from stage `j`. -/
def modifiedGramSchmidtQ {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin m -> Fin n -> Real :=
  fun i j =>
    gsNormalize
      (modifiedGramSchmidtVectors A j.val j)
      (gsColumnNorm2 (modifiedGramSchmidtVectors A j.val j)) i

/-- A computed exact MGS `q_k` column has unit squared norm when its stage
normalizer is nonzero. -/
theorem modifiedGramSchmidtQ_column_norm_sq {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    finiteVecNorm2Sq (gsColumn (modifiedGramSchmidtQ A) k) = 1 := by
  simpa [modifiedGramSchmidtQ, gsColumn] using
    (gsNormalize_norm_sq (modifiedGramSchmidtVectors A k.val k) hdiag)

/-- Computed MGS `R` coefficients.  Below-diagonal entries are definitionally
zero, diagonal entries are the stage norms, and strict upper entries are the
MGS inner-loop dot products. -/
def modifiedGramSchmidtR {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun k j =>
    if _hle : k.val <= j.val then
      if k = j then
        gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)
      else
        gsDot (gsColumn (modifiedGramSchmidtQ A) k)
          (modifiedGramSchmidtVectors A k.val j)
    else
      0

/-- The explicit MGS step updates a later column by projection removal. -/
theorem modifiedGramSchmidtStep_eq_projectAway_of_lt {m n : Nat}
    (V : Fin n -> Fin m -> Real) {k j : Fin n}
    (hkj : k < j) :
    modifiedGramSchmidtStep V k j =
      gsProjectAway (V j) (gsNormalize (V k) (gsColumnNorm2 (V k))) := by
  simp [modifiedGramSchmidtStep, hkj]

/-- The explicit MGS step leaves non-later columns unchanged. -/
theorem modifiedGramSchmidtStep_eq_self_of_not_lt {m n : Nat}
    (V : Fin n -> Fin m -> Real) {k j : Fin n}
    (hkj : Not (k < j)) :
    modifiedGramSchmidtStep V k j = V j := by
  simp [modifiedGramSchmidtStep, hkj]

/-- Advancing from stage `t` to `t+1` applies the MGS step at index `t`. -/
theorem modifiedGramSchmidtVectors_succ_eq_step {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t < n) :
    modifiedGramSchmidtVectors A (t + 1) =
      modifiedGramSchmidtStep (modifiedGramSchmidtVectors A t) (Fin.mk t ht) := by
  simp [modifiedGramSchmidtVectors, ht]

/-- Fin-indexed form of the stage-successor equation. -/
theorem modifiedGramSchmidtVectors_succ_eq_step_fin {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    modifiedGramSchmidtVectors A (k.val + 1) =
      modifiedGramSchmidtStep (modifiedGramSchmidtVectors A k.val) k := by
  simpa using modifiedGramSchmidtVectors_succ_eq_step A k.isLt

/-- A later column at stage `k+1` is obtained by removing the projection onto
the current normalized column. -/
theorem modifiedGramSchmidtVectors_succ_later {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k < j) :
    modifiedGramSchmidtVectors A (k.val + 1) j =
      gsProjectAway (modifiedGramSchmidtVectors A k.val j)
        (gsNormalize (modifiedGramSchmidtVectors A k.val k)
          (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k))) := by
  rw [modifiedGramSchmidtVectors_succ_eq_step_fin A k]
  exact modifiedGramSchmidtStep_eq_projectAway_of_lt
    (modifiedGramSchmidtVectors A k.val) hkj

/-- Exact MGS residuals are always source-column combinations whose coefficient
of the active source column is `1` and whose coefficients on later source
columns are zero.

This linear-combination invariant is independent of nonzero-pivot assumptions:
the algorithmic definitions remain algebraic even when a normalizer is zero. -/
theorem modifiedGramSchmidtVectors_exists_source_coeffs {m n : Nat}
    (A : Fin m -> Fin n -> Real) (t : Nat) (j : Fin n) :
    ∃ c : Fin n -> Real,
      rectMatMulVec A c = modifiedGramSchmidtVectors A t j ∧
        c j = 1 ∧
        ∀ r : Fin n, j.val < r.val -> c r = 0 := by
  revert j
  induction t with
  | zero =>
      intro j
      refine ⟨finiteBasisVec j, ?_, ?_, ?_⟩
      · exact rectMatMulVec_finiteBasisVec_gsColumn A j
      · simp [finiteBasisVec]
      · intro r hjr
        have hrne : r ≠ j := by
          intro hrj
          rw [hrj] at hjr
          exact (Nat.lt_irrefl j.val) hjr
        simp [finiteBasisVec, hrne]
  | succ t ih =>
      intro j
      by_cases ht : t < n
      · let k : Fin n := ⟨t, ht⟩
        by_cases hkj : k < j
        · rcases ih j with ⟨cj, hAcj, hcjj, hcj_supp⟩
          rcases ih k with ⟨ck, hAck, _hckk, hck_supp⟩
          let norm : Real :=
            gsColumnNorm2 (modifiedGramSchmidtVectors A t k)
          let alpha : Real :=
            gsDot (gsNormalize (modifiedGramSchmidtVectors A t k) norm)
              (modifiedGramSchmidtVectors A t j)
          let c : Fin n -> Real := fun r => cj r - (alpha / norm) * ck r
          refine ⟨c, ?_, ?_, ?_⟩
          · have hstep :
                modifiedGramSchmidtVectors A (t + 1) j =
                  gsProjectAway (modifiedGramSchmidtVectors A t j)
                    (gsNormalize (modifiedGramSchmidtVectors A t k)
                      (gsColumnNorm2 (modifiedGramSchmidtVectors A t k))) := by
              simpa [k] using
                (modifiedGramSchmidtVectors_succ_later (A := A)
                  (k := k) (j := j) hkj)
            ext i
            change rectMatMulVec A
                (fun r : Fin n => cj r - (alpha / norm) * ck r) i =
              modifiedGramSchmidtVectors A (t + 1) j i
            rw [hstep]
            rw [congrFun
              (rectMatMulVec_sub A cj
                (fun r : Fin n => (alpha / norm) * ck r)) i]
            rw [congrFun (rectMatMulVec_smul A (alpha / norm) ck) i]
            rw [congrFun hAcj i, congrFun hAck i]
            simp [gsProjectAway, gsNormalize, alpha, norm]
            ring
          · have hckj : ck j = 0 :=
              hck_supp j hkj
            simp [c, hcjj, hckj]
          · intro r hjr
            have hcjr : cj r = 0 := hcj_supp r hjr
            have hkr : k.val < r.val :=
              Nat.lt_trans hkj hjr
            have hckr : ck r = 0 := hck_supp r hkr
            simp [c, hcjr, hckr]
        · rcases ih j with ⟨cj, hAcj, hcjj, hcj_supp⟩
          refine ⟨cj, ?_, hcjj, hcj_supp⟩
          have hsame :
              modifiedGramSchmidtVectors A (t + 1) j =
                modifiedGramSchmidtVectors A t j := by
            rw [modifiedGramSchmidtVectors_succ_eq_step A ht]
            exact modifiedGramSchmidtStep_eq_self_of_not_lt
              (modifiedGramSchmidtVectors A t) hkj
          rw [hsame]
          exact hAcj
      · rcases ih j with ⟨cj, hAcj, hcjj, hcj_supp⟩
        refine ⟨cj, ?_, hcjj, hcj_supp⟩
        have hsame :
            modifiedGramSchmidtVectors A (t + 1) j =
              modifiedGramSchmidtVectors A t j := by
          simp [modifiedGramSchmidtVectors, ht]
        rw [hsame]
        exact hAcj

/-- Rank-to-MGS nonbreakdown for all exact stages: if the rectangular column
map for `A` is injective, then every MGS active residual has nonzero Euclidean
normalizer. -/
theorem modifiedGramSchmidtVectors_norm_ne_zero_of_rectMatMulVec_injective
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hinj : Function.Injective (rectMatMulVec A)) (j : Fin n) :
    gsColumnNorm2 (modifiedGramSchmidtVectors A j.val j) ≠ 0 := by
  rcases modifiedGramSchmidtVectors_exists_source_coeffs A j.val j with
    ⟨c, hAc, hcj, _hc_supp⟩
  intro hnorm
  have hvecnorm : vecNorm2 (modifiedGramSchmidtVectors A j.val j) = 0 := by
    simpa [gsColumnNorm2] using hnorm
  have hstage_zero :
      modifiedGramSchmidtVectors A j.val j = 0 := by
    ext i
    exact
      (vecNorm2_eq_zero_iff
        (modifiedGramSchmidtVectors A j.val j)).mp hvecnorm i
  have hAc_zero : rectMatMulVec A c = 0 := by
    rw [hAc, hstage_zero]
  have hA0_zero : rectMatMulVec A (0 : Fin n -> Real) = 0 := by
    ext i
    simp [rectMatMulVec]
  have hc_eq_zero : c = (0 : Fin n -> Real) := by
    apply hinj
    rw [hAc_zero, hA0_zero]
  have hcj_zero : c j = 0 := by
    simpa using congrFun hc_eq_zero j
  linarith

/-- One exact MGS step makes each later residual column orthogonal to the
current normalized `q_k` column.  This is the local orthogonality atom needed
for the full MGS orthonormal-columns route. -/
theorem modifiedGramSchmidtQ_dot_vectors_succ_later_eq_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k < j)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    gsDot (gsColumn (modifiedGramSchmidtQ A) k)
        (modifiedGramSchmidtVectors A (k.val + 1) j) = 0 := by
  rw [modifiedGramSchmidtVectors_succ_later A hkj]
  apply gsDot_projectAway_eq_zero_of_unit
  have hnorm := modifiedGramSchmidtQ_column_norm_sq A k hdiag
  simpa [gsDot_self_eq_finiteVecNorm2Sq] using hnorm

/-- One MGS projection step preserves an older residual orthogonality relation
provided the older `q_i` column is orthogonal to the current `q_k` column. -/
theorem modifiedGramSchmidtQ_dot_vectors_succ_later_eq_zero_of_prev
    {m n : Nat} (A : Fin m -> Fin n -> Real) {i k j : Fin n}
    (hkj : k < j)
    (hprev :
      gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (modifiedGramSchmidtVectors A k.val j) = 0)
    (hiq :
      gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (gsColumn (modifiedGramSchmidtQ A) k) = 0) :
    gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (modifiedGramSchmidtVectors A (k.val + 1) j) = 0 := by
  rw [modifiedGramSchmidtVectors_succ_later A hkj]
  apply gsDot_projectAway_eq_zero_of_left_orthogonal
  · exact hprev
  · simpa [modifiedGramSchmidtQ, gsColumn] using hiq

/-- If an older `q_i` column is already orthogonal to every intervening
normalized column, then its orthogonality to column `j`'s active residual
persists from the first MGS projection step through stage `j`. -/
theorem modifiedGramSchmidtQ_dot_vectors_stage_eq_zero_of_lt_of_prev
    {m n : Nat} (A : Fin m -> Fin n -> Real) {i j : Fin n}
    (hij : i < j)
    (hdiag_i :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A i.val i)) 0)
    (hprev :
      forall k : Fin n, i.val < k.val -> k.val < j.val ->
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
          (gsColumn (modifiedGramSchmidtQ A) k) = 0) :
    gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (modifiedGramSchmidtVectors A j.val j) = 0 := by
  let P : Nat -> Prop := fun t =>
    t <= j.val ->
      gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (modifiedGramSchmidtVectors A t j) = 0
  have hbase : P (i.val + 1) := by
    intro _hle
    exact modifiedGramSchmidtQ_dot_vectors_succ_later_eq_zero A hij hdiag_i
  have hstep : forall t, i.val + 1 <= t -> P t -> P (t + 1) := by
    intro t hit hP hsucc_le
    have htj : t < j.val := Nat.lt_of_succ_le hsucc_le
    have htn : t < n := Nat.lt_trans htj j.isLt
    let k : Fin n := ⟨t, htn⟩
    have hkj : k < j := by
      simpa [k] using htj
    have hprev_stage :
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
          (modifiedGramSchmidtVectors A k.val j) = 0 := by
      simpa [k] using hP (Nat.le_of_lt htj)
    have hi_k : i.val < k.val := by
      have hi_succ : i.val < i.val + 1 := Nat.lt_succ_self i.val
      exact Nat.lt_of_lt_of_le hi_succ (by simpa [k] using hit)
    have hiq :
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
          (gsColumn (modifiedGramSchmidtQ A) k) = 0 :=
      hprev k hi_k (by simpa [k] using htj)
    simpa [k] using
      modifiedGramSchmidtQ_dot_vectors_succ_later_eq_zero_of_prev
        (A := A) (i := i) (k := k) (j := j) hkj hprev_stage hiq
  have hle : i.val + 1 <= j.val := Nat.succ_le_of_lt hij
  have htarget : P j.val :=
    Nat.le_induction
      (m := i.val + 1)
      (P := fun t _ => P t)
      hbase
      (by
        intro t hit hPt
        exact hstep t hit hPt)
      j.val hle
  exact htarget le_rfl

/-- Conditional pairwise MGS orthogonality: once all intervening normalized
columns are known orthogonal to `q_i`, the final normalized `q_j` column is
orthogonal to `q_i`. -/
theorem modifiedGramSchmidtQ_dot_eq_zero_of_lt_of_prev
    {m n : Nat} (A : Fin m -> Fin n -> Real) {i j : Fin n}
    (hij : i < j)
    (hdiag_i :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A i.val i)) 0)
    (hprev :
      forall k : Fin n, i.val < k.val -> k.val < j.val ->
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
          (gsColumn (modifiedGramSchmidtQ A) k) = 0) :
    gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (gsColumn (modifiedGramSchmidtQ A) j) = 0 := by
  have hstage :=
    modifiedGramSchmidtQ_dot_vectors_stage_eq_zero_of_lt_of_prev
      (A := A) hij hdiag_i hprev
  rw [show gsColumn (modifiedGramSchmidtQ A) j =
      gsNormalize (modifiedGramSchmidtVectors A j.val j)
        (gsColumnNorm2 (modifiedGramSchmidtVectors A j.val j)) by rfl]
  rw [gsDot_normalize_right, hstage]
  simp

/-- Exact MGS produces pairwise orthogonal normalized columns under the
standard nonzero-stage hypothesis. -/
theorem modifiedGramSchmidtQ_dot_eq_zero_of_lt
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hdiag :
      forall k : Fin n,
        Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0)
    {i j : Fin n} (hij : i < j) :
    gsDot (gsColumn (modifiedGramSchmidtQ A) i)
        (gsColumn (modifiedGramSchmidtQ A) j) = 0 := by
  let P : Nat -> Prop := fun t =>
    forall j : Fin n, j.val = t ->
      forall i : Fin n, i < j ->
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
          (gsColumn (modifiedGramSchmidtQ A) j) = 0
  have hmain : forall t, P t := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro j hjt i hij
        apply modifiedGramSchmidtQ_dot_eq_zero_of_lt_of_prev A hij (hdiag i)
        intro k hik hkj
        have hkt : k.val < t := by
          simpa [hjt] using hkj
        exact ih k.val hkt k rfl i (by simpa using hik)
  exact hmain j.val j rfl i hij

/-- MGS `R` is zero below the diagonal by construction. -/
theorem modifiedGramSchmidtR_eq_zero_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {i j : Fin n}
    (hji : j.val < i.val) :
    modifiedGramSchmidtR A i j = 0 := by
  unfold modifiedGramSchmidtR
  have hnot : Not (i.val <= j.val) := Nat.not_le_of_gt hji
  simp [hnot]

/-- The MGS `R` factor has the repository's QR upper-trapezoidal shape. -/
theorem modifiedGramSchmidtR_upper_trapezoidal {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    IsUpperTrapezoidal n n (modifiedGramSchmidtR A) := by
  intro i j hji
  exact modifiedGramSchmidtR_eq_zero_of_lt A hji

/-- Diagonal MGS `R` entries are the stage vector norms. -/
theorem modifiedGramSchmidtR_diag {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    modifiedGramSchmidtR A k k =
      gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k) := by
  unfold modifiedGramSchmidtR
  simp

/-- Strict upper MGS `R` entries are the inner-loop dot products. -/
theorem modifiedGramSchmidtR_strict_upper {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n}
    (hkj : k.val < j.val) :
    modifiedGramSchmidtR A k j =
      gsDot (gsColumn (modifiedGramSchmidtQ A) k)
        (modifiedGramSchmidtVectors A k.val j) := by
  unfold modifiedGramSchmidtR
  have hle : k.val <= j.val := le_of_lt hkj
  have hne : Ne k j := by
    intro h
    have hval : k.val = j.val := congrArg Fin.val h
    have hlt : j.val < j.val := by
      rw [hval] at hkj
      exact hkj
    exact (Nat.lt_irrefl j.val) hlt
  simp [hle, hne]

/-- Source-facing exact Algorithm 19.12 output state. -/
structure ModifiedGramSchmidtState {m n : Nat}
    (A Q : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real) : Prop where
  q_def : Q = modifiedGramSchmidtQ A
  r_def : R = modifiedGramSchmidtR A
  upper : IsUpperTrapezoidal n n R

/-- The concrete exact MGS definitions satisfy the Algorithm 19.12 state
shape. -/
theorem modifiedGramSchmidtState_exact {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    ModifiedGramSchmidtState A (modifiedGramSchmidtQ A)
      (modifiedGramSchmidtR A) := by
  refine {
    q_def := rfl
    r_def := rfl
    upper := modifiedGramSchmidtR_upper_trapezoidal A
  }

/-- Source-style MGS stage matrix `A_t`: columns before `t` are the normalized
`q` columns, while columns from `t` onward are the active stage vectors. -/
def modifiedGramSchmidtSourceStage {m n : Nat}
    (A : Fin m -> Fin n -> Real) (t : Nat) : Fin m -> Fin n -> Real :=
  fun i j =>
    if _h : j.val < t then
      modifiedGramSchmidtQ A i j
    else
      modifiedGramSchmidtVectors A t j i

/-- A source-stage column before the active index is the corresponding `q`
column. -/
theorem modifiedGramSchmidtSourceStage_eq_q_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} {j : Fin n}
    (hjt : j.val < t) :
    gsColumn (modifiedGramSchmidtSourceStage A t) j =
      gsColumn (modifiedGramSchmidtQ A) j := by
  ext i
  simp [modifiedGramSchmidtSourceStage, gsColumn, hjt]

/-- A source-stage column at or after the active index is the stored active
stage vector. -/
theorem modifiedGramSchmidtSourceStage_eq_vector_of_not_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} {j : Fin n}
    (hjt : Not (j.val < t)) :
    gsColumn (modifiedGramSchmidtSourceStage A t) j =
      modifiedGramSchmidtVectors A t j := by
  ext i
  simp [modifiedGramSchmidtSourceStage, gsColumn, hjt]

/-- Source-style one-step MGS factor `R_k`: identity except for the active row,
where it stores the diagonal norm and the projection coefficients. -/
def modifiedGramSchmidtStepR {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n) : Fin n -> Fin n -> Real :=
  fun i j =>
    if _hdiag : i = j then
      if _hcurrent : i = k then
        gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)
      else
        1
    else if _hrow : i = k /\ k < j then
      gsDot (gsColumn (modifiedGramSchmidtQ A) k)
        (modifiedGramSchmidtVectors A k.val j)
    else
      0

/-- The current diagonal entry of `R_k` is the MGS stage norm. -/
theorem modifiedGramSchmidtStepR_current_diag {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    modifiedGramSchmidtStepR A k k k =
      gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k) := by
  simp [modifiedGramSchmidtStepR]

/-- Strict upper entries in the active row of `R_k` are MGS projection
coefficients. -/
theorem modifiedGramSchmidtStepR_current_strict_upper {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n}
    (hkj : k < j) :
    modifiedGramSchmidtStepR A k k j =
      gsDot (gsColumn (modifiedGramSchmidtQ A) k)
        (modifiedGramSchmidtVectors A k.val j) := by
  have hne : Ne k j := ne_of_lt hkj
  simp [modifiedGramSchmidtStepR, hne, hkj]

/-- Away from the active row, the one-step factor has identity diagonal
entries. -/
theorem modifiedGramSchmidtStepR_inactive_diag {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n}
    (hjk : Ne j k) :
    modifiedGramSchmidtStepR A k j j = 1 := by
  simp [modifiedGramSchmidtStepR, hjk]

/-- Away from the active row, the one-step factor is the identity row. -/
theorem modifiedGramSchmidtStepR_inactive_row {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k i : Fin n}
    (hik : Ne i k) (j : Fin n) :
    modifiedGramSchmidtStepR A k i j = idMatrix n i j := by
  by_cases hij : i = j
  case pos =>
    subst j
    simp [modifiedGramSchmidtStepR, idMatrix, hik]
  case neg =>
    have hnotrow : Not (i = k /\ k < j) := by
      intro h
      exact hik h.1
    simp [modifiedGramSchmidtStepR, idMatrix, hij, hnotrow]

/-- The active row of the one-step factor is the corresponding final MGS `R`
row. -/
theorem modifiedGramSchmidtStepR_current_row_eq_R {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k j : Fin n) :
    modifiedGramSchmidtStepR A k k j = modifiedGramSchmidtR A k j := by
  by_cases hkj : k.val < j.val
  case pos =>
    have hfin : k < j := hkj
    rw [modifiedGramSchmidtStepR_current_strict_upper A hfin,
      modifiedGramSchmidtR_strict_upper A hkj]
  case neg =>
    by_cases hjk : j.val < k.val
    case pos =>
      have hnotlt : Not (k < j) := by
        intro h
        exact Nat.lt_asymm hjk h
      have hne : Not (k = j) := by
        intro h
        have hval : k.val = j.val := congrArg Fin.val h
        rw [hval] at hjk
        exact (Nat.lt_irrefl j.val) hjk
      rw [modifiedGramSchmidtR_eq_zero_of_lt A hjk]
      simp [modifiedGramSchmidtStepR, hne, hnotlt]
    case neg =>
      have hle_kj : k.val <= j.val := Nat.le_of_not_gt hjk
      have hle_jk : j.val <= k.val := Nat.le_of_not_gt hkj
      have hval : k.val = j.val := Nat.le_antisymm hle_kj hle_jk
      have hkj_eq : k = j := Fin.ext hval
      subst j
      rw [modifiedGramSchmidtStepR_current_diag,
        modifiedGramSchmidtR_diag]

/-- The source-style one-step `R_k` is upper-trapezoidal. -/
theorem modifiedGramSchmidtStepR_upper_trapezoidal {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n) :
    IsUpperTrapezoidal n n (modifiedGramSchmidtStepR A k) := by
  intro i j hji
  have hne : Not (i = j) := by
    intro hij
    rw [hij] at hji
    exact (Nat.lt_irrefl j.val) hji
  by_cases hik : i = k
  case pos =>
    have hnotlt : Not (k < j) := by
      intro hkj
      have hkjVal : k.val < j.val := hkj
      have hjiK : j.val < k.val := by
        simpa [hik] using hji
      exact (Nat.lt_asymm hjiK) hkjVal
    have hnekj : Not (k = j) := by
      intro hkj
      exact hne (by rw [hik, hkj])
    simp [modifiedGramSchmidtStepR, hik, hnekj, hnotlt]
  case neg =>
    simp [modifiedGramSchmidtStepR, hne, hik]

/-- The current source-stage column recombines from stage `k+1` and the
diagonal entry of `R_k`, assuming the stage norm is nonzero. -/
theorem modifiedGramSchmidtSourceStage_current_recombine {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    gsColumn (modifiedGramSchmidtSourceStage A k.val) k =
      fun i =>
        gsColumn (modifiedGramSchmidtSourceStage A (k.val + 1)) k i *
          modifiedGramSchmidtStepR A k k k := by
  ext i
  have hnot : Not (k.val < k.val) := Nat.lt_irrefl k.val
  have hsucc : k.val < k.val + 1 := Nat.lt_succ_self k.val
  simp [modifiedGramSchmidtSourceStage, gsColumn, modifiedGramSchmidtQ,
    modifiedGramSchmidtStepR, gsNormalize, hsucc]
  field_simp [hdiag]

/-- A later source-stage column recombines from its next-stage residual column
and the active `q_k` column with coefficient `R_k(k,j)`. -/
theorem modifiedGramSchmidtSourceStage_later_recombine {m n : Nat}
    (A : Fin m -> Fin n -> Real) {k j : Fin n} (hkj : k < j) :
    gsColumn (modifiedGramSchmidtSourceStage A k.val) j =
      fun i =>
        gsColumn (modifiedGramSchmidtSourceStage A (k.val + 1)) j i +
          modifiedGramSchmidtStepR A k k j *
            gsColumn (modifiedGramSchmidtSourceStage A (k.val + 1)) k i := by
  ext i
  have hkjVal : k.val < j.val := hkj
  have hnot_jk : Not (j.val < k.val) :=
    fun h => (Nat.lt_asymm h hkjVal)
  have hnot_j_succ : Not (j.val < k.val + 1) :=
    Nat.not_lt_of_ge (Nat.succ_le_of_lt hkjVal)
  have hk_succ : k.val < k.val + 1 := Nat.lt_succ_self k.val
  have hne : Ne k j := ne_of_lt hkj
  have hdot :
      gsDot (gsColumn (modifiedGramSchmidtQ A) k)
          (modifiedGramSchmidtVectors A k.val j) =
        gsDot
          (gsNormalize (modifiedGramSchmidtVectors A k.val k)
            (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)))
          (modifiedGramSchmidtVectors A k.val j) := by
    rfl
  simp [modifiedGramSchmidtSourceStage, gsColumn,
    modifiedGramSchmidtStepR, hne, hkj,
    modifiedGramSchmidtVectors_succ_later A hkj,
    modifiedGramSchmidtQ, gsProjectAway, gsNormalize, hnot_jk,
    hnot_j_succ, hk_succ, hdot]

/-- Source-stage matrix recurrence for one exact MGS step:
`A_k = A_{k+1} R_k`, with the current stage norm required to be nonzero for
the diagonal normalization. -/
theorem modifiedGramSchmidtSourceStage_matrix_recurrence {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    modifiedGramSchmidtSourceStage A k.val =
      matMulRect m n n (modifiedGramSchmidtSourceStage A (k.val + 1))
        (modifiedGramSchmidtStepR A k) := by
  ext i j
  by_cases hjk : j.val < k.val
  case pos =>
    have hj_succ : j.val < k.val + 1 :=
      Nat.lt_trans hjk (Nat.lt_succ_self k.val)
    have hstage :
        modifiedGramSchmidtSourceStage A k.val i j =
          modifiedGramSchmidtSourceStage A (k.val + 1) i j := by
      simp [modifiedGramSchmidtSourceStage, hjk, hj_succ]
    have hnot_kj : Not (k < j) := by
      intro hkj
      have hkjVal : k.val < j.val := hkj
      exact (Nat.lt_asymm hjk) hkjVal
    have hj_ne_k : Not (j = k) := by
      intro hj_eq
      rw [hj_eq] at hjk
      exact (Nat.lt_irrefl k.val) hjk
    have hk_ne_j : Not (k = j) := by
      intro hk_eq
      exact hj_ne_k hk_eq.symm
    have hcol :
        forall c : Fin n,
          modifiedGramSchmidtStepR A k c j = idMatrix n c j := by
      intro c
      by_cases hcj : c = j
      case pos =>
        have hck : Not (c = k) := by
          intro hck
          have hjk_eq : j = k := by
            rw [<- hcj, hck]
          rw [hjk_eq] at hjk
          exact (Nat.lt_irrefl k.val) hjk
        simp [modifiedGramSchmidtStepR, idMatrix, hcj, hj_ne_k]
      case neg =>
        by_cases hck : c = k
        case pos =>
          simp [modifiedGramSchmidtStepR, idMatrix, hck, hnot_kj, hk_ne_j]
        case neg =>
          simp [modifiedGramSchmidtStepR, idMatrix, hcj, hck]
    have hprod :
        matMulRect m n n (modifiedGramSchmidtSourceStage A (k.val + 1))
            (modifiedGramSchmidtStepR A k) i j =
          modifiedGramSchmidtSourceStage A (k.val + 1) i j := by
      unfold matMulRect
      calc
        (Finset.univ.sum fun c : Fin n =>
            modifiedGramSchmidtSourceStage A (k.val + 1) i c *
              modifiedGramSchmidtStepR A k c j)
            =
          Finset.univ.sum fun c : Fin n =>
            modifiedGramSchmidtSourceStage A (k.val + 1) i c *
              idMatrix n c j := by
            apply Finset.sum_congr rfl
            intro c _
            rw [hcol c]
        _ = modifiedGramSchmidtSourceStage A (k.val + 1) i j := by
            simp [idMatrix, Finset.mem_univ]
    rw [hprod]
    exact hstage
  case neg =>
    by_cases hj_eq : j = k
    case pos =>
      subst j
      have hcol :
          forall c : Fin n,
            modifiedGramSchmidtStepR A k c k =
              if c = k then modifiedGramSchmidtStepR A k k k else 0 := by
        intro c
        by_cases hck : c = k
        case pos =>
          simp [hck]
        case neg =>
          simp [modifiedGramSchmidtStepR, hck]
      have hprod :
          matMulRect m n n (modifiedGramSchmidtSourceStage A (k.val + 1))
              (modifiedGramSchmidtStepR A k) i k =
            modifiedGramSchmidtSourceStage A (k.val + 1) i k *
              modifiedGramSchmidtStepR A k k k := by
        unfold matMulRect
        calc
          (Finset.univ.sum fun c : Fin n =>
              modifiedGramSchmidtSourceStage A (k.val + 1) i c *
                modifiedGramSchmidtStepR A k c k)
              =
            Finset.univ.sum fun c : Fin n =>
              modifiedGramSchmidtSourceStage A (k.val + 1) i c *
                (if c = k then modifiedGramSchmidtStepR A k k k else 0) := by
              apply Finset.sum_congr rfl
              intro c _
              rw [hcol c]
          _ = modifiedGramSchmidtSourceStage A (k.val + 1) i k *
                modifiedGramSchmidtStepR A k k k := by
              simp [Finset.mem_univ]
      have hrec :=
        congrFun
          (modifiedGramSchmidtSourceStage_current_recombine A k hdiag) i
      rw [hprod]
      exact hrec
    case neg =>
      have hle : k.val <= j.val := Nat.le_of_not_gt hjk
      have hne_val : Ne k.val j.val := by
        intro hval
        exact hj_eq (Fin.ext hval).symm
      have hkjVal : k.val < j.val := Nat.lt_of_le_of_ne hle hne_val
      have hkj : k < j := hkjVal
      have hne : Ne k j := ne_of_lt hkj
      have hterm :
          forall c : Fin n,
            modifiedGramSchmidtSourceStage A (k.val + 1) i c *
                modifiedGramSchmidtStepR A k c j =
              (if c = j then modifiedGramSchmidtSourceStage A (k.val + 1) i j
                else 0) +
              (if c = k then
                  modifiedGramSchmidtSourceStage A (k.val + 1) i k *
                    modifiedGramSchmidtStepR A k k j
                else 0) := by
        intro c
        by_cases hcj : c = j
        case pos =>
          have hck : Not (c = k) := by
            intro hck
            exact hne (by rw [<- hck, hcj])
          simp [modifiedGramSchmidtStepR, hcj, hj_eq]
        case neg =>
          by_cases hck : c = k
          case pos =>
            simp [modifiedGramSchmidtStepR, hck, hkj, hne]
          case neg =>
            simp [modifiedGramSchmidtStepR, hcj, hck]
      have hprod :
          matMulRect m n n (modifiedGramSchmidtSourceStage A (k.val + 1))
              (modifiedGramSchmidtStepR A k) i j =
            modifiedGramSchmidtSourceStage A (k.val + 1) i j +
              modifiedGramSchmidtStepR A k k j *
                modifiedGramSchmidtSourceStage A (k.val + 1) i k := by
        unfold matMulRect
        calc
          (Finset.univ.sum fun c : Fin n =>
              modifiedGramSchmidtSourceStage A (k.val + 1) i c *
                modifiedGramSchmidtStepR A k c j)
              =
            Finset.univ.sum fun c : Fin n =>
              (if c = j then modifiedGramSchmidtSourceStage A (k.val + 1) i j
                else 0) +
              (if c = k then
                  modifiedGramSchmidtSourceStage A (k.val + 1) i k *
                    modifiedGramSchmidtStepR A k k j
                else 0) := by
              apply Finset.sum_congr rfl
              intro c _
              exact hterm c
          _ =
            (Finset.univ.sum fun c : Fin n =>
              if c = j then modifiedGramSchmidtSourceStage A (k.val + 1) i j
                else 0) +
            (Finset.univ.sum fun c : Fin n =>
              if c = k then
                modifiedGramSchmidtSourceStage A (k.val + 1) i k *
                  modifiedGramSchmidtStepR A k k j
                else 0) := by
              rw [Finset.sum_add_distrib]
          _ = modifiedGramSchmidtSourceStage A (k.val + 1) i j +
                modifiedGramSchmidtSourceStage A (k.val + 1) i k *
                  modifiedGramSchmidtStepR A k k j := by
              simp [Finset.mem_univ]
          _ = modifiedGramSchmidtSourceStage A (k.val + 1) i j +
                modifiedGramSchmidtStepR A k k j *
                  modifiedGramSchmidtSourceStage A (k.val + 1) i k := by
              ring
      have hrec :=
        congrFun (modifiedGramSchmidtSourceStage_later_recombine A hkj) i
      rw [hprod]
      exact hrec

/-- Right multiplication by identity for rectangular matrices. -/
theorem matMulRect_id_right (m n : Nat) (A : Fin m -> Fin n -> Real) :
    matMulRect m n n A (idMatrix n) = A := by
  ext i j
  unfold matMulRect idMatrix
  simp [Finset.sum_ite_eq', Finset.mem_univ]

/-- Associativity for a rectangular matrix multiplied by two square factors:
`(A B) C = A (B C)`. -/
theorem matMulRect_assoc_square_right (m n : Nat)
    (A : Fin m -> Fin n -> Real)
    (B C : Fin n -> Fin n -> Real) :
    matMulRect m n n (matMulRect m n n A B) C =
      matMulRect m n n A (matMul n B C) := by
  ext i j
  unfold matMulRect matMul
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Linearity of right multiplication by a fixed square matrix with respect to
subtracting rectangular left factors. -/
theorem matMulRect_sub_left_square_right {m n : Nat}
    (A B : Fin m -> Fin n -> Real) (R : Fin n -> Fin n -> Real) :
    matMulRect m n n (fun i k => A i k - B i k) R =
      fun i j => matMulRect m n n A R i j -
        matMulRect m n n B R i j := by
  ext i j
  unfold matMulRect
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Linearity of square left multiplication by a fixed square matrix with
respect to subtracting the left factors. -/
theorem matMul_sub_left (n : Nat)
    (A B C : Fin n -> Fin n -> Real) :
    matMul n (fun i k => A i k - B i k) C =
      fun i j => matMul n A C i j - matMul n B C i j := by
  ext i j
  unfold matMul
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]

/-- Linearity of rectangular right multiplication by a fixed rectangular
matrix with respect to subtracting the right factors. -/
theorem matMulRect_sub_right (m n p : Nat)
    (A : Fin m -> Fin n -> Real)
    (B C : Fin n -> Fin p -> Real) :
    matMulRect m n p A (fun k j => B k j - C k j) =
      fun i j => matMulRect m n p A B i j -
        matMulRect m n p A C i j := by
  ext i j
  unfold matMulRect
  rw [<- Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Rectangular operator-2 bounds are stable under matrix addition. -/
theorem rectOpNorm2Le_add {m n : Nat}
    (M N : Fin m -> Fin n -> Real) {c d : Real}
    (hM : rectOpNorm2Le M c) (hN : rectOpNorm2Le N d) :
    rectOpNorm2Le (fun i j => M i j + N i j) (c + d) := by
  intro x
  have hsplit :
      rectMatMulVec (fun i j => M i j + N i j) x =
        fun i => rectMatMulVec M x i + rectMatMulVec N x i := by
    ext i
    unfold rectMatMulVec
    rw [<- Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  calc
    vecNorm2 (fun i => rectMatMulVec M x i + rectMatMulVec N x i)
        <= vecNorm2 (rectMatMulVec M x) + vecNorm2 (rectMatMulVec N x) :=
          vecNorm2_add_le _ _
    _ <= c * vecNorm2 x + d * vecNorm2 x := add_le_add (hM x) (hN x)
    _ = (c + d) * vecNorm2 x := by ring

/-- Rectangular operator-2 bounds are stable under matrix subtraction. -/
theorem rectOpNorm2Le_sub {m n : Nat}
    (M N : Fin m -> Fin n -> Real) {c d : Real}
    (hM : rectOpNorm2Le M c) (hN : rectOpNorm2Le N d) :
    rectOpNorm2Le (fun i j => M i j - N i j) (c + d) := by
  intro x
  have hsplit :
      rectMatMulVec (fun i j => M i j - N i j) x =
        fun i => rectMatMulVec M x i - rectMatMulVec N x i := by
    ext i
    unfold rectMatMulVec
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit]
  calc
    vecNorm2 (fun i => rectMatMulVec M x i - rectMatMulVec N x i)
        <= vecNorm2 (rectMatMulVec M x) +
          vecNorm2 (fun i => -rectMatMulVec N x i) := by
          simpa [sub_eq_add_neg] using
            vecNorm2_add_le (rectMatMulVec M x)
              (fun i => -rectMatMulVec N x i)
    _ = vecNorm2 (rectMatMulVec M x) + vecNorm2 (rectMatMulVec N x) := by
          rw [vecNorm2_neg]
    _ <= c * vecNorm2 x + d * vecNorm2 x := add_le_add (hM x) (hN x)
    _ = (c + d) * vecNorm2 x := by ring

/-- Rectangular operator-2 bounds are stable under negating the matrix. -/
theorem rectOpNorm2Le_neg {m n : Nat} {M : Fin m -> Fin n -> Real}
    {c : Real} (hM : rectOpNorm2Le M c) :
    rectOpNorm2Le (fun i j => -M i j) c := by
  intro x
  have hmul :
      rectMatMulVec (fun i j => -M i j) x =
        fun i => -rectMatMulVec M x i := by
    ext i
    unfold rectMatMulVec
    calc
      (Finset.univ.sum fun j : Fin n => (-M i j) * x j)
          = Finset.univ.sum fun j : Fin n => -(M i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = -(Finset.univ.sum fun j : Fin n => M i j * x j) := by
            rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hM x

/-- A square rectangular operator-2 certificate gives the square operator
predicate used by the source-facing Chapter 19 contracts. -/
theorem opNorm2Le_of_rectOpNorm2Le_square {n : Nat}
    (M : Fin n -> Fin n -> Real) {c : Real}
    (hM : rectOpNorm2Le M c) :
    opNorm2Le M c := by
  intro x
  simpa [opNorm2Le, rectOpNorm2Le, matMulVec, rectMatMulVec] using hM x

/-- Monotonicity of square operator-norm upper-bound predicates in the
radius. -/
theorem qr_opNorm2Le_mono {n : Nat} {M : Fin n -> Fin n -> Real}
    {c d : Real} (hcd : c <= d) (hM : opNorm2Le M c) :
    opNorm2Le M d := by
  intro x
  exact le_trans (hM x)
    (mul_le_mul_of_nonneg_right hcd (vecNorm2_nonneg _))

/-- Square operator-2 bounds are stable under negating the matrix. -/
theorem opNorm2Le_neg {n : Nat} {M : Fin n -> Fin n -> Real}
    {c : Real} (hM : opNorm2Le M c) :
    opNorm2Le (fun i j => -M i j) c := by
  intro x
  have hmul :
      matMulVec n (fun i j => -M i j) x =
        fun i => -matMulVec n M x i := by
    ext i
    unfold matMulVec
    calc
      (Finset.univ.sum fun j : Fin n => (-M i j) * x j)
          = Finset.univ.sum fun j : Fin n => -(M i j * x j) := by
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = -(Finset.univ.sum fun j : Fin n => M i j * x j) := by
            rw [Finset.sum_neg_distrib]
  rw [hmul]
  simpa [vecNorm2_neg] using hM x

/-- Common-`R` algebra used after the orthonormal repair step in Higham's MGS
proof: subtracting two factorizations with the same triangular factor turns
into a product equation for `Qhat - Q`. -/
theorem commonR_difference_product_eq_perturbation_difference {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {R : Fin n -> Fin n -> Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat R)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q R) :
    matMulRect m n n (fun i k => Qhat i k - Q i k) R =
      fun i j => dA1 i j - dA2 i j := by
  ext i j
  have hlin :=
    congrFun
      (congrFun (matMulRect_sub_left_square_right Qhat Q R) i) j
  rw [hlin]
  have hhatij := congrFun (congrFun hhat i) j
  have hQij := congrFun (congrFun hQ i) j
  rw [<- hhatij, <- hQij]
  ring

/-- Right-inverse form of the common-`R` algebra:
`Qhat - Q = (dA1 - dA2) * Rinv` whenever `R * Rinv = I`. -/
theorem commonR_difference_eq_perturbation_difference_mul_right_inverse
    {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {R Rinv : Fin n -> Fin n -> Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat R)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q R)
    (hRright : matMul n R Rinv = idMatrix n) :
    (fun i k => Qhat i k - Q i k) =
      matMulRect m n n (fun i j => dA1 i j - dA2 i j) Rinv := by
  calc
    (fun i k => Qhat i k - Q i k) =
        matMulRect m n n (fun i k => Qhat i k - Q i k) (idMatrix n) := by
          exact (matMulRect_id_right m n
            (fun i k => Qhat i k - Q i k)).symm
    _ = matMulRect m n n (fun i k => Qhat i k - Q i k)
        (matMul n R Rinv) := by
          rw [hRright]
    _ = matMulRect m n n
        (matMulRect m n n (fun i k => Qhat i k - Q i k) R) Rinv := by
          rw [<- matMulRect_assoc_square_right]
    _ = matMulRect m n n (fun i j => dA1 i j - dA2 i j) Rinv := by
          rw [commonR_difference_product_eq_perturbation_difference hhat hQ]

/-- Operator-norm consequence of the common-`R` right-inverse identity:
if `dA1 - dA2` and `Rinv` have rectangular operator-2 certificates, then so
does `Qhat - Q`. -/
theorem commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse
    {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {R Rinv : Fin n -> Fin n -> Real}
    {eta rho : Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat R)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q R)
    (hRright : matMul n R Rinv = idMatrix n)
    (hdiff : rectOpNorm2Le (fun i j => dA1 i j - dA2 i j) eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta) :
    rectOpNorm2Le (fun i k => Qhat i k - Q i k) (eta * rho) := by
  rw [commonR_difference_eq_perturbation_difference_mul_right_inverse
    hhat hQ hRright]
  simpa [matMulRect_eq_rectMatMul] using
    rectOpNorm2Le_rectMatMul
      (fun i j => dA1 i j - dA2 i j) Rinv heta hdiff hRinv

/-- Version of
`commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse`
using separate operator-2 certificates for `dA1` and `dA2`. -/
theorem commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse
    {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {R Rinv : Fin n -> Fin n -> Real}
    {eta1 eta2 rho : Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat R)
    (hQ :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q R)
    (hRright : matMul n R Rinv = idMatrix n)
    (hdA1 : rectOpNorm2Le dA1 eta1)
    (hdA2 : rectOpNorm2Le dA2 eta2)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta1 + eta2) :
    rectOpNorm2Le (fun i k => Qhat i k - Q i k) ((eta1 + eta2) * rho) := by
  exact
    commonR_difference_rectOpNorm2Le_of_perturbation_difference_mul_right_inverse
      hhat hQ hRright (rectOpNorm2Le_sub dA1 dA2 hdA1 hdA2) hRinv heta

/-- One-factor right-inverse cancellation: if `T = X * R` and `R * Rinv = I`,
then `X = T * Rinv`.  This is the top-block analogue of the common-`R`
subtraction algebra used in the MGS sensitivity route. -/
theorem right_factor_eq_product_mul_right_inverse {m n : Nat}
    {X T : Fin m -> Fin n -> Real} {R Rinv : Fin n -> Fin n -> Real}
    (hprod : T = matMulRect m n n X R)
    (hRright : matMul n R Rinv = idMatrix n) :
    X = matMulRect m n n T Rinv := by
  calc
    X = matMulRect m n n X (idMatrix n) := by
          exact (matMulRect_id_right m n X).symm
    _ = matMulRect m n n X (matMul n R Rinv) := by
          rw [hRright]
    _ = matMulRect m n n (matMulRect m n n X R) Rinv := by
          rw [<- matMulRect_assoc_square_right]
    _ = matMulRect m n n T Rinv := by
          rw [<- hprod]

/-- Operator-norm consequence of one-factor right-inverse cancellation. -/
theorem right_factor_rectOpNorm2Le_of_product_mul_right_inverse {m n : Nat}
    {X T : Fin m -> Fin n -> Real} {R Rinv : Fin n -> Fin n -> Real}
    {eta rho : Real}
    (hprod : T = matMulRect m n n X R)
    (hRright : matMul n R Rinv = idMatrix n)
    (hT : rectOpNorm2Le T eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta) :
    rectOpNorm2Le X (eta * rho) := by
  rw [right_factor_eq_product_mul_right_inverse hprod hRright]
  simpa [matMulRect_eq_rectMatMul] using
    rectOpNorm2Le_rectMatMul T Rinv heta hT hRinv

/-- Product of the exact MGS one-step factors through stage `t`, ordered as
`R_(t-1) * ... * R_0`.  This is the exact-arithmetic product appearing in the
source proof route toward Higham equation (19.33). -/
def modifiedGramSchmidtStepRProduct {m n : Nat}
    (A : Fin m -> Fin n -> Real) : Nat -> Fin n -> Fin n -> Real
  | 0 => idMatrix n
  | t + 1 =>
      if ht : t < n then
        matMul n (modifiedGramSchmidtStepR A (Fin.mk t ht))
          (modifiedGramSchmidtStepRProduct A t)
      else
        modifiedGramSchmidtStepRProduct A t

/-- The empty MGS one-step product is the identity matrix. -/
theorem modifiedGramSchmidtStepRProduct_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    modifiedGramSchmidtStepRProduct A 0 = idMatrix n := by
  rfl

/-- Successor equation for the MGS one-step product while the next stage
exists. -/
theorem modifiedGramSchmidtStepRProduct_succ_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t < n) :
    modifiedGramSchmidtStepRProduct A (t + 1) =
      matMul n (modifiedGramSchmidtStepR A (Fin.mk t ht))
        (modifiedGramSchmidtStepRProduct A t) := by
  simp [modifiedGramSchmidtStepRProduct, ht]

/-- Entrywise description of the partial product of MGS one-step factors:
rows already processed agree with the final exact MGS `R`, and inactive rows
remain identity rows. -/
theorem modifiedGramSchmidtStepRProduct_entry {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (i j : Fin n) :
    modifiedGramSchmidtStepRProduct A t i j =
      if i.val < t then modifiedGramSchmidtR A i j else idMatrix n i j := by
  revert i j
  induction t with
  | zero =>
      intro i j
      simp [modifiedGramSchmidtStepRProduct, idMatrix]
  | succ t ih =>
      intro i j
      have ht_lt : t < n := Nat.lt_of_succ_le ht
      have ht_le : t <= n := Nat.le_of_lt ht_lt
      let k : Fin n := Fin.mk t ht_lt
      rw [modifiedGramSchmidtStepRProduct_succ_of_lt A ht_lt]
      by_cases hit : i.val < t
      case pos =>
        have hit_succ : i.val < t + 1 :=
          Nat.lt_trans hit (Nat.lt_succ_self t)
        have hik : Ne i k := by
          intro hik
          have hval : i.val = t := congrArg Fin.val hik
          rw [hval] at hit
          exact (Nat.lt_irrefl t) hit
        have hrow :
            forall l : Fin n,
              modifiedGramSchmidtStepR A k i l = idMatrix n i l := by
          intro l
          exact modifiedGramSchmidtStepR_inactive_row A hik l
        calc
          matMul n (modifiedGramSchmidtStepR A k)
              (modifiedGramSchmidtStepRProduct A t) i j =
              matMul n (idMatrix n)
                (modifiedGramSchmidtStepRProduct A t) i j := by
                unfold matMul
                apply Finset.sum_congr rfl
                intro l _
                rw [hrow l]
          _ = modifiedGramSchmidtStepRProduct A t i j := by
                rw [matMul_id_left]
          _ = modifiedGramSchmidtR A i j := by
                have hih := ih ht_le i j
                simpa [hit] using hih
          _ = if i.val < t + 1 then modifiedGramSchmidtR A i j
                else idMatrix n i j := by
                simp [hit_succ]
      case neg =>
        by_cases hi_eq_t : i.val = t
        case pos =>
          have hik : i = k := Fin.ext hi_eq_t
          subst i
          have hk_succ : k.val < t + 1 := by
            simp [k]
          have hterm :
              forall l : Fin n,
                modifiedGramSchmidtStepR A k k l *
                    modifiedGramSchmidtStepRProduct A t l j =
                  modifiedGramSchmidtStepR A k k l * idMatrix n l j := by
            intro l
            by_cases hlt : l.val < t
            case pos =>
              have hbelow : l.val < k.val := by
                simpa [k] using hlt
              have hzero :
                  modifiedGramSchmidtStepR A k k l = 0 := by
                rw [modifiedGramSchmidtStepR_current_row_eq_R A k l,
                  modifiedGramSchmidtR_eq_zero_of_lt A hbelow]
              rw [hzero]
              ring
            case neg =>
              have hih := ih ht_le l j
              have hprod :
                  modifiedGramSchmidtStepRProduct A t l j =
                    idMatrix n l j := by
                simpa [hlt] using hih
              rw [hprod]
          calc
            matMul n (modifiedGramSchmidtStepR A k)
                (modifiedGramSchmidtStepRProduct A t) k j =
                matMul n (modifiedGramSchmidtStepR A k)
                  (idMatrix n) k j := by
                  unfold matMul
                  apply Finset.sum_congr rfl
                  intro l _
                  exact hterm l
            _ = modifiedGramSchmidtStepR A k k j := by
                  rw [matMul_id_right]
            _ = modifiedGramSchmidtR A k j := by
                  exact modifiedGramSchmidtStepR_current_row_eq_R A k j
            _ = if k.val < t + 1 then modifiedGramSchmidtR A k j
                  else idMatrix n k j := by
                  simp [hk_succ]
        case neg =>
          have hnot_succ : Not (i.val < t + 1) := by
            intro hsucc
            have hle_it : i.val <= t := Nat.lt_succ_iff.mp hsucc
            have hle_ti : t <= i.val := Nat.le_of_not_gt hit
            have hval : i.val = t := Nat.le_antisymm hle_it hle_ti
            exact hi_eq_t hval
          have hik : Ne i k := by
            intro hik
            exact hi_eq_t (congrArg Fin.val hik)
          have hrow :
              forall l : Fin n,
                modifiedGramSchmidtStepR A k i l = idMatrix n i l := by
            intro l
            exact modifiedGramSchmidtStepR_inactive_row A hik l
          calc
            matMul n (modifiedGramSchmidtStepR A k)
                (modifiedGramSchmidtStepRProduct A t) i j =
                matMul n (idMatrix n)
                  (modifiedGramSchmidtStepRProduct A t) i j := by
                  unfold matMul
                  apply Finset.sum_congr rfl
                  intro l _
                  rw [hrow l]
            _ = modifiedGramSchmidtStepRProduct A t i j := by
                  rw [matMul_id_left]
            _ = idMatrix n i j := by
                  have hih := ih ht_le i j
                  simpa [hit] using hih
            _ = if i.val < t + 1 then modifiedGramSchmidtR A i j
                  else idMatrix n i j := by
                  simp [hnot_succ]

/-- The full product of one-step MGS factors is the exact MGS `R` matrix. -/
theorem modifiedGramSchmidtStepRProduct_eq_R {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    modifiedGramSchmidtStepRProduct A n = modifiedGramSchmidtR A := by
  ext i j
  have hentry :=
    modifiedGramSchmidtStepRProduct_entry A (Nat.le_refl n) i j
  simpa [i.isLt] using hentry

/-- Source stage zero is the original input matrix. -/
theorem modifiedGramSchmidtSourceStage_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    modifiedGramSchmidtSourceStage A 0 = A := by
  ext i j
  simp [modifiedGramSchmidtSourceStage, modifiedGramSchmidtVectors,
    gsColumn]

/-- The final source stage is the exact MGS `Q` matrix. -/
theorem modifiedGramSchmidtSourceStage_final {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    modifiedGramSchmidtSourceStage A n = modifiedGramSchmidtQ A := by
  ext i j
  have hjn : j.val < n := j.isLt
  simp [modifiedGramSchmidtSourceStage, hjn]

/-- Iterated source-stage recurrence from the input matrix to stage `t`.
The nonzero diagonal hypothesis is required for every completed stage. -/
theorem modifiedGramSchmidtSourceStage_initial_matrix_recurrence {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (hdiag : forall k : Fin n, k.val < t ->
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    A =
      matMulRect m n n (modifiedGramSchmidtSourceStage A t)
        (modifiedGramSchmidtStepRProduct A t) := by
  induction t with
  | zero =>
      rw [modifiedGramSchmidtStepRProduct_zero, matMulRect_id_right,
        modifiedGramSchmidtSourceStage_zero]
  | succ t ih =>
      have ht_lt : t < n := Nat.lt_of_succ_le ht
      have ht_le : t <= n := Nat.le_of_lt ht_lt
      have hdiag_prev : forall k : Fin n, k.val < t ->
          Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0 := by
        intro k hk
        exact hdiag k (Nat.lt_trans hk (Nat.lt_succ_self t))
      have hdiag_t :
          Ne
            (gsColumnNorm2
              (modifiedGramSchmidtVectors A t (Fin.mk t ht_lt))) 0 :=
        hdiag (Fin.mk t ht_lt) (Nat.lt_succ_self t)
      have hstep :=
        modifiedGramSchmidtSourceStage_matrix_recurrence A
          (Fin.mk t ht_lt) hdiag_t
      calc
        A =
            matMulRect m n n (modifiedGramSchmidtSourceStage A t)
              (modifiedGramSchmidtStepRProduct A t) :=
              ih ht_le hdiag_prev
        _ =
            matMulRect m n n
              (matMulRect m n n
                (modifiedGramSchmidtSourceStage A (t + 1))
                (modifiedGramSchmidtStepR A (Fin.mk t ht_lt)))
              (modifiedGramSchmidtStepRProduct A t) := by
              rw [hstep]
        _ =
            matMulRect m n n
              (modifiedGramSchmidtSourceStage A (t + 1))
              (matMul n (modifiedGramSchmidtStepR A (Fin.mk t ht_lt))
                (modifiedGramSchmidtStepRProduct A t)) := by
              rw [matMulRect_assoc_square_right]
        _ =
            matMulRect m n n
              (modifiedGramSchmidtSourceStage A (t + 1))
              (modifiedGramSchmidtStepRProduct A (t + 1)) := by
              rw [modifiedGramSchmidtStepRProduct_succ_of_lt A ht_lt]

/-- Exact MGS product factorization obtained by iterating the source-stage
recurrence through all columns.  The product factor is the source-style
`R_(n-1) * ... * R_0` product, not yet the full floating-point stability
theorem of Higham Theorem 19.13. -/
theorem modifiedGramSchmidt_exact_product_factorization {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    A =
      matMulRect m n n (modifiedGramSchmidtQ A)
        (modifiedGramSchmidtStepRProduct A n) := by
  have hrec :=
    modifiedGramSchmidtSourceStage_initial_matrix_recurrence A
      (Nat.le_refl n) (fun k _ => hdiag k)
  simpa [modifiedGramSchmidtSourceStage_final A] using hrec

/-- Exact Algorithm 19.12 factorization `A = Q R` for the MGS definitions,
under the nonzero stage-norm assumptions needed for normalization. -/
theorem modifiedGramSchmidt_exact_factorization {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    A =
      matMulRect m n n (modifiedGramSchmidtQ A)
        (modifiedGramSchmidtR A) := by
  rw [<- modifiedGramSchmidtStepRProduct_eq_R A]
  exact modifiedGramSchmidt_exact_product_factorization A hdiag

/-- Top block vector `-e_k` in the Householder-MGS connection. -/
def mgsHouseholderTop {n : Nat} (k : Fin n) : Fin n -> Real :=
  fun i => if i = k then -1 else 0

/-- Source padded matrix `[0; A]` used to relate MGS on `A` to Householder QR
on a matrix with `n` zero rows stacked above `A`. -/
def mgsPaddedInput {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real
  | Sum.inl _i, _j => 0
  | Sum.inr i, j => A i j

/-- Padded stage matrix for the Householder-MGS connection.  After `t`
source reflectors, processed top rows contain the corresponding rows of the
exact MGS `R`, unprocessed top rows are zero, processed bottom columns are
zero, and active bottom columns are the exact MGS stage vectors. -/
def mgsPaddedStage {m n : Nat} (A : Fin m -> Fin n -> Real) (t : Nat) :
    Sum (Fin n) (Fin m) -> Fin n -> Real
  | Sum.inl i, j =>
      if i.val < t then modifiedGramSchmidtR A i j else 0
  | Sum.inr i, j =>
      if j.val < t then 0 else modifiedGramSchmidtVectors A t j i

/-- Final padded block `[R; 0]` for the exact Householder-MGS bridge. -/
def mgsPaddedRBlock {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real
  | Sum.inl i, j => modifiedGramSchmidtR A i j
  | Sum.inr _i, _j => 0

/-- Top `n x n` block of a padded Householder-MGS matrix. -/
def mgsPaddedTopBlock {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  fun i j => B (Sum.inl i) j

/-- Bottom `m x n` block of a padded Householder-MGS matrix. -/
def mgsPaddedBottomBlock {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  fun i j => B (Sum.inr i) j

/-- Reassemble a padded Householder-MGS matrix from explicit top and bottom
blocks. -/
def mgsStackedBlocks {m n : Nat}
    (Top : Fin n -> Fin n -> Real) (Bottom : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real
  | Sum.inl i, j => Top i j
  | Sum.inr i, j => Bottom i j

/-- Padded input with explicit top and bottom perturbation blocks.  This is
the source shape `[Delta A3; A + Delta A4]` in `(19.34)`. -/
def mgsPaddedPerturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  mgsStackedBlocks dTop (fun i j => A i j + dBottom i j)

/-- Top perturbation block extracted from a padded matrix relative to
`[0; A]`. -/
def mgsPaddedTopPerturbation {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsPaddedTopBlock B

/-- Bottom perturbation block extracted from a padded matrix relative to
`[0; A]`. -/
def mgsPaddedBottomPerturbation {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin m -> Fin n -> Real :=
  fun i j => mgsPaddedBottomBlock B i j - A i j

/-- Row index map from the sum-indexed padded matrix shape to `Fin (n + m)`.
Top rows occupy the first `n` positions and bottom rows occupy the last `m`
positions. -/
def mgsPaddedRowToFin {m n : Nat} :
    Sum (Fin n) (Fin m) -> Fin (n + m)
  | Sum.inl i => Fin.castAdd m i
  | Sum.inr i => Fin.natAdd n i

/-- Read a `Fin (n + m)` padded row as either a top or bottom row. -/
def mgsPaddedRowFromFin {m n : Nat}
    (r : Fin (n + m)) : Sum (Fin n) (Fin m) :=
  Fin.addCases (fun i : Fin n => Sum.inl i)
    (fun i : Fin m => Sum.inr i) r

/-- Convert a sum-indexed padded matrix into the `Fin (n + m)` row shape used
by the generic Householder QR theorem. -/
def mgsPaddedRowsToFin {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Fin (n + m) -> Fin n -> Real :=
  fun r j => B (mgsPaddedRowFromFin r) j

/-- Convert a `Fin (n + m)` row-indexed padded matrix back to the explicit
top/bottom sum-indexed shape. -/
def mgsPaddedRowsFromFin {m n : Nat}
    (C : Fin (n + m) -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  fun a j => C (mgsPaddedRowToFin a) j

/-- The matrix `[0; A]` in the row shape expected by the generic Householder
QR theorem. -/
def mgsPaddedFinInput {m n : Nat} (A : Fin m -> Fin n -> Real) :
    Fin (n + m) -> Fin n -> Real :=
  mgsPaddedRowsToFin (mgsPaddedInput A)

/-- Equivalence between explicit top/bottom padded rows and the contiguous
`Fin (n + m)` row indexing used by generic QR theorems. -/
def mgsPaddedRowEquivFin {m n : Nat} :
    Equiv (Sum (Fin n) (Fin m)) (Fin (n + m)) where
  toFun := mgsPaddedRowToFin
  invFun := mgsPaddedRowFromFin
  left_inv := by
    intro a
    cases a with
    | inl i =>
        simp [mgsPaddedRowFromFin, mgsPaddedRowToFin]
    | inr i =>
        simp [mgsPaddedRowFromFin, mgsPaddedRowToFin]
  right_inv := by
    intro r
    cases r using Fin.addCases with
    | left i =>
        simp [mgsPaddedRowFromFin, mgsPaddedRowToFin]
    | right i =>
        simp [mgsPaddedRowFromFin, mgsPaddedRowToFin]

/-- Euclidean norm of one column of a sum-indexed padded matrix. -/
noncomputable def mgsPaddedColumnNorm {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) (j : Fin n) : Real :=
  finiteVecNorm2 fun a : Sum (Fin n) (Fin m) => B a j

/-- Column norm of the stacked perturbation `[Delta A3; Delta A4]` appearing
in `(19.34)`. -/
noncomputable def mgsStackedPerturbationColumnNorm {m n : Nat}
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (j : Fin n) : Real :=
  mgsPaddedColumnNorm (mgsStackedBlocks dTop dBottom) j

/-- Columnwise perturbation-bound shape for the stacked perturbation
`[Delta A3; Delta A4]` in `(19.34)`. -/
def mgsStackedPerturbationColumnwiseBound {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (c : Real) : Prop :=
  forall j : Fin n,
    mgsStackedPerturbationColumnNorm dTop dBottom j <=
      c * columnFrob A j

/-- Source vector `[-e_k; q_k]` used in the Householder-MGS connection. -/
def mgsHouseholderVector {m n : Nat} (q : Fin m -> Real) (k : Fin n) :
    Sum (Fin n) (Fin m) -> Real :=
  sumBothVec (mgsHouseholderTop k) q

/-- Source reflector `P_k = I - v_k v_k^T` from the Householder-MGS bridge. -/
def mgsHouseholderReflector {m n : Nat} (q : Fin m -> Real) (k : Fin n) :
    Sum (Fin n) (Fin m) -> Sum (Fin n) (Fin m) -> Real :=
  fun a b =>
    finiteIdMatrix a b -
      mgsHouseholderVector q k a * mgsHouseholderVector q k b

/-- Column inner product `v_k^T b_j` for a sum-indexed padded column. -/
def mgsHouseholderColumnInner {m n : Nat}
    (q : Fin m -> Real) (k : Fin n)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) (j : Fin n) : Real :=
  Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
    mgsHouseholderVector q k a * B a j

/-- Apply the source reflector `P_k` to a padded matrix columnwise. -/
def mgsHouseholderApply {m n : Nat}
    (q : Fin m -> Real) (k : Fin n)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    Sum (Fin n) (Fin m) -> Fin n -> Real :=
  fun a j =>
    finiteMatVec (mgsHouseholderReflector q k) (fun b => B b j) a

@[simp] theorem mgsPaddedInput_top {m n : Nat}
    (A : Fin m -> Fin n -> Real) (i : Fin n) (j : Fin n) :
    mgsPaddedInput A (Sum.inl i) j = 0 := rfl

@[simp] theorem mgsPaddedInput_bottom {m n : Nat}
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n) :
    mgsPaddedInput A (Sum.inr i) j = A i j := rfl

theorem mgsPaddedTopBlock_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedTopBlock (mgsPaddedInput A) =
      (fun _ _ => 0 : Fin n -> Fin n -> Real) := by
  rfl

theorem mgsPaddedBottomBlock_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedBottomBlock (mgsPaddedInput A) = A := by
  rfl

theorem mgsPaddedTopBlock_paddedRBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedTopBlock (mgsPaddedRBlock A) =
      modifiedGramSchmidtR A := by
  rfl

theorem mgsPaddedBottomBlock_paddedRBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedBottomBlock (mgsPaddedRBlock A) =
      (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  rfl

theorem mgsPaddedTopBlock_stackedBlocks {m n : Nat}
    (Top : Fin n -> Fin n -> Real) (Bottom : Fin m -> Fin n -> Real) :
    mgsPaddedTopBlock (mgsStackedBlocks Top Bottom) = Top := by
  rfl

theorem mgsPaddedBottomBlock_stackedBlocks {m n : Nat}
    (Top : Fin n -> Fin n -> Real) (Bottom : Fin m -> Fin n -> Real) :
    mgsPaddedBottomBlock (mgsStackedBlocks Top Bottom) = Bottom := by
  rfl

theorem mgsPaddedTopBlock_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    mgsPaddedTopBlock (mgsPaddedPerturbedInput A dTop dBottom) =
      dTop := by
  rfl

theorem mgsPaddedBottomBlock_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    mgsPaddedBottomBlock (mgsPaddedPerturbedInput A dTop dBottom) =
      (fun i j => A i j + dBottom i j) := by
  rfl

theorem mgsPaddedTopPerturbation_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    mgsPaddedTopPerturbation (mgsPaddedPerturbedInput A dTop dBottom) =
      dTop := by
  rfl

theorem mgsPaddedBottomPerturbation_perturbedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real) :
    mgsPaddedBottomPerturbation A
        (mgsPaddedPerturbedInput A dTop dBottom) =
      dBottom := by
  ext i j
  dsimp [mgsPaddedBottomPerturbation, mgsPaddedBottomBlock,
    mgsPaddedPerturbedInput, mgsStackedBlocks]
  ring

theorem mgsPaddedPerturbedInput_eta {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    mgsPaddedPerturbedInput A
        (mgsPaddedTopPerturbation B)
        (mgsPaddedBottomPerturbation A B) =
      B := by
  ext a j
  cases a with
  | inl i =>
      rfl
  | inr i =>
      dsimp [mgsPaddedPerturbedInput, mgsStackedBlocks,
        mgsPaddedBottomPerturbation, mgsPaddedBottomBlock]
      ring

@[simp] theorem mgsPaddedRowFromFin_toFin_inl {m n : Nat}
    (i : Fin n) :
    mgsPaddedRowFromFin (m := m) (n := n)
      (mgsPaddedRowToFin (Sum.inl i)) = Sum.inl i := by
  simp [mgsPaddedRowFromFin, mgsPaddedRowToFin]

@[simp] theorem mgsPaddedRowFromFin_toFin_inr {m n : Nat}
    (i : Fin m) :
    mgsPaddedRowFromFin (m := m) (n := n)
      (mgsPaddedRowToFin (Sum.inr i)) = Sum.inr i := by
  simp [mgsPaddedRowFromFin, mgsPaddedRowToFin]

theorem mgsPaddedRowsFromFin_toFin {m n : Nat}
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    mgsPaddedRowsFromFin (mgsPaddedRowsToFin B) = B := by
  ext a j
  cases a with
  | inl i =>
      simp [mgsPaddedRowsFromFin, mgsPaddedRowsToFin]
  | inr i =>
      simp [mgsPaddedRowsFromFin, mgsPaddedRowsToFin]

theorem mgsPaddedRowsToFin_fromFin {m n : Nat}
    (C : Fin (n + m) -> Fin n -> Real) :
    mgsPaddedRowsToFin (mgsPaddedRowsFromFin C) = C := by
  ext r j
  cases r using Fin.addCases with
  | left i =>
      simp [mgsPaddedRowsFromFin, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, mgsPaddedRowToFin]
  | right i =>
      simp [mgsPaddedRowsFromFin, mgsPaddedRowsToFin,
        mgsPaddedRowFromFin, mgsPaddedRowToFin]

theorem mgsPaddedRowsFromFin_finInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedRowsFromFin (mgsPaddedFinInput A) = mgsPaddedInput A := by
  exact mgsPaddedRowsFromFin_toFin (mgsPaddedInput A)

/-- Economy-size bottom-left `Q` block induced by the padded
Householder-MGS row split. -/
def mgsPaddedEconomyQ {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real) :
    Fin m -> Fin n -> Real :=
  fun i k => Q (mgsPaddedRowToFin (Sum.inr i))
    (mgsPaddedRowToFin (Sum.inl k))

/-- Top-left `P11` block induced by the padded Householder-MGS row split. -/
def mgsPaddedEconomyP11 {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real) :
    Fin n -> Fin n -> Real :=
  fun i k => Q (mgsPaddedRowToFin (Sum.inl i))
    (mgsPaddedRowToFin (Sum.inl k))

/-- Top `n x n` `R` block induced by the padded Householder-MGS row split. -/
def mgsPaddedEconomyR {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  mgsPaddedTopBlock (mgsPaddedRowsFromFin R)

theorem mgsPaddedEconomyR_upper_trapezoidal {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real)
    (hR : IsUpperTrapezoidal (n + m) n R) :
    IsUpperTrapezoidal n n (mgsPaddedEconomyR R) := by
  intro i j hji
  unfold mgsPaddedEconomyR mgsPaddedTopBlock mgsPaddedRowsFromFin
    mgsPaddedRowToFin
  exact hR (Fin.castAdd m i) j (by simpa using hji)

theorem mgsPaddedTopBlock_rowsFromFin {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real) :
    mgsPaddedTopBlock (mgsPaddedRowsFromFin R) =
      (fun i j => R (mgsPaddedRowToFin (Sum.inl i)) j) := by
  rfl

theorem mgsPaddedBottomBlock_rowsFromFin {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real) :
    mgsPaddedBottomBlock (mgsPaddedRowsFromFin R) =
      (fun i j => R (mgsPaddedRowToFin (Sum.inr i)) j) := by
  rfl

/-- Top block of a padded product, after the lower block of the right factor has
vanished.  This is the `Delta A3 = P11 * R11` block needed by the
source-facing CS/polar repair step in Higham's proof of Theorem 19.13. -/
theorem mgsPaddedTopBlock_rowsFromFin_matMul_of_bottom_zero {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hRbot :
      mgsPaddedBottomBlock (mgsPaddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    mgsPaddedTopBlock
        (mgsPaddedRowsFromFin (matMulRect (n + m) (n + m) n Q R)) =
      matMulRect n n n (mgsPaddedEconomyP11 Q) (mgsPaddedEconomyR R) := by
  ext i j
  unfold mgsPaddedTopBlock mgsPaddedRowsFromFin matMulRect
  rw [Fin.sum_univ_add]
  have htail :
      (Finset.univ.sum fun k : Fin m =>
        Q (mgsPaddedRowToFin (Sum.inl i)) (Fin.natAdd n k) *
          R (Fin.natAdd n k) j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _hk
    have hR : R (Fin.natAdd n k) j = 0 := by
      have h := congrFun (congrFun hRbot k) j
      simpa [mgsPaddedBottomBlock, mgsPaddedRowsFromFin,
        mgsPaddedRowToFin] using h
    rw [hR, mul_zero]
  rw [htail, add_zero]
  simp [mgsPaddedEconomyP11, mgsPaddedEconomyR, mgsPaddedTopBlock,
    mgsPaddedRowsFromFin, mgsPaddedRowToFin]

theorem mgsPaddedBottomBlock_rowsFromFin_of_upper {m n : Nat}
    (R : Fin (n + m) -> Fin n -> Real)
    (hR : IsUpperTrapezoidal (n + m) n R) :
    mgsPaddedBottomBlock (mgsPaddedRowsFromFin R) =
      (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  ext i j
  unfold mgsPaddedBottomBlock mgsPaddedRowsFromFin mgsPaddedRowToFin
  have hlt : j.val < (Fin.natAdd n i).val := by
    exact Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right n i.val)
  exact hR (Fin.natAdd n i) j hlt

/-- Bottom block of a padded product, after the lower block of the right
factor has vanished.  This is the algebraic economy-product bridge consumed by
the QR-sensitivity step after equation `(19.34)`. -/
theorem mgsPaddedBottomBlock_rowsFromFin_matMul_of_bottom_zero {m n : Nat}
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hRbot :
      mgsPaddedBottomBlock (mgsPaddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    mgsPaddedBottomBlock
        (mgsPaddedRowsFromFin (matMulRect (n + m) (n + m) n Q R)) =
      matMulRect m n n (mgsPaddedEconomyQ Q) (mgsPaddedEconomyR R) := by
  ext i j
  unfold mgsPaddedBottomBlock mgsPaddedRowsFromFin matMulRect
  rw [Fin.sum_univ_add]
  have htail :
      (Finset.univ.sum fun k : Fin m =>
        Q (mgsPaddedRowToFin (Sum.inr i)) (Fin.natAdd n k) *
          R (Fin.natAdd n k) j) = 0 := by
    apply Finset.sum_eq_zero
    intro k _hk
    have hR : R (Fin.natAdd n k) j = 0 := by
      have h := congrFun (congrFun hRbot k) j
      simpa [mgsPaddedBottomBlock, mgsPaddedRowsFromFin,
        mgsPaddedRowToFin] using h
    rw [hR, mul_zero]
  rw [htail, add_zero]
  simp [mgsPaddedEconomyQ, mgsPaddedEconomyR, mgsPaddedTopBlock,
    mgsPaddedRowsFromFin, mgsPaddedRowToFin]

/-- Bottom-block consequence of a padded perturbed-input product.  It turns
`[Delta A3; A + Delta A4] = Q * Rhat` plus zero lower `Rhat` block into the
economy product `A + Delta A4 = Q21 * R11`. -/
theorem mgsPaddedPerturbedInput_bottom_eq_economyProduct {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hprod :
      mgsPaddedPerturbedInput A dTop dBottom =
        mgsPaddedRowsFromFin (matMulRect (n + m) (n + m) n Q R))
    (hRbot :
      mgsPaddedBottomBlock (mgsPaddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    (fun i j => A i j + dBottom i j) =
      matMulRect m n n (mgsPaddedEconomyQ Q) (mgsPaddedEconomyR R) := by
  calc
    (fun i j => A i j + dBottom i j) =
        mgsPaddedBottomBlock
          (mgsPaddedPerturbedInput A dTop dBottom) := by
          rw [mgsPaddedBottomBlock_perturbedInput A dTop dBottom]
    _ =
        mgsPaddedBottomBlock
          (mgsPaddedRowsFromFin (matMulRect (n + m) (n + m) n Q R)) := by
          rw [hprod]
    _ = matMulRect m n n (mgsPaddedEconomyQ Q)
          (mgsPaddedEconomyR R) := by
          exact mgsPaddedBottomBlock_rowsFromFin_matMul_of_bottom_zero Q R hRbot

/-- Top-block consequence of a padded perturbed-input product.  It preserves the
source block equation `Delta A3 = P11 * R11` from `(19.34)`, which is needed
before the orthonormal-repair argument can be instantiated. -/
theorem mgsPaddedPerturbedInput_top_eq_economyProduct {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (Q : Fin (n + m) -> Fin (n + m) -> Real)
    (R : Fin (n + m) -> Fin n -> Real)
    (hprod :
      mgsPaddedPerturbedInput A dTop dBottom =
        mgsPaddedRowsFromFin (matMulRect (n + m) (n + m) n Q R))
    (hRbot :
      mgsPaddedBottomBlock (mgsPaddedRowsFromFin R) =
        (fun _ _ => 0 : Fin m -> Fin n -> Real)) :
    dTop =
      matMulRect n n n (mgsPaddedEconomyP11 Q) (mgsPaddedEconomyR R) := by
  calc
    dTop =
        mgsPaddedTopBlock
          (mgsPaddedPerturbedInput A dTop dBottom) := by
          rw [mgsPaddedTopBlock_perturbedInput A dTop dBottom]
    _ =
        mgsPaddedTopBlock
          (mgsPaddedRowsFromFin (matMulRect (n + m) (n + m) n Q R)) := by
          rw [hprod]
    _ = matMulRect n n n (mgsPaddedEconomyP11 Q)
          (mgsPaddedEconomyR R) := by
          exact mgsPaddedTopBlock_rowsFromFin_matMul_of_bottom_zero Q R hRbot

theorem finiteVecNorm2_column_eq_columnFrob {m p : Nat}
    (A : Fin m -> Fin p -> Real) (j : Fin p) :
    finiteVecNorm2 (fun i : Fin m => A i j) = columnFrob A j := by
  unfold finiteVecNorm2 finiteVecNorm2Sq columnFrob
  rw [frobNorm_eq_sqrt_frobNormSq]
  congr 1
  unfold frobNormSq
  simp

theorem finiteVecNorm2_le_sumBothVec_right {IdxLeft IdxRight : Type*}
    [Fintype IdxLeft] [Fintype IdxRight]
    (x : IdxLeft -> Real) (y : IdxRight -> Real) :
    finiteVecNorm2 y <= finiteVecNorm2 (sumBothVec x y) := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_sumBothVec]
  apply Real.sqrt_le_sqrt
  have hx : 0 <= finiteVecNorm2Sq x := finiteVecNorm2Sq_nonneg x
  nlinarith

theorem finiteVecNorm2_le_sumBothVec_left {IdxLeft IdxRight : Type*}
    [Fintype IdxLeft] [Fintype IdxRight]
    (x : IdxLeft -> Real) (y : IdxRight -> Real) :
    finiteVecNorm2 x <= finiteVecNorm2 (sumBothVec x y) := by
  unfold finiteVecNorm2
  rw [finiteVecNorm2Sq_sumBothVec]
  apply Real.sqrt_le_sqrt
  have hy : 0 <= finiteVecNorm2Sq y := finiteVecNorm2Sq_nonneg y
  nlinarith

theorem mgsTopPerturbationColumnNorm_le_stacked {m n : Nat}
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (j : Fin n) :
    columnFrob dTop j <=
      mgsStackedPerturbationColumnNorm dTop dBottom j := by
  rw [<- finiteVecNorm2_column_eq_columnFrob dTop j]
  unfold mgsStackedPerturbationColumnNorm mgsPaddedColumnNorm
  have hshape :
      (fun a : Sum (Fin n) (Fin m) => mgsStackedBlocks dTop dBottom a j) =
        sumBothVec (fun i : Fin n => dTop i j)
          (fun i : Fin m => dBottom i j) := by
    ext a
    cases a with
    | inl i => rfl
    | inr i => rfl
  rw [hshape]
  exact finiteVecNorm2_le_sumBothVec_left
    (fun i : Fin n => dTop i j) (fun i : Fin m => dBottom i j)

theorem mgsBottomPerturbationColumnNorm_le_stacked {m n : Nat}
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    (j : Fin n) :
    columnFrob dBottom j <=
      mgsStackedPerturbationColumnNorm dTop dBottom j := by
  rw [<- finiteVecNorm2_column_eq_columnFrob dBottom j]
  unfold mgsStackedPerturbationColumnNorm mgsPaddedColumnNorm
  have hshape :
      (fun a : Sum (Fin n) (Fin m) => mgsStackedBlocks dTop dBottom a j) =
        sumBothVec (fun i : Fin n => dTop i j)
          (fun i : Fin m => dBottom i j) := by
    ext a
    cases a with
    | inl i => rfl
    | inr i => rfl
  rw [hshape]
  exact finiteVecNorm2_le_sumBothVec_right
    (fun i : Fin n => dTop i j) (fun i : Fin m => dBottom i j)

/-- The stacked columnwise budget from `(19.34)` controls each top-block
perturbation column. -/
theorem mgsTopPerturbation_columnFrob_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real}
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c) :
    forall j, columnFrob dTop j <= c * columnFrob A j := by
  intro j
  exact (mgsTopPerturbationColumnNorm_le_stacked dTop dBottom j).trans
    (hbound j)

/-- The stacked columnwise budget from `(19.34)` controls each bottom-block
perturbation column. -/
theorem mgsBottomPerturbation_columnFrob_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real}
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c) :
    forall j, columnFrob dBottom j <= c * columnFrob A j := by
  intro j
  exact (mgsBottomPerturbationColumnNorm_le_stacked dTop dBottom j).trans
    (hbound j)

theorem mgsTopPerturbation_frobNormRect_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real} (hc : 0 <= c)
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c) :
    frobNormRect dTop <= c * frobNormRect A := by
  apply frobNormRect_le_of_col_vecNorm2_le_rect dTop A hc
  intro j
  rw [<- finiteVecNorm2_fin (fun i : Fin n => dTop i j),
    <- finiteVecNorm2_fin (fun i : Fin m => A i j),
    finiteVecNorm2_column_eq_columnFrob dTop j,
    finiteVecNorm2_column_eq_columnFrob A j]
  exact (mgsTopPerturbationColumnNorm_le_stacked dTop dBottom j).trans
    (hbound j)

theorem mgsTopPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c residualBound : Real} (hc : 0 <= c)
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c)
    (hresidual :
      c * frobNormRect A <= residualBound) :
    rectOpNorm2Le dTop residualBound := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact
    (mgsTopPerturbation_frobNormRect_le_of_stackedColumnwiseBound
      A dTop dBottom hc hbound).trans hresidual

theorem mgsBottomPerturbation_frobNormRect_le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c : Real} (hc : 0 <= c)
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c) :
    frobNormRect dBottom <= c * frobNormRect A := by
  apply frobNormRect_le_of_col_vecNorm2_le dBottom A hc
  intro j
  rw [<- finiteVecNorm2_fin (fun i : Fin m => dBottom i j),
    <- finiteVecNorm2_fin (fun i : Fin m => A i j),
    finiteVecNorm2_column_eq_columnFrob dBottom j,
    finiteVecNorm2_column_eq_columnFrob A j]
  exact (mgsBottomPerturbationColumnNorm_le_stacked dTop dBottom j).trans
    (hbound j)

theorem mgsBottomPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dTop : Fin n -> Fin n -> Real) (dBottom : Fin m -> Fin n -> Real)
    {c residualBound : Real} (hc : 0 <= c)
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c)
    (hresidual :
      c * frobNormRect A <= residualBound) :
    rectOpNorm2Le dBottom residualBound := by
  apply rectOpNorm2Le_of_frobNormRect_le
  exact
    (mgsBottomPerturbation_frobNormRect_le_of_stackedColumnwiseBound
      A dTop dBottom hc hbound).trans hresidual

theorem mgsPaddedColumnNorm_rowsFromFin {m n : Nat}
    (C : Fin (n + m) -> Fin n -> Real) (j : Fin n) :
    mgsPaddedColumnNorm (mgsPaddedRowsFromFin C) j = columnFrob C j := by
  unfold mgsPaddedColumnNorm finiteVecNorm2 finiteVecNorm2Sq columnFrob
  rw [frobNorm_eq_sqrt_frobNormSq]
  congr 1
  calc
    (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
        mgsPaddedRowsFromFin C a j ^ 2)
        = Finset.univ.sum fun r : Fin (n + m) => C r j ^ 2 := by
            unfold mgsPaddedRowsFromFin
            exact
              Fintype.sum_equiv
                (mgsPaddedRowEquivFin (m := m) (n := n))
                (fun a : Sum (Fin n) (Fin m) =>
                  C (mgsPaddedRowToFin a) j ^ 2)
                (fun r : Fin (n + m) => C r j ^ 2)
                (fun _a => rfl)
    _ = frobNormSq (fun r (_ : Fin 1) => C r j) := by
            unfold frobNormSq
            simp

theorem mgsPaddedColumnNorm_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    mgsPaddedColumnNorm (mgsPaddedInput A) j = columnFrob A j := by
  unfold mgsPaddedColumnNorm
  rw [show (fun a : Sum (Fin n) (Fin m) => mgsPaddedInput A a j) =
      @sumInrVec (Fin n) (Fin m) (fun i : Fin m => A i j) by
        ext a
        cases a with
        | inl i =>
            rfl
        | inr i =>
            rfl]
  rw [finiteVecNorm2_sumInrVec]
  exact finiteVecNorm2_column_eq_columnFrob A j

theorem columnFrob_paddedFinInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) (j : Fin n) :
    columnFrob (mgsPaddedFinInput A) j = columnFrob A j := by
  rw [<- mgsPaddedColumnNorm_rowsFromFin (mgsPaddedFinInput A) j]
  rw [mgsPaddedRowsFromFin_finInput]
  exact mgsPaddedColumnNorm_paddedInput A j

theorem mgsStackedPerturbationColumnNorm_rowsFromFin_add {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (dA : Fin (n + m) -> Fin n -> Real) (j : Fin n) :
    mgsStackedPerturbationColumnNorm
        (mgsPaddedTopPerturbation
          (mgsPaddedRowsFromFin
            (fun r j => mgsPaddedFinInput A r j + dA r j)))
        (mgsPaddedBottomPerturbation A
          (mgsPaddedRowsFromFin
            (fun r j => mgsPaddedFinInput A r j + dA r j))) j =
      columnFrob dA j := by
  have hblocks :
      mgsStackedBlocks
          (mgsPaddedTopPerturbation
            (mgsPaddedRowsFromFin
              (fun r j => mgsPaddedFinInput A r j + dA r j)))
          (mgsPaddedBottomPerturbation A
            (mgsPaddedRowsFromFin
              (fun r j => mgsPaddedFinInput A r j + dA r j))) =
        mgsPaddedRowsFromFin dA := by
    ext a k
    cases a with
    | inl i =>
        simp [mgsStackedBlocks, mgsPaddedTopPerturbation,
          mgsPaddedTopBlock, mgsPaddedRowsFromFin, mgsPaddedFinInput,
          mgsPaddedRowsToFin, mgsPaddedInput]
    | inr i =>
        simp [mgsStackedBlocks, mgsPaddedBottomPerturbation,
          mgsPaddedBottomBlock, mgsPaddedRowsFromFin, mgsPaddedFinInput,
          mgsPaddedRowsToFin, mgsPaddedInput]
  unfold mgsStackedPerturbationColumnNorm
  rw [hblocks]
  exact mgsPaddedColumnNorm_rowsFromFin dA j

theorem mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_bound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dA : Fin (n + m) -> Fin n -> Real) {c : Real}
    (hbound : forall j : Fin n, columnFrob dA j <= c * columnFrob A j) :
    mgsStackedPerturbationColumnwiseBound A
      (mgsPaddedTopPerturbation
        (mgsPaddedRowsFromFin
          (fun r j => mgsPaddedFinInput A r j + dA r j)))
      (mgsPaddedBottomPerturbation A
        (mgsPaddedRowsFromFin
          (fun r j => mgsPaddedFinInput A r j + dA r j)))
      c := by
  intro j
  rw [mgsStackedPerturbationColumnNorm_rowsFromFin_add]
  exact hbound j

theorem mgsStackedPerturbationColumnwiseBound_of_rowsFromFin_add_padded_bound
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (dA : Fin (n + m) -> Fin n -> Real) {c : Real}
    (hbound : forall j : Fin n,
      columnFrob dA j <= c * columnFrob (mgsPaddedFinInput A) j) :
    mgsStackedPerturbationColumnwiseBound A
      (mgsPaddedTopPerturbation
        (mgsPaddedRowsFromFin
          (fun r j => mgsPaddedFinInput A r j + dA r j)))
      (mgsPaddedBottomPerturbation A
        (mgsPaddedRowsFromFin
          (fun r j => mgsPaddedFinInput A r j + dA r j)))
      c := by
  intro j
  rw [mgsStackedPerturbationColumnNorm_rowsFromFin_add]
  simpa [columnFrob_paddedFinInput A j] using hbound j

theorem mgsPaddedPerturbedInput_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedPerturbedInput A
        (fun _ _ => 0 : Fin n -> Fin n -> Real)
        (fun _ _ => 0 : Fin m -> Fin n -> Real) =
      mgsPaddedInput A := by
  ext a j
  cases a with
  | inl i =>
      rfl
  | inr i =>
      simp [mgsPaddedPerturbedInput, mgsStackedBlocks, mgsPaddedInput]

theorem mgsStackedPerturbationColumnNorm_zero {m n : Nat}
    (j : Fin n) :
    mgsStackedPerturbationColumnNorm
        (fun _ _ => 0 : Fin n -> Fin n -> Real)
        (fun _ _ => 0 : Fin m -> Fin n -> Real) j = 0 := by
  unfold mgsStackedPerturbationColumnNorm mgsPaddedColumnNorm
    mgsStackedBlocks
  rw [finiteVecNorm2_eq_zero_iff]
  intro a
  cases a with
  | inl i =>
      rfl
  | inr i =>
      rfl

theorem mgsStackedPerturbationColumnwiseBound_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) {c : Real} (hc : 0 <= c) :
    mgsStackedPerturbationColumnwiseBound A
      (fun _ _ => 0 : Fin n -> Fin n -> Real)
      (fun _ _ => 0 : Fin m -> Fin n -> Real)
      c := by
  intro j
  rw [mgsStackedPerturbationColumnNorm_zero]
  exact mul_nonneg hc (columnFrob_nonneg A j)

theorem mgsPaddedStage_top_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} {i : Fin n}
    (hit : i.val < t) (j : Fin n) :
    mgsPaddedStage A t (Sum.inl i) j = modifiedGramSchmidtR A i j := by
  simp [mgsPaddedStage, hit]

theorem mgsPaddedStage_top_of_not_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} {i : Fin n}
    (hit : Not (i.val < t)) (j : Fin n) :
    mgsPaddedStage A t (Sum.inl i) j = 0 := by
  simp [mgsPaddedStage, hit]

theorem mgsPaddedStage_bottom_of_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (i : Fin m)
    {j : Fin n} (hjt : j.val < t) :
    mgsPaddedStage A t (Sum.inr i) j = 0 := by
  simp [mgsPaddedStage, hjt]

theorem mgsPaddedStage_bottom_of_not_lt {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (i : Fin m)
    {j : Fin n} (hjt : Not (j.val < t)) :
    mgsPaddedStage A t (Sum.inr i) j =
      modifiedGramSchmidtVectors A t j i := by
  simp [mgsPaddedStage, hjt]

/-- The zeroth padded stage is the source matrix `[0; A]`. -/
theorem mgsPaddedStage_zero {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedStage A 0 = mgsPaddedInput A := by
  ext a j
  cases a with
  | inl i =>
      simp [mgsPaddedStage, mgsPaddedInput]
  | inr i =>
      simp [mgsPaddedStage, mgsPaddedInput, modifiedGramSchmidtVectors,
        gsColumn]

/-- The final padded stage is the exact block `[R; 0]`. -/
theorem mgsPaddedStage_final {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    mgsPaddedStage A n = mgsPaddedRBlock A := by
  ext a j
  cases a with
  | inl i =>
      simp [mgsPaddedStage, mgsPaddedRBlock, i.isLt]
  | inr i =>
      simp [mgsPaddedStage, mgsPaddedRBlock, j.isLt]

@[simp] theorem mgsHouseholderVector_top {m n : Nat}
    (q : Fin m -> Real) (k i : Fin n) :
    mgsHouseholderVector q k (Sum.inl i) = mgsHouseholderTop k i := rfl

@[simp] theorem mgsHouseholderVector_bottom {m n : Nat}
    (q : Fin m -> Real) (k : Fin n) (i : Fin m) :
    mgsHouseholderVector q k (Sum.inr i) = q i := rfl

@[simp] theorem mgsHouseholderTop_self {n : Nat} (k : Fin n) :
    mgsHouseholderTop k k = -1 := by
  simp [mgsHouseholderTop]

theorem mgsHouseholderTop_norm_sq {n : Nat} (k : Fin n) :
    finiteVecNorm2Sq (mgsHouseholderTop k) = 1 := by
  unfold finiteVecNorm2Sq mgsHouseholderTop
  simp [Finset.mem_univ]

/-- Squared norm of the source vector `[-e_k; q_k]`. -/
theorem mgsHouseholderVector_norm_sq {m n : Nat}
    (q : Fin m -> Real) (k : Fin n) :
    finiteVecNorm2Sq (mgsHouseholderVector q k) =
      1 + finiteVecNorm2Sq q := by
  calc
    finiteVecNorm2Sq (mgsHouseholderVector q k)
        = finiteVecNorm2Sq (mgsHouseholderTop k) +
            finiteVecNorm2Sq q := by
          simpa [mgsHouseholderVector] using
            (finiteVecNorm2Sq_sumBothVec (mgsHouseholderTop k) q)
    _ = 1 + finiteVecNorm2Sq q := by rw [mgsHouseholderTop_norm_sq]

/-- Equation `(19.28)` normalization channel: if the MGS column is unit
length, then the Householder-MGS vector satisfies `v_k^T v_k = 2`. -/
theorem mgsHouseholderVector_self_dot {m n : Nat}
    {q : Fin m -> Real} {k : Fin n}
    (hq : finiteVecNorm2Sq q = 1) :
    (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      mgsHouseholderVector q k a * mgsHouseholderVector q k a) = 2 := by
  have hsq : finiteVecNorm2Sq (mgsHouseholderVector q k) = 2 := by
    rw [mgsHouseholderVector_norm_sq, hq]
    norm_num
  simpa [finiteVecNorm2Sq, pow_two] using hsq

/-- The source vector built from the exact MGS column satisfies
`v_k^T v_k = 2` when the MGS stage normalizer is nonzero. -/
theorem mgsHouseholderVector_self_dot_computedQ {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      mgsHouseholderVector (gsColumn (modifiedGramSchmidtQ A) k) k a *
        mgsHouseholderVector (gsColumn (modifiedGramSchmidtQ A) k) k a) =
      2 := by
  exact mgsHouseholderVector_self_dot
    (modifiedGramSchmidtQ_column_norm_sq A k hdiag)

/-- The source reflector `I - v_k v_k^T` is symmetric. -/
theorem mgsHouseholderReflector_symmetric {m n : Nat}
    (q : Fin m -> Real) (k : Fin n) :
    IsSymmetricFiniteMatrix (mgsHouseholderReflector q k) := by
  intro a b
  unfold mgsHouseholderReflector finiteIdMatrix
  by_cases hab : a = b
  case pos =>
    subst b
    ring
  case neg =>
    have hba : Not (b = a) := by
      intro hba
      exact hab hba.symm
    simp [hab, hba, mul_comm]

/-- If `v_k^T v_k = 2`, the source reflector squares to the identity. -/
theorem mgsHouseholderReflector_mul_self_of_self_dot {m n : Nat}
    {q : Fin m -> Real} {k : Fin n}
    (hv : (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      mgsHouseholderVector q k a * mgsHouseholderVector q k a) = 2) :
    finiteMatMul (mgsHouseholderReflector q k)
        (mgsHouseholderReflector q k) =
      (finiteIdMatrix :
        Sum (Fin n) (Fin m) -> Sum (Fin n) (Fin m) -> Real) := by
  classical
  ext a c
  let v : Sum (Fin n) (Fin m) -> Real := mgsHouseholderVector q k
  have hidid :
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        finiteIdMatrix a b * finiteIdMatrix b c) = finiteIdMatrix a c := by
    simp [finiteIdMatrix, Finset.mem_univ]
  have hidv :
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        finiteIdMatrix a b * (v b * v c)) = v a * v c := by
    simp [finiteIdMatrix, Finset.mem_univ]
  have hvid :
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        (v a * v b) * finiteIdMatrix b c) = v a * v c := by
    simp [finiteIdMatrix, Finset.mem_univ]
  have hvv :
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        (v a * v b) * (v b * v c)) =
        v a *
          (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
            v b * v b) * v c := by
    rw [Finset.mul_sum]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  unfold finiteMatMul mgsHouseholderReflector
  calc
    (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
      (finiteIdMatrix a b - v a * v b) *
        (finiteIdMatrix b c - v b * v c))
        =
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        finiteIdMatrix a b * finiteIdMatrix b c -
          finiteIdMatrix a b * (v b * v c) -
          (v a * v b) * finiteIdMatrix b c +
          (v a * v b) * (v b * v c)) := by
          apply Finset.sum_congr rfl
          intro b _hb
          ring
    _ =
      finiteIdMatrix a c - v a * v c - v a * v c +
        v a *
          (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
            v b * v b) * v c := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            Finset.sum_sub_distrib, hidid, hidv, hvid, hvv]
    _ = finiteIdMatrix a c := by
          have hv' :
              (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
                v b * v b) = 2 := by
            simpa [v] using hv
          rw [hv']
          ring

/-- Applying `P_k = I - v_k v_k^T` to one padded column is the identity
column minus `v_k` times the scalar `v_k^T b_j`. -/
theorem mgsHouseholderApply_eq {m n : Nat}
    (q : Fin m -> Real) (k : Fin n)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real)
    (a : Sum (Fin n) (Fin m)) (j : Fin n) :
    mgsHouseholderApply q k B a j =
      B a j -
        mgsHouseholderVector q k a *
          mgsHouseholderColumnInner q k B j := by
  classical
  unfold mgsHouseholderApply mgsHouseholderReflector
    mgsHouseholderColumnInner finiteMatVec
  rw [show
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        (finiteIdMatrix a b -
            mgsHouseholderVector q k a * mgsHouseholderVector q k b) *
          B b j) =
        Finset.univ.sum (fun b : Sum (Fin n) (Fin m) =>
          finiteIdMatrix a b * B b j -
            (mgsHouseholderVector q k a * mgsHouseholderVector q k b) *
              B b j) by
        apply Finset.sum_congr rfl
        intro b _hb
        ring]
  rw [Finset.sum_sub_distrib]
  have hid :
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        finiteIdMatrix a b * B b j) = B a j := by
    simpa [finiteMatVec] using
      congr_fun
        (finiteMatVec_finiteIdMatrix
          (fun b : Sum (Fin n) (Fin m) => B b j)) a
  have hrank :
      (Finset.univ.sum fun b : Sum (Fin n) (Fin m) =>
        (mgsHouseholderVector q k a * mgsHouseholderVector q k b) *
          B b j) =
        mgsHouseholderVector q k a *
          Finset.univ.sum (fun b : Sum (Fin n) (Fin m) =>
            mgsHouseholderVector q k b * B b j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  rw [hid, hrank]

/-- If the source vector satisfies `v_k^T v_k = 2`, applying its source
reflector twice is the identity on padded matrices. -/
theorem mgsHouseholderApply_apply_self_of_self_dot {m n : Nat}
    {q : Fin m -> Real} {k : Fin n}
    (hv : (Finset.univ.sum fun a : Sum (Fin n) (Fin m) =>
      mgsHouseholderVector q k a * mgsHouseholderVector q k a) = 2)
    (B : Sum (Fin n) (Fin m) -> Fin n -> Real) :
    mgsHouseholderApply q k (mgsHouseholderApply q k B) = B := by
  classical
  ext a j
  unfold mgsHouseholderApply
  rw [<- finiteMatVec_finiteMatMul]
  rw [mgsHouseholderReflector_mul_self_of_self_dot hv]
  exact congrFun (finiteMatVec_finiteIdMatrix
    (fun b : Sum (Fin n) (Fin m) => B b j)) a

/-- For the source padded matrix `[0; A]`, the scalar `v_k^T b_j` is the MGS
dot product `q^T a_j`. -/
theorem mgsHouseholderColumnInner_padded {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    (k j : Fin n) :
    mgsHouseholderColumnInner q k (mgsPaddedInput A) j =
      gsDot q (gsColumn A j) := by
  unfold mgsHouseholderColumnInner mgsHouseholderVector mgsHouseholderTop
    mgsPaddedInput gsDot gsColumn sumBothVec
  rw [Fintype.sum_sum_type]
  simp

/-- At padded stage `k`, the scalar `v_k^T b_j` is the exact MGS row entry
`R_kj`. -/
theorem mgsHouseholderColumnInner_paddedStage {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k j : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderColumnInner (gsColumn (modifiedGramSchmidtQ A) k) k
      (mgsPaddedStage A k.val) j =
      modifiedGramSchmidtR A k j := by
  classical
  unfold mgsHouseholderColumnInner mgsHouseholderVector mgsHouseholderTop
    sumBothVec
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mgsPaddedStage]
  have htop :
      (Finset.univ.sum fun i : Fin n =>
        (if i = k then -1 else 0) *
          (if i.val < k.val then modifiedGramSchmidtR A i j else 0)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _hi
    by_cases hik : i = k
    case pos =>
      subst i
      simp
    case neg =>
      simp [hik]
  rw [htop, zero_add]
  by_cases hjk : j.val < k.val
  case pos =>
    rw [modifiedGramSchmidtR_eq_zero_of_lt A hjk]
    simp [hjk]
  case neg =>
    by_cases hkj : k.val < j.val
    case pos =>
      rw [modifiedGramSchmidtR_strict_upper A hkj]
      have hnot_jk : Not (j < k) := by
        intro hjk_fin
        exact hjk hjk_fin
      simp [hnot_jk, gsDot, gsColumn]
    case neg =>
      have hle_kj : k.val <= j.val := Nat.le_of_not_gt hjk
      have hle_jk : j.val <= k.val := Nat.le_of_not_gt hkj
      have hval : k.val = j.val := Nat.le_antisymm hle_kj hle_jk
      have hkj_eq : k = j := Fin.ext hval
      subst j
      rw [modifiedGramSchmidtR_diag]
      simp only [Nat.lt_irrefl, if_false]
      change
        gsDot (gsColumn (modifiedGramSchmidtQ A) k)
            (modifiedGramSchmidtVectors A k.val k) =
          gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)
      simpa [modifiedGramSchmidtQ, gsColumn] using
        (gsDot_normalize_self (modifiedGramSchmidtVectors A k.val k) hdiag)

/-- Applying the source reflector at stage `k` advances the exact padded
Householder-MGS stage from `k` to `k+1`. -/
theorem mgsHouseholderApply_paddedStage_eq_succ {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApply (gsColumn (modifiedGramSchmidtQ A) k) k
      (mgsPaddedStage A k.val) =
      mgsPaddedStage A (k.val + 1) := by
  classical
  ext a j
  rw [mgsHouseholderApply_eq,
    mgsHouseholderColumnInner_paddedStage A k j hdiag]
  cases a with
  | inl i =>
      by_cases hik : i = k
      case pos =>
        subst i
        have hk_succ : k.val < k.val + 1 := Nat.lt_succ_self k.val
        simp [mgsPaddedStage, mgsHouseholderVector, mgsHouseholderTop,
          sumBothVec, hk_succ]
      case neg =>
        by_cases hiklt : i.val < k.val
        case pos =>
          have hi_succ : i.val < k.val + 1 :=
            Nat.lt_trans hiklt (Nat.lt_succ_self k.val)
          simp [mgsPaddedStage, mgsHouseholderVector, mgsHouseholderTop,
            sumBothVec, hiklt, hi_succ, hik]
        case neg =>
          have hnot_succ : Not (i.val < k.val + 1) := by
            intro hi_succ
            have hik_le : k.val <= i.val := Nat.le_of_not_gt hiklt
            have hi_le_k : i.val <= k.val := Nat.le_of_lt_succ hi_succ
            have hval : i.val = k.val := Nat.le_antisymm hi_le_k hik_le
            exact hik (Fin.ext hval)
          simp [mgsPaddedStage, mgsHouseholderVector, mgsHouseholderTop,
            sumBothVec, hiklt, hnot_succ, hik]
  | inr i =>
      by_cases hjk : j.val < k.val
      case pos =>
        have hj_succ : j.val < k.val + 1 :=
          Nat.lt_trans hjk (Nat.lt_succ_self k.val)
        rw [modifiedGramSchmidtR_eq_zero_of_lt A hjk]
        simp [mgsPaddedStage, mgsHouseholderVector, sumBothVec, hjk,
          hj_succ]
      case neg =>
        by_cases hkj : k.val < j.val
        case pos =>
          have hnot_j_succ : Not (j.val < k.val + 1) :=
            Nat.not_lt_of_ge (Nat.succ_le_of_lt hkj)
          have hnot_jk : Not (j < k) := by
            intro hjk_fin
            exact hjk hjk_fin
          rw [modifiedGramSchmidtR_strict_upper A hkj]
          simp [mgsPaddedStage, mgsHouseholderVector, sumBothVec, hnot_jk,
            hnot_j_succ]
          rw [modifiedGramSchmidtVectors_succ_later A hkj]
          simp [gsProjectAway, gsColumn, modifiedGramSchmidtQ, gsNormalize]
          have hqdot :
              gsDot (gsColumn (modifiedGramSchmidtQ A) k)
                  (modifiedGramSchmidtVectors A k.val j) =
                gsDot
                  (gsNormalize (modifiedGramSchmidtVectors A k.val k)
                    (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)))
                  (modifiedGramSchmidtVectors A k.val j) := by
            rfl
          rw [hqdot]
          ring_nf
        case neg =>
          have hle_kj : k.val <= j.val := Nat.le_of_not_gt hjk
          have hle_jk : j.val <= k.val := Nat.le_of_not_gt hkj
          have hval : k.val = j.val := Nat.le_antisymm hle_kj hle_jk
          have hkj_eq : k = j := Fin.ext hval
          subst j
          have hk_succ : k.val < k.val + 1 := Nat.lt_succ_self k.val
          rw [modifiedGramSchmidtR_diag]
          simp [mgsPaddedStage, mgsHouseholderVector, sumBothVec, hk_succ,
            gsColumn, modifiedGramSchmidtQ, gsNormalize]
          field_simp [hdiag]
          ring

/-- Reverse exact one-step transition: because the source reflector is its own
inverse, applying it to stage `k+1` returns padded stage `k`. -/
theorem mgsHouseholderApply_paddedStage_succ_eq_current {m n : Nat}
    (A : Fin m -> Fin n -> Real) (k : Fin n)
    (hdiag :
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApply (gsColumn (modifiedGramSchmidtQ A) k) k
      (mgsPaddedStage A (k.val + 1)) =
      mgsPaddedStage A k.val := by
  have hfwd :=
    mgsHouseholderApply_paddedStage_eq_succ A k hdiag
  have hself :=
    mgsHouseholderApply_apply_self_of_self_dot
      (mgsHouseholderVector_self_dot_computedQ A k hdiag)
      (mgsPaddedStage A k.val)
  rw [<- hfwd]
  exact hself

/-- Prefix application of the exact source reflectors used in the
Householder-MGS connection.  At depth `t`, this applies the source reflectors
for stages `0, ..., t-1` that exist. -/
def mgsHouseholderApplyPrefix {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    Nat -> (Sum (Fin n) (Fin m) -> Fin n -> Real) ->
      Sum (Fin n) (Fin m) -> Fin n -> Real
  | 0, B => B
  | t + 1, B =>
      if ht : t < n then
        mgsHouseholderApply
          (gsColumn (modifiedGramSchmidtQ A) (Fin.mk t ht))
          (Fin.mk t ht)
          (mgsHouseholderApplyPrefix A t B)
      else
        mgsHouseholderApplyPrefix A t B

/-- Iterating the exact source reflectors advances the padded MGS stage from
`[0; A]` to stage `t`. -/
theorem mgsHouseholderApplyPrefix_paddedInput {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (hdiag : forall k : Fin n, k.val < t ->
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApplyPrefix A t (mgsPaddedInput A) =
      mgsPaddedStage A t := by
  induction t with
  | zero =>
      simp [mgsHouseholderApplyPrefix, mgsPaddedStage_zero]
  | succ t ih =>
      have ht_lt : t < n := Nat.lt_of_succ_le ht
      have ht_le : t <= n := Nat.le_of_lt ht_lt
      have hdiag_t : forall k : Fin n, k.val < t ->
          Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0 := by
        intro k hk
        exact hdiag k (Nat.lt_trans hk (Nat.lt_succ_self t))
      have hdiag_cur :
          Ne
            (gsColumnNorm2
              (modifiedGramSchmidtVectors A (Fin.mk t ht_lt).val
                (Fin.mk t ht_lt))) 0 := by
        exact hdiag (Fin.mk t ht_lt) (Nat.lt_succ_self t)
      simp [mgsHouseholderApplyPrefix, ht_lt]
      rw [ih ht_le hdiag_t]
      simpa using
        (mgsHouseholderApply_paddedStage_eq_succ A (Fin.mk t ht_lt)
          hdiag_cur)

/-- Full exact endpoint for the forward Householder-MGS prefix product:
applying all source reflectors to `[0; A]` gives `[R; 0]`. -/
theorem mgsHouseholderApplyPrefix_paddedInput_final {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApplyPrefix A n (mgsPaddedInput A) =
      mgsPaddedRBlock A := by
  rw [mgsHouseholderApplyPrefix_paddedInput A (Nat.le_refl n)]
  exact mgsPaddedStage_final A
  intro k _hk
  exact hdiag k

/-- Reverse-prefix application of the exact source reflectors used in the
printed Householder-MGS orientation.  At depth `t`, this applies the stage
`t-1` reflector first, then works backward to stage `0`. -/
def mgsHouseholderApplyReversePrefix {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    Nat -> (Sum (Fin n) (Fin m) -> Fin n -> Real) ->
      Sum (Fin n) (Fin m) -> Fin n -> Real
  | 0, B => B
  | t + 1, B =>
      if ht : t < n then
        mgsHouseholderApplyReversePrefix A t
          (mgsHouseholderApply
            (gsColumn (modifiedGramSchmidtQ A) (Fin.mk t ht))
            (Fin.mk t ht) B)
      else
        mgsHouseholderApplyReversePrefix A t B

/-- Iterating the reverse source reflectors sends padded stage `t` back to
the initial padded matrix `[0; A]`. -/
theorem mgsHouseholderApplyReversePrefix_paddedStage {m n : Nat}
    (A : Fin m -> Fin n -> Real) {t : Nat} (ht : t <= n)
    (hdiag : forall k : Fin n, k.val < t ->
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApplyReversePrefix A t (mgsPaddedStage A t) =
      mgsPaddedInput A := by
  induction t with
  | zero =>
      simp [mgsHouseholderApplyReversePrefix, mgsPaddedStage_zero]
  | succ t ih =>
      have ht_lt : t < n := Nat.lt_of_succ_le ht
      have ht_le : t <= n := Nat.le_of_lt ht_lt
      have hdiag_t : forall k : Fin n, k.val < t ->
          Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0 := by
        intro k hk
        exact hdiag k (Nat.lt_trans hk (Nat.lt_succ_self t))
      have hdiag_cur :
          Ne
            (gsColumnNorm2
              (modifiedGramSchmidtVectors A (Fin.mk t ht_lt).val
                (Fin.mk t ht_lt))) 0 := by
        exact hdiag (Fin.mk t ht_lt) (Nat.lt_succ_self t)
      simp [mgsHouseholderApplyReversePrefix, ht_lt]
      rw [mgsHouseholderApply_paddedStage_succ_eq_current A
        (Fin.mk t ht_lt) hdiag_cur]
      exact ih ht_le hdiag_t

/-- Printed-orientation exact endpoint for the Householder-MGS connection:
applying the reverse source-reflector prefix to `[R; 0]` recovers `[0; A]`. -/
theorem mgsHouseholderApplyReversePrefix_paddedRBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApplyReversePrefix A n (mgsPaddedRBlock A) =
      mgsPaddedInput A := by
  rw [<- mgsPaddedStage_final A]
  apply mgsHouseholderApplyReversePrefix_paddedStage A (Nat.le_refl n)
  intro k _hk
  exact hdiag k

/-- Top block extracted from the printed-orientation endpoint of `(19.34)`.
In exact arithmetic this is the zero block. -/
theorem mgsHouseholderApplyReversePrefix_paddedRBlock_topBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsPaddedTopBlock
        (mgsHouseholderApplyReversePrefix A n (mgsPaddedRBlock A)) =
      (fun _ _ => 0 : Fin n -> Fin n -> Real) := by
  rw [mgsHouseholderApplyReversePrefix_paddedRBlock A hdiag]
  exact mgsPaddedTopBlock_paddedInput A

/-- Bottom block extracted from the printed-orientation endpoint of `(19.34)`.
In exact arithmetic this recovers the original input matrix. -/
theorem mgsHouseholderApplyReversePrefix_paddedRBlock_bottomBlock {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsPaddedBottomBlock
        (mgsHouseholderApplyReversePrefix A n (mgsPaddedRBlock A)) =
      A := by
  rw [mgsHouseholderApplyReversePrefix_paddedRBlock A hdiag]
  exact mgsPaddedBottomBlock_paddedInput A

/-- Block form of the exact printed-orientation Householder-MGS endpoint. -/
theorem mgsHouseholderApplyReversePrefix_paddedRBlock_blocks {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsPaddedTopBlock
        (mgsHouseholderApplyReversePrefix A n (mgsPaddedRBlock A)) =
        (fun _ _ => 0 : Fin n -> Fin n -> Real) /\
      mgsPaddedBottomBlock
        (mgsHouseholderApplyReversePrefix A n (mgsPaddedRBlock A)) =
        A := by
  constructor
  exact mgsHouseholderApplyReversePrefix_paddedRBlock_topBlock A hdiag
  exact mgsHouseholderApplyReversePrefix_paddedRBlock_bottomBlock A hdiag

/-- Exact `(19.34)` perturbed-input form with zero perturbation blocks. -/
theorem mgsHouseholderApplyReversePrefix_paddedRBlock_perturbedInput_zero
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (hdiag : forall k : Fin n,
      Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    mgsHouseholderApplyReversePrefix A n (mgsPaddedRBlock A) =
      mgsPaddedPerturbedInput A
        (fun _ _ => 0 : Fin n -> Fin n -> Real)
        (fun _ _ => 0 : Fin m -> Fin n -> Real) := by
  rw [mgsHouseholderApplyReversePrefix_paddedRBlock A hdiag,
    mgsPaddedPerturbedInput_zero A]

/-- Current top row after applying the source reflector to `[0; A]`. -/
theorem mgsHouseholderApply_padded_top_current {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    (k j : Fin n) :
    mgsHouseholderApply q k (mgsPaddedInput A) (Sum.inl k) j =
      gsDot q (gsColumn A j) := by
  rw [mgsHouseholderApply_eq,
    mgsHouseholderColumnInner_padded]
  have htop :
      mgsHouseholderVector q k (Sum.inl k) = -1 := by
    simp [mgsHouseholderVector, mgsHouseholderTop, sumBothVec]
  simp [mgsPaddedInput, htop]

/-- Inactive top rows remain zero after applying the source reflector to
`[0; A]`. -/
theorem mgsHouseholderApply_padded_top_ne {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    {k i : Fin n} (hki : Ne i k) (j : Fin n) :
    mgsHouseholderApply q k (mgsPaddedInput A) (Sum.inl i) j = 0 := by
  rw [mgsHouseholderApply_eq,
    mgsHouseholderColumnInner_padded]
  have htop :
      mgsHouseholderVector q k (Sum.inl i) = 0 := by
    simp [mgsHouseholderVector, mgsHouseholderTop, sumBothVec, hki]
  simp [mgsPaddedInput, htop]

/-- Bottom block after applying the source reflector to `[0; A]`: this is the
MGS projection update. -/
theorem mgsHouseholderApply_padded_bottom {m n : Nat}
    (A : Fin m -> Fin n -> Real) (q : Fin m -> Real)
    (k : Fin n) (i : Fin m) (j : Fin n) :
    mgsHouseholderApply q k (mgsPaddedInput A) (Sum.inr i) j =
      A i j - q i * gsDot q (gsColumn A j) := by
  rw [mgsHouseholderApply_eq,
    mgsHouseholderColumnInner_padded]
  have hbot :
      mgsHouseholderVector q k (Sum.inr i) = q i := by
    simp [mgsHouseholderVector, sumBothVec]
  simp [mgsPaddedInput, hbot]

/-- Rectangular Gram matrix `Q^T Q` for an `m x n` matrix with candidate
orthonormal columns. -/
def rectangularGram {m n : Nat} (Q : Fin m -> Fin n -> Real) :
    Fin n -> Fin n -> Real :=
  matMulRect n m n (finiteTranspose Q) Q

/-- A rectangular Gram entry is the Gram-Schmidt dot product of the
corresponding columns. -/
theorem rectangularGram_eq_gsDot {m n : Nat}
    (Q : Fin m -> Fin n -> Real) (i j : Fin n) :
    rectangularGram Q i j = gsDot (gsColumn Q i) (gsColumn Q j) := by
  rfl

/-- Expanding `||Q*x||_2^2` through the rectangular Gram matrix `Q^T Q`. -/
theorem rectangularGram_quadratic_eq_vecNorm2Sq {m n : Nat}
    (Q : Fin m -> Fin n -> Real) (x : Fin n -> Real) :
    vecNorm2Sq (rectMatMulVec Q x) =
      Finset.univ.sum fun j : Fin n =>
        Finset.univ.sum fun k : Fin n =>
          rectangularGram Q j k * (x j * x k) := by
  unfold vecNorm2Sq rectMatMulVec
  calc
    (Finset.univ.sum fun i : Fin m =>
        (Finset.univ.sum fun j : Fin n => Q i j * x j) ^ 2)
        =
        Finset.univ.sum fun i : Fin m =>
          (Finset.univ.sum fun j : Fin n => Q i j * x j) *
            (Finset.univ.sum fun k : Fin n => Q i k * x k) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ =
        Finset.univ.sum fun i : Fin m =>
          Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun k : Fin n =>
              (Q i j * Q i k) * (x j * x k) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ =
        Finset.univ.sum fun j : Fin n =>
          Finset.univ.sum fun k : Fin n =>
            (Finset.univ.sum fun i : Fin m => Q i j * Q i k) *
              (x j * x k) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_mul]
    _ =
        Finset.univ.sum fun j : Fin n =>
          Finset.univ.sum fun k : Fin n =>
            rectangularGram Q j k * (x j * x k) := by
          rfl

/-- The quadratic form of the identity matrix is `||x||_2^2`. -/
theorem idMatrix_quadratic_eq_vecNorm2Sq {n : Nat} (x : Fin n -> Real) :
    (Finset.univ.sum fun j : Fin n =>
      Finset.univ.sum fun k : Fin n => idMatrix n j k * (x j * x k)) =
      vecNorm2Sq x := by
  unfold vecNorm2Sq
  simp [idMatrix, pow_two]

/-- A rectangular Gram matrix `Q^T Q` is symmetric. -/
theorem rectangularGram_symmetric {m n : Nat}
    (Q : Fin m -> Fin n -> Real) :
    forall i j : Fin n, rectangularGram Q i j = rectangularGram Q j i := by
  intro i j
  unfold rectangularGram matMulRect finiteTranspose
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A rectangular Gram matrix vanishes exactly when the rectangular matrix
itself vanishes. -/
theorem rectangularGram_eq_zero_iff {m n : Nat}
    (Q : Fin m -> Fin n -> Real) :
    rectangularGram Q = (fun _ _ => 0) <-> Q = fun _ _ => 0 := by
  constructor
  case mp =>
    intro hgram
    ext i j
    have hdiag : rectangularGram Q j j = 0 := by
      simpa using congrFun (congrFun hgram j) j
    have hsum :
        (Finset.univ.sum fun r : Fin m => Q r j ^ 2) = 0 := by
      simpa [rectangularGram, finiteTranspose, matMulRect, pow_two] using
        hdiag
    have hterms :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun r : Fin m => Q r j ^ 2)
        (by intro r _; exact sq_nonneg (Q r j))).mp hsum
    exact sq_eq_zero_iff.mp (hterms i (Finset.mem_univ i))
  case mpr =>
    intro hQ
    ext i j
    simp [rectangularGram, finiteTranspose, matMulRect, hQ]

/-- If two block-column Gram matrices add to the identity, the left block is a
unit rectangular contraction. -/
theorem rectOpNorm2Le_one_left_of_rectangularGram_add_eq_id
    {r m n : Nat} {A : Fin r -> Fin n -> Real} {B : Fin m -> Fin n -> Real}
    (hgram :
      (fun i j => rectangularGram A i j + rectangularGram B i j) =
        idMatrix n) :
    rectOpNorm2Le A 1 := by
  intro x
  have hAGram :
      forall j k : Fin n,
        rectangularGram A j k = idMatrix n j k - rectangularGram B j k := by
    intro j k
    have hsum := congrFun (congrFun hgram j) k
    linarith
  have hsqle : vecNorm2Sq (rectMatMulVec A x) <= vecNorm2Sq x := by
    calc
      vecNorm2Sq (rectMatMulVec A x)
          = Finset.univ.sum fun j : Fin n =>
              Finset.univ.sum fun k : Fin n =>
                rectangularGram A j k * (x j * x k) :=
            rectangularGram_quadratic_eq_vecNorm2Sq A x
      _ = Finset.univ.sum fun j : Fin n =>
              Finset.univ.sum fun k : Fin n =>
                (idMatrix n j k - rectangularGram B j k) * (x j * x k) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [hAGram j k]
      _ = (Finset.univ.sum fun j : Fin n =>
              Finset.univ.sum fun k : Fin n =>
                idMatrix n j k * (x j * x k)) -
            (Finset.univ.sum fun j : Fin n =>
              Finset.univ.sum fun k : Fin n =>
                rectangularGram B j k * (x j * x k)) := by
            simp_rw [sub_mul]
            rw [<- Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro j _
            rw [<- Finset.sum_sub_distrib]
      _ = vecNorm2Sq x - vecNorm2Sq (rectMatMulVec B x) := by
            rw [idMatrix_quadratic_eq_vecNorm2Sq]
            rw [rectangularGram_quadratic_eq_vecNorm2Sq B x]
      _ <= vecNorm2Sq x := by
            exact sub_le_self _ (vecNorm2Sq_nonneg _)
  unfold vecNorm2
  have hsqrt := Real.sqrt_le_sqrt hsqle
  simpa using hsqrt

/-- If two block-column Gram matrices add to the identity, the right block is a
unit rectangular contraction. -/
theorem rectOpNorm2Le_one_right_of_rectangularGram_add_eq_id
    {r m n : Nat} {A : Fin r -> Fin n -> Real} {B : Fin m -> Fin n -> Real}
    (hgram :
      (fun i j => rectangularGram A i j + rectangularGram B i j) =
        idMatrix n) :
    rectOpNorm2Le B 1 := by
  have hswap :
      (fun i j => rectangularGram B i j + rectangularGram A i j) =
        idMatrix n := by
    ext i j
    have hsum := congrFun (congrFun hgram i) j
    linarith
  exact rectOpNorm2Le_one_left_of_rectangularGram_add_eq_id hswap

/-- A rectangular operator-2 bound for `Q` gives an operator-2 bound for the
Gram matrix `Q^T Q`. -/
theorem rectangularGram_opNorm2Le_of_rectOpNorm2Le {m n : Nat}
    {Q : Fin m -> Fin n -> Real} {eta : Real}
    (heta : 0 <= eta) (hQ : rectOpNorm2Le Q eta) :
    opNorm2Le (rectangularGram Q) (eta ^ 2) := by
  have hQT : rectOpNorm2Le (finiteTranspose Q) eta :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q heta hQ
  have hprod :
      rectOpNorm2Le (rectMatMul (finiteTranspose Q) Q) (eta * eta) :=
    rectOpNorm2Le_rectMatMul (finiteTranspose Q) Q heta hQT hQ
  have hgram :
      rectOpNorm2Le (rectangularGram Q) (eta * eta) := by
    simpa [rectangularGram, matMulRect_eq_rectMatMul] using hprod
  have hgram' :
      rectOpNorm2Le (rectangularGram Q) (eta ^ 2) := by
    convert hgram using 1
    ring
  exact opNorm2Le_of_rectOpNorm2Le_square _ hgram'

/-- If two block-column Gram matrices add to the identity, the two Gram
matrices commute.  This is the algebraic simultaneous-diagonalization
precondition used by the CS/polar route. -/
theorem rectangularGram_commute_of_add_eq_id
    {r m n : Nat} {A : Fin r -> Fin n -> Real} {B : Fin m -> Fin n -> Real}
    (hgram :
      (fun i j => rectangularGram A i j + rectangularGram B i j) =
        idMatrix n) :
    matMul n (rectangularGram A) (rectangularGram B) =
      matMul n (rectangularGram B) (rectangularGram A) := by
  have hB :
      forall i j : Fin n,
        rectangularGram B i j = idMatrix n i j - rectangularGram A i j := by
    intro i j
    have hsum := congrFun (congrFun hgram i) j
    linarith
  ext i j
  have hleft :
      matMul n (rectangularGram A) (rectangularGram B) i j =
        rectangularGram A i j -
          matMul n (rectangularGram A) (rectangularGram A) i j := by
    calc
      matMul n (rectangularGram A) (rectangularGram B) i j
          =
          Finset.univ.sum fun k : Fin n =>
            rectangularGram A i k *
              (idMatrix n k j - rectangularGram A k j) := by
            unfold matMul
            apply Finset.sum_congr rfl
            intro k _
            rw [hB]
      _ =
          (Finset.univ.sum fun k : Fin n =>
            rectangularGram A i k * idMatrix n k j) -
            (Finset.univ.sum fun k : Fin n =>
              rectangularGram A i k * rectangularGram A k j) := by
            simp_rw [mul_sub]
            rw [Finset.sum_sub_distrib]
      _ =
          rectangularGram A i j -
            matMul n (rectangularGram A) (rectangularGram A) i j := by
            have hid :
                (Finset.univ.sum fun k : Fin n =>
                  rectangularGram A i k * idMatrix n k j) =
                  rectangularGram A i j := by
              simpa [matMul] using
                congrFun
                  (congrFun
                    (matMul_id_right n (rectangularGram A)) i) j
            rw [hid]
            rfl
  have hright :
      matMul n (rectangularGram B) (rectangularGram A) i j =
        rectangularGram A i j -
          matMul n (rectangularGram A) (rectangularGram A) i j := by
    calc
      matMul n (rectangularGram B) (rectangularGram A) i j
          =
          Finset.univ.sum fun k : Fin n =>
            (idMatrix n i k - rectangularGram A i k) *
              rectangularGram A k j := by
            unfold matMul
            apply Finset.sum_congr rfl
            intro k _
            rw [hB]
      _ =
          (Finset.univ.sum fun k : Fin n =>
            idMatrix n i k * rectangularGram A k j) -
            (Finset.univ.sum fun k : Fin n =>
              rectangularGram A i k * rectangularGram A k j) := by
            simp_rw [sub_mul]
            rw [Finset.sum_sub_distrib]
      _ =
          rectangularGram A i j -
            matMul n (rectangularGram A) (rectangularGram A) i j := by
            have hid :
                (Finset.univ.sum fun k : Fin n =>
                  idMatrix n i k * rectangularGram A k j) =
                  rectangularGram A i j := by
              simpa [matMul] using
                congrFun
                  (congrFun
                    (matMul_id_left n (rectangularGram A)) i) j
            rw [hid]
            rfl
  rw [hleft, hright]

/-- Block-column orthogonality for the padded Householder-MGS split.  If the
full padded matrix is orthogonal, then the top-left block `P11` and bottom-left
block `Q21` satisfy `P11^T P11 + Q21^T Q21 = I`.  This is the exact algebraic
input used before the CS/polar repair step in Higham's proof of Theorem 19.13. -/
theorem mgsPaddedEconomy_blocks_gram_sum_eq_id {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hP : IsOrthogonal (n + m) P) :
    (fun i j =>
        rectangularGram (mgsPaddedEconomyP11 P) i j +
          rectangularGram (mgsPaddedEconomyQ P) i j) =
      idMatrix n := by
  ext i j
  have hcol :=
    IsOrthogonal.col_orthonormal hP (Fin.castAdd m i) (Fin.castAdd m j)
  rw [Fin.sum_univ_add] at hcol
  have hidx :
      (if Fin.castAdd m i = Fin.castAdd m j then (1 : Real) else 0) =
        idMatrix n i j := by
    by_cases hij : i = j
    case pos =>
      subst j
      simp [idMatrix]
    case neg =>
      have hne : Not (Fin.castAdd m i = Fin.castAdd m j) := by
        intro hcast
        apply hij
        apply Fin.ext
        simpa using congrArg Fin.val hcast
      simp [idMatrix, hij, hne]
  simpa [rectangularGram, finiteTranspose, matMulRect,
    mgsPaddedEconomyP11, mgsPaddedEconomyQ, mgsPaddedRowToFin, hidx] using hcol

/-- Equivalent form of `mgsPaddedEconomy_blocks_gram_sum_eq_id`: the bottom-left
economy block has Gram matrix `I - P11^T P11`. -/
theorem mgsPaddedEconomyQ_gram_eq_id_sub_P11_gram {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hP : IsOrthogonal (n + m) P) :
    rectangularGram (mgsPaddedEconomyQ P) =
      fun i j => idMatrix n i j -
        rectangularGram (mgsPaddedEconomyP11 P) i j := by
  ext i j
  have hsum :=
    congrFun (congrFun (mgsPaddedEconomy_blocks_gram_sum_eq_id hP) i) j
  linarith

/-- Candidate `Q` has orthonormal columns, using the Gram-Schmidt QR naming
surface to avoid collisions with the RandNLA basis predicate. -/
def GramSchmidtOrthonormalColumns {m n : Nat}
    (Q : Fin m -> Fin n -> Real) : Prop :=
  forall i j : Fin n, rectangularGram Q i j = idMatrix n i j

/-- Exact MGS has orthonormal columns whenever all stage normalizers are
nonzero. -/
theorem modifiedGramSchmidtQ_orthonormal_columns {m n : Nat}
    (A : Fin m -> Fin n -> Real)
    (hdiag :
      forall k : Fin n,
        Ne (gsColumnNorm2 (modifiedGramSchmidtVectors A k.val k)) 0) :
    GramSchmidtOrthonormalColumns (modifiedGramSchmidtQ A) := by
  intro i j
  rw [rectangularGram_eq_gsDot]
  by_cases hij : i = j
  · subst j
    have hnorm := modifiedGramSchmidtQ_column_norm_sq A i (hdiag i)
    calc
      gsDot (gsColumn (modifiedGramSchmidtQ A) i)
          (gsColumn (modifiedGramSchmidtQ A) i)
          = finiteVecNorm2Sq (gsColumn (modifiedGramSchmidtQ A) i) :=
            gsDot_self_eq_finiteVecNorm2Sq _
      _ = 1 := hnorm
      _ = idMatrix n i i := by simp [idMatrix]
  · by_cases hlt : i.val < j.val
    · have hijFin : i < j := by
        simpa using hlt
      have hzero :=
        modifiedGramSchmidtQ_dot_eq_zero_of_lt A hdiag hijFin
      calc
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
            (gsColumn (modifiedGramSchmidtQ A) j)
            = 0 := hzero
        _ = idMatrix n i j := by simp [idMatrix, hij]
    · have hle : j.val <= i.val := Nat.le_of_not_gt hlt
      have hne_val : j.val ≠ i.val := by
        intro hval
        exact hij (Fin.ext hval.symm)
      have hjlt : j.val < i.val := lt_of_le_of_ne hle hne_val
      have hjiFin : j < i := by
        simpa using hjlt
      have hzero :=
        modifiedGramSchmidtQ_dot_eq_zero_of_lt A hdiag hjiFin
      calc
        gsDot (gsColumn (modifiedGramSchmidtQ A) i)
            (gsColumn (modifiedGramSchmidtQ A) j)
            = gsDot (gsColumn (modifiedGramSchmidtQ A) j)
                (gsColumn (modifiedGramSchmidtQ A) i) :=
              gsDot_comm _ _
        _ = 0 := hzero
        _ = idMatrix n i j := by simp [idMatrix, hij]

/-- Orthonormal columns give a unit rectangular operator-2 certificate. -/
theorem GramSchmidtOrthonormalColumns.rectOpNorm2Le_one {m n : Nat}
    {Q : Fin m -> Fin n -> Real}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2Le Q 1 := by
  intro x
  have hsq :
      vecNorm2Sq (rectMatMulVec Q x) = vecNorm2Sq x := by
    unfold vecNorm2Sq rectMatMulVec
    calc
      (Finset.univ.sum fun i : Fin m =>
          (Finset.univ.sum fun j : Fin n => Q i j * x j) ^ 2)
          =
          Finset.univ.sum fun i : Fin m =>
            (Finset.univ.sum fun j : Fin n => Q i j * x j) *
              (Finset.univ.sum fun k : Fin n => Q i k * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ =
          Finset.univ.sum fun i : Fin m =>
            Finset.univ.sum fun j : Fin n =>
              Finset.univ.sum fun k : Fin n =>
                (Q i j * Q i k) * (x j * x k) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
      _ =
          Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun k : Fin n =>
              (Finset.univ.sum fun i : Fin m => Q i j * Q i k) *
                (x j * x k) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
      _ =
          Finset.univ.sum fun j : Fin n =>
            Finset.univ.sum fun k : Fin n =>
              idMatrix n j k * (x j * x k) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro k _
            rw [show (Finset.univ.sum fun i : Fin m => Q i j * Q i k) =
                rectangularGram Q j k from by
              rfl]
            rw [hQ j k]
      _ =
          Finset.univ.sum fun j : Fin n => x j * x j := by
            simp [idMatrix]
      _ = Finset.univ.sum fun j : Fin n => x j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j _
            ring
  unfold vecNorm2
  rw [hsq]
  simp

/-- Square operator-2 certificates can be read as rectangular certificates in
the square case. -/
theorem rectOpNorm2Le_of_opNorm2Le_square {n : Nat}
    (M : Fin n -> Fin n -> Real) {c : Real}
    (hM : opNorm2Le M c) :
    rectOpNorm2Le M c := by
  intro x
  simpa [opNorm2Le, rectOpNorm2Le, matMulVec, rectMatMulVec] using hM x

/-- Square matrix products preserve operator-2 certificates, returned in the
rectangular predicate used by the QR files. -/
theorem rectOpNorm2Le_matMul_square {n : Nat}
    (A B : Fin n -> Fin n -> Real) {cA cB : Real}
    (hcA : 0 <= cA) (hA : opNorm2Le A cA) (hB : opNorm2Le B cB) :
    rectOpNorm2Le (matMul n A B) (cA * cB) := by
  have hprod :
      rectOpNorm2Le (rectMatMul A B) (cA * cB) :=
    rectOpNorm2Le_rectMatMul A B hcA
      (rectOpNorm2Le_of_opNorm2Le_square A hA)
      (rectOpNorm2Le_of_opNorm2Le_square B hB)
  simpa [rectMatMul, matMul] using hprod

/-- Orthonormal columns remain orthonormal after right multiplication by the
transpose of a square orthogonal matrix. -/
theorem GramSchmidtOrthonormalColumns.matMulRect_finiteTranspose_of_orthogonal
    {m n : Nat} {V : Fin m -> Fin n -> Real}
    {W : Fin n -> Fin n -> Real}
    (hV : GramSchmidtOrthonormalColumns V) (hW : IsOrthogonal n W) :
    GramSchmidtOrthonormalColumns
      (matMulRect m n n V (finiteTranspose W)) := by
  intro a b
  unfold rectangularGram matMulRect finiteTranspose
  calc
    (Finset.univ.sum fun i : Fin m =>
        (Finset.univ.sum fun k : Fin n => V i k * W a k) *
          (Finset.univ.sum fun l : Fin n => V i l * W b l))
        =
      Finset.univ.sum fun i : Fin m =>
        Finset.univ.sum fun k : Fin n =>
          Finset.univ.sum fun l : Fin n =>
            (V i k * V i l) * (W a k * W b l) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ =
      Finset.univ.sum fun k : Fin n =>
        Finset.univ.sum fun l : Fin n =>
          Finset.univ.sum fun i : Fin m =>
            (V i k * V i l) * (W a k * W b l) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ =
      Finset.univ.sum fun k : Fin n =>
        Finset.univ.sum fun l : Fin n =>
          (Finset.univ.sum fun i : Fin m => V i k * V i l) *
            (W a k * W b l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_mul]
    _ =
      Finset.univ.sum fun k : Fin n =>
        Finset.univ.sum fun l : Fin n =>
          idMatrix n k l * (W a k * W b l) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [show (Finset.univ.sum fun i : Fin m => V i k * V i l) =
              rectangularGram V k l from by rfl]
          rw [hV k l]
    _ = Finset.univ.sum fun k : Fin n => W a k * W b k := by
          simp [idMatrix, Finset.mem_univ]
    _ = idMatrix n a b := by
          have hrow := hW.row_orthonormal a b
          simpa [idMatrix] using hrow

/-- Multiplying an orthonormal rectangular factor on the right by a square
factor preserves the square factor's operator-2 bound. -/
theorem GramSchmidtOrthonormalColumns.rectOpNorm2Le_matMulRect_square_right
    {m n : Nat} {V : Fin m -> Fin n -> Real}
    {G : Fin n -> Fin n -> Real} {c : Real}
    (hV : GramSchmidtOrthonormalColumns V) (hG : opNorm2Le G c) :
    rectOpNorm2Le (matMulRect m n n V G) c := by
  have hprod :
      rectOpNorm2Le (rectMatMul V G) (1 * c) :=
    rectOpNorm2Le_rectMatMul V G (by norm_num)
      hV.rectOpNorm2Le_one
      (rectOpNorm2Le_of_opNorm2Le_square G hG)
  simpa [matMulRect_eq_rectMatMul] using hprod

/-- Finite transpose reverses square matrix multiplication. -/
theorem finiteTranspose_matMul {n : Nat}
    (A B : Fin n -> Fin n -> Real) :
    finiteTranspose (matMul n A B) =
      matMul n (finiteTranspose B) (finiteTranspose A) := by
  simpa [finiteTranspose, matTranspose] using matTranspose_matMul A B

/-- A finite diagonal matrix is symmetric. -/
theorem finiteTranspose_finiteDiagonal {n : Nat} (d : Fin n -> Real) :
    finiteTranspose (finiteDiagonal d) = finiteDiagonal d := by
  ext i j
  by_cases hij : i = j
  case pos =>
    subst j
    simp [finiteTranspose, finiteDiagonal]
  case neg =>
    have hji : Ne j i := by
      intro h
      exact hij h.symm
    simp [finiteTranspose, finiteDiagonal, hij, hji]

/-- If `V` has orthonormal columns, left multiplication by `V` preserves the
Gram matrix of a square right factor. -/
theorem rectangularGram_matMulRect_of_orthonormal_left {m n : Nat}
    {V : Fin m -> Fin n -> Real} (hV : GramSchmidtOrthonormalColumns V)
    (G : Fin n -> Fin n -> Real) :
    rectangularGram (matMulRect m n n V G) = matMul n (finiteTranspose G) G := by
  ext a b
  unfold rectangularGram matMulRect finiteTranspose matMul
  calc
    (Finset.univ.sum fun i : Fin m =>
        (Finset.univ.sum fun k : Fin n => V i k * G k a) *
          (Finset.univ.sum fun l : Fin n => V i l * G l b))
        =
      Finset.univ.sum fun i : Fin m =>
        Finset.univ.sum fun k : Fin n =>
          Finset.univ.sum fun l : Fin n =>
            (V i k * V i l) * (G k a * G l b) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          ring
    _ =
      Finset.univ.sum fun k : Fin n =>
        Finset.univ.sum fun l : Fin n =>
          Finset.univ.sum fun i : Fin m =>
            (V i k * V i l) * (G k a * G l b) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.sum_comm]
    _ =
      Finset.univ.sum fun k : Fin n =>
        Finset.univ.sum fun l : Fin n =>
          (Finset.univ.sum fun i : Fin m => V i k * V i l) *
            (G k a * G l b) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_mul]
    _ =
      Finset.univ.sum fun k : Fin n =>
        Finset.univ.sum fun l : Fin n =>
          idMatrix n k l * (G k a * G l b) := by
          apply Finset.sum_congr rfl
          intro k _
          apply Finset.sum_congr rfl
          intro l _
          rw [show (Finset.univ.sum fun i : Fin m => V i k * V i l) =
              rectangularGram V k l from by rfl]
          rw [hV k l]
    _ = Finset.univ.sum fun k : Fin n => G k a * G k b := by
          simp [idMatrix, Finset.mem_univ]

/-- The square version of
`rectangularGram_matMulRect_of_orthonormal_left` for an orthogonal left factor. -/
theorem rectangularGram_matMul_left_orthogonal {n : Nat}
    {U : Fin n -> Fin n -> Real} (hU : IsOrthogonal n U)
    (G : Fin n -> Fin n -> Real) :
    rectangularGram (matMul n U G) = matMul n (finiteTranspose G) G := by
  have hUcols : GramSchmidtOrthonormalColumns U := by
    intro i j
    have hcol := hU.col_orthonormal i j
    simpa [GramSchmidtOrthonormalColumns, rectangularGram, matMulRect,
      finiteTranspose, idMatrix] using hcol
  simpa [matMulRect, matMul] using
    rectangularGram_matMulRect_of_orthonormal_left hUcols G

/-- A finite diagonal matrix acts componentwise. -/
theorem matMulVec_finiteDiagonal {n : Nat} (d x : Fin n -> Real)
    (i : Fin n) :
    matMulVec n (finiteDiagonal d) x i = d i * x i := by
  unfold matMulVec finiteDiagonal
  simp

/-- A finite diagonal matrix whose entries have absolute value at most one is
an operator-2-norm contraction. -/
theorem opNorm2Le_finiteDiagonal_of_abs_le_one {n : Nat}
    (d : Fin n -> Real) (hd : forall i, |d i| <= 1) :
    opNorm2Le (finiteDiagonal d) 1 := by
  intro x
  have hpoint :
      forall i,
        |matMulVec n (finiteDiagonal d) x i| <=
          (fun k : Fin n => |x k|) i := by
    intro i
    calc
      |matMulVec n (finiteDiagonal d) x i|
          = |d i * x i| := by
              rw [matMulVec_finiteDiagonal]
      _ = |d i| * |x i| := by
              rw [abs_mul]
      _ <= 1 * |x i| := by
              exact mul_le_mul_of_nonneg_right (hd i) (abs_nonneg (x i))
      _ = |x i| := by ring
  calc
    vecNorm2 (matMulVec n (finiteDiagonal d) x)
        <= vecNorm2 (fun k : Fin n => |x k|) :=
          vecNorm2_le_of_abs_le _ _ hpoint
    _ = 1 * vecNorm2 x := by
          rw [vecNorm2_abs]
          ring

/-- Scalar CS estimate for the sine diagonal: if `c^2 + s^2 = 1`, then
`|s| <= 1`. -/
theorem csSine_abs_le_one {c s : Real}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    |s| <= 1 := by
  have hs_sq : s ^ 2 <= 1 := by
    nlinarith [sq_nonneg c]
  exact (sq_le_one_iff_abs_le_one s).mp hs_sq

/-- Scalar CS estimate for the cosine diagonal: if `c^2 + s^2 = 1`, then
`|c| <= 1`. -/
theorem csCosine_abs_le_one {c s : Real}
    (hcs : c ^ 2 + s ^ 2 = 1) :
    |c| <= 1 := by
  have hc_sq : c ^ 2 <= 1 := by
    nlinarith [sq_nonneg s]
  exact (sq_le_one_iff_abs_le_one c).mp hc_sq

/-- The diagonal CS sine factor is an operator-2-norm contraction. -/
theorem opNorm2Le_finiteDiagonal_csSine {n : Nat}
    (c s : Fin n -> Real)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le (finiteDiagonal s) 1 := by
  exact
    opNorm2Le_finiteDiagonal_of_abs_le_one s
      (fun i => csSine_abs_le_one (hcs i))

/-- The diagonal CS cosine factor is an operator-2-norm contraction. -/
theorem opNorm2Le_finiteDiagonal_csCosine {n : Nat}
    (c s : Fin n -> Real)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le (finiteDiagonal c) 1 := by
  exact
    opNorm2Le_finiteDiagonal_of_abs_le_one c
      (fun i => csCosine_abs_le_one (hcs i))

/-- Squaring a finite diagonal matrix squares its diagonal entries. -/
theorem matMul_finiteDiagonal_self {n : Nat} (d : Fin n -> Real) :
    matMul n (finiteDiagonal d) (finiteDiagonal d) =
      finiteDiagonal (fun i => d i ^ 2) := by
  ext i j
  by_cases hij : i = j
  case pos =>
    subst j
    simp [matMul, finiteDiagonal, pow_two]
  case neg =>
    simp [matMul, finiteDiagonal, hij]

/-- Diagonal CS square identity: `diag(c)^2 + diag(s)^2 = I` when
`c_i^2 + s_i^2 = 1`. -/
theorem matMul_finiteDiagonal_csSquareSum {n : Nat}
    (c s : Fin n -> Real)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    (fun i j =>
        matMul n (finiteDiagonal c) (finiteDiagonal c) i j +
          matMul n (finiteDiagonal s) (finiteDiagonal s) i j) =
      idMatrix n := by
  ext i j
  rw [matMul_finiteDiagonal_self c, matMul_finiteDiagonal_self s]
  by_cases hij : i = j
  case pos =>
    subst j
    simp [finiteDiagonal, idMatrix, hcs i]
  case neg =>
    simp [finiteDiagonal, idMatrix, hij]

/-- Source-shaped diagonal CS square identity for Problem 19.12:
`C^2 + S^2 = I` when `C = diag(c)`, `S = diag(s)`, and
`c_i^2 + s_i^2 = 1`. -/
theorem mgsProblem1912_csDiagonal_square_sum {n : Nat}
    {C S : Fin n -> Fin n -> Real} {c s : Fin n -> Real}
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    (fun i j => matMul n C C i j + matMul n S S i j) = idMatrix n := by
  rw [hCdiag, hSdiag]
  exact matMul_finiteDiagonal_csSquareSum c s hcs

/-- Removing an orthogonal left factor and a diagonal symmetric factor from the
top CS block gives the right-rotated diagonal square Gram matrix. -/
theorem rectangularGram_matMul_orthogonal_diag_right {n : Nat}
    {U C W : Fin n -> Fin n -> Real} {c : Fin n -> Real}
    (hUorth : IsOrthogonal n U)
    (hCdiag : C = finiteDiagonal c) :
    rectangularGram (matMul n U (matMul n C (finiteTranspose W))) =
      matMul n W (matMul n (matMul n C C) (finiteTranspose W)) := by
  have hCsym : finiteTranspose C = C := by
    rw [hCdiag]
    exact finiteTranspose_finiteDiagonal c
  calc
    rectangularGram (matMul n U (matMul n C (finiteTranspose W)))
        = matMul n (finiteTranspose (matMul n C (finiteTranspose W)))
            (matMul n C (finiteTranspose W)) := by
          exact rectangularGram_matMul_left_orthogonal hUorth
            (matMul n C (finiteTranspose W))
    _ = matMul n (matMul n W C) (matMul n C (finiteTranspose W)) := by
          rw [finiteTranspose_matMul, finiteTranspose_finiteTranspose, hCsym]
    _ = matMul n W (matMul n C (matMul n C (finiteTranspose W))) := by
          rw [matMul_assoc]
    _ = matMul n W (matMul n (matMul n C C) (finiteTranspose W)) := by
          congr 1
          rw [<- matMul_assoc]

/-- Removing an orthonormal rectangular left factor and a diagonal symmetric
factor from the bottom CS block gives the right-rotated diagonal square Gram
matrix. -/
theorem rectangularGram_matMulRect_orthonormal_diag_right {m n : Nat}
    {V : Fin m -> Fin n -> Real} {S W : Fin n -> Fin n -> Real}
    {s : Fin n -> Real}
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hSdiag : S = finiteDiagonal s) :
    rectangularGram (matMulRect m n n V (matMul n S (finiteTranspose W))) =
      matMul n W (matMul n (matMul n S S) (finiteTranspose W)) := by
  have hSsym : finiteTranspose S = S := by
    rw [hSdiag]
    exact finiteTranspose_finiteDiagonal s
  calc
    rectangularGram (matMulRect m n n V (matMul n S (finiteTranspose W)))
        = matMul n (finiteTranspose (matMul n S (finiteTranspose W)))
            (matMul n S (finiteTranspose W)) := by
          exact rectangularGram_matMulRect_of_orthonormal_left hVorth
            (matMul n S (finiteTranspose W))
    _ = matMul n (matMul n W S) (matMul n S (finiteTranspose W)) := by
          rw [finiteTranspose_matMul, finiteTranspose_finiteTranspose, hSsym]
    _ = matMul n W (matMul n S (matMul n S (finiteTranspose W))) := by
          rw [matMul_assoc]
    _ = matMul n W (matMul n (matMul n S S) (finiteTranspose W)) := by
          congr 1
          rw [<- matMul_assoc]

/-- Source-shaped CS block-column Gram identity for Problem 19.12:
if `P11 = U*C*W^T`, `P21 = V*S*W^T`, `U` and `W` are orthogonal,
`V` has orthonormal columns, and `C^2 + S^2 = I` is supplied by diagonal CS
data, then `P11^T P11 + P21^T P21 = I`. -/
theorem mgsProblem1912_csDiagonal_gram_sum_eq_id {m n : Nat}
    {P11 U C S W : Fin n -> Fin n -> Real}
    {P21 V : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
      idMatrix n := by
  have hTop :
      rectangularGram (matMul n U (matMul n C (finiteTranspose W))) =
        matMul n W (matMul n (matMul n C C) (finiteTranspose W)) :=
    rectangularGram_matMul_orthogonal_diag_right hUorth hCdiag
  have hBottom :
      rectangularGram (matMulRect m n n V (matMul n S (finiteTranspose W))) =
        matMul n W (matMul n (matMul n S S) (finiteTranspose W)) :=
    rectangularGram_matMulRect_orthonormal_diag_right hVorth hSdiag
  have hCS :
      (fun i j => matMul n C C i j + matMul n S S i j) = idMatrix n :=
    mgsProblem1912_csDiagonal_square_sum hCdiag hSdiag hcs
  have hWright : matMul n W (finiteTranspose W) = idMatrix n := by
    ext i j
    have hrow := hWorth.row_orthonormal i j
    simpa [matMul, finiteTranspose, idMatrix] using hrow
  have hsumMat :
      (fun i j =>
          matMul n W (matMul n (matMul n C C) (finiteTranspose W)) i j +
            matMul n W (matMul n (matMul n S S) (finiteTranspose W)) i j) =
        matMul n W
          (matMul n (fun i j => matMul n C C i j + matMul n S S i j)
            (finiteTranspose W)) := by
    symm
    calc
      matMul n W
          (matMul n (fun i j => matMul n C C i j + matMul n S S i j)
            (finiteTranspose W))
          = matMul n W
              (fun i j =>
                matMul n (matMul n C C) (finiteTranspose W) i j +
                  matMul n (matMul n S S) (finiteTranspose W) i j) := by
            rw [matMul_add_left]
      _ =
          fun i j =>
            matMul n W (matMul n (matMul n C C) (finiteTranspose W)) i j +
              matMul n W (matMul n (matMul n S S) (finiteTranspose W)) i j := by
            rw [matMul_add_right]
  ext i j
  rw [hP11, hP21]
  rw [congrFun (congrFun hTop i) j, congrFun (congrFun hBottom i) j]
  rw [congrFun (congrFun hsumMat i) j]
  calc
    matMul n W
        (matMul n (fun i j => matMul n C C i j + matMul n S S i j)
          (finiteTranspose W)) i j
        = matMul n W (matMul n (idMatrix n) (finiteTranspose W)) i j := by
          rw [hCS]
    _ = matMul n W (finiteTranspose W) i j := by
          rw [matMul_id_left]
    _ = idMatrix n i j := by
          rw [hWright]

/-- Scalar CS estimate used for the Problem 19.12 correction diagonal:
if `c^2 + s^2 = 1` and `s >= 0`, then `|c / (1 + s)| <= 1`. -/
theorem csHalfTangent_abs_le_one {c s : Real}
    (hs : 0 <= s) (hcs : c ^ 2 + s ^ 2 = 1) :
    |c / (1 + s)| <= 1 := by
  have hc_sq : c ^ 2 <= 1 := by
    nlinarith [sq_nonneg s]
  have hc_abs : |c| <= 1 := by
    exact (sq_le_one_iff_abs_le_one c).mp hc_sq
  have hden_pos : 0 < 1 + s := by linarith
  have hden_ge_one : 1 <= 1 + s := by linarith
  calc
    |c / (1 + s)| = |c| / |1 + s| := by
      rw [abs_div]
    _ = |c| / (1 + s) := by
      rw [abs_of_pos hden_pos]
    _ <= 1 / (1 + s) := by
      exact div_le_div_of_nonneg_right hc_abs hden_pos.le
    _ <= 1 := by
      exact (div_le_one hden_pos).2 hden_ge_one

/-- The diagonal Problem 19.12 correction factor is an operator-2-norm
contraction under the scalar CS identities. -/
theorem opNorm2Le_finiteDiagonal_csHalfTangent {n : Nat}
    (c s : Fin n -> Real)
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le (finiteDiagonal (fun i => c i / (1 + s i))) 1 := by
  exact
    opNorm2Le_finiteDiagonal_of_abs_le_one
      (fun i => c i / (1 + s i))
      (fun i => csHalfTangent_abs_le_one (hs i) (hcs i))

/-- Scalar identity behind `diag(c/(1+s)) * diag(c) = I - diag(s)`. -/
theorem csHalfTangent_mul_self {c s : Real}
    (hs : 0 <= s) (hcs : c ^ 2 + s ^ 2 = 1) :
    c / (1 + s) * c = 1 - s := by
  have hden_pos : 0 < 1 + s := by linarith
  have hden_ne : Ne (1 + s) 0 := ne_of_gt hden_pos
  field_simp [hden_ne]
  nlinarith

/-- Matrix form of the diagonal CS correction identity:
`diag(c/(1+s)) * diag(c) = I - diag(s)`. -/
theorem matMul_finiteDiagonal_csHalfTangent {n : Nat}
    (c s : Fin n -> Real)
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    matMul n (finiteDiagonal (fun i => c i / (1 + s i)))
        (finiteDiagonal c) =
      fun i j => idMatrix n i j - finiteDiagonal s i j := by
  ext i j
  by_cases hij : i = j
  case pos =>
    subst j
    simp [matMul, finiteDiagonal, idMatrix,
      csHalfTangent_mul_self (hs i) (hcs i)]
  case neg =>
    simp [matMul, finiteDiagonal, idMatrix, hij]

/-- Pure source-shaped correction-map data from Higham Problem 19.12.

This is the CS/polar payload before it is tied to a particular common
right factor `R`: `Q` has orthonormal columns, `F * P11 = Q - P21`, and
`F` is a contraction.  In the current MGS specialization the top block `P11`
is square. -/
structure MGSProblem1912CorrectionMapData (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 Q F : Fin m -> Fin n -> Real) : Prop where
  orthonormal : GramSchmidtOrthonormalColumns Q
  correction_factor :
    matMulRect m n n F P11 = fun i j => Q i j - P21 i j
  map_bound : rectOpNorm2Le F 1

/-- Additive orientation of the pure Problem 19.12 correction-map data:
`Q = P21 + F * P11`.

This is the form naturally produced by the CS/polar construction; the stored
field remains the subtraction form consumed by the existing repair lemmas. -/
theorem MGSProblem1912CorrectionMapData.add_factor_eq {m n : Nat}
    {P11 : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hdata : MGSProblem1912CorrectionMapData m n P11 P21 Q F) :
    Q = fun i j => P21 i j + matMulRect m n n F P11 i j := by
  ext i j
  have hcorr :
      matMulRect m n n F P11 i j = Q i j - P21 i j := by
    exact congrFun (congrFun hdata.correction_factor i) j
  rw [hcorr]
  ring

/-- Build pure Problem 19.12 correction-map data from the additive orientation
`Q = P21 + F * P11`.

This keeps the future CS/polar existence theorem from having to normalize its
output into a subtraction identity before the data can enter the existing
transport route. -/
theorem mgsProblem1912_correctionMapData_of_add_factor {m n : Nat}
    {P11 : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hQadd : Q = fun i j => P21 i j + matMulRect m n n F P11 i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  refine
    { orthonormal := hQorth
      correction_factor := ?_
      map_bound := hFbound }
  ext i j
  have hq :
      Q i j = P21 i j + matMulRect m n n F P11 i j := by
    exact congrFun (congrFun hQadd i) j
  rw [hq]
  ring

/-- Polar-factor algebra behind Higham Problem 19.12.

If the lower block has a polar-style factorization `P21 = Q * H`, and a
contractive bridge `T` satisfies `T * P11 = I - H`, then the correction map
`F = Q * T` has the required factor identity `F * P11 = Q - P21`. -/
theorem mgsProblem1912_polarAlgebra_correction_factor {m n : Nat}
    {P11 H T : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hP21 : P21 = matMulRect m n n Q H)
    (hF : F = matMulRect m n n Q T)
    (hTP : matMul n T P11 = fun i j => idMatrix n i j - H i j) :
    matMulRect m n n F P11 = fun i j => Q i j - P21 i j := by
  calc
    matMulRect m n n F P11
        = matMulRect m n n (matMulRect m n n Q T) P11 := by
          rw [hF]
    _ = matMulRect m n n Q (matMul n T P11) := by
          rw [matMulRect_assoc_square_right]
    _ = matMulRect m n n Q
        (fun i j => idMatrix n i j - H i j) := by
          rw [hTP]
    _ = fun i j =>
        matMulRect m n n Q (idMatrix n) i j -
          matMulRect m n n Q H i j := by
          rw [matMulRect_sub_right]
    _ = fun i j => Q i j - P21 i j := by
          rw [matMulRect_id_right, <- hP21]

/-- Build pure Problem 19.12 correction-map data from a polar-style algebraic
payload.

This is a non-diagonal alternative to the existing CS adapter: a future polar
existence theorem may supply `P21 = Q*H`, `T*P11 = I-H`, orthonormal columns of
`Q`, and the contraction bound for `F`. -/
theorem mgsProblem1912_correctionMapData_of_polarAlgebra {m n : Nat}
    {P11 H T : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hP21 : P21 = matMulRect m n n Q H)
    (hF : F = matMulRect m n n Q T)
    (hTP : matMul n T P11 = fun i j => idMatrix n i j - H i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  refine
    { orthonormal := hQorth
      correction_factor := ?_
      map_bound := hFbound }
  exact mgsProblem1912_polarAlgebra_correction_factor hP21 hF hTP

/-- Source-shaped polar-factor payload for the remaining Problem 19.12
existence step.

The open CS/polar theorem may target this data instead of diagonal CS factors:
`P21 = Q*H`, `Q` has orthonormal columns, `T*P11 = I-H`, and `T` is a
contraction. The checked algebra below then constructs the actual correction
map `F = Q*T`. -/
structure MGSProblem1912PolarFactorData (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 : Fin m -> Fin n -> Real) where
  q : Fin m -> Fin n -> Real
  hMat : Fin n -> Fin n -> Real
  tMat : Fin n -> Fin n -> Real
  bottom_factor : P21 = matMulRect m n n q hMat
  bridge_factor :
    matMul n tMat P11 = fun i j => idMatrix n i j - hMat i j
  q_orth : GramSchmidtOrthonormalColumns q
  t_bound : opNorm2Le tMat 1

/-- A polar-factor payload gives the pure Problem 19.12 correction-map data
with correction map `F = Q*T`. -/
theorem MGSProblem1912PolarFactorData.to_correctionMapData {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : MGSProblem1912PolarFactorData m n P11 P21) :
    MGSProblem1912CorrectionMapData m n P11 P21 hpolar.q
      (matMulRect m n n hpolar.q hpolar.tMat) := by
  exact
    mgsProblem1912_correctionMapData_of_polarAlgebra
      hpolar.bottom_factor rfl hpolar.bridge_factor hpolar.q_orth
      (GramSchmidtOrthonormalColumns.rectOpNorm2Le_matMulRect_square_right
        hpolar.q_orth hpolar.t_bound)

/-- Additive orientation supplied by a polar-factor payload. -/
theorem MGSProblem1912PolarFactorData.add_factor_eq {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : MGSProblem1912PolarFactorData m n P11 P21) :
    hpolar.q =
      fun i j =>
        P21 i j +
          matMulRect m n n (matMulRect m n n hpolar.q hpolar.tMat)
            P11 i j := by
  exact MGSProblem1912CorrectionMapData.add_factor_eq
    hpolar.to_correctionMapData

/-- Existential pure correction-map data from a polar-factor payload. -/
theorem mgsProblem1912_correctionMapData_exists_of_polarFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : MGSProblem1912PolarFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  exact Exists.intro hpolar.q
    (Exists.intro (matMulRect m n n hpolar.q hpolar.tMat)
      hpolar.to_correctionMapData)

/-- Existential additive Problem 19.12 witnesses from a polar-factor payload. -/
theorem mgsProblem1912_add_factor_exists_of_polarFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : MGSProblem1912PolarFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  refine Exists.intro hpolar.q
    (Exists.intro (matMulRect m n n hpolar.q hpolar.tMat) ?_)
  exact
    And.intro hpolar.add_factor_eq
      (And.intro hpolar.q_orth hpolar.to_correctionMapData.map_bound)

/-- Nonempty polar-factor payloads provide pure correction-map data. -/
theorem mgsProblem1912_correctionMapData_exists_of_polarFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Nonempty (MGSProblem1912PolarFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  cases hpolar with
  | intro hpolar =>
      exact mgsProblem1912_correctionMapData_exists_of_polarFactorData hpolar

/-- Nonempty polar-factor payloads provide additive Problem 19.12 witnesses. -/
theorem mgsProblem1912_add_factor_exists_of_polarFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hpolar : Nonempty (MGSProblem1912PolarFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  cases hpolar with
  | intro hpolar =>
      exact mgsProblem1912_add_factor_exists_of_polarFactorData hpolar

/-- Source-shaped correction map from Higham Problem 19.12 after choosing the
common right factor `R` and the top perturbation block.

In the printed proof this map is `F = V (I + S)^{-1} C U^T`, obtained from
the CS decomposition of the padded Householder block columns. The structure
records only the algebraic payload needed downstream: `F * DeltaA1` is the
common-`R` correction that replaces the non-orthonormal block `P21` by an
orthonormal factor `Q`, and `F` has operator norm at most one. -/
structure MGSProblem1912CorrectionMap (m n : Nat)
    (P21 Q : Fin m -> Fin n -> Real)
    (dTop R : Fin n -> Fin n -> Real)
    (F : Fin m -> Fin n -> Real) : Prop where
  orthonormal : GramSchmidtOrthonormalColumns Q
  correction :
    matMulRect m n n F dTop =
      matMulRect m n n (fun i k => Q i k - P21 i k) R
  map_bound : rectOpNorm2Le F 1

/-- Specialize pure Problem 19.12 correction-map data to a common right factor
`R` once the top perturbation has the source shape `DeltaA_top = P11 * R`. -/
theorem MGSProblem1912CorrectionMapData.to_correctionMap {m n : Nat}
    {P11 : Fin n -> Fin n -> Real}
    {P21 Q F : Fin m -> Fin n -> Real}
    (hdata : MGSProblem1912CorrectionMapData m n P11 P21 Q F)
    {dTop R : Fin n -> Fin n -> Real}
    (hdTop : dTop = matMul n P11 R) :
    MGSProblem1912CorrectionMap m n P21 Q dTop R F := by
  refine
    { orthonormal := hdata.orthonormal
      correction := ?_
      map_bound := hdata.map_bound }
  calc
    matMulRect m n n F dTop
        = matMulRect m n n F (matMul n P11 R) := by
          rw [hdTop]
    _ = matMulRect m n n (matMulRect m n n F P11) R := by
          rw [<- matMulRect_assoc_square_right]
    _ = matMulRect m n n (fun i k => Q i k - P21 i k) R := by
          rw [hdata.correction_factor]

/-- The CS-algebra factor identity behind Higham Problem 19.12.

The source proof writes
`P11 = U C W^T`, `P21 = V S W^T`, `Q = V W^T`, and
`F = V T U^T`, where diagonal algebra gives `T C = I - S`. This lemma
packages only the exact multiplication needed to turn that data into
`F P11 = Q - P21`. -/
theorem mgsProblem1912_csAlgebra_correction_factor {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hU : matMul n (finiteTranspose U) U = idMatrix n)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j) :
    matMulRect m n n F P11 = fun i j => Q i j - P21 i j := by
  have hprod :
      matMul n (matMul n T (finiteTranspose U))
          (matMul n U (matMul n C (finiteTranspose W))) =
        matMul n (fun i j => idMatrix n i j - S i j)
          (finiteTranspose W) := by
    calc
      matMul n (matMul n T (finiteTranspose U))
          (matMul n U (matMul n C (finiteTranspose W)))
          =
        matMul n T
          (matMul n (finiteTranspose U)
            (matMul n U (matMul n C (finiteTranspose W)))) := by
            rw [matMul_assoc]
      _ =
        matMul n T
          (matMul n (matMul n (finiteTranspose U) U)
            (matMul n C (finiteTranspose W))) := by
            rw [<- matMul_assoc n (finiteTranspose U) U
              (matMul n C (finiteTranspose W))]
      _ =
        matMul n T
          (matMul n (idMatrix n) (matMul n C (finiteTranspose W))) := by
            rw [hU]
      _ = matMul n T (matMul n C (finiteTranspose W)) := by
            rw [matMul_id_left]
      _ = matMul n (matMul n T C) (finiteTranspose W) := by
            rw [<- matMul_assoc]
      _ =
        matMul n (fun i j => idMatrix n i j - S i j)
          (finiteTranspose W) := by
            rw [hTC]
  have hidSub :
      matMul n (fun i j => idMatrix n i j - S i j)
          (finiteTranspose W) =
        fun i j =>
          finiteTranspose W i j -
            matMul n S (finiteTranspose W) i j := by
    calc
      matMul n (fun i j => idMatrix n i j - S i j)
          (finiteTranspose W)
          =
        fun i j =>
          matMul n (idMatrix n) (finiteTranspose W) i j -
            matMul n S (finiteTranspose W) i j := by
            rw [matMul_sub_left]
      _ =
        fun i j =>
          finiteTranspose W i j -
            matMul n S (finiteTranspose W) i j := by
            rw [matMul_id_left]
  calc
    matMulRect m n n F P11
        =
      matMulRect m n n
        (matMulRect m n n V (matMul n T (finiteTranspose U)))
        (matMul n U (matMul n C (finiteTranspose W))) := by
          rw [hF, hP11]
    _ =
      matMulRect m n n V
        (matMul n (matMul n T (finiteTranspose U))
          (matMul n U (matMul n C (finiteTranspose W)))) := by
          rw [matMulRect_assoc_square_right]
    _ =
      matMulRect m n n V
        (matMul n (fun i j => idMatrix n i j - S i j)
          (finiteTranspose W)) := by
          rw [hprod]
    _ =
      matMulRect m n n V
        (fun i j =>
          finiteTranspose W i j -
            matMul n S (finiteTranspose W) i j) := by
          rw [hidSub]
    _ =
      fun i j =>
        matMulRect m n n V (finiteTranspose W) i j -
          matMulRect m n n V
            (matMul n S (finiteTranspose W)) i j := by
          rw [matMulRect_sub_right]
    _ = fun i j => Q i j - P21 i j := by
          rw [<- hQ, <- hP21]

/-- Build the pure Problem 19.12 correction-map data from explicit
CS-decomposition algebra data. -/
theorem mgsProblem1912_correctionMapData_of_csAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hU : matMul n (finiteTranspose U) U = idMatrix n)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  refine
    { orthonormal := hQorth
      correction_factor := ?_
      map_bound := hFbound }
  exact mgsProblem1912_csAlgebra_correction_factor hP11 hP21 hQ hF hU hTC

/-- Build the Problem 19.12 correction map from explicit CS-decomposition
algebra data.

This pushes the previous correction-map bridge one layer closer to Higham's
printed proof. The remaining mathematical work is now the CS/polar existence
data and the norm/columnwise budget estimates for the constructed map. -/
theorem mgsProblem1912_correctionMap_of_csAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hU : matMul n (finiteTranspose U) U = idMatrix n)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hFbound : rectOpNorm2Le F 1) :
    MGSProblem1912CorrectionMap m n P21 Q dTop R F := by
  exact
    (mgsProblem1912_correctionMapData_of_csAlgebra
      hP11 hP21 hQ hF hU hTC hQorth hFbound).to_correctionMap hdTop

/-- Build the pure Problem 19.12 correction-map data from CS algebra plus the
orthogonality and diagonal-norm facts supplied by the source CS/polar route.

Compared with `mgsProblem1912_correctionMap_of_csAlgebra`, this theorem derives
the orthonormality of `Q = V W^T` and the unit operator-norm bound for
`F = V T U^T`. The still-open source work is the actual CS/polar existence
theorem and the diagonal estimate `||T||_2 <= 1`, together with the final
norm/columnwise perturbation budgets. -/
theorem mgsProblem1912_correctionMapData_of_csOrthogonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hTbound : opNorm2Le T 1) :
    MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  have hUleft : matMul n (finiteTranspose U) U = idMatrix n := by
    ext i j
    have hcol := hUorth.col_orthonormal i j
    simpa [matMul, finiteTranspose, idMatrix] using hcol
  have hQorth : GramSchmidtOrthonormalColumns Q := by
    rw [hQ]
    exact
      GramSchmidtOrthonormalColumns.matMulRect_finiteTranspose_of_orthogonal
        hVorth hWorth
  have hUtop : opNorm2Le (finiteTranspose U) 1 := by
    simpa [finiteTranspose, matTranspose] using
      hUorth.transpose_opNorm2Le_one
  have hmiddle_rect :
      rectOpNorm2Le (matMul n T (finiteTranspose U)) (1 * 1) :=
    rectOpNorm2Le_matMul_square T (finiteTranspose U) (by norm_num)
      hTbound hUtop
  have hmiddle : opNorm2Le (matMul n T (finiteTranspose U)) 1 := by
    apply opNorm2Le_of_rectOpNorm2Le_square
    simpa using hmiddle_rect
  have hFbound : rectOpNorm2Le F 1 := by
    rw [hF]
    exact
      GramSchmidtOrthonormalColumns.rectOpNorm2Le_matMulRect_square_right
        hVorth hmiddle
  exact
    mgsProblem1912_correctionMapData_of_csAlgebra hP11 hP21 hQ hF
      hUleft hTC hQorth hFbound

/-- Build the Problem 19.12 correction map from CS algebra plus the
orthogonality and diagonal-norm facts supplied by the source CS/polar route. -/
theorem mgsProblem1912_correctionMap_of_csOrthogonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hTC : matMul n T C = fun i j => idMatrix n i j - S i j)
    (hTbound : opNorm2Le T 1) :
    MGSProblem1912CorrectionMap m n P21 Q dTop R F := by
  exact
    (mgsProblem1912_correctionMapData_of_csOrthogonalAlgebra
      hP11 hP21 hQ hF hUorth hWorth hVorth hTC hTbound).to_correctionMap
      hdTop

/-- Build the Problem 19.12 correction map from source-shaped diagonal CS
data.

This specializes the orthogonal CS bridge to diagonal
`C = diag(c)`, `S = diag(s)`, and `T = diag(c/(1+s))`. The scalar CS
conditions `c_i^2 + s_i^2 = 1` and `s_i >= 0` supply both the diagonal
identity `T C = I - S` and the bound `||T||_2 <= 1`. -/
theorem mgsProblem1912_correctionMapData_of_csDiagonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  have hTC : matMul n T C = fun i j => idMatrix n i j - S i j := by
    rw [hTdiag, hCdiag, hSdiag]
    exact matMul_finiteDiagonal_csHalfTangent c s hs hcs
  have hTbound : opNorm2Le T 1 := by
    rw [hTdiag]
    exact opNorm2Le_finiteDiagonal_csHalfTangent c s hs hcs
  exact
    mgsProblem1912_correctionMapData_of_csOrthogonalAlgebra hP11 hP21 hQ
      hF hUorth hWorth hVorth hTC hTbound

/-- Build the Problem 19.12 correction map from source-shaped diagonal CS
data, after choosing the common right factor `R`. -/
theorem mgsProblem1912_correctionMap_of_csDiagonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    MGSProblem1912CorrectionMap m n P21 Q dTop R F := by
  exact
    (mgsProblem1912_correctionMapData_of_csDiagonalAlgebra
      hP11 hP21 hQ hF hUorth hWorth hVorth hCdiag hSdiag hTdiag
      hs hcs).to_correctionMap hdTop

/-- The top CS block `P11 = U C W^T` is a contraction when `C = diag(c)`,
`c_i^2 + s_i^2 = 1`, and `U` and `W` are orthogonal. -/
theorem mgsProblem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra
    {n : Nat}
    {P11 U C W : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hCdiag : C = finiteDiagonal c)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    opNorm2Le P11 1 := by
  have hCbound : opNorm2Le C 1 := by
    rw [hCdiag]
    exact opNorm2Le_finiteDiagonal_csCosine c s hcs
  have hWtop : opNorm2Le (finiteTranspose W) 1 := by
    simpa [finiteTranspose, matTranspose] using
      hWorth.transpose_opNorm2Le_one
  have hmiddle_rect :
      rectOpNorm2Le (matMul n C (finiteTranspose W)) (1 * 1) :=
    rectOpNorm2Le_matMul_square C (finiteTranspose W) (by norm_num)
      hCbound hWtop
  have hmiddle : opNorm2Le (matMul n C (finiteTranspose W)) 1 := by
    apply opNorm2Le_of_rectOpNorm2Le_square
    simpa using hmiddle_rect
  have hUbound : opNorm2Le U 1 := hUorth.opNorm2Le_one
  have hprod_rect :
      rectOpNorm2Le (matMul n U (matMul n C (finiteTranspose W))) (1 * 1) :=
    rectOpNorm2Le_matMul_square U (matMul n C (finiteTranspose W))
      (by norm_num) hUbound hmiddle
  have hprod : opNorm2Le (matMul n U (matMul n C (finiteTranspose W))) 1 := by
    apply opNorm2Le_of_rectOpNorm2Le_square
    simpa using hprod_rect
  simpa [hP11] using hprod

/-- The bottom CS block `P21 = V S W^T` is a rectangular contraction when
`S = diag(s)`, `c_i^2 + s_i^2 = 1`, `W` is orthogonal, and `V` has
orthonormal columns. -/
theorem mgsProblem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra
    {m n : Nat}
    {P21 V : Fin m -> Fin n -> Real}
    {S W : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hSdiag : S = finiteDiagonal s)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    rectOpNorm2Le P21 1 := by
  have hSbound : opNorm2Le S 1 := by
    rw [hSdiag]
    exact opNorm2Le_finiteDiagonal_csSine c s hcs
  have hWtop : opNorm2Le (finiteTranspose W) 1 := by
    simpa [finiteTranspose, matTranspose] using
      hWorth.transpose_opNorm2Le_one
  have hmiddle_rect :
      rectOpNorm2Le (matMul n S (finiteTranspose W)) (1 * 1) :=
    rectOpNorm2Le_matMul_square S (finiteTranspose W) (by norm_num)
      hSbound hWtop
  have hmiddle : opNorm2Le (matMul n S (finiteTranspose W)) 1 := by
    apply opNorm2Le_of_rectOpNorm2Le_square
    simpa using hmiddle_rect
  rw [hP21]
  exact
    GramSchmidtOrthonormalColumns.rectOpNorm2Le_matMulRect_square_right
      hVorth hmiddle

/-- Source-shaped diagonal CS factor payload for Problem 19.12.

This is the precise object the remaining CS/polar existence theorem should
produce from the padded block identities: factor equations for `P11` and
`P21`, the repaired orthonormal factor `Q`, the correction map `F`, and the
diagonal scalar CS data.  It packages the existence data only; the conversion
lemmas below still perform the checked algebraic transport. -/
structure MGSProblem1912CSDiagonalFactorData (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 : Fin m -> Fin n -> Real) where
  u : Fin n -> Fin n -> Real
  cMat : Fin n -> Fin n -> Real
  sMat : Fin n -> Fin n -> Real
  tMat : Fin n -> Fin n -> Real
  w : Fin n -> Fin n -> Real
  v : Fin m -> Fin n -> Real
  q : Fin m -> Fin n -> Real
  f : Fin m -> Fin n -> Real
  cDiag : Fin n -> Real
  sDiag : Fin n -> Real
  top_factor :
    P11 = matMul n u (matMul n cMat (finiteTranspose w))
  bottom_factor :
    P21 = matMulRect m n n v (matMul n sMat (finiteTranspose w))
  q_factor : q = matMulRect m n n v (finiteTranspose w)
  f_factor : f = matMulRect m n n v (matMul n tMat (finiteTranspose u))
  u_orth : IsOrthogonal n u
  w_orth : IsOrthogonal n w
  v_orth : GramSchmidtOrthonormalColumns v
  cMat_diag : cMat = finiteDiagonal cDiag
  sMat_diag : sMat = finiteDiagonal sDiag
  tMat_diag : tMat = finiteDiagonal (fun i => cDiag i / (1 + sDiag i))
  s_nonneg : forall i, 0 <= sDiag i
  cs_square : forall i, cDiag i ^ 2 + sDiag i ^ 2 = 1

/-- Package explicit diagonal CS witnesses into the source-shaped factor-data
object expected by the remaining Problem 19.12 CS/polar existence step. -/
def mgsProblem1912_csDiagonalFactorData_of_csDiagonalAlgebra {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    MGSProblem1912CSDiagonalFactorData m n P11 P21 where
  u := U
  cMat := C
  sMat := S
  tMat := T
  w := W
  v := V
  q := Q
  f := F
  cDiag := c
  sDiag := s
  top_factor := hP11
  bottom_factor := hP21
  q_factor := hQ
  f_factor := hF
  u_orth := hUorth
  w_orth := hWorth
  v_orth := hVorth
  cMat_diag := hCdiag
  sMat_diag := hSdiag
  tMat_diag := hTdiag
  s_nonneg := hs
  cs_square := hcs

/-- Explicit diagonal CS witnesses existentially provide the packaged factor
data, retaining the repaired `Q` and correction map `F` as its projections. -/
theorem mgsProblem1912_csDiagonalFactorData_exists_of_csDiagonalAlgebra
    {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Exists fun hdata : MGSProblem1912CSDiagonalFactorData m n P11 P21 =>
      hdata.q = Q /\ hdata.f = F := by
  refine
    Exists.intro
      (mgsProblem1912_csDiagonalFactorData_of_csDiagonalAlgebra
        hP11 hP21 hQ hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs
        hcs) ?_
  exact And.intro rfl rfl

/-- Explicit diagonal CS witnesses provide existence of the packaged factor
data, without exposing the particular repaired `Q` and correction map `F`. -/
theorem mgsProblem1912_csDiagonalFactorData_nonempty_of_csDiagonalAlgebra
    {m n : Nat}
    {P11 U C S T W : Fin n -> Fin n -> Real}
    {P21 Q V F : Fin m -> Fin n -> Real}
    {c s : Fin n -> Real}
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1) :
    Nonempty (MGSProblem1912CSDiagonalFactorData m n P11 P21) := by
  exact
    Nonempty.intro
      (mgsProblem1912_csDiagonalFactorData_of_csDiagonalAlgebra
        hP11 hP21 hQ hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs
        hcs)

/-- A source-shaped diagonal CS factor payload yields the pure Problem 19.12
correction-map data. -/
theorem MGSProblem1912CSDiagonalFactorData.to_correctionMapData {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    MGSProblem1912CorrectionMapData m n P11 P21 hcs.q hcs.f := by
  exact
    mgsProblem1912_correctionMapData_of_csDiagonalAlgebra
      hcs.top_factor hcs.bottom_factor hcs.q_factor hcs.f_factor
      hcs.u_orth hcs.w_orth hcs.v_orth hcs.cMat_diag hcs.sMat_diag
      hcs.tMat_diag hcs.s_nonneg hcs.cs_square

/-- A packaged diagonal CS factor payload supplies the source-facing additive
Problem 19.12 identity `Q = P21 + F * P11`. -/
theorem MGSProblem1912CSDiagonalFactorData.add_factor_eq {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    hcs.q = fun i j => P21 i j + matMulRect m n n hcs.f P11 i j := by
  exact MGSProblem1912CorrectionMapData.add_factor_eq
    hcs.to_correctionMapData

/-- Existential form of the previous bridge, matching the way the future
CS/polar theorem is expected to provide a repaired `Q` and correction map `F`. -/
theorem mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  exact Exists.intro hcs.q (Exists.intro hcs.f hcs.to_correctionMapData)

/-- Existential additive-orientation form of packaged diagonal CS factor data.

This is the weakest source-facing shape the remaining CS/polar theorem may
target if downstream code does not need the full packaged diagonal payload. -/
theorem mgsProblem1912_add_factor_exists_of_csDiagonalFactorData
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  refine Exists.intro hcs.q (Exists.intro hcs.f ?_)
  exact
    And.intro hcs.add_factor_eq
      (And.intro hcs.to_correctionMapData.orthonormal
        hcs.to_correctionMapData.map_bound)

/-- A source-shaped diagonal CS factor-payload existence certificate yields
existence of the pure Problem 19.12 correction-map data. -/
theorem mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Nonempty (MGSProblem1912CSDiagonalFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  cases hcs with
  | intro hcs =>
      exact mgsProblem1912_correctionMapData_exists_of_csDiagonalFactorData
        hcs

/-- A packaged diagonal CS factor-payload existence certificate yields
existence of the additive Problem 19.12 witnesses. -/
theorem mgsProblem1912_add_factor_exists_of_csDiagonalFactorData_nonempty
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : Nonempty (MGSProblem1912CSDiagonalFactorData m n P11 P21)) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  cases hcs with
  | intro hcs =>
      exact mgsProblem1912_add_factor_exists_of_csDiagonalFactorData hcs

/-- If the lower block in Problem 19.12 already has orthonormal columns, the
zero correction map is enough.  This closes the degenerate CS/polar branch
where the top block contributes no Gram defect. -/
theorem mgsProblem1912_correctionMapData_of_bottom_orthonormal {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hP21 : GramSchmidtOrthonormalColumns P21) :
    MGSProblem1912CorrectionMapData m n P11 P21 P21 (fun _ _ => 0) := by
  have hQadd :
      P21 =
        fun i j =>
          P21 i j +
            matMulRect m n n (fun (_ : Fin m) (_ : Fin n) => (0 : Real))
              P11 i j := by
    ext i j
    simp [matMulRect]
  have hFbound :
      rectOpNorm2Le (fun (_ : Fin m) (_ : Fin n) => (0 : Real)) 1 := by
    intro x
    have hzero :
        rectMatMulVec (fun (_ : Fin m) (_ : Fin n) => (0 : Real)) x =
          fun _ : Fin m => 0 := by
      ext i
      simp [rectMatMulVec]
    rw [hzero]
    have hnorm_zero : vecNorm2 (fun _ : Fin m => (0 : Real)) = 0 := by
      simp [vecNorm2, vecNorm2Sq]
    rw [hnorm_zero]
    simpa using vecNorm2_nonneg x
  exact mgsProblem1912_correctionMapData_of_add_factor
    hQadd hP21 hFbound

/-- Existence form of the zero-correction branch for Problem 19.12. -/
theorem mgsProblem1912_correctionMapData_exists_of_bottom_orthonormal
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hP21 : GramSchmidtOrthonormalColumns P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  let F0 : Fin m -> Fin n -> Real := fun _ _ => 0
  have hdata :
      MGSProblem1912CorrectionMapData m n P11 P21 P21 F0 :=
    mgsProblem1912_correctionMapData_of_bottom_orthonormal
      (P11 := P11) (P21 := P21) hP21
  exact
    Exists.intro P21 (Exists.intro F0 hdata)

/-- Additive-witness form of the zero-correction branch for Problem 19.12. -/
theorem mgsProblem1912_add_factor_exists_of_bottom_orthonormal {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hP21 : GramSchmidtOrthonormalColumns P21) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  let F0 : Fin m -> Fin n -> Real := fun _ _ => 0
  have hdata :
      MGSProblem1912CorrectionMapData m n P11 P21 P21 F0 :=
    mgsProblem1912_correctionMapData_of_bottom_orthonormal
      (P11 := P11) (P21 := P21) hP21
  exact
    Exists.intro P21
      (Exists.intro F0
        (And.intro hdata.add_factor_eq
          (And.intro hP21 hdata.map_bound)))

/-- Sanity check for the future CS/polar existence target: the block-column
Gram identity alone cannot imply the additive Problem 19.12 witnesses without
a tall/full-column-rank side condition.  For `m = 0`, `n = 1`, taking
`P11 = I` and the empty `P21` satisfies `P11^T P11 + P21^T P21 = I`, but no
matrix with zero rows can have one orthonormal column. -/
theorem mgsProblem1912_add_factor_gram_sum_not_dimension_free :
    let P11 : Fin 1 -> Fin 1 -> Real := idMatrix 1
    let P21 : Fin 0 -> Fin 1 -> Real := fun i => Fin.elim0 i
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
        idMatrix 1 /\
      Not (Exists fun Q : Fin 0 -> Fin 1 -> Real =>
        Exists fun F : Fin 0 -> Fin 1 -> Real =>
          (Q = fun i j => P21 i j + matMulRect 0 1 1 F P11 i j) /\
            GramSchmidtOrthonormalColumns Q /\
            rectOpNorm2Le F 1) := by
  dsimp only
  constructor
  case left =>
    ext i j
    fin_cases i
    fin_cases j
    simp [rectangularGram, finiteTranspose, matMulRect, idMatrix]
  case right =>
    intro h
    cases h with
    | intro Q hQ =>
        cases hQ with
        | intro F hF =>
            have hQorth : GramSchmidtOrthonormalColumns Q := hF.right.left
            have h00 := hQorth (0 : Fin 1) (0 : Fin 1)
            simp [rectangularGram, finiteTranspose, matMulRect, idMatrix] at h00

/-- Corrected source-shaped input for the remaining Problem 19.12 CS/polar
existence theorem.  The block-column Gram identity is not enough by itself:
the source tallness condition is carried explicitly as `n <= m`. -/
structure MGSProblem1912CSPolarInput (m n : Nat)
    (P11 : Fin n -> Fin n -> Real)
    (P21 : Fin m -> Fin n -> Real) : Prop where
  tall : n <= m
  gram_sum :
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
      idMatrix n

/-- The packaged diagonal CS factor data also supplies the block-column Gram
identity `P11^T P11 + P21^T P21 = I`. -/
theorem MGSProblem1912CSDiagonalFactorData.gram_sum_eq_id {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    (fun i j => rectangularGram P11 i j + rectangularGram P21 i j) =
      idMatrix n := by
  exact
    mgsProblem1912_csDiagonal_gram_sum_eq_id
      hcs.top_factor hcs.bottom_factor hcs.u_orth hcs.w_orth hcs.v_orth
      hcs.cMat_diag hcs.sMat_diag hcs.cs_square

/-- Supplied diagonal CS factor data satisfies the corrected CS/polar input
once the source tallness hypothesis is made explicit. -/
theorem MGSProblem1912CSPolarInput.of_csDiagonalFactorData {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hnm : n <= m)
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    MGSProblem1912CSPolarInput m n P11 P21 := by
  exact
    { tall := hnm
      gram_sum := hcs.gram_sum_eq_id }

/-- Full padded orthogonality plus source tallness gives the corrected
Problem 19.12 CS/polar input for the economy blocks. -/
theorem MGSProblem1912CSPolarInput.of_paddedEconomy_blocks {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hnm : n <= m)
    (hP : IsOrthogonal (n + m) P) :
    MGSProblem1912CSPolarInput m n
      (mgsPaddedEconomyP11 P) (mgsPaddedEconomyQ P) := by
  exact
    { tall := hnm
      gram_sum := mgsPaddedEconomy_blocks_gram_sum_eq_id hP }

/-- The corrected CS/polar input proves the top block is a square
operator-2 contraction. -/
theorem MGSProblem1912CSPolarInput.p11_opNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    opNorm2Le P11 1 := by
  exact opNorm2Le_of_rectOpNorm2Le_square P11
    (rectOpNorm2Le_one_left_of_rectangularGram_add_eq_id
      hinput.gram_sum)

/-- The corrected CS/polar input proves the bottom block is a rectangular
operator-2 contraction. -/
theorem MGSProblem1912CSPolarInput.p21_rectOpNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    rectOpNorm2Le P21 1 := by
  exact
    rectOpNorm2Le_one_right_of_rectangularGram_add_eq_id
      hinput.gram_sum

/-- The corrected CS/polar input rewrites the bottom block Gram matrix as the
complement of the top block Gram matrix. -/
theorem MGSProblem1912CSPolarInput.p21_gram_eq_id_sub_p11_gram {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    rectangularGram P21 =
      fun i j => idMatrix n i j - rectangularGram P11 i j := by
  ext i j
  have hsum := congrFun (congrFun hinput.gram_sum i) j
  linarith

/-- The corrected CS/polar input rewrites the top block Gram matrix as the
complement of the bottom block Gram matrix. -/
theorem MGSProblem1912CSPolarInput.p11_gram_eq_id_sub_p21_gram {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    rectangularGram P11 =
      fun i j => idMatrix n i j - rectangularGram P21 i j := by
  ext i j
  have hsum := congrFun (congrFun hinput.gram_sum i) j
  linarith

/-- The corrected CS/polar input exposes symmetry of the top Gram matrix. -/
theorem MGSProblem1912CSPolarInput.p11_gram_symmetric {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (_hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    forall i j : Fin n, rectangularGram P11 i j = rectangularGram P11 j i := by
  exact rectangularGram_symmetric P11

/-- The corrected CS/polar input exposes symmetry of the bottom Gram matrix. -/
theorem MGSProblem1912CSPolarInput.p21_gram_symmetric {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (_hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    forall i j : Fin n, rectangularGram P21 i j = rectangularGram P21 j i := by
  exact rectangularGram_symmetric P21

/-- The corrected CS/polar input proves that the top and bottom Gram matrices
commute, a local algebraic precondition for simultaneous CS diagonalization. -/
theorem MGSProblem1912CSPolarInput.grams_commute {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21) :
    matMul n (rectangularGram P11) (rectangularGram P21) =
      matMul n (rectangularGram P21) (rectangularGram P11) := by
  exact rectangularGram_commute_of_add_eq_id hinput.gram_sum

/-- If the top CS/polar block is zero, the corrected input says the bottom
block is already orthonormal. -/
theorem MGSProblem1912CSPolarInput.bottom_orthonormal_of_top_zero {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11zero : P11 = fun _ _ => 0) :
    GramSchmidtOrthonormalColumns P21 := by
  intro i j
  have hsum := congrFun (congrFun hinput.gram_sum i) j
  rw [hP11zero] at hsum
  simpa [rectangularGram, finiteTranspose, matMulRect] using hsum

/-- If the top CS/polar block has zero Gram matrix, the corrected input says
the bottom block is already orthonormal. -/
theorem MGSProblem1912CSPolarInput.bottom_orthonormal_of_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    GramSchmidtOrthonormalColumns P21 := by
  intro i j
  have hsum := congrFun (congrFun hinput.gram_sum i) j
  rw [hP11gram] at hsum
  simpa using hsum

/-- A zero top Gram matrix in the corrected CS/polar input means the top block
itself is zero. -/
theorem MGSProblem1912CSPolarInput.top_zero_of_top_gram_zero {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (_hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    P11 = fun _ _ => 0 := by
  exact (rectangularGram_eq_zero_iff P11).mp hP11gram

/-- Degenerate CS/polar correction-data existence: if the top block is zero,
the zero correction map repairs the already-orthonormal bottom block. -/
theorem mgsProblem1912_correctionMapData_exists_of_csPolarInput_top_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11zero : P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_bottom_orthonormal
      (hinput.bottom_orthonormal_of_top_zero hP11zero)

/-- Degenerate CS/polar additive-witness existence: if the top block is zero,
the full Problem 19.12 additive target follows with zero correction map. -/
theorem mgsProblem1912_add_factor_exists_of_csPolarInput_top_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11zero : P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_bottom_orthonormal
      (hinput.bottom_orthonormal_of_top_zero hP11zero)

/-- Degenerate CS/polar correction-data existence from a zero top Gram matrix.
This is the same zero-correction branch stated at the Gram level used by the
block-column identity. -/
theorem mgsProblem1912_correctionMapData_exists_of_csPolarInput_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      MGSProblem1912CorrectionMapData m n P11 P21 Q F := by
  exact
    mgsProblem1912_correctionMapData_exists_of_bottom_orthonormal
      (hinput.bottom_orthonormal_of_top_gram_zero hP11gram)

/-- Degenerate CS/polar additive-witness existence from a zero top Gram
matrix. -/
theorem mgsProblem1912_add_factor_exists_of_csPolarInput_top_gram_zero
    {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hinput : MGSProblem1912CSPolarInput m n P11 P21)
    (hP11gram : rectangularGram P11 = fun _ _ => 0) :
    Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun F : Fin m -> Fin n -> Real =>
      (Q = fun i j => P21 i j + matMulRect m n n F P11 i j) /\
        GramSchmidtOrthonormalColumns Q /\
        rectOpNorm2Le F 1 := by
  exact
    mgsProblem1912_add_factor_exists_of_bottom_orthonormal
      (hinput.bottom_orthonormal_of_top_gram_zero hP11gram)

/-- The packaged diagonal CS factor data proves the top block is a
contraction. -/
theorem MGSProblem1912CSDiagonalFactorData.p11_opNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    opNorm2Le P11 1 := by
  exact
    mgsProblem1912_p11_opNorm2Le_one_of_csDiagonalAlgebra
      hcs.top_factor hcs.u_orth hcs.w_orth hcs.cMat_diag hcs.cs_square

/-- The packaged diagonal CS factor data proves the bottom block is a
rectangular contraction. -/
theorem MGSProblem1912CSDiagonalFactorData.p21_rectOpNorm2Le_one {m n : Nat}
    {P11 : Fin n -> Fin n -> Real} {P21 : Fin m -> Fin n -> Real}
    (hcs : MGSProblem1912CSDiagonalFactorData m n P11 P21) :
    rectOpNorm2Le P21 1 := by
  exact
    mgsProblem1912_p21_rectOpNorm2Le_one_of_csDiagonalAlgebra
      hcs.bottom_factor hcs.w_orth hcs.v_orth hcs.sMat_diag hcs.cs_square

/-- A rectangular operator bound controls each column of a right product. -/
theorem columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob {m n p : Nat}
    (F : Fin m -> Fin n -> Real) (B : Fin n -> Fin p -> Real)
    {cF : Real} (hF : rectOpNorm2Le F cF) (j : Fin p) :
    columnFrob (matMulRect m n p F B) j <= cF * columnFrob B j := by
  have hleft :
      columnFrob (matMulRect m n p F B) j =
        vecNorm2 (rectMatMulVec F (fun k : Fin n => B k j)) := by
    rw [<- finiteVecNorm2_column_eq_columnFrob
        (matMulRect m n p F B) j,
      finiteVecNorm2_fin]
    rfl
  have hright :
      columnFrob B j = vecNorm2 (fun k : Fin n => B k j) := by
    rw [<- finiteVecNorm2_column_eq_columnFrob B j, finiteVecNorm2_fin]
  rw [hleft, hright]
  exact hF (fun k : Fin n => B k j)

/-- Operator-norm budget for the repaired Problem 19.12 perturbation
`F * DeltaA_top + DeltaA_bottom`. -/
theorem mgsRepairedPerturbation_rectOpNorm2Le_of_bounds {m n : Nat}
    {F dBottom : Fin m -> Fin n -> Real} {dTop : Fin n -> Fin n -> Real}
    {cF etaTop etaBottom : Real}
    (hcF : 0 <= cF)
    (hF : rectOpNorm2Le F cF)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom) :
    rectOpNorm2Le
      (fun i j => matMulRect m n n F dTop i j + dBottom i j)
      (cF * etaTop + etaBottom) := by
  have hprodRect :
      rectOpNorm2Le (rectMatMul F dTop) (cF * etaTop) :=
    rectOpNorm2Le_rectMatMul F dTop hcF hF hTop
  have hprod :
      rectOpNorm2Le (matMulRect m n n F dTop) (cF * etaTop) := by
    simpa [matMulRect, rectMatMul] using hprodRect
  exact rectOpNorm2Le_add (matMulRect m n n F dTop) dBottom hprod hBottom

/-- Columnwise budget for the repaired Problem 19.12 perturbation
`F * DeltaA_top + DeltaA_bottom`. -/
theorem mgsRepairedPerturbation_columnFrob_le_of_column_budget {m n : Nat}
    {A F dBottom : Fin m -> Fin n -> Real}
    {dTop : Fin n -> Fin n -> Real}
    {topBudget bottomBudget : Fin n -> Real} {cF c3 u : Real}
    (hcF : 0 <= cF)
    (hF : rectOpNorm2Le F cF)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hBudget :
      forall j, cF * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    forall j,
      columnFrob
          (fun i j => matMulRect m n n F dTop i j + dBottom i j) j <=
        c3 * u * columnFrob A j := by
  intro j
  have hprod :
      columnFrob (matMulRect m n n F dTop) j <=
        cF * columnFrob dTop j :=
    columnFrob_matMulRect_le_rectOpNorm2_mul_columnFrob F dTop hF j
  have hadd :
      columnFrob
          (fun i j => matMulRect m n n F dTop i j + dBottom i j) j <=
        columnFrob (matMulRect m n n F dTop) j +
          columnFrob dBottom j :=
    columnFrob_add_le (matMulRect m n n F dTop) dBottom j
  calc
    columnFrob
          (fun i j => matMulRect m n n F dTop i j + dBottom i j) j
        <= columnFrob (matMulRect m n n F dTop) j +
            columnFrob dBottom j := hadd
    _ <= cF * columnFrob dTop j + columnFrob dBottom j := by
          exact add_le_add hprod (le_refl (columnFrob dBottom j))
    _ <= cF * topBudget j + bottomBudget j := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hTopCol j) hcF)
            (hBottomCol j)
    _ <= c3 * u * columnFrob A j := hBudget j

/-- Algebraic repair step from Higham Problem 19.12.

Once a bounded correction map has been obtained, the repaired perturbation is
`F * DeltaA1 + DeltaA2`, and the bottom block factorization
`A + DeltaA2 = P21 * R` becomes an orthonormal common-`R` factorization
`A + (F * DeltaA1 + DeltaA2) = Q * R`. The norm and columnwise budgets are
passed in explicitly; the missing source work is to obtain them from the
CS/polar construction. -/
theorem mgsProblem1912_repair_of_correctionMap {m n : Nat}
    {A P21 Q : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    {dBottom F : Fin m -> Fin n -> Real}
    {eta2 c3 u : Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hmap : MGSProblem1912CorrectionMap m n P21 Q dTop R F)
    (hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2)
    (hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j)
            j <=
          c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  let dA2 : Fin m -> Fin n -> Real :=
    fun i j => matMulRect m n n F dTop i j + dBottom i j
  refine Exists.intro Q ?_
  refine Exists.intro dA2 ?_
  refine And.intro hmap.orthonormal ?_
  have hfact :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q R := by
    ext i j
    have hbottom_ij :
        A i j + dBottom i j = matMulRect m n n P21 R i j :=
      congrFun (congrFun hbottom i) j
    have hcorr_ij :
        matMulRect m n n F dTop i j =
          matMulRect m n n (fun i k => Q i k - P21 i k) R i j :=
      congrFun (congrFun hmap.correction i) j
    have hsub_ij :
        matMulRect m n n (fun i k => Q i k - P21 i k) R i j =
          matMulRect m n n Q R i j -
            matMulRect m n n P21 R i j :=
      congrFun
        (congrFun (matMulRect_sub_left_square_right Q P21 R) i) j
    calc
      A i j + dA2 i j
          = (A i j + dBottom i j) +
              matMulRect m n n F dTop i j := by
                simp [dA2]
                ring
      _ = matMulRect m n n P21 R i j +
            matMulRect m n n (fun i k => Q i k - P21 i k) R i j := by
                rw [hbottom_ij, hcorr_ij]
      _ = matMulRect m n n P21 R i j +
            (matMulRect m n n Q R i j -
              matMulRect m n n P21 R i j) := by
                rw [hsub_ij]
      _ = matMulRect m n n Q R i j := by ring
  exact And.intro hfact (And.intro hnorm hcol)

/-- Problem 19.12 repair with the repaired-perturbation budgets derived from
separate top and bottom perturbation budgets. -/
theorem mgsProblem1912_repair_of_correctionMap_of_perturbation_bounds
    {m n : Nat}
    {A P21 Q : Fin m -> Fin n -> Real}
    {dTop R : Fin n -> Fin n -> Real}
    {dBottom F : Fin m -> Fin n -> Real}
    {etaTop etaBottom eta2 c3 u : Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hmap : MGSProblem1912CorrectionMap m n P21 Q dTop R F)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  have hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2 :=
    rectOpNorm2Le_mono hNormBudget
      (mgsRepairedPerturbation_rectOpNorm2Le_of_bounds
        (by norm_num : (0 : Real) <= 1) hmap.map_bound hTop hBottom)
  have hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j) j <=
          c3 * u * columnFrob A j :=
    mgsRepairedPerturbation_columnFrob_le_of_column_budget
      (A := A) (F := F) (dBottom := dBottom) (dTop := dTop)
      (by norm_num : (0 : Real) <= 1) hmap.map_bound
      hTopCol hBottomCol hColBudget
  exact mgsProblem1912_repair_of_correctionMap hbottom hmap hnorm hcol

/-- Problem 19.12 repair from the pure correction-map data interface.

This is the data-first version of `mgsProblem1912_repair_of_correctionMap`:
the CS/polar existence theorem can provide `MGSProblem1912CorrectionMapData`
independently of the common `R`, and this theorem transports it through the
top-block equation `Delta A_top = P11 * R`. -/
theorem mgsProblem1912_repair_of_correctionMapData {m n : Nat}
    {A P21 Q F dBottom : Fin m -> Fin n -> Real}
    {P11 dTop R : Fin n -> Fin n -> Real}
    {eta2 c3 u : Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hdata : MGSProblem1912CorrectionMapData m n P11 P21 Q F)
    (hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2)
    (hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j)
            j <=
          c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    mgsProblem1912_repair_of_correctionMap hbottom
      (hdata.to_correctionMap hdTop) hnorm hcol

/-- Problem 19.12 repair from pure correction-map data, with the repaired
perturbation budgets derived from separate top and bottom budgets. -/
theorem mgsProblem1912_repair_of_correctionMapData_of_perturbation_bounds
    {m n : Nat}
    {A P21 Q F dBottom : Fin m -> Fin n -> Real}
    {P11 dTop R : Fin n -> Fin n -> Real}
    {etaTop etaBottom eta2 c3 u : Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hdata : MGSProblem1912CorrectionMapData m n P11 P21 Q F)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  exact
    mgsProblem1912_repair_of_correctionMap_of_perturbation_bounds
      hbottom (hdata.to_correctionMap hdTop)
      hTop hBottom hNormBudget hTopCol hBottomCol hColBudget

/-- Diagonal-CS version of the full Problem 19.12 repair step.

This combines `mgsProblem1912_correctionMap_of_csDiagonalAlgebra` with
`mgsProblem1912_repair_of_correctionMap`: once the CS/polar route supplies the
diagonal factor data and the repaired-perturbation budgets, the repaired
orthonormal common-`R` factorization follows directly. -/
theorem mgsProblem1912_repair_of_csDiagonalAlgebra {m n : Nat}
    {A P21 Q V F dBottom : Fin m -> Fin n -> Real}
    {P11 U C S T W dTop R : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    {eta2 c3 u : Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hnorm :
      rectOpNorm2Le
        (fun i j => matMulRect m n n F dTop i j + dBottom i j)
        eta2)
    (hcol :
      forall j,
        columnFrob
            (fun i j => matMulRect m n n F dTop i j + dBottom i j)
            j <=
          c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  have hmap : MGSProblem1912CorrectionMap m n P21 Q dTop R F :=
    mgsProblem1912_correctionMap_of_csDiagonalAlgebra hdTop hP11 hP21 hQ
      hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
  exact mgsProblem1912_repair_of_correctionMap hbottom hmap hnorm hcol

/-- Diagonal-CS Problem 19.12 repair with the repaired-perturbation budgets
derived from separate top and bottom perturbation budgets. -/
theorem mgsProblem1912_repair_of_csDiagonalAlgebra_of_perturbation_bounds
    {m n : Nat}
    {A P21 Q V F dBottom : Fin m -> Fin n -> Real}
    {P11 U C S T W dTop R : Fin n -> Fin n -> Real}
    {c s : Fin n -> Real}
    {etaTop etaBottom eta2 c3 u : Real}
    {topBudget bottomBudget : Fin n -> Real}
    (hbottom :
      (fun i j => A i j + dBottom i j) =
        matMulRect m n n P21 R)
    (hdTop : dTop = matMul n P11 R)
    (hP11 : P11 = matMul n U (matMul n C (finiteTranspose W)))
    (hP21 : P21 =
      matMulRect m n n V (matMul n S (finiteTranspose W)))
    (hQ : Q = matMulRect m n n V (finiteTranspose W))
    (hF : F = matMulRect m n n V (matMul n T (finiteTranspose U)))
    (hUorth : IsOrthogonal n U)
    (hWorth : IsOrthogonal n W)
    (hVorth : GramSchmidtOrthonormalColumns V)
    (hCdiag : C = finiteDiagonal c)
    (hSdiag : S = finiteDiagonal s)
    (hTdiag : T = finiteDiagonal (fun i => c i / (1 + s i)))
    (hs : forall i, 0 <= s i)
    (hcs : forall i, c i ^ 2 + s i ^ 2 = 1)
    (hTop : rectOpNorm2Le dTop etaTop)
    (hBottom : rectOpNorm2Le dBottom etaBottom)
    (hNormBudget : 1 * etaTop + etaBottom <= eta2)
    (hTopCol : forall j, columnFrob dTop j <= topBudget j)
    (hBottomCol : forall j, columnFrob dBottom j <= bottomBudget j)
    (hColBudget :
      forall j, 1 * topBudget j + bottomBudget j <=
        c3 * u * columnFrob A j) :
    Exists fun Qrepair : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Qrepair /\
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Qrepair R /\
      rectOpNorm2Le dA2 eta2 /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) := by
  have hmap : MGSProblem1912CorrectionMap m n P21 Q dTop R F :=
    mgsProblem1912_correctionMap_of_csDiagonalAlgebra hdTop hP11 hP21 hQ
      hF hUorth hWorth hVorth hCdiag hSdiag hTdiag hs hcs
  exact
    mgsProblem1912_repair_of_correctionMap_of_perturbation_bounds
      hbottom hmap hTop hBottom hNormBudget
      hTopCol hBottomCol hColBudget

/-- `Q^T Q - I`, the orthogonality residual appearing in Theorem 19.13. -/
def gramSchmidtOrthogonalityResidual {m n : Nat}
    (Q : Fin m -> Fin n -> Real) : Fin n -> Fin n -> Real :=
  fun i j => rectangularGram Q i j - idMatrix n i j

/-- The orthogonality residual of the bottom-left economy block is exactly the
negative top-left Gram defect.  This is the algebraic bridge from full padded
orthogonality toward the Problem 19.12 CS/polar repair route. -/
theorem mgsPaddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram {m n : Nat}
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    (hP : IsOrthogonal (n + m) P) :
    gramSchmidtOrthogonalityResidual (mgsPaddedEconomyQ P) =
      fun i j => -rectangularGram (mgsPaddedEconomyP11 P) i j := by
  ext i j
  have hgram :=
    congrFun (congrFun (mgsPaddedEconomyQ_gram_eq_id_sub_P11_gram hP) i) j
  unfold gramSchmidtOrthogonalityResidual
  rw [hgram]
  ring

/-- Norm consequence of the padded block identity before the CS/polar repair
step: controlling the top-left block controls the economy block's Gram
orthogonality residual quadratically. -/
theorem mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le
    {m n : Nat} {P : Fin (n + m) -> Fin (n + m) -> Real} {eta : Real}
    (hP : IsOrthogonal (n + m) P)
    (heta : 0 <= eta)
    (hP11 : rectOpNorm2Le (mgsPaddedEconomyP11 P) eta) :
    opNorm2Le (gramSchmidtOrthogonalityResidual (mgsPaddedEconomyQ P))
      (eta ^ 2) := by
  rw [mgsPaddedEconomyQ_orthogonalityResidual_eq_neg_P11_gram hP]
  exact opNorm2Le_neg
    (rectangularGram_opNorm2Le_of_rectOpNorm2Le heta hP11)

/-- Top-block right-inverse bridge: the source equation
`Delta A3 = P11 * R11`, plus a bounded right inverse for `R11`, controls the
top-left block `P11`. -/
theorem mgsPaddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse
    {m n : Nat} {P : Fin (n + m) -> Fin (n + m) -> Real}
    {dTop R Rinv : Fin n -> Fin n -> Real} {eta rho : Real}
    (htop : dTop = matMulRect n n n (mgsPaddedEconomyP11 P) R)
    (hRright : matMul n R Rinv = idMatrix n)
    (hdTop : rectOpNorm2Le dTop eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta) :
    rectOpNorm2Le (mgsPaddedEconomyP11 P) (eta * rho) := by
  exact right_factor_rectOpNorm2Le_of_product_mul_right_inverse
    htop hRright hdTop hRinv heta

/-- Combining the top-block right-inverse bridge with full padded orthogonality
gives a pre-repair Gram-residual bound for the economy `Q21` block. -/
theorem mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse
    {m n : Nat} {P : Fin (n + m) -> Fin (n + m) -> Real}
    {dTop R Rinv : Fin n -> Fin n -> Real} {eta rho : Real}
    (hP : IsOrthogonal (n + m) P)
    (htop : dTop = matMulRect n n n (mgsPaddedEconomyP11 P) R)
    (hRright : matMul n R Rinv = idMatrix n)
    (hdTop : rectOpNorm2Le dTop eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le (gramSchmidtOrthogonalityResidual (mgsPaddedEconomyQ P))
      ((eta * rho) ^ 2) := by
  exact
    mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_P11_rectOpNorm2Le
      hP (mul_nonneg heta hrho)
      (mgsPaddedEconomyP11_rectOpNorm2Le_of_top_product_right_inverse
        htop hRright hdTop hRinv heta)

/-- Pre-repair Gram-residual bound driven directly by the stacked perturbation
bound from `(19.34)`, the top equation `Delta A3 = P11 * R11`, and a bounded
right inverse for `R11`. -/
theorem mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_stacked_bound_top_product_right_inverse
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    {P : Fin (n + m) -> Fin (n + m) -> Real}
    {dTop : Fin n -> Fin n -> Real} {dBottom : Fin m -> Fin n -> Real}
    {R Rinv : Fin n -> Fin n -> Real} {c eta rho : Real}
    (hP : IsOrthogonal (n + m) P)
    (htop : dTop = matMulRect n n n (mgsPaddedEconomyP11 P) R)
    (hRright : matMul n R Rinv = idMatrix n)
    (hc : 0 <= c)
    (hbound : mgsStackedPerturbationColumnwiseBound A dTop dBottom c)
    (hresidual : c * frobNormRect A <= eta)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta)
    (hrho : 0 <= rho) :
    opNorm2Le (gramSchmidtOrthogonalityResidual (mgsPaddedEconomyQ P))
      ((eta * rho) ^ 2) := by
  exact
    mgsPaddedEconomyQ_orthogonalityResidual_opNorm2Le_of_top_product_right_inverse
      hP htop hRright
      (mgsTopPerturbation_rectOpNorm2Le_of_stackedColumnwiseBound
        A dTop dBottom hc hbound hresidual)
      hRinv heta hrho

/-- Orthonormal columns are equivalent to a zero Gram residual. -/
theorem gramSchmidtOrthogonalityResidual_eq_zero_of_orthonormal {m n : Nat}
    {Q : Fin m -> Fin n -> Real} (hQ : GramSchmidtOrthonormalColumns Q) :
    gramSchmidtOrthogonalityResidual Q = fun _ _ => 0 := by
  ext i j
  simp [gramSchmidtOrthogonalityResidual, hQ i j]

/-- Exact expansion of the Gram residual for a matrix `Qhat` close to an
orthonormal-column matrix `Q`.  This is the algebraic core of the later
`2*delta + delta^2` orthogonality-loss estimate. -/
theorem gramSchmidtOrthogonalityResidual_eq_close_expansion {m n : Nat}
    {Qhat Q : Fin m -> Fin n -> Real}
    (hQ : GramSchmidtOrthonormalColumns Q) :
    gramSchmidtOrthogonalityResidual Qhat =
      fun i j =>
        (Finset.univ.sum fun r : Fin m =>
          Q r i * (Qhat r j - Q r j)) +
        (Finset.univ.sum fun r : Fin m =>
          (Qhat r i - Q r i) * Q r j) +
        (Finset.univ.sum fun r : Fin m =>
          (Qhat r i - Q r i) * (Qhat r j - Q r j)) := by
  ext i j
  unfold gramSchmidtOrthogonalityResidual rectangularGram
  have horth :
      idMatrix n i j =
        (Finset.univ.sum fun r : Fin m => Q r i * Q r j) := by
    simpa [rectangularGram] using (hQ i j).symm
  calc
    (Finset.univ.sum fun r : Fin m => Qhat r i * Qhat r j) -
        idMatrix n i j =
        (Finset.univ.sum fun r : Fin m => Qhat r i * Qhat r j) -
          (Finset.univ.sum fun r : Fin m => Q r i * Q r j) := by
          rw [horth]
    _ = Finset.univ.sum fun r : Fin m =>
          Qhat r i * Qhat r j - Q r i * Q r j := by
          rw [Finset.sum_sub_distrib]
    _ = Finset.univ.sum fun r : Fin m =>
          Q r i * (Qhat r j - Q r j) +
            (Qhat r i - Q r i) * Q r j +
            (Qhat r i - Q r i) * (Qhat r j - Q r j) := by
          apply Finset.sum_congr rfl
          intro r _hr
          ring
    _ =
        (Finset.univ.sum fun r : Fin m =>
          Q r i * (Qhat r j - Q r j)) +
        (Finset.univ.sum fun r : Fin m =>
          (Qhat r i - Q r i) * Q r j) +
        (Finset.univ.sum fun r : Fin m =>
          (Qhat r i - Q r i) * (Qhat r j - Q r j)) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- If `Qhat` is within rectangular operator-2 distance `delta` of an
orthonormal-column `Q`, then the Gram residual of `Qhat` has the standard
`2*delta + delta^2` operator-2 bound. -/
theorem gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal
    {m n : Nat}
    {Qhat Q : Fin m -> Fin n -> Real} {delta : Real}
    (hQ : GramSchmidtOrthonormalColumns Q)
    (hclose : rectOpNorm2Le (fun i j => Qhat i j - Q i j) delta)
    (hdelta : 0 <= delta) :
    opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
      (2 * delta + delta ^ 2) := by
  let E : Fin m -> Fin n -> Real := fun i j => Qhat i j - Q i j
  have hres_prod :
      gramSchmidtOrthogonalityResidual Qhat =
        fun i j =>
          (rectMatMul (finiteTranspose Q) E i j +
            rectMatMul (finiteTranspose E) Q i j) +
          rectMatMul (finiteTranspose E) E i j := by
    ext i j
    have hentry := congrFun
      (congrFun (gramSchmidtOrthogonalityResidual_eq_close_expansion
        (Qhat := Qhat) (Q := Q) hQ) i) j
    simpa [rectMatMul, finiteTranspose, E] using hentry
  have hQrect : rectOpNorm2Le Q 1 :=
    GramSchmidtOrthonormalColumns.rectOpNorm2Le_one hQ
  have hQT : rectOpNorm2Le (finiteTranspose Q) 1 :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le Q (by norm_num) hQrect
  have hE : rectOpNorm2Le E delta := by
    simpa [E] using hclose
  have hET : rectOpNorm2Le (finiteTranspose E) delta :=
    rectOpNorm2Le_finiteTranspose_of_rectOpNorm2Le E hdelta hE
  have hT1 :
      rectOpNorm2Le (rectMatMul (finiteTranspose Q) E) (1 * delta) :=
    rectOpNorm2Le_rectMatMul (finiteTranspose Q) E (by norm_num) hQT hE
  have hT2 :
      rectOpNorm2Le (rectMatMul (finiteTranspose E) Q) (delta * 1) :=
    rectOpNorm2Le_rectMatMul (finiteTranspose E) Q hdelta hET hQrect
  have hT3 :
      rectOpNorm2Le (rectMatMul (finiteTranspose E) E) (delta * delta) :=
    rectOpNorm2Le_rectMatMul (finiteTranspose E) E hdelta hET hE
  have hT12 :
      rectOpNorm2Le
        (fun i j =>
          rectMatMul (finiteTranspose Q) E i j +
            rectMatMul (finiteTranspose E) Q i j)
        (1 * delta + delta * 1) :=
    rectOpNorm2Le_add
      (rectMatMul (finiteTranspose Q) E)
      (rectMatMul (finiteTranspose E) Q) hT1 hT2
  have hT123 :
      rectOpNorm2Le
        (fun i j =>
          (rectMatMul (finiteTranspose Q) E i j +
            rectMatMul (finiteTranspose E) Q i j) +
          rectMatMul (finiteTranspose E) E i j)
        ((1 * delta + delta * 1) + delta * delta) :=
    rectOpNorm2Le_add
      (fun i j =>
        rectMatMul (finiteTranspose Q) E i j +
          rectMatMul (finiteTranspose E) Q i j)
      (rectMatMul (finiteTranspose E) E) hT12 hT3
  have hT123' :
      rectOpNorm2Le
        (fun i j =>
          (rectMatMul (finiteTranspose Q) E i j +
            rectMatMul (finiteTranspose E) Q i j) +
          rectMatMul (finiteTranspose E) E i j)
        (2 * delta + delta ^ 2) := by
    convert hT123 using 1
    ring
  rw [hres_prod]
  exact opNorm2Le_of_rectOpNorm2Le_square _ hT123'

/-- Source-facing contract shape for Higham Theorem 19.13.

The printed theorem gives residual, orthogonality, and columnwise `R`-factor
backward-error bounds for MGS.  This structure records the same three channels
using the repository's predicate-style operator-2 bounds.  `normA` and
`kappaA` are external certificates for `||A||_2` and `kappa_2(A)`, and
`higherOrder` stands for the printed higher-order term. -/
structure ModifiedGramSchmidtBackwardError (m n : Nat)
    (A Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (c1 c2 c3 u normA kappaA higherOrder : Real) : Prop where
  upper : IsUpperTrapezoidal n n Rhat
  residual : Exists fun dA1 : Fin m -> Fin n -> Real =>
    (forall i j, A i j + dA1 i j = matMulRect m n n Qhat Rhat i j) /\
    rectOpNorm2Le dA1 (c1 * u * normA)
  orthogonality :
    opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
      (c2 * u * kappaA + higherOrder)
  r_factor : Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Q /\
      (forall i j, A i j + dA2 i j = matMulRect m n n Q Rhat i j) /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j)

/-- Output expected from the QR-sensitivity step in the proof of Higham
Theorem 19.13 after the economy-product form of `(19.34)` is available.

It deliberately contains only the QR-sensitivity consequences still missing
from the algebraic Householder-MGS handoff: the orthogonality-loss bound for
the computed economy `Qhat`, and the existence of a nearby orthonormal QR
witness that gives the columnwise `R`-factor quality channel. -/
structure ModifiedGramSchmidtQRSensitivityBridge (m n : Nat)
    (A Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (c2 c3 u kappaA higherOrder : Real) : Prop where
  orthogonality :
    opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
      (c2 * u * kappaA + higherOrder)
  r_factor : Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Q /\
      (forall i j, A i j + dA2 i j = matMulRect m n n Q Rhat i j) /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j)

/-- Source-labeled outputs of the QR-sensitivity route used in Higham
Theorem 19.13.

The printed proof obtains these from the sensitivity material around
`(19.35a)`, `(19.35b)`, `(19.36)`, and `(19.37)`, plus the nearby
orthonormal-witness argument for the `R`-factor.  The fields are still proof
obligations; this structure only makes the remaining route explicit instead of
hiding it behind one compact sensitivity hypothesis. -/
structure ModifiedGramSchmidtQRSensitivitySourceOutput (m n : Nat)
    (A Qhat : Fin m -> Fin n -> Real) (Rhat : Fin n -> Fin n -> Real)
    (c2 c3 u kappaA higherOrder : Real) : Prop where
  eq19_37_to_19_30_orthogonality :
    opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
      (c2 * u * kappaA + higherOrder)
  eq19_31_r_factor_quality : Exists fun Q : Fin m -> Fin n -> Real =>
    Exists fun dA2 : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns Q /\
      (forall i j, A i j + dA2 i j = matMulRect m n n Q Rhat i j) /\
      (forall j, columnFrob dA2 j <= c3 * u * columnFrob A j)

/-- The source-labeled QR-sensitivity outputs assemble the compact bridge used
by the MGS backward-error contract. -/
theorem ModifiedGramSchmidtQRSensitivityBridge.of_source_output {m n : Nat}
    {A Qhat : Fin m -> Fin n -> Real} {Rhat : Fin n -> Fin n -> Real}
    {c2 c3 u kappaA higherOrder : Real}
    (hsource :
      ModifiedGramSchmidtQRSensitivitySourceOutput m n A Qhat Rhat c2 c3 u
        kappaA higherOrder) :
    ModifiedGramSchmidtQRSensitivityBridge m n A Qhat Rhat c2 c3 u
      kappaA higherOrder where
  orthogonality := hsource.eq19_37_to_19_30_orthogonality
  r_factor := hsource.eq19_31_r_factor_quality

/-- Assemble the source-labeled QR-sensitivity outputs from a repaired
orthonormal factorization, perturbation bounds, a right-inverse certificate for
the common `Rhat`, and the scalar budget needed to fit the printed
orthogonality-loss constant.  This keeps the CS/polar repair and source
right-inverse estimates visible as hypotheses while closing the algebraic norm
bookkeeping from `(19.31)` to the Gram residual. -/
theorem ModifiedGramSchmidtQRSensitivitySourceOutput.of_commonR_bounds {m n : Nat}
    {A Qhat Q dA1 dA2 : Fin m -> Fin n -> Real}
    {Rhat Rinv : Fin n -> Fin n -> Real}
    {eta1 eta2 rho c2 c3 u kappaA higherOrder : Real}
    (hhat :
      (fun i j => A i j + dA1 i j) =
        matMulRect m n n Qhat Rhat)
    (hQfact :
      (fun i j => A i j + dA2 i j) =
        matMulRect m n n Q Rhat)
    (hQorth : GramSchmidtOrthonormalColumns Q)
    (hRright : matMul n Rhat Rinv = idMatrix n)
    (hdA1 : rectOpNorm2Le dA1 eta1)
    (hdA2 : rectOpNorm2Le dA2 eta2)
    (hRinv : rectOpNorm2Le Rinv rho)
    (heta : 0 <= eta1 + eta2)
    (hrho : 0 <= rho)
    (hbudget :
      2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2 <=
        c2 * u * kappaA + higherOrder)
    (hcol : forall j, columnFrob dA2 j <= c3 * u * columnFrob A j) :
    ModifiedGramSchmidtQRSensitivitySourceOutput m n A Qhat Rhat c2 c3 u
      kappaA higherOrder where
  eq19_37_to_19_30_orthogonality := by
    have hclose :
        rectOpNorm2Le (fun i k => Qhat i k - Q i k)
          ((eta1 + eta2) * rho) :=
      commonR_difference_rectOpNorm2Le_of_perturbation_bounds_mul_right_inverse
        hhat hQfact hRright hdA1 hdA2 hRinv heta
    have hdelta : 0 <= (eta1 + eta2) * rho := mul_nonneg heta hrho
    have horth :
        opNorm2Le (gramSchmidtOrthogonalityResidual Qhat)
          (2 * ((eta1 + eta2) * rho) + ((eta1 + eta2) * rho) ^ 2) :=
      gramSchmidtOrthogonalityResidual_opNorm2Le_of_close_orthonormal
        hQorth hclose hdelta
    exact qr_opNorm2Le_mono hbudget horth
  eq19_31_r_factor_quality := by
    refine Exists.intro Q ?_
    refine Exists.intro dA2 ?_
    refine And.intro hQorth ?_
    refine And.intro ?_ hcol
    intro i j
    exact congrFun (congrFun hQfact i) j

/-- Assemble the existing MGS backward-error contract from the compiled
economy product plus the separate QR-sensitivity outputs.  The residual
equation is supplied by the economy-product handoff; QR sensitivity supplies
only orthogonality loss and the orthonormal `R`-factor witness. -/
theorem ModifiedGramSchmidtBackwardError.of_economy_product_sensitivity
    {m n : Nat}
    {A Qhat : Fin m -> Fin n -> Real} {Rhat : Fin n -> Fin n -> Real}
    {dA1 : Fin m -> Fin n -> Real}
    {c1 c2 c3 u normA kappaA higherOrder : Real}
    (hupper : IsUpperTrapezoidal n n Rhat)
    (hprod : (fun i j => A i j + dA1 i j) =
      matMulRect m n n Qhat Rhat)
    (hresidual : rectOpNorm2Le dA1 (c1 * u * normA))
    (hsens :
      ModifiedGramSchmidtQRSensitivityBridge m n A Qhat Rhat c2 c3 u
        kappaA higherOrder) :
    ModifiedGramSchmidtBackwardError m n A Qhat Rhat c1 c2 c3 u normA
      kappaA higherOrder where
  upper := hupper
  residual := by
    refine Exists.intro dA1 ?_
    refine And.intro ?_ hresidual
    intro i j
    exact congrFun (congrFun hprod i) j
  orthogonality := hsens.orthogonality
  r_factor := hsens.r_factor

end

end NumStability
