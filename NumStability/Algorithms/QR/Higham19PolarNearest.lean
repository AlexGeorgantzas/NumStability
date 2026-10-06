import NumStability.Algorithms.QR.GramSchmidtPolar
import NumStability.Algorithms.QR.Higham19Sensitivity

namespace NumStability

open scoped BigOperators

noncomputable section

/-!
# Higham Chapter 19: nearest orthonormal polar factor

Higham, printed page 377, states that for a real `m x n` matrix with `m >= n`,
an orthonormal polar factor is a nearest matrix with orthonormal columns in
both the matrix 2-norm and the Frobenius norm.  The construction below uses the
repository's right-Gram eigendecomposition and its rank-tolerant completion of
the left singular vectors.  In particular, no full-column-rank hypothesis is
introduced.

The stronger square statement for every unitarily invariant norm is the
separate Fan--Hoffman theorem cited by Higham.  It is literature-review
material on this page and is deliberately source-deferred here; it is not
needed for the rectangular 2- and Frobenius-norm closure below.
-/

namespace Higham19PolarNearest

/-- A rectangular matrix with orthonormal columns preserves Euclidean vector
norms exactly. -/
theorem vecNorm2_rectMatMulVec_eq_of_orthonormal {m n : Nat}
    {Q : Fin m -> Fin n -> Real}
    (hQ : GramSchmidtOrthonormalColumns Q) (x : Fin n -> Real) :
    vecNorm2 (rectMatMulVec Q x) = vecNorm2 x := by
  unfold vecNorm2
  congr 1
  calc
    vecNorm2Sq (rectMatMulVec Q x) =
        Finset.univ.sum fun j : Fin n =>
          Finset.univ.sum fun k : Fin n =>
            rectangularGram Q j k * (x j * x k) :=
      rectangularGram_quadratic_eq_vecNorm2Sq Q x
    _ = Finset.univ.sum fun j : Fin n =>
          Finset.univ.sum fun k : Fin n =>
            idMatrix n j k * (x j * x k) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hQ j k]
    _ = vecNorm2Sq x := idMatrix_quadratic_eq_vecNorm2Sq x

/-- A square orthogonal table is, in particular, a table with orthonormal
columns in the rectangular QR predicate. -/
theorem gramSchmidtOrthonormalColumns_of_isOrthogonal {n : Nat}
    {Q : Fin n -> Fin n -> Real} (hQ : IsOrthogonal n Q) :
    GramSchmidtOrthonormalColumns Q := by
  intro i j
  simpa [GramSchmidtOrthonormalColumns, rectangularGram, idMatrix] using
    hQ.col_orthonormal i j

/-- A diagonal table whose entries are bounded by `c` has Euclidean
operator bound `c`. -/
theorem opNorm2Le_finiteDiagonal_of_abs_le {n : Nat}
    (d : Fin n -> Real) {c : Real} (hc : 0 <= c)
    (hd : forall i, |d i| <= c) :
    opNorm2Le (finiteDiagonal d) c := by
  intro x
  have hpoint : forall i : Fin n,
      |matMulVec n (finiteDiagonal d) x i| <= c * |x i| := by
    intro i
    rw [matMulVec_finiteDiagonal, abs_mul]
    exact mul_le_mul_of_nonneg_right (hd i) (abs_nonneg (x i))
  calc
    vecNorm2 (matMulVec n (finiteDiagonal d) x)
        <= vecNorm2 (fun i : Fin n => c * |x i|) :=
      vecNorm2_le_of_abs_le _ _ hpoint
    _ = c * vecNorm2 x := by
      rw [vecNorm2_smul, abs_of_nonneg hc, vecNorm2_abs]

/-- The spectral positive factor `V diag(sigma) V^T` is positive
semidefinite, including when some singular values vanish. -/
theorem rectRightGramPolarH_finitePSD {m n : Nat}
    (A : Fin m -> Fin n -> Real) :
    finitePSD (rectRightGramPolarH A) := by
  intro x
  let V := rectRightGramEigenbasis A
  let s := rectRightGramBasisSingularValue A
  let y : Fin n -> Real := fun a => Finset.univ.sum fun i : Fin n => V i a * x i
  have hH : forall i j : Fin n,
      rectRightGramPolarH A i j =
        Finset.univ.sum fun a : Fin n => V i a * s a * V j a := by
    intro i j
    simp only [rectRightGramPolarH, matMul, finiteDiagonal, finiteTranspose]
    simp
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hinner : forall (i a : Fin n),
      (Finset.univ.sum fun j : Fin n =>
          (V i a * s a * V j a) * x j) =
        (V i a * s a) * y a := by
    intro i a
    calc
      (Finset.univ.sum fun j : Fin n =>
          (V i a * s a * V j a) * x j) =
          Finset.univ.sum fun j : Fin n =>
            (V i a * s a) * (V j a * x j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (V i a * s a) *
          Finset.univ.sum (fun j : Fin n => V j a * x j) := by
        rw [Finset.mul_sum]
      _ = (V i a * s a) * y a := by rfl
  have hform :
      finiteQuadraticForm (rectRightGramPolarH A) x =
        Finset.univ.sum fun a : Fin n => s a * y a ^ 2 := by
    unfold finiteQuadraticForm finiteMatVec
    simp_rw [hH]
    calc
      (Finset.univ.sum fun i : Fin n =>
          x i * Finset.univ.sum (fun j : Fin n =>
            (Finset.univ.sum fun a : Fin n => V i a * s a * V j a) * x j)) =
          Finset.univ.sum fun i : Fin n =>
            x i * Finset.univ.sum (fun a : Fin n =>
              Finset.univ.sum fun j : Fin n =>
                (V i a * s a * V j a) * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        congr 1
        calc
          (Finset.univ.sum fun j : Fin n =>
              (Finset.univ.sum fun a : Fin n => V i a * s a * V j a) * x j) =
              Finset.univ.sum fun j : Fin n =>
                Finset.univ.sum fun a : Fin n =>
                  (V i a * s a * V j a) * x j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
          _ = Finset.univ.sum fun a : Fin n =>
                Finset.univ.sum fun j : Fin n =>
                  (V i a * s a * V j a) * x j := by
            rw [Finset.sum_comm]
      _ = Finset.univ.sum fun i : Fin n =>
            Finset.univ.sum fun a : Fin n =>
              x i * (Finset.univ.sum fun j : Fin n =>
                (V i a * s a * V j a) * x j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
      _ = Finset.univ.sum fun a : Fin n =>
            Finset.univ.sum fun i : Fin n =>
              x i * (Finset.univ.sum fun j : Fin n =>
                (V i a * s a * V j a) * x j) := by
        rw [Finset.sum_comm]
      _ = Finset.univ.sum fun a : Fin n => s a * y a ^ 2 := by
        apply Finset.sum_congr rfl
        intro a _
        simp_rw [hinner]
        calc
          (Finset.univ.sum fun i : Fin n => x i * ((V i a * s a) * y a)) =
              Finset.univ.sum fun i : Fin n =>
                (s a * y a) * (V i a * x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = (s a * y a) *
              Finset.univ.sum (fun i : Fin n => V i a * x i) := by
            symm
            rw [Finset.mul_sum]
          _ = s a * y a ^ 2 := by
            change (s a * y a) * y a = _
            ring
  rw [hform]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (rectRightGramBasisSingularValue_nonneg A a) (sq_nonneg _)

/-- Fix any rank-tolerant orthonormal completion of the left singular table.
Its polar factor `L V^T` minimizes the exact rectangular matrix 2-norm against
every matrix with orthonormal columns. -/
theorem completedRightGramPolar_nearest_rectOpNorm2 {m n : Nat}
    (A L : Fin m -> Fin n -> Real)
    (hL : GramSchmidtOrthonormalColumns L)
    (hrec :
      matMulRect m n n L
          (matMul n
            (finiteDiagonal (rectRightGramBasisSingularValue A))
            (finiteTranspose (rectRightGramEigenbasis A))) = A)
    (Q : Fin m -> Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    rectOpNorm2
        (fun i j => A i j -
          matMulRect m n n L
            (finiteTranspose (rectRightGramEigenbasis A)) i j) <=
      rectOpNorm2 (fun i j => A i j - Q i j) := by
  let V := rectRightGramEigenbasis A
  let Vt := finiteTranspose V
  let s := rectRightGramBasisSingularValue A
  let D := finiteDiagonal s
  let U : Fin m -> Fin n -> Real := matMulRect m n n L Vt
  let E : Fin m -> Fin n -> Real := fun i j => A i j - U i j
  let F : Fin m -> Fin n -> Real := fun i j => A i j - Q i j
  let c : Real := rectOpNorm2 F
  have hVorth : IsOrthogonal n V := by
    simpa [V] using rectRightGramEigenbasis_isOrthogonal A
  have hVtorth : IsOrthogonal n Vt := by
    simpa [Vt, V, finiteTranspose, matTranspose] using hVorth.transpose
  have hVtcols : GramSchmidtOrthonormalColumns Vt :=
    gramSchmidtOrthonormalColumns_of_isOrthogonal hVtorth
  have hVtV : matMul n Vt V = idMatrix n := by
    ext a b
    simpa [Vt, V, matMul, finiteTranspose, idMatrix] using
      hVorth.col_orthonormal a b
  have hAV : matMulRect m n n A V = matMulRect m n n L D := by
    calc
      matMulRect m n n A V =
          matMulRect m n n
            (matMulRect m n n L (matMul n D Vt)) V := by
        rw [hrec]
      _ = matMulRect m n n L (matMul n (matMul n D Vt) V) := by
        rw [matMulRect_assoc_square_right]
      _ = matMulRect m n n L (matMul n D (matMul n Vt V)) := by
        rw [matMul_assoc]
      _ = matMulRect m n n L (matMul n D (idMatrix n)) := by
        rw [hVtV]
      _ = matMulRect m n n L D := by
        rw [matMul_id_right]
  have hc : 0 <= c := by
    exact rectOpNorm2_nonneg F
  have hcoeff : forall a : Fin n, |s a - 1| <= c := by
    intro a
    let v : Fin n -> Real := fun j => V j a
    let l : Fin m -> Real := fun i => L i a
    have hvnorm : vecNorm2 v = 1 := by
      simpa [v, V] using hVorth.column_vecNorm2_eq_one a
    have hlnorm : vecNorm2 l = 1 := by
      have hdiag := hL a a
      unfold GramSchmidtOrthonormalColumns rectangularGram at hdiag
      simpa [l, idMatrix, vecNorm2, vecNorm2Sq, pow_two] using
        congrArg Real.sqrt hdiag
    have hQvnorm : vecNorm2 (rectMatMulVec Q v) = 1 := by
      rw [vecNorm2_rectMatMulVec_eq_of_orthonormal hQ, hvnorm]
    have hAv : rectMatMulVec A v = fun i : Fin m => s a * l i := by
      ext i
      have hij := congrFun (congrFun hAV i) a
      calc
        rectMatMulVec A v i = L i a * s a := by
          simpa [matMulRect, rectMatMulVec, D, V, v, l,
            finiteDiagonal] using hij
        _ = s a * l i := by ring
    have hAvnorm : vecNorm2 (rectMatMulVec A v) = s a := by
      rw [hAv, vecNorm2_smul, hlnorm, mul_one,
        abs_of_nonneg (rectRightGramBasisSingularValue_nonneg A a)]
    have hFv : rectMatMulVec F v =
        fun i : Fin m => rectMatMulVec A v i - rectMatMulVec Q v i := by
      ext i
      unfold F rectMatMulVec
      rw [<- Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hreverse : |s a - 1| <= vecNorm2 (rectMatMulVec F v) := by
      rw [hFv, <- hAvnorm, <- hQvnorm]
      exact abs_vecNorm2_sub_le_vecNorm2_sub _ _
    have hop := rectOpNorm2Le_rectOpNorm2 F v
    rw [hvnorm, mul_one] at hop
    exact hreverse.trans hop
  let d : Fin n -> Real := fun a => s a - 1
  have hdiag : opNorm2Le (finiteDiagonal d) c :=
    opNorm2Le_finiteDiagonal_of_abs_le d hc hcoeff
  have hEfactor :
      E = matMulRect m n n L (matMul n (finiteDiagonal d) Vt) := by
    ext i j
    change A i j - U i j = _
    rw [<- hrec]
    simp [U, d, s, Vt, V, matMulRect, matMul, finiteDiagonal,
      finiteTranspose]
    rw [<- Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  have hEcert : rectOpNorm2Le E c := by
    intro x
    let y : Fin n -> Real := rectMatMulVec Vt x
    have hynorm : vecNorm2 y = vecNorm2 x := by
      exact vecNorm2_rectMatMulVec_eq_of_orthonormal hVtcols x
    have haction :
        rectMatMulVec E x =
          rectMatMulVec L (matMulVec n (finiteDiagonal d) y) := by
      rw [hEfactor]
      change
        rectMatMulVec
            (rectMatMul L (rectMatMul (finiteDiagonal d) Vt)) x = _
      rw [rectMatMulVec_rectMatMul, rectMatMulVec_rectMatMul]
      rfl
    calc
      vecNorm2 (rectMatMulVec E x) =
          vecNorm2 (rectMatMulVec L (matMulVec n (finiteDiagonal d) y)) := by
        rw [haction]
      _ = vecNorm2 (matMulVec n (finiteDiagonal d) y) :=
        vecNorm2_rectMatMulVec_eq_of_orthonormal hL _
      _ <= c * vecNorm2 y := hdiag y
      _ = c * vecNorm2 x := by rw [hynorm]
  have hmain : rectOpNorm2 E <= c :=
    H19Sensitivity.rectOpNorm2_le_of_rectOpNorm2Le E hc hEcert
  simpa [E, F, U, Vt, V, c] using hmain

/-- The same rank-tolerant completed polar factor minimizes the rectangular
Frobenius norm against every matrix with orthonormal columns. -/
theorem completedRightGramPolar_nearest_frobNormRect {m n : Nat}
    (A L : Fin m -> Fin n -> Real)
    (hL : GramSchmidtOrthonormalColumns L)
    (hrec :
      matMulRect m n n L
          (matMul n
            (finiteDiagonal (rectRightGramBasisSingularValue A))
            (finiteTranspose (rectRightGramEigenbasis A))) = A)
    (Q : Fin m -> Fin n -> Real)
    (hQ : GramSchmidtOrthonormalColumns Q) :
    frobNormRect
        (fun i j => A i j -
          matMulRect m n n L
            (finiteTranspose (rectRightGramEigenbasis A)) i j) <=
      frobNormRect (fun i j => A i j - Q i j) := by
  let V := rectRightGramEigenbasis A
  let Vt := finiteTranspose V
  let s := rectRightGramBasisSingularValue A
  let D := finiteDiagonal s
  let U : Fin m -> Fin n -> Real := matMulRect m n n L Vt
  let E : Fin m -> Fin n -> Real := fun i j => A i j - U i j
  let F : Fin m -> Fin n -> Real := fun i j => A i j - Q i j
  have hVorth : IsOrthogonal n V := by
    simpa [V] using rectRightGramEigenbasis_isOrthogonal A
  have hVtV : matMul n Vt V = idMatrix n := by
    ext a b
    simpa [Vt, V, matMul, finiteTranspose, idMatrix] using
      hVorth.col_orthonormal a b
  have hAV : matMulRect m n n A V = matMulRect m n n L D := by
    calc
      matMulRect m n n A V =
          matMulRect m n n
            (matMulRect m n n L (matMul n D Vt)) V := by
        rw [hrec]
      _ = matMulRect m n n L (matMul n (matMul n D Vt) V) := by
        rw [matMulRect_assoc_square_right]
      _ = matMulRect m n n L (matMul n D (matMul n Vt V)) := by
        rw [matMul_assoc]
      _ = matMulRect m n n L (matMul n D (idMatrix n)) := by
        rw [hVtV]
      _ = matMulRect m n n L D := by
        rw [matMul_id_right]
  have hUV : matMulRect m n n U V = L := by
    calc
      matMulRect m n n U V =
          matMulRect m n n (matMulRect m n n L Vt) V := by rfl
      _ = matMulRect m n n L (matMul n Vt V) := by
        rw [matMulRect_assoc_square_right]
      _ = matMulRect m n n L (idMatrix n) := by rw [hVtV]
      _ = L := matMulRect_id_right m n L
  have hEV :
      matMulRect m n n E V =
        fun i a => L i a * (s a - 1) := by
    calc
      matMulRect m n n E V =
          fun i a => matMulRect m n n A V i a -
            matMulRect m n n U V i a := by
        exact matMulRect_sub_left_square_right A U V
      _ = fun i a => matMulRect m n n L D i a - L i a := by
        rw [hAV, hUV]
      _ = fun i a => L i a * (s a - 1) := by
        ext i a
        simp [matMulRect, D, finiteDiagonal]
        ring
  have hFV :
      matMulRect m n n F V =
        fun i a => L i a * s a - matMulRect m n n Q V i a := by
    calc
      matMulRect m n n F V =
          fun i a => matMulRect m n n A V i a -
            matMulRect m n n Q V i a := by
        exact matMulRect_sub_left_square_right A Q V
      _ = fun i a => matMulRect m n n L D i a -
            matMulRect m n n Q V i a := by
        rw [hAV]
      _ = fun i a => L i a * s a - matMulRect m n n Q V i a := by
        ext i a
        simp [matMulRect, D, finiteDiagonal]
  have hcol : forall a : Fin n,
      vecNorm2Sq (fun i : Fin m => L i a * (s a - 1)) <=
        vecNorm2Sq
          (fun i : Fin m => L i a * s a - matMulRect m n n Q V i a) := by
    intro a
    let l : Fin m -> Real := fun i => L i a
    let v : Fin n -> Real := fun j => V j a
    let qv : Fin m -> Real := fun i => matMulRect m n n Q V i a
    have hlsq : vecNorm2Sq l = 1 := by
      have hdiag := hL a a
      simpa [l, GramSchmidtOrthonormalColumns, rectangularGram,
        vecNorm2Sq, idMatrix, pow_two] using hdiag
    have hvnorm : vecNorm2 v = 1 := by
      simpa [v, V] using hVorth.column_vecNorm2_eq_one a
    have hqvaction : qv = rectMatMulVec Q v := by
      rfl
    have hqvnorm : vecNorm2 qv = 1 := by
      rw [hqvaction, vecNorm2_rectMatMulVec_eq_of_orthonormal hQ, hvnorm]
    have hqvsq : vecNorm2Sq qv = 1 := by
      rw [<- vecNorm2_sq, hqvnorm]
      norm_num
    let inner : Real := Finset.univ.sum fun i : Fin m => l i * qv i
    have hinner : inner <= 1 := by
      have habs := abs_vecInnerProduct_le_vecNorm2_mul l qv
      have hlnorm : vecNorm2 l = 1 := by
        rw [vecNorm2, hlsq, Real.sqrt_one]
      have habs' : |inner| <= 1 := by
        simpa [inner, hlnorm, hqvnorm] using habs
      exact (le_abs_self inner).trans habs'
    have hleft :
        vecNorm2Sq (fun i : Fin m => L i a * (s a - 1)) =
          (s a - 1) ^ 2 := by
      have hsmul := vecNorm2Sq_smul (s a - 1) l
      have heq :
          (fun i : Fin m => L i a * (s a - 1)) =
            fun i : Fin m => (s a - 1) * l i := by
        ext i
        simp [l]
        ring
      rw [heq, hsmul, hlsq, mul_one]
    have hright :
        vecNorm2Sq
            (fun i : Fin m => L i a * s a - matMulRect m n n Q V i a) =
          s a ^ 2 + 1 - 2 * s a * inner := by
      unfold vecNorm2Sq
      calc
        (Finset.univ.sum fun i : Fin m =>
            (L i a * s a - matMulRect m n n Q V i a) ^ 2) =
            Finset.univ.sum fun i : Fin m =>
              (s a) ^ 2 * l i ^ 2 + qv i ^ 2 -
                2 * s a * (l i * qv i) := by
          apply Finset.sum_congr rfl
          intro i _
          simp [l, qv]
          ring
        _ = s a ^ 2 * vecNorm2Sq l + vecNorm2Sq qv -
              2 * s a * inner := by
          unfold vecNorm2Sq inner
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [Finset.mul_sum, Finset.mul_sum]
        _ = s a ^ 2 + 1 - 2 * s a * inner := by
          rw [hlsq, hqvsq]
          ring
    rw [hleft, hright]
    have hs0 := rectRightGramBasisSingularValue_nonneg A a
    nlinarith
  have hsqTrans :
      frobNormSqRect (matMulRect m n n E V) <=
        frobNormSqRect (matMulRect m n n F V) := by
    rw [hEV, hFV, frobNormSqRect_eq_sum_vecNorm2Sq_cols,
      frobNormSqRect_eq_sum_vecNorm2Sq_cols]
    exact Finset.sum_le_sum fun a _ => hcol a
  have hEinv :
      frobNormSqRect (matMulRect m n n E V) = frobNormSqRect E := by
    simpa [matMulRect, matMulRectRight] using
      frobNormSqRect_orthogonal_right E V hVorth
  have hFinv :
      frobNormSqRect (matMulRect m n n F V) = frobNormSqRect F := by
    simpa [matMulRect, matMulRectRight] using
      frobNormSqRect_orthogonal_right F V hVorth
  have hsq : frobNormSqRect E <= frobNormSqRect F := by
    rw [hEinv, hFinv] at hsqTrans
    exact hsqTrans
  have hmain : frobNormRect E <= frobNormRect F := by
    unfold frobNormRect
    exact Real.sqrt_le_sqrt hsq
  simpa [E, F, U, Vt, V] using hmain

/-- **Higham, Chapter 19, printed page 377 (rank-tolerant source form).**

For every real tall matrix `A`, the concrete right-Gram construction supplies
an orthonormal polar factor `U` with positive-semidefinite symmetric factor
`H`.  Against every other matrix `Q` with orthonormal columns, `U` is no
farther from `A` in either the exact matrix 2-norm or the Frobenius norm.

No positivity or full-rank assumption is made on the singular values. -/
theorem higham19_exists_nearest_orthonormal_polar {m n : Nat}
    (A : Fin m -> Fin n -> Real) (hnm : n <= m) :
    Exists fun U : Fin m -> Fin n -> Real =>
      GramSchmidtOrthonormalColumns U /\
      A = matMulRect m n n U (rectRightGramPolarH A) /\
      IsSymmetricFiniteMatrix (rectRightGramPolarH A) /\
      finitePSD (rectRightGramPolarH A) /\
      forall Q : Fin m -> Fin n -> Real,
        GramSchmidtOrthonormalColumns Q ->
          rectOpNorm2 (fun i j => A i j - U i j) <=
              rectOpNorm2 (fun i j => A i j - Q i j) /\
            frobNormRect (fun i j => A i j - U i j) <=
              frobNormRect (fun i j => A i j - Q i j) := by
  obtain ⟨L, hL, hLpos⟩ :=
    exists_rectRightGramLeftSingularCompletion_of_tall A hnm
  let V := rectRightGramEigenbasis A
  let Vt := finiteTranspose V
  let s := rectRightGramBasisSingularValue A
  let D := finiteDiagonal s
  let U : Fin m -> Fin n -> Real := matMulRect m n n L Vt
  have hrec : matMulRect m n n L (matMul n D Vt) = A := by
    simpa [D, Vt, V, s] using
      rectRightGramLeftSingularCompletion_mul_diagonal_transpose_eq
        A L hLpos
  have hVorth : IsOrthogonal n V := by
    simpa [V] using rectRightGramEigenbasis_isOrthogonal A
  have hVtV : matMul n Vt V = idMatrix n := by
    ext a b
    simpa [Vt, V, matMul, finiteTranspose, idMatrix] using
      hVorth.col_orthonormal a b
  have hUorth : GramSchmidtOrthonormalColumns U := by
    exact
      GramSchmidtOrthonormalColumns.matMulRect_finiteTranspose_of_orthogonal
        hL hVorth
  have hfactorRight :
      matMulRect m n n U (rectRightGramPolarH A) = A := by
    calc
      matMulRect m n n U (rectRightGramPolarH A) =
          matMulRect m n n (matMulRect m n n L Vt)
            (matMul n V (matMul n D Vt)) := by rfl
      _ = matMulRect m n n L
            (matMul n Vt (matMul n V (matMul n D Vt))) := by
        rw [matMulRect_assoc_square_right]
      _ = matMulRect m n n L
            (matMul n (matMul n Vt V) (matMul n D Vt)) := by
        rw [<- matMul_assoc]
      _ = matMulRect m n n L
            (matMul n (idMatrix n) (matMul n D Vt)) := by
        rw [hVtV]
      _ = matMulRect m n n L (matMul n D Vt) := by
        rw [matMul_id_left]
      _ = A := hrec
  have hHsym : IsSymmetricFiniteMatrix (rectRightGramPolarH A) := by
    intro i j
    have h := congrFun
      (congrFun (rectRightGramPolarH_symmetric A) j) i
    simpa [finiteTranspose] using h
  refine ⟨U, hUorth, hfactorRight.symm, hHsym,
    rectRightGramPolarH_finitePSD A, ?_⟩
  intro Q hQ
  constructor
  · simpa [U, Vt, V, D, s] using
      completedRightGramPolar_nearest_rectOpNorm2 A L hL
        (by simpa [D, Vt, V, s] using hrec) Q hQ
  · simpa [U, Vt, V, D, s] using
      completedRightGramPolar_nearest_frobNormRect A L hL
        (by simpa [D, Vt, V, s] using hrec) Q hQ

end Higham19PolarNearest

end

end NumStability
