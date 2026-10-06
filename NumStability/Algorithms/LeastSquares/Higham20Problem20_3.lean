import NumStability.Algorithms.LeastSquares.Higham20MPProse

/-!
# Higham Chapter 20, Problem 20.3: the Moore--Penrose inverse from an SVD

The book writes a full SVD and replaces every positive singular value by its
reciprocal, leaving the zero singular directions at zero.  This file uses the
equivalent compact SVD: the `r` retained columns are the nonzero singular
directions.  The construction is valid for every rank, including `r = 0`.
-/

open scoped BigOperators

namespace NumStability

/-- Exact compact real SVD data
`A = U_r diag(sigma) V_r^T`.  The columns of `U_r` and `V_r` are
orthonormal and the retained singular values are positive. -/
structure Higham20CompactRealSVD {m n r : Nat}
    (A : Fin m -> Fin n -> Real)
    (U : Fin m -> Fin r -> Real) (sigma : Fin r -> Real)
    (V : Fin n -> Fin r -> Real) : Prop where
  factorization :
    rectMatMul (rectMatMul U (diagMatrix sigma)) (finiteTranspose V) = A
  left_columns_orthonormal :
    rectMatMul (finiteTranspose U) U = idMatrix r
  right_columns_orthonormal :
    rectMatMul (finiteTranspose V) V = idMatrix r
  singularValue_pos : forall k : Fin r, 0 < sigma k

/-- The reciprocal diagonal appearing in Problem 20.3. -/
noncomputable def higham20Problem20_3ReciprocalDiagonal {r : Nat}
    (sigma : Fin r -> Real) : Fin r -> Fin r -> Real :=
  diagMatrix (fun k => (sigma k)⁻¹)

/-- The compact-SVD Moore--Penrose candidate
`V_r diag(sigma⁻¹) U_r^T`. -/
noncomputable def higham20Problem20_3SVDPseudoinverse {m n r : Nat}
    (U : Fin m -> Fin r -> Real) (sigma : Fin r -> Real)
    (V : Fin n -> Fin r -> Real) : Fin n -> Fin m -> Real :=
  rectMatMul
    (rectMatMul V (higham20Problem20_3ReciprocalDiagonal sigma))
    (finiteTranspose U)

private theorem higham20_rectMatMul_cancel_middle
    {a p q b : Nat}
    (X : Fin a -> Fin p -> Real)
    (L : Fin p -> Fin q -> Real) (R : Fin q -> Fin p -> Real)
    (Y : Fin p -> Fin b -> Real)
    (hLR : rectMatMul L R = idMatrix p) :
    rectMatMul (rectMatMul X L) (rectMatMul R Y) =
      rectMatMul X Y := by
  calc
    rectMatMul (rectMatMul X L) (rectMatMul R Y) =
        rectMatMul X (rectMatMul L (rectMatMul R Y)) :=
          rectMatMul_assoc X L (rectMatMul R Y)
    _ = rectMatMul X (rectMatMul (rectMatMul L R) Y) := by
          rw [rectMatMul_assoc L R Y]
    _ = rectMatMul X (rectMatMul (idMatrix p) Y) := by rw [hLR]
    _ = rectMatMul X Y := by rw [rectMatMul_id_left]

private theorem higham20_problem20_3_reciprocalDiagonal_left_inverse
    {r : Nat} (sigma : Fin r -> Real)
    (hsigma : forall k : Fin r, sigma k ≠ 0) :
    rectMatMul (higham20Problem20_3ReciprocalDiagonal sigma)
        (diagMatrix sigma) = idMatrix r := by
  simpa [higham20Problem20_3ReciprocalDiagonal, rectMatMul, diagMatrix,
    finiteMatMul, finiteDiagonal, idMatrix, finiteIdMatrix] using
    (finiteMatMul_finiteDiagonal_inv_self hsigma)

private theorem higham20_problem20_3_reciprocalDiagonal_right_inverse
    {r : Nat} (sigma : Fin r -> Real)
    (hsigma : forall k : Fin r, sigma k ≠ 0) :
    rectMatMul (diagMatrix sigma)
        (higham20Problem20_3ReciprocalDiagonal sigma) = idMatrix r := by
  simpa [higham20Problem20_3ReciprocalDiagonal, rectMatMul, diagMatrix,
    finiteMatMul, finiteDiagonal, idMatrix, finiteIdMatrix] using
    (finiteMatMul_finiteDiagonal_self_inv hsigma)

/-- Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed.,
Chapter 20, Problem 20.3 (p. 405): for an arbitrary-rank compact SVD
`A = U_r diag(sigma) V_r^T`, replacing the nonzero singular values by their
reciprocals gives a matrix satisfying all four Moore--Penrose equations. -/
theorem higham20_problem20_3_compactSVD_moorePenrose
    {m n r : Nat} (A : Fin m -> Fin n -> Real)
    (U : Fin m -> Fin r -> Real) (sigma : Fin r -> Real)
    (V : Fin n -> Fin r -> Real)
    (hSVD : Higham20CompactRealSVD A U sigma V) :
    RectMoorePenrosePseudoinverse m n A
      (higham20Problem20_3SVDPseudoinverse U sigma V) := by
  let D : Fin r -> Fin r -> Real := diagMatrix sigma
  let Dinv : Fin r -> Fin r -> Real :=
    higham20Problem20_3ReciprocalDiagonal sigma
  let Aplus : Fin n -> Fin m -> Real :=
    higham20Problem20_3SVDPseudoinverse U sigma V
  have hsigma : forall k : Fin r, sigma k ≠ 0 :=
    fun k => ne_of_gt (hSVD.singularValue_pos k)
  have hDinvD : rectMatMul Dinv D = idMatrix r := by
    simpa [D, Dinv] using
      higham20_problem20_3_reciprocalDiagonal_left_inverse sigma hsigma
  have hDDinv : rectMatMul D Dinv = idMatrix r := by
    simpa [D, Dinv] using
      higham20_problem20_3_reciprocalDiagonal_right_inverse sigma hsigma
  have hA : rectMatMul (rectMatMul U D) (finiteTranspose V) = A := by
    simpa [D] using hSVD.factorization
  have hAplus :
      rectMatMul (rectMatMul V Dinv) (finiteTranspose U) = Aplus := by
    rfl
  have hAAplus :
      rectMatMul A Aplus = rectMatMul U (finiteTranspose U) := by
    rw [← hA, ← hAplus]
    calc
      rectMatMul
          (rectMatMul (rectMatMul U D) (finiteTranspose V))
          (rectMatMul (rectMatMul V Dinv) (finiteTranspose U)) =
          rectMatMul (rectMatMul U D)
            (rectMatMul Dinv (finiteTranspose U)) := by
              rw [rectMatMul_assoc V Dinv (finiteTranspose U)]
              exact higham20_rectMatMul_cancel_middle
                (rectMatMul U D) (finiteTranspose V) V
                (rectMatMul Dinv (finiteTranspose U))
                hSVD.right_columns_orthonormal
      _ = rectMatMul U (finiteTranspose U) := by
            exact higham20_rectMatMul_cancel_middle U D Dinv
              (finiteTranspose U) hDDinv
  have hAplusA :
      rectMatMul Aplus A = rectMatMul V (finiteTranspose V) := by
    rw [← hA, ← hAplus]
    calc
      rectMatMul
          (rectMatMul (rectMatMul V Dinv) (finiteTranspose U))
          (rectMatMul (rectMatMul U D) (finiteTranspose V)) =
          rectMatMul (rectMatMul V Dinv)
            (rectMatMul D (finiteTranspose V)) := by
              rw [rectMatMul_assoc U D (finiteTranspose V)]
              exact higham20_rectMatMul_cancel_middle
                (rectMatMul V Dinv) (finiteTranspose U) U
                (rectMatMul D (finiteTranspose V))
                hSVD.left_columns_orthonormal
      _ = rectMatMul V (finiteTranspose V) := by
            exact higham20_rectMatMul_cancel_middle V Dinv D
              (finiteTranspose V) hDinvD
  constructor
  · rw [hAAplus, ← hA]
    calc
      rectMatMul (rectMatMul U (finiteTranspose U))
          (rectMatMul (rectMatMul U D) (finiteTranspose V)) =
          rectMatMul U (rectMatMul D (finiteTranspose V)) := by
            rw [rectMatMul_assoc U D (finiteTranspose V)]
            exact higham20_rectMatMul_cancel_middle U (finiteTranspose U) U
              (rectMatMul D (finiteTranspose V))
              hSVD.left_columns_orthonormal
      _ = rectMatMul (rectMatMul U D) (finiteTranspose V) := by
            rw [rectMatMul_assoc]
  · change rectMatMul (rectMatMul Aplus A) Aplus = Aplus
    rw [hAplusA, ← hAplus]
    calc
      rectMatMul (rectMatMul V (finiteTranspose V))
          (rectMatMul (rectMatMul V Dinv) (finiteTranspose U)) =
          rectMatMul V (rectMatMul Dinv (finiteTranspose U)) := by
            rw [rectMatMul_assoc V Dinv (finiteTranspose U)]
            exact higham20_rectMatMul_cancel_middle V (finiteTranspose V) V
              (rectMatMul Dinv (finiteTranspose U))
              hSVD.right_columns_orthonormal
      _ = rectMatMul (rectMatMul V Dinv) (finiteTranspose U) := by
            rw [rectMatMul_assoc]
  · rw [hAAplus]
    exact rectMatMul_self_transpose_symmetric U
  · rw [hAplusA]
    exact rectMatMul_self_transpose_symmetric V

private theorem higham20_symmetric_eq_of_mul_eq_left
    {n : Nat} (P Q : Fin n -> Fin n -> Real)
    (hP : IsSymmetricFiniteMatrix P) (hQ : IsSymmetricFiniteMatrix Q)
    (hPQ : rectMatMul P Q = P) (hQP : rectMatMul Q P = Q) :
    P = Q := by
  ext i j
  calc
    P i j = rectMatMul P Q i j := by rw [hPQ]
    _ = rectMatMul Q P j i := by
      unfold rectMatMul
      apply Finset.sum_congr rfl
      intro k _
      rw [hP i k, hQ k j]
      ring
    _ = Q j i := by rw [hQP]
    _ = Q i j := hQ j i

private theorem higham20_symmetric_eq_of_mul_eq_right
    {n : Nat} (P Q : Fin n -> Fin n -> Real)
    (hP : IsSymmetricFiniteMatrix P) (hQ : IsSymmetricFiniteMatrix Q)
    (hPQ : rectMatMul P Q = Q) (hQP : rectMatMul Q P = P) :
    P = Q := by
  ext i j
  calc
    P i j = rectMatMul Q P i j := by rw [hQP]
    _ = rectMatMul P Q j i := by
      unfold rectMatMul
      apply Finset.sum_congr rfl
      intro k _
      rw [hQ i k, hP k j]
      ring
    _ = Q j i := by rw [hPQ]
    _ = Q i j := hQ j i

/-- The four Moore--Penrose equations determine the pseudoinverse uniquely.
This is the uniqueness assertion in Higham's Problem 20.3. -/
theorem higham20_problem20_3_moorePenrose_unique
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (X Y : Fin n -> Fin m -> Real)
    (hX : RectMoorePenrosePseudoinverse m n A X)
    (hY : RectMoorePenrosePseudoinverse m n A Y) :
    X = Y := by
  have hDomainXY :
      rectMatMul (rectMatMul X A) (rectMatMul Y A) = rectMatMul X A := by
    calc
      rectMatMul (rectMatMul X A) (rectMatMul Y A) =
          rectMatMul X (rectMatMul (rectMatMul A Y) A) := by
            rw [rectMatMul_assoc X A (rectMatMul Y A),
              ← rectMatMul_assoc A Y A]
      _ = rectMatMul X A := by rw [hY.reproduces_matrix]
  have hDomainYX :
      rectMatMul (rectMatMul Y A) (rectMatMul X A) = rectMatMul Y A := by
    calc
      rectMatMul (rectMatMul Y A) (rectMatMul X A) =
          rectMatMul Y (rectMatMul (rectMatMul A X) A) := by
            rw [rectMatMul_assoc Y A (rectMatMul X A),
              ← rectMatMul_assoc A X A]
      _ = rectMatMul Y A := by rw [hX.reproduces_matrix]
  have hDomain : rectMatMul X A = rectMatMul Y A :=
    higham20_symmetric_eq_of_mul_eq_left
      (rectMatMul X A) (rectMatMul Y A)
      hX.domain_projection_symmetric hY.domain_projection_symmetric
      hDomainXY hDomainYX
  have hRangeXY :
      rectMatMul (rectMatMul A X) (rectMatMul A Y) = rectMatMul A Y := by
    calc
      rectMatMul (rectMatMul A X) (rectMatMul A Y) =
          rectMatMul (rectMatMul (rectMatMul A X) A) Y := by
            exact (rectMatMul_assoc (rectMatMul A X) A Y).symm
      _ = rectMatMul A Y := by rw [hX.reproduces_matrix]
  have hRangeYX :
      rectMatMul (rectMatMul A Y) (rectMatMul A X) = rectMatMul A X := by
    calc
      rectMatMul (rectMatMul A Y) (rectMatMul A X) =
          rectMatMul (rectMatMul (rectMatMul A Y) A) X := by
            exact (rectMatMul_assoc (rectMatMul A Y) A X).symm
      _ = rectMatMul A X := by rw [hY.reproduces_matrix]
  have hRange : rectMatMul A X = rectMatMul A Y :=
    higham20_symmetric_eq_of_mul_eq_right
      (rectMatMul A X) (rectMatMul A Y)
      hX.range_projection_symmetric hY.range_projection_symmetric
      hRangeXY hRangeYX
  calc
    X = rectMatMul (rectMatMul X A) X := hX.reproduces_pseudoinverse.symm
    _ = rectMatMul (rectMatMul Y A) X := by rw [hDomain]
    _ = rectMatMul Y (rectMatMul A X) := rectMatMul_assoc Y A X
    _ = rectMatMul Y (rectMatMul A Y) := by rw [hRange]
    _ = rectMatMul (rectMatMul Y A) Y := (rectMatMul_assoc Y A Y).symm
    _ = Y := hY.reproduces_pseudoinverse

/-- Swapping a matrix and its Moore--Penrose inverse swaps the first two
Penrose equations and the two symmetric projections. -/
theorem RectMoorePenrosePseudoinverse.reverse
    {m n : Nat} {A : Fin m -> Fin n -> Real}
    {Aplus : Fin n -> Fin m -> Real}
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    RectMoorePenrosePseudoinverse n m Aplus A where
  reproduces_matrix := hMP.reproduces_pseudoinverse
  reproduces_pseudoinverse := hMP.reproduces_matrix
  range_projection_symmetric := hMP.domain_projection_symmetric
  domain_projection_symmetric := hMP.range_projection_symmetric

/-- Higham, 2nd ed., Chapter 20, Problem 20.3: the Moore--Penrose inverse is
involutive.  If `Aplus` is the Moore--Penrose inverse of `A`, then every
Moore--Penrose inverse `Aplusplus` of `Aplus` is exactly `A`. -/
theorem higham20_problem20_3_moorePenrose_involutive
    {m n : Nat} (A : Fin m -> Fin n -> Real)
    (Aplus : Fin n -> Fin m -> Real)
    (Aplusplus : Fin m -> Fin n -> Real)
    (hAplus : RectMoorePenrosePseudoinverse m n A Aplus)
    (hAplusplus : RectMoorePenrosePseudoinverse n m Aplus Aplusplus) :
    Aplusplus = A :=
  higham20_problem20_3_moorePenrose_unique Aplus Aplusplus A
    hAplusplus hAplus.reverse

/-- Problem 20.3 combined source endpoint: the compact-SVD reciprocal table is
the unique Moore--Penrose inverse, and taking its Moore--Penrose inverse again
returns the original arbitrary-rank matrix. -/
theorem higham20_problem20_3_compactSVD_unique_and_involutive
    {m n r : Nat} (A : Fin m -> Fin n -> Real)
    (U : Fin m -> Fin r -> Real) (sigma : Fin r -> Real)
    (V : Fin n -> Fin r -> Real)
    (hSVD : Higham20CompactRealSVD A U sigma V) :
    let Aplus := higham20Problem20_3SVDPseudoinverse U sigma V
    RectMoorePenrosePseudoinverse m n A Aplus /\
      (forall Y : Fin n -> Fin m -> Real,
        RectMoorePenrosePseudoinverse m n A Y -> Y = Aplus) /\
      (forall Aplusplus : Fin m -> Fin n -> Real,
        RectMoorePenrosePseudoinverse n m Aplus Aplusplus ->
          Aplusplus = A) := by
  dsimp only
  have hMP := higham20_problem20_3_compactSVD_moorePenrose A U sigma V hSVD
  refine ⟨hMP, ?_, ?_⟩
  · intro Y hY
    exact higham20_problem20_3_moorePenrose_unique A Y _ hY hMP
  · intro Aplusplus hAplusplus
    exact higham20_problem20_3_moorePenrose_involutive
      A _ Aplusplus hMP hAplusplus

end NumStability
