import NumStability.Algorithms.Underdetermined.UnderdeterminedSpec

/-!
# Higham, 2nd ed., Section 14.5 (p. 278): rectangular Schulz iteration

This module formalizes the exact algebraic core of the parallel matrix-inverse
iteration printed in Section 14.5.  It intentionally separates that exact
core from the source's spectral-norm initializer criterion, which is closed in
the companion module
`NumStability.Source.Higham.Chapter14.Section05.SpectralConvergence`.
-/

namespace NumStability.Ch14Ext

open NumStability

private theorem ch14ext_matrixOf_matMul (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    Matrix.of (matMul n A B) = Matrix.of A * Matrix.of B := by
  ext i j
  simp [matMul, Matrix.mul_apply]

private theorem ch14ext_matrixOf_idMatrix (n : ℕ) :
    Matrix.of (idMatrix n) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
  ext i j
  simp [idMatrix, Matrix.one_apply]

private theorem ch14ext_matrixOf_sub (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    Matrix.of (fun i j => A i j - B i j) = Matrix.of A - Matrix.of B := rfl

private theorem ch14ext_matrixOf_two_id (n : ℕ) :
    Matrix.of (fun i j => 2 * idMatrix n i j) =
      (1 : Matrix (Fin n) (Fin n) ℝ) + 1 := by
  ext i j
  by_cases h : i = j
  · simp [idMatrix, h]
    norm_num
  · simp [idMatrix, h]

private theorem ch14ext_matrixOf_rectMatMul {m n p : ℕ}
    (A : Fin m → Fin n → ℝ) (B : Fin n → Fin p → ℝ) :
    Matrix.of (rectMatMul A B) = Matrix.of A * Matrix.of B := by
  ext i j
  simp [rectMatMul, Matrix.mul_apply]

private theorem ch14ext_rectMatMul_eq_matMul (n : ℕ)
    (A B : Fin n → Fin n → ℝ) :
    rectMatMul A B = matMul n A B := rfl

private theorem ch14ext_rectMatMul_two_id_right {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    rectMatMul A (fun i j => 2 * idMatrix n i j) =
      fun i j => 2 * A i j := by
  ext i j
  unfold rectMatMul idMatrix
  simp [Finset.mem_univ]
  ring

private theorem ch14ext_rectMatMul_two_id_left {m n : ℕ}
    (A : Fin m → Fin n → ℝ) :
    rectMatMul (fun i j => 2 * idMatrix m i j) A =
      fun i j => 2 * A i j := by
  ext i j
  unfold rectMatMul idMatrix
  simp [Finset.mem_univ]

/-! ## Rectangular source surface -/

/-- One rectangular Schulz step.  For `A : m x n`, its inverse iterate has
shape `X : n x m`. -/
noncomputable def ch14ext_rectSchulzStep {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    Fin n → Fin m → ℝ :=
  rectMatMul X
    (fun i j => 2 * idMatrix m i j - rectMatMul A X i j)

/-- Rectangular Schulz iterates starting from `X0 : n x m`. -/
noncomputable def ch14ext_rectSchulzIter {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X0 : Fin n → Fin m → ℝ) :
    ℕ → (Fin n → Fin m → ℝ)
  | 0 => X0
  | k + 1 => ch14ext_rectSchulzStep A (ch14ext_rectSchulzIter A X0 k)

/-- Rectangular left residual `I_m - A X`. -/
noncomputable def ch14ext_rectSchulzLeftResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    Fin m → Fin m → ℝ :=
  fun i j => idMatrix m i j - rectMatMul A X i j

/-- Rectangular right residual `I_n - X A`. -/
noncomputable def ch14ext_rectSchulzRightResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - rectMatMul X A i j

/-- The source initializer `X0 = alpha A^T` for a rectangular matrix. -/
noncomputable def ch14ext_rectSchulzTransposeInitializer {m n : ℕ}
    (alpha : ℝ) (A : Fin m → Fin n → ℝ) : Fin n → Fin m → ℝ :=
  fun i j => alpha * A j i

/-- The two initial residuals are `I_m-alpha A A^T` and
`I_n-alpha A^T A`. -/
theorem ch14ext_rectSchulzResiduals_transposeInitializer {m n : ℕ}
    (alpha : ℝ) (A : Fin m → Fin n → ℝ) :
    ch14ext_rectSchulzLeftResidual A
        (ch14ext_rectSchulzTransposeInitializer alpha A) =
        (fun i j => idMatrix m i j -
          alpha * rectMatMul A (fun i j => A j i) i j) ∧
      ch14ext_rectSchulzRightResidual A
        (ch14ext_rectSchulzTransposeInitializer alpha A) =
        (fun i j => idMatrix n i j -
          alpha * rectMatMul (fun i j => A j i) A i j) := by
  constructor <;> ext i j
  · simp only [ch14ext_rectSchulzLeftResidual,
      ch14ext_rectSchulzTransposeInitializer, rectMatMul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp only [ch14ext_rectSchulzRightResidual,
      ch14ext_rectSchulzTransposeInitializer, rectMatMul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

private theorem ch14ext_matrixOf_two_id_sub_rectMatMul {d p : ℕ}
    (A : Fin d → Fin p → ℝ) (B : Fin p → Fin d → ℝ) :
    Matrix.of (fun i j => 2 * idMatrix d i j - rectMatMul A B i j) =
      (1 + 1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.of A * Matrix.of B := by
  rw [ch14ext_matrixOf_sub, ch14ext_matrixOf_two_id,
    ch14ext_matrixOf_rectMatMul]

private theorem ch14ext_matrixOf_rectSchulzStep {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    Matrix.of (ch14ext_rectSchulzStep A X) =
      Matrix.of X * ((1 + 1) - Matrix.of A * Matrix.of X) := by
  unfold ch14ext_rectSchulzStep
  rw [ch14ext_matrixOf_rectMatMul,
    ch14ext_matrixOf_two_id_sub_rectMatMul]

private theorem ch14ext_matrixOf_rectLeftResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    Matrix.of (ch14ext_rectSchulzLeftResidual A X) =
      1 - Matrix.of A * Matrix.of X := by
  ext i j
  simp [ch14ext_rectSchulzLeftResidual, rectMatMul, Matrix.mul_apply,
    idMatrix, Matrix.one_apply]

private theorem ch14ext_matrixOf_rectRightResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    Matrix.of (ch14ext_rectSchulzRightResidual A X) =
      1 - Matrix.of X * Matrix.of A := by
  ext i j
  simp [ch14ext_rectSchulzRightResidual, rectMatMul, Matrix.mul_apply,
    idMatrix, Matrix.one_apply]

/-- The two printed rectangular step forms agree. -/
theorem ch14ext_rectSchulzStep_eq_left_form {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    ch14ext_rectSchulzStep A X =
      rectMatMul
        (fun i j => 2 * idMatrix n i j - rectMatMul X A i j) X := by
  unfold ch14ext_rectSchulzStep
  rw [rectMatMul_sub_right, ch14ext_rectMatMul_two_id_right,
    rectMatMul_sub_left, ch14ext_rectMatMul_two_id_left,
    rectMatMul_assoc]

/-- One rectangular Schulz step squares the `m x m` left residual. -/
theorem ch14ext_rectSchulzLeftResidual_step {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    ch14ext_rectSchulzLeftResidual A (ch14ext_rectSchulzStep A X) =
      rectMatMul (ch14ext_rectSchulzLeftResidual A X)
        (ch14ext_rectSchulzLeftResidual A X) := by
  change Matrix.of
      (ch14ext_rectSchulzLeftResidual A (ch14ext_rectSchulzStep A X)) =
    Matrix.of (rectMatMul (ch14ext_rectSchulzLeftResidual A X)
      (ch14ext_rectSchulzLeftResidual A X))
  rw [ch14ext_matrixOf_rectLeftResidual, ch14ext_matrixOf_rectSchulzStep,
    ch14ext_matrixOf_rectMatMul, ch14ext_matrixOf_rectLeftResidual]
  rw [← Matrix.mul_assoc]
  set B : Matrix (Fin m) (Fin m) ℝ := Matrix.of A * Matrix.of X
  change 1 - B * (1 + 1 - B) = (1 - B) * (1 - B)
  noncomm_ring

/-- One rectangular Schulz step squares the `n x n` right residual. -/
theorem ch14ext_rectSchulzRightResidual_step {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X : Fin n → Fin m → ℝ) :
    ch14ext_rectSchulzRightResidual A (ch14ext_rectSchulzStep A X) =
      rectMatMul (ch14ext_rectSchulzRightResidual A X)
        (ch14ext_rectSchulzRightResidual A X) := by
  rw [ch14ext_rectSchulzStep_eq_left_form]
  change Matrix.of (ch14ext_rectSchulzRightResidual A
      (rectMatMul
        (fun i j => 2 * idMatrix n i j - rectMatMul X A i j) X)) =
    Matrix.of (rectMatMul (ch14ext_rectSchulzRightResidual A X)
      (ch14ext_rectSchulzRightResidual A X))
  simp only [ch14ext_matrixOf_rectRightResidual,
    ch14ext_matrixOf_rectMatMul,
    ch14ext_matrixOf_two_id_sub_rectMatMul]
  rw [Matrix.mul_assoc]
  set B : Matrix (Fin n) (Fin n) ℝ := Matrix.of X * Matrix.of A
  change 1 - (1 + 1 - B) * B = (1 - B) * (1 - B)
  noncomm_ring

/-! ## Square specialization and convergence support -/

/-- One Schulz inverse-iteration step in the first printed form
`X (2I - A X)`. -/
noncomputable def ch14ext_schulzStep (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n X (fun i j => 2 * idMatrix n i j - matMul n A X i j)

/-- The Schulz iterates starting from `X0`. -/
noncomputable def ch14ext_schulzIter (n : ℕ)
    (A X0 : Fin n → Fin n → ℝ) : ℕ → (Fin n → Fin n → ℝ)
  | 0 => X0
  | k + 1 => ch14ext_schulzStep n A (ch14ext_schulzIter n A X0 k)

/-- Left residual `I - A X`. -/
noncomputable def ch14ext_schulzLeftResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - matMul n A X i j

/-- Right residual `I - X A`. -/
noncomputable def ch14ext_schulzRightResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - matMul n X A i j

/-- The source's recommended starting matrix `X0 = alpha Aᵀ`, specialized to
the square-matrix surface used throughout this Chapter 14 development. -/
noncomputable def ch14ext_schulzTransposeInitializer (n : ℕ) (alpha : ℝ)
    (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => alpha * A j i

/-- The left residual of `X0 = alpha Aᵀ` is exactly `I - alpha A Aᵀ`. -/
theorem ch14ext_schulzLeftResidual_transposeInitializer (n : ℕ) (alpha : ℝ)
    (A : Fin n → Fin n → ℝ) :
    ch14ext_schulzLeftResidual n A
        (ch14ext_schulzTransposeInitializer n alpha A) =
      fun i j => idMatrix n i j -
        alpha * matMul n A (fun i j => A j i) i j := by
  ext i j
  simp only [ch14ext_schulzLeftResidual, ch14ext_schulzTransposeInitializer,
    matMul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem ch14ext_matrixOf_schulzStep (n : ℕ)
    (A X : Fin n → Fin n → ℝ) :
    Matrix.of (ch14ext_schulzStep n A X) =
      Matrix.of X * ((1 + 1) - Matrix.of A * Matrix.of X) := by
  unfold ch14ext_schulzStep
  rw [ch14ext_matrixOf_matMul, ch14ext_matrixOf_sub,
    ch14ext_matrixOf_two_id, ch14ext_matrixOf_matMul]

private theorem ch14ext_matrixOf_leftResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) :
    Matrix.of (ch14ext_schulzLeftResidual n A X) =
      1 - Matrix.of A * Matrix.of X := by
  ext i j
  simp [ch14ext_schulzLeftResidual, matMul, Matrix.mul_apply, idMatrix,
    Matrix.one_apply]

private theorem ch14ext_matrixOf_rightResidual (n : ℕ)
    (A X : Fin n → Fin n → ℝ) :
    Matrix.of (ch14ext_schulzRightResidual n A X) =
      1 - Matrix.of X * Matrix.of A := by
  ext i j
  simp [ch14ext_schulzRightResidual, matMul, Matrix.mul_apply, idMatrix,
    Matrix.one_apply]

/-- The two forms printed for a Schulz step agree:
`X (2I - A X) = (2I - X A) X`. -/
theorem ch14ext_schulzStep_eq_left_form (n : ℕ)
    (A X : Fin n → Fin n → ℝ) :
    ch14ext_schulzStep n A X =
      matMul n (fun i j => 2 * idMatrix n i j - matMul n X A i j) X := by
  change Matrix.of (ch14ext_schulzStep n A X) =
    Matrix.of (matMul n (fun i j => 2 * idMatrix n i j - matMul n X A i j) X)
  rw [ch14ext_matrixOf_schulzStep, ch14ext_matrixOf_matMul,
    ch14ext_matrixOf_sub, ch14ext_matrixOf_two_id,
    ch14ext_matrixOf_matMul]
  noncomm_ring

/-- One Schulz step squares the left residual. -/
theorem ch14ext_schulzLeftResidual_step (n : ℕ)
    (A X : Fin n → Fin n → ℝ) :
    ch14ext_schulzLeftResidual n A (ch14ext_schulzStep n A X) =
      matMul n (ch14ext_schulzLeftResidual n A X)
        (ch14ext_schulzLeftResidual n A X) := by
  change Matrix.of (ch14ext_schulzLeftResidual n A (ch14ext_schulzStep n A X)) =
    Matrix.of (matMul n (ch14ext_schulzLeftResidual n A X)
      (ch14ext_schulzLeftResidual n A X))
  rw [ch14ext_matrixOf_leftResidual, ch14ext_matrixOf_schulzStep,
    ch14ext_matrixOf_matMul, ch14ext_matrixOf_leftResidual]
  noncomm_ring

/-- One Schulz step squares the right residual. -/
theorem ch14ext_schulzRightResidual_step (n : ℕ)
    (A X : Fin n → Fin n → ℝ) :
    ch14ext_schulzRightResidual n A (ch14ext_schulzStep n A X) =
      matMul n (ch14ext_schulzRightResidual n A X)
        (ch14ext_schulzRightResidual n A X) := by
  rw [ch14ext_schulzStep_eq_left_form]
  change Matrix.of (ch14ext_schulzRightResidual n A
      (matMul n (fun i j => 2 * idMatrix n i j - matMul n X A i j) X)) =
    Matrix.of (matMul n (ch14ext_schulzRightResidual n A X)
      (ch14ext_schulzRightResidual n A X))
  rw [ch14ext_matrixOf_rightResidual, ch14ext_matrixOf_matMul,
    ch14ext_matrixOf_sub, ch14ext_matrixOf_two_id,
    ch14ext_matrixOf_matMul, ch14ext_matrixOf_matMul,
    ch14ext_matrixOf_rightResidual]
  noncomm_ring

/-- Powers of one matrix add their exponents.  This local bridge matches the
repository's recursive `matPow` with the product needed by the Schulz proof. -/
theorem ch14ext_matPow_add (n : ℕ) (E : Fin n → Fin n → ℝ) (a b : ℕ) :
    matPow n E (a + b) = matMul n (matPow n E a) (matPow n E b) := by
  induction b with
  | zero => simp [matPow_zero, matMul_id_right]
  | succ b ih =>
      rw [Nat.add_succ, matPow_succ_right, ih, matPow_succ_right,
        matMul_assoc]

/-- Rectangular Schulz left residuals satisfy
`I_m-A X_k=(I_m-A X_0)^(2^k)`. -/
theorem ch14ext_rectSchulzLeftResidual_iter {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X0 : Fin n → Fin m → ℝ) (k : ℕ) :
    ch14ext_rectSchulzLeftResidual A (ch14ext_rectSchulzIter A X0 k) =
      matPow m (ch14ext_rectSchulzLeftResidual A X0) (2 ^ k) := by
  induction k with
  | zero => simp [ch14ext_rectSchulzIter, matPow_one]
  | succ k ih =>
      rw [ch14ext_rectSchulzIter, ch14ext_rectSchulzLeftResidual_step,
        ch14ext_rectMatMul_eq_matMul, ih, ← ch14ext_matPow_add]
      congr 2
      simp

/-- Rectangular Schulz right residuals satisfy
`I_n-X_k A=(I_n-X_0 A)^(2^k)`. -/
theorem ch14ext_rectSchulzRightResidual_iter {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (X0 : Fin n → Fin m → ℝ) (k : ℕ) :
    ch14ext_rectSchulzRightResidual A (ch14ext_rectSchulzIter A X0 k) =
      matPow n (ch14ext_rectSchulzRightResidual A X0) (2 ^ k) := by
  induction k with
  | zero => simp [ch14ext_rectSchulzIter, matPow_one]
  | succ k ih =>
      rw [ch14ext_rectSchulzIter, ch14ext_rectSchulzRightResidual_step,
        ch14ext_rectMatMul_eq_matMul, ih, ← ch14ext_matPow_add]
      congr 2
      simp

/-! ## Moore--Penrose support identities

These exact identities isolate the nullspace issue in the rectangular source
claim. The canonical `Section05.SpectralConvergence` companion combines them with
right-Gram spectral decay and a canonical Moore--Penrose construction.
-/

/-- A Moore--Penrose certificate implies `A^T (A Aplus) = A^T`.  This is the
base support identity for the printed initializer `alpha A^T`. -/
theorem ch14ext_rectMoorePenrose_transpose_mul_rangeProjection {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) :
    rectMatMul (finiteTranspose A) (rectMatMul A Aplus) =
      finiteTranspose A := by
  ext i j
  calc
    rectMatMul (finiteTranspose A) (rectMatMul A Aplus) i j =
        ∑ k : Fin m, A k i * rectMatMul A Aplus k j := by
          rfl
    _ = ∑ k : Fin m, rectMatMul A Aplus j k * A k i := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hMP.range_projection_symmetric k j]
          ring
    _ = rectMatMul (rectMatMul A Aplus) A j i := by
          rfl
    _ = A j i := by rw [hMP.reproduces_matrix]
    _ = finiteTranspose A i j := by rfl

/-- Every iterate from `X0 = alpha A^T` is supported on the range projector
`A Aplus`: `X_k (A Aplus) = X_k`. -/
theorem ch14ext_rectSchulzIter_mul_rangeProjection {m n : ℕ}
    (alpha : ℝ) (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) (k : ℕ) :
    rectMatMul
        (ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k)
        (rectMatMul A Aplus) =
      ch14ext_rectSchulzIter A
        (ch14ext_rectSchulzTransposeInitializer alpha A) k := by
  induction k with
  | zero =>
      have hAtP :=
        ch14ext_rectMoorePenrose_transpose_mul_rangeProjection A Aplus hMP
      change rectMatMul
          (ch14ext_rectSchulzTransposeInitializer alpha A)
          (rectMatMul A Aplus) =
        ch14ext_rectSchulzTransposeInitializer alpha A
      ext i j
      have hentry := congrFun (congrFun hAtP i) j
      calc
        rectMatMul (ch14ext_rectSchulzTransposeInitializer alpha A)
            (rectMatMul A Aplus) i j =
            alpha * rectMatMul (finiteTranspose A)
              (rectMatMul A Aplus) i j := by
                unfold rectMatMul ch14ext_rectSchulzTransposeInitializer
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x _
                simp [finiteTranspose]
                ring
        _ = alpha * finiteTranspose A i j := by rw [hentry]
        _ = ch14ext_rectSchulzTransposeInitializer alpha A i j := by rfl
  | succ k ih =>
      let X := ch14ext_rectSchulzIter A
        (ch14ext_rectSchulzTransposeInitializer alpha A) k
      let Q : Fin n → Fin n → ℝ :=
        fun i j => 2 * idMatrix n i j - rectMatMul X A i j
      calc
        rectMatMul
            (ch14ext_rectSchulzIter A
              (ch14ext_rectSchulzTransposeInitializer alpha A) (k + 1))
            (rectMatMul A Aplus) =
            rectMatMul (rectMatMul Q X) (rectMatMul A Aplus) := by
              rw [ch14ext_rectSchulzIter,
                ch14ext_rectSchulzStep_eq_left_form]
        _ = rectMatMul Q
              (rectMatMul X (rectMatMul A Aplus)) :=
                rectMatMul_assoc Q X (rectMatMul A Aplus)
        _ = rectMatMul Q X := by
              rw [show rectMatMul X (rectMatMul A Aplus) = X by
                simpa [X] using ih]
        _ = ch14ext_rectSchulzIter A
              (ch14ext_rectSchulzTransposeInitializer alpha A) (k + 1) := by
                rw [ch14ext_rectSchulzIter]
                exact (ch14ext_rectSchulzStep_eq_left_form A X).symm

/-- Exact rectangular error identity
`Aplus-X_k = (I-X_k A) Aplus` for a Moore--Penrose target.  The identity
explains why the residual eigenvalue `1` on `ker A` is harmless: its product
with `Aplus` is killed by the support invariant above. -/
theorem ch14ext_rectMoorePenrose_sub_iter_eq_rightResidual_mul {m n : ℕ}
    (alpha : ℝ) (A : Fin m → Fin n → ℝ)
    (Aplus : Fin n → Fin m → ℝ)
    (hMP : RectMoorePenrosePseudoinverse m n A Aplus) (k : ℕ) :
    (fun i j => Aplus i j -
        ch14ext_rectSchulzIter A
          (ch14ext_rectSchulzTransposeInitializer alpha A) k i j) =
      rectMatMul
        (ch14ext_rectSchulzRightResidual A
          (ch14ext_rectSchulzIter A
            (ch14ext_rectSchulzTransposeInitializer alpha A) k))
        Aplus := by
  let X := ch14ext_rectSchulzIter A
    (ch14ext_rectSchulzTransposeInitializer alpha A) k
  have hsupport : rectMatMul X (rectMatMul A Aplus) = X := by
    simpa [X] using
      ch14ext_rectSchulzIter_mul_rangeProjection alpha A Aplus hMP k
  have hsupportM :
      Matrix.of X * (Matrix.of A * Matrix.of Aplus) = Matrix.of X := by
    rw [← ch14ext_matrixOf_rectMatMul, ← ch14ext_matrixOf_rectMatMul,
      hsupport]
  change Matrix.of Aplus - Matrix.of X =
    Matrix.of (rectMatMul (ch14ext_rectSchulzRightResidual A X) Aplus)
  rw [ch14ext_matrixOf_rectMatMul,
    ch14ext_matrixOf_rectRightResidual, Matrix.sub_mul, Matrix.one_mul,
    Matrix.mul_assoc, hsupportM]

/-- Exact left-residual formula for the Schulz iterates:
`I - A X_k = (I - A X_0)^(2^k)`. -/
theorem ch14ext_schulzLeftResidual_iter (n : ℕ)
    (A X0 : Fin n → Fin n → ℝ) (k : ℕ) :
    ch14ext_schulzLeftResidual n A (ch14ext_schulzIter n A X0 k) =
      matPow n (ch14ext_schulzLeftResidual n A X0) (2 ^ k) := by
  induction k with
  | zero => simp [ch14ext_schulzIter, matPow_one]
  | succ k ih =>
      rw [ch14ext_schulzIter, ch14ext_schulzLeftResidual_step, ih,
        ← ch14ext_matPow_add]
      congr 2
      simp

/-- Exact right-residual formula for the Schulz iterates:
`I - X_k A = (I - X_0 A)^(2^k)`. -/
theorem ch14ext_schulzRightResidual_iter (n : ℕ)
    (A X0 : Fin n → Fin n → ℝ) (k : ℕ) :
    ch14ext_schulzRightResidual n A (ch14ext_schulzIter n A X0 k) =
      matPow n (ch14ext_schulzRightResidual n A X0) (2 ^ k) := by
  induction k with
  | zero => simp [ch14ext_schulzIter, matPow_one]
  | succ k ih =>
      rw [ch14ext_schulzIter, ch14ext_schulzRightResidual_step, ih,
        ← ch14ext_matPow_add]
      congr 2
      simp

/-- A matrix power sampled at the Schulz exponents `2^k` tends entrywise to
zero whenever its infinity norm is strictly below one.  This is a convenient
repository-level sufficient condition, not a replacement for the book's
sharper spectral-2-norm initializer criterion. -/
theorem ch14ext_matPow_twoPow_entry_tendsto_zero_of_infNorm_lt_one
    {n : ℕ} (hn : 0 < n) (E : Fin n → Fin n → ℝ)
    (hcontract : infNorm E < 1) (i j : Fin n) :
    Filter.Tendsto (fun k => matPow n E (2 ^ k) i j)
      Filter.atTop (nhds 0) := by
  have hentry : ∀ k : ℕ,
      ‖matPow n E (2 ^ k) i j‖ ≤ infNorm E ^ (2 ^ k) := by
    intro k
    rw [Real.norm_eq_abs]
    calc
      |matPow n E (2 ^ k) i j| ≤
          ∑ l : Fin n, |matPow n E (2 ^ k) i l| :=
        Finset.single_le_sum (fun l _ => abs_nonneg (matPow n E (2 ^ k) i l))
          (Finset.mem_univ j)
      _ ≤ infNorm (matPow n E (2 ^ k)) := row_sum_le_infNorm _ _
      _ ≤ infNorm E ^ (2 ^ k) := infNorm_matPow_le hn E (2 ^ k)
  have hpow : Filter.Tendsto (fun m : ℕ => infNorm E ^ m)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (infNorm_nonneg E) hcontract
  have hexponents : Filter.Tendsto (fun k : ℕ => 2 ^ k)
      Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt one_lt_two
  exact squeeze_zero_norm' (Filter.Eventually.of_forall hentry)
    (hpow.comp hexponents)

/-- Under an infinity-norm contraction of the initial left residual, every
left-residual entry of the Schulz iterates tends to zero. -/
theorem ch14ext_schulzLeftResidual_tendsto_zero_of_infNorm_lt_one
    {n : ℕ} (hn : 0 < n) (A X0 : Fin n → Fin n → ℝ)
    (hcontract : infNorm (ch14ext_schulzLeftResidual n A X0) < 1)
    (i j : Fin n) :
    Filter.Tendsto
      (fun k => ch14ext_schulzLeftResidual n A
        (ch14ext_schulzIter n A X0 k) i j)
      Filter.atTop (nhds 0) := by
  simpa only [ch14ext_schulzLeftResidual_iter] using
    ch14ext_matPow_twoPow_entry_tendsto_zero_of_infNorm_lt_one hn
      (ch14ext_schulzLeftResidual n A X0) hcontract i j

/-- Exact reconstruction of an iterate from a left inverse and its left
residual: `X_k = A⁻¹ - A⁻¹(I-A X_k)`. -/
theorem ch14ext_schulzIter_eq_inverse_sub_leftResidual
    (n : ℕ) (A A_inv X0 : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv) (k : ℕ) :
    ch14ext_schulzIter n A X0 k =
      fun i j => A_inv i j -
        matMul n A_inv
          (ch14ext_schulzLeftResidual n A (ch14ext_schulzIter n A X0 k)) i j := by
  have hInvM : Matrix.of A_inv * Matrix.of A =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa [Matrix.mul_apply, Matrix.one_apply] using hInv i j
  change Matrix.of (ch14ext_schulzIter n A X0 k) =
    Matrix.of (fun i j => A_inv i j -
      matMul n A_inv
        (ch14ext_schulzLeftResidual n A (ch14ext_schulzIter n A X0 k)) i j)
  rw [ch14ext_matrixOf_sub, ch14ext_matrixOf_matMul,
    ch14ext_matrixOf_leftResidual]
  calc
    Matrix.of (ch14ext_schulzIter n A X0 k) =
        (Matrix.of A_inv * Matrix.of A) *
          Matrix.of (ch14ext_schulzIter n A X0 k) := by rw [hInvM, one_mul]
    _ = Matrix.of A_inv - Matrix.of A_inv *
        (1 - Matrix.of A * Matrix.of (ch14ext_schulzIter n A X0 k)) := by
      noncomm_ring

/-- A square Schulz iteration converges entrywise to a certified inverse under
the repository-level sufficient condition `‖I-A X0‖∞ < 1`. -/
theorem ch14ext_schulzIter_tendsto_inverse_of_leftResidual_infNorm_lt_one
    {n : ℕ} (hn : 0 < n) (A A_inv X0 : Fin n → Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hcontract : infNorm (ch14ext_schulzLeftResidual n A X0) < 1)
    (i j : Fin n) :
    Filter.Tendsto (fun k => ch14ext_schulzIter n A X0 k i j)
      Filter.atTop (nhds (A_inv i j)) := by
  have hproduct : Filter.Tendsto
      (fun k => matMul n A_inv
        (ch14ext_schulzLeftResidual n A (ch14ext_schulzIter n A X0 k)) i j)
      Filter.atTop (nhds 0) := by
    simpa [matMul] using
      tendsto_finset_sum (Finset.univ : Finset (Fin n))
        (fun l _ =>
          (ch14ext_schulzLeftResidual_tendsto_zero_of_infNorm_lt_one
            hn A X0 hcontract l j).const_mul (A_inv i l))
  have hlimit := (tendsto_const_nhds.sub hproduct :
    Filter.Tendsto
      (fun k => A_inv i j - matMul n A_inv
        (ch14ext_schulzLeftResidual n A (ch14ext_schulzIter n A X0 k)) i j)
      Filter.atTop (nhds (A_inv i j - 0)))
  rw [show (fun k => ch14ext_schulzIter n A X0 k i j) =
      (fun k => A_inv i j - matMul n A_inv
        (ch14ext_schulzLeftResidual n A (ch14ext_schulzIter n A X0 k)) i j) by
    funext k
    exact congrFun (congrFun
      (ch14ext_schulzIter_eq_inverse_sub_leftResidual n A A_inv X0 hInv k) i) j]
  simpa using hlimit

end NumStability.Ch14Ext
