import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 21: QR foundations for equations (21.1)-(21.4)

This file packages the exact algebra on printed pages 408-409.  An exact QR
certificate for `A^T` has the repository shape

`finiteTranspose A = matMulRectLeft Q (lsQRTallBlock R)`.

The rounded Householder factor has a different domain: source full row rank is
paired with the explicit computed-top-block nonbreakdown condition already
recorded by `Higham21QMethodFullRowRankComputedQRDomain`.
-/

/-- Full row rank of `A`, represented as full column rank of `A^T`, makes
    the underdetermined Gram matrix `A A^T` nonsingular. -/
theorem higham21_rectGram_det_ne_zero_of_transpose_full_col_rank
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hfull : lsRealRectColRank (finiteTranspose A) = m) :
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  have hinj : Function.Injective (rectMatMulVec (finiteTranspose A)) :=
    lsRealRectColRank_rectMatMulVec_injective_of_colRank_eq_card
      (finiteTranspose A) hfull
  have hdet :
      Matrix.det
        (rectLSGram (finiteTranspose A) : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    rectLSGram_det_ne_zero_of_rectMatMulVec_injective
      (finiteTranspose A) hinj
  simpa [rectLSGram, rectGram, finiteTranspose] using hdet

/-- Under an exact factorization `A^T = Q [R;0]`, full row rank of `A`
    forces the square top factor `R` to be nonsingular. -/
theorem higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m) :
    Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  have hA :
      A = finiteTranspose
        (matMulRectLeft Q (lsQRTallBlock (k := k) R)) := by
    ext i j
    have hij := congrFun (congrFun hAT j) i
    simpa [finiteTranspose] using hij
  have hdetGram :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hgram :
      rectGram A =
        fun i j : Fin m => ∑ row : Fin m, R row i * R row j := by
    calc
      rectGram A =
          rectGram
            (finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) R))) :=
        congrArg rectGram hA
      _ = fun i j : Fin m => ∑ row : Fin m, R row i * R row j :=
        higham21_eq21_5_qr_sne_gram_eq Q hQ R
  let RM : Matrix (Fin m) (Fin m) ℝ := R
  intro hdetR
  apply hdetGram
  calc
    Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) =
        Matrix.det
          ((fun i j : Fin m => ∑ row : Fin m, R row i * R row j) :
            Matrix (Fin m) (Fin m) ℝ) :=
      congrArg Matrix.det hgram
    _ = Matrix.det (RM.transpose * RM) := by
      congr 1
    _ = Matrix.det RM.transpose * Matrix.det RM :=
      Matrix.det_mul _ _
    _ = 0 := by simp [RM, Matrix.det_transpose, hdetR]

/-- The concrete source domain includes exactly the nonbreakdown needed to
    make the computed Householder top block nonsingular.  No claim is made
    that source rank alone preserves rank after rounding. -/
theorem higham21_eq21_1_computed_top_R_det_ne_zero_of_full_row_rank_domain
    {m k : ℕ} (fp : FPModel)
    (A : Fin m → Fin (m + k) → ℝ)
    (hdomain : Higham21QMethodFullRowRankComputedQRDomain m k fp A) :
    Matrix.det
      ((fun i j =>
        fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
          (Fin.castAdd k i) j) : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
  let Rtop : Fin m → Fin m → ℝ := fun i j =>
    fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)
      (Fin.castAdd k i) j
  have hupperTall :
      IsUpperTrapezoidal (m + k) m
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A)) :=
    fl_householderQRPanel_R_upper_trapezoidal fp (m + k) m
      (finiteTranspose A)
  have hupper : ∀ i j : Fin m, j.val < i.val → Rtop i j = 0 := by
    simpa [Rtop] using
      lsQRTallBlock_top_upper_of_upper_trapezoidal
        (fl_householderQRPanel_R fp (m + k) m (finiteTranspose A))
        hupperTall
  have hdiag : ∀ i : Fin m, Rtop i i ≠ 0 := by
    simpa [Rtop, Higham21QMethodTopBlockNonbreakdown,
      lsTheorem20_4ComputedQRNonbreakdown] using
      Higham21QMethodFullRowRankComputedQRDomain.nonbreakdown hdomain
  simpa [Rtop] using
    det_ne_zero_of_upper_triangular_diag_ne_zero m Rtop hupper hdiag

/-- Equations (21.1)-(21.3), core form: when `R` is nonsingular and
    `R^T y1 = b`, every solution, and only a solution, is
    `Q [y1; y2]` for an arbitrary free block `y2`. -/
theorem higham21_eq21_1_3_all_solutions_of_qr_R_det_ne_zero
    {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hdetR : Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b)
    (x : Fin (m + k) → ℝ) :
    rectMatMulVec
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R))) x = b ↔
      ∃ y2 : Fin k → ℝ,
        x = matMulVec (m + k) Q (Fin.append y1 y2) := by
  have hdetT :
      Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change
      Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdetR
  constructor
  · intro hx
    let y : Fin (m + k) → ℝ :=
      matMulVec (m + k) (matTranspose Q) x
    let z1 : Fin m → ℝ := fun i => y (Fin.castAdd k i)
    let z2 : Fin k → ℝ := fun i => y (Fin.natAdd m i)
    have hyAppend : Fin.append z1 z2 = y := by
      simpa [z1, z2] using
        higham21_finAppend_left_right (p := m) (q := k) y
    have hxRecover :
        matMulVec (m + k) Q (Fin.append z1 z2) = x := by
      rw [hyAppend]
      exact higham21_matMulVec_orthogonal_mul_transpose hQ x
    have hz1Solve :
        (fun j : Fin m => ∑ i : Fin m, R i j * z1 i) = b := by
      have hsystem := higham21_qr_transpose_system_eq Q hQ R z1 z2
      rw [← hsystem, hxRecover, hx]
    have hz1Eq : z1 = y1 :=
      (higham21_eq21_3_transpose_triangular_solution_unique_of_inverse
        R (nonsingInv m (matTranspose R)) b y1
        (isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT)
        hy1) z1 hz1Solve
    refine ⟨z2, ?_⟩
    calc
      x = matMulVec (m + k) Q (Fin.append z1 z2) := hxRecover.symm
      _ = matMulVec (m + k) Q (Fin.append y1 z2) := by rw [hz1Eq]
  · rintro ⟨y2, rfl⟩
    rw [higham21_qr_transpose_system_eq Q hQ R y1 y2, hy1]

/-- Source-matrix form of the arbitrary-`y2` parametrization under the exact
    QR certificate `A^T = Q [R;0]`. -/
theorem higham21_eq21_1_3_all_solutions_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b)
    (x : Fin (m + k) → ℝ) :
    rectMatMulVec A x = b ↔
      ∃ y2 : Fin k → ℝ,
        x = matMulVec (m + k) Q (Fin.append y1 y2) := by
  have hA :
      A = finiteTranspose
        (matMulRectLeft Q (lsQRTallBlock (k := k) R)) := by
    ext i j
    have hij := congrFun (congrFun hAT j) i
    simpa [finiteTranspose] using hij
  have hdetR :=
    higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
      A Q R hQ hAT hfull
  rw [hA]
  exact higham21_eq21_1_3_all_solutions_of_qr_R_det_ne_zero
    Q hQ R b y1 hdetR hy1 x

/-- The norm of `Q [y1;y2]` equals the zero-free-block norm exactly when
    `y2 = 0`.  This is the uniqueness part of the choice in (21.3). -/
theorem higham21_eq21_3_free_block_norm_eq_iff
    {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (y1 : Fin m → ℝ) (y2 : Fin k → ℝ) :
    vecNorm2 (matMulVec (m + k) Q (Fin.append y1 y2)) =
        vecNorm2
          (matMulVec (m + k) Q
            (Fin.append y1 (0 : Fin k → ℝ))) ↔
      y2 = 0 := by
  rw [vecNorm2_orthogonal Q (Fin.append y1 y2) hQ,
    vecNorm2_orthogonal Q (Fin.append y1 (0 : Fin k → ℝ)) hQ]
  constructor
  · intro hnorm
    have hsq :
        vecNorm2Sq (Fin.append y1 y2) =
          vecNorm2Sq (Fin.append y1 (0 : Fin k → ℝ)) := by
      calc
        vecNorm2Sq (Fin.append y1 y2) =
            vecNorm2 (Fin.append y1 y2) ^ 2 :=
          (vecNorm2_sq (Fin.append y1 y2)).symm
        _ = vecNorm2 (Fin.append y1 (0 : Fin k → ℝ)) ^ 2 := by rw [hnorm]
        _ = vecNorm2Sq (Fin.append y1 (0 : Fin k → ℝ)) :=
          vecNorm2_sq (Fin.append y1 (0 : Fin k → ℝ))
    have hzero : vecNorm2Sq (0 : Fin k → ℝ) = 0 := by
      simp [vecNorm2Sq]
    rw [lsVecNorm2Sq_append, lsVecNorm2Sq_append, hzero] at hsq
    have hy2sq : vecNorm2Sq y2 = 0 := by linarith
    have hy2normSq : vecNorm2 y2 ^ 2 = 0 := by
      rw [vecNorm2_sq]
      exact hy2sq
    have hy2norm : vecNorm2 y2 = 0 := sq_eq_zero_iff.mp hy2normSq
    exact funext ((vecNorm2_eq_zero_iff y2).mp hy2norm)
  · rintro rfl
    rfl

/-- Equation (21.3), core uniqueness form: the zero free block gives the
    unique minimum-2-norm solution in the complete QR parametrization. -/
theorem higham21_eq21_3_unique_min_norm_of_qr_R_det_ne_zero
    {m k : ℕ}
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hdetR : Matrix.det (R : Matrix (Fin m) (Fin m) ℝ) ≠ 0)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b)
    (x : Fin (m + k) → ℝ) :
    RectMinNormSolution m (m + k)
        (finiteTranspose
          (matMulRectLeft Q (lsQRTallBlock (k := k) R))) b x ↔
      x = matMulVec (m + k) Q
        (Fin.append y1 (0 : Fin k → ℝ)) := by
  constructor
  · intro hx
    obtain ⟨y2, hxParam⟩ :=
      (higham21_eq21_1_3_all_solutions_of_qr_R_det_ne_zero
        Q hQ R b y1 hdetR hy1 x).mp hx.system_eq
    have hzeroSolve :
        rectMatMulVec
            (finiteTranspose
              (matMulRectLeft Q (lsQRTallBlock (k := k) R)))
            (matMulVec (m + k) Q
              (Fin.append y1 (0 : Fin k → ℝ))) = b :=
      (higham21_eq21_1_3_all_solutions_of_qr_R_det_ne_zero
        Q hQ R b y1 hdetR hy1
          (matMulVec (m + k) Q
            (Fin.append y1 (0 : Fin k → ℝ)))).mpr ⟨0, rfl⟩
    have hle := hx.min_norm
      (matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)))
      hzeroSolve
    have hzeroLe :=
      higham21_eq21_3_q_factor_zero_free_block_min_norm Q hQ y1 y2
    have hnorm :
        vecNorm2 (matMulVec (m + k) Q (Fin.append y1 y2)) =
          vecNorm2
            (matMulVec (m + k) Q
              (Fin.append y1 (0 : Fin k → ℝ))) := by
      apply le_antisymm
      · simpa [hxParam] using hle
      · exact hzeroLe
    have hy2 : y2 = 0 :=
      (higham21_eq21_3_free_block_norm_eq_iff Q hQ y1 y2).mp hnorm
    calc
      x = matMulVec (m + k) Q (Fin.append y1 y2) := hxParam
      _ = matMulVec (m + k) Q
          (Fin.append y1 (0 : Fin k → ℝ)) := by rw [hy2]
  · rintro rfl
    exact higham21_eq21_3_q_method_min_norm_of_qr_R_det_ne_zero
      Q hQ R b y1 hdetR hy1

/-- Source-matrix form of the unique minimum-norm conclusion under
    `A^T = Q [R;0]` and full row rank. -/
theorem higham21_eq21_3_unique_min_norm_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b)
    (x : Fin (m + k) → ℝ) :
    RectMinNormSolution m (m + k) A b x ↔
      x = matMulVec (m + k) Q
        (Fin.append y1 (0 : Fin k → ℝ)) := by
  have hA :
      A = finiteTranspose
        (matMulRectLeft Q (lsQRTallBlock (k := k) R)) := by
    ext i j
    have hij := congrFun (congrFun hAT j) i
    simpa [finiteTranspose] using hij
  have hdetR :=
    higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
      A Q R hQ hAT hfull
  rw [hA]
  exact higham21_eq21_3_unique_min_norm_of_qr_R_det_ne_zero
    Q hQ R b y1 hdetR hy1 x

/-- Equation (21.4): the Q-method vector and the canonical Gram
    pseudoinverse action are the same vector under one exact QR/full-rank
    domain. -/
theorem higham21_eq21_4_q_method_eq_gram_pseudoinverse_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b y1 : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (hy1 : (fun j : Fin m => ∑ i : Fin m, R i j * y1 i) = b) :
    matMulVec (m + k) Q (Fin.append y1 (0 : Fin k → ℝ)) =
      rectMatMulVec (undetAplusOfGramNonsingInv A) b := by
  have hdetGram :
      Matrix.det (rectGram A : Matrix (Fin m) (Fin m) ℝ) ≠ 0 :=
    higham21_rectGram_det_ne_zero_of_transpose_full_col_rank A hfull
  have hcanonical :
      RectMinNormSolution m (m + k) A b
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b) :=
    higham21_eq21_4_rect_pseudoinverse_formula_min_norm_of_gram_det_ne_zero
      A b hdetGram
  have hunique :=
    (higham21_eq21_3_unique_min_norm_of_full_row_rank_exact_qr
      A Q R b y1 hQ hAT hfull hy1
        (rectMatMulVec (undetAplusOfGramNonsingInv A) b)).mp hcanonical
  exact hunique.symm

/-- Equations (21.1)-(21.3) with the printed coordinate
    `y1 = R^{-T} b` instantiated by the repository nonsingular inverse. -/
theorem higham21_eq21_1_3_all_solutions_inverse_coordinates_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (x : Fin (m + k) → ℝ) :
    rectMatMulVec A x = b ↔
      ∃ y2 : Fin k → ℝ,
        x = matMulVec (m + k) Q
          (Fin.append
            (matMulVec m (nonsingInv m (matTranspose R)) b) y2) := by
  have hdetR :=
    higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
      A Q R hQ hAT hfull
  have hdetT :
      Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change
      Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdetR
  have hInv :=
    isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT
  have hy1 :
      (fun j : Fin m =>
        ∑ i : Fin m,
          R i j * matMulVec m (nonsingInv m (matTranspose R)) b i) = b := by
    simpa [matMulVec, matTranspose] using
      matMulVec_of_isRightInverse
        (matTranspose R) (nonsingInv m (matTranspose R)) hInv.2 b
  exact higham21_eq21_1_3_all_solutions_of_full_row_rank_exact_qr
    A Q R b (matMulVec m (nonsingInv m (matTranspose R)) b)
      hQ hAT hfull hy1 x

/-- Equation (21.3) with `R^{-T}b` instantiated: this vector is the unique
    minimum-norm solution. -/
theorem higham21_eq21_3_inverse_coordinates_unique_min_norm_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m)
    (x : Fin (m + k) → ℝ) :
    RectMinNormSolution m (m + k) A b x ↔
      x = matMulVec (m + k) Q
        (Fin.append
          (matMulVec m (nonsingInv m (matTranspose R)) b)
          (0 : Fin k → ℝ)) := by
  have hdetR :=
    higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
      A Q R hQ hAT hfull
  have hdetT :
      Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change
      Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdetR
  have hInv :=
    isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT
  have hy1 :
      (fun j : Fin m =>
        ∑ i : Fin m,
          R i j * matMulVec m (nonsingInv m (matTranspose R)) b i) = b := by
    simpa [matMulVec, matTranspose] using
      matMulVec_of_isRightInverse
        (matTranspose R) (nonsingInv m (matTranspose R)) hInv.2 b
  exact higham21_eq21_3_unique_min_norm_of_full_row_rank_exact_qr
    A Q R b (matMulVec m (nonsingInv m (matTranspose R)) b)
      hQ hAT hfull hy1 x

/-- Equation (21.4) in the printed `R^{-T}b` form. -/
theorem higham21_eq21_4_inverse_coordinates_eq_gram_pseudoinverse_of_full_row_rank_exact_qr
    {m k : ℕ}
    (A : Fin m → Fin (m + k) → ℝ)
    (Q : Fin (m + k) → Fin (m + k) → ℝ)
    (R : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ)
    (hQ : IsOrthogonal (m + k) Q)
    (hAT : finiteTranspose A =
      matMulRectLeft Q (lsQRTallBlock (k := k) R))
    (hfull : lsRealRectColRank (finiteTranspose A) = m) :
    matMulVec (m + k) Q
        (Fin.append
          (matMulVec m (nonsingInv m (matTranspose R)) b)
          (0 : Fin k → ℝ)) =
      rectMatMulVec (undetAplusOfGramNonsingInv A) b := by
  have hdetR :=
    higham21_eq21_1_top_R_det_ne_zero_of_full_row_rank_exact_qr
      A Q R hQ hAT hfull
  have hdetT :
      Matrix.det (matTranspose R : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
    change
      Matrix.det (Matrix.transpose (R : Matrix (Fin m) (Fin m) ℝ)) ≠ 0
    simpa [Matrix.det_transpose] using hdetR
  have hInv :=
    isInverse_nonsingInv_of_det_ne_zero m (matTranspose R) hdetT
  have hy1 :
      (fun j : Fin m =>
        ∑ i : Fin m,
          R i j * matMulVec m (nonsingInv m (matTranspose R)) b i) = b := by
    simpa [matMulVec, matTranspose] using
      matMulVec_of_isRightInverse
        (matTranspose R) (nonsingInv m (matTranspose R)) hInv.2 b
  exact
    higham21_eq21_4_q_method_eq_gram_pseudoinverse_of_full_row_rank_exact_qr
      A Q R b (matMulVec m (nonsingInv m (matTranspose R)) b)
        hQ hAT hfull hy1

end NumStability
