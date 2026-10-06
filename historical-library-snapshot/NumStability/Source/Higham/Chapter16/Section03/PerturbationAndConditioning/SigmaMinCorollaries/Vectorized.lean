import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.FirstOrder
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.Separation
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SigmaMinBounds.Vectorized
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.SingularValue
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredLyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Conditioning.StructuredSylvester
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Basic
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Lyapunov
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Rectangular
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.SchurCoordinates
import NumStability.Algorithms.MatrixEquations.Sylvester.Equation.Vectorization
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixSpectral
import NumStability.Source.Higham.Chapter16.Foundations.Core
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.Equation27
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.Lyapunov
import NumStability.Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.StructuredSylvester

/-!
# Source.Higham.Chapter16.Section03.PerturbationAndConditioning.SigmaMinCorollaries.Vectorized

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Algorithms/Sylvester/Higham16VecNorm.lean
--
-- Vec/Frobenius norm bridges for Higham, Accuracy and Stability of
-- Numerical Algorithms, 2nd ed., Chapter 16.







namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius
































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the source `SepLowerBound` trivial-kernel route. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_eq_zero_iff_of_sepLowerBound :=
  sylvesterVecCoeff_mulVec_eq_zero_iff_of_sepLowerBound

/-- Higham, 2nd ed., Chapter 16.3, equation (16.26): source-numbered
    alias for the positive exact-infimum trivial-kernel route. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_eq_zero_iff_of_pos_le_sylvesterSepInf :=
  sylvesterVecCoeff_mulVec_eq_zero_iff_of_pos_le_sylvesterSepInf





















































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equation (16.26):
    source-numbered form of the operator-sigma-min trivial-kernel route for the
    vectorized Sylvester coefficient. -/
theorem H16_eq16_26_sylvesterVecCoeff_mulVec_eq_zero_iff_of_operator_sigmaMin
    (n : Nat) (A B : Fin n -> Fin n -> Real) (sigma : Real)
    (hsigma : 0 < sigma)
    (hSigmaMin : forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y))
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_operator_sigmaMin
      n A B sigma hsigma hSigmaMin x































/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for operator-sigma-min vectorized coefficient
    injectivity. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_injective_of_operator_sigmaMin :=
  sylvesterVecCoeff_mulVec_injective_of_operator_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26):
    source-numbered alias for operator-sigma-min vectorized coefficient
    surjectivity. -/
alias H16_eq16_26_sylvesterVecCoeff_mulVec_surjective_of_operator_sigmaMin :=
  sylvesterVecCoeff_mulVec_surjective_of_operator_sigmaMin























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.1, equations (16.3)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    a uniform lower bound on the diagonal coordinate gaps `|a_i - b_j|`
    gives the same Frobenius lower bound for the original Sylvester operator
    after the supplied orthogonal coordinate transformations. -/
theorem sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (sylvesterOp n A B Y) := by
  intro Y
  let Yc : Fin n -> Fin n -> Real :=
    rectMatMul (matTranspose U) (rectMatMul Y V)
  have hYnorm : frobNorm Yc = frobNorm Y := by
    dsimp [Yc]
    calc
      frobNorm (rectMatMul (matTranspose U) (rectMatMul Y V))
          = frobNorm (rectMatMul Y V) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_left (matTranspose U)
                (rectMatMul Y V) hU.transpose)
      _ = frobNorm Y := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_right Y V hV)
  have hYexpand :
      rectMatMul U (rectMatMul Yc (matTranspose V)) = Y := by
    dsimp [Yc]
    exact rectMatMul_schur_coords_expand U V Y hU hV
  have htrans :
      sylvesterOpRect n n A B Y =
        rectMatMul U
          (rectMatMul
            (sylvesterOpRect n n (Matrix.diagonal a)
              (Matrix.diagonal b) Yc)
            (matTranspose V)) := by
    have h :=
      sylvester_schur_transform_identity n n
        U (Matrix.diagonal a) A V (Matrix.diagonal b) B Yc
        hU hV hA hB
    rwa [hYexpand] at h
  have hOut :
      frobNorm (sylvesterOp n A B Y) =
        frobNorm (sylvesterOp n (Matrix.diagonal a)
          (Matrix.diagonal b) Yc) := by
    rw [<- sylvesterOpRect_square_eq_sylvesterOp n A B Y, htrans]
    calc
      frobNorm
          (rectMatMul U
            (rectMatMul
              (sylvesterOpRect n n (Matrix.diagonal a)
                (Matrix.diagonal b) Yc)
              (matTranspose V)))
          = frobNorm
              (rectMatMul
                (sylvesterOpRect n n (Matrix.diagonal a)
                  (Matrix.diagonal b) Yc)
                (matTranspose V)) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_left U
                (rectMatMul
                  (sylvesterOpRect n n (Matrix.diagonal a)
                    (Matrix.diagonal b) Yc)
                  (matTranspose V)) hU)
      _ = frobNorm
            (sylvesterOpRect n n (Matrix.diagonal a)
              (Matrix.diagonal b) Yc) := by
            simpa [rectMatMul, matMul] using
              (frobNorm_orthogonal_right
                (sylvesterOpRect n n (Matrix.diagonal a)
                  (Matrix.diagonal b) Yc)
                (matTranspose V) hV.transpose)
      _ = frobNorm (sylvesterOp n (Matrix.diagonal a)
            (Matrix.diagonal b) Yc) := by
            rw [sylvesterOpRect_square_eq_sylvesterOp]
  have hdiag :=
    sylvesterOp_sigmaMin_diagonal_of_entrywise_abs_ge n
      a b sigma hsigma hgap Yc
  calc
    sigma * frobNorm Y = sigma * frobNorm Yc := by
      rw [hYnorm]
    _ <= frobNorm (sylvesterOp n (Matrix.diagonal a)
          (Matrix.diagonal b) Yc) := hdiag
    _ = frobNorm (sylvesterOp n A B Y) := hOut.symm

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    the corresponding product-index vec/Kronecker coefficient inherits the
    same sigma lower bound from the Schur-coordinate diagonal gap. -/
theorem sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  intro x
  let Y : Fin n -> Fin n -> Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have h :=
    sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap Y
  rw [<- hvecY]
  rw [sylvesterVecCoeff_mulVec_vec n n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y,
    sylvesterOpRect_square_eq_sylvesterOp n A B Y,
    finiteVecNorm2_vec_eq_frobNorm n n (sylvesterOp n A B Y)]
  exact h

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    a supplied Schur-coordinate gap gives a finite Gram-eigenvalue lower
    bound for the original vec/Kronecker Sylvester coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (sylvesterVecCoeff n n A B) (le_of_lt hsigma)
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    for supplied orthogonal diagonal Schur coordinates, spectral-coordinate
    exclusion `a_i != b_j` supplies some positive sigma-min lower bound for the
    original vec/Kronecker Sylvester coefficient. -/
theorem exists_sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧
      forall x : Prod (Fin n) (Fin n) -> Real,
        sigma * finiteVecNorm2 x <=
          finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x) := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3):
    for supplied orthogonal diagonal Schur coordinates, spectral-coordinate
    exclusion `a_i != b_j` supplies a positive Gram-eigenvalue lower bound for
    the original vec/Kronecker Sylvester coefficient. -/
theorem exists_sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧
      forall p : Prod (Fin n) (Fin n),
        sigma ^ 2 <= finiteHermitianEigenvalues
          (finiteMatrixGram (sylvesterVecCoeff n n A B))
          (isSymmetricFiniteMatrix_finiteMatrixGram
            (sylvesterVecCoeff n n A B)) p := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvesterVecCoeff_schurDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case: a positive coordinate gap makes
    the original square vec/Kronecker Sylvester coefficient nonsingular. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  exact
    sylvesterVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n
      A B hsigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    pairwise spectral-coordinate exclusion makes the original square
    vec/Kronecker Sylvester coefficient nonsingular. -/
theorem sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    (sylvesterVecCoeff n n A B).det ≠ 0 := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  exact
    sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the exact trivial-kernel statement for
    the original vec/Kronecker Sylvester coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_eq_zero_iff_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (x : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B) x = 0 ↔ x = 0 := by
  exact
    sylvesterVecCoeff_mulVec_eq_zero_iff_of_det_ne_zero n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      x

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion makes the original vectorized coefficient
    action injective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_injective_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Function.Injective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_injective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion makes the original vectorized coefficient
    action surjective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_surjective_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Function.Surjective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_surjective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion makes the original vectorized coefficient
    solve bijective. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_bijective_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    Function.Bijective (Matrix.mulVec (sylvesterVecCoeff n n A B)) := by
  exact
    finiteMatrix_mulVec_bijective_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives a unique vectorized coefficient
    solution for every right-hand side. -/
theorem existsUnique_sylvesterVecCoeff_schurDiagonal_mulVec_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c := by
  exact
    existsUnique_finiteMatrix_mulVec_of_det_ne_zero
      (sylvesterVecCoeff n n A B)
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      c

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the right nonsingular-inverse action
    for the original vectorized coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_mulVec_nonsingInv_mulVec_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (rhs : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)
        (Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs) =
      rhs := by
  exact
    sylvesterVecCoeff_mulVec_nonsingInv_mulVec_of_det_ne_zero n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      rhs

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the left nonsingular-inverse action
    for the original vectorized coefficient. -/
theorem sylvesterVecCoeff_schurDiagonal_nonsingInv_mulVec_mulVec_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (z : Prod (Fin n) (Fin n) -> Real) :
    Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹
        (Matrix.mulVec (sylvesterVecCoeff n n A B) z) =
      z := by
  exact
    sylvesterVecCoeff_nonsingInv_mulVec_mulVec_of_det_ne_zero n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      z

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion identifies every exact vectorized coefficient
    solution with the nonsingular-inverse vector. -/
theorem sylvesterVecCoeff_schurDiagonal_eq_nonsingInv_mulVec_of_mulVec_eq_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    {z rhs : Prod (Fin n) (Fin n) -> Real}
    (hz : Matrix.mulVec (sylvesterVecCoeff n n A B) z = rhs) :
    z = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ rhs := by
  exact
    sylvesterVecCoeff_eq_nonsingInv_mulVec_of_mulVec_eq_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      hz

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.5), supplied
    orthogonal diagonal Schur-coordinate case:
    spectral-coordinate exclusion gives the unique vectorized coefficient
    solution together with its nonsingular-inverse formula. -/
theorem existsUnique_sylvesterVecCoeff_schurDiagonal_nonsingInv_mulVec_solution_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j)
    (c : Prod (Fin n) (Fin n) -> Real) :
    ∃! x : Prod (Fin n) (Fin n) -> Real,
      Matrix.mulVec (sylvesterVecCoeff n n A B) x = c ∧
        x = Matrix.mulVec (sylvesterVecCoeff n n A B)⁻¹ c := by
  exact
    existsUnique_sylvesterVecCoeff_nonsingInv_mulVec_solution_of_det_ne_zero
      n A B
      (sylvesterVecCoeff_schurDiagonal_det_ne_zero_of_entrywise_ne n
        U A V B a b hn hU hV hA hB hsep)
      c

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    a uniform Schur-coordinate gap gives a `SepLowerBound` certificate for
    the original Sylvester operator. -/
theorem SepLowerBound_schurDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|) :
    SepLowerBound n A B sigma := by
  exact
    sepLowerBound_of_sylvesterOp_sigmaMin n A B sigma hsigma
      (sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    a uniform Schur-coordinate gap is below the exact infimum model of
    `sep(A,B)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hne : (sylvesterSepRatios n A B).Nonempty) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A B sigma
      (SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26), supplied orthogonal
    diagonal Schur-coordinate case:
    in positive dimension, a uniform Schur-coordinate gap is below the exact
    infimum model of `sep(A,B)`. -/
theorem sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n A B := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A B sigma
      (SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hn

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied Schur-diagonal uniform-gap `SepLowerBound`
    certificate. -/
alias H16_eq16_26_SepLowerBound_schurDiagonal_of_entrywise_abs_ge :=
  SepLowerBound_schurDiagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied Schur-diagonal exact-infimum lower-bound route from
    nonempty feasible ratios. -/
alias H16_eq16_26_sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge :=
  sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the positive-dimensional supplied Schur-diagonal exact-infimum
    lower-bound route. -/
alias H16_eq16_26_sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim :=
  sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), and equation
    (16.26): for supplied orthogonal diagonal Schur coordinates, pairwise
    spectral-coordinate exclusion gives some positive `SepLowerBound`
    certificate for the original Sylvester operator. -/
theorem exists_SepLowerBound_schurDiagonal_of_entrywise_ne (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, SepLowerBound n A B sigma := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  exact
    ⟨sigma, SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
      U A V B a b sigma hU hV hA hB hsigma hgap⟩

/-- Higham, 2nd ed., Chapter 16.1, equations (16.2)-(16.3), and equation
    (16.26): for supplied orthogonal diagonal Schur coordinates, pairwise
    spectral-coordinate exclusion gives a positive lower bound on the exact
    `sep(A,B)` infimum model. -/
theorem exists_sylvesterSepInf_schurDiagonal_pos_lower_bound_of_entrywise_ne
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (hn : 0 < n)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hsep : forall i j, a i ≠ b j) :
    ∃ sigma : Real, 0 < sigma ∧ sigma <= sylvesterSepInf n A B := by
  obtain ⟨sigma, hsigma, hgap⟩ :=
    exists_pos_sylvesterDiagonalGap_of_entrywise_ne n a b hn hsep
  refine ⟨sigma, hsigma, ?_⟩
  exact
    sylvesterSepInf_schurDiagonal_ge_of_entrywise_abs_ge_of_pos_dim n
      U A V B a b sigma hU hV hA hB hsigma hgap hn

































/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    a uniform spectral-coordinate sum gap gives a `SepLowerBound` certificate
    for the Sylvester special case `sep(A,-A^T)`. -/
theorem SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    SepLowerBound n A (fun i j => -matTranspose A i j) sigma := by
  have hnegAT :
      (fun i j => -matTranspose A i j) =
        rectMatMul U
          (rectMatMul (Matrix.diagonal (fun i : Fin n => -a i))
            (matTranspose U)) := by
    rw [hA]
    ext i j
    simp [rectMatMul, matTranspose, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hgapSylv :
      forall i j, sigma <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hgap i j
  exact
    SepLowerBound_schurDiagonal_of_entrywise_abs_ge n
      U A U (fun i j => -matTranspose A i j)
      a (fun i : Fin n => -a i) sigma hU hU hA hnegAT
      hsigma hgapSylv

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    the spectral-coordinate sum gap is below the exact infimum model of
    `sep(A,-A^T)` whenever the feasible ratio set is nonempty. -/
theorem sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hne : (sylvesterSepRatios n A
      (fun i j => -matTranspose A i j)).Nonempty) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_nonempty n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    supplied orthogonal spectral-coordinate Lyapunov case:
    in positive dimension, the spectral-coordinate sum gap is below the exact
    infimum model of `sep(A,-A^T)`. -/
theorem sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hn : 0 < n) :
    sigma <= sylvesterSepInf n A (fun i j => -matTranspose A i j) := by
  exact
    SepLowerBound_le_sylvesterSepInf_of_pos_dim n A
      (fun i j => -matTranspose A i j) sigma
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hn

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied spectral-coordinate Lyapunov `sep(A,-A^T)`
    lower-bound certificate. -/
alias H16_eq16_26_SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge :=
  SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the supplied spectral-coordinate Lyapunov exact-infimum
    lower-bound route from a nonempty feasible ratio set. -/
alias H16_eq16_26_sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge :=
  sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.4, equation (16.26): source-numbered
    alias for the positive-dimensional supplied spectral-coordinate Lyapunov
    exact-infimum lower-bound route. -/
alias H16_eq16_26_sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim :=
  sylvesterSepInf_lyapunovSpectralDiagonal_ge_of_entrywise_abs_ge_of_pos_dim



























































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    if `A = U diag(a) U^T`, then a uniform lower bound on
    `|a_i + a_j|` gives the same Frobenius lower bound for the original
    Lyapunov operator. -/
theorem lyapunovOp_sigmaMin_spectralDiagonal_of_entrywise_abs_ge (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall Y : Fin n -> Fin n -> Real,
      sigma * frobNorm Y <= frobNorm (lyapunovOp n A Y) := by
  have hnegAT :
      (fun i j => -matTranspose A i j) =
        rectMatMul U
          (rectMatMul (Matrix.diagonal (fun i : Fin n => -a i))
            (matTranspose U)) := by
    rw [hA]
    ext i j
    simp [rectMatMul, matTranspose, Matrix.diagonal]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  have hgapSylv :
      forall i j, sigma <= |a i - (fun k : Fin n => -a k) j| := by
    intro i j
    simpa [sub_eq_add_neg] using hgap i j
  intro Y
  have h :=
    sylvesterOp_sigmaMin_schurDiagonal_of_entrywise_abs_ge n
      U A U (fun i j => -matTranspose A i j)
      a (fun i : Fin n => -a i) sigma hU hU hA hnegAT
      hsigma hgapSylv Y
  rwa [<- lyapunovOp_eq_sylvesterOp n A Y] at h

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    the original-coordinate Lyapunov vec/Kronecker coefficient inherits the
    same sigma lower bound from the spectral-coordinate diagonal sums. -/
theorem lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x) := by
  intro x
  let Y : Matrix (Fin n) (Fin n) Real := fun i j => x (j, i)
  have hvecY : Matrix.vec Y = x := by
    ext p
    rfl
  have hOp :=
    lyapunovOp_sigmaMin_spectralDiagonal_of_entrywise_abs_ge n
      U A a sigma hU hA hsigma hgap Y
  let Amat : Matrix (Fin n) (Fin n) Real := A
  let Ymat : Matrix (Fin n) (Fin n) Real := Y
  have hLY :
      Amat * Ymat + Ymat * Matrix.transpose Amat = lyapunovOp n A Y := by
    ext i j
    simp [Amat, Ymat, Y, lyapunovOp, matMul, matTranspose, Matrix.mul_apply]
  rw [<- hvecY]
  rw [lyapunovVecCoeff_mulVec_vec n A Y,
    finiteVecNorm2_vec_eq_frobNorm n n Y, hLY,
    finiteVecNorm2_vec_eq_frobNorm n n (lyapunovOp n A Y)]
  exact hOp

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    a spectral-coordinate gap gives a finite Gram-eigenvalue lower bound for
    the original Lyapunov vec/Kronecker coefficient. -/
theorem lyapunovVecCoeff_spectralDiagonal_gram_eigenvalues_ge_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    forall p : Prod (Fin n) (Fin n),
      sigma ^ 2 <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p := by
  exact
    finiteMatrixGram_eigenvalues_ge_of_sigmaMin_lower_bound
      (lyapunovVecCoeff n A) (le_of_lt hsigma)
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case: a positive spectral-coordinate sum gap makes the
    original square Lyapunov vec/Kronecker coefficient nonsingular. -/
theorem lyapunovVecCoeff_spectralDiagonal_det_ne_zero_of_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|) :
    (lyapunovVecCoeff n A).det ≠ 0 := by
  exact
    lyapunovVecCoeff_det_ne_zero_of_vecCoeff_sigmaMin n
      A hsigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)












































































































































/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a positive
    lower bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterOp_sigmaMin_of_vecCoeff_sigmaMin n A B sigma hCoeff)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a concrete
    left inverse and operator-2 radius for the printed Sylvester
    vec/Kronecker coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma M * eps := by
  have hPsi :=
    sylvesterPsi_of_vecCoeff_left_inverse_finiteOpNorm2Le_isPsiFirstOrderBound
      n A B X alpha beta gamma M Pinv halpha hbeta hgamma hM hX hLeft hPinv
  have hPsi_nonneg :
      0 <= sylvesterPsi_of_inverseOpBound n X alpha beta gamma M := by
    unfold sylvesterPsi_of_inverseOpBound
    have hsum : 0 <= alpha + beta :=
      add_nonneg (le_of_lt halpha) (le_of_lt hbeta)
    have hprod : 0 <= (alpha + beta) * frobNorm X :=
      mul_nonneg hsum (le_of_lt hX)
    have hnum : 0 <= (alpha + beta) * frobNorm X + gamma :=
      add_nonneg hprod (le_of_lt hgamma)
    exact div_nonneg (mul_nonneg hM hnum) (le_of_lt hX)
  exact
    sylvester_relative_first_order_bound_of_psi n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
      (sylvesterPsi_of_inverseOpBound n X alpha beta gamma M) eps
      hPsi hX hPsi_nonneg halpha hbeta hgamma heps
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-shaped first-order relative perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem H16_eq16_24_structured_condition_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma lam eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma
      (Real.sqrt lam) eps halpha hbeta hgamma
      (Real.sqrt_pos.mpr hlam) heps hX
      (sylvesterVecCoeff_sigmaMin_of_gram_eigenvalues n A B
        (le_of_lt hlam) hEig)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    relative Sylvester first-order perturbation bound from a positive lower
    bound on the concrete Kronecker/vectorized Sylvester coefficient. -/
theorem sylvester_relative_first_order_bound_of_vecCoeff_sigmaMin (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hCoeff
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    relative Sylvester first-order perturbation bound from a concrete left
    inverse and operator-2 radius for the printed vec/Kronecker coefficient. -/
theorem sylvester_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma M * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma M eps Pinv
      halpha hbeta hgamma hM heps hX hLeft hPinv
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    relative Sylvester first-order perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Sylvester
    coefficient. -/
theorem sylvester_relative_first_order_bound_of_vecCoeff_gram_eigenvalues
    (n : Nat)
    (A B X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma lam eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_gram_eigenvalues n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma lam eps
      halpha hbeta hgamma hlam heps hX hEig
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24):
    source-numbered aliases for finite Gram-eigenvalue Sylvester
    first-order condition wrappers. -/
alias H16_eq16_23_sylvester_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  sylvester_first_order_bound_of_vecCoeff_gram_eigenvalues

alias H16_eq16_24_sylvester_relative_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  sylvester_relative_first_order_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    diagonal case: source-shaped first-order relative perturbation bound from
    the concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_24_structured_condition_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) (Matrix.diagonal b)
      X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a b sigma (le_of_lt hsigma) hgap)
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    source-shaped first-order relative perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_24_structured_condition_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hDeltaA hDeltaB hDeltaC hLin





























/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    diagonal case: relative Sylvester first-order perturbation bound from the
    concrete diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_diagonal_of_vecCoeff_entrywise_abs_ge n
      a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      halpha hbeta hgamma hsigma heps hX hgap
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX <=
      sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) *
        frobNorm X *
        sylvesterScaledPerturbationTripleNorm n DeltaA DeltaB DeltaC
          alpha beta gamma := by
  exact
    sylvester_first_order_bound_of_vecCoeff_sigmaMin n
      A B X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma
      halpha hbeta hgamma hsigma hX
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hsigma hgap)
      hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.23)-(16.24),
    supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester first-order perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X DeltaA DeltaB DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha beta gamma sigma eps : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (halpha : 0 < alpha) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i - b j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaB : frobNorm DeltaB <= eps * beta)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A B DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j + matMul n X DeltaB i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 3 *
        sylvesterPsi_of_inverseOpBound n X alpha beta gamma (1 / sigma) * eps := by
  exact
    H16_eq16_24_structured_condition_schurDiagonal_of_vecCoeff_entrywise_abs_ge n
      U A V B a b X DeltaA DeltaB DeltaC DeltaX alpha beta gamma sigma eps
      hU hV hA hB halpha hbeta hgamma hsigma heps hX hgap
      hDeltaA hDeltaB hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23):
    source-numbered alias for the concrete Sylvester vec/Kronecker sigma-min
    first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_of_vecCoeff_sigmaMin :=
  sylvester_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23):
    source-numbered alias for the concrete Sylvester vec/Kronecker
    left-inverse first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    sigma-min first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_of_vecCoeff_sigmaMin :=
  sylvester_relative_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24):
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    left-inverse first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  sylvester_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23), diagonal case:
    source-numbered alias for the concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24), diagonal case:
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.23), supplied orthogonal
    Schur-diagonal case:
    source-numbered alias for the concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_23_sylvester_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.24), supplied orthogonal
    Schur-diagonal case:
    source-numbered alias for the relative concrete Sylvester vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_24_sylvester_relative_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge :=
  sylvester_relative_first_order_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge




































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0)) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester perturbation bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hdX_ne : Not (frobNormSq dX = 0))
    (hX_ne : Not (frobNorm X = 0))
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hdX_ne hX_ne hX_pos



























































/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    total supplied orthogonal diagonal Schur-coordinate case:
    Frobenius first-order Sylvester perturbation bound from the concrete
    Schur-diagonal vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.25)-(16.26),
    total supplied orthogonal diagonal Schur-coordinate case:
    relative Sylvester perturbation bound from the concrete Schur-diagonal
    vec/Kronecker coefficient lower-bound certificate. -/
theorem sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma
      (sylvesterVecCoeff_schurDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A V B a b sigma hU hV hA hB hSigma hgap)
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from a positive lower bound on the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma hCoeff
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative Sylvester perturbation bound
    from a positive lower bound on the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (sylvesterVecCoeff n n A B) x))
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_sigmaMin_total n
      A B X dA dB dC dX sigma hSigma hCoeff
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from a concrete left inverse of the printed vec/Kronecker coefficient. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      M * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
      n A B X dA dB dC dX M Pinv hM hLeft hPinv
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative Sylvester perturbation bound
    from a concrete left inverse of the printed vec/Kronecker coefficient. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (M : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (hM : 0 < M)
    (hLeft : Pinv * sylvesterVecCoeff n n A B = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (1 / M) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total
      n A B X dA dB dC dX M Pinv hM hLeft hPinv
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from a Gram-eigenvalue certificate for the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues_total
    (n : Nat)
    (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / Real.sqrt lam) *
        ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_of_vecCoeff_gram_eigenvalues_total n
      A B X dA dB dC dX lam hLam hEig
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25):
    source-numbered alias for the total relative Sylvester perturbation bound
    from a Gram-eigenvalue certificate for the concrete vectorized coefficient. -/
theorem H16_eq16_25_sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues_total
    (n : Nat) (A B X dA dB dC dX : Fin n -> Fin n -> Real)
    (lam : Real) (hLam : 0 < lam)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (sylvesterVecCoeff n n A B))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (sylvesterVecCoeff n n A B)) p)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma (Real.sqrt lam) * eps := by
  exact
    sylvester_relative_perturbation_of_vecCoeff_gram_eigenvalues_total n
      A B X dA dB dC dX lam hLam hEig
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), diagonal case:
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from the diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total
      n a b X dA dB dC dX sigma hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), diagonal case:
    source-numbered alias for the total relative Sylvester perturbation bound
    from the diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real) (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n (Matrix.diagonal a) (Matrix.diagonal b) dX i j =
        dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n (Matrix.diagonal a) (Matrix.diagonal b)
        X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total
      n a b X dA dB dC dX sigma hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), supplied orthogonal
    diagonal Schur-coordinate case:
    source-numbered alias for the total Frobenius Sylvester perturbation bound
    from the Schur-diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j) :
    frobNorm dX <=
      (1 / sigma) * ((alpha + beta) * frobNorm X + gamma) * eps := by
  exact
    sylvester_perturbation_bound_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
      n U A V B a b X dA dB dC dX sigma hU hV hA hB hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.25), supplied orthogonal
    diagonal Schur-coordinate case:
    source-numbered alias for the total relative Sylvester perturbation bound
    from the Schur-diagonal concrete coefficient certificate. -/
theorem H16_eq16_25_sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A V B : Fin n -> Fin n -> Real) (a b : Fin n -> Real)
    (X dA dB dC dX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U) (hV : IsOrthogonal n V)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hB : B = rectMatMul V (rectMatMul (Matrix.diagonal b) (matTranspose V)))
    (hSigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i - b j|)
    (alpha beta gamma eps : Real)
    (hAlpha : 0 <= alpha) (hBeta : 0 <= beta)
    (hGamma : 0 <= gamma) (hEps : 0 <= eps)
    (hdA : frobNorm dA <= eps * alpha)
    (hdB : frobNorm dB <= eps * beta)
    (hdC : frobNorm dC <= eps * gamma)
    (hLin : forall i j, sylvesterOp n A B dX i j =
      dC i j - matMul n dA X i j + matMul n X dB i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm dX / frobNorm X <=
      condSylvester n A B X alpha beta gamma sigma * eps := by
  exact
    sylvester_relative_perturbation_schurDiagonal_of_vecCoeff_entrywise_abs_ge_total
      n U A V B a b X dA dB dC dX sigma hU hV hA hB hSigma hgap
      alpha beta gamma eps hAlpha hBeta hGamma hEps
      hdA hdB hdC hLin hX_pos





























































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin (n : Nat)
    (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovOp_sigmaMin_of_vecCoeff_sigmaMin n A sigma hCoeff)
      hDeltaA hDeltaC hLin

























/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    relative Lyapunov first-order perturbation bound from a positive lower
    bound on the concrete vectorized Lyapunov coefficient. -/
theorem lyapunov_relative_first_order_bound_of_vecCoeff_sigmaMin
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hCoeff : forall x : Prod (Fin n) (Fin n) -> Real,
      sigma * finiteVecNorm2 x <=
        finiteVecNorm2 (Matrix.mulVec (lyapunovVecCoeff n A) x))
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hCoeff
      hDeltaA hDeltaC hLin
















































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the concrete Lyapunov vec/Kronecker sigma-min
    first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_vecCoeff_sigmaMin :=
  lyapunov_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    sigma-min first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_of_vecCoeff_sigmaMin :=
  lyapunov_relative_first_order_bound_of_vecCoeff_sigmaMin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the concrete Lyapunov vec/Kronecker left-inverse
    first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    left-inverse first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le :=
  lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-numbered aliases for finite Gram-eigenvalue Lyapunov
    first-order condition wrappers. -/
alias H16_eq16_27_lyapunov_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  lyapunov_first_order_bound_of_vecCoeff_gram_eigenvalues

alias H16_eq16_27_lyapunov_relative_first_order_bound_of_vecCoeff_gram_eigenvalues :=
  lyapunov_relative_first_order_bound_of_vecCoeff_gram_eigenvalues

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a concrete
    left inverse and operator-2 radius for the printed Lyapunov
    vec/Kronecker coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_left_inverse_finiteOpNorm2Le
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma M eps : Real)
    (Pinv : Matrix (Prod (Fin n) (Fin n)) (Prod (Fin n) (Fin n)) Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hM : 0 <= M) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hLeft : Pinv * lyapunovVecCoeff n A = 1)
    (hPinv : finiteOpNorm2Le Pinv M)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma M * eps := by
  exact
    lyapunov_relative_first_order_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le
      n A X DeltaA DeltaC DeltaX alpha gamma M eps Pinv
      halpha hgamma hM heps hX hLeft hPinv
      hDeltaA hDeltaC hLin





































































































































































































































































































































/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total Lyapunov perturbation endpoint from a
    concrete vec-coefficient sigma-min lower bound. -/
alias H16_eq16_27_lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total :=
  lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative Lyapunov perturbation endpoint
    from a concrete vec-coefficient sigma-min lower bound. -/
alias H16_eq16_27_lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total :=
  lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total Lyapunov perturbation endpoint from a
    concrete left inverse and finite operator-2 bound. -/
alias H16_eq16_27_lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total :=
  lyapunov_perturbation_bound_of_vecCoeff_left_inverse_finiteOpNorm2Le_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative Lyapunov perturbation endpoint
    from a concrete left inverse and finite operator-2 bound. -/
alias H16_eq16_27_lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total :=
  lyapunov_relative_perturbation_of_vecCoeff_left_inverse_finiteOpNorm2Le_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total Lyapunov perturbation endpoint from a
    finite Gram-eigenvalue lower-bound certificate. -/
alias H16_eq16_27_lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues_total :=
  lyapunov_perturbation_bound_of_vecCoeff_gram_eigenvalues_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative Lyapunov perturbation endpoint
    from a finite Gram-eigenvalue lower-bound certificate. -/
alias H16_eq16_27_lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues_total :=
  lyapunov_relative_perturbation_of_vecCoeff_gram_eigenvalues_total




























































/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total diagonal Lyapunov perturbation endpoint
    from concrete pair-sum gap data. -/
alias H16_eq16_27_lyapunov_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_perturbation_bound_diagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative diagonal Lyapunov perturbation
    endpoint from concrete pair-sum gap data. -/
alias H16_eq16_27_lyapunov_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_relative_perturbation_diagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    total supplied orthogonal spectral-coordinate case:
    Frobenius Lyapunov perturbation bound from the concrete spectral-diagonal
    Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_perturbation_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j) :
    frobNorm DeltaX <=
      (1 / sigma) * (2 * alpha * frobNorm X + gamma) * eps := by
  exact
    lyapunov_perturbation_bound_of_vecCoeff_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27),
    total supplied orthogonal spectral-coordinate case:
    relative Lyapunov perturbation bound from the concrete spectral-diagonal
    Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_perturbation_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (hsigma : 0 < sigma)
    (hgap : forall i j, sigma <= |a i + a j|)
    (alpha gamma eps : Real)
    (halpha : 0 <= alpha) (hgamma : 0 <= gamma) (heps : 0 <= eps)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      sylvesterOp n A (fun i' j' => -matTranspose A i' j') DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j +
          matMul n X (fun i' j' => -matTranspose DeltaA i' j') i j)
    (hX_pos : 0 < frobNorm X) :
    frobNorm DeltaX / frobNorm X <=
      condSylvester n A (fun i j => -matTranspose A i j) X
        alpha alpha gamma sigma * eps := by
  exact
    lyapunov_relative_perturbation_of_vecCoeff_sigmaMin_total n
      A X DeltaA DeltaC DeltaX sigma hsigma
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      alpha gamma eps halpha hgamma heps
      hDeltaA hDeltaC hLin hX_pos

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total supplied spectral-coordinate
    Lyapunov perturbation endpoint. -/
alias H16_eq16_27_lyapunov_perturbation_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_perturbation_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equations (16.26)-(16.27):
    source-numbered alias for the total relative supplied spectral-coordinate
    Lyapunov perturbation endpoint. -/
alias H16_eq16_27_lyapunov_relative_perturbation_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total :=
  lyapunov_relative_perturbation_spectralDiagonal_of_vecCoeff_entrywise_abs_ge_total

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27):
    source-shaped Lyapunov first-order perturbation bound from a finite
    Gram-eigenvalue lower bound for the concrete vectorized Lyapunov
    coefficient. -/
theorem H16_eq16_27_lyapunov_condition_of_vecCoeff_gram_eigenvalues
    (n : Nat) (A X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma lam eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hlam : 0 < lam) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hEig : forall p : Prod (Fin n) (Fin n),
      lam <= finiteHermitianEigenvalues
        (finiteMatrixGram (lyapunovVecCoeff n A))
        (isSymmetricFiniteMatrix_finiteMatrixGram
          (lyapunovVecCoeff n A)) p)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma
          (1 / Real.sqrt lam) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma (Real.sqrt lam) eps
      halpha hgamma (Real.sqrt_pos.mpr hlam) heps hX
      (lyapunovVecCoeff_sigmaMin_of_gram_eigenvalues n A
        (le_of_lt hlam) hEig)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-shaped Lyapunov first-order perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem H16_eq16_27_lyapunov_condition_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      (Matrix.diagonal a) X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovVecCoeff_diagonal_sigmaMin_of_entrywise_abs_ge n
        a sigma (le_of_lt hsigma) hgap)
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-shaped Lyapunov first-order perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem H16_eq16_27_lyapunov_condition_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_vecCoeff_sigmaMin n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hDeltaA hDeltaC hLin




























/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    relative Lyapunov first-order perturbation bound from the concrete
    diagonal Lyapunov vec/Kronecker coefficient lower-bound certificate. -/
theorem lyapunov_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n (Matrix.diagonal a) DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_diagonal_of_vecCoeff_entrywise_abs_ge n
      a X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX hgap
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    Frobenius first-order Lyapunov perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem lyapunov_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX <=
      lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) *
        frobNorm X *
        lyapunovScaledPerturbationPairNorm n DeltaA DeltaC alpha gamma := by
  exact
    (lyapunovCond_of_vecCoeff_sigmaMin_isLyapunovConditionFirstOrderBound
      n A X alpha gamma sigma halpha hgamma hsigma hX
      (lyapunovVecCoeff_spectralDiagonal_sigmaMin_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap))
      DeltaA DeltaC DeltaX hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    relative Lyapunov first-order perturbation bound from the concrete
    spectral-diagonal Lyapunov vec/Kronecker coefficient lower-bound
    certificate. -/
theorem lyapunov_relative_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_spectralDiagonal_of_vecCoeff_entrywise_abs_ge n
      U A a X DeltaA DeltaC DeltaX alpha gamma sigma eps
      hU hA halpha hgamma hsigma heps hX hgap
      hDeltaA hDeltaC hLin

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), diagonal case:
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_relative_first_order_bound_diagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-numbered alias for the concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-numbered alias for the relative concrete Lyapunov vec/Kronecker
    entrywise-gap first-order bound. -/
alias H16_eq16_27_lyapunov_relative_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge :=
  lyapunov_relative_first_order_bound_spectralDiagonal_of_vecCoeff_entrywise_abs_ge

/-- Higham, 2nd ed., Chapter 16.3, equation (16.27), supplied orthogonal
    spectral-coordinate case:
    source-shaped Lyapunov first-order perturbation bound from the
    spectral-coordinate `sep(A,-A^T)` lower-bound certificate. -/
theorem H16_eq16_27_lyapunov_condition_spectralDiagonal_of_sep_entrywise_abs_ge
    (n : Nat)
    (U A : Fin n -> Fin n -> Real) (a : Fin n -> Real)
    (X DeltaA DeltaC DeltaX : Fin n -> Fin n -> Real)
    (alpha gamma sigma eps : Real)
    (hU : IsOrthogonal n U)
    (hA : A = rectMatMul U (rectMatMul (Matrix.diagonal a) (matTranspose U)))
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hsigma : 0 < sigma) (heps : 0 <= eps)
    (hX : 0 < frobNorm X)
    (hgap : forall i j, sigma <= |a i + a j|)
    (hDeltaA : frobNorm DeltaA <= eps * alpha)
    (hDeltaC : frobNorm DeltaC <= eps * gamma)
    (hLin : forall i j,
      lyapunovOp n A DeltaX i j =
        DeltaC i j - matMul n DeltaA X i j -
          matMul n X (matTranspose DeltaA) i j) :
    frobNorm DeltaX / frobNorm X <=
      Real.sqrt 2 *
        lyapunovCond_of_inverseOpBound n X alpha gamma (1 / sigma) * eps := by
  exact
    H16_eq16_27_lyapunov_condition_of_sepLowerBound n
      A X DeltaA DeltaC DeltaX alpha gamma sigma eps
      halpha hgamma hsigma heps hX
      (SepLowerBound_lyapunovSpectralDiagonal_of_entrywise_abs_ge n
        U A a sigma hU hA hsigma hgap)
      hDeltaA hDeltaC hLin

end NumStability
