import Mathlib.Data.Real.Basic
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Problem10Bauer.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part01
import NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.Part06
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.SingularValues.Basic
import NumStability.Analysis.SingularValues.Realification

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 20 — Support

Canonical source correspondence module extracted without change from LSPerturbation.
-/

/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with the
    perturbed-side left inverse derived from the first Penrose equation.

    The Chapter 7 Moore-Penrose bridge turns `B Bplus B = B` plus injectivity
    of `x ↦ B*x` into `Bplus B = I`, leaving the same range-projection
    symmetry condition used by the direct operator-bound theorem above. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_injective_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hBinj : Function.Injective (rectMatMulVec B))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hleftB : rectMatMul Bplus B = idMatrix (k + 1) := by
    ext i j
    simpa [rectMatMul, idMatrix] using
      theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective
        B Bplus hBpenrose1 hBinj i j
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB
/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with the
    perturbed-side injectivity derived from the smallness condition.

    The A-side left inverse and operator bound supply the lower action radius
    `1 / Aplus_norm`; the source smallness condition `eta = Aplus_norm * delta
    < 1` makes the perturbation strict enough to preserve injectivity of `B`.
    The first Penrose equation for `Bplus` then supplies the remaining
    perturbed-side left-inverse field. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hsmall_mul : Aplus_norm * delta < 1 := by
    simpa [heta] using hsmall
  have hdelta_lt : delta < 1 / Aplus_norm := by
    rw [lt_div_iff₀ hAplus_pos]
    simpa [mul_comm] using hsmall_mul
  have hlowerA :
      ∀ x : Fin (k + 1) → ℝ,
        (1 / Aplus_norm) * vecNorm2 x ≤
          vecNorm2 (rectMatMulVec A x) :=
    wedinLemma20_11_lowerActionBound_of_left_inverse_rectOpNorm2Le
      A Aplus hAplus_pos hleftA hAplus
  have hBinj : Function.Injective (rectMatMulVec B) :=
    wedinLemma20_11_rectMatMulVec_injective_of_sub_rectOpNorm2Le_lt
      A B hlowerA hDelta hdelta_lt
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_injective_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hBpenrose1 hBinj hSymB
/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    full-column predicate-form pseudoinverse perturbation bound with both
    rectangular left-inverse fields derived from Penrose1 data.

    On the `A` side, Penrose1 plus injectivity gives `Aplus A = I`; the
    smallness condition then preserves injectivity for `B`, and Penrose1 plus
    the Chapter 7 bridge gives `Bplus B = I`. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_Bpenrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hApenrose1 : rectMatMul (rectMatMul A Aplus) A = A)
    (hAinj : Function.Injective (rectMatMulVec A))
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) := by
  have hleftA : rectMatMul Aplus A = idMatrix (k + 1) := by
    ext i j
    simpa [rectMatMul, idMatrix] using
      theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective
        A Aplus hApenrose1 hAinj i j
  exact
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_penrose1_small_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hBpenrose1 hSymB
/-- Higham, 2nd ed., Chapter 20, Lemma 20.11:
    matrix-rank source wrapper for the full-column predicate-form
    pseudoinverse perturbation bound.

    Full column rank of `A` is represented by `(Matrix.of A).rank = k + 1`;
    Chapter 7 turns that rank hypothesis and A-side Penrose1 into the explicit
    left inverse needed by the operator-bound route. -/
theorem wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_rank_Bpenrose1_small_rectOpNorm2Le
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {Aplus_norm delta eta : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hApenrose1 : rectMatMul (rectMatMul A Aplus) A = A)
    (hArank : (Matrix.of A).rank = k + 1)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hBpenrose1 : rectMatMul (rectMatMul B Bplus) B = B)
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) :=
  wedinLemma20_11_rectOpNorm2Le_Bplus_of_Apenrose1_Bpenrose1_small_rectOpNorm2Le
    A B Aplus Bplus hAplus_pos heta hsmall hApenrose1
    (ch7_rectMatMulVec_injective_of_matrix_rank_eq_width A hArank)
    hAplus hDelta hBpenrose1 hSymB
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the complement of a symmetric idempotent projection is positive
    semidefinite. -/
theorem wedinLemma20_12_projectionComplement_finitePSD
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hIdemP : rectMatMul P P = P) :
    finitePSD (fun i j => idMatrix m i j - P i j) := by
  have hPSD :
      finitePSD
        (rectMatMul
          (rectMatMul (idMatrix m)
            (fun i j => idMatrix m i j - P i j))
          (idMatrix m)) :=
    wedinLemma20_12_projection_mul_projectionComplement_mul_projection_finitePSD
      (idMatrix m) P (ch7_idMatrix_symmetric m) hP hIdemP
  simpa [rectMatMul_id_left, rectMatMul_id_right] using hPSD
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    a symmetric idempotent projection is Loewner-bounded by the identity. -/
theorem wedinLemma20_12_projection_loewnerLe_id
    {m : ℕ} (P : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hIdemP : rectMatMul P P = P) :
    finiteLoewnerLe P (fun i j : Fin m => finiteIdMatrix i j) := by
  have hPSD :
      finitePSD (fun i j => idMatrix m i j - P i j) :=
    wedinLemma20_12_projectionComplement_finitePSD P hP hIdemP
  have hLe : finiteLoewnerLe P (idMatrix m) :=
    (finiteLoewnerLe_iff_sub_finitePSD P (idMatrix m)).mpr hPSD
  simpa [idMatrix, finiteIdMatrix] using hLe
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compression `PQP` is Loewner-bounded by the identity. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe (rectMatMul (rectMatMul P Q) P)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_projection
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id P hP hIdemP)
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the swapped companion-square compression `QPQ` is Loewner-bounded by the
    identity. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe (rectMatMul (rectMatMul Q P) Q)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_projection_swapped
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id Q hQ hIdemQ)
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the companion-square compression
    `PQP` is at most one. -/
theorem wedinLemma20_12_projection_mul_swapped_mul_projection_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul P Q) P)
        (wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
          P Q hP hQ hIdemQ) a ≤ 1 := by
  have hSym :=
    wedinLemma20_12_projection_mul_swapped_mul_projection_symmetric
      P Q hP hQ hIdemQ
  have hLe :
      finiteLoewnerLe (rectMatMul (rectMatMul P Q) P)
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa using
      wedinLemma20_12_projection_mul_swapped_mul_projection_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  exact
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      (rectMatMul (rectMatMul P Q) P) hSym hLe a
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of the swapped companion-square
    compression `QPQ` is at most one. -/
theorem wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues (rectMatMul (rectMatMul Q P) Q)
        (wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
          P Q hP hQ hIdemP) a ≤ 1 := by
  have hSym :=
    wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_symmetric
      P Q hP hQ hIdemP
  have hLe :
      finiteLoewnerLe (rectMatMul (rectMatMul Q P) Q)
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa using
      wedinLemma20_12_projection_swapped_mul_projection_mul_projection_swapped_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  exact
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      (rectMatMul (rectMatMul Q P) Q) hSym hLe a
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the companion-square compressions `PQP` and `QPQ` have the same
    complexified spectral radius.

This is a direct spectral-radius bridge for the principal-angle route.  It uses
only projection idempotence and the finite-dimensional fact `rho(AB)=rho(BA)`;
it does not yet identify this radius with the exact operator-2 norm of the PSD
compressions. -/
theorem wedinLemma20_12_toLin_spectralRadius_projection_mul_swapped_mul_projection_eq_swapped
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul P Q) P))) =
      spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul Q P) Q))) := by
  let Pc : Matrix (Fin m) (Fin m) ℂ := realRectToCMatrix P
  let Qc : Matrix (Fin m) (Fin m) ℂ := realRectToCMatrix Q
  have hPidemC : Pc * Pc = Pc := by
    have hbase :
        realRectToCMatrix (rectMatMul P P) =
          realRectToCMatrix P := by
      rw [hIdemP]
    simpa [Pc, realRectToCMatrix_rectMatMul] using hbase
  have hQidemC : Qc * Qc = Qc := by
    have hbase :
        realRectToCMatrix (rectMatMul Q Q) =
          realRectToCMatrix Q := by
      rw [hIdemQ]
    simpa [Qc, realRectToCMatrix_rectMatMul] using hbase
  have hPQP :
      (show Matrix (Fin m) (Fin m) ℂ from
        realRectToCMatrix (rectMatMul (rectMatMul P Q) P)) =
        (Pc * Qc) * Pc := by
    ext i j
    simp [Pc, Qc, realRectToCMatrix_rectMatMul, complexMatrixMul,
      Matrix.mul_apply]
  have hQPQ :
      (show Matrix (Fin m) (Fin m) ℂ from
        realRectToCMatrix (rectMatMul (rectMatMul Q P) Q)) =
        (Qc * Pc) * Qc := by
    ext i j
    simp [Pc, Qc, realRectToCMatrix_rectMatMul, complexMatrixMul,
      Matrix.mul_apply]
  calc
    spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul P Q) P)))
        = spectralRadius ℂ (Matrix.toLin' (Pc * (Qc * Pc))) := by
            rw [hPQP, Matrix.mul_assoc]
    _ = spectralRadius ℂ (Matrix.toLin' ((Qc * Pc) * Pc)) :=
            ch7_toLin_spectralRadius_mul_comm_eq Pc (Qc * Pc)
    _ = spectralRadius ℂ (Matrix.toLin' (Qc * Pc)) := by
            rw [Matrix.mul_assoc, hPidemC]
    _ = spectralRadius ℂ (Matrix.toLin' (Pc * Qc)) :=
            ch7_toLin_spectralRadius_mul_comm_eq Qc Pc
    _ = spectralRadius ℂ (Matrix.toLin' ((Pc * Qc) * Qc)) := by
            rw [Matrix.mul_assoc, hQidemC]
    _ = spectralRadius ℂ (Matrix.toLin' (Qc * (Pc * Qc))) :=
            (ch7_toLin_spectralRadius_mul_comm_eq Qc (Pc * Qc)).symm
    _ = spectralRadius ℂ
        (Matrix.toLin'
          (show Matrix (Fin m) (Fin m) ℂ from
            realRectToCMatrix (rectMatMul (rectMatMul Q P) Q))) := by
            rw [hQPQ, Matrix.mul_assoc]
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    the `P`-range `D^2` compression is Loewner-bounded above by the identity. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe
      (rectMatMul
        (rectMatMul P
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        P)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_projection
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id P hP hIdemP)
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped identity upper bound for the `Q`-range `D^2` compression. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_id
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q) :
    finiteLoewnerLe
      (rectMatMul
        (rectMatMul Q
          (rectMatMul (fun i j => P i j - Q i j)
            (fun i j => P i j - Q i j)))
        Q)
      (fun i j : Fin m => finiteIdMatrix i j) :=
  finiteLoewnerLe_trans
    (wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_projection_swapped
      P Q hP hQ hIdemP hIdemQ)
    (wedinLemma20_12_projection_loewnerLe_id Q hQ hIdemQ)
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `P(P-Q)^2P` is at most one. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) a ≤ 1 := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  have hSym : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hLe :
      finiteLoewnerLe MP
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  simpa [MP] using
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      MP hSym hLe a
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    every finite Hermitian eigenvalue of `Q(P-Q)^2Q` is at most one. -/
theorem wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_le_one
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (a : Fin m) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) a ≤ 1 := by
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSym : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hLe :
      finiteLoewnerLe MQ
        (fun i j : Fin m => (1 : ℝ) * finiteIdMatrix i j) := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_loewnerLe_id
        P Q hP hQ hIdemP hIdemQ
  simpa [MQ] using
    finiteHermitianEigenvalues_le_of_finiteLoewnerLe_smul_id
      MQ hSym hLe a
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    endpoint characterization for the selected top eigenvalue of
    `P(P-Q)^2P`.  Under a top-index certificate, that top value is `1`
    exactly when the exceptional range/kernel subspace
    `ran(P) ∩ ker(Q)` contains a nonzero vector.

This packages the `lambda = 1` endpoint into a finite-dimensional
range/kernel problem; it does not compare the two endpoint multiplicities. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_exists_projection_range_projection_swapped_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP = 1 ↔
      ∃ x : Fin m → ℝ,
        x ≠ 0 ∧
        rectMatMulVec P x = x ∧
        rectMatMulVec Q x = 0 := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  have hSymP : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaP : ℝ := finiteHermitianEigenvalues MP hSymP aP
  have hTopP' :
      ∀ a : Fin m, finiteHermitianEigenvalues MP hSymP a ≤ lambdaP := by
    intro a
    simpa [MP, lambdaP] using hTopP a
  constructor
  · intro hTop_eq_one
    have hLambda_eq_one : lambdaP = 1 := by
      simpa [MP, lambdaP] using hTop_eq_one
    let xP : Fin m → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MP hSymP).eigenvectorBasis aP)
    have hxP_ne : xP ≠ 0 := by
      intro hx0
      have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MP hSymP aP
      change finiteVecNorm2Sq xP = 1 at hnorm
      rw [hx0] at hnorm
      simp [finiteVecNorm2Sq] at hnorm
    have hxP_eig :
        rectMatMulVec MP xP = fun i => lambdaP * xP i := by
      have h := finiteMatVec_finiteHermitianEigenvector_eq MP hSymP aP
      simpa [finiteMatVec, rectMatMulVec, MP, xP, lambdaP] using h
    have hLambda_ne_zero : lambdaP ≠ 0 := by
      simp [hLambda_eq_one]
    have hxP_range :
        rectMatMulVec P xP = xP :=
      wedinLemma20_12_projection_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
        P Q hIdemP lambdaP xP
        (by simpa [MP] using hxP_eig) hLambda_ne_zero
    have hxP_compress_self : rectMatMulVec MP xP = xP := by
      calc
        rectMatMulVec MP xP = fun i => lambdaP * xP i := hxP_eig
        _ = xP := by
              ext i
              simp [hLambda_eq_one]
    have hxQ_zero : rectMatMulVec Q xP = 0 :=
      (wedinLemma20_12_projection_range_projectionDiff_sq_compression_eq_self_iff_projection_swapped_zero
        P Q hP hQ hIdemP hIdemQ xP hxP_range).mp
        (by simpa [MP] using hxP_compress_self)
    exact ⟨xP, hxP_ne, hxP_range, hxQ_zero⟩
  · rintro ⟨x, hx_ne, hxP_range, hxQ_zero⟩
    have hxP_compress_self :
        rectMatMulVec MP x = x := by
      simpa [MP] using
        (wedinLemma20_12_projection_range_projectionDiff_sq_compression_eq_self_iff_projection_swapped_zero
          P Q hP hQ hIdemP hIdemQ x hxP_range).mpr hxQ_zero
    have hxP_eig :
        finiteMatVec MP x = fun i => (1 : ℝ) * x i := by
      calc
        finiteMatVec MP x = rectMatMulVec MP x := by
            rfl
        _ = x := hxP_compress_self
        _ = fun i => (1 : ℝ) * x i := by
            ext i
            simp
    have hOne_mem :
        (1 : ℝ) ∈ Set.range (finiteHermitianEigenvalues MP hSymP) :=
      finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
        MP hSymP hx_ne hxP_eig
    rcases hOne_mem with ⟨bP, hbP⟩
    have hOne_le : (1 : ℝ) ≤ lambdaP := by
      rw [← hbP]
      exact hTopP' bP
    have hTop_le_one : lambdaP ≤ 1 := by
      simpa [MP, lambdaP] using
        wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_le_one
          P Q hP hQ hIdemP hIdemQ aP
    simpa [MP, lambdaP] using le_antisymm hTop_le_one hOne_le
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    swapped endpoint characterization for the selected top eigenvalue of
    `Q(P-Q)^2Q`.  Under a top-index certificate, that top value is `1`
    exactly when `ran(Q) ∩ ker(P)` contains a nonzero vector. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_swapped_eq_one_iff_exists_projection_swapped_range_projection_zero
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aQ : Fin m}
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ = 1 ↔
      ∃ x : Fin m → ℝ,
        x ≠ 0 ∧
        rectMatMulVec Q x = x ∧
        rectMatMulVec P x = 0 := by
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSymQ : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaQ : ℝ := finiteHermitianEigenvalues MQ hSymQ aQ
  have hTopQ' :
      ∀ a : Fin m, finiteHermitianEigenvalues MQ hSymQ a ≤ lambdaQ := by
    intro a
    simpa [MQ, lambdaQ] using hTopQ a
  constructor
  · intro hTop_eq_one
    have hLambda_eq_one : lambdaQ = 1 := by
      simpa [MQ, lambdaQ] using hTop_eq_one
    let xQ : Fin m → ℝ :=
      ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MQ hSymQ).eigenvectorBasis aQ)
    have hxQ_ne : xQ ≠ 0 := by
      intro hx0
      have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MQ hSymQ aQ
      change finiteVecNorm2Sq xQ = 1 at hnorm
      rw [hx0] at hnorm
      simp [finiteVecNorm2Sq] at hnorm
    have hxQ_eig :
        rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := by
      have h := finiteMatVec_finiteHermitianEigenvector_eq MQ hSymQ aQ
      simpa [finiteMatVec, rectMatMulVec, MQ, xQ, lambdaQ] using h
    have hLambda_ne_zero : lambdaQ ≠ 0 := by
      simp [hLambda_eq_one]
    have hxQ_range :
        rectMatMulVec Q xQ = xQ :=
      wedinLemma20_12_projection_swapped_range_of_projectionDiff_sq_compression_eigenvalue_ne_zero
        P Q hIdemQ lambdaQ xQ
        (by simpa [MQ] using hxQ_eig) hLambda_ne_zero
    have hxQ_compress_self : rectMatMulVec MQ xQ = xQ := by
      calc
        rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := hxQ_eig
        _ = xQ := by
              ext i
              simp [hLambda_eq_one]
    have hxP_zero : rectMatMulVec P xQ = 0 :=
      (wedinLemma20_12_projection_swapped_range_projectionDiff_sq_compression_eq_self_iff_projection_zero
        P Q hP hQ hIdemP hIdemQ xQ hxQ_range).mp
        (by simpa [MQ] using hxQ_compress_self)
    exact ⟨xQ, hxQ_ne, hxQ_range, hxP_zero⟩
  · rintro ⟨x, hx_ne, hxQ_range, hxP_zero⟩
    have hxQ_compress_self :
        rectMatMulVec MQ x = x := by
      simpa [MQ] using
        (wedinLemma20_12_projection_swapped_range_projectionDiff_sq_compression_eq_self_iff_projection_zero
          P Q hP hQ hIdemP hIdemQ x hxQ_range).mpr hxP_zero
    have hxQ_eig :
        finiteMatVec MQ x = fun i => (1 : ℝ) * x i := by
      calc
        finiteMatVec MQ x = rectMatMulVec MQ x := by
            rfl
        _ = x := hxQ_compress_self
        _ = fun i => (1 : ℝ) * x i := by
            ext i
            simp
    have hOne_mem :
        (1 : ℝ) ∈ Set.range (finiteHermitianEigenvalues MQ hSymQ) :=
      finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
        MQ hSymQ hx_ne hxQ_eig
    rcases hOne_mem with ⟨bQ, hbQ⟩
    have hOne_le : (1 : ℝ) ≤ lambdaQ := by
      rw [← hbQ]
      exact hTopQ' bQ
    have hTop_le_one : lambdaQ ≤ 1 := by
      simpa [MQ, lambdaQ] using
        wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_le_one
          P Q hP hQ hIdemP hIdemQ aQ
    simpa [MQ, lambdaQ] using le_antisymm hTop_le_one hOne_le
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    endpoint selected-top transfer for the `lambda = 1` case.  Under equal
    projection range dimension, the selected top eigenvalue of `P(P-Q)^2P` is
    `1` iff the selected top eigenvalue of `Q(P-Q)^2Q` is `1`.

This combines the endpoint range/kernel characterizations with the
rank-nullity nonzero-transfer bridge. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one_of_range_finrank_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP aQ : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP)
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP = 1 ↔
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ = 1 := by
  have hEndpointP :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_exists_projection_range_projection_swapped_zero
      P Q hP hQ hIdemP hIdemQ hTopP
  have hEndpointQ :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_swapped_eq_one_iff_exists_projection_swapped_range_projection_zero
      P Q hP hQ hIdemP hIdemQ hTopQ
  have hTransfer :=
    wedinLemma20_12_exists_projection_range_projection_swapped_zero_iff_exists_projection_swapped_range_projection_zero_of_range_finrank_eq
      P Q hP hQ hIdemP hIdemQ hRangeFinrank
  constructor
  · intro hP_one
    exact hEndpointQ.mpr (hTransfer.mp (hEndpointP.mp hP_one))
  · intro hQ_one
    exact hEndpointP.mpr (hTransfer.mpr (hEndpointQ.mp hQ_one))
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    source range-projection endpoint transfer for the `lambda = 1` case.
    For the projections `A*Aplus` and `B*Bplus`, the equal range-dimension
    hypothesis required by the abstract endpoint theorem follows from the two
    left inverses `Aplus*A = I` and `Bplus*B = I`. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_rangeProjection_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    {aA aB : Fin m}
    (hTopA : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul A Aplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul A Aplus))
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul A Aplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul A Aplus))
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aA)
    (hTopB : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul B Bplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul B Bplus))
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul (rectMatMul B Bplus)
              (rectMatMul
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
                (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
            (rectMatMul B Bplus))
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
            (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
            (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aB) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul (rectMatMul A Aplus)
            (rectMatMul
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
          (rectMatMul A Aplus))
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
          (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
          (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aA = 1 ↔
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul (rectMatMul B Bplus)
            (rectMatMul
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)
              (fun i j => rectMatMul A Aplus i j - rectMatMul B Bplus i j)))
          (rectMatMul B Bplus))
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          (rectMatMul A Aplus) (rectMatMul B Bplus) hSymA hSymB
          (rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA)
          (rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB)) aB = 1 := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  have hIdemA : rectMatMul PA PA = PA := by
    simpa [PA] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA
  have hIdemB : rectMatMul PB PB = PB := by
    simpa [PB] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB
  have hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of PA : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of PB : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) := by
    simpa [PA, PB] using
      wedinLemma20_12_rangeProjection_range_finrank_eq_of_left_inverses
        A B Aplus Bplus hleftA hleftB
  simpa [PA, PB, hIdemA, hIdemB] using
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one_of_range_finrank_eq
      PA PB (by simpa [PA] using hSymA) (by simpa [PB] using hSymB)
      hIdemA hIdemB hTopA hTopB hRangeFinrank
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    unconditional selected-top equality for the two `D^2` projection
    compressions under equal projection-range dimension.

The proof splits the selected top value into the three spectral cases allowed
by `0 <= lambda <= 1`: zero is handled by nonnegativity, one by the endpoint
range/kernel transfer, and the open interval by the compressed eigenvector
transfer to the opposite range. -/
theorem wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_swapped_of_top_of_range_finrank_eq
    {m : ℕ} (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    {aP aQ : Fin m}
    (hTopP : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)
          (wedinLemma20_12_projectionDiff_sq_compression_symmetric
            P Q hP hQ hIdemP hIdemQ) aP)
    (hTopQ : ∀ a : Fin m,
      finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) a ≤
        finiteHermitianEigenvalues
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)
          (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
            P Q hP hQ hIdemP hIdemQ) aQ)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul P
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          P)
        (wedinLemma20_12_projectionDiff_sq_compression_symmetric
          P Q hP hQ hIdemP hIdemQ) aP =
      finiteHermitianEigenvalues
        (rectMatMul
          (rectMatMul Q
            (rectMatMul (fun i j => P i j - Q i j)
              (fun i j => P i j - Q i j)))
          Q)
        (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
          P Q hP hQ hIdemP hIdemQ) aQ := by
  let MP : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul P
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      P
  let MQ : Fin m → Fin m → ℝ :=
    rectMatMul
      (rectMatMul Q
        (rectMatMul (fun i j => P i j - Q i j)
          (fun i j => P i j - Q i j)))
      Q
  have hSymP : IsSymmetricFiniteMatrix MP := by
    simpa [MP] using
      wedinLemma20_12_projectionDiff_sq_compression_symmetric
        P Q hP hQ hIdemP hIdemQ
  have hSymQ : IsSymmetricFiniteMatrix MQ := by
    simpa [MQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
        P Q hP hQ hIdemP hIdemQ
  let lambdaP : ℝ := finiteHermitianEigenvalues MP hSymP aP
  let lambdaQ : ℝ := finiteHermitianEigenvalues MQ hSymQ aQ
  have hTopP' :
      ∀ a : Fin m, finiteHermitianEigenvalues MP hSymP a ≤ lambdaP := by
    intro a
    simpa [MP, lambdaP] using hTopP a
  have hTopQ' :
      ∀ a : Fin m, finiteHermitianEigenvalues MQ hSymQ a ≤ lambdaQ := by
    intro a
    simpa [MQ, lambdaQ] using hTopQ a
  have hEndpoint :
      lambdaP = 1 ↔ lambdaQ = 1 := by
    simpa [MP, MQ, lambdaP, lambdaQ] using
      wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_one_iff_swapped_eq_one_of_range_finrank_eq
        P Q hP hQ hIdemP hIdemQ hTopP hTopQ hRangeFinrank
  have hQ_nonneg : 0 ≤ lambdaQ := by
    simpa [MQ, lambdaQ] using
      wedinLemma20_12_projectionDiff_sq_compression_swapped_finiteHermitianEigenvalues_nonneg
        P Q hP hQ hIdemP hIdemQ aQ
  have hP_nonneg : 0 ≤ lambdaP := by
    simpa [MP, lambdaP] using
      wedinLemma20_12_projectionDiff_sq_compression_finiteHermitianEigenvalues_nonneg
        P Q hP hQ hIdemP hIdemQ aP
  have hP_le_Q : lambdaP ≤ lambdaQ := by
    by_cases hP_zero : lambdaP = 0
    · simpa [hP_zero] using hQ_nonneg
    · by_cases hP_one : lambdaP = 1
      · have hQ_one : lambdaQ = 1 := hEndpoint.mp hP_one
        rw [hP_one, hQ_one]
      · let xP : Fin m → ℝ :=
          ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MP hSymP).eigenvectorBasis aP)
        have hxP_ne : xP ≠ 0 := by
          intro hx0
          have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MP hSymP aP
          change finiteVecNorm2Sq xP = 1 at hnorm
          rw [hx0] at hnorm
          simp [finiteVecNorm2Sq] at hnorm
        have hxP_eig : rectMatMulVec MP xP = fun i => lambdaP * xP i := by
          have h := finiteMatVec_finiteHermitianEigenvector_eq MP hSymP aP
          simpa [finiteMatVec, rectMatMulVec, MP, xP, lambdaP] using h
        obtain ⟨yQ, hyQ_ne, _hyQ_range, hyQ_eig⟩ :=
          wedinLemma20_12_exists_projection_swapped_range_projectionDiff_sq_compression_eigenvector_of_projection_range
            P Q hIdemP hIdemQ lambdaP xP
            (by simpa [MP] using hxP_eig) hxP_ne hP_zero hP_one
        have hyQ_eig_finite :
            finiteMatVec MQ yQ = fun i => lambdaP * yQ i := by
          simpa [finiteMatVec, rectMatMulVec, MQ] using hyQ_eig
        have hRangeQ :
            lambdaP ∈ Set.range (finiteHermitianEigenvalues MQ hSymQ) :=
          finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
            MQ hSymQ hyQ_ne hyQ_eig_finite
        rcases hRangeQ with ⟨bQ, hbQ⟩
        rw [← hbQ]
        exact hTopQ' bQ
  have hQ_le_P : lambdaQ ≤ lambdaP := by
    by_cases hQ_zero : lambdaQ = 0
    · simpa [hQ_zero] using hP_nonneg
    · by_cases hQ_one : lambdaQ = 1
      · have hP_one : lambdaP = 1 := hEndpoint.mpr hQ_one
        rw [hQ_one, hP_one]
      · let xQ : Fin m → ℝ :=
          ⇑((IsSymmetricFiniteMatrix.to_matrix_isHermitian MQ hSymQ).eigenvectorBasis aQ)
        have hxQ_ne : xQ ≠ 0 := by
          intro hx0
          have hnorm := finiteVecNorm2Sq_finiteHermitianEigenvector_eq_one MQ hSymQ aQ
          change finiteVecNorm2Sq xQ = 1 at hnorm
          rw [hx0] at hnorm
          simp [finiteVecNorm2Sq] at hnorm
        have hxQ_eig : rectMatMulVec MQ xQ = fun i => lambdaQ * xQ i := by
          have h := finiteMatVec_finiteHermitianEigenvector_eq MQ hSymQ aQ
          simpa [finiteMatVec, rectMatMulVec, MQ, xQ, lambdaQ] using h
        obtain ⟨yP, hyP_ne, _hyP_range, hyP_eig⟩ :=
          wedinLemma20_12_exists_projection_range_projectionDiff_sq_compression_eigenvector_of_projection_swapped_range
            P Q hIdemP hIdemQ lambdaQ xQ
            (by simpa [MQ] using hxQ_eig) hxQ_ne hQ_zero hQ_one
        have hyP_eig_finite :
            finiteMatVec MP yP = fun i => lambdaQ * yP i := by
          simpa [finiteMatVec, rectMatMulVec, MP] using hyP_eig
        have hRangeP :
            lambdaQ ∈ Set.range (finiteHermitianEigenvalues MP hSymP) :=
          finiteHermitianEigenvalues_mem_range_of_finiteMatVec_eigenvector
            MP hSymP hyP_ne hyP_eig_finite
        rcases hRangeP with ⟨bP, hbP⟩
        rw [← hbP]
        exact hTopP' bP
  simpa [MP, MQ, lambdaP, lambdaQ] using le_antisymm hP_le_Q hQ_le_P
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    equality of the exact complexified Euclidean operator norms of the two
    `D^2` projection compressions.

This packages the selected-top eigenvalue equality through the existing PSD
top-eigenvalue/operator-norm wrappers for `P(P-Q)^2P` and `Q(P-Q)^2Q`. -/
theorem wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_swapped_of_range_finrank_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P)) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)) := by
  obtain ⟨aP, hOpP, hTopP⟩ :=
    wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projectionDiff_sq_compression_eq
      hm P Q hP hQ hIdemP hIdemQ
  obtain ⟨aQ, hOpQ, hTopQ⟩ :=
    wedinLemma20_12_exists_topEigenvalue_complexMatrixOp2_projectionDiff_sq_compression_swapped_eq
      hm P Q hP hQ hIdemP hIdemQ
  have hEigEq :=
    wedinLemma20_12_top_finiteHermitianEigenvalue_projectionDiff_sq_compression_eq_swapped_of_top_of_range_finrank_eq
      P Q hP hQ hIdemP hIdemQ hTopP hTopQ hRangeFinrank
  calc
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul P
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            P))
        = finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)
            (wedinLemma20_12_projectionDiff_sq_compression_symmetric
              P Q hP hQ hIdemP hIdemQ) aP := hOpP
    _ = finiteHermitianEigenvalues
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)
            (wedinLemma20_12_projectionDiff_sq_compression_swapped_symmetric
              P Q hP hQ hIdemP hIdemQ) aQ := hEigEq
    _ = complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul Q
              (rectMatMul (fun i j => P i j - Q i j)
                (fun i j => P i j - Q i j)))
            Q)) := hOpQ.symm
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    Stewart--Sun cross-projection norm equality for finite symmetric
    idempotent projections with equal projection-range dimension.

This is the abstract principal-angle equality used to remove the conditional
`complexMatrixOp2` hypothesis from the source Lemma 20.12 `min` bound. -/
theorem wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_range_finrank_eq
    {m : ℕ} (hm : 0 < m) (P Q : Fin m → Fin m → ℝ)
    (hP : IsSymmetricFiniteMatrix P)
    (hQ : IsSymmetricFiniteMatrix Q)
    (hIdemP : rectMatMul P P = P)
    (hIdemQ : rectMatMul Q Q = Q)
    (hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of P : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of Q : Matrix (Fin m) (Fin m) ℝ).mulVecLin))) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul P (fun i j => idMatrix m i j - Q i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul Q (fun i j => idMatrix m i j - P i j))) := by
  have hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul P
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              P)) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul Q
                (rectMatMul (fun i j => P i j - Q i j)
                  (fun i j => P i j - Q i j)))
              Q)) :=
    wedinLemma20_12_complexMatrixOp2_projectionDiff_sq_compression_eq_swapped_of_range_finrank_eq
      hm P Q hP hQ hIdemP hIdemQ hRangeFinrank
  exact
    wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_projectionDiff_sq_compression_eq
      P Q hP hQ hIdemP hIdemQ hEq
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12 dependency:
    source range-projection Stewart--Sun equality.  For the projections
    `A*Aplus` and `B*Bplus`, the equal range-dimension hypothesis follows from
    the two source left inverses. -/
theorem wedinLemma20_12_complexMatrixOp2_rangeProjection_crossProjection_eq_of_left_inverses
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus)) :
    complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul B Bplus)
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
      complexMatrixOp2
        (realRectToCMatrix
          (rectMatMul
            (rectMatMul A Aplus)
            (fun i j => idMatrix m i j - rectMatMul B Bplus i j))) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  have hIdemA : rectMatMul PA PA = PA := by
    simpa [PA] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse A Aplus hleftA
  have hIdemB : rectMatMul PB PB = PB := by
    simpa [PB] using
      rectMatMul_rangeProjection_idempotent_of_left_inverse B Bplus hleftB
  have hRangeFinrank :
      Module.finrank ℝ
          (LinearMap.range ((Matrix.of PB : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) =
        Module.finrank ℝ
          (LinearMap.range ((Matrix.of PA : Matrix (Fin m) (Fin m) ℝ).mulVecLin)) := by
    simpa [PA, PB] using
      wedinLemma20_12_rangeProjection_range_finrank_eq_of_left_inverses
        B A Bplus Aplus hleftB hleftA
  simpa [PA, PB] using
    wedinLemma20_12_complexMatrixOp2_crossProjection_eq_of_range_finrank_eq
      hm PB PA (by simpa [PB] using hSymB) (by simpa [PA] using hSymA)
      hIdemB hIdemA hRangeFinrank
/-- Higham, 2nd ed., Chapter 20, Lemma 20.12:
    source `min` projector bound with the Stewart--Sun/principal-angle equality
    discharged.

This is the source-facing Lemma 20.12 surface in the repository's
`rectOpNorm2Le` API:
`||P_B(I-P_A)||₂ <= ||A-B||₂ * min(||Aplus||₂, ||Bplus||₂)`. -/
theorem wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    {delta Aplus_norm Bplus_norm : ℝ}
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus_norm_nonneg : 0 ≤ Aplus_norm)
    (hBplus_norm_nonneg : 0 ≤ Bplus_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hBplus : rectOpNorm2Le Bplus Bplus_norm) :
    rectOpNorm2Le
      (rectMatMul
        (rectMatMul B Bplus)
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
      (delta * min Aplus_norm Bplus_norm) := by
  have hEq :
      complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul B Bplus)
              (fun i j => idMatrix m i j - rectMatMul A Aplus i j))) =
        complexMatrixOp2
          (realRectToCMatrix
            (rectMatMul
              (rectMatMul A Aplus)
              (fun i j => idMatrix m i j - rectMatMul B Bplus i j))) :=
    wedinLemma20_12_complexMatrixOp2_rangeProjection_crossProjection_eq_of_left_inverses
      hm A B Aplus Bplus hleftA hleftB hSymA hSymB
  exact
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min_of_complexMatrixOp2_eq
      A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      hAplus_norm_nonneg hBplus_norm_nonneg hAplus hBplus hEq
/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.1):
    printed relative solution perturbation bound using the source-facing
    Lemma 20.12 `min` projector surface.

This removes the old caller-facing cross-projection equality hypothesis by
combining Lemma 20.11's `Bplus` radius with the proved Lemma 20.12 bound
`||P_B(I-P_A)||₂ <= delta * min(||Aplus||₂, ||Bplus||₂)`. -/
theorem wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_min_surface_column_orthogonal
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
      wedinTheorem20_1SolutionRelativeRHS
        kappa eps A_norm (vecNorm2 x) (vecNorm2 r) := by
  have hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - eta)) :=
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB
  have hden_pos : 0 < 1 - eta :=
    wedinLemma20_11_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - eta) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hPBIPA_min :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * min Aplus_norm (Aplus_norm / (1 - eta))) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min
      hm A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      (le_of_lt hAplus_pos) hBplus_radius_nonneg hAplus hBplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    rectOpNorm2Le_mono
      (mul_le_mul_of_nonneg_left
        (min_le_left Aplus_norm (Aplus_norm / (1 - eta))) hdelta_nonneg)
      hPBIPA_min
  exact
    wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_projector_bound_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos hA_norm_pos
      hx_norm_pos hkappa hdelta heta hsmall hleftB hSymB hPBIPA hBplus
      hDeltaA hDeltab hDeltaA_norm_budget hDeltab_norm_budget
      hrangeA_residual hB hr hs horth_s
/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equation (20.2):
    printed relative residual perturbation bound using the source-facing
    Lemma 20.12 `min` projector surface.

This wrapper removes both the raw `P_B(I-P_A)` projector-bound hypothesis and
the earlier exact cross-projection equality hypothesis.  Lemma 20.11 supplies
the `Bplus` radius used by the Lemma 20.12 `min` surface, and monotonicity of
`rectOpNorm2Le` weakens `delta * min(...)` to the printed `delta*||Aplus||₂`
radius consumed by the residual perturbation algebra. -/
theorem wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {delta Aplus_norm DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_nonneg : 0 ≤ A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (hsmall : kappa * eps < 1)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
      wedinTheorem20_1ResidualRelativeRHS kappa eps := by
  have heta : kappa * eps = Aplus_norm * delta := by
    rw [hkappa, hdelta]
    ring
  have hBplus :
      rectOpNorm2Le Bplus (Aplus_norm / (1 - kappa * eps)) :=
    wedinLemma20_11_rectOpNorm2Le_Bplus_of_left_inverse_rectOpNorm2Le
      A B Aplus Bplus hAplus_pos heta hsmall hleftA hAplus hDelta
      hleftB hSymB
  have hden_pos : 0 < 1 - kappa * eps :=
    wedinTheorem20_1_denominator_pos hsmall
  have hBplus_radius_nonneg : 0 ≤ Aplus_norm / (1 - kappa * eps) :=
    div_nonneg (le_of_lt hAplus_pos) (le_of_lt hden_pos)
  have hPBIPA_min :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * min Aplus_norm (Aplus_norm / (1 - kappa * eps))) :=
    wedinLemma20_12_rectOpNorm2Le_rangeProjection_mul_projectionComplement_swapped_min
      hm A B Aplus Bplus hleftA hleftB hSymA hSymB hDelta
      (le_of_lt hAplus_pos) hBplus_radius_nonneg hAplus hBplus
  have hdelta_nonneg : 0 ≤ delta :=
    rectOpNorm2Le_radius_nonneg (M := fun i j => B i j - A i j) hDelta
  have hPBIPA :
      rectOpNorm2Le
        (rectMatMul
          (rectMatMul B Bplus)
          (fun i j => idMatrix m i j - rectMatMul A Aplus i j))
        (delta * Aplus_norm) :=
    rectOpNorm2Le_mono
      (mul_le_mul_of_nonneg_left
        (min_le_left Aplus_norm (Aplus_norm / (1 - kappa * eps)))
        hdelta_nonneg)
      hPBIPA_min
  exact
    wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_projector_bound_geometry_column_orthogonal
      A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hA_norm_nonneg
      heps_nonneg hkappa hdelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
      hDeltab_norm_budget hleftA hleftB hSymA hSymB hrangeA_residual
      hPBIPA hB hr hs horth_s
/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equations (20.1)-(20.2):
    combined source-facing Wedin perturbation surface at the repository
    residual-definition and column-orthogonality API.

This packages the separately proved solution and residual displayed bounds
after Lemmas 20.11 and 20.12 have discharged the `Bplus` and projector
hypotheses.  The two right-hand-side perturbation budgets are kept separate
because the printed solution and residual estimates use different normalizers. -/
theorem wedinTheorem20_1_solution_and_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ) (b Deltab r s : Fin m → ℝ)
    (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall_eta : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget_solution :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r))
    (hDeltab_norm_budget_residual : Deltab_norm ≤ eps * vecNorm2 b)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    (vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        wedinTheorem20_1SolutionRelativeRHS
          kappa eps A_norm (vecNorm2 x) (vecNorm2 r)) ∧
      (vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
        wedinTheorem20_1ResidualRelativeRHS kappa eps) := by
  have hsmall_kappa : kappa * eps < 1 := by
    have h : kappa * eps = eta := by
      rw [hkappa, heta, hdelta]
      ring
    rw [h]
    exact hsmall_eta
  constructor
  · exact
      wedinTheorem20_1_solutionRelativeRHS_le_of_residual_definitions_min_surface_column_orthogonal
        hm A B Aplus Bplus DeltaA b Deltab r s x y hAplus_pos hA_norm_pos
        hx_norm_pos hkappa hdelta heta hsmall_eta hleftA hleftB hSymA hSymB
        hDelta hAplus hDeltaA hDeltab hDeltaA_norm_budget
        hDeltab_norm_budget_solution hrangeA_residual hB hr hs horth_s
  · exact
      wedinTheorem20_1_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
        hm A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos hAplus_pos
        (le_of_lt hA_norm_pos) heps_nonneg hkappa hdelta hsmall_kappa hAplus
        hDelta hDeltaA hDeltab hDeltaA_norm_budget
        hDeltab_norm_budget_residual hleftA hleftB hSymA hSymB
        hrangeA_residual hB hr hs horth_s

end NumStability
