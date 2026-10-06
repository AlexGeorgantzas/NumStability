import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.NormalEquations
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# AugmentedSystem

Canonical reusable module extracted without change from LSQRSolve.
-/

/-- Component form of Higham, 2nd ed., Chapter 20, equation (20.3):
    `[I A; A^T 0][r; x] = [b; 0]`. -/
def LSAugmentedNormalSystem {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b r : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, r i + rectMatMulVec A x i = b i) ∧
  (∀ j : Fin n, ∑ i : Fin m, A i j * r i = 0)
/-- Higham, 2nd ed., Chapter 20, equations (20.15a)-(20.15b):
    arbitrary-right-hand-side augmented least-squares system
    `r + A x = f`, `A^T r = g`.

    The special case `f = b`, `g = 0` is the augmented normal-equation
    system (20.3). -/
def LSAugmentedSystem {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, r i + rectMatMulVec A x i = f i) ∧
  (∀ j : Fin n, ∑ i : Fin m, A i j * r i = g j)
/-- Asymmetric arbitrary-right-hand-side augmented LS system.  This is the
    exact system shape used by Higham, 2nd ed., Chapter 20, Theorem 20.4:
    the two appearances of `A` in (20.15) may be perturbed differently. -/
def LSAsymmetricAugmentedSystem {m n : ℕ}
    (A1 A2 : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, r i + rectMatMulVec A1 x i = f i) ∧
  (∀ j : Fin n, ∑ i : Fin m, A2 i j * r i = g j)
/-- The asymmetric augmented system reduces to (20.15) when the two matrix
    occurrences agree. -/
theorem LSAsymmetricAugmentedSystem.symmetric_iff {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ) :
    LSAsymmetricAugmentedSystem A A f g r x ↔
      LSAugmentedSystem A f g r x := Iff.rfl
/-- Equation (20.3) is the zero-`g` special case of the arbitrary augmented
    system (20.15). -/
theorem LSAugmentedSystem.iff_augmentedNormalSystem_zero_rhs {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b r : Fin m → ℝ) (x : Fin n → ℝ) :
    LSAugmentedSystem A b (0 : Fin n → ℝ) r x ↔
      LSAugmentedNormalSystem A b r x := by
  constructor
  · intro h
    constructor
    · exact h.1
    · intro j
      simpa using h.2 j
  · intro h
    constructor
    · exact h.1
    · intro j
      simpa using h.2 j
/-- Higham, 2nd ed., Chapter 20, equation (20.4): the perturbed augmented
    least-squares system
    `[I A + DeltaA; (A + DeltaA)^T 0] [s; y] = [b + Deltab; 0]`. -/
def LSPerturbedAugmentedSystem {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (s : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  LSAugmentedSystem (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) (0 : Fin n → ℝ) s y
/-- Component form of Higham's perturbed augmented system (20.4). -/
theorem LSPerturbedAugmentedSystem.iff_component {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (s : Fin m → ℝ) (y : Fin n → ℝ) :
    LSPerturbedAugmentedSystem A DeltaA b Deltab s y ↔
      (∀ i : Fin m,
        s i + rectMatMulVec (fun i j => A i j + DeltaA i j) y i =
          b i + Deltab i) ∧
      (∀ j : Fin n, ∑ i : Fin m, (A i j + DeltaA i j) * s i = 0) := by
  rfl
/-- Higham, 2nd ed., Chapter 20, Section 20.5, exact transformed QR solve
    formula for the arbitrary augmented system (20.15): after writing
    `d = [d₁; d₂]`, if `R^T h = g` and `R x = d₁ - h`, then
    `r = [h; d₂]` and `x` solve the transformed system
    `r + [R; 0] x = d`, `[R^T 0] r = g`.

    This is the exact algebraic solve of the transformed system only; it does
    not construct the QR factorization, lift the result back by `Q`, or prove
    the rounded perturbation bound in Theorem 20.4. -/
theorem LSAugmentedSystem.transformed_qr_solution {n k : ℕ}
    (R : Fin n → Fin n → ℝ)
    (d1 h x : Fin n → ℝ) (d2 : Fin k → ℝ) (g : Fin n → ℝ)
    (hRt : ∀ j : Fin n, ∑ i : Fin n, R i j * h i = g j)
    (hRx : rectMatMulVec R x = fun i : Fin n => d1 i - h i) :
    LSAugmentedSystem (lsQRTallBlock R) (Fin.append d1 d2) g
      (Fin.append h d2) x := by
  constructor
  · intro i
    exact Fin.addCases
      (motive := fun i : Fin (n + k) =>
        Fin.append h d2 i + rectMatMulVec (lsQRTallBlock R) x i =
          Fin.append d1 d2 i)
      (fun i => by
      have hmul :
          rectMatMulVec (lsQRTallBlock R) x (Fin.castAdd k i) =
            rectMatMulVec R x i := by
        simpa [Fin.append_left] using
          congrFun (lsQRTallBlock_mulVec R x) (Fin.castAdd k i)
      have hRxi : rectMatMulVec R x i = d1 i - h i := congrFun hRx i
      change Fin.append h d2 (Fin.castAdd k i) +
          rectMatMulVec (lsQRTallBlock R) x (Fin.castAdd k i) =
        Fin.append d1 d2 (Fin.castAdd k i)
      rw [hmul, hRxi]
      simp [Fin.append_left])
      (fun i => by
      have hmul :
          rectMatMulVec (lsQRTallBlock R) x (Fin.natAdd n i) = 0 := by
        simpa [Fin.append_right] using
          congrFun (lsQRTallBlock_mulVec R x) (Fin.natAdd n i)
      change Fin.append h d2 (Fin.natAdd n i) +
          rectMatMulVec (lsQRTallBlock R) x (Fin.natAdd n i) =
        Fin.append d1 d2 (Fin.natAdd n i)
      rw [hmul]
      simp [Fin.append_right])
      i
  · intro j
    exact (congrFun (lsQRTallBlock_transpose_mulVec_append R h d2) j).trans
      (hRt j)
/-- Higham, 2nd ed., Chapter 20, equation (20.17): the scaled augmented
    least-squares coefficient matrix `C(alpha) = [[alpha I, A], [A^T, 0]]`. -/
noncomputable def lsScaledAugmentedMatrix {m n : ℕ} (alpha : ℝ)
    (A : Fin m → Fin n → ℝ) : Fin (m + n) → Fin (m + n) → ℝ :=
  Fin.append
    (fun i : Fin m => Fin.append (fun j : Fin m => alpha * idMatrix m i j) (A i))
    (fun j : Fin n => Fin.append (fun i : Fin m => A i j) (fun _ : Fin n => 0))
/-- Higham, 2nd ed., Chapter 20, equation (20.17): the scaled augmented
    coefficient matrix `C(alpha) = [[alpha I, A], [A^T, 0]]` is symmetric. -/
theorem lsScaledAugmentedMatrix_symmetric {m n : ℕ} (alpha : ℝ)
    (A : Fin m → Fin n → ℝ) :
    IsSymmetricFiniteMatrix (lsScaledAugmentedMatrix alpha A) := by
  intro p q
  refine Fin.addCases (motive := fun p : Fin (m + n) =>
    lsScaledAugmentedMatrix alpha A p q =
      lsScaledAugmentedMatrix alpha A q p) ?topRow ?bottomRow p
  · intro i
    refine Fin.addCases (motive := fun q : Fin (m + n) =>
      lsScaledAugmentedMatrix alpha A (Fin.castAdd n i) q =
        lsScaledAugmentedMatrix alpha A q (Fin.castAdd n i)) ?topLeft ?topRight q
    · intro j
      unfold lsScaledAugmentedMatrix
      by_cases hij : i = j
      · subst j
        simp [Fin.append_left, idMatrix]
      · have hji : j ≠ i := fun h => hij h.symm
        simp [Fin.append_left, idMatrix, hij, hji]
    · intro j
      simp [lsScaledAugmentedMatrix, Fin.append_left, Fin.append_right]
  · intro i
    refine Fin.addCases (motive := fun q : Fin (m + n) =>
      lsScaledAugmentedMatrix alpha A (Fin.natAdd m i) q =
        lsScaledAugmentedMatrix alpha A q (Fin.natAdd m i)) ?bottomLeft ?bottomRight q
    · intro j
      simp [lsScaledAugmentedMatrix, Fin.append_left, Fin.append_right]
    · intro j
      simp [lsScaledAugmentedMatrix, Fin.append_right]
/-- Specialization of the symmetric-eigenvector orthogonality lemma to the
    scaled augmented matrix `C(alpha)` from (20.17). -/
theorem lsScaledAugmentedMatrix_eigenvectors_sum_mul_eq_zero {m n : ℕ}
    {alpha lambda mu : ℝ} (A : Fin m → Fin n → ℝ)
    {x y : Fin (m + n) → ℝ}
    (hx : rectMatMulVec (lsScaledAugmentedMatrix alpha A) x =
      fun i => lambda * x i)
    (hy : rectMatMulVec (lsScaledAugmentedMatrix alpha A) y =
      fun i => mu * y i)
    (hlambda_mu : lambda ≠ mu) :
    (∑ i : Fin (m + n), x i * y i) = 0 :=
  isSymmetricFiniteMatrix_eigenvectors_sum_mul_eq_zero
    (lsScaledAugmentedMatrix_symmetric alpha A) hx hy hlambda_mu
/-- Higham, 2nd ed., Chapter 20, equation (20.17): at `alpha = 0`, the
    scaled augmented matrix is the `finSumFinEquiv` reindexing of the standard
    self-adjoint dilation `[[0, A], [A^T, 0]]`. -/
theorem lsScaledAugmentedMatrix_zero_eq_reindexed_rectSelfAdjointDilation
    {m n : ℕ} (A : Fin m → Fin n → ℝ) :
    lsScaledAugmentedMatrix 0 A =
      fun p q : Fin (m + n) =>
        rectSelfAdjointDilation A (finSumFinEquiv.symm p) (finSumFinEquiv.symm q) := by
  ext p q
  refine Fin.addCases (motive := fun p : Fin (m + n) =>
    lsScaledAugmentedMatrix 0 A p q =
      rectSelfAdjointDilation A (finSumFinEquiv.symm p) (finSumFinEquiv.symm q))
    ?topRow ?bottomRow p
  · intro i
    refine Fin.addCases (motive := fun q : Fin (m + n) =>
      lsScaledAugmentedMatrix 0 A (Fin.castAdd n i) q =
        rectSelfAdjointDilation A (finSumFinEquiv.symm (Fin.castAdd n i))
          (finSumFinEquiv.symm q)) ?topLeft ?topRight q
    · intro j
      simp [lsScaledAugmentedMatrix, rectSelfAdjointDilation, idMatrix]
    · intro j
      simp [lsScaledAugmentedMatrix, rectSelfAdjointDilation]
  · intro i
    refine Fin.addCases (motive := fun q : Fin (m + n) =>
      lsScaledAugmentedMatrix 0 A (Fin.natAdd m i) q =
        rectSelfAdjointDilation A (finSumFinEquiv.symm (Fin.natAdd m i))
          (finSumFinEquiv.symm q)) ?bottomLeft ?bottomRight q
    · intro j
      simp [lsScaledAugmentedMatrix, rectSelfAdjointDilation]
    · intro j
      simp [lsScaledAugmentedMatrix, rectSelfAdjointDilation]
/-- Component form of the scaled augmented system with coefficient matrix
    `C(alpha)` from equation (20.17). -/
def LSScaledAugmentedSystem {m n : ℕ} (alpha : ℝ)
    (A : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, alpha * r i + rectMatMulVec A x i = f i) ∧
  (∀ j : Fin n, ∑ i : Fin m, A i j * r i = g j)
/-- Matrix-vector multiplication by the scaled augmented matrix in (20.17). -/
theorem lsScaledAugmentedMatrix_mulVec {m n : ℕ} (alpha : ℝ)
    (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A) (Fin.append r x) =
      Fin.append
        (fun i : Fin m => alpha * r i + rectMatMulVec A x i)
        (fun j : Fin n => ∑ i : Fin m, A i j * r i) := by
  ext k
  refine Fin.addCases
    (motive := fun k : Fin (m + n) =>
      rectMatMulVec (lsScaledAugmentedMatrix alpha A) (Fin.append r x) k =
        Fin.append
          (fun i : Fin m => alpha * r i + rectMatMulVec A x i)
          (fun j : Fin n => ∑ i : Fin m, A i j * r i) k)
    ?left ?right k
  · intro i
    unfold rectMatMulVec lsScaledAugmentedMatrix
    rw [Fin.append_left, Fin.append_left, Fin.sum_univ_add]
    have hid :
        (∑ j : Fin m, (alpha * idMatrix m i j) * r j) = alpha * r i := by
      calc
        (∑ j : Fin m, (alpha * idMatrix m i j) * r j)
            = alpha * (∑ j : Fin m, idMatrix m i j * r j) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = alpha * r i := by
                rw [congrFun (idMatrix_mulVec m r) i]
    simp [Fin.append_left, Fin.append_right]
    rw [hid]
  · intro j
    unfold rectMatMulVec lsScaledAugmentedMatrix
    rw [Fin.append_right, Fin.append_right, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
/-- Higham, 2nd ed., Chapter 20, equation (20.17): at `alpha = 0`, the
    scaled augmented matrix-vector action is the `finSumFinEquiv` reindexing
    of the self-adjoint-dilation action on the paired vector `(r,x)`. -/
theorem lsScaledAugmentedMatrix_zero_mulVec_eq_reindexed_rectSelfAdjointDilation_sumBothVec
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) (x : Fin n → ℝ) :
    rectMatMulVec (lsScaledAugmentedMatrix 0 A) (Fin.append r x) =
      fun p : Fin (m + n) =>
        finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)
          (finSumFinEquiv.symm p) := by
  ext p
  rw [lsScaledAugmentedMatrix_mulVec]
  refine Fin.addCases
    (motive := fun p : Fin (m + n) =>
      Fin.append
          (fun i : Fin m => 0 * r i + rectMatMulVec A x i)
          (fun j : Fin n => ∑ i : Fin m, A i j * r i) p =
        finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)
          (finSumFinEquiv.symm p)) ?left ?right p
  · intro i
    rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
    simp [sumBothVec]
  · intro j
    rw [finiteMatVec_rectSelfAdjointDilation_sumBothVec]
    simp [sumBothVec]
/-- Higham, 2nd ed., Chapter 20, equation (20.17): the Rayleigh form of the
    zero-scaled augmented matrix `C(0)` on the source-indexed vector `[r; x]`
    is `2 * rᵀ A x`. This is the `Fin (m+n)` counterpart of the repository's
    self-adjoint-dilation quadratic-form identity used by the later
    (20.18)-(20.19) spectral route. -/
theorem lsScaledAugmentedMatrix_zero_quadraticForm_append_eq
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (r : Fin m → ℝ) (x : Fin n → ℝ) :
    finiteQuadraticForm (lsScaledAugmentedMatrix 0 A) (Fin.append r x) =
      2 * ∑ i : Fin m, r i * rectMatMulVec A x i := by
  classical
  have hswap :
      (∑ j : Fin n, x j * ∑ i : Fin m, A i j * r i) =
        ∑ i : Fin m, r i * ∑ j : Fin n, A i j * x j := by
    calc
      (∑ j : Fin n, x j * ∑ i : Fin m, A i j * r i)
          = ∑ j : Fin n, ∑ i : Fin m, x j * (A i j * r i) := by
              apply Finset.sum_congr rfl
              intro j _
              rw [Finset.mul_sum]
      _ = ∑ i : Fin m, ∑ j : Fin n, x j * (A i j * r i) := by
              rw [Finset.sum_comm]
      _ = ∑ i : Fin m, r i * ∑ j : Fin n, A i j * x j := by
              apply Finset.sum_congr rfl
              intro i _
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
  unfold finiteQuadraticForm
  rw [show finiteMatVec (lsScaledAugmentedMatrix 0 A) (Fin.append r x) =
      rectMatMulVec (lsScaledAugmentedMatrix 0 A) (Fin.append r x) by rfl]
  rw [lsScaledAugmentedMatrix_mulVec]
  rw [Fin.sum_univ_add]
  simp [Fin.append_left, Fin.append_right, rectMatMulVec, hswap]
  ring
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): the Rayleigh
    form of the zero-scaled source matrix `C(0)` on an arbitrary
    source-indexed vector is the Rayleigh form of the repository
    self-adjoint dilation under the `finSumFinEquiv` split. -/
theorem lsScaledAugmentedMatrix_zero_quadraticForm_eq_reindexed_rectSelfAdjointDilation
    {m n : ℕ} (A : Fin m → Fin n → ℝ) (z : Fin (m + n) → ℝ) :
    finiteQuadraticForm (lsScaledAugmentedMatrix 0 A) z =
      finiteQuadraticForm (rectSelfAdjointDilation A)
        (sumBothVec (fun i : Fin m => z (Fin.castAdd n i))
          (fun j : Fin n => z (Fin.natAdd m j))) := by
  classical
  let r : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  have hz : z = Fin.append r x := by
    ext p
    refine Fin.addCases
      (motive := fun p : Fin (m + n) => z p = Fin.append r x p)
      ?left ?right p
    · intro i
      simp [r, Fin.append_left]
    · intro j
      simp [x, Fin.append_right]
  calc
    finiteQuadraticForm (lsScaledAugmentedMatrix 0 A) z
        = finiteQuadraticForm (lsScaledAugmentedMatrix 0 A) (Fin.append r x) := by
            rw [hz]
    _ = 2 * ∑ i : Fin m, r i * rectMatMulVec A x i :=
        lsScaledAugmentedMatrix_zero_quadraticForm_append_eq A r x
    _ = finiteQuadraticForm (rectSelfAdjointDilation A) (sumBothVec r x) := by
        rw [finiteQuadraticForm_rectSelfAdjointDilation_sumBothVec]
    _ = finiteQuadraticForm (rectSelfAdjointDilation A)
          (sumBothVec (fun i : Fin m => z (Fin.castAdd n i))
            (fun j : Fin n => z (Fin.natAdd m j))) := by rfl
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): a rectangular
    operator-2 bound for `A` gives the source-indexed Loewner upper bound
    `C(0) <= L I`. This is a quadratic-form control bridge for the later
    spectral route, not the full eigenvalue multiplicity theorem. -/
theorem lsScaledAugmentedMatrix_zero_finiteLoewnerLe_scalar_id_of_rectOpNorm2Le
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hA : rectOpNorm2Le A L) :
    finiteLoewnerLe (lsScaledAugmentedMatrix 0 A)
      (fun p q : Fin (m + n) => L * finiteIdMatrix p q) := by
  classical
  intro z
  let r : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  let w : Fin m ⊕ Fin n → ℝ := sumBothVec r x
  have hnorm_sq : finiteVecNorm2Sq z = finiteVecNorm2Sq w := by
    unfold finiteVecNorm2Sq w r x sumBothVec
    rw [Fin.sum_univ_add, Fintype.sum_sum_type]
    simp
  have hq_id :
      finiteQuadraticForm (fun p q : Fin (m + n) => L * finiteIdMatrix p q) z =
        finiteQuadraticForm (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) w := by
    rw [finiteQuadraticForm_smul_finiteIdMatrix,
      finiteQuadraticForm_smul_finiteIdMatrix, hnorm_sq]
  calc
    finiteQuadraticForm (lsScaledAugmentedMatrix 0 A) z
        = finiteQuadraticForm (rectSelfAdjointDilation A) w := by
            simpa [w, r, x] using
              lsScaledAugmentedMatrix_zero_quadraticForm_eq_reindexed_rectSelfAdjointDilation A z
    _ ≤ finiteQuadraticForm (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) w :=
        finiteLoewnerLe_rectSelfAdjointDilation_of_rectOpNorm2Le A hL hA w
    _ = finiteQuadraticForm (fun p q : Fin (m + n) => L * finiteIdMatrix p q) z :=
        hq_id.symm
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): a rectangular
    operator-2 bound for `A` also gives the lower Loewner side for the
    zero-scaled source matrix, written as `-C(0) <= L I`. -/
theorem lsScaledAugmentedMatrix_zero_neg_finiteLoewnerLe_scalar_id_of_rectOpNorm2Le
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hA : rectOpNorm2Le A L) :
    finiteLoewnerLe (fun p q : Fin (m + n) => -lsScaledAugmentedMatrix 0 A p q)
      (fun p q : Fin (m + n) => L * finiteIdMatrix p q) := by
  classical
  intro z
  let r : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  let w : Fin m ⊕ Fin n → ℝ := sumBothVec r x
  have hnorm_sq : finiteVecNorm2Sq z = finiteVecNorm2Sq w := by
    unfold finiteVecNorm2Sq w r x sumBothVec
    rw [Fin.sum_univ_add, Fintype.sum_sum_type]
    simp
  have hq_id :
      finiteQuadraticForm (fun p q : Fin (m + n) => L * finiteIdMatrix p q) z =
        finiteQuadraticForm (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) w := by
    rw [finiteQuadraticForm_smul_finiteIdMatrix,
      finiteQuadraticForm_smul_finiteIdMatrix, hnorm_sq]
  have hq_neg :
      finiteQuadraticForm
          (fun p q : Fin (m + n) => -lsScaledAugmentedMatrix 0 A p q) z =
        finiteQuadraticForm
          (fun a b : Fin m ⊕ Fin n => -rectSelfAdjointDilation A a b) w := by
    rw [finiteQuadraticForm_neg, finiteQuadraticForm_neg]
    congr 1
    simpa [w, r, x] using
      lsScaledAugmentedMatrix_zero_quadraticForm_eq_reindexed_rectSelfAdjointDilation A z
  calc
    finiteQuadraticForm
        (fun p q : Fin (m + n) => -lsScaledAugmentedMatrix 0 A p q) z
        = finiteQuadraticForm
            (fun a b : Fin m ⊕ Fin n => -rectSelfAdjointDilation A a b) w := hq_neg
    _ ≤ finiteQuadraticForm (fun a b : Fin m ⊕ Fin n => L * finiteIdMatrix a b) w :=
        finiteLoewnerLe_neg_rectSelfAdjointDilation_of_rectOpNorm2Le A hL hA w
    _ = finiteQuadraticForm (fun p q : Fin (m + n) => L * finiteIdMatrix p q) z :=
        hq_id.symm
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): any finite
    operator-2 upper bound for the repository self-adjoint dilation transfers
    to the source-indexed zero-scaled augmented matrix `C(0)`. This is an
    operator-bound bridge, not the full spectral multiplicity or
    condition-number formula. -/
theorem lsScaledAugmentedMatrix_zero_finiteOpNorm2Le_of_rectSelfAdjointDilation
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {L : ℝ}
    (hD : finiteOpNorm2Le (rectSelfAdjointDilation A) L) :
    finiteOpNorm2Le (lsScaledAugmentedMatrix 0 A) L := by
  classical
  intro z
  let r : Fin m → ℝ := fun i => z (Fin.castAdd n i)
  let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  have hz : z = Fin.append r x := by
    ext p
    refine Fin.addCases
      (motive := fun p : Fin (m + n) => z p = Fin.append r x p)
      ?left ?right p
    · intro i
      simp [r, Fin.append_left]
    · intro j
      simp [x, Fin.append_right]
  have hnorm_z_sq :
      finiteVecNorm2Sq z = finiteVecNorm2Sq (sumBothVec r x) := by
    rw [hz]
    unfold finiteVecNorm2Sq sumBothVec
    rw [Fin.sum_univ_add, Fintype.sum_sum_type]
    simp [Fin.append_left, Fin.append_right]
  have hnorm_z : finiteVecNorm2 z = finiteVecNorm2 (sumBothVec r x) := by
    unfold finiteVecNorm2
    rw [hnorm_z_sq]
  have haction_sq :
      finiteVecNorm2Sq (finiteMatVec (lsScaledAugmentedMatrix 0 A) z) =
        finiteVecNorm2Sq
          (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)) := by
    rw [hz]
    unfold finiteVecNorm2Sq
    rw [show finiteMatVec (lsScaledAugmentedMatrix 0 A) (Fin.append r x) =
        rectMatMulVec (lsScaledAugmentedMatrix 0 A) (Fin.append r x) by rfl]
    rw [lsScaledAugmentedMatrix_zero_mulVec_eq_reindexed_rectSelfAdjointDilation_sumBothVec]
    exact Fintype.sum_equiv finSumFinEquiv.symm
      (fun p : Fin (m + n) =>
        (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)
          (finSumFinEquiv.symm p)) ^ 2)
      (fun q : Fin m ⊕ Fin n =>
        (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x) q) ^ 2)
      (by intro p; rfl)
  have haction :
      finiteVecNorm2 (finiteMatVec (lsScaledAugmentedMatrix 0 A) z) =
        finiteVecNorm2
          (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)) := by
    unfold finiteVecNorm2
    rw [haction_sq]
  calc
    finiteVecNorm2 (finiteMatVec (lsScaledAugmentedMatrix 0 A) z)
        =
          finiteVecNorm2
            (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)) := haction
    _ ≤ L * finiteVecNorm2 (sumBothVec r x) := hD (sumBothVec r x)
    _ = L * finiteVecNorm2 z := by rw [hnorm_z]
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): any finite
    operator-2 upper bound for the source-indexed zero-scaled augmented
    matrix `C(0)` transfers back to the repository self-adjoint dilation.
    Together with the forward bridge, this gives an exact operator-bound
    equivalence across the source/repository reindexing, not the full
    spectral multiplicity or condition-number formula. -/
theorem rectSelfAdjointDilation_finiteOpNorm2Le_of_lsScaledAugmentedMatrix_zero
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {L : ℝ}
    (hC : finiteOpNorm2Le (lsScaledAugmentedMatrix 0 A) L) :
    finiteOpNorm2Le (rectSelfAdjointDilation A) L := by
  classical
  intro w
  let r : Fin m → ℝ := fun i => w (Sum.inl i)
  let x : Fin n → ℝ := fun j => w (Sum.inr j)
  let z : Fin (m + n) → ℝ := Fin.append r x
  have hw : w = sumBothVec r x := by
    ext a
    cases a <;> rfl
  have hnorm_sq :
      finiteVecNorm2Sq w = finiteVecNorm2Sq z := by
    rw [hw]
    unfold finiteVecNorm2Sq sumBothVec z
    rw [Fintype.sum_sum_type, Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  have hnorm : finiteVecNorm2 w = finiteVecNorm2 z := by
    unfold finiteVecNorm2
    rw [hnorm_sq]
  have hCaction :
      finiteMatVec (lsScaledAugmentedMatrix 0 A) z =
        fun p : Fin (m + n) =>
          finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)
            (finSumFinEquiv.symm p) := by
    change rectMatMulVec (lsScaledAugmentedMatrix 0 A) z = _
    simpa [z] using
      lsScaledAugmentedMatrix_zero_mulVec_eq_reindexed_rectSelfAdjointDilation_sumBothVec
        A r x
  have haction_sq :
      finiteVecNorm2Sq (finiteMatVec (rectSelfAdjointDilation A) w) =
        finiteVecNorm2Sq (finiteMatVec (lsScaledAugmentedMatrix 0 A) z) := by
    rw [hw]
    unfold finiteVecNorm2Sq
    rw [hCaction]
    exact Fintype.sum_equiv finSumFinEquiv
      (fun q : Fin m ⊕ Fin n =>
        (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x) q) ^ 2)
      (fun p : Fin (m + n) =>
        (finiteMatVec (rectSelfAdjointDilation A) (sumBothVec r x)
          (finSumFinEquiv.symm p)) ^ 2)
      (by intro q; simp)
  have haction :
      finiteVecNorm2 (finiteMatVec (rectSelfAdjointDilation A) w) =
        finiteVecNorm2 (finiteMatVec (lsScaledAugmentedMatrix 0 A) z) := by
    unfold finiteVecNorm2
    rw [haction_sq]
  calc
    finiteVecNorm2 (finiteMatVec (rectSelfAdjointDilation A) w)
        = finiteVecNorm2 (finiteMatVec (lsScaledAugmentedMatrix 0 A) z) := haction
    _ ≤ L * finiteVecNorm2 z := hC z
    _ = L * finiteVecNorm2 w := by rw [hnorm]
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): the finite
    operator-2 upper-bound predicate is invariant under the reindexing between
    the zero-scaled source matrix `C(0)` and the repository self-adjoint
    dilation `[[0,A],[Aᵀ,0]]`. -/
theorem lsScaledAugmentedMatrix_zero_finiteOpNorm2Le_iff_rectSelfAdjointDilation
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {L : ℝ} :
    finiteOpNorm2Le (lsScaledAugmentedMatrix 0 A) L ↔
      finiteOpNorm2Le (rectSelfAdjointDilation A) L := by
  constructor
  · exact rectSelfAdjointDilation_finiteOpNorm2Le_of_lsScaledAugmentedMatrix_zero A
  · exact lsScaledAugmentedMatrix_zero_finiteOpNorm2Le_of_rectSelfAdjointDilation A
/-- Higham, 2nd ed., Chapter 20, equations (20.17)-(20.19): a Frobenius
    bound for `A` gives a conservative finite operator-2 bound for the
    zero-scaled augmented matrix `C(0)`. This is a reusable upper-bound
    corollary, not the sharp spectral norm statement. -/
theorem lsScaledAugmentedMatrix_zero_finiteOpNorm2Le_of_frobNormRect_le
    {m n : ℕ} (A : Fin m → Fin n → ℝ) {L : ℝ}
    (hL : 0 ≤ L) (hF : frobNormRect A ≤ L) :
    finiteOpNorm2Le (lsScaledAugmentedMatrix 0 A) (Real.sqrt 2 * L) :=
  lsScaledAugmentedMatrix_zero_finiteOpNorm2Le_of_rectSelfAdjointDilation A
    (finiteOpNorm2Le_rectSelfAdjointDilation_of_frobNormRect_le A hL hF)
/-- The component equations for the scaled augmented system are exactly the
    block matrix-vector equation using `C(alpha)` from (20.17). -/
theorem LSScaledAugmentedSystem.iff_scaledAugmentedMatrix_mulVec {m n : ℕ}
    (alpha : ℝ) (A : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ) :
    LSScaledAugmentedSystem alpha A f g r x ↔
      rectMatMulVec (lsScaledAugmentedMatrix alpha A) (Fin.append r x) =
        Fin.append f g := by
  constructor
  · intro h
    rw [lsScaledAugmentedMatrix_mulVec]
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (m + n) =>
        Fin.append
            (fun i : Fin m => alpha * r i + rectMatMulVec A x i)
            (fun j : Fin n => ∑ i : Fin m, A i j * r i) k =
          Fin.append f g k)
      ?left ?right k
    · intro i
      simp [Fin.append_left, h.1 i]
    · intro j
      simp [Fin.append_right, h.2 j]
  · intro h
    constructor
    · intro i
      have hi := congrFun h (Fin.castAdd n i)
      rw [congrFun (lsScaledAugmentedMatrix_mulVec alpha A r x) (Fin.castAdd n i)] at hi
      simpa [Fin.append_left] using hi
    · intro j
      have hj := congrFun h (Fin.natAdd m j)
      rw [congrFun (lsScaledAugmentedMatrix_mulVec alpha A r x) (Fin.natAdd m j)] at hj
      simpa [Fin.append_right] using hj
/-- The unscaled case `alpha = 1` recovers the existing arbitrary augmented
    system (20.15). -/
theorem LSScaledAugmentedSystem.one_iff_augmentedSystem {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r : Fin m → ℝ) (x : Fin n → ℝ) :
    LSScaledAugmentedSystem (1 : ℝ) A f g r x ↔
      LSAugmentedSystem A f g r x := by
  constructor
  · intro h
    constructor
    · intro i
      simpa using h.1 i
    · exact h.2
  · intro h
    constructor
    · intro i
      simpa using h.1 i
    · exact h.2
private theorem lsAugmentedInverseAction_Aplus_mul_A {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (gramInv : Fin n → Fin n → ℝ)
    (hAplus : ∀ j i, Aplus j i = ∑ k : Fin n, gramInv j k * A i k)
    (hGramInv : IsInverse n (rectLSGram A) gramInv) :
    ∀ j k : Fin n, ∑ i : Fin m, Aplus j i * A i k =
      if j = k then 1 else 0 := by
  intro j k
  calc
    ∑ i : Fin m, Aplus j i * A i k
        = ∑ i : Fin m, (∑ p : Fin n, gramInv j p * A i p) * A i k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hAplus j i]
    _ = ∑ i : Fin m, ∑ p : Fin n, (gramInv j p * A i p) * A i k := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
    _ = ∑ p : Fin n, ∑ i : Fin m, (gramInv j p * A i p) * A i k := by
            rw [Finset.sum_comm]
    _ = ∑ p : Fin n, gramInv j p * rectLSGram A p k := by
            apply Finset.sum_congr rfl
            intro p _
            unfold rectLSGram
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = if j = k then 1 else 0 := hGramInv.1 j k
private theorem lsAugmentedInverseAction_gram_mul_Aplus {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (gramInv : Fin n → Fin n → ℝ)
    (hAplus : ∀ j i, Aplus j i = ∑ k : Fin n, gramInv j k * A i k)
    (hGramInv : IsInverse n (rectLSGram A) gramInv) :
    ∀ j : Fin n, ∀ i : Fin m,
      ∑ k : Fin n, rectLSGram A j k * Aplus k i = A i j := by
  intro j i
  calc
    ∑ k : Fin n, rectLSGram A j k * Aplus k i
        = ∑ k : Fin n, rectLSGram A j k *
            (∑ p : Fin n, gramInv k p * A i p) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [hAplus k i]
    _ = ∑ p : Fin n, (∑ k : Fin n, rectLSGram A j k * gramInv k p) * A i p := by
            simp_rw [Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro p _
            apply Finset.sum_congr rfl
            intro k _
            ring
    _ = ∑ p : Fin n, (if j = p then 1 else 0) * A i p := by
            apply Finset.sum_congr rfl
            intro p _
            rw [hGramInv.2 j p]
    _ = A i j := by
            simp
/-- Higham, 2nd ed., Chapter 20, equation (20.6), exact block action:
    if `A^+ = (A^T A)^{-1} A^T`, the supplied Gram inverse is a two-sided
    inverse of `A^T A`, and that inverse is symmetric, then the displayed
    vector produced by (20.6) solves the arbitrary augmented system
    `[I A; A^T 0][r; x] = [u; v]`.

    This proves the algebraic inverse-action formula used by Theorem 20.2.
    It intentionally leaves the full-rank/SVD theorem that supplies `A^+`,
    `gramInv`, and symmetry as a separate pseudoinverse foundation. -/
theorem LSAugmentedSystem.of_eq20_6_inverse_action {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (Aplus : Fin n → Fin m → ℝ)
    (gramInv : Fin n → Fin n → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAplus : ∀ j i, Aplus j i = ∑ k : Fin n, gramInv j k * A i k)
    (hGramInv : IsInverse n (rectLSGram A) gramInv)
    (hGramInv_symm : ∀ j k : Fin n, gramInv j k = gramInv k j) :
    LSAugmentedSystem A u v
      (lsAugmentedInverseActionTop A Aplus u v)
      (lsAugmentedInverseActionBottom Aplus gramInv u v) := by
  have hAplusA :=
    lsAugmentedInverseAction_Aplus_mul_A A Aplus gramInv hAplus hGramInv
  have hGramAplus : ∀ j : Fin n, ∀ i : Fin m,
      ∑ k : Fin n, rectLSGram A j k * Aplus k i = A i j := by
    exact lsAugmentedInverseAction_gram_mul_Aplus A Aplus gramInv hAplus hGramInv
  constructor
  · intro i
    have htop_right :
        (∑ j : Fin n, Aplus j i * v j) =
          rectMatMulVec A (matMulVec n gramInv v) i := by
      calc
        ∑ j : Fin n, Aplus j i * v j
            = ∑ j : Fin n, (∑ k : Fin n, gramInv j k * A i k) * v j := by
                apply Finset.sum_congr rfl
                intro j _
                rw [hAplus j i]
        _ = ∑ j : Fin n, ∑ k : Fin n, (gramInv j k * A i k) * v j := by
                apply Finset.sum_congr rfl
                intro j _
                rw [Finset.sum_mul]
        _ = ∑ k : Fin n, ∑ j : Fin n, (gramInv j k * A i k) * v j := by
                rw [Finset.sum_comm]
        _ = ∑ k : Fin n, A i k * (∑ j : Fin n, gramInv k j * v j) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                rw [hGramInv_symm j k]
                ring
        _ = rectMatMulVec A (matMulVec n gramInv v) i := by
                rfl
    have hbottom_action :
        rectMatMulVec A (lsAugmentedInverseActionBottom Aplus gramInv u v) i =
          rectMatMulVec A (rectMatMulVec Aplus u) i -
            rectMatMulVec A (matMulVec n gramInv v) i := by
      unfold lsAugmentedInverseActionBottom rectMatMulVec
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    unfold lsAugmentedInverseActionTop
    rw [hbottom_action, htop_right]
    ring
  · intro j
    have hleft :
        (∑ i : Fin m, A i j * rectMatMulVec A (rectMatMulVec Aplus u) i) =
          ∑ i : Fin m, A i j * u i := by
      calc
        ∑ i : Fin m, A i j * rectMatMulVec A (rectMatMulVec Aplus u) i
            = ∑ i : Fin m, A i j *
                (∑ k : Fin n, A i k * rectMatMulVec Aplus u k) := by
                rfl
        _ = ∑ i : Fin m, ∑ k : Fin n,
              A i j * (A i k * rectMatMulVec Aplus u k) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ = ∑ k : Fin n, ∑ i : Fin m,
              A i j * (A i k * rectMatMulVec Aplus u k) := by
                rw [Finset.sum_comm]
        _ = ∑ k : Fin n, (∑ i : Fin m, A i j * A i k) *
              rectMatMulVec Aplus u k := by
                apply Finset.sum_congr rfl
                intro k _
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ k : Fin n, rectLSGram A j k * rectMatMulVec Aplus u k := by
                rfl
        _ = ∑ i : Fin m, (∑ k : Fin n, rectLSGram A j k * Aplus k i) * u i := by
                unfold rectMatMulVec
                simp_rw [Finset.mul_sum, Finset.sum_mul]
                rw [Finset.sum_comm]
                apply Finset.sum_congr rfl
                intro i _
                apply Finset.sum_congr rfl
                intro k _
                ring
        _ = ∑ i : Fin m, A i j * u i := by
                apply Finset.sum_congr rfl
                intro i _
                rw [hGramAplus j i]
    have hright :
        (∑ i : Fin m, A i j * (∑ k : Fin n, Aplus k i * v k)) = v j := by
      calc
        ∑ i : Fin m, A i j * (∑ k : Fin n, Aplus k i * v k)
            = ∑ i : Fin m, ∑ k : Fin n, A i j * (Aplus k i * v k) := by
                apply Finset.sum_congr rfl
                intro i _
                rw [Finset.mul_sum]
        _ = ∑ k : Fin n, ∑ i : Fin m, A i j * (Aplus k i * v k) := by
                rw [Finset.sum_comm]
        _ = ∑ k : Fin n, (∑ i : Fin m, Aplus k i * A i j) * v k := by
                apply Finset.sum_congr rfl
                intro k _
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = ∑ k : Fin n, (if k = j then 1 else 0) * v k := by
                apply Finset.sum_congr rfl
                intro k _
                rw [hAplusA k j]
        _ = v j := by
                simp
    unfold lsAugmentedInverseActionTop
    calc
      ∑ i : Fin m,
          A i j *
            (u i - rectMatMulVec A (rectMatMulVec Aplus u) i +
              ∑ k : Fin n, Aplus k i * v k)
          =
            ∑ i : Fin m, A i j * u i -
              ∑ i : Fin m, A i j *
                rectMatMulVec A (rectMatMulVec Aplus u) i +
              ∑ i : Fin m, A i j *
                (∑ k : Fin n, Aplus k i * v k) := by
              simp_rw [mul_add, mul_sub]
              rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = v j := by
              rw [hleft, hright]
              ring
/-- Determinant-facing form of Higham, 2nd ed., Chapter 20, equation (20.6):
    if `det(A^T A) ≠ 0`, the concrete tables
    `A^+ = (A^T A)^{-1} A^T` and `(A^T A)^{-1}` make the displayed block
    action solve the augmented system. -/
theorem LSAugmentedSystem.of_eq20_6_nonsing_gram {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hdet : Matrix.det (rectLSGram A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    LSAugmentedSystem A u v
      (lsAugmentedInverseActionTop A (lsAplusOfGramNonsingInv A) u v)
      (lsAugmentedInverseActionBottom
        (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A) u v) := by
  exact
    LSAugmentedSystem.of_eq20_6_inverse_action A
      (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A) u v
      (by
        intro j i
        rfl)
      (lsGramNonsingInv_isInverse_of_det_ne_zero A hdet)
      (by
        intro j k
        exact lsGramNonsingInv_symmetric A j k)
/-- Full-column-rank form of Higham, 2nd ed., Chapter 20, equation (20.6):
    the concrete Gram inverse and pseudoinverse solve the augmented system
    when `x ↦ A x` is injective. -/
theorem LSAugmentedSystem.of_eq20_6_full_column_rank {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    LSAugmentedSystem A u v
      (lsAugmentedInverseActionTop A (lsAplusOfGramNonsingInv A) u v)
      (lsAugmentedInverseActionBottom
        (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A) u v) := by
  exact
    LSAugmentedSystem.of_eq20_6_nonsing_gram A u v
      (rectLSGram_det_ne_zero_of_rectMatMulVec_injective A hA)
/-- Full-column-rank Gram pseudoinverse support: a nonzero Gram determinant
    makes `(AᵀA)^{-1}Aᵀ` a left inverse for `A`. -/
theorem lsAplusOfGramNonsingInv_mul_self_of_det_ne_zero {m n : ℕ}
    (A : Fin m → Fin n → ℝ)
    (hdet : Matrix.det (rectLSGram A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    rectMatMul (lsAplusOfGramNonsingInv A) A = idMatrix n := by
  ext j k
  have hentry :=
    lsAugmentedInverseAction_Aplus_mul_A
      A (lsAplusOfGramNonsingInv A) (lsGramNonsingInv A)
      (by intro j i; rfl)
      (lsGramNonsingInv_isInverse_of_det_ne_zero A hdet) j k
  simpa [rectMatMul, idMatrix] using hentry
/-- Full-column-rank Gram pseudoinverse package for the reduced Wedin route:
    injectivity of `x ↦ A*x` supplies both the left inverse and symmetric
    range-projection fields required by the repository Moore--Penrose-style
    least-squares interfaces. -/
theorem lsAplusOfGramNonsingInv_left_inverse_and_projection_symmetric
    {m n : ℕ} (A : Fin m → Fin n → ℝ)
    (hA : Function.Injective (rectMatMulVec A)) :
    rectMatMul (lsAplusOfGramNonsingInv A) A = idMatrix n ∧
      IsSymmetricFiniteMatrix (rectMatMul A (lsAplusOfGramNonsingInv A)) := by
  constructor
  · exact
      lsAplusOfGramNonsingInv_mul_self_of_det_ne_zero A
        (rectLSGram_det_ne_zero_of_rectMatMulVec_injective A hA)
  · exact lsAplusOfGramNonsingInv_projection_symmetric A
private theorem matMulVec_eq_zero_of_inverse {n : ℕ}
    (T Tinv : Fin n → Fin n → ℝ) (hInv : IsInverse n T Tinv)
    {x : Fin n → ℝ} (hx : ∀ i : Fin n, matMulVec n T x i = 0) :
    x = 0 := by
  ext i
  calc
    x i = matMulVec n (idMatrix n) x i := by rw [matMulVec_id]
    _ = matMulVec n (matMul n Tinv T) x i := by
          have hmat : matMul n Tinv T = idMatrix n := by
            ext a b
            exact hInv.1 a b
          rw [hmat]
    _ = matMulVec n Tinv (matMulVec n T x) i := by
          exact matMulVec_matMul n Tinv T x i
    _ = matMulVec n Tinv 0 i := by
          congr 1
          ext j
          exact hx j
    _ = 0 := by
          unfold matMulVec
          simp
/-- Uniqueness for Higham's augmented least-squares system when `Aᵀ A` has a
    supplied inverse. -/
theorem LSAugmentedSystem.eq_of_gram_inverse {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (f : Fin m → ℝ) (g : Fin n → ℝ)
    (r₁ r₂ : Fin m → ℝ) (x₁ x₂ : Fin n → ℝ)
    (gramInv : Fin n → Fin n → ℝ)
    (hGramInv : IsInverse n (rectLSGram A) gramInv)
    (h₁ : LSAugmentedSystem A f g r₁ x₁)
    (h₂ : LSAugmentedSystem A f g r₂ x₂) :
    r₁ = r₂ ∧ x₁ = x₂ := by
  let dr : Fin m → ℝ := fun i => r₁ i - r₂ i
  let dx : Fin n → ℝ := fun j => x₁ j - x₂ j
  have hrow : ∀ i : Fin m, dr i + rectMatMulVec A dx i = 0 := by
    intro i
    have htop₁ := h₁.1 i
    have htop₂ := h₂.1 i
    have hsum :
        (∑ j : Fin n, A i j * (x₁ j - x₂ j)) =
          (∑ j : Fin n, A i j * x₁ j) -
            (∑ j : Fin n, A i j * x₂ j) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    calc
      dr i + rectMatMulVec A dx i
          = (r₁ i + rectMatMulVec A x₁ i) -
              (r₂ i + rectMatMulVec A x₂ i) := by
              unfold dr dx rectMatMulVec
              rw [hsum]
              ring
      _ = f i - f i := by
              rw [htop₁, htop₂]
      _ = 0 := by ring
  have hcol : ∀ j : Fin n, ∑ i : Fin m, A i j * dr i = 0 := by
    intro j
    have hbot₁ := h₁.2 j
    have hbot₂ := h₂.2 j
    have hsum :
        (∑ i : Fin m, A i j * (r₁ i - r₂ i)) =
          (∑ i : Fin m, A i j * r₁ i) -
            (∑ i : Fin m, A i j * r₂ i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      ∑ i : Fin m, A i j * dr i
          = (∑ i : Fin m, A i j * r₁ i) -
              (∑ i : Fin m, A i j * r₂ i) := by
              unfold dr
              exact hsum
      _ = g j - g j := by
              rw [hbot₁, hbot₂]
      _ = 0 := by ring
  have hgram_zero : ∀ j : Fin n, matMulVec n (rectLSGram A) dx j = 0 := by
    intro j
    have hrepr :=
      congrFun (rectLSGram_mulVec_eq_transpose_rectMatMulVec A dx) j
    calc
      matMulVec n (rectLSGram A) dx j
          = ∑ i : Fin m, A i j * rectMatMulVec A dx i := hrepr
      _ = ∑ i : Fin m, A i j * (-dr i) := by
              apply Finset.sum_congr rfl
              intro i _
              have hi := hrow i
              have hdx : rectMatMulVec A dx i = -dr i := by
                linarith
              rw [hdx]
      _ = -∑ i : Fin m, A i j * dr i := by
              rw [← Finset.sum_neg_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := by
              rw [hcol j]
              ring
  have hdx_zero : dx = 0 :=
    matMulVec_eq_zero_of_inverse (rectLSGram A) gramInv hGramInv hgram_zero
  have hx_eq : x₁ = x₂ := by
    ext j
    have hj : x₁ j - x₂ j = 0 := by
      simpa [dx] using congrFun hdx_zero j
    linarith
  have hdr_zero : ∀ i : Fin m, dr i = 0 := by
    intro i
    have hi := hrow i
    have hdxi : rectMatMulVec A dx i = 0 := by
      rw [hdx_zero]
      unfold rectMatMulVec
      simp
    linarith
  have hr_eq : r₁ = r₂ := by
    ext i
    have hi := hdr_zero i
    unfold dr at hi
    linarith
  exact ⟨hr_eq, hx_eq⟩
/-- Subtract an exact and a perturbed augmented least-squares system.  The
    resulting difference is exactly Higham's right-hand side in (20.6). -/
theorem LSAugmentedSystem.difference_of_perturbed {m n : ℕ}
    (A DeltaA : Fin m → Fin n → ℝ) (b Deltab : Fin m → ℝ)
    (r s : Fin m → ℝ) (x y : Fin n → ℝ)
    (hExact : LSAugmentedSystem A b (0 : Fin n → ℝ) r x)
    (hPert :
      LSAugmentedSystem (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i) (0 : Fin n → ℝ) s y) :
    LSAugmentedSystem A (lsEq20_6RhsTop DeltaA Deltab y)
      (lsEq20_6RhsBottom DeltaA s)
      (fun i => s i - r i) (fun j => y j - x j) := by
  constructor
  · intro i
    have hsplitPert :
        rectMatMulVec (fun i j => A i j + DeltaA i j) y i =
          rectMatMulVec A y i + rectMatMulVec DeltaA y i := by
      unfold rectMatMulVec
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hpertTop : s i + rectMatMulVec A y i +
        rectMatMulVec DeltaA y i = b i + Deltab i := by
      have hp := hPert.1 i
      rw [hsplitPert] at hp
      linarith
    have hsub :
        rectMatMulVec A (fun j => y j - x j) i =
          rectMatMulVec A y i - rectMatMulVec A x i := by
      exact congrFun (rectMatMulVec_sub A y x) i
    calc
      (s i - r i) + rectMatMulVec A (fun j => y j - x j) i
          =
            (s i + rectMatMulVec A y i + rectMatMulVec DeltaA y i) -
              (r i + rectMatMulVec A x i) -
              rectMatMulVec DeltaA y i := by
              rw [hsub]
              ring
      _ = (b i + Deltab i) - b i - rectMatMulVec DeltaA y i := by
              rw [hpertTop, hExact.1 i]
      _ = lsEq20_6RhsTop DeltaA Deltab y i := by
              unfold lsEq20_6RhsTop
              ring
  · intro j
    have hsplitPert :
        (∑ i : Fin m, (A i j + DeltaA i j) * s i) =
          (∑ i : Fin m, A i j * s i) +
            (∑ i : Fin m, DeltaA i j * s i) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hpertBottom :
        (∑ i : Fin m, A i j * s i) +
          (∑ i : Fin m, DeltaA i j * s i) = 0 := by
      have hp := hPert.2 j
      simp at hp
      rw [hsplitPert] at hp
      exact hp
    have hdiff :
        (∑ i : Fin m, A i j * (s i - r i)) =
          (∑ i : Fin m, A i j * s i) -
            (∑ i : Fin m, A i j * r i) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      ∑ i : Fin m, A i j * (s i - r i)
          =
            (∑ i : Fin m, A i j * s i) -
              (∑ i : Fin m, A i j * r i) := hdiff
      _ = ∑ i : Fin m, A i j * s i := by
              have hExactBot : (∑ i : Fin m, A i j * r i) = 0 := by
                simpa using hExact.2 j
              rw [hExactBot]
              ring
      _ = -∑ i : Fin m, DeltaA i j * s i := by
              linarith
      _ = lsEq20_6RhsBottom DeltaA s j := by
              rfl
/-- The positive branch in Björck's eigenvalue formula (20.18) for the scaled
    augmented matrix. -/
noncomputable def lsScaledAugmentedEigenvaluePlus (alpha sigma : ℝ) : ℝ :=
  alpha / 2 + Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2)
/-- The negative branch in Björck's eigenvalue formula (20.18) for the scaled
    augmented matrix. -/
noncomputable def lsScaledAugmentedEigenvalueMinus (alpha sigma : ℝ) : ℝ :=
  alpha / 2 - Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2)
/-- The positive branch in (20.18) satisfies the scalar quadratic associated
    with a singular value `sigma`: `lambda^2 - alpha lambda - sigma^2 = 0`. -/
theorem lsScaledAugmentedEigenvaluePlus_quadratic (alpha sigma : ℝ) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ^ 2 -
        alpha * lsScaledAugmentedEigenvaluePlus alpha sigma - sigma ^ 2 = 0 := by
  unfold lsScaledAugmentedEigenvaluePlus
  ring_nf
  have hrad : 0 ≤ alpha ^ 2 * (1 / 4) + sigma ^ 2 := by positivity
  have hsqrt : (Real.sqrt (alpha ^ 2 * (1 / 4) + sigma ^ 2)) ^ 2 =
      alpha ^ 2 * (1 / 4) + sigma ^ 2 :=
    Real.sq_sqrt hrad
  rw [hsqrt]
  ring
/-- The negative branch in (20.18) satisfies the scalar quadratic associated
    with a singular value `sigma`: `lambda^2 - alpha lambda - sigma^2 = 0`. -/
theorem lsScaledAugmentedEigenvalueMinus_quadratic (alpha sigma : ℝ) :
    lsScaledAugmentedEigenvalueMinus alpha sigma ^ 2 -
        alpha * lsScaledAugmentedEigenvalueMinus alpha sigma - sigma ^ 2 = 0 := by
  unfold lsScaledAugmentedEigenvalueMinus
  ring_nf
  have hrad : 0 ≤ alpha ^ 2 * (1 / 4) + sigma ^ 2 := by positivity
  have hsqrt : (Real.sqrt (alpha ^ 2 * (1 / 4) + sigma ^ 2)) ^ 2 =
      alpha ^ 2 * (1 / 4) + sigma ^ 2 :=
    Real.sq_sqrt hrad
  rw [hsqrt]
  ring
/-- The two scalar branches in (20.18) sum to the scaling parameter `alpha`. -/
theorem lsScaledAugmentedEigenvaluePlus_add_minus (alpha sigma : ℝ) :
    lsScaledAugmentedEigenvaluePlus alpha sigma +
        lsScaledAugmentedEigenvalueMinus alpha sigma = alpha := by
  unfold lsScaledAugmentedEigenvaluePlus lsScaledAugmentedEigenvalueMinus
  ring
/-- The two scalar branches in (20.18) have product `-sigma^2`. -/
theorem lsScaledAugmentedEigenvaluePlus_mul_minus (alpha sigma : ℝ) :
    lsScaledAugmentedEigenvaluePlus alpha sigma *
        lsScaledAugmentedEigenvalueMinus alpha sigma = -sigma ^ 2 := by
  unfold lsScaledAugmentedEigenvaluePlus lsScaledAugmentedEigenvalueMinus
  ring_nf
  rw [show (Real.sqrt (alpha ^ 2 * (1 / 4) + sigma ^ 2)) ^ 2 =
      alpha ^ 2 * (1 / 4) + sigma ^ 2 from by
    exact Real.sq_sqrt (by positivity)]
  ring
/-- For the source scaling range `alpha >= 0`, the positive branch in (20.18)
    is nonnegative. -/
theorem lsScaledAugmentedEigenvaluePlus_nonneg {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) :
    0 ≤ lsScaledAugmentedEigenvaluePlus alpha sigma := by
  unfold lsScaledAugmentedEigenvaluePlus
  positivity
/-- For the source scaling range `alpha >= 0`, the negative branch in (20.18)
    is nonpositive. -/
theorem lsScaledAugmentedEigenvalueMinus_nonpos {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) :
    lsScaledAugmentedEigenvalueMinus alpha sigma ≤ 0 := by
  unfold lsScaledAugmentedEigenvalueMinus
  have hsq : (alpha / 2) ^ 2 ≤ alpha ^ 2 / 4 + sigma ^ 2 := by
    nlinarith [sq_nonneg sigma]
  have hleft_nonneg : 0 ≤ alpha / 2 := by positivity
  have hsqrt_ge : alpha / 2 ≤ Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) := by
    exact (Real.le_sqrt hleft_nonneg (by positivity)).2 (by simpa [sq] using hsq)
  linarith
/-- If `sigma` is nonzero and `alpha >= 0`, the positive branch in (20.18) is
    strictly positive. -/
theorem lsScaledAugmentedEigenvaluePlus_pos_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    0 < lsScaledAugmentedEigenvaluePlus alpha sigma := by
  unfold lsScaledAugmentedEigenvaluePlus
  have hsigmasq_pos : 0 < sigma ^ 2 := sq_pos_of_ne_zero hsigma
  have hsqrt_pos : 0 < Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) := by
    apply Real.sqrt_pos.2
    nlinarith [sq_nonneg alpha, hsigmasq_pos]
  have hhalf_nonneg : 0 ≤ alpha / 2 := by positivity
  nlinarith
/-- If `sigma` is nonzero and `alpha >= 0`, the negative branch in (20.18) is
    strictly negative. -/
theorem lsScaledAugmentedEigenvalueMinus_neg_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    lsScaledAugmentedEigenvalueMinus alpha sigma < 0 := by
  unfold lsScaledAugmentedEigenvalueMinus
  have hsigmasq_pos : 0 < sigma ^ 2 := sq_pos_of_ne_zero hsigma
  have hsq_lt : (alpha / 2) ^ 2 < alpha ^ 2 / 4 + sigma ^ 2 := by
    nlinarith [hsigmasq_pos]
  have hleft_nonneg : 0 ≤ alpha / 2 := by positivity
  have hsqrt_gt : alpha / 2 < Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) := by
    exact (Real.lt_sqrt (y := alpha ^ 2 / 4 + sigma ^ 2) hleft_nonneg).2
      (by simpa [sq] using hsq_lt)
  linarith
/-- Under a nonzero singular value, the positive branch in (20.18) is a
    nonzero scalar. -/
theorem lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≠ 0 :=
  ne_of_gt (lsScaledAugmentedEigenvaluePlus_pos_of_sigma_ne_zero
    (alpha := alpha) (sigma := sigma) halpha hsigma)
/-- Under a nonzero singular value, the negative branch in (20.18) is a
    nonzero scalar. -/
theorem lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    lsScaledAugmentedEigenvalueMinus alpha sigma ≠ 0 :=
  ne_of_lt (lsScaledAugmentedEigenvalueMinus_neg_of_sigma_ne_zero
    (alpha := alpha) (sigma := sigma) halpha hsigma)
/-- Under a nonzero singular value, the positive branch in (20.18) is strictly
    above the left-nullspace branch `alpha`. -/
theorem lsScaledAugmentedEigenvaluePlus_gt_alpha_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    alpha < lsScaledAugmentedEigenvaluePlus alpha sigma := by
  unfold lsScaledAugmentedEigenvaluePlus
  have hsigmasq_pos : 0 < sigma ^ 2 := sq_pos_of_ne_zero hsigma
  have hsq_lt : (alpha / 2) ^ 2 < alpha ^ 2 / 4 + sigma ^ 2 := by
    nlinarith [hsigmasq_pos]
  have hleft_nonneg : 0 ≤ alpha / 2 := by positivity
  have hsqrt_gt : alpha / 2 < Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) := by
    exact (Real.lt_sqrt (y := alpha ^ 2 / 4 + sigma ^ 2) hleft_nonneg).2
      (by simpa [sq] using hsq_lt)
  linarith
/-- Under a nonzero singular value, the negative branch in (20.18) is strictly
    below the left-nullspace branch `alpha`. -/
theorem lsScaledAugmentedEigenvalueMinus_lt_alpha_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    lsScaledAugmentedEigenvalueMinus alpha sigma < alpha := by
  have hminus_neg :=
    lsScaledAugmentedEigenvalueMinus_neg_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  linarith
/-- Under a nonzero singular value, the two (20.18) branches are strictly
    ordered. -/
theorem lsScaledAugmentedEigenvalueMinus_lt_plus_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    lsScaledAugmentedEigenvalueMinus alpha sigma <
      lsScaledAugmentedEigenvaluePlus alpha sigma := by
  exact lt_trans
    (lsScaledAugmentedEigenvalueMinus_neg_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma)
    (lsScaledAugmentedEigenvaluePlus_pos_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma)
/-- Under a nonzero singular value, the two displayed branches in (20.18) are
    distinct. -/
theorem lsScaledAugmentedEigenvaluePlus_ne_minus_of_sigma_ne_zero {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≠
      lsScaledAugmentedEigenvalueMinus alpha sigma := by
  exact (ne_of_lt
    (lsScaledAugmentedEigenvalueMinus_lt_plus_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma)).symm
/-- Magnitude product for the two (20.18) singular-value branches. This is a
    scalar ingredient for the later condition-number analysis in (20.19). -/
theorem lsScaledAugmentedEigenvaluePlus_mul_abs_minus {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) :
    lsScaledAugmentedEigenvaluePlus alpha sigma *
        |lsScaledAugmentedEigenvalueMinus alpha sigma| = sigma ^ 2 := by
  have hprod := lsScaledAugmentedEigenvaluePlus_mul_minus alpha sigma
  have hminus_nonpos :=
    lsScaledAugmentedEigenvalueMinus_nonpos (alpha := alpha) (sigma := sigma) halpha
  rw [abs_of_nonpos hminus_nonpos]
  nlinarith
/-- Balanced scaling for (20.19): if `sigma = sqrt 2 * alpha`, then the
    negative (20.18) branch has magnitude exactly `alpha`. -/
theorem lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
    {alpha sigma : ℝ} (halpha : 0 ≤ alpha)
    (hsigma : sigma = Real.sqrt 2 * alpha) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma| = alpha := by
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_arg : Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) = 3 * alpha / 2 := by
    rw [hsigma]
    have harg : alpha ^ 2 / 4 + (Real.sqrt 2 * alpha) ^ 2 =
        (3 * alpha / 2) ^ 2 := by
      nlinarith [hsqrt2_sq]
    rw [harg]
    rw [Real.sqrt_sq_eq_abs]
    rw [abs_of_nonneg]
    positivity
  unfold lsScaledAugmentedEigenvalueMinus
  rw [hsqrt_arg]
  have hminus : alpha / 2 - 3 * alpha / 2 = -alpha := by ring
  rw [hminus]
  rw [abs_neg, abs_of_nonneg halpha]
/-- A scalar upper envelope used in the `alpha = sigma_min / sqrt 2` part of
    (20.19): when `sqrt 2 * alpha <= sigma`, the positive branch is at most
    `sqrt 2 * sigma`. -/
theorem lsScaledAugmentedEigenvaluePlus_le_sqrt_two_mul_sigma_of_sqrt_two_mul_alpha_le
    {alpha sigma : ℝ} (halpha : 0 ≤ alpha) (hsigma : 0 ≤ sigma)
    (hscale : Real.sqrt 2 * alpha ≤ sigma) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≤ Real.sqrt 2 * sigma := by
  unfold lsScaledAugmentedEigenvaluePlus
  set s : ℝ := Real.sqrt 2
  have hs_pos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos.2 (by norm_num)
  have hs_sq : s ^ 2 = (2 : ℝ) := by
    dsimp [s]
    exact Real.sq_sqrt (by norm_num)
  have hscale' : s * alpha ≤ sigma := by
    simpa [s] using hscale
  have hrhs_nonneg : 0 ≤ s * sigma - alpha / 2 := by
    nlinarith [hs_sq, halpha, hsigma, hscale']
  have hsq : alpha ^ 2 / 4 + sigma ^ 2 ≤ (s * sigma - alpha / 2) ^ 2 := by
    have hprod : 0 ≤ sigma * (sigma - s * alpha) := by
      exact mul_nonneg hsigma (sub_nonneg.mpr hscale')
    nlinarith [hs_sq, hprod]
  have hsqrt_le : Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) ≤
      s * sigma - alpha / 2 := by
    exact (Real.sqrt_le_iff).2 ⟨hrhs_nonneg, hsq⟩
  nlinarith
/-- A scalar lower envelope for the positive (20.18) branch: for the source
    nonnegative scaling range, the positive branch dominates the singular value
    `sigma`. -/
theorem lsScaledAugmentedEigenvaluePlus_ge_sigma {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) (hsigma : 0 ≤ sigma) :
    sigma ≤ lsScaledAugmentedEigenvaluePlus alpha sigma := by
  unfold lsScaledAugmentedEigenvaluePlus
  by_cases hsmall : sigma ≤ alpha / 2
  · have hsqrt_nonneg : 0 ≤ Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) :=
      Real.sqrt_nonneg _
    linarith
  · have hleft_nonneg : 0 ≤ sigma - alpha / 2 := by linarith
    have hsq : (sigma - alpha / 2) ^ 2 ≤ alpha ^ 2 / 4 + sigma ^ 2 := by
      have hprod : 0 ≤ alpha * sigma := mul_nonneg halpha hsigma
      nlinarith [hprod]
    have hsqrt_ge :
        sigma - alpha / 2 ≤ Real.sqrt (alpha ^ 2 / 4 + sigma ^ 2) := by
      exact (Real.le_sqrt hleft_nonneg (by positivity)).2
        (by simpa [sq] using hsq)
    linarith
/-- Monotonicity in the nonnegative singular value for the positive branch in
    (20.18).  This is scalar infrastructure for selecting the largest branch
    from the largest singular value in (20.19). -/
theorem lsScaledAugmentedEigenvaluePlus_mono_sigma_nonneg {alpha sigma tau : ℝ}
    (hsigma : 0 ≤ sigma) (hsig_le : sigma ≤ tau) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≤
      lsScaledAugmentedEigenvaluePlus alpha tau := by
  have htau : 0 ≤ tau := le_trans hsigma hsig_le
  have hsq : sigma ^ 2 ≤ tau ^ 2 := by
    have hprod : 0 ≤ (tau - sigma) * (tau + sigma) :=
      mul_nonneg (sub_nonneg.mpr hsig_le) (add_nonneg htau hsigma)
    nlinarith [hprod]
  have hrad : alpha ^ 2 / 4 + sigma ^ 2 ≤ alpha ^ 2 / 4 + tau ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hrad
  unfold lsScaledAugmentedEigenvaluePlus
  linarith
/-- Strict monotonicity in the nonnegative singular value for the positive
    branch in (20.18).  This strengthens the scalar ordering infrastructure
    used to select extremal branches in the later (20.19) condition-number
    bridge. -/
theorem lsScaledAugmentedEigenvaluePlus_strictMono_sigma_nonneg
    {alpha sigma tau : ℝ} (hsigma : 0 ≤ sigma) (hsig_lt : sigma < tau) :
    lsScaledAugmentedEigenvaluePlus alpha sigma <
      lsScaledAugmentedEigenvaluePlus alpha tau := by
  have hsq : sigma ^ 2 < tau ^ 2 := by
    have hprod : 0 < (tau - sigma) * (tau + sigma) := by
      exact mul_pos (sub_pos.mpr hsig_lt)
        (add_pos_of_pos_of_nonneg (lt_of_le_of_lt hsigma hsig_lt) hsigma)
    nlinarith [hprod]
  have hrad_nonneg : 0 ≤ alpha ^ 2 / 4 + sigma ^ 2 := by positivity
  have hrad : alpha ^ 2 / 4 + sigma ^ 2 <
      alpha ^ 2 / 4 + tau ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_lt_sqrt hrad_nonneg hrad
  unfold lsScaledAugmentedEigenvaluePlus
  linarith
/-- Monotonicity in the nonnegative singular value for the magnitude of the
    negative branch in (20.18).  This is scalar infrastructure for selecting the
    smallest negative-branch magnitude from the smallest singular value in
    (20.19). -/
theorem lsScaledAugmentedEigenvalueMinus_abs_mono_sigma_nonneg
    {alpha sigma tau : ℝ} (halpha : 0 ≤ alpha)
    (hsigma : 0 ≤ sigma) (hsig_le : sigma ≤ tau) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
      |lsScaledAugmentedEigenvalueMinus alpha tau| := by
  have htau : 0 ≤ tau := le_trans hsigma hsig_le
  have hsq : sigma ^ 2 ≤ tau ^ 2 := by
    have hprod : 0 ≤ (tau - sigma) * (tau + sigma) :=
      mul_nonneg (sub_nonneg.mpr hsig_le) (add_nonneg htau hsigma)
    nlinarith [hprod]
  have hrad : alpha ^ 2 / 4 + sigma ^ 2 ≤ alpha ^ 2 / 4 + tau ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_le_sqrt hrad
  have hminus_sigma :=
    lsScaledAugmentedEigenvalueMinus_nonpos (alpha := alpha) (sigma := sigma) halpha
  have hminus_tau :=
    lsScaledAugmentedEigenvalueMinus_nonpos (alpha := alpha) (sigma := tau) halpha
  rw [abs_of_nonpos hminus_sigma, abs_of_nonpos hminus_tau]
  unfold lsScaledAugmentedEigenvalueMinus
  linarith
/-- Strict monotonicity in the nonnegative singular value for the magnitude of
    the negative branch in (20.18).  This is the strict counterpart of
    `lsScaledAugmentedEigenvalueMinus_abs_mono_sigma_nonneg` for the later
    extremal branch and multiplicity analysis in (20.19). -/
theorem lsScaledAugmentedEigenvalueMinus_abs_strictMono_sigma_nonneg
    {alpha sigma tau : ℝ} (halpha : 0 ≤ alpha)
    (hsigma : 0 ≤ sigma) (hsig_lt : sigma < tau) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma| <
      |lsScaledAugmentedEigenvalueMinus alpha tau| := by
  have hsq : sigma ^ 2 < tau ^ 2 := by
    have hprod : 0 < (tau - sigma) * (tau + sigma) := by
      exact mul_pos (sub_pos.mpr hsig_lt)
        (add_pos_of_pos_of_nonneg (lt_of_le_of_lt hsigma hsig_lt) hsigma)
    nlinarith [hprod]
  have hrad_nonneg : 0 ≤ alpha ^ 2 / 4 + sigma ^ 2 := by positivity
  have hrad : alpha ^ 2 / 4 + sigma ^ 2 <
      alpha ^ 2 / 4 + tau ^ 2 := by
    nlinarith
  have hsqrt := Real.sqrt_lt_sqrt hrad_nonneg hrad
  have hminus_sigma :=
    lsScaledAugmentedEigenvalueMinus_nonpos (alpha := alpha) (sigma := sigma) halpha
  have hminus_tau :=
    lsScaledAugmentedEigenvalueMinus_nonpos (alpha := alpha) (sigma := tau) halpha
  rw [abs_of_nonpos hminus_sigma, abs_of_nonpos hminus_tau]
  unfold lsScaledAugmentedEigenvalueMinus
  linarith
/-- For the source scaling range `alpha >= 0`, the positive branch in (20.18)
    dominates the magnitude of the negative branch. -/
theorem lsScaledAugmentedEigenvalueMinus_abs_le_plus {alpha sigma : ℝ}
    (halpha : 0 ≤ alpha) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤
      lsScaledAugmentedEigenvaluePlus alpha sigma := by
  have hminus_nonpos :=
    lsScaledAugmentedEigenvalueMinus_nonpos (alpha := alpha) (sigma := sigma) halpha
  rw [abs_of_nonpos hminus_nonpos]
  have hsum := lsScaledAugmentedEigenvaluePlus_add_minus alpha sigma
  linarith
/-- Scalar branch-ratio form of the achieved upper bound in (20.19).  It is the
    exact denominator/numerator estimate behind the source choice
    `alpha = sigma_min / sqrt 2`, before any global spectral multiplicity theorem
    for `C(alpha)` is invoked. -/
theorem lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio
    {alpha sigmaMin sigmaMax : ℝ} (halpha : 0 < alpha)
    (hsigmaMin : sigmaMin = Real.sqrt 2 * alpha)
    (hsigmaMax : sigmaMin ≤ sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
      2 * (sigmaMax / sigmaMin) := by
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsigmaMin_pos : 0 < sigmaMin := by
    rw [hsigmaMin]
    positivity
  have hsigmaMax_nonneg : 0 ≤ sigmaMax :=
    le_trans (le_of_lt hsigmaMin_pos) hsigmaMax
  have hscale : Real.sqrt 2 * alpha ≤ sigmaMax := by
    simpa [hsigmaMin] using hsigmaMax
  have hplus :=
    lsScaledAugmentedEigenvaluePlus_le_sqrt_two_mul_sigma_of_sqrt_two_mul_alpha_le
      (alpha := alpha) (sigma := sigmaMax) halpha_nonneg hsigmaMax_nonneg hscale
  have hminus :=
    lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg hsigmaMin
  rw [hminus, hsigmaMin]
  have hdiv : lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha ≤
      (Real.sqrt 2 * sigmaMax) / alpha :=
    div_le_div_of_nonneg_right hplus (le_of_lt halpha)
  calc
    lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha
        ≤ (Real.sqrt 2 * sigmaMax) / alpha := hdiv
    _ = 2 * (sigmaMax / (Real.sqrt 2 * alpha)) := by
        field_simp [ne_of_gt halpha, ne_of_gt hsqrt2_pos]
        ring_nf
        nlinarith [hsqrt2_sq]
/-- Source-facing form of the scalar branch-ratio upper bound in (20.19), using
    the displayed balanced scaling `alpha = sigma_min / sqrt 2`. -/
theorem lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio_of_alpha_eq_div_sqrt_two
    {alpha sigmaMin sigmaMax : ℝ} (hsigmaMin_pos : 0 < sigmaMin)
    (halpha : alpha = sigmaMin / Real.sqrt 2) (hsigmaMax : sigmaMin ≤ sigmaMax) :
    lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| ≤
      2 * (sigmaMax / sigmaMin) := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    positivity
  have hsigmaMin : sigmaMin = Real.sqrt 2 * alpha := by
    rw [halpha]
    field_simp [hsqrt2_ne]
  exact
    lsScaledAugmentedBalancedBranchRatio_le_two_sigma_ratio
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      halpha_pos hsigmaMin hsigmaMax
/-- Scalar branch-ratio form of the lower bound in (20.19).  It records the
    denominator identity and positive-branch lower envelope behind the source
    choice `alpha = sigma_min / sqrt 2`, before the global spectral
    multiplicity theorem for `C(alpha)` is invoked. -/
theorem lsScaledAugmentedBalancedBranchRatio_ge_sqrt_two_sigma_ratio
    {alpha sigmaMin sigmaMax : ℝ} (halpha : 0 < alpha)
    (hsigmaMin : sigmaMin = Real.sqrt 2 * alpha)
    (hsigmaMax : 0 ≤ sigmaMax) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
  have halpha_nonneg : 0 ≤ alpha := le_of_lt halpha
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hplus :=
    lsScaledAugmentedEigenvaluePlus_ge_sigma
      (alpha := alpha) (sigma := sigmaMax) halpha_nonneg hsigmaMax
  have hminus :=
    lsScaledAugmentedEigenvalueMinus_abs_eq_alpha_of_sigma_eq_sqrt_two_mul
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg hsigmaMin
  rw [hminus, hsigmaMin]
  have hdiv :
      sigmaMax / alpha ≤
        lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha :=
    div_le_div_of_nonneg_right hplus halpha_nonneg
  calc
    Real.sqrt 2 * (sigmaMax / (Real.sqrt 2 * alpha))
        = sigmaMax / alpha := by
          field_simp [ne_of_gt halpha, ne_of_gt hsqrt2_pos]
    _ ≤ lsScaledAugmentedEigenvaluePlus alpha sigmaMax / alpha := hdiv
/-- Source-facing form of the scalar branch-ratio lower bound in (20.19), using
    the displayed balanced scaling `alpha = sigma_min / sqrt 2`. -/
theorem lsScaledAugmentedBalancedBranchRatio_ge_sqrt_two_sigma_ratio_of_alpha_eq_div_sqrt_two
    {alpha sigmaMin sigmaMax : ℝ} (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMax : 0 ≤ sigmaMax) (halpha : alpha = sigmaMin / Real.sqrt 2) :
    Real.sqrt 2 * (sigmaMax / sigmaMin) ≤
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
  have hsqrt2_pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt2_pos
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    positivity
  have hsigmaMin : sigmaMin = Real.sqrt 2 * alpha := by
    rw [halpha]
    field_simp [hsqrt2_ne]
  exact
    lsScaledAugmentedBalancedBranchRatio_ge_sqrt_two_sigma_ratio
      (alpha := alpha) (sigmaMin := sigmaMin) (sigmaMax := sigmaMax)
      halpha_pos hsigmaMin hsigmaMax
/-- Scalar witness for the final comparison in (20.19): with scaling
    `alpha = sigmaMax`, the extremal branch ratio is strictly larger than
    `(sigmaMax / sigmaMin)^2`.  This is the source-facing scalar certificate
    behind the statement that some scaled augmented systems can be worse than
    `kappa_2(A)^2`, before the global spectral/multiplicity theorem connects
    these branches to the matrix condition number of `C(alpha)`. -/
theorem lsScaledAugmentedBranchRatio_gt_sigma_ratio_sq_of_alpha_eq_sigmaMax
    {alpha sigmaMin sigmaMax : ℝ} (hsigmaMin_pos : 0 < sigmaMin)
    (hsigmaMax : sigmaMin ≤ sigmaMax) (halpha : alpha = sigmaMax) :
    (sigmaMax / sigmaMin) ^ 2 <
      lsScaledAugmentedEigenvaluePlus alpha sigmaMax /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMin| := by
  let Pmin := lsScaledAugmentedEigenvaluePlus alpha sigmaMin
  let Pmax := lsScaledAugmentedEigenvaluePlus alpha sigmaMax
  let Dmin := |lsScaledAugmentedEigenvalueMinus alpha sigmaMin|
  have hsigmaMax_pos : 0 < sigmaMax := lt_of_lt_of_le hsigmaMin_pos hsigmaMax
  have halpha_nonneg : 0 ≤ alpha := by
    rw [halpha]
    exact le_of_lt hsigmaMax_pos
  have hPmin_gt : sigmaMax < Pmin := by
    change sigmaMax < lsScaledAugmentedEigenvaluePlus alpha sigmaMin
    rw [← halpha]
    exact lsScaledAugmentedEigenvaluePlus_gt_alpha_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg (ne_of_gt hsigmaMin_pos)
  have hPmax_ge : sigmaMax ≤ Pmax :=
    lsScaledAugmentedEigenvaluePlus_ge_sigma
      (alpha := alpha) (sigma := sigmaMax) halpha_nonneg (le_of_lt hsigmaMax_pos)
  have hPmax_pos : 0 < Pmax := lt_of_lt_of_le hsigmaMax_pos hPmax_ge
  have hprod_gt : sigmaMax * sigmaMax < Pmin * Pmax :=
    mul_lt_mul_of_nonneg_of_pos hPmin_gt hPmax_ge
      (le_of_lt hsigmaMax_pos) hPmax_pos
  have hprod_min : Pmin * Dmin = sigmaMin ^ 2 :=
    lsScaledAugmentedEigenvaluePlus_mul_abs_minus
      (alpha := alpha) (sigma := sigmaMin) halpha_nonneg
  have hDmin_pos : 0 < Dmin := by
    exact abs_pos.mpr
      (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigmaMin) halpha_nonneg (ne_of_gt hsigmaMin_pos))
  have hDmin_ne : Dmin ≠ 0 := ne_of_gt hDmin_pos
  have hsigmaMin_ne : sigmaMin ≠ 0 := ne_of_gt hsigmaMin_pos
  have hsigmaMin_sq_pos : 0 < sigmaMin ^ 2 := sq_pos_of_ne_zero hsigmaMin_ne
  have hsigmaMin_sq_ne : sigmaMin ^ 2 ≠ 0 := ne_of_gt hsigmaMin_sq_pos
  have hsq_div : (sigmaMax / sigmaMin) ^ 2 =
      sigmaMax * sigmaMax / sigmaMin ^ 2 := by
    field_simp [hsigmaMin_ne]
  have hratio_eq : Pmax / Dmin = (Pmin * Pmax) / sigmaMin ^ 2 := by
    have hPmin_ne : Pmin ≠ 0 :=
      ne_of_gt (lt_trans hsigmaMax_pos hPmin_gt)
    field_simp [hDmin_ne, hsigmaMin_sq_ne, hPmin_ne]
    nlinarith [hprod_min]
  rw [hsq_div, hratio_eq]
  exact div_lt_div_of_pos_right hprod_gt hsigmaMin_sq_pos
/-- Block-action certificate behind (20.18): if `u,v` are a singular-vector
    pair for singular value `sigma` and `lambda` satisfies the displayed
    quadratic, then `[lambda u; sigma v]` is scaled by `lambda` under
    `C(alpha)`. This records the source eigenvector algebra without asserting
    multiplicities or a global spectral decomposition. -/
theorem lsScaledAugmentedMatrix_singularPair_eigenvector_of_quadratic {m n : ℕ}
    (alpha sigma lambda : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hquad : lambda ^ 2 - alpha * lambda - sigma ^ 2 = 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append (fun i => lambda * u i) (fun j => sigma * v j)) =
      fun k => lambda *
        Fin.append (fun i => lambda * u i) (fun j => sigma * v j) k := by
  rw [lsScaledAugmentedMatrix_mulVec]
  ext k
  refine Fin.addCases
    (motive := fun k : Fin (m + n) =>
      Fin.append
          (fun i : Fin m => alpha * (lambda * u i) +
            rectMatMulVec A (fun j : Fin n => sigma * v j) i)
          (fun j : Fin n => ∑ i : Fin m, A i j * (lambda * u i)) k =
        lambda *
          Fin.append (fun i => lambda * u i) (fun j => sigma * v j) k)
    ?left ?right k
  · intro i
    have hmul :
        rectMatMulVec A (fun j : Fin n => sigma * v j) i =
          sigma ^ 2 * u i := by
      unfold rectMatMulVec at *
      calc
        ∑ j : Fin n, A i j * (sigma * v j)
            = sigma * ∑ j : Fin n, A i j * v j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = sigma * (sigma * u i) := by rw [congrFun hAv i]
        _ = sigma ^ 2 * u i := by ring
    have hscalar : alpha * lambda + sigma ^ 2 = lambda ^ 2 := by
      nlinarith
    simp [Fin.append_left, hmul]
    calc
      alpha * (lambda * u i) + sigma ^ 2 * u i =
          (alpha * lambda + sigma ^ 2) * u i := by ring
      _ = lambda * (lambda * u i) := by rw [hscalar]; ring
  · intro j
    have hmul : (∑ i : Fin m, A i j * (lambda * u i)) =
        lambda * sigma * v j := by
      calc
        ∑ i : Fin m, A i j * (lambda * u i)
            = lambda * ∑ i : Fin m, A i j * u i := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ = lambda * (sigma * v j) := by rw [congrFun hATu j]
        _ = lambda * sigma * v j := by ring
    simp [Fin.append_right, hmul]
    ring
/-- Source-normalized block-action certificate behind (20.18): if `lambda` is a
    nonzero root of the displayed quadratic, then the equivalent vector
    `[u; (sigma / lambda) v]` is scaled by `lambda` under `C(alpha)`.

    This is the printed eigenvector normalization used by the later
    multiplicity and condition-number routes; it is still local eigenvector
    algebra, not a global spectral decomposition. -/
theorem lsScaledAugmentedMatrix_singularPair_normalized_eigenvector_of_quadratic
    {m n : ℕ}
    (alpha sigma lambda : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hlambda : lambda ≠ 0)
    (hquad : lambda ^ 2 - alpha * lambda - sigma ^ 2 = 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u (fun j => (sigma / lambda) * v j)) =
      fun k => lambda * Fin.append u (fun j => (sigma / lambda) * v j) k := by
  rw [lsScaledAugmentedMatrix_mulVec]
  have hscalar : alpha + sigma ^ 2 / lambda = lambda := by
    field_simp [hlambda]
    nlinarith
  ext k
  refine Fin.addCases
    (motive := fun k : Fin (m + n) =>
      Fin.append
          (fun i : Fin m => alpha * u i +
            rectMatMulVec A (fun j : Fin n => (sigma / lambda) * v j) i)
          (fun j : Fin n => ∑ i : Fin m, A i j * u i) k =
        lambda * Fin.append u (fun j => (sigma / lambda) * v j) k)
    ?left ?right k
  · intro i
    have hmul :
        rectMatMulVec A (fun j : Fin n => (sigma / lambda) * v j) i =
          (sigma ^ 2 / lambda) * u i := by
      unfold rectMatMulVec at *
      calc
        ∑ j : Fin n, A i j * ((sigma / lambda) * v j)
            = (sigma / lambda) * ∑ j : Fin n, A i j * v j := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = (sigma / lambda) * (sigma * u i) := by
                rw [congrFun hAv i]
        _ = (sigma ^ 2 / lambda) * u i := by ring
    simp [Fin.append_left, hmul]
    calc
      alpha * u i + sigma ^ 2 / lambda * u i =
          (alpha + sigma ^ 2 / lambda) * u i := by ring
      _ = lambda * u i := by rw [hscalar]
  · intro j
    have hmul : (∑ i : Fin m, A i j * u i) = sigma * v j :=
      congrFun hATu j
    simp [Fin.append_right, hmul]
    field_simp [hlambda]
/-- The source-normalized singular-pair vector `[u; (sigma / lambda) v]` is
    nonzero when `sigma`, `lambda`, and the right singular vector are nonzero. -/
theorem lsScaledAugmentedMatrix_singularPair_normalized_vector_ne_zero {m n : ℕ}
    (sigma lambda : ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hsigma : sigma ≠ 0) (hlambda : lambda ≠ 0) (hv : v ≠ 0) :
    Fin.append u (fun j => (sigma / lambda) * v j) ≠ 0 := by
  intro hzero
  apply hv
  ext j
  have hright := congrFun hzero (Fin.natAdd m j)
  have hmul : (sigma / lambda) * v j = 0 := by
    simpa [Fin.append_right] using hright
  exact (mul_eq_zero.mp hmul).resolve_left (div_ne_zero hsigma hlambda)
/-- The positive branch in (20.18) gives the corresponding singular-pair
    block-action certificate for `C(alpha)`. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_eigenvector {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append
          (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
          (fun j => sigma * v j)) =
      fun k => lsScaledAugmentedEigenvaluePlus alpha sigma *
        Fin.append
          (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
          (fun j => sigma * v j) k :=
  lsScaledAugmentedMatrix_singularPair_eigenvector_of_quadratic
    alpha sigma (lsScaledAugmentedEigenvaluePlus alpha sigma) A u v hAv hATu
    (lsScaledAugmentedEigenvaluePlus_quadratic alpha sigma)
/-- The positive branch in (20.18) in source-normalized eigenvector form:
    `[u; (sigma / lambda_+) v]` is scaled by `lambda_+` under `C(alpha)`. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_normalized_eigenvector
    {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)) =
      fun k => lsScaledAugmentedEigenvaluePlus alpha sigma *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k :=
  lsScaledAugmentedMatrix_singularPair_normalized_eigenvector_of_quadratic
    alpha sigma (lsScaledAugmentedEigenvaluePlus alpha sigma) A u v hAv hATu
    (lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma)
    (lsScaledAugmentedEigenvaluePlus_quadratic alpha sigma)
/-- The positive-branch vector used in (20.18)'s singular-pair certificate is
    nonzero when the singular value and right singular vector are nonzero. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_vector_ne_zero {m n : ℕ}
    (alpha sigma : ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    Fin.append
        (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
        (fun j => sigma * v j) ≠ 0 := by
  intro hzero
  apply hv
  ext j
  have hright := congrFun hzero (Fin.natAdd m j)
  simpa [Fin.append_right, hsigma] using hright
/-- Packaged positive-branch eigenpair certificate for (20.18): the singular
    pair gives both the block-action identity for `C(alpha)` and a nonzero
    block vector.  This is still local eigenvector algebra, not a global
    multiplicity theorem. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_eigenpair {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append
          (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
          (fun j => sigma * v j)) =
      fun k => lsScaledAugmentedEigenvaluePlus alpha sigma *
        Fin.append
          (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
          (fun j => sigma * v j) k) ∧
      Fin.append
        (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
        (fun j => sigma * v j) ≠ 0 := by
  exact
    ⟨lsScaledAugmentedMatrix_singularPair_plus_eigenvector
        alpha sigma A u v hAv hATu,
      lsScaledAugmentedMatrix_singularPair_plus_vector_ne_zero
        alpha sigma u v hsigma hv⟩
/-- Packaged positive-branch source-normalized eigenpair certificate for
    (20.18): the singular pair gives the normalized block-action identity and a
    nonzero normalized block vector. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_normalized_eigenpair
    {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)) =
      fun k => lsScaledAugmentedEigenvaluePlus alpha sigma *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) ∧
      Fin.append u
        (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) ≠ 0 := by
  have hlambda :=
    lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  exact
    ⟨lsScaledAugmentedMatrix_singularPair_plus_normalized_eigenvector
        alpha sigma A u v hAv hATu halpha hsigma,
      lsScaledAugmentedMatrix_singularPair_normalized_vector_ne_zero
        sigma (lsScaledAugmentedEigenvaluePlus alpha sigma) u v
        hsigma hlambda hv⟩
/-- The negative branch in (20.18) gives the corresponding singular-pair
    block-action certificate for `C(alpha)`. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_eigenvector {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append
          (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
          (fun j => sigma * v j)) =
      fun k => lsScaledAugmentedEigenvalueMinus alpha sigma *
        Fin.append
          (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
          (fun j => sigma * v j) k :=
  lsScaledAugmentedMatrix_singularPair_eigenvector_of_quadratic
    alpha sigma (lsScaledAugmentedEigenvalueMinus alpha sigma) A u v hAv hATu
    (lsScaledAugmentedEigenvalueMinus_quadratic alpha sigma)
/-- The negative branch in (20.18) in source-normalized eigenvector form:
    `[u; (sigma / lambda_-) v]` is scaled by `lambda_-` under `C(alpha)`. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_normalized_eigenvector
    {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)) =
      fun k => lsScaledAugmentedEigenvalueMinus alpha sigma *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k :=
  lsScaledAugmentedMatrix_singularPair_normalized_eigenvector_of_quadratic
    alpha sigma (lsScaledAugmentedEigenvalueMinus alpha sigma) A u v hAv hATu
    (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma)
    (lsScaledAugmentedEigenvalueMinus_quadratic alpha sigma)
/-- The negative-branch vector used in (20.18)'s singular-pair certificate is
    nonzero when the singular value and right singular vector are nonzero. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_vector_ne_zero {m n : ℕ}
    (alpha sigma : ℝ) (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    Fin.append
        (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
        (fun j => sigma * v j) ≠ 0 := by
  intro hzero
  apply hv
  ext j
  have hright := congrFun hzero (Fin.natAdd m j)
  simpa [Fin.append_right, hsigma] using hright
/-- Packaged negative-branch eigenpair certificate for (20.18): the singular
    pair gives both the block-action identity for `C(alpha)` and a nonzero
    block vector.  This is still local eigenvector algebra, not a global
    multiplicity theorem. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_eigenpair {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append
          (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
          (fun j => sigma * v j)) =
      fun k => lsScaledAugmentedEigenvalueMinus alpha sigma *
        Fin.append
          (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
          (fun j => sigma * v j) k) ∧
      Fin.append
        (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
        (fun j => sigma * v j) ≠ 0 := by
  exact
    ⟨lsScaledAugmentedMatrix_singularPair_minus_eigenvector
        alpha sigma A u v hAv hATu,
      lsScaledAugmentedMatrix_singularPair_minus_vector_ne_zero
        alpha sigma u v hsigma hv⟩
/-- Packaged negative-branch source-normalized eigenpair certificate for
    (20.18): the singular pair gives the normalized block-action identity and a
    nonzero normalized block vector. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_normalized_eigenpair
    {m n : ℕ}
    (alpha sigma : ℝ) (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)) =
      fun k => lsScaledAugmentedEigenvalueMinus alpha sigma *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) ∧
      Fin.append u
        (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) ≠ 0 := by
  have hlambda :=
    lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  exact
    ⟨lsScaledAugmentedMatrix_singularPair_minus_normalized_eigenvector
        alpha sigma A u v hAv hATu halpha hsigma,
      lsScaledAugmentedMatrix_singularPair_normalized_vector_ne_zero
        sigma (lsScaledAugmentedEigenvalueMinus alpha sigma) u v
        hsigma hlambda hv⟩
/-- Operator-norm lower-bound certificate for the positive branch in (20.18):
    any finite operator-2 bound for `C(alpha)` must dominate the magnitude of
    a witnessed positive-branch eigenvalue.  This is a norm/eigenpair bridge
    toward the condition-number formula (20.19), not a global spectral
    decomposition. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_abs_eigenvalue_le_of_finiteOpNorm2Le
    {m n : ℕ} {alpha sigma L : ℝ} {A : Fin m → Fin n → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hC : finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A) L)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    |lsScaledAugmentedEigenvaluePlus alpha sigma| ≤ L := by
  let z : Fin (m + n) → ℝ :=
    Fin.append
      (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
      (fun j => sigma * v j)
  have heig_rect :=
    lsScaledAugmentedMatrix_singularPair_plus_eigenpair
      alpha sigma A u v hAv hATu hsigma hv
  have heig :
      finiteMatVec (lsScaledAugmentedMatrix alpha A) z =
        fun k => lsScaledAugmentedEigenvaluePlus alpha sigma * z k := by
    simpa [z, finiteMatVec, rectMatMulVec] using heig_rect.1
  exact
    finiteOpNorm2Le_abs_eigenvalue_le
      (M := lsScaledAugmentedMatrix alpha A)
      (lambda := lsScaledAugmentedEigenvaluePlus alpha sigma)
      (c := L) (x := z) hC heig_rect.2 heig
/-- Non-absolute source form of the positive-branch operator-norm lower-bound
    certificate for (20.18)-(20.19). -/
theorem lsScaledAugmentedMatrix_singularPair_plus_eigenvalue_le_of_finiteOpNorm2Le
    {m n : ℕ} {alpha sigma L : ℝ} {A : Fin m → Fin n → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hC : finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A) L)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    lsScaledAugmentedEigenvaluePlus alpha sigma ≤ L := by
  have h :=
    lsScaledAugmentedMatrix_singularPair_plus_abs_eigenvalue_le_of_finiteOpNorm2Le
      (hC := hC) (hAv := hAv) (hATu := hATu) hsigma hv
  rwa [abs_of_nonneg
    (lsScaledAugmentedEigenvaluePlus_nonneg
      (alpha := alpha) (sigma := sigma) halpha)] at h
/-- Operator-norm lower-bound certificate for the negative branch in (20.18):
    any finite operator-2 bound for `C(alpha)` must dominate the magnitude of
    a witnessed negative-branch eigenvalue.  This is a norm/eigenpair bridge
    toward the condition-number formula (20.19), not a global spectral
    decomposition. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_abs_eigenvalue_le_of_finiteOpNorm2Le
    {m n : ℕ} {alpha sigma L : ℝ} {A : Fin m → Fin n → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hC : finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A) L)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma| ≤ L := by
  let z : Fin (m + n) → ℝ :=
    Fin.append
      (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
      (fun j => sigma * v j)
  have heig_rect :=
    lsScaledAugmentedMatrix_singularPair_minus_eigenpair
      alpha sigma A u v hAv hATu hsigma hv
  have heig :
      finiteMatVec (lsScaledAugmentedMatrix alpha A) z =
        fun k => lsScaledAugmentedEigenvalueMinus alpha sigma * z k := by
    simpa [z, finiteMatVec, rectMatMulVec] using heig_rect.1
  exact
    finiteOpNorm2Le_abs_eigenvalue_le
      (M := lsScaledAugmentedMatrix alpha A)
      (lambda := lsScaledAugmentedEigenvalueMinus alpha sigma)
      (c := L) (x := z) hC heig_rect.2 heig
/-- Inverse-operator-norm lower-bound certificate for the positive branch in
    (20.18): any finite operator-2 bound for a left-inverse candidate of
    `C(alpha)` must dominate the reciprocal magnitude of a witnessed
    positive-branch eigenvalue.  This is the inverse-norm side of the
    condition-number bridge for (20.19), not a proof of global invertibility or
    spectral multiplicity. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_abs_recip_eigenvalue_le_of_inverse_finiteOpNorm2Le
    {m n : ℕ} {alpha sigma D : ℝ} {A : Fin m → Fin n → ℝ}
    {Cinv : Fin (m + n) → Fin (m + n) → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hCinv : finiteOpNorm2Le Cinv D)
    (hLeft : IsLeftInverse (m + n) (lsScaledAugmentedMatrix alpha A) Cinv)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    |lsScaledAugmentedEigenvaluePlus alpha sigma|⁻¹ ≤ D := by
  let z : Fin (m + n) → ℝ :=
    Fin.append
      (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
      (fun j => sigma * v j)
  have heig_rect :=
    lsScaledAugmentedMatrix_singularPair_plus_eigenpair
      alpha sigma A u v hAv hATu hsigma hv
  have heig :
      finiteMatVec (lsScaledAugmentedMatrix alpha A) z =
        fun k => lsScaledAugmentedEigenvaluePlus alpha sigma * z k := by
    simpa [z, finiteMatVec, rectMatMulVec] using heig_rect.1
  exact
    finiteOpNorm2Le_inverse_abs_recip_eigenvalue_le_of_isLeftInverse
      (M := lsScaledAugmentedMatrix alpha A) (Minv := Cinv)
      (lambda := lsScaledAugmentedEigenvaluePlus alpha sigma)
      (c := D) (x := z) hCinv hLeft
      (lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha hsigma)
      heig_rect.2 heig
/-- Inverse-operator-norm lower-bound certificate for the negative branch in
    (20.18): any finite operator-2 bound for a left-inverse candidate of
    `C(alpha)` must dominate the reciprocal magnitude of a witnessed
    negative-branch eigenvalue. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_abs_recip_eigenvalue_le_of_inverse_finiteOpNorm2Le
    {m n : ℕ} {alpha sigma D : ℝ} {A : Fin m → Fin n → ℝ}
    {Cinv : Fin (m + n) → Fin (m + n) → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hCinv : finiteOpNorm2Le Cinv D)
    (hLeft : IsLeftInverse (m + n) (lsScaledAugmentedMatrix alpha A) Cinv)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    |lsScaledAugmentedEigenvalueMinus alpha sigma|⁻¹ ≤ D := by
  let z : Fin (m + n) → ℝ :=
    Fin.append
      (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
      (fun j => sigma * v j)
  have heig_rect :=
    lsScaledAugmentedMatrix_singularPair_minus_eigenpair
      alpha sigma A u v hAv hATu hsigma hv
  have heig :
      finiteMatVec (lsScaledAugmentedMatrix alpha A) z =
        fun k => lsScaledAugmentedEigenvalueMinus alpha sigma * z k := by
    simpa [z, finiteMatVec, rectMatMulVec] using heig_rect.1
  exact
    finiteOpNorm2Le_inverse_abs_recip_eigenvalue_le_of_isLeftInverse
      (M := lsScaledAugmentedMatrix alpha A) (Minv := Cinv)
      (lambda := lsScaledAugmentedEigenvalueMinus alpha sigma)
      (c := D) (x := z) hCinv hLeft
      (lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha hsigma)
      heig_rect.2 heig
/-- Condition-number product bridge for the two scalar branches in
    (20.18)-(20.19): an operator-2 bound for `C(alpha)` and an operator-2 bound
    for an explicit left-inverse candidate bound the ratio of a witnessed
    positive branch to the magnitude of a witnessed negative branch.  The
    remaining spectral work is to prove that the selected branches are the
    global extremal eigenvalues of `C(alpha)`. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_abs_ratio_le_opNorm_mul_inverseOpNorm
    {m n : ℕ} {alpha sigmaPlus sigmaMinus L D : ℝ}
    {A : Fin m → Fin n → ℝ}
    {Cinv : Fin (m + n) → Fin (m + n) → ℝ}
    {uPlus uMinus : Fin m → ℝ} {vPlus vMinus : Fin n → ℝ}
    (hC : finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A) L)
    (hCinv : finiteOpNorm2Le Cinv D)
    (hLeft : IsLeftInverse (m + n) (lsScaledAugmentedMatrix alpha A) Cinv)
    (hAvPlus : rectMatMulVec A vPlus = fun i => sigmaPlus * uPlus i)
    (hATuPlus : (fun j : Fin n => ∑ i : Fin m, A i j * uPlus i) =
      fun j => sigmaPlus * vPlus j)
    (hAvMinus : rectMatMulVec A vMinus = fun i => sigmaMinus * uMinus i)
    (hATuMinus : (fun j : Fin n => ∑ i : Fin m, A i j * uMinus i) =
      fun j => sigmaMinus * vMinus j)
    (halpha : 0 ≤ alpha)
    (hsigmaPlus : sigmaPlus ≠ 0) (hvPlus : vPlus ≠ 0)
    (hsigmaMinus : sigmaMinus ≠ 0) (hvMinus : vMinus ≠ 0) :
    |lsScaledAugmentedEigenvaluePlus alpha sigmaPlus| /
        |lsScaledAugmentedEigenvalueMinus alpha sigmaMinus| ≤ L * D := by
  have hplus :
      |lsScaledAugmentedEigenvaluePlus alpha sigmaPlus| ≤ L :=
    lsScaledAugmentedMatrix_singularPair_plus_abs_eigenvalue_le_of_finiteOpNorm2Le
      (hC := hC) (hAv := hAvPlus) (hATu := hATuPlus)
      hsigmaPlus hvPlus
  have hminusInv :
      |lsScaledAugmentedEigenvalueMinus alpha sigmaMinus|⁻¹ ≤ D :=
    lsScaledAugmentedMatrix_singularPair_minus_abs_recip_eigenvalue_le_of_inverse_finiteOpNorm2Le
      (hCinv := hCinv) (hLeft := hLeft)
      (hAv := hAvMinus) (hATu := hATuMinus)
      halpha hsigmaMinus hvMinus
  have hL_nonneg : 0 ≤ L :=
    le_trans (abs_nonneg _) hplus
  have hrecip_nonneg :
      0 ≤ |lsScaledAugmentedEigenvalueMinus alpha sigmaMinus|⁻¹ :=
    inv_nonneg.mpr (abs_nonneg _)
  have hprod :
      |lsScaledAugmentedEigenvaluePlus alpha sigmaPlus| *
          |lsScaledAugmentedEigenvalueMinus alpha sigmaMinus|⁻¹ ≤ L * D :=
    mul_le_mul hplus hminusInv hrecip_nonneg hL_nonneg
  simpa [div_eq_mul_inv] using hprod
/-- Higham, 2nd ed., Chapter 20, Section 20.5, equations (20.18)-(20.19):
    spectral upper-bound bridge for the scaled augmented matrix `C(alpha)`.
    If a complete orthogonal diagonalization of `C(alpha)` is supplied and all
    displayed eigenvalue magnitudes are bounded by `L`, then `C(alpha)` has
    finite operator-2 norm at most `L`.  This is the reusable upper-bound half
    needed by the full condition-number formula; it does not construct the
    eigenbasis or prove multiplicities. -/
theorem lsScaledAugmentedMatrix_finiteOpNorm2Le_of_orthogonal_diagonalization
    {m n : ℕ} {alpha L : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q) (hL : 0 ≤ L)
    (hd : ∀ i : Fin (m + n), |d i| ≤ L) :
    finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A) L :=
  finiteOpNorm2Le_of_isOrthogonal_diagonalization hdiag hQ hL hd
/-- `opNorm2` corollary of
    `lsScaledAugmentedMatrix_finiteOpNorm2Le_of_orthogonal_diagonalization`.
    This is the source-facing norm side required before (20.19)'s upper
    condition-number inequality can be instantiated. -/
theorem lsScaledAugmentedMatrix_opNorm2_le_of_orthogonal_diagonalization
    {m n : ℕ} {alpha L : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q) (hL : 0 ≤ L)
    (hd : ∀ i : Fin (m + n), |d i| ≤ L) :
    opNorm2 (lsScaledAugmentedMatrix alpha A) ≤ L :=
  opNorm2_le_of_finiteOpNorm2Le (lsScaledAugmentedMatrix alpha A) hL
    (lsScaledAugmentedMatrix_finiteOpNorm2Le_of_orthogonal_diagonalization
      hdiag hQ hL hd)
/-- Equations (20.18)-(20.19) inverse-candidate handoff: once a complete
    orthogonal diagonalization of `C(alpha)` has nonzero diagonal entries, the
    reciprocal diagonal in the same orthogonal basis is a two-sided inverse.
    This closes the algebraic inverse-candidate step, while still leaving the
    construction of the complete eigenbasis and multiplicity proof open. -/
theorem lsScaledAugmentedMatrix_isInverse_of_orthogonal_diagonalization
    {m n : ℕ} {alpha : ℝ} {A : Fin m → Fin n → ℝ}
    {Q : Fin (m + n) → Fin (m + n) → ℝ} {d : Fin (m + n) → ℝ}
    (hdiag : lsScaledAugmentedMatrix alpha A =
      finiteMatMul Q (finiteMatMul (finiteDiagonal d) (matTranspose Q)))
    (hQ : IsOrthogonal (m + n) Q)
    (hd : ∀ i : Fin (m + n), d i ≠ 0) :
    IsInverse (m + n) (lsScaledAugmentedMatrix alpha A)
      (finiteMatMul Q
        (finiteMatMul (finiteDiagonal fun i => (d i)⁻¹) (matTranspose Q))) :=
  isInverse_of_isOrthogonal_diagonalization hdiag hQ hd
/-- In a nonzero singular-pair certificate for (20.18), the left singular-vector
    side is nonzero whenever the right singular-vector side is nonzero. -/
theorem lsScaledAugmentedMatrix_singularPair_left_vector_ne_zero {m n : ℕ}
    {sigma : ℝ} {A : Fin m → Fin n → ℝ}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hsigma : sigma ≠ 0) (hv : v ≠ 0) :
    u ≠ 0 := by
  intro hu
  apply hv
  ext j
  have hleft : (∑ i : Fin m, A i j * u i) = sigma * v j :=
    congrFun hATu j
  have hzero : sigma * v j = 0 := by
    simpa [hu] using hleft.symm
  exact (mul_eq_zero.mp hzero).resolve_left hsigma
/-- Linear-combination certificate for the two singular-pair branches in
    (20.18).  For a nonzero singular pair and `alpha >= 0`, the positive- and
    negative-branch block vectors have only the trivial two-term linear
    combination equal to zero.  This is local independence infrastructure for
    the later global spectral multiplicity theorem. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_coefficients_eq_zero
    {m n : ℕ} {alpha sigma cPlus cMinus : ℝ}
    {A : Fin m → Fin n → ℝ} {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0)
    (hcomb :
      (fun k : Fin (m + n) =>
        cPlus *
            Fin.append
              (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
              (fun j => sigma * v j) k +
          cMinus *
            Fin.append
              (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
              (fun j => sigma * v j) k) = 0) :
    cPlus = 0 ∧ cMinus = 0 := by
  have hv_exists : ∃ j : Fin n, v j ≠ 0 := by
    by_contra hnone
    apply hv
    ext j
    by_contra hvj
    exact hnone ⟨j, hvj⟩
  have hu : u ≠ 0 :=
    lsScaledAugmentedMatrix_singularPair_left_vector_ne_zero
      (hATu := hATu) hsigma hv
  have hu_exists : ∃ i : Fin m, u i ≠ 0 := by
    by_contra hnone
    apply hu
    ext i
    by_contra hui
    exact hnone ⟨i, hui⟩
  rcases hv_exists with ⟨j, hvj⟩
  have hright := congrFun hcomb (Fin.natAdd m j)
  have hsum_mul : (cPlus + cMinus) * (sigma * v j) = 0 := by
    simpa [Fin.append_right, add_mul] using hright
  have hsum : cPlus + cMinus = 0 :=
    (mul_eq_zero.mp hsum_mul).resolve_right (mul_ne_zero hsigma hvj)
  rcases hu_exists with ⟨i, hui⟩
  have hleft := congrFun hcomb (Fin.castAdd n i)
  have hbranch_ne :
      lsScaledAugmentedEigenvaluePlus alpha sigma -
          lsScaledAugmentedEigenvalueMinus alpha sigma ≠ 0 := by
    exact sub_ne_zero.mpr
      (lsScaledAugmentedEigenvaluePlus_ne_minus_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha hsigma)
  have hprod :
      cPlus *
        ((lsScaledAugmentedEigenvaluePlus alpha sigma -
            lsScaledAugmentedEigenvalueMinus alpha sigma) * u i) = 0 := by
    have hminus : cMinus = -cPlus := by linarith
    rw [hminus] at hleft
    have hleft' :
        cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) +
            (-cPlus) *
              (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) = 0 := by
      simpa [Fin.append_left] using hleft
    nlinarith
  have hfac :
      (lsScaledAugmentedEigenvaluePlus alpha sigma -
          lsScaledAugmentedEigenvalueMinus alpha sigma) * u i ≠ 0 :=
    mul_ne_zero hbranch_ne hui
  have hcPlus : cPlus = 0 :=
    (mul_eq_zero.mp hprod).resolve_right hfac
  have hcMinus : cMinus = 0 := by linarith
  exact ⟨hcPlus, hcMinus⟩
/-- Linear-combination certificate separating the two singular-pair branches
    from a nonzero left-nullspace branch in (20.18).  This is local independence
    infrastructure for the later global spectral multiplicity theorem: it does
    not assert that a complete singular-vector/nullspace basis has been
    constructed. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_leftNull_coefficients_eq_zero
    {m n : ℕ} {alpha sigma cPlus cMinus cAlpha : ℝ}
    {A : Fin m → Fin n → ℝ} {u w : Fin m → ℝ} {v : Fin n → ℝ}
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hATw : ∀ j : Fin n, ∑ i : Fin m, A i j * w i = 0)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hcomb :
      (fun k : Fin (m + n) =>
        cPlus *
            Fin.append
              (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
              (fun j => sigma * v j) k +
          cMinus *
            Fin.append
              (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
              (fun j => sigma * v j) k +
          cAlpha * Fin.append w (0 : Fin n → ℝ) k) = 0) :
    cPlus = 0 ∧ cMinus = 0 ∧ cAlpha = 0 := by
  have hv_exists : ∃ j : Fin n, v j ≠ 0 := by
    by_contra hnone
    apply hv
    ext j
    by_contra hvj
    exact hnone ⟨j, hvj⟩
  rcases hv_exists with ⟨j, hvj⟩
  have hright := congrFun hcomb (Fin.natAdd m j)
  have hsum_mul : (cPlus + cMinus) * (sigma * v j) = 0 := by
    simpa [Fin.append_right, add_mul] using hright
  have hsum : cPlus + cMinus = 0 :=
    (mul_eq_zero.mp hsum_mul).resolve_right (mul_ne_zero hsigma hvj)
  have hminus : cMinus = -cPlus := by linarith
  rw [hminus] at hcomb
  have hleft_fun :
      (fun i : Fin m =>
        cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) +
          (-cPlus) * (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) +
          cAlpha * w i) = 0 := by
    ext i
    have hleft := congrFun hcomb (Fin.castAdd n i)
    simpa [Fin.append_left] using hleft
  have hsum_left := congrArg
    (fun z : Fin m → ℝ => ∑ i : Fin m, A i j * z i) hleft_fun
  have hsum_left_zero :
      (∑ i : Fin m,
        A i j *
          (cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) +
            (-cPlus) * (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) +
            cAlpha * w i)) = 0 := by
    simpa using hsum_left
  have hsum_plus :
      (∑ i : Fin m,
        A i j * (cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i))) =
        cPlus * lsScaledAugmentedEigenvaluePlus alpha sigma *
          (∑ i : Fin m, A i j * u i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum_minus :
      (∑ i : Fin m,
        A i j * ((-cPlus) * (lsScaledAugmentedEigenvalueMinus alpha sigma * u i))) =
        (-cPlus) * lsScaledAugmentedEigenvalueMinus alpha sigma *
          (∑ i : Fin m, A i j * u i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum_alpha :
      (∑ i : Fin m, A i j * (cAlpha * w i)) =
        cAlpha * (∑ i : Fin m, A i j * w i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum_eval :
      (∑ i : Fin m,
        A i j *
          (cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) +
            (-cPlus) * (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) +
            cAlpha * w i)) =
        cPlus *
          ((lsScaledAugmentedEigenvaluePlus alpha sigma -
              lsScaledAugmentedEigenvalueMinus alpha sigma) * (sigma * v j)) := by
    calc
      (∑ i : Fin m,
        A i j *
          (cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) +
            (-cPlus) * (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) +
            cAlpha * w i))
          = (∑ i : Fin m,
              A i j * (cPlus * (lsScaledAugmentedEigenvaluePlus alpha sigma * u i))) +
            (∑ i : Fin m,
              A i j * ((-cPlus) * (lsScaledAugmentedEigenvalueMinus alpha sigma * u i))) +
            (∑ i : Fin m, A i j * (cAlpha * w i)) := by
              rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = cPlus * lsScaledAugmentedEigenvaluePlus alpha sigma *
              (∑ i : Fin m, A i j * u i) +
            (-cPlus) * lsScaledAugmentedEigenvalueMinus alpha sigma *
              (∑ i : Fin m, A i j * u i) +
            cAlpha * (∑ i : Fin m, A i j * w i) := by
              rw [hsum_plus, hsum_minus, hsum_alpha]
      _ = cPlus * lsScaledAugmentedEigenvaluePlus alpha sigma * (sigma * v j) +
            (-cPlus) * lsScaledAugmentedEigenvalueMinus alpha sigma * (sigma * v j) +
            cAlpha * 0 := by
              rw [congrFun hATu j, hATw j]
      _ = cPlus *
          ((lsScaledAugmentedEigenvaluePlus alpha sigma -
              lsScaledAugmentedEigenvalueMinus alpha sigma) * (sigma * v j)) := by
              ring
  have hcPlus_prod :
      cPlus *
          ((lsScaledAugmentedEigenvaluePlus alpha sigma -
              lsScaledAugmentedEigenvalueMinus alpha sigma) * (sigma * v j)) = 0 := by
    rw [← hsum_eval]
    exact hsum_left_zero
  have hbranch_ne :
      lsScaledAugmentedEigenvaluePlus alpha sigma -
          lsScaledAugmentedEigenvalueMinus alpha sigma ≠ 0 := by
    exact sub_ne_zero.mpr
      (lsScaledAugmentedEigenvaluePlus_ne_minus_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha hsigma)
  have hfac :
      (lsScaledAugmentedEigenvaluePlus alpha sigma -
          lsScaledAugmentedEigenvalueMinus alpha sigma) * (sigma * v j) ≠ 0 :=
    mul_ne_zero hbranch_ne (mul_ne_zero hsigma hvj)
  have hcPlus : cPlus = 0 :=
    (mul_eq_zero.mp hcPlus_prod).resolve_right hfac
  have hcMinus : cMinus = 0 := by linarith
  have hAlpha_w : (fun i : Fin m => cAlpha * w i) = 0 := by
    rw [hcPlus] at hleft_fun
    simpa using hleft_fun
  have hcAlpha : cAlpha = 0 := by
    by_contra hc
    apply hw
    ext i
    have hi := congrFun hAlpha_w i
    exact (mul_eq_zero.mp hi).resolve_left hc
  exact ⟨hcPlus, hcMinus, hcAlpha⟩
/-- Source-normalized linear-combination certificate for the two singular-pair
    branches in (20.18).  This is the same independence content as
    `lsScaledAugmentedMatrix_singularPair_plus_minus_coefficients_eq_zero`,
    but stated for the printed vectors `[u; (sigma / lambda_\pm) v]`. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_coefficients_eq_zero
    {m n : ℕ} {alpha sigma cPlus cMinus : ℝ}
    {A : Fin m → Fin n → ℝ} {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0)
    (hcomb :
      (fun k : Fin (m + n) =>
        cPlus *
            Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k +
          cMinus *
            Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) =
        0) :
    cPlus = 0 ∧ cMinus = 0 := by
  have hplus_ne :
      lsScaledAugmentedEigenvaluePlus alpha sigma ≠ 0 :=
    lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  have hminus_ne :
      lsScaledAugmentedEigenvalueMinus alpha sigma ≠ 0 :=
    lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  have hcombScaled :
      (fun k : Fin (m + n) =>
        (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
              (fun j => sigma * v j) k +
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
              (fun j => sigma * v j) k) = 0 := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (m + n) =>
        (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
              (fun j => sigma * v j) k +
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
              (fun j => sigma * v j) k = 0) ?top ?bottom k
    · intro i
      have htop := congrFun hcomb (Fin.castAdd n i)
      have hplus :
          (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
              (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) =
            cPlus * u i := by
        field_simp [hplus_ne]
      have hminus :
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
              (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) =
            cMinus * u i := by
        field_simp [hminus_ne]
      simpa [Fin.append_left, hplus, hminus] using htop
    · intro j
      have hright := congrFun hcomb (Fin.natAdd m j)
      have hplus :
          (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
              (sigma * v j) =
            cPlus *
              ((sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) := by
        ring
      have hminus :
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
              (sigma * v j) =
            cMinus *
              ((sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) := by
        ring
      simpa [Fin.append_right, hplus, hminus] using hright
  rcases
    lsScaledAugmentedMatrix_singularPair_plus_minus_coefficients_eq_zero
      (hATu := hATu) halpha hsigma hv hcombScaled with
    ⟨hplusCoeff, hminusCoeff⟩
  have hcPlus : cPlus = 0 := by
    have hmul := congrArg
      (fun t => t * lsScaledAugmentedEigenvaluePlus alpha sigma) hplusCoeff
    field_simp [hplus_ne] at hmul
    simpa using hmul
  have hcMinus : cMinus = 0 := by
    have hmul := congrArg
      (fun t => t * lsScaledAugmentedEigenvalueMinus alpha sigma) hminusCoeff
    field_simp [hminus_ne] at hmul
    simpa using hmul
  exact ⟨hcPlus, hcMinus⟩
/-- Source-normalized linear-combination certificate separating the two printed
    singular-pair branches from a nonzero left-nullspace branch in (20.18).
    This is local independence infrastructure only; it does not assert a global
    eigenbasis or the source multiplicity count. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_leftNull_normalized_coefficients_eq_zero
    {m n : ℕ} {alpha sigma cPlus cMinus cAlpha : ℝ}
    {A : Fin m → Fin n → ℝ} {u w : Fin m → ℝ} {v : Fin n → ℝ}
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hATw : ∀ j : Fin n, ∑ i : Fin m, A i j * w i = 0)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (hcomb :
      (fun k : Fin (m + n) =>
        cPlus *
            Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k +
          cMinus *
            Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k +
          cAlpha * Fin.append w (0 : Fin n → ℝ) k) = 0) :
    cPlus = 0 ∧ cMinus = 0 ∧ cAlpha = 0 := by
  have hplus_ne :
      lsScaledAugmentedEigenvaluePlus alpha sigma ≠ 0 :=
    lsScaledAugmentedEigenvaluePlus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  have hminus_ne :
      lsScaledAugmentedEigenvalueMinus alpha sigma ≠ 0 :=
    lsScaledAugmentedEigenvalueMinus_ne_zero_of_sigma_ne_zero
      (alpha := alpha) (sigma := sigma) halpha hsigma
  have hcombScaled :
      (fun k : Fin (m + n) =>
        (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
              (fun j => sigma * v j) k +
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
              (fun j => sigma * v j) k +
          cAlpha * Fin.append w (0 : Fin n → ℝ) k) = 0 := by
    ext k
    refine Fin.addCases
      (motive := fun k : Fin (m + n) =>
        (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvaluePlus alpha sigma * u i)
              (fun j => sigma * v j) k +
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
            Fin.append
              (fun i => lsScaledAugmentedEigenvalueMinus alpha sigma * u i)
              (fun j => sigma * v j) k +
          cAlpha * Fin.append w (0 : Fin n → ℝ) k = 0) ?top ?bottom k
    · intro i
      have htop := congrFun hcomb (Fin.castAdd n i)
      have hplus :
          (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
              (lsScaledAugmentedEigenvaluePlus alpha sigma * u i) =
            cPlus * u i := by
        field_simp [hplus_ne]
      have hminus :
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
              (lsScaledAugmentedEigenvalueMinus alpha sigma * u i) =
            cMinus * u i := by
        field_simp [hminus_ne]
      simpa [Fin.append_left, hplus, hminus] using htop
    · intro j
      have hright := congrFun hcomb (Fin.natAdd m j)
      have hplus :
          (cPlus / lsScaledAugmentedEigenvaluePlus alpha sigma) *
              (sigma * v j) =
            cPlus *
              ((sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) := by
        ring
      have hminus :
          (cMinus / lsScaledAugmentedEigenvalueMinus alpha sigma) *
              (sigma * v j) =
            cMinus *
              ((sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) := by
        ring
      simpa [Fin.append_right, hplus, hminus] using hright
  rcases
    lsScaledAugmentedMatrix_singularPair_plus_minus_leftNull_coefficients_eq_zero
      (hATu := hATu) hATw halpha hsigma hv hw hcombScaled with
    ⟨hplusCoeff, hminusCoeff, hcAlpha⟩
  have hcPlus : cPlus = 0 := by
    have hmul := congrArg
      (fun t => t * lsScaledAugmentedEigenvaluePlus alpha sigma) hplusCoeff
    field_simp [hplus_ne] at hmul
    simpa using hmul
  have hcMinus : cMinus = 0 := by
    have hmul := congrArg
      (fun t => t * lsScaledAugmentedEigenvalueMinus alpha sigma) hminusCoeff
    field_simp [hminus_ne] at hmul
    simpa using hmul
  exact ⟨hcPlus, hcMinus, hcAlpha⟩
/-- The remaining `alpha` eigenvalue action in (20.18): any vector in the left
    nullspace of `A` gives `[u; 0]` scaled by `alpha` under `C(alpha)`. The
    source multiplicity `m - n` requires a separate rank/nullity basis theorem,
    which is intentionally not hidden here. -/
theorem lsScaledAugmentedMatrix_leftNull_eigenvector {m n : ℕ} (alpha : ℝ)
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ)
    (hATu : ∀ j : Fin n, ∑ i : Fin m, A i j * u i = 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u (0 : Fin n → ℝ)) =
      fun k => alpha * Fin.append u (0 : Fin n → ℝ) k := by
  rw [lsScaledAugmentedMatrix_mulVec]
  ext k
  refine Fin.addCases
    (motive := fun k : Fin (m + n) =>
      Fin.append
          (fun i : Fin m => alpha * u i + rectMatMulVec A (0 : Fin n → ℝ) i)
          (fun j : Fin n => ∑ i : Fin m, A i j * u i) k =
        alpha * Fin.append u (0 : Fin n → ℝ) k)
    ?left ?right k
  · intro i
    simp [Fin.append_left, rectMatMulVec]
  · intro j
    simp [Fin.append_right, hATu j]
/-- The left-nullspace vector `[u; 0]` used for the `alpha` branch in (20.18)
    is nonzero whenever `u` is nonzero. -/
theorem lsScaledAugmentedMatrix_leftNull_vector_ne_zero {m n : ℕ}
    (u : Fin m → ℝ) (hu : u ≠ 0) :
    Fin.append u (0 : Fin n → ℝ) ≠ 0 := by
  intro hzero
  apply hu
  ext i
  have hleft := congrFun hzero (Fin.castAdd n i)
  simpa [Fin.append_left] using hleft
/-- Packaged left-nullspace eigenpair certificate for the `alpha` branch in
    (20.18): a nonzero left-null vector gives both the block-action identity
    for `C(alpha)` and a nonzero block vector. -/
theorem lsScaledAugmentedMatrix_leftNull_eigenpair {m n : ℕ} (alpha : ℝ)
    (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ)
    (hATu : ∀ j : Fin n, ∑ i : Fin m, A i j * u i = 0)
    (hu : u ≠ 0) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (Fin.append u (0 : Fin n → ℝ)) =
      fun k => alpha * Fin.append u (0 : Fin n → ℝ) k) ∧
      Fin.append u (0 : Fin n → ℝ) ≠ 0 := by
  exact
    ⟨lsScaledAugmentedMatrix_leftNull_eigenvector alpha A u hATu,
      lsScaledAugmentedMatrix_leftNull_vector_ne_zero u hu⟩
/-- Source-facing dot-product expansion for the normalized singular-pair
    branch vectors in Björck's eigenvalue formula (20.18).  It reduces
    orthogonality of appended branch vectors to the dot products of their
    left and right singular-vector components. -/
theorem lsScaledAugmentedMatrix_singularPair_normalized_dot_eq {m n : ℕ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ) (beta gamma : ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u (fun j => beta * v j) k *
        Fin.append w (fun j => gamma * z j) k) =
      (∑ i : Fin m, u i * w i) +
        beta * gamma * (∑ j : Fin n, v j * z j) :=
  finAppend_sum_mul_smul_eq u w v z beta gamma
/-- If both component singular-vector dot products vanish, then the
    corresponding source-normalized appended branch vectors in (20.18) are
    orthogonal. -/
theorem lsScaledAugmentedMatrix_singularPair_normalized_dot_eq_zero_of_orthogonal
    {m n : ℕ} (u w : Fin m → ℝ) (v z : Fin n → ℝ) (beta gamma : ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u (fun j => beta * v j) k *
        Fin.append w (fun j => gamma * z j) k) = 0 := by
  rw [lsScaledAugmentedMatrix_singularPair_normalized_dot_eq, hleft, hright]
  ring
/-- Squared Euclidean norm of a source-normalized appended branch vector in
    (20.18), reduced to the squared norms of its left and right singular-vector
    components. -/
theorem lsScaledAugmentedMatrix_singularPair_normalized_vecNorm2Sq_eq
    {m n : ℕ} (u : Fin m → ℝ) (v : Fin n → ℝ) (beta : ℝ) :
    vecNorm2Sq (Fin.append u (fun j => beta * v j)) =
      vecNorm2Sq u + beta ^ 2 * vecNorm2Sq v := by
  unfold vecNorm2Sq
  simp only [pow_two]
  rw [lsScaledAugmentedMatrix_singularPair_normalized_dot_eq]
/-- Positive-branch squared Euclidean norm formula for the printed
    source-normalized singular-pair vector in (20.18). -/
theorem lsScaledAugmentedMatrix_singularPair_plus_normalized_vecNorm2Sq_eq
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    vecNorm2Sq
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)) =
      vecNorm2Sq u +
        (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) ^ 2 * vecNorm2Sq v :=
  lsScaledAugmentedMatrix_singularPair_normalized_vecNorm2Sq_eq u v
    (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma)
/-- Negative-branch squared Euclidean norm formula for the printed
    source-normalized singular-pair vector in (20.18). -/
theorem lsScaledAugmentedMatrix_singularPair_minus_normalized_vecNorm2Sq_eq
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    vecNorm2Sq
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)) =
      vecNorm2Sq u +
        (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) ^ 2 * vecNorm2Sq v :=
  lsScaledAugmentedMatrix_singularPair_normalized_vecNorm2Sq_eq u v
    (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma)
/-- If both singular-vector components are unit in squared Euclidean norm, then
    the positive printed branch vector in (20.18) has squared norm
    `1 + (sigma/lambda_+)^2`. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_normalized_vecNorm2Sq_eq_one_add_sq_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    vecNorm2Sq
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)) =
      1 + (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) ^ 2 := by
  rw [lsScaledAugmentedMatrix_singularPair_plus_normalized_vecNorm2Sq_eq,
    hu, hv]
  ring
/-- If both singular-vector components are unit in squared Euclidean norm, then
    the negative printed branch vector in (20.18) has squared norm
    `1 + (sigma/lambda_-)^2`. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_normalized_vecNorm2Sq_eq_one_add_sq_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    vecNorm2Sq
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)) =
      1 + (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) ^ 2 := by
  rw [lsScaledAugmentedMatrix_singularPair_minus_normalized_vecNorm2Sq_eq,
    hu, hv]
  ring
/-- Squared Euclidean norm of a left-nullspace branch vector `[u;0]` in the
    `alpha` eigenspace of (20.18). -/
theorem lsScaledAugmentedMatrix_leftNull_vecNorm2Sq_eq {m n : ℕ}
    (u : Fin m → ℝ) :
    vecNorm2Sq (Fin.append u (0 : Fin n → ℝ)) = vecNorm2Sq u := by
  unfold vecNorm2Sq
  simp only [pow_two]
  rw [finAppend_sum_mul_eq]
  simp
/-- A unit left-nullspace component gives a unit `[u;0]` branch vector in the
    `alpha` eigenspace of (20.18). -/
theorem lsScaledAugmentedMatrix_leftNull_vecNorm2Sq_eq_one_of_unit_component
    {m n : ℕ} (u : Fin m → ℝ) (hu : vecNorm2Sq u = 1) :
    vecNorm2Sq (Fin.append u (0 : Fin n → ℝ)) = 1 := by
  rw [lsScaledAugmentedMatrix_leftNull_vecNorm2Sq_eq, hu]
/-- Unit component data make the positive printed branch vector in (20.18)
    nonzero in squared Euclidean norm. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_normalized_vecNorm2Sq_pos_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    0 <
      vecNorm2Sq
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)) := by
  rw [
    lsScaledAugmentedMatrix_singularPair_plus_normalized_vecNorm2Sq_eq_one_add_sq_of_unit_components
      u v hu hv]
  nlinarith [sq_nonneg (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma)]
/-- Unit component data make the negative printed branch vector in (20.18)
    nonzero in squared Euclidean norm. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_normalized_vecNorm2Sq_pos_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    0 <
      vecNorm2Sq
        (Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)) := by
  rw [
    lsScaledAugmentedMatrix_singularPair_minus_normalized_vecNorm2Sq_eq_one_add_sq_of_unit_components
      u v hu hv]
  nlinarith [sq_nonneg (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma)]
/-- A unit left-nullspace component makes the `[u;0]` branch in (20.18)
    nonzero in squared Euclidean norm. -/
theorem lsScaledAugmentedMatrix_leftNull_vecNorm2Sq_pos_of_unit_component
    {m n : ℕ} (u : Fin m → ℝ) (hu : vecNorm2Sq u = 1) :
    0 < vecNorm2Sq (Fin.append u (0 : Fin n → ℝ)) := by
  rw [lsScaledAugmentedMatrix_leftNull_vecNorm2Sq_eq_one_of_unit_component u hu]
  norm_num
/-- Self-normalizing the positive printed branch vector in (20.18) gives unit
    Euclidean norm, once the component singular vectors have unit squared norm. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    vecNorm2
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) =
      1 := by
  apply vecNorm2_inv_smul_self_of_pos
  unfold vecNorm2
  exact Real.sqrt_pos.mpr
    (lsScaledAugmentedMatrix_singularPair_plus_normalized_vecNorm2Sq_pos_of_unit_components
      u v hu hv)
/-- Self-normalizing the negative printed branch vector in (20.18) gives unit
    Euclidean norm, once the component singular vectors have unit squared norm. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    vecNorm2
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) =
      1 := by
  apply vecNorm2_inv_smul_self_of_pos
  unfold vecNorm2
  exact Real.sqrt_pos.mpr
    (lsScaledAugmentedMatrix_singularPair_minus_normalized_vecNorm2Sq_pos_of_unit_components
      u v hu hv)
/-- Self-normalizing a left-nullspace branch vector `[u;0]` in (20.18) gives
    unit Euclidean norm when the left component has unit squared norm. -/
theorem
    lsScaledAugmentedMatrix_leftNull_rescaled_vecNorm2_eq_one_of_unit_component
    {m n : ℕ} (u : Fin m → ℝ) (hu : vecNorm2Sq u = 1) :
    vecNorm2
        (fun k : Fin (m + n) =>
          (vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
            Fin.append u (0 : Fin n → ℝ) k) =
      1 := by
  apply vecNorm2_inv_smul_self_of_pos
  unfold vecNorm2
  exact Real.sqrt_pos.mpr
    (lsScaledAugmentedMatrix_leftNull_vecNorm2Sq_pos_of_unit_component u hu)
/-- Same-branch positive/positive dot-product expansion for the source-normalized
    singular-pair vectors in (20.18), allowing different singular values and
    different left/right singular-vector components. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_dot_eq
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvaluePlus alpha tau) * z j) k) =
      (∑ i : Fin m, u i * w i) +
        (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) *
          (tau / lsScaledAugmentedEigenvaluePlus alpha tau) *
            (∑ j : Fin n, v j * z j) :=
  lsScaledAugmentedMatrix_singularPair_normalized_dot_eq u w v z
    (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma)
    (tau / lsScaledAugmentedEigenvaluePlus alpha tau)
/-- Component-orthogonality corollary of
    `lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_dot_eq`.  This is
    the same-eigenvalue multiplicity case needed by a later complete orthogonal
    singular-vector basis for (20.18). -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvaluePlus alpha tau) * z j) k) = 0 := by
  rw [lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_dot_eq,
    hleft, hright]
  ring
/-- Mixed positive/negative dot-product expansion for source-normalized
    singular-pair vectors in (20.18), allowing different singular values and
    different left/right singular-vector components. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j) k) =
      (∑ i : Fin m, u i * w i) +
        (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) *
          (tau / lsScaledAugmentedEigenvalueMinus alpha tau) *
            (∑ j : Fin n, v j * z j) :=
  lsScaledAugmentedMatrix_singularPair_normalized_dot_eq u w v z
    (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma)
    (tau / lsScaledAugmentedEigenvalueMinus alpha tau)
/-- Component-orthogonality corollary of
    `lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq`. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j) k) = 0 := by
  rw [lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq,
    hleft, hright]
  ring
/-- Same-branch negative/negative dot-product expansion for source-normalized
    singular-pair vectors in (20.18), allowing different singular values and
    different left/right singular-vector components. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_dot_eq
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j) k) =
      (∑ i : Fin m, u i * w i) +
        (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) *
          (tau / lsScaledAugmentedEigenvalueMinus alpha tau) *
            (∑ j : Fin n, v j * z j) :=
  lsScaledAugmentedMatrix_singularPair_normalized_dot_eq u w v z
    (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma)
    (tau / lsScaledAugmentedEigenvalueMinus alpha tau)
/-- Component-orthogonality corollary of
    `lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_dot_eq`.  This
    handles negative-branch eigenspace multiplicities in the later (20.18)
    complete-basis route. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j) k) = 0 := by
  rw [lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_dot_eq,
    hleft, hright]
  ring
/-- Dot-product expansion between a positive source-normalized branch vector
    and a left-nullspace branch vector `[w;0]` in (20.18). -/
theorem lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_dot_eq
    {m n : ℕ} {alpha sigma : ℝ}
    (u w : Fin m → ℝ) (v : Fin n → ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w (0 : Fin n → ℝ) k) =
      (∑ i : Fin m, u i * w i) := by
  rw [finAppend_sum_mul_eq]
  simp
/-- Component-orthogonality corollary for a positive source-normalized branch
    vector and a left-nullspace branch vector in (20.18). -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_dot_eq_zero_of_left_orthogonal
    {m n : ℕ} {alpha sigma : ℝ}
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w (0 : Fin n → ℝ) k) = 0 := by
  rw [lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_dot_eq,
    hleft]
/-- Dot-product expansion between a negative source-normalized branch vector
    and a left-nullspace branch vector `[w;0]` in (20.18). -/
theorem lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_dot_eq
    {m n : ℕ} {alpha sigma : ℝ}
    (u w : Fin m → ℝ) (v : Fin n → ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k *
        Fin.append w (0 : Fin n → ℝ) k) =
      (∑ i : Fin m, u i * w i) := by
  rw [finAppend_sum_mul_eq]
  simp
/-- Component-orthogonality corollary for a negative source-normalized branch
    vector and a left-nullspace branch vector in (20.18). -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_dot_eq_zero_of_left_orthogonal
    {m n : ℕ} {alpha sigma : ℝ}
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k *
        Fin.append w (0 : Fin n → ℝ) k) = 0 := by
  rw [lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_dot_eq,
    hleft]
/-- Dot-product expansion for two left-nullspace branch vectors `[u;0]` and
    `[w;0]` in the `alpha` eigenspace of (20.18). -/
theorem lsScaledAugmentedMatrix_leftNull_leftNull_dot_eq {m n : ℕ}
    (u w : Fin m → ℝ) :
    (∑ k : Fin (m + n),
      Fin.append u (0 : Fin n → ℝ) k *
        Fin.append w (0 : Fin n → ℝ) k) =
      (∑ i : Fin m, u i * w i) := by
  rw [finAppend_sum_mul_eq]
  simp
/-- Component-orthogonality corollary for two left-nullspace branch vectors in
    the `alpha` eigenspace of (20.18). -/
theorem lsScaledAugmentedMatrix_leftNull_leftNull_dot_eq_zero_of_left_orthogonal
    {m n : ℕ} (u w : Fin m → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0) :
    (∑ k : Fin (m + n),
      Fin.append u (0 : Fin n → ℝ) k *
        Fin.append w (0 : Fin n → ℝ) k) = 0 := by
  rw [lsScaledAugmentedMatrix_leftNull_leftNull_dot_eq, hleft]
/-- Component orthogonality is preserved after inverse-2-norm rescaling of two
    positive source-normalized branch vectors from (20.18). -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) *
      ((vecNorm2
          (Fin.append w
            (fun j =>
              (tau / lsScaledAugmentedEigenvaluePlus alpha tau) * z j)))⁻¹ *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvaluePlus alpha tau) * z j) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_dot_eq_zero_of_component_orthogonal
      u w v z hleft hright
/-- Component orthogonality is preserved after inverse-2-norm rescaling of a
    positive and a negative source-normalized branch vector from (20.18). -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) *
      ((vecNorm2
          (Fin.append w
            (fun j =>
              (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j)))⁻¹ *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq_zero_of_component_orthogonal
      u w v z hleft hright
/-- Component orthogonality is preserved after inverse-2-norm rescaling of two
    negative source-normalized branch vectors from (20.18). -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {alpha sigma tau : ℝ}
    (u w : Fin m → ℝ) (v z : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0)
    (hright : (∑ j : Fin n, v j * z j) = 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) *
      ((vecNorm2
          (Fin.append w
            (fun j =>
              (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j)))⁻¹ *
        Fin.append w
          (fun j => (tau / lsScaledAugmentedEigenvalueMinus alpha tau) * z j) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_dot_eq_zero_of_component_orthogonal
      u w v z hleft hright
/-- Left-component orthogonality is preserved after inverse-2-norm rescaling of
    a positive source-normalized branch vector and a left-null branch vector. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_rescaled_dot_eq_zero_of_left_orthogonal
    {m n : ℕ} {alpha sigma : ℝ}
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) *
      ((vecNorm2 (Fin.append w (0 : Fin n → ℝ)))⁻¹ *
        Fin.append w (0 : Fin n → ℝ) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_dot_eq_zero_of_left_orthogonal
      u w v hleft
/-- Left-component orthogonality is preserved after inverse-2-norm rescaling of
    a negative source-normalized branch vector and a left-null branch vector. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_rescaled_dot_eq_zero_of_left_orthogonal
    {m n : ℕ} {alpha sigma : ℝ}
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) *
      ((vecNorm2 (Fin.append w (0 : Fin n → ℝ)))⁻¹ *
        Fin.append w (0 : Fin n → ℝ) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_dot_eq_zero_of_left_orthogonal
      u w v hleft
/-- Left-component orthogonality is preserved after inverse-2-norm rescaling of
    two left-null branch vectors `[u;0]` and `[w;0]` from (20.18). -/
theorem
    lsScaledAugmentedMatrix_leftNull_leftNull_rescaled_dot_eq_zero_of_left_orthogonal
    {m n : ℕ} (u w : Fin m → ℝ)
    (hleft : (∑ i : Fin m, u i * w i) = 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
        Fin.append u (0 : Fin n → ℝ) k) *
      ((vecNorm2 (Fin.append w (0 : Fin n → ℝ)))⁻¹ *
        Fin.append w (0 : Fin n → ℝ) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_leftNull_leftNull_dot_eq_zero_of_left_orthogonal
      u w hleft
/-- The inverse-2-norm rescaled positive branch vector in (20.18) remains an
    eigenvector of `C(alpha)` with eigenvalue `lambda_+`. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_eigenvector
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) =
      fun k => lsScaledAugmentedEigenvaluePlus alpha sigma *
        ((vecNorm2
            (Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
          Fin.append u
            (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) := by
  apply rectMatMulVec_vecNorm2_inv_smul_eigenvector
  exact
    lsScaledAugmentedMatrix_singularPair_plus_normalized_eigenvector
      alpha sigma A u v hAv hATu halpha hsigma
/-- The inverse-2-norm rescaled negative branch vector in (20.18) remains an
    eigenvector of `C(alpha)` with eigenvalue `lambda_-`. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_eigenvector
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) =
      fun k => lsScaledAugmentedEigenvalueMinus alpha sigma *
        ((vecNorm2
            (Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
          Fin.append u
            (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) := by
  apply rectMatMulVec_vecNorm2_inv_smul_eigenvector
  exact
    lsScaledAugmentedMatrix_singularPair_minus_normalized_eigenvector
      alpha sigma A u v hAv hATu halpha hsigma
/-- The inverse-2-norm rescaled left-nullspace branch vector `[u;0]` in (20.18)
    remains an eigenvector of `C(alpha)` with eigenvalue `alpha`. -/
theorem lsScaledAugmentedMatrix_leftNull_rescaled_eigenvector {m n : ℕ}
    (alpha : ℝ) (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ)
    (hATu : ∀ j : Fin n, ∑ i : Fin m, A i j * u i = 0) :
    rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (fun k : Fin (m + n) =>
          (vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
            Fin.append u (0 : Fin n → ℝ) k) =
      fun k => alpha *
        ((vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
          Fin.append u (0 : Fin n → ℝ) k) := by
  apply rectMatMulVec_vecNorm2_inv_smul_eigenvector
  exact lsScaledAugmentedMatrix_leftNull_eigenvector alpha A u hATu
/-- A unit positive branch in (20.18), packaged with both its rescaled
    eigenvector equation for `C(alpha)` and unit Euclidean norm.  This is
    orthonormal-basis infrastructure only; it does not assert completeness or
    the global multiplicity count. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_unit_eigenpair_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) =
      fun k => lsScaledAugmentedEigenvaluePlus alpha sigma *
        ((vecNorm2
            (Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
          Fin.append u
            (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k)) ∧
      vecNorm2
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) =
        1 := by
  exact
    ⟨lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_eigenvector
        A u v hAv hATu halpha hsigma,
      lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
        u v hu hv⟩
/-- A unit negative branch in (20.18), packaged with both its rescaled
    eigenvector equation for `C(alpha)` and unit Euclidean norm.  This is
    orthonormal-basis infrastructure only; it does not assert completeness or
    the global multiplicity count. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_unit_eigenpair_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) =
      fun k => lsScaledAugmentedEigenvalueMinus alpha sigma *
        ((vecNorm2
            (Fin.append u
              (fun j =>
                (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
          Fin.append u
            (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k)) ∧
      vecNorm2
        (fun k : Fin (m + n) =>
          (vecNorm2
              (Fin.append u
                (fun j =>
                  (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
            Fin.append u
              (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) =
        1 := by
  exact
    ⟨lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_eigenvector
        A u v hAv hATu halpha hsigma,
      lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
        u v hu hv⟩
/-- A unit left-null branch in (20.18), packaged with both its rescaled
    eigenvector equation for `C(alpha)` and unit Euclidean norm.  This is
    orthonormal-basis infrastructure only; it does not assert completeness or
    the global multiplicity count. -/
theorem lsScaledAugmentedMatrix_leftNull_rescaled_unit_eigenpair_of_unit_component
    {m n : ℕ} (alpha : ℝ) (A : Fin m → Fin n → ℝ) (u : Fin m → ℝ)
    (hATu : ∀ j : Fin n, ∑ i : Fin m, A i j * u i = 0)
    (hu : vecNorm2Sq u = 1) :
    (rectMatMulVec (lsScaledAugmentedMatrix alpha A)
        (fun k : Fin (m + n) =>
          (vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
            Fin.append u (0 : Fin n → ℝ) k) =
      fun k => alpha *
        ((vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
          Fin.append u (0 : Fin n → ℝ) k)) ∧
      vecNorm2
        (fun k : Fin (m + n) =>
          (vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
            Fin.append u (0 : Fin n → ℝ) k) =
        1 := by
  exact
    ⟨lsScaledAugmentedMatrix_leftNull_rescaled_eigenvector alpha A u hATu,
      lsScaledAugmentedMatrix_leftNull_rescaled_vecNorm2_eq_one_of_unit_component
        u hu⟩
/-- The inverse-2-norm rescaled positive branch vector in (20.18) is nonzero
    under unit component data. -/
theorem
    lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_vector_ne_zero_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    (fun k : Fin (m + n) =>
      (vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) ≠
      0 := by
  apply vecNorm2_eq_one_ne_zero
  exact
    lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
      u v hu hv
/-- The inverse-2-norm rescaled negative branch vector in (20.18) is nonzero
    under unit component data. -/
theorem
    lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_vector_ne_zero_of_unit_components
    {m n : ℕ} {alpha sigma : ℝ}
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hu : vecNorm2Sq u = 1) (hv : vecNorm2Sq v = 1) :
    (fun k : Fin (m + n) =>
      (vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) ≠
      0 := by
  apply vecNorm2_eq_one_ne_zero
  exact
    lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
      u v hu hv
/-- The inverse-2-norm rescaled left-null branch vector in (20.18) is nonzero
    under unit left-component data. -/
theorem lsScaledAugmentedMatrix_leftNull_rescaled_vector_ne_zero_of_unit_component
    {m n : ℕ} (u : Fin m → ℝ) (hu : vecNorm2Sq u = 1) :
    (fun k : Fin (m + n) =>
      (vecNorm2 (Fin.append u (0 : Fin n → ℝ)))⁻¹ *
        Fin.append u (0 : Fin n → ℝ) k) ≠ 0 := by
  apply vecNorm2_eq_one_ne_zero
  exact
    lsScaledAugmentedMatrix_leftNull_rescaled_vecNorm2_eq_one_of_unit_component
      u hu
/-- Orthogonality of the two source-normalized singular-pair branches in
    Björck's eigenvalue formula (20.18).  This is a source-facing spectral
    decomposition dependency: it proves the printed `lambda_+` and `lambda_-`
    vectors are orthogonal, but it still does not assert global multiplicities
    or completeness of the eigenbasis. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq_zero
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j =>
            (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append u
          (fun j =>
            (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) = 0 := by
  exact
    lsScaledAugmentedMatrix_eigenvectors_sum_mul_eq_zero
      (alpha := alpha) (lambda := lsScaledAugmentedEigenvaluePlus alpha sigma)
      (mu := lsScaledAugmentedEigenvalueMinus alpha sigma) A
      (x := Fin.append u
        (fun j =>
          (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j))
      (y := Fin.append u
        (fun j =>
          (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j))
      (lsScaledAugmentedMatrix_singularPair_plus_normalized_eigenvector
        alpha sigma A u v hAv hATu halpha hsigma)
      (lsScaledAugmentedMatrix_singularPair_minus_normalized_eigenvector
        alpha sigma A u v hAv hATu halpha hsigma)
      (lsScaledAugmentedEigenvaluePlus_ne_minus_of_sigma_ne_zero
        (alpha := alpha) (sigma := sigma) halpha hsigma)
/-- Orthogonality of the source-normalized positive singular-pair branch in
    (20.18) against the left-nullspace `alpha` branch. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_dot_eq_zero
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hATw : ∀ j : Fin n, ∑ i : Fin m, A i j * w i = 0)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j =>
            (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k *
        Fin.append w (0 : Fin n → ℝ) k) = 0 := by
  exact
    lsScaledAugmentedMatrix_eigenvectors_sum_mul_eq_zero
      (alpha := alpha) (lambda := lsScaledAugmentedEigenvaluePlus alpha sigma)
      (mu := alpha) A
      (x := Fin.append u
        (fun j =>
          (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j))
      (y := Fin.append w (0 : Fin n → ℝ))
      (lsScaledAugmentedMatrix_singularPair_plus_normalized_eigenvector
        alpha sigma A u v hAv hATu halpha hsigma)
      (lsScaledAugmentedMatrix_leftNull_eigenvector alpha A w hATw)
      (ne_of_gt
        (lsScaledAugmentedEigenvaluePlus_gt_alpha_of_sigma_ne_zero
          (alpha := alpha) (sigma := sigma) halpha hsigma))
/-- Orthogonality of the source-normalized negative singular-pair branch in
    (20.18) against the left-nullspace `alpha` branch. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_dot_eq_zero
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hATw : ∀ j : Fin n, ∑ i : Fin m, A i j * w i = 0)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    (∑ k : Fin (m + n),
      Fin.append u
          (fun j =>
            (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k *
        Fin.append w (0 : Fin n → ℝ) k) = 0 := by
  exact
    lsScaledAugmentedMatrix_eigenvectors_sum_mul_eq_zero
      (alpha := alpha) (lambda := lsScaledAugmentedEigenvalueMinus alpha sigma)
      (mu := alpha) A
      (x := Fin.append u
        (fun j =>
          (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j))
      (y := Fin.append w (0 : Fin n → ℝ))
      (lsScaledAugmentedMatrix_singularPair_minus_normalized_eigenvector
        alpha sigma A u v hAv hATu halpha hsigma)
      (lsScaledAugmentedMatrix_leftNull_eigenvector alpha A w hATw)
      (ne_of_lt
        (lsScaledAugmentedEigenvalueMinus_lt_alpha_of_sigma_ne_zero
          (alpha := alpha) (sigma := sigma) halpha hsigma))
/-- Orthogonality of the two source-normalized singular-pair branches in
    (20.18) is preserved after inverse-2-norm rescaling. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_rescaled_dot_eq_zero
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) *
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_dot_eq_zero
      A u v hAv hATu halpha hsigma
/-- Orthogonality of the source-normalized positive singular-pair branch and
    the left-nullspace branch in (20.18) is preserved after inverse-2-norm
    rescaling. -/
theorem lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_rescaled_dot_eq_zero
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hATw : ∀ j : Fin n, ∑ i : Fin m, A i j * w i = 0)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvaluePlus alpha sigma) * v j) k) *
      ((vecNorm2 (Fin.append w (0 : Fin n → ℝ)))⁻¹ *
        Fin.append w (0 : Fin n → ℝ) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_dot_eq_zero
      A u w v hAv hATu hATw halpha hsigma
/-- Orthogonality of the source-normalized negative singular-pair branch and
    the left-nullspace branch in (20.18) is preserved after inverse-2-norm
    rescaling. -/
theorem lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_rescaled_dot_eq_zero
    {m n : ℕ}
    {alpha sigma : ℝ} (A : Fin m → Fin n → ℝ)
    (u w : Fin m → ℝ) (v : Fin n → ℝ)
    (hAv : rectMatMulVec A v = fun i => sigma * u i)
    (hATu : (fun j : Fin n => ∑ i : Fin m, A i j * u i) =
      fun j => sigma * v j)
    (hATw : ∀ j : Fin n, ∑ i : Fin m, A i j * w i = 0)
    (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0) :
    (∑ k : Fin (m + n),
      ((vecNorm2
          (Fin.append u
            (fun j =>
              (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j)))⁻¹ *
        Fin.append u
          (fun j => (sigma / lsScaledAugmentedEigenvalueMinus alpha sigma) * v j) k) *
      ((vecNorm2 (Fin.append w (0 : Fin n → ℝ)))⁻¹ *
        Fin.append w (0 : Fin n → ℝ) k)) =
      0 := by
  apply vecNorm2_inv_smul_dot_eq_zero_of_dot_eq_zero
  exact
    lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_dot_eq_zero
      A u w v hAv hATu hATw halpha hsigma
/-- Branch-indexed inverse-2-norm rescaled eigenvectors for Higham, 2nd ed.,
    Chapter 20, equation (20.18).  The index type is
    `(plus singular branches) ⊕ (minus singular branches) ⊕ (left-null
    branches)`, written as `Sum (Sum ι ι) κ`.  This records the actual family
    shape needed for the later complete-basis proof; it does not assert that
    the family is complete. -/
noncomputable def lsScaledAugmentedMatrixBranchVector {m n : ℕ} {ι κ : Type*}
    (alpha : ℝ) (sigma : ι → ℝ)
    (u : ι → Fin m → ℝ) (v : ι → Fin n → ℝ)
    (w : κ → Fin m → ℝ) :
    Sum (Sum ι ι) κ → Fin (m + n) → ℝ
  | Sum.inl (Sum.inl i) =>
      fun k : Fin (m + n) =>
        (vecNorm2
            (Fin.append (u i)
              (fun j : Fin n =>
                (sigma i / lsScaledAugmentedEigenvaluePlus alpha (sigma i)) *
                  v i j)))⁻¹ *
          Fin.append (u i)
            (fun j : Fin n =>
              (sigma i / lsScaledAugmentedEigenvaluePlus alpha (sigma i)) *
                v i j) k
  | Sum.inl (Sum.inr i) =>
      fun k : Fin (m + n) =>
        (vecNorm2
            (Fin.append (u i)
              (fun j : Fin n =>
                (sigma i / lsScaledAugmentedEigenvalueMinus alpha (sigma i)) *
                  v i j)))⁻¹ *
          Fin.append (u i)
            (fun j : Fin n =>
              (sigma i / lsScaledAugmentedEigenvalueMinus alpha (sigma i)) *
                v i j) k
  | Sum.inr k =>
      fun r : Fin (m + n) =>
        (vecNorm2 (Fin.append (w k) (0 : Fin n → ℝ)))⁻¹ *
          Fin.append (w k) (0 : Fin n → ℝ) r
/-- Displayed eigenvalue attached to a branch vector in Higham, 2nd ed.,
    Chapter 20, equation (20.18). -/
noncomputable def lsScaledAugmentedMatrixBranchEigenvalue {ι κ : Type*}
    (alpha : ℝ) (sigma : ι → ℝ) :
    Sum (Sum ι ι) κ → ℝ
  | Sum.inl (Sum.inl i) => lsScaledAugmentedEigenvaluePlus alpha (sigma i)
  | Sum.inl (Sum.inr i) => lsScaledAugmentedEigenvalueMinus alpha (sigma i)
  | Sum.inr _ => alpha
/-- Unit component data make every branch-indexed vector in the (20.18)
    family a Euclidean unit vector.  This is one half of the future
    orthonormal-column construction for the complete `Q` matrix. -/
theorem lsScaledAugmentedMatrixBranchVector_vecNorm2_eq_one_of_unit_components
    {m n : ℕ} {ι κ : Type*} {alpha : ℝ} {sigma : ι → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (hu : ∀ i : ι, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : ι, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : κ, vecNorm2Sq (w k) = 1) :
    ∀ a : Sum (Sum ι ι) κ,
      vecNorm2 (lsScaledAugmentedMatrixBranchVector alpha sigma u v w a) = 1 := by
  intro a
  rcases a with ((i | i) | k)
  · simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
        (alpha := alpha) (sigma := sigma i) (u i) (v i) (hu i) (hv i)
  · simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_vecNorm2_eq_one_of_unit_components
        (alpha := alpha) (sigma := sigma i) (u i) (v i) (hu i) (hv i)
  · simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_leftNull_rescaled_vecNorm2_eq_one_of_unit_component
        (m := m) (n := n) (w k) (hw k)
/-- Every branch-indexed vector in the (20.18) family is an eigenvector of
    `C(alpha)` for its displayed branch eigenvalue, assuming supplied
    singular-pair equations for the `ι` branches and supplied left-nullspace
    equations for the `κ` branches.  Completeness and multiplicity are still
    separate obligations. -/
theorem lsScaledAugmentedMatrixBranchVector_eigenvector
    {m n : ℕ} {ι κ : Type*} {alpha : ℝ} {sigma : ι → ℝ}
    {A : Fin m → Fin n → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (halpha : 0 ≤ alpha) (hsigma : ∀ i : ι, sigma i ≠ 0) :
    ∀ a : Sum (Sum ι ι) κ,
      rectMatMulVec (lsScaledAugmentedMatrix alpha A)
          (lsScaledAugmentedMatrixBranchVector alpha sigma u v w a) =
        fun r : Fin (m + n) =>
          lsScaledAugmentedMatrixBranchEigenvalue alpha sigma a *
            lsScaledAugmentedMatrixBranchVector alpha sigma u v w a r := by
  intro a
  rcases a with ((i | i) | k)
  · simpa [lsScaledAugmentedMatrixBranchVector,
      lsScaledAugmentedMatrixBranchEigenvalue] using
      lsScaledAugmentedMatrix_singularPair_plus_normalized_rescaled_eigenvector
        A (u i) (v i) (hAv i) (hATu i) halpha (hsigma i)
  · simpa [lsScaledAugmentedMatrixBranchVector,
      lsScaledAugmentedMatrixBranchEigenvalue] using
      lsScaledAugmentedMatrix_singularPair_minus_normalized_rescaled_eigenvector
        A (u i) (v i) (hAv i) (hATu i) halpha (hsigma i)
  · simpa [lsScaledAugmentedMatrixBranchVector,
      lsScaledAugmentedMatrixBranchEigenvalue] using
      lsScaledAugmentedMatrix_leftNull_rescaled_eigenvector
        alpha A (w k) (hATw k)
/-- Pairwise dot-zero statement for the branch-indexed (20.18) family.  The
    hypotheses are exactly the component orthogonality data for distinct
    singular-vector branches, the left-nullspace component orthogonality, and
    the singular-pair/left-null equations needed for the cross-branch
    eigenvalue-orthogonality cases.  This still does not assert that the index
    type is complete. -/
theorem
    lsScaledAugmentedMatrixBranchVector_pairwise_dot_eq_zero_of_component_orthogonal
    {m n : ℕ} {ι κ : Type*} {alpha : ℝ} {sigma : ι → ℝ}
    {A : Fin m → Fin n → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (hleft : ∀ i j : ι, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : ι, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : κ, k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (halpha : 0 ≤ alpha) (hsigma : ∀ i : ι, sigma i ≠ 0) :
    ∀ a b : Sum (Sum ι ι) κ, a ≠ b →
      (∑ r : Fin (m + n),
        lsScaledAugmentedMatrixBranchVector alpha sigma u v w a r *
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w b r) = 0 := by
  classical
  have hdot_comm :
      ∀ x y : Fin (m + n) → ℝ,
        (∑ r : Fin (m + n), x r * y r) =
          ∑ r : Fin (m + n), y r * x r := by
    intro x y
    apply Finset.sum_congr rfl
    intro r _
    ring
  intro a b hab
  rcases a with ((i | i) | k) <;> rcases b with ((j | j) | l)
  · have hij : i ≠ j := by
      intro hij
      apply hab
      simp [hij]
    simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_singularPair_plus_plus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
        (alpha := alpha) (sigma := sigma i) (tau := sigma j)
        (u i) (u j) (v i) (v j) (hleft i j hij) (hright i j hij)
  · by_cases hij : i = j
    · subst j
      simpa [lsScaledAugmentedMatrixBranchVector] using
        lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_rescaled_dot_eq_zero
          A (u i) (v i) (hAv i) (hATu i) halpha (hsigma i)
    · simpa [lsScaledAugmentedMatrixBranchVector] using
        lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
          (alpha := alpha) (sigma := sigma i) (tau := sigma j)
          (u i) (u j) (v i) (v j) (hleft i j hij) (hright i j hij)
  · simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_rescaled_dot_eq_zero
        A (u i) (w l) (v i) (hAv i) (hATu i) (hATw l) halpha (hsigma i)
  · calc
      (∑ r : Fin (m + n),
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w
              (Sum.inl (Sum.inr i)) r *
            lsScaledAugmentedMatrixBranchVector alpha sigma u v w
              (Sum.inl (Sum.inl j)) r)
          =
            ∑ r : Fin (m + n),
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                  (Sum.inl (Sum.inl j)) r *
                lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                  (Sum.inl (Sum.inr i)) r := by
              exact hdot_comm _ _
      _ = 0 := by
          by_cases hij : i = j
          · subst j
            simpa [lsScaledAugmentedMatrixBranchVector] using
              lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_rescaled_dot_eq_zero
                A (u i) (v i) (hAv i) (hATu i) halpha (hsigma i)
          · have hji : j ≠ i := fun hji => hij hji.symm
            simpa [lsScaledAugmentedMatrixBranchVector] using
              lsScaledAugmentedMatrix_singularPair_plus_minus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
                (alpha := alpha) (sigma := sigma j) (tau := sigma i)
                (u j) (u i) (v j) (v i) (hleft j i hji) (hright j i hji)
  · have hij : i ≠ j := by
      intro hij
      apply hab
      simp [hij]
    simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_singularPair_minus_minus_normalized_rescaled_dot_eq_zero_of_component_orthogonal
        (alpha := alpha) (sigma := sigma i) (tau := sigma j)
        (u i) (u j) (v i) (v j) (hleft i j hij) (hright i j hij)
  · simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_rescaled_dot_eq_zero
        A (u i) (w l) (v i) (hAv i) (hATu i) (hATw l) halpha (hsigma i)
  · calc
      (∑ r : Fin (m + n),
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w (Sum.inr k) r *
            lsScaledAugmentedMatrixBranchVector alpha sigma u v w
              (Sum.inl (Sum.inl j)) r)
          =
            ∑ r : Fin (m + n),
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                  (Sum.inl (Sum.inl j)) r *
                lsScaledAugmentedMatrixBranchVector alpha sigma u v w (Sum.inr k) r := by
              exact hdot_comm _ _
      _ = 0 := by
          simpa [lsScaledAugmentedMatrixBranchVector] using
            lsScaledAugmentedMatrix_singularPair_plus_leftNull_normalized_rescaled_dot_eq_zero
              A (u j) (w k) (v j) (hAv j) (hATu j) (hATw k)
              halpha (hsigma j)
  · calc
      (∑ r : Fin (m + n),
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w (Sum.inr k) r *
            lsScaledAugmentedMatrixBranchVector alpha sigma u v w
              (Sum.inl (Sum.inr j)) r)
          =
            ∑ r : Fin (m + n),
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w
                  (Sum.inl (Sum.inr j)) r *
                lsScaledAugmentedMatrixBranchVector alpha sigma u v w (Sum.inr k) r := by
              exact hdot_comm _ _
      _ = 0 := by
          simpa [lsScaledAugmentedMatrixBranchVector] using
            lsScaledAugmentedMatrix_singularPair_minus_leftNull_normalized_rescaled_dot_eq_zero
              A (u j) (w k) (v j) (hAv j) (hATu j) (hATw k)
              halpha (hsigma j)
  · have hkl : k ≠ l := by
      intro hkl
      apply hab
      simp [hkl]
    simpa [lsScaledAugmentedMatrixBranchVector] using
      lsScaledAugmentedMatrix_leftNull_leftNull_rescaled_dot_eq_zero_of_left_orthogonal
        (m := m) (n := n) (w k) (w l) (hnull k l hkl)
/-- A complete finite enumeration of the branch-indexed (20.18) family gives
    an orthogonal matrix whose columns are the displayed branch vectors.  The
    equivalence `e` is the still-supplied multiplicity/completeness witness. -/
theorem lsScaledAugmentedMatrixBranchVector_isOrthogonal_of_complete_equiv
    {m n : ℕ} {ι κ : Type*} {alpha : ℝ} {sigma : ι → ℝ}
    {A : Fin m → Fin n → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (e : Fin (m + n) ≃ Sum (Sum ι ι) κ)
    (hu : ∀ i : ι, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : ι, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : κ, vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : ι, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : ι, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : κ, k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (halpha : 0 ≤ alpha) (hsigma : ∀ i : ι, sigma i ≠ 0) :
    IsOrthogonal (m + n)
      (fun r c : Fin (m + n) =>
        lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r) := by
  classical
  apply IsOrthogonal.of_col_orthonormal
  intro c d
  by_cases hcd : c = d
  · subst d
    have hnorm :
        vecNorm2
            (lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c)) =
          1 :=
      lsScaledAugmentedMatrixBranchVector_vecNorm2_eq_one_of_unit_components
        (alpha := alpha) (sigma := sigma) (u := u) (v := v) (w := w)
        hu hv hw (e c)
    have hsq :
        vecNorm2Sq
            (lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c)) =
          1 := by
      have hpow :
          vecNorm2
              (lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c)) ^ 2 =
            (1 : ℝ) ^ 2 := by
        rw [hnorm]
      simpa [vecNorm2_sq] using hpow
    simpa [vecNorm2Sq, pow_two] using hsq
  · have hecd : e c ≠ e d := by
      intro heq
      exact hcd (e.injective heq)
    calc
      (∑ k : Fin (m + n),
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) k *
            lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e d) k)
          = 0 :=
            lsScaledAugmentedMatrixBranchVector_pairwise_dot_eq_zero_of_component_orthogonal
              (alpha := alpha) (sigma := sigma) (A := A) (u := u) (v := v) (w := w)
              hleft hright hnull hAv hATu hATw halpha hsigma (e c) (e d) hecd
      _ = if c = d then 1 else 0 := by simp [hcd]
/-- Complete branch enumeration handoff for Higham, 2nd ed., Chapter 20,
    equations (20.18)-(20.19): once the supplied branch index really enumerates
    all `m+n` displayed eigenvectors, the scaled augmented matrix has the
    corresponding orthogonal diagonalization.  This removes the old black-box
    `Q D Q^T` hypothesis, leaving only the source multiplicity/completeness
    witness and extremal branch data for the final condition-number theorem. -/
theorem
    lsScaledAugmentedMatrix_branch_orthogonal_diagonalization_of_complete_equiv
    {m n : ℕ} {ι κ : Type*} {alpha : ℝ} {sigma : ι → ℝ}
    {A : Fin m → Fin n → ℝ}
    {u : ι → Fin m → ℝ} {v : ι → Fin n → ℝ}
    {w : κ → Fin m → ℝ}
    (e : Fin (m + n) ≃ Sum (Sum ι ι) κ)
    (hu : ∀ i : ι, vecNorm2Sq (u i) = 1)
    (hv : ∀ i : ι, vecNorm2Sq (v i) = 1)
    (hw : ∀ k : κ, vecNorm2Sq (w k) = 1)
    (hleft : ∀ i j : ι, i ≠ j → (∑ r : Fin m, u i r * u j r) = 0)
    (hright : ∀ i j : ι, i ≠ j → (∑ c : Fin n, v i c * v j c) = 0)
    (hnull : ∀ k l : κ, k ≠ l → (∑ r : Fin m, w k r * w l r) = 0)
    (hAv : ∀ i : ι, rectMatMulVec A (v i) = fun r => sigma i * u i r)
    (hATu : ∀ i : ι,
      (fun j : Fin n => ∑ r : Fin m, A r j * u i r) =
        fun j => sigma i * v i j)
    (hATw : ∀ k : κ, ∀ j : Fin n, ∑ r : Fin m, A r j * w k r = 0)
    (halpha : 0 ≤ alpha) (hsigma : ∀ i : ι, sigma i ≠ 0) :
    lsScaledAugmentedMatrix alpha A =
      finiteMatMul
        (fun r c : Fin (m + n) =>
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r)
        (finiteMatMul
          (finiteDiagonal
            (fun c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchEigenvalue alpha sigma (e c)))
          (matTranspose
            (fun r c : Fin (m + n) =>
              lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r))) := by
  classical
  let Q : Fin (m + n) → Fin (m + n) → ℝ :=
    fun r c => lsScaledAugmentedMatrixBranchVector alpha sigma u v w (e c) r
  let d : Fin (m + n) → ℝ :=
    fun c => lsScaledAugmentedMatrixBranchEigenvalue alpha sigma (e c)
  have hQ : IsOrthogonal (m + n) Q :=
    lsScaledAugmentedMatrixBranchVector_isOrthogonal_of_complete_equiv
      (alpha := alpha) (sigma := sigma) (A := A) (u := u) (v := v) (w := w)
      e hu hv hw hleft hright hnull hAv hATu hATw halpha hsigma
  have heig : ∀ c : Fin (m + n),
      finiteMatVec (lsScaledAugmentedMatrix alpha A) (fun r => Q r c) =
        fun r => d c * Q r c := by
    intro c
    simpa [Q, d, finiteMatVec, rectMatMulVec] using
      lsScaledAugmentedMatrixBranchVector_eigenvector
        (alpha := alpha) (sigma := sigma) (A := A) (u := u) (v := v) (w := w)
        hAv hATu hATw halpha hsigma (e c)
  simpa [Q, d] using
    finiteMatrix_eq_orthogonal_diagonalization_of_eigenvector_columns hQ heig
/-- Finite branch-count constructor for Higham, 2nd ed., Chapter 20,
    equations (20.18)-(20.19).  If the displayed branch count
    `2 * card ι + card κ` equals the augmented dimension `m+n`, the branch
    index type can be used as a complete finite column enumeration. -/
noncomputable def lsScaledAugmentedBranchEquivOfCardEq
    (m n : ℕ) (ι κ : Type*) [Fintype ι] [Fintype κ]
    (hcard : 2 * Fintype.card ι + Fintype.card κ = m + n) :
    Fin (m + n) ≃ Sum (Sum ι ι) κ :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_sum, Fintype.card_sum]
    omega)
/-- Index attaining the finite minimum singular branch value in the
    branch-indexed (20.18) family. -/
noncomputable def lsScaledAugmentedBranchSigmaMinIndex
    {ι : Type*} [Fintype ι] [Nonempty ι] (sigma : ι → ℝ) : ι :=
  Classical.choose
    (Finset.exists_min_image (Finset.univ : Finset ι) sigma
      Finset.univ_nonempty)
/-- Index attaining the finite maximum singular branch value in the
    branch-indexed (20.18) family. -/
noncomputable def lsScaledAugmentedBranchSigmaMaxIndex
    {ι : Type*} [Fintype ι] [Nonempty ι] (sigma : ι → ℝ) : ι :=
  Classical.choose
    (Finset.exists_max_image (Finset.univ : Finset ι) sigma
      Finset.univ_nonempty)
/-- Finite minimum singular branch value used by the source-shaped
    cardinality theorem for (20.18)-(20.19). -/
noncomputable def lsScaledAugmentedBranchSigmaMin
    {ι : Type*} [Fintype ι] [Nonempty ι] (sigma : ι → ℝ) : ℝ :=
  sigma (lsScaledAugmentedBranchSigmaMinIndex sigma)
/-- Finite maximum singular branch value used by the source-shaped
    cardinality theorem for (20.18)-(20.19). -/
noncomputable def lsScaledAugmentedBranchSigmaMax
    {ι : Type*} [Fintype ι] [Nonempty ι] (sigma : ι → ℝ) : ℝ :=
  sigma (lsScaledAugmentedBranchSigmaMaxIndex sigma)
/-- The finite branch minimum is bounded above by every branch value. -/
theorem lsScaledAugmentedBranchSigmaMin_le
    {ι : Type*} [Fintype ι] [Nonempty ι] (sigma : ι → ℝ) (i : ι) :
    lsScaledAugmentedBranchSigmaMin sigma ≤ sigma i := by
  have hspec :=
    Classical.choose_spec
      (Finset.exists_min_image (Finset.univ : Finset ι) sigma
        Finset.univ_nonempty)
  exact hspec.2 i (by simp)
/-- Every branch value is bounded above by the finite branch maximum. -/
theorem lsScaledAugmentedBranchSigma_le_max
    {ι : Type*} [Fintype ι] [Nonempty ι] (sigma : ι → ℝ) (i : ι) :
    sigma i ≤ lsScaledAugmentedBranchSigmaMax sigma := by
  have hspec :=
    Classical.choose_spec
      (Finset.exists_max_image (Finset.univ : Finset ι) sigma
        Finset.univ_nonempty)
  exact hspec.2 i (by simp)
/-- Finite branch minima are invariant under reindexing by an equivalence. -/
theorem lsScaledAugmentedBranchSigmaMin_eq_of_equiv
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (sigma : ι → ℝ) (tau : κ → ℝ) (e : ι ≃ κ)
    (h : ∀ i : ι, sigma i = tau (e i)) :
    lsScaledAugmentedBranchSigmaMin sigma =
      lsScaledAugmentedBranchSigmaMin tau := by
  apply le_antisymm
  · have hle :=
      lsScaledAugmentedBranchSigmaMin_le sigma
        (e.symm (lsScaledAugmentedBranchSigmaMinIndex tau))
    simpa [lsScaledAugmentedBranchSigmaMin,
      h (e.symm (lsScaledAugmentedBranchSigmaMinIndex tau))] using hle
  · have hle :=
      lsScaledAugmentedBranchSigmaMin_le tau
        (e (lsScaledAugmentedBranchSigmaMinIndex sigma))
    simpa [lsScaledAugmentedBranchSigmaMin,
      h (lsScaledAugmentedBranchSigmaMinIndex sigma)] using hle
/-- Finite branch maxima are invariant under reindexing by an equivalence. -/
theorem lsScaledAugmentedBranchSigmaMax_eq_of_equiv
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (sigma : ι → ℝ) (tau : κ → ℝ) (e : ι ≃ κ)
    (h : ∀ i : ι, sigma i = tau (e i)) :
    lsScaledAugmentedBranchSigmaMax sigma =
      lsScaledAugmentedBranchSigmaMax tau := by
  apply le_antisymm
  · have hle :=
      lsScaledAugmentedBranchSigma_le_max tau
        (e (lsScaledAugmentedBranchSigmaMaxIndex sigma))
    simpa [lsScaledAugmentedBranchSigmaMax,
      h (lsScaledAugmentedBranchSigmaMaxIndex sigma)] using hle
  · have hle :=
      lsScaledAugmentedBranchSigma_le_max sigma
        (e.symm (lsScaledAugmentedBranchSigmaMaxIndex tau))
    simpa [lsScaledAugmentedBranchSigmaMax,
      h (e.symm (lsScaledAugmentedBranchSigmaMaxIndex tau))] using hle
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    source-shaped rectangular branch count.  For the usual full-column-rank
    least-squares dimensions `A : R^{m x n}` with `n <= m`, the `n` positive
    singular branches, their paired negative branches, and the `m-n`
    left-nullspace branches have total size `m+n`. -/
theorem lsScaledAugmentedSourceBranchCardEq {m n : ℕ} (hmn : n ≤ m) :
    2 * Fintype.card (Fin n) + Fintype.card (Fin (m - n)) = m + n := by
  simp [Fintype.card_fin]
  omega
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    source-shaped complete branch enumeration for a tall rectangular matrix. -/
noncomputable def lsScaledAugmentedSourceBranchEquiv
    (m n : ℕ) (hmn : n ≤ m) :
    Fin (m + n) ≃ Sum (Sum (Fin n) (Fin n)) (Fin (m - n)) :=
  lsScaledAugmentedBranchEquivOfCardEq m n (Fin n) (Fin (m - n))
    (lsScaledAugmentedSourceBranchCardEq hmn)
/-- Higham, 2nd ed., Chapter 20, equations (20.18)-(20.19):
    reciprocal-diagonal inverse candidate built from the source-shaped branch
    family `Fin n ⊕ Fin n ⊕ Fin (m-n)`. -/
noncomputable def lsScaledAugmentedSourceBranchInverseCandidate
    {m n : ℕ} (hmn : n ≤ m) (alpha : ℝ)
    (sigma : Fin n → ℝ) (u : Fin n → Fin m → ℝ)
    (v : Fin n → Fin n → ℝ) (w : Fin (m - n) → Fin m → ℝ) :
    Fin (m + n) → Fin (m + n) → ℝ :=
  finiteMatMul
    (fun r c : Fin (m + n) =>
      lsScaledAugmentedMatrixBranchVector alpha sigma u v w
        (lsScaledAugmentedSourceBranchEquiv m n hmn c) r)
    (finiteMatMul
      (finiteDiagonal
        (fun c : Fin (m + n) =>
          (lsScaledAugmentedMatrixBranchEigenvalue alpha sigma
            (lsScaledAugmentedSourceBranchEquiv m n hmn c))⁻¹))
      (matTranspose
        (fun r c : Fin (m + n) =>
          lsScaledAugmentedMatrixBranchVector alpha sigma u v w
            (lsScaledAugmentedSourceBranchEquiv m n hmn c) r)))
/-- Higham, 2nd ed., Chapter 20, Lemma 20.6: augmented system with
    different perturbations in the primal and transposed blocks. -/
def LSAsymmetricPerturbedAugmentedSystem {m n : ℕ}
    (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ) (b s : Fin m → ℝ)
    (y : Fin n → ℝ) : Prop :=
  (∀ i : Fin m, s i + rectMatMulVec (fun i j => A i j + DeltaA1 i j) y i = b i) ∧
  (∀ j : Fin n, ∑ i : Fin m, (A i j + DeltaA2 i j) * s i = 0)
/-- Zero-residual branch in the proof of Lemma 20.6: if the asymmetric
    augmented-system residual is zero, taking `DeltaA = DeltaA1` gives a
    symmetric perturbed augmented system. -/
theorem LSAsymmetricPerturbedAugmentedSystem.to_augmentedSystem_of_s_eq_zero
    {m n : ℕ} (A DeltaA1 DeltaA2 : Fin m → Fin n → ℝ)
    (b s : Fin m → ℝ) (y : Fin n → ℝ)
    (h : LSAsymmetricPerturbedAugmentedSystem A DeltaA1 DeltaA2 b s y)
    (hs : s = 0) :
    LSAugmentedSystem (fun i j => A i j + DeltaA1 i j) b (0 : Fin n → ℝ)
      (0 : Fin m → ℝ) y := by
  subst s
  constructor
  · intro i
    simpa using h.1 i
  · intro j
    simp
private theorem matMulVec_orthogonal_mul_transpose_lsq {m : ℕ}
    {Q : Fin m → Fin m → ℝ} (hQ : IsOrthogonal m Q)
    (f : Fin m → ℝ) :
    matMulVec m Q (matMulVec m (matTranspose Q) f) = f := by
  ext i
  calc
    matMulVec m Q (matMulVec m (matTranspose Q) f) i
        = matMulVec m (matMul m Q (matTranspose Q)) f i := by
            exact (matMulVec_matMul m Q (matTranspose Q) f i).symm
    _ = matMulVec m (idMatrix m) f i := by
            have hmat : matMul m Q (matTranspose Q) = idMatrix m := by
              ext a b
              exact hQ.right_inv a b
            rw [hmat]
    _ = f i := by
            exact congrFun (matMulVec_id m f) i
private theorem matMulRectLeft_transpose_action_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B : Fin m → Fin n → ℝ)
    (y : Fin m → ℝ) (hQ : IsOrthogonal m Q) :
    (fun j : Fin n =>
      ∑ i : Fin m, matMulRectLeft Q B i j * matMulVec m Q y i) =
      fun j : Fin n => ∑ i : Fin m, B i j * y i := by
  ext j
  unfold matMulRectLeft matMulVec
  calc
    ∑ i : Fin m, (∑ k : Fin m, Q i k * B k j) *
        (∑ l : Fin m, Q i l * y l)
        = ∑ i : Fin m, ∑ k : Fin m, ∑ l : Fin m,
            (Q i k * B k j) * (Q i l * y l) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ k : Fin m, ∑ l : Fin m, ∑ i : Fin m,
          (Q i k * B k j) * (Q i l * y l) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_comm]
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (∑ i : Fin m, Q i k * Q i l) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = ∑ k : Fin m, ∑ l : Fin m,
          (if k = l then 1 else 0) * (B k j * y l) := by
            apply Finset.sum_congr rfl
            intro k _
            apply Finset.sum_congr rfl
            intro l _
            rw [hQ.col_orthonormal k l]
    _ = ∑ k : Fin m, B k j * y k := by
            simp [Finset.mem_univ]
/-- Higham, 2nd ed., Chapter 20, Section 20.5: an exact solution of the
    transformed augmented system obtained by applying an orthogonal `Q^T`
    lifts back to an exact solution of the original augmented system.

    This is exact algebra only.  It assumes the transformed system has already
    been solved and does not model the computed QR or triangular solves. -/
theorem LSAugmentedSystem.of_transformed_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B A : Fin m → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (hA : A = matMulRectLeft Q B)
    (htrans :
      LSAugmentedSystem B (matMulVec m (matTranspose Q) f) g y x) :
    LSAugmentedSystem A f g (matMulVec m Q y) x := by
  constructor
  · intro i
    have hsum :
        (fun t : Fin m => y t + rectMatMulVec B x t) =
          matMulVec m (matTranspose Q) f := by
      ext t
      exact htrans.1 t
    have hAx :
        rectMatMulVec A x i =
          matMulVec m Q (rectMatMulVec B x) i := by
      rw [hA]
      exact congrFun (rectMatMulVec_matMulRectLeft Q B x) i
    calc
      matMulVec m Q y i + rectMatMulVec A x i
          = matMulVec m Q y i + matMulVec m Q (rectMatMulVec B x) i := by
              rw [hAx]
      _ = matMulVec m Q (fun t : Fin m => y t + rectMatMulVec B x t) i := by
              exact (congrFun (matMulVec_add_right m Q y (rectMatMulVec B x)) i).symm
      _ = matMulVec m Q (matMulVec m (matTranspose Q) f) i := by
              rw [hsum]
      _ = f i := by
              exact congrFun (matMulVec_orthogonal_mul_transpose_lsq hQ f) i
  · intro j
    have hcols :
        (fun j : Fin n =>
          ∑ i : Fin m, matMulRectLeft Q B i j * matMulVec m Q y i) =
          fun j : Fin n => ∑ i : Fin m, B i j * y i :=
      matMulRectLeft_transpose_action_orthogonal Q B y hQ
    calc
      ∑ i : Fin m, A i j * matMulVec m Q y i
          = ∑ i : Fin m, matMulRectLeft Q B i j * matMulVec m Q y i := by
              rw [hA]
      _ = ∑ i : Fin m, B i j * y i := by
              exact congrFun hcols j
      _ = g j := htrans.2 j
/-- Orthogonal lift for the asymmetric augmented system in Theorem 20.4.
    If a transformed system with two matrix occurrences `B1` and `B2` is
    solved exactly, then applying the same orthogonal `Q` to both occurrences
    lifts the solution to the original coordinates. -/
theorem LSAsymmetricAugmentedSystem.of_transformed_orthogonal {m n : ℕ}
    (Q : Fin m → Fin m → ℝ) (B1 B2 A1 A2 : Fin m → Fin n → ℝ)
    (f : Fin m → ℝ) (g : Fin n → ℝ) (y : Fin m → ℝ) (x : Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (hA1 : A1 = matMulRectLeft Q B1)
    (hA2 : A2 = matMulRectLeft Q B2)
    (htrans :
      LSAsymmetricAugmentedSystem B1 B2
        (matMulVec m (matTranspose Q) f) g y x) :
    LSAsymmetricAugmentedSystem A1 A2 f g (matMulVec m Q y) x := by
  constructor
  · intro i
    have hsum :
        (fun t : Fin m => y t + rectMatMulVec B1 x t) =
          matMulVec m (matTranspose Q) f := by
      ext t
      exact htrans.1 t
    have hAx :
        rectMatMulVec A1 x i =
          matMulVec m Q (rectMatMulVec B1 x) i := by
      rw [hA1]
      exact congrFun (rectMatMulVec_matMulRectLeft Q B1 x) i
    calc
      matMulVec m Q y i + rectMatMulVec A1 x i
          = matMulVec m Q y i + matMulVec m Q (rectMatMulVec B1 x) i := by
              rw [hAx]
      _ = matMulVec m Q (fun t : Fin m => y t + rectMatMulVec B1 x t) i := by
              exact (congrFun (matMulVec_add_right m Q y (rectMatMulVec B1 x)) i).symm
      _ = matMulVec m Q (matMulVec m (matTranspose Q) f) i := by
              rw [hsum]
      _ = f i := by
              exact congrFun (matMulVec_orthogonal_mul_transpose_lsq hQ f) i
  · intro j
    have hcols :
        (fun j : Fin n =>
          ∑ i : Fin m, matMulRectLeft Q B2 i j * matMulVec m Q y i) =
          fun j : Fin n => ∑ i : Fin m, B2 i j * y i :=
      matMulRectLeft_transpose_action_orthogonal Q B2 y hQ
    calc
      ∑ i : Fin m, A2 i j * matMulVec m Q y i
          = ∑ i : Fin m, matMulRectLeft Q B2 i j * matMulVec m Q y i := by
              rw [hA2]
      _ = ∑ i : Fin m, B2 i j * y i := by
              exact congrFun hcols j
      _ = g j := htrans.2 j
/-- Higham, 2nd ed., Chapter 20, Section 20.5: supplied-factor exact QR
    solution of the arbitrary augmented system (20.15).  If
    `A = Q [R; 0]`, `Q` is orthogonal, `Q^T f = [d₁; d₂]`,
    `R^T h = g`, and `R x = d₁ - h`, then
    `r = Q [h; d₂]` and `x` solve `r + A x = f`, `A^T r = g`.

    This theorem closes the exact supplied-factor QR algebra only; Theorem 20.4's
    computed Householder QR path and componentwise perturbation bounds remain
    separate open work. -/
theorem LSAugmentedSystem.exact_qr_solution_of_factors {n k : ℕ}
    (Q : Fin (n + k) → Fin (n + k) → ℝ)
    (A : Fin (n + k) → Fin n → ℝ) (R : Fin n → Fin n → ℝ)
    (f : Fin (n + k) → ℝ)
    (d1 h x : Fin n → ℝ) (d2 : Fin k → ℝ) (g : Fin n → ℝ)
    (hQ : IsOrthogonal (n + k) Q)
    (hA : A = matMulRectLeft Q (lsQRTallBlock R))
    (hd : matMulVec (n + k) (matTranspose Q) f = Fin.append d1 d2)
    (hRt : ∀ j : Fin n, ∑ i : Fin n, R i j * h i = g j)
    (hRx : rectMatMulVec R x = fun i : Fin n => d1 i - h i) :
    LSAugmentedSystem A f g
      (matMulVec (n + k) Q (Fin.append h d2)) x := by
  have htrans_base :
      LSAugmentedSystem (lsQRTallBlock R) (Fin.append d1 d2) g
        (Fin.append h d2) x :=
    LSAugmentedSystem.transformed_qr_solution R d1 h x d2 g hRt hRx
  have htrans :
      LSAugmentedSystem (lsQRTallBlock R)
        (matMulVec (n + k) (matTranspose Q) f) g (Fin.append h d2) x := by
    simpa [hd] using htrans_base
  exact
    LSAugmentedSystem.of_transformed_orthogonal Q (lsQRTallBlock R) A f g
      (Fin.append h d2) x hQ hA htrans

end NumStability
