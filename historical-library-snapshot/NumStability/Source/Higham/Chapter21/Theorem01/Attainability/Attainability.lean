import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Cholesky.Solve.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.RankGeometry
import NumStability.Algorithms.LinearSystems.QR.GramSchmidt
import NumStability.Algorithms.LinearSystems.Underdetermined.MinimumNorm.Pseudoinverse.UnderdeterminedSpec
import NumStability.Analysis.Conditioning.LinearSystems.InversePerturbation
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.PerturbationTheory
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core
import NumStability.Source.Higham.Chapter20.Theorem03.QRSolve
import NumStability.Source.Higham.Chapter21.Equation06.Perturbation
import NumStability.Source.Higham.Chapter21.Equation07.UnderdeterminedSolve

/-!
# Source.Higham.Chapter21.Theorem01.Attainability.Attainability

W04 semantic leaf; declaration commands are preserved byte-for-byte from C0006.
-/

-- Algorithms/Underdetermined/Higham21Attainability.lean
--
-- Holder p-norm first-order attainability in Higham's Theorem 21.1.



namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- The complete printed first-order majorant in Theorem 21.1, equation
    (21.6). -/
noncomputable def higham21Theorem21_1Majorant {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real) :
    Fin n -> Real :=
  fun j =>
    higham21Theorem21_1NullspaceMajorant A E b j +
      higham21Theorem21_1DataMajorant A E b f j

theorem higham21Theorem21_1Majorant_nonneg {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (hE : forall i j, 0 <= E i j) (hf : forall i, 0 <= f i) :
    forall j, 0 <= higham21Theorem21_1Majorant A E b f j := by
  intro j
  exact add_nonneg
    (higham21Theorem21_1NullspaceMajorant_nonneg A E b hE j)
    (higham21Theorem21_1DataMajorant_nonneg A E b f hE hf j)

/-- The null-space source vector in the first-order expansion (21.7). -/
noncomputable def higham21Theorem21_1NullspaceSource {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real) (b : Fin m -> Real) :
    Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let w := rectTransposeMulVec DeltaA z
  fun j => w j - rectMatMulVec Aplus (rectMatMulVec A w) j

/-- The pseudoinverse-range source vector in the first-order expansion
    (21.7). -/
noncomputable def higham21Theorem21_1DataSource {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real) : Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let q := fun i => Deltab i - rectMatMulVec DeltaA x i
  rectMatMulVec Aplus q






























































/-- The two named source vectors are orthogonal. -/
theorem higham21_theorem21_1_sources_orthogonal {m n : Nat}
    (A DeltaA : Fin m -> Fin n -> Real)
    (b Deltab : Fin m -> Real)
    (hdet : Matrix.det (rectGram A : Matrix (Fin m) (Fin m) Real) ≠ 0) :
    (Finset.univ.sum fun j : Fin n =>
      higham21Theorem21_1NullspaceSource A DeltaA b j *
        higham21Theorem21_1DataSource A DeltaA b Deltab j) = 0 := by
  simpa [higham21Theorem21_1NullspaceSource,
    higham21Theorem21_1DataSource] using
      (higham21Eq21_7_source_vectors_orthogonal
        A DeltaA b Deltab hdet)






































































































/-- Sign perturbation attaining a chosen coordinate of the null-space
    majorant. -/
noncomputable def higham21Theorem21_1NullspaceAttainingDeltaA {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) : Fin m -> Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  let z := rectTransposeMulVec Aplus x
  let P := lsAugmentedProjectionBlock Aplus A
  fun i k =>
    eps * summationAbsSign (P j0 k) * E i k * summationAbsSign (z i)

theorem higham21Theorem21_1NullspaceAttainingDeltaA_abs {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) (heps : 0 <= eps)
    (hE : forall i k, 0 <= E i k) :
    forall i k,
      abs (higham21Theorem21_1NullspaceAttainingDeltaA
        A E b eps j0 i k) = eps * E i k := by
  intro i k
  simp [higham21Theorem21_1NullspaceAttainingDeltaA, abs_mul,
    abs_summationAbsSign, abs_of_nonneg heps, abs_of_nonneg (hE i k)]

theorem higham21Theorem21_1NullspaceAttainingDeltaA_source_coord
    {m n : Nat} (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) :
    higham21Theorem21_1NullspaceSource A
        (higham21Theorem21_1NullspaceAttainingDeltaA A E b eps j0) b j0 =
      eps * higham21Theorem21_1NullspaceMajorant A E b j0 := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let z : Fin m -> Real := rectTransposeMulVec Aplus x
  let P : Fin n -> Fin n -> Real := lsAugmentedProjectionBlock Aplus A
  let DeltaA : Fin m -> Fin n -> Real :=
    higham21Theorem21_1NullspaceAttainingDeltaA A E b eps j0
  let w : Fin n -> Real := rectTransposeMulVec DeltaA z
  let W : Fin n -> Real := lsComponentwiseTransposeMajorant E z
  have hw : forall k,
      w k = eps * summationAbsSign (P j0 k) * W k := by
    intro k
    change
      (Finset.univ.sum fun i : Fin m =>
        (eps * summationAbsSign (P j0 k) * E i k *
          summationAbsSign (z i)) * z i) =
        eps * summationAbsSign (P j0 k) *
          (Finset.univ.sum fun i : Fin m => E i k * abs (z i))
    calc
      (Finset.univ.sum fun i : Fin m =>
          (eps * summationAbsSign (P j0 k) * E i k *
            summationAbsSign (z i)) * z i) =
          Finset.univ.sum (fun i : Fin m =>
            (eps * summationAbsSign (P j0 k)) *
              (E i k * abs (z i))) := by
            apply Finset.sum_congr rfl
            intro i _
            calc
              (eps * summationAbsSign (P j0 k) * E i k *
                  summationAbsSign (z i)) * z i =
                  (eps * summationAbsSign (P j0 k) * E i k) *
                    (summationAbsSign (z i) * z i) := by ring
              _ = (eps * summationAbsSign (P j0 k)) *
                    (E i k * abs (z i)) := by
                  rw [summationAbsSign_mul_eq_abs]
                  ring
      _ = eps * summationAbsSign (P j0 k) *
          (Finset.univ.sum fun i : Fin m => E i k * abs (z i)) := by
            rw [Finset.mul_sum]
  have hprojection :
      higham21Theorem21_1NullspaceSource A DeltaA b j0 =
        rectMatMulVec P w j0 := by
    have hact := congrFun (lsAugmentedProjectionBlock_mulVec Aplus A w) j0
    exact hact.symm
  calc
    higham21Theorem21_1NullspaceSource A
        (higham21Theorem21_1NullspaceAttainingDeltaA A E b eps j0) b j0 =
        Finset.univ.sum (fun k : Fin n => P j0 k * w k) := by
          change higham21Theorem21_1NullspaceSource A DeltaA b j0 = _
          rw [hprojection]
          rfl
    _ = Finset.univ.sum (fun k : Fin n =>
        P j0 k * (eps * summationAbsSign (P j0 k) * W k)) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hw k]
    _ = eps * Finset.univ.sum (fun k : Fin n => abs (P j0 k) * W k) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          calc
            P j0 k * (eps * summationAbsSign (P j0 k) * W k) =
                eps * (P j0 k * summationAbsSign (P j0 k)) * W k := by
              ring
            _ = eps * (abs (P j0 k) * W k) := by
              rw [mul_summationAbsSign_eq_abs]
              ring
    _ = eps * higham21Theorem21_1NullspaceMajorant A E b j0 := by
          rfl

/-- Sign matrix attaining the `E|x|` part of a chosen coordinate of the data
    majorant. -/
noncomputable def higham21Theorem21_1DataAttainingDeltaA {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) : Fin m -> Fin n -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  let x := rectMatMulVec Aplus b
  fun i k =>
    -(eps * summationAbsSign (Aplus j0 i) * E i k *
      summationAbsSign (x k))

/-- Sign right-hand-side perturbation attaining the `f` part of a chosen
    coordinate of the data majorant. -/
noncomputable def higham21Theorem21_1DataAttainingDeltab {m n : Nat}
    (A : Fin m -> Fin n -> Real) (f : Fin m -> Real)
    (eps : Real) (j0 : Fin n) : Fin m -> Real :=
  let Aplus := undetAplusOfGramNonsingInv A
  fun i => eps * summationAbsSign (Aplus j0 i) * f i

theorem higham21Theorem21_1DataAttainingDeltaA_abs {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b : Fin m -> Real)
    (eps : Real) (j0 : Fin n) (heps : 0 <= eps)
    (hE : forall i k, 0 <= E i k) :
    forall i k,
      abs (higham21Theorem21_1DataAttainingDeltaA
        A E b eps j0 i k) = eps * E i k := by
  intro i k
  simp [higham21Theorem21_1DataAttainingDeltaA, abs_mul,
    abs_summationAbsSign, abs_of_nonneg heps, abs_of_nonneg (hE i k)]

theorem higham21Theorem21_1DataAttainingDeltab_abs {m n : Nat}
    (A : Fin m -> Fin n -> Real) (f : Fin m -> Real)
    (eps : Real) (j0 : Fin n) (heps : 0 <= eps)
    (hf : forall i, 0 <= f i) :
    forall i,
      abs (higham21Theorem21_1DataAttainingDeltab A f eps j0 i) =
        eps * f i := by
  intro i
  simp [higham21Theorem21_1DataAttainingDeltab, abs_mul,
    abs_summationAbsSign, abs_of_nonneg heps, abs_of_nonneg (hf i)]

theorem higham21Theorem21_1DataAttainers_source_coord {m n : Nat}
    (A E : Fin m -> Fin n -> Real) (b f : Fin m -> Real)
    (eps : Real) (j0 : Fin n) :
    higham21Theorem21_1DataSource A
        (higham21Theorem21_1DataAttainingDeltaA A E b eps j0) b
        (higham21Theorem21_1DataAttainingDeltab A f eps j0) j0 =
      eps * higham21Theorem21_1DataMajorant A E b f j0 := by
  let Aplus : Fin n -> Fin m -> Real := undetAplusOfGramNonsingInv A
  let x : Fin n -> Real := rectMatMulVec Aplus b
  let DeltaA : Fin m -> Fin n -> Real :=
    higham21Theorem21_1DataAttainingDeltaA A E b eps j0
  let Deltab : Fin m -> Real :=
    higham21Theorem21_1DataAttainingDeltab A f eps j0
  let q : Fin m -> Real := fun i => Deltab i - rectMatMulVec DeltaA x i
  let budget : Fin m -> Real := lsComponentwiseDataMajorant E f x
  have haction : forall i,
      rectMatMulVec DeltaA x i =
        -(eps * summationAbsSign (Aplus j0 i)) *
          rectMatMulVec E (fun k => abs (x k)) i := by
    intro i
    change
      (Finset.univ.sum fun k : Fin n =>
        (-(eps * summationAbsSign (Aplus j0 i) * E i k *
          summationAbsSign (x k))) * x k) =
        -(eps * summationAbsSign (Aplus j0 i)) *
          (Finset.univ.sum fun k : Fin n => E i k * abs (x k))
    calc
      (Finset.univ.sum fun k : Fin n =>
          (-(eps * summationAbsSign (Aplus j0 i) * E i k *
            summationAbsSign (x k))) * x k) =
          Finset.univ.sum (fun k : Fin n =>
            (-(eps * summationAbsSign (Aplus j0 i))) *
              (E i k * abs (x k))) := by
            apply Finset.sum_congr rfl
            intro k _
            calc
              (-(eps * summationAbsSign (Aplus j0 i) * E i k *
                  summationAbsSign (x k))) * x k =
                  -(eps * summationAbsSign (Aplus j0 i) * E i k) *
                    (summationAbsSign (x k) * x k) := by ring
              _ = (-(eps * summationAbsSign (Aplus j0 i))) *
                    (E i k * abs (x k)) := by
                  rw [summationAbsSign_mul_eq_abs]
                  ring
      _ = -(eps * summationAbsSign (Aplus j0 i)) *
          (Finset.univ.sum fun k : Fin n => E i k * abs (x k)) := by
            rw [Finset.mul_sum]
  have hq : forall i,
      q i = eps * summationAbsSign (Aplus j0 i) * budget i := by
    intro i
    change
      eps * summationAbsSign (Aplus j0 i) * f i -
          rectMatMulVec DeltaA x i =
        eps * summationAbsSign (Aplus j0 i) *
          (f i + rectMatMulVec E (fun k => abs (x k)) i)
    rw [haction i]
    ring
  calc
    higham21Theorem21_1DataSource A
        (higham21Theorem21_1DataAttainingDeltaA A E b eps j0) b
        (higham21Theorem21_1DataAttainingDeltab A f eps j0) j0 =
        Finset.univ.sum (fun i : Fin m => Aplus j0 i * q i) := by
          rfl
    _ = Finset.univ.sum (fun i : Fin m =>
        Aplus j0 i *
          (eps * summationAbsSign (Aplus j0 i) * budget i)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hq i]
    _ = eps * Finset.univ.sum (fun i : Fin m =>
        abs (Aplus j0 i) * budget i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          calc
            Aplus j0 i *
                (eps * summationAbsSign (Aplus j0 i) * budget i) =
                eps * (Aplus j0 i * summationAbsSign (Aplus j0 i)) *
                  budget i := by ring
            _ = eps * (abs (Aplus j0 i) * budget i) := by
              rw [mul_summationAbsSign_eq_abs]
              ring
    _ = eps * higham21Theorem21_1DataMajorant A E b f j0 := by
          rfl

/-- Index at which the larger of the two source majorants is globally
    maximal. -/
noncomputable def higham21Theorem21_1MajorantArgmax {m n : Nat}
    (hn : 0 < n) (A E : Fin m -> Fin n -> Real)
    (b f : Fin m -> Real) : Fin n :=
  (Finset.exists_max_image Finset.univ
    (fun j : Fin n => max
      (higham21Theorem21_1NullspaceMajorant A E b j)
      (higham21Theorem21_1DataMajorant A E b f j))
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose

theorem higham21Theorem21_1MajorantArgmax_spec {m n : Nat}
    (hn : 0 < n) (A E : Fin m -> Fin n -> Real)
    (b f : Fin m -> Real) :
    forall j : Fin n,
      max (higham21Theorem21_1NullspaceMajorant A E b j)
          (higham21Theorem21_1DataMajorant A E b f j) <=
        max
          (higham21Theorem21_1NullspaceMajorant A E b
            (higham21Theorem21_1MajorantArgmax hn A E b f))
          (higham21Theorem21_1DataMajorant A E b f
            (higham21Theorem21_1MajorantArgmax hn A E b f)) := by
  intro j
  exact
    ((Finset.exists_max_image Finset.univ
      (fun k : Fin n => max
        (higham21Theorem21_1NullspaceMajorant A E b k)
        (higham21Theorem21_1DataMajorant A E b f k))
      ⟨⟨0, hn⟩, Finset.mem_univ _⟩).choose_spec.2
        j (Finset.mem_univ j))

/-- The explicit finite-dimensional loss used in the constructive half of
    Theorem 21.1. -/
noncomputable def higham21Theorem21_1HolderAttainmentFactor
    (n : Nat) (p : Real) : Real :=
  2 * (n : Real) ^ p⁻¹ *
    (n : Real) ^ abs (p⁻¹ - (2 : Real)⁻¹)




































































































































































































































































































end NumStability
