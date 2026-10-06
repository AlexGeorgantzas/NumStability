/-
# The rational-function certificate used by Spijker's lemma

This file supplies the algebraic bridge that is implicit in the usual Kreiss
proof: every scalar resolvent coefficient is a quotient of two polynomials of
degree at most the matrix dimension.  The denominator is the characteristic
polynomial and the numerator is obtained from the adjugate of the characteristic
matrix.  Keeping the certificate separate prevents the geometric arc-length
theorem from silently assuming that the matrix specialization is rational.
-/

import NumStability.Analysis.MatrixPowersKreissSpijker
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace NumStability

open scoped ComplexOrder

open Complex Matrix Polynomial

noncomputable section

/-- A deliberately small certificate for a scalar function to be rational of
order at most `n`. -/
structure RationalOrderCertificate (n : ℕ) (f : ℂ → ℂ) where
  numerator : ℂ[X]
  denominator : ℂ[X]
  numerator_degree : numerator.natDegree ≤ n
  denominator_degree : denominator.natDegree ≤ n
  value_eq : ∀ z, denominator.eval z ≠ 0 →
    f z = numerator.eval z / denominator.eval z

/-- The plain matrix underlying a `CStarMatrix`. -/
def cstarMatrixEntries {m n : Type*}
    (A : CStarMatrix m n ℂ) : Matrix m n ℂ := fun i j => A i j

/-- Ring equivalences preserve the totalized ring inverse. -/
lemma ringEquiv_map_ringInverse
    {R S : Type*} [Ring R] [Ring S] (e : R ≃+* S) (x : R) :
    e (Ring.inverse x) = Ring.inverse (e x) := by
  by_cases hx : IsUnit x
  · let u : Rˣ := hx.unit
    have hu : (u : R) = x := hx.unit_spec
    let eu : Sˣ := Units.map e.toMonoidHom u
    calc
      e (Ring.inverse x) = e (Ring.inverse (u : R)) := by rw [hu]
      _ = e (↑u⁻¹ : R) := by rw [Ring.inverse_unit]
      _ = (↑eu⁻¹ : S) := rfl
      _ = Ring.inverse (eu : S) := (Ring.inverse_unit eu).symm
      _ = Ring.inverse (e (u : R)) := by rfl
  · have he : ¬IsUnit (e x) := by
      intro hex
      apply hx
      simpa using hex.map e.symm.toMonoidHom
    rw [Ring.inverse_non_unit _ hx, Ring.inverse_non_unit _ he, map_zero]

/-- A determinant of a square polynomial matrix whose entries have degree at
most `d` has degree at most the matrix size times `d`. -/
lemma natDegree_det_le_card_mul
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    (M : Matrix ι ι ℂ[X]) (d : ℕ)
    (hM : ∀ i j, (M i j).natDegree ≤ d) :
    M.det.natDegree ≤ Fintype.card ι * d := by
  rw [Matrix.det_apply]
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro σ
  calc
    (Polynomial.natDegree
        ((Equiv.Perm.sign σ) • ∏ i : ι, M (σ i) i)) ≤
        Polynomial.natDegree (∏ i : ι, M (σ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hσ | hσ
      · rw [hσ, one_smul]
      · rw [hσ, Units.neg_smul, one_smul, Polynomial.natDegree_neg]
    _ ≤ ∑ i : ι, Polynomial.natDegree (M (σ i) i) :=
      Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _i : ι, d := Finset.sum_le_sum fun i _ => hM (σ i) i
    _ = Fintype.card ι * d := by simp

/-- Every entry of the adjugate of the characteristic matrix has degree at
most the matrix dimension.  The slightly loose `n` bound is exactly what the
order-`n` rational theorem needs. -/
lemma natDegree_charmatrix_adjugate_apply_le
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ((Matrix.charmatrix A).adjugate i j).natDegree ≤ n := by
  rw [Matrix.adjugate_apply]
  have hentry : ∀ a b,
      ((Matrix.updateRow (Matrix.charmatrix A) j (Pi.single i 1)) a b).natDegree ≤ 1 := by
    intro a b
    classical
    by_cases ha : a = j
    · subst a
      rw [Matrix.updateRow_self]
      by_cases hbi : b = i
      · subst b
        rw [Pi.single_eq_same]
        simp
      · rw [Pi.single_eq_of_ne hbi]
        simp
    · rw [Matrix.updateRow_ne ha]
      by_cases hab : a = b
      · subst b
        simp [Matrix.charmatrix_apply_eq]
      · simp [Matrix.charmatrix_apply_ne _ _ _ hab]
  simpa using natDegree_det_le_card_mul
    (Matrix.updateRow (Matrix.charmatrix A) j (Pi.single i 1)) 1 hentry

/-- Polynomial numerator `vᴴ adj(zI-A) u`. -/
def spijkerResolventNumeratorPolynomial
    {n : ℕ} (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) : ℂ[X] :=
  ∑ i : Fin n, Polynomial.C (starRingEnd ℂ (v i)) *
    ∑ j : Fin n, (Matrix.charmatrix (cstarMatrixEntries A)).adjugate i j *
      Polynomial.C (u j)

/-- The numerator polynomial has degree at most the matrix dimension. -/
lemma spijkerResolventNumeratorPolynomial_natDegree_le
    {n : ℕ} (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) :
    (spijkerResolventNumeratorPolynomial A u v).natDegree ≤ n := by
  classical
  unfold spijkerResolventNumeratorPolynomial
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro i
  calc
    (Polynomial.C (starRingEnd ℂ (v i)) *
        ∑ j : Fin n,
          (Matrix.charmatrix (cstarMatrixEntries A)).adjugate i j *
            Polynomial.C (u j)).natDegree
        ≤ (Polynomial.C (starRingEnd ℂ (v i))).natDegree +
        (∑ j : Fin n,
          (Matrix.charmatrix (cstarMatrixEntries A)).adjugate i j *
            Polynomial.C (u j)).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 0 + n := by
          gcongr
          · simp
          · refine (Polynomial.natDegree_sum_le _ _).trans ?_
            refine Multiset.max_le_of_forall_le _ _ ?_
            simp only [forall_apply_eq_imp_iff, true_and, Function.comp_apply,
              Multiset.mem_map, exists_imp, Finset.mem_univ_val]
            intro j
            calc
              ((Matrix.charmatrix (cstarMatrixEntries A)).adjugate i j *
                  Polynomial.C (u j)).natDegree
                  ≤ ((Matrix.charmatrix (cstarMatrixEntries A)).adjugate i j).natDegree +
                    (Polynomial.C (u j)).natDegree := Polynomial.natDegree_mul_le
              _ ≤ n + 0 := Nat.add_le_add
                (natDegree_charmatrix_adjugate_apply_le
                  (cstarMatrixEntries A) i j) (by simp)
              _ = n := by simp
    _ = n := by simp

/-- Evaluating the numerator polynomial gives the expected adjugate matrix
coefficient. -/
lemma eval_spijkerResolventNumeratorPolynomial
    {n : ℕ} (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) (z : ℂ) :
    (spijkerResolventNumeratorPolynomial A u v).eval z =
      inner ℂ v
        (complexMatrixEuclideanLin
          (fun i j =>
            (Matrix.scalar (Fin n) z - cstarMatrixEntries A).adjugate i j) u) := by
  classical
  let M : Matrix (Fin n) (Fin n) ℂ := cstarMatrixEntries A
  have hevalCharmatrix :
      (Polynomial.evalRingHom z).mapMatrix (Matrix.charmatrix M) =
        Matrix.scalar (Fin n) z - M := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.charmatrix_apply_eq]
    · simp [hij]
  have hevalAdjugate : ∀ i j,
      Polynomial.eval z ((Matrix.charmatrix M).adjugate i j) =
        (Matrix.scalar (Fin n) z - M).adjugate i j := by
    intro i j
    change ((Polynomial.evalRingHom z).mapMatrix
      (Matrix.charmatrix M).adjugate) i j = _
    rw [RingHom.map_adjugate, hevalCharmatrix]
  simp only [spijkerResolventNumeratorPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]
  simp_rw [show Matrix.charmatrix (cstarMatrixEntries A) = Matrix.charmatrix M from rfl,
    hevalAdjugate]
  simp [M, complexMatrixEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

/-- The scalar resolvent coefficient is rational of order at most `n`, with
the characteristic polynomial as denominator. -/
noncomputable def spijkerResolventCoefficient_rationalOrderCertificate
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) :
    RationalOrderCertificate n (spijkerResolventCoefficient A u v) := by
  classical
  let M : Matrix (Fin n) (Fin n) ℂ := cstarMatrixEntries A
  refine
    { numerator := spijkerResolventNumeratorPolynomial A u v
      denominator := M.charpoly
      numerator_degree := spijkerResolventNumeratorPolynomial_natDegree_le A u v
      denominator_degree := by
        simp [M]
      value_eq := ?_ }
  intro z hz
  rw [Matrix.eval_charpoly] at hz
  have hunit : IsUnit (Matrix.scalar (Fin n) z - M).det :=
    isUnit_iff_ne_zero.mpr hz
  change cstarMatrixEuclideanCoefficientCLM u v
      (Ring.inverse (CStarMatrix.ofMatrix
        ((Matrix.scalar (Fin n) z - M) : Matrix (Fin n) (Fin n) ℂ))) = _
  have hmapInv := ringEquiv_map_ringInverse
    (CStarMatrix.ofMatrixRingEquiv :
      Matrix (Fin n) (Fin n) ℂ ≃+* CStarMatrix (Fin n) (Fin n) ℂ)
    (Matrix.scalar (Fin n) z - M)
  change CStarMatrix.ofMatrix
      (Ring.inverse (Matrix.scalar (Fin n) z - M)) =
    Ring.inverse (CStarMatrix.ofMatrix (Matrix.scalar (Fin n) z - M)) at hmapInv
  rw [← hmapInv]
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  rw [Matrix.nonsing_inv_apply _ hunit]
  change cstarMatrixEuclideanCoefficientCLM u v
      ((↑hunit.unit⁻¹ : ℂ) • CStarMatrix.ofMatrix
        (Matrix.scalar (Fin n) z - M).adjugate) = _
  rw [map_smul]
  rw [eval_spijkerResolventNumeratorPolynomial, Matrix.eval_charpoly]
  simp only [M]
  simp [cstarMatrixEuclideanCoefficientCLM_apply, div_eq_mul_inv, mul_comm]

/-- On every exterior circle used by the Kreiss proof, the denominator in the
rational certificate is nonzero. -/
lemma spijkerResolventCoefficient_certificate_denominator_ne_on_exteriorCircle
    {n : ℕ} [Nonempty (Fin n)]
    (A : CStarMatrix (Fin n) (Fin n) ℂ)
    (u v : EuclideanSpace ℂ (Fin n)) {K R : ℝ}
    (hK : KreissResolventBound A K) (hR : 1 < R) :
    ∀ z ∈ Metric.sphere (0 : ℂ) R,
      (spijkerResolventCoefficient_rationalOrderCertificate A u v).denominator.eval z ≠ 0 := by
  intro z hz
  let M : Matrix (Fin n) (Fin n) ℂ := cstarMatrixEntries A
  change M.charpoly.eval z ≠ 0
  rw [Matrix.eval_charpoly]
  have hnorm : ‖z‖ = R := by
    simpa [Metric.mem_sphere, dist_zero_right] using hz
  have hzout : 1 < ‖z‖ := by simpa [hnorm] using hR
  have hcs : IsUnit
      (CStarMatrix.ofMatrix (Matrix.scalar (Fin n) z - M)) := by
    simpa [M, cstarMatrixEntries, Algebra.algebraMap_eq_smul_one] using (hK z hzout).1
  have hplain : IsUnit (Matrix.scalar (Fin n) z - M) := by
    have hmapped := hcs.map
      (CStarMatrix.ofMatrixRingEquiv :
        Matrix (Fin n) (Fin n) ℂ ≃+* CStarMatrix (Fin n) (Fin n) ℂ).symm.toMonoidHom
    simpa using hmapped
  exact ((Matrix.isUnit_iff_isUnit_det
    (Matrix.scalar (Fin n) z - M)).mp hplain).ne_zero

end

end NumStability
