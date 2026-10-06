import NumStability.Algorithms.TestMatrices.Higham28Contracts
import NumStability.Analysis.JordanNormalForm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

namespace NumStability

open scoped BigOperators ComplexConjugate
open Matrix Module Polynomial

noncomputable section

/-- The reverse standard-basis vector used by the companion Krylov proof. -/
private noncomputable def companionCyclicSeed (n : ℕ) (hn : 0 < n) : Fin n → ℂ :=
  Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1

/-- The final companion Krylov step closes with the coefficient vector. -/
private theorem companion_transpose_pow_seed_succ
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ n)
        (companionCyclicSeed n hn) =
      fun i => a (n - 1 - i.val) := by
  have hnform : n = (n - 1) + 1 := by omega
  have hp : (companionMatrix n a).transpose ^ n =
      (companionMatrix n a).transpose ^ (n - 1 + 1) :=
    congrArg (fun k => (companionMatrix n a).transpose ^ k) hnform
  rw [hp]
  rw [pow_succ']
  rw [← Matrix.mulVec_mulVec]
  have hk : (⟨n - 1, by omega⟩ : Fin n).val = n - 1 := rfl
  rw [show companionCyclicSeed n hn =
      Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1 by rfl]
  rw [show Matrix.mulVec ((companionMatrix n a).transpose ^ (n - 1))
      (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨n - 1, by omega⟩ : Fin n) 1 by
        simpa using companion_transpose_krylov_eq_reverseBasis hn a
          (⟨n - 1, by omega⟩ : Fin n)]
  have hrev : (Fin.rev ⟨n - 1, by omega⟩ : Fin n) =
      (⟨0, hn⟩ : Fin n) := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [hrev, Matrix.mulVec_single_one]
  funext i
  simp [companionMatrix]

/-- The source polynomial genuinely annihilates the companion matrix. -/
theorem companionCharacteristicFormula_aeval_transpose
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    Polynomial.aeval (companionMatrix n a).transpose
        (companionCharacteristicFormula n a) = 0 := by
  let A : Matrix (Fin n) (Fin n) ℂ := (companionMatrix n a).transpose
  let v : Fin n → ℂ := companionCyclicSeed n hn
  have hseed : Matrix.mulVec
      (Polynomial.aeval A (companionCharacteristicFormula n a)) v = 0 := by
    rw [companionCharacteristicFormula, map_sub, map_pow, map_sum]
    simp only [Polynomial.aeval_X, Polynomial.aeval_monomial]
    rw [Matrix.sub_mulVec]
    simp_rw [Matrix.sum_mulVec]
    simp_rw [← Algebra.smul_def]
    simp_rw [Matrix.smul_mulVec]
    rw [show Matrix.mulVec (A ^ n) v = fun i => a (n - 1 - i.val) by
      simpa [A, v] using companion_transpose_pow_seed_succ hn a]
    funext i
    simp only [Pi.sub_apply, Pi.zero_apply, Finset.sum_apply]
    rw [sub_eq_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (Fin.rev i).val]
    · have hpow := companion_transpose_krylov_eq_reverseBasis hn a (Fin.rev i)
      change Matrix.mulVec (A ^ (Fin.rev i).val) v =
        Pi.single (Fin.rev (Fin.rev i)) 1 at hpow
      rw [Fin.rev_rev] at hpow
      rw [hpow]
      simp [Fin.val_rev]
      congr 1 <;> omega
    · intro k hk hki
      let kfin : Fin n := ⟨k, Finset.mem_range.mp hk⟩
      have hpow := companion_transpose_krylov_eq_reverseBasis hn a kfin
      change Matrix.mulVec (A ^ k) v = Pi.single kfin.rev 1 at hpow
      rw [hpow]
      have hrevne : kfin.rev ≠ i := by
        intro h
        apply hki
        have := congrArg Fin.val (congrArg Fin.rev h)
        simpa [kfin] using this
      simp [hrevne]
    · intro hnot
      exact (hnot (Finset.mem_range.mpr (Fin.rev i).isLt)).elim
  apply Matrix.ext fun i j => ?_
  let k : Fin n := Fin.rev j
  have hkrylov : Matrix.mulVec (A ^ k.val) v = Pi.single j 1 := by
    have h := companion_transpose_krylov_eq_reverseBasis hn a k
    simpa only [A, v, companionCyclicSeed, k, Fin.rev_rev] using h
  have hcomm :
      Polynomial.aeval A (companionCharacteristicFormula n a) * A ^ k.val =
        A ^ k.val * Polynomial.aeval A (companionCharacteristicFormula n a) := by
    calc
      Polynomial.aeval A (companionCharacteristicFormula n a) * A ^ k.val =
          Polynomial.aeval A (companionCharacteristicFormula n a) *
            Polynomial.aeval A (Polynomial.X ^ k.val) := by simp
      _ = Polynomial.aeval A
          (companionCharacteristicFormula n a * Polynomial.X ^ k.val) := by
            rw [map_mul]
      _ = Polynomial.aeval A
          (Polynomial.X ^ k.val * companionCharacteristicFormula n a) := by
            rw [mul_comm]
      _ = A ^ k.val *
          Polynomial.aeval A (companionCharacteristicFormula n a) := by
            rw [map_mul]
            simp
  have hkill : Matrix.mulVec
      (Polynomial.aeval A (companionCharacteristicFormula n a))
      (Pi.single j 1) = 0 := by
    rw [← hkrylov, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, hseed]
    simp
  have hcol := congrFun hkill i
  simpa [Matrix.mulVec_single_one, A] using hcol

/-- The source polynomial is monic of exactly the matrix order. -/
theorem companionCharacteristicFormula_monic
    (n : ℕ) (a : ℕ → ℂ) :
    (companionCharacteristicFormula n a).Monic := by
  apply Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [companionCharacteristicFormula_coeff]
    simp [ne_of_gt hN, not_lt_of_ge hN.le]
  · rw [companionCharacteristicFormula_coeff]
    simp

theorem companionCharacteristicFormula_natDegree
    (n : ℕ) (a : ℕ → ℂ) :
    (companionCharacteristicFormula n a).natDegree = n := by
  apply le_antisymm
  · exact (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => by
      rw [companionCharacteristicFormula_coeff]
      simp [ne_of_gt hN, not_lt_of_ge hN.le])
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [companionCharacteristicFormula_coeff]
    simp

/-- The explicit companion Krylov basis forces the minimal polynomial to
have full degree. -/
private theorem companion_transpose_minpoly_natDegree_ge
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    n ≤ (minpoly ℂ (companionMatrix n a).transpose).natDegree := by
  let A : Matrix (Fin n) (Fin n) ℂ := (companionMatrix n a).transpose
  let q : Polynomial ℂ := minpoly ℂ A
  let v : Fin n → ℂ := companionCyclicSeed n hn
  by_contra hnot
  have hm : q.natDegree < n := Nat.lt_of_not_ge hnot
  let m : Fin n := ⟨q.natDegree, hm⟩
  let i : Fin n := Fin.rev m
  have hqzero : Polynomial.aeval A q = 0 := by
    exact minpoly.aeval ℂ A
  have hvec : Matrix.mulVec (Polynomial.aeval A q) v = 0 := by
    rw [hqzero]
    simp
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range] at hvec
  simp_rw [← Algebra.smul_def] at hvec
  simp_rw [Matrix.sum_mulVec, Matrix.smul_mulVec] at hvec
  have hcoord := congrFun hvec i
  simp only [Pi.zero_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hcoord
  have hsum :
      (∑ k ∈ Finset.range (q.natDegree + 1),
          q.coeff k * (Matrix.mulVec (A ^ k) v) i) = q.coeff q.natDegree := by
    rw [Finset.sum_eq_single q.natDegree]
    · let mfin : Fin n := ⟨q.natDegree, hm⟩
      have hpow := companion_transpose_krylov_eq_reverseBasis hn a mfin
      change Matrix.mulVec (A ^ q.natDegree) v = Pi.single mfin.rev 1 at hpow
      have hi : mfin.rev = i := by rfl
      rw [hpow, hi]
      simp
    · intro k hk hkm
      have hkdeg : k < q.natDegree := by
        have := Finset.mem_range.mp hk
        omega
      have hkn : k < n := lt_trans hkdeg hm
      let kfin : Fin n := ⟨k, hkn⟩
      have hpow := companion_transpose_krylov_eq_reverseBasis hn a kfin
      change Matrix.mulVec (A ^ k) v = Pi.single kfin.rev 1 at hpow
      rw [hpow]
      have hne : kfin.rev ≠ i := by
        intro h
        have hv := congrArg Fin.val (congrArg Fin.rev h)
        apply hkm
        simpa [kfin, i, m] using hv
      simp [hne]
    · intro hmem
      exact (hmem (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
  rw [hsum] at hcoord
  have hmonic : q.Monic := minpoly.monic (Matrix.isIntegral A)
  have hone : q.coeff q.natDegree = 1 := hmonic.coeff_natDegree
  rw [hone] at hcoord
  exact one_ne_zero hcoord

/-- Higham, p. 523: the characteristic polynomial of the displayed
companion matrix is exactly `X^n - ∑ aₖ X^k`. -/
theorem companionMatrix_charpoly
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    (companionMatrix n a).charpoly =
      companionCharacteristicFormula n a := by
  let A : Matrix (Fin n) (Fin n) ℂ := (companionMatrix n a).transpose
  let q : Polynomial ℂ := minpoly ℂ A
  have hdeg : n ≤ q.natDegree := by
    simpa [A, q] using companion_transpose_minpoly_natDegree_ge hn a
  have hqmonic : q.Monic := minpoly.monic (Matrix.isIntegral A)
  have hcmonic := companionCharacteristicFormula_monic n a
  have hq_dvd_c : q ∣ companionCharacteristicFormula n a := by
    apply minpoly.dvd ℂ A
    simpa [A] using companionCharacteristicFormula_aeval_transpose hn a
  have hc_eq_q : companionCharacteristicFormula n a = q := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hqmonic hcmonic hq_dvd_c
    rw [companionCharacteristicFormula_natDegree]
    exact hdeg
  have hq_dvd_char : q ∣ A.charpoly := Matrix.minpoly_dvd_charpoly A
  have hchar_eq_q : A.charpoly = q := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      hqmonic (Matrix.charpoly_monic A) hq_dvd_char
    rw [Matrix.charpoly_natDegree_eq_dim]
    simpa using hdeg
  calc
    (companionMatrix n a).charpoly = A.charpoly := by
      simpa [A] using (Matrix.charpoly_transpose (companionMatrix n a)).symm
    _ = q := hchar_eq_q
    _ = companionCharacteristicFormula n a := hc_eq_q.symm

/-- The source's `compan(poly(A))`: build a companion matrix from the
nonleading coefficients of a matrix characteristic polynomial. -/
noncomputable def companionOfMatrix
    {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  companionMatrix n (fun k => -M.charpoly.coeff k)

/-- Higham, p. 523: `compan(poly(A))` has exactly the same characteristic
polynomial, hence the same eigenvalues with algebraic multiplicity. -/
theorem companionOfMatrix_charpoly
    {n : ℕ} (hn : 0 < n) (M : Matrix (Fin n) (Fin n) ℂ) :
    (companionOfMatrix M).charpoly = M.charpoly := by
  rw [companionOfMatrix, companionMatrix_charpoly hn]
  apply Polynomial.ext
  intro k
  rw [companionCharacteristicFormula_coeff]
  by_cases hkn : k = n
  · subst k
    simp only [if_pos]
    rw [show M.charpoly.coeff n = M.charpoly.coeff M.charpoly.natDegree by
      rw [Matrix.charpoly_natDegree_eq_dim]
      simp]
    exact (Matrix.charpoly_monic M).coeff_natDegree.symm
  · rw [if_neg hkn]
    by_cases hk : k < n
    · simp [hk]
    · rw [if_neg hk]
      symm
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Matrix.charpoly_natDegree_eq_dim]
      simp
      omega

/-- Similarity preserves matrix rank. -/
theorem Matrix.IsSimilar.rank_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : Matrix.IsSimilar A B) :
    A.rank = B.rank := by
  obtain ⟨P, hP⟩ := h
  have hPdet : IsUnit (P : Matrix n n ℂ).det := by
    have hunit : IsUnit (P : Matrix n n ℂ) := P.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hunit
    exact hunit
  have hPidet : IsUnit (↑P⁻¹ : Matrix n n ℂ).det := by
    have hunit : IsUnit (↑P⁻¹ : Matrix n n ℂ) := P⁻¹.isUnit
    rw [Matrix.isUnit_iff_isUnit_det] at hunit
    exact hunit
  calc
    A.rank = ((↑P⁻¹ : Matrix n n ℂ) * A).rank := by
      symm
      exact Matrix.rank_mul_eq_right_of_isUnit_det
        (↑P⁻¹ : Matrix n n ℂ) A hPidet
    _ = ((↑P⁻¹ : Matrix n n ℂ) * A * (↑P : Matrix n n ℂ)).rank := by
      symm
      exact Matrix.rank_mul_eq_left_of_isUnit_det
        (↑P : Matrix n n ℂ) ((↑P⁻¹ : Matrix n n ℂ) * A) hPdet
    _ = B.rank := congrArg Matrix.rank hP

/-- Similarity preserves the scalar-shift ranks used in Higham's
nonderogatoriness characterization. -/
theorem Matrix.IsSimilar.rank_sub_scalar_eq
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n ℂ} (h : Matrix.IsSimilar A B) (lambda : ℂ) :
    (A - lambda • (1 : Matrix n n ℂ)).rank =
      (B - lambda • (1 : Matrix n n ℂ)).rank := by
  have hs := (Matrix.IsSimilar.add_scalar (-lambda) h).rank_eq
  have hAeq : A - lambda • (1 : Matrix n n ℂ) =
      (-lambda) • (1 : Matrix n n ℂ) + A := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  have hBeq : B - lambda • (1 : Matrix n n ℂ) =
      (-lambda) • (1 : Matrix n n ℂ) + B := by
    ext i j
    simp [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
    ring
  rw [hAeq, hBeq]
  exact hs

/-- Higham, p. 523: every matrix similar to a companion matrix inherits the
rank-form nonderogatoriness bound. -/
theorem isSimilar_companion_rank_sub_scalar_ge
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (a : ℕ → ℂ)
    (h : Matrix.IsSimilar A (companionMatrix n a)) (lambda : ℂ) :
    n - 1 ≤ Matrix.rank
      (A - lambda • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  rw [h.rank_sub_scalar_eq lambda]
  exact companionMatrix_sub_scalar_rank_ge n a lambda

/-- A concrete order-two counterexample to the source's printed complex
normality characterization: `a₀=a₁=1` gives a real symmetric (hence normal)
companion although the higher coefficient is nonzero. -/
def companionOrderTwoNormalCounterexampleCoefficients : ℕ → ℂ :=
  fun k => if k = 0 ∨ k = 1 then 1 else 0

theorem companionOrderTwoNormalCounterexample_coeff_one :
    companionOrderTwoNormalCounterexampleCoefficients 1 = 1 := by
  simp [companionOrderTwoNormalCounterexampleCoefficients]

theorem companionOrderTwoNormalCounterexample_isSelfAdjoint :
    IsSelfAdjoint
      (companionMatrix 2 companionOrderTwoNormalCounterexampleCoefficients) := by
  rw [isSelfAdjoint_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [companionMatrix, companionOrderTwoNormalCounterexampleCoefficients,
      Matrix.conjTranspose_apply]

theorem companionOrderTwoNormalCounterexample_isStarNormal :
    IsStarNormal
      (companionMatrix 2 companionOrderTwoNormalCounterexampleCoefficients) :=
  companionOrderTwoNormalCounterexample_isSelfAdjoint.isStarNormal

end

end NumStability
