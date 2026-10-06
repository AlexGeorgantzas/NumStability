/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.FourierTransform
import NumStability.Analysis.ComplexArithmetic
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace NumStability

open scoped BigOperators Matrix.Norms.L2Operator Matrix
open ComplexConjugate

/-! # Literal radix-2 FFT execution for Higham Chapter 24

Binary indices expose the input least-significant bit and output
most-significant bit at every recursion.  This is the recursive form of the
bit-reversal permutation in Theorem 24.1.
-/

/-- A length-`t` binary index, stored from the bit exposed at the current FFT
recursion to the remaining bits. -/
def Higham24BitIndex : ℕ → Type
  | 0 => Unit
  | t + 1 => Fin 2 × Higham24BitIndex t

instance higham24BitIndexFintype : ∀ t, Fintype (Higham24BitIndex t)
  | 0 => by
      change Fintype Unit
      infer_instance
  | t + 1 => by
      change Fintype (Fin 2 × Higham24BitIndex t)
      letI := higham24BitIndexFintype t
      infer_instance

instance higham24BitIndexDecidableEq : ∀ t, DecidableEq (Higham24BitIndex t)
  | 0 => by
      change DecidableEq Unit
      infer_instance
  | t + 1 => by
      change DecidableEq (Fin 2 × Higham24BitIndex t)
      letI := higham24BitIndexDecidableEq t
      infer_instance

/-- Interpret the recursive bits from least significant to most significant.
This is the input order consumed by decimation in time. -/
def higham24BitIndexLEValue : ∀ t, Higham24BitIndex t → ℕ
  | 0, _ => 0
  | t + 1, p => p.1.val + 2 * higham24BitIndexLEValue t p.2

/-- Interpret the same recursive bits from most significant to least
significant.  This is the natural output order of the recursion. -/
def higham24BitIndexBEValue : ∀ t, Higham24BitIndex t → ℕ
  | 0, _ => 0
  | t + 1, p => p.1.val * 2 ^ t + higham24BitIndexBEValue t p.2

@[simp] theorem higham24BitIndexLEValue_zero (i : Higham24BitIndex 0) :
    higham24BitIndexLEValue 0 i = 0 := rfl

@[simp] theorem higham24BitIndexLEValue_succ (t : ℕ)
    (b : Fin 2) (i : Higham24BitIndex t) :
    higham24BitIndexLEValue (t + 1) (b, i) =
      b.val + 2 * higham24BitIndexLEValue t i := rfl

@[simp] theorem higham24BitIndexBEValue_zero (i : Higham24BitIndex 0) :
    higham24BitIndexBEValue 0 i = 0 := rfl

@[simp] theorem higham24BitIndexBEValue_succ (t : ℕ)
    (b : Fin 2) (i : Higham24BitIndex t) :
    higham24BitIndexBEValue (t + 1) (b, i) =
      b.val * 2 ^ t + higham24BitIndexBEValue t i := rfl

/-- The scalar Fourier weight `exp(-2*pi*i/n)`. -/
noncomputable def higham24FourierRoot (n : ℕ) : ℂ :=
  Complex.exp (((((-2 : ℝ) * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I))

theorem higham24FourierRoot_pow_card (n : ℕ) (hn : 0 < n) :
    higham24FourierRoot n ^ n = 1 := by
  simpa [higham24FourierRoot] using
    higham9_13_fourierRoot_pow_card n 1 hn

theorem higham24FourierRoot_double (m : ℕ) (hm : 0 < m) :
    higham24FourierRoot (2 * m) ^ 2 = higham24FourierRoot m := by
  unfold higham24FourierRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor
  · norm_num
  · norm_num
    field_simp [hmR]

/-- The source butterfly block
`B = [[I, Ω], [I, -Ω]]`, indexed without flattening the two block rows.
The diagonal entries of `Ω` are the exact Fourier weights. -/
noncomputable def higham24ButterflyMatrix (k : ℕ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1
    else if p.1 = 0 then higham24FourierRoot (2 ^ (k + 1)) ^ q.2.val
    else -(higham24FourierRoot (2 ^ (k + 1)) ^ q.2.val)
  else 0

/-- Every diagonal Fourier weight in the Chapter 24 butterfly has modulus one. -/
theorem higham24_butterfly_weight_unit (k : ℕ) (j : Fin (2 ^ k)) :
    conj (higham24FourierRoot (2 ^ (k + 1))) ^ j.val *
        higham24FourierRoot (2 ^ (k + 1)) ^ j.val = 1 := by
  rw [← mul_pow]
  have hbase : conj (higham24FourierRoot (2 ^ (k + 1))) *
      higham24FourierRoot (2 ^ (k + 1)) = 1 := by
    have hnorm : ‖higham24FourierRoot (2 ^ (k + 1))‖ = 1 := by
      unfold higham24FourierRoot
      let a : ℝ := (-2 : ℝ) * Real.pi / ((2 ^ (k + 1) : ℕ) : ℝ)
      change ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1
      have hre : ((a : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre, Real.exp_zero]
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnorm]
    norm_num
  rw [hbase, one_pow]

/-- Exact orthogonality of the columns of one source butterfly block. -/
theorem higham24_butterfly_gram (k : ℕ) :
    Matrix.conjTranspose (higham24ButterflyMatrix k) *
        higham24ButterflyMatrix k = (2 : ℂ) • 1 := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Fin (2 ^ k),
    conj (higham24ButterflyMatrix k p q) *
      higham24ButterflyMatrix k p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases q with ⟨qb, qj⟩
  rcases s with ⟨sb, sj⟩
  by_cases hj : qj = sj
  · subst sj
    fin_cases qb <;> fin_cases sb <;>
      simp [higham24ButterflyMatrix, Matrix.smul_apply,
        higham24_butterfly_weight_unit] <;> norm_num
  · simp [higham24ButterflyMatrix, Matrix.smul_apply, hj, Ne.symm hj]

/-- The first norm identity used in (24.3): `‖B‖₂ = √2`. -/
theorem higham24_butterfly_norm (k : ℕ) :
    ‖higham24ButterflyMatrix k‖ = Real.sqrt 2 := by
  have hgram := congrArg norm (higham24_butterfly_gram k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hgram
  have hrhs : ‖(2 : ℂ) • (1 : Matrix (Fin 2 × Fin (2 ^ k))
      (Fin 2 × Fin (2 ^ k)) ℂ)‖ = 2 := by
    have hone : ‖(1 : Matrix (Fin 2 × Fin (2 ^ k))
        (Fin 2 × Fin (2 ^ k)) ℂ)‖ = 1 := by
      rw [show (1 : Matrix (Fin 2 × Fin (2 ^ k))
          (Fin 2 × Fin (2 ^ k)) ℂ) =
            Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
        Matrix.l2_opNorm_diagonal, Pi.norm_def,
        Finset.sup_const Finset.univ_nonempty]
      simp
    rw [norm_smul, hone]
    norm_num
  rw [hrhs] at hgram
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith [norm_nonneg (higham24ButterflyMatrix k)]

/-- Entrywise absolute value of the butterfly, represented over `ℂ`. -/
noncomputable def higham24AbsButterflyMatrix (k : ℕ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then 1 else 0

/-- The preceding definition is literally the entrywise modulus of `B`. -/
theorem higham24_absButterfly_eq_entrywise_norm (k : ℕ) :
    (fun p q => (‖higham24ButterflyMatrix k p q‖ : ℂ)) =
      higham24AbsButterflyMatrix k := by
  ext p q
  rcases p with ⟨pb, pj⟩
  rcases q with ⟨qb, qj⟩
  by_cases h : pj = qj
  · subst qj
    have hroot : ‖higham24FourierRoot (2 ^ (k + 1))‖ = 1 := by
      unfold higham24FourierRoot
      let a : ℝ := (-2 : ℝ) * Real.pi / ((2 ^ (k + 1) : ℕ) : ℝ)
      change ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1
      have hre : ((a : ℂ) * Complex.I).re = 0 := by
        simp [Complex.mul_re]
      rw [Complex.norm_exp, hre, Real.exp_zero]
    fin_cases pb <;> fin_cases qb <;>
      simp [higham24ButterflyMatrix, higham24AbsButterflyMatrix,
        hroot, norm_pow]
  · simp [higham24ButterflyMatrix, higham24AbsButterflyMatrix, h]

/-- The absolute butterfly satisfies `|B|ᴴ |B| = 2 |B|`. -/
theorem higham24_abs_butterfly_gram (k : ℕ) :
    Matrix.conjTranspose (higham24AbsButterflyMatrix k) *
        higham24AbsButterflyMatrix k =
      (2 : ℂ) • higham24AbsButterflyMatrix k := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Fin (2 ^ k),
    conj (higham24AbsButterflyMatrix k p q) *
      higham24AbsButterflyMatrix k p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases h : q.2 = s.2
  · simp [higham24AbsButterflyMatrix, h, Matrix.smul_apply]
    norm_num
  · simp [higham24AbsButterflyMatrix, h, Ne.symm h, Matrix.smul_apply]

/-- The butterfly half of the absolute-value identity in (24.3). -/
theorem higham24_abs_butterfly_norm (k : ℕ) :
    ‖higham24AbsButterflyMatrix k‖ = 2 := by
  have hgram := congrArg norm (higham24_abs_butterfly_gram k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul] at hgram
  norm_num at hgram
  have hne : higham24AbsButterflyMatrix k ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0, 0)) (0, 0)
    simp [higham24AbsButterflyMatrix] at hentry
  rcases hgram with hnorm | hzero
  · exact hnorm
  · exact (hne hzero).elim

/-- The source stage `A_k = I_(2^(t-k)) ⊗ B_(2^k)`.  Its product index is
kept nested; for the source range `1 ≤ k ≤ t` it has cardinality `2^t`. -/
noncomputable def higham24StageMatrix (t k : ℕ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24ButterflyMatrix (k - 1))

/-- Exact scaled-isometry identity for a full radix-2 stage. -/
theorem higham24_stage_gram (t k : ℕ) :
    Matrix.conjTranspose (higham24StageMatrix t k) *
        higham24StageMatrix t k = (2 : ℂ) • 1 := by
  simp only [higham24StageMatrix, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    higham24_butterfly_gram]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  by_cases ha : ia = ja <;> by_cases hb : ib = jb
  · subst ja; subst jb; simp [Matrix.kroneckerMap, Matrix.smul_apply]
  · simp [Matrix.kroneckerMap, Matrix.smul_apply, ha, hb]
  · simp [Matrix.kroneckerMap, Matrix.smul_apply, ha, hb]
  · simp [Matrix.kroneckerMap, Matrix.smul_apply, ha, hb]

/-- The stage half of (24.3): every exact `A_k` has `2`-norm `√2`. -/
theorem higham24_stage_norm (t k : ℕ) :
    ‖higham24StageMatrix t k‖ = Real.sqrt 2 := by
  have hgram := congrArg norm (higham24_stage_gram t k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hgram
  have hrhs : ‖(2 : ℂ) • (1 : Matrix
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ)‖ = 2 := by
    have hone : ‖(1 : Matrix
        (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
        (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ)‖ = 1 := by
      rw [show (1 : Matrix
          (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
          (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ) =
            Matrix.diagonal (fun _ => (1 : ℂ)) from Matrix.diagonal_one.symm,
        Matrix.l2_opNorm_diagonal, Pi.norm_def,
        Finset.sup_const Finset.univ_nonempty]
      simp
    rw [norm_smul, hone]
    norm_num
  rw [hrhs] at hgram
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith [norm_nonneg (higham24StageMatrix t k)]

/-- Entrywise absolute value of the source stage `A_k`. -/
noncomputable def higham24AbsStageMatrix (t k : ℕ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24AbsButterflyMatrix (k - 1))

/-- The absolute stage definition is literally entrywise modulus of `A_k`. -/
theorem higham24_absStage_eq_entrywise_norm (t k : ℕ) :
    (fun p q => (‖higham24StageMatrix t k p q‖ : ℂ)) =
      higham24AbsStageMatrix t k := by
  ext p q
  rcases p with ⟨pa, pb⟩
  rcases q with ⟨qa, qb⟩
  simp only [higham24StageMatrix, higham24AbsStageMatrix, Matrix.kronecker]
  by_cases h : pa = qa
  · subst qa
    simp only [Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply,
      if_pos, one_mul]
    exact congrFun (congrFun
      (higham24_absButterfly_eq_entrywise_norm (k - 1)) pb) qb
  · simp [Matrix.kroneckerMap, h]

/-- The absolute source stage satisfies `|A_k|ᴴ |A_k| = 2 |A_k|`. -/
theorem higham24_abs_stage_gram (t k : ℕ) :
    Matrix.conjTranspose (higham24AbsStageMatrix t k) *
        higham24AbsStageMatrix t k =
      (2 : ℂ) • higham24AbsStageMatrix t k := by
  simp only [higham24AbsStageMatrix, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    higham24_abs_butterfly_gram]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  simp only [Matrix.smul_apply]
  by_cases ha : ia = ja
  · subst ja; simp
  · simp [ha]

/-- The stage half of the absolute-value identity in (24.3). -/
theorem higham24_abs_stage_norm (t k : ℕ) :
    ‖higham24AbsStageMatrix t k‖ = 2 := by
  have hgram := congrArg norm (higham24_abs_stage_gram t k)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul] at hgram
  norm_num at hgram
  have hne : higham24AbsStageMatrix t k ≠ 0 := by
    intro hzero
    have hentry := congrFun (congrFun hzero (0, (0, 0))) (0, (0, 0))
    simp [higham24AbsStageMatrix, Matrix.kronecker, Matrix.kroneckerMap,
      higham24AbsButterflyMatrix] at hentry
  exact hgram.resolve_right hne

/-- The additive butterfly perturbation induced by weight errors `e_j`.
Only the diagonal-weight block changes, with opposite signs in the two rows. -/
noncomputable def higham24ButterflyPerturbation (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 0
    else if p.1 = 0 then e q.2 else -(e q.2)
  else 0

noncomputable def higham24ButterflyPerturbationGramDiagonal (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) : (Fin 2 × Fin (2 ^ k)) → ℂ :=
  fun q => if q.1 = 0 then 0 else 2 * (conj (e q.2) * e q.2)

theorem higham24_butterflyPerturbation_gram (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) :
    Matrix.conjTranspose (higham24ButterflyPerturbation k e) *
        higham24ButterflyPerturbation k e =
      Matrix.diagonal (higham24ButterflyPerturbationGramDiagonal k e) := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Fin (2 ^ k),
    conj (higham24ButterflyPerturbation k e p q) *
      higham24ButterflyPerturbation k e p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases q with ⟨qb, qj⟩
  rcases s with ⟨sb, sj⟩
  by_cases hj : qj = sj
  · subst sj
    fin_cases qb <;> fin_cases sb
    all_goals simp [higham24ButterflyPerturbation,
      higham24ButterflyPerturbationGramDiagonal] <;> ring
  · simp [higham24ButterflyPerturbation, hj, Ne.symm hj]

theorem higham24_butterflyPerturbation_norm_le (k : ℕ)
    (e : Fin (2 ^ k) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (he : ∀ j, ‖e j‖ ≤ mu) :
    ‖higham24ButterflyPerturbation k e‖ ≤ mu * Real.sqrt 2 := by
  have hsq : ‖higham24ButterflyPerturbation k e‖ *
      ‖higham24ButterflyPerturbation k e‖ ≤ 2 * mu ^ 2 := by
    calc
      ‖higham24ButterflyPerturbation k e‖ *
          ‖higham24ButterflyPerturbation k e‖ =
          ‖Matrix.conjTranspose (higham24ButterflyPerturbation k e) *
            higham24ButterflyPerturbation k e‖ := by
              rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖Matrix.diagonal
          (higham24ButterflyPerturbationGramDiagonal k e)‖ := by
            rw [higham24_butterflyPerturbation_gram]
      _ = ‖higham24ButterflyPerturbationGramDiagonal k e‖ :=
            Matrix.l2_opNorm_diagonal _
      _ ≤ 2 * mu ^ 2 := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro q
        rcases q with ⟨qb, qj⟩
        fin_cases qb
        · simp [higham24ButterflyPerturbationGramDiagonal]
          positivity
        · simp [higham24ButterflyPerturbationGramDiagonal]
          nlinarith [norm_nonneg (e qj), he qj]
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hrhs_sq : (mu * Real.sqrt 2) ^ 2 = 2 * mu ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    ring
  have hrhs_nonneg : 0 ≤ mu * Real.sqrt 2 := mul_nonneg hmu hsqrt
  nlinarith [norm_nonneg (higham24ButterflyPerturbation k e)]

/-- The full stage perturbation `ΔA_k = I ⊗ ΔB_k`. -/
noncomputable def higham24StagePerturbation (t k : ℕ)
    (e : Fin (2 ^ (k - 1)) → ℂ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24ButterflyPerturbation (k - 1) e)

theorem higham24_stagePerturbation_gram (t k : ℕ)
    (e : Fin (2 ^ (k - 1)) → ℂ) :
    Matrix.conjTranspose (higham24StagePerturbation t k e) *
        higham24StagePerturbation t k e =
      Matrix.diagonal (fun q =>
        higham24ButterflyPerturbationGramDiagonal (k - 1) e q.2) := by
  simp only [higham24StagePerturbation, Matrix.kronecker]
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul,
    Matrix.conjTranspose_one, Matrix.one_mul,
    higham24_butterflyPerturbation_gram]
  ext i j
  rcases i with ⟨ia, ib⟩
  rcases j with ⟨ja, jb⟩
  by_cases ha : ia = ja
  · subst ja
    by_cases hb : ib = jb
    · subst jb; simp [Matrix.kroneckerMap]
    · simp [Matrix.kroneckerMap, hb]
  · simp [Matrix.kroneckerMap, ha]

theorem higham24_stagePerturbation_norm_le (t k : ℕ)
    (e : Fin (2 ^ (k - 1)) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (he : ∀ j, ‖e j‖ ≤ mu) :
    ‖higham24StagePerturbation t k e‖ ≤ mu * Real.sqrt 2 := by
  have hsq : ‖higham24StagePerturbation t k e‖ *
      ‖higham24StagePerturbation t k e‖ ≤ 2 * mu ^ 2 := by
    calc
      ‖higham24StagePerturbation t k e‖ *
          ‖higham24StagePerturbation t k e‖ =
          ‖Matrix.conjTranspose (higham24StagePerturbation t k e) *
            higham24StagePerturbation t k e‖ := by
              rw [Matrix.l2_opNorm_conjTranspose_mul_self]
      _ = ‖Matrix.diagonal
          (fun q : Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))) =>
            higham24ButterflyPerturbationGramDiagonal (k - 1) e q.2)‖ := by
            rw [higham24_stagePerturbation_gram]
      _ = ‖fun q : Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))) =>
          higham24ButterflyPerturbationGramDiagonal (k - 1) e q.2‖ :=
            Matrix.l2_opNorm_diagonal _
      _ ≤ 2 * mu ^ 2 := by
        apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro q
        rcases q with ⟨qa, qb, qj⟩
        fin_cases qb
        · simp [higham24ButterflyPerturbationGramDiagonal]
          positivity
        · simp [higham24ButterflyPerturbationGramDiagonal]
          nlinarith [norm_nonneg (e qj), he qj]
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hrhs_sq : (mu * Real.sqrt 2) ^ 2 = 2 * mu ^ 2 := by
    rw [mul_pow, hsqrt_sq]
    ring
  have hrhs_nonneg : 0 ≤ mu * Real.sqrt 2 := mul_nonneg hmu hsqrt
  nlinarith [norm_nonneg (higham24StagePerturbation t k e)]

/-- A butterfly using the actually computed diagonal weights. -/
noncomputable def higham24ComputedButterflyMatrix (k : ℕ)
    (weight : Fin (2 ^ k) → ℂ) :
    Matrix (Fin 2 × Fin (2 ^ k)) (Fin 2 × Fin (2 ^ k)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1
    else if p.1 = 0 then weight q.2 else -(weight q.2)
  else 0

theorem higham24_computedButterfly_sub (k : ℕ)
    (weight : Fin (2 ^ k) → ℂ) :
    higham24ComputedButterflyMatrix k weight - higham24ButterflyMatrix k =
      higham24ButterflyPerturbation k (fun j =>
        weight j - higham24FourierRoot (2 ^ (k + 1)) ^ j.val) := by
  ext p q
  rcases p with ⟨pb, pj⟩
  rcases q with ⟨qb, qj⟩
  by_cases hj : pj = qj
  · subst qj
    fin_cases pb <;> fin_cases qb
    all_goals simp [higham24ComputedButterflyMatrix, higham24ButterflyMatrix,
      higham24ButterflyPerturbation] <;> ring
  · simp [higham24ComputedButterflyMatrix, higham24ButterflyMatrix,
      higham24ButterflyPerturbation, hj]

/-- The source computed stage `Ã_k = I ⊗ B̃_k`. -/
noncomputable def higham24ComputedStageMatrix (t k : ℕ)
    (weight : Fin (2 ^ (k - 1)) → ℂ) :
    Matrix (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1))))
      (Fin (2 ^ (t - k)) × (Fin 2 × Fin (2 ^ (k - 1)))) ℂ :=
  Matrix.kronecker
    (1 : Matrix (Fin (2 ^ (t - k))) (Fin (2 ^ (t - k))) ℂ)
    (higham24ComputedButterflyMatrix (k - 1) weight)

theorem higham24_computedStage_sub (t k : ℕ)
    (weight : Fin (2 ^ (k - 1)) → ℂ) (hk : 1 ≤ k) :
    higham24ComputedStageMatrix t k weight - higham24StageMatrix t k =
      higham24StagePerturbation t k (fun j =>
        weight j - higham24FourierRoot (2 ^ k) ^ j.val) := by
  ext p q
  rcases p with ⟨pa, pb⟩
  rcases q with ⟨qa, qb⟩
  simp only [higham24ComputedStageMatrix, higham24StageMatrix,
    higham24StagePerturbation, Matrix.kronecker, Matrix.sub_apply]
  by_cases h : pa = qa
  · subst qa
    simp only [Matrix.kroneckerMap, Matrix.of_apply, Matrix.one_apply, if_pos,
      one_mul]
    simpa [Nat.sub_add_cancel hk] using
      congrFun (congrFun
        (higham24_computedButterfly_sub (k - 1) weight) pb) qb
  · simp [Matrix.kroneckerMap, h]

/-- Equation (24.4), including the printed representation
`Ã_k = A_k + ΔA_k` and the relative stage-norm bound. -/
theorem higham24_eq24_4 (t k : ℕ)
    (weight : Fin (2 ^ (k - 1)) → ℂ) (mu : ℝ)
    (hk : 1 ≤ k) (_hkt : k ≤ t) (hmu : 0 ≤ mu)
    (hw : ∀ j, Higham24WeightApproximation
      (higham24FourierRoot (2 ^ k) ^ j.val) (weight j) mu) :
    higham24ComputedStageMatrix t k weight = higham24StageMatrix t k +
        higham24StagePerturbation t k (fun j =>
          weight j - higham24FourierRoot (2 ^ k) ^ j.val) ∧
      ‖higham24StagePerturbation t k (fun j =>
          weight j - higham24FourierRoot (2 ^ k) ^ j.val)‖ ≤
        mu * ‖higham24StageMatrix t k‖ := by
  constructor
  · have hsub := higham24_computedStage_sub t k weight hk
    rw [sub_eq_iff_eq_add] at hsub
    simpa [add_comm] using hsub
  · rw [higham24_stage_norm]
    exact higham24_stagePerturbation_norm_le t k _ mu hmu fun j =>
      higham24_eq24_2_error_bound (hw j)

/-- A DFT written on recursive binary indices.  Input indices use their
little-endian value; output indices use their big-endian value. -/
noncomputable def higham24BinaryDFT (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t) : ℂ :=
  ∑ j, higham24FourierRoot (2 ^ t) ^
      (higham24BitIndexBEValue t k * higham24BitIndexLEValue t j) * x j

/-- Literal recursive decimation-in-time radix-2 FFT. -/
noncomputable def higham24Radix2FFT : ∀ t,
    (Higham24BitIndex t → ℂ) → Higham24BitIndex t → ℂ
  | 0, x, _ => x ()
  | t + 1, x, p =>
      let even := higham24Radix2FFT t (fun j => x (0, j)) p.2
      let odd := higham24Radix2FFT t (fun j => x (1, j)) p.2
      even + higham24FourierRoot (2 ^ (t + 1)) ^
        (higham24BitIndexBEValue (t + 1) p) * odd

theorem higham24FourierRoot_pow_reduce_two_blocks
    (m : ℕ) (hm : 0 < m) (b : Fin 2) (r j : ℕ) :
    higham24FourierRoot m ^ ((b.val * m + r) * j) =
      higham24FourierRoot m ^ (r * j) := by
  rw [Nat.add_mul, pow_add]
  have hblock :
      higham24FourierRoot m ^ (b.val * m * j) = 1 := by
    calc
      higham24FourierRoot m ^ (b.val * m * j) =
          higham24FourierRoot m ^ (m * (b.val * j)) := by
            congr 1
            ring
      _ = (higham24FourierRoot m ^ m) ^ (b.val * j) := by rw [pow_mul]
      _ = 1 := by rw [higham24FourierRoot_pow_card m hm]; simp
  rw [hblock, one_mul]

theorem higham24FourierRoot_even_exponent
    (m : ℕ) (hm : 0 < m) (b : Fin 2) (r j : ℕ) :
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (2 * j)) =
      higham24FourierRoot m ^ (r * j) := by
  calc
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (2 * j)) =
        higham24FourierRoot (2 * m) ^ (2 * ((b.val * m + r) * j)) := by
          congr 1
          ring
    _ = (higham24FourierRoot (2 * m) ^ 2) ^ ((b.val * m + r) * j) := by
          rw [pow_mul]
    _ = higham24FourierRoot m ^ ((b.val * m + r) * j) := by
          rw [higham24FourierRoot_double m hm]
    _ = higham24FourierRoot m ^ (r * j) :=
          higham24FourierRoot_pow_reduce_two_blocks m hm b r j

theorem higham24FourierRoot_odd_exponent
    (m : ℕ) (hm : 0 < m) (b : Fin 2) (r j : ℕ) :
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (1 + 2 * j)) =
      higham24FourierRoot (2 * m) ^ (b.val * m + r) *
        higham24FourierRoot m ^ (r * j) := by
  calc
    higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (1 + 2 * j)) =
        higham24FourierRoot (2 * m) ^
          ((b.val * m + r) + (b.val * m + r) * (2 * j)) := by
            congr 1
            ring
    _ = higham24FourierRoot (2 * m) ^ (b.val * m + r) *
          higham24FourierRoot (2 * m) ^ ((b.val * m + r) * (2 * j)) := by
            rw [pow_add]
    _ = higham24FourierRoot (2 * m) ^ (b.val * m + r) *
          higham24FourierRoot m ^ (r * j) := by
            rw [higham24FourierRoot_even_exponent m hm b r j]

/-- The literal recursion computes the binary-index DFT exactly. -/
theorem higham24Radix2FFT_eq_binaryDFT :
    ∀ t (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t),
      higham24Radix2FFT t x k = higham24BinaryDFT t x k := by
  intro t
  induction t with
  | zero =>
      intro x k
      change Unit at k
      rcases k with ⟨⟩
      simp [higham24Radix2FFT, higham24BinaryDFT,
        Higham24BitIndex, higham24BitIndexBEValue,
        higham24BitIndexLEValue]
  | succ t ih =>
      intro x k
      rcases k with ⟨b, k⟩
      rw [higham24Radix2FFT]
      rw [ih (fun j => x (0, j)) k, ih (fun j => x (1, j)) k]
      unfold higham24BinaryDFT
      conv_rhs =>
        change ∑ j : Fin 2 × Higham24BitIndex t, _
        rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [higham24BitIndexBEValue_succ, higham24BitIndexLEValue_succ,
        Fin.val_zero, Fin.val_one, zero_add]
      apply congrArg₂ (· + ·)
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [show 2 ^ (t + 1) = 2 * 2 ^ t by rw [pow_succ']]
        rw [higham24FourierRoot_even_exponent (2 ^ t) (by positivity) b
          (higham24BitIndexBEValue t k) (higham24BitIndexLEValue t j)]
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [show 2 ^ (t + 1) = 2 * 2 ^ t by rw [pow_succ']]
        rw [higham24FourierRoot_odd_exponent (2 ^ t) (by positivity) b
          (higham24BitIndexBEValue t k) (higham24BitIndexLEValue t j)]
        ring

/-- Little-endian binary words enumerate `Fin (2^t)`. -/
def higham24BitIndexLEEquiv : ∀ t, Higham24BitIndex t ≃ Fin (2 ^ t)
  | 0 => finOneEquiv.symm
  | t + 1 =>
      (Equiv.prodCongr (Equiv.refl (Fin 2)) (higham24BitIndexLEEquiv t)).trans
        ((Equiv.prodComm (Fin 2) (Fin (2 ^ t))).trans
          (finProdFinEquiv.trans (finCongr (by rw [pow_succ]))))

/-- Big-endian binary words enumerate `Fin (2^t)`. -/
def higham24BitIndexBEEquiv : ∀ t, Higham24BitIndex t ≃ Fin (2 ^ t)
  | 0 => finOneEquiv.symm
  | t + 1 =>
      (Equiv.prodCongr (Equiv.refl (Fin 2)) (higham24BitIndexBEEquiv t)).trans
        (finProdFinEquiv.trans (finCongr (by rw [pow_succ'])))

theorem higham24BitIndexLEEquiv_val :
    ∀ t (i : Higham24BitIndex t),
      (higham24BitIndexLEEquiv t i).val = higham24BitIndexLEValue t i := by
  intro t
  induction t with
  | zero => intro i; cases i; rfl
  | succ t ih =>
      intro i
      rcases i with ⟨b, i⟩
      change b.val + 2 * (higham24BitIndexLEEquiv t i).val =
        b.val + 2 * higham24BitIndexLEValue t i
      rw [ih]

theorem higham24BitIndexBEEquiv_val :
    ∀ t (i : Higham24BitIndex t),
      (higham24BitIndexBEEquiv t i).val = higham24BitIndexBEValue t i := by
  intro t
  induction t with
  | zero => intro i; cases i; rfl
  | succ t ih =>
      intro i
      rcases i with ⟨b, i⟩
      change (higham24BitIndexBEEquiv t i).val + 2 ^ t * b.val =
        b.val * 2 ^ t + higham24BitIndexBEValue t i
      rw [ih]
      ring

theorem higham24FourierRoot_pow (n q : ℕ) (hn : 0 < n) :
    higham24FourierRoot n ^ q =
      Complex.exp (((((-2 : ℝ) * Real.pi * (q : ℝ) / (n : ℝ) : ℝ) : ℂ) *
        Complex.I)) := by
  unfold higham24FourierRoot
  rw [← Complex.exp_nat_mul]
  congr 1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  simp only [Complex.ext_iff, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  constructor
  · norm_num
  · norm_num
    field_simp [hnR]

/-- The binary-index DFT is the canonical Chapter 24 DFT after the explicit
input/output reindexings. -/
theorem higham24BinaryDFT_eq_dftApply (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t) :
    higham24BinaryDFT t x k =
      higham24DFTApply
        (fun i => x ((higham24BitIndexLEEquiv t).symm i))
        (higham24BitIndexBEEquiv t k) := by
  unfold higham24BinaryDFT higham24DFTApply higham24DFT
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  apply Fintype.sum_equiv (higham24BitIndexLEEquiv t)
  intro j
  rw [(higham24BitIndexLEEquiv t).symm_apply_apply]
  rw [higham24FourierRoot_pow (2 ^ t)
    (higham24BitIndexBEValue t k * higham24BitIndexLEValue t j) (by positivity)]
  unfold higham9_13_fourierVandermonde
  rw [higham24BitIndexBEEquiv_val, higham24BitIndexLEEquiv_val]
  apply congrArg (fun z : ℂ => z * x j)
  congr 1
  norm_num [Nat.cast_mul]
  ring

/-- Source-facing radix-2 correctness theorem.  The input permutation is the
bit-reversal map from little-endian recursive words to ordinary `Fin` indices;
the output is in ordinary DFT order. -/
theorem higham24Radix2FFT_eq_dftApply (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (k : Higham24BitIndex t) :
    higham24Radix2FFT t x k =
      higham24DFTApply
        (fun i => x ((higham24BitIndexLEEquiv t).symm i))
        (higham24BitIndexBEEquiv t k) := by
  rw [higham24Radix2FFT_eq_binaryDFT, higham24BinaryDFT_eq_dftApply]

/-- The final radix-2 stage on binary indices.  The first input column is `I`;
the second is the diagonal Fourier-weight block, including its lower sign. -/
noncomputable def higham24BinaryTopStageMatrix (t : ℕ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1
    else higham24FourierRoot (2 ^ (t + 1)) ^
      higham24BitIndexBEValue (t + 1) p
  else 0

/-- Block-diagonal lift `I₂ ⊗ M` to one more binary index. -/
noncomputable def higham24BinaryLiftMatrix {t : ℕ}
    (M : Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.1 = q.1 then M p.2 q.2 else 0

theorem higham24_binaryTopStage_mulVec (t : ℕ)
    (x : Higham24BitIndex (t + 1) → ℂ)
    (p : Higham24BitIndex (t + 1)) :
    (higham24BinaryTopStageMatrix t).mulVec x p =
      x (0, p.2) + higham24FourierRoot (2 ^ (t + 1)) ^
        higham24BitIndexBEValue (t + 1) p * x (1, p.2) := by
  simp only [Matrix.mulVec, dotProduct, higham24BinaryTopStageMatrix]
  change (∑ q : Fin 2 × Higham24BitIndex t, _) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

theorem higham24_binaryLift_mulVec {t : ℕ}
    (M : Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ)
    (x : Higham24BitIndex (t + 1) → ℂ)
    (p : Higham24BitIndex (t + 1)) :
    (higham24BinaryLiftMatrix M).mulVec x p =
      M.mulVec (fun j => x (p.1, j)) p.2 := by
  simp only [Matrix.mulVec, dotProduct, higham24BinaryLiftMatrix]
  change (∑ q : Fin 2 × Higham24BitIndex t, _) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨b, i⟩
  fin_cases b <;> simp

/-- The literal ordered product `A_t ⋯ A₁` on binary indices.  Recursively,
the earlier stages lift block-diagonally and the new `B_(2^(t+1))` stage is
multiplied on the left. -/
noncomputable def higham24BinaryStageProduct : ∀ t,
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ
  | 0 => 1
  | t + 1 => higham24BinaryTopStageMatrix t *
      higham24BinaryLiftMatrix (higham24BinaryStageProduct t)

theorem higham24_binaryStageProduct_mulVec :
    ∀ t (x : Higham24BitIndex t → ℂ) (p : Higham24BitIndex t),
    (higham24BinaryStageProduct t).mulVec x p =
      higham24Radix2FFT t x p := by
  intro t
  induction t with
  | zero =>
      intro x p
      change Unit at p
      rcases p with ⟨⟩
      rw [higham24BinaryStageProduct, Matrix.one_mulVec]
      rfl
  | succ t ih =>
      intro x p
      rw [higham24BinaryStageProduct, ← Matrix.mulVec_mulVec,
        higham24_binaryTopStage_mulVec]
      rw [higham24_binaryLift_mulVec, higham24_binaryLift_mulVec, ih, ih]
      rfl

noncomputable def higham24BinaryDFTMatrix (t : ℕ) :
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ :=
  fun k j => higham24FourierRoot (2 ^ t) ^
    (higham24BitIndexBEValue t k * higham24BitIndexLEValue t j)

theorem higham24_binaryDFTMatrix_mulVec (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (p : Higham24BitIndex t) :
    (higham24BinaryDFTMatrix t).mulVec x p = higham24BinaryDFT t x p := by
  rfl

theorem higham24_binaryDFTMatrix_eq_stageProduct (t : ℕ) :
    higham24BinaryDFTMatrix t = higham24BinaryStageProduct t := by
  ext p q
  let x : Higham24BitIndex t → ℂ := Pi.single q 1
  have hp := higham24_binaryStageProduct_mulVec t x p
  rw [higham24Radix2FFT_eq_binaryDFT] at hp
  have hd := higham24_binaryDFTMatrix_mulVec t x p
  simpa [x, Matrix.col_apply, Matrix.mulVec_single] using hd.trans hp.symm

/-- The source bit-reversal permutation `P_n`, expressed on binary words.
It sends a big-endian input coordinate to the little-endian coordinate consumed
by the decimation-in-time stage product. -/
noncomputable def higham24BitReversalMatrix (t : ℕ) :
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ :=
  fun p q => if higham24BitIndexLEEquiv t p =
      higham24BitIndexBEEquiv t q then 1 else 0

/-- The canonical DFT matrix with both coordinates read in big-endian order. -/
noncomputable def higham24BigEndianDFTMatrix (t : ℕ) :
    Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ :=
  fun p q => higham24FourierRoot (2 ^ t) ^
    (higham24BitIndexBEValue t p * higham24BitIndexBEValue t q)

/-- Theorem 24.1 / equation (24.1), with all reindexing explicit:
`F_n = A_t ⋯ A₁ P_n` for `n = 2^t`. -/
theorem higham24_theorem24_1_stage_factorization (t : ℕ) :
    higham24BigEndianDFTMatrix t =
      higham24BinaryStageProduct t * higham24BitReversalMatrix t := by
  rw [← higham24_binaryDFTMatrix_eq_stageProduct]
  ext p q
  rw [Matrix.mul_apply]
  let j0 : Higham24BitIndex t :=
    (higham24BitIndexLEEquiv t).symm (higham24BitIndexBEEquiv t q)
  rw [Finset.sum_eq_single j0]
  · have hj0 : higham24BitIndexLEValue t j0 =
        higham24BitIndexBEValue t q := by
      rw [← higham24BitIndexLEEquiv_val,
        ← higham24BitIndexBEEquiv_val]
      simp [j0]
    simp [higham24BigEndianDFTMatrix, higham24BinaryDFTMatrix,
      higham24BitReversalMatrix, j0, hj0]
  · intro j _hj hne
    have hdiff : higham24BitIndexLEEquiv t j ≠
        higham24BitIndexBEEquiv t q := by
      intro heq
      apply hne
      exact (higham24BitIndexLEEquiv t).injective
        (by simpa [j0] using heq)
    simp [higham24BitReversalMatrix, hdiff]
  · intro hnot
    exact (hnot (Finset.mem_univ j0)).elim

/-- Literal rounded recursion.  Each butterfly uses the repository's rounded
complex multiplication and addition; the supplied weight table permits the
computed weights of (24.2). -/
noncomputable def higham24RoundedRadix2FFT (fp : FPModel)
    (weight : ∀ t, Higham24BitIndex t → ℂ) : ∀ t,
    (Higham24BitIndex t → ℂ) → Higham24BitIndex t → ℂ
  | 0, x, _ => x ()
  | t + 1, x, p =>
      let even := higham24RoundedRadix2FFT fp weight t (fun j => x (0, j)) p.2
      let odd := higham24RoundedRadix2FFT fp weight t (fun j => x (1, j)) p.2
      fl_complexAdd fp even (fl_complexMul fp (weight (t + 1) p) odd)

/-- One literal rounded butterfly output satisfies the primitive complex
addition/multiplication error decomposition used to build a stage contract. -/
theorem higham24_roundedButterfly_pointwise_error_bound
    (fp : FPModel) (hgamma2 : gammaValid fp 2) (a w b : ℂ) :
    ‖fl_complexAdd fp a (fl_complexMul fp w b) - (a + w * b)‖ ≤
      fp.u * ‖a + fl_complexMul fp w b‖ +
        Real.sqrt 2 * gamma fp 2 * ‖w * b‖ := by
  calc
    ‖fl_complexAdd fp a (fl_complexMul fp w b) - (a + w * b)‖ =
        ‖(fl_complexAdd fp a (fl_complexMul fp w b) -
            (a + fl_complexMul fp w b)) +
          (fl_complexMul fp w b - w * b)‖ := by
            congr 1
            ring
    _ ≤ ‖fl_complexAdd fp a (fl_complexMul fp w b) -
          (a + fl_complexMul fp w b)‖ +
        ‖fl_complexMul fp w b - w * b‖ := norm_add_le _ _
    _ ≤ fp.u * ‖a + fl_complexMul fp w b‖ +
        Real.sqrt 2 * gamma fp 2 * ‖w * b‖ :=
      add_le_add (fl_complexAdd_error_bound fp a (fl_complexMul fp w b))
        (fl_complexMul_error_bound fp hgamma2 w b)

/-- The complex multiply followed by the complex add in one radix-2 butterfly
fits inside the source `γ₄` coefficient.  This is the scalar arithmetic bridge
needed before constructing the stage perturbation in Theorem 24.2. -/
theorem higham24_sqrtTwo_gamma2_add_u_le_gamma4
    (fp : FPModel) (hgamma4 : gammaValid fp 4) :
    Real.sqrt 2 * gamma fp 2 + fp.u +
        (Real.sqrt 2 * gamma fp 2) * fp.u ≤ gamma fp 4 := by
  have hgamma2 : gammaValid fp 2 :=
    gammaValid_mono fp (by norm_num) hgamma4
  have hgamma2_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hgamma2
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hs0 := Real.sqrt_nonneg (2 : ℝ)
    have hs2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    nlinarith
  have hmul : Real.sqrt 2 * gamma fp 2 ≤
      (3 / 2 : ℝ) * gamma fp 2 :=
    mul_le_mul_of_nonneg_right hsqrt hgamma2_nonneg
  have hfirst :
      Real.sqrt 2 * gamma fp 2 + fp.u +
          (Real.sqrt 2 * gamma fp 2) * fp.u ≤
        (3 / 2 : ℝ) * gamma fp 2 + fp.u +
          ((3 / 2 : ℝ) * gamma fp 2) * fp.u :=
    add_le_add (add_le_add hmul le_rfl)
      (mul_le_mul_of_nonneg_right hmul fp.u_nonneg)
  refine hfirst.trans ?_
  have hu4 : 4 * fp.u < 1 := by
    simpa [gammaValid] using hgamma4
  have hd2 : 0 < 1 - 2 * fp.u := by linarith
  have hd4 : 0 < 1 - 4 * fp.u := by linarith
  have hd2c : 1 - fp.u * 2 ≠ 0 := by nlinarith
  have hd4c : 1 - fp.u * 4 ≠ 0 := by nlinarith
  have hgamma2_eq : gamma fp 2 = 2 * fp.u / (1 - 2 * fp.u) := by
    norm_num [gamma]
  have hgamma4_eq : gamma fp 4 = 4 * fp.u / (1 - 4 * fp.u) := by
    norm_num [gamma]
  rw [hgamma2_eq, hgamma4_eq]
  have hleft :
      (3 / 2 : ℝ) * (2 * fp.u / (1 - 2 * fp.u)) + fp.u +
          ((3 / 2 : ℝ) * (2 * fp.u / (1 - 2 * fp.u))) * fp.u =
        (4 * fp.u + fp.u ^ 2) / (1 - 2 * fp.u) := by
    field_simp [ne_of_gt hd2, hd2c]
    ring
  rw [hleft]
  have hiff :
      ((4 * fp.u + fp.u ^ 2) / (1 - 2 * fp.u) ≤
          4 * fp.u / (1 - 4 * fp.u)) ↔
        (0 ≤ 4 * fp.u / (1 - 4 * fp.u) -
          (4 * fp.u + fp.u ^ 2) / (1 - 2 * fp.u)) := by
    constructor <;> intro h <;> linarith
  rw [hiff]
  have hdiff :
      4 * fp.u / (1 - 4 * fp.u) -
          (4 * fp.u + fp.u ^ 2) / (1 - 2 * fp.u) =
        (7 * fp.u ^ 2 + 4 * fp.u ^ 3) /
          ((1 - 4 * fp.u) * (1 - 2 * fp.u)) := by
    field_simp [ne_of_gt hd2, ne_of_gt hd4, hd2c, hd4c]
    ring
  rw [hdiff]
  apply div_nonneg
  · exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg fp.u))
      (mul_nonneg (by norm_num)
        (mul_nonneg (sq_nonneg fp.u) fp.u_nonneg))
  · exact le_of_lt (mul_pos hd4 hd2)

/-- One literal rounded radix-2 butterfly is a two-term exact linear
combination with separate relative perturbations on its two inputs, and both
perturbations are bounded by `γ₄`.  The witnesses are obtained from the
repository's primitive rounded complex multiply and add models; no stage or
final FFT error conclusion is assumed. -/
theorem higham24_roundedButterfly_exists_relative_coefficients
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (a w b : ℂ) :
    ∃ deltaA deltaB : ℂ,
      ‖deltaA‖ ≤ gamma fp 4 ∧ ‖deltaB‖ ≤ gamma fp 4 ∧
        fl_complexAdd fp a (fl_complexMul fp w b) =
          a * (1 + deltaA) + w * b * (1 + deltaB) := by
  have hgamma2 : gammaValid fp 2 :=
    gammaValid_mono fp (by norm_num) hgamma4
  rcases fl_complexMul_rel_error_model fp hgamma2 w b with
    ⟨deltaMul, hdeltaMul, hmul⟩
  rcases fl_complexAdd_rel_error_model fp a (fl_complexMul fp w b) with
    ⟨deltaAdd, hdeltaAdd, hadd⟩
  let deltaB : ℂ := (1 + deltaMul) * (1 + deltaAdd) - 1
  refine ⟨deltaAdd, deltaB, ?_, ?_, ?_⟩
  · exact hdeltaAdd.trans (u_le_gamma fp (by norm_num) hgamma4)
  · have hdeltaB_eq : deltaB =
        deltaMul + deltaAdd + deltaMul * deltaAdd := by
      dsimp [deltaB]
      ring
    rw [hdeltaB_eq]
    have hradius_nonneg :
        0 ≤ Real.sqrt 2 * gamma fp 2 :=
      mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hgamma2)
    have hproduct : ‖deltaMul‖ * ‖deltaAdd‖ ≤
        (Real.sqrt 2 * gamma fp 2) * fp.u :=
      mul_le_mul hdeltaMul hdeltaAdd (norm_nonneg deltaAdd) hradius_nonneg
    calc
      ‖deltaMul + deltaAdd + deltaMul * deltaAdd‖ ≤
          ‖deltaMul + deltaAdd‖ + ‖deltaMul * deltaAdd‖ := norm_add_le _ _
      _ ≤ (‖deltaMul‖ + ‖deltaAdd‖) + ‖deltaMul * deltaAdd‖ :=
        add_le_add (norm_add_le _ _) le_rfl
      _ = ‖deltaMul‖ + ‖deltaAdd‖ + ‖deltaMul‖ * ‖deltaAdd‖ := by
        rw [norm_mul]
      _ ≤ Real.sqrt 2 * gamma fp 2 + fp.u +
          (Real.sqrt 2 * gamma fp 2) * fp.u :=
        add_le_add (add_le_add hdeltaMul hdeltaAdd) hproduct
      _ ≤ gamma fp 4 :=
        higham24_sqrtTwo_gamma2_add_u_le_gamma4 fp hgamma4
  · rw [hadd, hmul]
    dsimp [deltaB]
    ring

/-- An entrywise relative perturbation bound gives the Euclidean operator
`2`-norm estimate used in the stage analysis.  This is the finite-dimensional
monotonicity step behind `‖E‖₂ ≤ c ‖|A|‖₂`; unlike the later FFT trace
interface, it is proved directly from the matrix entries. -/
theorem higham24_op2_le_scaled_abs_of_entrywise
    {m n : ℕ} (hn : 0 < n) (A E : CMatrix m n) (c : ℝ)
    (hc : 0 ≤ c)
    (hentry : ∀ i j, ‖E i j‖ ≤ c * ‖A i j‖) :
    complexMatrixOp2 E ≤ c * complexMatrixOp2 (complexAbsMatrix A) := by
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  let νsrc : CVec n → ℝ :=
    complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))
  let νtgt : CVec m → ℝ :=
    complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ))
  have hmono : IsMonotoneComplexVectorNorm νtgt := by
    simpa [νtgt] using
      complexVecLpNorm_ofReal_monotone (n := m) (p := (2 : ℝ)) (by norm_num)
  have hbound :
      HasComplexMatrixLpBound (ENNReal.ofReal (2 : ℝ)) E
        (c * complexMatrixOp2 (complexAbsMatrix A)) := by
    refine ⟨mul_nonneg hc (complexMatrixOp2_nonneg _), ?_⟩
    intro x
    have hcomponent :
        componentwiseAbsLe (complexMatrixVecMul E x)
          (complexVecSMul (c : ℂ)
            (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x))) := by
      intro i
      calc
        ‖complexMatrixVecMul E x i‖
            ≤ ∑ j : Fin n, ‖E i j * x j‖ := by
              unfold complexMatrixVecMul
              exact norm_sum_le Finset.univ (fun j : Fin n => E i j * x j)
        _ = ∑ j : Fin n, ‖E i j‖ * ‖x j‖ := by
              apply Finset.sum_congr rfl
              intro j _hj
              rw [norm_mul]
        _ ≤ ∑ j : Fin n, (c * ‖A i j‖) * ‖x j‖ := by
              apply Finset.sum_le_sum
              intro j _hj
              exact mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
        _ = c * ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _hj
              ring
        _ = c *
              ‖complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x) i‖ := by
              rw [complexMatrixVecMul_absMatrix_absVec_norm_apply]
        _ = ‖complexVecSMul (c : ℂ)
              (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x)) i‖ := by
              simp [complexVecSMul, abs_of_nonneg hc]
    calc
      νtgt (complexMatrixVecMul E x)
          ≤ νtgt (complexVecSMul (c : ℂ)
              (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x))) :=
            hmono _ _ hcomponent
      _ = c * νtgt
            (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x)) := by
            have hsmul :=
              (complexVecLpNorm_isComplexVectorNorm
                (n := m) (ENNReal.ofReal (2 : ℝ))).smul
                (c : ℂ)
                (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x))
            simpa [νtgt, abs_of_nonneg hc] using hsmul
      _ ≤ c * (complexMatrixOp2 (complexAbsMatrix A) *
            νsrc (complexAbsVec x)) := by
            exact mul_le_mul_of_nonneg_left
              ((complexMatrixOp2_hasComplexMatrixLpBound
                (complexAbsMatrix A)).2 (complexAbsVec x)) hc
      _ = (c * complexMatrixOp2 (complexAbsMatrix A)) * νsrc x := by
            have habs : νsrc (complexAbsVec x) = νsrc x := by
              simpa [νsrc] using
                complexVecLpNorm_ofReal_abs_eq
                  (n := n) (p := (2 : ℝ)) (by norm_num) x
            rw [habs]
            ring
  have hvalue :=
    complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn (2 : ℝ) (by norm_num) E
  have hle := isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
    hvalue hbound
  simpa [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn E] using hle

/-- Entrywise modulus of a complex matrix, retaining arbitrary finite index
types and the matrix operator-norm instance. -/
noncomputable def higham24EntrywiseAbsMatrix
    {ι κ : Type*} (A : Matrix ι κ ℂ) : Matrix ι κ ℂ :=
  fun i j => (‖A i j‖ : ℂ)

/-- Index-generic form of the same entrywise-to-operator-`2` argument.  This
version is needed for the binary product indices used by the literal FFT
recursion, and is proved directly in Mathlib's Euclidean matrix norm. -/
theorem higham24_l2OpNorm_le_scaled_abs_of_entrywise
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A E : Matrix ι κ ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hentry : ∀ i j, ‖E i j‖ ≤ c * ‖A i j‖) :
    ‖E‖ ≤ c * ‖higham24EntrywiseAbsMatrix A‖ := by
  let absA : Matrix ι κ ℂ := higham24EntrywiseAbsMatrix A
  rw [Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hc (norm_nonneg absA)) ?_
  intro x
  let xabs : EuclideanSpace ℂ κ :=
    WithLp.toLp (2 : ENNReal) (fun j => (‖WithLp.ofLp x j‖ : ℂ))
  let y : EuclideanSpace ℂ ι :=
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := ι) (n := κ)).trans
      LinearMap.toContinuousLinearMap E) x
  let yabs : EuclideanSpace ℂ ι :=
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := ι) (n := κ)).trans
      LinearMap.toContinuousLinearMap absA) xabs
  have hxabs : ‖xabs‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    simp [xabs]
  have hcoord (i : ι) : ‖y i‖ ≤ c * ‖yabs i‖ := by
    have htarget :
        ‖yabs i‖ = ∑ j : κ, ‖A i j‖ * ‖WithLp.ofLp x j‖ := by
      change ‖∑ j : κ, (‖A i j‖ : ℂ) * (‖WithLp.ofLp x j‖ : ℂ)‖ = _
      calc
        ‖∑ j : κ, (‖A i j‖ : ℂ) * (‖WithLp.ofLp x j‖ : ℂ)‖ =
            ‖((∑ j : κ, ‖A i j‖ * ‖WithLp.ofLp x j‖ : ℝ) : ℂ)‖ := by
              congr 1
              rw [Complex.ofReal_sum]
              apply Finset.sum_congr rfl
              intro j _hj
              rw [Complex.ofReal_mul]
        _ = ∑ j : κ, ‖A i j‖ * ‖WithLp.ofLp x j‖ :=
          Complex.norm_of_nonneg
            (Finset.sum_nonneg fun j _hj =>
              mul_nonneg (norm_nonneg _) (norm_nonneg _))
    calc
      ‖y i‖ = ‖∑ j : κ, E i j * WithLp.ofLp x j‖ := by rfl
      _ ≤ ∑ j : κ, ‖E i j * WithLp.ofLp x j‖ :=
        norm_sum_le Finset.univ _
      _ = ∑ j : κ, ‖E i j‖ * ‖WithLp.ofLp x j‖ := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [norm_mul]
      _ ≤ ∑ j : κ, (c * ‖A i j‖) * ‖WithLp.ofLp x j‖ := by
        apply Finset.sum_le_sum
        intro j _hj
        exact mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
      _ = c * ∑ j : κ, ‖A i j‖ * ‖WithLp.ofLp x j‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
      _ = c * ‖yabs i‖ := by rw [htarget]
  have hy_le : ‖y‖ ≤ ‖(c : ℂ) • yabs‖ := by
    refine (sq_le_sq₀ (norm_nonneg y) (norm_nonneg ((c : ℂ) • yabs))).mp ?_
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro i _hi
    apply (sq_le_sq₀ (norm_nonneg (y i))
      (norm_nonneg (((c : ℂ) • yabs) i))).mpr
    change ‖y i‖ ≤ ‖(c : ℂ) * yabs i‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    exact hcoord i
  calc
    ‖((Matrix.toEuclideanLin (𝕜 := ℂ) (m := ι) (n := κ)).trans
        LinearMap.toContinuousLinearMap E) x‖ = ‖y‖ := rfl
    _ ≤ ‖(c : ℂ) • yabs‖ := hy_le
    _ = c * ‖yabs‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    _ ≤ c * (‖absA‖ * ‖xabs‖) := by
      exact mul_le_mul_of_nonneg_left (Matrix.l2_opNorm_mulVec absA xabs) hc
    _ = (c * ‖absA‖) * ‖x‖ := by rw [hxabs]; ring
    _ = (c * ‖higham24EntrywiseAbsMatrix A‖) * ‖x‖ := by rfl

/-- Every Chapter 24 Fourier root has unit modulus. -/
theorem higham24FourierRoot_norm (n : ℕ) : ‖higham24FourierRoot n‖ = 1 := by
  unfold higham24FourierRoot
  let a : ℝ := (-2 : ℝ) * Real.pi / (n : ℝ)
  change ‖Complex.exp ((a : ℂ) * Complex.I)‖ = 1
  have hre : ((a : ℂ) * Complex.I).re = 0 := by
    simp [Complex.mul_re]
  rw [Complex.norm_exp, hre, Real.exp_zero]

/-- The half-period Fourier weight in a radix-2 stage is `-1`. -/
theorem higham24FourierRoot_pow_half (t : ℕ) :
    higham24FourierRoot (2 ^ (t + 1)) ^ (2 ^ t) = -1 := by
  let r : ℝ := (-2 : ℝ) * Real.pi / ((2 ^ (t + 1) : ℕ) : ℝ)
  change Complex.exp ((r : ℂ) * Complex.I) ^ (2 ^ t) = -1
  rw [← Complex.exp_nat_mul]
  have hpow : ((2 ^ (t + 1) : ℕ) : ℝ) =
      2 * ((2 ^ t : ℕ) : ℝ) := by
    norm_num [pow_succ]
    ring
  have hpos : (0 : ℝ) < ((2 ^ t : ℕ) : ℝ) := by positivity
  have hscalar :
      ((2 ^ t : ℕ) : ℝ) * r = -Real.pi := by
    dsimp [r]
    rw [hpow]
    field_simp [hpos.ne']
  have harg :
      ((2 ^ t : ℕ) : ℂ) * ((r : ℂ) * Complex.I) =
        -((Real.pi : ℂ) * Complex.I) := by
    have hnat : ((2 ^ t : ℕ) : ℂ) =
        ((((2 ^ t : ℕ) : ℝ)) : ℂ) := by norm_num
    rw [hnat, ← mul_assoc, ← Complex.ofReal_mul, hscalar]
    simp [mul_comm]
  rw [harg, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The actually supplied row weights, before arithmetic rounding, as a
matrix on the literal recursive binary indices. -/
noncomputable def higham24ComputedBinaryTopStageMatrix (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 1 else weight p
  else 0

/-- Literal rounded application of the preceding binary top stage. -/
noncomputable def higham24RoundedBinaryTopStageApply (fp : FPModel) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : Higham24BitIndex (t + 1) → ℂ) :
    Higham24BitIndex (t + 1) → ℂ :=
  fun p => fl_complexAdd fp (z (0, p.2))
    (fl_complexMul fp (weight p) (z (1, p.2)))

/-- Entrywise absolute value of the exact binary top stage. -/
noncomputable def higham24BinaryAbsTopStageMatrix (t : ℕ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.2 = q.2 then 1 else 0

theorem higham24_binaryAbsTopStage_gram (t : ℕ) :
    Matrix.conjTranspose (higham24BinaryAbsTopStageMatrix t) *
        higham24BinaryAbsTopStageMatrix t =
      (2 : ℂ) • higham24BinaryAbsTopStageMatrix t := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Higham24BitIndex t,
    conj (higham24BinaryAbsTopStageMatrix t p q) *
      higham24BinaryAbsTopStageMatrix t p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  by_cases h : q.2 = s.2
  · simp [higham24BinaryAbsTopStageMatrix, h, Matrix.smul_apply]
    norm_num
  · simp [higham24BinaryAbsTopStageMatrix, h, Ne.symm h, Matrix.smul_apply]

/-- Binary-index form of the absolute-stage identity `‖|A_k|‖₂ = 2`. -/
theorem higham24_binaryAbsTopStage_norm (t : ℕ) :
    ‖higham24BinaryAbsTopStageMatrix t‖ = 2 := by
  have hgram := congrArg norm (higham24_binaryAbsTopStage_gram t)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, norm_smul] at hgram
  norm_num at hgram
  have hne : higham24BinaryAbsTopStageMatrix t ≠ 0 := by
    intro hzero
    let j0 : Higham24BitIndex t := (higham24BitIndexBEEquiv t).symm 0
    have hentry : (1 : ℂ) = 0 := by
      have h := congrArg
        (fun M : Matrix (Higham24BitIndex (t + 1))
            (Higham24BitIndex (t + 1)) ℂ => M (0, j0) (0, j0)) hzero
      have h' : higham24BinaryAbsTopStageMatrix t (0, j0) (0, j0) =
          (0 : ℂ) := by
        simpa only [Pi.zero_apply] using h
      simp [higham24BinaryAbsTopStageMatrix] at h'
    exact one_ne_zero hentry
  exact hgram.resolve_right hne

/-- The sparsity mask for a perturbation confined to the second input of
each radix-2 butterfly. -/
noncomputable def higham24BinarySecondColumnMask (t : ℕ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 0 else 1
  else 0

theorem higham24_binarySecondColumnMask_gram (t : ℕ) :
    Matrix.conjTranspose (higham24BinarySecondColumnMask t) *
        higham24BinarySecondColumnMask t =
      Matrix.diagonal (fun q => if q.1 = 0 then (0 : ℂ) else 2) := by
  ext q s
  rw [Matrix.mul_apply]
  change (∑ p : Fin 2 × Higham24BitIndex t,
    conj (higham24BinarySecondColumnMask t p q) *
      higham24BinarySecondColumnMask t p s) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases q with ⟨qb, qj⟩
  rcases s with ⟨sb, sj⟩
  have hrow (b : Fin 2) :
      (∑ y : Higham24BitIndex t,
        conj (higham24BinarySecondColumnMask t (b, y) (qb, qj)) *
          higham24BinarySecondColumnMask t (b, y) (sb, sj)) =
        conj (higham24BinarySecondColumnMask t (b, qj) (qb, qj)) *
          higham24BinarySecondColumnMask t (b, qj) (sb, sj) := by
    apply Finset.sum_eq_single qj
    · intro y _hy hne
      simp [higham24BinarySecondColumnMask, hne]
    · simp
  rw [hrow 0, hrow 1]
  by_cases hj : qj = sj
  · subst sj
    by_cases hb : qb = sb
    · subst sb
      fin_cases qb <;> norm_num [higham24BinarySecondColumnMask]
    · have hpair : (qb, qj) ≠ (sb, qj) := by
        intro h
        exact hb (congrArg Prod.fst h)
      fin_cases qb <;> fin_cases sb <;>
        simp [higham24BinarySecondColumnMask, Matrix.diagonal_apply] at hb ⊢
      intro hp
      have hfirst := congrArg Prod.fst hp
      norm_num at hfirst
  · have hpair : (qb, qj) ≠ (sb, sj) := by
      intro h
      exact hj (congrArg Prod.snd h)
    simp [higham24BinarySecondColumnMask, hj, Matrix.diagonal_apply]
    intro hp
    exact (hpair hp).elim

/-- The second-column mask has operator norm `√2`, independently of the
number of butterflies. -/
theorem higham24_binarySecondColumnMask_norm (t : ℕ) :
    ‖higham24BinarySecondColumnMask t‖ = Real.sqrt 2 := by
  have hgram := congrArg norm (higham24_binarySecondColumnMask_gram t)
  rw [Matrix.l2_opNorm_conjTranspose_mul_self,
    Matrix.l2_opNorm_diagonal] at hgram
  have hdiag : ‖(fun q : Higham24BitIndex (t + 1) =>
      if q.1 = 0 then (0 : ℂ) else 2)‖ = 2 := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (by norm_num)).2
      intro q
      rcases q with ⟨qb, qj⟩
      fin_cases qb <;> simp
    · let j0 : Higham24BitIndex t := (higham24BitIndexBEEquiv t).symm 0
      have hcoord := norm_le_pi_norm
        (fun q : Higham24BitIndex (t + 1) =>
          if q.1 = 0 then (0 : ℂ) else 2) (1, j0)
      simpa using hcoord
  rw [hdiag] at hgram
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  nlinarith [norm_nonneg (higham24BinarySecondColumnMask t)]

/-- A row-dependent perturbation confined to the second input column of each
binary butterfly. -/
noncomputable def higham24BinarySecondColumnPerturbation (t : ℕ)
    (d : Higham24BitIndex (t + 1) → ℂ) :
    Matrix (Higham24BitIndex (t + 1)) (Higham24BitIndex (t + 1)) ℂ :=
  fun p q => if p.2 = q.2 then
    if q.1 = 0 then 0 else d p
  else 0

theorem higham24_entrywiseAbs_binarySecondColumnMask (t : ℕ) :
    higham24EntrywiseAbsMatrix (higham24BinarySecondColumnMask t) =
      higham24BinarySecondColumnMask t := by
  ext p q
  by_cases hj : p.2 = q.2
  · by_cases hb : q.1 = 0 <;>
      simp [higham24EntrywiseAbsMatrix, higham24BinarySecondColumnMask, hj, hb]
  · simp [higham24EntrywiseAbsMatrix, higham24BinarySecondColumnMask, hj]

/-- Uniform rowwise coefficient bounds give the sharp block-diagonal
`μ√2` norm estimate for a second-column perturbation. -/
theorem higham24_binarySecondColumnPerturbation_norm_le (t : ℕ)
    (d : Higham24BitIndex (t + 1) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (hd : ∀ p, ‖d p‖ ≤ mu) :
    ‖higham24BinarySecondColumnPerturbation t d‖ ≤ mu * Real.sqrt 2 := by
  have hentry : ∀ p q,
      ‖higham24BinarySecondColumnPerturbation t d p q‖ ≤
        mu * ‖higham24BinarySecondColumnMask t p q‖ := by
    intro p q
    by_cases hj : p.2 = q.2
    · by_cases hb : q.1 = 0
      · simp [higham24BinarySecondColumnPerturbation,
          higham24BinarySecondColumnMask, hj, hb]
      · simpa [higham24BinarySecondColumnPerturbation,
          higham24BinarySecondColumnMask, hj, hb] using hd p
    · simp [higham24BinarySecondColumnPerturbation,
        higham24BinarySecondColumnMask, hj]
  have hnorm := higham24_l2OpNorm_le_scaled_abs_of_entrywise
    (higham24BinarySecondColumnMask t)
    (higham24BinarySecondColumnPerturbation t d) mu hmu hentry
  rw [higham24_entrywiseAbs_binarySecondColumnMask,
    higham24_binarySecondColumnMask_norm] at hnorm
  exact hnorm

/-- Exact Fourier weight used in a row of the binary top stage. -/
noncomputable def higham24ExactBinaryTopWeight (t : ℕ)
    (p : Higham24BitIndex (t + 1)) : ℂ :=
  higham24FourierRoot (2 ^ (t + 1)) ^
    higham24BitIndexBEValue (t + 1) p

theorem higham24_exactBinaryTopWeight_norm (t : ℕ)
    (p : Higham24BitIndex (t + 1)) :
    ‖higham24ExactBinaryTopWeight t p‖ = 1 := by
  simp [higham24ExactBinaryTopWeight, norm_pow, higham24FourierRoot_norm]

theorem higham24_exactBinaryTopWeight_lower (t : ℕ)
    (j : Higham24BitIndex t) :
    higham24ExactBinaryTopWeight t (1, j) =
      -higham24ExactBinaryTopWeight t (0, j) := by
  unfold higham24ExactBinaryTopWeight
  simp only [higham24BitIndexBEValue_succ, Fin.val_one, one_mul,
    Fin.val_zero, zero_mul, zero_add]
  rw [pow_add, higham24FourierRoot_pow_half]
  ring

@[simp] theorem higham24_computedBinaryTopStage_exactWeight (t : ℕ) :
    higham24ComputedBinaryTopStageMatrix t (higham24ExactBinaryTopWeight t) =
      higham24BinaryTopStageMatrix t := by
  rfl

theorem higham24_computedBinaryTopStage_sub (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ) :
    higham24ComputedBinaryTopStageMatrix t weight -
        higham24BinaryTopStageMatrix t =
      higham24BinarySecondColumnPerturbation t
        (fun p => weight p - higham24ExactBinaryTopWeight t p) := by
  ext p q
  by_cases hj : p.2 = q.2
  · by_cases hb : q.1 = 0 <;>
      simp [higham24ComputedBinaryTopStageMatrix,
        higham24BinaryTopStageMatrix, higham24ExactBinaryTopWeight,
        higham24BinarySecondColumnPerturbation, hj, hb]
  · simp [higham24ComputedBinaryTopStageMatrix,
      higham24BinaryTopStageMatrix,
      higham24BinarySecondColumnPerturbation, hj]

/-- Weight model (24.2) gives the `μ√2` computed-stage perturbation bound on
the actual binary top-stage matrix. -/
theorem higham24_computedBinaryTopStage_sub_norm_le (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ p, Higham24WeightApproximation
      (higham24ExactBinaryTopWeight t p) (weight p) mu) :
    ‖higham24ComputedBinaryTopStageMatrix t weight -
        higham24BinaryTopStageMatrix t‖ ≤ mu * Real.sqrt 2 := by
  rw [higham24_computedBinaryTopStage_sub]
  exact higham24_binarySecondColumnPerturbation_norm_le t _ mu hmu
    (fun p => higham24_eq24_2_error_bound (hw p))

/-- The entrywise absolute computed-weight stage is the exact absolute stage
plus a second-column perturbation in the weight moduli. -/
theorem higham24_entrywiseAbs_computedBinaryTopStage (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ) :
    higham24EntrywiseAbsMatrix
        (higham24ComputedBinaryTopStageMatrix t weight) =
      higham24BinaryAbsTopStageMatrix t +
        higham24BinarySecondColumnPerturbation t
          (fun p => ((‖weight p‖ - 1 : ℝ) : ℂ)) := by
  ext p q
  by_cases hj : p.2 = q.2
  · by_cases hb : q.1 = 0
    · simp [higham24EntrywiseAbsMatrix,
        higham24ComputedBinaryTopStageMatrix,
        higham24BinaryAbsTopStageMatrix,
        higham24BinarySecondColumnPerturbation, hj, hb]
    · simp [higham24EntrywiseAbsMatrix,
        higham24ComputedBinaryTopStageMatrix,
        higham24BinaryAbsTopStageMatrix,
        higham24BinarySecondColumnPerturbation, hj, hb]
  · simp [higham24EntrywiseAbsMatrix,
      higham24ComputedBinaryTopStageMatrix,
      higham24BinaryAbsTopStageMatrix,
      higham24BinarySecondColumnPerturbation, hj]

/-- The printed absolute-stage estimate
`‖|Ã_k|‖₂ ≤ 2 + μ√2 = (√2+μ)‖A_k‖₂`, proved from (24.2). -/
theorem higham24_computedBinaryTopStage_abs_norm_le (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ p, Higham24WeightApproximation
      (higham24ExactBinaryTopWeight t p) (weight p) mu) :
    ‖higham24EntrywiseAbsMatrix
        (higham24ComputedBinaryTopStageMatrix t weight)‖ ≤
      2 + mu * Real.sqrt 2 := by
  have hd : ∀ p : Higham24BitIndex (t + 1),
      ‖((‖weight p‖ - 1 : ℝ) : ℂ)‖ ≤ mu := by
    intro p
    have hexact : ‖higham24ExactBinaryTopWeight t p‖ = 1 := by
      simp [higham24ExactBinaryTopWeight, norm_pow, higham24FourierRoot_norm]
    calc
      ‖((‖weight p‖ - 1 : ℝ) : ℂ)‖ = |‖weight p‖ - 1| := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ = |‖weight p‖ - ‖higham24ExactBinaryTopWeight t p‖| := by rw [hexact]
      _ ≤ ‖weight p - higham24ExactBinaryTopWeight t p‖ :=
        abs_norm_sub_norm_le _ _
      _ ≤ mu := higham24_eq24_2_error_bound (hw p)
  rw [higham24_entrywiseAbs_computedBinaryTopStage]
  calc
    ‖higham24BinaryAbsTopStageMatrix t +
        higham24BinarySecondColumnPerturbation t
          (fun p => ((‖weight p‖ - 1 : ℝ) : ℂ))‖
        ≤ ‖higham24BinaryAbsTopStageMatrix t‖ +
          ‖higham24BinarySecondColumnPerturbation t
            (fun p => ((‖weight p‖ - 1 : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 2 + mu * Real.sqrt 2 := by
      rw [higham24_binaryAbsTopStage_norm]
      exact add_le_add le_rfl
        (higham24_binarySecondColumnPerturbation_norm_le t _ mu hmu hd)

/-- The literal rounded binary top stage produces an explicit arithmetic
perturbation satisfying `|E| ≤ γ₄ |Ã|` entrywise. -/
theorem higham24_roundedBinaryTopStage_exists_perturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : Higham24BitIndex (t + 1) → ℂ) :
    ∃ E : Matrix (Higham24BitIndex (t + 1))
        (Higham24BitIndex (t + 1)) ℂ,
      (∀ p q, ‖E p q‖ ≤ gamma fp 4 *
        ‖higham24ComputedBinaryTopStageMatrix t weight p q‖) ∧
      higham24RoundedBinaryTopStageApply fp t weight z =
        (higham24ComputedBinaryTopStageMatrix t weight + E).mulVec z := by
  choose deltaA deltaB hdeltaA hdeltaB hrounded using
    fun p : Higham24BitIndex (t + 1) =>
      higham24_roundedButterfly_exists_relative_coefficients
        fp hgamma4 (z (0, p.2)) (weight p) (z (1, p.2))
  let E : Matrix (Higham24BitIndex (t + 1))
      (Higham24BitIndex (t + 1)) ℂ := fun p q =>
    if p.2 = q.2 then
      if q.1 = 0 then deltaA p else weight p * deltaB p
    else 0
  refine ⟨E, ?_, ?_⟩
  · intro p q
    by_cases hj : p.2 = q.2
    · by_cases hb : q.1 = 0
      · simpa [E, higham24ComputedBinaryTopStageMatrix, hj, hb,
          gamma_nonneg fp hgamma4] using hdeltaA p
      · have hmul : ‖weight p * deltaB p‖ ≤
            gamma fp 4 * ‖weight p‖ := by
          rw [norm_mul]
          calc
            ‖weight p‖ * ‖deltaB p‖
                ≤ ‖weight p‖ * gamma fp 4 :=
                  mul_le_mul_of_nonneg_left (hdeltaB p) (norm_nonneg _)
            _ = gamma fp 4 * ‖weight p‖ := by ring
        simpa [E, higham24ComputedBinaryTopStageMatrix, hj, hb] using hmul
    · simp [E, higham24ComputedBinaryTopStageMatrix, hj]
  · funext p
    change fl_complexAdd fp (z (0, p.2))
        (fl_complexMul fp (weight p) (z (1, p.2))) = _
    simp only [Matrix.mulVec, dotProduct]
    change _ = ∑ q : Fin 2 × Higham24BitIndex t,
      (higham24ComputedBinaryTopStageMatrix t weight + E) p q * z q
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    have hrow (b : Fin 2) :
        (∑ j : Higham24BitIndex t,
          (higham24ComputedBinaryTopStageMatrix t weight + E) p (b, j) *
            z (b, j)) =
          (higham24ComputedBinaryTopStageMatrix t weight + E) p (b, p.2) *
            z (b, p.2) := by
      apply Finset.sum_eq_single p.2
      · intro j _hj hne
        simp [higham24ComputedBinaryTopStageMatrix, E, Ne.symm hne]
      · simp
    rw [hrow 0, hrow 1]
    simp [higham24ComputedBinaryTopStageMatrix, E]
    rw [hrounded p]
    ring

/-- The arithmetic perturbation of the literal rounded stage has the printed
`γ₄(2+μ√2)` norm bound once (24.2) is supplied. -/
theorem higham24_roundedBinaryTopStage_exists_arithmetic_op2_bound
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : Higham24BitIndex (t + 1) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ p, Higham24WeightApproximation
      (higham24ExactBinaryTopWeight t p) (weight p) mu) :
    ∃ E : Matrix (Higham24BitIndex (t + 1))
        (Higham24BitIndex (t + 1)) ℂ,
      higham24RoundedBinaryTopStageApply fp t weight z =
        (higham24ComputedBinaryTopStageMatrix t weight + E).mulVec z ∧
      ‖E‖ ≤ gamma fp 4 * (2 + mu * Real.sqrt 2) := by
  rcases higham24_roundedBinaryTopStage_exists_perturbation
      fp hgamma4 t weight z with ⟨E, hentry, happly⟩
  refine ⟨E, happly, ?_⟩
  have hE := higham24_l2OpNorm_le_scaled_abs_of_entrywise
    (higham24ComputedBinaryTopStageMatrix t weight) E
    (gamma fp 4) (gamma_nonneg fp hgamma4) hentry
  exact hE.trans (mul_le_mul_of_nonneg_left
    (higham24_computedBinaryTopStage_abs_norm_le t weight mu hmu hw)
    (gamma_nonneg fp hgamma4))

/-- Complete one-stage producer for the coefficient
`η = μ + γ₄(√2+μ)`: the literal rounded operation is one exact source stage
plus a produced perturbation of norm at most `η√2`. -/
theorem higham24_roundedBinaryTopStage_exists_total_op2_bound
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : Higham24BitIndex (t + 1) → ℂ) (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ p, Higham24WeightApproximation
      (higham24ExactBinaryTopWeight t p) (weight p) mu) :
    ∃ Delta : Matrix (Higham24BitIndex (t + 1))
        (Higham24BitIndex (t + 1)) ℂ,
      higham24RoundedBinaryTopStageApply fp t weight z =
        (higham24BinaryTopStageMatrix t + Delta).mulVec z ∧
      ‖Delta‖ ≤ higham24Eta mu (gamma fp 4) * Real.sqrt 2 := by
  rcases higham24_roundedBinaryTopStage_exists_arithmetic_op2_bound
      fp hgamma4 t weight z mu hmu hw with ⟨E, happly, hE⟩
  let Delta :=
    higham24ComputedBinaryTopStageMatrix t weight -
      higham24BinaryTopStageMatrix t + E
  refine ⟨Delta, ?_, ?_⟩
  · rw [happly]
    congr 1
    ext p q
    simp [Delta]
    ring
  · have hweight := higham24_computedBinaryTopStage_sub_norm_le
      t weight mu hmu hw
    have hsum : ‖Delta‖ ≤ mu * Real.sqrt 2 +
        gamma fp 4 * (2 + mu * Real.sqrt 2) := by
      calc
        ‖Delta‖ ≤
            ‖higham24ComputedBinaryTopStageMatrix t weight -
              higham24BinaryTopStageMatrix t‖ + ‖E‖ := by
                exact norm_add_le _ _
        _ ≤ mu * Real.sqrt 2 + gamma fp 4 *
            (2 + mu * Real.sqrt 2) := add_le_add hweight hE
    have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
    have hcoeff : mu * Real.sqrt 2 + gamma fp 4 *
          (2 + mu * Real.sqrt 2) =
        higham24Eta mu (gamma fp 4) * Real.sqrt 2 := by
      calc
        mu * Real.sqrt 2 + gamma fp 4 * (2 + mu * Real.sqrt 2) =
            mu * Real.sqrt 2 + gamma fp 4 *
              ((Real.sqrt 2) ^ 2 + mu * Real.sqrt 2) := by rw [hsqrt_sq]
        _ = higham24Eta mu (gamma fp 4) * Real.sqrt 2 := by
          unfold higham24Eta
          ring
    exact hsum.trans_eq hcoeff

/-- Euclidean norm on the literal recursive binary index type. -/
noncomputable def higham24BinaryEuclideanNorm (t : ℕ)
    (x : Higham24BitIndex t → ℂ) : ℝ :=
  ‖(WithLp.toLp (2 : ENNReal) x : EuclideanSpace ℂ (Higham24BitIndex t))‖

/-- The exact binary top stage is a scaled isometry: applying it multiplies
the Euclidean vector norm by `√2`. -/
theorem higham24_binaryTopStage_euclideanNorm (t : ℕ)
    (z : Higham24BitIndex (t + 1) → ℂ) :
    higham24BinaryEuclideanNorm (t + 1)
        ((higham24BinaryTopStageMatrix t).mulVec z) =
      Real.sqrt 2 * higham24BinaryEuclideanNorm (t + 1) z := by
  have hpair (j : Higham24BitIndex t) :
      ‖(higham24BinaryTopStageMatrix t).mulVec z (0, j)‖ ^ 2 +
          ‖(higham24BinaryTopStageMatrix t).mulVec z (1, j)‖ ^ 2 =
        2 * (‖z (0, j)‖ ^ 2 + ‖z (1, j)‖ ^ 2) := by
    rw [higham24_binaryTopStage_mulVec, higham24_binaryTopStage_mulVec]
    change ‖z (0, j) + higham24ExactBinaryTopWeight t (0, j) * z (1, j)‖ ^ 2 +
        ‖z (0, j) + higham24ExactBinaryTopWeight t (1, j) * z (1, j)‖ ^ 2 = _
    rw [higham24_exactBinaryTopWeight_lower, neg_mul]
    change ‖z (0, j) + higham24ExactBinaryTopWeight t (0, j) * z (1, j)‖ ^ 2 +
        ‖z (0, j) - higham24ExactBinaryTopWeight t (0, j) * z (1, j)‖ ^ 2 = _
    calc
      ‖z (0, j) + higham24ExactBinaryTopWeight t (0, j) * z (1, j)‖ ^ 2 +
          ‖z (0, j) - higham24ExactBinaryTopWeight t (0, j) * z (1, j)‖ ^ 2 =
        2 * (‖z (0, j)‖ ^ 2 +
          ‖higham24ExactBinaryTopWeight t (0, j) * z (1, j)‖ ^ 2) :=
            parallelogram_law_with_norm ℂ _ _
      _ = 2 * (‖z (0, j)‖ ^ 2 + ‖z (1, j)‖ ^ 2) := by
        rw [norm_mul, higham24_exactBinaryTopWeight_norm]
        ring
  have hsquares :
      higham24BinaryEuclideanNorm (t + 1)
          ((higham24BinaryTopStageMatrix t).mulVec z) ^ 2 =
        2 * higham24BinaryEuclideanNorm (t + 1) z ^ 2 := by
    unfold higham24BinaryEuclideanNorm
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    change (∑ p : Fin 2 × Higham24BitIndex t,
        ‖(higham24BinaryTopStageMatrix t).mulVec z p‖ ^ 2) =
      2 * ∑ q : Fin 2 × Higham24BitIndex t, ‖z q‖ ^ 2
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_two,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    exact hpair j
  have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hrhs_sq :
      (Real.sqrt 2 * higham24BinaryEuclideanNorm (t + 1) z) ^ 2 =
        2 * higham24BinaryEuclideanNorm (t + 1) z ^ 2 := by
    rw [mul_pow, hsqrt_sq]
  have hleft_nonneg : 0 ≤ higham24BinaryEuclideanNorm (t + 1)
      ((higham24BinaryTopStageMatrix t).mulVec z) := by
    exact norm_nonneg _
  have hz_nonneg : 0 ≤ higham24BinaryEuclideanNorm (t + 1) z := by
    exact norm_nonneg _
  have hrhs_nonneg :
      0 ≤ Real.sqrt 2 * higham24BinaryEuclideanNorm (t + 1) z :=
    mul_nonneg hsqrt hz_nonneg
  nlinarith [hsquares, hrhs_sq]

/-- Matrix operator norm controls the literal binary Euclidean vector norm. -/
theorem higham24_binaryEuclideanNorm_mulVec_le (t : ℕ)
    (A : Matrix (Higham24BitIndex t) (Higham24BitIndex t) ℂ)
    (z : Higham24BitIndex t → ℂ) :
    higham24BinaryEuclideanNorm t (A.mulVec z) ≤
      ‖A‖ * higham24BinaryEuclideanNorm t z := by
  simpa [higham24BinaryEuclideanNorm] using
    Matrix.l2_opNorm_mulVec A
      (WithLp.toLp (2 : ENNReal) z :
        EuclideanSpace ℂ (Higham24BitIndex t))

/-- Join the two length-`2^t` branches into the recursive binary index. -/
def higham24BinaryJoin {t : ℕ}
    (v : Fin 2 → Higham24BitIndex t → ℂ) :
    Higham24BitIndex (t + 1) → ℂ :=
  fun p => v p.1 p.2

theorem higham24_binaryEuclideanNorm_join_sq {t : ℕ}
    (v : Fin 2 → Higham24BitIndex t → ℂ) :
    higham24BinaryEuclideanNorm (t + 1) (higham24BinaryJoin v) ^ 2 =
      ∑ b : Fin 2, higham24BinaryEuclideanNorm t (v b) ^ 2 := by
  unfold higham24BinaryEuclideanNorm higham24BinaryJoin
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ p : Fin 2 × Higham24BitIndex t, ‖v p.1 p.2‖ ^ 2) =
    ∑ b : Fin 2,
      ‖(WithLp.toLp (2 : ENNReal) (v b) :
        EuclideanSpace ℂ (Higham24BitIndex t))‖ ^ 2
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _hb
  rw [EuclideanSpace.norm_sq_eq]

/-- A common relative bound on the two branches gives the same relative
bound after joining them in Euclidean norm. -/
theorem higham24_binaryEuclideanNorm_join_le
    {t : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (e a : Fin 2 → Higham24BitIndex t → ℂ)
    (hbranch : ∀ b, higham24BinaryEuclideanNorm t (e b) ≤
      r * higham24BinaryEuclideanNorm t (a b)) :
    higham24BinaryEuclideanNorm (t + 1) (higham24BinaryJoin e) ≤
      r * higham24BinaryEuclideanNorm (t + 1) (higham24BinaryJoin a) := by
  have hsq_branch : ∀ b : Fin 2,
      higham24BinaryEuclideanNorm t (e b) ^ 2 ≤
        (r * higham24BinaryEuclideanNorm t (a b)) ^ 2 := by
    intro b
    exact (sq_le_sq₀ (by exact norm_nonneg _)
      (mul_nonneg hr (norm_nonneg _))).mpr (hbranch b)
  have hsum :
      (∑ b : Fin 2, higham24BinaryEuclideanNorm t (e b) ^ 2) ≤
        ∑ b : Fin 2, (r * higham24BinaryEuclideanNorm t (a b)) ^ 2 :=
    Finset.sum_le_sum fun b _hb => hsq_branch b
  have he_sq := higham24_binaryEuclideanNorm_join_sq e
  have ha_sq := higham24_binaryEuclideanNorm_join_sq a
  have hsq :
      higham24BinaryEuclideanNorm (t + 1) (higham24BinaryJoin e) ^ 2 ≤
        (r * higham24BinaryEuclideanNorm (t + 1)
          (higham24BinaryJoin a)) ^ 2 := by
    rw [he_sq, mul_pow, ha_sq]
    calc
      (∑ b : Fin 2, higham24BinaryEuclideanNorm t (e b) ^ 2) ≤
          ∑ b : Fin 2,
            (r * higham24BinaryEuclideanNorm t (a b)) ^ 2 := hsum
      _ = r ^ 2 *
          ∑ b : Fin 2, higham24BinaryEuclideanNorm t (a b) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _hb
        ring
  exact (sq_le_sq₀ (by exact norm_nonneg _)
    (mul_nonneg hr (norm_nonneg _))).mp hsq

theorem higham24_binaryEuclideanNorm_sub_add_le {t : ℕ}
    (x y : Higham24BitIndex t → ℂ) :
    higham24BinaryEuclideanNorm t x ≤
      higham24BinaryEuclideanNorm t (x - y) +
        higham24BinaryEuclideanNorm t y := by
  unfold higham24BinaryEuclideanNorm
  have h := norm_add_le
    (WithLp.toLp (2 : ENNReal) (x - y) :
      EuclideanSpace ℂ (Higham24BitIndex t))
    (WithLp.toLp (2 : ENNReal) y :
      EuclideanSpace ℂ (Higham24BitIndex t))
  have heq :
      (WithLp.toLp (2 : ENNReal) (x - y) :
          EuclideanSpace ℂ (Higham24BitIndex t)) +
        WithLp.toLp (2 : ENNReal) y = WithLp.toLp (2 : ENNReal) x := by
    ext i
    simp
  rw [heq] at h
  exact h

/-- The top radix-2 stage with the actually supplied weight in each output
row, transported to the canonical `Fin (2^(t+1))` indexing used by the local
operator-norm API.  The lower-row sign is already part of that row's Fourier
weight. -/
noncomputable def higham24ComputedTopStageFinMatrix (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ) :
    CMatrix (2 ^ (t + 1)) (2 ^ (t + 1)) :=
  fun p q =>
    let pb := (higham24BitIndexBEEquiv (t + 1)).symm p
    let qb := (higham24BitIndexBEEquiv (t + 1)).symm q
    if pb.2 = qb.2 then
      if qb.1 = 0 then 1 else weight pb
    else 0

/-- Literal rounded application of one top radix-2 stage on canonical `Fin`
coordinates.  This is an actual computation from `fl_complexMul` and
`fl_complexAdd`, not a stage-error certificate. -/
noncomputable def higham24RoundedTopStageFinApply (fp : FPModel) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : CVec (2 ^ (t + 1))) : CVec (2 ^ (t + 1)) :=
  fun p =>
    let pb := (higham24BitIndexBEEquiv (t + 1)).symm p
    fl_complexAdd fp
      (z (higham24BitIndexBEEquiv (t + 1) (0, pb.2)))
      (fl_complexMul fp (weight pb)
        (z (higham24BitIndexBEEquiv (t + 1) (1, pb.2))))

/-- A literal rounded top stage is exactly a computed-weight matrix plus an
arithmetic perturbation whose entries satisfy the source componentwise
`γ₄ |Ã|` estimate.  Both the perturbation matrix and all of its coefficients
are produced from the primitive floating-point operations. -/
theorem higham24_roundedTopStage_exists_perturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : CVec (2 ^ (t + 1))) :
    ∃ E : CMatrix (2 ^ (t + 1)) (2 ^ (t + 1)),
      (∀ p q, ‖E p q‖ ≤ gamma fp 4 *
        ‖higham24ComputedTopStageFinMatrix t weight p q‖) ∧
      higham24RoundedTopStageFinApply fp t weight z =
        complexMatrixVecMul
          (higham24ComputedTopStageFinMatrix t weight + E) z := by
  let e := higham24BitIndexBEEquiv (t + 1)
  choose deltaA deltaB hdeltaA hdeltaB hrounded using
    fun p : Fin (2 ^ (t + 1)) =>
      higham24_roundedButterfly_exists_relative_coefficients
        fp hgamma4
        (z (e (0, (e.symm p).2)))
        (weight (e.symm p))
        (z (e (1, (e.symm p).2)))
  let E : CMatrix (2 ^ (t + 1)) (2 ^ (t + 1)) := fun p q =>
    let pb := e.symm p
    let qb := e.symm q
    if pb.2 = qb.2 then
      if qb.1 = 0 then deltaA p else weight pb * deltaB p
    else 0
  refine ⟨E, ?_, ?_⟩
  · intro p q
    let pb := e.symm p
    let qb := e.symm q
    by_cases hj : pb.2 = qb.2
    · by_cases hb : qb.1 = 0
      · simpa [E, higham24ComputedTopStageFinMatrix, e, pb, qb, hj, hb,
          gamma_nonneg fp hgamma4] using hdeltaA p
      · have hmul : ‖weight pb * deltaB p‖ ≤
            gamma fp 4 * ‖weight pb‖ := by
          rw [norm_mul]
          calc
            ‖weight pb‖ * ‖deltaB p‖
                ≤ ‖weight pb‖ * gamma fp 4 :=
                  mul_le_mul_of_nonneg_left (hdeltaB p) (norm_nonneg _)
            _ = gamma fp 4 * ‖weight pb‖ := by ring
        simpa [E, higham24ComputedTopStageFinMatrix, e, pb, qb, hj, hb]
          using hmul
    · simp [E, higham24ComputedTopStageFinMatrix, e, pb, qb, hj]
  · funext p
    let pb := e.symm p
    have hsum :
        (∑ q : Fin (2 ^ (t + 1)),
          (higham24ComputedTopStageFinMatrix t weight + E) p q * z q) =
        ∑ qb : Higham24BitIndex (t + 1),
          (higham24ComputedTopStageFinMatrix t weight + E) p (e qb) * z (e qb) := by
      exact (Fintype.sum_equiv e
        (fun qb : Higham24BitIndex (t + 1) =>
          (higham24ComputedTopStageFinMatrix t weight + E) p (e qb) * z (e qb))
        (fun q : Fin (2 ^ (t + 1)) =>
          (higham24ComputedTopStageFinMatrix t weight + E) p q * z q)
        (fun _ => rfl)).symm
    change fl_complexAdd fp (z (e (0, pb.2)))
        (fl_complexMul fp (weight pb) (z (e (1, pb.2)))) = _
    unfold complexMatrixVecMul
    rw [hsum]
    change _ = ∑ qb : Fin 2 × Higham24BitIndex t,
      (higham24ComputedTopStageFinMatrix t weight + E) p (e qb) * z (e qb)
    have hrow (b : Fin 2) :
        (∑ j : Higham24BitIndex t,
          (higham24ComputedTopStageFinMatrix t weight + E) p (e (b, j)) *
            z (e (b, j))) =
          (higham24ComputedTopStageFinMatrix t weight + E) p (e (b, pb.2)) *
            z (e (b, pb.2)) := by
      apply Finset.sum_eq_single pb.2
      · intro j _hj hne
        simp [higham24ComputedTopStageFinMatrix, E, e, pb, Ne.symm hne]
      · simp
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [hrow 0, hrow 1]
    simp [higham24ComputedTopStageFinMatrix, E, e, pb]
    rw [hrounded p]
    ring

/-- Operator-norm form of the literal top-stage producer.  The only
hypothesis is validity of `γ₄`; the matrix perturbation itself comes from the
rounded operations in `higham24RoundedTopStageFinApply`. -/
theorem higham24_roundedTopStage_exists_op2_perturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4) (t : ℕ)
    (weight : Higham24BitIndex (t + 1) → ℂ)
    (z : CVec (2 ^ (t + 1))) :
    ∃ E : CMatrix (2 ^ (t + 1)) (2 ^ (t + 1)),
      higham24RoundedTopStageFinApply fp t weight z =
        complexMatrixVecMul
          (higham24ComputedTopStageFinMatrix t weight + E) z ∧
      complexMatrixOp2 E ≤ gamma fp 4 *
        complexMatrixOp2
          (complexAbsMatrix (higham24ComputedTopStageFinMatrix t weight)) := by
  rcases higham24_roundedTopStage_exists_perturbation
      fp hgamma4 t weight z with ⟨E, hentry, happly⟩
  refine ⟨E, happly, ?_⟩
  exact higham24_op2_le_scaled_abs_of_entrywise
    (by positivity) (higham24ComputedTopStageFinMatrix t weight) E
    (gamma fp 4) (gamma_nonneg fp hgamma4) hentry

/-- Canonical Euclidean norm on binary-index vectors, transported to the
repository's `Fin`-indexed complex `L²` norm. -/
noncomputable def higham24BinaryVecNorm2 (t : ℕ)
    (x : Higham24BitIndex t → ℂ) : ℝ :=
  complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
    (fun i => x ((higham24BitIndexBEEquiv t).symm i))

/-- The source-facing transported norm is exactly the Euclidean norm on the
literal binary index type. -/
theorem higham24_binaryVecNorm2_eq_euclideanNorm (t : ℕ)
    (x : Higham24BitIndex t → ℂ) :
    higham24BinaryVecNorm2 t x = higham24BinaryEuclideanNorm t x := by
  unfold higham24BinaryVecNorm2 higham24BinaryEuclideanNorm
  rw [complexVecLpNorm_two_eq_toLp]
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  let e := higham24BitIndexBEEquiv t
  exact (Fintype.sum_equiv e
    (fun i : Higham24BitIndex t => ‖x i‖ ^ 2)
    (fun j : Fin (2 ^ t) => ‖x (e.symm j)‖ ^ 2)
    (fun i => by simp [e])).symm

/-- End-to-end absolute forward-error bound for the literal rounded radix-2
executor.  Every recursive branch uses the same produced one-stage
perturbation theorem; no trace or final-error identity is assumed. -/
theorem higham24_roundedRadix2FFT_euclidean_forward_bound
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu) :
    ∀ t (x : Higham24BitIndex t → ℂ),
      higham24BinaryEuclideanNorm t
          (higham24RoundedRadix2FFT fp weight t x -
            higham24Radix2FFT t x) ≤
        ((1 + higham24Eta mu (gamma fp 4)) ^ t - 1) *
          higham24BinaryEuclideanNorm t (higham24Radix2FFT t x) := by
  let eta := higham24Eta mu (gamma fp 4)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    unfold higham24Eta
    exact add_nonneg hmu
      (mul_nonneg (gamma_nonneg fp hgamma4)
        (add_nonneg (Real.sqrt_nonneg _) hmu))
  intro t
  induction t with
  | zero =>
      intro x
      simp [higham24RoundedRadix2FFT, higham24Radix2FFT,
        higham24BinaryEuclideanNorm]
  | succ t ih =>
      intro x
      let exactBranch : Fin 2 → Higham24BitIndex t → ℂ := fun b =>
        higham24Radix2FFT t (fun j => x (b, j))
      let roundedBranch : Fin 2 → Higham24BitIndex t → ℂ := fun b =>
        higham24RoundedRadix2FFT fp weight t (fun j => x (b, j))
      let z : Higham24BitIndex (t + 1) → ℂ :=
        higham24BinaryJoin exactBranch
      let zhat : Higham24BitIndex (t + 1) → ℂ :=
        higham24BinaryJoin roundedBranch
      let branchError : Fin 2 → Higham24BitIndex t → ℂ := fun b =>
        roundedBranch b - exactBranch b
      let r : ℝ := (1 + eta) ^ t - 1
      have hr : 0 ≤ r := by
        dsimp [r]
        exact sub_nonneg.mpr (one_le_pow₀ (by linarith))
      have hbranch : ∀ b : Fin 2,
          higham24BinaryEuclideanNorm t (branchError b) ≤
            r * higham24BinaryEuclideanNorm t (exactBranch b) := by
        intro b
        simpa [branchError, roundedBranch, exactBranch, r, eta] using
          ih (fun j => x (b, j))
      have hjoin0 := higham24_binaryEuclideanNorm_join_le
        r hr branchError exactBranch hbranch
      have hjoinEq : higham24BinaryJoin branchError = zhat - z := by
        funext p
        rfl
      have hjoin : higham24BinaryEuclideanNorm (t + 1) (zhat - z) ≤
          r * higham24BinaryEuclideanNorm (t + 1) z := by
        rw [← hjoinEq]
        exact hjoin0
      have hzhat : higham24BinaryEuclideanNorm (t + 1) zhat ≤
          (1 + r) * higham24BinaryEuclideanNorm (t + 1) z := by
        calc
          higham24BinaryEuclideanNorm (t + 1) zhat ≤
              higham24BinaryEuclideanNorm (t + 1) (zhat - z) +
                higham24BinaryEuclideanNorm (t + 1) z :=
            higham24_binaryEuclideanNorm_sub_add_le zhat z
          _ ≤ r * higham24BinaryEuclideanNorm (t + 1) z +
                higham24BinaryEuclideanNorm (t + 1) z :=
            add_le_add hjoin le_rfl
          _ = (1 + r) * higham24BinaryEuclideanNorm (t + 1) z := by ring
      have hwtop : ∀ p : Higham24BitIndex (t + 1),
          Higham24WeightApproximation
            (higham24ExactBinaryTopWeight t p) (weight (t + 1) p) mu := by
        intro p
        simpa [higham24ExactBinaryTopWeight] using hw (t + 1) p
      rcases higham24_roundedBinaryTopStage_exists_total_op2_bound
          fp hgamma4 t (weight (t + 1)) zhat mu hmu hwtop with
        ⟨Delta, hroundedStage, hDelta⟩
      have hrounded :
          higham24RoundedRadix2FFT fp weight (t + 1) x =
            higham24RoundedBinaryTopStageApply fp t (weight (t + 1)) zhat := by
        funext p
        rfl
      have hexact :
          higham24Radix2FFT (t + 1) x =
            (higham24BinaryTopStageMatrix t).mulVec z := by
        funext p
        rw [higham24_binaryTopStage_mulVec]
        rfl
      have herr :
          higham24RoundedRadix2FFT fp weight (t + 1) x -
              higham24Radix2FFT (t + 1) x =
            (higham24BinaryTopStageMatrix t).mulVec (zhat - z) +
              Delta.mulVec zhat := by
        rw [hrounded, hroundedStage, hexact, Matrix.add_mulVec,
          Matrix.mulVec_sub]
        ext p
        simp
        ring
      have htri :
          higham24BinaryEuclideanNorm (t + 1)
              ((higham24BinaryTopStageMatrix t).mulVec (zhat - z) +
                Delta.mulVec zhat) ≤
            higham24BinaryEuclideanNorm (t + 1)
                ((higham24BinaryTopStageMatrix t).mulVec (zhat - z)) +
              higham24BinaryEuclideanNorm (t + 1) (Delta.mulVec zhat) := by
        unfold higham24BinaryEuclideanNorm
        simpa using norm_add_le
          (WithLp.toLp (2 : ENNReal)
            ((higham24BinaryTopStageMatrix t).mulVec (zhat - z)) :
              EuclideanSpace ℂ (Higham24BitIndex (t + 1)))
          (WithLp.toLp (2 : ENNReal) (Delta.mulVec zhat) :
              EuclideanSpace ℂ (Higham24BitIndex (t + 1)))
      have hDeltaAction :
          higham24BinaryEuclideanNorm (t + 1) (Delta.mulVec zhat) ≤
            (eta * Real.sqrt 2) *
              ((1 + r) * higham24BinaryEuclideanNorm (t + 1) z) := by
        calc
          higham24BinaryEuclideanNorm (t + 1) (Delta.mulVec zhat) ≤
              ‖Delta‖ * higham24BinaryEuclideanNorm (t + 1) zhat :=
            higham24_binaryEuclideanNorm_mulVec_le (t + 1) Delta zhat
          _ ≤ (eta * Real.sqrt 2) *
              ((1 + r) * higham24BinaryEuclideanNorm (t + 1) z) := by
            calc
              ‖Delta‖ * higham24BinaryEuclideanNorm (t + 1) zhat ≤
                  (eta * Real.sqrt 2) *
                    higham24BinaryEuclideanNorm (t + 1) zhat :=
                mul_le_mul_of_nonneg_right (by simpa [eta] using hDelta)
                  (norm_nonneg _)
              _ ≤ (eta * Real.sqrt 2) *
                  ((1 + r) * higham24BinaryEuclideanNorm (t + 1) z) :=
                mul_le_mul_of_nonneg_left hzhat
                  (mul_nonneg heta (Real.sqrt_nonneg _))
      have herror :
          higham24BinaryEuclideanNorm (t + 1)
              (higham24RoundedRadix2FFT fp weight (t + 1) x -
                higham24Radix2FFT (t + 1) x) ≤
            Real.sqrt 2 *
                (r * higham24BinaryEuclideanNorm (t + 1) z) +
              (eta * Real.sqrt 2) *
                ((1 + r) * higham24BinaryEuclideanNorm (t + 1) z) := by
        rw [herr]
        calc
          higham24BinaryEuclideanNorm (t + 1)
              ((higham24BinaryTopStageMatrix t).mulVec (zhat - z) +
                Delta.mulVec zhat) ≤
              higham24BinaryEuclideanNorm (t + 1)
                  ((higham24BinaryTopStageMatrix t).mulVec (zhat - z)) +
                higham24BinaryEuclideanNorm (t + 1) (Delta.mulVec zhat) := htri
          _ = Real.sqrt 2 *
                higham24BinaryEuclideanNorm (t + 1) (zhat - z) +
              higham24BinaryEuclideanNorm (t + 1) (Delta.mulVec zhat) := by
            rw [higham24_binaryTopStage_euclideanNorm]
          _ ≤ Real.sqrt 2 *
                (r * higham24BinaryEuclideanNorm (t + 1) z) +
              (eta * Real.sqrt 2) *
                ((1 + r) * higham24BinaryEuclideanNorm (t + 1) z) :=
            add_le_add
              (mul_le_mul_of_nonneg_left hjoin (Real.sqrt_nonneg _))
              hDeltaAction
      have hexactNorm :
          higham24BinaryEuclideanNorm (t + 1)
              (higham24Radix2FFT (t + 1) x) =
            Real.sqrt 2 * higham24BinaryEuclideanNorm (t + 1) z := by
        rw [hexact, higham24_binaryTopStage_euclideanNorm]
      have hrnext :
          (1 + eta) ^ (t + 1) - 1 = (1 + eta) * r + eta := by
        dsimp [r]
        rw [pow_succ']
        ring
      calc
        higham24BinaryEuclideanNorm (t + 1)
            (higham24RoundedRadix2FFT fp weight (t + 1) x -
              higham24Radix2FFT (t + 1) x) ≤
            Real.sqrt 2 *
                (r * higham24BinaryEuclideanNorm (t + 1) z) +
              (eta * Real.sqrt 2) *
                ((1 + r) * higham24BinaryEuclideanNorm (t + 1) z) := herror
        _ = ((1 + eta) * r + eta) *
            (Real.sqrt 2 * higham24BinaryEuclideanNorm (t + 1) z) := by ring
        _ = ((1 + eta) ^ (t + 1) - 1) *
            higham24BinaryEuclideanNorm (t + 1)
              (higham24Radix2FFT (t + 1) x) := by
          rw [hrnext, hexactNorm]

/-- Literal source-facing Theorem 24.2.  The relative bound is derived from
the rounded executor itself; the zero exact-output case is handled by Lean's
total division, and the positive case divides the proved absolute bound. -/
theorem higham24_theorem24_2_literal
    (fp : FPModel) (hgamma4 : gammaValid fp 4)
    (weight : ∀ s, Higham24BitIndex s → ℂ)
    (mu : ℝ) (hmu : 0 ≤ mu)
    (hw : ∀ s (p : Higham24BitIndex s),
      Higham24WeightApproximation
        (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
        (weight s p) mu)
    (t : ℕ) (x : Higham24BitIndex t → ℂ)
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1) :
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x) ≤
        higham24RelativeFFTBound t (higham24Eta mu (gamma fp 4)) := by
  let eta := higham24Eta mu (gamma fp 4)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    unfold higham24Eta
    exact add_nonneg hmu
      (mul_nonneg (gamma_nonneg fp hgamma4)
        (add_nonneg (Real.sqrt_nonneg _) hmu))
  have habs := higham24_roundedRadix2FFT_euclidean_forward_bound
    fp hgamma4 weight mu hmu hw t x
  have hrnonneg : 0 ≤ (1 + eta) ^ t - 1 :=
    sub_nonneg.mpr (one_le_pow₀ (by linarith))
  rw [higham24_binaryVecNorm2_eq_euclideanNorm,
    higham24_binaryVecNorm2_eq_euclideanNorm]
  have hratio :
      higham24BinaryEuclideanNorm t
          (higham24RoundedRadix2FFT fp weight t x -
            higham24Radix2FFT t x) /
        higham24BinaryEuclideanNorm t (higham24Radix2FFT t x) ≤
      (1 + eta) ^ t - 1 := by
    by_cases hz : higham24BinaryEuclideanNorm t
        (higham24Radix2FFT t x) = 0
    · simp [hz, hrnonneg]
    · have hpos : 0 < higham24BinaryEuclideanNorm t
          (higham24Radix2FFT t x) :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      apply (div_le_iff₀ hpos).2
      simpa [eta] using habs
  exact hratio.trans
    (higham24_eq24_5_product_bound t eta heta hvalid)

/-- An honest explicit execution domain for the product argument in (24.5).
It records exact and computed intermediate states and only a stage-local
normalized error inequality; the final theorem is not a field of the
contract. -/
structure Higham24ExplicitStageExecution
    {V : Type*} [NormedAddCommGroup V]
    (t : ℕ) (eta : ℝ) where
  exactState : ℕ → V
  computedState : ℕ → V
  referenceNorm : ℝ
  referenceNorm_pos : 0 < referenceNorm
  initial : computedState 0 = exactState 0
  step_bound : ∀ k, k < t →
    ‖computedState (k + 1) - exactState (k + 1)‖ / referenceNorm ≤
      (1 + eta) *
        (‖computedState k - exactState k‖ / referenceNorm) + eta

/-- The explicit execution domain is nonvacuous: an exact sequence is a
computed sequence with zero stage error for every nonnegative `eta`. -/
def higham24ExactStageExecution
    {V : Type*} [NormedAddCommGroup V]
    (t : ℕ) (eta : ℝ) (heta : 0 ≤ eta) (state : ℕ → V)
    (referenceNorm : ℝ) (href : 0 < referenceNorm) :
    Higham24ExplicitStageExecution (V := V) t eta where
  exactState := state
  computedState := state
  referenceNorm := referenceNorm
  referenceNorm_pos := href
  initial := rfl
  step_bound := by
    intro k hk
    simp [heta]

/-- Theorem 24.2/(24.5) on the strongest honest explicit stage domain: local
rounded-stage estimates accumulate to the printed relative product bound. -/
theorem higham24_theorem24_2_explicitDomain
    {V : Type*} [NormedAddCommGroup V]
    {t : ℕ} {eta : ℝ} (heta : 0 ≤ eta)
    (hvalid : (t : ℝ) * eta < 1)
    (execution : Higham24ExplicitStageExecution (V := V) t eta) :
    ‖execution.computedState t - execution.exactState t‖ /
        execution.referenceNorm ≤ higham24RelativeFFTBound t eta := by
  let relativeError : ℕ → ℝ := fun k =>
    ‖execution.computedState k - execution.exactState k‖ /
      execution.referenceNorm
  have hzero : relativeError 0 = 0 := by
    simp [relativeError, execution.initial]
  have hbound : ∀ k, k ≤ t → relativeError k ≤ (1 + eta) ^ k - 1 := by
    intro k hk
    induction k with
    | zero => simp [hzero]
    | succ k ih =>
        have hkt : k < t := Nat.lt_of_succ_le hk
        have hrec : relativeError (k + 1) ≤
            (1 + eta) * relativeError k + eta := by
          simpa [relativeError] using execution.step_bound k hkt
        have hone : 0 ≤ 1 + eta := add_nonneg zero_le_one heta
        have hmul := mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkt)) hone
        calc
          relativeError (k + 1) ≤ (1 + eta) * relativeError k + eta := hrec
          _ ≤ (1 + eta) * ((1 + eta) ^ k - 1) + eta :=
            add_le_add hmul le_rfl
          _ = (1 + eta) ^ (k + 1) - 1 := by rw [pow_succ']; ring
  exact le_trans (hbound t le_rfl)
    (higham24_eq24_5_product_bound t eta heta hvalid)

/-- Runtime error trace for the literal rounded recursion.  The `step` field is
the precise stage-local obligation produced by the weight and complex
arithmetic analysis in the printed proof.  It is deliberately local, rather
than assuming the final theorem conclusion. -/
structure Higham24Radix2ForwardErrorTrace (fp : FPModel)
    (weight : ∀ t, Higham24BitIndex t → ℂ) (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (eta : ℝ) where
  relativeError : ℕ → ℝ
  initial : relativeError 0 = 0
  step : ∀ k, k < t →
    relativeError (k + 1) ≤ (1 + eta) * relativeError k + eta
  final : relativeError t =
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x)

/-- Source-shaped certificate for Theorem 24.2.  Besides the local error
trace, it records the computed-weight model (24.2), nonnegativity of `μ`, and
the validity condition needed for `γ₄`.  Thus the source-facing theorem below
does not hide these assumptions behind the final error conclusion. -/
structure Higham24SourceRadix2ForwardErrorTrace (fp : FPModel)
    (weight : ∀ t, Higham24BitIndex t → ℂ) (t : ℕ)
    (x : Higham24BitIndex t → ℂ) (mu : ℝ) extends
    Higham24Radix2ForwardErrorTrace fp weight t x
      (higham24Eta mu (gamma fp 4)) where
  mu_nonneg : 0 ≤ mu
  gamma4_valid : gammaValid fp 4
  weight_error : ∀ s (p : Higham24BitIndex s), s ≤ t →
    Higham24WeightApproximation
      (higham24FourierRoot (2 ^ s) ^ higham24BitIndexBEValue s p)
      (weight s p) mu

theorem higham24_errorTrace_le_one_add_pow_sub_one
    {fp : FPModel} {weight : ∀ t, Higham24BitIndex t → ℂ}
    {t : ℕ} {x : Higham24BitIndex t → ℂ} {eta : ℝ}
    (heta : 0 ≤ eta)
    (trace : Higham24Radix2ForwardErrorTrace fp weight t x eta) :
    trace.relativeError t ≤ (1 + eta) ^ t - 1 := by
  have hbound : ∀ k, k ≤ t →
      trace.relativeError k ≤ (1 + eta) ^ k - 1 := by
    intro k hk
    induction k with
    | zero => simp [trace.initial]
    | succ k ih =>
        have hkt : k < t := Nat.lt_of_succ_le hk
        have hrec := trace.step k hkt
        have hone : 0 ≤ 1 + eta := add_nonneg zero_le_one heta
        have hmul := mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hkt)) hone
        calc
          trace.relativeError (k + 1) ≤
              (1 + eta) * trace.relativeError k + eta := hrec
          _ ≤ (1 + eta) * ((1 + eta) ^ k - 1) + eta :=
            add_le_add hmul le_rfl
          _ = (1 + eta) ^ (k + 1) - 1 := by rw [pow_succ']; ring
  exact hbound t le_rfl

/-- Conditional error-bound assembly for the literal rounded radix-2 executor,
under a visible stage-local trace certificate.  This lemma does not produce
that certificate from the floating operations. -/
theorem higham24_theorem24_2_of_errorTrace
    {fp : FPModel} {weight : ∀ t, Higham24BitIndex t → ℂ}
    {t : ℕ} {x : Higham24BitIndex t → ℂ} {eta : ℝ}
    (heta : 0 ≤ eta) (hvalid : (t : ℝ) * eta < 1)
    (trace : Higham24Radix2ForwardErrorTrace fp weight t x eta) :
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x) ≤
        higham24RelativeFFTBound t eta := by
  rw [← trace.final]
  exact le_trans (higham24_errorTrace_le_one_add_pow_sub_one heta trace)
    (higham24_eq24_5_product_bound t eta heta hvalid)

/-- Conditional assembly specialized to the Theorem 24.2 coefficient
`η = μ + γ₄(√2 + μ)` printed in the chapter.  Its explicit source trace remains
an implementation-specific input rather than a derived result. -/
theorem higham24_theorem24_2_of_sourceTrace
    {fp : FPModel} {weight : ∀ t, Higham24BitIndex t → ℂ}
    {t : ℕ} {x : Higham24BitIndex t → ℂ} {mu : ℝ}
    (hvalid : (t : ℝ) * higham24Eta mu (gamma fp 4) < 1)
    (trace : Higham24SourceRadix2ForwardErrorTrace fp weight t x mu) :
    higham24BinaryVecNorm2 t
        (higham24RoundedRadix2FFT fp weight t x - higham24Radix2FFT t x) /
      higham24BinaryVecNorm2 t (higham24Radix2FFT t x) ≤
        higham24RelativeFFTBound t (higham24Eta mu (gamma fp 4)) := by
  have heta : 0 ≤ higham24Eta mu (gamma fp 4) := by
    unfold higham24Eta
    exact add_nonneg trace.mu_nonneg
      (mul_nonneg (gamma_nonneg fp trace.gamma4_valid)
        (add_nonneg (Real.sqrt_nonneg _) trace.mu_nonneg))
  exact higham24_theorem24_2_of_errorTrace heta hvalid
    trace.toHigham24Radix2ForwardErrorTrace

end NumStability
