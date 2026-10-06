-- Analysis/MatrixNorms/Comparisons.lean
--
-- Quantitative comparisons among standard finite matrix norms.

import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Realification

/-!
# Matrix-norm comparisons

Collects dimension-, rank-, and singular-value-sensitive inequalities between
Frobenius, operator, entrywise, and induced matrix norms.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Rank-sensitive squared Frobenius/operator-2 comparison:
    `||A||_F^2 <= rank(A) * ||A||_2^2`. -/
theorem complexMatrixFrobeniusSq_le_rank_mul_complexMatrixOp2_sq {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobeniusSq A ≤
      (complexMatrixRank A : ℝ) * complexMatrixOp2 A ^ 2 := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq]
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun i => complexMatrixSingularValue A i ≠ 0)
  have hsum_support :
      (∑ i : Fin n, complexMatrixSingularValue A i ^ 2) =
        ∑ i ∈ s, complexMatrixSingularValue A i ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun i => complexMatrixSingularValue A i ≠ 0)
      (f := fun i => complexMatrixSingularValue A i ^ 2)]
    have hzero :
        ∑ i ∈ Finset.univ.filter
            (fun i => complexMatrixSingularValue A i = 0),
          complexMatrixSingularValue A i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp at hi
      simp [hi]
    simp [s, hzero]
  calc
    (∑ i : Fin n, complexMatrixSingularValue A i ^ 2)
        = ∑ i ∈ s, complexMatrixSingularValue A i ^ 2 := hsum_support
    _ ≤ ∑ _i ∈ s, complexMatrixOp2 A ^ 2 := by
          apply Finset.sum_le_sum
          intro i _hi
          exact (sq_le_sq₀ (complexMatrixSingularValue_nonneg A i)
            (complexMatrixOp2_nonneg A)).mpr
            (complexMatrixSingularValue_le_complexMatrixOp2 A i)
    _ = (s.card : ℝ) * complexMatrixOp2 A ^ 2 := by
          simp [nsmul_eq_mul]
    _ = (complexMatrixRank A : ℝ) * complexMatrixOp2 A ^ 2 := by
          have hcard_s : s.card = complexMatrixRank A := by
            calc
              s.card =
                  Fintype.card {i : Fin n // complexMatrixSingularValue A i ≠ 0} := by
                    simp [s, Fintype.card_subtype]
              _ = complexMatrixRank A :=
                    (complexMatrixRank_eq_card_nonzero_singularValue A).symm
          rw [hcard_s]

/-- Rank-sensitive Frobenius/operator-2 comparison:
    `||A||_F <= sqrt(rank(A)) * ||A||_2`. -/
theorem complexMatrixFrobenius_le_sqrt_rank_mul_complexMatrixOp2 {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixFrobenius A ≤
      Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A := by
  have hsq :
      complexMatrixFrobenius A ^ 2 ≤
        (Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A) ^ 2 := by
    rw [complexMatrixFrobenius_sq]
    calc
      complexMatrixFrobeniusSq A
          ≤ (complexMatrixRank A : ℝ) * complexMatrixOp2 A ^ 2 :=
            complexMatrixFrobeniusSq_le_rank_mul_complexMatrixOp2_sq A
      _ = (Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  exact (sq_le_sq₀ (complexMatrixFrobenius_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg A))).mp hsq

/-- Table 6.2 `S` versus `2` rank-sensitive entry, in product-square-root
    form: `||A||_S <= sqrt(mn) * sqrt(rank A) * ||A||_2`. -/
theorem complexMatrixEntrywiseSumNorm_le_sqrt_card_mul_sqrt_rank_mul_op2 {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixEntrywiseSumNorm A ≤
      Real.sqrt ((m * n : ℕ) : ℝ) *
        (Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A) := by
  have hS := complexMatrixEntrywiseSumNorm_le_sqrt_card_mul_frobenius A
  have hF := complexMatrixFrobenius_le_sqrt_rank_mul_complexMatrixOp2 A
  exact hS.trans
    (mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg _))

/-- Table 6.2 `S` versus `2` rank-sensitive entry in the printed
    single-square-root form. -/
theorem complexMatrixEntrywiseSumNorm_le_sqrt_card_rank_mul_op2 {m n : ℕ}
    (A : CMatrix m n) :
    complexMatrixEntrywiseSumNorm A ≤
      Real.sqrt (((m * n : ℕ) : ℝ) * (complexMatrixRank A : ℝ)) *
        complexMatrixOp2 A := by
  have h := complexMatrixEntrywiseSumNorm_le_sqrt_card_mul_sqrt_rank_mul_op2 A
  calc
    complexMatrixEntrywiseSumNorm A ≤
        Real.sqrt ((m * n : ℕ) : ℝ) *
          (Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A) := h
    _ = (Real.sqrt ((m * n : ℕ) : ℝ) *
          Real.sqrt (complexMatrixRank A : ℝ)) * complexMatrixOp2 A := by ring
    _ = Real.sqrt (((m * n : ℕ) : ℝ) * (complexMatrixRank A : ℝ)) *
          complexMatrixOp2 A := by
        rw [← Real.sqrt_mul (Nat.cast_nonneg ((m * n : ℕ)))]

/-- All entries have the same absolute value. This is the first equality
    condition in the Cauchy-Schwarz step for the rank-sensitive `S/2` Table
    6.2 bound. -/
def ComplexMatrixFlatEntryNorm {m n : Nat} (A : CMatrix m n) : Prop :=
  ∃ rho : Real, 0 ≤ rho ∧ ∀ i j, ‖A i j‖ = rho

/-- Every nonzero local singular value is equal to the operator `2`-norm.
    This is the second equality condition in the Frobenius/operator-rank step
    for the rank-sensitive `S/2` Table 6.2 bound. -/
def ComplexMatrixPositiveSingularValuesEqualOp2 {m n : Nat} (A : CMatrix m n) :
    Prop :=
  ∀ i : Fin n, complexMatrixSingularValue A i ≠ 0 →
    complexMatrixSingularValue A i = complexMatrixOp2 A

/-- Mean of a finite real family, used to package the equality case of the
    finite Cauchy-Schwarz inequality. -/
noncomputable def finiteRealMean {α : Type*} [Fintype α] (x : α → Real) : Real :=
  (Finset.sum Finset.univ x) / (Fintype.card α : Real)

/-- Variance identity around the finite mean. -/
theorem sum_sq_sub_finiteRealMean_eq {α : Type*} [Fintype α]
    (x : α → Real) (hN : Ne (Fintype.card α : Real) 0) :
    Finset.sum Finset.univ (fun i => (x i - finiteRealMean x) ^ 2) =
      Finset.sum Finset.univ (fun i => x i ^ 2) -
        (Finset.sum Finset.univ x) ^ 2 / (Fintype.card α : Real) := by
  unfold finiteRealMean
  set S : Real := Finset.sum Finset.univ x with hS
  calc
    Finset.sum Finset.univ (fun i => (x i - S / (Fintype.card α : Real)) ^ 2)
        = Finset.sum Finset.univ
            (fun i => x i ^ 2 - 2 * (S / (Fintype.card α : Real)) * x i +
              (S / (Fintype.card α : Real)) ^ 2) := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = Finset.sum Finset.univ (fun i => x i ^ 2) -
          2 * (S / (Fintype.card α : Real)) * S +
          (Fintype.card α : Real) * (S / (Fintype.card α : Real)) ^ 2 := by
            simp [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
              Finset.sum_const, hS, nsmul_eq_mul]
    _ = Finset.sum Finset.univ (fun i => x i ^ 2) - S ^ 2 / (Fintype.card α : Real) := by
            field_simp [hN]
            ring
    _ = Finset.sum Finset.univ (fun i => x i ^ 2) -
          (Finset.sum Finset.univ x) ^ 2 / (Fintype.card α : Real) := by
            rw [hS]

/-- Equality in the finite real Cauchy-Schwarz estimate forces all entries to
    equal the finite mean. -/
theorem forall_eq_finiteRealMean_of_sum_sq_eq_card_mul_sum_sq {α : Type*}
    [Fintype α] [Nonempty α] (x : α → Real)
    (h : (Finset.sum Finset.univ x) ^ 2 =
      (Fintype.card α : Real) * Finset.sum Finset.univ (fun i => x i ^ 2)) :
    ∀ i : α, x i = finiteRealMean x := by
  have hN_nat : Ne (Fintype.card α) 0 := Fintype.card_ne_zero
  have hN : Ne (Fintype.card α : Real) 0 := by
    exact_mod_cast hN_nat
  have hvar : Finset.sum Finset.univ (fun i => (x i - finiteRealMean x) ^ 2) = 0 := by
    rw [sum_sq_sub_finiteRealMean_eq x hN]
    rw [h]
    field_simp [hN]
    ring
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
    (f := fun i => (x i - finiteRealMean x) ^ 2)
    (by intro i _hi; exact sq_nonneg (x i - finiteRealMean x))).mp hvar
  intro i
  have hi : (x i - finiteRealMean x) ^ 2 = 0 := hterms i (Finset.mem_univ i)
  have hdiff : x i - finiteRealMean x = 0 := sq_eq_zero_iff.mp hi
  exact sub_eq_zero.mp hdiff

/-- If every term in a finite real sum is bounded above by a constant and the
    sum attains the cardinality times that constant, every term attains it. -/
theorem finset_forall_eq_const_of_sum_eq_card_mul_of_le {α : Type*}
    (s : Finset α) (f : α → Real) (c : Real)
    (hle : ∀ i, i ∈ s → f i ≤ c)
    (h : Finset.sum s f = (s.card : Real) * c) :
    ∀ i, i ∈ s → f i = c := by
  have hsum_zero : Finset.sum s (fun i => c - f i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, h]
    simp [nsmul_eq_mul]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (s := s)
    (f := fun i => c - f i)
    (by
      intro i hi
      exact sub_nonneg.mpr (hle i hi))).mp hsum_zero
  intro i hi
  have hzero : c - f i = 0 := hterms i hi
  linarith

/-- Higham Problem 6.9, lower equality case in singular-value form:
    all singular values except the largest one are zero. -/
def ComplexMatrixOnlyTopSingularValuePossiblyNonzero {m n : Nat}
    (hn : 0 < n) (A : CMatrix m n) : Prop :=
  ∀ i : Fin n, i ≠ ⟨0, hn⟩ → complexMatrixSingularValue A i = 0

/-- Higham Problem 6.9, upper equality case in singular-value form:
    every singular value equals the largest/operator-2 value. -/
def ComplexMatrixAllSingularValuesEqualOp2 {m n : Nat}
    (A : CMatrix m n) : Prop :=
  ∀ i : Fin n, complexMatrixSingularValue A i = complexMatrixOp2 A

/-- If only the largest singular value can be nonzero, then the Frobenius square
    equals the squared operator `2`-norm. -/
theorem complexMatrixFrobeniusSq_eq_op2_sq_of_onlyTopSingularValue
    {m n : Nat} (hn : 0 < n) (A : CMatrix m n)
    (honly : ComplexMatrixOnlyTopSingularValuePossiblyNonzero hn A) :
    complexMatrixFrobeniusSq A = complexMatrixOp2 A ^ 2 := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq]
  rw [Finset.sum_eq_single (⟨0, hn⟩ : Fin n)]
  · rw [← complexMatrixOp2_eq_top_singularValue hn A]
  · intro i _hi hi_ne
    simp [honly i hi_ne]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

/-- Conversely, equality in the lower Problem 6.9 bound forces all non-top
    singular values to be zero. -/
theorem complexMatrixOnlyTopSingularValuePossiblyNonzero_of_frobeniusSq_eq_op2_sq
    {m n : Nat} (hn : 0 < n) (A : CMatrix m n)
    (h : complexMatrixFrobeniusSq A = complexMatrixOp2 A ^ 2) :
    ComplexMatrixOnlyTopSingularValuePossiblyNonzero hn A := by
  classical
  let top : Fin n := ⟨0, hn⟩
  have hsum :
      (∑ i : Fin n, complexMatrixSingularValue A i ^ 2) =
        complexMatrixSingularValue A top ^ 2 := by
    simpa [top, complexMatrixFrobeniusSq_eq_sum_singularValue_sq,
      complexMatrixOp2_eq_top_singularValue hn A] using h
  have hsplit :
      (∑ i : Fin n, complexMatrixSingularValue A i ^ 2) =
        complexMatrixSingularValue A top ^ 2 +
          ∑ i ∈ Finset.univ.erase top, complexMatrixSingularValue A i ^ 2 := by
    conv_lhs =>
      rw [← Finset.insert_erase (Finset.mem_univ top)]
    rw [Finset.sum_insert (Finset.notMem_erase top Finset.univ)]
  have htail_zero :
      ∑ i ∈ Finset.univ.erase top, complexMatrixSingularValue A i ^ 2 = 0 := by
    nlinarith
  have htail_terms := (Finset.sum_eq_zero_iff_of_nonneg
    (s := Finset.univ.erase top)
    (f := fun i => complexMatrixSingularValue A i ^ 2)
    (by intro i _hi; exact sq_nonneg (complexMatrixSingularValue A i))).mp htail_zero
  intro i hi_ne
  have hi_mem : i ∈ Finset.univ.erase top := by
    simp [top, hi_ne]
  exact sq_eq_zero_iff.mp (htail_terms i hi_mem)

/-- Norm-form lower equality case for Higham Problem 6.9:
    `||A||₂ = ||A||_F` when only the top singular value can be nonzero. -/
theorem complexMatrixFrobenius_eq_op2_of_onlyTopSingularValue
    {m n : Nat} (hn : 0 < n) (A : CMatrix m n)
    (honly : ComplexMatrixOnlyTopSingularValuePossiblyNonzero hn A) :
    complexMatrixFrobenius A = complexMatrixOp2 A := by
  apply (sq_eq_sq₀ (complexMatrixFrobenius_nonneg A)
    (complexMatrixOp2_nonneg A)).mp
  rw [complexMatrixFrobenius_sq,
    complexMatrixFrobeniusSq_eq_op2_sq_of_onlyTopSingularValue hn A honly]

/-- Converse norm-form lower equality case for Higham Problem 6.9. -/
theorem complexMatrixOnlyTopSingularValuePossiblyNonzero_of_frobenius_eq_op2
    {m n : Nat} (hn : 0 < n) (A : CMatrix m n)
    (h : complexMatrixFrobenius A = complexMatrixOp2 A) :
    ComplexMatrixOnlyTopSingularValuePossiblyNonzero hn A := by
  apply complexMatrixOnlyTopSingularValuePossiblyNonzero_of_frobeniusSq_eq_op2_sq
    hn A
  rw [← complexMatrixFrobenius_sq A, h]

/-- If every singular value equals the operator `2`-norm, the Frobenius square
    attains the upper Problem 6.9 bound. -/
theorem complexMatrixFrobeniusSq_eq_card_mul_op2_sq_of_allSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n)
    (hall : ComplexMatrixAllSingularValuesEqualOp2 A) :
    complexMatrixFrobeniusSq A = (n : Real) * complexMatrixOp2 A ^ 2 := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq]
  calc
    (∑ i : Fin n, complexMatrixSingularValue A i ^ 2)
        = ∑ _i : Fin n, complexMatrixOp2 A ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [hall i]
    _ = (n : Real) * complexMatrixOp2 A ^ 2 := by
            simp [nsmul_eq_mul]

/-- Conversely, equality in the squared upper Problem 6.9 bound forces every
    singular value to equal the operator `2`-norm. -/
theorem complexMatrixAllSingularValuesEqualOp2_of_frobeniusSq_eq_card_mul_op2_sq
    {m n : Nat} (A : CMatrix m n)
    (h : complexMatrixFrobeniusSq A = (n : Real) * complexMatrixOp2 A ^ 2) :
    ComplexMatrixAllSingularValuesEqualOp2 A := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq] at h
  have heq_sq := finset_forall_eq_const_of_sum_eq_card_mul_of_le Finset.univ
    (fun i : Fin n => complexMatrixSingularValue A i ^ 2)
    (complexMatrixOp2 A ^ 2)
    (by
      intro i _hi
      exact (sq_le_sq₀ (complexMatrixSingularValue_nonneg A i)
        (complexMatrixOp2_nonneg A)).mpr
        (complexMatrixSingularValue_le_complexMatrixOp2 A i))
    (by simpa [nsmul_eq_mul] using h)
  intro i
  exact (sq_eq_sq₀ (complexMatrixSingularValue_nonneg A i)
    (complexMatrixOp2_nonneg A)).mp (heq_sq i (Finset.mem_univ i))

/-- Norm-form upper equality case for Higham Problem 6.9:
    `||A||_F = sqrt n * ||A||₂` when all local singular values equal `||A||₂`. -/
theorem complexMatrixFrobenius_eq_sqrt_card_mul_op2_of_allSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n)
    (hall : ComplexMatrixAllSingularValuesEqualOp2 A) :
    complexMatrixFrobenius A =
      Real.sqrt (n : Real) * complexMatrixOp2 A := by
  apply (sq_eq_sq₀ (complexMatrixFrobenius_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg A))).mp
  rw [complexMatrixFrobenius_sq,
    complexMatrixFrobeniusSq_eq_card_mul_op2_sq_of_allSingularValuesEqualOp2 A hall,
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Converse norm-form upper equality case for Higham Problem 6.9. -/
theorem complexMatrixAllSingularValuesEqualOp2_of_frobenius_eq_sqrt_card_mul_op2
    {m n : Nat} (A : CMatrix m n)
    (h : complexMatrixFrobenius A =
      Real.sqrt (n : Real) * complexMatrixOp2 A) :
    ComplexMatrixAllSingularValuesEqualOp2 A := by
  apply complexMatrixAllSingularValuesEqualOp2_of_frobeniusSq_eq_card_mul_op2_sq A
  rw [← complexMatrixFrobenius_sq A, h, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg n)]

/-- Converse equality condition for the entrywise-sum/Frobenius
    Cauchy-Schwarz step: equality forces all entry moduli to be equal. -/
theorem complexMatrixFlatEntryNorm_of_entrywiseSumNorm_sq_eq_card_mul_frobeniusSq
    {m n : Nat} (A : CMatrix m n)
    (h : complexMatrixEntrywiseSumNorm A ^ 2 =
      ((m * n : Nat) : Real) * complexMatrixFrobeniusSq A) :
    ComplexMatrixFlatEntryNorm A := by
  by_cases hmn : m * n = 0
  · apply Exists.intro 0
    exact And.intro le_rfl (by
      intro i j
      have hmpos : 0 < m := Nat.zero_lt_of_lt i.2
      have hnpos : 0 < n := Nat.zero_lt_of_lt j.2
      have hprod : 0 < m * n := Nat.mul_pos hmpos hnpos
      omega)
  · have hmpos : 0 < m := by
      exact Nat.pos_of_ne_zero (fun hm0 => hmn (by simp [hm0]))
    have hnpos : 0 < n := by
      exact Nat.pos_of_ne_zero (fun hn0 => hmn (by simp [hn0]))
    let x : Fin m × Fin n → Real := fun ij => ‖A ij.1 ij.2‖
    haveI : Nonempty (Fin m × Fin n) :=
      Nonempty.intro (⟨0, hmpos⟩, ⟨0, hnpos⟩)
    have hx_eq :
        (Finset.sum Finset.univ x) ^ 2 =
          (Fintype.card (Fin m × Fin n) : Real) *
            Finset.sum Finset.univ (fun ij => x ij ^ 2) := by
      rw [complexMatrixFrobeniusSq_eq_entrywise_sum] at h
      simpa [x, complexMatrixEntrywiseSumNorm, Fintype.card_prod,
        Fintype.card_fin, Nat.cast_mul] using h
    have hconst := forall_eq_finiteRealMean_of_sum_sq_eq_card_mul_sum_sq x hx_eq
    apply Exists.intro (finiteRealMean x)
    exact And.intro
      (by
        unfold finiteRealMean
        have hcard_pos : 0 < (Fintype.card (Fin m × Fin n) : Real) := by
          exact_mod_cast Fintype.card_pos
        exact div_nonneg
          (Finset.sum_nonneg (fun ij _ => norm_nonneg (A ij.1 ij.2)))
          (le_of_lt hcard_pos))
      (by
        intro i j
        exact hconst (i, j))

/-- Converse equality condition for the Frobenius/operator-rank step: equality
    forces every nonzero singular value to equal the operator `2`-norm. -/
theorem complexMatrixPositiveSingularValuesEqualOp2_of_frobeniusSq_eq_rank_mul_op2_sq
    {m n : Nat} (A : CMatrix m n)
    (h : complexMatrixFrobeniusSq A =
      (complexMatrixRank A : Real) * complexMatrixOp2 A ^ 2) :
    ComplexMatrixPositiveSingularValuesEqualOp2 A := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq] at h
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun i => complexMatrixSingularValue A i ≠ 0)
  have hsum_support :
      (∑ i : Fin n, complexMatrixSingularValue A i ^ 2) =
        ∑ i ∈ s, complexMatrixSingularValue A i ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun i => complexMatrixSingularValue A i ≠ 0)
      (f := fun i => complexMatrixSingularValue A i ^ 2)]
    have hzero :
        ∑ i ∈ Finset.univ.filter
            (fun i => complexMatrixSingularValue A i = 0),
          complexMatrixSingularValue A i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp at hi
      simp [hi]
    simp [s, hzero]
  have hcard_s : s.card = complexMatrixRank A := by
    calc
      s.card =
          Fintype.card
            {i : Fin n // complexMatrixSingularValue A i ≠ 0} := by
            simp [s, Fintype.card_subtype]
      _ = complexMatrixRank A :=
            (complexMatrixRank_eq_card_nonzero_singularValue A).symm
  have hsum_eq_const :
      (∑ i ∈ s, complexMatrixSingularValue A i ^ 2) =
        (s.card : Real) * complexMatrixOp2 A ^ 2 := by
    rw [← hsum_support, h, hcard_s]
  have heq_sq := finset_forall_eq_const_of_sum_eq_card_mul_of_le s
    (fun i => complexMatrixSingularValue A i ^ 2)
    (complexMatrixOp2 A ^ 2)
    (by
      intro i _hi
      have hle := complexMatrixSingularValue_le_complexMatrixOp2 A i
      have hsig := complexMatrixSingularValue_nonneg A i
      have hop := complexMatrixOp2_nonneg A
      nlinarith)
    hsum_eq_const
  intro i hi_nonzero
  have hi_s : i ∈ s := by
    simp [s, hi_nonzero]
  have hsquares : complexMatrixSingularValue A i ^ 2 = complexMatrixOp2 A ^ 2 :=
    heq_sq i hi_s
  have h_abs := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsquares
  rw [abs_of_nonneg (complexMatrixSingularValue_nonneg A i),
    abs_of_nonneg (complexMatrixOp2_nonneg A)] at h_abs
  exact h_abs

/-- In full local rank, the structural spectral condition says every singular
    value, not merely every nonzero one, equals the operator `2`-norm. -/
theorem complexMatrixSingularValue_eq_op2_of_rank_eq_card_of_positiveSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n) (hrank : complexMatrixRank A = n)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    ∀ i : Fin n, complexMatrixSingularValue A i = complexMatrixOp2 A := by
  intro i
  exact hsv i (complexMatrixSingularValue_ne_zero_of_rank_eq_card A hrank i)

/-- If all Gram eigenvalues are a common real scalar, the Gram operator is
    that scalar times the identity. -/
theorem complexMatrixGramLin_eq_smul_id_of_all_gramEigenvalues_eq
    {m n : Nat} (A : CMatrix m n) {lam : Real}
    (hlam : ∀ i : Fin n, complexMatrixGramEigenvalues A i = lam) :
    complexMatrixGramLin A =
      (lam : Complex) •
        (LinearMap.id :
          EuclideanSpace Complex (Fin n) →ₗ[Complex] EuclideanSpace Complex (Fin n)) := by
  apply LinearMap.ext_on
    (Module.Basis.span_eq (complexMatrixGramEigenvectorBasis A).toBasis)
  rintro x ⟨i, rfl⟩
  change (complexMatrixGramLin A) (complexMatrixGramEigenvectorBasis A i) =
    ((lam : Complex) •
      (LinearMap.id :
        EuclideanSpace Complex (Fin n) →ₗ[Complex] EuclideanSpace Complex (Fin n)))
        (complexMatrixGramEigenvectorBasis A i)
  rw [complexMatrixGramLin_apply_eigenvectorBasis A i, hlam i]
  rw [LinearMap.smul_apply]
  rfl

/-- Full local rank plus the structural spectral condition makes the Gram
    eigenvalues all equal to `||A||_2^2`. -/
theorem complexMatrixGramEigenvalues_eq_op2_sq_of_rank_eq_card_of_positiveSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n) (hrank : complexMatrixRank A = n)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    ∀ i : Fin n, complexMatrixGramEigenvalues A i = complexMatrixOp2 A ^ 2 := by
  intro i
  rw [← complexMatrixSingularValue_sq]
  rw [complexMatrixSingularValue_eq_op2_of_rank_eq_card_of_positiveSingularValuesEqualOp2
    A hrank hsv i]

/-- Full local rank plus the structural spectral condition makes `A† A` a
    scalar operator, with scalar `||A||_2^2`. -/
theorem complexMatrixGramLin_eq_op2_sq_smul_id_of_rank_eq_card_of_positiveSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n) (hrank : complexMatrixRank A = n)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    complexMatrixGramLin A =
      ((complexMatrixOp2 A ^ 2 : Real) : Complex) •
        (LinearMap.id :
          EuclideanSpace Complex (Fin n) →ₗ[Complex] EuclideanSpace Complex (Fin n)) := by
  exact complexMatrixGramLin_eq_smul_id_of_all_gramEigenvalues_eq A
    (complexMatrixGramEigenvalues_eq_op2_sq_of_rank_eq_card_of_positiveSingularValuesEqualOp2
      A hrank hsv)

/-- Concrete coordinate form of the previous full-rank spectral bridge:
    `A†A = ||A||_2^2 I`. -/
theorem complexMatrix_conjTranspose_mul_self_eq_op2_sq_smul_id_of_rank_eq_card_of_positiveSingularValuesEqualOp2
    {n : Nat} (A : CMatrix n n) (hrank : complexMatrixRank A = n)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
      (((complexMatrixOp2 A ^ 2 : Real) : Complex) •
        (1 : Matrix (Fin n) (Fin n) Complex)) := by
  rw [← complexMatrixGramLin_toMatrix A]
  rw [complexMatrixGramLin_eq_op2_sq_smul_id_of_rank_eq_card_of_positiveSingularValuesEqualOp2
    A hrank hsv]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [LinearMap.toMatrix_apply]
  · simp [LinearMap.toMatrix_apply, hij]

/-- Converse structural equality package for the rank-sensitive `S/2` bound:
    if the squared final bound is sharp and the entry index set is nonempty,
    then the Cauchy-Schwarz and spectral-rank equality conditions both hold. -/
theorem complexMatrixS2StructuralConditions_of_entrywiseSumNorm_sq_eq_card_rank_mul_op2_sq
    {m n : Nat} (hmn : 0 < m * n) (A : CMatrix m n)
    (h : complexMatrixEntrywiseSumNorm A ^ 2 =
      (((m * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A ^ 2) :
    ComplexMatrixFlatEntryNorm A ∧ ComplexMatrixPositiveSingularValuesEqualOp2 A := by
  let card : Real := ((m * n : Nat) : Real)
  let rankOp : Real := (complexMatrixRank A : Real) * complexMatrixOp2 A ^ 2
  have hcard_pos : 0 < card := by
    dsimp [card]
    exact_mod_cast hmn
  have hcard_nonneg : 0 ≤ card := le_of_lt hcard_pos
  have hS_le_F :
      complexMatrixEntrywiseSumNorm A ^ 2 ≤ card * complexMatrixFrobeniusSq A := by
    simpa [card] using complexMatrixEntrywiseSumNorm_sq_le_card_mul_frobeniusSq A
  have hF_le_R :
      complexMatrixFrobeniusSq A ≤ rankOp := by
    simpa [rankOp] using complexMatrixFrobeniusSq_le_rank_mul_complexMatrixOp2_sq A
  have hcardF_le_R :
      card * complexMatrixFrobeniusSq A ≤ card * rankOp :=
    mul_le_mul_of_nonneg_left hF_le_R hcard_nonneg
  have hS_eq_upper :
      complexMatrixEntrywiseSumNorm A ^ 2 = card * rankOp := by
    dsimp [card, rankOp]
    rw [h]
    ring
  have hupper_le_cardF :
      card * rankOp ≤ card * complexMatrixFrobeniusSq A := by
    rw [← hS_eq_upper]
    exact hS_le_F
  have hcardF_eq_upper :
      card * complexMatrixFrobeniusSq A = card * rankOp :=
    le_antisymm hcardF_le_R hupper_le_cardF
  have hS_eq_cardF :
      complexMatrixEntrywiseSumNorm A ^ 2 = card * complexMatrixFrobeniusSq A := by
    rw [hS_eq_upper, ← hcardF_eq_upper]
  have hF_eq_R :
      complexMatrixFrobeniusSq A = rankOp := by
    exact mul_left_cancel₀ (ne_of_gt hcard_pos) hcardF_eq_upper
  constructor
  · exact complexMatrixFlatEntryNorm_of_entrywiseSumNorm_sq_eq_card_mul_frobeniusSq
      A (by simpa [card] using hS_eq_cardF)
  · exact complexMatrixPositiveSingularValuesEqualOp2_of_frobeniusSq_eq_rank_mul_op2_sq
      A (by simpa [rankOp] using hF_eq_R)

/-- Source-facing nonsquared converse for the rank-sensitive `S/2` equality:
    the printed equality implies the two structural equality conditions. -/
theorem complexMatrixS2StructuralConditions_of_entrywiseSumNorm_eq_sqrt_card_rank_mul_op2
    {m n : Nat} (hmn : 0 < m * n) (A : CMatrix m n)
    (h : complexMatrixEntrywiseSumNorm A =
      Real.sqrt (((m * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A) :
    ComplexMatrixFlatEntryNorm A ∧ ComplexMatrixPositiveSingularValuesEqualOp2 A := by
  apply complexMatrixS2StructuralConditions_of_entrywiseSumNorm_sq_eq_card_rank_mul_op2_sq
    hmn A
  rw [h, mul_pow, Real.sq_sqrt
    (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]

/-- Full-rank square necessary-condition package for the `S/2` equality:
    sharpness gives flat entries and scalar Gram `A†A = ||A||_2^2 I`.  This is
    the checked bridge toward the scalar-multiple Hadamard specialization. -/
theorem complexMatrixFullRankS2Equality_flatEntryNorm_and_conjTranspose_mul_self_eq_op2_sq_smul_id
    {n : Nat} (hn : 0 < n) (A : CMatrix n n)
    (hrank : complexMatrixRank A = n)
    (h : complexMatrixEntrywiseSumNorm A =
      Real.sqrt (((n * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A) :
    ComplexMatrixFlatEntryNorm A ∧
      (complexCMatrixAsMatrix A).conjTranspose * complexCMatrixAsMatrix A =
        (((complexMatrixOp2 A ^ 2 : Real) : Complex) •
          (1 : Matrix (Fin n) (Fin n) Complex)) := by
  have hmn : 0 < n * n := Nat.mul_pos hn hn
  have hstruct :=
    complexMatrixS2StructuralConditions_of_entrywiseSumNorm_eq_sqrt_card_rank_mul_op2
      hmn A h
  exact ⟨hstruct.1,
    complexMatrix_conjTranspose_mul_self_eq_op2_sq_smul_id_of_rank_eq_card_of_positiveSingularValuesEqualOp2
      A hrank hstruct.2⟩

/-- Equality in the Frobenius/operator-rank squared estimate follows from the
    condition that all positive local singular values equal the top singular
    value. -/
theorem complexMatrixFrobeniusSq_eq_rank_mul_op2_sq_of_positiveSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    complexMatrixFrobeniusSq A =
      (complexMatrixRank A : Real) * complexMatrixOp2 A ^ 2 := by
  rw [complexMatrixFrobeniusSq_eq_sum_singularValue_sq]
  let s : Finset (Fin n) :=
    Finset.univ.filter (fun i => complexMatrixSingularValue A i ≠ 0)
  have hsum_support :
      (∑ i : Fin n, complexMatrixSingularValue A i ^ 2) =
        ∑ i ∈ s, complexMatrixSingularValue A i ^ 2 := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ)
      (p := fun i => complexMatrixSingularValue A i ≠ 0)
      (f := fun i => complexMatrixSingularValue A i ^ 2)]
    have hzero :
        ∑ i ∈ Finset.univ.filter
            (fun i => complexMatrixSingularValue A i = 0),
          complexMatrixSingularValue A i ^ 2 = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp at hi
      simp [hi]
    simp [s, hzero]
  calc
    (∑ i : Fin n, complexMatrixSingularValue A i ^ 2)
        = ∑ i ∈ s, complexMatrixSingularValue A i ^ 2 := hsum_support
    _ = ∑ _i ∈ s, complexMatrixOp2 A ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          have hi_nonzero : complexMatrixSingularValue A i ≠ 0 := by
            simpa [s] using hi
          rw [hsv i hi_nonzero]
    _ = (s.card : Real) * complexMatrixOp2 A ^ 2 := by
          simp [nsmul_eq_mul]
    _ = (complexMatrixRank A : Real) * complexMatrixOp2 A ^ 2 := by
          have hcard_s : s.card = complexMatrixRank A := by
            calc
              s.card =
                  Fintype.card
                    {i : Fin n // complexMatrixSingularValue A i ≠ 0} := by
                    simp [s, Fintype.card_subtype]
              _ = complexMatrixRank A :=
                    (complexMatrixRank_eq_card_nonzero_singularValue A).symm
          rw [hcard_s]

/-- Equality in the entrywise-sum/Frobenius Cauchy-Schwarz squared estimate
    follows when all entry moduli are equal. -/
theorem complexMatrixEntrywiseSumNorm_sq_eq_card_mul_frobeniusSq_of_flatEntryNorm
    {m n : Nat} (A : CMatrix m n) (hflat : ComplexMatrixFlatEntryNorm A) :
    complexMatrixEntrywiseSumNorm A ^ 2 =
      ((m * n : Nat) : Real) * complexMatrixFrobeniusSq A := by
  let rho : Real := Classical.choose hflat
  have hrho_spec : 0 ≤ rho ∧ ∀ i j, ‖A i j‖ = rho :=
    Classical.choose_spec hflat
  have hA : ∀ i j, ‖A i j‖ = rho := hrho_spec.2
  have hS :
      complexMatrixEntrywiseSumNorm A = ((m * n : Nat) : Real) * rho := by
    rw [complexMatrixEntrywiseSumNorm_eq_sum_sum]
    calc
      (∑ i : Fin m, ∑ j : Fin n, ‖A i j‖)
          = ∑ _i : Fin m, ∑ _j : Fin n, rho := by
              apply Finset.sum_congr rfl
              intro i _hi
              apply Finset.sum_congr rfl
              intro j _hj
              rw [hA i j]
      _ = (m : Real) * ((n : Real) * rho) := by
              simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
      _ = ((m * n : Nat) : Real) * rho := by
              rw [Nat.cast_mul]
              ring
  have hF :
      complexMatrixFrobeniusSq A = ((m * n : Nat) : Real) * rho ^ 2 := by
    rw [complexMatrixFrobeniusSq_eq_entrywise_sum]
    calc
      (∑ ij : Fin m × Fin n, ‖A ij.1 ij.2‖ ^ 2)
          = ∑ _ij : Fin m × Fin n, rho ^ 2 := by
              apply Finset.sum_congr rfl
              intro ij _hi
              rw [hA ij.1 ij.2]
      _ = ((m * n : Nat) : Real) * rho ^ 2 := by
              simp [Finset.sum_const, Fintype.card_prod, Fintype.card_fin,
                nsmul_eq_mul, Nat.cast_mul]
  rw [hS, hF]
  ring

/-- Squared equality in the rank-sensitive `S/2` bound from the two structural
    equality conditions: flat entries and equal nonzero singular values. -/
theorem complexMatrixEntrywiseSumNorm_sq_eq_card_rank_mul_op2_sq_of_flatEntryNorm_of_positiveSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n)
    (hflat : ComplexMatrixFlatEntryNorm A)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    complexMatrixEntrywiseSumNorm A ^ 2 =
      (((m * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A ^ 2 := by
  rw [complexMatrixEntrywiseSumNorm_sq_eq_card_mul_frobeniusSq_of_flatEntryNorm
    A hflat]
  rw [complexMatrixFrobeniusSq_eq_rank_mul_op2_sq_of_positiveSingularValuesEqualOp2
    A hsv]
  ring

/-- Equality in the rank-sensitive `S/2` bound from the two structural equality
    conditions: flat entries and equal nonzero singular values. This is the
    forward direction of the corrected general equality characterization; the
    special square full-rank real Hadamard iff is a stronger corollary. -/
theorem complexMatrixEntrywiseSumNorm_eq_sqrt_card_rank_mul_op2_of_flatEntryNorm_of_positiveSingularValuesEqualOp2
    {m n : Nat} (A : CMatrix m n)
    (hflat : ComplexMatrixFlatEntryNorm A)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    complexMatrixEntrywiseSumNorm A =
      Real.sqrt (((m * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A := by
  have hsq :
      complexMatrixEntrywiseSumNorm A ^ 2 =
        (Real.sqrt (((m * n : Nat) : Real) * (complexMatrixRank A : Real)) *
          complexMatrixOp2 A) ^ 2 := by
    rw [complexMatrixEntrywiseSumNorm_sq_eq_card_rank_mul_op2_sq_of_flatEntryNorm_of_positiveSingularValuesEqualOp2
      A hflat hsv]
    rw [mul_pow, Real.sq_sqrt
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  have hrhs_nonneg :
      0 ≤ Real.sqrt (((m * n : Nat) : Real) * (complexMatrixRank A : Real)) *
        complexMatrixOp2 A :=
    mul_nonneg (Real.sqrt_nonneg _) (complexMatrixOp2_nonneg A)
  have h_abs := (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
  rw [abs_of_nonneg (complexMatrixEntrywiseSumNorm_nonneg A),
    abs_of_nonneg hrhs_nonneg] at h_abs
  exact h_abs

/-- The Euclidean operator `2`-norm is an admissible bound for the local
    source-facing matrix `p = 2` norm predicate. -/
theorem complexMatrixOp2_hasComplexMatrixLpBound {m n : ℕ} (A : CMatrix m n) :
    HasComplexMatrixLpBound (ENNReal.ofReal (2 : ℝ)) A (complexMatrixOp2 A) := by
  refine ⟨complexMatrixOp2_nonneg A, ?_⟩
  intro x
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) := by norm_num
  have h :=
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin m) (n := Fin n) ≪≫ₗ
        LinearMap.toContinuousLinearMap) (A : Matrix (Fin m) (Fin n) ℂ)).le_opNorm
      (WithLp.toLp (2 : ENNReal) x)
  rw [h2]
  simpa [complexMatrixOp2, complexVecLpNorm, complexMatrixVecMul] using h

/-- Any local least-bound value for the source-facing matrix `p = 2` norm
    bounds the explicit Euclidean operator `2`-norm. -/
theorem complexMatrixOp2_le_of_isComplexMatrixLpNormValue_two
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) A c) :
    complexMatrixOp2 A ≤ c := by
  let L : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin m) :=
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := Fin m) (n := Fin n) ≪≫ₗ
      LinearMap.toContinuousLinearMap) (A : Matrix (Fin m) (Fin n) ℂ)
  have hbound : HasComplexMatrixLpBound (ENNReal.ofReal (2 : ℝ)) A c :=
    hasComplexMatrixLpBound_of_complexMatrixLpNormValue_ofReal
      (m := m) (n := n) hn (by norm_num) hA
  have hL : ‖L‖ ≤ c := by
    refine ContinuousLinearMap.opNorm_le_bound L hbound.1 ?_
    intro y
    have hcoord :
        WithLp.ofLp (L y) = complexMatrixVecMul A (WithLp.ofLp y) := by
      rfl
    calc
      ‖L y‖ =
          complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
            (complexMatrixVecMul A (WithLp.ofLp y)) := by
            rw [← complexVecLpNorm_two_ofLp_eq (L y), hcoord]
      _ ≤ c * complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) (WithLp.ofLp y) :=
            hbound.2 (WithLp.ofLp y)
      _ = c * ‖y‖ := by
            rw [complexVecLpNorm_two_ofLp_eq y]
  simpa [complexMatrixOp2, L] using hL

/-- Exact bridge between the local least-bound `p = 2` matrix norm predicate
    and the Euclidean operator `2`-norm. -/
theorem isComplexMatrixLpNormValue_two_eq_complexMatrixOp2
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n} {c : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) A c) :
    c = complexMatrixOp2 A := by
  exact le_antisymm
    (isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound hA
      (complexMatrixOp2_hasComplexMatrixLpBound A))
    (complexMatrixOp2_le_of_isComplexMatrixLpNormValue_two hn hA)

/-- Concrete source-facing `p = 2` matrix norm equals Mathlib's Euclidean
    operator norm wrapper. -/
theorem complexMatrixLpNormOfReal_two_eq_complexMatrixOp2
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A =
      complexMatrixOp2 A :=
  isComplexMatrixLpNormValue_two_eq_complexMatrixOp2 hn
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn (2 : ℝ) (by norm_num) A)

/-- Table 6.2 `M` versus `2` entry:
    `||A||_M <= ||A||_2`. -/
theorem complexMatrixEntrywiseMaxNorm_le_op2 {m n : ℕ} (A : CMatrix m n) :
    complexMatrixEntrywiseMaxNorm A ≤ complexMatrixOp2 A := by
  apply complexMatrixEntrywiseMaxNorm_le_of_coord_le A (complexMatrixOp2_nonneg A)
  intro i j
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j.2
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  have hd := complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
    (m := m) (n := n) hn (2 : ℝ) (by norm_num) A
  have hbound := hd.1 (standardBasisCVec j)
  have hcoord :=
    complexVecLpNorm_coord_le (n := m) (ENNReal.ofReal (2 : ℝ))
      (complexMatrixVecMul A (standardBasisCVec j)) i
  calc
    ‖A i j‖
        = ‖complexMatrixVecMul A (standardBasisCVec j) i‖ := by
          rw [complexMatrixVecMul_standardBasisCVec A j]
    _ ≤ complexVecLpNorm (ENNReal.ofReal (2 : ℝ))
        (complexMatrixVecMul A (standardBasisCVec j)) := hcoord
    _ ≤ complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A *
        complexVecLpNorm (ENNReal.ofReal (2 : ℝ)) (standardBasisCVec j) := hbound
    _ = complexMatrixOp2 A := by
          rw [complexVecLpNorm_standardBasisCVec, mul_one,
            complexMatrixLpNormOfReal_two_eq_complexMatrixOp2]

/-- Higham Problem 6.1 rank-one standard-basis witness:
    the Euclidean operator norm of `e_i e_j^T` is `1`. -/
theorem complexMatrixOp2_rankOne_standard_standard {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixOp2
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  apply le_antisymm
  · have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j0.2
    have h :=
      complexMatrixOp2_le_complexMatrixFrobenius hn
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
    simpa [complexMatrixFrobenius_rankOne_standard_standard i0 j0] using h
  · have h :=
      complexMatrixEntrywiseMaxNorm_le_op2
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
    simpa [complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0] using h

/-- Higham Problem 6.1 rank-one column witness:
    the Euclidean operator norm of `e e_j^T` is `sqrt m`. -/
theorem complexMatrixOp2_rankOne_const_standard {m n : ℕ}
    (j0 : Fin n) :
    complexMatrixOp2
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) =
      Real.sqrt (m : ℝ) := by
  apply le_antisymm
  · have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) j0.2
    have h :=
      complexMatrixOp2_le_complexMatrixFrobenius hn
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0))
    simpa [complexMatrixFrobenius_rankOne_const_standard j0] using h
  · haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
    let A : CMatrix m n :=
      complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)
    have hbound :=
      hasComplexMatrixLpBound_apply (complexMatrixOp2_hasComplexMatrixLpBound A)
        (standardBasisCVec j0)
    have hmul :
        complexMatrixVecMul A (standardBasisCVec j0) =
          (fun _ : Fin m => (1 : ℂ)) := by
      ext i
      rw [complexMatrixVecMul_standardBasisCVec]
      simp [A, complexMatrixRankOne, standardBasisCVec]
    rw [hmul, complexVecLpNorm_const_one_ofReal (by norm_num),
      complexVecLpNorm_standardBasisCVec, mul_one] at hbound
    rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num] at hbound
    simpa [Real.sqrt_eq_rpow] using hbound

/-- Higham Problem 6.1 rank-one row witness:
    the Euclidean operator norm of `e_i e^T` is `sqrt n`. -/
theorem complexMatrixOp2_rankOne_standard_const {m n : ℕ}
    (i0 : Fin m) (hn : 0 < n) :
    complexMatrixOp2
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) =
      Real.sqrt (n : ℝ) := by
  apply le_antisymm
  · have h :=
      complexMatrixOp2_le_complexMatrixFrobenius hn
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ)))
    simpa [complexMatrixFrobenius_rankOne_standard_const i0] using h
  · haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
    let A : CMatrix m n :=
      complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))
    have hbound :=
      hasComplexMatrixLpBound_apply (complexMatrixOp2_hasComplexMatrixLpBound A)
        (fun _ : Fin n => (1 : ℂ))
    have hmul :
        complexMatrixVecMul A (fun _ : Fin n => (1 : ℂ)) =
          (fun i : Fin m => (n : ℂ) * standardBasisCVec i0 i) := by
      ext i
      unfold complexMatrixVecMul A complexMatrixRankOne
      by_cases hi : i = i0
      · simp [standardBasisCVec, hi, Finset.sum_const, Fintype.card_fin]
      · simp [standardBasisCVec, hi]
    have htarget :
        complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ))
            (complexMatrixVecMul A (fun _ : Fin n => (1 : ℂ))) =
          (n : ℝ) := by
      rw [hmul]
      rw [complexVecLpNorm_ofReal_eq_sum_rpow (by norm_num)]
      have hsum :
          (∑ i : Fin m, ‖(n : ℂ) * standardBasisCVec i0 i‖ ^ (2 : ℝ)) =
            (n : ℝ) ^ (2 : ℝ) := by
        calc
          (∑ i : Fin m, ‖(n : ℂ) * standardBasisCVec i0 i‖ ^ (2 : ℝ))
              = ∑ i : Fin m, if i = i0 then (n : ℝ) ^ (2 : ℝ) else 0 := by
                apply Finset.sum_congr rfl
                intro i _hi
                by_cases hi : i = i0
                · simp [standardBasisCVec, hi]
                · simp [standardBasisCVec, hi]
          _ = (n : ℝ) ^ (2 : ℝ) := by simp
      rw [hsum]
      have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num]
      rw [← Real.sqrt_eq_rpow]
      have hpow : (n : ℝ) ^ (2 : ℝ) = (n : ℝ) ^ 2 := by
        norm_num [Real.rpow_natCast]
      rw [hpow]
      exact Real.sqrt_sq hn_nonneg
    rw [htarget, complexVecLpNorm_const_one_ofReal (by norm_num)] at hbound
    rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num] at hbound
    rw [← Real.sqrt_eq_rpow] at hbound
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    have hsqrt_mul_eq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
    have hbound' :
        Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) ≤
          complexMatrixOp2 A * Real.sqrt (n : ℝ) := by
      simpa [hsqrt_mul_eq] using hbound
    exact le_of_mul_le_mul_right hbound' hsqrt_pos

/-- Higham Problem 6.1 rank-one all-ones witness:
    the Euclidean operator norm of `e e^T` is `sqrt (m*n)`. -/
theorem complexMatrixOp2_rankOne_const_const {m n : ℕ}
    (hn : 0 < n) :
    complexMatrixOp2
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) =
      Real.sqrt ((m * n : ℕ) : ℝ) := by
  apply le_antisymm
  · have h :=
      complexMatrixOp2_le_complexMatrixFrobenius hn
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ)))
    simpa [complexMatrixFrobenius_rankOne_const_const] using h
  · haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
    let A : CMatrix m n :=
      complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))
    have hbound :=
      hasComplexMatrixLpBound_apply (complexMatrixOp2_hasComplexMatrixLpBound A)
        (fun _ : Fin n => (1 : ℂ))
    have hmul :
        complexMatrixVecMul A (fun _ : Fin n => (1 : ℂ)) =
          (fun _ : Fin m => (n : ℂ)) := by
      ext i
      unfold complexMatrixVecMul A complexMatrixRankOne
      simp [Finset.sum_const, Fintype.card_fin]
    have htarget :
        complexVecLpNorm (n := m) (ENNReal.ofReal (2 : ℝ))
            (complexMatrixVecMul A (fun _ : Fin n => (1 : ℂ))) =
          (n : ℝ) * Real.sqrt (m : ℝ) := by
      rw [hmul]
      have hconst :
          (fun _ : Fin m => (n : ℂ)) =
            complexVecSMul (n : ℂ) (fun _ : Fin m => (1 : ℂ)) := by
        ext i
        simp [complexVecSMul]
      rw [hconst]
      have hsmul :=
        (complexVecLpNorm_isComplexVectorNorm (n := m) (ENNReal.ofReal (2 : ℝ))).smul
          (n : ℂ) (fun _ : Fin m => (1 : ℂ))
      rw [complexVecLpNorm_const_one_ofReal (by norm_num)] at hsmul
      rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num] at hsmul
      rw [← Real.sqrt_eq_rpow] at hsmul
      have hnorm : ‖(n : ℂ)‖ = (n : ℝ) := by simp
      simpa [hnorm] using hsmul
    rw [htarget, complexVecLpNorm_const_one_ofReal (by norm_num)] at hbound
    rw [show (2 : ℝ)⁻¹ = (1 : ℝ) / 2 by norm_num] at hbound
    rw [← Real.sqrt_eq_rpow] at hbound
    have hsqrt_pos : 0 < Real.sqrt (n : ℝ) :=
      Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
    have hsqrt_n_mul_eq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
      rw [← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
    have hsqrt_mn :
        Real.sqrt ((m * n : ℕ) : ℝ) =
          Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg m)]
    have hbound' :
        Real.sqrt ((m * n : ℕ) : ℝ) * Real.sqrt (n : ℝ) ≤
          complexMatrixOp2 A * Real.sqrt (n : ℝ) := by
      simpa [hsqrt_mn, hsqrt_n_mul_eq, mul_assoc, mul_left_comm, mul_comm] using hbound
    exact le_of_mul_le_mul_right hbound' hsqrt_pos

/-- Higham Problem 6.1 rank-one standard-basis witness:
    the concrete matrix `1`-norm of `e_i e_j^T` is `1`. -/
theorem complexMatrixOneNorm_rankOne_standard_standard {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixOneNorm
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  apply le_antisymm
  · apply complexMatrixOneNorm_le_of_col_sum_le zero_le_one
    intro j
    by_cases hj : j = j0
    · have hcol :
          (∑ i : Fin m, ‖standardBasisCVec i0 i‖) = 1 := by
        simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec i0
      have hy : ‖standardBasisCVec j0 j0‖ = 1 := by
        simp [standardBasisCVec]
      simpa [complexMatrixRankOne, hj, hy] using le_of_eq hcol
    · simp [complexMatrixRankOne, standardBasisCVec, hj]
  · have h :=
      complexMatrixOneNorm_col_sum_le
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) j0
    have hcol :
        (∑ i : Fin m, ‖standardBasisCVec i0 i‖) = 1 := by
      simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec i0
    have hy : ‖standardBasisCVec j0 j0‖ = 1 := by
      simp [standardBasisCVec]
    simpa [complexMatrixRankOne, hcol, hy] using h

set_option linter.unusedTactic false in
/-- Higham Problem 6.1 rank-one column witness:
    the concrete matrix `1`-norm of `e e_j^T` is `m`. -/
theorem complexMatrixOneNorm_rankOne_const_standard {m n : ℕ}
    (j0 : Fin n) :
    complexMatrixOneNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) =
      (m : ℝ) := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 3 }
  apply le_antisymm
  · apply complexMatrixOneNorm_le_of_col_sum_le (Nat.cast_nonneg m)
    intro j
    by_cases hj : j = j0
    · simp [complexMatrixRankOne, standardBasisCVec, hj,
        Finset.sum_const, Fintype.card_fin]
    · simp [complexMatrixRankOne, standardBasisCVec, hj, Nat.cast_nonneg]
  · have h :=
      complexMatrixOneNorm_col_sum_le
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) j0
    simpa [complexMatrixRankOne, standardBasisCVec,
      Finset.sum_const, Fintype.card_fin] using h

/-- Higham Problem 6.1 rank-one row witness:
    the concrete matrix `1`-norm of `e_i e^T` is `1` when there is a column. -/
theorem complexMatrixOneNorm_rankOne_standard_const {m n : ℕ}
    (i0 : Fin m) (hn : 0 < n) :
    complexMatrixOneNorm
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) = 1 := by
  apply le_antisymm
  · apply complexMatrixOneNorm_le_of_col_sum_le zero_le_one
    intro j
    have hcol :
        (∑ i : Fin m, ‖standardBasisCVec i0 i‖) = 1 := by
      simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec i0
    simpa [complexMatrixRankOne] using le_of_eq hcol
  · let j0 : Fin n := ⟨0, hn⟩
    have h :=
      complexMatrixOneNorm_col_sum_le
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) j0
    have hcol :
        (∑ i : Fin m, ‖standardBasisCVec i0 i‖) = 1 := by
      simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec i0
    simpa [complexMatrixRankOne, hcol] using h

/-- Higham Problem 6.1 rank-one all-ones witness:
    the concrete matrix `1`-norm of `e e^T` is `m` when there is a column. -/
theorem complexMatrixOneNorm_rankOne_const_const {m n : ℕ}
    (hn : 0 < n) :
    complexMatrixOneNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) =
      (m : ℝ) := by
  apply le_antisymm
  · apply complexMatrixOneNorm_le_of_col_sum_le (Nat.cast_nonneg m)
    intro j
    simp [complexMatrixRankOne, Finset.sum_const, Fintype.card_fin]
  · let j0 : Fin n := ⟨0, hn⟩
    have h :=
      complexMatrixOneNorm_col_sum_le
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) j0
    simpa [complexMatrixRankOne, Finset.sum_const, Fintype.card_fin] using h

/-- Higham Problem 6.1 rank-one standard-basis witness:
    the concrete matrix infinity norm of `e_i e_j^T` is `1`. -/
theorem complexMatrixInfNorm_rankOne_standard_standard {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    complexMatrixInfNorm
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) = 1 := by
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le zero_le_one
    intro i
    by_cases hi : i = i0
    · have hrow :
          (∑ j : Fin n, ‖standardBasisCVec j0 j‖) = 1 := by
        simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec j0
      have hx : ‖standardBasisCVec i0 i0‖ = 1 := by
        simp [standardBasisCVec]
      simpa [complexMatrixRankOne, hi, hx] using le_of_eq hrow
    · simp [complexMatrixRankOne, standardBasisCVec, hi]
  · have h :=
      complexMatrixInfNorm_row_sum_le
        (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) i0
    have hrow :
        (∑ j : Fin n, ‖standardBasisCVec j0 j‖) = 1 := by
      simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec j0
    have hx : ‖standardBasisCVec i0 i0‖ = 1 := by
      simp [standardBasisCVec]
    simpa [complexMatrixRankOne, hrow, hx] using h

/-- Higham Problem 6.1 rank-one column witness:
    the concrete matrix infinity norm of `e e_j^T` is `1` when there is a row. -/
theorem complexMatrixInfNorm_rankOne_const_standard {m n : ℕ}
    (hm : 0 < m) (j0 : Fin n) :
    complexMatrixInfNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) = 1 := by
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le zero_le_one
    intro i
    have hrow :
        (∑ j : Fin n, ‖standardBasisCVec j0 j‖) = 1 := by
      simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec j0
    simpa [complexMatrixRankOne] using le_of_eq hrow
  · let i0 : Fin m := ⟨0, hm⟩
    have h :=
      complexMatrixInfNorm_row_sum_le
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0)) i0
    have hrow :
        (∑ j : Fin n, ‖standardBasisCVec j0 j‖) = 1 := by
      simpa [complexVecOneNorm] using complexVecOneNorm_standardBasisCVec j0
    simpa [complexMatrixRankOne, hrow] using h

set_option linter.unusedTactic false in
/-- Higham Problem 6.1 rank-one row witness:
    the concrete matrix infinity norm of `e_i e^T` is `n`. -/
theorem complexMatrixInfNorm_rankOne_standard_const {m n : ℕ}
    (i0 : Fin m) :
    complexMatrixInfNorm
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) =
      (n : ℝ) := by
  -- Preserve frozen auxiliary names across the semantic module split.
  run_tac do
    let ngen ← Lean.getDeclNGen
    Lean.setDeclNGen { ngen with idx := 3 }
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le (Nat.cast_nonneg n)
    intro i
    by_cases hi : i = i0
    · simp [complexMatrixRankOne, standardBasisCVec, hi,
        Finset.sum_const, Fintype.card_fin]
    · simp [complexMatrixRankOne, standardBasisCVec, hi, Nat.cast_nonneg]
  · have h :=
      complexMatrixInfNorm_row_sum_le
        (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ))) i0
    simpa [complexMatrixRankOne, standardBasisCVec,
      Finset.sum_const, Fintype.card_fin] using h

/-- Higham Problem 6.1 rank-one all-ones witness:
    the concrete matrix infinity norm of `e e^T` is `n` when there is a row. -/
theorem complexMatrixInfNorm_rankOne_const_const {m n : ℕ}
    (hm : 0 < m) :
    complexMatrixInfNorm
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) =
      (n : ℝ) := by
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le (Nat.cast_nonneg n)
    intro i
    simp [complexMatrixRankOne, Finset.sum_const, Fintype.card_fin]
  · let i0 : Fin m := ⟨0, hm⟩
    have h :=
      complexMatrixInfNorm_row_sum_le
        (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ))) i0
    simpa [complexMatrixRankOne, Finset.sum_const, Fintype.card_fin] using h

theorem complexMatrixLpNormOfReal_two_eq_top_singularValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A =
      complexMatrixSingularValue A ⟨0, hn⟩ := by
  rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2,
    complexMatrixOp2_eq_top_singularValue hn A]

/-- Higham, 2nd ed., Chapter 6, equation (6.17), right inequality:
    the local square `p -> p` matrix norm value is bounded by the local
    `2 -> 2` value with factor `n^|1/p - 1/2|`. -/
theorem complexMatrixLpNorm_le_card_rpow_abs_mul_complexMatrixTwoNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) {A : CMatrix n n} {dp d2 : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hA2 : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ)))
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))) A d2) :
    dp ≤ (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹| * d2 := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by
    rw [ENNReal.one_le_ofReal]
    norm_num⟩
  let νp : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let ν2 : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))
  let c : ℝ := (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹|
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) |p⁻¹ - (2 : ℝ)⁻¹|
  have hν2 : IsComplexVectorNorm ν2 :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal (2 : ℝ))
  have hd2_nonneg : 0 ≤ d2 :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hν2 hν2 hA2
  by_cases hp2 : p ≤ 2
  · have habs : |p⁻¹ - (2 : ℝ)⁻¹| = p⁻¹ - (2 : ℝ)⁻¹ := by
      have hhalf_le : (2 : ℝ)⁻¹ ≤ p⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hp_pos hp2)
      exact abs_of_nonneg (sub_nonneg.mpr hhalf_le)
    apply hAp.2
    intro x
    calc
      νp (complexMatrixVecMul A x)
          ≤ c * ν2 (complexMatrixVecMul A x) := by
            simpa [νp, ν2, c, habs] using
              (complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
                (n := n) (p := (2 : ℝ)) (q := p) hp hp2
                (complexMatrixVecMul A x))
      _ ≤ c * (d2 * ν2 x) :=
            mul_le_mul_of_nonneg_left (hA2.1 x) hc_nonneg
      _ ≤ c * (d2 * νp x) := by
            have hx : ν2 x ≤ νp x := by
              simpa [νp, ν2] using
                (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
                  (n := n) (p := (2 : ℝ)) (q := p) hp hp2 x)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hx hd2_nonneg) hc_nonneg
      _ = (c * d2) * νp x := by ring
  · have h2p : 2 ≤ p := le_of_not_ge hp2
    have habs : |p⁻¹ - (2 : ℝ)⁻¹| = (2 : ℝ)⁻¹ - p⁻¹ := by
      have hinv_le : p⁻¹ ≤ (2 : ℝ)⁻¹ := by
        have htwo_pos : (0 : ℝ) < 2 := by norm_num
        simpa [one_div] using (one_div_le_one_div_of_le htwo_pos h2p)
      simpa using
        (abs_of_nonpos (sub_nonpos.mpr hinv_le) :
          |p⁻¹ - (2 : ℝ)⁻¹| = -(p⁻¹ - (2 : ℝ)⁻¹))
    apply hAp.2
    intro x
    calc
      νp (complexMatrixVecMul A x)
          ≤ ν2 (complexMatrixVecMul A x) := by
            simpa [νp, ν2] using
              (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
                (n := n) (p := p) (q := (2 : ℝ)) (by norm_num) h2p
                (complexMatrixVecMul A x))
      _ ≤ d2 * ν2 x := hA2.1 x
      _ ≤ d2 * (c * νp x) := by
            have hx : ν2 x ≤ c * νp x := by
              simpa [νp, ν2, c, habs] using
                (complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
                  (n := n) (p := p) (q := (2 : ℝ)) (by norm_num) h2p x)
            exact mul_le_mul_of_nonneg_left hx hd2_nonneg
      _ = (c * d2) * νp x := by ring

/-- Higham, 2nd ed., Chapter 6, equation (6.17), left inequality in product
    form: the local square `2 -> 2` matrix norm value is bounded by the local
    `p -> p` value with factor `n^|1/p - 1/2|`. -/
theorem complexMatrixTwoNorm_le_card_rpow_abs_mul_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) {A : CMatrix n n} {dp d2 : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hA2 : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ)))
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))) A d2) :
    d2 ≤ (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹| * dp := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  haveI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by
    rw [ENNReal.one_le_ofReal]
    norm_num⟩
  let νp : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let ν2 : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))
  let c : ℝ := (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹|
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) |p⁻¹ - (2 : ℝ)⁻¹|
  have hνp : IsComplexVectorNorm νp :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hν2 : IsComplexVectorNorm ν2 :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal (2 : ℝ))
  have hdp_nonneg : 0 ≤ dp :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hνp hνp hAp
  by_cases hp2 : p ≤ 2
  · have habs : |p⁻¹ - (2 : ℝ)⁻¹| = p⁻¹ - (2 : ℝ)⁻¹ := by
      have hhalf_le : (2 : ℝ)⁻¹ ≤ p⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hp_pos hp2)
      exact abs_of_nonneg (sub_nonneg.mpr hhalf_le)
    apply hA2.2
    intro x
    calc
      ν2 (complexMatrixVecMul A x)
          ≤ νp (complexMatrixVecMul A x) := by
            simpa [νp, ν2] using
              (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
                (n := n) (p := (2 : ℝ)) (q := p) hp hp2
                (complexMatrixVecMul A x))
      _ ≤ dp * νp x := hAp.1 x
      _ ≤ dp * (c * ν2 x) := by
            have hx : νp x ≤ c * ν2 x := by
              simpa [νp, ν2, c, habs] using
                (complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
                  (n := n) (p := (2 : ℝ)) (q := p) hp hp2 x)
            exact mul_le_mul_of_nonneg_left hx hdp_nonneg
      _ = (c * dp) * ν2 x := by ring
  · have h2p : 2 ≤ p := le_of_not_ge hp2
    have habs : |p⁻¹ - (2 : ℝ)⁻¹| = (2 : ℝ)⁻¹ - p⁻¹ := by
      have hinv_le : p⁻¹ ≤ (2 : ℝ)⁻¹ := by
        have htwo_pos : (0 : ℝ) < 2 := by norm_num
        simpa [one_div] using (one_div_le_one_div_of_le htwo_pos h2p)
      simpa using
        (abs_of_nonpos (sub_nonpos.mpr hinv_le) :
          |p⁻¹ - (2 : ℝ)⁻¹| = -(p⁻¹ - (2 : ℝ)⁻¹))
    apply hA2.2
    intro x
    calc
      ν2 (complexMatrixVecMul A x)
          ≤ c * νp (complexMatrixVecMul A x) := by
            simpa [νp, ν2, c, habs] using
              (complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
                (n := n) (p := p) (q := (2 : ℝ)) (by norm_num) h2p
                (complexMatrixVecMul A x))
      _ ≤ c * (dp * νp x) :=
            mul_le_mul_of_nonneg_left (hAp.1 x) hc_nonneg
      _ ≤ c * (dp * ν2 x) := by
            have hx : νp x ≤ ν2 x := by
              simpa [νp, ν2] using
                (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
                  (n := n) (p := p) (q := (2 : ℝ)) (by norm_num) h2p x)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hx hdp_nonneg) hc_nonneg
      _ = (c * dp) * ν2 x := by ring

/-- Higham, 2nd ed., Chapter 6, equation (6.17), source-facing divided left
    inequality, relative to supplied local square `p -> p` and `2 -> 2`
    mixed-subordinate norm values. -/
theorem complexMatrixTwoNorm_div_card_rpow_abs_le_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) {A : CMatrix n n} {dp d2 : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hA2 : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ)))
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))) A d2) :
    d2 / ((n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹|) ≤ dp := by
  have hc_pos : 0 < (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹| :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) |p⁻¹ - (2 : ℝ)⁻¹|
  rw [div_le_iff₀ hc_pos]
  simpa [mul_comm] using
    (complexMatrixTwoNorm_le_card_rpow_abs_mul_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
      hn hp hAp hA2)

/-- Higham, 2nd ed., Chapter 6, equation (6.17), bundled two-sided local
    comparison between supplied square `p -> p` and `2 -> 2`
    mixed-subordinate norm values. -/
theorem complexMatrixTwoNorm_lpNorm_equiv_bounds_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) {A : CMatrix n n} {dp d2 : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hA2 : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ)))
      (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))) A d2) :
    d2 / ((n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹|) ≤ dp ∧
      dp ≤ (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹| * d2 :=
  ⟨complexMatrixTwoNorm_div_card_rpow_abs_le_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
      hn hp hAp hA2,
    complexMatrixLpNorm_le_card_rpow_abs_mul_complexMatrixTwoNorm_of_mixedSubordinateMatrixNormValue
      hn hp hAp hA2⟩

/-- Source-facing form of Higham equation (6.17), using local matrix `p`- and
    `2`-norm value predicates. -/
theorem complexMatrixLpNormValue_twoNorm_equiv_bounds
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix n n} {dp d2 : ℝ}
    (hAp : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A dp)
    (hA2 : IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) A d2) :
    d2 / ((n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹|) ≤ dp ∧
      dp ≤ (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹| * d2 := by
  have hAp_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp := by
    simpa [IsComplexMatrixLpNormValue] using hAp
  have hA2_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ)))
        (complexVecLpNorm (n := n) (ENNReal.ofReal (2 : ℝ))) A d2 := by
    simpa [IsComplexMatrixLpNormValue] using hA2
  exact complexMatrixTwoNorm_lpNorm_equiv_bounds_of_mixedSubordinateMatrixNormValue
    (n := n) hn (p := p) hp hAp_mixed hA2_mixed

/-- Higham, 2nd ed., Chapter 6, equation (6.15), upper-comparison
    dependency: supplied local square `p -> p` and `q -> q`
    mixed-subordinate norm values differ by at most `n^|1/p - 1/q|`. -/
theorem complexMatrixLpNorm_le_card_rpow_abs_mul_complexMatrixLqNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {A : CMatrix n n} {dp dq : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hAq : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) A dq) :
    dp ≤ (n : ℝ) ^ |p⁻¹ - q⁻¹| * dq := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hq⟩
  let νp : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let νq : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal q)
  let c : ℝ := (n : ℝ) ^ |p⁻¹ - q⁻¹|
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq_pos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg n) |p⁻¹ - q⁻¹|
  have hνq : IsComplexVectorNorm νq :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal q)
  have hdq_nonneg : 0 ≤ dq :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hνq hνq hAq
  by_cases hpq : p ≤ q
  · have habs : |p⁻¹ - q⁻¹| = p⁻¹ - q⁻¹ := by
      have hq_inv_le : q⁻¹ ≤ p⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hp_pos hpq)
      exact abs_of_nonneg (sub_nonneg.mpr hq_inv_le)
    apply hAp.2
    intro x
    calc
      νp (complexMatrixVecMul A x)
          ≤ c * νq (complexMatrixVecMul A x) := by
            simpa [νp, νq, c, habs] using
              (complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
                (n := n) (p := q) (q := p) hp hpq (complexMatrixVecMul A x))
      _ ≤ c * (dq * νq x) :=
            mul_le_mul_of_nonneg_left (hAq.1 x) hc_nonneg
      _ ≤ c * (dq * νp x) := by
            have hx : νq x ≤ νp x := by
              simpa [νp, νq] using
                (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
                  (n := n) (p := q) (q := p) hp hpq x)
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hx hdq_nonneg) hc_nonneg
      _ = (c * dq) * νp x := by ring
  · have hqp : q ≤ p := le_of_not_ge hpq
    have habs : |p⁻¹ - q⁻¹| = q⁻¹ - p⁻¹ := by
      have hp_inv_le : p⁻¹ ≤ q⁻¹ := by
        simpa [one_div] using (one_div_le_one_div_of_le hq_pos hqp)
      simpa using
        (abs_of_nonpos (sub_nonpos.mpr hp_inv_le) :
          |p⁻¹ - q⁻¹| = -(p⁻¹ - q⁻¹))
    apply hAp.2
    intro x
    calc
      νp (complexMatrixVecMul A x)
          ≤ νq (complexMatrixVecMul A x) := by
            simpa [νp, νq] using
              (complexVecLpNorm_le_complexVecLpNorm_of_exponent_le
                (n := n) (p := p) (q := q) hq hqp (complexMatrixVecMul A x))
      _ ≤ dq * νq x := hAq.1 x
      _ ≤ dq * (c * νp x) := by
            have hx : νq x ≤ c * νp x := by
              simpa [νp, νq, c, habs] using
                (complexVecLpNorm_le_card_rpow_mul_complexVecLpNorm_of_exponent_le
                  (n := n) (p := p) (q := q) hq hqp x)
            exact mul_le_mul_of_nonneg_left hx hdq_nonneg
      _ = (c * dq) * νp x := by ring

/-- Higham, 2nd ed., Chapter 6, equation (6.15), divided comparison
    dependency between supplied local square `p -> p` and `q -> q`
    mixed-subordinate norm values. -/
theorem complexMatrixLqNorm_div_card_rpow_abs_le_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {A : CMatrix n n} {dp dq : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hAq : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) A dq) :
    dq / ((n : ℝ) ^ |p⁻¹ - q⁻¹|) ≤ dp := by
  have hc_pos : 0 < (n : ℝ) ^ |p⁻¹ - q⁻¹| :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) |p⁻¹ - q⁻¹|
  have habs_comm : |q⁻¹ - p⁻¹| = |p⁻¹ - q⁻¹| := by
    rw [abs_sub_comm]
  have h :=
    complexMatrixLpNorm_le_card_rpow_abs_mul_complexMatrixLqNorm_of_mixedSubordinateMatrixNormValue
      (n := n) hn (p := q) (q := p) hq hp hAq hAp
  rw [div_le_iff₀ hc_pos]
  simpa [habs_comm, mul_comm] using h

/-- Higham, 2nd ed., Chapter 6, equation (6.15), bundled local
    two-sided comparison between supplied square `p -> p` and `q -> q`
    mixed-subordinate norm values.  This is the local upper-bound layer; the
    source's max/equality attainability statement remains a separate target. -/
theorem complexMatrixLpNorm_equiv_bounds_of_mixedSubordinateMatrixNormValue
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {A : CMatrix n n} {dp dq : ℝ}
    (hAp : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp)
    (hAq : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal q))
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) A dq) :
    dq / ((n : ℝ) ^ |p⁻¹ - q⁻¹|) ≤ dp ∧
      dp ≤ (n : ℝ) ^ |p⁻¹ - q⁻¹| * dq :=
  ⟨complexMatrixLqNorm_div_card_rpow_abs_le_complexMatrixLpNorm_of_mixedSubordinateMatrixNormValue
      hn hp hq hAp hAq,
    complexMatrixLpNorm_le_card_rpow_abs_mul_complexMatrixLqNorm_of_mixedSubordinateMatrixNormValue
      hn hp hq hAp hAq⟩

/-- Source-facing local form of Higham equation (6.15), using local matrix
    `p`- and `q`-norm value predicates.  This packages the two-sided comparison
    layer; the Schneider-Strang sharp max/equality formula remains separate. -/
theorem complexMatrixLpNormValue_pq_equiv_bounds
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    {A : CMatrix n n} {dp dq : ℝ}
    (hAp : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A dp)
    (hAq : IsComplexMatrixLpNormValue (ENNReal.ofReal q) A dq) :
    dq / ((n : ℝ) ^ |p⁻¹ - q⁻¹|) ≤ dp ∧
      dp ≤ (n : ℝ) ^ |p⁻¹ - q⁻¹| * dq := by
  have hAp_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A dp := by
    simpa [IsComplexMatrixLpNormValue] using hAp
  have hAq_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal q))
        (complexVecLpNorm (n := n) (ENNReal.ofReal q)) A dq := by
    simpa [IsComplexMatrixLpNormValue] using hAq
  exact complexMatrixLpNorm_equiv_bounds_of_mixedSubordinateMatrixNormValue
    (n := n) hn (p := p) (q := q) hp hq hAp_mixed hAq_mixed

/-- Lower-bound half of Higham Problem 6.15 for finite real exponents:
    the local `p`-norm value of `A` is bounded by that of its entrywise
    absolute matrix `|A|`. -/
theorem complexMatrixLpNormValue_le_absMatrixLpNormValue
    {m n : ℕ} {p : ℝ} (hp : 1 ≤ p) {A : CMatrix m n} {d e : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d)
    (hAbsA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexAbsMatrix A) e) :
    d ≤ e := by
  let νsrc : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let νtgt : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue νsrc νtgt A d := by
    simpa [νsrc, νtgt, IsComplexMatrixLpNormValue] using hA
  have hAbs_mixed :
      IsMixedSubordinateMatrixNormValue νsrc νtgt (complexAbsMatrix A) e := by
    simpa [νsrc, νtgt, IsComplexMatrixLpNormValue] using hAbsA
  have htgt_mono : IsMonotoneComplexVectorNorm νtgt := by
    simpa [νtgt] using complexVecLpNorm_ofReal_monotone (n := m) (p := p) hp
  have hsrc_abs : ∀ x : CVec n, νsrc (complexAbsVec x) = νsrc x := by
    intro x
    simpa [νsrc] using
      complexVecLpNorm_ofReal_abs_eq (n := n) (p := p)
        (lt_of_lt_of_le zero_lt_one hp) x
  apply hA_mixed.2 e
  intro x
  calc
    νtgt (complexMatrixVecMul A x)
        ≤ νtgt (complexMatrixVecMul (complexAbsMatrix A) (complexAbsVec x)) :=
          htgt_mono _ _ (complexMatrixVecMul_componentwiseAbsLe_absMatrix A x)
    _ ≤ e * νsrc (complexAbsVec x) := hAbs_mixed.1 (complexAbsVec x)
    _ = e * νsrc x := by rw [hsrc_abs x]

/-- Source-facing complex `2`-norm monotonicity under entrywise absolute value:
    `||A||_2 <= || |A| ||_2`. -/
theorem complexMatrixOp2_le_complexMatrixOp2_absMatrix
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 A ≤ complexMatrixOp2 (complexAbsMatrix A) := by
  have hA :
      IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) A
        (complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A) :=
    complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn (2 : ℝ) (by norm_num) A
  have hAbsA :
      IsComplexMatrixLpNormValue (ENNReal.ofReal (2 : ℝ)) (complexAbsMatrix A)
        (complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) (complexAbsMatrix A)) :=
    complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn (2 : ℝ) (by norm_num)
      (complexAbsMatrix A)
  have hle :=
    complexMatrixLpNormValue_le_absMatrixLpNormValue
      (m := m) (n := n) (p := (2 : ℝ)) (by norm_num) hA hAbsA
  simpa [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn A,
    complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn (complexAbsMatrix A)] using hle

/-- The operator `2`-norm of the entrywise absolute matrix is bounded by the
    original Frobenius norm. -/
theorem complexMatrixOp2_absMatrix_le_complexMatrixFrobenius
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 (complexAbsMatrix A) ≤ complexMatrixFrobenius A := by
  calc
    complexMatrixOp2 (complexAbsMatrix A)
        ≤ complexMatrixFrobenius (complexAbsMatrix A) :=
          complexMatrixOp2_le_complexMatrixFrobenius hn (complexAbsMatrix A)
    _ = complexMatrixFrobenius A := complexMatrixFrobenius_absMatrix_eq A

/-- Rank-sensitive source-facing absolute-matrix/operator-2 comparison:
    `|| |A| ||_2 <= sqrt(rank A) * ||A||_2`. -/
theorem complexMatrixOp2_absMatrix_le_sqrt_rank_mul_complexMatrixOp2
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 (complexAbsMatrix A) ≤
      Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A := by
  exact (complexMatrixOp2_absMatrix_le_complexMatrixFrobenius hn A).trans
    (complexMatrixFrobenius_le_sqrt_rank_mul_complexMatrixOp2 A)

/-- Combined source-facing Lemma 6.6-style absolute-matrix `2`-norm chain. -/
theorem complexMatrixOp2_absMatrix_bounds
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixOp2 A ≤ complexMatrixOp2 (complexAbsMatrix A) ∧
      complexMatrixOp2 (complexAbsMatrix A) ≤
        Real.sqrt (complexMatrixRank A : ℝ) * complexMatrixOp2 A := by
  exact ⟨complexMatrixOp2_le_complexMatrixOp2_absMatrix hn A,
    complexMatrixOp2_absMatrix_le_sqrt_rank_mul_complexMatrixOp2 hn A⟩

/-- Higham, 2nd ed., Chapter 6, Lemma 6.6: concrete matrix `p = 2`
    notation for `||A||_2 <= || |A| ||_2`. -/
theorem complexMatrixLpNormOfReal_two_le_absMatrix
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A ≤
      complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) (complexAbsMatrix A) := by
  simpa [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn A,
    complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn (complexAbsMatrix A)] using
    complexMatrixOp2_le_complexMatrixOp2_absMatrix hn A

/-- Higham, 2nd ed., Chapter 6, Lemma 6.6: concrete matrix `p = 2`
    notation for `|| |A| ||_2 <= ||A||_F`. -/
theorem complexMatrixLpNormOfReal_two_absMatrix_le_complexMatrixFrobenius
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) (complexAbsMatrix A) ≤
      complexMatrixFrobenius A := by
  simpa [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn (complexAbsMatrix A)] using
    complexMatrixOp2_absMatrix_le_complexMatrixFrobenius hn A

/-- Higham, 2nd ed., Chapter 6, Lemma 6.6: concrete matrix `p = 2`
    notation for the rank-sensitive bound
    `|| |A| ||_2 <= sqrt(rank A) * ||A||_2`. -/
theorem complexMatrixLpNormOfReal_two_absMatrix_le_sqrt_rank_mul
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) (complexAbsMatrix A) ≤
      Real.sqrt (complexMatrixRank A : ℝ) *
        complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A := by
  simpa [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn A,
    complexMatrixLpNormOfReal_two_eq_complexMatrixOp2 hn (complexAbsMatrix A)] using
    complexMatrixOp2_absMatrix_le_sqrt_rank_mul_complexMatrixOp2 hn A

/-- Higham, 2nd ed., Chapter 6, Lemma 6.6: combined concrete matrix
    `p = 2` absolute-value chain
    `||A||_2 <= || |A| ||_2 <= sqrt(rank A) * ||A||_2`. -/
theorem complexMatrixLpNormOfReal_two_absMatrix_bounds
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A ≤
        complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) (complexAbsMatrix A) ∧
      complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) (complexAbsMatrix A) ≤
        Real.sqrt (complexMatrixRank A : ℝ) *
          complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A := by
  exact ⟨complexMatrixLpNormOfReal_two_le_absMatrix hn A,
    complexMatrixLpNormOfReal_two_absMatrix_le_sqrt_rank_mul hn A⟩

/-- Source-facing predicate for the row/column-sum part of a real magic-square
    matrix. The permutation of the integers `1, ..., n^2` is not needed for the
    induced-norm theorem; nonnegative entries and common row/column sums are the
    mathematical content used in Higham Problem 6.4's norm identity. -/
def IsRealMagicSquareWithSum {n : Nat}
    (A : Fin n -> Fin n -> Real) (mu : Real) : Prop :=
  (forall i j, 0 <= A i j) /\
    (forall i, (Finset.univ.sum (fun j : Fin n => A i j)) = mu) /\
      (forall j, (Finset.univ.sum (fun i : Fin n => A i j)) = mu)

lemma IsRealMagicSquareWithSum.mu_nonneg {n : Nat} (hn : 0 < n)
    {A : Fin n -> Fin n -> Real} {mu : Real}
    (hA : IsRealMagicSquareWithSum A mu) :
    0 <= mu := by
  let j0 : Fin n := ⟨0, hn⟩
  rw [← hA.2.2 j0]
  exact Finset.sum_nonneg (fun i _hi => hA.1 i j0)

/-- A real magic-square row/column-sum matrix has complexified matrix 1-norm
    equal to its common sum. -/
lemma IsRealMagicSquareWithSum.complexMatrixOneNorm_eq {n : Nat} (hn : 0 < n)
    {A : Fin n -> Fin n -> Real} {mu : Real}
    (hA : IsRealMagicSquareWithSum A mu) :
    complexMatrixOneNorm (realRectToCMatrix A) = mu := by
  have hmu : 0 <= mu := hA.mu_nonneg hn
  apply le_antisymm
  · apply complexMatrixOneNorm_le_of_col_sum_le hmu
    intro j
    have hsum :
        (Finset.univ.sum (fun i : Fin n => ‖realRectToCMatrix A i j‖))
          = Finset.univ.sum (fun i : Fin n => A i j) := by
            apply Finset.sum_congr rfl
            intro i _hi
            change ‖((A i j : Real) : Complex)‖ = A i j
            exact complexNorm_ofReal_of_nonneg (hA.1 i j)
    exact le_of_eq (hsum.trans (hA.2.2 j))
  · let j0 : Fin n := ⟨0, hn⟩
    have h := complexMatrixOneNorm_col_sum_le (realRectToCMatrix A) j0
    have hsum :
        (Finset.univ.sum (fun i : Fin n => ‖realRectToCMatrix A i j0‖)) = mu := by
      calc
        (Finset.univ.sum (fun i : Fin n => ‖realRectToCMatrix A i j0‖))
            = Finset.univ.sum (fun i : Fin n => A i j0) := by
              apply Finset.sum_congr rfl
              intro i _hi
              change ‖((A i j0 : Real) : Complex)‖ = A i j0
              exact complexNorm_ofReal_of_nonneg (hA.1 i j0)
        _ = mu := hA.2.2 j0
    simpa [hsum] using h

/-- A real magic-square row/column-sum matrix has complexified matrix
    infinity-norm equal to its common sum. -/
lemma IsRealMagicSquareWithSum.complexMatrixInfNorm_eq {n : Nat} (hn : 0 < n)
    {A : Fin n -> Fin n -> Real} {mu : Real}
    (hA : IsRealMagicSquareWithSum A mu) :
    complexMatrixInfNorm (realRectToCMatrix A) = mu := by
  have hmu : 0 <= mu := hA.mu_nonneg hn
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le hmu
    intro i
    have hsum :
        (Finset.univ.sum (fun j : Fin n => ‖realRectToCMatrix A i j‖))
          = Finset.univ.sum (fun j : Fin n => A i j) := by
            apply Finset.sum_congr rfl
            intro j _hi
            change ‖((A i j : Real) : Complex)‖ = A i j
            exact complexNorm_ofReal_of_nonneg (hA.1 i j)
    exact le_of_eq (hsum.trans (hA.2.1 i))
  · let i0 : Fin n := ⟨0, hn⟩
    have h := complexMatrixInfNorm_row_sum_le (realRectToCMatrix A) i0
    have hsum :
        (Finset.univ.sum (fun j : Fin n => ‖realRectToCMatrix A i0 j‖)) = mu := by
      calc
        (Finset.univ.sum (fun j : Fin n => ‖realRectToCMatrix A i0 j‖))
            = Finset.univ.sum (fun j : Fin n => A i0 j) := by
              apply Finset.sum_congr rfl
              intro j _hi
              change ‖((A i0 j : Real) : Complex)‖ = A i0 j
              exact complexNorm_ofReal_of_nonneg (hA.1 i0 j)
        _ = mu := hA.2.1 i0
    simpa [hsum] using h

lemma IsRealMagicSquareWithSum.complexMatrixVecMul_const_one {n : Nat}
    {A : Fin n -> Fin n -> Real} {mu : Real}
    (hA : IsRealMagicSquareWithSum A mu) :
    complexMatrixVecMul (realRectToCMatrix A) (fun _ : Fin n => (1 : Complex)) =
      complexVecSMul (mu : Complex) (fun _ : Fin n => (1 : Complex)) := by
  ext i
  calc
    complexMatrixVecMul (realRectToCMatrix A) (fun _ : Fin n => (1 : Complex)) i
        = (Finset.univ.sum (fun j : Fin n => ((A i j : Real) : Complex))) := by
          simp [complexMatrixVecMul, realRectToCMatrix]
    _ = ((Finset.univ.sum (fun j : Fin n => A i j)) : Complex) := by
          exact_mod_cast rfl
    _ = (mu : Complex) := by
          exact_mod_cast hA.2.1 i
    _ = complexVecSMul (mu : Complex) (fun _ : Fin n => (1 : Complex)) i := by
          simp [complexVecSMul]

/-- Higham Problem 6.4, finite-real `p` form: a real magic-square
    row/column-sum matrix has induced complex matrix `p`-norm equal to its
    common magic sum. -/
theorem IsRealMagicSquareWithSum.complexMatrixLpNormOfReal_eq {n : Nat}
    (hn : 0 < n) {p : Real} (hp : 1 <= p)
    {A : Fin n -> Fin n -> Real} {mu : Real}
    (hmu_pos : 0 < mu)
    (hA : IsRealMagicSquareWithSum A mu) :
    complexMatrixLpNormOfReal hn p hp (realRectToCMatrix A) = mu := by
  let C : CMatrix n n := realRectToCMatrix A
  have hone : complexMatrixOneNorm C = mu := by
    simpa [C] using hA.complexMatrixOneNorm_eq hn
  have hinf : complexMatrixInfNorm C = mu := by
    simpa [C] using hA.complexMatrixInfNorm_eq hn
  have hupper := complexMatrixLpNormOfReal_rieszThorin_one_top
    (m := n) (n := n) hn hp C
  have hgeom : mu ^ p⁻¹ * mu ^ (1 - p⁻¹) = mu := by
    have hpow := Real.rpow_add hmu_pos p⁻¹ (1 - p⁻¹)
    rw [hpow.symm]
    have hsum : p⁻¹ + (1 - p⁻¹) = (1 : Real) := by ring
    rw [hsum, Real.rpow_one]
  have hupper_mu : complexMatrixLpNormOfReal hn p hp C <= mu := by
    simpa [hone, hinf, hgeom] using hupper
  have hd : IsComplexMatrixLpNormValue (ENNReal.ofReal p) C
      (complexMatrixLpNormOfReal hn p hp C) :=
    complexMatrixLpNormOfReal_isComplexMatrixLpNormValue hn p hp C
  haveI : Fact (1 <= ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  let one : CVec n := fun _ : Fin n => (1 : Complex)
  have hone_map :
      complexMatrixVecMul C one = complexVecSMul (mu : Complex) one := by
    simpa [C, one] using hA.complexMatrixVecMul_const_one
  have hnu_nonneg :
      0 <= complexVecLpNorm (n := n) (ENNReal.ofReal p) one :=
    (complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal p)).nonneg one
  have hnu_ne :
      complexVecLpNorm (n := n) (ENNReal.ofReal p) one ≠ 0 := by
    intro hzero
    have hone_zero :=
      ((complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal p)).eq_zero_iff one).mp
        hzero
    exact complexVecConstOne_ne_zero hn hone_zero
  have hnu_pos :
      0 < complexVecLpNorm (n := n) (ENNReal.ofReal p) one :=
    lt_of_le_of_ne hnu_nonneg (Ne.symm hnu_ne)
  have hlower_raw := hd.1 one
  have hlower_scaled :
      mu * complexVecLpNorm (n := n) (ENNReal.ofReal p) one <=
        complexMatrixLpNormOfReal hn p hp C *
          complexVecLpNorm (n := n) (ENNReal.ofReal p) one := by
    calc
      mu * complexVecLpNorm (n := n) (ENNReal.ofReal p) one
          = complexVecLpNorm (n := n) (ENNReal.ofReal p) (complexMatrixVecMul C one) := by
            have hsmul :=
              (complexVecLpNorm_isComplexVectorNorm (n := n) (ENNReal.ofReal p)).smul
                (mu : Complex) one
            rw [hone_map, hsmul]
            rw [complexNorm_ofReal_of_nonneg hmu_pos.le]
      _ <= complexMatrixLpNormOfReal hn p hp C *
            complexVecLpNorm (n := n) (ENNReal.ofReal p) one := hlower_raw
  have hlower : mu <= complexMatrixLpNormOfReal hn p hp C := by
    exact (mul_le_mul_iff_of_pos_right hnu_pos).mp hlower_scaled
  exact le_antisymm hupper_mu hlower

/-- Higham Problem 6.4, `p = infinity` endpoint in the local concrete API. -/
theorem IsRealMagicSquareWithSum.complexMatrixInfNorm_endpoint_eq {n : Nat}
    (hn : 0 < n) {A : Fin n -> Fin n -> Real} {mu : Real}
    (hA : IsRealMagicSquareWithSum A mu) :
    complexMatrixInfNorm (realRectToCMatrix A) = mu :=
  hA.complexMatrixInfNorm_eq hn

/-- Higham, 2nd ed., Chapter 6, Lemma 6.6: rank-sensitive absolute-matrix
    bound transported to the older real rectangular operator-bound predicate.

If `||A x||_2 <= c ||x||_2` for every real vector `x`, then
`|| |A| x||_2 <= sqrt(rank A) * c * ||x||_2`, where `rank A` is the rank of
the complexification. -/
theorem rectOpNorm2Le_absMatrixRect_sqrt_rank_mul_of_rectOpNorm2Le
    {m n : Nat} (hn : 0 < n) (A : Fin m -> Fin n -> Real) {c : Real}
    (hc : 0 <= c) (hA : rectOpNorm2Le A c) :
    rectOpNorm2Le (absMatrixRect A)
      (Real.sqrt (realRectMatrixRank A : Real) * c) := by
  have hcomplex :
      complexMatrixOp2 (realRectToCMatrix A) <= c :=
    complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le A hc hA
  have hAbs :=
    complexMatrixOp2_absMatrix_le_sqrt_rank_mul_complexMatrixOp2
      hn (realRectToCMatrix A)
  have hscaled :
      complexMatrixOp2 (complexAbsMatrix (realRectToCMatrix A)) <=
        Real.sqrt (realRectMatrixRank A : Real) * c := by
    simpa [realRectMatrixRank] using
      hAbs.trans
        (mul_le_mul_of_nonneg_left hcomplex (Real.sqrt_nonneg _))
  have hrealAbs :
      complexMatrixOp2 (realRectToCMatrix (absMatrixRect A)) <=
        Real.sqrt (realRectMatrixRank A : Real) * c := by
    simpa [realRectToCMatrix_absMatrixRect A] using hscaled
  exact rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le
    (absMatrixRect A) hrealAbs

/-- Entrywise conjugation preserves finite real-exponent local matrix `p`-norm
    values. -/
theorem complexConjMatrixLpNormValue {m n : ℕ} {p d : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d) :
    IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexConjMatrix A) d := by
  let νsrc : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let νtgt : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  have hA_mixed : IsMixedSubordinateMatrixNormValue νsrc νtgt A d := by
    simpa [νsrc, νtgt, IsComplexMatrixLpNormValue] using hA
  have hsrc_conj : ∀ x : CVec n, νsrc (complexConjVec x) = νsrc x := by
    intro x
    simpa [νsrc] using
      complexVecLpNorm_ofReal_conj_eq (n := n) (p := p)
        (lt_of_lt_of_le zero_lt_one hp) x
  have htgt_conj : ∀ y : CVec m, νtgt (complexConjVec y) = νtgt y := by
    intro y
    simpa [νtgt] using
      complexVecLpNorm_ofReal_conj_eq (n := m) (p := p)
        (lt_of_lt_of_le zero_lt_one hp) y
  change IsMixedSubordinateMatrixNormValue νsrc νtgt (complexConjMatrix A) d
  constructor
  case left =>
    intro x
    calc
      νtgt (complexMatrixVecMul (complexConjMatrix A) x)
          = νtgt (complexConjVec (complexMatrixVecMul A (complexConjVec x))) := by
              rw [complexMatrixVecMul_conjMatrix]
      _ = νtgt (complexMatrixVecMul A (complexConjVec x)) := htgt_conj _
      _ ≤ d * νsrc (complexConjVec x) := hA_mixed.1 _
      _ = d * νsrc x := by rw [hsrc_conj x]
  case right =>
    intro e he
    apply hA_mixed.2 e
    intro x
    have h := he (complexConjVec x)
    calc
      νtgt (complexMatrixVecMul A x)
          = νtgt (complexConjVec
              (complexMatrixVecMul (complexConjMatrix A) (complexConjVec x))) := by
              rw [complexMatrixVecMul_conjMatrix]
              simp [complexConjVec_involutive]
      _ = νtgt (complexMatrixVecMul (complexConjMatrix A) (complexConjVec x)) :=
          htgt_conj _
      _ ≤ e * νsrc (complexConjVec x) := h
      _ = e * νsrc x := by rw [hsrc_conj x]

/-- Bound half of Higham equation (6.21), finite real-exponent local form:
    a `q`-norm value for `A` is a `p`-bound for `A^T` under Holder
    conjugacy. -/
theorem complexMatrixTransposeLpNorm_mixedBound
    {m n : ℕ} (hn : 0 < n) {p q d : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix m n}
    (hAq : IsComplexMatrixLpNormValue (ENNReal.ofReal q) A d) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := m) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexMatrixTranspose A) d := by
  intro y
  have hqfact : 1 ≤ ENNReal.ofReal q := by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.symm.lt
  have hpfact : 1 ≤ ENNReal.ofReal p := by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt
  letI : Fact (1 ≤ ENNReal.ofReal q) := ⟨hqfact⟩
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨hpfact⟩
  have hAq_mixed : IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal q))
        (complexVecLpNorm (n := m) (ENNReal.ofReal q)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hAq
  have hq_src : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal q)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal q)
  have hq_tgt : IsComplexVectorNorm
      (complexVecLpNorm (n := m) (ENNReal.ofReal q)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal q)
  have hd_nonneg : 0 ≤ d :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hq_src hq_tgt hAq_mixed
  let E : ℝ := d * complexVecLpNorm (ENNReal.ofReal p) y
  have hp_tgt : IsComplexVectorNorm
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hE_nonneg : 0 ≤ E := mul_nonneg hd_nonneg (hp_tgt.nonneg y)
  have hbound : ∀ x : CVec n,
      ‖∑ j : Fin n, complexMatrixVecMul (complexMatrixTranspose A) y j * x j‖ ≤
        E * complexVecLpNorm (ENNReal.ofReal q) x := by
    intro x
    calc
      ‖∑ j : Fin n, complexMatrixVecMul (complexMatrixTranspose A) y j * x j‖
          = ‖∑ i : Fin m, y i * complexMatrixVecMul A x i‖ := by
              rw [complexMatrixTranspose_pairing A x y]
      _ ≤ complexVecLpNorm (ENNReal.ofReal p) y *
            complexVecLpNorm (ENNReal.ofReal q) (complexMatrixVecMul A x) := by
            simpa using complexVecLpNorm_holder hpq.symm
              (fun i : Fin m => y i) (complexMatrixVecMul A x)
      _ ≤ complexVecLpNorm (ENNReal.ofReal p) y *
            (d * complexVecLpNorm (ENNReal.ofReal q) x) := by
            exact mul_le_mul_of_nonneg_left (hAq_mixed.1 x) (hp_tgt.nonneg y)
      _ = E * complexVecLpNorm (ENNReal.ofReal q) x := by
            dsimp [E]
            ring
  exact complexVecLpNorm_le_of_rowFunctional_bound
      (n := n) (p := q) (q := p) hpq.symm
      (fun j : Fin n => complexMatrixVecMul (complexMatrixTranspose A) y j)
      hE_nonneg hbound

/-- Least-value inequality corresponding to the transpose half of Higham
    equation (6.21). -/
theorem complexMatrixTransposeLpNormValue_le
    {m n : ℕ} (hn : 0 < n) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix m n}
    (hAq : IsComplexMatrixLpNormValue (ENNReal.ofReal q) A d)
    (hATp : IsComplexMatrixLpNormValue (ENNReal.ofReal p)
      (complexMatrixTranspose A) e) :
    e ≤ d := by
  have hATp_mixed : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := m) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexMatrixTranspose A) e := by
    simpa [IsComplexMatrixLpNormValue] using hATp
  exact hATp_mixed.2 d (complexMatrixTransposeLpNorm_mixedBound hn hpq hAq)

/-- Higham, 2nd ed., Chapter 6, equation (6.21), transpose version for finite
    real Holder-conjugate exponents in the local matrix p-norm value API. -/
theorem complexMatrixTransposeLpNormValue_eq
    {m n : ℕ} (hn : 0 < n) (hm : 0 < m) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix m n}
    (hAq : IsComplexMatrixLpNormValue (ENNReal.ofReal q) A d)
    (hATp : IsComplexMatrixLpNormValue (ENNReal.ofReal p)
      (complexMatrixTranspose A) e) :
    e = d := by
  have hle : e ≤ d := complexMatrixTransposeLpNormValue_le hn hpq hAq hATp
  have hAq' : IsComplexMatrixLpNormValue (ENNReal.ofReal q)
        (complexMatrixTranspose (complexMatrixTranspose A)) d := by
    simpa using hAq
  have hge : d ≤ e :=
    complexMatrixTransposeLpNormValue_le (m := n) (n := m) (hn := hm)
      (p := q) (q := p) (d := e) (e := d) hpq.symm hATp hAq'
  exact le_antisymm hle hge

/-- Higham, 2nd ed., Chapter 6, equation (6.21), finite real-exponent local
    form: for Holder-conjugate exponents, `||A^*||_p = ||A||_q`. -/
theorem complexMatrixAdjointLpNormValue_eq
    {m n : ℕ} (hn : 0 < n) (hm : 0 < m) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix m n}
    (hAq : IsComplexMatrixLpNormValue (ENNReal.ofReal q) A d)
    (hAdjp : IsComplexMatrixLpNormValue (ENNReal.ofReal p)
      (complexMatrixAdjoint A) e) :
    e = d := by
  have hq_ge : 1 ≤ q := le_of_lt hpq.symm.lt
  have hConjAq : IsComplexMatrixLpNormValue (ENNReal.ofReal q)
      (complexConjMatrix A) d :=
    complexConjMatrixLpNormValue hq_ge hAq
  exact complexMatrixTransposeLpNormValue_eq (m := m) (n := n)
    hn hm hpq hConjAq hAdjp

/-- General lower-bound half of Higham equation (6.12): any genuine mixed
    subordinate `p -> p` matrix norm value bounds the `L^p` norm of every
    column.  The concrete p-norm value can later be supplied by the full matrix
    p-norm API. -/
theorem complexMatrixLpNorm_column_lpNorm_le_of_mixedSubordinateMatrixNormValue
    {m n : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] {A : CMatrix m n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A d)
    (j : Fin n) :
    complexVecLpNorm p (fun i : Fin m => A i j) ≤ d := by
  have h := hA.1 (standardBasisCVec j)
  rw [complexMatrixVecMul_standardBasisCVec A j,
    complexVecLpNorm_standardBasisCVec p j, mul_one] at h
  exact h

/-- General lower-bound half of Higham equation (6.13), for finite conjugate
    exponents: any genuine mixed subordinate `p -> p` matrix norm value bounds
    the finite `L^q` norm of every row. -/
theorem complexMatrixLpNorm_row_dualLpNorm_le_of_mixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d)
    (i : Fin m) :
    complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j) ≤ d := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  have hsrc : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have htgt : IsComplexVectorNorm
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hd_nonneg : 0 ≤ d := by
    obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hsrc hn
    have h := hA.1 u
    rw [hu, mul_one] at h
    exact (htgt.nonneg (complexMatrixVecMul A u)).trans h
  refine complexVecLpNorm_le_of_rowFunctional_bound hpq
    (fun j : Fin n => A i j) hd_nonneg ?_
  intro x
  calc
    ‖∑ j : Fin n, A i j * x j‖
        = ‖complexMatrixRowFunctional A i x‖ := by
            rw [complexMatrixRowFunctional_apply]
    _ = ‖complexMatrixVecMul A x i‖ := rfl
    _ ≤ complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x) :=
        complexVecLpNorm_coord_le (ENNReal.ofReal p) (complexMatrixVecMul A x) i
    _ ≤ d * complexVecLpNorm (ENNReal.ofReal p) x := hA.1 x

/-- General lower-bound half of Higham Problem 6.14, equation (6.24), packaged
    as a row maximum: the maximum row `L^q` norm is bounded by any local
    `p -> p` subordinate matrix norm value. -/
theorem complexMatrixRowDualMaxLpNorm_le_of_mixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d) :
    complexMatrixRowDualMaxNorm
      (fun i : Fin m =>
        complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) ≤ d := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.symm.lt⟩
  let νn : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let νm : CVec m → ℝ := complexVecLpNorm (n := m) (ENNReal.ofReal p)
  have hνn : IsComplexVectorNorm νn :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hνm : IsComplexVectorNorm νm :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hd_nonneg : 0 ≤ d :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hνn hνm hA
  apply complexMatrixRowDualMaxNorm_le_of_row_le
  · intro i
    unfold complexVecLpNorm
    exact norm_nonneg
      (WithLp.toLp (ENNReal.ofReal q) (fun j : Fin n => A i j))
  · exact hd_nonneg
  · intro i
    exact complexMatrixLpNorm_row_dualLpNorm_le_of_mixedSubordinateMatrixNormValue
      (m := m) (n := n) hn hpq hA i

/-- Source-facing lower half of Higham equation (6.12): a local matrix
    `p`-norm value bounds the maximum finite `L^p` norm of the columns. -/
theorem complexMatrixColumnMaxLpNorm_le_of_complexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    {A : CMatrix m n} {d : ℝ}
    (hA : IsComplexMatrixLpNormValue p A d) :
    complexMatrixColumnMaxVectorNorm
      (complexVecLpNorm (n := m) p) A ≤ d := by
  have hνn : IsComplexVectorNorm (complexVecLpNorm (n := n) p) :=
    complexVecLpNorm_isComplexVectorNorm p
  have hνm : IsComplexVectorNorm (complexVecLpNorm (n := m) p) :=
    complexVecLpNorm_isComplexVectorNorm p
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) p) (complexVecLpNorm (n := m) p) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  have hd_nonneg : 0 ≤ d :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hνn hνm hA_mixed
  exact complexMatrixColumnMaxVectorNorm_le_of_col_le hνm hd_nonneg
    (fun j =>
      complexMatrixLpNorm_column_lpNorm_le_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) p hA_mixed j)

/-- Source-facing form of Higham equation (6.12): a local matrix `p`-norm
    value is squeezed between the maximum column `L^p` norm and the standard
    finite-dimensional upper comparison factor. -/
theorem complexMatrixLpNormValue_columnMax_bounds
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} {d : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d) :
    complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A ≤ d ∧
      d ≤
        (n : ℝ) ^ (1 - p⁻¹) *
          complexMatrixColumnMaxVectorNorm
            (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  exact
    ⟨complexMatrixColumnMaxLpNorm_le_of_complexMatrixLpNormValue
        (m := m) (n := n) hn (ENNReal.ofReal p) hA,
      complexMatrixLpNorm_le_card_rpow_mul_columnMax_lpNorm_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) (p := p) hp hA_mixed⟩

/-- Source-facing sparse-row bounds in Higham Problem 6.14, equation (6.23):
    if every row has at most `μ` nonzeros, then a local matrix `p`-norm value is
    squeezed between the maximum column `L^p` norm and the sparse-row upper
    factor. -/
theorem complexMatrixLpNormValue_sparseRows_bounds
    {m n μ : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} {d : ℝ}
    (hrows : complexMatrixRowsSupportCardLe A μ)
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d) :
    complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A ≤ d ∧
      d ≤
        (μ : ℝ) ^ (1 - p⁻¹) *
          complexMatrixColumnMaxVectorNorm
            (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  exact
    ⟨complexMatrixColumnMaxLpNorm_le_of_complexMatrixLpNormValue
        (m := m) (n := n) hn (ENNReal.ofReal p) hA,
      complexMatrixLpNorm_le_sparseRows_rpow_mul_columnMax_lpNorm_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) (μ := μ) hp hrows hA_mixed⟩

/-- Source-facing sparse-column bounds in Higham Problem 6.14, equation (6.24):
    if every column has at most `μ` nonzeros, then a local matrix `p`-norm value
    is squeezed between the maximum row `L^q` norm and the sparse-column upper
    factor. -/
theorem complexMatrixLpNormValue_sparseColumns_bounds
    {m n μ : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} {d : ℝ}
    (hcols : complexMatrixColumnsSupportCardLe A μ)
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d) :
    complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) ≤ d ∧
      d ≤
        (μ : ℝ) ^ p⁻¹ *
          complexMatrixRowDualMaxNorm
            (fun i : Fin m =>
              complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  exact
    ⟨complexMatrixRowDualMaxLpNorm_le_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) hn hpq hA_mixed,
      complexMatrixLpNorm_le_sparseColumns_rpow_mul_rowDualMax_lpNorm_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) (μ := μ) hpq hcols hA_mixed⟩

/-- Equation (6.11), p = 1 upper-bound form:
    the maximum absolute column sum bounds the matrix action induced by the
    complex vector 1-norm. -/
theorem complexMatrixOneNorm_mixedSubordinateMatrixBound
    {m n : ℕ} (A : CMatrix m n) :
    MixedSubordinateMatrixBound complexVecOneNorm complexVecOneNorm A
      (complexMatrixOneNorm A) := by
  intro x
  unfold complexVecOneNorm complexMatrixVecMul
  calc
    (∑ i : Fin m, ‖∑ j : Fin n, A i j * x j‖)
        ≤ ∑ i : Fin m, ∑ j : Fin n, ‖A i j * x j‖ := by
          apply Finset.sum_le_sum
          intro i _
          exact norm_sum_le _ _
    _ = ∑ i : Fin m, ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          exact norm_mul (A i j) (x j)
    _ = ∑ j : Fin n, ∑ i : Fin m, ‖A i j‖ * ‖x j‖ := by
          rw [Finset.sum_comm]
    _ = ∑ j : Fin n, (∑ i : Fin m, ‖A i j‖) * ‖x j‖ := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ ≤ ∑ j : Fin n, complexMatrixOneNorm A * ‖x j‖ := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right
            (complexMatrixOneNorm_col_sum_le A j) (norm_nonneg (x j))
    _ = complexMatrixOneNorm A * ∑ j : Fin n, ‖x j‖ := by
          rw [Finset.mul_sum]

/-- Equation (6.11), p = 1: for nonempty source dimension, the maximum
    absolute column sum is the least mixed subordinate bound induced by the
    complex vector 1-norm. -/
theorem complexMatrixOneNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMixedSubordinateMatrixNormValue complexVecOneNorm complexVecOneNorm A
      (complexMatrixOneNorm A) := by
  refine ⟨complexMatrixOneNorm_mixedSubordinateMatrixBound A, ?_⟩
  intro d hd
  have hd_nonneg : 0 ≤ d := by
    let j0 : Fin n := ⟨0, hn⟩
    have h := hd (standardBasisCVec j0)
    rw [complexMatrixVecMul_standardBasisCVec A j0,
      complexVecOneNorm_standardBasisCVec j0, mul_one] at h
    exact (Finset.sum_nonneg (fun i _ => norm_nonneg (A i j0))).trans h
  apply complexMatrixOneNorm_le_of_col_sum_le hd_nonneg
  intro j
  have h := hd (standardBasisCVec j)
  rw [complexMatrixVecMul_standardBasisCVec A j,
    complexVecOneNorm_standardBasisCVec j, mul_one] at h
  exact h

/-- Equation (6.11), p = infinity upper-bound form:
    the maximum absolute row sum bounds the matrix action induced by the
    complex vector infinity norm. -/
theorem complexMatrixInfNorm_mixedSubordinateMatrixBound
    {m n : ℕ} (A : CMatrix m n) :
    MixedSubordinateMatrixBound complexVecInfNorm complexVecInfNorm A
      (complexMatrixInfNorm A) := by
  intro x
  apply complexVecInfNorm_le_of_coord_le
  · exact mul_nonneg (complexMatrixInfNorm_nonneg A) (complexVecInfNorm_nonneg x)
  · intro i
    calc
      ‖complexMatrixVecMul A x i‖
          = ‖∑ j : Fin n, A i j * x j‖ := rfl
      _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ := by
            apply Finset.sum_congr rfl
            intro j _
            exact norm_mul (A i j) (x j)
      _ ≤ ∑ j : Fin n, ‖A i j‖ * complexVecInfNorm x := by
            apply Finset.sum_le_sum
            intro j _
            exact mul_le_mul_of_nonneg_left
              (complexVecInfNorm_coord_le x j) (norm_nonneg (A i j))
      _ = (∑ j : Fin n, ‖A i j‖) * complexVecInfNorm x := by
            rw [Finset.sum_mul]
      _ ≤ complexMatrixInfNorm A * complexVecInfNorm x :=
            mul_le_mul_of_nonneg_right
              (complexMatrixInfNorm_row_sum_le A i) (complexVecInfNorm_nonneg x)

/-- Equation (6.11), p = infinity: for nonempty source dimension, the maximum
    absolute row sum is the least mixed subordinate bound induced by the
    complex vector infinity norm. -/
theorem complexMatrixInfNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsMixedSubordinateMatrixNormValue complexVecInfNorm complexVecInfNorm A
      (complexMatrixInfNorm A) := by
  refine ⟨complexMatrixInfNorm_mixedSubordinateMatrixBound A, ?_⟩
  intro d hd
  have hd_nonneg : 0 ≤ d := by
    obtain ⟨u, hu_unit⟩ :=
      exists_unit_complexVectorNorm complexVecInfNorm_isComplexVectorNorm hn
    have h := hd u
    rw [hu_unit, mul_one] at h
    exact (complexVecInfNorm_nonneg (complexMatrixVecMul A u)).trans h
  apply complexMatrixInfNorm_le_of_row_sum_le hd_nonneg
  intro i
  let x : CVec n := fun j => complexUnitPhase (A i j)
  have hx_le_one : complexVecInfNorm x ≤ 1 := by
    apply complexVecInfNorm_le_of_coord_le _ zero_le_one
    intro j
    exact complexUnitPhase_norm_le_one (A i j)
  have hrow :
      complexMatrixVecMul A x i = (∑ j : Fin n, (‖A i j‖ : ℂ)) := by
    unfold complexMatrixVecMul
    apply Finset.sum_congr rfl
    intro j _
    exact mul_complexUnitPhase_eq_norm (A i j)
  have hsum_cast :
      (∑ j : Fin n, (‖A i j‖ : ℂ)) =
        ((∑ j : Fin n, ‖A i j‖ : ℝ) : ℂ) := by
    norm_num
  have hrow_norm :
      ‖complexMatrixVecMul A x i‖ = ∑ j : Fin n, ‖A i j‖ := by
    have hsum_nonneg : 0 ≤ ∑ j : Fin n, ‖A i j‖ :=
      Finset.sum_nonneg (fun j _ => norm_nonneg (A i j))
    rw [hrow, hsum_cast, Complex.norm_of_nonneg hsum_nonneg]
  calc
    (∑ j : Fin n, ‖A i j‖)
        = ‖complexMatrixVecMul A x i‖ := hrow_norm.symm
    _ ≤ complexVecInfNorm (complexMatrixVecMul A x) :=
        complexVecInfNorm_coord_le (complexMatrixVecMul A x) i
    _ ≤ d * complexVecInfNorm x := hd x
    _ ≤ d * 1 := mul_le_mul_of_nonneg_left hx_le_one hd_nonneg
    _ = d := by ring

/-- The concrete column-sum matrix norm is the local matrix `L^1` norm value. -/
theorem complexMatrixOneNorm_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsComplexMatrixLpNormValue 1 A (complexMatrixOneNorm A) := by
  unfold IsComplexMatrixLpNormValue
  convert complexMatrixOneNorm_isMixedSubordinateMatrixNormValue
    (m := m) (n := n) hn A using 1
  · funext x
    exact complexVecLpNorm_one_eq_complexVecOneNorm x
  · funext x
    exact complexVecLpNorm_one_eq_complexVecOneNorm x

/-- The concrete row-sum matrix norm is the local matrix `L^∞` norm value. -/
theorem complexMatrixInfNorm_isComplexMatrixLpNormValue
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    IsComplexMatrixLpNormValue ∞ A (complexMatrixInfNorm A) := by
  unfold IsComplexMatrixLpNormValue
  convert complexMatrixInfNorm_isMixedSubordinateMatrixNormValue
    (m := m) (n := n) hn A using 1
  · funext x
    exact complexVecLpNorm_infty_eq_complexVecInfNorm x
  · funext x
    exact complexVecLpNorm_infty_eq_complexVecInfNorm x

/-- The chosen endpoint-aware local matrix `L^1` norm is the column-sum norm. -/
theorem complexMatrixLpNorm_one_eq_complexMatrixOneNorm
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    @complexMatrixLpNorm m n hn 1 ⟨le_rfl⟩ A = complexMatrixOneNorm A :=
  complexMatrixLpNorm_eq_of_isComplexMatrixLpNormValue
    (m := m) (n := n) hn (p := 1) (A := A)
    (c := complexMatrixOneNorm A)
    (complexMatrixOneNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn A)

/-- The chosen endpoint-aware local matrix `L^∞` norm is the row-sum norm. -/
theorem complexMatrixLpNorm_top_eq_complexMatrixInfNorm
    {m n : ℕ} (hn : 0 < n) (A : CMatrix m n) :
    @complexMatrixLpNorm m n hn ∞ ⟨le_top⟩ A = complexMatrixInfNorm A :=
  complexMatrixLpNorm_eq_of_isComplexMatrixLpNormValue
    (m := m) (n := n) hn (p := ∞) (A := A)
    (c := complexMatrixInfNorm A)
    (complexMatrixInfNorm_isComplexMatrixLpNormValue (m := m) (n := n) hn A)

/-- Double-endpoint `LpInterpolationData` Riesz-Thorin wrapper for
    `p₀ = 1`, `p₁ = ∞`, stated with the chosen endpoint-aware matrix norm. -/
theorem complexMatrixLpNorm_le_rieszThorin_one_top_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {r θ : ℝ} (hr : 1 ≤ r)
    (hθ : LpInterpolationData 1 ∞ (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact hr⟩ A ≤
      (@complexMatrixLpNorm m n hn 1 ⟨le_rfl⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn ∞ ⟨le_top⟩ A) ^ θ := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_one, lpRecipExp_top, lpRecipExp_ofReal hrpos] at hrec
  have hleft : r⁻¹ = 1 - θ := by linarith
  have hright : 1 - r⁻¹ = θ := by linarith
  have hOne := complexMatrixLpNorm_one_eq_complexMatrixOneNorm
    (m := m) (n := n) hn A
  have hInf := complexMatrixLpNorm_top_eq_complexMatrixInfNorm
    (m := m) (n := n) hn A
  simpa [complexMatrixLpNormOfReal, hleft, hright, hOne, hInf] using
    (complexMatrixLpNormOfReal_rieszThorin_one_top
      (m := m) (n := n) hn (p := r) hr A)

/-- Double-endpoint `LpInterpolationData` Riesz-Thorin wrapper for
    `p₀ = ∞`, `p₁ = 1`, stated with the chosen endpoint-aware matrix norm. -/
theorem complexMatrixLpNorm_le_rieszThorin_top_one_of_interpolationData
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {r θ : ℝ} (hr : 1 ≤ r)
    (hθ : LpInterpolationData ∞ 1 (ENNReal.ofReal r) θ) :
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
        ⟨by rw [ENNReal.one_le_ofReal]; exact hr⟩ A ≤
      (@complexMatrixLpNorm m n hn ∞ ⟨le_top⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn 1 ⟨le_rfl⟩ A) ^ θ := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrec := hθ.reciprocal_eq
  rw [lpRecipExp_top, lpRecipExp_one, lpRecipExp_ofReal hrpos] at hrec
  have hright : r⁻¹ = θ := by linarith
  have hleft : 1 - r⁻¹ = 1 - θ := by linarith
  have hOne := complexMatrixLpNorm_one_eq_complexMatrixOneNorm
    (m := m) (n := n) hn A
  have hInf := complexMatrixLpNorm_top_eq_complexMatrixInfNorm
    (m := m) (n := n) hn A
  calc
    @complexMatrixLpNorm m n hn (ENNReal.ofReal r)
          ⟨by rw [ENNReal.one_le_ofReal]; exact hr⟩ A
        ≤ (@complexMatrixLpNorm m n hn 1 ⟨le_rfl⟩ A) ^ θ *
          (@complexMatrixLpNorm m n hn ∞ ⟨le_top⟩ A) ^ (1 - θ) := by
            simpa [complexMatrixLpNormOfReal, hright, hleft, hOne, hInf] using
              (complexMatrixLpNormOfReal_rieszThorin_one_top
                (m := m) (n := n) hn (p := r) hr A)
    _ = (@complexMatrixLpNorm m n hn ∞ ⟨le_top⟩ A) ^ (1 - θ) *
          (@complexMatrixLpNorm m n hn 1 ⟨le_rfl⟩ A) ^ θ := by
            ring

/-- Closed concrete cases for the source-facing Riesz-Thorin matrix p-norm
    dispatcher.  This records exactly the finite/endpoint cases currently
    proved locally; the strict-interior endpoint-capable analytic case remains
    outside this case data until it is proved. -/
inductive ComplexMatrixLpNormRieszThorinClosedCase :
    ℝ≥0∞ → ℝ≥0∞ → ℝ≥0∞ → ℝ → Prop where
  | finiteReal {p0 q0 p1 q1 r q θ : ℝ}
      (hpq0 : p0.HolderConjugate q0) (hpq1 : p1.HolderConjugate q1)
      (hrq : r.HolderConjugate q)
      (hθ : LpInterpolationData
        (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        (ENNReal.ofReal p0) (ENNReal.ofReal p1) (ENNReal.ofReal r) θ
  | one_top_left {p1 q1 r q θ : ℝ}
      (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
      (hθ : LpInterpolationData 1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        1 (ENNReal.ofReal p1) (ENNReal.ofReal r) θ
  | top_one_left {p1 q1 r q θ : ℝ}
      (hpq1 : p1.HolderConjugate q1) (hrq : r.HolderConjugate q)
      (hθ : LpInterpolationData ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        ∞ (ENNReal.ofReal p1) (ENNReal.ofReal r) θ
  | finite_left_top_one {p0 q0 r q θ : ℝ}
      (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
      (hθ : LpInterpolationData (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        (ENNReal.ofReal p0) ∞ (ENNReal.ofReal r) θ
  | finite_left_one_top {p0 q0 r q θ : ℝ}
      (hpq0 : p0.HolderConjugate q0) (hrq : r.HolderConjugate q)
      (hθ : LpInterpolationData (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        (ENNReal.ofReal p0) 1 (ENNReal.ofReal r) θ
  | theta_zero {p0 p1 r : ℝ≥0∞} {θ : ℝ}
      (hp0case : 1 ≤ p0)
      (hθ : LpInterpolationData p0 p1 r θ) (hθ0 : θ = 0) :
      ComplexMatrixLpNormRieszThorinClosedCase p0 p1 r θ
  | theta_one {p0 p1 r : ℝ≥0∞} {θ : ℝ}
      (hp1case : 1 ≤ p1)
      (hθ : LpInterpolationData p0 p1 r θ) (hθ1 : θ = 1) :
      ComplexMatrixLpNormRieszThorinClosedCase p0 p1 r θ
  | strict_eq_one {p0 p1 r : ℝ≥0∞} {θ : ℝ}
      (hp0case : 1 ≤ p0) (hp1case : 1 ≤ p1)
      (hθ : LpInterpolationData p0 p1 r θ)
      (hθ0 : 0 < θ) (hθ1 : θ < 1) (hrcase : r = 1) :
      ComplexMatrixLpNormRieszThorinClosedCase p0 p1 r θ
  | strict_eq_top {p0 p1 r : ℝ≥0∞} {θ : ℝ}
      (hp0case : 1 ≤ p0) (hp1case : 1 ≤ p1)
      (hθ : LpInterpolationData p0 p1 r θ)
      (hθ0 : 0 < θ) (hθ1 : θ < 1) (hrcase : r = ∞) :
      ComplexMatrixLpNormRieszThorinClosedCase p0 p1 r θ
  | one_top {r θ : ℝ}
      (hrcase : 1 ≤ r)
      (hθ : LpInterpolationData 1 ∞ (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        1 ∞ (ENNReal.ofReal r) θ
  | top_one {r θ : ℝ}
      (hrcase : 1 ≤ r)
      (hθ : LpInterpolationData ∞ 1 (ENNReal.ofReal r) θ) :
      ComplexMatrixLpNormRieszThorinClosedCase
        ∞ 1 (ENNReal.ofReal r) θ

/-- Build closed-case Riesz-Thorin evidence for a finite real target exponent
    from endpoint/finite source-exponent cases. -/
theorem ComplexMatrixLpNormRieszThorinClosedCase.of_endpointFinite_target_ofReal
    {p0 p1 : ℝ≥0∞} {r θ : ℝ}
    (hp0case : LpEndpointFiniteExponentCase p0)
    (hp1case : LpEndpointFiniteExponentCase p1)
    (hr : 1 < r)
    (hθ : LpInterpolationData p0 p1 (ENNReal.ofReal r) θ) :
    ComplexMatrixLpNormRieszThorinClosedCase p0 p1 (ENNReal.ofReal r) θ := by
  cases hp0case with
  | one =>
      cases hp1case with
      | one =>
          exact False.elim
            (LpInterpolationData.false_of_one_one_target_gt_one hr hθ)
      | finite hp1 =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.one_top_left
            (Real.HolderConjugate.conjExponent hp1)
            (Real.HolderConjugate.conjExponent hr) hθ
      | top =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.one_top
            (le_of_lt hr) hθ
  | finite hp0 =>
      cases hp1case with
      | one =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.finite_left_one_top
            (Real.HolderConjugate.conjExponent hp0)
            (Real.HolderConjugate.conjExponent hr) hθ
      | finite hp1 =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.finiteReal
            (Real.HolderConjugate.conjExponent hp0)
            (Real.HolderConjugate.conjExponent hp1)
            (Real.HolderConjugate.conjExponent hr) hθ
      | top =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.finite_left_top_one
            (Real.HolderConjugate.conjExponent hp0)
            (Real.HolderConjugate.conjExponent hr) hθ
  | top =>
      cases hp1case with
      | one =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.top_one
            (le_of_lt hr) hθ
      | finite hp1 =>
          exact ComplexMatrixLpNormRieszThorinClosedCase.top_one_left
            (Real.HolderConjugate.conjExponent hp1)
            (Real.HolderConjugate.conjExponent hr) hθ
      | top =>
          exact False.elim
            (LpInterpolationData.false_of_top_top_target_gt_one hr hθ)

/-- Conservative closed-case evidence generated from the source-facing
    interpolation data and endpoint-aware exponent hypotheses. -/
theorem ComplexMatrixLpNormRieszThorinClosedCase.of_interpolationData
    {p0 p1 r : ℝ≥0∞} {θ : ℝ}
    (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p0 p1 r θ) :
    ComplexMatrixLpNormRieszThorinClosedCase p0 p1 r θ := by
  by_cases hθ_zero : θ = 0
  · exact ComplexMatrixLpNormRieszThorinClosedCase.theta_zero hp0 hθ hθ_zero
  by_cases hθ_one : θ = 1
  · exact ComplexMatrixLpNormRieszThorinClosedCase.theta_one hp1 hθ hθ_one
  have hθ_pos : 0 < θ := lt_of_le_of_ne hθ.theta_nonneg (Ne.symm hθ_zero)
  have hθ_lt_one : θ < 1 := lt_of_le_of_ne hθ.theta_le_one hθ_one
  cases LpEndpointFiniteExponentCase.of_one_le hr with
  | one =>
      exact ComplexMatrixLpNormRieszThorinClosedCase.strict_eq_one
        hp0 hp1 hθ hθ_pos hθ_lt_one rfl
  | finite hr_real =>
      exact ComplexMatrixLpNormRieszThorinClosedCase.of_endpointFinite_target_ofReal
        (LpEndpointFiniteExponentCase.of_one_le hp0)
        (LpEndpointFiniteExponentCase.of_one_le hp1)
        hr_real hθ
  | top =>
      exact ComplexMatrixLpNormRieszThorinClosedCase.strict_eq_top
        hp0 hp1 hθ hθ_pos hθ_lt_one rfl

/-- Conservative Riesz-Thorin dispatcher over the concrete finite/endpoint
    cases that are already proved locally. -/
theorem complexMatrixLpNorm_le_rieszThorin_of_closedCase
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 p1 r : ℝ≥0∞} {θ : ℝ}
    (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) (hr : 1 ≤ r)
    (hcase : ComplexMatrixLpNormRieszThorinClosedCase p0 p1 r θ) :
    @complexMatrixLpNorm m n hn r ⟨hr⟩ A ≤
      (@complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A) ^ θ := by
  cases hcase with
  | finiteReal hpq0 hpq1 hrq hθ =>
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_of_interpolationData
          (m := m) (n := n) (A := A) hn hpq0 hpq1 hrq hθ)
  | one_top_left hpq1 hrq hθ =>
      simpa [ENNReal.ofReal_one] using
        (complexMatrixLpNorm_le_rieszThorin_one_top_left_of_interpolationData
          (m := m) (n := n) (A := A) hn hpq1 hrq hθ)
  | top_one_left hpq1 hrq hθ =>
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_top_one_left_of_interpolationData
          (m := m) (n := n) (A := A) hn hpq1 hrq hθ)
  | finite_left_top_one hpq0 hrq hθ =>
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_finite_left_top_one_of_interpolationData
          (m := m) (n := n) (A := A) hn hpq0 hrq hθ)
  | finite_left_one_top hpq0 hrq hθ =>
      simpa [ENNReal.ofReal_one] using
        (complexMatrixLpNorm_le_rieszThorin_finite_left_one_top_of_interpolationData
          (m := m) (n := n) (A := A) hn hpq0 hrq hθ)
  | theta_zero _hp0case hθ hθ0 =>
      letI hp0Fact : Fact (1 ≤ p0) := ⟨hp0⟩
      have hB0 : HasComplexMatrixLpBound p0 A
          (@complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A) :=
        hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
          (m := m) (n := n) hn
          (@complexMatrixLpNorm_isComplexMatrixLpNormValue
            m n hn p0 ⟨hp0⟩ A)
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_endpoint_theta_zero
          (m := m) (n := n) (A := A) hn
          (M₀ := @complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A)
          (M₁ := @complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A)
          hp0 hr hθ hθ0 hB0)
  | theta_one _hp1case hθ hθ1 =>
      letI hp1Fact : Fact (1 ≤ p1) := ⟨hp1⟩
      have hB1 : HasComplexMatrixLpBound p1 A
          (@complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A) :=
        hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
          (m := m) (n := n) hn
          (@complexMatrixLpNorm_isComplexMatrixLpNormValue
            m n hn p1 ⟨hp1⟩ A)
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_endpoint_theta_one
          (m := m) (n := n) (A := A) hn
          (M₀ := @complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A)
          (M₁ := @complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A)
          hp1 hr hθ hθ1 hB1)
  | strict_eq_one _hp0case _hp1case hθ hθ0 hθ1 hrcase =>
      letI hp0Fact : Fact (1 ≤ p0) := ⟨hp0⟩
      letI hp1Fact : Fact (1 ≤ p1) := ⟨hp1⟩
      have hB0 : HasComplexMatrixLpBound p0 A
          (@complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A) :=
        hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
          (m := m) (n := n) hn
          (@complexMatrixLpNorm_isComplexMatrixLpNormValue
            m n hn p0 ⟨hp0⟩ A)
      have hB1 : HasComplexMatrixLpBound p1 A
          (@complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A) :=
        hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
          (m := m) (n := n) hn
          (@complexMatrixLpNorm_isComplexMatrixLpNormValue
            m n hn p1 ⟨hp1⟩ A)
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_strict_eq_one
          (m := m) (n := n) (A := A) hn
          (M₀ := @complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A)
          (M₁ := @complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A)
          hp0 hp1 hθ hθ0 hθ1 hrcase hB0 hB1)
  | strict_eq_top _hp0case _hp1case hθ hθ0 hθ1 hrcase =>
      letI hp0Fact : Fact (1 ≤ p0) := ⟨hp0⟩
      letI hp1Fact : Fact (1 ≤ p1) := ⟨hp1⟩
      have hB0 : HasComplexMatrixLpBound p0 A
          (@complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A) :=
        hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
          (m := m) (n := n) hn
          (@complexMatrixLpNorm_isComplexMatrixLpNormValue
            m n hn p0 ⟨hp0⟩ A)
      have hB1 : HasComplexMatrixLpBound p1 A
          (@complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A) :=
        hasComplexMatrixLpBound_of_complexMatrixLpNormValue_nonempty
          (m := m) (n := n) hn
          (@complexMatrixLpNorm_isComplexMatrixLpNormValue
            m n hn p1 ⟨hp1⟩ A)
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_strict_eq_top
          (m := m) (n := n) (A := A) hn
          (M₀ := @complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A)
          (M₁ := @complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A)
          hp0 hp1 hθ hθ0 hθ1 hrcase hB0 hB1)
  | one_top hrcase hθ =>
      simpa using
        (complexMatrixLpNorm_le_rieszThorin_one_top_of_interpolationData
          (m := m) (n := n) (A := A) hn hrcase hθ)
  | top_one hrcase hθ =>
      simpa [ENNReal.ofReal_one] using
        (complexMatrixLpNorm_le_rieszThorin_top_one_of_interpolationData
          (m := m) (n := n) (A := A) hn hrcase hθ)

/-- Higham, 2nd ed., Chapter 6, equation (6.18), endpoint-aware source form:
    Riesz-Thorin log-convexity for the local matrix `L^p` norm, with finite
    and endpoint exponents dispatched from `LpInterpolationData`. -/
theorem complexMatrixLpNorm_le_rieszThorin_of_interpolationData_all
    {m n : ℕ} (hn : 0 < n) {A : CMatrix m n}
    {p0 p1 r : ℝ≥0∞} {θ : ℝ}
    (hp0 : 1 ≤ p0) (hp1 : 1 ≤ p1) (hr : 1 ≤ r)
    (hθ : LpInterpolationData p0 p1 r θ) :
    @complexMatrixLpNorm m n hn r ⟨hr⟩ A ≤
      (@complexMatrixLpNorm m n hn p0 ⟨hp0⟩ A) ^ (1 - θ) *
        (@complexMatrixLpNorm m n hn p1 ⟨hp1⟩ A) ^ θ := by
  exact complexMatrixLpNorm_le_rieszThorin_of_closedCase
    (m := m) (n := n) (A := A) hn hp0 hp1 hr
    (ComplexMatrixLpNormRieszThorinClosedCase.of_interpolationData
      hp0 hp1 hr hθ)

/-- Higham, 2nd ed., Chapter 6, Problem 6.11(a), rectangular generalization:
    for the source `1`-norm and any target vector norm `νβ`, the mixed
    subordinate matrix norm is the maximum of the target norms of the columns. -/
theorem complexMatrixColumnMaxVectorNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} {νβ : CVec m → ℝ} (hβ : IsComplexVectorNorm νβ)
    (hn : 0 < n) (A : CMatrix m n) :
    IsMixedSubordinateMatrixNormValue complexVecOneNorm νβ A
      (complexMatrixColumnMaxVectorNorm νβ A) := by
  refine ⟨?_, ?_⟩
  · intro x
    have hsum :
        νβ (fun i : Fin m =>
            ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i) ≤
          ∑ j : Fin n, νβ (complexVecSMul (x j) (fun k : Fin m => A k j)) :=
      hβ.sum_le (fun j : Fin n => complexVecSMul (x j) (fun k : Fin m => A k j))
    have hAx :
        complexMatrixVecMul A x =
          fun i : Fin m =>
            ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i := by
      ext i
      unfold complexMatrixVecMul complexVecSMul
      apply Finset.sum_congr rfl
      intro j _
      ring
    calc
      νβ (complexMatrixVecMul A x)
          = νβ (fun i : Fin m =>
              ∑ j : Fin n, complexVecSMul (x j) (fun k : Fin m => A k j) i) := by
              rw [hAx]
      _ ≤ ∑ j : Fin n, νβ (complexVecSMul (x j) (fun k : Fin m => A k j)) := hsum
      _ = ∑ j : Fin n, ‖x j‖ * νβ (fun i : Fin m => A i j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact hβ.smul (x j) (fun i : Fin m => A i j)
      _ ≤ ∑ j : Fin n, complexMatrixColumnMaxVectorNorm νβ A * ‖x j‖ := by
            apply Finset.sum_le_sum
            intro j _
            have hcol :=
              mul_le_mul_of_nonneg_left
                (complexMatrixColumnMaxVectorNorm_col_le hβ A j) (norm_nonneg (x j))
            simpa [mul_comm, mul_left_comm, mul_assoc] using hcol
      _ = complexMatrixColumnMaxVectorNorm νβ A * ∑ j : Fin n, ‖x j‖ := by
            rw [Finset.mul_sum]
      _ = complexMatrixColumnMaxVectorNorm νβ A * complexVecOneNorm x := by
            rfl
  · intro d hd
    have hd_nonneg : 0 ≤ d := by
      let j0 : Fin n := ⟨0, hn⟩
      have h := hd (standardBasisCVec j0)
      rw [complexMatrixVecMul_standardBasisCVec A j0,
        complexVecOneNorm_standardBasisCVec j0, mul_one] at h
      exact (hβ.nonneg (fun i : Fin m => A i j0)).trans h
    apply complexMatrixColumnMaxVectorNorm_le_of_col_le hβ hd_nonneg
    intro j
    have h := hd (standardBasisCVec j)
    rw [complexMatrixVecMul_standardBasisCVec A j,
      complexVecOneNorm_standardBasisCVec j, mul_one] at h
    exact h

/-- Higham, 2nd ed., Chapter 6, Problem 6.11(b), rectangular generalization:
    for an arbitrary source norm `να` and target infinity norm, the mixed
    subordinate matrix norm is the maximum of the dual norm values of the row
    functionals. -/
theorem complexMatrixRowDualMaxNorm_isMixedSubordinateMatrixNormValue
    {m n : ℕ} {να : CVec n → ℝ} (hα : IsComplexVectorNorm να) (hn : 0 < n)
    (A : CMatrix m n) (drow : Fin m → ℝ)
    (hrow : ∀ i : Fin m,
      IsDualFunctionalNormValue να (complexMatrixRowFunctional A i) (drow i)) :
    IsMixedSubordinateMatrixNormValue να complexVecInfNorm A
      (complexMatrixRowDualMaxNorm drow) := by
  refine ⟨?_, ?_⟩
  · intro x
    apply complexVecInfNorm_le_of_coord_le
    · exact mul_nonneg (complexMatrixRowDualMaxNorm_nonneg drow) (hα.nonneg x)
    · intro i
      calc
        ‖complexMatrixVecMul A x i‖
            = ‖complexMatrixRowFunctional A i x‖ := by rfl
        _ ≤ drow i * να x := (hrow i).bound x
        _ ≤ complexMatrixRowDualMaxNorm drow * να x :=
            mul_le_mul_of_nonneg_right
              (complexMatrixRowDualMaxNorm_row_le hα hn hrow i) (hα.nonneg x)
  · intro d hd
    have hd_nonneg : 0 ≤ d := by
      obtain ⟨u, hu_unit⟩ := exists_unit_complexVectorNorm hα hn
      have h := hd u
      rw [hu_unit, mul_one] at h
      exact (complexVecInfNorm_nonneg (complexMatrixVecMul A u)).trans h
    apply complexMatrixRowDualMaxNorm_le_of_row_le
    · intro i
      exact dualFunctionalNormValue_nonneg_of_nonempty hα hn (hrow i)
    · exact hd_nonneg
    · intro i
      apply (hrow i).least d
      intro x
      calc
        ‖complexMatrixRowFunctional A i x‖
            = ‖complexMatrixVecMul A x i‖ := by rfl
        _ ≤ complexVecInfNorm (complexMatrixVecMul A x) :=
            complexVecInfNorm_coord_le (complexMatrixVecMul A x) i
        _ ≤ d * να x := hd x

/-- General upper-bound half of Higham equation (6.13), as a mixed subordinate
    bound: the matrix acting from finite `L^p` to finite `L^p` is bounded by
    `m^(1/p)` times the maximum finite `L^q` norm of its rows, for finite
    Holder conjugate exponents `p` and `q`. -/
theorem complexMatrixLpNorm_upper_bound_by_rowDualMax_lpNorm
    {m n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : CMatrix m n) :
    MixedSubordinateMatrixBound
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A
      ((m : ℝ) ^ p⁻¹ *
        complexMatrixRowDualMaxNorm
          (fun i : Fin m =>
            complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))) := by
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  let να : CVec n → ℝ := complexVecLpNorm (n := n) (ENNReal.ofReal p)
  let drow : Fin m → ℝ := fun i : Fin m =>
    complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)
  let R : ℝ := complexMatrixRowDualMaxNorm drow
  let c : ℝ := (m : ℝ) ^ p⁻¹
  have hα : IsComplexVectorNorm να :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hrow : ∀ i : Fin m,
      IsDualFunctionalNormValue να (complexMatrixRowFunctional A i) (drow i) := by
    intro i
    simpa [να, drow] using complexMatrixRowFunctional_lpDualValue hn hpq A i
  have hR : MixedSubordinateMatrixBound να complexVecInfNorm A R :=
    (complexMatrixRowDualMaxNorm_isMixedSubordinateMatrixNormValue
      hα hn A drow hrow).1
  have hc_nonneg : 0 ≤ c := Real.rpow_nonneg (Nat.cast_nonneg m) p⁻¹
  intro x
  calc
    complexVecLpNorm (ENNReal.ofReal p) (complexMatrixVecMul A x)
        ≤ c * complexVecInfNorm (complexMatrixVecMul A x) := by
          simpa [c] using
            complexVecLpNorm_le_card_rpow_mul_complexVecInfNorm (n := m)
              (p := p) (le_of_lt hpq.lt) (complexMatrixVecMul A x)
    _ ≤ c * (R * να x) :=
          mul_le_mul_of_nonneg_left (hR x) hc_nonneg
    _ = ((m : ℝ) ^ p⁻¹ *
          complexMatrixRowDualMaxNorm
            (fun i : Fin m =>
              complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j))) *
        complexVecLpNorm (ENNReal.ofReal p) x := by
          simp [c, R, drow, να, mul_assoc]

/-- General upper-bound half of Higham equation (6.13), relative to the local
    least-bound matrix-norm API. -/
theorem complexMatrixLpNorm_le_card_rpow_mul_rowDualMax_lpNorm_of_mixedSubordinateMatrixNormValue
    {m n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} {d : ℝ}
    (hA : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d) :
    d ≤
      (m : ℝ) ^ p⁻¹ *
        complexMatrixRowDualMaxNorm
          (fun i : Fin m =>
            complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) :=
  hA.2 _ (complexMatrixLpNorm_upper_bound_by_rowDualMax_lpNorm hn hpq A)

/-- Source-facing form of Higham equation (6.13): a local matrix `p`-norm
    value is squeezed between the maximum row `L^q` norm and the standard
    finite-dimensional upper comparison factor. -/
theorem complexMatrixLpNormValue_rowDualMax_bounds
    {m n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} {d : ℝ}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d) :
    complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) ≤ d ∧
      d ≤
        (m : ℝ) ^ p⁻¹ *
          complexMatrixRowDualMaxNorm
            (fun i : Fin m =>
              complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  have hA_mixed :
      IsMixedSubordinateMatrixNormValue
        (complexVecLpNorm (n := n) (ENNReal.ofReal p))
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  exact
    ⟨complexMatrixRowDualMaxLpNorm_le_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) hn hpq hA_mixed,
      complexMatrixLpNorm_le_card_rpow_mul_rowDualMax_lpNorm_of_mixedSubordinateMatrixNormValue
        (m := m) (n := n) hn hpq hA_mixed⟩

/-- Column-bound half of Higham Problem 6.15's sharp upper estimate:
    `|| |A| ||_p <= n^(1-1/p) ||A||_p`, finite local form. -/
theorem complexAbsMatrixLpNormValue_le_card_rpow_one_sub_inv_mul_complexMatrixLpNormValue
    {n : ℕ} (hn : 0 < n) {p d e : ℝ} (hp : 1 ≤ p) {A : CMatrix n n}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d)
    (hAbsA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexAbsMatrix A) e) :
    e ≤ (n : ℝ) ^ (1 - p⁻¹) * d := by
  have hp_pos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hc_nonneg : 0 ≤ (n : ℝ) ^ (1 - p⁻¹) :=
    Real.rpow_nonneg (Nat.cast_nonneg n) (1 - p⁻¹)
  have hAbs_col :=
    (complexMatrixLpNormValue_columnMax_bounds (m := n) (n := n) hn hp hAbsA).2
  have hA_col :=
    (complexMatrixLpNormValue_columnMax_bounds (m := n) (n := n) hn hp hA).1
  calc
    e ≤ (n : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := n) (ENNReal.ofReal p)) (complexAbsMatrix A) :=
          hAbs_col
    _ = (n : ℝ) ^ (1 - p⁻¹) *
        complexMatrixColumnMaxVectorNorm
          (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A := by
          rw [complexMatrixColumnMaxLpNorm_absMatrix_eq
            (m := n) (n := n) (p := p) hp_pos A]
    _ ≤ (n : ℝ) ^ (1 - p⁻¹) * d :=
          mul_le_mul_of_nonneg_left hA_col hc_nonneg

/-- Row-dual half of Higham Problem 6.15's sharp upper estimate:
    `|| |A| ||_p <= n^(1/p) ||A||_p`, finite local form. -/
theorem complexAbsMatrixLpNormValue_le_card_rpow_inv_mul_complexMatrixLpNormValue
    {n : ℕ} (hn : 0 < n) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix n n}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d)
    (hAbsA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexAbsMatrix A) e) :
    e ≤ (n : ℝ) ^ p⁻¹ * d := by
  have hc_nonneg : 0 ≤ (n : ℝ) ^ p⁻¹ :=
    Real.rpow_nonneg (Nat.cast_nonneg n) p⁻¹
  have hAbs_row :=
    (complexMatrixLpNormValue_rowDualMax_bounds (m := n) (n := n) hn hpq hAbsA).2
  have hA_row :=
    (complexMatrixLpNormValue_rowDualMax_bounds (m := n) (n := n) hn hpq hA).1
  calc
    e ≤ (n : ℝ) ^ p⁻¹ *
        complexMatrixRowDualMaxNorm
          (fun i : Fin n =>
            complexVecLpNorm (ENNReal.ofReal q)
              (fun j : Fin n => complexAbsMatrix A i j)) :=
          hAbs_row
    _ = (n : ℝ) ^ p⁻¹ *
        complexMatrixRowDualMaxNorm
          (fun i : Fin n =>
            complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
          rw [complexMatrixRowDualMaxLpNorm_absMatrix_eq
            (m := n) (n := n) (q := q) hpq.symm.pos A]
    _ ≤ (n : ℝ) ^ p⁻¹ * d :=
          mul_le_mul_of_nonneg_left hA_row hc_nonneg

/-- Sharp finite local upper estimate in Higham Problem 6.15:
    `|| |A| ||_p <= n^min(1/p, 1-1/p) ||A||_p`. -/
theorem complexAbsMatrixLpNormValue_le_card_rpow_min_inv_mul_complexMatrixLpNormValue
    {n : ℕ} (hn : 0 < n) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix n n}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d)
    (hAbsA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexAbsMatrix A) e) :
    e ≤ (n : ℝ) ^ min p⁻¹ (1 - p⁻¹) * d := by
  have hp : 1 ≤ p := le_of_lt hpq.lt
  have hrow :=
    complexAbsMatrixLpNormValue_le_card_rpow_inv_mul_complexMatrixLpNormValue
      hn hpq hA hAbsA
  have hcol :=
    complexAbsMatrixLpNormValue_le_card_rpow_one_sub_inv_mul_complexMatrixLpNormValue
      hn hp hA hAbsA
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact hp⟩
  have hν : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hA_mixed : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  have hd_nonneg : 0 ≤ d :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hν hν hA_mixed
  have hbase : 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hn
  have hmin_prod :
      min ((n : ℝ) ^ p⁻¹ * d) ((n : ℝ) ^ (1 - p⁻¹) * d) =
        (n : ℝ) ^ min p⁻¹ (1 - p⁻¹) * d := by
    by_cases h : p⁻¹ ≤ 1 - p⁻¹
    · have hpow :
          (n : ℝ) ^ p⁻¹ ≤ (n : ℝ) ^ (1 - p⁻¹) :=
        Real.rpow_le_rpow_of_exponent_le hbase h
      have hprod :
          (n : ℝ) ^ p⁻¹ * d ≤ (n : ℝ) ^ (1 - p⁻¹) * d :=
        mul_le_mul_of_nonneg_right hpow hd_nonneg
      rw [min_eq_left hprod, min_eq_left h]
    · have h' : 1 - p⁻¹ ≤ p⁻¹ := le_of_not_ge h
      have hpow :
          (n : ℝ) ^ (1 - p⁻¹) ≤ (n : ℝ) ^ p⁻¹ :=
        Real.rpow_le_rpow_of_exponent_le hbase h'
      have hprod :
          (n : ℝ) ^ (1 - p⁻¹) * d ≤ (n : ℝ) ^ p⁻¹ * d :=
        mul_le_mul_of_nonneg_right hpow hd_nonneg
      rw [min_eq_right hprod, min_eq_right h']
  calc
    e ≤ min ((n : ℝ) ^ p⁻¹ * d) ((n : ℝ) ^ (1 - p⁻¹) * d) :=
      le_min hrow hcol
    _ = (n : ℝ) ^ min p⁻¹ (1 - p⁻¹) * d := hmin_prod

/-- Finite local form of the two main inequalities in Higham Problem 6.15. -/
theorem complexMatrixLpNormValue_absMatrix_bounds
    {n : ℕ} (hn : 0 < n) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix n n}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d)
    (hAbsA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexAbsMatrix A) e) :
    d ≤ e ∧ e ≤ (n : ℝ) ^ min p⁻¹ (1 - p⁻¹) * d := by
  exact
    ⟨complexMatrixLpNormValue_le_absMatrixLpNormValue (le_of_lt hpq.lt) hA hAbsA,
      complexAbsMatrixLpNormValue_le_card_rpow_min_inv_mul_complexMatrixLpNormValue
        hn hpq hA hAbsA⟩

/-- Final finite local `sqrt n` corollary in Higham Problem 6.15. -/
theorem complexAbsMatrixLpNormValue_le_card_rpow_half_mul_complexMatrixLpNormValue
    {n : ℕ} (hn : 0 < n) {p q d e : ℝ}
    (hpq : p.HolderConjugate q) {A : CMatrix n n}
    (hA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) A d)
    (hAbsA : IsComplexMatrixLpNormValue (ENNReal.ofReal p) (complexAbsMatrix A) e) :
    e ≤ (n : ℝ) ^ ((1 : ℝ) / 2) * d := by
  have hupper :=
    complexAbsMatrixLpNormValue_le_card_rpow_min_inv_mul_complexMatrixLpNormValue
      hn hpq hA hAbsA
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.lt⟩
  have hν : IsComplexVectorNorm
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) :=
    complexVecLpNorm_isComplexVectorNorm (ENNReal.ofReal p)
  have hA_mixed : IsMixedSubordinateMatrixNormValue
      (complexVecLpNorm (n := n) (ENNReal.ofReal p))
      (complexVecLpNorm (n := n) (ENNReal.ofReal p)) A d := by
    simpa [IsComplexMatrixLpNormValue] using hA
  have hd_nonneg : 0 ≤ d :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hν hν hA_mixed
  have hbase : 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hn
  have hmin_le_half : min p⁻¹ (1 - p⁻¹) ≤ (1 : ℝ) / 2 := by
    have hleft := min_le_left p⁻¹ (1 - p⁻¹)
    have hright := min_le_right p⁻¹ (1 - p⁻¹)
    linarith
  have hpow :
      (n : ℝ) ^ min p⁻¹ (1 - p⁻¹) ≤ (n : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hbase hmin_le_half
  exact hupper.trans (mul_le_mul_of_nonneg_right hpow hd_nonneg)

/-- Concrete-function form of Higham equation (6.12): the chosen local matrix
    `p`-norm is squeezed between the maximum column `L^p` norm and the standard
    finite-dimensional upper comparison factor. -/
theorem complexMatrixLpNormOfReal_columnMax_bounds
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) (A : CMatrix m n) :
    complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A ≤
          complexMatrixLpNormOfReal hn p hp A ∧
      complexMatrixLpNormOfReal hn p hp A ≤
        (n : ℝ) ^ (1 - p⁻¹) *
          complexMatrixColumnMaxVectorNorm
            (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A := by
  exact complexMatrixLpNormValue_columnMax_bounds
    (m := m) (n := n) hn hp
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p hp A)

/-- Concrete-function form of Higham equation (6.13): the chosen local matrix
    `p`-norm is squeezed between the maximum row dual `L^q` norm and the
    standard finite-dimensional upper comparison factor. -/
theorem complexMatrixLpNormOfReal_rowDualMax_bounds
    {m n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : CMatrix m n) :
    complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) ≤
          complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A ∧
      complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A ≤
        (m : ℝ) ^ p⁻¹ *
          complexMatrixRowDualMaxNorm
            (fun i : Fin m =>
              complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  exact complexMatrixLpNormValue_rowDualMax_bounds
    (m := m) (n := n) hn hpq
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p (le_of_lt hpq.lt) A)

/-- Concrete-function form of Higham equation (6.16), comparing the chosen
    local matrix `p`-norm with the concrete matrix `1`-norm. -/
theorem complexMatrixLpNormOfReal_oneNorm_equiv_bounds
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) (A : CMatrix n n) :
    complexMatrixOneNorm A / ((n : ℝ) ^ (1 - p⁻¹)) ≤
        complexMatrixLpNormOfReal hn p hp A ∧
      complexMatrixLpNormOfReal hn p hp A ≤
        (n : ℝ) ^ (1 - p⁻¹) * complexMatrixOneNorm A := by
  exact complexMatrixLpNormValue_oneNorm_equiv_bounds
    (n := n) hn hp
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p hp A)

/-- Concrete-function form of Higham equation (6.17), comparing the chosen
    local matrix `p`-norm with the chosen local matrix `2`-norm. -/
theorem complexMatrixLpNormOfReal_twoNorm_equiv_bounds
    {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) (A : CMatrix n n) :
    complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A /
          ((n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹|) ≤
        complexMatrixLpNormOfReal hn p hp A ∧
      complexMatrixLpNormOfReal hn p hp A ≤
        (n : ℝ) ^ |p⁻¹ - (2 : ℝ)⁻¹| *
          complexMatrixLpNormOfReal hn (2 : ℝ) (by norm_num) A := by
  exact complexMatrixLpNormValue_twoNorm_equiv_bounds
    (n := n) hn hp
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p hp A)
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn (2 : ℝ) (by norm_num) A)

/-- Concrete-function form of Higham equation (6.15), comparing the chosen
    local matrix `p`- and `q`-norms. -/
theorem complexMatrixLpNormOfReal_pq_equiv_bounds
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (A : CMatrix n n) :
    complexMatrixLpNormOfReal hn q hq A /
          ((n : ℝ) ^ |p⁻¹ - q⁻¹|) ≤
        complexMatrixLpNormOfReal hn p hp A ∧
      complexMatrixLpNormOfReal hn p hp A ≤
        (n : ℝ) ^ |p⁻¹ - q⁻¹| *
          complexMatrixLpNormOfReal hn q hq A := by
  exact complexMatrixLpNormValue_pq_equiv_bounds
    (n := n) hn hp hq
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p hp A)
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn q hq A)

/-- Concrete-function sparse-row form of Higham Problem 6.14, equation (6.23). -/
theorem complexMatrixLpNormOfReal_sparseRows_bounds
    {m n μ : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {A : CMatrix m n} (hrows : complexMatrixRowsSupportCardLe A μ) :
    complexMatrixColumnMaxVectorNorm
        (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A ≤
          complexMatrixLpNormOfReal hn p hp A ∧
      complexMatrixLpNormOfReal hn p hp A ≤
        (μ : ℝ) ^ (1 - p⁻¹) *
          complexMatrixColumnMaxVectorNorm
            (complexVecLpNorm (n := m) (ENNReal.ofReal p)) A := by
  exact complexMatrixLpNormValue_sparseRows_bounds
    (m := m) (n := n) (μ := μ) hn hp hrows
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p hp A)

/-- Concrete-function sparse-column form of Higham Problem 6.14, equation
    (6.24). -/
theorem complexMatrixLpNormOfReal_sparseColumns_bounds
    {m n μ : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    {A : CMatrix m n} (hcols : complexMatrixColumnsSupportCardLe A μ) :
    complexMatrixRowDualMaxNorm
        (fun i : Fin m =>
          complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) ≤
          complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A ∧
      complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A ≤
        (μ : ℝ) ^ p⁻¹ *
          complexMatrixRowDualMaxNorm
            (fun i : Fin m =>
              complexVecLpNorm (ENNReal.ofReal q) (fun j : Fin n => A i j)) := by
  exact complexMatrixLpNormValue_sparseColumns_bounds
    (m := m) (n := n) (μ := μ) hn hpq hcols
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := m) (n := n) hn p (le_of_lt hpq.lt) A)

/-- Concrete-function finite local form of the main two-sided inequalities in
    Higham Problem 6.15 for entrywise absolute values. -/
theorem complexMatrixLpNormOfReal_absMatrix_bounds
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : CMatrix n n) :
    complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A ≤
        complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) (complexAbsMatrix A) ∧
      complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) (complexAbsMatrix A) ≤
        (n : ℝ) ^ min p⁻¹ (1 - p⁻¹) *
          complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A := by
  exact complexMatrixLpNormValue_absMatrix_bounds
    (n := n) hn hpq
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p (le_of_lt hpq.lt) A)
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p (le_of_lt hpq.lt) (complexAbsMatrix A))

/-- Concrete-function `sqrt n` corollary in Higham Problem 6.15 for entrywise
    absolute values. -/
theorem complexMatrixLpNormOfReal_absMatrix_le_card_rpow_half_mul
    {n : ℕ} (hn : 0 < n) {p q : ℝ} (hpq : p.HolderConjugate q)
    (A : CMatrix n n) :
    complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) (complexAbsMatrix A) ≤
      (n : ℝ) ^ ((1 : ℝ) / 2) *
        complexMatrixLpNormOfReal hn p (le_of_lt hpq.lt) A := by
  exact complexAbsMatrixLpNormValue_le_card_rpow_half_mul_complexMatrixLpNormValue
    (n := n) hn hpq
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p (le_of_lt hpq.lt) A)
    (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
      (m := n) (n := n) hn p (le_of_lt hpq.lt) (complexAbsMatrix A))

/-- The maximum-column-sum norm is an admissible endpoint bound for the local
    source-facing matrix `p = 1` norm predicate. -/
theorem complexMatrixOneNorm_hasComplexMatrixLpBound
    {m n : ℕ} (A : CMatrix m n) :
    HasComplexMatrixLpBound (1 : ℝ≥0∞) A (complexMatrixOneNorm A) := by
  refine ⟨complexMatrixOneNorm_nonneg A, ?_⟩
  intro x
  have h :=
    complexMatrixOneNorm_mixedSubordinateMatrixBound (m := m) (n := n) A x
  simpa [complexVecLpNorm_one_eq_complexVecOneNorm] using h

/-- The maximum-row-sum norm is an admissible endpoint bound for the local
    source-facing matrix `p = infinity` norm predicate. -/
theorem complexMatrixInfNorm_hasComplexMatrixLpBound
    {m n : ℕ} (A : CMatrix m n) :
    HasComplexMatrixLpBound (∞ : ℝ≥0∞) A (complexMatrixInfNorm A) := by
  refine ⟨complexMatrixInfNorm_nonneg A, ?_⟩
  intro x
  have h :=
    complexMatrixInfNorm_mixedSubordinateMatrixBound (m := m) (n := n) A x
  simpa [complexVecLpNorm_infty_eq_complexVecInfNorm] using h

/-- Higham, 2nd ed., Chapter 6, equation (6.20), strict-interior wrapper:
    `||A||_p <= ||A||_1^(2/p - 1) ||A||_2^(2 - 2/p)` for `1 < p <= 2`. -/
theorem complexMatrixLpNormOfReal_rieszThorin_one_two_of_gt_one
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2)
    (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn p (le_of_lt hp1) A ≤
      complexMatrixOneNorm A ^ (2 * p⁻¹ - 1) *
        complexMatrixOp2 A ^ (2 - 2 * p⁻¹) := by
  let q : ℝ := Real.conjExponent p
  let θ : ℝ := 2 - 2 * p⁻¹
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp1
  have hp_pos : 0 < p := zero_lt_one.trans hp1
  haveI hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hp1⟩
  haveI hqFact : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    rw [ENNReal.one_le_ofReal]
    exact le_of_lt hpq.symm.lt⟩
  have hθ0 : 0 ≤ θ := by
    dsimp [θ]
    have hinv_le_one : p⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (le_of_lt hp1)
    nlinarith
  have hθ1 : θ ≤ 1 := by
    dsimp [θ]
    field_simp [hp_pos.ne']
    nlinarith [hp2]
  have hpowX0 : (p * (1 : ℝ)) * (1 : ℝ) = p := by ring
  have hpowX1 : (p * (2 : ℝ)⁻¹) * (2 : ℝ) = p := by ring
  have hpowY1 : (q * (2 : ℝ)⁻¹) * (2 : ℝ) = q := by ring
  have hX : p * ((1 - θ) * (1 : ℝ) + θ * (2 : ℝ)⁻¹) = 1 := by
    dsimp [θ]
    field_simp [hp_pos.ne']
    ring
  have htheta_half : θ * (2 : ℝ)⁻¹ = 1 - p⁻¹ := by
    dsimp [θ]
    ring
  have hq_mul : q * (1 - p⁻¹) = 1 := by
    have hq_inv_eq : q⁻¹ = 1 - p⁻¹ := by
      linarith [hpq.inv_add_inv_eq_one]
    calc
      q * (1 - p⁻¹) = q * q⁻¹ := by rw [hq_inv_eq]
      _ = 1 := by field_simp [hpq.symm.pos.ne']
  have hY : q * ((1 - θ) * (0 : ℝ) + θ * (2 : ℝ)⁻¹) = 1 := by
    calc
      q * ((1 - θ) * (0 : ℝ) + θ * (2 : ℝ)⁻¹) = q * (θ * (2 : ℝ)⁻¹) := by
        ring
      _ = q * (1 - p⁻¹) := by rw [htheta_half]
      _ = 1 := hq_mul
  have hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A (complexMatrixOneNorm A) := by
    simpa using complexMatrixOneNorm_hasComplexMatrixLpBound (m := m) (n := n) A
  have hA1 : HasComplexMatrixLpBound (ENNReal.ofReal (2 : ℝ)) A (complexMatrixOp2 A) :=
    complexMatrixOp2_hasComplexMatrixLpBound A
  have hbound :
      HasComplexMatrixLpBound (ENNReal.ofReal p) A
        (complexMatrixOneNorm A ^ (1 - θ) * complexMatrixOp2 A ^ θ) :=
    hasComplexMatrixLpBound_of_rieszThorin_one_top_finite_right
      (A := A) (p1 := (2 : ℝ)) (q1 := (2 : ℝ))
      (scaleX := p) (leftX := (1 : ℝ)) (rightX := (2 : ℝ)⁻¹)
      (targetX := p)
      (scaleY := q) (rightY := (2 : ℝ)⁻¹)
      (targetY := q)
      (M0 := complexMatrixOneNorm A) (M1 := complexMatrixOp2 A)
      (θ := θ)
      Real.HolderConjugate.two_two hpq.symm
      hpowX0 hpowX1 hpowY1 hX hY
      (le_of_lt hp_pos) zero_le_one (by norm_num)
      (le_of_lt hpq.symm.pos) (by norm_num)
      hθ0 hθ1 hA0 hA1
  have hmain :
      complexMatrixLpNormOfReal hn p (le_of_lt hp1) A ≤
        complexMatrixOneNorm A ^ (1 - θ) * complexMatrixOp2 A ^ θ :=
    isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
      (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
        (m := m) (n := n) hn p (le_of_lt hp1) A)
      hbound
  have hfirst : 1 - θ = 2 * p⁻¹ - 1 := by
    dsimp [θ]
    ring
  rw [hfirst] at hmain
  simpa [θ] using hmain

/-- Higham, 2nd ed., Chapter 6, equation (6.20):
    `||A||_p <= ||A||_1^(2/p - 1) ||A||_2^(2 - 2/p)` for `1 <= p <= 2`. -/
theorem complexMatrixLpNormOfReal_rieszThorin_one_two
    {m n : ℕ} (hn : 0 < n) {p : ℝ} (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (A : CMatrix m n) :
    complexMatrixLpNormOfReal hn p hp1 A ≤
      complexMatrixOneNorm A ^ (2 * p⁻¹ - 1) *
        complexMatrixOp2 A ^ (2 - 2 * p⁻¹) := by
  by_cases hp_eq : p = 1
  · subst p
    have hA0 : HasComplexMatrixLpBound (ENNReal.ofReal (1 : ℝ)) A (complexMatrixOneNorm A) := by
      simpa using complexMatrixOneNorm_hasComplexMatrixLpBound (m := m) (n := n) A
    have hmain :
        complexMatrixLpNormOfReal hn (1 : ℝ) (by norm_num) A ≤ complexMatrixOneNorm A :=
      isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound
        (complexMatrixLpNormOfReal_isComplexMatrixLpNormValue
          (m := m) (n := n) hn (1 : ℝ) (by norm_num) A)
        hA0
    calc
      complexMatrixLpNormOfReal hn (1 : ℝ) hp1 A ≤ complexMatrixOneNorm A := by
        simpa using hmain
      _ = complexMatrixOneNorm A ^ (2 * (1 : ℝ)⁻¹ - 1) *
            complexMatrixOp2 A ^ (2 - 2 * (1 : ℝ)⁻¹) := by
        have hone_exp : 2 * (1 : ℝ)⁻¹ - 1 = (1 : ℝ) := by norm_num
        have hzero_exp : 2 - 2 * (1 : ℝ)⁻¹ = (0 : ℝ) := by norm_num
        rw [hone_exp, hzero_exp, Real.rpow_one, Real.rpow_zero, mul_one]
  · have hp_gt : 1 < p := lt_of_le_of_ne hp1 (Ne.symm hp_eq)
    simpa using
      complexMatrixLpNormOfReal_rieszThorin_one_two_of_gt_one
        (m := m) (n := n) hn hp_gt hp2 A
end NumStability
