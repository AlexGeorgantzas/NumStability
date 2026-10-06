-- Source/Higham/Chapter06/Problem01.lean
--
-- Higham Chapter 6, Problem 6.1 source-facing theorem package.

import NumStability.Analysis.MatrixNorms.Hadamard

/-!
# Higham Chapter 6, Problem 6.1

Formalizes the rank-one witness profiles and sharp norm-quotient entries from
Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., Problem 6.1.
-/

namespace NumStability

open scoped BigOperators
open scoped ComplexOrder
open ENNReal


/-- Source-facing norm-value profile for one of Higham Problem 6.1's
    rank-one witnesses.  The six fields collect the concrete matrix
    `1`, `infinity`, `M`, `S`, `F`, and `2` norm values used to read the
    Table 6.2 sharpness witnesses from the raw Lean theorems. -/
structure HighamProblem61RankOneNormProfile {m n : ℕ} (A : CMatrix m n)
    (oneNorm infNorm maxNorm sumNorm froNorm opTwoNorm : ℝ) : Prop where
  oneNorm_eq : complexMatrixOneNorm A = oneNorm
  infNorm_eq : complexMatrixInfNorm A = infNorm
  entrywiseMax_eq : complexMatrixEntrywiseMaxNorm A = maxNorm
  entrywiseSum_eq : complexMatrixEntrywiseSumNorm A = sumNorm
  frobenius_eq : complexMatrixFrobenius A = froNorm
  opTwo_eq : complexMatrixOp2 A = opTwoNorm

/-- Table-level package for the four rank-one witnesses prescribed in Higham
    Problem 6.1: `e_i e_j^T`, `e e_j^T`, `e_i e^T`, and `e e^T`. -/
structure HighamProblem61RankOneTableProfiles {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) : Prop where
  standard_standard :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      1 1 1 1 1 1
  const_standard :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0))
      (m : ℝ) 1 1 (m : ℝ) (Real.sqrt (m : ℝ)) (Real.sqrt (m : ℝ))
  standard_const :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ)))
      1 (n : ℝ) 1 (n : ℝ) (Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ))
  const_const :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ)))
      (m : ℝ) (n : ℝ) 1 ((m * n : ℕ) : ℝ)
      (Real.sqrt ((m * n : ℕ) : ℝ)) (Real.sqrt ((m * n : ℕ) : ℝ))

/-- Problem 6.1 profile for the `e_i e_j^T` witness. -/
theorem highamProblem61_rankOne_standard_standard_profile {m n : ℕ}
    (i0 : Fin m) (j0 : Fin n) :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact complexMatrixOneNorm_rankOne_standard_standard i0 j0
  · exact complexMatrixInfNorm_rankOne_standard_standard i0 j0
  · exact complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0
  · exact complexMatrixEntrywiseSumNorm_rankOne_standard_standard i0 j0
  · exact complexMatrixFrobenius_rankOne_standard_standard i0 j0
  · exact complexMatrixOp2_rankOne_standard_standard i0 j0

/-- Problem 6.1 profile for the column witness `e e_j^T`. -/
theorem highamProblem61_rankOne_const_standard_profile {m n : ℕ}
    (hm : 0 < m) (j0 : Fin n) :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (standardBasisCVec j0))
      (m : ℝ) 1 1 (m : ℝ) (Real.sqrt (m : ℝ)) (Real.sqrt (m : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact complexMatrixOneNorm_rankOne_const_standard j0
  · exact complexMatrixInfNorm_rankOne_const_standard hm j0
  · exact complexMatrixEntrywiseMaxNorm_rankOne_const_standard hm j0
  · exact complexMatrixEntrywiseSumNorm_rankOne_const_standard j0
  · exact complexMatrixFrobenius_rankOne_const_standard j0
  · exact complexMatrixOp2_rankOne_const_standard j0

/-- Problem 6.1 profile for the row witness `e_i e^T`. -/
theorem highamProblem61_rankOne_standard_const_profile {m n : ℕ}
    (i0 : Fin m) (hn : 0 < n) :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : ℂ)))
      1 (n : ℝ) 1 (n : ℝ) (Real.sqrt (n : ℝ)) (Real.sqrt (n : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact complexMatrixOneNorm_rankOne_standard_const i0 hn
  · exact complexMatrixInfNorm_rankOne_standard_const i0
  · exact complexMatrixEntrywiseMaxNorm_rankOne_standard_const i0 hn
  · exact complexMatrixEntrywiseSumNorm_rankOne_standard_const i0
  · exact complexMatrixFrobenius_rankOne_standard_const i0
  · exact complexMatrixOp2_rankOne_standard_const i0 hn

/-- Problem 6.1 profile for the all-ones witness `e e^T`. -/
theorem highamProblem61_rankOne_const_const_profile {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    HighamProblem61RankOneNormProfile
      (complexMatrixRankOne (fun _ : Fin m => (1 : ℂ)) (fun _ : Fin n => (1 : ℂ)))
      (m : ℝ) (n : ℝ) 1 ((m * n : ℕ) : ℝ)
      (Real.sqrt ((m * n : ℕ) : ℝ)) (Real.sqrt ((m * n : ℕ) : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact complexMatrixOneNorm_rankOne_const_const hn
  · exact complexMatrixInfNorm_rankOne_const_const hm
  · exact complexMatrixEntrywiseMaxNorm_rankOne_const_const hm hn
  · exact complexMatrixEntrywiseSumNorm_rankOne_const_const
  · exact complexMatrixFrobenius_rankOne_const_const
  · exact complexMatrixOp2_rankOne_const_const hn

/-- Source-facing wrapper collecting all four Problem 6.1 rank-one witness
    profiles in one table-level statement. -/
theorem highamProblem61_rankOne_table_profiles {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (i0 : Fin m) (j0 : Fin n) :
    HighamProblem61RankOneTableProfiles i0 j0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact highamProblem61_rankOne_standard_standard_profile i0 j0
  · exact highamProblem61_rankOne_const_standard_profile hm j0
  · exact highamProblem61_rankOne_standard_const_profile i0 hn
  · exact highamProblem61_rankOne_const_const_profile hm hn

/-- A source-facing sharpness witness for one entry of Higham Table 6.2.
    It records an actual matrix where the denominator norm is positive and the
    numerator norm attains the printed constant times the denominator norm. -/
structure HighamProblem61NormQuotientWitness {m n : Nat} (A : CMatrix m n)
    (numerator denominator : CMatrix m n → Real) (alpha : Real) : Prop where
  denominator_pos : 0 < denominator A
  numerator_eq_alpha_mul_denominator : numerator A = alpha * denominator A

lemma highamProblem61_sqrt_nat_mul_self (k : Nat) :
    Real.sqrt (k : Real) * Real.sqrt (k : Real) = (k : Real) := by
  rw [← sq]
  exact Real.sq_sqrt (Nat.cast_nonneg k)

theorem highamProblem61_normQuotientWitness_of_eq {m n : Nat}
    {A : CMatrix m n} {numerator denominator : CMatrix m n → Real}
    {alpha numValue denValue : Real}
    (hnum : numerator A = numValue) (hden : denominator A = denValue)
    (hden_pos : 0 < denValue) (hcalc : numValue = alpha * denValue) :
    HighamProblem61NormQuotientWitness A numerator denominator alpha := by
  refine ⟨?_, ?_⟩
  · rw [hden]
    exact hden_pos
  · rw [hnum, hden]
    exact hcalc

/-- Corrected general equality package for the rank-sensitive `S/2` entry of
    Higham Table 6.2.  Flat entries and equal nonzero singular values give a
    genuine quotient witness; the unrestricted Hadamard-only converse would be
    false because lower-rank flat partial isometries also attain equality. -/
theorem highamProblem61_s2_structural_quotient_witness {m n : Nat}
    {A : CMatrix m n} (hop2 : 0 < complexMatrixOp2 A)
    (hflat : ComplexMatrixFlatEntryNorm A)
    (hsv : ComplexMatrixPositiveSingularValuesEqualOp2 A) :
    HighamProblem61NormQuotientWitness
      A complexMatrixEntrywiseSumNorm complexMatrixOp2
      (Real.sqrt (((m * n : Nat) : Real) * (complexMatrixRank A : Real))) := by
  exact highamProblem61_normQuotientWitness_of_eq
    (complexMatrixEntrywiseSumNorm_eq_sqrt_card_rank_mul_op2_of_flatEntryNorm_of_positiveSingularValuesEqualOp2
      A hflat hsv)
    rfl
    hop2
    rfl

/-- Converse package for the corrected rank-sensitive `S/2` equality route:
    any nonempty source-facing `S/2` quotient witness satisfies the two
    structural equality conditions. -/
theorem highamProblem61_s2_structural_conditions_of_quotient_witness {m n : Nat}
    (hmn : 0 < m * n) {A : CMatrix m n}
    (hw :
      HighamProblem61NormQuotientWitness
        A complexMatrixEntrywiseSumNorm complexMatrixOp2
        (Real.sqrt (((m * n : Nat) : Real) * (complexMatrixRank A : Real)))) :
    ComplexMatrixFlatEntryNorm A ∧ ComplexMatrixPositiveSingularValuesEqualOp2 A := by
  exact complexMatrixS2StructuralConditions_of_entrywiseSumNorm_eq_sqrt_card_rank_mul_op2
    hmn A hw.numerator_eq_alpha_mul_denominator

/-- Source-facing quotient package for the rank-one-attained entries of
    Higham Table 6.2.  The rank-sensitive `S/2` row is kept separate because
    its source equality discussion uses Hadamard/Vandermonde structure rather
    than only the four rank-one witnesses. -/
structure HighamProblem61RankOneTableQuotientWitnesses {m n : Nat}
    (i0 : Fin m) (j0 : Fin n) : Prop where
  one_over_two :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixOneNorm complexMatrixOp2 (Real.sqrt (m : Real))
  one_over_infty :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixOneNorm complexMatrixInfNorm (m : Real)
  one_over_frobenius :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixOneNorm complexMatrixFrobenius (Real.sqrt (m : Real))
  one_over_entrywiseMax :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixOneNorm complexMatrixEntrywiseMaxNorm (m : Real)
  one_over_entrywiseSum :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixOneNorm complexMatrixEntrywiseSumNorm 1
  two_over_one :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixOp2 complexMatrixOneNorm (Real.sqrt (n : Real))
  two_over_infty :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixOp2 complexMatrixInfNorm (Real.sqrt (m : Real))
  two_over_frobenius :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixOp2 complexMatrixFrobenius 1
  two_over_entrywiseMax :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (fun _ : Fin n => (1 : Complex)))
      complexMatrixOp2 complexMatrixEntrywiseMaxNorm
      (Real.sqrt ((m * n : Nat) : Real))
  two_over_entrywiseSum :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixOp2 complexMatrixEntrywiseSumNorm 1
  infty_over_one :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixInfNorm complexMatrixOneNorm (n : Real)
  infty_over_two :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixInfNorm complexMatrixOp2 (Real.sqrt (n : Real))
  infty_over_frobenius :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixInfNorm complexMatrixFrobenius (Real.sqrt (n : Real))
  infty_over_entrywiseMax :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixInfNorm complexMatrixEntrywiseMaxNorm (n : Real)
  infty_over_entrywiseSum :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixInfNorm complexMatrixEntrywiseSumNorm 1
  frobenius_over_one :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixFrobenius complexMatrixOneNorm (Real.sqrt (n : Real))
  frobenius_over_two :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixFrobenius complexMatrixOp2
      (Real.sqrt
        (complexMatrixRank
          (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0)) : Real))
  frobenius_over_infty :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixFrobenius complexMatrixInfNorm (Real.sqrt (m : Real))
  frobenius_over_entrywiseMax :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (fun _ : Fin n => (1 : Complex)))
      complexMatrixFrobenius complexMatrixEntrywiseMaxNorm
      (Real.sqrt ((m * n : Nat) : Real))
  frobenius_over_entrywiseSum :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixFrobenius complexMatrixEntrywiseSumNorm 1
  entrywiseMax_over_one :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixEntrywiseMaxNorm complexMatrixOneNorm 1
  entrywiseMax_over_two :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixEntrywiseMaxNorm complexMatrixOp2 1
  entrywiseMax_over_infty :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixEntrywiseMaxNorm complexMatrixInfNorm 1
  entrywiseMax_over_frobenius :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixEntrywiseMaxNorm complexMatrixFrobenius 1
  entrywiseMax_over_entrywiseSum :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (standardBasisCVec j0))
      complexMatrixEntrywiseMaxNorm complexMatrixEntrywiseSumNorm 1
  entrywiseSum_over_one :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (standardBasisCVec i0) (fun _ : Fin n => (1 : Complex)))
      complexMatrixEntrywiseSumNorm complexMatrixOneNorm (n : Real)
  entrywiseSum_over_infty :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (standardBasisCVec j0))
      complexMatrixEntrywiseSumNorm complexMatrixInfNorm (m : Real)
  entrywiseSum_over_frobenius :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (fun _ : Fin n => (1 : Complex)))
      complexMatrixEntrywiseSumNorm complexMatrixFrobenius
      (Real.sqrt ((m * n : Nat) : Real))
  entrywiseSum_over_entrywiseMax :
    HighamProblem61NormQuotientWitness
      (complexMatrixRankOne (fun _ : Fin m => (1 : Complex)) (fun _ : Fin n => (1 : Complex)))
      complexMatrixEntrywiseSumNorm complexMatrixEntrywiseMaxNorm ((m * n : Nat) : Real)

/-- Higham Problem 6.1: the four prescribed rank-one matrices attain all
    Table 6.2 quotient constants except the rank-sensitive `S/2` entry, whose
    Hadamard/Vandermonde equality cases are tracked separately. -/
theorem highamProblem61_rankOne_table_quotient_witnesses {m n : Nat}
    (hm : 0 < m) (hn : 0 < n) (i0 : Fin m) (j0 : Fin n) :
    HighamProblem61RankOneTableQuotientWitnesses i0 j0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOneNorm_rankOne_const_standard j0)
      (complexMatrixOp2_rankOne_const_standard j0)
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hm))
      (by rw [highamProblem61_sqrt_nat_mul_self m])
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOneNorm_rankOne_const_standard j0)
      (complexMatrixInfNorm_rankOne_const_standard hm j0)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOneNorm_rankOne_const_standard j0)
      (complexMatrixFrobenius_rankOne_const_standard j0)
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hm))
      (by rw [highamProblem61_sqrt_nat_mul_self m])
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOneNorm_rankOne_const_standard j0)
      (complexMatrixEntrywiseMaxNorm_rankOne_const_standard hm j0)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOneNorm_rankOne_const_standard j0)
      (complexMatrixEntrywiseSumNorm_rankOne_const_standard j0)
      (Nat.cast_pos.mpr hm)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOp2_rankOne_standard_const i0 hn)
      (complexMatrixOneNorm_rankOne_standard_const i0 hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOp2_rankOne_const_standard j0)
      (complexMatrixInfNorm_rankOne_const_standard hm j0)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOp2_rankOne_standard_standard i0 j0)
      (complexMatrixFrobenius_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOp2_rankOne_const_const hn)
      (complexMatrixEntrywiseMaxNorm_rankOne_const_const hm hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixOp2_rankOne_standard_standard i0 j0)
      (complexMatrixEntrywiseSumNorm_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixInfNorm_rankOne_standard_const i0)
      (complexMatrixOneNorm_rankOne_standard_const i0 hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixInfNorm_rankOne_standard_const i0)
      (complexMatrixOp2_rankOne_standard_const i0 hn)
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))
      (by rw [highamProblem61_sqrt_nat_mul_self n])
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixInfNorm_rankOne_standard_const i0)
      (complexMatrixFrobenius_rankOne_standard_const i0)
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))
      (by rw [highamProblem61_sqrt_nat_mul_self n])
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixInfNorm_rankOne_standard_const i0)
      (complexMatrixEntrywiseMaxNorm_rankOne_standard_const i0 hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixInfNorm_rankOne_standard_const i0)
      (complexMatrixEntrywiseSumNorm_rankOne_standard_const i0)
      (Nat.cast_pos.mpr hn)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixFrobenius_rankOne_standard_const i0)
      (complexMatrixOneNorm_rankOne_standard_const i0 hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixFrobenius_rankOne_standard_standard i0 j0)
      (complexMatrixOp2_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by rw [complexMatrixRank_rankOne_standard_standard i0 j0]; norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixFrobenius_rankOne_const_standard j0)
      (complexMatrixInfNorm_rankOne_const_standard hm j0)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixFrobenius_rankOne_const_const)
      (complexMatrixEntrywiseMaxNorm_rankOne_const_const hm hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixFrobenius_rankOne_standard_standard i0 j0)
      (complexMatrixEntrywiseSumNorm_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0)
      (complexMatrixOneNorm_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0)
      (complexMatrixOp2_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0)
      (complexMatrixInfNorm_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0)
      (complexMatrixFrobenius_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseMaxNorm_rankOne_standard_standard i0 j0)
      (complexMatrixEntrywiseSumNorm_rankOne_standard_standard i0 j0)
      (by norm_num)
      (by norm_num)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseSumNorm_rankOne_standard_const i0)
      (complexMatrixOneNorm_rankOne_standard_const i0 hn)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseSumNorm_rankOne_const_standard j0)
      (complexMatrixInfNorm_rankOne_const_standard hm j0)
      (by norm_num)
      (by ring)
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseSumNorm_rankOne_const_const)
      (complexMatrixFrobenius_rankOne_const_const)
      (Real.sqrt_pos.2 (Nat.cast_pos.mpr (Nat.mul_pos hm hn)))
      (by rw [highamProblem61_sqrt_nat_mul_self (m * n)])
  · exact highamProblem61_normQuotientWitness_of_eq
      (complexMatrixEntrywiseSumNorm_rankOne_const_const)
      (complexMatrixEntrywiseMaxNorm_rankOne_const_const hm hn)
      (by norm_num)
      (by ring)

lemma highamProblem61_s2_hadamard_calc (n : Nat) :
    Real.sqrt (((n * n : Nat) : Real) * (n : Real)) * Real.sqrt (n : Real) =
      ((n * n : Nat) : Real) := by
  have hnonneg : 0 <= (((n * n : Nat) : Real) * (n : Real)) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  calc
    Real.sqrt (((n * n : Nat) : Real) * (n : Real)) * Real.sqrt (n : Real)
        = Real.sqrt ((((n * n : Nat) : Real) * (n : Real)) * (n : Real)) := by
          rw [Real.sqrt_mul hnonneg]
    _ = Real.sqrt (((n * n : Nat) : Real) * ((n : Real) * (n : Real))) := by
          ring_nf
    _ = Real.sqrt (((n * n : Nat) : Real) * ((n * n : Nat) : Real)) := by
          norm_num [Nat.cast_mul]
    _ = ((n * n : Nat) : Real) := by
          rw [Real.sqrt_mul_self (Nat.cast_nonneg _)]

/-- Higham Problem 6.1, Table 6.2, `S/2` sharpness witness for real square
    Hadamard matrices: `||H||_S = sqrt(n*n*rank(H)) * ||H||_2`. -/
theorem highamProblem61_hadamard_s2_quotient_witness {n : Nat} (hn : 0 < n)
    {H : Fin n -> Fin n -> Real} (hH : IsRealHadamardMatrix H) :
    HighamProblem61NormQuotientWitness
      (realRectToCMatrix H)
      complexMatrixEntrywiseSumNorm complexMatrixOp2
      (Real.sqrt (((n * n : Nat) : Real) *
        (complexMatrixRank (realRectToCMatrix H) : Real))) := by
  exact highamProblem61_normQuotientWitness_of_eq
    hH.complexMatrixEntrywiseSumNorm_eq
    (hH.complexMatrixOp2_eq_sqrt hn)
    (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))
    (by
      rw [hH.complexMatrixRank_eq hn]
      exact (highamProblem61_s2_hadamard_calc n).symm)

/-- Higham Problem 6.1, Table 6.2, complex-Hadamard `S/2` sharpness witness:
    `||H||_S = sqrt(n*n*rank(H)) * ||H||_2`.  This covers the abstract
    roots-of-unity/Vandermonde equality case once the Fourier matrix is shown
    to satisfy `IsComplexHadamardMatrix`. -/
theorem highamProblem61_complexHadamard_s2_quotient_witness {n : Nat} (hn : 0 < n)
    {H : CMatrix n n} (hH : IsComplexHadamardMatrix H) :
    HighamProblem61NormQuotientWitness
      H complexMatrixEntrywiseSumNorm complexMatrixOp2
      (Real.sqrt (((n * n : Nat) : ℝ) * (complexMatrixRank H : ℝ))) := by
  exact highamProblem61_normQuotientWitness_of_eq
    hH.complexMatrixEntrywiseSumNorm_eq
    (hH.complexMatrixOp2_eq_sqrt hn)
    (Real.sqrt_pos.2 (Nat.cast_pos.mpr hn))
    (by
      rw [hH.complexMatrixRank_eq hn]
      exact (highamProblem61_s2_hadamard_calc n).symm)

/-- Higham Problem 6.1, Table 6.2, literal roots-of-unity/Vandermonde
    `S/2` sharpness witness. -/
theorem highamProblem61_fourierVandermonde_s2_quotient_witness
    {n : Nat} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    HighamProblem61NormQuotientWitness
      (complexFourierVandermondeMatrix n ζ)
      complexMatrixEntrywiseSumNorm complexMatrixOp2
      (Real.sqrt (((n * n : Nat) : ℝ) *
        (complexMatrixRank (complexFourierVandermondeMatrix n ζ) : ℝ))) :=
  highamProblem61_complexHadamard_s2_quotient_witness hn
    (complexFourierVandermonde_isComplexHadamard_of_isPrimitiveRoot hn hζ)
end NumStability
