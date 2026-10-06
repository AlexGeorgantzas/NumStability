/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Companion

namespace NumStability

open scoped BigOperators ComplexConjugate
open Matrix Module Polynomial

noncomputable section

private noncomputable def companionReverseCoefficients
    (n : ℕ) (a : ℕ → ℂ) : Fin n → ℂ :=
  fun i => a (n - 1 - i.val)

private noncomputable def companionCoefficientMoment
    (n : ℕ) (a : ℕ → ℂ) (x : Fin n → ℂ) : ℂ :=
  ∑ j : Fin n, companionReverseCoefficients n a j * x j

private theorem companionGramFormula_mulVec_apply
    (n : ℕ) (a : ℕ → ℂ) (x : Fin n → ℂ) (i : Fin n) :
    Matrix.mulVec (companionGramFormula n a) x i =
      star (companionReverseCoefficients n a i) *
          companionCoefficientMoment n a x +
        if i.val + 1 < n then x i else 0 := by
  classical
  simp only [Matrix.mulVec, dotProduct, companionGramFormula,
    companionReverseCoefficients, companionCoefficientMoment]
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp [Finset.mul_sum, mul_assoc]
  · by_cases hi : i.val + 1 < n
    · simp [hi]
    · simp [hi]

private theorem companionReverseCoefficients_norm_sq_sum
    (n : ℕ) (a : ℕ → ℂ) :
    (∑ i : Fin n, ‖companionReverseCoefficients n a i‖ ^ 2) =
      ∑ k ∈ Finset.range n, ‖a k‖ ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range]
  have hrev : ∀ i : Fin n,
      companionReverseCoefficients n a i = a (Fin.rev i).val := by
    intro i
    unfold companionReverseCoefficients
    congr 1
    simp [Fin.rev]
    omega
  simp_rw [hrev]
  exact Equiv.sum_comp Fin.revPerm (fun i : Fin n => ‖a i.val‖ ^ 2)

private theorem fin_add_one_lt_iff_ne_last {m : ℕ} (i : Fin (m + 2)) :
    i.val + 1 < m + 2 ↔ i ≠ Fin.last (m + 1) := by
  constructor
  · intro hi hlast
    subst i
    simp at hi
  · intro hne
    have hi := i.isLt
    have hval : i.val ≠ m + 1 := by
      intro h
      apply hne
      apply Fin.ext
      simpa using h
    omega

private theorem companionReverseCoefficients_last
    (m : ℕ) (a : ℕ → ℂ) :
    companionReverseCoefficients (m + 2) a (Fin.last (m + 1)) = a 0 := by
  unfold companionReverseCoefficients
  congr 1
  simp

private theorem companionCoefficientMoment_truncated
    (m : ℕ) (a : ℕ → ℂ) (x : Fin (m + 2) → ℂ) :
    (∑ i : Fin (m + 2),
        if i.val + 1 < m + 2 then
          companionReverseCoefficients (m + 2) a i * x i else 0) =
      companionCoefficientMoment (m + 2) a x -
        a 0 * x (Fin.last (m + 1)) := by
  classical
  simp_rw [fin_add_one_lt_iff_ne_last]
  rw [← Finset.sum_filter]
  rw [Finset.filter_ne']
  have hsum := Finset.sum_erase_add Finset.univ
    (fun i : Fin (m + 2) =>
      companionReverseCoefficients (m + 2) a i * x i)
    (Finset.mem_univ (Fin.last (m + 1)))
  have hsum' :
      (∑ i ∈ Finset.univ.erase (Fin.last (m + 1)),
          companionReverseCoefficients (m + 2) a i * x i) +
          a 0 * x (Fin.last (m + 1)) =
        ∑ i : Fin (m + 2),
          companionReverseCoefficients (m + 2) a i * x i := by
    simpa [companionReverseCoefficients_last] using hsum
  unfold companionCoefficientMoment
  linear_combination hsum'

private theorem companionReverseCoefficients_star_sum
    (n : ℕ) (a : ℕ → ℂ) :
    (∑ i : Fin n,
        companionReverseCoefficients n a i *
          star (companionReverseCoefficients n a i)) =
      ((∑ k ∈ Finset.range n, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
  have hnorm := companionReverseCoefficients_norm_sq_sum n a
  calc
    (∑ i : Fin n,
        companionReverseCoefficients n a i *
          star (companionReverseCoefficients n a i)) =
      ∑ i : Fin n, ((‖companionReverseCoefficients n a i‖ ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Complex.star_def]
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
        ring
    _ = ((∑ k ∈ Finset.range n, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
      exact_mod_cast hnorm

private theorem companionCoefficientMoment_gram
    (m : ℕ) (a : ℕ → ℂ) (x : Fin (m + 2) → ℂ) :
    companionCoefficientMoment (m + 2) a
        (Matrix.mulVec (companionGramFormula (m + 2) a) x) =
      (companionSingularAlpha (m + 2) a : ℂ) *
          companionCoefficientMoment (m + 2) a x -
        a 0 * x (Fin.last (m + 1)) := by
  classical
  let s := companionCoefficientMoment (m + 2) a x
  unfold companionCoefficientMoment
  simp_rw [companionGramFormula_mulVec_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ i : Fin (m + 2),
          companionReverseCoefficients (m + 2) a i *
            (star (companionReverseCoefficients (m + 2) a i) * s)) =
        ((∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 : ℝ) : ℂ) * s := by
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    rw [companionReverseCoefficients_star_sum]
  rw [show companionCoefficientMoment (m + 2) a x = s by rfl]
  rw [hfirst]
  simp_rw [mul_ite, mul_zero]
  rw [companionCoefficientMoment_truncated]
  unfold companionSingularAlpha
  push_cast
  change
    ((∑ k ∈ Finset.range (m + 2), (‖a k‖ ^ 2 : ℂ)) * s +
        (s - a 0 * x (Fin.last (m + 1)))) =
      (1 + ∑ k ∈ Finset.range (m + 2), (‖a k‖ ^ 2 : ℂ)) * s -
        a 0 * x (Fin.last (m + 1))
  ring

private theorem companionCoefficientMoment_smul
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) (x : Fin n → ℂ) :
    companionCoefficientMoment n a (lambda • x) =
      lambda * companionCoefficientMoment n a x := by
  classical
  unfold companionCoefficientMoment
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem companion_norm_sq_complex
    (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  rw [Complex.star_def]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  ring

/-- Higham, Section 28.6, p. 523: for an order at least two companion
matrix, every eigenvalue of `CᴴC` is either `1` or is a root of the printed
quadratic for the two exceptional squared singular values. -/
theorem companionGram_eigenvalue_eq_one_or_exceptional
    (m : ℕ) (a : ℕ → ℂ) (lambda : ℂ) (x : Fin (m + 2) → ℂ)
    (hx : x ≠ 0)
    (heig : Matrix.mulVec (companionGramFormula (m + 2) a) x =
      lambda • x) :
    lambda = 1 ∨
      lambda ^ 2 - (companionSingularAlpha (m + 2) a : ℂ) * lambda +
          ((‖a 0‖ ^ 2 : ℝ) : ℂ) = 0 := by
  classical
  let s := companionCoefficientMoment (m + 2) a x
  let ell : Fin (m + 2) := Fin.last (m + 1)
  by_cases hlambda : lambda = 1
  · exact Or.inl hlambda
  right
  have hmoment0 := congrArg
    (companionCoefficientMoment (m + 2) a) heig
  have hmoment :
      lambda * s =
        (companionSingularAlpha (m + 2) a : ℂ) * s - a 0 * x ell := by
    rw [companionCoefficientMoment_gram,
      companionCoefficientMoment_smul] at hmoment0
    simpa [s, ell] using hmoment0.symm
  have hlast0 := congrFun heig ell
  have hlast : lambda * x ell = star (a 0) * s := by
    rw [companionGramFormula_mulVec_apply] at hlast0
    simp only [Pi.smul_apply, smul_eq_mul] at hlast0
    have hcond : ¬ ell.val + 1 < m + 2 := by simp [ell]
    rw [if_neg hcond] at hlast0
    rw [show companionReverseCoefficients (m + 2) a ell = a 0 by
      simpa [ell] using companionReverseCoefficients_last m a] at hlast0
    simpa [s, add_zero] using hlast0.symm
  have hpoly_s :
      (lambda ^ 2 - (companionSingularAlpha (m + 2) a : ℂ) * lambda +
          ((‖a 0‖ ^ 2 : ℝ) : ℂ)) * s = 0 := by
    calc
      (lambda ^ 2 - (companionSingularAlpha (m + 2) a : ℂ) * lambda +
            ((‖a 0‖ ^ 2 : ℝ) : ℂ)) * s =
          lambda * (lambda * s) -
            (companionSingularAlpha (m + 2) a : ℂ) * (lambda * s) +
              ((‖a 0‖ ^ 2 : ℝ) : ℂ) * s := by ring
      _ = lambda *
            ((companionSingularAlpha (m + 2) a : ℂ) * s - a 0 * x ell) -
            (companionSingularAlpha (m + 2) a : ℂ) * (lambda * s) +
              ((‖a 0‖ ^ 2 : ℝ) : ℂ) * s := by rw [hmoment]
      _ = (companionSingularAlpha (m + 2) a : ℂ) * (lambda * s) -
            a 0 * (lambda * x ell) -
            (companionSingularAlpha (m + 2) a : ℂ) * (lambda * s) +
              ((‖a 0‖ ^ 2 : ℝ) : ℂ) * s := by ring
      _ = (companionSingularAlpha (m + 2) a : ℂ) * (lambda * s) -
            a 0 * (star (a 0) * s) -
            (companionSingularAlpha (m + 2) a : ℂ) * (lambda * s) +
              ((‖a 0‖ ^ 2 : ℝ) : ℂ) * s := by rw [hlast]
      _ = 0 := by rw [companion_norm_sq_complex]; ring
  by_cases hs : s = 0
  · have hnonlast : ∀ i : Fin (m + 2), i ≠ ell → x i = 0 := by
      intro i hine
      have hi := congrFun heig i
      rw [companionGramFormula_mulVec_apply] at hi
      have hcond : i.val + 1 < m + 2 := by
        rw [fin_add_one_lt_iff_ne_last]
        simpa [ell] using hine
      rw [if_pos hcond] at hi
      simp only [Pi.smul_apply, smul_eq_mul] at hi
      rw [show companionCoefficientMoment (m + 2) a x = s by rfl, hs] at hi
      simp only [mul_zero, zero_add] at hi
      have hcoef : 1 - lambda ≠ 0 := sub_ne_zero.mpr (Ne.symm hlambda)
      apply (mul_eq_zero.mp ?_).resolve_left hcoef
      linear_combination hi
    have hxell : x ell ≠ 0 := by
      intro hxell0
      apply hx
      funext i
      by_cases hi : i = ell
      · simpa [hi] using hxell0
      · exact hnonlast i hi
    have hlambda0 : lambda = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hxell
      rw [hlast, hs, mul_zero]
    have ha0 : a 0 = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_right hxell
      have hm := hmoment
      rw [hs, mul_zero, mul_zero, zero_sub] at hm
      have hm' : -(a 0 * x ell) = 0 := hm.symm
      simpa using hm'
    simp [hlambda0, ha0]
  · exact (mul_eq_zero.mp hpoly_s).resolve_right hs

/-- The same classification for the actual companion Gram matrix `CᴴC`. -/
theorem companion_conjTranspose_mul_self_eigenvalue_eq_one_or_exceptional
    (m : ℕ) (a : ℕ → ℂ) (lambda : ℂ) (x : Fin (m + 2) → ℂ)
    (hx : x ≠ 0)
    (heig : Matrix.mulVec
      ((companionMatrix (m + 2) a).conjTranspose *
        companionMatrix (m + 2) a) x = lambda • x) :
    lambda = 1 ∨
      lambda ^ 2 - (companionSingularAlpha (m + 2) a : ℂ) * lambda +
          ((‖a 0‖ ^ 2 : ℝ) : ℂ) = 0 := by
  apply companionGram_eigenvalue_eq_one_or_exceptional m a lambda x hx
  rw [← companion_conjTranspose_mul_self]
  exact heig

private theorem matrix_rank_add_le {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc
    Module.finrank ℂ (LinearMap.range (A.mulVecLin + B.mulVecLin)) ≤
        Module.finrank ℂ
          ((LinearMap.range A.mulVecLin) ⊔ (LinearMap.range B.mulVecLin) :
            Submodule ℂ (Fin n → ℂ)) :=
      Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ Module.finrank ℂ (LinearMap.range A.mulVecLin) +
          Module.finrank ℂ (LinearMap.range B.mulVecLin) :=
      Submodule.finrank_add_le_finrank_add_finrank _ _

private noncomputable def companionLastBasis (m : ℕ) : Fin (m + 2) → ℂ :=
  Pi.single (Fin.last (m + 1)) 1

private theorem companionGram_sub_one_eq_rankTwo
    (m : ℕ) (a : ℕ → ℂ) :
    companionGramFormula (m + 2) a -
        (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) =
      Matrix.vecMulVec
          (fun i => star (companionReverseCoefficients (m + 2) a i))
          (companionReverseCoefficients (m + 2) a) +
        Matrix.vecMulVec (-(companionLastBasis m)) (companionLastBasis m) := by
  classical
  ext i j
  simp only [companionGramFormula, Matrix.sub_apply, Matrix.one_apply,
    Matrix.add_apply, Matrix.vecMulVec_apply]
  by_cases hij : i = j
  · subst j
    by_cases hilast : i = Fin.last (m + 1)
    · subst i
      simp [companionLastBasis, companionReverseCoefficients]
      ring
    · have hi : i.val + 1 < m + 2 := by
        rw [fin_add_one_lt_iff_ne_last]
        exact hilast
      simp [hi, companionLastBasis, companionReverseCoefficients, hilast]
  · by_cases hilast : i = Fin.last (m + 1)
    · have hjlast : j ≠ Fin.last (m + 1) := by
        intro hj
        exact hij (hilast.trans hj.symm)
      have hjlast' : Fin.last (m + 1) ≠ j := Ne.symm hjlast
      simp [hij, companionLastBasis, Pi.single_apply,
        companionReverseCoefficients, hilast, hjlast, hjlast']
    · by_cases hjlast : j = Fin.last (m + 1)
      · simp [hij, companionLastBasis, Pi.single_apply,
          companionReverseCoefficients, hilast, hjlast]
      · simp [hij, companionLastBasis, Pi.single_apply,
          companionReverseCoefficients, hilast, hjlast]

/-- In order at least two, `CᴴC-I` has rank at most two. Thus the unit
squared singular value has codimension at most two, while the preceding
theorem classifies the remaining values by Higham's exceptional quadratic. -/
theorem companion_conjTranspose_mul_self_sub_one_rank_le_two
    (m : ℕ) (a : ℕ → ℂ) :
    Matrix.rank
      ((companionMatrix (m + 2) a).conjTranspose *
          companionMatrix (m + 2) a -
        (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ)) ≤ 2 := by
  rw [companion_conjTranspose_mul_self]
  rw [companionGram_sub_one_eq_rankTwo]
  calc
    Matrix.rank
        (Matrix.vecMulVec
            (fun i => star (companionReverseCoefficients (m + 2) a i))
            (companionReverseCoefficients (m + 2) a) +
          Matrix.vecMulVec (-(companionLastBasis m)) (companionLastBasis m)) ≤
      Matrix.rank
          (Matrix.vecMulVec
            (fun i => star (companionReverseCoefficients (m + 2) a i))
            (companionReverseCoefficients (m + 2) a)) +
        Matrix.rank
          (Matrix.vecMulVec (-(companionLastBasis m)) (companionLastBasis m)) :=
      matrix_rank_add_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add
      (Matrix.rank_vecMulVec_le _ _) (Matrix.rank_vecMulVec_le _ _)
    _ = 2 := by norm_num

private noncomputable def companionRankTwoLeft
    (m : ℕ) (a : ℕ → ℂ) : Matrix (Fin (m + 2)) (Fin 2) ℂ :=
  fun i r =>
    if r = 0 then
      star (companionReverseCoefficients (m + 2) a i)
    else
      -(companionLastBasis m i)

private noncomputable def companionRankTwoRight
    (m : ℕ) (a : ℕ → ℂ) : Matrix (Fin 2) (Fin (m + 2)) ℂ :=
  fun r j =>
    if r = 0 then
      companionReverseCoefficients (m + 2) a j
    else
      companionLastBasis m j

private theorem companionRankTwoLeft_mul_right
    (m : ℕ) (a : ℕ → ℂ) :
    companionRankTwoLeft m a * companionRankTwoRight m a =
      companionGramFormula (m + 2) a -
        (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) := by
  classical
  rw [companionGram_sub_one_eq_rankTwo]
  ext i j
  simp [companionRankTwoLeft, companionRankTwoRight, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.vecMulVec_apply]

private theorem sum_mul_companionLastBasis
    (m : ℕ) (f : Fin (m + 2) → ℂ) :
    (∑ i : Fin (m + 2), f i * companionLastBasis m i) =
      f (Fin.last (m + 1)) := by
  classical
  calc
    (∑ i : Fin (m + 2), f i * companionLastBasis m i) =
        f (Fin.last (m + 1)) *
          companionLastBasis m (Fin.last (m + 1)) := by
      apply Fintype.sum_eq_single
      intro i hi
      simp [companionLastBasis, Pi.single, Function.update, hi]
    _ = f (Fin.last (m + 1)) := by
      simp [companionLastBasis, Pi.single, Function.update]

private theorem companionLastBasis_mul_sum
    (m : ℕ) (f : Fin (m + 2) → ℂ) :
    (∑ i : Fin (m + 2), companionLastBasis m i * f i) =
      f (Fin.last (m + 1)) := by
  classical
  calc
    (∑ i : Fin (m + 2), companionLastBasis m i * f i) =
        companionLastBasis m (Fin.last (m + 1)) *
          f (Fin.last (m + 1)) := by
      apply Fintype.sum_eq_single
      intro i hi
      simp [companionLastBasis, Pi.single, Function.update, hi]
    _ = f (Fin.last (m + 1)) := by
      simp [companionLastBasis, Pi.single, Function.update]

private noncomputable def companionExceptionalCore
    (m : ℕ) (a : ℕ → ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(companionSingularAlpha (m + 2) a : ℂ), -a 0;
     star (a 0), 0]

private theorem one_add_companionRankTwoRight_mul_left
    (m : ℕ) (a : ℕ → ℂ) :
    (1 : Matrix (Fin 2) (Fin 2) ℂ) +
        companionRankTwoRight m a * companionRankTwoLeft m a =
      companionExceptionalCore m a := by
  classical
  ext i j
  fin_cases i <;> fin_cases j
  · change 1 +
        (∑ x : Fin (m + 2),
          companionReverseCoefficients (m + 2) a x *
            star (companionReverseCoefficients (m + 2) a x)) =
        (companionSingularAlpha (m + 2) a : ℂ)
    rw [companionReverseCoefficients_star_sum]
    unfold companionSingularAlpha
    push_cast
    ring
  · change
      (if (0 : Fin 2) = 1 then 1 else 0) +
          (companionRankTwoRight m a * companionRankTwoLeft m a) 0 1 =
        companionExceptionalCore m a 0 1
    rw [if_neg (by decide), zero_add]
    change
        (∑ x : Fin (m + 2),
          companionReverseCoefficients (m + 2) a x *
            (-(companionLastBasis m x))) = -a 0
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib, sum_mul_companionLastBasis]
    rw [companionReverseCoefficients_last]
  · change
      (if (1 : Fin 2) = 0 then 1 else 0) +
          (companionRankTwoRight m a * companionRankTwoLeft m a) 1 0 =
        companionExceptionalCore m a 1 0
    rw [if_neg (by decide), zero_add]
    change
        (∑ x : Fin (m + 2),
          companionLastBasis m x *
            star (companionReverseCoefficients (m + 2) a x)) = star (a 0)
    rw [companionLastBasis_mul_sum]
    rw [companionReverseCoefficients_last]
  · change 1 +
      (∑ x : Fin (m + 2),
        companionLastBasis m x * (-(companionLastBasis m x))) = 0
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib, companionLastBasis_mul_sum]
    simp [companionLastBasis, Pi.single, Function.update]

private theorem companionExceptionalCore_charpoly
    (m : ℕ) (a : ℕ → ℂ) :
    (companionExceptionalCore m a).charpoly =
      X ^ 2 - C (companionSingularAlpha (m + 2) a : ℂ) * X +
        C ((‖a 0‖ ^ 2 : ℝ) : ℂ) := by
  have htrace :
      (companionExceptionalCore m a).trace =
        (companionSingularAlpha (m + 2) a : ℂ) := by
    rw [Matrix.trace_fin_two]
    change (companionSingularAlpha (m + 2) a : ℂ) + 0 = _
    ring
  have hdet :
      (companionExceptionalCore m a).det = ((‖a 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.det_fin_two]
    change
      (companionSingularAlpha (m + 2) a : ℂ) * 0 -
          (-a 0) * star (a 0) = ((‖a 0‖ ^ 2 : ℝ) : ℂ)
    rw [companion_norm_sq_complex]
    ring
  rw [Matrix.charpoly_fin_two, htrace, hdet]

private theorem matrix_sub_scalar_neg_one_eq_one_add
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) :
    M - Matrix.scalar n (-1) = 1 + M := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.sub_apply, Matrix.add_apply,
      Matrix.scalar_apply, add_comm]
  · simp [Matrix.sub_apply, Matrix.add_apply,
      Matrix.scalar_apply, hij]

/-- Higham, Section 28.6, p. 523: the companion Gram characteristic
polynomial consists of `m` unit factors and the printed exceptional
quadratic.  This factorization is valid without genericity hypotheses. -/
theorem companion_conjTranspose_mul_self_charpoly
    (m : ℕ) (a : ℕ → ℂ) :
    ((companionMatrix (m + 2) a).conjTranspose *
        companionMatrix (m + 2) a).charpoly =
      (X - C (1 : ℂ)) ^ m *
        (X ^ 2 - C (companionSingularAlpha (m + 2) a : ℂ) * X +
          C ((‖a 0‖ ^ 2 : ℝ) : ℂ)) := by
  classical
  let L := companionRankTwoLeft m a
  let R := companionRankTwoRight m a
  let G := companionGramFormula (m + 2) a
  have hLR : L * R = G - 1 := by
    simpa [L, R, G] using companionRankTwoLeft_mul_right m a
  have hmul :
      (L * R).charpoly = X ^ m * (R * L).charpoly := by
    simpa [L, R] using
      Matrix.charpoly_mul_comm_of_le L R (by simp)
  have hlargeMatrix : L * R - Matrix.scalar (Fin (m + 2)) (-1) = G := by
    rw [matrix_sub_scalar_neg_one_eq_one_add, hLR]
    abel
  have hsmallMatrix :
      R * L - Matrix.scalar (Fin 2) (-1) = companionExceptionalCore m a := by
    rw [matrix_sub_scalar_neg_one_eq_one_add]
    exact one_add_companionRankTwoRight_mul_left m a
  have hlargeShift :
      G.charpoly = (L * R).charpoly.comp (X - C (1 : ℂ)) := by
    rw [← hlargeMatrix]
    simpa using Matrix.charpoly_sub_scalar (L * R) (-1)
  have hsmallShift :
      (companionExceptionalCore m a).charpoly =
        (R * L).charpoly.comp (X - C (1 : ℂ)) := by
    rw [← hsmallMatrix]
    simpa using Matrix.charpoly_sub_scalar (R * L) (-1)
  rw [companion_conjTranspose_mul_self]
  change G.charpoly = _
  calc
    G.charpoly = (L * R).charpoly.comp (X - C (1 : ℂ)) := hlargeShift
    _ = (X ^ m * (R * L).charpoly).comp (X - C (1 : ℂ)) := by
      rw [hmul]
    _ = (X - C (1 : ℂ)) ^ m *
        (R * L).charpoly.comp (X - C (1 : ℂ)) := by simp
    _ = (X - C (1 : ℂ)) ^ m *
        (companionExceptionalCore m a).charpoly := by rw [hsmallShift]
    _ = (X - C (1 : ℂ)) ^ m *
        (X ^ 2 - C (companionSingularAlpha (m + 2) a : ℂ) * X +
          C ((‖a 0‖ ^ 2 : ℝ) : ℂ)) := by
      rw [companionExceptionalCore_charpoly]

/-- The canonical squared singular values of an order-at-least-two companion:
the Hermitian eigenvalues of `CᴴC`. -/
noncomputable def companionSquaredSingularValues
    (m : ℕ) (a : ℕ → ℂ) : Fin (m + 2) → ℝ :=
  (Matrix.isHermitian_conjTranspose_mul_self
    (companionMatrix (m + 2) a)).eigenvalues

theorem companionSquaredSingularValues_nonneg
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) :
    0 ≤ companionSquaredSingularValues m a i := by
  exact Matrix.eigenvalues_conjTranspose_mul_self_nonneg
    (companionMatrix (m + 2) a) i

/-- Every canonical squared singular value is `1` or obeys the two-root
quadratic printed by Higham. -/
theorem companionSquaredSingularValues_eq_one_or_exceptional
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) :
    companionSquaredSingularValues m a i = 1 ∨
      (companionSquaredSingularValues m a i : ℂ) ^ 2 -
          (companionSingularAlpha (m + 2) a : ℂ) *
            companionSquaredSingularValues m a i +
          ((‖a 0‖ ^ 2 : ℝ) : ℂ) = 0 := by
  let C := companionMatrix (m + 2) a
  let G := C.conjTranspose * C
  let hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self C
  let v : Fin (m + 2) → ℂ := ⇑(hG.eigenvectorBasis i)
  have hv : v ≠ 0 := by
    have hvvec : hG.eigenvectorBasis i ≠ 0 :=
      hG.eigenvectorBasis.orthonormal.ne_zero i
    intro hv0
    apply hvvec
    apply PiLp.ext
    intro j
    exact congrFun hv0 j
  have heig : Matrix.mulVec G v =
      (companionSquaredSingularValues m a i : ℂ) • v := by
    simpa [C, G, hG, v, companionSquaredSingularValues] using
      hG.mulVec_eigenvectorBasis i
  simpa [C, G] using
    companion_conjTranspose_mul_self_eigenvalue_eq_one_or_exceptional
      m a (companionSquaredSingularValues m a i : ℂ) v hv heig

noncomputable def companionExceptionalDiscriminant
    (m : ℕ) (a : ℕ → ℂ) : ℝ :=
  companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2

noncomputable def companionExceptionalSquaredSingularValuePlus
    (m : ℕ) (a : ℕ → ℂ) : ℝ :=
  (companionSingularAlpha (m + 2) a +
    Real.sqrt (companionExceptionalDiscriminant m a)) / 2

noncomputable def companionExceptionalSquaredSingularValueMinus
    (m : ℕ) (a : ℕ → ℂ) : ℝ :=
  (companionSingularAlpha (m + 2) a -
    Real.sqrt (companionExceptionalDiscriminant m a)) / 2

theorem companionExceptionalDiscriminant_nonneg
    (m : ℕ) (a : ℕ → ℂ) :
    0 ≤ companionExceptionalDiscriminant m a := by
  have hmem : 0 ∈ Finset.range (m + 2) := by simp
  have hsum : ‖a 0‖ ^ 2 ≤
      ∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 := by
    exact Finset.single_le_sum (fun k hk => sq_nonneg ‖a k‖) hmem
  have halpha : 1 + ‖a 0‖ ^ 2 ≤ companionSingularAlpha (m + 2) a := by
    unfold companionSingularAlpha
    linarith
  have hq : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  unfold companionExceptionalDiscriminant
  nlinarith [sq_nonneg (‖a 0‖ ^ 2 - 1)]

theorem companionExceptionalSquaredSingularValuePlus_isRoot
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValuePlus m a ^ 2 -
        companionSingularAlpha (m + 2) a *
          companionExceptionalSquaredSingularValuePlus m a + ‖a 0‖ ^ 2 = 0 := by
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValuePlus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  nlinarith

theorem companionExceptionalSquaredSingularValueMinus_isRoot
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValueMinus m a ^ 2 -
        companionSingularAlpha (m + 2) a *
          companionExceptionalSquaredSingularValueMinus m a + ‖a 0‖ ^ 2 = 0 := by
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  nlinarith

theorem companionExceptionalSquaredSingularValues_sum
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValuePlus m a +
        companionExceptionalSquaredSingularValueMinus m a =
      companionSingularAlpha (m + 2) a := by
  unfold companionExceptionalSquaredSingularValuePlus
    companionExceptionalSquaredSingularValueMinus
  ring

theorem companionExceptionalSquaredSingularValues_mul
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValuePlus m a *
        companionExceptionalSquaredSingularValueMinus m a = ‖a 0‖ ^ 2 := by
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValuePlus
    companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  nlinarith

private theorem companion_two_sub_alpha_le_exceptional_sqrt
    (m : ℕ) (a : ℕ → ℂ) :
    2 - companionSingularAlpha (m + 2) a ≤
      Real.sqrt (companionExceptionalDiscriminant m a) := by
  have hmem : 0 ∈ Finset.range (m + 2) := by simp
  have hsum : ‖a 0‖ ^ 2 ≤
      ∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 := by
    exact Finset.single_le_sum (fun k hk => sq_nonneg ‖a k‖) hmem
  have hq : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  have hr0 :
      0 ≤ Real.sqrt (companionExceptionalDiscriminant m a) :=
    Real.sqrt_nonneg _
  have hr2 := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalDiscriminant at hr0 hr2 ⊢
  have halpha :
      companionSingularAlpha (m + 2) a =
        1 + ∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 := rfl
  by_cases hnonpos : 2 - companionSingularAlpha (m + 2) a ≤ 0
  · linarith
  · have hpos : 0 < 2 - companionSingularAlpha (m + 2) a :=
      lt_of_not_ge hnonpos
    have hsquare :
        (2 - companionSingularAlpha (m + 2) a) ^ 2 ≤
          Real.sqrt
              (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) ^ 2 := by
      rw [hr2, halpha]
      nlinarith
    nlinarith [sq_nonneg
      (Real.sqrt
          (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) +
        (2 - companionSingularAlpha (m + 2) a))]

private theorem companion_alpha_sub_two_le_exceptional_sqrt
    (m : ℕ) (a : ℕ → ℂ) :
    companionSingularAlpha (m + 2) a - 2 ≤
      Real.sqrt (companionExceptionalDiscriminant m a) := by
  have hmem : 0 ∈ Finset.range (m + 2) := by simp
  have hsum : ‖a 0‖ ^ 2 ≤
      ∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 := by
    exact Finset.single_le_sum (fun k hk => sq_nonneg ‖a k‖) hmem
  have hq : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  have hr0 :
      0 ≤ Real.sqrt (companionExceptionalDiscriminant m a) :=
    Real.sqrt_nonneg _
  have hr2 := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalDiscriminant at hr0 hr2 ⊢
  have halpha :
      companionSingularAlpha (m + 2) a =
        1 + ∑ k ∈ Finset.range (m + 2), ‖a k‖ ^ 2 := rfl
  by_cases hnonpos : companionSingularAlpha (m + 2) a - 2 ≤ 0
  · linarith
  · have hpos : 0 < companionSingularAlpha (m + 2) a - 2 :=
      lt_of_not_ge hnonpos
    have hsquare :
        (companionSingularAlpha (m + 2) a - 2) ^ 2 ≤
          Real.sqrt
              (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) ^ 2 := by
      rw [hr2, halpha]
      nlinarith
    nlinarith [sq_nonneg
      (Real.sqrt
          (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) +
        (companionSingularAlpha (m + 2) a - 2))]

theorem companionExceptionalSquaredSingularValueMinus_nonneg
    (m : ℕ) (a : ℕ → ℂ) :
    0 ≤ companionExceptionalSquaredSingularValueMinus m a := by
  have hq : 0 ≤ ‖a 0‖ ^ 2 := sq_nonneg _
  have halpha : 0 ≤ companionSingularAlpha (m + 2) a := by
    unfold companionSingularAlpha
    positivity
  have hr0 :
      0 ≤ Real.sqrt (companionExceptionalDiscriminant m a) :=
    Real.sqrt_nonneg _
  have hr2 := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalDiscriminant at hr0 hr2
  have hrle :
      Real.sqrt
          (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) ≤
        companionSingularAlpha (m + 2) a := by
    have hsquare :
        Real.sqrt
              (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) ^ 2 ≤
          companionSingularAlpha (m + 2) a ^ 2 := by
      rw [hr2]
      nlinarith
    nlinarith [sq_nonneg
      (Real.sqrt
          (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2) +
        companionSingularAlpha (m + 2) a)]
  unfold companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant
  exact div_nonneg (sub_nonneg.mpr hrle) (by norm_num)

theorem companionExceptionalSquaredSingularValueMinus_le_one
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValueMinus m a ≤ 1 := by
  have h := companion_alpha_sub_two_le_exceptional_sqrt m a
  unfold companionExceptionalSquaredSingularValueMinus
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem one_le_companionExceptionalSquaredSingularValuePlus
    (m : ℕ) (a : ℕ → ℂ) :
    1 ≤ companionExceptionalSquaredSingularValuePlus m a := by
  have h := companion_two_sub_alpha_le_exceptional_sqrt m a
  unfold companionExceptionalSquaredSingularValuePlus
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

theorem companionExceptionalSquaredSingularValueMinus_le_plus
    (m : ℕ) (a : ℕ → ℂ) :
    companionExceptionalSquaredSingularValueMinus m a ≤
      companionExceptionalSquaredSingularValuePlus m a := by
  have hsqrt :
      0 ≤ Real.sqrt (companionExceptionalDiscriminant m a) :=
    Real.sqrt_nonneg _
  unfold companionExceptionalSquaredSingularValueMinus
    companionExceptionalSquaredSingularValuePlus
  linarith

/-- The exceptional quadratic is exactly the product of Higham's two
displayed linear factors. -/
theorem companionExceptionalQuadratic_eq_mul
    (m : ℕ) (a : ℕ → ℂ) :
    X ^ 2 - C (companionSingularAlpha (m + 2) a : ℂ) * X +
        C ((‖a 0‖ ^ 2 : ℝ) : ℂ) =
      (X - C (companionExceptionalSquaredSingularValuePlus m a : ℂ)) *
        (X - C (companionExceptionalSquaredSingularValueMinus m a : ℂ)) := by
  have hsum :
      (companionExceptionalSquaredSingularValuePlus m a : ℂ) +
          companionExceptionalSquaredSingularValueMinus m a =
        (companionSingularAlpha (m + 2) a : ℂ) := by
    exact_mod_cast companionExceptionalSquaredSingularValues_sum m a
  have hmul :
      (companionExceptionalSquaredSingularValuePlus m a : ℂ) *
          companionExceptionalSquaredSingularValueMinus m a =
        ((‖a 0‖ ^ 2 : ℝ) : ℂ) := by
    exact_mod_cast companionExceptionalSquaredSingularValues_mul m a
  rw [← hsum, ← hmul]
  rw [Polynomial.C_add, Polynomial.C_mul]
  ring

/-- Exact linear-factor form of the companion Gram characteristic
polynomial. -/
theorem companion_conjTranspose_mul_self_charpoly_linearFactors
    (m : ℕ) (a : ℕ → ℂ) :
    ((companionMatrix (m + 2) a).conjTranspose *
        companionMatrix (m + 2) a).charpoly =
      (X - C (1 : ℂ)) ^ m *
        ((X - C (companionExceptionalSquaredSingularValuePlus m a : ℂ)) *
          (X - C (companionExceptionalSquaredSingularValueMinus m a : ℂ))) := by
  rw [companion_conjTranspose_mul_self_charpoly,
    companionExceptionalQuadratic_eq_mul]

/-- The roots of the companion Gram characteristic polynomial, with full
algebraic multiplicity: `m` printed unit values and the two exceptional
values.  Degenerate coincidences are retained in the multiset. -/
theorem companion_conjTranspose_mul_self_roots_charpoly
    (m : ℕ) (a : ℕ → ℂ) :
    ((companionMatrix (m + 2) a).conjTranspose *
        companionMatrix (m + 2) a).charpoly.roots =
      Multiset.replicate m (1 : ℂ) +
        {(companionExceptionalSquaredSingularValuePlus m a : ℂ),
          (companionExceptionalSquaredSingularValueMinus m a : ℂ)} := by
  rw [companion_conjTranspose_mul_self_charpoly_linearFactors]
  let p := companionExceptionalSquaredSingularValuePlus m a
  let q := companionExceptionalSquaredSingularValueMinus m a
  have houter :
      (X - C (1 : ℂ)) ^ m *
          ((X - C (p : ℂ)) * (X - C (q : ℂ))) ≠ 0 :=
    mul_ne_zero (pow_ne_zero m (Polynomial.X_sub_C_ne_zero 1))
      (mul_ne_zero (Polynomial.X_sub_C_ne_zero (p : ℂ))
        (Polynomial.X_sub_C_ne_zero (q : ℂ)))
  have hinner :
      (X - C (p : ℂ)) * (X - C (q : ℂ)) ≠ 0 :=
    mul_ne_zero (Polynomial.X_sub_C_ne_zero (p : ℂ))
      (Polynomial.X_sub_C_ne_zero (q : ℂ))
  have hone :
      (X - C (1 : ℂ)).roots = ({1} : Multiset ℂ) :=
    Polynomial.roots_X_sub_C 1
  have hp :
      (X - C (p : ℂ)).roots = ({(p : ℂ)} : Multiset ℂ) :=
    Polynomial.roots_X_sub_C (p : ℂ)
  have hq :
      (X - C (q : ℂ)).roots = ({(q : ℂ)} : Multiset ℂ) :=
    Polynomial.roots_X_sub_C (q : ℂ)
  change
    ((X - C (1 : ℂ)) ^ m *
        ((X - C (p : ℂ)) * (X - C (q : ℂ)))).roots = _
  rw [Polynomial.roots_mul houter, Polynomial.roots_pow,
    Polynomial.roots_mul hinner, hone, hp, hq, Multiset.nsmul_singleton]
  simp [p, q, Multiset.singleton_add]

/-- Exact canonical squared-singular-value multiset.  This is the strict
multiplicity/occurrence form of Higham's printed list: `m = n - 2` unit
entries followed by the two exceptional entries, including coincidences. -/
theorem companionSquaredSingularValues_multiset_eq
    (m : ℕ) (a : ℕ → ℂ) :
    Multiset.map (companionSquaredSingularValues m a) Finset.univ.val =
      Multiset.replicate m (1 : ℝ) +
        {companionExceptionalSquaredSingularValuePlus m a,
          companionExceptionalSquaredSingularValueMinus m a} := by
  let M := companionMatrix (m + 2) a
  let G := M.conjTranspose * M
  let hG : G.IsHermitian := Matrix.isHermitian_conjTranspose_mul_self M
  apply Multiset.map_injective Complex.ofReal_injective
  simp only [Multiset.map_map]
  change
    Multiset.map (Complex.ofReal ∘ hG.eigenvalues) Finset.univ.val =
      Multiset.map Complex.ofReal
        (Multiset.replicate m (1 : ℝ) +
          {companionExceptionalSquaredSingularValuePlus m a,
            companionExceptionalSquaredSingularValueMinus m a})
  have hspectral :
      G.charpoly.roots =
        Multiset.map (Complex.ofReal ∘ hG.eigenvalues) Finset.univ.val := by
    simpa only [RCLike.ofReal_eq_complex_ofReal] using
      hG.roots_charpoly_eq_eigenvalues
  rw [← hspectral]
  rw [show G =
      (companionMatrix (m + 2) a).conjTranspose *
        companionMatrix (m + 2) a by rfl]
  rw [companion_conjTranspose_mul_self_roots_charpoly]
  simp [Multiset.map_add]

theorem companionExceptionalSquaredSingularValuePlus_occurs
    (m : ℕ) (a : ℕ → ℂ) :
    ∃ i : Fin (m + 2),
      companionSquaredSingularValues m a i =
        companionExceptionalSquaredSingularValuePlus m a := by
  have hmem :
      companionExceptionalSquaredSingularValuePlus m a ∈
        Multiset.map (companionSquaredSingularValues m a) Finset.univ.val := by
    rw [companionSquaredSingularValues_multiset_eq]
    simp
  rcases Multiset.mem_map.mp hmem with ⟨i, hi, heq⟩
  exact ⟨i, heq⟩

theorem companionExceptionalSquaredSingularValueMinus_occurs
    (m : ℕ) (a : ℕ → ℂ) :
    ∃ i : Fin (m + 2),
      companionSquaredSingularValues m a i =
        companionExceptionalSquaredSingularValueMinus m a := by
  have hmem :
      companionExceptionalSquaredSingularValueMinus m a ∈
        Multiset.map (companionSquaredSingularValues m a) Finset.univ.val := by
    rw [companionSquaredSingularValues_multiset_eq]
    simp
  rcases Multiset.mem_map.mp hmem with ⟨i, hi, heq⟩
  exact ⟨i, heq⟩

/-- Exact algebraic multiplicity of the numerical value `1`.  The two
indicator terms are necessary: an exceptional value can itself degenerate
to `1`, although the displayed middle block always contributes `m` copies. -/
theorem companionSquaredSingularValues_count_one
    (m : ℕ) (a : ℕ → ℂ) :
    Multiset.count (1 : ℝ)
        (Multiset.map (companionSquaredSingularValues m a) Finset.univ.val) =
      m +
        (if (1 : ℝ) = companionExceptionalSquaredSingularValuePlus m a then 1 else 0) +
        (if (1 : ℝ) = companionExceptionalSquaredSingularValueMinus m a then 1 else 0) := by
  rw [companionSquaredSingularValues_multiset_eq, Multiset.count_add,
    Multiset.count_replicate]
  simp only [if_pos]
  change
    m + Multiset.count (1 : ℝ)
        (companionExceptionalSquaredSingularValuePlus m a ::ₘ
          {companionExceptionalSquaredSingularValueMinus m a}) = _
  rw [Multiset.count_cons, Multiset.count_singleton]
  ac_rfl

theorem companionSquaredSingularValues_count_one_eq_sub_two
    (m : ℕ) (a : ℕ → ℂ)
    (hplus : companionExceptionalSquaredSingularValuePlus m a ≠ 1)
    (hminus : companionExceptionalSquaredSingularValueMinus m a ≠ 1) :
    Multiset.count (1 : ℝ)
        (Multiset.map (companionSquaredSingularValues m a) Finset.univ.val) = m := by
  rw [companionSquaredSingularValues_count_one]
  simp [Ne.symm hplus, Ne.symm hminus]

/-- Higham's explicit classification: a squared singular value other than
one equals one of the two displayed exceptional roots. -/
theorem companionSquaredSingularValues_eq_one_or_eq_plus_or_eq_minus
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) :
    companionSquaredSingularValues m a i = 1 ∨
      companionSquaredSingularValues m a i =
        companionExceptionalSquaredSingularValuePlus m a ∨
      companionSquaredSingularValues m a i =
        companionExceptionalSquaredSingularValueMinus m a := by
  rcases companionSquaredSingularValues_eq_one_or_exceptional m a i with h | h
  · exact Or.inl h
  right
  have hreal :
      companionSquaredSingularValues m a i ^ 2 -
          companionSingularAlpha (m + 2) a *
            companionSquaredSingularValues m a i + ‖a 0‖ ^ 2 = 0 := by
    exact_mod_cast h
  have hsqrt := Real.sq_sqrt (companionExceptionalDiscriminant_nonneg m a)
  unfold companionExceptionalSquaredSingularValuePlus
    companionExceptionalSquaredSingularValueMinus
  unfold companionExceptionalDiscriminant at hsqrt ⊢
  have hfactor :
      (2 * companionSquaredSingularValues m a i -
          companionSingularAlpha (m + 2) a -
          Real.sqrt
            (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2)) *
        (2 * companionSquaredSingularValues m a i -
          companionSingularAlpha (m + 2) a +
          Real.sqrt
            (companionSingularAlpha (m + 2) a ^ 2 - 4 * ‖a 0‖ ^ 2)) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hp | hm
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Singular values themselves, obtained as the nonnegative square roots of
the canonical Gram eigenvalues. -/
noncomputable def companionSingularValues
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) : ℝ :=
  Real.sqrt (companionSquaredSingularValues m a i)

/-- Exact singular-value multiset corresponding to the squared-value
factorization: `m` unit singular values and the two displayed exceptional
square roots, with degeneracies preserved. -/
theorem companionSingularValues_multiset_eq
    (m : ℕ) (a : ℕ → ℂ) :
    Multiset.map (companionSingularValues m a) Finset.univ.val =
      Multiset.replicate m (1 : ℝ) +
        {Real.sqrt (companionExceptionalSquaredSingularValuePlus m a),
          Real.sqrt (companionExceptionalSquaredSingularValueMinus m a)} := by
  change
    Multiset.map
        (Real.sqrt ∘ companionSquaredSingularValues m a) Finset.univ.val = _
  rw [← Multiset.map_map]
  rw [companionSquaredSingularValues_multiset_eq]
  simp [Multiset.map_add, Multiset.map_replicate]

/-- Higham's displayed exceptional singular-value formula: all singular
values are one except for values drawn from the two explicit square roots. -/
theorem companionSingularValues_eq_one_or_eq_exceptional
    (m : ℕ) (a : ℕ → ℂ) (i : Fin (m + 2)) :
    companionSingularValues m a i = 1 ∨
      companionSingularValues m a i =
          Real.sqrt (companionExceptionalSquaredSingularValuePlus m a) ∨
      companionSingularValues m a i =
          Real.sqrt (companionExceptionalSquaredSingularValueMinus m a) := by
  rcases companionSquaredSingularValues_eq_one_or_eq_plus_or_eq_minus m a i with
    h | h | h
  · left
    simp [companionSingularValues, h]
  · right
    left
    simp [companionSingularValues, h]
  · right
    right
    simp [companionSingularValues, h]

/-- Exact order-two correction to the false normality characterization on
Higham p. 523. At order two, normality permits a nonzero higher coefficient:
the complete condition is `|a₀|²=1` together with
`conj(a₁) a₀ = a₁`. -/
theorem companion_orderTwo_isStarNormal_iff (a : ℕ → ℂ) :
    IsStarNormal (companionMatrix 2 a) ↔
      star (a 0) * a 0 = 1 ∧ star (a 1) * a 0 = a 1 := by
  rw [isStarNormal_iff]
  change
    (companionMatrix 2 a).conjTranspose * companionMatrix 2 a =
        companionMatrix 2 a * (companionMatrix 2 a).conjTranspose ↔ _
  constructor
  · intro h
    constructor
    · have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h
      simpa [companionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply] using h11
    · have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 1) h
      simpa [companionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply] using h01
  · rintro ⟨h0, h1⟩
    have h0' : a 0 * star (a 0) = 1 := by simpa [mul_comm] using h0
    have h1star := congrArg star h1
    simp only [star_mul, star_star] at h1star
    ext i j
    fin_cases i <;> fin_cases j
    · simp [companionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]
      change star (a 1) * a 1 + 1 =
        a 1 * star (a 1) + a 0 * star (a 0)
      rw [h0']
      ring
    · simpa [companionMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply] using h1
    · simpa [companionMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply] using h1star
    · simpa [companionMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply] using h0

private theorem companion_normal_higher_a0_unit (m : ℕ) (a : ℕ → ℂ)
    (h : (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
      companionMatrix (m + 3) a * (companionMatrix (m + 3) a).conjTranspose) :
    star (a 0) * a 0 = 1 := by
  let ell : Fin (m + 3) := Fin.last (m + 2)
  have hd := congrArg
    (fun M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ => M ell ell) h
  rw [companion_conjTranspose_mul_self] at hd
  simp [companionGramFormula, ell, companionMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply] at hd
  let p : Fin (m + 3) := ⟨m + 1, by omega⟩
  have hp : ∀ x : Fin (m + 3), m + 1 = x.val ↔ x = p := by
    intro x
    constructor
    · intro hx
      exact Fin.ext hx.symm
    · rintro rfl
      rfl
  simp_rw [hp] at hd
  simp at hd
  exact hd

private theorem companion_normal_higher_coeff_vanish
    (m k : ℕ) (a : ℕ → ℂ) (hk0 : 0 < k) (hk : k < m + 2)
    (h : (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
      companionMatrix (m + 3) a * (companionMatrix (m + 3) a).conjTranspose) :
    a k = 0 := by
  let i : Fin (m + 3) := ⟨m + 2 - k, by omega⟩
  have hi0 : 0 < i.val := by simp [i]; omega
  have hicond : i.val + 1 < m + 3 := by simp [i]; omega
  have hd := congrArg
    (fun M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ => M i i) h
  rw [companion_conjTranspose_mul_self] at hd
  simp [companionGramFormula, companionMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, hicond, hi0.ne'] at hd
  let p : Fin (m + 3) := ⟨i.val - 1, by omega⟩
  have hp : ∀ x : Fin (m + 3), i.val = x.val + 1 ↔ x = p := by
    intro x
    constructor
    · intro hx
      apply Fin.ext
      simp [p]
      omega
    · rintro rfl
      simp [p]
      omega
  simp_rw [hp] at hd
  simp at hd
  have hrev : m + 2 - i.val = k := by simp [i]; omega
  simpa [hrev] using hd

private theorem companion_normal_higher_last_coeff_vanish (m : ℕ) (a : ℕ → ℂ)
    (h : (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
      companionMatrix (m + 3) a * (companionMatrix (m + 3) a).conjTranspose) :
    a (m + 2) = 0 := by
  let ell : Fin (m + 3) := Fin.last (m + 2)
  let z : Fin (m + 3) := ⟨0, by omega⟩
  have ha1 : a 1 = 0 :=
    companion_normal_higher_coeff_vanish m 1 a (by omega) (by omega) h
  have he := congrArg
    (fun M : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ => M ell z) h
  rw [companion_conjTranspose_mul_self] at he
  simp [companionGramFormula, companionMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, ell, z] at he
  let p : Fin (m + 3) := ⟨m + 1, by omega⟩
  have hp : ∀ x : Fin (m + 3), m + 1 = x.val ↔ x = p := by
    intro x
    constructor
    · intro hx
      exact Fin.ext hx.symm
    · rintro rfl
      rfl
  simp_rw [hp] at he
  simp at he
  have hindex : m + 2 - p.val = 1 := by simp [p]
  rw [hindex, ha1] at he
  have ha0unit := companion_normal_higher_a0_unit m a h
  have ha0ne : star (a 0) ≠ 0 := by
    intro ha0
    rw [ha0, zero_mul] at ha0unit
    norm_num at ha0unit
  have he' : star (a 0) * a (m + 2) = 0 := by simpa using he
  exact (mul_eq_zero.mp he').resolve_left ha0ne

/-- Exact higher-order repair of the false normality statement on p. 523.
For orders at least three, a companion is normal exactly when the constant
coefficient has unit modulus and every higher coefficient vanishes. Order two
is governed separately by `companion_orderTwo_isStarNormal_iff`. -/
theorem companion_orderAtLeastThree_isStarNormal_iff
    (m : ℕ) (a : ℕ → ℂ) :
    IsStarNormal (companionMatrix (m + 3) a) ↔
      star (a 0) * a 0 = 1 ∧
        ∀ k, 0 < k → k < m + 3 → a k = 0 := by
  rw [isStarNormal_iff]
  change
    (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
        companionMatrix (m + 3) a *
          (companionMatrix (m + 3) a).conjTranspose ↔ _
  constructor
  · intro h
    refine ⟨companion_normal_higher_a0_unit m a h, ?_⟩
    intro k hk0 hk
    by_cases hlast : k = m + 2
    · simpa [hlast] using companion_normal_higher_last_coeff_vanish m a h
    · exact companion_normal_higher_coeff_vanish m k a hk0 (by omega) h
  · rintro ⟨ha0, ha⟩
    let ell : Fin (m + 3) := Fin.last (m + 2)
    have hcoeff : ∀ i : Fin (m + 3),
        a (m + 3 - 1 - i.val) = if i = ell then a 0 else 0 := by
      intro i
      by_cases hi : i = ell
      · subst i
        simp [ell]
      · rw [if_neg hi]
        apply ha
        · have hiv : i.val ≠ m + 2 := by
            intro hiv
            apply hi
            apply Fin.ext
            simpa [ell] using hiv
          omega
        · omega
    have hleft :
        (companionMatrix (m + 3) a).conjTranspose * companionMatrix (m + 3) a =
          (1 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) := by
      rw [companion_conjTranspose_mul_self]
      ext i j
      simp only [companionGramFormula, Matrix.one_apply]
      rw [hcoeff i, hcoeff j]
      have hicond : i.val + 1 < m + 3 ↔ i ≠ ell := by
        constructor
        · intro hi hlast
          subst i
          simp [ell] at hi
        · intro hine
          have hval : i.val ≠ m + 2 := by
            intro hval
            apply hine
            apply Fin.ext
            simpa [ell] using hval
          omega
      simp only [hicond]
      by_cases hi : i = ell
      · by_cases hj : j = ell
        · subst i
          subst j
          simpa using ha0
        · have hji : ell ≠ j := Ne.symm hj
          simp [hi, hj, hji]
      · by_cases hj : j = ell
        · simp [hi, hj]
        · simp [hi, hj]
    have hright :
        companionMatrix (m + 3) a *
            (companionMatrix (m + 3) a).conjTranspose =
          (1 : Matrix (Fin (m + 3)) (Fin (m + 3)) ℂ) :=
      mul_eq_one_comm.mp hleft
    rw [hleft, hright]

end

end NumStability
