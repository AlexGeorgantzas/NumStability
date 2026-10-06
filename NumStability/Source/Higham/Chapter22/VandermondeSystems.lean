/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.Coprime.Lemmas
import NumStability.Analysis.Norms
import NumStability.Algorithms.LU.TridiagonalCond
import Mathlib.Topology.Basic

namespace NumStability

open scoped BigOperators Topology
open Filter

/-! # Higham Chapter 22: Vandermonde systems

Canonical source-correspondence owner for the chapter's Vandermonde-system
development.

This module records the exact algebraic core of the chapter: Higham's column-node
orientation, nonsingularity, Lagrange cardinal functions, Algorithms 22.1,
22.2, 22.3, and 22.8, and their polynomial/recurrence objects. Citation-only
condition estimates and the rounded factor analyses remain explicit source
obligations.  The exact Stage-I/II factors below are produced from the loops;
no final solve or error inequality is stored as a domain field.
-/

section Vandermonde

variable {n : ℕ}

/-- Higham, 2nd ed., Chapter 22, p. 416: the Vandermonde matrix whose columns
are indexed by the nodes and whose rows are powers.  Mathlib's Vandermonde
matrix uses the transpose orientation, so this is a source-facing adapter. -/
def higham22Vandermonde (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.transpose (Matrix.vandermonde alpha)

@[simp]
theorem higham22Vandermonde_apply (alpha : Fin n → ℂ) (i j : Fin n) :
    higham22Vandermonde alpha i j = alpha j ^ (i : ℕ) := by
  rfl

/-- The source Vandermonde determinant is nonzero exactly when the nodes are
distinct.  This closes the precise nonsingularity prose immediately after
equation (22.1). -/
theorem higham22_vandermonde_det_ne_zero_iff {alpha : Fin n → ℂ} :
    (higham22Vandermonde alpha).det ≠ 0 ↔ Function.Injective alpha := by
  simpa [higham22Vandermonde, Matrix.det_transpose] using
    (Matrix.det_vandermonde_ne_zero_iff (v := alpha))

/-- Equation (22.1), evaluated rather than represented as a polynomial: the
`i`th Lagrange cardinal function. -/
noncomputable def higham22LagrangeValue
    (alpha : Fin n → ℂ) (i : Fin n) (x : ℂ) : ℂ :=
  ∏ k : Fin n, if k = i then 1 else (x - alpha k) / (alpha i - alpha k)

/-- Equation (22.1) at its own interpolation node. -/
theorem higham22_lagrangeValue_self
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    higham22LagrangeValue alpha i (alpha i) = 1 := by
  unfold higham22LagrangeValue
  apply Finset.prod_eq_one
  intro k _hk
  by_cases hki : k = i
  · simp [hki]
  · have hne : alpha i - alpha k ≠ 0 := by
      exact sub_ne_zero.mpr (halpha.ne (Ne.symm hki))
    simp [hki, hne]

/-- Equation (22.1) vanishes at every other interpolation node. -/
theorem higham22_lagrangeValue_other
    {alpha : Fin n → ℂ} (i j : Fin n) (hji : j ≠ i) :
    higham22LagrangeValue alpha i (alpha j) = 0 := by
  unfold higham22LagrangeValue
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [hji]

/-- Cardinal form of equation (22.1). -/
theorem higham22_lagrangeValue_node
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i j : Fin n) :
    higham22LagrangeValue alpha i (alpha j) = if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    simp [higham22_lagrangeValue_self halpha]
  · simp [hji, higham22_lagrangeValue_other i j hji]

/-- Higham, 2nd ed., Algorithm 22.1, p. 417, stage I: the monic master
polynomial formed by successively adjoining all interpolation nodes. -/
noncomputable def higham22Algorithm1MasterPolynomial
    (alpha : Fin n → ℂ) : Polynomial ℂ :=
  ∏ k : Fin n, (Polynomial.X - Polynomial.C (alpha k))

/-- Higham, 2nd ed., Algorithm 22.1, p. 417, stage II: synthetic division of
the master polynomial by the factor belonging to node `i`. -/
noncomputable def higham22Algorithm1SyntheticQuotient
    (alpha : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
  higham22Algorithm1MasterPolynomial alpha /ₘ
    (Polynomial.X - Polynomial.C (alpha i))

/-- The synthetic quotient is exactly the product with factor `i` removed. -/
theorem higham22_algorithm1SyntheticQuotient_eq_prod_erase
    (alpha : Fin n → ℂ) (i : Fin n) :
    higham22Algorithm1SyntheticQuotient alpha i =
      ∏ k ∈ (Finset.univ.erase i),
        (Polynomial.X - Polynomial.C (alpha k)) := by
  unfold higham22Algorithm1SyntheticQuotient higham22Algorithm1MasterPolynomial
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  exact Polynomial.mul_divByMonic_cancel_left _
    (Polynomial.monic_X_sub_C (alpha i))

/-- The exact denominator used to normalize the row produced for node `i`. -/
noncomputable def higham22Algorithm1Denominator
    (alpha : Fin n → ℂ) (i : Fin n) : ℂ :=
  (higham22Algorithm1SyntheticQuotient alpha i).eval (alpha i)

/-- Distinct nodes make every normalization denominator in Algorithm 22.1
nonzero. -/
theorem higham22_algorithm1Denominator_ne_zero
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    higham22Algorithm1Denominator alpha i ≠ 0 := by
  rw [higham22Algorithm1Denominator,
    higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply sub_ne_zero.mpr
  exact halpha.ne (Ne.symm (Finset.ne_of_mem_erase hk))

/-- The quotient evaluated at a different node vanishes. -/
theorem higham22_algorithm1SyntheticQuotient_eval_other
    (alpha : Fin n → ℂ) (i j : Fin n) (hji : j ≠ i) :
    (higham22Algorithm1SyntheticQuotient alpha i).eval (alpha j) = 0 := by
  rw [higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  simp

/-- Multiset of interpolation nodes with node `i` omitted. -/
noncomputable def higham22NodesExcept
    (alpha : Fin n → ℂ) (i : Fin n) : Multiset ℂ :=
  (Finset.univ.erase i).val.map alpha

/-- The elementary symmetric function appearing in equation (22.2). -/
noncomputable def higham22ElementarySymmetricExcept
    (alpha : Fin n → ℂ) (i : Fin n) (r : ℕ) : ℂ :=
  (higham22NodesExcept alpha i).esymm r

/-- Vieta coefficient formula for the synthetic quotient. -/
theorem higham22_algorithm1SyntheticQuotient_coeff
    (alpha : Fin n → ℂ) (i j : Fin n) :
    (higham22Algorithm1SyntheticQuotient alpha i).coeff (j : ℕ) =
      (-1) ^ (n - 1 - (j : ℕ)) *
        higham22ElementarySymmetricExcept alpha i (n - 1 - (j : ℕ)) := by
  rw [higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  have hcard : (higham22NodesExcept alpha i).card = n - 1 := by
    simp [higham22NodesExcept]
  have hj : (j : ℕ) ≤ (higham22NodesExcept alpha i).card := by
    rw [hcard]
    omega
  have hv := Multiset.prod_X_sub_C_coeff (higham22NodesExcept alpha i) hj
  rw [hcard] at hv
  simpa [higham22NodesExcept, higham22ElementarySymmetricExcept] using hv

/-- Product form of the normalization denominator in Algorithm 22.1. -/
theorem higham22_algorithm1Denominator_eq_prod
    (alpha : Fin n → ℂ) (i : Fin n) :
    higham22Algorithm1Denominator alpha i =
      ∏ k ∈ Finset.univ.erase i, (alpha i - alpha k) := by
  rw [higham22Algorithm1Denominator,
    higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  simp [Polynomial.eval_prod]

/-- The printed two-stage Algorithm 22.1: form the master polynomial, apply
synthetic division for each node, and normalize the quotient coefficients.
Rows are indexed by nodes and columns by powers, matching `V⁻¹`. -/
noncomputable def higham22Algorithm1Printed
    (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j ↦
    (higham22Algorithm1SyntheticQuotient alpha i).coeff (j : ℕ) /
      higham22Algorithm1Denominator alpha i

/-- Higham, 2nd ed., equation (22.2), pp. 416--417: the explicit inverse
entry in terms of an elementary symmetric function.  Our `n × n` convention
corresponds to the source's indices `0,...,n-1`. -/
theorem higham22_eq22_2_inverse_entry
    (alpha : Fin n → ℂ) (i j : Fin n) :
    higham22Algorithm1Printed alpha i j =
      ((-1) ^ (n - 1 - (j : ℕ)) *
        higham22ElementarySymmetricExcept alpha i (n - 1 - (j : ℕ))) /
      (∏ k ∈ Finset.univ.erase i, (alpha i - alpha k)) := by
  rw [higham22Algorithm1Printed,
    higham22_algorithm1SyntheticQuotient_coeff,
    higham22_algorithm1Denominator_eq_prod]

/-- Norm of an elementary symmetric function is bounded by the corresponding
elementary symmetric function of the norms. -/
theorem higham22_norm_esymm_le (s : Multiset ℂ) (r : ℕ) :
    ‖s.esymm r‖ ≤ (s.map norm).esymm r := by
  have hnormprod : ∀ t : Multiset ℂ, ‖t.prod‖ = (t.map norm).prod := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | @cons a t ih => simp [ih]
  unfold Multiset.esymm
  calc
    ‖((s.powersetCard r).map Multiset.prod).sum‖ ≤
        (((s.powersetCard r).map Multiset.prod).map norm).sum :=
      norm_multiset_sum_le _
    _ = ((((s.map norm).powersetCard r).map Multiset.prod).sum) := by
      rw [Multiset.powersetCard_map]
      simp only [Multiset.map_map]
      apply congrArg Multiset.sum
      apply Multiset.map_congr rfl
      intro t _ht
      exact hnormprod t

/-- Sum of all elementary symmetric functions equals the product of `1+x`. -/
theorem higham22_sum_esymm_eq_prod_one_add (s : Multiset ℝ) :
    (∑ r : Fin (s.card + 1), s.esymm (r : ℕ)) =
      (s.map fun x ↦ 1 + x).prod := by
  have h := congrArg (Polynomial.eval (1 : ℝ))
    (Multiset.prod_X_add_C_eq_sum_esymm s)
  simpa [Polynomial.eval_finset_sum, Polynomial.eval_multiset_prod,
    ← Fin.sum_univ_eq_sum_range,
    Multiset.map_map] using h.symm

/-- The synthetic quotient has degree below the matrix dimension. -/
theorem higham22_algorithm1SyntheticQuotient_natDegree_lt
    (alpha : Fin n → ℂ) (i : Fin n) :
    (higham22Algorithm1SyntheticQuotient alpha i).natDegree < n := by
  unfold higham22Algorithm1SyntheticQuotient
  rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C (alpha i)),
    show (higham22Algorithm1MasterPolynomial alpha).natDegree = n by
      unfold higham22Algorithm1MasterPolynomial
      rw [Polynomial.natDegree_prod_of_monic]
      · simp
      · intro k _hk
        exact Polynomial.monic_X_sub_C (alpha k),
    Polynomial.natDegree_X_sub_C]
  exact Nat.sub_lt (Fin.pos i) Nat.zero_lt_one

/-- The Mahler measure of a synthetic quotient is the product occurring in
the lower estimate of equation (22.3). -/
theorem higham22_algorithm1SyntheticQuotient_mahlerMeasure
    (alpha : Fin n → ℂ) (i : Fin n) :
    (higham22Algorithm1SyntheticQuotient alpha i).mahlerMeasure =
      ∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖ := by
  rw [higham22_algorithm1SyntheticQuotient_eq_prod_erase]
  induction Finset.univ.erase i using Finset.induction_on with
  | empty => simp
  | @insert k s hks ih =>
      simp only [Finset.prod_insert hks, Polynomial.mahlerMeasure_mul,
        Polynomial.mahlerMeasure_X_sub_C, ih]

/-- The sum of the coefficient norms of a synthetic quotient is bounded below
by its Mahler-measure product. -/
theorem higham22_algorithm1SyntheticQuotient_coeff_norm_sum_lower
    (alpha : Fin n → ℂ) (i : Fin n) :
    (∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖) ≤
      ∑ j : Fin n, ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖ := by
  let q := higham22Algorithm1SyntheticQuotient alpha i
  have hdegree : q.degree < (n : WithBot ℕ) := by
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast higham22_algorithm1SyntheticQuotient_natDegree_lt alpha i)
  calc
    (∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖) = q.mahlerMeasure := by
      symm
      exact higham22_algorithm1SyntheticQuotient_mahlerMeasure alpha i
    _ ≤ q.sum (fun _ a ↦ ‖a‖) := Polynomial.mahlerMeasure_le_sum_norm_coeff q
    _ = ∑ j : Fin n, ‖q.coeff j‖ := by
      symm
      exact Polynomial.sum_fin (fun (_ : ℕ) (a : ℂ) ↦ ‖a‖) (by simp) hdegree

/-- Vieta's formula bounds the coefficient one-norm of a synthetic quotient
by the product occurring in the upper estimate of equation (22.3). -/
theorem higham22_algorithm1SyntheticQuotient_coeff_norm_sum_upper
    (alpha : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖) ≤
      ∏ k ∈ Finset.univ.erase i, (1 + ‖alpha k‖) := by
  let s := higham22NodesExcept alpha i
  have hpoint (j : Fin n) :
      ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖ ≤
        (s.map norm).esymm (n - 1 - (j : ℕ)) := by
    rw [higham22_algorithm1SyntheticQuotient_coeff]
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    exact higham22_norm_esymm_le s (n - 1 - (j : ℕ))
  calc
    (∑ j : Fin n, ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖) ≤
        ∑ j : Fin n, (s.map norm).esymm (n - 1 - (j : ℕ)) :=
      Finset.sum_le_sum fun j _hj ↦ hpoint j
    _ = ∑ r : Fin n, (s.map norm).esymm (r : ℕ) := by
      rw [← Equiv.sum_comp Fin.revPerm]
      apply Finset.sum_congr rfl
      intro j _hj
      simp [Fin.revPerm]
      congr 1
      omega
    _ = (s.map (fun z ↦ 1 + ‖z‖)).prod := by
      have h := higham22_sum_esymm_eq_prod_one_add (s.map norm)
      have hcard : (s.map norm).card + 1 = n := by
        have hn : 1 ≤ n := Nat.succ_le_iff.mpr (Fin.pos i)
        simp [s, higham22NodesExcept, Nat.sub_add_cancel hn]
      rw [hcard] at h
      simpa [Multiset.map_map] using h
    _ = ∏ k ∈ Finset.univ.erase i, (1 + ‖alpha k‖) := by
      simp only [s, higham22NodesExcept, Multiset.map_map]
      exact Finset.prod_map_val (Finset.univ.erase i) (fun k ↦ 1 + ‖alpha k‖)

/-- The rowwise lower product in Higham's equation (22.3). -/
noncomputable def higham22Eq22_3LowerRow
    (alpha : Fin n → ℂ) (i : Fin n) : ℝ :=
  (∏ k ∈ Finset.univ.erase i, max 1 ‖alpha k‖) /
    (∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖)

/-- The rowwise upper product in Higham's equation (22.3). -/
noncomputable def higham22Eq22_3UpperRow
    (alpha : Fin n → ℂ) (i : Fin n) : ℝ :=
  (∏ k ∈ Finset.univ.erase i, (1 + ‖alpha k‖)) /
    (∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖)

theorem higham22_eq22_3LowerRow_nonneg
    (alpha : Fin n → ℂ) (i : Fin n) :
    0 ≤ higham22Eq22_3LowerRow alpha i := by
  unfold higham22Eq22_3LowerRow
  positivity

theorem higham22_eq22_3UpperRow_nonneg
    (alpha : Fin n → ℂ) (i : Fin n) :
    0 ≤ higham22Eq22_3UpperRow alpha i := by
  unfold higham22Eq22_3UpperRow
  positivity

/-- The absolute row sum of the printed inverse is the coefficient one-norm
divided by the product of node separations. -/
theorem higham22_algorithm1Printed_row_norm_eq
    (alpha : Fin n → ℂ) (i : Fin n) :
    (∑ j : Fin n, ‖higham22Algorithm1Printed alpha i j‖) =
      (∑ j : Fin n,
          ‖(higham22Algorithm1SyntheticQuotient alpha i).coeff j‖) /
        (∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖) := by
  simp only [higham22Algorithm1Printed, norm_div]
  rw [Finset.sum_div, higham22_algorithm1Denominator_eq_prod]
  simp

/-- Pointwise lower half of equation (22.3). -/
theorem higham22_eq22_3_row_lower
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    higham22Eq22_3LowerRow alpha i ≤
      ∑ j : Fin n, ‖higham22Algorithm1Printed alpha i j‖ := by
  rw [higham22_algorithm1Printed_row_norm_eq]
  unfold higham22Eq22_3LowerRow
  have hden : 0 < ∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖ := by
    apply Finset.prod_pos
    intro k hk
    exact norm_pos_iff.mpr <| sub_ne_zero.mpr <|
      halpha.ne (Ne.symm (Finset.ne_of_mem_erase hk))
  exact (div_le_div_iff_of_pos_right hden).mpr
    (higham22_algorithm1SyntheticQuotient_coeff_norm_sum_lower alpha i)

/-- Pointwise upper half of equation (22.3). -/
theorem higham22_eq22_3_row_upper
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i : Fin n) :
    (∑ j : Fin n, ‖higham22Algorithm1Printed alpha i j‖) ≤
      higham22Eq22_3UpperRow alpha i := by
  rw [higham22_algorithm1Printed_row_norm_eq]
  unfold higham22Eq22_3UpperRow
  have hden : 0 < ∏ k ∈ Finset.univ.erase i, ‖alpha i - alpha k‖ := by
    apply Finset.prod_pos
    intro k hk
    exact norm_pos_iff.mpr <| sub_ne_zero.mpr <|
      halpha.ne (Ne.symm (Finset.ne_of_mem_erase hk))
  exact (div_le_div_iff_of_pos_right hden).mpr
    (higham22_algorithm1SyntheticQuotient_coeff_norm_sum_upper alpha i)

/-- The maximum lower product in equation (22.3). -/
noncomputable def higham22Eq22_3LowerBound (alpha : Fin n → ℂ) : ℝ :=
  ((Finset.univ.sup
    (fun i : Fin n ↦ Real.toNNReal (higham22Eq22_3LowerRow alpha i)) : NNReal) : ℝ)

/-- The maximum upper product in equation (22.3). -/
noncomputable def higham22Eq22_3UpperBound (alpha : Fin n → ℂ) : ℝ :=
  ((Finset.univ.sup
    (fun i : Fin n ↦ Real.toNNReal (higham22Eq22_3UpperRow alpha i)) : NNReal) : ℝ)

/-- Higham, 2nd ed., equation (22.3): the exact two-sided infinity-norm
bound for the inverse produced by Algorithm 22.1. -/
theorem higham22_eq22_3
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Eq22_3LowerBound alpha ≤
        complexMatrixInfNorm (higham22Algorithm1Printed alpha) ∧
      complexMatrixInfNorm (higham22Algorithm1Printed alpha) ≤
        higham22Eq22_3UpperBound alpha := by
  constructor
  · unfold higham22Eq22_3LowerBound
    let f : Fin n → NNReal :=
      fun i ↦ Real.toNNReal (higham22Eq22_3LowerRow alpha i)
    have hsup : Finset.univ.sup f ≤
        Real.toNNReal (complexMatrixInfNorm (higham22Algorithm1Printed alpha)) := by
      apply Finset.sup_le
      intro i _hi
      exact Real.toNNReal_le_toNNReal <|
        (higham22_eq22_3_row_lower halpha i).trans
          (complexMatrixInfNorm_row_sum_le (higham22Algorithm1Printed alpha) i)
    have hreal : ((Finset.univ.sup f : NNReal) : ℝ) ≤
        ((Real.toNNReal
          (complexMatrixInfNorm (higham22Algorithm1Printed alpha)) : NNReal) : ℝ) := by
      exact_mod_cast hsup
    rw [Real.coe_toNNReal _
      (complexMatrixInfNorm_nonneg (higham22Algorithm1Printed alpha))] at hreal
    simpa [f] using hreal
  · unfold higham22Eq22_3UpperBound
    let f : Fin n → NNReal :=
      fun i ↦ Real.toNNReal (higham22Eq22_3UpperRow alpha i)
    apply complexMatrixInfNorm_le_of_row_sum_le (NNReal.coe_nonneg _)
    intro i
    refine (higham22_eq22_3_row_upper halpha i).trans ?_
    have hsup : f i ≤ Finset.univ.sup f :=
      Finset.le_sup (s := (Finset.univ : Finset (Fin n))) (f := f)
        (Finset.mem_univ i)
    have hreal : ((f i : NNReal) : ℝ) ≤
        ((Finset.univ.sup f : NNReal) : ℝ) := by
      exact_mod_cast hsup
    rw [Real.coe_toNNReal _ (higham22_eq22_3UpperRow_nonneg alpha i)] at hreal
    simpa [f] using hreal

/-- Root-of-unity nodes for Table 22.1 row (V7). -/
noncomputable def higham22RootUnityNodes (n : ℕ) (ζ : ℂ) : Fin n → ℂ :=
  fun j ↦ ζ ^ (j : ℕ)

/-- The root-of-unity Vandermonde is exactly the repository Fourier matrix. -/
theorem higham22_rootUnityVandermonde_eq_fourier (n : ℕ) (ζ : ℂ) :
    higham22Vandermonde (higham22RootUnityNodes n ζ) =
      complexFourierVandermondeMatrix n ζ := by
  ext i j
  change (ζ ^ (j : ℕ)) ^ (i : ℕ) = ζ ^ ((i : ℕ) * (j : ℕ))
  calc
    (ζ ^ (j : ℕ)) ^ (i : ℕ) = ζ ^ ((j : ℕ) * (i : ℕ)) := (pow_mul _ _ _).symm
    _ = ζ ^ ((i : ℕ) * (j : ℕ)) := by rw [Nat.mul_comm]

/-- Explicit inverse candidate for the root-of-unity Vandermonde. -/
noncomputable def higham22RootUnityInverse (n : ℕ) (ζ : ℂ) : CMatrix n n :=
  fun i j ↦ (n : ℂ)⁻¹ *
    complexMatrixAdjoint (complexFourierVandermondeMatrix n ζ) i j

/-- The explicit Fourier inverse is a left inverse. -/
theorem higham22_rootUnityInverse_mul_vandermonde
    {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    complexCMatrixAsMatrix (higham22RootUnityInverse n ζ) *
        higham22Vandermonde (higham22RootUnityNodes n ζ) = 1 := by
  rw [higham22_rootUnityVandermonde_eq_fourier]
  have hH := complexFourierVandermonde_isComplexHadamard_of_isPrimitiveRoot hn hζ
  have hgram := hH.conjTranspose_mul_self
  change (((n : ℂ)⁻¹) •
      (complexCMatrixAsMatrix (complexFourierVandermondeMatrix n ζ)).conjTranspose) *
        complexCMatrixAsMatrix (complexFourierVandermondeMatrix n ζ) = 1
  rw [Matrix.smul_mul, hgram, smul_smul]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  simp [hnC]

/-- Table 22.1 (V7): the Euclidean condition product of the roots-of-unity
Vandermonde and its explicit inverse is exactly one. -/
theorem higham22_table22_1_V7_kappa2
    {n : ℕ} (hn : 0 < n) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) :
    complexMatrixOp2 (higham22Vandermonde (higham22RootUnityNodes n ζ)) *
      complexMatrixOp2 (higham22RootUnityInverse n ζ) = 1 := by
  have hH := complexFourierVandermonde_isComplexHadamard_of_isPrimitiveRoot hn hζ
  rw [higham22_rootUnityVandermonde_eq_fourier,
    hH.complexMatrixOp2_eq_sqrt hn]
  have hinv : higham22RootUnityInverse n ζ =
      (((n : ℂ)⁻¹) •
        (complexMatrixAdjoint (complexFourierVandermondeMatrix n ζ) :
          Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := by
    rfl
  rw [hinv]
  rw [complexMatrixOp2_smul, complexMatrixOp2_adjoint_eq,
    hH.complexMatrixOp2_eq_sqrt hn]
  have hnorm : ‖((n : ℂ)⁻¹)‖ = ((n : ℝ)⁻¹) := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hnorm]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hsqrt : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  field_simp [hnR]
  nlinarith

/-- Each row computed by Algorithm 22.1 is the corresponding cardinal
polynomial at every node. -/
theorem higham22_algorithm1Printed_cardinal
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) (i j : Fin n) :
    ∑ k : Fin n,
        higham22Algorithm1Printed alpha i k * alpha j ^ (k : ℕ) =
      if j = i then 1 else 0 := by
  let q := higham22Algorithm1SyntheticQuotient alpha i
  let d := higham22Algorithm1Denominator alpha i
  have heval : q.eval (alpha j) = ∑ k : Fin n, q.coeff (k : ℕ) * alpha j ^ (k : ℕ) := by
    rw [Polynomial.eval_eq_sum_range'
      (higham22_algorithm1SyntheticQuotient_natDegree_lt alpha i),
      ← Fin.sum_univ_eq_sum_range]
  have hd : d ≠ 0 := higham22_algorithm1Denominator_ne_zero halpha i
  rw [show (∑ k : Fin n,
        higham22Algorithm1Printed alpha i k * alpha j ^ (k : ℕ)) = q.eval (alpha j) / d by
      rw [heval]
      simp_rw [higham22Algorithm1Printed, q, d, div_mul_eq_mul_div]
      simp [div_eq_mul_inv, Finset.sum_mul]]
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    change d / d = 1
    exact div_self hd
  · rw [if_neg hji, higham22_algorithm1SyntheticQuotient_eval_other alpha i j hji,
      zero_div]

/-- End-to-end exact correctness of the printed Algorithm 22.1 path. -/
theorem higham22_algorithm1Printed_leftInverse
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Algorithm1Printed alpha * higham22Vandermonde alpha = 1 := by
  ext i j
  simpa [Matrix.mul_apply, higham22Vandermonde, eq_comm] using
    higham22_algorithm1Printed_cardinal halpha i j

/-- Exact mathematical output specification of Algorithm 22.1.  The chapter's
two-stage floating-point implementation is deliberately not identified with
this noncomputable inverse. -/
noncomputable def higham22Algorithm1OutputSpec
    (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (higham22Vandermonde alpha)⁻¹

/-- The exact output specification associated with Algorithm 22.1 is a right
inverse for distinct nodes.  This does not model the printed execution path. -/
theorem higham22_algorithm1OutputSpec_rightInverse
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Vandermonde alpha * higham22Algorithm1OutputSpec alpha = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [isUnit_iff_ne_zero]
  exact higham22_vandermonde_det_ne_zero_iff.mpr halpha

/-- The exact output specification associated with Algorithm 22.1 is also a
left inverse for distinct nodes.  This does not model the printed execution path. -/
theorem higham22_algorithm1OutputSpec_leftInverse
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Algorithm1OutputSpec alpha * higham22Vandermonde alpha = 1 := by
  apply Matrix.nonsing_inv_mul
  rw [isUnit_iff_ne_zero]
  exact higham22_vandermonde_det_ne_zero_iff.mpr halpha

/-- The printed Algorithm 22.1 path agrees with the inverse output
specification for distinct nodes. -/
theorem higham22_algorithm1Printed_eq_outputSpec
    {alpha : Fin n → ℂ} (halpha : Function.Injective alpha) :
    higham22Algorithm1Printed alpha = higham22Algorithm1OutputSpec alpha := by
  calc
    higham22Algorithm1Printed alpha =
        higham22Algorithm1Printed alpha * 1 := by simp
    _ = higham22Algorithm1Printed alpha *
        (higham22Vandermonde alpha * higham22Algorithm1OutputSpec alpha) := by
          rw [higham22_algorithm1OutputSpec_rightInverse halpha]
    _ = (higham22Algorithm1Printed alpha * higham22Vandermonde alpha) *
        higham22Algorithm1OutputSpec alpha := by rw [Matrix.mul_assoc]
    _ = higham22Algorithm1OutputSpec alpha := by
      rw [higham22_algorithm1Printed_leftInverse halpha, one_mul]

/-- Higham, 2nd ed., equation (22.4), p. 418: the symbolic `5 × 5`
confluent Vandermonde matrix with multiplicities three at `alpha₀` and two at
`alpha₁`.  Successive confluent columns are derivatives of the preceding
monomial column. -/
def higham22ConfluentExample (alpha₀ alpha₁ : ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  ![![1, 0, 0, 1, 0],
    ![alpha₀, 1, 0, alpha₁, 1],
    ![alpha₀ ^ 2, 2 * alpha₀, 2, alpha₁ ^ 2, 2 * alpha₁],
    ![alpha₀ ^ 3, 3 * alpha₀ ^ 2, 6 * alpha₀,
      alpha₁ ^ 3, 3 * alpha₁ ^ 2],
    ![alpha₀ ^ 4, 4 * alpha₀ ^ 3, 12 * alpha₀ ^ 2,
      alpha₁ ^ 4, 4 * alpha₁ ^ 3]]

/-- Determinant of the symbolic confluent example (22.4). -/
theorem higham22_confluentExample_det (alpha₀ alpha₁ : ℂ) :
    (higham22ConfluentExample alpha₀ alpha₁).det =
      2 * (alpha₁ - alpha₀) ^ 6 := by
  simp [higham22ConfluentExample, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Fin.succAbove]
  ring

/-- The transpose in the prose after (22.4) is nonsingular exactly when its
two nonconfluent nodes are distinct. -/
theorem higham22_confluentExample_transpose_det_ne_zero_iff
    (alpha₀ alpha₁ : ℂ) :
    (higham22ConfluentExample alpha₀ alpha₁).transpose.det ≠ 0 ↔
      alpha₀ ≠ alpha₁ := by
  rw [Matrix.det_transpose, higham22_confluentExample_det]
  constructor
  · intro h hEq
    apply h
    simp [hEq]
  · intro h
    exact mul_ne_zero (by norm_num) (pow_ne_zero 6 (sub_ne_zero.mpr h.symm))

/-- General Hermite uniqueness behind the precise prose following (22.4).
If all derivatives below the assigned multiplicity vanish at distinct nodes,
a polynomial of degree below the total multiplicity is zero. -/
theorem higham22_confluent_polynomial_unique
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (halpha : Function.Injective alpha) (p : Polynomial ℂ)
    (hdegree : p.natDegree < ∑ i, multiplicity i)
    (hvanish : ∀ (i : ι) (r : ℕ), r < multiplicity i →
      (Polynomial.derivative^[r] p).eval (alpha i) = 0) :
    p = 0 := by
  by_contra hp
  have hmultiplicity : ∀ i,
      multiplicity i ≤ p.rootMultiplicity (alpha i) := by
    intro i
    cases hmi : multiplicity i with
    | zero => simp
    | succ m =>
        exact Nat.succ_le_iff.mpr
          (Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative
            (n := m) hp (fun r hr ↦ hvanish i r (by
              rw [hmi]
              exact Nat.lt_succ_of_le hr)))
  have hprod :
      (∏ i, (Polynomial.X - Polynomial.C (alpha i)) ^ multiplicity i) ∣ p := by
    apply Fintype.prod_dvd_of_coprime
    · intro i j hij
      exact (Polynomial.pairwise_coprime_X_sub_C halpha hij).pow
    · intro i
      exact (pow_dvd_pow _ (hmultiplicity i)).trans
        (p.pow_rootMultiplicity_dvd (alpha i))
  have hprodDegree :
      (∏ i, (Polynomial.X - Polynomial.C (alpha i)) ^ multiplicity i).natDegree =
        ∑ i, multiplicity i := by
    rw [Polynomial.natDegree_prod_of_monic]
    · simp
    · intro i _hi
      exact (Polynomial.monic_X_sub_C (alpha i)).pow (multiplicity i)
  have hle := Polynomial.natDegree_le_of_dvd hprod hp
  rw [hprodDegree] at hle
  exact (not_lt_of_ge hle) hdegree

/-- A confluent column records a node and a derivative order below that node's
multiplicity. -/
abbrev Higham22ConfluentSlot {ι : Type*} (multiplicity : ι → ℕ) :=
  Σ i, Fin (multiplicity i)

/-- Canonical finite enumeration of all confluent columns. -/
noncomputable def higham22ConfluentSlotEquivFin
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) :
    Higham22ConfluentSlot multiplicity ≃
      Fin (Fintype.card (Higham22ConfluentSlot multiplicity)) :=
  Fintype.equivFin _

/-- Polynomial of degree below `N` whose coefficient vector is `x`. -/
noncomputable def higham22CoefficientPolynomial {N : ℕ}
    (x : Fin N → ℂ) : Polynomial ℂ :=
  ((Polynomial.degreeLTEquiv ℂ N).symm x : Polynomial.degreeLT ℂ N).1

/-- Derivative evaluation of the coefficient polynomial is the corresponding
finite linear combination of differentiated monomials. -/
theorem higham22CoefficientPolynomial_iterateDerivative_eval {N : ℕ}
    (x : Fin N → ℂ) (r : ℕ) (a : ℂ) :
    (Polynomial.derivative^[r] (higham22CoefficientPolynomial x)).eval a =
      ∑ k : Fin N, x k *
        (Polynomial.derivative^[r] (Polynomial.X ^ (k : ℕ))).eval a := by
  unfold higham22CoefficientPolynomial Polynomial.degreeLTEquiv
  change (Polynomial.derivative^[r]
    (∑ k : Fin N, Polynomial.monomial (k : ℕ) (x k))).eval a = _
  rw [Polynomial.iterate_derivative_sum]
  simp_rw [← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_C]

/-- General confluent Vandermonde matrix from the prose following (22.4).
Rows are monomial degrees and columns are enumerated node/derivative slots. -/
noncomputable def higham22ConfluentVandermonde
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) (alpha : ι → ℂ) :
    Matrix
      (Fin (Fintype.card (Higham22ConfluentSlot multiplicity)))
      (Fin (Fintype.card (Higham22ConfluentSlot multiplicity))) ℂ :=
  fun degree column ↦
    let slot := (higham22ConfluentSlotEquivFin multiplicity).symm column
    (Polynomial.derivative^[slot.2.val]
      (Polynomial.X ^ degree.val)).eval (alpha slot.1)

/-- A coordinate of the transposed confluent matrix-vector product is exactly
the requested derivative evaluation of the coefficient polynomial. -/
theorem higham22_confluentVandermonde_transpose_mulVec_apply
    {ι : Type*} [Fintype ι] (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (x : Fin (Fintype.card (Higham22ConfluentSlot multiplicity)) → ℂ)
    (slot : Higham22ConfluentSlot multiplicity) :
    (higham22ConfluentVandermonde multiplicity alpha).transpose.mulVec x
        (higham22ConfluentSlotEquivFin multiplicity slot) =
      (Polynomial.derivative^[slot.2.val]
        (higham22CoefficientPolynomial x)).eval (alpha slot.1) := by
  rw [higham22CoefficientPolynomial_iterateDerivative_eval]
  simp only [higham22ConfluentVandermonde, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct]
  rw [Equiv.symm_apply_apply]
  simp [mul_comm]

/-- General nonsingularity claim following (22.4): distinct nonconfluent nodes
make the transpose of the confluent Vandermonde matrix injective. -/
theorem higham22_confluentVandermonde_transpose_mulVec_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (halpha : Function.Injective alpha) :
    Function.Injective
      (higham22ConfluentVandermonde multiplicity alpha).transpose.mulVec := by
  intro x y hxy
  let z := x - y
  have hz :
      (higham22ConfluentVandermonde multiplicity alpha).transpose.mulVec z = 0 := by
    simp [z, Matrix.mulVec_sub, hxy]
  let p := higham22CoefficientPolynomial z
  have hpzero : p = 0 := by
    by_cases hp : p = 0
    · exact hp
    apply higham22_confluent_polynomial_unique multiplicity alpha halpha p
    · have hpDegree : p.natDegree <
          Fintype.card (Higham22ConfluentSlot multiplicity) := by
        apply (Polynomial.natDegree_lt_iff_degree_lt hp).mpr
        exact Polynomial.mem_degreeLT.mp
          (((Polynomial.degreeLTEquiv ℂ
            (Fintype.card (Higham22ConfluentSlot multiplicity))).symm z).property)
      simpa [Higham22ConfluentSlot] using hpDegree
    · intro i r hr
      let slot : Higham22ConfluentSlot multiplicity := ⟨i, ⟨r, hr⟩⟩
      have hcoord := congrFun hz (higham22ConfluentSlotEquivFin multiplicity slot)
      simpa [p, slot] using
        (higham22_confluentVandermonde_transpose_mulVec_apply
          multiplicity alpha z slot).symm.trans hcoord
  have hzzero : z = 0 := by
    have hsubtype :
        (Polynomial.degreeLTEquiv ℂ
          (Fintype.card (Higham22ConfluentSlot multiplicity))).symm z = 0 := by
      apply Subtype.ext
      exact hpzero
    have himage := congrArg
      (Polynomial.degreeLTEquiv ℂ
        (Fintype.card (Higham22ConfluentSlot multiplicity))) hsubtype
    simpa using himage
  exact sub_eq_zero.mp hzzero

/-- Determinantal form of the general nonsingularity prose following (22.4). -/
theorem higham22_confluentVandermonde_transpose_det_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (multiplicity : ι → ℕ) (alpha : ι → ℂ)
    (halpha : Function.Injective alpha) :
    (higham22ConfluentVandermonde multiplicity alpha).transpose.det ≠ 0 := by
  have hunit : IsUnit
      (higham22ConfluentVandermonde multiplicity alpha).transpose :=
    Matrix.mulVec_injective_iff_isUnit.mp
      (higham22_confluentVandermonde_transpose_mulVec_injective
        multiplicity alpha halpha)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

end Vandermonde

section VandermondeLike

/-- Higham, 2nd ed., equation (22.5): repeated nodes occur in contiguous
blocks.  This is an explicit source assumption on the input ordering. -/
def Higham22ContiguousNodes {N : ℕ} (alpha : Fin N → ℂ) : Prop :=
  ∀ i j : Fin N, i < j → alpha i = alpha j →
    ∀ k : Fin N, i ≤ k → k ≤ j → alpha k = alpha i

/-- Direct source-facing form of equation (22.5). -/
theorem higham22_eq22_5 {N : ℕ} {alpha : Fin N → ℂ}
    (h : Higham22ContiguousNodes alpha)
    {i j k : Fin N} (hij : i < j) (hα : alpha i = alpha j)
    (hik : i ≤ k) (hkj : k ≤ j) :
    alpha k = alpha i :=
  h i j hij hα k hik hkj

/-- Higham's equation (22.8), the Newton divided-difference form. -/
noncomputable def higham22NewtonPolynomial {N : ℕ}
    (alpha c : Fin N → ℂ) : Polynomial ℂ :=
  ∑ i : Fin N, Polynomial.C (c i) *
    ∏ j ∈ Finset.Iio i, (Polynomial.X - Polynomial.C (alpha j))

/-- Equation (22.8) evaluated at an arbitrary point. -/
theorem higham22_eq22_8 {N : ℕ} (alpha c : Fin N → ℂ) (x : ℂ) :
    (higham22NewtonPolynomial alpha c).eval x =
      ∑ i : Fin N, c i * ∏ j ∈ Finset.Iio i, (x - alpha j) := by
  simp [higham22NewtonPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_prod]

/-- One scalar branch of the confluent divided-difference recurrence (22.9).
The derivative datum is already the derivative of the required order. -/
noncomputable def higham22DividedDifferenceStep
    (left right alphaLeft alphaRight derivativeDatum : ℂ) (order : ℕ) : ℂ :=
  if alphaRight = alphaLeft then
    derivativeDatum / (Nat.factorial order : ℂ)
  else
    (right - left) / (alphaRight - alphaLeft)

/-- Distinct-node branch of equation (22.9). -/
theorem higham22_eq22_9_distinct
    {left right alphaLeft alphaRight derivativeDatum : ℂ} {order : ℕ}
    (h : alphaRight ≠ alphaLeft) :
    higham22DividedDifferenceStep left right alphaLeft alphaRight
        derivativeDatum order =
      (right - left) / (alphaRight - alphaLeft) := by
  simp [higham22DividedDifferenceStep, h]

/-- Confluent derivative branch of equation (22.9). -/
theorem higham22_eq22_9_equal
    (left right alpha derivativeDatum : ℂ) (order : ℕ) :
    higham22DividedDifferenceStep left right alpha alpha derivativeDatum order =
      derivativeDatum / (Nat.factorial order : ℂ) := by
  simp [higham22DividedDifferenceStep]

/-- Polynomial version of the nested multiplication in (22.10)--(22.11).
The list is in source order `(alpha_k,c_k),...,(alpha_n,c_n)`. -/
noncomputable def higham22NewtonPolynomialNest : List (ℂ × ℂ) → Polynomial ℂ
  | [] => 0
  | (alpha, c) :: rest =>
      Polynomial.C c +
        (Polynomial.X - Polynomial.C alpha) * higham22NewtonPolynomialNest rest

/-- Equation (22.10): the terminal nested polynomial is constant. -/
@[simp]
theorem higham22_eq22_10_polynomial (alpha c : ℂ) :
    higham22NewtonPolynomialNest [(alpha, c)] = Polynomial.C c := by
  simp [higham22NewtonPolynomialNest]

/-- Equation (22.11), as an equality of polynomials. -/
@[simp]
theorem higham22_eq22_11_polynomial (alpha c : ℂ) (rest : List (ℂ × ℂ)) :
    higham22NewtonPolynomialNest ((alpha, c) :: rest) =
      (Polynomial.X - Polynomial.C alpha) *
          higham22NewtonPolynomialNest rest + Polynomial.C c := by
  simp [higham22NewtonPolynomialNest, add_comm]

/-- Source-facing basis expansion used in equation (22.12). -/
noncomputable def higham22BasisExpansion {N : ℕ}
    (p : Fin N → Polynomial ℂ) (a : Fin N → ℂ) : Polynomial ℂ :=
  ∑ j : Fin N, Polynomial.C (a j) * p j

/-- Equation (22.12) evaluated at a point. -/
theorem higham22_eq22_12_eval {N : ℕ}
    (p : Fin N → Polynomial ℂ) (a : Fin N → ℂ) (x : ℂ) :
    (higham22BasisExpansion p a).eval x =
      ∑ j : Fin N, a j * (p j).eval x := by
  simp [higham22BasisExpansion, Polynomial.eval_finset_sum]

/-- Equation (22.6): a polynomial family satisfying Higham's three-term
recurrence.  Natural-number indices keep the mathematical recurrence separate
from a later finite implementation. -/
def Higham22ThreeTermRecurrence
    (theta beta gamma : ℕ → ℂ) (p : ℕ → Polynomial ℂ) : Prop :=
  p 0 = 1 ∧
    p 1 = Polynomial.C (theta 0) * (Polynomial.X - Polynomial.C (beta 0)) ∧
    ∀ j : ℕ,
      p (j + 2) =
        Polynomial.C (theta (j + 1)) *
            (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1) -
          Polynomial.C (gamma (j + 1)) * p j

/-- The polynomial family generated by a row of Higham's Table 22.2.  This is
the recurrence (22.6) as an executable exact-arithmetic definition. -/
noncomputable def higham22PolynomialSequence
    (theta beta gamma : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.C (theta 0) *
      (Polynomial.X - Polynomial.C (beta 0))
  | j + 2 =>
      Polynomial.C (theta (j + 1)) *
          (Polynomial.X - Polynomial.C (beta (j + 1))) *
        higham22PolynomialSequence theta beta gamma (j + 1) -
      Polynomial.C (gamma (j + 1)) *
        higham22PolynomialSequence theta beta gamma j

/-- Every generated family satisfies the exact three-term recurrence (22.6). -/
theorem higham22PolynomialSequence_recurrence
    (theta beta gamma : ℕ → ℂ) :
    Higham22ThreeTermRecurrence theta beta gamma
      (higham22PolynomialSequence theta beta gamma) := by
  refine ⟨rfl, rfl, ?_⟩
  intro j
  rfl

/-- Table 22.2, monomial row. -/
def higham22MonomialTheta (_j : ℕ) : ℂ := 1
def higham22MonomialBeta (_j : ℕ) : ℂ := 0
def higham22MonomialGamma (_j : ℕ) : ℂ := 0

/-- Table 22.2, Chebyshev row, including the exceptional `theta₀ = 1`. -/
def higham22ChebyshevTheta : ℕ → ℂ
  | 0 => 1
  | _j + 1 => 2
def higham22ChebyshevBeta (_j : ℕ) : ℂ := 0
def higham22ChebyshevGamma : ℕ → ℂ
  | 0 => 0
  | _j + 1 => 1

/-- Table 22.2, Legendre row. -/
noncomputable def higham22LegendreTheta (j : ℕ) : ℂ :=
  ((2 : ℂ) * j + 1) / (j + 1)
def higham22LegendreBeta (_j : ℕ) : ℂ := 0
noncomputable def higham22LegendreGamma (j : ℕ) : ℂ :=
  (j : ℂ) / (j + 1)

/-- Table 22.2, physicists' Hermite row. -/
def higham22HermiteTheta (_j : ℕ) : ℂ := 2
def higham22HermiteBeta (_j : ℕ) : ℂ := 0
def higham22HermiteGamma (j : ℕ) : ℂ := 2 * j

/-- Table 22.2, Laguerre row. -/
noncomputable def higham22LaguerreTheta (j : ℕ) : ℂ :=
  -1 / (j + 1)
def higham22LaguerreBeta (j : ℕ) : ℂ :=
  2 * j + 1
noncomputable def higham22LaguerreGamma (j : ℕ) : ℂ :=
  (j : ℂ) / (j + 1)

/-- The monomial parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_monomial :
    Higham22ThreeTermRecurrence
      higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
      (higham22PolynomialSequence
        higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Chebyshev parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_chebyshev :
    Higham22ThreeTermRecurrence
      higham22ChebyshevTheta higham22ChebyshevBeta higham22ChebyshevGamma
      (higham22PolynomialSequence
        higham22ChebyshevTheta higham22ChebyshevBeta higham22ChebyshevGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Legendre parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_legendre :
    Higham22ThreeTermRecurrence
      higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma
      (higham22PolynomialSequence
        higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Hermite parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_hermite :
    Higham22ThreeTermRecurrence
      higham22HermiteTheta higham22HermiteBeta higham22HermiteGamma
      (higham22PolynomialSequence
        higham22HermiteTheta higham22HermiteBeta higham22HermiteGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- The Laguerre parameters in Table 22.2 satisfy (22.6). -/
theorem higham22_table22_2_laguerre :
    Higham22ThreeTermRecurrence
      higham22LaguerreTheta higham22LaguerreBeta higham22LaguerreGamma
      (higham22PolynomialSequence
        higham22LaguerreTheta higham22LaguerreBeta higham22LaguerreGamma) :=
  higham22PolynomialSequence_recurrence _ _ _

/-- A recurrence whose parameters preserve the value one has `p_j(1)=1` for
all `j`.  This is the normalization note attached to the Legendre row of
Table 22.2. -/
theorem higham22PolynomialSequence_eval_one_of_preserved
    (theta beta gamma : ℕ → ℂ)
    (hzero : theta 0 * (1 - beta 0) = 1)
    (hstep : ∀ j : ℕ,
      theta (j + 1) * (1 - beta (j + 1)) - gamma (j + 1) = 1) :
    ∀ j : ℕ,
      (higham22PolynomialSequence theta beta gamma j).eval 1 = 1 := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero => simp [higham22PolynomialSequence]
  | one => simpa [higham22PolynomialSequence] using hzero
  | more j hj hj1 =>
      simp only [higham22PolynomialSequence, Polynomial.eval_sub,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [hj1, hj]
      simpa using hstep j

/-- Legendre normalization from Table 22.2: `p_j(1)=1`. -/
theorem higham22_table22_2_legendre_eval_one (j : ℕ) :
    (higham22PolynomialSequence
      higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma j).eval 1 = 1 := by
  apply higham22PolynomialSequence_eval_one_of_preserved
  · simp [higham22LegendreTheta, higham22LegendreBeta]
  · intro k
    have hk2 : (2 + (k : ℂ)) ≠ 0 := by
      rw [show (2 : ℂ) + (k : ℂ) = ((k + 2 : ℕ) : ℂ) by
        norm_num
        ring]
      exact_mod_cast Nat.succ_ne_zero (k + 1)
    norm_num [higham22LegendreTheta, higham22LegendreBeta,
      higham22LegendreGamma] at *
    have hden : (k : ℂ) + 1 + 1 ≠ 0 := by
      intro h
      apply hk2
      calc
        (2 : ℂ) + k = k + 1 + 1 := by ring
        _ = 0 := h
    field_simp [hden]
    ring

/-- The nonzero-`theta` side condition following (22.6) holds for every row
of Table 22.2. -/
theorem higham22_table22_2_theta_ne_zero :
    (∀ j, higham22MonomialTheta j ≠ 0) ∧
    (∀ j, higham22ChebyshevTheta j ≠ 0) ∧
    (∀ j, higham22LegendreTheta j ≠ 0) ∧
    (∀ j, higham22HermiteTheta j ≠ 0) ∧
    (∀ j, higham22LaguerreTheta j ≠ 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    norm_num [higham22MonomialTheta]
  · intro j
    cases j <;> norm_num [higham22ChebyshevTheta]
  · intro j
    unfold higham22LegendreTheta
    apply div_ne_zero
    · exact_mod_cast Nat.succ_ne_zero (2 * j)
    · exact_mod_cast Nat.succ_ne_zero j
  · intro j
    norm_num [higham22HermiteTheta]
  · intro j
    unfold higham22LaguerreTheta
    apply div_ne_zero
    · norm_num
    · exact_mod_cast Nat.succ_ne_zero j

/-- Polynomial state underlying the reverse Clenshaw loop.  The two returned
polynomials are the consecutive states `b_j,b_{j+1}`. -/
noncomputable def higham22ClenshawPolynomialAux
    (theta beta gamma : ℕ → ℂ) : ℕ → List ℂ → Polynomial ℂ × Polynomial ℂ
  | _j, [] => (0, 0)
  | j, a :: as =>
      let next := higham22ClenshawPolynomialAux theta beta gamma (j + 1) as
      (Polynomial.C a +
          Polynomial.C (theta j) * (Polynomial.X - Polynomial.C (beta j)) * next.1 -
          Polynomial.C (gamma (j + 1)) * next.2,
        next.1)

/-- Exact polynomial computed by the scalar part of Algorithm 22.8. -/
noncomputable def higham22ClenshawPolynomial
    (theta beta gamma : ℕ → ℂ) (a : List ℂ) : Polynomial ℂ :=
  (higham22ClenshawPolynomialAux theta beta gamma 0 a).1

/-- The normalized derivative state of the printed extended Clenshaw loop.
Index `i` stores the `i`th derivative divided by `i!`; the final scaling in
Algorithm 22.8 restores ordinary derivatives. -/
noncomputable def higham22ClenshawJetAux
    (theta beta gamma : ℕ → ℂ) (x : ℂ) :
    ℕ → List ℂ → (ℕ → ℂ) × (ℕ → ℂ)
  | _j, [] => (0, 0)
  | j, a :: as =>
      let next := higham22ClenshawJetAux theta beta gamma x (j + 1) as
      (fun i ↦
        theta j * ((x - beta j) * next.1 i +
          if i = 0 then 0 else next.1 (i - 1)) -
        gamma (j + 1) * next.2 i + if i = 0 then a else 0,
       next.1)

/-- The actual outputs of Algorithm 22.8 after its final factorial scaling. -/
noncomputable def higham22Algorithm22_8
    (theta beta gamma : ℕ → ℂ) (a : List ℂ) (x : ℂ) (i : ℕ) : ℂ :=
  (Nat.factorial i : ℂ) *
    (higham22ClenshawJetAux theta beta gamma x 0 a).1 i

/-- Multiplication by a linear factor shifts Taylor coefficients exactly as
used by the inner derivative loop of Algorithm 22.8. -/
theorem higham22_taylor_linear_mul_coeff
    (x beta : ℂ) (q : Polynomial ℂ) (i : ℕ) :
    (Polynomial.taylor x ((Polynomial.X - Polynomial.C beta) * q)).coeff i =
      (x - beta) * (Polynomial.taylor x q).coeff i +
        if i = 0 then 0 else (Polynomial.taylor x q).coeff (i - 1) := by
  rcases i with _ | i
  · simp [Polynomial.taylor_mul]
  · rw [Polynomial.taylor_mul]
    rw [show Polynomial.taylor x (Polynomial.X - Polynomial.C beta) =
        Polynomial.X + Polynomial.C (x - beta) by
      simp only [map_sub, Polynomial.taylor_X, Polynomial.taylor_C]
      ring]
    rw [add_mul]
    simp [Polynomial.coeff_add, Polynomial.coeff_X_mul]
    rw [sub_mul, Polynomial.coeff_sub,
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    ring

/-- The numerical jet loop is the Taylor-coefficient loop of the polynomial
Clenshaw state. -/
theorem higham22_clenshawJetAux_eq_taylor_coeff
    (theta beta gamma : ℕ → ℂ) (x : ℂ) (j : ℕ) (a : List ℂ) (i : ℕ) :
    (higham22ClenshawJetAux theta beta gamma x j a).1 i =
        (Polynomial.taylor x
          (higham22ClenshawPolynomialAux theta beta gamma j a).1).coeff i ∧
      (higham22ClenshawJetAux theta beta gamma x j a).2 i =
        (Polynomial.taylor x
          (higham22ClenshawPolynomialAux theta beta gamma j a).2).coeff i := by
  induction a generalizing j i with
  | nil => simp [higham22ClenshawJetAux, higham22ClenshawPolynomialAux]
  | cons a as ih =>
      have hnext := ih (j + 1) i
      constructor
      · simp only [higham22ClenshawJetAux, higham22ClenshawPolynomialAux]
        rw [map_sub, map_add]
        simp only [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.taylor_C]
        rw [show Polynomial.taylor x
              (Polynomial.C (theta j) * (Polynomial.X - Polynomial.C (beta j)) *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1) =
              Polynomial.C (theta j) * Polynomial.taylor x
                ((Polynomial.X - Polynomial.C (beta j)) *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1) by
              simp [Polynomial.taylor_mul]
              ring_nf]
        rw [show Polynomial.taylor x
              (Polynomial.C (gamma (j + 1)) *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2) =
              Polynomial.C (gamma (j + 1)) * Polynomial.taylor x
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2 by
              simp [Polynomial.taylor_mul]]
        simp only [Polynomial.coeff_C_mul]
        rw [higham22_taylor_linear_mul_coeff]
        by_cases hi : i = 0
        · subst i
          rw [← hnext.1, ← hnext.2]
          simp
          ring
        · have hprev := ih (j + 1) (i - 1)
          rw [← hnext.1, ← hnext.2, ← hprev.1]
          simp [Polynomial.coeff_C, hi]
      · simpa [higham22ClenshawJetAux, higham22ClenshawPolynomialAux] using hnext.1

/-- A list-indexed polynomial expansion in the recurrence basis. -/
noncomputable def higham22IndexedBasisSum
    (p : ℕ → Polynomial ℂ) : ℕ → List ℂ → Polynomial ℂ
  | _j, [] => 0
  | j, a :: as => Polynomial.C a * p j + higham22IndexedBasisSum p (j + 1) as

/-- General Clenshaw invariant for a tail beginning at a positive index. -/
theorem higham22_clenshawPolynomialAux_invariant
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (j : ℕ) (hj : 1 ≤ j) (a : List ℂ) :
    p j * (higham22ClenshawPolynomialAux theta beta gamma j a).1 -
        Polynomial.C (gamma j) * p (j - 1) *
          (higham22ClenshawPolynomialAux theta beta gamma j a).2 =
      higham22IndexedBasisSum p j a := by
  induction a generalizing j with
  | nil => simp [higham22ClenshawPolynomialAux, higham22IndexedBasisSum]
  | cons a as ih =>
      have hrec : p (j + 1) =
          Polynomial.C (theta j) *
              (Polynomial.X - Polynomial.C (beta j)) * p j -
            Polynomial.C (gamma j) * p (j - 1) := by
        cases j with
        | zero => omega
        | succ j =>
            simpa [Nat.succ_eq_add_one, Nat.add_assoc] using hp.2.2 j
      have htail := ih (j + 1) (by omega)
      have htail' :
          p (j + 1) *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
              Polynomial.C (gamma (j + 1)) * p j *
                (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2 =
            higham22IndexedBasisSum p (j + 1) as := by
        simpa using htail
      simp only [higham22ClenshawPolynomialAux, higham22IndexedBasisSum]
      calc
        p j *
              (Polynomial.C a +
                Polynomial.C (theta j) *
                    (Polynomial.X - Polynomial.C (beta j)) *
                      (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
                Polynomial.C (gamma (j + 1)) *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2) -
            Polynomial.C (gamma j) * p (j - 1) *
              (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 =
          Polynomial.C a * p j +
            (Polynomial.C (theta j) *
                  (Polynomial.X - Polynomial.C (beta j)) * p j -
                Polynomial.C (gamma j) * p (j - 1)) *
              (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
            Polynomial.C (gamma (j + 1)) * p j *
              (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2 := by
            ring
        _ = Polynomial.C a * p j +
              (p (j + 1) *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).1 -
                Polynomial.C (gamma (j + 1)) * p j *
                  (higham22ClenshawPolynomialAux theta beta gamma (j + 1) as).2) := by
            rw [hrec]
            ring
        _ = Polynomial.C a * p j + higham22IndexedBasisSum p (j + 1) as := by
            rw [htail']

/-- The scalar reverse loop computes the represented basis polynomial. -/
theorem higham22_clenshawPolynomial_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p) (a : List ℂ) :
    higham22ClenshawPolynomial theta beta gamma a =
      higham22IndexedBasisSum p 0 a := by
  cases a with
  | nil => simp [higham22ClenshawPolynomial, higham22ClenshawPolynomialAux,
      higham22IndexedBasisSum]
  | cons a as =>
      have htail := higham22_clenshawPolynomialAux_invariant hp 1 (by omega) as
      have htail' :
          (Polynomial.C (theta 0) *
                (Polynomial.X - Polynomial.C (beta 0))) *
              (higham22ClenshawPolynomialAux theta beta gamma 1 as).1 -
            Polynomial.C (gamma 1) *
              (higham22ClenshawPolynomialAux theta beta gamma 1 as).2 =
          higham22IndexedBasisSum p 1 as := by
        simpa [hp.1, hp.2.1] using htail
      simp only [higham22ClenshawPolynomial, higham22ClenshawPolynomialAux,
        higham22IndexedBasisSum]
      rw [hp.1]
      rw [← htail']
      ring

/-- End-to-end exact correctness of the printed extended Clenshaw recurrence:
its `i`th output is the ordinary `i`th derivative of the represented
polynomial at `x`. -/
theorem higham22_algorithm22_8_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (a : List ℂ) (x : ℂ) (i : ℕ) :
    higham22Algorithm22_8 theta beta gamma a x i =
      ((Polynomial.derivative^[i]) (higham22IndexedBasisSum p 0 a)).eval x := by
  unfold higham22Algorithm22_8
  rw [(higham22_clenshawJetAux_eq_taylor_coeff theta beta gamma x 0 a i).1]
  rw [Polynomial.taylor_coeff]
  change (Nat.factorial i : ℂ) *
      (Polynomial.hasseDeriv i
        (higham22ClenshawPolynomial theta beta gamma a)).eval x = _
  rw [higham22_clenshawPolynomial_correct hp]
  have hfun := Polynomial.factorial_smul_hasseDeriv (R := ℂ) (k := i)
  have hpoly := congrFun hfun (higham22IndexedBasisSum p 0 a)
  have heval := congrArg (Polynomial.eval x) hpoly
  simpa [nsmul_eq_mul] using heval

/-- Synthesis of a finitely supported coefficient vector in the polynomial
basis `p`. -/
noncomputable def higham22BasisSynthesis (p : ℕ → Polynomial ℂ) :
    (ℕ →₀ ℂ) →ₗ[ℂ] Polynomial ℂ :=
  (Finsupp.lsum ℂ) fun j ↦
    LinearMap.toSpanSingleton ℂ (Polynomial ℂ) (p j)

/-- Sparse coefficient row for multiplication by `x-alpha`, obtained by
solving the three-term recurrence for `x p_j`. -/
noncomputable def higham22BasisMultiplyRow
    (theta beta gamma : ℕ → ℂ) (alpha : ℂ) (j : ℕ) : ℕ →₀ ℂ :=
  Finsupp.single (j + 1) (theta j)⁻¹ +
    Finsupp.single j (beta j - alpha) +
      if j = 0 then 0 else Finsupp.single (j - 1) (gamma j / theta j)

/-- Linear sparse update used in equations (22.13)--(22.14). -/
noncomputable def higham22BasisMultiply
    (theta beta gamma : ℕ → ℂ) (alpha : ℂ) :
    (ℕ →₀ ℂ) →ₗ[ℂ] (ℕ →₀ ℂ) :=
  (Finsupp.lsum ℂ) fun j ↦
    LinearMap.toSpanSingleton ℂ (ℕ →₀ ℂ)
      (higham22BasisMultiplyRow theta beta gamma alpha j)

/-- Coordinate formula for multiplication by `x - alpha` in the recurrence
basis.  This is the coefficient-level form of (22.13)--(22.14). -/
theorem higham22_basisMultiply_apply (theta beta gamma : ℕ → ℂ) (alpha : ℂ)
    (b : ℕ →₀ ℂ) (r : ℕ) :
    higham22BasisMultiply theta beta gamma alpha b r =
      (if r = 0 then 0 else b (r - 1) / theta (r - 1)) +
        (beta r - alpha) * b r +
        (gamma (r + 1) / theta (r + 1)) * b (r + 1) := by
  classical
  induction b using Finsupp.induction with
  | zero => simp [higham22BasisMultiply]
  | single_add a z b haz hz ih =>
      rw [map_add]
      simp only [Finsupp.add_apply]
      rw [ih]
      simp [higham22BasisMultiply, higham22BasisMultiplyRow]
      simp only [Finsupp.single_apply]
      by_cases hr : r = 0
      · subst r
        cases a with
        | zero => simp <;> ring
        | succ a =>
            cases a with
            | zero => simp <;> ring
            | succ a => simp <;> ring
      · by_cases hprev : a + 1 = r
        · have har : a = r - 1 := by omega
          have hne : a ≠ r := by omega
          have hsub : a - 1 ≠ r := by omega
          have hnext : a ≠ r + 1 := by omega
          have hrr : r - 1 ≠ r := by omega
          have hone : r - 1 + 1 = r := by omega
          have hsubsub : r - 1 - 1 ≠ r := by omega
          simp [hr, hprev, har, hne, hsub, hnext, hrr]
          rw [if_pos hone]
          by_cases hzero : r - 1 = 0
          · rw [if_pos hzero]
            simp
            ring
          · rw [if_neg hzero, Finsupp.single_eq_of_ne hsubsub.symm]
            ring
        · by_cases hdiag : a = r
          · have hsub : a - 1 ≠ r := by omega
            have hprev' : a ≠ r - 1 := by omega
            have hnext : a ≠ r + 1 := by omega
            have hrr : r ≠ r - 1 := by omega
            simp [hr, hprev, hdiag, hsub, hprev', hnext, hrr]
            ring
          · by_cases hnext : a = r + 1
            · have ha0 : a ≠ 0 := by omega
              have hsub : a - 1 = r := by omega
              have hprev' : a ≠ r - 1 := by omega
              have htwo : r + 1 + 1 ≠ r := by omega
              have hfar : r + 1 ≠ r - 1 := by omega
              simp [hr, hprev, hdiag, hnext, ha0, hsub, hprev', htwo, hfar]
              ring
            · have hsub : a - 1 ≠ r := by omega
              have hprev' : a ≠ r - 1 := by omega
              by_cases ha0 : a = 0
              · subst a
                have hzero : 0 ≠ r - 1 := hprev'
                simp [hr, hprev, hdiag, hnext, hzero]
              · rw [if_neg ha0, Finsupp.single_eq_of_ne hsub.symm]
                simp [hr, hprev, hdiag, hnext, hsub, hprev', ha0]

/-- One executable Stage-II coefficient step: form `(x-alpha)q+c` from the
coefficient vector of `q`. -/
noncomputable def higham22StageIICoefficientStep
    (theta beta gamma : ℕ → ℂ) (alpha c : ℂ) (b : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.single 0 c + higham22BasisMultiply theta beta gamma alpha b

/-- The sparse multiplication row synthesizes to `(x-alpha)p_j`. -/
theorem higham22_basisMultiplyRow_synthesis
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (alpha : ℂ) (j : ℕ) :
    higham22BasisSynthesis p
        (higham22BasisMultiplyRow theta beta gamma alpha j) =
      (Polynomial.X - Polynomial.C alpha) * p j := by
  cases j with
  | zero =>
      simp only [higham22BasisMultiplyRow, if_pos, add_zero]
      rw [map_add]
      simp only [higham22BasisSynthesis, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply]
      rw [hp.1, hp.2.1]
      simp only [Polynomial.smul_eq_C_mul]
      have hC : Polynomial.C (theta 0)⁻¹ * Polynomial.C (theta 0) = 1 := by
        rw [← Polynomial.C_mul]
        simp [htheta 0]
      calc
        Polynomial.C (theta 0)⁻¹ *
              (Polynomial.C (theta 0) *
                (Polynomial.X - Polynomial.C (beta 0))) +
            Polynomial.C (beta 0 - alpha) * 1 =
          (Polynomial.C (theta 0)⁻¹ * Polynomial.C (theta 0)) *
              (Polynomial.X - Polynomial.C (beta 0)) +
            Polynomial.C (beta 0 - alpha) := by ring
        _ = Polynomial.X - Polynomial.C alpha := by rw [hC]; simp
        _ = (Polynomial.X - Polynomial.C alpha) * 1 := by ring
  | succ j =>
      have hrec := hp.2.2 j
      simp only [higham22BasisMultiplyRow, Nat.succ_ne_zero, if_false]
      rw [map_add, map_add]
      simp only [higham22BasisSynthesis, Finsupp.lsum_single,
        LinearMap.toSpanSingleton_apply]
      rw [hrec]
      simp only [Polynomial.smul_eq_C_mul]
      have hjsub : j + 1 - 1 = j := by omega
      rw [hjsub]
      have hC : Polynomial.C (theta (j + 1))⁻¹ *
          Polynomial.C (theta (j + 1)) = 1 := by
        rw [← Polynomial.C_mul]
        simp [htheta (j + 1)]
      have hdiv : Polynomial.C (gamma (j + 1) / theta (j + 1)) =
          Polynomial.C (gamma (j + 1)) * Polynomial.C (theta (j + 1))⁻¹ := by
        rw [← Polynomial.C_mul]
        rfl
      rw [hdiv]
      calc
        Polynomial.C (theta (j + 1))⁻¹ *
                (Polynomial.C (theta (j + 1)) *
                      (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1) -
                  Polynomial.C (gamma (j + 1)) * p j) +
              Polynomial.C (beta (j + 1) - alpha) * p (j + 1) +
            Polynomial.C (gamma (j + 1)) *
                Polynomial.C (theta (j + 1))⁻¹ * p j =
          (Polynomial.C (theta (j + 1))⁻¹ *
              Polynomial.C (theta (j + 1))) *
                (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1) +
            Polynomial.C (beta (j + 1) - alpha) * p (j + 1) := by ring
        _ = (Polynomial.X - Polynomial.C alpha) * p (j + 1) := by
          rw [hC]
          simp
          ring

/-- Linear multiplication update is correct after basis synthesis. -/
theorem higham22_basisMultiply_synthesis
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (alpha : ℂ) (b : ℕ →₀ ℂ) :
    higham22BasisSynthesis p (higham22BasisMultiply theta beta gamma alpha b) =
      (Polynomial.X - Polynomial.C alpha) * higham22BasisSynthesis p b := by
  induction b using Finsupp.induction with
  | zero => simp
  | single_add j a b hja ha0 ih =>
      rw [map_add, map_add, map_add, ih]
      have hsingle :
          higham22BasisMultiply theta beta gamma alpha (Finsupp.single j a) =
            a • higham22BasisMultiplyRow theta beta gamma alpha j := by
        simp [higham22BasisMultiply]
      rw [hsingle, map_smul, higham22_basisMultiplyRow_synthesis hp htheta]
      have hsynth :
          higham22BasisSynthesis p (Finsupp.single j a) = a • p j := by
        simp [higham22BasisSynthesis]
      rw [hsynth]
      simp [Polynomial.smul_eq_C_mul, mul_add]
      ring

/-- Equations (22.13)--(22.14), compressed into their common exact sparse
coefficient update. -/
theorem higham22_stageIICoefficientStep_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (alpha c : ℂ) (b : ℕ →₀ ℂ) :
    higham22BasisSynthesis p
        (higham22StageIICoefficientStep theta beta gamma alpha c b) =
      (Polynomial.X - Polynomial.C alpha) * higham22BasisSynthesis p b +
        Polynomial.C c := by
  rw [higham22StageIICoefficientStep, map_add,
    higham22_basisMultiply_synthesis hp htheta]
  simp [higham22BasisSynthesis, hp.1, Polynomial.smul_eq_C_mul, add_comm]

/-- Executable exact Stage II of Algorithm 22.2, processing Newton data in
source order by the backward nesting recurrence. -/
noncomputable def higham22Algorithm22_2StageII
    (theta beta gamma : ℕ → ℂ) : List (ℂ × ℂ) → (ℕ →₀ ℂ)
  | [] => 0
  | (alpha, c) :: rest =>
      higham22StageIICoefficientStep theta beta gamma alpha c
        (higham22Algorithm22_2StageII theta beta gamma rest)

/-- End-to-end Stage-II invariant: the computed sparse coefficients synthesize
to the nested Newton polynomial. -/
theorem higham22_algorithm22_2StageII_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (data : List (ℂ × ℂ)) :
    higham22BasisSynthesis p
        (higham22Algorithm22_2StageII theta beta gamma data) =
      higham22NewtonPolynomialNest data := by
  induction data with
  | nil => simp [higham22Algorithm22_2StageII, higham22NewtonPolynomialNest]
  | cons ac rest ih =>
      rcases ac with ⟨alpha, c⟩
      rw [higham22Algorithm22_2StageII,
        higham22_stageIICoefficientStep_correct hp htheta, ih]
      simp [higham22NewtonPolynomialNest, add_comm]

/-- Index of the previous saved Stage-I value (`clast`) before row `j` is
processed in Algorithm 22.2. -/
noncomputable def higham22StageILastSaved (alpha : ℕ → ℂ) (k : ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 =>
      if j + 1 ≤ k then k
      else if alpha (j + 1) = alpha (j + 1 - k - 1) then
        higham22StageILastSaved alpha k j
      else j + 1

/-- The saved Stage-I index never moves to the right of the part of the row
already scanned. -/
theorem higham22StageILastSaved_le
    (alpha : ℕ → ℂ) (k j : ℕ) (hkj : k ≤ j) :
    higham22StageILastSaved alpha k j ≤ j := by
  induction j with
  | zero =>
      have hk : k = 0 := Nat.le_zero.mp hkj
      subst k
      rfl
  | succ j ih =>
      simp only [higham22StageILastSaved]
      split_ifs with hle heq
      · exact hkj
      · exact (ih (Nat.le_of_lt_succ (Nat.lt_of_not_ge hle))).trans
          (Nat.le_succ j)
      · exact Nat.le_refl (j + 1)

/-- One full outer sweep of the printed confluent divided-difference Stage I.
The `clast` scan is represented by `higham22StageILastSaved`. -/
noncomputable def higham22Algorithm22_2StageIStep
    (alpha c : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  fun j ↦
    if j ≤ k then c j
    else if alpha j = alpha (j - k - 1) then
      c j / (k + 1 : ℂ)
    else
      (c j - c (higham22StageILastSaved alpha k (j - 1))) /
        (alpha j - alpha (j - k - 1))

/-- The copied-prefix branch of Stage I. -/
theorem higham22_algorithm22_2StageIStep_of_le
    (alpha c : ℕ → ℂ) {k j : ℕ} (h : j ≤ k) :
    higham22Algorithm22_2StageIStep alpha c k j = c j := by
  simp [higham22Algorithm22_2StageIStep, h]

/-- The confluent branch of Stage I. -/
theorem higham22_algorithm22_2StageIStep_of_equal
    (alpha c : ℕ → ℂ) {k j : ℕ} (hjk : k < j)
    (hα : alpha j = alpha (j - k - 1)) :
    higham22Algorithm22_2StageIStep alpha c k j = c j / (k + 1 : ℂ) := by
  simp [higham22Algorithm22_2StageIStep, Nat.not_le_of_gt hjk, hα]

/-- The ordinary divided-difference branch of Stage I, including the saved
`clast` index of the printed in-place loop. -/
theorem higham22_algorithm22_2StageIStep_of_distinct
    (alpha c : ℕ → ℂ) {k j : ℕ} (hjk : k < j)
    (hα : alpha j ≠ alpha (j - k - 1)) :
    higham22Algorithm22_2StageIStep alpha c k j =
      (c j - c (higham22StageILastSaved alpha k (j - 1))) /
        (alpha j - alpha (j - k - 1)) := by
  simp [higham22Algorithm22_2StageIStep, Nat.not_le_of_gt hjk, hα]

/-- Exact Stage-I states `c^(k)` of Algorithm 22.2. -/
noncomputable def higham22Algorithm22_2StageI
    (alpha f : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => f
  | k + 1 =>
      higham22Algorithm22_2StageIStep alpha
        (higham22Algorithm22_2StageI alpha f k) k

/-- Equation (22.15), actual Stage-I state recurrence. -/
theorem higham22_eq22_15
    (alpha f : ℕ → ℂ) (k : ℕ) :
    higham22Algorithm22_2StageI alpha f (k + 1) =
      higham22Algorithm22_2StageIStep alpha
        (higham22Algorithm22_2StageI alpha f k) k := rfl

/-- Extend a finite source vector by zero.  This lets the literal
natural-indexed in-place recurrences be reused without adding fictitious
coordinates to a finite matrix factor. -/
def higham22FinExtend {N : ℕ} (x : Fin N → ℂ) : ℕ → ℂ :=
  fun j ↦ if h : j < N then x ⟨j, h⟩ else 0

@[simp]
theorem higham22FinExtend_apply {N : ℕ} (x : Fin N → ℂ) (i : Fin N) :
    higham22FinExtend x i = x i := by
  simp [higham22FinExtend, i.isLt]

theorem higham22FinExtend_add {N : ℕ} (x y : Fin N → ℂ) :
    higham22FinExtend (x + y) = higham22FinExtend x + higham22FinExtend y := by
  funext j
  simp only [higham22FinExtend, Pi.add_apply]
  split_ifs <;> simp

theorem higham22FinExtend_smul {N : ℕ} (z : ℂ) (x : Fin N → ℂ) :
    higham22FinExtend (z • x) = z • higham22FinExtend x := by
  funext j
  simp only [higham22FinExtend, Pi.smul_apply]
  split_ifs <;> simp

@[simp]
theorem higham22FinExtend_single {N : ℕ}
    (j : Fin N) (z : ℂ) (m : ℕ) :
    higham22FinExtend (Pi.single j z) m = if m = j then z else 0 := by
  by_cases hm : m < N
  · simp [higham22FinExtend, hm, Pi.single_apply, Fin.ext_iff]
  · have hmj : m ≠ (j : ℕ) := by omega
    simp [higham22FinExtend, hm, hmj]

theorem higham22Algorithm22_2StageIStep_add
    (alpha c d : ℕ → ℂ) (k : ℕ) :
    higham22Algorithm22_2StageIStep alpha (c + d) k =
      higham22Algorithm22_2StageIStep alpha c k +
        higham22Algorithm22_2StageIStep alpha d k := by
  funext j
  simp only [higham22Algorithm22_2StageIStep, Pi.add_apply]
  split_ifs <;> ring

theorem higham22Algorithm22_2StageIStep_smul
    (alpha c : ℕ → ℂ) (z : ℂ) (k : ℕ) :
    higham22Algorithm22_2StageIStep alpha (z • c) k =
      z • higham22Algorithm22_2StageIStep alpha c k := by
  funext j
  simp only [higham22Algorithm22_2StageIStep, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The actual `k`th Stage-I sweep, as a linear map on the finite source
vector.  Its definition calls the same confluent/ordinary branch graph as
the printed in-place implementation. -/
noncomputable def higham22StageILowerLinear {N : ℕ}
    (alpha : Fin N → ℂ) (k : ℕ) :
    (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) where
  toFun c := fun i ↦
    higham22Algorithm22_2StageIStep
      (higham22FinExtend alpha) (higham22FinExtend c) k i
  map_add' c d := by
    rw [higham22FinExtend_add,
      higham22Algorithm22_2StageIStep_add]
    rfl
  map_smul' z c := by
    rw [higham22FinExtend_smul,
      higham22Algorithm22_2StageIStep_smul]
    rfl

/-- The finite lower factor `L_k` produced from the actual Stage-I sweep. -/
noncomputable def higham22StageILowerFactor {N : ℕ}
    (alpha : Fin N → ℂ) (k : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  LinearMap.toMatrix' (higham22StageILowerLinear alpha k)

/-- The factor acts exactly as the printed Stage-I sweep. -/
@[simp]
theorem higham22_stageILowerFactor_mulVec {N : ℕ}
    (alpha c : Fin N → ℂ) (k : ℕ) :
    (higham22StageILowerFactor alpha k).mulVec c =
      fun i : Fin N ↦ higham22Algorithm22_2StageIStep
        (higham22FinExtend alpha) (higham22FinExtend c) k i := by
  simp [higham22StageILowerFactor, higham22StageILowerLinear]

/-- The loop-derived `L_k` really is lower triangular. -/
theorem higham22_stageILowerFactor_lowerTriangular {N : ℕ}
    (alpha : Fin N → ℂ) (k : ℕ) :
    Matrix.BlockTriangular (higham22StageILowerFactor alpha k)
      OrderDual.toDual := by
  intro i j hij
  change i < j at hij
  rw [higham22StageILowerFactor, LinearMap.toMatrix'_apply]
  change higham22Algorithm22_2StageIStep
      (higham22FinExtend alpha)
      (higham22FinExtend (Pi.single j 1)) k i = 0
  by_cases hik : (i : ℕ) ≤ k
  · simp [higham22Algorithm22_2StageIStep, hik, higham22FinExtend,
      ne_of_lt hij]
  · have hki : k < (i : ℕ) := Nat.lt_of_not_ge hik
    have hlastle :
        higham22StageILastSaved (higham22FinExtend alpha) k ((i : ℕ) - 1) ≤
          (i : ℕ) - 1 :=
      higham22StageILastSaved_le _ _ _ (by omega)
    have hlasti :
        higham22StageILastSaved (higham22FinExtend alpha) k ((i : ℕ) - 1) <
          (i : ℕ) := by omega
    have hlastN :
        higham22StageILastSaved (higham22FinExtend alpha) k ((i : ℕ) - 1) < N :=
      hlasti.trans i.isLt
    have hlastj :
        higham22StageILastSaved (higham22FinExtend alpha) k ((i : ℕ) - 1) <
          (j : ℕ) := hlasti.trans hij
    have hiZero : higham22FinExtend (Pi.single j 1) i = 0 := by
      rw [higham22FinExtend_apply]
      simp [ne_of_lt hij]
    have hjlast : j ≠
        (⟨higham22StageILastSaved (higham22FinExtend alpha) k
          ((i : ℕ) - 1), hlastN⟩ : Fin N) := by
      exact ne_of_gt hlastj
    have hlastZero :
        higham22FinExtend (Pi.single j 1)
            (higham22StageILastSaved (higham22FinExtend alpha) k
              ((i : ℕ) - 1)) = 0 := by
      simp [higham22FinExtend, hlastN, hjlast]
    simp [higham22Algorithm22_2StageIStep, hik, hiZero, hlastZero]

/-- Finite Stage I, using exactly the source sweeps `L_0,L_1,...`. -/
noncomputable def higham22Algorithm22_2StageIFin {N : ℕ}
    (alpha f : Fin N → ℂ) : ℕ → (Fin N → ℂ)
  | 0 => f
  | k + 1 => higham22StageILowerLinear alpha k
      (higham22Algorithm22_2StageIFin alpha f k)

/-- The finite Stage-I executor is not a new specification: on every source
coordinate it is exactly the original natural-indexed in-place recurrence. -/
theorem higham22_algorithm22_2StageIFin_eq_stageI {N : ℕ}
    (alpha f : Fin N → ℂ) (steps : ℕ) (i : Fin N) :
    higham22Algorithm22_2StageIFin alpha f steps i =
      higham22Algorithm22_2StageI
        (higham22FinExtend alpha) (higham22FinExtend f) steps i := by
  induction steps generalizing i with
  | zero =>
      simp [higham22Algorithm22_2StageIFin, higham22Algorithm22_2StageI]
  | succ k ih =>
      rw [higham22Algorithm22_2StageIFin, higham22Algorithm22_2StageI]
      change higham22Algorithm22_2StageIStep
          (higham22FinExtend alpha)
          (higham22FinExtend
            (higham22Algorithm22_2StageIFin alpha f k)) k i =
        higham22Algorithm22_2StageIStep
          (higham22FinExtend alpha)
          (higham22Algorithm22_2StageI
            (higham22FinExtend alpha) (higham22FinExtend f) k) k i
      by_cases hik : (i : ℕ) ≤ k
      · simp [higham22Algorithm22_2StageIStep, hik, ih]
      · have hki : k < (i : ℕ) := Nat.lt_of_not_ge hik
        by_cases hα : higham22FinExtend alpha i =
            higham22FinExtend alpha ((i : ℕ) - k - 1)
        · simp [higham22Algorithm22_2StageIStep, hik, hα, ih]
        · have hlastle :
              higham22StageILastSaved (higham22FinExtend alpha) k
                  ((i : ℕ) - 1) ≤ (i : ℕ) - 1 :=
            higham22StageILastSaved_le _ _ _ (by omega)
          have hlasti :
              higham22StageILastSaved (higham22FinExtend alpha) k
                  ((i : ℕ) - 1) < (i : ℕ) := by omega
          have hlastN :
              higham22StageILastSaved (higham22FinExtend alpha) k
                  ((i : ℕ) - 1) < N := hlasti.trans i.isLt
          simp [higham22Algorithm22_2StageIStep, hik,
            higham22FinExtend, i.isLt, hlastN, ih]

/-- Independent two-dimensional divided-difference table for distinct nodes.
The prefix `j ≤ k` consists of coefficients already frozen by earlier
sweeps; the remaining row is the standard ordinary recurrence. -/
noncomputable def higham22OrdinaryDividedDifferenceTable
    (alpha f : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, j => f j
  | k + 1, j =>
      if j ≤ k then higham22OrdinaryDividedDifferenceTable alpha f k j
      else
        (higham22OrdinaryDividedDifferenceTable alpha f k j -
            higham22OrdinaryDividedDifferenceTable alpha f k (j - 1)) /
          (alpha j - alpha (j - k - 1))

theorem higham22StageILastSaved_eq_k_of_le
    (alpha : ℕ → ℂ) (k j : ℕ) (hjk : j ≤ k) :
    higham22StageILastSaved alpha k j = k := by
  cases j <;> simp [higham22StageILastSaved, hjk]

/-- With distinct nodes every ordinary branch saves the immediately
preceding table entry, exactly as in the standard divided-difference table. -/
theorem higham22StageILastSaved_eq_pred_of_injective
    (alpha : ℕ → ℂ) (halpha : Function.Injective alpha)
    (k j : ℕ) (hkj : k < j) :
    higham22StageILastSaved alpha k (j - 1) = j - 1 := by
  cases j with
  | zero => omega
  | succ t =>
      by_cases htk : t ≤ k
      · have hkt : k = t := by omega
        simpa [hkt] using
          higham22StageILastSaved_eq_k_of_le alpha k t htk
      · cases t with
        | zero => omega
        | succ r =>
            have hindex : r + 1 ≠ r + 1 - k - 1 := by omega
            have hnode : alpha (r + 1) ≠ alpha (r + 1 - k - 1) :=
              halpha.ne hindex
            simp [higham22StageILastSaved, htk, hnode]

/-- Actual Stage-I invariant in the nonconfluent case: every executable
state equals the mathematical ordinary divided-difference table.  This is a
producer theorem from the loop, not a premise containing interpolation. -/
theorem higham22_algorithm22_2StageI_ordinary_invariant
    (alpha f : ℕ → ℂ) (halpha : Function.Injective alpha)
    (steps j : ℕ) :
    higham22Algorithm22_2StageI alpha f steps j =
      higham22OrdinaryDividedDifferenceTable alpha f steps j := by
  induction steps generalizing j with
  | zero => rfl
  | succ k ih =>
      rw [higham22Algorithm22_2StageI,
        higham22OrdinaryDividedDifferenceTable]
      by_cases hjk : j ≤ k
      · simp [higham22Algorithm22_2StageIStep, hjk, ih]
      · have hkj : k < j := Nat.lt_of_not_ge hjk
        have hindex : j ≠ j - k - 1 := by omega
        have hnode : alpha j ≠ alpha (j - k - 1) := halpha.ne hindex
        have hlast :=
          higham22StageILastSaved_eq_pred_of_injective alpha halpha k j hkj
        simp [higham22Algorithm22_2StageIStep, hjk, hnode, hlast, ih]

/-- Natural-indexed form of the source ordering assumption (22.5). -/
def Higham22ContiguousNodesNat (alpha : ℕ → ℂ) : Prop :=
  ∀ i j, i < j → alpha i = alpha j →
    ∀ m, i ≤ m → m ≤ j → alpha m = alpha i

/-- Initial-segment form of (22.5), suitable for a zero-extended finite
source vector. -/
def Higham22ContiguousNodesNatOn (alpha : ℕ → ℂ) (N : ℕ) : Prop :=
  ∀ i j, i < j → j < N → alpha i = alpha j →
    ∀ m, i ≤ m → m ≤ j → alpha m = alpha i

theorem higham22FinExtend_contiguousNodesNatOn {N : ℕ}
    {alpha : Fin N → ℂ} (hcontig : Higham22ContiguousNodes alpha) :
    Higham22ContiguousNodesNatOn (higham22FinExtend alpha) N := by
  intro i j hij hjN hα m him hmj
  have hiN : i < N := hij.trans hjN
  have hmN : m < N := lt_of_le_of_lt hmj hjN
  have hαfin : alpha ⟨i, hiN⟩ = alpha ⟨j, hjN⟩ := by
    calc
      alpha ⟨i, hiN⟩ = higham22FinExtend alpha i :=
        (higham22FinExtend_apply alpha ⟨i, hiN⟩).symm
      _ = higham22FinExtend alpha j := hα
      _ = alpha ⟨j, hjN⟩ := higham22FinExtend_apply alpha ⟨j, hjN⟩
  have hfin := hcontig ⟨i, hiN⟩ ⟨j, hjN⟩ hij hαfin
    ⟨m, hmN⟩ him hmj
  calc
    higham22FinExtend alpha m = alpha ⟨m, hmN⟩ :=
      higham22FinExtend_apply alpha ⟨m, hmN⟩
    _ = alpha ⟨i, hiN⟩ := hfin
    _ = higham22FinExtend alpha i :=
      (higham22FinExtend_apply alpha ⟨i, hiN⟩).symm

/-- Source recurrence (22.9) as a two-dimensional confluent divided-
difference table.  In the confluent branch the original derivative datum
`f j` is divided by `(k+1)!`, rather than assuming the in-place loop has
already accumulated the preceding factorial factors. -/
noncomputable def higham22ConfluentDividedDifferenceTable
    (alpha f : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0, j => f j
  | k + 1, j =>
      if j ≤ k then higham22ConfluentDividedDifferenceTable alpha f k j
      else if alpha j = alpha (j - k - 1) then
        f j / (Nat.factorial (k + 1) : ℂ)
      else
        (higham22ConfluentDividedDifferenceTable alpha f k j -
            higham22ConfluentDividedDifferenceTable alpha f k
              (higham22StageILastSaved alpha k (j - 1))) /
          (alpha j - alpha (j - k - 1))

/-- If the whole active window ends at the same node, the actual in-place
loop has accumulated exactly the factorial normalization printed in (22.9). -/
theorem higham22_algorithm22_2StageI_eq_div_factorial_of_window_equal
    (alpha f : ℕ → ℂ) (k j : ℕ) (hkj : k ≤ j)
    (hwindow : ∀ r, r < k → alpha j = alpha (j - r - 1)) :
    higham22Algorithm22_2StageI alpha f k j =
      f j / (Nat.factorial k : ℂ) := by
  induction k with
  | zero => simp [higham22Algorithm22_2StageI]
  | succ k ih =>
      have hkj' : k < j := by omega
      have hprev : ∀ r, r < k → alpha j = alpha (j - r - 1) :=
        fun r hr ↦ hwindow r (hr.trans (Nat.lt_succ_self k))
      have hendpoint : alpha j = alpha (j - k - 1) :=
        hwindow k (Nat.lt_succ_self k)
      rw [higham22Algorithm22_2StageI]
      simp only [higham22Algorithm22_2StageIStep,
        Nat.not_le_of_gt hkj', if_false, hendpoint, if_true]
      rw [ih (Nat.le_of_lt hkj') hprev, Nat.factorial_succ, Nat.cast_mul,
        Nat.cast_add, Nat.cast_one]
      have hfac : (Nat.factorial k : ℂ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero k
      have hsucc : (k + 1 : ℂ) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero k
      field_simp

/-- Equation (22.9) invariant for the actual Stage-I graph, including
repeated contiguous nodes and raw derivative data. -/
theorem higham22_algorithm22_2StageI_confluent_invariant_on
    (alpha f : ℕ → ℂ) (N : ℕ)
    (hcontig : Higham22ContiguousNodesNatOn alpha N)
    (steps j : ℕ) (hjN : j < N) :
    higham22Algorithm22_2StageI alpha f steps j =
      higham22ConfluentDividedDifferenceTable alpha f steps j := by
  induction steps generalizing j with
  | zero => rfl
  | succ k ih =>
      rw [higham22Algorithm22_2StageI,
        higham22ConfluentDividedDifferenceTable]
      by_cases hjk : j ≤ k
      · simp [higham22Algorithm22_2StageIStep, hjk, ih j hjN]
      · have hkj : k < j := Nat.lt_of_not_ge hjk
        by_cases hendpoint : alpha j = alpha (j - k - 1)
        · have hleftlt : j - k - 1 < j := by omega
          have hblock : ∀ m, j - k - 1 ≤ m → m ≤ j →
              alpha m = alpha (j - k - 1) :=
            hcontig (j - k - 1) j hleftlt hjN hendpoint.symm
          have hwindow : ∀ r, r < k →
              alpha j = alpha (j - r - 1) := by
            intro r hr
            have hm := hblock (j - r - 1) (by omega) (by omega)
            exact hendpoint.trans hm.symm
          have hfactor :=
            higham22_algorithm22_2StageI_eq_div_factorial_of_window_equal
              alpha f k j (Nat.le_of_lt hkj) hwindow
          simp only [higham22Algorithm22_2StageIStep,
            Nat.not_le_of_gt hkj, if_false, hendpoint, if_true]
          rw [hfactor, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
            Nat.cast_one]
          have hfac : (Nat.factorial k : ℂ) ≠ 0 := by
            exact_mod_cast Nat.factorial_ne_zero k
          have hsucc : (k + 1 : ℂ) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero k
          field_simp
        · have hlastle : higham22StageILastSaved alpha k (j - 1) ≤ j - 1 :=
            higham22StageILastSaved_le _ _ _ (by omega)
          have hlastN : higham22StageILastSaved alpha k (j - 1) < N := by
            omega
          simp [higham22Algorithm22_2StageIStep, hjk, hendpoint,
            ih j hjN, ih _ hlastN]

theorem higham22_algorithm22_2StageI_confluent_invariant
    (alpha f : ℕ → ℂ) (hcontig : Higham22ContiguousNodesNat alpha)
    (steps j : ℕ) :
    higham22Algorithm22_2StageI alpha f steps j =
      higham22ConfluentDividedDifferenceTable alpha f steps j := by
  apply higham22_algorithm22_2StageI_confluent_invariant_on
    alpha f (j + 1) _ steps j (Nat.lt_succ_self j)
  intro i q hiq _hqN hα m him hmq
  exact hcontig i q hiq hα m him hmq

/-- Finite source-facing repeated-node invariant for Stage I of Algorithm
22.2. -/
theorem higham22_algorithm22_2StageIFin_confluent_invariant {N : ℕ}
    (alpha f : Fin N → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (steps : ℕ) (j : Fin N) :
    higham22Algorithm22_2StageIFin alpha f steps j =
      higham22ConfluentDividedDifferenceTable
        (higham22FinExtend alpha) (higham22FinExtend f) steps j := by
  rw [higham22_algorithm22_2StageIFin_eq_stageI]
  exact higham22_algorithm22_2StageI_confluent_invariant_on
    _ _ N (higham22FinExtend_contiguousNodesNatOn hcontig) steps j j.isLt

/-- Once a divided-difference coefficient reaches the diagonal it is copied
unchanged by all later Stage-I sweeps. -/
theorem higham22ConfluentDividedDifferenceTable_eq_diagonal_of_le
    (alpha f : ℕ → ℂ) {j steps : ℕ} (hjs : j ≤ steps) :
    higham22ConfluentDividedDifferenceTable alpha f steps j =
      higham22ConfluentDividedDifferenceTable alpha f j j := by
  induction steps with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjs
      subst j
      rfl
  | succ k ih =>
      by_cases hjk : j ≤ k
      · rw [higham22ConfluentDividedDifferenceTable]
        simp only [hjk, if_true]
        exact ih hjk
      · have hj : j = k + 1 := by omega
        subst j
        rfl

/-- Final finite Stage I exposes the diagonal confluent divided differences
used as Newton coefficients. -/
theorem higham22_algorithm22_2StageIFin_eq_confluent_diagonal {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (j : Fin (n + 1)) :
    higham22Algorithm22_2StageIFin alpha f n j =
      higham22ConfluentDividedDifferenceTable
        (higham22FinExtend alpha) (higham22FinExtend f) j j := by
  rw [higham22_algorithm22_2StageIFin_confluent_invariant alpha f hcontig]
  exact higham22ConfluentDividedDifferenceTable_eq_diagonal_of_le _ _
    (by omega)

/-- Product `L_{s-1}⋯L_0` of the factors genuinely extracted from Stage I. -/
noncomputable def higham22StageILowerProduct {N : ℕ}
    (alpha : Fin N → ℂ) : ℕ → Matrix (Fin N) (Fin N) ℂ
  | 0 => 1
  | k + 1 => higham22StageILowerFactor alpha k *
      higham22StageILowerProduct alpha k

/-- The finite Stage-I product computes the actual finite Stage-I state. -/
theorem higham22_stageILowerProduct_mulVec {N : ℕ}
    (alpha f : Fin N → ℂ) (steps : ℕ) :
    (higham22StageILowerProduct alpha steps).mulVec f =
      higham22Algorithm22_2StageIFin alpha f steps := by
  induction steps with
  | zero => simp [higham22StageILowerProduct, higham22Algorithm22_2StageIFin]
  | succ k ih =>
      rw [higham22StageILowerProduct,
        ← Matrix.mulVec_mulVec f (higham22StageILowerFactor alpha k)
          (higham22StageILowerProduct alpha k), ih]
      simp [higham22StageILowerFactor, higham22StageILowerLinear,
        higham22Algorithm22_2StageIFin]

/-- End-to-end exact Algorithm 22.2 state: Stage I generates the Newton
coefficients and Stage II performs the sparse recurrence-basis conversion. -/
noncomputable def higham22Algorithm22_2
    (theta beta gamma : ℕ → ℂ) {N : ℕ}
    (alpha f : Fin N → ℂ) : ℕ →₀ ℂ :=
  let alphaNat : ℕ → ℂ := fun j ↦ if h : j < N then alpha ⟨j, h⟩ else 0
  let fNat : ℕ → ℂ := fun j ↦ if h : j < N then f ⟨j, h⟩ else 0
  let c := higham22Algorithm22_2StageI alphaNat fNat N
  higham22Algorithm22_2StageII theta beta gamma
    (List.ofFn fun i : Fin N ↦ (alpha i, c i))

/-- Exact polynomial invariant for the whole implemented Algorithm 22.2 path.
It synthesizes to the Newton nest generated by the actual Stage-I output. -/
theorem higham22_algorithm22_2_newton_invariant
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {N : ℕ} (alpha f : Fin N → ℂ) :
    higham22BasisSynthesis p
        (higham22Algorithm22_2 theta beta gamma alpha f) =
      let alphaNat : ℕ → ℂ := fun j ↦ if h : j < N then alpha ⟨j, h⟩ else 0
      let fNat : ℕ → ℂ := fun j ↦ if h : j < N then f ⟨j, h⟩ else 0
      let c := higham22Algorithm22_2StageI alphaNat fNat N
      higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin N ↦ (alpha i, c i)) := by
  simp only [higham22Algorithm22_2]
  apply higham22_algorithm22_2StageII_correct hp htheta

/-- Vandermonde-like matrix from section 22.2. -/
noncomputable def higham22VandermondeLike {n : ℕ}
    (p : Fin n → Polynomial ℂ) (alpha : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j ↦ (p i).eval (alpha j)

/-- Equation (22.7): the polynomial represented in the chosen basis. -/
noncomputable def higham22Psi {n : ℕ}
    (p : Fin n → Polynomial ℂ) (a : Fin n → ℂ) : Polynomial ℂ :=
  ∑ i : Fin n, Polynomial.C (a i) * p i

/-- Evaluation form of equation (22.7). -/
theorem higham22_eq22_7_eval {n : ℕ}
    (p : Fin n → Polynomial ℂ) (a : Fin n → ℂ) (x : ℂ) :
    (higham22Psi p a).eval x = ∑ i : Fin n, a i * (p i).eval x := by
  simp [higham22Psi, Polynomial.eval_finset_sum]

/-- Equations (22.10)--(22.11), in source order: nested multiplication for a
Newton-form polynomial.  Each pair stores `(alpha_k, c_k)`. -/
def higham22NewtonNest : List (ℂ × ℂ) → ℂ → ℂ
  | [], _x => 0
  | (alpha, c) :: rest, x => (x - alpha) * higham22NewtonNest rest x + c

@[simp]
theorem higham22_eq22_10_empty (x : ℂ) :
    higham22NewtonNest [] x = 0 := rfl

@[simp]
theorem higham22_eq22_11_step (alpha c : ℂ)
    (rest : List (ℂ × ℂ)) (x : ℂ) :
    higham22NewtonNest ((alpha, c) :: rest) x =
      (x - alpha) * higham22NewtonNest rest x + c := rfl

/-! The literal primal Algorithm 22.3 is recorded next.  The repeated-node
Hermite argument identifying the dual factor product with `P⁻ᵀ` is proved
after the finite Algorithm 22.2 factor construction below. -/

/-- The descending inner loop in Stage I of the printed Algorithm 22.3.
For an upper loop index `m`, it visits `j = m, ..., 2`; the updated coordinate
is the source coordinate `k+j`. -/
noncomputable def higham22Algorithm22_3StageIInner
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (k : ℕ) :
    ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, d => d
  | 1, d => d
  | j + 2, d =>
      let r := j + 2
      let d' := Function.update d (k + r)
        ((gamma (r - 1) / theta (r - 1)) * d (k + r - 2) +
          (beta (r - 1) - alpha k) * d (k + r - 1) +
          d (k + r) / theta (r - 1))
      higham22Algorithm22_3StageIInner theta beta gamma alpha k (j + 1) d'

/-- The increasing outer loop `k = 0, ..., n-2` in Stage I of Algorithm 22.3.
The natural argument counts completed outer sweeps. -/
noncomputable def higham22Algorithm22_3StageIOuter
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ) :
    ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, d => d
  | k + 1, d =>
      let previous :=
        higham22Algorithm22_3StageIOuter theta beta gamma alpha n k d
      let swept :=
        higham22Algorithm22_3StageIInner theta beta gamma alpha k (n - k) previous
      Function.update swept (k + 1)
        ((beta 0 - alpha k) * swept k + swept (k + 1) / theta 0)

/-- Stage I of Algorithm 22.3, including the final source assignment to `d_n`.
Here `n` is the largest vector index, so the vector has length `n+1`. -/
noncomputable def higham22Algorithm22_3StageI
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ)
    (b : ℕ → ℂ) : ℕ → ℂ :=
  if n = 0 then b
  else
    let d := higham22Algorithm22_3StageIOuter theta beta gamma alpha n (n - 1) b
    Function.update d n
      ((beta 0 - alpha (n - 1)) * d (n - 1) + d n / theta 0)

/-- The descending inner loop in Stage II of Algorithm 22.3.  Besides the
in-place vector it returns the source variable `xlast`.  Calling it with
`count = n-k` visits exactly `j = n, ..., k+1`. -/
noncomputable def higham22Algorithm22_3StageIIInner
    (alpha : ℕ → ℂ) (k : ℕ) :
    ℕ → (ℕ → ℂ) → ℂ → ((ℕ → ℂ) × ℂ)
  | 0, x, xlast => (x, xlast)
  | count + 1, x, xlast =>
      let j := k + count + 1
      if alpha j = alpha (j - k - 1) then
        higham22Algorithm22_3StageIIInner alpha k count
          (Function.update x j (x j / (k + 1 : ℂ))) xlast
      else
        let temp := x j / (alpha j - alpha (j - k - 1))
        higham22Algorithm22_3StageIIInner alpha k count
          (Function.update x j (temp - xlast)) temp

/-- The descending outer recursion `k = s-1, ..., 0` in Stage II of
Algorithm 22.3.  Naming this source loop separately exposes its induction
principle while retaining the printed in-place update order. -/
noncomputable def higham22Algorithm22_3StageIIOuter
    (alpha : ℕ → ℂ) (n : ℕ) : ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, y => y
  | k + 1, y =>
      let result := higham22Algorithm22_3StageIIInner alpha k (n - k) y 0
      higham22Algorithm22_3StageIIOuter alpha n k
        (Function.update result.1 k (result.1 k - result.2))

/-- The descending outer loop `k = n-1, ..., 0` in Stage II of Algorithm
22.3. -/
noncomputable def higham22Algorithm22_3StageII
    (alpha : ℕ → ℂ) (n : ℕ) (x : ℕ → ℂ) : ℕ → ℂ :=
  higham22Algorithm22_3StageIIOuter alpha n n x

/-- The actual two-stage primal Algorithm 22.3.  Its output is restricted to
the source vector indices `0, ..., n`; the internal natural-indexed state makes
the printed in-place update order explicit. -/
noncomputable def higham22Algorithm22_3
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  let alphaNat : ℕ → ℂ := fun j ↦ if h : j < n + 1 then alpha ⟨j, h⟩ else 0
  let bNat : ℕ → ℂ := fun j ↦ if h : j < n + 1 then b ⟨j, h⟩ else 0
  let d := higham22Algorithm22_3StageI theta beta gamma alphaNat n bNat
  fun i ↦ higham22Algorithm22_3StageII alphaNat n d i

/-- The confluent branch of the actual Stage-II inner loop. -/
theorem higham22_algorithm22_3StageIIInner_of_equal
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ)
    (hα : alpha (k + count + 1) = alpha (k + count + 1 - k - 1)) :
    higham22Algorithm22_3StageIIInner alpha k (count + 1) x xlast =
      higham22Algorithm22_3StageIIInner alpha k count
        (Function.update x (k + count + 1)
          (x (k + count + 1) / (k + 1 : ℂ))) xlast := by
  simp [higham22Algorithm22_3StageIIInner, hα]

/-- The ordinary divided-difference branch of the actual Stage-II inner loop. -/
theorem higham22_algorithm22_3StageIIInner_of_distinct
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ)
    (hα : alpha (k + count + 1) ≠ alpha (k + count + 1 - k - 1)) :
    higham22Algorithm22_3StageIIInner alpha k (count + 1) x xlast =
      let temp := x (k + count + 1) /
        (alpha (k + count + 1) - alpha (k + count + 1 - k - 1))
      higham22Algorithm22_3StageIIInner alpha k count
        (Function.update x (k + count + 1) (temp - xlast)) temp := by
  simp [higham22Algorithm22_3StageIIInner, hα]

/-- The two assignments preceding the backward loop in the printed Stage II of
Algorithm 22.2.  The parameter `n` is the largest source vector index. -/
noncomputable def higham22Algorithm22_2PrintedStageIIInitial
    (theta beta : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ)
    (c : ℕ → ℂ) : ℕ → ℂ :=
  if n = 0 then c
  else
    Function.update
      (Function.update c (n - 1)
        (c (n - 1) + (beta 0 - alpha (n - 1)) * c n))
      n (c n / theta 0)

/-- One simultaneous mathematical view of the source's in-place update for a
fixed `k` in Stage II of Algorithm 22.2.  The printed ascending inner loop has
the same values because every right-hand side reads only coordinates at or
above the coordinate being written. -/
noncomputable def higham22Algorithm22_2PrintedStageIIStep
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n k : ℕ)
    (a : ℕ → ℂ) : ℕ → ℂ :=
  fun i ↦
    if i = k then
      a k + (beta 0 - alpha k) * a (k + 1) +
        (gamma 1 / theta 1) * a (k + 2)
    else if k < i ∧ i + 2 ≤ n then
      let j := i - k
      a i / theta (j - 1) + (beta j - alpha k) * a (i + 1) +
        (gamma (j + 1) / theta (j + 1)) * a (i + 2)
    else if i = n - 1 then
      a (n - 1) / theta (n - k - 2) +
        (beta (n - k - 1) - alpha k) * a n
    else if i = n then
      a n / theta (n - k - 1)
    else
      a i

/-- The descending source loop `k = n-2, ..., 0` in Stage II of Algorithm
22.2.  Calling this function with `steps = n-1` executes exactly that range. -/
noncomputable def higham22Algorithm22_2PrintedStageIIOuter
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ) :
    ℕ → (ℕ → ℂ) → (ℕ → ℂ)
  | 0, a => a
  | k + 1, a =>
      higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n k
        (higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a)

/-- The literal Stage II of Algorithm 22.2, with its special first two
assignments followed by the descending outer loop. -/
noncomputable def higham22Algorithm22_2PrintedStageII
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n : ℕ)
    (c : ℕ → ℂ) : ℕ → ℂ :=
  let initial := higham22Algorithm22_2PrintedStageIIInitial theta beta alpha n c
  higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n (n - 1) initial

/-- Equation (22.16) as the actual fixed-`k` state recurrence implemented by
the printed Stage-II outer loop. -/
theorem higham22_eq22_16
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n k : ℕ)
    (a : ℕ → ℂ) :
    higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n (k + 1) a =
      higham22Algorithm22_2PrintedStageIIOuter theta beta gamma alpha n k
        (higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a) := rfl

theorem higham22Algorithm22_2PrintedStageIIStep_add
    (theta beta gamma alpha a b : ℕ → ℂ) (n k : ℕ) :
    higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k (a + b) =
      higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a +
        higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k b := by
  funext i
  simp only [higham22Algorithm22_2PrintedStageIIStep, Pi.add_apply]
  split_ifs <;> ring

theorem higham22Algorithm22_2PrintedStageIIStep_smul
    (theta beta gamma alpha a : ℕ → ℂ) (z : ℂ) (n k : ℕ) :
    higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k (z • a) =
      z • higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a := by
  funext i
  simp only [higham22Algorithm22_2PrintedStageIIStep, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The actual `k`th Stage-II sweep as a linear map on the finite source
vector.  This is the matrix-free producer of Higham's `U_k`. -/
noncomputable def higham22StageIIUpperLinear
    (theta beta gamma : ℕ → ℂ) {n : ℕ} (alpha : Fin (n + 1) → ℂ) (k : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun a := fun i ↦
    higham22Algorithm22_2PrintedStageIIStep theta beta gamma
      (higham22FinExtend alpha) n k (higham22FinExtend a) i
  map_add' a b := by
    rw [higham22FinExtend_add,
      higham22Algorithm22_2PrintedStageIIStep_add]
    rfl
  map_smul' z a := by
    rw [higham22FinExtend_smul,
      higham22Algorithm22_2PrintedStageIIStep_smul]
    rfl

/-- The finite upper factor `U_k` produced from the actual Stage-II sweep. -/
noncomputable def higham22StageIIUpperFactor
    (theta beta gamma : ℕ → ℂ) {n : ℕ} (alpha : Fin (n + 1) → ℂ) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  LinearMap.toMatrix' (higham22StageIIUpperLinear theta beta gamma alpha k)

/-- The extracted upper factor acts exactly as the printed Stage-II sweep. -/
@[simp]
theorem higham22_stageIIUpperFactor_mulVec
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    (higham22StageIIUpperFactor theta beta gamma alpha k).mulVec a =
      fun i : Fin (n + 1) ↦
        higham22Algorithm22_2PrintedStageIIStep theta beta gamma
          (higham22FinExtend alpha) n k (higham22FinExtend a) i := by
  simp [higham22StageIIUpperFactor, higham22StageIIUpperLinear]

/-- The loop-derived `U_k` really is upper triangular. -/
theorem higham22_stageIIUpperFactor_upperTriangular
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (k : ℕ) :
    Matrix.BlockTriangular
      (higham22StageIIUpperFactor theta beta gamma alpha k) id := by
  intro i j hji
  change j < i at hji
  have hjiNat : (j : ℕ) < (i : ℕ) := hji
  rw [higham22StageIIUpperFactor, LinearMap.toMatrix'_apply]
  change higham22Algorithm22_2PrintedStageIIStep theta beta gamma
      (higham22FinExtend alpha) n k (higham22FinExtend (Pi.single j 1)) i = 0
  simp only [higham22Algorithm22_2PrintedStageIIStep]
  split_ifs with hiK hInterior hiLast hiN
  · have hk0 : k ≠ (j : ℕ) := by omega
    have hk1 : k + 1 ≠ (j : ℕ) := by omega
    have hk2 : k + 2 ≠ (j : ℕ) := by omega
    simp [higham22FinExtend_single, hk0, hk1, hk2]
  · have hi0 : (i : ℕ) ≠ (j : ℕ) := by omega
    have hi1 : (i : ℕ) + 1 ≠ (j : ℕ) := by omega
    have hi2 : (i : ℕ) + 2 ≠ (j : ℕ) := by omega
    simp [higham22FinExtend_single, Fin.ext_iff,
      hi0, hi1, hi2]
  · have hn1 : n - 1 ≠ (j : ℕ) := by omega
    have hn : n ≠ (j : ℕ) := by omega
    simp [higham22FinExtend_single, hn1, hn]
  · have hn : n ≠ (j : ℕ) := by omega
    simp [higham22FinExtend_single, hn]
  · have hi0 : (i : ℕ) ≠ (j : ℕ) := by omega
    simp [Fin.ext_iff, hi0]

/-- Finite Stage II.  At `steps = n` this applies
`U_0⋯U_{n-1}` in exactly the descending source-loop order. -/
noncomputable def higham22Algorithm22_2StageIIFin
    (theta beta gamma : ℕ → ℂ) {n : ℕ} (alpha : Fin (n + 1) → ℂ) :
    ℕ → (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)
  | 0, a => a
  | k + 1, a => higham22Algorithm22_2StageIIFin theta beta gamma alpha k
      (higham22StageIIUpperLinear theta beta gamma alpha k a)

/-- Tail vector reindexed so coordinate `k+r` becomes sparse coefficient `r`.
This exposes the shifted coefficient convention used by the printed Stage-II
loop. -/
noncomputable def higham22ShiftedCoefficients {n : ℕ} (k : ℕ)
    (a : Fin (n + 1) → ℂ) : ℕ →₀ ℂ := by
  classical
  exact Finsupp.onFinset (Finset.range (n + 1 - k))
    (fun r => higham22FinExtend a (k + r)) (by
      intro r hr
      simp only [Finset.mem_range]
      by_contra hnot
      have hout : ¬ k + r < n + 1 := by omega
      simp [higham22FinExtend, hout] at hr)

@[simp]
theorem higham22ShiftedCoefficients_apply {n : ℕ} (k r : ℕ)
    (a : Fin (n + 1) → ℂ) :
    higham22ShiftedCoefficients k a r = higham22FinExtend a (k + r) := by
  simp [higham22ShiftedCoefficients]

/-- One literal `U_k` sweep is exactly one sparse `(x-alpha_k)q+c_k`
coefficient update after reindexing the active tail. -/
theorem higham22_printedStageIIStep_shifted {n : ℕ}
    (theta beta gamma : ℕ → ℂ) (alpha a : Fin (n + 1) → ℂ)
    (k : ℕ) (hk : k ≤ n) :
    higham22ShiftedCoefficients k
        (fun i : Fin (n + 1) =>
          higham22Algorithm22_2PrintedStageIIStep theta beta gamma
            (higham22FinExtend alpha) n k (higham22FinExtend a) i) =
      Finsupp.single 0 (higham22FinExtend a k) +
        higham22BasisMultiply theta beta gamma (higham22FinExtend alpha k)
          (higham22ShiftedCoefficients (k + 1) a) := by
  classical
  ext r
  rw [higham22ShiftedCoefficients_apply]
  simp only [Finsupp.add_apply, Finsupp.single_apply]
  rw [higham22_basisMultiply_apply]
  simp only [higham22ShiftedCoefficients_apply]
  cases r with
  | zero =>
      have hklt : k < n + 1 := by omega
      simp only [Nat.add_zero, if_pos rfl, zero_add, Nat.zero_sub,
        Nat.add_sub_cancel]
      rw [higham22FinExtend_apply
        (fun i : Fin (n + 1) =>
          higham22Algorithm22_2PrintedStageIIStep theta beta gamma
            (higham22FinExtend alpha) n k (higham22FinExtend a) i)
        ⟨k, hklt⟩]
      simp [higham22Algorithm22_2PrintedStageIIStep]
      ring
  | succ r =>
      simp only [Nat.succ_ne_zero, if_false, Nat.zero_ne_add_one,
        Nat.add_sub_cancel, zero_add]
      by_cases hi : k + (r + 1) < n + 1
      · conv_lhs => rw [higham22FinExtend, dif_pos hi]
        change higham22Algorithm22_2PrintedStageIIStep theta beta gamma
            (higham22FinExtend alpha) n k (higham22FinExtend a) (k + (r + 1)) = _
        have hne : k + (r + 1) ≠ k := by omega
        simp only [higham22Algorithm22_2PrintedStageIIStep, if_neg hne]
        by_cases hinterior : k < k + (r + 1) ∧ k + (r + 1) + 2 ≤ n
        · rw [if_pos hinterior]
          have hj : k + (r + 1) - k = r + 1 := by omega
          have hi0 : k + 1 + r = k + (r + 1) := by omega
          have hi1 : k + 1 + (r + 1) = k + (r + 1) + 1 := by omega
          have hi2 : k + 1 + (r + 1 + 1) = k + (r + 1) + 2 := by omega
          rw [hj]
          simp only [Nat.add_sub_cancel]
          rw [hi0, hi1, hi2]
        · rw [if_neg hinterior]
          by_cases hlast : k + (r + 1) = n - 1
          · rw [if_pos hlast]
            have hr : r = n - k - 2 := by omega
            have hr1 : r + 1 = n - k - 1 := by omega
            have hbeta : n - k - 2 + 1 = n - k - 1 := by omega
            have hi0 : k + 1 + r = n - 1 := by omega
            have hi1 : k + 1 + (r + 1) = n := by omega
            have hout : ¬ k + 1 + (r + 1 + 1) < n + 1 := by omega
            have hzero : higham22FinExtend a (k + 1 + (r + 1 + 1)) = 0 := by
              simp [higham22FinExtend, hout]
            rw [hi0, hi1, hzero, hr, hbeta]
            ring
          · have hn : k + (r + 1) = n := by omega
            have hnlast : k + (r + 1) ≠ n - 1 := hlast
            rw [if_neg hnlast, if_pos hn]
            have hr : r = n - k - 1 := by omega
            have hi0 : k + 1 + r = n := by omega
            have hout1 : ¬ k + 1 + (r + 1) < n + 1 := by omega
            have hout2 : ¬ k + 1 + (r + 1 + 1) < n + 1 := by omega
            have hzero1 : higham22FinExtend a (k + 1 + (r + 1)) = 0 := by
              simp [higham22FinExtend, hout1]
            have hzero2 : higham22FinExtend a (k + 1 + (r + 1 + 1)) = 0 := by
              simp [higham22FinExtend, hout2]
            rw [hi0, hzero1, hzero2, hr]
            ring
      · conv_lhs => rw [higham22FinExtend, dif_neg hi]
        have hout0 : ¬ k + 1 + r < n + 1 := by omega
        have hout1 : ¬ k + 1 + (r + 1) < n + 1 := by omega
        have hout2 : ¬ k + 1 + (r + 1 + 1) < n + 1 := by omega
        have hzero0 : higham22FinExtend a (k + 1 + r) = 0 := by
          simp [higham22FinExtend, hout0]
        have hzero1 : higham22FinExtend a (k + 1 + (r + 1)) = 0 := by
          simp [higham22FinExtend, hout1]
        have hzero2 : higham22FinExtend a (k + 1 + (r + 1 + 1)) = 0 := by
          simp [higham22FinExtend, hout2]
        rw [hzero0, hzero1, hzero2]
        ring

/-- A finite Newton prefix wrapped around an arbitrary tail polynomial. -/
noncomputable def higham22NewtonPrefixTail (alpha c : ℕ → ℂ) :
    ℕ → ℕ → Polynomial ℂ → Polynomial ℂ
  | _start, 0, q => q
  | start, count + 1, q =>
      Polynomial.C (c start) +
        (Polynomial.X - Polynomial.C (alpha start)) *
          higham22NewtonPrefixTail alpha c (start + 1) count q

theorem higham22NewtonPrefixTail_append (alpha c : ℕ → ℂ)
    (start count : ℕ) (q : Polynomial ℂ) :
    higham22NewtonPrefixTail alpha c start (count + 1) q =
      higham22NewtonPrefixTail alpha c start count
        (Polynomial.C (c (start + count)) +
          (Polynomial.X - Polynomial.C (alpha (start + count))) * q) := by
  induction count generalizing start with
  | zero => simp [higham22NewtonPrefixTail]
  | succ count ih =>
      change Polynomial.C (c start) +
          (Polynomial.X - Polynomial.C (alpha start)) *
            higham22NewtonPrefixTail alpha c (start + 1) (count + 1) q =
        Polynomial.C (c start) +
          (Polynomial.X - Polynomial.C (alpha start)) *
            higham22NewtonPrefixTail alpha c (start + 1) count
              (Polynomial.C (c (start + (count + 1))) +
                (Polynomial.X - Polynomial.C (alpha (start + (count + 1)))) * q)
      rw [ih (start + 1)]
      have hindex : start + 1 + count = start + (count + 1) := by omega
      rw [hindex]

theorem higham22NewtonPrefixTail_congr_c
    (alpha c d : ℕ → ℂ) (start count : ℕ) (q : Polynomial ℂ)
    (hcd : ∀ r, r < count → c (start + r) = d (start + r)) :
    higham22NewtonPrefixTail alpha c start count q =
      higham22NewtonPrefixTail alpha d start count q := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
      simp only [higham22NewtonPrefixTail]
      have h0 : c start = d start := by
        simpa using hcd 0 (by omega)
      rw [h0]
      have htail : higham22NewtonPrefixTail alpha c (start + 1) count q =
          higham22NewtonPrefixTail alpha d (start + 1) count q := by
        apply ih (start := start + 1)
        intro r hr
        have hindex : start + 1 + r = start + (r + 1) := by omega
        rw [hindex]
        exact hcd (r + 1) (by omega)
      rw [htail]

theorem higham22_stageIIUpperLinear_of_lt {n : ℕ}
    (theta beta gamma : ℕ → ℂ) (alpha a : Fin (n + 1) → ℂ)
    (k : ℕ) (hk : k < n) (i : Fin (n + 1)) (hi : (i : ℕ) < k) :
    higham22StageIIUpperLinear theta beta gamma alpha k a i = a i := by
  have hik : (i : ℕ) ≠ k := by omega
  have hinterior : ¬(k < (i : ℕ) ∧ (i : ℕ) + 2 ≤ n) := by omega
  have hilast : (i : ℕ) ≠ n - 1 := by omega
  have hin : (i : ℕ) ≠ n := by omega
  simp [higham22StageIIUpperLinear,
    higham22Algorithm22_2PrintedStageIIStep, hik, hinterior, hilast, hin]

theorem higham22_stageIIUpperLinear_extend_of_lt {n : ℕ}
    (theta beta gamma : ℕ → ℂ) (alpha a : Fin (n + 1) → ℂ)
    (k r : ℕ) (hk : k < n) (hr : r < k) :
    higham22FinExtend (higham22StageIIUpperLinear theta beta gamma alpha k a) r =
      higham22FinExtend a r := by
  have hrN : r < n + 1 := by omega
  rw [show higham22FinExtend
      (higham22StageIIUpperLinear theta beta gamma alpha k a) r =
        higham22StageIIUpperLinear theta beta gamma alpha k a ⟨r, hrN⟩ by
      simp [higham22FinExtend, hrN]]
  rw [higham22_stageIIUpperLinear_of_lt theta beta gamma alpha a k hk ⟨r, hrN⟩ hr]
  simp [higham22FinExtend, hrN]

/-- Literal finite Stage-II loop invariant: the first `steps` Newton nodes
wrap the still-shifted tail polynomial. -/
theorem higham22_stageIIFin_polynomial_invariant
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (steps : ℕ) (hsteps : steps ≤ n) :
    higham22BasisSynthesis p
        (higham22ShiftedCoefficients 0
          (higham22Algorithm22_2StageIIFin theta beta gamma alpha steps a)) =
      higham22NewtonPrefixTail (higham22FinExtend alpha) (higham22FinExtend a)
        0 steps
        (higham22BasisSynthesis p (higham22ShiftedCoefficients steps a)) := by
  induction steps generalizing a with
  | zero => rfl
  | succ k ih =>
      rw [higham22Algorithm22_2StageIIFin]
      let b := higham22StageIIUpperLinear theta beta gamma alpha k a
      change higham22BasisSynthesis p
          (higham22ShiftedCoefficients 0
            (higham22Algorithm22_2StageIIFin theta beta gamma alpha k b)) = _
      rw [ih b (by omega)]
      have hk : k < n := by omega
      rw [higham22NewtonPrefixTail_congr_c
        (higham22FinExtend alpha) (higham22FinExtend b) (higham22FinExtend a)
        0 k (higham22BasisSynthesis p (higham22ShiftedCoefficients k b)) (by
          intro r hr
          simpa [b] using higham22_stageIIUpperLinear_extend_of_lt
            theta beta gamma alpha a k r hk (by omega))]
      have hshift : higham22ShiftedCoefficients k b =
          higham22StageIICoefficientStep theta beta gamma
            (higham22FinExtend alpha k) (higham22FinExtend a k)
            (higham22ShiftedCoefficients (k + 1) a) := by
        simpa [b, higham22StageIIUpperLinear,
          higham22StageIICoefficientStep] using
          higham22_printedStageIIStep_shifted theta beta gamma alpha a k
            (by omega)
      rw [hshift, higham22_stageIICoefficientStep_correct hp htheta]
      rw [higham22NewtonPrefixTail_append]
      apply congrArg
        (higham22NewtonPrefixTail
          (higham22FinExtend alpha) (higham22FinExtend a) 0 k)
      simp only [Nat.zero_add]
      ring

theorem higham22ShiftedCoefficients_last {n : ℕ}
    (a : Fin (n + 1) → ℂ) :
    higham22ShiftedCoefficients n a = Finsupp.single 0 (higham22FinExtend a n) := by
  classical
  ext r
  cases r with
  | zero => simp
  | succ r =>
      have hout : ¬ n + (r + 1) < n + 1 := by omega
      simp [higham22ShiftedCoefficients_apply, higham22FinExtend, hout]

theorem higham22NewtonPrefixTail_eq_nest (alpha c : ℕ → ℂ)
    (start count : ℕ) :
    higham22NewtonPrefixTail alpha c start count
        (Polynomial.C (c (start + count))) =
      higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin (count + 1) =>
          (alpha (start + i), c (start + i))) := by
  induction count generalizing start with
  | zero => simp [higham22NewtonPrefixTail, higham22NewtonPolynomialNest]
  | succ count ih =>
      rw [List.ofFn_succ]
      simp only [higham22NewtonPrefixTail, higham22NewtonPolynomialNest]
      have htail : start + (count + 1) = start + 1 + count := by omega
      rw [htail]
      rw [ih (start + 1)]
      simp only [Fin.val_zero, Nat.add_zero]
      have hfun :
          (fun i : Fin (count + 1) =>
            (alpha (start + 1 + i), c (start + 1 + i))) =
          (fun i : Fin (count + 1) =>
            (alpha (start + i.succ), c (start + i.succ))) := by
        funext i
        congr 2 <;> simp <;> omega
      rw [hfun]

/-- The literal finite Stage-II loop synthesizes to the nested Newton
polynomial; this is the direct bridge from the printed loop to (22.10)--(22.14). -/
theorem higham22_algorithm22_2StageIIFin_polynomial_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha c : Fin (n + 1) → ℂ) :
    higham22BasisSynthesis p
        (higham22ShiftedCoefficients 0
          (higham22Algorithm22_2StageIIFin theta beta gamma alpha n c)) =
      higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin (n + 1) => (alpha i, c i)) := by
  rw [higham22_stageIIFin_polynomial_invariant hp htheta alpha c n (by omega)]
  rw [higham22ShiftedCoefficients_last]
  simp only [higham22BasisSynthesis, Finsupp.lsum_single,
    LinearMap.toSpanSingleton_apply, hp.1,
    Polynomial.smul_eq_C_mul, mul_one]
  have hnest := higham22NewtonPrefixTail_eq_nest
    (higham22FinExtend alpha) (higham22FinExtend c) 0 n
  simp only [Nat.zero_add] at hnest
  rw [hnest]
  congr 2
  funext i
  simp

theorem higham22ShiftedCoefficients_zero_eq_sum {n : ℕ}
    (a : Fin (n + 1) → ℂ) :
    higham22ShiftedCoefficients 0 a =
      ∑ i : Fin (n + 1), Finsupp.single (i : ℕ) (a i) := by
  classical
  ext r
  by_cases hr : r < n + 1
  · let i : Fin (n + 1) := ⟨r, hr⟩
    rw [Finsupp.finset_sum_apply]
    rw [Finset.sum_eq_single i]
    · simp [higham22ShiftedCoefficients_apply, higham22FinExtend, hr, i]
    · intro j _hju hji
      have hne : (j : ℕ) ≠ r := by
        intro h
        apply hji
        exact Fin.ext h
      simp [Finsupp.single_apply, hne]
    · simp
  · rw [Finsupp.finset_sum_apply]
    have hleft : higham22ShiftedCoefficients 0 a r = 0 := by
      simp [higham22ShiftedCoefficients_apply, higham22FinExtend, hr]
    rw [hleft]
    symm
    apply Finset.sum_eq_zero
    intro i _hi
    have hne : (i : ℕ) ≠ r := by omega
    simp [Finsupp.single_apply, hne]

theorem higham22_basisSynthesis_shifted_zero {n : ℕ}
    (p : ℕ → Polynomial ℂ) (a : Fin (n + 1) → ℂ) :
    higham22BasisSynthesis p (higham22ShiftedCoefficients 0 a) =
      higham22BasisExpansion (fun i : Fin (n + 1) => p i) a := by
  rw [higham22ShiftedCoefficients_zero_eq_sum]
  simp [higham22BasisSynthesis, higham22BasisExpansion,
    Polynomial.smul_eq_C_mul]

/-- Source-facing literal Stage-II correctness in the finite recurrence basis. -/
theorem higham22_algorithm22_2StageIIFin_correct
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha c : Fin (n + 1) → ℂ) :
    higham22BasisExpansion (fun i : Fin (n + 1) => p i)
        (higham22Algorithm22_2StageIIFin theta beta gamma alpha n c) =
      higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin (n + 1) => (alpha i, c i)) := by
  rw [← higham22_basisSynthesis_shifted_zero]
  exact higham22_algorithm22_2StageIIFin_polynomial_correct hp htheta alpha c

/-- Product `U_0⋯U_{s-1}` of the factors produced from Stage II. -/
noncomputable def higham22StageIIUpperProduct
    (theta beta gamma : ℕ → ℂ) {n : ℕ} (alpha : Fin (n + 1) → ℂ) :
    ℕ → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0 => 1
  | k + 1 => higham22StageIIUpperProduct theta beta gamma alpha k *
      higham22StageIIUpperFactor theta beta gamma alpha k

/-- The finite Stage-II product computes the actual Stage-II loop. -/
theorem higham22_stageIIUpperProduct_mulVec
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (steps : ℕ) :
    (higham22StageIIUpperProduct theta beta gamma alpha steps).mulVec a =
      higham22Algorithm22_2StageIIFin theta beta gamma alpha steps a := by
  induction steps generalizing a with
  | zero => simp [higham22StageIIUpperProduct, higham22Algorithm22_2StageIIFin]
  | succ k ih =>
      rw [higham22StageIIUpperProduct,
        ← Matrix.mulVec_mulVec a
          (higham22StageIIUpperProduct theta beta gamma alpha k)
          (higham22StageIIUpperFactor theta beta gamma alpha k),
        higham22_stageIIUpperFactor_mulVec, ih]
      rfl

/-- The actual printed two-stage dual Algorithm 22.2. -/
noncomputable def higham22Algorithm22_2Printed
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  let c := higham22Algorithm22_2StageIFin alpha f n
  higham22Algorithm22_2StageIIFin theta beta gamma alpha n c

/-- The complete literal Algorithm 22.2 path synthesizes to the Newton nest
whose coefficients are produced by its actual Stage-I loop. -/
theorem higham22_algorithm22_2Printed_newton_invariant
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    higham22BasisExpansion (fun i : Fin (n + 1) => p i)
        (higham22Algorithm22_2Printed theta beta gamma alpha f) =
      higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin (n + 1) =>
          (alpha i, higham22Algorithm22_2StageIFin alpha f n i)) := by
  unfold higham22Algorithm22_2Printed
  exact higham22_algorithm22_2StageIIFin_correct hp htheta alpha _

/-- The finite product in equation (22.17), produced from the two actual
loop graphs.  No inverse or target factorization is assumed here. -/
noncomputable def higham22Algorithm22_2FactorProduct
    (theta beta gamma : ℕ → ℂ) {n : ℕ} (alpha : Fin (n + 1) → ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  higham22StageIIUpperProduct theta beta gamma alpha n *
    higham22StageILowerProduct alpha n

/-- Higham (22.22): for four nodes (`n = 3`), the generic factor product
    specializes to the six displayed factors `U₀ U₁ U₂ L₂ L₁ L₀`.
    The entries of these factors are the definitions immediately preceding
    (22.17), so this theorem is the source-label bridge for the displayed
    four-by-four example rather than a second factorization assumption. -/
theorem higham22_eq22_22_four_node_six_factor
    (theta beta gamma : ℕ → ℂ) (alpha : Fin 4 → ℂ) :
    higham22Algorithm22_2FactorProduct theta beta gamma alpha =
      ((higham22StageIIUpperFactor theta beta gamma alpha 0 *
          higham22StageIIUpperFactor theta beta gamma alpha 1) *
          higham22StageIIUpperFactor theta beta gamma alpha 2) *
        (higham22StageILowerFactor alpha 2 *
          (higham22StageILowerFactor alpha 1 *
            higham22StageILowerFactor alpha 0)) := by
  simp [higham22Algorithm22_2FactorProduct,
    higham22StageIIUpperProduct, higham22StageILowerProduct]

/-- Algorithmic half of equation (22.17): the loop-derived finite product
acts exactly as the implemented Algorithm 22.2. -/
theorem higham22_eq22_17_algorithm_product
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    (higham22Algorithm22_2FactorProduct theta beta gamma alpha).mulVec f =
      higham22Algorithm22_2Printed theta beta gamma alpha f := by
  rw [higham22Algorithm22_2FactorProduct,
    ← Matrix.mulVec_mulVec f
      (higham22StageIIUpperProduct theta beta gamma alpha n)
      (higham22StageILowerProduct alpha n),
    higham22_stageILowerProduct_mulVec,
    higham22_stageIIUpperProduct_mulVec]
  rfl

/-! ### Hermite interpolation and the inverse half of equation (22.17)

The lemmas below derive repeated-node interpolation from monic polynomial
quotients, the actual Stage-I table, and the literal Stage-II synthesis.
No inverse or interpolation conclusion is assumed as a premise. -/

noncomputable def higham22HermiteWindowQuotient (alpha : ℕ → ℂ) (start : ℕ)
    (q : Polynomial ℂ) : ℕ → Polynomial ℂ
  | 0 => q
  | k + 1 => higham22HermiteWindowQuotient alpha start q k /ₘ
      (Polynomial.X - Polynomial.C (alpha (start + k)))

noncomputable def higham22HermiteWindowDD (alpha : ℕ → ℂ) (q : Polynomial ℂ)
    (start k : ℕ) : ℂ :=
  (higham22HermiteWindowQuotient alpha start q k).eval (alpha (start + k))

theorem higham22Hermite_reconstruct_divByMonic (q : Polynomial ℂ) (a : ℂ) :
    q = Polynomial.C (q.eval a) +
      (Polynomial.X - Polynomial.C a) *
        (q /ₘ (Polynomial.X - Polynomial.C a)) := by
  rw [Polynomial.X_sub_C_mul_divByMonic_eq_sub_modByMonic]
  rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
  ring

theorem higham22Hermite_hasseDeriv_divByMonic_eval (q : Polynomial ℂ) (a : ℂ) (k : ℕ) :
    (Polynomial.hasseDeriv k
        (q /ₘ (Polynomial.X - Polynomial.C a))).eval a =
      (Polynomial.hasseDeriv (k + 1) q).eval a := by
  rw [← Polynomial.taylor_coeff, ← Polynomial.taylor_coeff]
  nth_rewrite 2 [higham22Hermite_reconstruct_divByMonic q a]
  rw [map_add, Polynomial.taylor_mul]
  simp [Polynomial.taylor_X, Polynomial.taylor_C,
    Polynomial.coeff_add, Polynomial.coeff_X_mul]

theorem higham22Hermite_repeated_windowQuotient_hasse
    (alpha : ℕ → ℂ) (q : Polynomial ℂ) (start k : ℕ)
    (hrepeat : ∀ r, r < k → alpha (start + r) = alpha (start + k)) :
    ∀ m,
      (Polynomial.hasseDeriv m (higham22HermiteWindowQuotient alpha start q k)).eval
          (alpha (start + k)) =
        (Polynomial.hasseDeriv (m + k) q).eval (alpha (start + k)) := by
  induction k with
  | zero => simp [higham22HermiteWindowQuotient]
  | succ k ih =>
      have hprefix : ∀ r, r < k → alpha (start + r) = alpha (start + k) := by
        intro r hr
        exact (hrepeat r (by omega)).trans (hrepeat k (by omega)).symm
      have hlast : alpha (start + k) = alpha (start + (k + 1)) :=
        hrepeat k (by omega)
      intro m
      simp only [higham22HermiteWindowQuotient]
      rw [hlast]
      rw [higham22Hermite_hasseDeriv_divByMonic_eval]
      rw [← hlast]
      rw [ih hprefix (m + 1)]
      have hindex : m + 1 + k = m + (k + 1) := by omega
      rw [hindex]

theorem higham22Hermite_repeated_windowDD_eq_hasse
    (alpha : ℕ → ℂ) (q : Polynomial ℂ) (start k : ℕ)
    (hrepeat : ∀ r, r < k → alpha (start + r) = alpha (start + k)) :
    higham22HermiteWindowDD alpha q start k =
      (Polynomial.hasseDeriv k q).eval (alpha (start + k)) := by
  simpa [higham22HermiteWindowDD] using
    higham22Hermite_repeated_windowQuotient_hasse alpha q start k hrepeat 0

noncomputable def higham22HermiteNodeOrder (alpha : ℕ → ℂ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => if alpha (j + 1) = alpha j then higham22HermiteNodeOrder alpha j + 1 else 0

theorem higham22HermiteNodeOrder_le (alpha : ℕ → ℂ) (j : ℕ) :
    higham22HermiteNodeOrder alpha j ≤ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [higham22HermiteNodeOrder]
      split_ifs <;> omega

theorem higham22HermiteNodeOrder_recent_equal (alpha : ℕ → ℂ) {j r : ℕ}
    (hr : r < higham22HermiteNodeOrder alpha j) :
    alpha (j - r - 1) = alpha j := by
  induction j generalizing r with
  | zero => simp [higham22HermiteNodeOrder] at hr
  | succ j ih =>
      simp only [higham22HermiteNodeOrder] at hr
      by_cases hnode : alpha (j + 1) = alpha j
      · rw [if_pos hnode] at hr
        cases r with
        | zero => simpa using hnode.symm
        | succ r =>
            have hr' : r < higham22HermiteNodeOrder alpha j := by omega
            have hindex : j + 1 - (r + 1) - 1 = j - r - 1 := by omega
            rw [hindex, ih hr']
            exact hnode.symm
      · rw [if_neg hnode] at hr
        omega

theorem higham22HermiteNodeOrder_boundary_ne (alpha : ℕ → ℂ) {j : ℕ}
    (hj : higham22HermiteNodeOrder alpha j < j) :
    alpha j ≠ alpha (j - higham22HermiteNodeOrder alpha j - 1) := by
  induction j with
  | zero => omega
  | succ j ih =>
      simp only [higham22HermiteNodeOrder] at hj ⊢
      by_cases hnode : alpha (j + 1) = alpha j
      · rw [if_pos hnode] at hj ⊢
        have hj' : higham22HermiteNodeOrder alpha j < j := by omega
        have hb := ih hj'
        have hindex : j + 1 - (higham22HermiteNodeOrder alpha j + 1) - 1 =
            j - higham22HermiteNodeOrder alpha j - 1 := by omega
        rw [hindex]
        intro h
        exact hb (hnode.symm.trans h)
      · rw [if_neg hnode] at hj ⊢
        simpa using hnode

theorem higham22HermiteNodeOrder_ne_of_le
    (alpha : ℕ → ℂ) (hcontig : Higham22ContiguousNodesNat alpha)
    {j k : ℕ} (horder : higham22HermiteNodeOrder alpha j ≤ k) (hkj : k < j) :
    alpha j ≠ alpha (j - k - 1) := by
  intro hEq
  have horderj : higham22HermiteNodeOrder alpha j < j := horder.trans_lt hkj
  have hboundary := higham22HermiteNodeOrder_boundary_ne alpha horderj
  have hleft : j - k - 1 < j := by omega
  have hblock := hcontig (j - k - 1) j hleft hEq.symm
    (j - higham22HermiteNodeOrder alpha j - 1) (by omega) (by omega)
  exact hboundary (hEq.trans hblock.symm)

theorem higham22HermiteNodeOrder_lt_of_equal
    (alpha : ℕ → ℂ) (hcontig : Higham22ContiguousNodesNat alpha)
    {j k : ℕ} (hkj : k < j) (hEq : alpha j = alpha (j - k - 1)) :
    k < higham22HermiteNodeOrder alpha j := by
  by_contra h
  exact higham22HermiteNodeOrder_ne_of_le alpha hcontig (Nat.le_of_not_gt h) hkj hEq

theorem higham22HermiteNodeOrder_ne_of_le_on
    (alpha : ℕ → ℂ) (N : ℕ) (hcontig : Higham22ContiguousNodesNatOn alpha N)
    {j k : ℕ} (hjN : j < N) (horder : higham22HermiteNodeOrder alpha j ≤ k) (hkj : k < j) :
    alpha j ≠ alpha (j - k - 1) := by
  intro hEq
  have horderj : higham22HermiteNodeOrder alpha j < j := horder.trans_lt hkj
  have hboundary := higham22HermiteNodeOrder_boundary_ne alpha horderj
  have hleft : j - k - 1 < j := by omega
  have hblock := hcontig (j - k - 1) j hleft hjN hEq.symm
    (j - higham22HermiteNodeOrder alpha j - 1) (by omega) (by omega)
  exact hboundary (hEq.trans hblock.symm)

theorem higham22HermiteNodeOrder_lt_of_equal_on
    (alpha : ℕ → ℂ) (N : ℕ) (hcontig : Higham22ContiguousNodesNatOn alpha N)
    {j k : ℕ} (hjN : j < N) (hkj : k < j)
    (hEq : alpha j = alpha (j - k - 1)) :
    k < higham22HermiteNodeOrder alpha j := by
  by_contra h
  exact higham22HermiteNodeOrder_ne_of_le_on alpha N hcontig hjN
    (Nat.le_of_not_gt h) hkj hEq

theorem higham22HermiteNodeOrder_le_of_ne (alpha : ℕ → ℂ) {j k : ℕ}
    (hkj : k < j) (hne : alpha j ≠ alpha (j - k - 1)) :
    higham22HermiteNodeOrder alpha j ≤ k := by
  by_contra h
  have heq := higham22HermiteNodeOrder_recent_equal alpha
    (j := j) (r := k) (Nat.lt_of_not_ge h)
  exact hne heq.symm

def Higham22HermiteData (alpha f : ℕ → ℂ) (q : Polynomial ℂ) : Prop :=
  ∀ j, f j = ((Polynomial.derivative^[higham22HermiteNodeOrder alpha j]) q).eval (alpha j)

def Higham22HermiteDataOn (alpha f : ℕ → ℂ) (q : Polynomial ℂ) (N : ℕ) : Prop :=
  ∀ j, j < N →
    f j = ((Polynomial.derivative^[higham22HermiteNodeOrder alpha j]) q).eval (alpha j)

theorem higham22Hermite_hermiteData_div_factorial
    {alpha f : ℕ → ℂ} {q : Polynomial ℂ}
    (hdata : Higham22HermiteData alpha f q) (j : ℕ) :
    f j / (Nat.factorial (higham22HermiteNodeOrder alpha j) : ℂ) =
      (Polynomial.hasseDeriv (higham22HermiteNodeOrder alpha j) q).eval (alpha j) := by
  rw [hdata]
  have hfun := Polynomial.factorial_smul_hasseDeriv
    (R := ℂ) (k := higham22HermiteNodeOrder alpha j)
  have hpoly := congrFun hfun q
  have heval := congrArg (Polynomial.eval (alpha j)) hpoly
  simp only [nsmul_eq_mul, Polynomial.eval_smul,
    smul_eq_mul] at heval
  have hfac : (Nat.factorial (higham22HermiteNodeOrder alpha j) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (higham22HermiteNodeOrder alpha j)
  apply (div_eq_iff hfac).2
  simpa [mul_comm] using heval.symm

theorem higham22Hermite_hermiteDataOn_div_factorial
    {alpha f : ℕ → ℂ} {q : Polynomial ℂ} {N : ℕ}
    (hdata : Higham22HermiteDataOn alpha f q N) {j : ℕ} (hjN : j < N) :
    f j / (Nat.factorial (higham22HermiteNodeOrder alpha j) : ℂ) =
      (Polynomial.hasseDeriv (higham22HermiteNodeOrder alpha j) q).eval (alpha j) := by
  rw [hdata j hjN]
  have hfun := Polynomial.factorial_smul_hasseDeriv
    (R := ℂ) (k := higham22HermiteNodeOrder alpha j)
  have hpoly := congrFun hfun q
  have heval := congrArg (Polynomial.eval (alpha j)) hpoly
  simp only [nsmul_eq_mul, Polynomial.eval_smul, smul_eq_mul] at heval
  have hfac : (Nat.factorial (higham22HermiteNodeOrder alpha j) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (higham22HermiteNodeOrder alpha j)
  apply (div_eq_iff hfac).2
  simpa [mul_comm] using heval.symm

theorem higham22Hermite_divByMonic_mul
    (p q r : Polynomial ℂ) (hq : q.Monic) (hr : r.Monic) :
    (p /ₘ q) /ₘ r = p /ₘ (q * r) := by
  let a := p /ₘ q
  let rq := p %ₘ q
  let b := a /ₘ r
  let rr := a %ₘ r
  let remainder := rq + q * rr
  have hpq : rq + q * a = p := by
    exact Polynomial.modByMonic_add_div p q
  have har : rr + r * b = a := by
    exact Polynomial.modByMonic_add_div a r
  have hreconstruct : remainder + (q * r) * b = p := by
    dsimp [remainder]
    rw [← hpq]
    rw [← har]
    ring
  have hrq : rq.degree < q.degree :=
    Polynomial.degree_modByMonic_lt p hq
  have hrr : rr.degree < r.degree :=
    Polynomial.degree_modByMonic_lt a hr
  have hqne : q.degree ≠ ⊥ := Polynomial.degree_ne_bot.mpr hq.ne_zero
  have hqrr : (q * rr).degree < (q * r).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_mul]
    exact WithBot.add_lt_add_left hqne hrr
  have hqle : q.degree ≤ (q * r).degree := by
    rw [Polynomial.degree_mul, Polynomial.degree_eq_natDegree hq.ne_zero,
      Polynomial.degree_eq_natDegree hr.ne_zero]
    exact_mod_cast Nat.le_add_right q.natDegree r.natDegree
  have hremainder : remainder.degree < (q * r).degree := by
    exact (Polynomial.degree_add_le rq (q * rr)).trans_lt
      (max_lt (hrq.trans_le hqle) hqrr)
  exact (Polynomial.div_modByMonic_unique b remainder (hq.mul hr)
    ⟨hreconstruct, hremainder⟩).1.symm

theorem higham22Hermite_divLinear_eval_of_ne (q : Polynomial ℂ) (a b : ℂ) (hba : b ≠ a) :
    (q /ₘ (Polynomial.X - Polynomial.C a)).eval b =
      (q.eval b - q.eval a) / (b - a) := by
  have h := congrArg (Polynomial.eval b) (higham22Hermite_reconstruct_divByMonic q a)
  simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_sub, Polynomial.eval_X] at h
  apply (eq_div_iff (sub_ne_zero.mpr hba)).2
  rw [h]
  ring

theorem higham22Hermite_divLinear_eval_symm (q : Polynomial ℂ) (a b : ℂ) :
    (q /ₘ (Polynomial.X - Polynomial.C a)).eval b =
      (q /ₘ (Polynomial.X - Polynomial.C b)).eval a := by
  by_cases hab : a = b
  · subst b
    rfl
  rw [higham22Hermite_divLinear_eval_of_ne q a b (Ne.symm hab),
    higham22Hermite_divLinear_eval_of_ne q b a hab]
  have hneg : a - b = -(b - a) := by ring
  rw [hneg, div_neg]
  ring

theorem higham22Hermite_divLinear_comm (q : Polynomial ℂ) (a b : ℂ) :
    (q /ₘ (Polynomial.X - Polynomial.C a)) /ₘ
          (Polynomial.X - Polynomial.C b) =
      (q /ₘ (Polynomial.X - Polynomial.C b)) /ₘ
          (Polynomial.X - Polynomial.C a) := by
  rw [higham22Hermite_divByMonic_mul q _ _ (Polynomial.monic_X_sub_C a)
      (Polynomial.monic_X_sub_C b),
    higham22Hermite_divByMonic_mul q _ _ (Polynomial.monic_X_sub_C b)
      (Polynomial.monic_X_sub_C a), mul_comm]

noncomputable def higham22HermiteListDD (q : Polynomial ℂ) : List ℂ → ℂ
  | [] => 0
  | [a] => q.eval a
  | a :: b :: rest =>
      higham22HermiteListDD (q /ₘ (Polynomial.X - Polynomial.C a)) (b :: rest)

theorem higham22HermiteListDD_perm (q : Polynomial ℂ) {xs ys : List ℂ}
    (hperm : xs.Perm ys) : higham22HermiteListDD q xs = higham22HermiteListDD q ys := by
  induction hperm generalizing q with
  | nil => rfl
  | @cons a xs ys hperm ih =>
      cases xs with
      | nil =>
          rw [← List.Perm.nil_eq hperm]
      | cons b rest =>
          cases ys with
          | nil => simp at hperm
          | cons c rest' =>
              simp only [higham22HermiteListDD]
              exact ih _
  | @swap a b xs =>
      cases xs with
      | nil =>
          simp only [higham22HermiteListDD]
          exact higham22Hermite_divLinear_eval_symm q b a
      | cons c rest =>
          simp only [higham22HermiteListDD]
          rw [higham22Hermite_divLinear_comm]
  | trans hxy hyz ihxy ihyz => exact (ihxy q).trans (ihyz q)

noncomputable def higham22HermiteListQuotient (q : Polynomial ℂ) : List ℂ → Polynomial ℂ
  | [] => q
  | a :: rest =>
      higham22HermiteListQuotient (q /ₘ (Polynomial.X - Polynomial.C a)) rest

theorem higham22HermiteListQuotient_append (q : Polynomial ℂ) (xs ys : List ℂ) :
    higham22HermiteListQuotient q (xs ++ ys) =
      higham22HermiteListQuotient (higham22HermiteListQuotient q xs) ys := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.cons_append, higham22HermiteListQuotient]
      exact ih _

theorem higham22HermiteListDD_append_singleton (q : Polynomial ℂ) (xs : List ℂ) (a : ℂ) :
    higham22HermiteListDD q (xs ++ [a]) = (higham22HermiteListQuotient q xs).eval a := by
  induction xs generalizing q with
  | nil => rfl
  | cons b xs ih =>
      simp only [List.cons_append]
      cases xs with
      | nil => rfl
      | cons c rest =>
          simp only [higham22HermiteListDD, higham22HermiteListQuotient]
          exact ih _

theorem higham22HermiteListDD_cons_of_ne_nil (q : Polynomial ℂ) (a : ℂ)
    {xs : List ℂ} (hxs : xs ≠ []) :
    higham22HermiteListDD q (a :: xs) =
      higham22HermiteListDD (q /ₘ (Polynomial.X - Polynomial.C a)) xs := by
  cases xs with
  | nil => exact (hxs rfl).elim
  | cons b rest => rfl

theorem higham22HermiteListQuotient_divLinear_comm (q : Polynomial ℂ)
    (a : ℂ) (xs : List ℂ) :
    higham22HermiteListQuotient (q /ₘ (Polynomial.X - Polynomial.C a)) xs =
      higham22HermiteListQuotient q xs /ₘ (Polynomial.X - Polynomial.C a) := by
  induction xs generalizing q with
  | nil => rfl
  | cons b xs ih =>
      simp only [higham22HermiteListQuotient]
      rw [higham22Hermite_divLinear_comm q a b]
      exact ih _

theorem higham22HermiteListDD_first_last_recurrence (q : Polynomial ℂ)
    (a b : ℂ) (middle : List ℂ) (hba : b ≠ a) :
    higham22HermiteListDD q (a :: (middle ++ [b])) =
      (higham22HermiteListDD q (middle ++ [b]) - higham22HermiteListDD q (a :: middle)) /
        (b - a) := by
  rw [higham22HermiteListDD_cons_of_ne_nil q a (by simp),
    higham22HermiteListDD_append_singleton, higham22HermiteListQuotient_divLinear_comm,
    higham22Hermite_divLinear_eval_of_ne _ a b hba,
    ← higham22HermiteListDD_append_singleton q middle b,
    ← higham22HermiteListDD_append_singleton q middle a]
  congr 2
  apply higham22HermiteListDD_perm q
  simpa using (List.perm_middle (l₁ := middle) (l₂ := []) (a := a))

def higham22HermiteWindowNodes (alpha : ℕ → ℂ) (start k : ℕ) : List ℂ :=
  (List.range k).map fun r => alpha (start + r)

theorem higham22HermiteWindowNodes_succ (alpha : ℕ → ℂ) (start k : ℕ) :
    higham22HermiteWindowNodes alpha start (k + 1) =
      higham22HermiteWindowNodes alpha start k ++ [alpha (start + k)] := by
  simp [higham22HermiteWindowNodes, List.range_succ]

theorem higham22HermiteWindowNodes_cons (alpha : ℕ → ℂ) (start k : ℕ) :
    higham22HermiteWindowNodes alpha start (k + 1) =
      alpha start :: higham22HermiteWindowNodes alpha (start + 1) k := by
  rw [higham22HermiteWindowNodes, higham22HermiteWindowNodes, List.range_succ_eq_map,
    List.map_cons, List.map_map]
  congr 2
  funext r
  apply congrArg alpha
  omega

theorem higham22HermiteWindowQuotient_eq_list (alpha : ℕ → ℂ) (q : Polynomial ℂ)
    (start k : ℕ) :
    higham22HermiteWindowQuotient alpha start q k =
      higham22HermiteListQuotient q (higham22HermiteWindowNodes alpha start k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [higham22HermiteWindowNodes_succ, higham22HermiteListQuotient_append,
        higham22HermiteWindowQuotient, ih]
      rfl

theorem higham22HermiteWindowDD_eq_list (alpha : ℕ → ℂ) (q : Polynomial ℂ)
    (start k : ℕ) :
    higham22HermiteWindowDD alpha q start k =
      higham22HermiteListDD q (higham22HermiteWindowNodes alpha start (k + 1)) := by
  rw [higham22HermiteWindowNodes_succ, higham22HermiteListDD_append_singleton,
    ← higham22HermiteWindowQuotient_eq_list]
  rfl

theorem higham22HermiteWindowDD_first_last_recurrence (alpha : ℕ → ℂ)
    (q : Polynomial ℂ) (start k : ℕ)
    (hne : alpha (start + k + 1) ≠ alpha start) :
    higham22HermiteWindowDD alpha q start (k + 1) =
      (higham22HermiteWindowDD alpha q (start + 1) k -
          higham22HermiteWindowDD alpha q start k) /
        (alpha (start + k + 1) - alpha start) := by
  have htail : higham22HermiteWindowNodes alpha (start + 1) (k + 1) =
      higham22HermiteWindowNodes alpha (start + 1) k ++ [alpha (start + k + 1)] := by
    rw [higham22HermiteWindowNodes_succ]
    congr 3
    omega
  have hhead : higham22HermiteWindowNodes alpha start (k + 1) =
      alpha start :: higham22HermiteWindowNodes alpha (start + 1) k :=
    higham22HermiteWindowNodes_cons alpha start k
  have hfull : higham22HermiteWindowNodes alpha start ((k + 1) + 1) =
      alpha start ::
        (higham22HermiteWindowNodes alpha (start + 1) k ++ [alpha (start + k + 1)]) := by
    rw [higham22HermiteWindowNodes_cons, htail]
  rw [higham22HermiteWindowDD_eq_list, higham22HermiteWindowDD_eq_list,
    higham22HermiteWindowDD_eq_list, hfull, htail, hhead]
  exact higham22HermiteListDD_first_last_recurrence q _ _ _ hne

theorem higham22HermiteWindowDD_slide_of_block_equal (alpha : ℕ → ℂ)
    (q : Polynomial ℂ) (start k : ℕ)
    (hblock : ∀ m, start ≤ m → m ≤ start + k + 1 →
      alpha m = alpha start) :
    higham22HermiteWindowDD alpha q start k =
      higham22HermiteWindowDD alpha q (start + 1) k := by
  have hrepeat0 : ∀ r, r < k →
      alpha (start + r) = alpha (start + k) := by
    intro r hr
    rw [hblock (start + r) (by omega) (by omega),
      hblock (start + k) (by omega) (by omega)]
  have hrepeat1 : ∀ r, r < k →
      alpha (start + 1 + r) = alpha (start + 1 + k) := by
    intro r hr
    rw [hblock (start + 1 + r) (by omega) (by omega),
      hblock (start + 1 + k) (by omega) (by omega)]
  rw [higham22Hermite_repeated_windowDD_eq_hasse alpha q start k hrepeat0,
    higham22Hermite_repeated_windowDD_eq_hasse alpha q (start + 1) k hrepeat1,
    hblock (start + k) (by omega) (by omega),
    hblock (start + 1 + k) (by omega) (by omega)]

theorem higham22Hermite_confluentTable_eq_windowDD
    (alpha f : ℕ → ℂ) (q : Polynomial ℂ)
    (N : ℕ) (hcontig : Higham22ContiguousNodesNatOn alpha N)
    (hdata : Higham22HermiteDataOn alpha f q N) :
    ∀ k j, j < N → k ≤ j → higham22HermiteNodeOrder alpha j ≤ k →
      higham22ConfluentDividedDifferenceTable alpha f k j =
        higham22HermiteWindowDD alpha q (j - k) k := by
  intro k
  induction k with
  | zero =>
      intro j _hjN _hkj horder
      have horder0 : higham22HermiteNodeOrder alpha j = 0 :=
        Nat.eq_zero_of_le_zero horder
      rw [higham22ConfluentDividedDifferenceTable, hdata j _hjN, horder0]
      simp [higham22HermiteWindowDD, higham22HermiteWindowQuotient]
  | succ k ih =>
      have hsaved : ∀ t, k ≤ t →
          t < N →
          higham22ConfluentDividedDifferenceTable alpha f k
              (higham22StageILastSaved alpha k t) =
            higham22HermiteWindowDD alpha q (t - k) k := by
        intro t hkt htN
        induction t, hkt using Nat.le_induction with
        | base =>
            rw [higham22StageILastSaved_eq_k_of_le alpha k k le_rfl]
            simpa using ih k htN le_rfl (higham22HermiteNodeOrder_le alpha k)
        | succ t hkt hsaved =>
            simp only [higham22StageILastSaved]
            rw [if_neg (by omega : ¬t + 1 ≤ k)]
            by_cases heq : alpha (t + 1) = alpha (t + 1 - k - 1)
            · rw [if_pos heq, hsaved (by omega)]
              have heq' : alpha (t - k) = alpha (t + 1) := by
                have hindex : t + 1 - k - 1 = t - k := by omega
                rw [hindex] at heq
                exact heq.symm
              have hblock : ∀ m, t - k ≤ m → m ≤ t - k + k + 1 →
                  alpha m = alpha (t - k) := by
                intro m hmleft hmright
                exact hcontig (t - k) (t + 1) (by omega) htN heq' m hmleft
                  (by omega)
              have hshift : t - k + 1 = t + 1 - k := by omega
              rw [← hshift]
              exact higham22HermiteWindowDD_slide_of_block_equal alpha q (t - k) k hblock
            · rw [if_neg heq]
              exact ih (t + 1) htN (by omega)
                (higham22HermiteNodeOrder_le_of_ne alpha (by omega) heq)
      intro j hjN hkj horder
      rw [higham22ConfluentDividedDifferenceTable]
      rw [if_neg (by omega : ¬j ≤ k)]
      by_cases heq : alpha j = alpha (j - k - 1)
      · rw [if_pos heq]
        have hordergt : k < higham22HermiteNodeOrder alpha j :=
          higham22HermiteNodeOrder_lt_of_equal_on alpha N hcontig hjN (by omega) heq
        have hordereq : higham22HermiteNodeOrder alpha j = k + 1 := by omega
        have hfac := higham22Hermite_hermiteDataOn_div_factorial hdata hjN
        have hrepeat : ∀ r, r < k + 1 →
            alpha (j - k - 1 + r) = alpha (j - k - 1 + (k + 1)) := by
          intro r hr
          have hleft := hcontig (j - k - 1) j (by omega) hjN heq.symm
          calc
            alpha (j - k - 1 + r) = alpha (j - k - 1) :=
              hleft _ (by omega) (by omega)
            _ = alpha (j - k - 1 + (k + 1)) :=
              (hleft _ (by omega) (by omega)).symm
        calc
          f j / (Nat.factorial (k + 1) : ℂ) =
              (Polynomial.hasseDeriv (k + 1) q).eval (alpha j) := by
                simpa [hordereq] using hfac
          _ = higham22HermiteWindowDD alpha q (j - (k + 1)) (k + 1) := by
                rw [show j - (k + 1) = j - k - 1 by omega,
                  higham22Hermite_repeated_windowDD_eq_hasse alpha q
                  (j - k - 1) (k + 1) hrepeat]
                congr 2 <;> omega
      · rw [if_neg heq, ih j hjN (by omega)
            (higham22HermiteNodeOrder_le_of_ne alpha (by omega) heq),
          hsaved (j - 1) (by omega) (by omega)]
        have hrec := higham22HermiteWindowDD_first_last_recurrence alpha q
          (j - k - 1) k (by
            intro h
            rw [show j - k - 1 + k + 1 = j by omega] at h
            exact heq h)
        have h0 : j - (k + 1) = j - k - 1 := by omega
        have h2 : j - k - 1 = j - 1 - k := by omega
        have h1 : j - 1 - k + 1 = j - k := by omega
        have h3 : j - 1 - k + k + 1 = j := by omega
        simpa only [h0, h2, h1, h3] using hrec.symm

theorem higham22HermiteWindowQuotient_natDegree (alpha : ℕ → ℂ)
    (q : Polynomial ℂ) (start k : ℕ) :
    (higham22HermiteWindowQuotient alpha start q k).natDegree = q.natDegree - k := by
  induction k with
  | zero => simp [higham22HermiteWindowQuotient]
  | succ k ih =>
      rw [higham22HermiteWindowQuotient,
        Polynomial.natDegree_divByMonic _
          (Polynomial.monic_X_sub_C (alpha (start + k))),
        Polynomial.natDegree_X_sub_C, ih]
      omega

theorem higham22HermiteWindowQuotient_eq_zero_of_natDegree_lt
    (alpha : ℕ → ℂ) (q : Polynomial ℂ) (start count : ℕ)
    (hdegree : q.natDegree < count) :
    higham22HermiteWindowQuotient alpha start q count = 0 := by
  cases count with
  | zero => omega
  | succ k =>
      rw [higham22HermiteWindowQuotient]
      apply (Polynomial.divByMonic_eq_zero_iff
        (Polynomial.monic_X_sub_C (alpha (start + k)))).2
      apply Polynomial.degree_lt_degree
      rw [Polynomial.natDegree_X_sub_C,
        higham22HermiteWindowQuotient_natDegree]
      omega

theorem higham22Hermite_newtonPrefixTail_windowQuotient
    (alpha : ℕ → ℂ) (q : Polynomial ℂ) (count : ℕ) :
    higham22NewtonPrefixTail alpha (fun i => higham22HermiteWindowDD alpha q 0 i)
        0 count (higham22HermiteWindowQuotient alpha 0 q count) = q := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [higham22NewtonPrefixTail_append]
      have htail :
          Polynomial.C (higham22HermiteWindowDD alpha q 0 count) +
              (Polynomial.X - Polynomial.C (alpha count)) *
                higham22HermiteWindowQuotient alpha 0 q (count + 1) =
            higham22HermiteWindowQuotient alpha 0 q count := by
        simpa [higham22HermiteWindowDD, higham22HermiteWindowQuotient] using
          (higham22Hermite_reconstruct_divByMonic
            (higham22HermiteWindowQuotient alpha 0 q count) (alpha count)).symm
      simp only [Nat.zero_add]
      rw [htail]
      exact ih

theorem higham22Hermite_newtonNest_windowDD_eq
    (alpha : ℕ → ℂ) (q : Polynomial ℂ) (n : ℕ)
    (hdegree : q.natDegree < n + 1) :
    higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin (n + 1) =>
          (alpha i, higham22HermiteWindowDD alpha q 0 i)) = q := by
  let c : ℕ → ℂ := fun i => higham22HermiteWindowDD alpha q 0 i
  have hzero : higham22HermiteWindowQuotient alpha 0 q (n + 1) = 0 :=
    higham22HermiteWindowQuotient_eq_zero_of_natDegree_lt alpha q 0 (n + 1) hdegree
  have hreconstruct := higham22Hermite_newtonPrefixTail_windowQuotient alpha q (n + 1)
  rw [hzero] at hreconstruct
  have hnest := higham22NewtonPrefixTail_eq_nest alpha c 0 n
  calc
    higham22NewtonPolynomialNest
          (List.ofFn fun i : Fin (n + 1) =>
            (alpha i, higham22HermiteWindowDD alpha q 0 i)) =
        higham22NewtonPrefixTail alpha c 0 n (Polynomial.C (c n)) := by
          simpa [c] using hnest.symm
    _ = higham22NewtonPrefixTail alpha c 0 (n + 1) 0 := by
          rw [higham22NewtonPrefixTail_append]
          simp
    _ = q := by simpa [c] using hreconstruct

theorem higham22Hermite_confluentTable_newtonNest_eq
    (alpha f : ℕ → ℂ) (q : Polynomial ℂ) (N : ℕ)
    (hcontig : Higham22ContiguousNodesNatOn alpha N)
    (hdata : Higham22HermiteDataOn alpha f q N) (n : ℕ) (hnN : n < N)
    (hdegree : q.natDegree < n + 1) :
    higham22NewtonPolynomialNest
        (List.ofFn fun i : Fin (n + 1) =>
          (alpha i,
            higham22ConfluentDividedDifferenceTable alpha f i i)) = q := by
  rw [← higham22Hermite_newtonNest_windowDD_eq alpha q n hdegree]
  apply congrArg higham22NewtonPolynomialNest
  apply List.ofFn_inj.mpr
  funext i
  congr 2
  simpa using (higham22Hermite_confluentTable_eq_windowDD alpha f q N hcontig hdata
    i i (by omega) le_rfl (higham22HermiteNodeOrder_le alpha i))

theorem higham22Hermite_recurrence_natDegree_leadingCoeff
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (j : ℕ) :
    (p j).natDegree = j ∧ (p j).leadingCoeff ≠ 0 := by
  induction j using Nat.twoStepInduction with
  | zero => simp [hp.1]
  | one =>
      rw [hp.2.1]
      constructor
      · rw [Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr (htheta 0))
            (Polynomial.X_sub_C_ne_zero (beta 0)),
          Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C]
      · rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
          Polynomial.leadingCoeff_X_sub_C, mul_one]
        exact htheta 0
  | more j hj hsj =>
      rw [hp.2.2 j]
      let a := Polynomial.C (theta (j + 1)) *
        (Polynomial.X - Polynomial.C (beta (j + 1))) * p (j + 1)
      let b := Polynomial.C (gamma (j + 1)) * p j
      have ha0 : a ≠ 0 := by
        apply mul_ne_zero
        · exact mul_ne_zero (Polynomial.C_ne_zero.mpr (htheta (j + 1)))
            (Polynomial.X_sub_C_ne_zero _)
        · exact Polynomial.leadingCoeff_ne_zero.mp hsj.2
      have hadegree : a.natDegree = j + 2 := by
        simp only [a]
        rw [Polynomial.natDegree_mul
            (mul_ne_zero (Polynomial.C_ne_zero.mpr (htheta (j + 1)))
              (Polynomial.X_sub_C_ne_zero _))
            (Polynomial.leadingCoeff_ne_zero.mp hsj.2),
          Polynomial.natDegree_mul (Polynomial.C_ne_zero.mpr (htheta (j + 1)))
            (Polynomial.X_sub_C_ne_zero _),
          Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C, hsj.1]
        omega
      have hbdegree : b.natDegree ≤ j := by
        exact (Polynomial.natDegree_C_mul_le _ _).trans_eq hj.1
      have hba : b.natDegree < a.natDegree := by omega
      have hlca : a.leadingCoeff ≠ 0 :=
        Polynomial.leadingCoeff_ne_zero.mpr ha0
      change (a - b).natDegree = j + 2 ∧ (a - b).leadingCoeff ≠ 0
      rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hba,
        Polynomial.leadingCoeff_sub_of_degree_lt
          (Polynomial.degree_lt_degree hba)]
      exact ⟨hadegree, hlca⟩

noncomputable def higham22HermiteBasisCoefficientMatrix {N : ℕ}
    (p : Fin N → Polynomial ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => (p j).coeff i

theorem higham22Hermite_basisCoefficientMatrix_upperTriangular
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (N : ℕ) :
    Matrix.BlockTriangular
      (higham22HermiteBasisCoefficientMatrix (fun i : Fin N => p i)) id := by
  intro i j hji
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [(higham22Hermite_recurrence_natDegree_leadingCoeff hp htheta j).1]
  change (j : ℕ) < (i : ℕ) at hji
  exact hji

theorem higham22Hermite_basisCoefficientMatrix_diagonal_ne_zero
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {N : ℕ} (i : Fin N) :
    higham22HermiteBasisCoefficientMatrix (fun j : Fin N => p j) i i ≠ 0 := by
  have h := higham22Hermite_recurrence_natDegree_leadingCoeff hp htheta (i : ℕ)
  simpa [higham22HermiteBasisCoefficientMatrix, Polynomial.leadingCoeff, h.1] using h.2

theorem higham22Hermite_basisCoefficientMatrix_det_ne_zero
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (N : ℕ) :
    (higham22HermiteBasisCoefficientMatrix (fun i : Fin N => p i)).det ≠ 0 := by
  rw [Matrix.det_of_upperTriangular
    (higham22Hermite_basisCoefficientMatrix_upperTriangular hp htheta N)]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _hi
  exact higham22Hermite_basisCoefficientMatrix_diagonal_ne_zero hp htheta i

theorem higham22Hermite_basisCoefficientMatrix_mulVec_apply
    {N : ℕ} (p : Fin N → Polynomial ℂ) (a : Fin N → ℂ) (i : Fin N) :
    (higham22HermiteBasisCoefficientMatrix p).mulVec a i =
      (higham22BasisExpansion p a).coeff i := by
  simp [higham22HermiteBasisCoefficientMatrix, Matrix.mulVec, dotProduct,
    higham22BasisExpansion, Polynomial.coeff_sum, Polynomial.coeff_C_mul,
    mul_comm]

theorem higham22Hermite_basisExpansion_injective
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) (N : ℕ) :
    Function.Injective
      (higham22BasisExpansion (fun i : Fin N => p i)) := by
  have hdet := higham22Hermite_basisCoefficientMatrix_det_ne_zero hp htheta N
  have hunit : IsUnit
      (higham22HermiteBasisCoefficientMatrix (fun i : Fin N => p i)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hinj : Function.Injective
      (higham22HermiteBasisCoefficientMatrix (fun i : Fin N => p i)).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  intro a b hab
  apply hinj
  funext i
  rw [higham22Hermite_basisCoefficientMatrix_mulVec_apply,
    higham22Hermite_basisCoefficientMatrix_mulVec_apply, hab]

noncomputable def higham22HermiteFiniteNodeOrder {N : ℕ}
    (alpha : Fin N → ℂ) (j : Fin N) : ℕ :=
  higham22HermiteNodeOrder (higham22FinExtend alpha) j

noncomputable def higham22HermiteConfluentVandermondeLike {N : ℕ}
    (p : Fin N → Polynomial ℂ) (alpha : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j =>
    ((Polynomial.derivative^[higham22HermiteFiniteNodeOrder alpha j]) (p i)).eval (alpha j)

theorem higham22Hermite_confluentVandermondeLike_transpose_mulVec_apply
    {N : ℕ} (p : Fin N → Polynomial ℂ) (alpha a : Fin N → ℂ)
    (j : Fin N) :
    (higham22HermiteConfluentVandermondeLike p alpha).transpose.mulVec a j =
      ((Polynomial.derivative^[higham22HermiteFiniteNodeOrder alpha j])
        (higham22BasisExpansion p a)).eval (alpha j) := by
  simp only [higham22HermiteConfluentVandermondeLike, Matrix.transpose_apply,
    Matrix.mulVec, dotProduct, higham22BasisExpansion,
    Polynomial.iterate_derivative_sum, Polynomial.eval_finset_sum,
    Polynomial.iterate_derivative_C_mul, Polynomial.eval_mul,
    Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

theorem higham22Hermite_basisExpansion_natDegree_lt
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ} (a : Fin (n + 1) → ℂ) :
    (higham22BasisExpansion (fun i : Fin (n + 1) => p i) a).natDegree < n + 1 := by
  unfold higham22BasisExpansion
  apply lt_of_le_of_lt
    (Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.univ)
      (fun i : Fin (n + 1) => Polynomial.C (a i) * p i) (n := n) ?_)
    (Nat.lt_succ_self n)
  intro i _hi
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by rw [(higham22Hermite_recurrence_natDegree_leadingCoeff hp htheta i).1]; omega)

theorem higham22Hermite_algorithm22_2Printed_recovers_confluent_data
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (a : Fin (n + 1) → ℂ) :
    higham22Algorithm22_2Printed theta beta gamma alpha
        ((higham22HermiteConfluentVandermondeLike
          (fun i : Fin (n + 1) => p i) alpha).transpose.mulVec a) = a := by
  let pfin : Fin (n + 1) → Polynomial ℂ := fun i => p i
  let P := higham22HermiteConfluentVandermondeLike pfin alpha
  let f : Fin (n + 1) → ℂ := P.transpose.mulVec a
  let q := higham22BasisExpansion pfin a
  have hdata : Higham22HermiteDataOn
      (higham22FinExtend alpha) (higham22FinExtend f) q (n + 1) := by
    intro j hj
    let jf : Fin (n + 1) := ⟨j, hj⟩
    have hm := higham22Hermite_confluentVandermondeLike_transpose_mulVec_apply
      pfin alpha a jf
    have hmf : f jf =
        ((Polynomial.derivative^[higham22HermiteFiniteNodeOrder alpha jf]) q).eval
          (alpha jf) := by
      simpa [f, P, q] using hm
    calc
      higham22FinExtend f j = f jf := higham22FinExtend_apply f jf
      _ = ((Polynomial.derivative^[higham22HermiteFiniteNodeOrder alpha jf]) q).eval
            (alpha jf) := hmf
      _ = ((Polynomial.derivative^[higham22HermiteNodeOrder (higham22FinExtend alpha) j]) q).eval
            (higham22FinExtend alpha j) := by
              rw [higham22FinExtend_apply alpha jf]
              rfl
  have hdegree : q.natDegree < n + 1 := by
    simpa [q, pfin] using higham22Hermite_basisExpansion_natDegree_lt hp htheta a
  have hinterp := higham22Hermite_confluentTable_newtonNest_eq
    (higham22FinExtend alpha) (higham22FinExtend f) q (n + 1)
    (higham22FinExtend_contiguousNodesNatOn hcontig) hdata n (by omega) hdegree
  have htable :
      higham22NewtonPolynomialNest
          (List.ofFn fun i : Fin (n + 1) =>
            (alpha i,
              higham22ConfluentDividedDifferenceTable
                (higham22FinExtend alpha) (higham22FinExtend f) i i)) = q := by
    simpa using hinterp
  have hstage :
      higham22NewtonPolynomialNest
          (List.ofFn fun i : Fin (n + 1) =>
            (alpha i, higham22Algorithm22_2StageIFin alpha f n i)) = q := by
    rw [← htable]
    apply congrArg higham22NewtonPolynomialNest
    apply List.ofFn_inj.mpr
    funext i
    congr 2
    exact higham22_algorithm22_2StageIFin_eq_confluent_diagonal
      alpha f hcontig i
  have hpoly := higham22_algorithm22_2Printed_newton_invariant
    hp htheta alpha f
  rw [hstage] at hpoly
  apply higham22Hermite_basisExpansion_injective hp htheta (n + 1)
  simpa [pfin, q, f, P] using hpoly

theorem higham22Hermite_eq22_17_product_mul_confluentTranspose
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha) :
    higham22Algorithm22_2FactorProduct theta beta gamma alpha *
        (higham22HermiteConfluentVandermondeLike
          (fun i : Fin (n + 1) => p i) alpha).transpose = 1 := by
  let A := higham22Algorithm22_2FactorProduct theta beta gamma alpha *
    (higham22HermiteConfluentVandermondeLike
      (fun i : Fin (n + 1) => p i) alpha).transpose
  have hact : ∀ a : Fin (n + 1) → ℂ, A.mulVec a = a := by
    intro a
    change (higham22Algorithm22_2FactorProduct theta beta gamma alpha *
      (higham22HermiteConfluentVandermondeLike
        (fun i : Fin (n + 1) => p i) alpha).transpose).mulVec a = a
    rw [← Matrix.mulVec_mulVec,
      higham22_eq22_17_algorithm_product]
    exact higham22Hermite_algorithm22_2Printed_recovers_confluent_data
      hp htheta alpha hcontig a
  apply Matrix.ext
  intro i j
  have h := congrFun (hact (Pi.single j 1)) i
  simpa [A, Matrix.mulVec, dotProduct, Matrix.one_apply,
    Pi.single_apply, eq_comm] using h

theorem higham22Hermite_eq22_17_inverse
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha) :
    higham22Algorithm22_2FactorProduct theta beta gamma alpha =
      (higham22HermiteConfluentVandermondeLike
        (fun i : Fin (n + 1) => p i) alpha).transpose⁻¹ := by
  exact (Matrix.inv_eq_left_inv
    (higham22Hermite_eq22_17_product_mul_confluentTranspose hp htheta alpha hcontig)).symm

/-- Final-solve form of Algorithm 22.2: under the source ordering assumption
(22.5), the literal two-stage loop solves the confluent transposed system. -/
theorem higham22Hermite_algorithm22_2Printed_solve
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (f : Fin (n + 1) → ℂ) :
    (higham22HermiteConfluentVandermondeLike
        (fun i : Fin (n + 1) => p i) alpha).transpose.mulVec
        (higham22Algorithm22_2Printed theta beta gamma alpha f) = f := by
  rw [← higham22_eq22_17_algorithm_product]
  rw [Matrix.mulVec_mulVec]
  rw [mul_eq_one_comm.mpr
    (higham22Hermite_eq22_17_product_mul_confluentTranspose
      hp htheta alpha hcontig)]
  exact Matrix.one_mulVec f

/-- Factor-transpose realization of the primal Algorithm 22.3 derived from
equation (22.17).  The earlier natural-indexed definitions retain the literal
printed in-place loop; this finite realization exposes its mathematical factor
action directly. -/
noncomputable def higham22Algorithm22_3Factorized
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  (higham22Algorithm22_2FactorProduct theta beta gamma alpha).transpose.mulVec b

/-- Final-solve theorem for the factor-transpose realization of Algorithm
22.3: it solves the primal confluent Vandermonde-like system. -/
theorem higham22Hermite_algorithm22_3Factorized_solve
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (b : Fin (n + 1) → ℂ) :
    (higham22HermiteConfluentVandermondeLike
        (fun i : Fin (n + 1) => p i) alpha).mulVec
        (higham22Algorithm22_3Factorized theta beta gamma alpha b) = b := by
  have hleft := higham22Hermite_eq22_17_product_mul_confluentTranspose
    hp htheta alpha hcontig
  have hright :
      higham22HermiteConfluentVandermondeLike
          (fun i : Fin (n + 1) => p i) alpha *
        (higham22Algorithm22_2FactorProduct theta beta gamma alpha).transpose = 1 := by
    have ht := congrArg Matrix.transpose hleft
    simpa [Matrix.transpose_mul] using ht
  rw [higham22Algorithm22_3Factorized, Matrix.mulVec_mulVec, hright,
    Matrix.one_mulVec]


/-! ### Literal Algorithm 22.3 executor bridge

The lemmas below derive both transpose-factor stages from the separately
implemented source loop.  In particular, the Stage-II invariant accounts for
the printed `xlast` carry across repeated-node branches. -/

theorem higham22_algorithm22_3StageIInner_apply
    (theta beta gamma alpha : ℕ → ℂ) (k count : ℕ)
    (d : ℕ → ℂ) (m : ℕ) :
    higham22Algorithm22_3StageIInner theta beta gamma alpha k count d m =
      if k + 2 ≤ m ∧ m ≤ k + count then
        (gamma (m - k - 1) / theta (m - k - 1)) * d (m - 2) +
          (beta (m - k - 1) - alpha k) * d (m - 1) +
          d m / theta (m - k - 1)
      else d m := by
  induction count using Nat.twoStepInduction generalizing d m with
  | zero =>
      simp only [higham22Algorithm22_3StageIInner]
      rw [if_neg (by omega : ¬(k + 2 ≤ m ∧ m ≤ k + 0))]
  | one =>
      simp only [higham22Algorithm22_3StageIInner]
      rw [if_neg (by omega : ¬(k + 2 ≤ m ∧ m ≤ k + 1))]
  | more c ih ih1 =>
      simp only [higham22Algorithm22_3StageIInner]
      let d' := Function.update d (k + (c + 2))
        ((gamma (c + 2 - 1) / theta (c + 2 - 1)) * d (k + (c + 2) - 2) +
          (beta (c + 2 - 1) - alpha k) * d (k + (c + 2) - 1) +
          d (k + (c + 2)) / theta (c + 2 - 1))
      change higham22Algorithm22_3StageIInner theta beta gamma alpha k
          (c + 1) d' m = _
      rw [ih1 d' m]
      by_cases htop : m = k + (c + 2)
      · rw [if_neg (by omega : ¬(k + 2 ≤ m ∧ m ≤ k + (c + 1)))]
        rw [if_pos (by omega : k + 2 ≤ m ∧ m ≤ k + (c + 2))]
        subst m
        simp [d']
      · by_cases hactive : k + 2 ≤ m ∧ m ≤ k + (c + 1)
        · rw [if_pos hactive, if_pos (by omega : k + 2 ≤ m ∧ m ≤ k + (c + 2))]
          have hm0 : m ≠ k + (c + 2) := by omega
          have hm1 : m - 1 ≠ k + (c + 2) := by omega
          have hm2 : m - 2 ≠ k + (c + 2) := by omega
          simp [d', hm0, hm1, hm2]
        · rw [if_neg hactive, if_neg (by omega : ¬(k + 2 ≤ m ∧ m ≤ k + (c + 2)))]
          simp [d', htop]

noncomputable def higham22Algorithm22_3StageISweep
    (theta beta gamma alpha : ℕ → ℂ) (n k : ℕ)
    (d : ℕ → ℂ) : ℕ → ℂ :=
  let swept := higham22Algorithm22_3StageIInner
    theta beta gamma alpha k (n - k) d
  Function.update swept (k + 1)
    ((beta 0 - alpha k) * swept k + swept (k + 1) / theta 0)

theorem higham22_stageIIUpperFactor_transpose_mulVec_apply
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) (k : ℕ) (hk : k < n)
    (i : Fin (n + 1)) :
    (higham22StageIIUpperFactor theta beta gamma alpha k).transpose.mulVec b i =
      if (i : ℕ) ≤ k then b i
      else if (i : ℕ) = k + 1 then
        (beta 0 - higham22FinExtend alpha k) * higham22FinExtend b k +
          higham22FinExtend b (k + 1) / theta 0
      else
        (gamma ((i : ℕ) - k - 1) / theta ((i : ℕ) - k - 1)) *
            higham22FinExtend b ((i : ℕ) - 2) +
          (beta ((i : ℕ) - k - 1) - higham22FinExtend alpha k) *
            higham22FinExtend b ((i : ℕ) - 1) +
          higham22FinExtend b i / theta ((i : ℕ) - k - 1) := by
  classical
  rw [Matrix.mulVec]
  simp only [dotProduct, Matrix.transpose_apply, higham22StageIIUpperFactor,
    LinearMap.toMatrix'_apply, higham22StageIIUpperLinear]
  by_cases hi0 : (i : ℕ) ≤ k
  · rw [if_pos hi0]
    calc
      _ = ∑ x : Fin (n + 1), if x = i then b x else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        change higham22Algorithm22_2PrintedStageIIStep theta beta gamma
            (higham22FinExtend alpha) n k
            (higham22FinExtend (Pi.single i 1)) x * b x = _
        simp only [higham22Algorithm22_2PrintedStageIIStep]
        split_ifs with hxk hinterior hlast hn
        all_goals
          simp only [higham22FinExtend_single]
          split_ifs <;> subst_vars
        all_goals try omega
        all_goals simp
      _ = b i := by simp
  · rw [if_neg hi0]
    by_cases hi1 : (i : ℕ) = k + 1
    · rw [if_pos hi1]
      let kf : Fin (n + 1) := ⟨k, by omega⟩
      let k1f : Fin (n + 1) := ⟨k + 1, by omega⟩
      calc
        _ = ∑ x : Fin (n + 1),
              if x = kf then
                (beta 0 - higham22FinExtend alpha k) * b x
              else if x = k1f then b x / theta 0 else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          change higham22Algorithm22_2PrintedStageIIStep theta beta gamma
              (higham22FinExtend alpha) n k
              (higham22FinExtend (Pi.single i 1)) x * b x = _
          simp only [higham22Algorithm22_2PrintedStageIIStep]
          split_ifs
          all_goals dsimp [kf, k1f] at *
          all_goals simp only [Fin.ext_iff] at *
          all_goals simp only [higham22FinExtend_single]
          all_goals split_ifs <;> subst_vars
          all_goals try omega
          all_goals simp
          all_goals
            rw [div_eq_mul_inv, mul_comm (b x)]
            apply congrArg (fun z : ℂ => z * b x)
            apply congrArg Inv.inv
            apply congrArg theta
            omega
        _ = (beta 0 - higham22FinExtend alpha k) * higham22FinExtend b k +
              higham22FinExtend b (k + 1) / theta 0 := by
          have hkf_ne : kf ≠ k1f := by
            simp [kf, k1f, Fin.ext_iff]
          calc
            _ = (∑ x : Fin (n + 1),
                    if x = kf then
                      (beta 0 - higham22FinExtend alpha k) * b x else 0) +
                  ∑ x : Fin (n + 1),
                    if x = k1f then b x / theta 0 else 0 := by
                rw [← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro x _hx
                by_cases hx : x = kf
                · subst x
                  simp [hkf_ne]
                · simp [hx]
            _ = (beta 0 - higham22FinExtend alpha k) * b kf +
                  b k1f / theta 0 := by
                rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
            _ = _ := by
                have hkle : k ≤ n := Nat.le_of_lt hk
                simp [kf, k1f, higham22FinExtend, hkle, hk]
    · rw [if_neg hi1]
      have hi2 : k + 2 ≤ (i : ℕ) := by omega
      let im2 : Fin (n + 1) := ⟨(i : ℕ) - 2, by omega⟩
      let im1 : Fin (n + 1) := ⟨(i : ℕ) - 1, by omega⟩
      let r := (i : ℕ) - k - 1
      calc
        _ = ∑ x : Fin (n + 1),
              if x = im2 then (gamma r / theta r) * b x
              else if x = im1 then
                (beta r - higham22FinExtend alpha k) * b x
              else if x = i then b x / theta r else 0 := by
          apply Finset.sum_congr rfl
          intro x _hx
          change higham22Algorithm22_2PrintedStageIIStep theta beta gamma
              (higham22FinExtend alpha) n k
              (higham22FinExtend (Pi.single i 1)) x * b x = _
          simp only [higham22Algorithm22_2PrintedStageIIStep]
          split_ifs
          all_goals dsimp [im2, im1, r] at *
          all_goals simp only [Fin.ext_iff] at *
          all_goals simp only [higham22FinExtend_single]
          all_goals split_ifs <;> subst_vars
          all_goals try omega
          all_goals simp
          all_goals try ring
          all_goals first
            | left
              apply congrArg beta
              omega
            | left
              apply congrArg₂ (· * ·)
              · apply congrArg gamma
                omega
              · apply congrArg Inv.inv
                apply congrArg theta
                omega
            | rw [mul_comm]
              apply congrArg (fun z : ℂ => b x * z)
              apply congrArg Inv.inv
              apply congrArg theta
              omega
        _ = (gamma r / theta r) * higham22FinExtend b ((i : ℕ) - 2) +
              (beta r - higham22FinExtend alpha k) *
                  higham22FinExtend b ((i : ℕ) - 1) +
                higham22FinExtend b i / theta r := by
          have him2_ne_im1 : im2 ≠ im1 := by
            simp [im2, im1, Fin.ext_iff]
            omega
          have him2_ne_i : im2 ≠ i := by
            simp [im2, Fin.ext_iff]
            omega
          have him1_ne_i : im1 ≠ i := by
            simp [im1, Fin.ext_iff]
            omega
          calc
            _ = (∑ x : Fin (n + 1),
                    if x = im2 then (gamma r / theta r) * b x else 0) +
                  (∑ x : Fin (n + 1),
                    if x = im1 then
                      (beta r - higham22FinExtend alpha k) * b x else 0) +
                  ∑ x : Fin (n + 1),
                    if x = i then b x / theta r else 0 := by
                rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
                apply Finset.sum_congr rfl
                intro x _hx
                by_cases hx2 : x = im2
                · subst x
                  simp [him2_ne_im1, him2_ne_i]
                · by_cases hx1 : x = im1
                  · subst x
                    simp [hx2, him1_ne_i]
                  · simp [hx2, hx1]
            _ = (gamma r / theta r) * b im2 +
                  (beta r - higham22FinExtend alpha k) * b im1 +
                    b i / theta r := by
                rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq',
                  Fintype.sum_ite_eq']
            _ = _ := by
                have hb2 : higham22FinExtend b ((i : ℕ) - 2) = b im2 := by
                  change higham22FinExtend b (im2 : ℕ) = b im2
                  exact higham22FinExtend_apply b im2
                have hb1 : higham22FinExtend b ((i : ℕ) - 1) = b im1 := by
                  change higham22FinExtend b (im1 : ℕ) = b im1
                  exact higham22FinExtend_apply b im1
                rw [hb2, hb1, higham22FinExtend_apply b i]

theorem higham22_algorithm22_3StageISweep_eq_upper_transpose_mulVec
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) (k : ℕ) (hk : k < n) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageISweep theta beta gamma (higham22FinExtend alpha) n k
          (higham22FinExtend b) i) =
      (higham22StageIIUpperFactor theta beta gamma alpha k).transpose.mulVec b := by
  funext i
  rw [higham22_stageIIUpperFactor_transpose_mulVec_apply theta beta gamma alpha b k hk i]
  by_cases hi0 : (i : ℕ) ≤ k
  · rw [if_pos hi0]
    have hik1 : (i : ℕ) ≠ k + 1 := by omega
    have hnot : ¬(k + 2 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k + (n - k)) := by omega
    simp [higham22Algorithm22_3StageISweep, higham22_algorithm22_3StageIInner_apply, hik1, hi0,
      hnot, higham22FinExtend_apply]
  · rw [if_neg hi0]
    by_cases hi1 : (i : ℕ) = k + 1
    · rw [if_pos hi1]
      have hknot : ¬(k + 2 ≤ k ∧ k ≤ k + (n - k)) := by omega
      have hk1not : ¬(k + 2 ≤ k + 1 ∧ k + 1 ≤ k + (n - k)) := by omega
      simp [higham22Algorithm22_3StageISweep, higham22_algorithm22_3StageIInner_apply, hi1, hknot, hk1not,
        higham22FinExtend]
    · rw [if_neg hi1]
      have hi2 : k + 2 ≤ (i : ℕ) := by omega
      have hkn : k ≤ n := Nat.le_of_lt hk
      have htop : (i : ℕ) ≤ k + (n - k) := by omega
      have hik1 : (i : ℕ) ≠ k + 1 := by omega
      simp [higham22Algorithm22_3StageISweep, higham22_algorithm22_3StageIInner_apply, hi2, htop, hik1,
        higham22FinExtend_apply]

theorem higham22_algorithm22_3StageISweep_restrict_eq_upper_transpose_mulVec
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (d : ℕ → ℂ) (k : ℕ) (hk : k < n) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageISweep theta beta gamma (higham22FinExtend alpha) n k d i) =
      (higham22StageIIUpperFactor theta beta gamma alpha k).transpose.mulVec
        (fun i => d i) := by
  funext i
  rw [higham22_stageIIUpperFactor_transpose_mulVec_apply theta beta gamma alpha
    (fun i => d i) k hk i]
  by_cases hi0 : (i : ℕ) ≤ k
  · rw [if_pos hi0]
    have hik1 : (i : ℕ) ≠ k + 1 := by omega
    have hnot : ¬(k + 2 ≤ (i : ℕ) ∧ (i : ℕ) ≤ k + (n - k)) := by omega
    simp [higham22Algorithm22_3StageISweep, higham22_algorithm22_3StageIInner_apply, hik1, hnot]
  · rw [if_neg hi0]
    by_cases hi1 : (i : ℕ) = k + 1
    · rw [if_pos hi1]
      have ha : higham22FinExtend alpha k = alpha ⟨k, by omega⟩ := by
        simp [higham22FinExtend, show k < n + 1 by omega]
      have hd0 : higham22FinExtend (fun q : Fin (n + 1) => d q) k = d k := by
        simp [higham22FinExtend, show k < n + 1 by omega]
      have hd1 : higham22FinExtend (fun q : Fin (n + 1) => d q) (k + 1) =
          d (k + 1) := by
        simp [higham22FinExtend, show k + 1 < n + 1 by omega]
      simp [higham22Algorithm22_3StageISweep, higham22_algorithm22_3StageIInner_apply, hi1,
        ha, hd0, hd1]
    · rw [if_neg hi1]
      have hi2 : k + 2 ≤ (i : ℕ) := by omega
      have hkn : k ≤ n := Nat.le_of_lt hk
      have htop : (i : ℕ) ≤ k + (n - k) := by omega
      have hik1 : (i : ℕ) ≠ k + 1 := by omega
      have ha : higham22FinExtend alpha k = alpha ⟨k, by omega⟩ := by
        simp [higham22FinExtend, show k < n + 1 by omega]
      have hd2 : higham22FinExtend (fun q : Fin (n + 1) => d q)
          ((i : ℕ) - 2) = d ((i : ℕ) - 2) := by
        simp [higham22FinExtend, show (i : ℕ) - 2 < n + 1 by omega]
      have hd1 : higham22FinExtend (fun q : Fin (n + 1) => d q)
          ((i : ℕ) - 1) = d ((i : ℕ) - 1) := by
        simp [higham22FinExtend, show (i : ℕ) - 1 < n + 1 by omega]
      have hdi : higham22FinExtend (fun q : Fin (n + 1) => d q) i = d i := by
        exact higham22FinExtend_apply _ i
      simp [higham22Algorithm22_3StageISweep, higham22_algorithm22_3StageIInner_apply, hi2, htop, hik1,
        ha, hd2, hd1, hdi]

theorem higham22_algorithm22_3StageIOuter_restrict_eq_upperProduct_transpose_mulVec
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (steps : ℕ) (hsteps : steps ≤ n)
    (d : ℕ → ℂ) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageIOuter theta beta gamma
          (higham22FinExtend alpha) n steps d i) =
      (higham22StageIIUpperProduct theta beta gamma alpha steps).transpose.mulVec
        (fun i => d i) := by
  induction steps generalizing d with
  | zero =>
      simp [higham22Algorithm22_3StageIOuter, higham22StageIIUpperProduct]
  | succ k ih =>
      let previous := higham22Algorithm22_3StageIOuter theta beta gamma
        (higham22FinExtend alpha) n k d
      change (fun i : Fin (n + 1) =>
          higham22Algorithm22_3StageISweep theta beta gamma (higham22FinExtend alpha) n k
            previous i) = _
      rw [higham22_algorithm22_3StageISweep_restrict_eq_upper_transpose_mulVec
        theta beta gamma alpha previous k (by omega)]
      rw [ih (by omega) d]
      rw [higham22StageIIUpperProduct, Matrix.transpose_mul,
        ← Matrix.mulVec_mulVec]

theorem higham22_algorithm22_3StageI_eq_outer
    (theta beta gamma alpha : ℕ → ℂ) (n : ℕ) (d : ℕ → ℂ) :
    higham22Algorithm22_3StageI theta beta gamma alpha n d =
      higham22Algorithm22_3StageIOuter theta beta gamma alpha n n d := by
  cases n with
  | zero =>
      simp [higham22Algorithm22_3StageI, higham22Algorithm22_3StageIOuter]
  | succ m =>
      simp [higham22Algorithm22_3StageI, higham22Algorithm22_3StageIOuter,
        higham22Algorithm22_3StageISweep, higham22Algorithm22_3StageIInner]

theorem higham22_algorithm22_3StageI_restrict_eq_upperProduct_transpose_mulVec
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageI theta beta gamma
          (higham22FinExtend alpha) n (higham22FinExtend b) i) =
      (higham22StageIIUpperProduct theta beta gamma alpha n).transpose.mulVec b := by
  rw [higham22_algorithm22_3StageI_eq_outer]
  rw [higham22_algorithm22_3StageIOuter_restrict_eq_upperProduct_transpose_mulVec
    theta beta gamma alpha n le_rfl (higham22FinExtend b)]
  congr 1
  funext i
  exact higham22FinExtend_apply b i

noncomputable def higham22Algorithm22_3StageIISweep
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ) : ℕ → ℂ :=
  let result := higham22Algorithm22_3StageIIInner alpha k count x xlast
  Function.update result.1 k (result.1 k - result.2)

theorem higham22_algorithm22_3StageIIInner_above
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ)
    (m : ℕ) (hm : k + count < m) :
    (higham22Algorithm22_3StageIIInner alpha k count x xlast).1 m = x m := by
  induction count generalizing x xlast with
  | zero => simp [higham22Algorithm22_3StageIIInner]
  | succ count ih =>
      simp only [higham22Algorithm22_3StageIIInner]
      by_cases heq : alpha (k + count + 1) = alpha (k + count + 1 - k - 1)
      · rw [if_pos heq]
        rw [ih _ _ (by omega)]
        simp [show m ≠ k + count + 1 by omega]
      · rw [if_neg heq]
        rw [ih _ _ (by omega)]
        simp [show m ≠ k + count + 1 by omega]

theorem higham22_algorithm22_3StageIISweep_above
    (alpha : ℕ → ℂ) (k count : ℕ) (x : ℕ → ℂ) (xlast : ℂ)
    (m : ℕ) (hm : k + count < m) :
    higham22Algorithm22_3StageIISweep alpha k count x xlast m = x m := by
  simp [higham22Algorithm22_3StageIISweep, show m ≠ k by omega,
    higham22_algorithm22_3StageIIInner_above alpha k count x xlast m hm]

noncomputable def higham22Algorithm22_3StageIIPrefixDot
    (k count : ℕ) (x c : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k + count + 1), x j * c j

noncomputable def higham22Algorithm22_3StageIIPrefixForwardDot
    (alpha : ℕ → ℂ) (k count : ℕ) (x c : ℕ → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (k + count + 1),
    x j * higham22Algorithm22_2StageIStep alpha c k j

theorem higham22_algorithm22_3StageIIPrefixDot_succ
    (k count : ℕ) (x c : ℕ → ℂ) :
    higham22Algorithm22_3StageIIPrefixDot k (count + 1) x c =
      higham22Algorithm22_3StageIIPrefixDot k count x c + x (k + count + 1) * c (k + count + 1) := by
  unfold higham22Algorithm22_3StageIIPrefixDot
  rw [show k + (count + 1) + 1 = (k + count + 1) + 1 by omega,
    Finset.sum_range_succ]

theorem higham22_algorithm22_3StageIIPrefixForwardDot_succ
    (alpha : ℕ → ℂ) (k count : ℕ) (x c : ℕ → ℂ) :
    higham22Algorithm22_3StageIIPrefixForwardDot alpha k (count + 1) x c =
      higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x c +
        x (k + count + 1) *
          higham22Algorithm22_2StageIStep alpha c k (k + count + 1) := by
  unfold higham22Algorithm22_3StageIIPrefixForwardDot
  rw [show k + (count + 1) + 1 = (k + count + 1) + 1 by omega,
    Finset.sum_range_succ]

theorem higham22_algorithm22_3StageIIPrefixForwardDot_update_top
    (alpha : ℕ → ℂ) (k count : ℕ) (x c : ℕ → ℂ) (z : ℂ) :
    higham22Algorithm22_3StageIIPrefixForwardDot alpha k count
        (Function.update x (k + count + 1) z) c =
      higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x c := by
  unfold higham22Algorithm22_3StageIIPrefixForwardDot
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : j < k + count + 1 := Finset.mem_range.mp hj
  simp [show j ≠ k + count + 1 by omega]

theorem higham22_algorithm22_3StageII_adjoint_invariant
    (alpha : ℕ → ℂ) (k count : ℕ) (x c : ℕ → ℂ) (xlast : ℂ) :
    higham22Algorithm22_3StageIIPrefixDot k count
        (higham22Algorithm22_3StageIISweep alpha k count x xlast) c =
      higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x c -
        xlast * c (higham22StageILastSaved alpha k (k + count)) := by
  induction count generalizing x xlast with
  | zero =>
      have hupdate :
          (∑ j ∈ Finset.range k,
              Function.update x k (x k - xlast) j * c j) =
            ∑ j ∈ Finset.range k, x j * c j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        simp [show j ≠ k by omega]
      have hforward :
          (∑ j ∈ Finset.range k,
              x j * higham22Algorithm22_2StageIStep alpha c k j) =
            ∑ j ∈ Finset.range k, x j * c j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hjk : j < k := Finset.mem_range.mp hj
        simp [higham22Algorithm22_2StageIStep, Nat.le_of_lt hjk]
      rw [show higham22StageILastSaved alpha k (k + 0) = k by
        exact higham22StageILastSaved_eq_k_of_le alpha k k le_rfl]
      simp only [higham22Algorithm22_3StageIIPrefixDot, higham22Algorithm22_3StageIIPrefixForwardDot,
        higham22Algorithm22_3StageIISweep, higham22Algorithm22_3StageIIInner,
        Finset.sum_range_succ, Nat.add_zero]
      rw [hupdate, hforward]
      simp [higham22Algorithm22_2StageIStep]
      ring
  | succ count ih =>
      let j := k + count + 1
      by_cases heq : alpha j = alpha (j - k - 1)
      · let x' := Function.update x j (x j / (k + 1 : ℂ))
        have hsweep :
            higham22Algorithm22_3StageIISweep alpha k (count + 1) x xlast =
              higham22Algorithm22_3StageIISweep alpha k count x' xlast := by
          funext m
          simp [higham22Algorithm22_3StageIISweep, higham22Algorithm22_3StageIIInner,
            j, heq, x']
        have htop : higham22Algorithm22_3StageIISweep alpha k count x' xlast j = x' j :=
          higham22_algorithm22_3StageIISweep_above alpha k count x' xlast j (by simp [j])
        have hprefix :
            higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x' c =
              higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x c := by
          simpa [j, x'] using
            higham22_algorithm22_3StageIIPrefixForwardDot_update_top alpha k count x c
              (x j / (k + 1 : ℂ))
        have hstep :
            higham22Algorithm22_2StageIStep alpha c k j =
              c j / (k + 1 : ℂ) :=
          higham22_algorithm22_2StageIStep_of_equal alpha c (by simp [j]) heq
        have hlast :
            higham22StageILastSaved alpha k (k + (count + 1)) =
              higham22StageILastSaved alpha k (k + count) := by
          rw [show k + (count + 1) = (k + count) + 1 by omega]
          simp [higham22StageILastSaved, heq, j]
        calc
          higham22Algorithm22_3StageIIPrefixDot k (count + 1)
              (higham22Algorithm22_3StageIISweep alpha k (count + 1) x xlast) c =
              higham22Algorithm22_3StageIIPrefixDot k count
                  (higham22Algorithm22_3StageIISweep alpha k count x' xlast) c +
                higham22Algorithm22_3StageIISweep alpha k count x' xlast j * c j := by
            rw [hsweep, higham22_algorithm22_3StageIIPrefixDot_succ]
          _ = (higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x' c -
                xlast * c (higham22StageILastSaved alpha k (k + count))) +
              x' j * c j := by rw [ih x' xlast, htop]
          _ = higham22Algorithm22_3StageIIPrefixForwardDot alpha k (count + 1) x c -
                xlast * c (higham22StageILastSaved alpha k (k + (count + 1))) := by
            rw [higham22_algorithm22_3StageIIPrefixForwardDot_succ, hprefix, hstep, hlast]
            simp [x']
            ring
      · let den := alpha j - alpha (j - k - 1)
        let temp := x j / den
        let x' := Function.update x j (temp - xlast)
        have hsweep :
            higham22Algorithm22_3StageIISweep alpha k (count + 1) x xlast =
              higham22Algorithm22_3StageIISweep alpha k count x' temp := by
          funext m
          simp [higham22Algorithm22_3StageIISweep, higham22Algorithm22_3StageIIInner,
            j, heq, den, temp, x']
        have htop : higham22Algorithm22_3StageIISweep alpha k count x' temp j = x' j :=
          higham22_algorithm22_3StageIISweep_above alpha k count x' temp j (by simp [j])
        have hprefix :
            higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x' c =
              higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x c := by
          simpa [j, x'] using
            higham22_algorithm22_3StageIIPrefixForwardDot_update_top alpha k count x c
              (temp - xlast)
        have hstep :
            higham22Algorithm22_2StageIStep alpha c k j =
              (c j - c (higham22StageILastSaved alpha k (k + count))) / den := by
          have hs := higham22_algorithm22_2StageIStep_of_distinct
            alpha c (k := k) (j := j) (by simp [j]) heq
          simpa [j, den] using hs
        have hlast :
            higham22StageILastSaved alpha k (k + (count + 1)) = j := by
          rw [show k + (count + 1) = (k + count) + 1 by omega]
          simp [higham22StageILastSaved, heq, j]
        calc
          higham22Algorithm22_3StageIIPrefixDot k (count + 1)
              (higham22Algorithm22_3StageIISweep alpha k (count + 1) x xlast) c =
              higham22Algorithm22_3StageIIPrefixDot k count
                  (higham22Algorithm22_3StageIISweep alpha k count x' temp) c +
                higham22Algorithm22_3StageIISweep alpha k count x' temp j * c j := by
            rw [hsweep, higham22_algorithm22_3StageIIPrefixDot_succ]
          _ = (higham22Algorithm22_3StageIIPrefixForwardDot alpha k count x' c -
                temp * c (higham22StageILastSaved alpha k (k + count))) +
              x' j * c j := by rw [ih x' temp, htop]
          _ = higham22Algorithm22_3StageIIPrefixForwardDot alpha k (count + 1) x c -
                xlast * c (higham22StageILastSaved alpha k (k + (count + 1))) := by
            rw [higham22_algorithm22_3StageIIPrefixForwardDot_succ, hprefix, hstep, hlast]
            simp [x', temp, den]
            ring

theorem higham22_algorithm22_3StageIIPrefixDot_full
    {n : ℕ} (k : ℕ) (hk : k ≤ n) (x : ℕ → ℂ)
    (c : Fin (n + 1) → ℂ) :
    higham22Algorithm22_3StageIIPrefixDot k (n - k) x (higham22FinExtend c) =
      (fun i : Fin (n + 1) => x i) ⬝ᵥ c := by
  unfold higham22Algorithm22_3StageIIPrefixDot dotProduct
  rw [show k + (n - k) + 1 = n + 1 by omega]
  rw [← Fin.sum_univ_eq_sum_range
    (fun j => x j * higham22FinExtend c j) (n + 1)]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [higham22FinExtend_apply]

theorem higham22_algorithm22_3StageIIPrefixForwardDot_full
    {n : ℕ} (alpha : Fin (n + 1) → ℂ) (k : ℕ) (hk : k ≤ n)
    (x : ℕ → ℂ) (c : Fin (n + 1) → ℂ) :
    higham22Algorithm22_3StageIIPrefixForwardDot (higham22FinExtend alpha) k (n - k)
        x (higham22FinExtend c) =
      (fun i : Fin (n + 1) => x i) ⬝ᵥ
        (higham22StageILowerFactor alpha k).mulVec c := by
  rw [higham22_stageILowerFactor_mulVec]
  unfold higham22Algorithm22_3StageIIPrefixForwardDot dotProduct
  rw [show k + (n - k) + 1 = n + 1 by omega]
  rw [Fin.sum_univ_eq_sum_range
    (fun j => x j * higham22Algorithm22_2StageIStep
      (higham22FinExtend alpha) (higham22FinExtend c) k j) (n + 1)]

theorem higham22_algorithm22_3StageIISweep_dot
    {n : ℕ} (alpha : Fin (n + 1) → ℂ) (k : ℕ) (hk : k ≤ n)
    (x : ℕ → ℂ) (c : Fin (n + 1) → ℂ) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageIISweep (higham22FinExtend alpha) k (n - k) x 0 i) ⬝ᵥ c =
      (fun i : Fin (n + 1) => x i) ⬝ᵥ
        (higham22StageILowerFactor alpha k).mulVec c := by
  have h := higham22_algorithm22_3StageII_adjoint_invariant
    (higham22FinExtend alpha) k (n - k) x (higham22FinExtend c) 0
  rw [higham22_algorithm22_3StageIIPrefixDot_full k hk _ c,
    higham22_algorithm22_3StageIIPrefixForwardDot_full alpha k hk x c] at h
  simpa using h

theorem higham22_algorithm22_3StageIISweep_eq_lower_transpose_mulVec
    {n : ℕ} (alpha : Fin (n + 1) → ℂ) (k : ℕ) (hk : k ≤ n)
    (x : ℕ → ℂ) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageIISweep (higham22FinExtend alpha) k (n - k) x 0 i) =
      (higham22StageILowerFactor alpha k).transpose.mulVec
        (fun i : Fin (n + 1) => x i) := by
  funext i
  have hdot := higham22_algorithm22_3StageIISweep_dot alpha k hk x (Pi.single i 1)
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose] at hdot
  simpa [dotProduct, Pi.single_apply, eq_comm] using hdot

theorem higham22_algorithm22_3StageIIOuter_restrict_eq_lowerProduct_transpose_mulVec
    {n : ℕ} (alpha : Fin (n + 1) → ℂ) (steps : ℕ) (hsteps : steps ≤ n)
    (x : ℕ → ℂ) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageIIOuter
          (higham22FinExtend alpha) n steps x i) =
      (higham22StageILowerProduct alpha steps).transpose.mulVec
        (fun i : Fin (n + 1) => x i) := by
  induction steps generalizing x with
  | zero =>
      simp [higham22Algorithm22_3StageIIOuter, higham22StageILowerProduct]
  | succ k ih =>
      let y := higham22Algorithm22_3StageIISweep (higham22FinExtend alpha) k (n - k) x 0
      change (fun i : Fin (n + 1) =>
          higham22Algorithm22_3StageIIOuter
            (higham22FinExtend alpha) n k y i) = _
      rw [ih (by omega) y]
      rw [higham22_algorithm22_3StageIISweep_eq_lower_transpose_mulVec alpha k (by omega) x]
      rw [higham22StageILowerProduct, Matrix.transpose_mul,
        ← Matrix.mulVec_mulVec]

theorem higham22_algorithm22_3StageII_restrict_eq_lowerProduct_transpose_mulVec
    {n : ℕ} (alpha : Fin (n + 1) → ℂ) (x : ℕ → ℂ) :
    (fun i : Fin (n + 1) =>
        higham22Algorithm22_3StageII (higham22FinExtend alpha) n x i) =
      (higham22StageILowerProduct alpha n).transpose.mulVec
        (fun i : Fin (n + 1) => x i) := by
  unfold higham22Algorithm22_3StageII
  exact higham22_algorithm22_3StageIIOuter_restrict_eq_lowerProduct_transpose_mulVec
    alpha n le_rfl x

theorem higham22_algorithm22_3_eq_factorized
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha b : Fin (n + 1) → ℂ) :
    higham22Algorithm22_3 theta beta gamma alpha b =
      higham22Algorithm22_3Factorized theta beta gamma alpha b := by
  change (fun i : Fin (n + 1) =>
      higham22Algorithm22_3StageII (higham22FinExtend alpha) n
        (higham22Algorithm22_3StageI theta beta gamma
          (higham22FinExtend alpha) n (higham22FinExtend b)) i) = _
  rw [higham22_algorithm22_3StageII_restrict_eq_lowerProduct_transpose_mulVec]
  rw [higham22_algorithm22_3StageI_restrict_eq_upperProduct_transpose_mulVec]
  rw [higham22Algorithm22_3Factorized, higham22Algorithm22_2FactorProduct,
    Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

theorem higham22Hermite_algorithm22_3_solve
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (b : Fin (n + 1) → ℂ) :
    (higham22HermiteConfluentVandermondeLike
        (fun i : Fin (n + 1) => p i) alpha).mulVec
        (higham22Algorithm22_3 theta beta gamma alpha b) = b := by
  rw [higham22_algorithm22_3_eq_factorized]
  exact higham22Hermite_algorithm22_3Factorized_solve
    hp htheta alpha hcontig b

/-! ### Actual rounded operation graph for Algorithm 22.2 -/

/-- Scalar standard-model interface used by the Chapter 22 rounded graph.
Each primitive returns an actual value and a local relative-error witness; no
factor perturbation or final error conclusion is stored in the interface. -/
structure Higham22ScalarRoundModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  flAdd : ℂ → ℂ → ℂ
  flSub : ℂ → ℂ → ℂ
  flMul : ℂ → ℂ → ℂ
  flDiv : ℂ → ℂ → ℂ
  add_model : ∀ x y, ∃ δ : ℂ, ‖δ‖ ≤ u ∧ flAdd x y = (x + y) * (1 + δ)
  sub_model : ∀ x y, ∃ δ : ℂ, ‖δ‖ ≤ u ∧ flSub x y = (x - y) * (1 + δ)
  mul_model : ∀ x y, ∃ δ : ℂ, ‖δ‖ ≤ u ∧ flMul x y = (x * y) * (1 + δ)
  div_model : ∀ x y, ∃ δ : ℂ, ‖δ‖ ≤ u ∧ flDiv x y = (x / y) * (1 + δ)

/-- The strengthened standard model used in the printed proof of (22.19).
Besides the usual multiplicative relative-error equation, subtraction admits
Higham's equivalent reciprocal form.  This is essential when a rounded node
difference is subsequently used as a divisor: it contributes a bounded
`(1+δ)` factor, exactly as in equations (5.9)--(5.10). -/
structure Higham22SourceRoundModel extends Higham22ScalarRoundModel where
  sub_model_div : ∀ x y, ∃ δ : ℂ, ‖δ‖ ≤ u ∧
    flSub x y = (x - y) / (1 + δ)
  /-- Negation is exact in the source floating-point model. -/
  flSub_zero_left : ∀ x, flSub 0 x = -x
  /-- Adding an exact zero to a stored floating-point value is exact. -/
  flAdd_zero_right : ∀ x, flAdd x 0 = x
  /-- Division of a stored floating-point value by the exact unit is exact. -/
  flDiv_one : ∀ x, flDiv x 1 = x

namespace Higham22ScalarRoundModel

/-- Exact arithmetic is the zero-unit-roundoff instance of the primitive
interface. -/
noncomputable def exact : Higham22ScalarRoundModel where
  u := 0
  u_nonneg := le_rfl
  flAdd := (· + ·)
  flSub := (· - ·)
  flMul := (· * ·)
  flDiv := (· / ·)
  add_model x y := ⟨0, by simp, by simp⟩
  sub_model x y := ⟨0, by simp, by simp⟩
  mul_model x y := ⟨0, by simp, by simp⟩
  div_model x y := ⟨0, by simp, by simp⟩

end Higham22ScalarRoundModel

namespace Higham22SourceRoundModel

/-- Exact arithmetic satisfies both equivalent forms of the source's standard
relative-error model. -/
noncomputable def exact : Higham22SourceRoundModel where
  toHigham22ScalarRoundModel := Higham22ScalarRoundModel.exact
  sub_model_div x y := ⟨0, by simp [Higham22ScalarRoundModel.exact],
    by simp [Higham22ScalarRoundModel.exact]⟩
  flSub_zero_left x := by simp [Higham22ScalarRoundModel.exact]
  flAdd_zero_right x := by simp [Higham22ScalarRoundModel.exact]
  flDiv_one x := by simp [Higham22ScalarRoundModel.exact]

end Higham22SourceRoundModel

/-- One actual rounded Stage-I sweep.  The branch and `clast` graph is
identical to Algorithm 22.2; subtraction and division are explicit primitive
rounding calls. -/
noncomputable def higham22RoundedAlgorithm22_2StageIStep
    (rm : Higham22ScalarRoundModel) (alpha c : ℕ → ℂ) (k : ℕ) : ℕ → ℂ :=
  fun j ↦
    if j ≤ k then c j
    else if alpha j = alpha (j - k - 1) then
      rm.flDiv (c j) (k + 1 : ℂ)
    else
      rm.flDiv
        (rm.flSub (c j) (c (higham22StageILastSaved alpha k (j - 1))))
        (rm.flSub (alpha j) (alpha (j - k - 1)))

/-- The actual recursively rounded Stage-I states. -/
noncomputable def higham22RoundedAlgorithm22_2StageI
    (rm : Higham22ScalarRoundModel) (alpha f : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => f
  | k + 1 => higham22RoundedAlgorithm22_2StageIStep rm alpha
      (higham22RoundedAlgorithm22_2StageI rm alpha f k) k

/-- Finite rounded Stage I used by the end-to-end executor. -/
noncomputable def higham22RoundedAlgorithm22_2StageIFin {N : ℕ}
    (rm : Higham22ScalarRoundModel) (alpha f : Fin N → ℂ) :
    ℕ → (Fin N → ℂ)
  | 0 => f
  | k + 1 => fun i ↦
      higham22RoundedAlgorithm22_2StageIStep rm
        (higham22FinExtend alpha)
        (higham22FinExtend
          (higham22RoundedAlgorithm22_2StageIFin rm alpha f k)) k i

/-- A rounded three-term inner product with the source evaluation order. -/
def higham22RoundedThreeTerm
    (rm : Higham22ScalarRoundModel)
    (x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  rm.flAdd (rm.flAdd x0 (rm.flMul w1 x1)) (rm.flMul w2 x2)

/-- One actual rounded Stage-II `U_k` sweep.  Coefficient differences and
ratios are formed by the same primitive graph that is charged in (22.20). -/
noncomputable def higham22RoundedAlgorithm22_2StageIIStep
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) (alpha : ℕ → ℂ) (n k : ℕ)
    (a : ℕ → ℂ) : ℕ → ℂ :=
  fun i ↦
    if i = k then
      higham22RoundedThreeTerm rm (a k)
        (rm.flSub (beta 0) (alpha k)) (a (k + 1))
        (rm.flDiv (gamma 1) (theta 1)) (a (k + 2))
    else if k < i ∧ i + 2 ≤ n then
      let j := i - k
      higham22RoundedThreeTerm rm
        (rm.flDiv (a i) (theta (j - 1)))
        (rm.flSub (beta j) (alpha k)) (a (i + 1))
        (rm.flDiv (gamma (j + 1)) (theta (j + 1))) (a (i + 2))
    else if i = n - 1 then
      rm.flAdd
        (rm.flDiv (a (n - 1)) (theta (n - k - 2)))
        (rm.flMul (rm.flSub (beta (n - k - 1)) (alpha k)) (a n))
    else if i = n then
      rm.flDiv (a n) (theta (n - k - 1))
    else
      a i

/-- Actual rounded Stage II, applying `U_{n-1},...,U_0` in source order. -/
noncomputable def higham22RoundedAlgorithm22_2StageIIFin
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ} (alpha : Fin (n + 1) → ℂ) :
    ℕ → (Fin (n + 1) → ℂ) → (Fin (n + 1) → ℂ)
  | 0, a => a
  | k + 1, a => higham22RoundedAlgorithm22_2StageIIFin rm
      theta beta gamma alpha k
      (fun i ↦ higham22RoundedAlgorithm22_2StageIIStep rm theta beta gamma
        (higham22FinExtend alpha) n k (higham22FinExtend a) i)

/-- End-to-end actual rounded Algorithm 22.2. -/
noncomputable def higham22RoundedAlgorithm22_2
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  let c := higham22RoundedAlgorithm22_2StageIFin rm alpha f n
  higham22RoundedAlgorithm22_2StageIIFin rm theta beta gamma alpha n c

theorem higham22RoundedAlgorithm22_2StageIStep_exact
    (alpha c : ℕ → ℂ) (k : ℕ) :
    higham22RoundedAlgorithm22_2StageIStep
        Higham22ScalarRoundModel.exact alpha c k =
      higham22Algorithm22_2StageIStep alpha c k := by
  funext j
  simp [higham22RoundedAlgorithm22_2StageIStep,
    Higham22ScalarRoundModel.exact, higham22Algorithm22_2StageIStep]

theorem higham22RoundedAlgorithm22_2StageIFin_exact {N : ℕ}
    (alpha f : Fin N → ℂ) (steps : ℕ) :
    higham22RoundedAlgorithm22_2StageIFin
        Higham22ScalarRoundModel.exact alpha f steps =
      higham22Algorithm22_2StageIFin alpha f steps := by
  induction steps with
  | zero => rfl
  | succ k ih =>
      funext i
      simp only [higham22RoundedAlgorithm22_2StageIFin,
        higham22Algorithm22_2StageIFin]
      rw [ih, higham22RoundedAlgorithm22_2StageIStep_exact]
      rfl

theorem higham22RoundedAlgorithm22_2StageIIStep_exact
    (theta beta gamma alpha : ℕ → ℂ) (n k : ℕ) (a : ℕ → ℂ) :
    higham22RoundedAlgorithm22_2StageIIStep
        Higham22ScalarRoundModel.exact theta beta gamma alpha n k a =
      higham22Algorithm22_2PrintedStageIIStep theta beta gamma alpha n k a := by
  funext i
  simp only [higham22RoundedAlgorithm22_2StageIIStep,
    higham22Algorithm22_2PrintedStageIIStep]
  split_ifs <;> simp [higham22RoundedThreeTerm,
    Higham22ScalarRoundModel.exact]

theorem higham22RoundedAlgorithm22_2StageIIFin_exact
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (steps : ℕ) (a : Fin (n + 1) → ℂ) :
    higham22RoundedAlgorithm22_2StageIIFin
        Higham22ScalarRoundModel.exact theta beta gamma alpha steps a =
      higham22Algorithm22_2StageIIFin theta beta gamma alpha steps a := by
  induction steps generalizing a with
  | zero => rfl
  | succ k ih =>
      simp only [higham22RoundedAlgorithm22_2StageIIFin,
        higham22Algorithm22_2StageIIFin]
      rw [higham22RoundedAlgorithm22_2StageIIStep_exact, ih]
      rfl

/-- Exact arithmetic specialization of the actual rounded graph recovers the
exact finite Algorithm 22.2 executor. -/
theorem higham22RoundedAlgorithm22_2_exact
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    higham22RoundedAlgorithm22_2 Higham22ScalarRoundModel.exact
        theta beta gamma alpha f =
      higham22Algorithm22_2Printed theta beta gamma alpha f := by
  simp only [higham22RoundedAlgorithm22_2, higham22Algorithm22_2Printed]
  rw [higham22RoundedAlgorithm22_2StageIFin_exact,
    higham22RoundedAlgorithm22_2StageIIFin_exact]

namespace Higham22ScalarRoundModel

noncomputable def addError (rm : Higham22ScalarRoundModel) (x y : ℂ) : ℂ :=
  if x + y = 0 then 0 else Classical.choose (rm.add_model x y)

theorem addError_bound (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    ‖rm.addError x y‖ ≤ rm.u :=
  by
    by_cases h : x + y = 0
    · simp [addError, h, rm.u_nonneg]
    · simpa [addError, h] using (Classical.choose_spec (rm.add_model x y)).1

theorem flAdd_eq (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    rm.flAdd x y = (x + y) * (1 + rm.addError x y) :=
  by
    by_cases h : x + y = 0
    · have hs := (Classical.choose_spec (rm.add_model x y)).2
      have hz : rm.flAdd x y = 0 :=
        hs.trans (mul_eq_zero.mpr (Or.inl h))
      simp [addError, h, hz]
    · simpa [addError, h] using (Classical.choose_spec (rm.add_model x y)).2

noncomputable def subError (rm : Higham22ScalarRoundModel) (x y : ℂ) : ℂ :=
  if x - y = 0 then 0 else Classical.choose (rm.sub_model x y)

theorem subError_bound (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    ‖rm.subError x y‖ ≤ rm.u :=
  by
    by_cases h : x - y = 0
    · simp [subError, h, rm.u_nonneg]
    · simpa [subError, h] using (Classical.choose_spec (rm.sub_model x y)).1

theorem flSub_eq (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    rm.flSub x y = (x - y) * (1 + rm.subError x y) :=
  by
    by_cases h : x - y = 0
    · have hs := (Classical.choose_spec (rm.sub_model x y)).2
      have hz : rm.flSub x y = 0 :=
        hs.trans (mul_eq_zero.mpr (Or.inl h))
      simp [subError, h, hz]
    · simpa [subError, h] using (Classical.choose_spec (rm.sub_model x y)).2

noncomputable def mulError (rm : Higham22ScalarRoundModel) (x y : ℂ) : ℂ :=
  if x * y = 0 then 0 else Classical.choose (rm.mul_model x y)

theorem mulError_bound (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    ‖rm.mulError x y‖ ≤ rm.u :=
  by
    by_cases h : x * y = 0
    · simp [mulError, h, rm.u_nonneg]
    · simpa [mulError, h] using (Classical.choose_spec (rm.mul_model x y)).1

theorem flMul_eq (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    rm.flMul x y = (x * y) * (1 + rm.mulError x y) :=
  by
    by_cases h : x * y = 0
    · have hs := (Classical.choose_spec (rm.mul_model x y)).2
      have hz : rm.flMul x y = 0 :=
        hs.trans (mul_eq_zero.mpr (Or.inl h))
      simp [mulError, h, hz]
    · simpa [mulError, h] using (Classical.choose_spec (rm.mul_model x y)).2

noncomputable def divError (rm : Higham22ScalarRoundModel) (x y : ℂ) : ℂ :=
  if x / y = 0 then 0 else Classical.choose (rm.div_model x y)

theorem divError_bound (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    ‖rm.divError x y‖ ≤ rm.u :=
  by
    by_cases h : x / y = 0
    · simp [divError, h, rm.u_nonneg]
    · simpa [divError, h] using (Classical.choose_spec (rm.div_model x y)).1

theorem flDiv_eq (rm : Higham22ScalarRoundModel) (x y : ℂ) :
    rm.flDiv x y = (x / y) * (1 + rm.divError x y) :=
  by
    by_cases h : x / y = 0
    · have hs := (Classical.choose_spec (rm.div_model x y)).2
      have hz : rm.flDiv x y = 0 :=
        hs.trans (mul_eq_zero.mpr (Or.inl h))
      simp [divError, h, hz]
    · simpa [divError, h] using (Classical.choose_spec (rm.div_model x y)).2

end Higham22ScalarRoundModel

namespace Higham22SourceRoundModel

noncomputable def subDivError (rm : Higham22SourceRoundModel) (x y : ℂ) : ℂ :=
  Classical.choose (rm.sub_model_div x y)

theorem subDivError_bound (rm : Higham22SourceRoundModel) (x y : ℂ) :
    ‖rm.subDivError x y‖ ≤ rm.u :=
  (Classical.choose_spec (rm.sub_model_div x y)).1

theorem flSub_eq_div (rm : Higham22SourceRoundModel) (x y : ℂ) :
    rm.flSub x y = (x - y) / (1 + rm.subDivError x y) :=
  (Classical.choose_spec (rm.sub_model_div x y)).2

end Higham22SourceRoundModel

noncomputable def higham22ComplexErrorProd :
    (m : ℕ) → (Fin m → ℂ) → ℂ
  | 0, _ => 1
  | m + 1, δ => (1 + δ 0) * higham22ComplexErrorProd m (fun i => δ i.succ)

theorem higham22ComplexErrorProd_norm_le
    (u : ℝ) (hu : 0 ≤ u) : ∀ (m : ℕ) (δ : Fin m → ℂ),
    (∀ i, ‖δ i‖ ≤ u) →
      ‖higham22ComplexErrorProd m δ‖ ≤ (1 + u) ^ m := by
  intro m
  induction m with
  | zero =>
      intro δ hδ
      simp [higham22ComplexErrorProd]
  | succ m ih =>
      intro δ hδ
      rw [higham22ComplexErrorProd, norm_mul]
      calc
        ‖1 + δ 0‖ * ‖higham22ComplexErrorProd m (fun i => δ i.succ)‖
            ≤ (1 + ‖δ 0‖) * ‖higham22ComplexErrorProd m (fun i => δ i.succ)‖ := by
              simpa using mul_le_mul_of_nonneg_right
                (norm_add_le 1 (δ 0)) (norm_nonneg _)
        _ ≤ (1 + u) * (1 + u) ^ m := by
              apply mul_le_mul
              · linarith [hδ 0]
              · exact ih (fun i => δ i.succ) (fun i => hδ i.succ)
              · exact norm_nonneg _
              · linarith
        _ = (1 + u) ^ (m + 1) := by rw [pow_succ]; ring

theorem higham22ComplexErrorProd_sub_one_norm_le
    (u : ℝ) (hu : 0 ≤ u) : ∀ (m : ℕ) (δ : Fin m → ℂ),
    (∀ i, ‖δ i‖ ≤ u) →
      ‖higham22ComplexErrorProd m δ - 1‖ ≤ (1 + u) ^ m - 1 := by
  intro m
  induction m with
  | zero =>
      intro δ hδ
      simp [higham22ComplexErrorProd]
  | succ m ih =>
      intro δ hδ
      let tail := higham22ComplexErrorProd m (fun i => δ i.succ)
      have hrewrite : (1 + δ 0) * tail - 1 = δ 0 * tail + (tail - 1) := by ring
      rw [higham22ComplexErrorProd, hrewrite]
      calc
        ‖δ 0 * tail + (tail - 1)‖ ≤ ‖δ 0 * tail‖ + ‖tail - 1‖ := norm_add_le _ _
        _ = ‖δ 0‖ * ‖tail‖ + ‖tail - 1‖ := by rw [norm_mul]
        _ ≤ u * (1 + u) ^ m + ((1 + u) ^ m - 1) := by
              apply add_le_add
              · exact mul_le_mul (hδ 0)
                  (higham22ComplexErrorProd_norm_le u hu m _ (fun i => hδ i.succ))
                  (norm_nonneg _) hu
              · exact ih (fun i => δ i.succ) (fun i => hδ i.succ)
        _ = (1 + u) ^ (m + 1) - 1 := by rw [pow_succ]; ring

theorem higham22_one_add_ne_zero_of_norm_lt_one {δ : ℂ}
    (hδ : ‖δ‖ < 1) : 1 + δ ≠ 0 := by
  intro hzero
  have hδeq : δ = -1 := by
    apply eq_neg_of_add_eq_zero_left
    simpa [add_comm] using hzero
  rw [hδeq] at hδ
  norm_num at hδ

/-! ### Operational division nonbreakdown for rounded Algorithm 22.2 -/

/-- A nonzero exact difference remains nonzero after the actual rounded
subtraction primitive.  This is the key operational fact needed before that
rounded difference is passed to `flDiv` in the distinct-node branch. -/
theorem higham22_flSub_ne_zero_of_ne
    (rm : Higham22ScalarRoundModel) (huround : rm.u < 1)
    {x y : ℂ} (hxy : x ≠ y) :
    rm.flSub x y ≠ 0 := by
  rw [Higham22ScalarRoundModel.flSub_eq]
  exact mul_ne_zero (sub_ne_zero.mpr hxy)
    (higham22_one_add_ne_zero_of_norm_lt_one
      ((rm.subError_bound x y).trans_lt huround))

/-- The denominator selected by one active Stage-I row of the literal rounded
executor.  Equal nodes use the exact positive integer `k+1`; distinct nodes
use the actually rounded node difference. -/
noncomputable def higham22RoundedAlgorithm22_2StageIDenominator
    (rm : Higham22ScalarRoundModel) (alpha : ℕ → ℂ) (k j : ℕ) : ℂ :=
  if alpha j = alpha (j - k - 1) then
    (k + 1 : ℂ)
  else
    rm.flSub (alpha j) (alpha (j - k - 1))

/-- Every Stage-I denominator selected by the actual rounded branch graph is
nonzero when `u < 1`. -/
theorem higham22RoundedAlgorithm22_2StageIDenominator_ne_zero
    (rm : Higham22ScalarRoundModel) (huround : rm.u < 1)
    (alpha : ℕ → ℂ) (k j : ℕ) :
    higham22RoundedAlgorithm22_2StageIDenominator rm alpha k j ≠ 0 := by
  by_cases heq : alpha j = alpha (j - k - 1)
  · simp only [higham22RoundedAlgorithm22_2StageIDenominator, heq, if_true]
    exact_mod_cast Nat.succ_ne_zero k
  · simp only [higham22RoundedAlgorithm22_2StageIDenominator, heq, if_false]
    exact higham22_flSub_ne_zero_of_ne rm huround heq

/-- Complete inventory of the exact recurrence-coefficient denominators that
can be supplied to `flDiv` by one Stage-II sweep.  The two `interior` fields
correspond to `theta (j-1)` and `theta (j+1)` with `j=i-k`; the last two fields
are the printed terminal-row denominators. -/
structure Higham22RoundedStageIIDivisorsNonzero
    (theta : ℕ → ℂ) (n k : ℕ) : Prop where
  thetaOne : theta 1 ≠ 0
  thetaInteriorLeft : ∀ i, theta (i - k - 1) ≠ 0
  thetaInteriorRight : ∀ i, theta (i - k + 1) ≠ 0
  thetaTerminalPrev : theta (n - k - 2) ≠ 0
  thetaTerminalLast : theta (n - k - 1) ≠ 0

/-- A nowhere-zero recurrence coefficient sequence discharges the complete
Stage-II divisor inventory. -/
theorem higham22RoundedStageIIDivisorsNonzero_of_theta
    {theta : ℕ → ℂ} (htheta : ∀ j, theta j ≠ 0) (n k : ℕ) :
    Higham22RoundedStageIIDivisorsNonzero theta n k where
  thetaOne := htheta 1
  thetaInteriorLeft i := htheta (i - k - 1)
  thetaInteriorRight i := htheta (i - k + 1)
  thetaTerminalPrev := htheta (n - k - 2)
  thetaTerminalLast := htheta (n - k - 1)

/-- End-to-end nonbreakdown certificate for every division reached by the
finite rounded Algorithm 22.2 executor. -/
def Higham22RoundedAlgorithm22_2DivisionsNonzero
    (rm : Higham22ScalarRoundModel) (theta : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) : Prop :=
  (∀ k, k < n → ∀ i : Fin (n + 1),
      higham22RoundedAlgorithm22_2StageIDenominator rm
        (higham22FinExtend alpha) k i ≠ 0) ∧
    (∀ k, k < n → Higham22RoundedStageIIDivisorsNonzero theta n k)

/-- The source smallness condition and the printed `theta_j ≠ 0` assumption
derive operational nonbreakdown; it is not assumed as an opaque executor
precondition. -/
theorem higham22RoundedAlgorithm22_2_divisions_nonzero
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta : ℕ → ℂ) (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :
    Higham22RoundedAlgorithm22_2DivisionsNonzero
      rm.toHigham22ScalarRoundModel theta alpha := by
  constructor
  · intro k _hk i
    exact higham22RoundedAlgorithm22_2StageIDenominator_ne_zero
      rm.toHigham22ScalarRoundModel huround (higham22FinExtend alpha) k i
  · intro k _hk
    exact higham22RoundedStageIIDivisorsNonzero_of_theta htheta n k

noncomputable def higham22StageIRowMultiplier {N : ℕ}
    (rm : Higham22SourceRoundModel) (alpha c : Fin N → ℂ) (k : ℕ)
    (i : Fin N) : ℂ :=
  let base := rm.toHigham22ScalarRoundModel
  let a := higham22FinExtend alpha
  let x := higham22FinExtend c
  let saved := higham22StageILastSaved a k ((i : ℕ) - 1)
  if (i : ℕ) ≤ k then 1
  else if a i = a ((i : ℕ) - k - 1) then
    1 + base.divError (x i) (k + 1 : ℂ)
  else
    (1 + base.subError (x i) (x saved)) *
      (1 + rm.subDivError (a i) (a ((i : ℕ) - k - 1))) *
      (1 + base.divError
        (base.flSub (x i) (x saved))
        (base.flSub (a i) (a ((i : ℕ) - k - 1))))

noncomputable def higham22RoundedStageILowerFactor {N : ℕ}
    (rm : Higham22SourceRoundModel) (alpha c : Fin N → ℂ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i j => higham22StageIRowMultiplier rm alpha c k i *
    higham22StageILowerFactor alpha k i j

theorem higham22_roundedStageILowerFactor_mulVec {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) :
    (higham22RoundedStageILowerFactor rm alpha c k).mulVec c =
      fun i : Fin N => higham22RoundedAlgorithm22_2StageIStep
        rm.toHigham22ScalarRoundModel (higham22FinExtend alpha)
          (higham22FinExtend c) k i := by
  funext i
  let base := rm.toHigham22ScalarRoundModel
  let a := higham22FinExtend alpha
  let x := higham22FinExtend c
  let saved := higham22StageILastSaved a k ((i : ℕ) - 1)
  have hrow :
      (higham22RoundedStageILowerFactor rm alpha c k).mulVec c i =
        higham22StageIRowMultiplier rm alpha c k i *
          (higham22StageILowerFactor alpha k).mulVec c i := by
    simp only [higham22RoundedStageILowerFactor, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  rw [hrow, higham22_stageILowerFactor_mulVec]
  change higham22StageIRowMultiplier rm alpha c k i *
      higham22Algorithm22_2StageIStep a x k i =
    higham22RoundedAlgorithm22_2StageIStep base a x k i
  by_cases hik : (i : ℕ) ≤ k
  · simp [higham22StageIRowMultiplier, higham22Algorithm22_2StageIStep,
      higham22RoundedAlgorithm22_2StageIStep, hik]
  · by_cases heq : a i = a ((i : ℕ) - k - 1)
    · simp only [higham22StageIRowMultiplier,
        higham22Algorithm22_2StageIStep,
        higham22RoundedAlgorithm22_2StageIStep, hik, if_false, heq, if_true,
        base, a, x]
      rw [Higham22ScalarRoundModel.flDiv_eq]
      ring
    · have hden : a i - a ((i : ℕ) - k - 1) ≠ 0 := sub_ne_zero.mpr heq
      have hsubdiv :
          1 + rm.subDivError (a i) (a ((i : ℕ) - k - 1)) ≠ 0 := by
        apply higham22_one_add_ne_zero_of_norm_lt_one
        exact (rm.subDivError_bound _ _).trans_lt huround
      simp only [higham22StageIRowMultiplier, hik, if_false, heq,
        higham22Algorithm22_2StageIStep,
        higham22RoundedAlgorithm22_2StageIStep, base, a, x, saved]
      rw [Higham22ScalarRoundModel.flDiv_eq,
        Higham22ScalarRoundModel.flSub_eq,
        Higham22SourceRoundModel.flSub_eq_div]
      field_simp [hden, hsubdiv]
      <;> ring

theorem higham22_stageIRowMultiplier_sub_one_norm_le {N : ℕ}
    (rm : Higham22SourceRoundModel)
    (alpha c : Fin N → ℂ) (k : ℕ) (i : Fin N) :
    ‖higham22StageIRowMultiplier rm alpha c k i - 1‖ ≤
      (1 + rm.u) ^ 3 - 1 := by
  let base := rm.toHigham22ScalarRoundModel
  let a := higham22FinExtend alpha
  let x := higham22FinExtend c
  let saved := higham22StageILastSaved a k ((i : ℕ) - 1)
  by_cases hik : (i : ℕ) ≤ k
  · have hbase : 1 ≤ 1 + rm.u := by linarith [rm.u_nonneg]
    have hp : 1 ≤ (1 + rm.u) ^ 3 := one_le_pow₀ hbase
    simpa [higham22StageIRowMultiplier, hik] using (sub_nonneg.mpr hp)
  · by_cases heq : a i = a ((i : ℕ) - k - 1)
    · simp only [higham22StageIRowMultiplier, hik, if_false, heq, if_true,
        base, a, x, add_sub_cancel_left]
      apply (base.divError_bound _ _).trans
      have hu := rm.u_nonneg
      nlinarith [sq_nonneg rm.u, mul_nonneg hu (sq_nonneg rm.u)]
    · let δ0 := base.subError (x i) (x saved)
      let δ1 := rm.subDivError (a i) (a ((i : ℕ) - k - 1))
      let δ2 := base.divError
        (base.flSub (x i) (x saved))
        (base.flSub (a i) (a ((i : ℕ) - k - 1)))
      have hδ : ∀ r : Fin 3, ‖![δ0, δ1, δ2] r‖ ≤ rm.u := by
        intro r
        fin_cases r
        · exact base.subError_bound _ _
        · exact rm.subDivError_bound _ _
        · exact base.divError_bound _ _
      have hprod := higham22ComplexErrorProd_sub_one_norm_le
        rm.u rm.u_nonneg 3 ![δ0, δ1, δ2] hδ
      have heq' : alpha i ≠
          higham22FinExtend alpha ((i : ℕ) - k - 1) := by
        simpa [a] using heq
      simpa [higham22StageIRowMultiplier, hik, heq, base, a, x, saved,
        heq', δ0, δ1, δ2, higham22ComplexErrorProd, mul_assoc] using hprod

noncomputable def higham22RoundedStageIDelta {N : ℕ}
    (rm : Higham22SourceRoundModel) (alpha c : Fin N → ℂ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  higham22RoundedStageILowerFactor rm alpha c k -
    higham22StageILowerFactor alpha k

/-- Equation (22.19), produced from the actual rounded Stage-I operation
graph.  The perturbation matrix is extracted from the primitive rounding
witnesses and is not supplied as an assumption. -/
theorem higham22_eq22_19_actual_stageI {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) :
    (higham22StageILowerFactor alpha k +
        higham22RoundedStageIDelta rm alpha c k).mulVec c =
      (fun i : Fin N => higham22RoundedAlgorithm22_2StageIStep
        rm.toHigham22ScalarRoundModel (higham22FinExtend alpha)
          (higham22FinExtend c) k i) ∧
    ∀ i j,
      ‖higham22RoundedStageIDelta rm alpha c k i j‖ ≤
        ((1 + rm.u) ^ 3 - 1) * ‖higham22StageILowerFactor alpha k i j‖ := by
  constructor
  · rw [show higham22StageILowerFactor alpha k +
        higham22RoundedStageIDelta rm alpha c k =
      higham22RoundedStageILowerFactor rm alpha c k by
        ext i j
        simp [higham22RoundedStageIDelta]]
    exact higham22_roundedStageILowerFactor_mulVec rm huround alpha c k
  · intro i j
    change ‖higham22StageIRowMultiplier rm alpha c k i *
        higham22StageILowerFactor alpha k i j -
      higham22StageILowerFactor alpha k i j‖ ≤ _
    rw [show higham22StageIRowMultiplier rm alpha c k i *
          higham22StageILowerFactor alpha k i j -
        higham22StageILowerFactor alpha k i j =
          (higham22StageIRowMultiplier rm alpha c k i - 1) *
            higham22StageILowerFactor alpha k i j by ring, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (higham22_stageIRowMultiplier_sub_one_norm_le rm alpha c k i)
      (norm_nonneg _)

noncomputable def higham22ThreeTermMul1
    (rm : Higham22ScalarRoundModel) (w1 x1 : ℂ) : ℂ :=
  rm.flMul w1 x1

noncomputable def higham22ThreeTermMul2
    (rm : Higham22ScalarRoundModel) (w2 x2 : ℂ) : ℂ :=
  rm.flMul w2 x2

noncomputable def higham22ThreeTermSum1
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 : ℂ) : ℂ :=
  rm.flAdd x0 (higham22ThreeTermMul1 rm w1 x1)

noncomputable def higham22ThreeTermEta0
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  (1 + rm.addError x0 (higham22ThreeTermMul1 rm w1 x1)) *
    (1 + rm.addError
      (higham22ThreeTermSum1 rm x0 w1 x1)
      (higham22ThreeTermMul2 rm w2 x2))

noncomputable def higham22ThreeTermEta1
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  (1 + rm.mulError w1 x1) *
    (1 + rm.addError x0 (higham22ThreeTermMul1 rm w1 x1)) *
    (1 + rm.addError
      (higham22ThreeTermSum1 rm x0 w1 x1)
      (higham22ThreeTermMul2 rm w2 x2))

noncomputable def higham22ThreeTermEta2
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  (1 + rm.mulError w2 x2) *
    (1 + rm.addError
      (higham22ThreeTermSum1 rm x0 w1 x1)
      (higham22ThreeTermMul2 rm w2 x2))

theorem higham22RoundedThreeTerm_linearized
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) :
    higham22RoundedThreeTerm rm x0 w1 x1 w2 x2 =
      higham22ThreeTermEta0 rm x0 w1 x1 w2 x2 * x0 +
      higham22ThreeTermEta1 rm x0 w1 x1 w2 x2 * w1 * x1 +
      higham22ThreeTermEta2 rm x0 w1 x1 w2 x2 * w2 * x2 := by
  rw [higham22RoundedThreeTerm,
    Higham22ScalarRoundModel.flAdd_eq,
    Higham22ScalarRoundModel.flAdd_eq,
    Higham22ScalarRoundModel.flMul_eq,
    Higham22ScalarRoundModel.flMul_eq]
  simp only [higham22ThreeTermEta0, higham22ThreeTermEta1,
    higham22ThreeTermEta2, higham22ThreeTermMul1,
    higham22ThreeTermMul2, higham22ThreeTermSum1]
  rw [Higham22ScalarRoundModel.flMul_eq,
    Higham22ScalarRoundModel.flMul_eq,
    Higham22ScalarRoundModel.flAdd_eq]
  ring

theorem higham22ThreeTermEta0_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) :
    ‖higham22ThreeTermEta0 rm x0 w1 x1 w2 x2 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ0 := rm.addError x0 (higham22ThreeTermMul1 rm w1 x1)
  let δ1 := rm.addError
    (higham22ThreeTermSum1 rm x0 w1 x1)
    (higham22ThreeTermMul2 rm w2 x2)
  have hδ : ∀ r : Fin 4, ‖![δ0, δ1, 0, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact rm.addError_bound _ _
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![δ0, δ1, 0, 0] hδ
  simpa [higham22ThreeTermEta0, δ0, δ1,
    higham22ComplexErrorProd, mul_assoc] using h

theorem higham22ThreeTermEta1_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) :
    ‖higham22ThreeTermEta1 rm x0 w1 x1 w2 x2 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ0 := rm.mulError w1 x1
  let δ1 := rm.addError x0 (higham22ThreeTermMul1 rm w1 x1)
  let δ2 := rm.addError
    (higham22ThreeTermSum1 rm x0 w1 x1)
    (higham22ThreeTermMul2 rm w2 x2)
  have hδ : ∀ r : Fin 4, ‖![δ0, δ1, δ2, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact rm.mulError_bound _ _
    · exact rm.addError_bound _ _
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![δ0, δ1, δ2, 0] hδ
  simpa [higham22ThreeTermEta1, δ0, δ1, δ2,
    higham22ComplexErrorProd, mul_assoc] using h

theorem higham22ThreeTermEta2_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (x0 w1 x1 w2 x2 : ℂ) :
    ‖higham22ThreeTermEta2 rm x0 w1 x1 w2 x2 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ0 := rm.mulError w2 x2
  let δ1 := rm.addError
    (higham22ThreeTermSum1 rm x0 w1 x1)
    (higham22ThreeTermMul2 rm w2 x2)
  have hδ : ∀ r : Fin 4, ‖![δ0, δ1, 0, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact rm.mulError_bound _ _
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![δ0, δ1, 0, 0] hδ
  simpa [higham22ThreeTermEta2, δ0, δ1,
    higham22ComplexErrorProd, mul_assoc] using h

noncomputable def higham22ThreeTermTotalEta0
    (rm : Higham22ScalarRoundModel) (ε0 x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  (1 + ε0) * higham22ThreeTermEta0 rm x0 w1 x1 w2 x2

noncomputable def higham22ThreeTermTotalEta1
    (rm : Higham22ScalarRoundModel) (ε1 x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  (1 + ε1) * higham22ThreeTermEta1 rm x0 w1 x1 w2 x2

noncomputable def higham22ThreeTermTotalEta2
    (rm : Higham22ScalarRoundModel) (ε2 x0 w1 x1 w2 x2 : ℂ) : ℂ :=
  (1 + ε2) * higham22ThreeTermEta2 rm x0 w1 x1 w2 x2

theorem higham22ThreeTermTotalEta0_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (ε0 x0 w1 x1 w2 x2 : ℂ)
    (hε0 : ‖ε0‖ ≤ rm.u) :
    ‖higham22ThreeTermTotalEta0 rm ε0 x0 w1 x1 w2 x2 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ1 := rm.addError x0 (higham22ThreeTermMul1 rm w1 x1)
  let δ2 := rm.addError
    (higham22ThreeTermSum1 rm x0 w1 x1)
    (higham22ThreeTermMul2 rm w2 x2)
  have hδ : ∀ r : Fin 4, ‖![ε0, δ1, δ2, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact hε0
    · exact rm.addError_bound _ _
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![ε0, δ1, δ2, 0] hδ
  simpa [higham22ThreeTermTotalEta0, higham22ThreeTermEta0,
    δ1, δ2, higham22ComplexErrorProd, mul_assoc] using h

theorem higham22ThreeTermTotalEta1_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (ε1 x0 w1 x1 w2 x2 : ℂ)
    (hε1 : ‖ε1‖ ≤ rm.u) :
    ‖higham22ThreeTermTotalEta1 rm ε1 x0 w1 x1 w2 x2 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ1 := rm.mulError w1 x1
  let δ2 := rm.addError x0 (higham22ThreeTermMul1 rm w1 x1)
  let δ3 := rm.addError
    (higham22ThreeTermSum1 rm x0 w1 x1)
    (higham22ThreeTermMul2 rm w2 x2)
  have hδ : ∀ r : Fin 4, ‖![ε1, δ1, δ2, δ3] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact hε1
    · exact rm.mulError_bound _ _
    · exact rm.addError_bound _ _
    · exact rm.addError_bound _ _
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![ε1, δ1, δ2, δ3] hδ
  simpa [higham22ThreeTermTotalEta1, higham22ThreeTermEta1,
    δ1, δ2, δ3, higham22ComplexErrorProd, mul_assoc] using h

theorem higham22ThreeTermTotalEta2_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (ε2 x0 w1 x1 w2 x2 : ℂ)
    (hε2 : ‖ε2‖ ≤ rm.u) :
    ‖higham22ThreeTermTotalEta2 rm ε2 x0 w1 x1 w2 x2 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ1 := rm.mulError w2 x2
  let δ2 := rm.addError
    (higham22ThreeTermSum1 rm x0 w1 x1)
    (higham22ThreeTermMul2 rm w2 x2)
  have hδ : ∀ r : Fin 4, ‖![ε2, δ1, δ2, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact hε2
    · exact rm.mulError_bound _ _
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![ε2, δ1, δ2, 0] hδ
  simpa [higham22ThreeTermTotalEta2, higham22ThreeTermEta2,
    δ1, δ2, higham22ComplexErrorProd, mul_assoc] using h

noncomputable def higham22TwoTermTotalEta0
    (rm : Higham22ScalarRoundModel) (ε0 x0 w x1 : ℂ) : ℂ :=
  (1 + ε0) * (1 + rm.addError x0 (rm.flMul w x1))

noncomputable def higham22TwoTermTotalEta1
    (rm : Higham22ScalarRoundModel) (ε1 x0 w x1 : ℂ) : ℂ :=
  (1 + ε1) * (1 + rm.mulError w x1) *
    (1 + rm.addError x0 (rm.flMul w x1))

theorem higham22TwoTermTotalEta0_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (ε0 x0 w x1 : ℂ)
    (hε0 : ‖ε0‖ ≤ rm.u) :
    ‖higham22TwoTermTotalEta0 rm ε0 x0 w x1 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ1 := rm.addError x0 (rm.flMul w x1)
  have hδ : ∀ r : Fin 4, ‖![ε0, δ1, 0, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact hε0
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![ε0, δ1, 0, 0] hδ
  simpa [higham22TwoTermTotalEta0, δ1,
    higham22ComplexErrorProd, mul_assoc] using h

theorem higham22TwoTermTotalEta1_sub_one_norm_le
    (rm : Higham22ScalarRoundModel) (ε1 x0 w x1 : ℂ)
    (hε1 : ‖ε1‖ ≤ rm.u) :
    ‖higham22TwoTermTotalEta1 rm ε1 x0 w x1 - 1‖ ≤
      (1 + rm.u) ^ 4 - 1 := by
  let δ1 := rm.mulError w x1
  let δ2 := rm.addError x0 (rm.flMul w x1)
  have hδ : ∀ r : Fin 4, ‖![ε1, δ1, δ2, 0] r‖ ≤ rm.u := by
    intro r
    fin_cases r
    · exact hε1
    · exact rm.mulError_bound _ _
    · exact rm.addError_bound _ _
    · simpa using rm.u_nonneg
  have h := higham22ComplexErrorProd_sub_one_norm_le
    rm.u rm.u_nonneg 4 ![ε1, δ1, δ2, 0] hδ
  simpa [higham22TwoTermTotalEta1, δ1, δ2,
    higham22ComplexErrorProd, mul_assoc] using h

theorem higham22RoundedThreeTerm_precomputed_linearized
    (rm : Higham22ScalarRoundModel)
    (x0hat w1hat x1 w2hat x2 x0 w1 w2 ε0 ε1 ε2 : ℂ)
    (hx0 : x0hat = x0 * (1 + ε0))
    (hw1 : w1hat = w1 * (1 + ε1))
    (hw2 : w2hat = w2 * (1 + ε2)) :
    higham22RoundedThreeTerm rm x0hat w1hat x1 w2hat x2 =
      higham22ThreeTermTotalEta0 rm ε0 x0hat w1hat x1 w2hat x2 * x0 +
      higham22ThreeTermTotalEta1 rm ε1 x0hat w1hat x1 w2hat x2 * w1 * x1 +
      higham22ThreeTermTotalEta2 rm ε2 x0hat w1hat x1 w2hat x2 * w2 * x2 := by
  let η0 := higham22ThreeTermEta0 rm x0hat w1hat x1 w2hat x2
  let η1 := higham22ThreeTermEta1 rm x0hat w1hat x1 w2hat x2
  let η2 := higham22ThreeTermEta2 rm x0hat w1hat x1 w2hat x2
  have hlin := higham22RoundedThreeTerm_linearized rm x0hat w1hat x1 w2hat x2
  change higham22RoundedThreeTerm rm x0hat w1hat x1 w2hat x2 =
    η0 * x0hat + η1 * w1hat * x1 + η2 * w2hat * x2 at hlin
  change higham22RoundedThreeTerm rm x0hat w1hat x1 w2hat x2 =
    (1 + ε0) * η0 * x0 + (1 + ε1) * η1 * w1 * x1 +
      (1 + ε2) * η2 * w2 * x2
  rw [hlin, hx0, hw1, hw2]
  ring

theorem higham22RoundedTwoTerm_precomputed_linearized
    (rm : Higham22ScalarRoundModel)
    (x0hat what x1 x0 w ε0 ε1 : ℂ)
    (hx0 : x0hat = x0 * (1 + ε0))
    (hw : what = w * (1 + ε1)) :
    rm.flAdd x0hat (rm.flMul what x1) =
      higham22TwoTermTotalEta0 rm ε0 x0hat what x1 * x0 +
      higham22TwoTermTotalEta1 rm ε1 x0hat what x1 * w * x1 := by
  let m := rm.flMul what x1
  let δm := rm.mulError what x1
  let δa := rm.addError x0hat m
  have hm : m = (what * x1) * (1 + δm) := by
    exact rm.flMul_eq what x1
  have ha : rm.flAdd x0hat m = (x0hat + m) * (1 + δa) := by
    exact rm.flAdd_eq x0hat m
  change rm.flAdd x0hat m =
    (1 + ε0) * (1 + δa) * x0 +
      (1 + ε1) * (1 + δm) * (1 + δa) * w * x1
  rw [ha, hm, hx0, hw]
  ring

noncomputable def higham22StageIILinearizedStep
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma alpha : ℕ → ℂ) (n k : ℕ) (a z : ℕ → ℂ) : ℕ → ℂ :=
  fun i =>
    if i = k then
      let x0 := a k
      let w1 := rm.flSub (beta 0) (alpha k)
      let x1 := a (k + 1)
      let w2 := rm.flDiv (gamma 1) (theta 1)
      let x2 := a (k + 2)
      higham22ThreeTermTotalEta0 rm 0 x0 w1 x1 w2 x2 * z k +
        higham22ThreeTermTotalEta1 rm
            (rm.subError (beta 0) (alpha k)) x0 w1 x1 w2 x2 *
          (beta 0 - alpha k) * z (k + 1) +
        higham22ThreeTermTotalEta2 rm
            (rm.divError (gamma 1) (theta 1)) x0 w1 x1 w2 x2 *
          (gamma 1 / theta 1) * z (k + 2)
    else if k < i ∧ i + 2 ≤ n then
      let j := i - k
      let x0 := rm.flDiv (a i) (theta (j - 1))
      let w1 := rm.flSub (beta j) (alpha k)
      let x1 := a (i + 1)
      let w2 := rm.flDiv (gamma (j + 1)) (theta (j + 1))
      let x2 := a (i + 2)
      higham22ThreeTermTotalEta0 rm
            (rm.divError (a i) (theta (j - 1))) x0 w1 x1 w2 x2 *
          (z i / theta (j - 1)) +
        higham22ThreeTermTotalEta1 rm
            (rm.subError (beta j) (alpha k)) x0 w1 x1 w2 x2 *
          (beta j - alpha k) * z (i + 1) +
        higham22ThreeTermTotalEta2 rm
            (rm.divError (gamma (j + 1)) (theta (j + 1))) x0 w1 x1 w2 x2 *
          (gamma (j + 1) / theta (j + 1)) * z (i + 2)
    else if i = n - 1 then
      let x0 := rm.flDiv (a (n - 1)) (theta (n - k - 2))
      let w := rm.flSub (beta (n - k - 1)) (alpha k)
      higham22TwoTermTotalEta0 rm
            (rm.divError (a (n - 1)) (theta (n - k - 2))) x0 w (a n) *
          (z (n - 1) / theta (n - k - 2)) +
        higham22TwoTermTotalEta1 rm
            (rm.subError (beta (n - k - 1)) (alpha k)) x0 w (a n) *
          (beta (n - k - 1) - alpha k) * z n
    else if i = n then
      (1 + rm.divError (a n) (theta (n - k - 1))) *
        (z n / theta (n - k - 1))
    else
      z i

theorem higham22StageIILinearizedStep_actual
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma alpha : ℕ → ℂ) (n k : ℕ) (a : ℕ → ℂ) :
    higham22StageIILinearizedStep rm theta beta gamma alpha n k a a =
      higham22RoundedAlgorithm22_2StageIIStep rm theta beta gamma alpha n k a := by
  funext i
  simp only [higham22StageIILinearizedStep,
    higham22RoundedAlgorithm22_2StageIIStep]
  split_ifs with h0 h1 h2 h3
  · symm
    apply higham22RoundedThreeTerm_precomputed_linearized
    · ring
    · exact rm.flSub_eq _ _
    · exact rm.flDiv_eq _ _
  · symm
    apply higham22RoundedThreeTerm_precomputed_linearized
    · exact rm.flDiv_eq _ _
    · exact rm.flSub_eq _ _
    · exact rm.flDiv_eq _ _
  · symm
    apply higham22RoundedTwoTerm_precomputed_linearized
    · exact rm.flDiv_eq _ _
    · exact rm.flSub_eq _ _
  · rw [Higham22ScalarRoundModel.flDiv_eq]
    ring
  · rfl

noncomputable def higham22RoundedStageIIUpperLinear
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun z := fun i => higham22StageIILinearizedStep rm theta beta gamma
    (higham22FinExtend alpha) n k (higham22FinExtend a)
      (higham22FinExtend z) i
  map_add' z w := by
    funext i
    rw [higham22FinExtend_add]
    simp only [higham22StageIILinearizedStep, Pi.add_apply]
    split_ifs <;> ring
  map_smul' s z := by
    funext i
    rw [higham22FinExtend_smul]
    simp only [higham22StageIILinearizedStep, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    split_ifs <;> ring

noncomputable def higham22RoundedStageIIUpperFactor
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  LinearMap.toMatrix' (higham22RoundedStageIIUpperLinear
    rm theta beta gamma alpha a k)

theorem higham22_roundedStageIIUpperFactor_mulVec
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    (higham22RoundedStageIIUpperFactor rm theta beta gamma alpha a k).mulVec a =
      fun i : Fin (n + 1) => higham22RoundedAlgorithm22_2StageIIStep rm
        theta beta gamma (higham22FinExtend alpha) n k
          (higham22FinExtend a) i := by
  simp only [higham22RoundedStageIIUpperFactor,
    LinearMap.toMatrix'_mulVec,
    higham22RoundedStageIIUpperLinear]
  change (fun i : Fin (n + 1) =>
      higham22StageIILinearizedStep rm theta beta gamma
        (higham22FinExtend alpha) n k (higham22FinExtend a)
          (higham22FinExtend a) i) = _
  funext i
  exact congrFun (higham22StageIILinearizedStep_actual rm theta beta gamma
    (higham22FinExtend alpha) n k (higham22FinExtend a)) i

theorem higham22_eta_mul_sub_self_norm_le
    (η c : ℂ) (q : ℝ) (hη : ‖η - 1‖ ≤ q) :
    ‖η * c - c‖ ≤ q * ‖c‖ := by
  rw [show η * c - c = (η - 1) * c by ring, norm_mul]
  exact mul_le_mul_of_nonneg_right hη (norm_nonneg c)

noncomputable def higham22RoundedStageIIDelta
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  higham22RoundedStageIIUpperFactor rm theta beta gamma alpha a k -
    higham22StageIIUpperFactor theta beta gamma alpha k

theorem higham22_roundedStageIIDelta_bound
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) (hk : k < n) :
    ∀ i j,
      ‖higham22RoundedStageIIDelta rm theta beta gamma alpha a k i j‖ ≤
        ((1 + rm.u) ^ 4 - 1) *
          ‖higham22StageIIUpperFactor theta beta gamma alpha k i j‖ := by
  intro i j
  let z : ℕ → ℂ := higham22FinExtend (Pi.single j 1)
  have hz (m : ℕ) : z m = if m = (j : ℕ) then 1 else 0 := by
    simpa [z] using higham22FinExtend_single j (1 : ℂ) m
  rw [higham22RoundedStageIIDelta, Matrix.sub_apply,
    higham22RoundedStageIIUpperFactor, higham22StageIIUpperFactor,
    LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply]
  change ‖higham22StageIILinearizedStep rm theta beta gamma
      (higham22FinExtend alpha) n k (higham22FinExtend a) z i -
      higham22Algorithm22_2PrintedStageIIStep theta beta gamma
        (higham22FinExtend alpha) n k z i‖ ≤
    ((1 + rm.u) ^ 4 - 1) *
      ‖higham22Algorithm22_2PrintedStageIIStep theta beta gamma
        (higham22FinExtend alpha) n k z i‖
  simp only [higham22StageIILinearizedStep,
    higham22Algorithm22_2PrintedStageIIStep]
  split_ifs with hi hinter hlast hn
  · by_cases hj0 : (j : ℕ) = k
    · have hj1 : k + 1 ≠ (j : ℕ) := by omega
      have hj2 : k + 2 ≠ (j : ℕ) := by omega
      rw [hz k, hz (k + 1), hz (k + 2)]
      simp [hj0.symm, hj1, hj2]
      apply higham22ThreeTermTotalEta0_sub_one_norm_le
      simpa using rm.u_nonneg
    · by_cases hj1 : (j : ℕ) = k + 1
      · have hj0' : k ≠ (j : ℕ) := by omega
        have hj2 : k + 2 ≠ (j : ℕ) := by omega
        rw [hz k, hz (k + 1), hz (k + 2)]
        simp [hj0', hj1.symm, hj2]
        apply higham22_eta_mul_sub_self_norm_le
        exact higham22ThreeTermTotalEta1_sub_one_norm_le rm _ _ _ _ _ _
          (rm.subError_bound _ _)
      · by_cases hj2 : (j : ℕ) = k + 2
        · have hj0' : k ≠ (j : ℕ) := by omega
          have hj1' : k + 1 ≠ (j : ℕ) := by omega
          rw [hz k, hz (k + 1), hz (k + 2)]
          simp [hj0', hj1', hj2.symm]
          rw [← norm_div]
          apply higham22_eta_mul_sub_self_norm_le
          exact higham22ThreeTermTotalEta2_sub_one_norm_le rm _ _ _ _ _ _
            (rm.divError_bound _ _)
        · have hj0' : k ≠ (j : ℕ) := Ne.symm hj0
          have hj1' : k + 1 ≠ (j : ℕ) := Ne.symm hj1
          have hj2' : k + 2 ≠ (j : ℕ) := Ne.symm hj2
          rw [hz k, hz (k + 1), hz (k + 2)]
          simp [hj0', hj1', hj2']
  · by_cases hj0 : (j : ℕ) = (i : ℕ)
    · have hj1 : (i : ℕ) + 1 ≠ (j : ℕ) := by omega
      have hj2 : (i : ℕ) + 2 ≠ (j : ℕ) := by omega
      rw [hz i, hz ((i : ℕ) + 1), hz ((i : ℕ) + 2)]
      simp [hj0.symm, hj1, hj2]
      rw [← norm_inv]
      apply higham22_eta_mul_sub_self_norm_le
      exact higham22ThreeTermTotalEta0_sub_one_norm_le rm _ _ _ _ _ _
        (rm.divError_bound _ _)
    · by_cases hj1 : (j : ℕ) = (i : ℕ) + 1
      · have hj0' : (i : ℕ) ≠ (j : ℕ) := by omega
        have hj2 : (i : ℕ) + 2 ≠ (j : ℕ) := by omega
        rw [hz i, hz ((i : ℕ) + 1), hz ((i : ℕ) + 2)]
        simp [hj0', hj1.symm, hj2]
        apply higham22_eta_mul_sub_self_norm_le
        exact higham22ThreeTermTotalEta1_sub_one_norm_le rm _ _ _ _ _ _
          (rm.subError_bound _ _)
      · by_cases hj2 : (j : ℕ) = (i : ℕ) + 2
        · have hj0' : (i : ℕ) ≠ (j : ℕ) := by omega
          have hj1' : (i : ℕ) + 1 ≠ (j : ℕ) := by omega
          rw [hz i, hz ((i : ℕ) + 1), hz ((i : ℕ) + 2)]
          simp [hj0', hj1', hj2.symm]
          rw [← norm_div]
          apply higham22_eta_mul_sub_self_norm_le
          exact higham22ThreeTermTotalEta2_sub_one_norm_le rm _ _ _ _ _ _
            (rm.divError_bound _ _)
        · have hj0' : (i : ℕ) ≠ (j : ℕ) := Ne.symm hj0
          have hj1' : (i : ℕ) + 1 ≠ (j : ℕ) := Ne.symm hj1
          have hj2' : (i : ℕ) + 2 ≠ (j : ℕ) := Ne.symm hj2
          rw [hz i, hz ((i : ℕ) + 1), hz ((i : ℕ) + 2)]
          simp [hj0', hj1', hj2']
  · by_cases hj0 : (j : ℕ) = n - 1
    · have hnpos : 0 < n := by omega
      have hj1 : n ≠ (j : ℕ) := by omega
      have hnprev : n ≠ n - 1 := by omega
      rw [hz (n - 1), hz n]
      simp [hj0.symm, hj1, hnprev]
      rw [← norm_inv]
      apply higham22_eta_mul_sub_self_norm_le
      exact higham22TwoTermTotalEta0_sub_one_norm_le rm _ _ _ _
        (rm.divError_bound _ _)
    · by_cases hj1 : (j : ℕ) = n
      · have hnpos : 0 < n := by omega
        have hj0' : n - 1 ≠ (j : ℕ) := by omega
        have hprevn : n - 1 ≠ n := by omega
        have hjprev : (j : ℕ) - 1 ≠ (j : ℕ) := by omega
        rw [hz (n - 1), hz n]
        simp [hj0', hj1.symm, hprevn, hjprev]
        apply higham22_eta_mul_sub_self_norm_le
        exact higham22TwoTermTotalEta1_sub_one_norm_le rm _ _ _ _
          (rm.subError_bound _ _)
      · have hj0' : n - 1 ≠ (j : ℕ) := Ne.symm hj0
        have hj1' : n ≠ (j : ℕ) := Ne.symm hj1
        rw [hz (n - 1), hz n]
        simp [hj0', hj1']
  · by_cases hj : (j : ℕ) = n
    · rw [hz n]
      simp [hj.symm]
      have hq : rm.u ≤ (1 + rm.u) ^ 4 - 1 := by
        have hu := rm.u_nonneg
        nlinarith [sq_nonneg rm.u, mul_nonneg hu (sq_nonneg rm.u)]
      rw [← norm_inv]
      apply higham22_eta_mul_sub_self_norm_le
      simpa using (rm.divError_bound _ _).trans hq
    · have hj' : n ≠ (j : ℕ) := Ne.symm hj
      rw [hz n]
      simp [hj']
  · simp
    exact mul_nonneg
      (sub_nonneg.mpr (one_le_pow₀ (by linarith [rm.u_nonneg])))
      (norm_nonneg _)

/-- Equation (22.20), produced from the actual rounded Stage-II operation
graph.  The perturbation matrix is extracted from the primitive rounding
witnesses and is not supplied as an assumption. -/
theorem higham22_eq22_20_actual_stageII
    (rm : Higham22ScalarRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (k : ℕ) (hk : k < n) :
    (higham22StageIIUpperFactor theta beta gamma alpha k +
        higham22RoundedStageIIDelta rm theta beta gamma alpha a k).mulVec a =
      (fun i : Fin (n + 1) => higham22RoundedAlgorithm22_2StageIIStep rm
        theta beta gamma (higham22FinExtend alpha) n k
          (higham22FinExtend a) i) ∧
    ∀ i j,
      ‖higham22RoundedStageIIDelta rm theta beta gamma alpha a k i j‖ ≤
        ((1 + rm.u) ^ 4 - 1) *
          ‖higham22StageIIUpperFactor theta beta gamma alpha k i j‖ := by
  constructor
  · rw [show higham22StageIIUpperFactor theta beta gamma alpha k +
        higham22RoundedStageIIDelta rm theta beta gamma alpha a k =
      higham22RoundedStageIIUpperFactor rm theta beta gamma alpha a k by
        ext i j
        simp [higham22RoundedStageIIDelta]]
    exact higham22_roundedStageIIUpperFactor_mulVec
      rm theta beta gamma alpha a k
  · exact higham22_roundedStageIIDelta_bound
      rm theta beta gamma alpha a k hk

/-! ### Theorem 22.4 factor-product kernel -/

/-- The exact coefficient `c(n,u)` from Theorem 22.4. -/
noncomputable def higham22Theorem22_4Coefficient (n : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ (7 * n) - 1

/-- The local relative budgets in (22.20) and (22.19), in source product
order: the `n` upper factors cost four operations each and the `n` lower
factors cost three. -/
noncomputable def higham22FactorRelativeBudget (u : ℝ) (n : ℕ) :
    Fin (n + n) → ℝ :=
  Fin.append (fun _ : Fin n ↦ (1 + u) ^ 4 - 1)
    (fun _ : Fin n ↦ (1 + u) ^ 3 - 1)

theorem higham22_scalarSeqProd_eq_fin_prod (m : ℕ) (a : Fin m → ℝ) :
    scalarSeqProd m a = ∏ i : Fin m, a i := by
  induction m with
  | zero => simp [scalarSeqProd]
  | succ m ih =>
      rw [scalarSeqProd, Fin.prod_univ_succ]
      rw [ih]

/-- The `4n+3n=7n` operation count underlying `c(n,u)`. -/
theorem higham22_factorRelativeBudget_product (u : ℝ) (n : ℕ) :
    scalarSeqProd (n + n) (fun r ↦ 1 + higham22FactorRelativeBudget u n r) =
      (1 + u) ^ (7 * n) := by
  rw [higham22_scalarSeqProd_eq_fin_prod]
  rw [show (∏ r : Fin (n + n), (1 + higham22FactorRelativeBudget u n r)) =
      (∏ r : Fin (n + n), Fin.append
        (fun _ : Fin n ↦ (1 + u) ^ 4)
        (fun _ : Fin n ↦ (1 + u) ^ 3) r) by
    apply Finset.prod_congr rfl
    intro r _hr
    refine Fin.addCases ?_ ?_ r
    · intro i
      rw [higham22FactorRelativeBudget, Fin.append_left, Fin.append_left]
      ring
    · intro i
      rw [higham22FactorRelativeBudget, Fin.append_right, Fin.append_right]
      ring]
  rw [fin_prod_append]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul, ← pow_mul, ← pow_add]
  congr 1
  omega

/-- Theorem 22.4's Lemma 3.8 step for a real specialization of the exact
factor sequence.  Unlike the removed target-bearing certificate, the premises
are only the local equations (22.19)--(22.20); the complete product error and
the sharp `(1+u)^(7n)-1` coefficient are derived here. -/
theorem higham22_theorem22_4_factor_product_bound
    (dim n : ℕ)
    (X deltaX : Fin (n + n) → Fin dim → Fin dim → ℝ)
    (u : ℝ) (hu : 0 ≤ u)
    (hdeltaX : ∀ r i j,
      |deltaX r i j| ≤ higham22FactorRelativeBudget u n r * |X r i j|) :
    ∀ i j,
      |matSeqProd dim (n + n)
          (fun r i j ↦ X r i j + deltaX r i j) i j -
        matSeqProd dim (n + n) X i j| ≤
      higham22Theorem22_4Coefficient n u *
        matSeqProd dim (n + n) (fun r ↦ absMatrix dim (X r)) i j := by
  have hscale : ∀ r, 0 ≤ higham22FactorRelativeBudget u n r := by
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro k
      rw [higham22FactorRelativeBudget, Fin.append_left]
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith : 1 ≤ 1 + u))
    · intro k
      rw [higham22FactorRelativeBudget, Fin.append_right]
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith : 1 ≤ 1 + u))
  intro i j
  have h := matSeqProd_componentwise_perturbation_bound dim (n + n)
    X deltaX (higham22FactorRelativeBudget u n) hscale hdeltaX i j
  rw [higham22_factorRelativeBudget_product] at h
  simpa [higham22Theorem22_4Coefficient] using h

/-- Left-to-right product of complex square matrices. -/
noncomputable def higham22ComplexMatSeqProd (d : ℕ) : (m : ℕ) →
    (Fin m → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) ℂ
  | 0, _ => 1
  | m + 1, X => X 0 * higham22ComplexMatSeqProd d m (fun r => X r.succ)

/-- Entrywise norm of a complex matrix, as a nonnegative real matrix. -/
noncomputable def higham22NormMatrix {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Fin d → Fin d → ℝ :=
  fun i j => ‖A i j‖

/-- Complex analogue of the absolute-value half of Higham's Lemma 3.8. -/
theorem higham22ComplexMatSeqProd_norm_perturbed_le
    (d m : ℕ) (X ΔX : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (δ : Fin m → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, ‖ΔX r i j‖ ≤ δ r * ‖X r i j‖) :
    ∀ i j,
      ‖higham22ComplexMatSeqProd d m (fun r => X r + ΔX r) i j‖ ≤
        scalarSeqProd m (fun r => 1 + δ r) *
          matSeqProd d m (fun r => higham22NormMatrix (X r)) i j := by
  induction m with
  | zero =>
      intro i j
      simp only [higham22ComplexMatSeqProd, scalarSeqProd, matSeqProd,
        Matrix.one_apply, one_mul]
      unfold idMatrix
      split <;> simp
  | succ m ih =>
      intro i j
      let tailPert : Fin m → Matrix (Fin d) (Fin d) ℂ :=
        fun r => X r.succ + ΔX r.succ
      let tailAbs : Fin m → Fin d → Fin d → ℝ :=
        fun r => higham22NormMatrix (X r.succ)
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      have htail : ∀ k j,
          ‖higham22ComplexMatSeqProd d m tailPert k j‖ ≤
            tailScale * matSeqProd d m tailAbs k j := by
        intro k j
        simpa [tailPert, tailAbs, tailScale] using
          ih (fun r => X r.succ) (fun r => ΔX r.succ)
            (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ) k j
      have hhead : ∀ k,
          ‖X 0 i k + ΔX 0 i k‖ ≤ (1 + δ 0) * ‖X 0 i k‖ := by
        intro k
        calc
          ‖X 0 i k + ΔX 0 i k‖ ≤ ‖X 0 i k‖ + ‖ΔX 0 i k‖ := norm_add_le _ _
          _ ≤ ‖X 0 i k‖ + δ 0 * ‖X 0 i k‖ := by
            linarith [hΔ 0 i k]
          _ = (1 + δ 0) * ‖X 0 i k‖ := by ring
      unfold higham22ComplexMatSeqProd
      rw [Matrix.mul_apply]
      calc
        ‖∑ k : Fin d,
            (X 0 i k + ΔX 0 i k) *
              higham22ComplexMatSeqProd d m tailPert k j‖
            ≤ ∑ k : Fin d,
                ‖(X 0 i k + ΔX 0 i k) *
                  higham22ComplexMatSeqProd d m tailPert k j‖ :=
              norm_sum_le _ _
        _ = ∑ k : Fin d,
              ‖X 0 i k + ΔX 0 i k‖ *
                ‖higham22ComplexMatSeqProd d m tailPert k j‖ := by
              apply Finset.sum_congr rfl
              intro k _
              rw [norm_mul]
        _ ≤ ∑ k : Fin d,
              ((1 + δ 0) * ‖X 0 i k‖) *
                (tailScale * matSeqProd d m tailAbs k j) := by
              apply Finset.sum_le_sum
              intro k _
              exact mul_le_mul (hhead k) (htail k j)
                (norm_nonneg _) (mul_nonneg (by linarith [hδ 0]) (norm_nonneg _))
        _ = (1 + δ 0) * tailScale *
              (∑ k : Fin d, higham22NormMatrix (X 0) i k *
                matSeqProd d m tailAbs k j) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro k _
              simp [higham22NormMatrix]
              ring
        _ = scalarSeqProd (m + 1) (fun r => 1 + δ r) *
              matSeqProd d (m + 1)
                (fun r => higham22NormMatrix (X r)) i j := by
              change (1 + δ 0) * tailScale *
                    (∑ k : Fin d, higham22NormMatrix (X 0) i k *
                      matSeqProd d m tailAbs k j) =
                ((1 + δ 0) * tailScale) *
                    (∑ k : Fin d, higham22NormMatrix (X 0) i k *
                      matSeqProd d m tailAbs k j)
              ring

/-- Complex componentwise form of Higham's Lemma 3.8. -/
theorem higham22ComplexMatSeqProd_componentwise_perturbation_bound
    (d m : ℕ) (X ΔX : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (δ : Fin m → ℝ) (hδ : ∀ r, 0 ≤ δ r)
    (hΔ : ∀ r i j, ‖ΔX r i j‖ ≤ δ r * ‖X r i j‖) :
    ∀ i j,
      ‖higham22ComplexMatSeqProd d m (fun r => X r + ΔX r) i j -
        higham22ComplexMatSeqProd d m X i j‖ ≤
        (scalarSeqProd m (fun r => 1 + δ r) - 1) *
          matSeqProd d m (fun r => higham22NormMatrix (X r)) i j := by
  induction m with
  | zero =>
      intro i j
      simp [higham22ComplexMatSeqProd, scalarSeqProd, matSeqProd]
  | succ m ih =>
      intro i j
      let tailX : Fin m → Matrix (Fin d) (Fin d) ℂ := fun r => X r.succ
      let tailΔ : Fin m → Matrix (Fin d) (Fin d) ℂ := fun r => ΔX r.succ
      let tailPert : Fin m → Matrix (Fin d) (Fin d) ℂ :=
        fun r => X r.succ + ΔX r.succ
      let tailAbs : Fin m → Fin d → Fin d → ℝ :=
        fun r => higham22NormMatrix (X r.succ)
      let tailScale : ℝ := scalarSeqProd m (fun r => 1 + δ r.succ)
      have htail_abs : ∀ k j,
          ‖higham22ComplexMatSeqProd d m tailPert k j‖ ≤
            tailScale * matSeqProd d m tailAbs k j := by
        intro k j
        simpa [tailX, tailΔ, tailPert, tailAbs, tailScale] using
          higham22ComplexMatSeqProd_norm_perturbed_le d m tailX tailΔ
            (fun r => δ r.succ) (fun r => hδ r.succ)
              (fun r => hΔ r.succ) k j
      have htail_err : ∀ k j,
          ‖higham22ComplexMatSeqProd d m tailPert k j -
              higham22ComplexMatSeqProd d m tailX k j‖ ≤
            (tailScale - 1) * matSeqProd d m tailAbs k j := by
        intro k j
        simpa [tailX, tailΔ, tailPert, tailAbs, tailScale] using
          ih tailX tailΔ (fun r => δ r.succ) (fun r => hδ r.succ)
            (fun r => hΔ r.succ) k j
      have htailScale_one : 1 ≤ tailScale := by
        exact one_le_scalarSeqProd m (fun r => 1 + δ r.succ)
          (fun r => by linarith [hδ r.succ])
      have hterm : ∀ k : Fin d,
          ‖(X 0 i k + ΔX 0 i k) *
                higham22ComplexMatSeqProd d m tailPert k j -
              X 0 i k * higham22ComplexMatSeqProd d m tailX k j‖ ≤
            ‖ΔX 0 i k‖ *
                ‖higham22ComplexMatSeqProd d m tailPert k j‖ +
              ‖X 0 i k‖ *
                ‖higham22ComplexMatSeqProd d m tailPert k j -
                  higham22ComplexMatSeqProd d m tailX k j‖ := by
        intro k
        rw [show (X 0 i k + ΔX 0 i k) *
                higham22ComplexMatSeqProd d m tailPert k j -
              X 0 i k * higham22ComplexMatSeqProd d m tailX k j =
            ΔX 0 i k * higham22ComplexMatSeqProd d m tailPert k j +
              X 0 i k *
                (higham22ComplexMatSeqProd d m tailPert k j -
                  higham22ComplexMatSeqProd d m tailX k j) by ring]
        calc
          ‖ΔX 0 i k * higham22ComplexMatSeqProd d m tailPert k j +
              X 0 i k *
                (higham22ComplexMatSeqProd d m tailPert k j -
                  higham22ComplexMatSeqProd d m tailX k j)‖ ≤
              ‖ΔX 0 i k * higham22ComplexMatSeqProd d m tailPert k j‖ +
                ‖X 0 i k *
                  (higham22ComplexMatSeqProd d m tailPert k j -
                    higham22ComplexMatSeqProd d m tailX k j)‖ := norm_add_le _ _
          _ = _ := by rw [norm_mul, norm_mul]
      calc
        ‖higham22ComplexMatSeqProd d (m + 1)
              (fun r => X r + ΔX r) i j -
            higham22ComplexMatSeqProd d (m + 1) X i j‖ ≤
            ∑ k : Fin d,
              ‖(X 0 i k + ΔX 0 i k) *
                    higham22ComplexMatSeqProd d m tailPert k j -
                  X 0 i k *
                    higham22ComplexMatSeqProd d m tailX k j‖ := by
              simp only [higham22ComplexMatSeqProd, Matrix.add_apply,
                Matrix.mul_apply]
              rw [← Finset.sum_sub_distrib]
              exact norm_sum_le _ _
        _ ≤ ∑ k : Fin d,
              (‖ΔX 0 i k‖ *
                  ‖higham22ComplexMatSeqProd d m tailPert k j‖ +
                ‖X 0 i k‖ *
                  ‖higham22ComplexMatSeqProd d m tailPert k j -
                    higham22ComplexMatSeqProd d m tailX k j‖) := by
              apply Finset.sum_le_sum
              intro k _
              exact hterm k
        _ = (∑ k : Fin d,
              ‖ΔX 0 i k‖ *
                ‖higham22ComplexMatSeqProd d m tailPert k j‖) +
            ∑ k : Fin d,
              ‖X 0 i k‖ *
                ‖higham22ComplexMatSeqProd d m tailPert k j -
                  higham22ComplexMatSeqProd d m tailX k j‖ := by
              rw [Finset.sum_add_distrib]
        _ ≤ (∑ k : Fin d,
              (δ 0 * ‖X 0 i k‖) *
                (tailScale * matSeqProd d m tailAbs k j)) +
            ∑ k : Fin d,
              ‖X 0 i k‖ *
                ((tailScale - 1) * matSeqProd d m tailAbs k j) := by
              apply add_le_add <;> apply Finset.sum_le_sum <;> intro k _
              · calc
                  ‖ΔX 0 i k‖ *
                      ‖higham22ComplexMatSeqProd d m tailPert k j‖ ≤
                    (δ 0 * ‖X 0 i k‖) *
                      ‖higham22ComplexMatSeqProd d m tailPert k j‖ :=
                        mul_le_mul_of_nonneg_right (hΔ 0 i k) (norm_nonneg _)
                  _ ≤ (δ 0 * ‖X 0 i k‖) *
                      (tailScale * matSeqProd d m tailAbs k j) :=
                        mul_le_mul_of_nonneg_left (htail_abs k j)
                          (mul_nonneg (hδ 0) (norm_nonneg _))
              · exact mul_le_mul_of_nonneg_left (htail_err k j) (norm_nonneg _)
        _ = (δ 0 * tailScale + (tailScale - 1)) *
              (∑ k : Fin d, higham22NormMatrix (X 0) i k *
                matSeqProd d m tailAbs k j) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro k _
              simp [higham22NormMatrix]
              ring
        _ = (scalarSeqProd (m + 1) (fun r => 1 + δ r) - 1) *
              matSeqProd d (m + 1)
                (fun r => higham22NormMatrix (X r)) i j := by
              change (δ 0 * tailScale + (tailScale - 1)) *
                    (∑ k : Fin d, higham22NormMatrix (X 0) i k *
                      matSeqProd d m tailAbs k j) =
                (((1 + δ 0) * tailScale) - 1) *
                    (∑ k : Fin d, higham22NormMatrix (X 0) i k *
                      matSeqProd d m tailAbs k j)
              ring

theorem higham22ComplexMatSeqProd_cons {d m : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ)
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    higham22ComplexMatSeqProd d (m + 1) (Fin.cons A X) =
      A * higham22ComplexMatSeqProd d m X := by
  rfl

theorem higham22ComplexMatSeqProd_snoc {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    higham22ComplexMatSeqProd d (m + 1) (Fin.snoc X A) =
      higham22ComplexMatSeqProd d m X * A := by
  induction m with
  | zero =>
      change (Fin.snoc X A : Fin 1 → Matrix (Fin d) (Fin d) ℂ)
          (Fin.last 0) * 1 = 1 * A
      rw [Fin.snoc_last]
      simp
  | succ m ih =>
      rw [higham22ComplexMatSeqProd]
      have hhead : (Fin.snoc X A :
          Fin (m + 2) → Matrix (Fin d) (Fin d) ℂ) (0 : Fin (m + 2)) =
          X (0 : Fin (m + 1)) := by
        rw [show (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc by rfl,
          Fin.snoc_castSucc]
      have htail : (fun r : Fin (m + 1) =>
          (Fin.snoc X A : Fin (m + 2) → Matrix (Fin d) (Fin d) ℂ) r.succ) =
          (Fin.snoc (fun r : Fin m => X r.succ) A :
            Fin (m + 1) → Matrix (Fin d) (Fin d) ℂ) := by
        funext r
        refine Fin.lastCases ?_ (fun q => ?_) r
        · rw [show (Fin.last m).succ = Fin.last (m + 1) by
              apply Fin.ext
              simp,
            Fin.snoc_last, Fin.snoc_last]
        · rw [show q.castSucc.succ = q.succ.castSucc by
              apply Fin.ext
              rfl,
            Fin.snoc_castSucc, Fin.snoc_castSucc]
      rw [hhead, htail, ih]
      change X 0 *
          (higham22ComplexMatSeqProd d m (fun r => X r.succ) * A) =
        (X 0 * higham22ComplexMatSeqProd d m (fun r => X r.succ)) * A
      exact (Matrix.mul_assoc _ _ _).symm

theorem higham22ComplexMatSeqProd_append {d m n : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (Y : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    higham22ComplexMatSeqProd d (m + n) (Fin.append X Y) =
      higham22ComplexMatSeqProd d m X *
        higham22ComplexMatSeqProd d n Y := by
  induction n with
  | zero =>
      have hxy : Fin.append X Y = X := by
        funext r
        change Fin.append X Y (Fin.castAdd 0 r) = X r
        exact Fin.append_left X Y r
      rw [hxy]
      simp [higham22ComplexMatSeqProd]
  | succ n ih =>
      let Y0 : Fin n → Matrix (Fin d) (Fin d) ℂ :=
        fun r => Y r.castSucc
      let A : Matrix (Fin d) (Fin d) ℂ := Y (Fin.last n)
      have hy : Y = Fin.snoc Y0 A := by
        funext r
        refine Fin.lastCases ?_ (fun q => ?_) r <;> simp [Y0, A]
      have happ : Fin.append X (Fin.snoc Y0 A) =
          (Fin.snoc (Fin.append X Y0) A :
            Fin (m + n + 1) → Matrix (Fin d) (Fin d) ℂ) := by
        funext r
        refine Fin.lastCases ?_ (fun q => ?_) r
        · calc
            Fin.append X (Fin.snoc Y0 A) (Fin.last (m + n)) =
                Fin.append X (Fin.snoc Y0 A)
                  (Fin.natAdd m (Fin.last n)) := by
                    congr 2
            _ = (Fin.snoc Y0 A :
                  Fin (n + 1) → Matrix (Fin d) (Fin d) ℂ) (Fin.last n) :=
                  Fin.append_right X (Fin.snoc Y0 A) (Fin.last n)
            _ = A := @Fin.snoc_last n
              (fun _ : Fin (n + 1) => Matrix (Fin d) (Fin d) ℂ) A Y0
            _ = (Fin.snoc (Fin.append X Y0) A :
                  Fin (m + n + 1) → Matrix (Fin d) (Fin d) ℂ)
                    (Fin.last (m + n)) := by
                  have hlast :
                      (Fin.snoc (Fin.append X Y0) A :
                        Fin (m + n + 1) → Matrix (Fin d) (Fin d) ℂ)
                          (Fin.last (m + n)) = A :=
                    @Fin.snoc_last (m + n)
                      (fun _ : Fin (m + n + 1) =>
                        Matrix (Fin d) (Fin d) ℂ) A (Fin.append X Y0)
                  exact hlast.symm
        · refine Fin.addCases ?_ ?_ q
          · intro k
            rw [Fin.snoc_castSucc]
            rw [show (Fin.castAdd n k).castSucc = Fin.castAdd (n + 1) k by
              apply Fin.ext
              rfl]
            rw [Fin.append_left, Fin.append_left]
          · intro k
            rw [Fin.snoc_castSucc, Fin.append_right]
            rw [show (Fin.natAdd m k).castSucc = Fin.natAdd m k.castSucc by
              apply Fin.ext
              rfl]
            rw [Fin.append_right, Fin.snoc_castSucc]
      rw [hy, happ]
      change higham22ComplexMatSeqProd d ((m + n) + 1)
          (Fin.snoc (Fin.append X Y0) A) =
        higham22ComplexMatSeqProd d m X *
          higham22ComplexMatSeqProd d (n + 1) (Fin.snoc Y0 A)
      rw [higham22ComplexMatSeqProd_snoc,
        ih, higham22ComplexMatSeqProd_snoc, Matrix.mul_assoc]

/-- Exact lower factors in product order `L_{s-1},...,L_0`. -/
noncomputable def higham22ExactStageILowerFactorSeq {N : ℕ}
    (alpha : Fin N → ℂ) : (s : ℕ) → Fin s → Matrix (Fin N) (Fin N) ℂ
  | 0 => Fin.elim0
  | k + 1 => Fin.cons (higham22StageILowerFactor alpha k)
      (higham22ExactStageILowerFactorSeq alpha k)

/-- Actual rounded lower factors, with each factor extracted at the state on
which its primitive Stage-I sweep acts. -/
noncomputable def higham22RoundedStageILowerFactorSeq {N : ℕ}
    (rm : Higham22SourceRoundModel) (alpha f : Fin N → ℂ) :
    (s : ℕ) → Fin s → Matrix (Fin N) (Fin N) ℂ
  | 0 => Fin.elim0
  | k + 1 =>
      Fin.cons
        (higham22RoundedStageILowerFactor rm alpha
          (higham22RoundedAlgorithm22_2StageIFin
            rm.toHigham22ScalarRoundModel alpha f k) k)
        (higham22RoundedStageILowerFactorSeq rm alpha f k)

theorem higham22_exactStageILowerFactorSeq_product {N : ℕ}
    (alpha : Fin N → ℂ) (s : ℕ) :
    higham22ComplexMatSeqProd N s
        (higham22ExactStageILowerFactorSeq alpha s) =
      higham22StageILowerProduct alpha s := by
  induction s with
  | zero => rfl
  | succ k ih =>
      rw [higham22ExactStageILowerFactorSeq,
        higham22ComplexMatSeqProd_cons, higham22StageILowerProduct, ih]

theorem higham22_roundedStageILowerFactorSeq_mulVec {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha f : Fin N → ℂ) (s : ℕ) :
    (higham22ComplexMatSeqProd N s
      (higham22RoundedStageILowerFactorSeq rm alpha f s)).mulVec f =
        higham22RoundedAlgorithm22_2StageIFin
          rm.toHigham22ScalarRoundModel alpha f s := by
  induction s with
  | zero =>
      simp [higham22ComplexMatSeqProd,
        higham22RoundedAlgorithm22_2StageIFin]
  | succ k ih =>
      rw [higham22RoundedStageILowerFactorSeq,
        higham22ComplexMatSeqProd_cons,
        ← Matrix.mulVec_mulVec, ih]
      rw [show higham22RoundedStageILowerFactor rm alpha
            (higham22RoundedAlgorithm22_2StageIFin
              rm.toHigham22ScalarRoundModel alpha f k) k =
          higham22StageILowerFactor alpha k +
            higham22RoundedStageIDelta rm alpha
              (higham22RoundedAlgorithm22_2StageIFin
                rm.toHigham22ScalarRoundModel alpha f k) k by
        ext i j
        simp [higham22RoundedStageIDelta]]
      simpa [higham22RoundedAlgorithm22_2StageIFin] using
        (higham22_eq22_19_actual_stageI rm huround alpha
          (higham22RoundedAlgorithm22_2StageIFin
            rm.toHigham22ScalarRoundModel alpha f k) k).1

theorem higham22_roundedStageILowerFactorSeq_bound {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha f : Fin N → ℂ) (s : ℕ) :
    ∀ r i j,
      ‖higham22RoundedStageILowerFactorSeq rm alpha f s r i j -
          higham22ExactStageILowerFactorSeq alpha s r i j‖ ≤
        ((1 + rm.u) ^ 3 - 1) *
          ‖higham22ExactStageILowerFactorSeq alpha s r i j‖ := by
  induction s with
  | zero => intro r; exact Fin.elim0 r
  | succ k ih =>
      intro r
      refine Fin.cases ?_ (fun q => ?_) r
      · intro i j
        simpa [higham22RoundedStageILowerFactorSeq,
          higham22ExactStageILowerFactorSeq,
          higham22RoundedStageIDelta] using
          (higham22_eq22_19_actual_stageI rm huround alpha
            (higham22RoundedAlgorithm22_2StageIFin
              rm.toHigham22ScalarRoundModel alpha f k) k).2 i j
      · intro i j
        simpa [higham22RoundedStageILowerFactorSeq,
          higham22ExactStageILowerFactorSeq] using ih q i j

/-- Exact upper factors in product order `U_0,...,U_{s-1}`. -/
noncomputable def higham22ExactStageIIUpperFactorSeq
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :
    (s : ℕ) → Fin s → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0 => Fin.elim0
  | k + 1 => Fin.snoc (higham22ExactStageIIUpperFactorSeq
      theta beta gamma alpha k)
      (higham22StageIIUpperFactor theta beta gamma alpha k)

/-- Actual rounded upper factors.  Recursion follows the descending execution
order; `Fin.snoc` records the factors in matrix-product order. -/
noncomputable def higham22RoundedStageIIUpperFactorSeq
    (rm : Higham22ScalarRoundModel) (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :
    (s : ℕ) → (Fin (n + 1) → ℂ) →
      Fin s → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ
  | 0, _ => Fin.elim0
  | k + 1, a =>
      let b : Fin (n + 1) → ℂ := fun i =>
        higham22RoundedAlgorithm22_2StageIIStep rm theta beta gamma
          (higham22FinExtend alpha) n k (higham22FinExtend a) i
      Fin.snoc (higham22RoundedStageIIUpperFactorSeq rm theta beta gamma
        alpha k b)
        (higham22RoundedStageIIUpperFactor rm theta beta gamma alpha a k)

theorem higham22_exactStageIIUpperFactorSeq_product
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (s : ℕ) :
    higham22ComplexMatSeqProd (n + 1) s
        (higham22ExactStageIIUpperFactorSeq theta beta gamma alpha s) =
      higham22StageIIUpperProduct theta beta gamma alpha s := by
  induction s with
  | zero => rfl
  | succ k ih =>
      rw [higham22ExactStageIIUpperFactorSeq,
        higham22ComplexMatSeqProd_snoc, higham22StageIIUpperProduct, ih]

theorem higham22_roundedStageIIUpperFactorSeq_mulVec
    (rm : Higham22ScalarRoundModel) (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (s : ℕ) (hs : s ≤ n) :
    (higham22ComplexMatSeqProd (n + 1) s
      (higham22RoundedStageIIUpperFactorSeq rm theta beta gamma alpha s a)).mulVec a =
        higham22RoundedAlgorithm22_2StageIIFin rm theta beta gamma alpha s a := by
  induction s generalizing a with
  | zero =>
      simp [higham22ComplexMatSeqProd,
        higham22RoundedAlgorithm22_2StageIIFin]
  | succ k ih =>
      let b : Fin (n + 1) → ℂ := fun i =>
        higham22RoundedAlgorithm22_2StageIIStep rm theta beta gamma
          (higham22FinExtend alpha) n k (higham22FinExtend a) i
      rw [higham22RoundedStageIIUpperFactorSeq,
        higham22ComplexMatSeqProd_snoc,
        ← Matrix.mulVec_mulVec]
      have hWa :
          (higham22RoundedStageIIUpperFactor rm theta beta gamma alpha a k).mulVec a = b := by
        rw [show higham22RoundedStageIIUpperFactor rm theta beta gamma alpha a k =
            higham22StageIIUpperFactor theta beta gamma alpha k +
              higham22RoundedStageIIDelta rm theta beta gamma alpha a k by
          ext i j
          simp [higham22RoundedStageIIDelta]]
        exact (higham22_eq22_20_actual_stageII rm theta beta gamma alpha a k
          (by omega)).1
      rw [hWa]
      change (higham22ComplexMatSeqProd (n + 1) k
        (higham22RoundedStageIIUpperFactorSeq rm theta beta gamma alpha k b)).mulVec b = _
      rw [ih b (by omega)]
      rfl

theorem higham22_roundedStageIIUpperFactorSeq_bound
    (rm : Higham22ScalarRoundModel) (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha a : Fin (n + 1) → ℂ) (s : ℕ) (hs : s ≤ n) :
    ∀ r i j,
      ‖higham22RoundedStageIIUpperFactorSeq rm theta beta gamma alpha s a r i j -
          higham22ExactStageIIUpperFactorSeq theta beta gamma alpha s r i j‖ ≤
        ((1 + rm.u) ^ 4 - 1) *
          ‖higham22ExactStageIIUpperFactorSeq theta beta gamma alpha s r i j‖ := by
  induction s generalizing a with
  | zero => intro r; exact Fin.elim0 r
  | succ k ih =>
      let b : Fin (n + 1) → ℂ := fun i =>
        higham22RoundedAlgorithm22_2StageIIStep rm theta beta gamma
          (higham22FinExtend alpha) n k (higham22FinExtend a) i
      intro r
      refine Fin.lastCases ?_ (fun q => ?_) r
      · intro i j
        simpa [higham22RoundedStageIIUpperFactorSeq,
          higham22ExactStageIIUpperFactorSeq,
          higham22RoundedStageIIDelta] using
          (higham22_eq22_20_actual_stageII rm theta beta gamma alpha a k
            (by omega)).2 i j
      · intro i j
        simpa [higham22RoundedStageIIUpperFactorSeq,
          higham22ExactStageIIUpperFactorSeq, b] using
          ih b (by omega) q i j

/-- The exact `2n` factor sequence in the product order of (22.17). -/
noncomputable def higham22ExactAlgorithm22_2FactorSeq
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :
    Fin (n + n) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Fin.append
    (higham22ExactStageIIUpperFactorSeq theta beta gamma alpha n)
    (higham22ExactStageILowerFactorSeq alpha n)

/-- The actual `2n` rounded factor sequence.  Every matrix is extracted from
the primitive-operation state on which its sweep was executed. -/
noncomputable def higham22RoundedAlgorithm22_2FactorSeq
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    Fin (n + n) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  let c := higham22RoundedAlgorithm22_2StageIFin
    rm.toHigham22ScalarRoundModel alpha f n
  Fin.append
    (higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
      theta beta gamma alpha n c)
    (higham22RoundedStageILowerFactorSeq rm alpha f n)

noncomputable def higham22RoundedAlgorithm22_2FactorDelta
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    Fin (n + n) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun r => higham22RoundedAlgorithm22_2FactorSeq rm theta beta gamma alpha f r -
    higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r

theorem higham22_exactAlgorithm22_2FactorSeq_product
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :
    higham22ComplexMatSeqProd (n + 1) (n + n)
        (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha) =
      higham22Algorithm22_2FactorProduct theta beta gamma alpha := by
  rw [higham22ExactAlgorithm22_2FactorSeq,
    higham22ComplexMatSeqProd_append,
    higham22_exactStageIIUpperFactorSeq_product,
    higham22_exactStageILowerFactorSeq_product]
  rfl

/-- Equation (22.21): the product of the actual rounded factors computes the
actual rounded Algorithm 22.2 output. -/
theorem higham22_eq22_21_actual_rounded_factor_product
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    (higham22ComplexMatSeqProd (n + 1) (n + n)
      (higham22RoundedAlgorithm22_2FactorSeq rm theta beta gamma alpha f)).mulVec f =
        higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
          theta beta gamma alpha f := by
  let c := higham22RoundedAlgorithm22_2StageIFin
    rm.toHigham22ScalarRoundModel alpha f n
  rw [higham22RoundedAlgorithm22_2FactorSeq,
    higham22ComplexMatSeqProd_append,
    ← Matrix.mulVec_mulVec,
    higham22_roundedStageILowerFactorSeq_mulVec rm huround]
  change (higham22ComplexMatSeqProd (n + 1) n
      (higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
        theta beta gamma alpha n c)).mulVec c = _
  rw [higham22_roundedStageIIUpperFactorSeq_mulVec
    rm.toHigham22ScalarRoundModel theta beta gamma alpha c n (by omega)]
  rfl

theorem higham22_roundedAlgorithm22_2FactorSeq_bound
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    ∀ r i j,
      ‖higham22RoundedAlgorithm22_2FactorDelta rm theta beta gamma alpha f r i j‖ ≤
        higham22FactorRelativeBudget rm.u n r *
          ‖higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r i j‖ := by
  intro r
  refine Fin.addCases ?_ ?_ r
  · intro k i j
    simpa [higham22RoundedAlgorithm22_2FactorDelta,
      higham22RoundedAlgorithm22_2FactorSeq,
      higham22ExactAlgorithm22_2FactorSeq,
      higham22FactorRelativeBudget] using
      higham22_roundedStageIIUpperFactorSeq_bound
        rm.toHigham22ScalarRoundModel theta beta gamma alpha
          (higham22RoundedAlgorithm22_2StageIFin
            rm.toHigham22ScalarRoundModel alpha f n) n (by omega) k i j
  · intro k i j
    change ‖higham22RoundedAlgorithm22_2FactorDelta rm theta beta gamma
        alpha f (Fin.natAdd n k) i j‖ ≤
      higham22FactorRelativeBudget rm.u n (Fin.natAdd n k) *
        ‖higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha
          (Fin.natAdd n k) i j‖
    simpa only [higham22RoundedAlgorithm22_2FactorDelta,
      higham22RoundedAlgorithm22_2FactorSeq,
      higham22ExactAlgorithm22_2FactorSeq,
      higham22FactorRelativeBudget, Fin.append_right] using
      higham22_roundedStageILowerFactorSeq_bound rm huround alpha f n k i j

/-- Theorem 22.4 at the actual factor-product level, with the exact printed
coefficient `(1+u)^(7n)-1`. -/
theorem higham22_theorem22_4_actual_factor_product_bound
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    ∀ i j,
      ‖higham22ComplexMatSeqProd (n + 1) (n + n)
            (higham22RoundedAlgorithm22_2FactorSeq rm theta beta gamma alpha f) i j -
          higham22Algorithm22_2FactorProduct theta beta gamma alpha i j‖ ≤
        higham22Theorem22_4Coefficient n rm.u *
          matSeqProd (n + 1) (n + n)
            (fun r => higham22NormMatrix
              (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r)) i j := by
  have hscale : ∀ r, 0 ≤ higham22FactorRelativeBudget rm.u n r := by
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro k
      rw [higham22FactorRelativeBudget, Fin.append_left]
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith [rm.u_nonneg]))
    · intro k
      rw [higham22FactorRelativeBudget, Fin.append_right]
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith [rm.u_nonneg]))
  have h := higham22ComplexMatSeqProd_componentwise_perturbation_bound
    (n + 1) (n + n)
    (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha)
    (higham22RoundedAlgorithm22_2FactorDelta rm theta beta gamma alpha f)
    (higham22FactorRelativeBudget rm.u n) hscale
    (higham22_roundedAlgorithm22_2FactorSeq_bound
      rm huround theta beta gamma alpha f)
  intro i j
  have hij := h i j
  rw [show (fun r =>
        higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r +
          higham22RoundedAlgorithm22_2FactorDelta rm theta beta gamma alpha f r) =
      higham22RoundedAlgorithm22_2FactorSeq rm theta beta gamma alpha f by
        funext r
        ext p q
        simp [higham22RoundedAlgorithm22_2FactorDelta]] at hij
  rw [higham22_exactAlgorithm22_2FactorSeq_product,
    higham22_factorRelativeBudget_product] at hij
  simpa [higham22Theorem22_4Coefficient] using hij

/-- Operational form of Theorem 22.4.  In addition to the printed sharp
factor-product bound, this endpoint certifies that every division in the
literal rounded Algorithm 22.2 graph has a nonzero denominator.  In
particular, nonbreakdown is derived from `u < 1`, node branching, and the
source recurrence hypothesis `theta_j ≠ 0`; it is not hidden by Lean's total
division. -/
theorem higham22_theorem22_4_actual_factor_product_bound_and_nonbreakdown
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    Higham22RoundedAlgorithm22_2DivisionsNonzero
        rm.toHigham22ScalarRoundModel theta alpha ∧
      ∀ i j,
        ‖higham22ComplexMatSeqProd (n + 1) (n + n)
              (higham22RoundedAlgorithm22_2FactorSeq rm theta beta gamma alpha f) i j -
            higham22Algorithm22_2FactorProduct theta beta gamma alpha i j‖ ≤
          higham22Theorem22_4Coefficient n rm.u *
            matSeqProd (n + 1) (n + n)
              (fun r => higham22NormMatrix
                (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r)) i j := by
  exact ⟨higham22RoundedAlgorithm22_2_divisions_nonzero
      rm huround theta htheta alpha,
    higham22_theorem22_4_actual_factor_product_bound
      rm huround theta beta gamma alpha f⟩

/-- Equation (22.18), for the actual rounded executor. -/
theorem higham22_eq22_18_actual_forward_error
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
          theta beta gamma alpha f i -
        higham22Algorithm22_2Printed theta beta gamma alpha f i‖ ≤
      higham22Theorem22_4Coefficient n rm.u *
        ∑ j : Fin (n + 1),
          matSeqProd (n + 1) (n + n)
              (fun r => higham22NormMatrix
                (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r)) i j *
            ‖f j‖ := by
  let R := higham22ComplexMatSeqProd (n + 1) (n + n)
    (higham22RoundedAlgorithm22_2FactorSeq rm theta beta gamma alpha f)
  let E := higham22Algorithm22_2FactorProduct theta beta gamma alpha
  let M := matSeqProd (n + 1) (n + n)
    (fun r => higham22NormMatrix
      (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r))
  rw [← higham22_eq22_21_actual_rounded_factor_product rm huround]
  rw [← higham22_eq22_17_algorithm_product]
  change ‖R.mulVec f i - E.mulVec f i‖ ≤ _
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ j : Fin (n + 1), (R i j * f j - E i j * f j)‖ ≤
        ∑ j : Fin (n + 1), ‖R i j * f j - E i j * f j‖ := norm_sum_le _ _
    _ = ∑ j : Fin (n + 1), ‖R i j - E i j‖ * ‖f j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show R i j * f j - E i j * f j = (R i j - E i j) * f j by ring,
        norm_mul]
    _ ≤ ∑ j : Fin (n + 1),
        (higham22Theorem22_4Coefficient n rm.u * M i j) * ‖f j‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right
        (higham22_theorem22_4_actual_factor_product_bound
          rm huround theta beta gamma alpha f i j) (norm_nonneg _)
    _ = higham22Theorem22_4Coefficient n rm.u *
        ∑ j : Fin (n + 1), M i j * ‖f j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-! ### Corollary 22.5: checkerboard no-cancellation -/

noncomputable def higham22CheckerSign {d : ℕ} (i : Fin d) : ℂ :=
  (-1 : ℂ) ^ (i : ℕ)

def Higham22Checkerboard {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ i j, higham22CheckerSign i * A i j * higham22CheckerSign j =
    (‖A i j‖ : ℂ)

theorem higham22_checkerSign_sq {d : ℕ} (i : Fin d) :
    higham22CheckerSign i * higham22CheckerSign i = 1 := by
  rw [higham22CheckerSign, ← pow_add]
  rw [show (i : ℕ) + i = 2 * (i : ℕ) by omega, pow_mul]
  simp

theorem higham22_checkerSign_norm {d : ℕ} (i : Fin d) :
    ‖higham22CheckerSign i‖ = 1 := by
  simp [higham22CheckerSign]

theorem higham22_checkerSign_eq_neg_of_val_eq_succ {d : ℕ}
    (i j : Fin d) (hij : (i : ℕ) = (j : ℕ) + 1) :
    higham22CheckerSign i = -higham22CheckerSign j := by
  simp only [higham22CheckerSign, hij, pow_succ]
  ring

theorem higham22_checkerboard_one (d : ℕ) :
    Higham22Checkerboard (1 : Matrix (Fin d) (Fin d) ℂ) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.one_apply, if_pos rfl]
    simp only [mul_one]
    rw [higham22_checkerSign_sq]
    simp
  · rw [Matrix.one_apply, if_neg hij]
    simp

theorem higham22_checkerboard_mul_scaled_sum {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : Higham22Checkerboard A) (hB : Higham22Checkerboard B)
    (i j : Fin d) :
    higham22CheckerSign i * (A * B) i j * higham22CheckerSign j =
      ((∑ k : Fin d, ‖A i k‖ * ‖B k j‖ : ℝ) : ℂ) := by
  change (∀ p q, higham22CheckerSign p * A p q * higham22CheckerSign q =
    (‖A p q‖ : ℂ)) at hA
  change (∀ p q, higham22CheckerSign p * B p q * higham22CheckerSign q =
    (‖B p q‖ : ℂ)) at hB
  rw [Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  change (∑ k : Fin d,
    higham22CheckerSign i * (A i k * B k j) * higham22CheckerSign j) = _
  rw [show (∑ k : Fin d,
      higham22CheckerSign i * (A i k * B k j) * higham22CheckerSign j) =
    ∑ k : Fin d,
      (higham22CheckerSign i * A i k * higham22CheckerSign k) *
        (higham22CheckerSign k * B k j * higham22CheckerSign j) by
    apply Finset.sum_congr rfl
    intro k _
    rw [show (higham22CheckerSign i * A i k * higham22CheckerSign k) *
          (higham22CheckerSign k * B k j * higham22CheckerSign j) =
        (higham22CheckerSign i * (A i k * B k j) * higham22CheckerSign j) *
          (higham22CheckerSign k * higham22CheckerSign k) by ring,
      higham22_checkerSign_sq, mul_one]]
  simp_rw [hA, hB]
  push_cast
  rfl

theorem higham22_checkerboard_mul {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : Higham22Checkerboard A) (hB : Higham22Checkerboard B) :
    Higham22Checkerboard (A * B) := by
  intro i j
  let S : ℝ := ∑ k : Fin d, ‖A i k‖ * ‖B k j‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hscaled := higham22_checkerboard_mul_scaled_sum A B hA hB i j
  have hn' : ‖(A * B) i j‖ = S := by
    calc
      ‖(A * B) i j‖ =
          ‖higham22CheckerSign i * (A * B) i j * higham22CheckerSign j‖ := by
            simp [norm_mul, higham22_checkerSign_norm]
      _ = ‖(S : ℂ)‖ := congrArg norm hscaled
      _ = S := by simp [hS]
  rw [hscaled]
  exact congrArg Complex.ofReal hn'.symm

theorem higham22_checkerboard_mul_norm {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : Higham22Checkerboard A) (hB : Higham22Checkerboard B)
    (i j : Fin d) :
    ‖(A * B) i j‖ = ∑ k : Fin d, ‖A i k‖ * ‖B k j‖ := by
  let S : ℝ := ∑ k : Fin d, ‖A i k‖ * ‖B k j‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun k _ =>
    mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hscaled := higham22_checkerboard_mul_scaled_sum A B hA hB i j
  change ‖(A * B) i j‖ = S
  calc
    ‖(A * B) i j‖ =
        ‖higham22CheckerSign i * (A * B) i j * higham22CheckerSign j‖ := by
          simp [norm_mul, higham22_checkerSign_norm]
    _ = ‖(S : ℂ)‖ := congrArg norm hscaled
    _ = S := by simp [hS]

theorem higham22_checkerboard_complexSeqProd {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ r, Higham22Checkerboard (X r)) :
    Higham22Checkerboard (higham22ComplexMatSeqProd d m X) := by
  induction m with
  | zero => exact higham22_checkerboard_one d
  | succ m ih =>
      rw [higham22ComplexMatSeqProd]
      exact higham22_checkerboard_mul _ _ (hX 0)
        (ih (fun r => X r.succ) (fun r => hX r.succ))

/-- No subtractive cancellation in a product of checkerboard factors. -/
theorem higham22_checkerboard_complexSeqProd_norm_eq {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ r, Higham22Checkerboard (X r)) :
    ∀ i j,
      ‖higham22ComplexMatSeqProd d m X i j‖ =
        matSeqProd d m (fun r => higham22NormMatrix (X r)) i j := by
  induction m with
  | zero =>
      intro i j
      simp only [higham22ComplexMatSeqProd, matSeqProd, Matrix.one_apply]
      unfold idMatrix
      split <;> simp
  | succ m ih =>
      intro i j
      rw [higham22ComplexMatSeqProd]
      rw [higham22_checkerboard_mul_norm _ _ (hX 0)
        (higham22_checkerboard_complexSeqProd (fun r => X r.succ)
          (fun r => hX r.succ))]
      simp only [matSeqProd, matMul]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (fun r => X r.succ) (fun r => hX r.succ)]
      rfl

/-- Corollary 22.5's no-cancellation specialization of (22.18), stated for
the actual factor sequence.  The next lemmas discharge `hchecker` from the
printed node and recurrence-parameter sign conditions. -/
theorem higham22_corollary22_5_of_checkerboard
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ)
    (hchecker : ∀ r,
      Higham22Checkerboard
        (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r))
    (i : Fin (n + 1)) :
    ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
          theta beta gamma alpha f i -
        higham22Algorithm22_2Printed theta beta gamma alpha f i‖ ≤
      higham22Theorem22_4Coefficient n rm.u *
        ∑ j : Fin (n + 1),
          ‖higham22Algorithm22_2FactorProduct theta beta gamma alpha i j‖ *
            ‖f j‖ := by
  have hnocancel := higham22_checkerboard_complexSeqProd_norm_eq
    (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha) hchecker
  have hprod := higham22_exactAlgorithm22_2FactorSeq_product
    theta beta gamma alpha
  have hnc : ∀ p q,
      matSeqProd (n + 1) (n + n)
          (fun r => higham22NormMatrix
            (higham22ExactAlgorithm22_2FactorSeq theta beta gamma alpha r)) p q =
        ‖higham22Algorithm22_2FactorProduct theta beta gamma alpha p q‖ := by
    intro p q
    rw [← hnocancel p q, hprod]
  simpa only [hnc] using higham22_eq22_18_actual_forward_error
    rm huround theta beta gamma alpha f i

noncomputable def higham22RealFinToComplex {N : ℕ}
    (x : Fin N → ℝ) : Fin N → ℂ := fun i => x i

theorem higham22StageILastSaved_eq_pred_of_strictMono {N : ℕ}
    (alpha : Fin N → ℝ) (halpha : StrictMono alpha)
    (k j : ℕ) (hjN : j < N) (hkj : k < j) :
    higham22StageILastSaved
        (higham22FinExtend (higham22RealFinToComplex alpha)) k (j - 1) =
      j - 1 := by
  cases j with
  | zero => omega
  | succ t =>
      by_cases htk : t ≤ k
      · have hkt : k = t := by omega
        simpa [hkt] using higham22StageILastSaved_eq_k_of_le
          (higham22FinExtend (higham22RealFinToComplex alpha)) k t htk
      · cases t with
        | zero => omega
        | succ r =>
            have hrN : r + 1 < N := by omega
            have hsubN : r + 1 - k - 1 < N := by omega
            have hsub : r + 1 - k - 1 < r + 1 := by omega
            have hnode :
                higham22FinExtend (higham22RealFinToComplex alpha) (r + 1) ≠
                  higham22FinExtend (higham22RealFinToComplex alpha)
                    (r + 1 - k - 1) := by
              simp only [higham22FinExtend, hrN, hsubN, dite_true,
                higham22RealFinToComplex]
              intro heq
              have hlt :
                  (⟨r + 1 - k - 1, hsubN⟩ : Fin N) < ⟨r + 1, hrN⟩ := hsub
              exact (ne_of_lt (halpha hlt)) (Complex.ofReal_injective heq.symm)
            simp [higham22StageILastSaved, htk, hnode]

/-- Increasing real nodes make each actual Stage-I factor checkerboard. -/
theorem higham22_stageILowerFactor_checkerboard_of_strictMono {N : ℕ}
    (alpha : Fin N → ℝ) (halpha : StrictMono alpha) (k : ℕ) :
    Higham22Checkerboard
      (higham22StageILowerFactor (higham22RealFinToComplex alpha) k) := by
  intro i j
  rw [higham22StageILowerFactor, LinearMap.toMatrix'_apply]
  change higham22CheckerSign i *
      higham22Algorithm22_2StageIStep
        (higham22FinExtend (higham22RealFinToComplex alpha))
        (higham22FinExtend (Pi.single j 1)) k i *
      higham22CheckerSign j =
    (‖higham22Algorithm22_2StageIStep
        (higham22FinExtend (higham22RealFinToComplex alpha))
        (higham22FinExtend (Pi.single j 1)) k i‖ : ℂ)
  by_cases hik : (i : ℕ) ≤ k
  · simp only [higham22Algorithm22_2StageIStep, hik, if_true]
    rw [higham22FinExtend_apply]
    by_cases hij : i = j
    · subst j
      simp [Pi.single_apply, higham22_checkerSign_sq]
    · simp [Pi.single_apply, hij]
  · have hki : k < (i : ℕ) := Nat.lt_of_not_ge hik
    let q : Fin N := ⟨(i : ℕ) - k - 1, by omega⟩
    let p : Fin N := ⟨(i : ℕ) - 1, by omega⟩
    have hqi : q < i := by
      apply Fin.mk_lt_mk.mpr
      change (i : ℕ) - k - 1 < (i : ℕ)
      omega
    have hpi : (p : ℕ) + 1 = (i : ℕ) := by simp [p]; omega
    have hden : 0 < alpha i - alpha q := sub_pos.mpr (halpha hqi)
    have hqext :
        higham22FinExtend (higham22RealFinToComplex alpha)
            ((i : ℕ) - k - 1) = (alpha q : ℂ) := by
      change higham22FinExtend (higham22RealFinToComplex alpha) (q : ℕ) = _
      rw [higham22FinExtend_apply]
      rfl
    have hnode :
        higham22FinExtend (higham22RealFinToComplex alpha) i ≠
          higham22FinExtend (higham22RealFinToComplex alpha)
            ((i : ℕ) - k - 1) := by
      rw [higham22FinExtend_apply]
      rw [hqext]
      simp only [higham22RealFinToComplex]
      exact_mod_cast ne_of_gt (halpha hqi)
    have hlast := higham22StageILastSaved_eq_pred_of_strictMono

      alpha halpha k i i.isLt hki
    simp only [higham22Algorithm22_2StageIStep, hik, if_false, hnode,
      hlast]
    rw [higham22FinExtend_apply]
    have hpExt :
        higham22FinExtend (Pi.single j (1 : ℂ) : Fin N → ℂ) ((i : ℕ) - 1) =
          (Pi.single j (1 : ℂ) : Fin N → ℂ) p := by
      change higham22FinExtend (Pi.single j (1 : ℂ) : Fin N → ℂ) (p : ℕ) = _
      rw [higham22FinExtend_apply]
    rw [hpExt]
    rw [higham22FinExtend_apply]
    rw [hqext]
    have hireal : higham22RealFinToComplex alpha i = (alpha i : ℂ) := rfl
    rw [hireal]
    have hdiff : (alpha i : ℂ) - (alpha q : ℂ) = ((alpha i - alpha q : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hdiff]
    by_cases hji : j = i
    · subst j
      have hpi_ne : p ≠ i := ne_of_lt (by
        apply Fin.mk_lt_mk.mpr
        change (i : ℕ) - 1 < (i : ℕ)
        omega)
      simp [Pi.single_apply, hpi_ne, higham22_checkerSign_sq,
        Complex.norm_real, abs_of_pos hden]
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hden]
      calc
        higham22CheckerSign i * (↑(alpha i - alpha q) : ℂ)⁻¹ *
              higham22CheckerSign i =
            (higham22CheckerSign i * higham22CheckerSign i) *
              (↑(alpha i - alpha q) : ℂ)⁻¹ := by ring
        _ = (↑(alpha i - alpha q) : ℂ)⁻¹ := by
          rw [higham22_checkerSign_sq]
          ring
    · by_cases hjp : j = p
      · subst j
        have hip : i ≠ p := by exact ne_of_gt (by
          apply Fin.mk_lt_mk.mpr
          change (i : ℕ) - 1 < (i : ℕ)
          omega)
        have hsign : higham22CheckerSign i = -higham22CheckerSign p :=
          higham22_checkerSign_eq_neg_of_val_eq_succ i p hpi.symm
        simp [Pi.single_apply, hip, hsign, higham22_checkerSign_sq,
          Complex.norm_real, abs_of_pos hden]
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hden]
        calc
          -(higham22CheckerSign p *
                (-1 / (↑(alpha i - alpha q) : ℂ)) *
              higham22CheckerSign p) =
              (higham22CheckerSign p * higham22CheckerSign p) *
                (↑(alpha i - alpha q) : ℂ)⁻¹ := by ring
          _ = (↑(alpha i - alpha q) : ℂ)⁻¹ := by
            rw [higham22_checkerSign_sq]
            ring
      · have hip : i ≠ j := Ne.symm hji
        have hpj : p ≠ j := Ne.symm hjp
        simp [Pi.single_apply, hip, hpj]

noncomputable def higham22RealNatToComplex (x : ℕ → ℝ) : ℕ → ℂ :=
  fun j => x j

theorem higham22_checkerSign_eq_of_val_eq_add_two {d : ℕ}
    (i j : Fin d) (hij : (j : ℕ) = (i : ℕ) + 2) :
    higham22CheckerSign j = higham22CheckerSign i := by
  simp [higham22CheckerSign, hij, pow_add]

theorem higham22_checker_entry_same_of_nonneg {d : ℕ}
    (i : Fin d) (x : ℝ) (hx : 0 ≤ x) :
    higham22CheckerSign i * (x : ℂ) * higham22CheckerSign i =
      (‖(x : ℂ)‖ : ℂ) := by
  rw [show higham22CheckerSign i * (x : ℂ) * higham22CheckerSign i =
      (higham22CheckerSign i * higham22CheckerSign i) * (x : ℂ) by ring,
    higham22_checkerSign_sq]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx]

theorem higham22_checker_entry_next_of_nonpos {d : ℕ}
    (i j : Fin d) (hij : (j : ℕ) = (i : ℕ) + 1)

    (x : ℝ) (hx : x ≤ 0) :
    higham22CheckerSign i * (x : ℂ) * higham22CheckerSign j =
      (‖(x : ℂ)‖ : ℂ) := by
  have hs : higham22CheckerSign j = -higham22CheckerSign i :=
    higham22_checkerSign_eq_neg_of_val_eq_succ j i hij
  rw [hs]
  rw [show higham22CheckerSign i * (x : ℂ) * (-higham22CheckerSign i) =
      -(higham22CheckerSign i * higham22CheckerSign i) * (x : ℂ) by ring,
    higham22_checkerSign_sq]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hx]

theorem higham22_checker_entry_nextTwo_of_nonneg {d : ℕ}
    (i j : Fin d) (hij : (j : ℕ) = (i : ℕ) + 2)
    (x : ℝ) (hx : 0 ≤ x) :
    higham22CheckerSign i * (x : ℂ) * higham22CheckerSign j =
      (‖(x : ℂ)‖ : ℂ) := by
  rw [higham22_checkerSign_eq_of_val_eq_add_two i j hij]
  exact higham22_checker_entry_same_of_nonneg i x hx

theorem higham22_stageIIUpperFactor_checkerboard_of_signs
    (theta beta gamma : ℕ → ℝ) {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (htheta : ∀ r, 0 < theta r) (hgamma : ∀ r, 0 ≤ gamma r)
    (hbeta : ∀ r (q : Fin (n + 1)),
      r + (q : ℕ) ≤ n - 1 → beta r ≤ alpha q)
    (k : ℕ) (hk : k < n) :
    Higham22Checkerboard
      (higham22StageIIUpperFactor
        (higham22RealNatToComplex theta)
        (higham22RealNatToComplex beta)
        (higham22RealNatToComplex gamma)
        (higham22RealFinToComplex alpha) k) := by
  let kf : Fin (n + 1) := ⟨k, by omega⟩
  have hkext :
      higham22FinExtend (higham22RealFinToComplex alpha) k = (alpha kf : ℂ) := by
    change higham22FinExtend (higham22RealFinToComplex alpha) (kf : ℕ) = _
    rw [higham22FinExtend_apply]
    rfl
  intro i j
  rw [higham22StageIIUpperFactor, LinearMap.toMatrix'_apply]
  change higham22CheckerSign i *
      higham22Algorithm22_2PrintedStageIIStep
        (higham22RealNatToComplex theta)
        (higham22RealNatToComplex beta)
        (higham22RealNatToComplex gamma)
        (higham22FinExtend (higham22RealFinToComplex alpha)) n k
        (higham22FinExtend (Pi.single j 1)) i *
      higham22CheckerSign j =
    (‖higham22Algorithm22_2PrintedStageIIStep
        (higham22RealNatToComplex theta)
        (higham22RealNatToComplex beta)
        (higham22RealNatToComplex gamma)
        (higham22FinExtend (higham22RealFinToComplex alpha)) n k
        (higham22FinExtend (Pi.single j 1)) i‖ : ℂ)
  simp only [higham22Algorithm22_2PrintedStageIIStep]
  split_ifs with hiK hInterior hiLast hiN
  · simp only [higham22FinExtend_single]
    by_cases hj0 : k = (j : ℕ)
    · have hij : i = j := Fin.ext (by omega)
      subst j
      simp [hj0, higham22_checkerSign_sq]
    · by_cases hj1 : k + 1 = (j : ℕ)
      · have hx : beta 0 - alpha kf ≤ 0 := by
          have hk_le : k ≤ n - 1 := by omega
          have hb := hbeta 0 kf (by simpa [kf] using hk_le)
          linarith
        have hj2 : k + 2 ≠ (j : ℕ) := by omega
        have hs := higham22_checker_entry_next_of_nonpos i j
          (by omega) (beta 0 - alpha kf) hx
        simpa [hj0, hj1, hj2, hkext, higham22RealNatToComplex,
          higham22RealFinToComplex] using hs
      · by_cases hj2 : k + 2 = (j : ℕ)
        · have hx : 0 ≤ gamma 1 / theta 1 :=
            div_nonneg (hgamma 1) (le_of_lt (htheta 1))
          have hs := higham22_checker_entry_nextTwo_of_nonneg i j
            (by omega) (gamma 1 / theta 1) hx
          simpa [hj0, hj1, hj2, hkext, higham22RealNatToComplex,
            higham22RealFinToComplex] using hs
        · simp [hj0, hj1, hj2]
  · simp only [higham22FinExtend_single]
    let r := (i : ℕ) - k

    by_cases hj0 : (i : ℕ) = (j : ℕ)
    · have hij : i = j := Fin.ext hj0
      subst j
      have hx : 0 ≤ 1 / theta (r - 1) :=
        div_nonneg (by norm_num) (le_of_lt (htheta (r - 1)))
      have hs := higham22_checker_entry_same_of_nonneg i
        (1 / theta (r - 1)) hx
      simpa [r, hj0, higham22RealNatToComplex] using hs
    · by_cases hj1 : (i : ℕ) + 1 = (j : ℕ)
      · have hx : beta r - alpha kf ≤ 0 := by
          have hb := hbeta r kf (by dsimp [r, kf]; omega)
          linarith
        have hj2 : (i : ℕ) + 2 ≠ (j : ℕ) := by omega
        have hs := higham22_checker_entry_next_of_nonpos i j
          hj1.symm (beta r - alpha kf) hx
        simpa [r, hj0, hj1, hj2, hkext, higham22RealNatToComplex,
          higham22RealFinToComplex] using hs
      · by_cases hj2 : (i : ℕ) + 2 = (j : ℕ)
        · have hx : 0 ≤ gamma (r + 1) / theta (r + 1) :=
            div_nonneg (hgamma (r + 1)) (le_of_lt (htheta (r + 1)))
          have hs := higham22_checker_entry_nextTwo_of_nonneg i j hj2.symm
            (gamma (r + 1) / theta (r + 1)) hx
          simpa [r, hj0, hj1, hj2, hkext, higham22RealNatToComplex,
            higham22RealFinToComplex] using hs
        · simp [r, hj0, hj1, hj2]
  · simp only [higham22FinExtend_single]
    let r := n - k - 1
    by_cases hj0 : n - 1 = (j : ℕ)
    · have hij : i = j := Fin.ext (by omega)
      subst j
      have hnin : n ≠ (i : ℕ) := by omega
      have hx : 0 ≤ 1 / theta (n - k - 2) :=
        div_nonneg (by norm_num) (le_of_lt (htheta (n - k - 2)))
      have hs := higham22_checker_entry_same_of_nonneg i
        (1 / theta (n - k - 2)) hx
      simpa [hj0, hnin, higham22RealNatToComplex] using hs
    · by_cases hj1 : n = (j : ℕ)
      · have hx : beta r - alpha kf ≤ 0 := by
          have hb := hbeta r kf (by dsimp [r, kf]; omega)
          linarith
        have hjprev : (j : ℕ) - 1 ≠ (j : ℕ) := by omega
        have hs := higham22_checker_entry_next_of_nonpos i j
          (by omega) (beta r - alpha kf) hx
        simpa [r, hj0, hj1, hjprev, hkext, higham22RealNatToComplex,
          higham22RealFinToComplex] using hs
      · simp [hj0, hj1]
  · simp only [higham22FinExtend_single]
    by_cases hj0 : n = (j : ℕ)
    · have hij : i = j := Fin.ext (by omega)
      subst j
      have hx : 0 ≤ 1 / theta (n - k - 1) :=
        div_nonneg (by norm_num) (le_of_lt (htheta (n - k - 1)))
      have hs := higham22_checker_entry_same_of_nonneg i
        (1 / theta (n - k - 1)) hx
      simpa [hj0, higham22RealNatToComplex] using hs
    · simp [hj0]
  · simp only [higham22FinExtend_single]
    by_cases hij : i = j
    · subst j
      simp [higham22_checkerSign_sq]
    · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
      simp [hv]

theorem higham22_exactStageILowerFactorSeq_checkerboard_of_strictMono
    {N : ℕ} (alpha : Fin N → ℝ) (halpha : StrictMono alpha) :
    ∀ (s : ℕ) (r : Fin s),
      Higham22Checkerboard
        (higham22ExactStageILowerFactorSeq
          (higham22RealFinToComplex alpha) s r) := by
  intro s
  induction s with
  | zero => intro r; exact Fin.elim0 r
  | succ k ih =>
      intro r
      refine Fin.cases ?_ (fun q => ?_) r
      · simpa [higham22ExactStageILowerFactorSeq] using
          higham22_stageILowerFactor_checkerboard_of_strictMono alpha halpha k
      · simpa [higham22ExactStageILowerFactorSeq] using ih q

theorem higham22_exactStageIIUpperFactorSeq_checkerboard_of_signs

    (theta beta gamma : ℕ → ℝ) {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (htheta : ∀ r, 0 < theta r) (hgamma : ∀ r, 0 ≤ gamma r)
    (hbeta : ∀ r (q : Fin (n + 1)),
      r + (q : ℕ) ≤ n - 1 → beta r ≤ alpha q) :
    ∀ (s : ℕ), s ≤ n → ∀ r,
      Higham22Checkerboard
        (higham22ExactStageIIUpperFactorSeq
          (higham22RealNatToComplex theta)
          (higham22RealNatToComplex beta)
          (higham22RealNatToComplex gamma)
          (higham22RealFinToComplex alpha) s r) := by
  intro s hs
  induction s with
  | zero => intro r; exact Fin.elim0 r
  | succ k ih =>
      intro r
      refine Fin.lastCases ?_ (fun q => ?_) r
      · simpa [higham22ExactStageIIUpperFactorSeq] using
          higham22_stageIIUpperFactor_checkerboard_of_signs
            theta beta gamma alpha htheta hgamma hbeta k (by omega)
      · simpa [higham22ExactStageIIUpperFactorSeq] using ih (by omega) q

theorem higham22_exactAlgorithm22_2FactorSeq_checkerboard_of_signs
    (theta beta gamma : ℕ → ℝ) {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (halpha : StrictMono alpha)
    (htheta : ∀ r, 0 < theta r) (hgamma : ∀ r, 0 ≤ gamma r)
    (hbeta : ∀ r (q : Fin (n + 1)),
      r + (q : ℕ) ≤ n - 1 → beta r ≤ alpha q) :
    ∀ r,
      Higham22Checkerboard
        (higham22ExactAlgorithm22_2FactorSeq
          (higham22RealNatToComplex theta)
          (higham22RealNatToComplex beta)
          (higham22RealNatToComplex gamma)
          (higham22RealFinToComplex alpha) r) := by
  intro r
  refine Fin.addCases ?_ ?_ r
  · intro q
    rw [higham22ExactAlgorithm22_2FactorSeq, Fin.append_left]
    exact higham22_exactStageIIUpperFactorSeq_checkerboard_of_signs
      theta beta gamma alpha htheta hgamma hbeta n le_rfl q
  · intro q
    rw [higham22ExactAlgorithm22_2FactorSeq, Fin.append_right]
    exact higham22_exactStageILowerFactorSeq_checkerboard_of_strictMono
      alpha halpha n q

/-- Corollary 22.5 from the source's real sign conditions. -/
theorem higham22_corollary22_5_of_signs
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℝ) {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (halpha : StrictMono alpha)
    (htheta : ∀ r, 0 < theta r) (hgamma : ∀ r, 0 ≤ gamma r)
    (hbeta : ∀ r (q : Fin (n + 1)),
      r + (q : ℕ) ≤ n - 1 → beta r ≤ alpha q)
    (f : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
          (higham22RealNatToComplex theta)
          (higham22RealNatToComplex beta)
          (higham22RealNatToComplex gamma)
          (higham22RealFinToComplex alpha) f i -
        higham22Algorithm22_2Printed
          (higham22RealNatToComplex theta)
          (higham22RealNatToComplex beta)
          (higham22RealNatToComplex gamma)
          (higham22RealFinToComplex alpha) f i‖ ≤
      higham22Theorem22_4Coefficient n rm.u *
        ∑ j : Fin (n + 1),
          ‖higham22Algorithm22_2FactorProduct
            (higham22RealNatToComplex theta)
            (higham22RealNatToComplex beta)
            (higham22RealNatToComplex gamma)
            (higham22RealFinToComplex alpha) i j‖ * ‖f j‖ := by
  exact higham22_corollary22_5_of_checkerboard rm huround
    (higham22RealNatToComplex theta)
    (higham22RealNatToComplex beta)
    (higham22RealNatToComplex gamma)
    (higham22RealFinToComplex alpha) f
    (higham22_exactAlgorithm22_2FactorSeq_checkerboard_of_signs
      theta beta gamma alpha halpha htheta hgamma hbeta) i


def higham22MonomialThetaReal (_j : ℕ) : ℝ := 1
def higham22MonomialBetaReal (_j : ℕ) : ℝ := 0
def higham22MonomialGammaReal (_j : ℕ) : ℝ := 0

def higham22ChebyshevThetaReal : ℕ → ℝ
  | 0 => 1
  | _j + 1 => 2
def higham22ChebyshevBetaReal (_j : ℕ) : ℝ := 0
def higham22ChebyshevGammaReal : ℕ → ℝ
  | 0 => 0
  | _j + 1 => 1

noncomputable def higham22LegendreThetaReal (j : ℕ) : ℝ :=
  ((2 : ℝ) * j + 1) / (j + 1)
def higham22LegendreBetaReal (_j : ℕ) : ℝ := 0
noncomputable def higham22LegendreGammaReal (j : ℕ) : ℝ :=
  (j : ℝ) / (j + 1)

def higham22HermiteThetaReal (_j : ℕ) : ℝ := 2
def higham22HermiteBetaReal (_j : ℕ) : ℝ := 0
def higham22HermiteGammaReal (j : ℕ) : ℝ := 2 * j

theorem higham22_monomial_real_parameters :
    higham22RealNatToComplex higham22MonomialThetaReal = higham22MonomialTheta ∧
    higham22RealNatToComplex higham22MonomialBetaReal = higham22MonomialBeta ∧
    higham22RealNatToComplex higham22MonomialGammaReal = higham22MonomialGamma := by
  constructor
  · funext j; simp [higham22RealNatToComplex, higham22MonomialThetaReal,
      higham22MonomialTheta]
  constructor
  · funext j; simp [higham22RealNatToComplex, higham22MonomialBetaReal,
      higham22MonomialBeta]
  · funext j; simp [higham22RealNatToComplex, higham22MonomialGammaReal,
      higham22MonomialGamma]

theorem higham22_chebyshev_real_parameters :
    higham22RealNatToComplex higham22ChebyshevThetaReal = higham22ChebyshevTheta ∧
    higham22RealNatToComplex higham22ChebyshevBetaReal = higham22ChebyshevBeta ∧
    higham22RealNatToComplex higham22ChebyshevGammaReal = higham22ChebyshevGamma := by
  constructor
  · funext j; cases j <;> simp [higham22RealNatToComplex,
      higham22ChebyshevThetaReal, higham22ChebyshevTheta]
  constructor
  · funext j; simp [higham22RealNatToComplex, higham22ChebyshevBetaReal,
      higham22ChebyshevBeta]
  · funext j; cases j <;> simp [higham22RealNatToComplex,
      higham22ChebyshevGammaReal, higham22ChebyshevGamma]

theorem higham22_legendre_real_parameters :
    higham22RealNatToComplex higham22LegendreThetaReal = higham22LegendreTheta ∧
    higham22RealNatToComplex higham22LegendreBetaReal = higham22LegendreBeta ∧
    higham22RealNatToComplex higham22LegendreGammaReal = higham22LegendreGamma := by
  constructor
  · funext j
    simp [higham22RealNatToComplex, higham22LegendreThetaReal,
      higham22LegendreTheta]
  constructor
  · funext j; simp [higham22RealNatToComplex, higham22LegendreBetaReal,
      higham22LegendreBeta]
  · funext j
    simp [higham22RealNatToComplex, higham22LegendreGammaReal,
      higham22LegendreGamma]

theorem higham22_hermite_real_parameters :
    higham22RealNatToComplex higham22HermiteThetaReal = higham22HermiteTheta ∧
    higham22RealNatToComplex higham22HermiteBetaReal = higham22HermiteBeta ∧
    higham22RealNatToComplex higham22HermiteGammaReal = higham22HermiteGamma := by
  constructor
  · funext j; simp [higham22RealNatToComplex, higham22HermiteThetaReal,
      higham22HermiteTheta]
  constructor
  · funext j; simp [higham22RealNatToComplex, higham22HermiteBetaReal,
      higham22HermiteBeta]
  · funext j; simp [higham22RealNatToComplex, higham22HermiteGammaReal,
      higham22HermiteGamma]

def Higham22Corollary22_5Bound
    (rm : Higham22SourceRoundModel) (theta beta gamma : ℕ → ℂ)
    {n : ℕ} (alpha f : Fin (n + 1) → ℂ) : Prop :=
  ∀ i : Fin (n + 1),

    ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
          theta beta gamma alpha f i -
        higham22Algorithm22_2Printed theta beta gamma alpha f i‖ ≤
      higham22Theorem22_4Coefficient n rm.u *
        ∑ j : Fin (n + 1),
          ‖higham22Algorithm22_2FactorProduct theta beta gamma alpha i j‖ *
            ‖f j‖

/-- Corollary 22.5 for the four named bases in the source: monomial,
Chebyshev, Legendre, and Hermite. -/
theorem higham22_corollary22_5_named_bases
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    {n : ℕ} (alpha : Fin (n + 1) → ℝ)
    (halpha : StrictMono alpha) (halpha0 : ∀ q, 0 ≤ alpha q)
    (f : Fin (n + 1) → ℂ) :
    Higham22Corollary22_5Bound rm
        higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
        (higham22RealFinToComplex alpha) f ∧
    Higham22Corollary22_5Bound rm
        higham22ChebyshevTheta higham22ChebyshevBeta higham22ChebyshevGamma
        (higham22RealFinToComplex alpha) f ∧
    Higham22Corollary22_5Bound rm
        higham22LegendreTheta higham22LegendreBeta higham22LegendreGamma
        (higham22RealFinToComplex alpha) f ∧
    Higham22Corollary22_5Bound rm
        higham22HermiteTheta higham22HermiteBeta higham22HermiteGamma
        (higham22RealFinToComplex alpha) f := by
  rcases higham22_monomial_real_parameters with ⟨hmθ, hmβ, hmγ⟩
  rcases higham22_chebyshev_real_parameters with ⟨hcθ, hcβ, hcγ⟩
  rcases higham22_legendre_real_parameters with ⟨hlθ, hlβ, hlγ⟩
  rcases higham22_hermite_real_parameters with ⟨hhθ, hhβ, hhγ⟩
  have hbetaZero : ∀ r (q : Fin (n + 1)),
      r + (q : ℕ) ≤ n - 1 → (0 : ℝ) ≤ alpha q := by
    intro r q _
    exact halpha0 q
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have h := higham22_corollary22_5_of_signs rm huround
      higham22MonomialThetaReal higham22MonomialBetaReal
      higham22MonomialGammaReal alpha halpha
      (by intro r; norm_num [higham22MonomialThetaReal])
      (by intro r; norm_num [higham22MonomialGammaReal])
      (by intro r q hr; simpa [higham22MonomialBetaReal] using
        hbetaZero r q hr) f i
    rw [hmθ, hmβ, hmγ] at h
    exact h
  · intro i
    have h := higham22_corollary22_5_of_signs rm huround
      higham22ChebyshevThetaReal higham22ChebyshevBetaReal
      higham22ChebyshevGammaReal alpha halpha
      (by intro r; cases r <;> norm_num [higham22ChebyshevThetaReal])
      (by intro r; cases r <;> norm_num [higham22ChebyshevGammaReal])
      (by intro r q hr; simpa [higham22ChebyshevBetaReal] using
        hbetaZero r q hr) f i
    rw [hcθ, hcβ, hcγ] at h
    exact h
  · intro i
    have h := higham22_corollary22_5_of_signs rm huround
      higham22LegendreThetaReal higham22LegendreBetaReal
      higham22LegendreGammaReal alpha halpha
      (by
        intro r
        unfold higham22LegendreThetaReal
        positivity)
      (by
        intro r
        unfold higham22LegendreGammaReal
        positivity)
      (by intro r q hr; simpa [higham22LegendreBetaReal] using
        hbetaZero r q hr) f i
    rw [hlθ, hlβ, hlγ] at h
    exact h
  · intro i
    have h := higham22_corollary22_5_of_signs rm huround
      higham22HermiteThetaReal higham22HermiteBetaReal
      higham22HermiteGammaReal alpha halpha
      (by intro r; norm_num [higham22HermiteThetaReal])
      (by intro r; simp [higham22HermiteGammaReal])
      (by intro r q hr; simpa [higham22HermiteBetaReal] using
        hbetaZero r q hr) f i

    rw [hhθ, hhβ, hhγ] at h
    exact h


/-! ### Theorem 22.6 conditional residual-product kernel -/

/-- The exact (non-asymptotic) coefficient `d(n,u)` in Theorem 22.6. -/
noncomputable def higham22Theorem22_6Coefficient (n : ℕ) (u : ℝ) : ℝ :=
  (1 + higham22Theorem22_4Coefficient n u) ^ n /
      (1 - u) ^ (3 * n) - 1

/-- Relative budgets for the inverse factors in (22.23): the first `n`
factors use the proved lower-factor inverse radius `(1-u)^{-3}-1`, while the
last `n` use the explicitly assumed upper-factor radius (22.24). -/
noncomputable def higham22InverseFactorRelativeBudget (u : ℝ) (n : ℕ) :
    Fin (n + n) → ℝ :=
  Fin.append (fun _ : Fin n ↦ ((1 - u) ^ 3)⁻¹ - 1)
    (fun _ : Fin n ↦ higham22Theorem22_4Coefficient n u)

/-- The scalar product calculation in (22.25). -/
theorem higham22_inverseFactorRelativeBudget_product
    (u : ℝ) (n : ℕ) (hu1 : u < 1) :
    scalarSeqProd (n + n)
        (fun r ↦ 1 + higham22InverseFactorRelativeBudget u n r) =
      1 + higham22Theorem22_6Coefficient n u := by
  rw [higham22_scalarSeqProd_eq_fin_prod]
  rw [show (∏ r : Fin (n + n),
      (1 + higham22InverseFactorRelativeBudget u n r)) =
      (∏ r : Fin (n + n), Fin.append
        (fun _ : Fin n ↦ ((1 - u) ^ 3)⁻¹)
        (fun _ : Fin n ↦ 1 + higham22Theorem22_4Coefficient n u) r) by
    apply Finset.prod_congr rfl
    intro r _hr
    refine Fin.addCases ?_ ?_ r
    · intro i
      rw [higham22InverseFactorRelativeBudget,
        Fin.append_left, Fin.append_left]
      ring
    · intro i
      rw [higham22InverseFactorRelativeBudget,
        Fin.append_right, Fin.append_right]]
  rw [fin_prod_append]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hinvpow : ((1 - u) ^ 3)⁻¹ ^ n = ((1 - u) ^ (3 * n))⁻¹ := by
    rw [inv_pow, pow_mul]
  rw [hinvpow]
  simp only [higham22Theorem22_6Coefficient, div_eq_mul_inv]
  ring

/-- Theorem 22.6's Lemma 3.8 step.  This theorem is deliberately conditional
on local upper-inverse bounds, exactly as the source theorem is conditional on
(22.24); the residual product and `d(n,u)` conclusion are derived. -/
theorem higham22_theorem22_6_inverse_factor_product_bound
    (dim n : ℕ)
    (X deltaX : Fin (n + n) → Fin dim → Fin dim → ℝ)
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (hdeltaX : ∀ r i j,
      |deltaX r i j| ≤
        higham22InverseFactorRelativeBudget u n r * |X r i j|) :
    ∀ i j,
      |matSeqProd dim (n + n)
          (fun r i j ↦ X r i j + deltaX r i j) i j -
        matSeqProd dim (n + n) X i j| ≤
      higham22Theorem22_6Coefficient n u *
        matSeqProd dim (n + n) (fun r ↦ absMatrix dim (X r)) i j := by
  have hc : 0 ≤ higham22Theorem22_4Coefficient n u := by
    unfold higham22Theorem22_4Coefficient
    exact sub_nonneg.mpr (one_le_pow₀ (by linarith : 1 ≤ 1 + u))
  have hscale : ∀ r, 0 ≤ higham22InverseFactorRelativeBudget u n r := by
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro k
      rw [higham22InverseFactorRelativeBudget, Fin.append_left]
      apply sub_nonneg.mpr
      rw [one_le_inv₀]
      · exact pow_le_one₀ (by linarith : 0 ≤ 1 - u)
          (by linarith : 1 - u ≤ 1)
      · exact pow_pos (by linarith : 0 < 1 - u) _
    · intro k
      rw [higham22InverseFactorRelativeBudget, Fin.append_right]
      exact hc
  intro i j
  have h := matSeqProd_componentwise_perturbation_bound dim (n + n)
    X deltaX (higham22InverseFactorRelativeBudget u n) hscale hdeltaX i j
  rw [higham22_inverseFactorRelativeBudget_product u n hu1] at h
  simpa [higham22Theorem22_6Coefficient] using h

/-! ### Problem 22.8: upper-bidiagonal inverse perturbations -/

/-- First identity in Problem 22.8, written using the repository's Chapter 15
explicit upper-bidiagonal inverse-entry formula.  The multiplier displays every
diagonal and superdiagonal relative perturbation separately. -/
theorem higham22_problem22_8_general_factor
    {N : ℕ} (u e deltaDiag deltaSuper : Fin N → ℝ) (i j : Fin N)
    (hij : (i : ℕ) ≤ j) (hdiag : ∀ p, 1 + deltaDiag p ≠ 0) :
    upperBidiagInvEntry
        (fun p ↦ (1 + deltaDiag p) * u p)
        (fun p ↦ (1 + deltaSuper p) * e p) i j =
      ((∏ p ∈ Finset.univ.filter
          (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j),
          (1 + deltaSuper p) / (1 + deltaDiag p)) /
        (1 + deltaDiag j)) * upperBidiagInvEntry u e i j := by
  simp only [upperBidiagInvEntry, not_lt.mpr hij, if_false]
  have hterm : ∀ p : Fin N,
      -((1 + deltaSuper p) * e p) / ((1 + deltaDiag p) * u p) =
        ((1 + deltaSuper p) / (1 + deltaDiag p)) * (-e p / u p) := by
    intro p
    field_simp [hdiag p]
    <;> ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  field_simp [hdiag j]
  <;> ring

/-- Difference form of the first Problem 22.8 identity. -/
theorem higham22_problem22_8_general_difference
    {N : ℕ} (u e deltaDiag deltaSuper : Fin N → ℝ) (i j : Fin N)
    (hij : (i : ℕ) ≤ j) (hdiag : ∀ p, 1 + deltaDiag p ≠ 0) :
    upperBidiagInvEntry
          (fun p ↦ (1 + deltaDiag p) * u p)
          (fun p ↦ (1 + deltaSuper p) * e p) i j -
        upperBidiagInvEntry u e i j =
      (((∏ p ∈ Finset.univ.filter
          (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j),
          (1 + deltaSuper p) / (1 + deltaDiag p)) /
        (1 + deltaDiag j)) - 1) * upperBidiagInvEntry u e i j := by
  rw [higham22_problem22_8_general_factor
    u e deltaDiag deltaSuper i j hij hdiag]
  ring

/-- Appendix A's structured monomial case:
`Û = diag(1+ε) Ũ`, while each superdiagonal entry of `Ũ` has one
additional factor `1+δ`.  The row factor cancels from every interior ratio. -/
theorem higham22_problem22_8_structured_factor
    {N : ℕ} (u e eps delta : Fin N → ℝ) (i j : Fin N)
    (hij : (i : ℕ) ≤ j) (heps : ∀ p, 1 + eps p ≠ 0) :
    upperBidiagInvEntry
        (fun p ↦ (1 + eps p) * u p)
        (fun p ↦ (1 + eps p) * (1 + delta p) * e p) i j =
      ((∏ p ∈ Finset.univ.filter
          (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j), (1 + delta p)) /
        (1 + eps j)) * upperBidiagInvEntry u e i j := by
  simp only [upperBidiagInvEntry, not_lt.mpr hij, if_false]
  have hterm : ∀ p : Fin N,
      -((1 + eps p) * (1 + delta p) * e p) / ((1 + eps p) * u p) =
        (1 + delta p) * (-e p / u p) := by
    intro p
    field_simp [heps p]
    <;> ring
  simp_rw [hterm]
  rw [Finset.prod_mul_distrib]
  field_simp [heps j]
  <;> ring

/-- Difference form of the structured Appendix A factor identity. -/
theorem higham22_problem22_8_structured_difference
    {N : ℕ} (u e eps delta : Fin N → ℝ) (i j : Fin N)
    (hij : (i : ℕ) ≤ j) (heps : ∀ p, 1 + eps p ≠ 0) :
    upperBidiagInvEntry
          (fun p ↦ (1 + eps p) * u p)
          (fun p ↦ (1 + eps p) * (1 + delta p) * e p) i j -
        upperBidiagInvEntry u e i j =
      (((∏ p ∈ Finset.univ.filter
          (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j), (1 + delta p)) /
        (1 + eps j)) - 1) * upperBidiagInvEntry u e i j := by
  rw [higham22_problem22_8_structured_factor u e eps delta i j hij heps]
  ring

/-- Mixed signed product lemma needed by Problem 22.8.  It is proved from the
repository's genuine `prod_error_bound` and `gamma_mul`, rather than assumed as
an inverse-perturbation certificate. -/
theorem higham22_problem22_8_mixed_product
    {N : ℕ} (eps delta : Fin N → ℝ) (i j : Fin N) (uround : ℝ)
    (hu0 : 0 ≤ uround)
    (heps : ∀ p, |eps p| ≤ uround)
    (hdelta : ∀ p, |delta p| ≤ uround)
    (hu1 : uround < 1)
    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff uround hu0)
      ((Finset.univ.filter
        (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j)).card + 1)) :
    ∃ η : ℝ,
      |η| ≤ gamma (FPModel.exactWithUnitRoundoff uround hu0)
        ((Finset.univ.filter
          (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j)).card + 1) ∧
      ((∏ p ∈ Finset.univ.filter
          (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j), (1 + delta p)) /
        (1 + eps j)) = 1 + η := by
  let S : Finset (Fin N) := Finset.univ.filter
    (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j)
  let fp := FPModel.exactWithUnitRoundoff uround hu0
  let d : Fin S.card → ℝ := fun k ↦ delta ((S.equivFin).symm k)
  have hvalidS : gammaValid fp S.card :=
    gammaValid_mono fp (Nat.le_succ S.card) (by simpa [fp, S] using hvalid)
  have hd : ∀ k, |d k| ≤ fp.u := by
    intro k
    simpa [d, fp, FPModel.exactWithUnitRoundoff] using
      hdelta (((S.equivFin).symm k).1)
  obtain ⟨θ, hθ, hprod⟩ := prod_error_bound fp S.card d hd hvalidS
  have hprodS : (∏ p ∈ S, (1 + delta p)) = 1 + θ := by
    calc
      (∏ p ∈ S, (1 + delta p)) = ∏ p : S, (1 + delta p.1) := by
        exact (Finset.prod_attach S (fun p ↦ 1 + delta p)).symm
      _ = ∏ k : Fin S.card, (1 + d k) := by
        apply Fintype.prod_equiv S.equivFin
        intro p
        simp [d]
      _ = 1 + θ := hprod
  have hepsj : |eps j| ≤ fp.u := by
    simpa [fp, FPModel.exactWithUnitRoundoff] using heps j
  have hpos : 0 < 1 + eps j := by
    dsimp [fp, FPModel.exactWithUnitRoundoff] at hepsj
    linarith [neg_abs_le (eps j)]
  let α : ℝ := -eps j / (1 + eps j)
  have hαeq : 1 / (1 + eps j) = 1 + α := by
    simp only [α]
    field_simp [hpos.ne']
    ring
  have hα : |α| ≤ gamma fp 1 := by
    simp only [α, abs_div, abs_neg, abs_of_pos hpos]
    have h1u : 0 < 1 - fp.u := by
      dsimp [fp, FPModel.exactWithUnitRoundoff]
      linarith
    have hgamma1 : gamma fp 1 = fp.u / (1 - fp.u) := by
      unfold gamma
      simp
    rw [hgamma1, ← sub_nonneg]
    have key : fp.u / (1 - fp.u) - |eps j| / (1 + eps j) =
        (fp.u * (1 + eps j) - |eps j| * (1 - fp.u)) /
          ((1 - fp.u) * (1 + eps j)) := by
      field_simp [h1u.ne', hpos.ne']
    rw [key]
    apply div_nonneg
    · nlinarith [neg_abs_le (eps j), fp.u_nonneg]
    · exact le_of_lt (mul_pos h1u hpos)
  obtain ⟨η, hη, hηeq⟩ := gamma_mul fp S.card 1 θ α hθ hα
    (by simpa [fp, S] using hvalid)
  refine ⟨η, by simpa [fp, S] using hη, ?_⟩
  change ((∏ p ∈ S, (1 + delta p)) / (1 + eps j)) = 1 + η
  rw [hprodS]
  calc
    (1 + θ) / (1 + eps j) = (1 + θ) * (1 + α) := by
      rw [div_eq_mul_inv]
      congr 1
      simpa [one_div] using hαeq
    _ = 1 + η := hηeq

/-- Problem 22.8's componentwise inverse-entry bound for the actual Appendix A
row-scaled/superdiagonal perturbation structure. -/
theorem higham22_problem22_8_inverse_entry_bound
    {N : ℕ} (u e eps delta : Fin N → ℝ) (i j : Fin N) (uround : ℝ)
    (hu0 : 0 ≤ uround)
    (heps : ∀ p, |eps p| ≤ uround)
    (hdelta : ∀ p, |delta p| ≤ uround)
    (hvalid : gammaValid (FPModel.exactWithUnitRoundoff uround hu0) N) :
    |upperBidiagInvEntry
          (fun p ↦ (1 + eps p) * u p)
          (fun p ↦ (1 + eps p) * (1 + delta p) * e p) i j -
        upperBidiagInvEntry u e i j| ≤
      gamma (FPModel.exactWithUnitRoundoff uround hu0) N *
        |upperBidiagInvEntry u e i j| := by
  let fp := FPModel.exactWithUnitRoundoff uround hu0
  have hu1 : uround < 1 := by
    have hv := hvalid
    unfold gammaValid at hv
    dsimp [FPModel.exactWithUnitRoundoff] at hv
    have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le i) i.isLt
    have hN : (1 : ℝ) ≤ N := by
      exact_mod_cast (Nat.succ_le_iff.mpr hNpos)
    have hu_le : uround ≤ (N : ℝ) * uround := by
      simpa using mul_le_mul_of_nonneg_right hN hu0
    linarith
  have heps_ne : ∀ p, 1 + eps p ≠ 0 := by
    intro p
    have hp : 0 < 1 + eps p := by
      linarith [neg_abs_le (eps p), heps p]
    exact hp.ne'
  by_cases hij : (i : ℕ) ≤ j
  · let S : Finset (Fin N) := Finset.univ.filter
      (fun p : Fin N ↦ (i : ℕ) ≤ p ∧ (p : ℕ) < j)
    have hSsub : S ⊂ (Finset.univ : Finset (Fin N)) := by
      rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.filter_subset _ _, ?_⟩
      intro hEq
      have hjmem : j ∈ S := by simpa [hEq]
      simp [S] at hjmem
    have hcardlt : S.card < N := by
      simpa using Finset.card_lt_card hSsub
    have hcard : S.card + 1 ≤ N := by omega
    have hvalidS : gammaValid fp (S.card + 1) :=
      gammaValid_mono fp hcard (by simpa [fp] using hvalid)
    obtain ⟨η, hη, hratio⟩ := higham22_problem22_8_mixed_product
      eps delta i j uround hu0 heps hdelta hu1
        (by simpa [S, fp] using hvalidS)
    have hdiff := higham22_problem22_8_structured_difference
      u e eps delta i j hij heps_ne
    have hfactor :
        upperBidiagInvEntry
              (fun p ↦ (1 + eps p) * u p)
              (fun p ↦ (1 + eps p) * (1 + delta p) * e p) i j -
            upperBidiagInvEntry u e i j =
          η * upperBidiagInvEntry u e i j := by
      rw [hdiff, hratio]
      ring
    rw [hfactor, abs_mul]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    exact hη.trans (gamma_mono fp hcard (by simpa [fp] using hvalid))
  · have hji : (j : ℕ) < i := Nat.lt_of_not_ge hij
    simp [upperBidiagInvEntry, hji]

/-- The rational coefficient printed in the conclusion of Problem 22.8. -/
noncomputable def higham22Problem22_8Coefficient (N : ℕ) (uround : ℝ) : ℝ :=
  (N : ℝ) * uround / (1 - (N : ℝ) * uround)

/-- Source-coefficient form of Problem 22.8. -/
theorem higham22_problem22_8_source_coefficient
    {N : ℕ} (u e eps delta : Fin N → ℝ) (i j : Fin N) (uround : ℝ)
    (hu0 : 0 ≤ uround)
    (heps : ∀ p, |eps p| ≤ uround)
    (hdelta : ∀ p, |delta p| ≤ uround)
    (hvalid : gammaValid (FPModel.exactWithUnitRoundoff uround hu0) N) :
    |upperBidiagInvEntry
          (fun p ↦ (1 + eps p) * u p)
          (fun p ↦ (1 + eps p) * (1 + delta p) * e p) i j -
        upperBidiagInvEntry u e i j| ≤
      higham22Problem22_8Coefficient N uround *
        |upperBidiagInvEntry u e i j| := by
  simpa [higham22Problem22_8Coefficient, gamma,
    FPModel.exactWithUnitRoundoff] using
      higham22_problem22_8_inverse_entry_bound
        u e eps delta i j uround hu0 heps hdelta hvalid

/-! ## Closure notes

The exact Hermite factorization, the actual rounded factor-product analysis,
the checkerboard specializations, Problem 22.8, and the conditional residual
chain are producer theorems in this module.  Equation (22.24) remains explicit
as the source's simplifying upper-inverse assumption for general Theorem 22.6;
it is not replaced by a target-bearing certificate.  The abstract Problem 22.8
coefficient and the printed `n(n+4)` derivative at zero are recorded below,
but a producer connecting Problem 22.8 to the actual state-dependent rounded
monomial Stage-II factor sequence is still required for Corollary 22.7. -/

section SignAndRefinement
/-- Exact scalar model of refinement when the verified residual solve contracts
the error by a fixed factor. -/
noncomputable def higham22RefinementError (q e0 : ℝ) : ℕ → ℝ
  | 0 => e0
  | k + 1 => q * higham22RefinementError q e0 k

theorem higham22_refinementError_closed (q e0 : ℝ) (k : ℕ) :
    higham22RefinementError q e0 k = q ^ k * e0 := by
  induction k with
  | zero => simp [higham22RefinementError]
  | succ k ih => rw [higham22RefinementError, ih, pow_succ]; ring

/-- Precise refinement consequence 22.B2: a contraction factor tends the
error to zero. -/
theorem higham22_refinement_converges (q e0 : ℝ)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (higham22RefinementError q e0) atTop (𝓝 0) := by
  have hqabs : |q| < 1 := by simpa [abs_of_nonneg hq0]
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hqabs).mul_const e0
  have heq : higham22RefinementError q e0 = (fun k ↦ q ^ k * e0) := by
    funext k
    exact higham22_refinementError_closed q e0 k
  rw [heq]
  simpa using h

end SignAndRefinement

end VandermondeLike


/-- Reverse a finite matrix sequence without changing its entries. -/
noncomputable def higham22ReverseMatrixSeq {d : ℕ} :
    (m : ℕ) → (Fin m → Matrix (Fin d) (Fin d) ℂ) →
      Fin m → Matrix (Fin d) (Fin d) ℂ
  | 0, _ => Fin.elim0
  | m + 1, X => Fin.cons (X (Fin.last m))
      (higham22ReverseMatrixSeq m (fun r => X r.castSucc))

noncomputable def higham22ReverseInverseMatrixSeq {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    Fin m → Matrix (Fin d) (Fin d) ℂ :=
  fun r => (higham22ReverseMatrixSeq m X r)⁻¹

theorem higham22_reverseMatrixSeq_snoc {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    higham22ReverseMatrixSeq (m + 1) (Fin.snoc X A) =
      Fin.cons A (higham22ReverseMatrixSeq m X) := by
  funext r
  refine Fin.cases ?_ (fun q => ?_) r
  · simp [higham22ReverseMatrixSeq]
  · simp [higham22ReverseMatrixSeq]

theorem higham22_reverseInverseMatrixSeq_snoc {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (A : Matrix (Fin d) (Fin d) ℂ) :
    higham22ReverseInverseMatrixSeq (Fin.snoc X A) =
      Fin.cons A⁻¹ (higham22ReverseInverseMatrixSeq X) := by
  funext r
  rw [higham22ReverseInverseMatrixSeq,
    higham22_reverseMatrixSeq_snoc]
  refine Fin.cases ?_ (fun q => ?_) r
  · simp
  · rfl

/-- Equation (22.23)'s algebraic factor reversal: the inverse of a finite
product is the product of the factor inverses in reverse order. -/
theorem higham22_eq22_23_reverse_inverse_product {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ) :
    higham22ComplexMatSeqProd d m (higham22ReverseInverseMatrixSeq X) =
      (higham22ComplexMatSeqProd d m X)⁻¹ := by
  induction m with
  | zero => simp [higham22ComplexMatSeqProd, higham22ReverseInverseMatrixSeq,
      higham22ReverseMatrixSeq]
  | succ m ih =>
      let X0 : Fin m → Matrix (Fin d) (Fin d) ℂ := fun r => X r.castSucc
      let A : Matrix (Fin d) (Fin d) ℂ := X (Fin.last m)
      have hX : X = Fin.snoc X0 A := by
        funext r
        refine Fin.lastCases ?_ (fun q => ?_) r
        · simp [A]
        · simp [X0]
      rw [hX, higham22ComplexMatSeqProd_snoc, Matrix.mul_inv_rev]
      rw [higham22_reverseInverseMatrixSeq_snoc]
      rw [higham22ComplexMatSeqProd_cons, ih]

noncomputable def higham22ExactAlgorithm22_2InverseFactorSeq
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :

    Fin (n + n) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Fin.append
    (higham22ReverseInverseMatrixSeq
      (higham22ExactStageILowerFactorSeq alpha n))
    (higham22ReverseInverseMatrixSeq
      (higham22ExactStageIIUpperFactorSeq theta beta gamma alpha n))

noncomputable def higham22RoundedAlgorithm22_2InverseFactorSeq
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    Fin (n + n) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  let c := higham22RoundedAlgorithm22_2StageIFin
    rm.toHigham22ScalarRoundModel alpha f n
  Fin.append
    (higham22ReverseInverseMatrixSeq
      (higham22RoundedStageILowerFactorSeq rm alpha f n))
    (higham22ReverseInverseMatrixSeq
      (higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
        theta beta gamma alpha n c))

noncomputable def higham22RoundedAlgorithm22_2InverseFactorDelta
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    Fin (n + n) → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  fun r => higham22RoundedAlgorithm22_2InverseFactorSeq
      rm theta beta gamma alpha f r -
    higham22ExactAlgorithm22_2InverseFactorSeq theta beta gamma alpha r

theorem higham22_eq22_23_exact_inverse_factor_product
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) :
    higham22ComplexMatSeqProd (n + 1) (n + n)
        (higham22ExactAlgorithm22_2InverseFactorSeq
          theta beta gamma alpha) =
      (higham22Algorithm22_2FactorProduct theta beta gamma alpha)⁻¹ := by
  rw [higham22ExactAlgorithm22_2InverseFactorSeq,
    higham22ComplexMatSeqProd_append,
    higham22_eq22_23_reverse_inverse_product,
    higham22_eq22_23_reverse_inverse_product,
    higham22_exactStageILowerFactorSeq_product,
    higham22_exactStageIIUpperFactorSeq_product,
    higham22Algorithm22_2FactorProduct, Matrix.mul_inv_rev]

theorem higham22_eq22_23_rounded_inverse_factor_product
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) :
    higham22ComplexMatSeqProd (n + 1) (n + n)
        (higham22RoundedAlgorithm22_2InverseFactorSeq
          rm theta beta gamma alpha f) =
      (higham22ComplexMatSeqProd (n + 1) (n + n)
      (higham22RoundedAlgorithm22_2FactorSeq
          rm theta beta gamma alpha f))⁻¹ := by
  let c := higham22RoundedAlgorithm22_2StageIFin
    rm.toHigham22ScalarRoundModel alpha f n
  rw [higham22RoundedAlgorithm22_2InverseFactorSeq,
    higham22ComplexMatSeqProd_append,
    higham22_eq22_23_reverse_inverse_product,

    higham22_eq22_23_reverse_inverse_product,
    higham22RoundedAlgorithm22_2FactorSeq,
    higham22ComplexMatSeqProd_append, Matrix.mul_inv_rev]

/-- The source's sole simplifying assumption (22.24), stated exactly on the
actual rounded upper-factor inverses.  Reversal places those `n` factors in
the last half of the inverse-factor sequence. -/
def Higham22Eq22_24
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (c : ℝ) : Prop :=
  let a := higham22RoundedAlgorithm22_2StageIFin
    rm.toHigham22ScalarRoundModel alpha f n
  (∀ q : Fin n, IsUnit
      (higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
        theta beta gamma alpha n a q).det) ∧
    ∀ q : Fin n, ∀ i j,
      ‖(higham22RoundedStageIIUpperFactorSeq rm.toHigham22ScalarRoundModel
            theta beta gamma alpha n a q)⁻¹ i j -
          (higham22ExactStageIIUpperFactorSeq theta beta gamma alpha n q)⁻¹ i j‖ ≤
        c * ‖(higham22ExactStageIIUpperFactorSeq
          theta beta gamma alpha n q)⁻¹ i j‖

noncomputable def higham22InverseFactorRelativeBudgetWith
    (u c : ℝ) (n : ℕ) : Fin (n + n) → ℝ :=
  Fin.append (fun _ : Fin n => ((1 - u) ^ 3)⁻¹ - 1)
    (fun _ : Fin n => c)

noncomputable def higham22Theorem22_6CoefficientWith
    (n : ℕ) (u c : ℝ) : ℝ :=
  (1 + c) ^ n / (1 - u) ^ (3 * n) - 1

theorem higham22_inverseFactorRelativeBudgetWith_product
    (u c : ℝ) (n : ℕ) (hu1 : u < 1) :
    scalarSeqProd (n + n)
        (fun r => 1 + higham22InverseFactorRelativeBudgetWith u c n r) =
      1 + higham22Theorem22_6CoefficientWith n u c := by
  rw [higham22_scalarSeqProd_eq_fin_prod]
  rw [show (∏ r : Fin (n + n),
      (1 + higham22InverseFactorRelativeBudgetWith u c n r)) =
      (∏ r : Fin (n + n), Fin.append
        (fun _ : Fin n => ((1 - u) ^ 3)⁻¹)
        (fun _ : Fin n => 1 + c) r) by
    apply Finset.prod_congr rfl
    intro r _hr
    refine Fin.addCases ?_ ?_ r
    · intro i
      rw [higham22InverseFactorRelativeBudgetWith,
        Fin.append_left, Fin.append_left]
      ring
    · intro i
      rw [higham22InverseFactorRelativeBudgetWith,
        Fin.append_right, Fin.append_right]]
  rw [fin_prod_append]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hinvpow : ((1 - u) ^ 3)⁻¹ ^ n = ((1 - u) ^ (3 * n))⁻¹ := by
    rw [inv_pow, pow_mul]
  rw [hinvpow]
  simp only [higham22Theorem22_6CoefficientWith, div_eq_mul_inv]
  ring


noncomputable def higham22InverseLocalError (δ : ℂ) : ℂ :=
  -δ / (1 + δ)

theorem higham22_one_add_inverseLocalError {δ : ℂ}
    (hδ : 1 + δ ≠ 0) :
    1 + higham22InverseLocalError δ = (1 + δ)⁻¹ := by
  unfold higham22InverseLocalError
  field_simp [hδ]
  ring

theorem higham22_inverseLocalError_norm_le
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1) {δ : ℂ}
    (hδ : ‖δ‖ ≤ u) :
    ‖higham22InverseLocalError δ‖ ≤ u / (1 - u) := by
  have hδlt : ‖δ‖ < 1 := hδ.trans_lt hu1
  have hne : 1 + δ ≠ 0 := higham22_one_add_ne_zero_of_norm_lt_one hδlt
  have hdenpos : 0 < ‖1 + δ‖ := norm_pos_iff.mpr hne
  have hdenlower : 1 - u ≤ ‖1 + δ‖ := by
    have htri : (1 : ℝ) ≤ ‖1 + δ‖ + ‖δ‖ := by
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖(1 + δ) - δ‖ := by ring
        _ ≤ ‖1 + δ‖ + ‖δ‖ := norm_sub_le _ _
    linarith
  have hqnonneg : 0 ≤ u / (1 - u) := div_nonneg hu (by linarith)
  have hqident : (u / (1 - u)) * (1 - u) = u := by
    field_simp [ne_of_gt (by linarith : 0 < 1 - u)]
  have hmul : u ≤ (u / (1 - u)) * ‖1 + δ‖ := by
    calc
      u = (u / (1 - u)) * (1 - u) := hqident.symm
      _ ≤ (u / (1 - u)) * ‖1 + δ‖ :=
        mul_le_mul_of_nonneg_left hdenlower hqnonneg
  unfold higham22InverseLocalError
  rw [norm_div, norm_neg]
  exact (div_le_iff₀ hdenpos).2 (hδ.trans (by simpa [mul_comm] using hmul))

theorem higham22_complexErrorProd_inverse_eq
    (m : ℕ) (δ : Fin m → ℂ) (hne : ∀ i, 1 + δ i ≠ 0) :
    higham22ComplexErrorProd m (fun i => higham22InverseLocalError (δ i)) =
      (higham22ComplexErrorProd m δ)⁻¹ := by
  induction m with
  | zero => simp [higham22ComplexErrorProd]
  | succ m ih =>
      rw [higham22ComplexErrorProd, higham22ComplexErrorProd,
        higham22_one_add_inverseLocalError (hne 0),
        ih (fun i => δ i.succ) (fun i => hne i.succ)]
      rw [mul_inv_rev]
      ring

theorem higham22_complexErrorProd_inverse_sub_one_norm_le
    (u : ℝ) (hu : 0 ≤ u) (hu1 : u < 1)
    (m : ℕ) (δ : Fin m → ℂ) (hδ : ∀ i, ‖δ i‖ ≤ u) :
    ‖(higham22ComplexErrorProd m δ)⁻¹ - 1‖ ≤
      ((1 - u) ^ m)⁻¹ - 1 := by
  let q := u / (1 - u)
  have hq : 0 ≤ q := div_nonneg hu (by linarith)
  have hne : ∀ i, 1 + δ i ≠ 0 := fun i =>
    higham22_one_add_ne_zero_of_norm_lt_one ((hδ i).trans_lt hu1)
  have heps : ∀ i, ‖higham22InverseLocalError (δ i)‖ ≤ q := fun i =>

    higham22_inverseLocalError_norm_le u hu hu1 (hδ i)
  have h := higham22ComplexErrorProd_sub_one_norm_le q hq m
    (fun i => higham22InverseLocalError (δ i)) heps
  rw [higham22_complexErrorProd_inverse_eq m δ hne] at h
  have hone : 1 + q = (1 - u)⁻¹ := by
    dsimp [q]
    field_simp [ne_of_gt (by linarith : 0 < 1 - u)]
    ring
  rw [hone, inv_pow] at h
  exact h

theorem higham22_stageIRowMultiplier_inv_sub_one_norm_le {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) (i : Fin N) :
    ‖(higham22StageIRowMultiplier rm alpha c k i)⁻¹ - 1‖ ≤
      ((1 - rm.u) ^ 3)⁻¹ - 1 := by
  let base := rm.toHigham22ScalarRoundModel
  let a := higham22FinExtend alpha
  let x := higham22FinExtend c
  let saved := higham22StageILastSaved a k ((i : ℕ) - 1)
  by_cases hik : (i : ℕ) ≤ k
  · have hpos : 0 < (1 - rm.u) ^ 3 := pow_pos (by linarith) _
    have hbase0 : 0 ≤ 1 - rm.u := by linarith
    have hbase1 : 1 - rm.u ≤ 1 := by linarith [rm.u_nonneg]
    have hle : (1 - rm.u) ^ 3 ≤ 1 :=
      pow_le_one₀ hbase0 hbase1
    have hone : 1 ≤ ((1 - rm.u) ^ 3)⁻¹ :=
      (one_le_inv₀ hpos).2 hle
    simpa [higham22StageIRowMultiplier, hik] using sub_nonneg.mpr hone
  · by_cases heq : a i = a ((i : ℕ) - k - 1)
    · let δ := base.divError (x i) (k + 1 : ℂ)
      let eps : Fin 3 → ℂ := ![δ, 0, 0]
      have heps : ∀ r, ‖eps r‖ ≤ rm.u := by
        intro r
        fin_cases r
        · exact base.divError_bound _ _
        · simpa [eps] using rm.u_nonneg
        · simpa [eps] using rm.u_nonneg
      have h := higham22_complexErrorProd_inverse_sub_one_norm_le
        rm.u rm.u_nonneg huround 3 eps heps
      simpa [higham22StageIRowMultiplier, hik, heq, base, a, x,
        δ, eps, higham22ComplexErrorProd] using h
    · let δ0 := base.subError (x i) (x saved)
      let δ1 := rm.subDivError (a i) (a ((i : ℕ) - k - 1))
      let δ2 := base.divError
        (base.flSub (x i) (x saved))
        (base.flSub (a i) (a ((i : ℕ) - k - 1)))
      let eps : Fin 3 → ℂ := ![δ0, δ1, δ2]
      have heps : ∀ r, ‖eps r‖ ≤ rm.u := by
        intro r
        fin_cases r
        · exact base.subError_bound _ _
        · exact rm.subDivError_bound _ _
        · exact base.divError_bound _ _
      have h := higham22_complexErrorProd_inverse_sub_one_norm_le
        rm.u rm.u_nonneg huround 3 eps heps
      have heq' : alpha i ≠
          higham22FinExtend alpha ((i : ℕ) - k - 1) := by
        simpa [a] using heq
      simpa [higham22StageIRowMultiplier, hik, heq, base, a, x, saved,

        heq', δ0, δ1, δ2, eps, higham22ComplexErrorProd, mul_assoc] using h

theorem higham22_stageIRowMultiplier_ne_zero {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) (i : Fin N) :
    higham22StageIRowMultiplier rm alpha c k i ≠ 0 := by
  let base := rm.toHigham22ScalarRoundModel
  let a := higham22FinExtend alpha
  let x := higham22FinExtend c
  let saved := higham22StageILastSaved a k ((i : ℕ) - 1)
  by_cases hik : (i : ℕ) ≤ k
  · simp [higham22StageIRowMultiplier, hik]
  · by_cases heq : a i = a ((i : ℕ) - k - 1)
    · simp only [higham22StageIRowMultiplier, hik, if_false, heq, if_true,
        base, a, x]
      exact higham22_one_add_ne_zero_of_norm_lt_one
        ((base.divError_bound _ _).trans_lt huround)
    · simp only [higham22StageIRowMultiplier, hik, if_false, heq,
        base, a, x, saved]
      exact mul_ne_zero
        (mul_ne_zero
          (higham22_one_add_ne_zero_of_norm_lt_one
            ((base.subError_bound _ _).trans_lt huround))
          (higham22_one_add_ne_zero_of_norm_lt_one
            ((rm.subDivError_bound _ _).trans_lt huround)))
        (higham22_one_add_ne_zero_of_norm_lt_one
          ((base.divError_bound _ _).trans_lt huround))

noncomputable def higham22StageIRowDiagonal {N : ℕ}
    (rm : Higham22SourceRoundModel) (alpha c : Fin N → ℂ) (k : ℕ) :
    Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal (higham22StageIRowMultiplier rm alpha c k)

theorem higham22_roundedStageILowerFactor_eq_diagonal_mul {N : ℕ}
    (rm : Higham22SourceRoundModel) (alpha c : Fin N → ℂ) (k : ℕ) :
    higham22RoundedStageILowerFactor rm alpha c k =
      higham22StageIRowDiagonal rm alpha c k *
        higham22StageILowerFactor alpha k := by
  ext i j
  simp [higham22RoundedStageILowerFactor, higham22StageIRowDiagonal,
    Matrix.diagonal_mul]

theorem higham22_roundedStageILowerFactor_inverse_bound {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) :
    ∀ i j,
      ‖(higham22RoundedStageILowerFactor rm alpha c k)⁻¹ i j -
          (higham22StageILowerFactor alpha k)⁻¹ i j‖ ≤
        (((1 - rm.u) ^ 3)⁻¹ - 1) *
          ‖(higham22StageILowerFactor alpha k)⁻¹ i j‖ := by
  intro i j
  rw [higham22_roundedStageILowerFactor_eq_diagonal_mul,
    Matrix.mul_inv_rev, higham22StageIRowDiagonal, Matrix.inv_diagonal,
    Matrix.mul_diagonal]
  have hdunit : IsUnit (higham22StageIRowMultiplier rm alpha c k) := by
    rw [Pi.isUnit_iff]
    intro q
    exact (isUnit_iff_ne_zero.mpr
      (higham22_stageIRowMultiplier_ne_zero rm huround alpha c k q))
  rcases hdunit with ⟨du, hdu⟩

  have hinvApply :
      Ring.inverse (higham22StageIRowMultiplier rm alpha c k) j =
        (higham22StageIRowMultiplier rm alpha c k j)⁻¹ := by
    rw [← hdu, Ring.inverse_unit]
    have hmul :
        (↑du : Fin N → ℂ) j * (↑(du⁻¹) : Fin N → ℂ) j = 1 := by
      exact congrFun du.val_inv j
    have hduj : (↑du : Fin N → ℂ) j ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hmul
      exact zero_ne_one hmul
    exact ((mul_eq_one_iff_inv_eq₀ hduj).mp hmul).symm
  rw [hinvApply]
  change ‖(higham22StageILowerFactor alpha k)⁻¹ i j *
        (higham22StageIRowMultiplier rm alpha c k j)⁻¹ -
      (higham22StageILowerFactor alpha k)⁻¹ i j‖ ≤ _
  rw [show (higham22StageILowerFactor alpha k)⁻¹ i j *
          (higham22StageIRowMultiplier rm alpha c k j)⁻¹ -
        (higham22StageILowerFactor alpha k)⁻¹ i j =
      (higham22StageILowerFactor alpha k)⁻¹ i j *
        ((higham22StageIRowMultiplier rm alpha c k j)⁻¹ - 1) by ring,
    norm_mul]
  have h := mul_le_mul_of_nonneg_left
    (higham22_stageIRowMultiplier_inv_sub_one_norm_le
      rm huround alpha c k j)
    (norm_nonneg ((higham22StageILowerFactor alpha k)⁻¹ i j))
  simpa [mul_comm] using h

theorem higham22_reverseInverseMatrixSeq_bound {d m : ℕ}
    (X Y : Fin m → Matrix (Fin d) (Fin d) ℂ) (ρ : ℝ)
    (h : ∀ q i j, ‖(Y q)⁻¹ i j - (X q)⁻¹ i j‖ ≤
      ρ * ‖(X q)⁻¹ i j‖) :
    ∀ q i j,
      ‖higham22ReverseInverseMatrixSeq Y q i j -
          higham22ReverseInverseMatrixSeq X q i j‖ ≤
        ρ * ‖higham22ReverseInverseMatrixSeq X q i j‖ := by
  induction m with
  | zero =>
      intro q
      exact Fin.elim0 q
  | succ m ih =>
      let X0 : Fin m → Matrix (Fin d) (Fin d) ℂ := fun q => X q.castSucc
      let Y0 : Fin m → Matrix (Fin d) (Fin d) ℂ := fun q => Y q.castSucc
      let XA : Matrix (Fin d) (Fin d) ℂ := X (Fin.last m)
      let YA : Matrix (Fin d) (Fin d) ℂ := Y (Fin.last m)
      have hX : X = Fin.snoc X0 XA := by
        funext q
        refine Fin.lastCases ?_ (fun r => ?_) q
        · simp [XA]
        · simp [X0]
      have hY : Y = Fin.snoc Y0 YA := by
        funext q
        refine Fin.lastCases ?_ (fun r => ?_) q
        · simp [YA]
        · simp [Y0]
      rw [hX, hY, higham22_reverseInverseMatrixSeq_snoc,
        higham22_reverseInverseMatrixSeq_snoc]
      intro q
      refine Fin.cases ?_ (fun r => ?_) q
      · intro i j

        simpa [XA, YA] using h (Fin.last m) i j
      · intro i j
        apply ih X0 Y0
        intro r i j
        simpa [X0, Y0] using h r.castSucc i j

theorem higham22_roundedStageILowerFactorSeq_inverse_bound {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha f : Fin N → ℂ) (s : ℕ) :
    ∀ r i j,
      ‖(higham22RoundedStageILowerFactorSeq rm alpha f s r)⁻¹ i j -
          (higham22ExactStageILowerFactorSeq alpha s r)⁻¹ i j‖ ≤
        (((1 - rm.u) ^ 3)⁻¹ - 1) *
          ‖(higham22ExactStageILowerFactorSeq alpha s r)⁻¹ i j‖ := by
  induction s with
  | zero =>
      intro r
      exact Fin.elim0 r
  | succ k ih =>
      intro r
      refine Fin.cases ?_ (fun q => ?_) r
      · intro i j
        simpa [higham22RoundedStageILowerFactorSeq,
          higham22ExactStageILowerFactorSeq] using
          higham22_roundedStageILowerFactor_inverse_bound rm huround alpha
            (higham22RoundedAlgorithm22_2StageIFin
              rm.toHigham22ScalarRoundModel alpha f k) k i j
      · intro i j
        simpa [higham22RoundedStageILowerFactorSeq,
          higham22ExactStageILowerFactorSeq] using ih q i j

theorem higham22_reversedStageILowerFactorSeq_inverse_bound {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha f : Fin N → ℂ) (s : ℕ) :
    ∀ r i j,
      ‖higham22ReverseInverseMatrixSeq
            (higham22RoundedStageILowerFactorSeq rm alpha f s) r i j -
          higham22ReverseInverseMatrixSeq
            (higham22ExactStageILowerFactorSeq alpha s) r i j‖ ≤
        (((1 - rm.u) ^ 3)⁻¹ - 1) *
          ‖higham22ReverseInverseMatrixSeq
            (higham22ExactStageILowerFactorSeq alpha s) r i j‖ :=
  higham22_reverseInverseMatrixSeq_bound _ _ _
    (higham22_roundedStageILowerFactorSeq_inverse_bound
      rm huround alpha f s)

theorem higham22_reversedStageIIUpperFactorSeq_inverse_bound
    (rm : Higham22SourceRoundModel)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (c : ℝ)
    (h22_24 : Higham22Eq22_24 rm theta beta gamma alpha f c) :
    let a := higham22RoundedAlgorithm22_2StageIFin
      rm.toHigham22ScalarRoundModel alpha f n
    ∀ r i j,
      ‖higham22ReverseInverseMatrixSeq
            (higham22RoundedStageIIUpperFactorSeq
              rm.toHigham22ScalarRoundModel theta beta gamma alpha n a) r i j -
          higham22ReverseInverseMatrixSeq
            (higham22ExactStageIIUpperFactorSeq
              theta beta gamma alpha n) r i j‖ ≤

        c * ‖higham22ReverseInverseMatrixSeq
          (higham22ExactStageIIUpperFactorSeq
            theta beta gamma alpha n) r i j‖ := by
  dsimp only
  apply higham22_reverseInverseMatrixSeq_bound
  exact h22_24.2

theorem higham22_actual_inverse_factor_delta_bound
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (c : ℝ)
    (h22_24 : Higham22Eq22_24 rm theta beta gamma alpha f c) :
    ∀ r i j,
      ‖higham22RoundedAlgorithm22_2InverseFactorDelta
          rm theta beta gamma alpha f r i j‖ ≤
        higham22InverseFactorRelativeBudgetWith rm.u c n r *
          ‖higham22ExactAlgorithm22_2InverseFactorSeq
            theta beta gamma alpha r i j‖ := by
  intro r
  refine Fin.addCases ?_ ?_ r
  · intro q i j
    simpa [higham22RoundedAlgorithm22_2InverseFactorDelta,
      higham22RoundedAlgorithm22_2InverseFactorSeq,
      higham22ExactAlgorithm22_2InverseFactorSeq,
      higham22InverseFactorRelativeBudgetWith, Fin.append_right] using
      higham22_reversedStageILowerFactorSeq_inverse_bound
        rm huround alpha f n q i j
  · intro q i j
    unfold higham22RoundedAlgorithm22_2InverseFactorDelta
    dsimp only [higham22RoundedAlgorithm22_2InverseFactorSeq,
      higham22ExactAlgorithm22_2InverseFactorSeq,
      higham22InverseFactorRelativeBudgetWith]
    simp only [Fin.append_right]
    exact
      higham22_reversedStageIIUpperFactorSeq_inverse_bound
        rm theta beta gamma alpha f c h22_24 q i j

theorem higham22_theorem22_6_actual_inverse_factor_product_bound
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h22_24 : Higham22Eq22_24 rm theta beta gamma alpha f c) :
    ∀ i j,
      ‖higham22ComplexMatSeqProd (n + 1) (n + n)
            (higham22RoundedAlgorithm22_2InverseFactorSeq
              rm theta beta gamma alpha f) i j -
          higham22ComplexMatSeqProd (n + 1) (n + n)
            (higham22ExactAlgorithm22_2InverseFactorSeq
              theta beta gamma alpha) i j‖ ≤
        higham22Theorem22_6CoefficientWith n rm.u c *
          matSeqProd (n + 1) (n + n)
            (fun r => higham22NormMatrix
              (higham22ExactAlgorithm22_2InverseFactorSeq
                theta beta gamma alpha r)) i j := by
  have hscale : ∀ r,
      0 ≤ higham22InverseFactorRelativeBudgetWith rm.u c n r := by
    intro r
    refine Fin.addCases ?_ ?_ r
    · intro q
      rw [higham22InverseFactorRelativeBudgetWith, Fin.append_left]

      apply sub_nonneg.mpr
      rw [one_le_inv₀]
      · exact pow_le_one₀ (by linarith [rm.u_nonneg])
          (by linarith [rm.u_nonneg])
      · exact pow_pos (by linarith : 0 < 1 - rm.u) _
    · intro q
      rw [higham22InverseFactorRelativeBudgetWith, Fin.append_right]
      exact hc
  have hseq :
      (fun r =>
          higham22ExactAlgorithm22_2InverseFactorSeq
              theta beta gamma alpha r +
            higham22RoundedAlgorithm22_2InverseFactorDelta
              rm theta beta gamma alpha f r) =
        higham22RoundedAlgorithm22_2InverseFactorSeq
          rm theta beta gamma alpha f := by
    funext r
    ext i j
    simp [higham22RoundedAlgorithm22_2InverseFactorDelta]
  intro i j
  have h := higham22ComplexMatSeqProd_componentwise_perturbation_bound
    (n + 1) (n + n)
    (higham22ExactAlgorithm22_2InverseFactorSeq
      theta beta gamma alpha)
    (higham22RoundedAlgorithm22_2InverseFactorDelta
      rm theta beta gamma alpha f)
    (higham22InverseFactorRelativeBudgetWith rm.u c n)
    hscale
    (higham22_actual_inverse_factor_delta_bound
      rm huround theta beta gamma alpha f c h22_24) i j
  rw [hseq,
    higham22_inverseFactorRelativeBudgetWith_product
      rm.u c n huround] at h
  simpa using h

/-- Theorem 22.6 in the inverse-matrix form displayed after (22.23). -/
theorem higham22_theorem22_6_actual_inverse_matrix_bound
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h22_24 : Higham22Eq22_24 rm theta beta gamma alpha f c) :
    ∀ i j,
      ‖(higham22ComplexMatSeqProd (n + 1) (n + n)
            (higham22RoundedAlgorithm22_2FactorSeq
              rm theta beta gamma alpha f))⁻¹ i j -
          (higham22Algorithm22_2FactorProduct
            theta beta gamma alpha)⁻¹ i j‖ ≤
        higham22Theorem22_6CoefficientWith n rm.u c *
          matSeqProd (n + 1) (n + n)
            (fun r => higham22NormMatrix
              (higham22ExactAlgorithm22_2InverseFactorSeq
                theta beta gamma alpha r)) i j := by
  intro i j
  rw [← higham22_eq22_23_rounded_inverse_factor_product,
    ← higham22_eq22_23_exact_inverse_factor_product]
  exact higham22_theorem22_6_actual_inverse_factor_product_bound
    rm huround theta beta gamma alpha f c hc h22_24 i j

theorem higham22ComplexMatSeqProd_det_isUnit {d m : ℕ}
    (X : Fin m → Matrix (Fin d) (Fin d) ℂ)

    (hX : ∀ q, IsUnit (X q).det) :
    IsUnit (higham22ComplexMatSeqProd d m X).det := by
  induction m with
  | zero =>
      simp [higham22ComplexMatSeqProd]
  | succ m ih =>
      rw [higham22ComplexMatSeqProd, Matrix.det_mul]
      exact (hX 0).mul
        (ih (fun q => X q.succ) (fun q => hX q.succ))

theorem higham22_stageILowerFactor_diagonal_ne_zero {N : ℕ}
    (alpha : Fin N → ℂ) (k : ℕ) (i : Fin N) :
    higham22StageILowerFactor alpha k i i ≠ 0 := by
  rw [higham22StageILowerFactor, LinearMap.toMatrix'_apply]
  change higham22Algorithm22_2StageIStep
      (higham22FinExtend alpha)
      (higham22FinExtend (Pi.single i 1)) k i ≠ 0
  by_cases hik : (i : ℕ) ≤ k
  · simp [higham22Algorithm22_2StageIStep, hik]
  · by_cases heq : higham22FinExtend alpha i =
        higham22FinExtend alpha ((i : ℕ) - k - 1)
    · simp [higham22Algorithm22_2StageIStep, hik, heq]
      exact_mod_cast Nat.succ_ne_zero k
    · have hsave :
          higham22StageILastSaved (higham22FinExtend alpha) k
              ((i : ℕ) - 1) < (i : ℕ) := by
        have hle := higham22StageILastSaved_le
          (higham22FinExtend alpha) k ((i : ℕ) - 1) (by omega)
        omega
      have hsne :
          higham22StageILastSaved (higham22FinExtend alpha) k
              ((i : ℕ) - 1) ≠ (i : ℕ) := ne_of_lt hsave
      have heq' : alpha i ≠
          higham22FinExtend alpha ((i : ℕ) - k - 1) := by
        simpa using heq
      simp [higham22Algorithm22_2StageIStep, hik, heq,
        heq', higham22FinExtend_single, hsne]
      exact sub_ne_zero.mpr heq'

theorem higham22_stageILowerFactor_det_isUnit {N : ℕ}
    (alpha : Fin N → ℂ) (k : ℕ) :
    IsUnit (higham22StageILowerFactor alpha k).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [Matrix.det_of_lowerTriangular _
    (higham22_stageILowerFactor_lowerTriangular alpha k)]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    higham22_stageILowerFactor_diagonal_ne_zero alpha k i

theorem higham22_stageIRowDiagonal_det_isUnit {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) :
    IsUnit (higham22StageIRowDiagonal rm alpha c k).det := by
  apply isUnit_iff_ne_zero.mpr
  rw [higham22StageIRowDiagonal, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr fun i _ =>
    higham22_stageIRowMultiplier_ne_zero rm huround alpha c k i

theorem higham22_roundedStageILowerFactor_det_isUnit {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha c : Fin N → ℂ) (k : ℕ) :

    IsUnit (higham22RoundedStageILowerFactor rm alpha c k).det := by
  rw [higham22_roundedStageILowerFactor_eq_diagonal_mul,
    Matrix.det_mul]
  exact (higham22_stageIRowDiagonal_det_isUnit
    rm huround alpha c k).mul
      (higham22_stageILowerFactor_det_isUnit alpha k)

theorem higham22_roundedStageILowerFactorSeq_det_isUnit {N : ℕ}
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (alpha f : Fin N → ℂ) (s : ℕ) :
    ∀ q, IsUnit
      (higham22RoundedStageILowerFactorSeq rm alpha f s q).det := by
  induction s with
  | zero =>
      intro q
      exact Fin.elim0 q
  | succ k ih =>
      intro q
      refine Fin.cases ?_ (fun r => ?_) q
      · simpa [higham22RoundedStageILowerFactorSeq] using
          higham22_roundedStageILowerFactor_det_isUnit rm huround alpha
            (higham22RoundedAlgorithm22_2StageIFin
              rm.toHigham22ScalarRoundModel alpha f k) k
      · simpa [higham22RoundedStageILowerFactorSeq] using ih r

theorem higham22_roundedAlgorithm22_2FactorProduct_det_isUnit
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    (theta beta gamma : ℕ → ℂ) {n : ℕ}
    (alpha f : Fin (n + 1) → ℂ) (c : ℝ)
    (h22_24 : Higham22Eq22_24 rm theta beta gamma alpha f c) :
    IsUnit (higham22ComplexMatSeqProd (n + 1) (n + n)
      (higham22RoundedAlgorithm22_2FactorSeq
        rm theta beta gamma alpha f)).det := by
  apply higham22ComplexMatSeqProd_det_isUnit
  intro r
  refine Fin.addCases ?_ ?_ r
  · intro q
    simpa [higham22RoundedAlgorithm22_2FactorSeq] using h22_24.1 q
  · intro q
    unfold higham22RoundedAlgorithm22_2FactorSeq
    simp only [Fin.append_right]
    exact higham22_roundedStageILowerFactorSeq_det_isUnit
      rm huround alpha f n q

/-- Equation (22.25): the residual of the actual rounded Algorithm 22.2
output, obtained from the actual inverse-factor product estimate. -/
theorem higham22_eq22_25_actual_residual_bound
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    {theta beta gamma : ℕ → ℂ} {p : ℕ → Polynomial ℂ}
    (hp : Higham22ThreeTermRecurrence theta beta gamma p)
    (htheta : ∀ j, theta j ≠ 0) {n : ℕ}
    (alpha : Fin (n + 1) → ℂ) (hcontig : Higham22ContiguousNodes alpha)
    (f : Fin (n + 1) → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (h22_24 : Higham22Eq22_24 rm theta beta gamma alpha f c) :
    ∀ i,
      ‖f i -
          (higham22HermiteConfluentVandermondeLike
            (fun q : Fin (n + 1) => p q) alpha).transpose.mulVec
            (higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
              theta beta gamma alpha f) i‖ ≤

        higham22Theorem22_6CoefficientWith n rm.u c *
          ∑ j : Fin (n + 1),
            matSeqProd (n + 1) (n + n)
                (fun r => higham22NormMatrix
                  (higham22ExactAlgorithm22_2InverseFactorSeq
                    theta beta gamma alpha r)) i j *
              ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
                theta beta gamma alpha f j‖ := by
  let W := higham22ComplexMatSeqProd (n + 1) (n + n)
    (higham22RoundedAlgorithm22_2FactorSeq
      rm theta beta gamma alpha f)
  let A := higham22Algorithm22_2FactorProduct theta beta gamma alpha
  let P := (higham22HermiteConfluentVandermondeLike
    (fun q : Fin (n + 1) => p q) alpha).transpose
  let xhat := higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
    theta beta gamma alpha f
  have hWunit : IsUnit W.det := by
    exact higham22_roundedAlgorithm22_2FactorProduct_det_isUnit
      rm huround theta beta gamma alpha f c h22_24
  have hWx : W.mulVec f = xhat := by
    exact higham22_eq22_21_actual_rounded_factor_product
      rm huround theta beta gamma alpha f
  have hWinvx : W⁻¹.mulVec xhat = f := by
    rw [← hWx, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul W hWunit, Matrix.one_mulVec]
  have hAinv : A⁻¹ = P := by
    exact Matrix.inv_eq_right_inv
      (higham22Hermite_eq22_17_product_mul_confluentTranspose
        hp htheta alpha hcontig)
  intro i
  change ‖f i - P.mulVec xhat i‖ ≤ _
  have hres : f i - P.mulVec xhat i =
      (W⁻¹ - A⁻¹).mulVec xhat i := by
    rw [← hWinvx, hAinv]
    simp [Matrix.mulVec, dotProduct, Finset.sum_sub_distrib, sub_mul]
  rw [hres, Matrix.mulVec]
  calc
    ‖∑ j : Fin (n + 1), (W⁻¹ - A⁻¹) i j * xhat j‖
        ≤ ∑ j : Fin (n + 1), ‖(W⁻¹ - A⁻¹) i j * xhat j‖ :=
      norm_sum_le _ _
    _ = ∑ j : Fin (n + 1),
          ‖(W⁻¹ - A⁻¹) i j‖ * ‖xhat j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul]
    _ ≤ ∑ j : Fin (n + 1),
          (higham22Theorem22_6CoefficientWith n rm.u c *
            matSeqProd (n + 1) (n + n)
              (fun r => higham22NormMatrix
                (higham22ExactAlgorithm22_2InverseFactorSeq
                  theta beta gamma alpha r)) i j) * ‖xhat j‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_right
      · exact higham22_theorem22_6_actual_inverse_matrix_bound
          rm huround theta beta gamma alpha f c hc h22_24 i j
      · exact norm_nonneg _
    _ = higham22Theorem22_6CoefficientWith n rm.u c *
          ∑ j : Fin (n + 1),
            matSeqProd (n + 1) (n + n)

                (fun r => higham22NormMatrix
                  (higham22ExactAlgorithm22_2InverseFactorSeq
                    theta beta gamma alpha r)) i j * ‖xhat j‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring



noncomputable def higham22Corollary22_7UpperInverseCoefficient
    (n : ℕ) (u : ℝ) : ℝ :=
  higham22Problem22_8Coefficient (n + 1) u

noncomputable def higham22Corollary22_7Coefficient
    (n : ℕ) (u : ℝ) : ℝ :=
  higham22Theorem22_6CoefficientWith n u
    (higham22Corollary22_7UpperInverseCoefficient n u)

theorem higham22_corollary22_7_coefficient_explicit
    (n : ℕ) (u : ℝ)
    (hnu : 1 - ((n + 1 : ℕ) : ℝ) * u ≠ 0) :
    higham22Corollary22_7Coefficient n u =
      (1 - ((n + 1 : ℕ) : ℝ) * u)⁻¹ ^ n /
          (1 - u) ^ (3 * n) - 1 := by
  unfold higham22Corollary22_7Coefficient
    higham22Corollary22_7UpperInverseCoefficient
    higham22Theorem22_6CoefficientWith
    higham22Problem22_8Coefficient
  congr 2
  field_simp [hnu]
  ring

theorem higham22_corollary22_7_first_order (n : ℕ) :
    HasDerivAt (higham22Corollary22_7Coefficient n)
      ((n : ℝ) * ((n : ℝ) + 4)) 0 := by
  unfold higham22Corollary22_7Coefficient
    higham22Corollary22_7UpperInverseCoefficient
    higham22Theorem22_6CoefficientWith
    higham22Problem22_8Coefficient
  let a : ℝ := ((n + 1 : ℕ) : ℝ)
  have hlin : HasDerivAt (fun u : ℝ => a * u) a 0 := by
    simpa using HasDerivAt.const_mul a (hasDerivAt_id (0 : ℝ))
  have hden : HasDerivAt (fun u : ℝ => 1 - a * u) (-a) 0 := by
    simpa using hlin.const_sub 1
  have hfrac : HasDerivAt
      (fun u : ℝ => a * u / (1 - a * u)) a 0 := by
    convert hlin.div hden (by norm_num) using 1 <;> norm_num
  have hone : HasDerivAt
      (fun u : ℝ => 1 + a * u / (1 - a * u)) a 0 := by
    simpa using hfrac.const_add 1
  have hnum := hone.pow n
  have hbase : HasDerivAt (fun u : ℝ => 1 - u) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub 1
  have hdenpow := hbase.pow (3 * n)
  have hden0 : ((fun u : ℝ => 1 - u) ^ (3 * n)) 0 ≠ 0 := by
    simp
  have hquot := hnum.div hdenpow hden0
  have hfinal := hquot.sub_const 1
  convert hfinal using 1
  all_goals simp [a] <;> push_cast <;> ring

/-- Conditional monomial residual specialization at the coefficient stated by
Corollary 22.7.  The explicit `h22_24` argument marks the remaining producer
gap: the source invokes Problem 22.8 to supply this specialization at dimension
`n+1`, whereas the current theorem does not yet derive it from the actual
rounded Stage-II factors.  The derivative theorem above records the printed
`n(n+4)u + O(u²)` first-order coefficient. -/
theorem higham22_corollary22_7_monomial_residual
    (rm : Higham22SourceRoundModel) (huround : rm.u < 1)
    {n : ℕ} (alpha : Fin (n + 1) → ℝ) (halpha : StrictMono alpha)
    (f : Fin (n + 1) → ℂ)

    (hvalid : gammaValid
      (FPModel.exactWithUnitRoundoff rm.u rm.u_nonneg) (n + 1))
    (h22_24 : Higham22Eq22_24 rm
      higham22MonomialTheta higham22MonomialBeta higham22MonomialGamma
      (fun i => (alpha i : ℂ)) f
      (higham22Corollary22_7UpperInverseCoefficient n rm.u)) :
    ∀ i,
      ‖f i -
          (higham22HermiteConfluentVandermondeLike
            (fun q : Fin (n + 1) =>
              higham22PolynomialSequence higham22MonomialTheta
                higham22MonomialBeta higham22MonomialGamma q)
            (fun q => (alpha q : ℂ))).transpose.mulVec
            (higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
              higham22MonomialTheta higham22MonomialBeta
              higham22MonomialGamma (fun q => (alpha q : ℂ)) f) i‖ ≤
        higham22Corollary22_7Coefficient n rm.u *
          ∑ j : Fin (n + 1),
            matSeqProd (n + 1) (n + n)
                (fun r => higham22NormMatrix
                  (higham22ExactAlgorithm22_2InverseFactorSeq
                    higham22MonomialTheta higham22MonomialBeta
                    higham22MonomialGamma (fun q => (alpha q : ℂ)) r)) i j *
              ‖higham22RoundedAlgorithm22_2 rm.toHigham22ScalarRoundModel
                higham22MonomialTheta higham22MonomialBeta
                higham22MonomialGamma (fun q => (alpha q : ℂ)) f j‖ := by
  have hcontig : Higham22ContiguousNodes (fun q => (alpha q : ℂ)) := by
    intro i j hij heq
    have heqr : alpha i = alpha j := Complex.ofReal_injective heq
    exact (ne_of_lt hij (halpha.injective heqr)).elim
  have hc : 0 ≤ higham22Corollary22_7UpperInverseCoefficient n rm.u := by
    unfold higham22Corollary22_7UpperInverseCoefficient
      higham22Problem22_8Coefficient
    have hv := hvalid
    unfold gammaValid at hv
    dsimp [FPModel.exactWithUnitRoundoff] at hv
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg _) rm.u_nonneg
    · linarith
  simpa [higham22Corollary22_7Coefficient] using
    higham22_eq22_25_actual_residual_bound rm huround
      higham22_table22_2_monomial
      (by intro j; norm_num [higham22MonomialTheta])
      (fun q => (alpha q : ℂ)) hcontig f
      (higham22Corollary22_7UpperInverseCoefficient n rm.u) hc h22_24


end NumStability
