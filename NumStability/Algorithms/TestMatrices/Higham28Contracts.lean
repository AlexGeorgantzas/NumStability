/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.TestMatrices.Higham28Probability
import NumStability.Algorithms.TestMatrices.Higham28RandsvdNorm
import NumStability.Algorithms.TestMatrices.Higham28Asymptotics
import NumStability.Algorithms.TestMatrices.Higham28Pascal
import NumStability.Algorithms.HighamChapter9
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Block

namespace NumStability

open scoped BigOperators

/-! # Higham Chapter 28: deterministic contracts and exact constructions

The exact algebra proved in `Higham28` and `Higham28Exact` is unconditional.
This companion module proves further source-facing constructions where the
needed finite algebra is available and records only genuine upstream domains
for citation-dependent remainder.  Printed conclusions are never themselves
assumed.
-/

/-! ## Cauchy minors and total positivity -/

/-- Strict total positivity, stated on every square submatrix selected by
strictly increasing row and column embeddings. -/
def IsStrictlyTotallyPositive {m n : ℕ} (A : RMat m n) : Prop :=
  ∀ (k : ℕ) (_hk : 0 < k) (r : Fin k → Fin m) (c : Fin k → Fin n),
    StrictMono r → StrictMono c →
      0 < Matrix.det (fun i j => A (r i) (c j))

/-- Numerator of the square Cauchy determinant product. -/
noncomputable def cauchyDetNumerator (n : ℕ) (x y : RVec n) : ℝ :=
  ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) * (y j - y i)

/-- Denominator of the square Cauchy determinant product. -/
noncomputable def cauchyDetDenominator (n : ℕ) (x y : RVec n) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, (x i + y j)

theorem cauchyDetFormula_eq_num_div_den (n : ℕ) (x y : RVec n) :
    cauchyDetFormula n x y =
      cauchyDetNumerator n x y / cauchyDetDenominator n x y := rfl

/-- Source-only regularity assumptions for the printed square Cauchy
formulas.  These hypotheses say that the two node families have no repeats
and that every matrix denominator is nonzero; they contain none of the
determinant, inverse, LU, or total-positivity conclusions. -/
structure CauchyAdmissible {n : ℕ} (x y : RVec n) : Prop where
  x_injective : Function.Injective x
  y_injective : Function.Injective y
  sum_ne_zero : ∀ i j, x i + y j ≠ 0

theorem cauchyAdmissible_of_strictMono_of_pos
    {n : ℕ} (x y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j) :
    CauchyAdmissible x y where
  x_injective := hx.injective
  y_injective := hy.injective
  sum_ne_zero := fun i j ↦ ne_of_gt (hsum i j)

/-- Under the actual source regularity assumptions, the denominator in the
printed Cauchy determinant product is nonzero. -/
theorem cauchyDetDenominator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyDetDenominator n x y ≠ 0 := by
  unfold cauchyDetDenominator
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j _
  exact h.sum_ne_zero i j

/-- Distinct source nodes also make every Vandermonde factor in the numerator
nonzero. -/
theorem cauchyDetNumerator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyDetNumerator n x y ≠ 0 := by
  unfold cauchyDetNumerator
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro i _
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  apply mul_ne_zero
  · exact sub_ne_zero.mpr fun heq ↦
      (ne_of_gt hij) (h.x_injective heq)
  · exact sub_ne_zero.mpr fun heq ↦
      (ne_of_gt hij) (h.y_injective heq)

/-- Consequently the right-hand side of Cauchy's printed determinant formula
is itself nonzero.  The remaining open step is proving that it equals the
matrix determinant. -/
theorem cauchyDetFormula_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y) :
    cauchyDetFormula n x y ≠ 0 := by
  rw [cauchyDetFormula_eq_num_div_den]
  exact div_ne_zero (cauchyDetNumerator_ne_zero h)
    (cauchyDetDenominator_ne_zero h)

/-- The paired numerator exactly as printed in the inverse-entry formula. -/
noncomputable def cauchyInverseNumerator
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  ∏ k : Fin n, (x j + y k) * (x k + y i)

/-- The three denominator factors exactly as printed in the inverse-entry
formula. -/
noncomputable def cauchyInverseDenominator
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  (x j + y i) *
    (∏ k ∈ Finset.univ.erase j, (x j - x k)) *
    (∏ k ∈ Finset.univ.erase i, (y i - y k))

theorem cauchyInverseEntry_eq_num_div_den
    (n : ℕ) (x y : RVec n) (i j : Fin n) :
    cauchyInverseEntry n x y i j =
      cauchyInverseNumerator n x y i j /
        cauchyInverseDenominator n x y i j := rfl

theorem cauchyInverseNumerator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseNumerator n x y i j ≠ 0 := by
  unfold cauchyInverseNumerator
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro k _
  exact mul_ne_zero (h.sum_ne_zero j k) (h.sum_ne_zero k i)

theorem cauchyInverseDenominator_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseDenominator n x y i j ≠ 0 := by
  unfold cauchyInverseDenominator
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact h.sum_ne_zero j i
    · refine Finset.prod_ne_zero_iff.mpr ?_
      intro k hk
      rcases Finset.mem_erase.mp hk with ⟨hkj, _⟩
      exact sub_ne_zero.mpr fun heq ↦
        hkj (h.x_injective heq).symm
  · refine Finset.prod_ne_zero_iff.mpr ?_
    intro k hk
    rcases Finset.mem_erase.mp hk with ⟨hki, _⟩
    exact sub_ne_zero.mpr fun heq ↦
      hki (h.y_injective heq).symm

/-- Every displayed candidate inverse entry is well-defined and nonzero on
the genuine source domain.  This is a precursor, not the missing matrix
inverse theorem. -/
theorem cauchyInverseEntry_ne_zero
    {n : ℕ} {x y : RVec n} (h : CauchyAdmissible x y)
    (i j : Fin n) :
    cauchyInverseEntry n x y i j ≠ 0 := by
  rw [cauchyInverseEntry_eq_num_div_den]
  exact div_ne_zero (cauchyInverseNumerator_ne_zero h i j)
    (cauchyInverseDenominator_ne_zero h i j)

/-- Higham's unit-lower Cauchy `L` formula, translated from
`1 ≤ j < i ≤ n` to zero-based `Fin n` indices. -/
noncomputable def cauchyLowerEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  if j < i then
    ((x j + y j) / (x i + y j)) *
      (∏ k ∈ Finset.Iio j,
        ((x j + y k) * (x i - x k)) /
          ((x i + y k) * (x j - x k)))
  else if i = j then 1 else 0

/-- Higham's upper Cauchy `U` formula on the source range
`1 ≤ i ≤ j ≤ n`. -/
noncomputable def cauchyUpperEntry
    (n : ℕ) (x y : RVec n) (i j : Fin n) : ℝ :=
  if i ≤ j then
    ((∏ k ∈ Finset.Iio i, (x i - x k) * (y j - y k)) /
      ((x i + y j) *
        (∏ k ∈ Finset.Iio i, (x i + y k) * (x k + y j))))
  else 0

noncomputable def cauchyLower
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j ↦ cauchyLowerEntry n x y i j

noncomputable def cauchyUpper
    (n : ℕ) (x y : RVec n) : RSqMat n :=
  fun i j ↦ cauchyUpperEntry n x y i j

@[simp]
theorem cauchyLower_diagonal
    {n : ℕ} (x y : RVec n) (i : Fin n) :
    cauchyLower n x y i i = 1 := by
  simp [cauchyLower, cauchyLowerEntry]

theorem cauchyLower_entry_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hji : j < i) :
    cauchyLower n x y i j =
      ((x j + y j) / (x i + y j)) *
        (∏ k ∈ Finset.Iio j,
          ((x j + y k) * (x i - x k)) /
            ((x i + y k) * (x j - x k))) := by
  simp [cauchyLower, cauchyLowerEntry, hji]

theorem cauchyUpper_entry_of_le
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hij : i ≤ j) :
    cauchyUpper n x y i j =
      (∏ k ∈ Finset.Iio i, (x i - x k) * (y j - y k)) /
        ((x i + y j) *
          (∏ k ∈ Finset.Iio i, (x i + y k) * (x k + y j))) := by
  simp [cauchyUpper, cauchyUpperEntry, hij]

theorem cauchyLower_zero_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hij : i < j) :
    cauchyLower n x y i j = 0 := by
  simp [cauchyLower, cauchyLowerEntry, hij.asymm, hij.ne]

theorem cauchyUpper_zero_of_lt
    {n : ℕ} (x y : RVec n) (i j : Fin n) (hji : j < i) :
    cauchyUpper n x y i j = 0 := by
  simp [cauchyUpper, cauchyUpperEntry, show ¬i ≤ j by omega]

/-- The exact scalar Schur-complement identity for the first Cauchy pivot.
It is the local algebra needed by a genuine induction for the determinant and
Cho LU formulas. -/
theorem cauchy_firstPivot_schur_entry
    (xi x0 yj y0 : ℝ)
    (hij : xi + yj ≠ 0) (hi0 : xi + y0 ≠ 0)
    (h0j : x0 + yj ≠ 0) :
    1 / (xi + yj) -
        ((x0 + y0) / (xi + y0)) * (1 / (x0 + yj)) =
      ((xi - x0) * (yj - y0)) /
        ((xi + yj) * (xi + y0) * (x0 + yj)) := by
  field_simp
  ring

/-- Ordered positive Cauchy nodes make the printed determinant product
strictly positive. -/
theorem cauchyDetFormula_pos_of_strictMono_of_pos
    {n : ℕ} (x y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j) :
    0 < cauchyDetFormula n x y := by
  rw [cauchyDetFormula_eq_num_div_den]
  apply div_pos
  · unfold cauchyDetNumerator
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    exact mul_pos (sub_pos.mpr (hx hij)) (sub_pos.mpr (hy hij))
  · unfold cauchyDetDenominator
    exact Finset.prod_pos fun i _ ↦ Finset.prod_pos fun j _ ↦ hsum i j

/-- The determinant-product side of every ordered Cauchy minor is positive.
The still-open foundation is the equality between this product and the
minor's matrix determinant. -/
theorem cauchyMinorDetFormula_pos
    {m n k : ℕ} (x : RVec m) (y : RVec n)
    (hx : StrictMono x) (hy : StrictMono y)
    (hsum : ∀ i j, 0 < x i + y j)
    (r : Fin k → Fin m) (c : Fin k → Fin n)
    (hr : StrictMono r) (hc : StrictMono c) :
    0 < cauchyDetFormula k (fun i ↦ x (r i)) (fun j ↦ y (c j)) := by
  apply cauchyDetFormula_pos_of_strictMono_of_pos
  · exact hx.comp hr
  · exact hy.comp hc
  · exact fun i j ↦ hsum (r i) (c j)

/-! The general determinant equality, inverse products, Cho LU product,
inverse-entry sum, and strict total positivity remain open.  They require a
genuine finite Cauchy determinant/partial-fraction induction; no proposition
containing one of those identities is used here as a substitute proof. -/

/-! ## Pascal similarity, perturbation, and cube roots -/

/-- The signed Pascal involution conjugates the symmetric Pascal matrix to
its proved inverse.  Unlike the citation-dependent spectral consequence,
this matrix identity follows entirely from the local binomial algebra. -/
theorem signedPascal_conj_pascalMatrix (n : ℕ) :
    signedPascal n * pascalMatrix n * signedPascal n =
      (signedPascal n).transpose * signedPascal n := by
  rw [pascalMatrix_eq_lower_mul_transpose,
    signedPascal_eq_lower_mul_signDiagonal]
  have hleft := pascal_lower_sign_lower_eq_sign n
  calc
    (pascalLower n * pascalSignDiagonal n) *
        (pascalLower n * (pascalLower n).transpose) *
        (pascalLower n * pascalSignDiagonal n) =
      (pascalLower n * pascalSignDiagonal n * pascalLower n) *
        ((pascalLower n).transpose * pascalLower n) *
        pascalSignDiagonal n := by noncomm_ring
    _ = pascalSignDiagonal n *
        ((pascalLower n).transpose * pascalLower n) *
        pascalSignDiagonal n := by rw [hleft]
    _ = (pascalLower n * pascalSignDiagonal n).transpose *
        (pascalLower n * pascalSignDiagonal n) := by
      rw [Matrix.transpose_mul, pascalSignDiagonal_transpose]
      noncomm_ring

/-- The reciprocal-eigenvalue consequence of the proved Pascal similarity.
No spectral theorem is assumed: the proof applies the explicit inverse and
the signed involution directly to an eigenvector. -/
theorem pascal_reciprocal_eigenpair
    {n : ℕ} (lambda : ℝ) (v : RVec n)
    (hlambda : lambda ≠ 0) (hv : v ≠ 0)
    (heigen : Matrix.mulVec (pascalMatrix n) v = lambda • v) :
    let w := Matrix.mulVec (signedPascal n) v
    w ≠ 0 ∧ Matrix.mulVec (pascalMatrix n) w = lambda⁻¹ • w := by
  let P := pascalMatrix n
  let S := signedPascal n
  let B := (signedPascal n).transpose * signedPascal n
  let w := Matrix.mulVec S v
  have heigenP : Matrix.mulVec P v = lambda • v := by
    simpa [P] using heigen
  have hSS : S * S = (1 : RSqMat n) := signedPascal_mul_self n
  have hPw : P * B = (1 : RSqMat n) := pascalMatrix_mul_signedGram n
  have hsim : S * P * S = B := signedPascal_conj_pascalMatrix n
  have hSw : Matrix.mulVec S w = v := by
    rw [show w = Matrix.mulVec S v by rfl, Matrix.mulVec_mulVec, hSS,
      Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    rw [← hSw, hw0]
    simp
  have hBw : Matrix.mulVec B w = lambda • w := by
    calc
      Matrix.mulVec B w = Matrix.mulVec (S * P * S) w := by rw [hsim]
      _ = Matrix.mulVec (S * P) (Matrix.mulVec S w) := by
        exact (Matrix.mulVec_mulVec w (S * P) S).symm
      _ = Matrix.mulVec S (Matrix.mulVec P (Matrix.mulVec S w)) := by
        exact (Matrix.mulVec_mulVec (Matrix.mulVec S w) S P).symm
      _ = Matrix.mulVec S (Matrix.mulVec P v) := by rw [hSw]
      _ = Matrix.mulVec S (lambda • v) := by rw [heigenP]
      _ = lambda • w := by rw [Matrix.mulVec_smul]
  have happly := congrArg (Matrix.mulVec P) hBw
  have hscale : w = lambda • Matrix.mulVec P w := by
    simpa [Matrix.mulVec_mulVec, hPw, Matrix.mulVec_smul] using happly
  change w ≠ 0 ∧ Matrix.mulVec P w = lambda⁻¹ • w
  refine ⟨hw, ?_⟩
  funext i
  have hi := congrFun hscale i
  simp only [Pi.smul_apply, smul_eq_mul] at hi ⊢
  calc
    Matrix.mulVec P w i = lambda⁻¹ * (lambda * Matrix.mulVec P w i) := by
      field_simp
    _ = lambda⁻¹ * w i := by rw [← hi]
    _ = (lambda⁻¹ • w) i := by simp

/-- Corrected all-orders form of the characteristic-polynomial reciprocity
claim on p. 519.  Mathlib's convention is `det(XI-P)`, so odd orders are
anti-palindromic and even orders are palindromic.  The source's sign-free
identity is therefore valid only in even order (already `n=1` is a
counterexample). -/
theorem pascal_charpoly_reciprocal (n : ℕ) :
    (pascalMatrix n).charpoly =
      Polynomial.C ((-1 : ℝ) ^ n) * (pascalMatrix n).charpoly.reverse := by
  let P : RSqMat n := pascalMatrix n
  let S : RSqMat n := signedPascal n
  let B : RSqMat n := S.transpose * S
  have hdet : IsUnit (Matrix.det P) := by
    rw [show Matrix.det P = 1 by simpa [P] using pascalMatrix_det n]
    exact isUnit_one
  have hPunit : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).mpr hdet
  have hBinv : P⁻¹ = B := by
    have hBP : B * P = (1 : RSqMat n) := by
      simpa [P, B, S] using signedGram_mul_pascalMatrix n
    calc
      P⁻¹ = 1 * P⁻¹ := by rw [Matrix.one_mul]
      _ = (B * P) * P⁻¹ := by rw [hBP]
      _ = B * (P * P⁻¹) := by rw [Matrix.mul_assoc]
      _ = B := by rw [Matrix.mul_nonsing_inv P hdet, Matrix.mul_one]
  have hcharB : B.charpoly = P.charpoly := by
    have hconj : S * P * S = B := by
      simpa [P, S, B] using signedPascal_conj_pascalMatrix n
    rw [← hconj]
    calc
      (S * P * S).charpoly = (S * (P * S)).charpoly := by
        rw [Matrix.mul_assoc]
      _ = (P * S * S).charpoly := Matrix.charpoly_mul_comm S (P * S)
      _ = P.charpoly := by
        rw [Matrix.mul_assoc]
        have hSS : S * S = (1 : RSqMat n) := by
          simpa [S] using signedPascal_mul_self n
        rw [hSS, Matrix.mul_one]
  have hcharInv : P⁻¹.charpoly = P.charpoly := by rw [hBinv, hcharB]
  have hinv := Matrix.charpoly_inv P hPunit
  rw [hcharInv] at hinv
  have hdetOne : Matrix.det P = 1 := by simpa [P] using pascalMatrix_det n
  rw [hdetOne] at hinv
  simp only [Ring.inverse_one, Polynomial.C_1, mul_one,
    Fintype.card_fin] at hinv
  rw [← Matrix.reverse_charpoly] at hinv
  simpa [P] using hinv

/-- In even order the corrected theorem specializes to the sign-free
palindromic identity printed by Higham. -/
theorem pascal_charpoly_palindromic_of_even (n : ℕ) (hn : Even n) :
    (pascalMatrix n).charpoly = (pascalMatrix n).charpoly.reverse := by
  calc
    (pascalMatrix n).charpoly =
        Polynomial.C ((-1 : ℝ) ^ n) *
          (pascalMatrix n).charpoly.reverse := pascal_charpoly_reciprocal n
    _ = (pascalMatrix n).charpoly.reverse := by
      rw [Even.neg_one_pow hn]
      simp

/-- The final coordinate vector for an order-`n+1` Pascal matrix. -/
noncomputable def pascalLastBasis (n : ℕ) : RVec (n + 1) :=
  Pi.single (Fin.last n) 1

/-- The matrix that subtracts one from the final diagonal entry and changes
no other entry. -/
noncomputable def pascalLastEntryPerturbation (n : ℕ) : RSqMat (n + 1) :=
  Matrix.single (Fin.last n) (Fin.last n) (-1)

@[simp]
theorem pascalLastEntryPerturbation_apply (n : ℕ) (i j : Fin (n + 1)) :
    pascalLastEntryPerturbation n i j =
      if i = Fin.last n ∧ j = Fin.last n then -1 else 0 := by
  simp [pascalLastEntryPerturbation, Matrix.single_apply, eq_comm]

/-- The last column of the proved inverse `SᵀS`.  It is the source's
rank-one-perturbation kernel certificate. -/
noncomputable def pascalLastKernel (n : ℕ) : RVec (n + 1) :=
  Matrix.mulVec
    ((signedPascal (n + 1)).transpose * signedPascal (n + 1))
    (pascalLastBasis n)

@[simp]
theorem pascalLastKernel_last (n : ℕ) :
    pascalLastKernel n (Fin.last n) = 1 := by
  rw [pascalLastKernel, pascalLastBasis, Matrix.mulVec_single_one]
  change ((signedPascal (n + 1)).transpose * signedPascal (n + 1))
    (Fin.last n) (Fin.last n) = 1
  rw [pascalInverseFormula_apply_of_le (Fin.last n) (Fin.last n) le_rfl]
  simp

theorem pascalLastKernel_ne_zero (n : ℕ) : pascalLastKernel n ≠ 0 := by
  intro hzero
  have h := congrFun hzero (Fin.last n)
  simp at h

theorem pascalMatrix_mulVec_pascalLastKernel (n : ℕ) :
    Matrix.mulVec (pascalMatrix (n + 1)) (pascalLastKernel n) =
      pascalLastBasis n := by
  rw [pascalLastKernel, Matrix.mulVec_mulVec,
    pascalMatrix_mul_signedGram, Matrix.one_mulVec]

theorem pascalLastEntryPerturbation_mulVec_pascalLastKernel (n : ℕ) :
    Matrix.mulVec (pascalLastEntryPerturbation n) (pascalLastKernel n) =
      -pascalLastBasis n := by
  rw [pascalLastEntryPerturbation, Matrix.single_mulVec,
    pascalLastKernel_last]
  funext i
  by_cases hi : i = Fin.last n
  · subst i
    simp [pascalLastBasis]
  · simp [pascalLastBasis, hi]

/-- Higham, 2nd ed., Section 28.4, p. 520: subtracting one from the final
diagonal entry of every nonempty symmetric Pascal matrix makes it singular.
The conclusion supplies an explicit nonzero kernel vector, rather than
assuming singularity or a determinant identity. -/
theorem pascal_sub_last_entry_has_nonzero_kernel (n : ℕ) :
    ∃ z : RVec (n + 1), z ≠ 0 ∧
      Matrix.mulVec
        (pascalMatrix (n + 1) + pascalLastEntryPerturbation n) z = 0 := by
  refine ⟨pascalLastKernel n, pascalLastKernel_ne_zero n, ?_⟩
  rw [Matrix.add_mulVec, pascalMatrix_mulVec_pascalLastKernel,
    pascalLastEntryPerturbation_mulVec_pascalLastKernel]
  simp

/-- A concrete coordinate certificate for a singular rank-one perturbation.
The cancellation premise is the upstream entrywise arithmetic calculation,
not a matrix-singularity assumption. -/
theorem singular_rankOne_perturbation_of_coordinate_cancellation
    {n : ℕ} (A : RSqMat n) (u v z : RVec n)
    (hz : z ≠ 0)
    (hcancel : ∀ i : Fin n,
      (∑ j : Fin n, (A i j + u i * v j) * z j) = 0) :
    ∃ E : RSqMat n, (∀ i j, E i j = u i * v j) ∧
      ∃ z ≠ 0, Matrix.mulVec (A + E) z = 0 := by
  refine ⟨fun i j => u i * v j, fun _ _ => rfl, z, hz, ?_⟩
  funext i
  simpa [Matrix.mulVec, dotProduct] using hcancel i

/-- The rank-one perturbation contract is nonvacuous already for the
order-one Pascal matrix: subtracting its sole entry makes it singular. -/
theorem pascal_order_one_has_singular_rankOne_perturbation :
    ∃ E : RSqMat 1, (∀ i j, E i j = (-1 : ℝ) * 1) ∧
      ∃ z ≠ 0, Matrix.mulVec (pascalMatrix 1 + E) z = 0 := by
  apply singular_rankOne_perturbation_of_coordinate_cancellation
    (pascalMatrix 1) (fun _ => -1) (fun _ => 1) (fun _ => 1)
  · intro h
    have := congrFun h (0 : Fin 1)
    norm_num at this
  · intro i
    fin_cases i
    norm_num [pascalMatrix, Fin.sum_univ_succ]

/-! ## Toeplitz discrete-sine and companion constructions -/

/-- The displayed sine vector for the symmetric tridiagonal Toeplitz family. -/
noncomputable def toeplitzSineVector (n : ℕ) (k : Fin n) : RVec n :=
  fun i => Real.sin (((i.val + 1 : ℕ) * (k.val + 1 : ℕ) : ℝ) *
    Real.pi / (n + 1 : ℕ))

/-- The displayed eigenvalue `d + 2c cos(k*pi/(n+1))`, with source index
`k=1,...,n` translated to `Fin n`. -/
noncomputable def symmetricToeplitzEigenvalue
    (n : ℕ) (c d : ℝ) (k : Fin n) : ℝ :=
  d + 2 * c * Real.cos (((k.val + 1 : ℕ) : ℝ) * Real.pi /
    (n + 1 : ℕ))

/-- Multiplication by a tridiagonal Toeplitz matrix reduces to the diagonal
entry and the at most two neighboring vector entries. -/
theorem tridiagonalToeplitz_mulVec_apply
    {n : ℕ} (c d e : ℝ) (x : RVec n) (i : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d e) x i =
      d * x i +
        (if h : i.val + 1 < n then e * x ⟨i.val + 1, h⟩ else 0) +
        (if h : 0 < i.val then c * x ⟨i.val - 1, by omega⟩ else 0) := by
  let A : RSqMat n := fun r _ => x r
  have h := tridiagonalToeplitz_mul_apply_right n c d e A i i
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, A] using h

private theorem sin_neighbor_identity (x θ : ℝ) :
    Real.sin (x - θ) + Real.sin (x + θ) =
      2 * Real.cos θ * Real.sin x := by
  rw [Real.sin_sub, Real.sin_add]
  ring

private theorem toeplitzSineVector_angle
    {n : ℕ} (k i : Fin n) :
    toeplitzSineVector n k i =
      Real.sin (((i.val + 1 : ℕ) : ℝ) *
        ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) := by
  unfold toeplitzSineVector
  congr 1
  push_cast
  ring

private theorem toeplitz_sine_boundary
    {n : ℕ} (k : Fin n) :
    Real.sin (((n + 1 : ℕ) : ℝ) *
      ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) = 0 := by
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  rw [show (((n + 1 : ℕ) : ℝ) *
      ((((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ))) =
      ((k.val + 1 : ℕ) : ℝ) * Real.pi by field_simp]
  exact Real.sin_nat_mul_pi (k.val + 1)

/-- Higham, p. 522: the displayed sine vector is an actual eigenvector of the
symmetric tridiagonal Toeplitz matrix.  The trigonometric recurrence and both
boundary cases are proved here, rather than supplied as a hypothesis. -/
theorem symmetricToeplitz_sine_eigenpair
    {n : ℕ} (c d : ℝ) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d c)
        (toeplitzSineVector n k) =
      symmetricToeplitzEigenvalue n c d k • toeplitzSineVector n k := by
  funext i
  rw [tridiagonalToeplitz_mulVec_apply]
  rw [show symmetricToeplitzEigenvalue n c d k =
      d + 2 * c * Real.cos
        (((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)) by rfl]
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [toeplitzSineVector_angle]
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  let x : ℝ := ((i.val + 1 : ℕ) : ℝ) * θ
  rw [show (((k.val + 1 : ℕ) : ℝ) * Real.pi / ((n + 1 : ℕ) : ℝ)) = θ by rfl]
  by_cases hs : i.val + 1 < n
  · by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hcur : ((i.val + 1 : ℕ) : ℝ) * θ = x := rfl
      have hsucc :
          ((i.val + 1 + 1 : ℕ) : ℝ) * θ = x + θ := by
        dsimp [x]
        push_cast
        ring
      have hpred :
          ((i.val - 1 + 1 : ℕ) : ℝ) * θ = x - θ := by
        rw [Nat.sub_add_cancel hp]
        dsimp [x]
        push_cast
        ring
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val + 1 + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val - 1 + 1 : ℕ) : ℝ) * θ) =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hcur, hsucc, hpred]
      have hrec := sin_neighbor_identity x θ
      linear_combination c * hrec
    · have hi0 : i.val = 0 := by omega
      simp only [hs, hp, ↓reduceDIte]
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) +
          c * Real.sin (((i.val + 1 + 1 : ℕ) : ℝ) * θ) + 0 =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hi0]
      norm_num
      rw [show 2 * θ = θ + θ by ring, Real.sin_add]
      ring
  · have hilast : i.val + 1 = n := by omega
    by_cases hp : 0 < i.val
    · simp only [hs, hp, ↓reduceDIte]
      have hcur : ((i.val + 1 : ℕ) : ℝ) * θ = x := rfl
      have hpred :
          ((i.val - 1 + 1 : ℕ) : ℝ) * θ = x - θ := by
        rw [Nat.sub_add_cancel hp]
        dsimp [x]
        push_cast
        ring
      have hboundary : Real.sin (x + θ) = 0 := by
        rw [show x + θ = ((n + 1 : ℕ) : ℝ) * θ by
          dsimp [x]
          rw [show ((i.val + 1 : ℕ) : ℝ) = (n : ℝ) by exact_mod_cast hilast]
          push_cast
          ring]
        exact toeplitz_sine_boundary k
      change d * Real.sin (((i.val + 1 : ℕ) : ℝ) * θ) + 0 +
          c * Real.sin (((i.val - 1 + 1 : ℕ) : ℝ) * θ) =
        (d + 2 * c * Real.cos θ) *
          Real.sin (((i.val + 1 : ℕ) : ℝ) * θ)
      rw [hcur, hpred]
      have hrec := sin_neighbor_identity x θ
      rw [hboundary] at hrec
      linear_combination c * hrec
    · have hn1 : n = 1 := by omega
      subst n
      fin_cases i
      fin_cases k
      dsimp [θ, x]
      norm_num [toeplitzSineVector, symmetricToeplitzEigenvalue]

/-- The displayed sine eigenvector is nonzero; its first component has angle
strictly between zero and pi. -/
theorem toeplitzSineVector_ne_zero
    {n : ℕ} (k : Fin n) : toeplitzSineVector n k ≠ 0 := by
  let i0 : Fin n := ⟨0, Nat.zero_lt_of_lt k.isLt⟩
  let θ : ℝ := (((k.val + 1 : ℕ) : ℝ) * Real.pi) / ((n + 1 : ℕ) : ℝ)
  have hden : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hratio : ((k.val + 1 : ℕ) : ℝ) < ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ k.isLt
  have hθlt : θ < Real.pi := by
    dsimp [θ]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθpos hθlt
  intro hzero
  have hz := congrFun hzero i0
  have hi : toeplitzSineVector n k i0 = Real.sin θ := by
    rw [toeplitzSineVector_angle]
    simp [i0, θ]
  rw [hi] at hz
  exact (ne_of_gt hsin) hz

private theorem scaledSineColumn_eq
    {n : ℕ} (k : Fin n) :
    (fun i : Fin n => higham9_12_sineMatrix n i k) =
      Real.sqrt (2 / ((n : ℝ) + 1)) • toeplitzSineVector n k := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold higham9_12_sineMatrix toeplitzSineVector
  congr 2
  norm_num [Nat.cast_add]

/-- The normalized discrete-sine columns are eigenvectors as well. -/
theorem symmetricToeplitz_scaled_sine_eigenpair
    {n : ℕ} (c d : ℝ) (k : Fin n) :
    Matrix.mulVec (tridiagonalToeplitz n c d c)
        (fun i => higham9_12_sineMatrix n i k) =
      symmetricToeplitzEigenvalue n c d k •
        (fun i => higham9_12_sineMatrix n i k) := by
  rw [scaledSineColumn_eq]
  rw [Matrix.mulVec_smul, symmetricToeplitz_sine_eigenpair]
  simp [smul_smul, mul_comm]

/-- The normalized sine matrix is orthogonal, reusing the independently
proved finite sine-product identity from Chapter 9. -/
theorem higham9_sineMatrix_isOrthogonal
    {n : ℕ} (hn : 0 < n) : IsOrthogonal n (higham9_12_sineMatrix n) := by
  apply IsOrthogonal.of_col_orthonormal
  intro i j
  simpa [higham9_12_sineMatrix_symm] using
    higham9_12_sineMatrix_mul_self hn i j

/-- Exact orthogonal diagonalization of every nonempty symmetric tridiagonal
Toeplitz matrix.  This supplies the complete symmetric-family eigenvalue
multiset without an assumed component identity or independence hypothesis. -/
theorem symmetricToeplitz_orthogonal_diagonalization
    {n : ℕ} (hn : 0 < n) (c d : ℝ) :
    tridiagonalToeplitz n c d c =
      finiteMatMul (higham9_12_sineMatrix n)
        (finiteMatMul (finiteDiagonal (symmetricToeplitzEigenvalue n c d))
          (matTranspose (higham9_12_sineMatrix n))) := by
  apply finiteMatrix_eq_orthogonal_diagonalization_of_orthonormal_eigenvectors
  · intro i j
    exact (higham9_sineMatrix_isOrthogonal hn).col_orthonormal i j
  · intro k
    simpa [finiteMatVec, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
      symmetricToeplitz_scaled_sine_eigenpair c d k

/-- The monic polynomial encoded by the companion matrix: `X^n - sum a_k X^k`. -/
noncomputable def companionCharacteristicFormula
    (n : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ n -
    ∑ k ∈ Finset.range n, Polynomial.monomial k (a k)

theorem companionCharacteristicFormula_coeff
    (n : ℕ) (a : ℕ → ℂ) (k : ℕ) :
    (companionCharacteristicFormula n a).coeff k =
      if k = n then 1 else if k < n then -a k else 0 := by
  have hsum :
      (∑ b ∈ Finset.range n, Polynomial.monomial b (a b)).coeff k =
        if k < n then a k else 0 := by
    rw [Polynomial.finset_sum_coeff]
    by_cases hk : k < n
    · rw [Finset.sum_eq_single k]
      · simp [hk]
      · intro b hb hbk
        simp [Polynomial.coeff_monomial, hbk]
      · simp [hk]
    · rw [if_neg hk]
      apply Finset.sum_eq_zero
      intro b hb
      rw [Polynomial.coeff_monomial]
      simp only [ite_eq_right_iff]
      intro hbk
      subst b
      exact (hk (Finset.mem_range.mp hb)).elim
  rw [companionCharacteristicFormula, Polynomial.coeff_sub,
    Polynomial.coeff_X_pow, hsum]
  by_cases hkn : k = n
  · subst k
    simp
  · by_cases hk : k < n <;> simp [hkn, hk]

/-- Left cyclicity: the transpose Krylov family generated by `v` is a basis.
This is the algebraic precursor used in the standard proof that a companion
matrix is nonderogatory. -/
def IsLeftCyclicFor {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : Prop :=
  LinearIndependent ℂ
    (fun k : Fin n => Matrix.mulVec (A.transpose ^ k.val) v)

def HasLeftCyclicVector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∃ v, IsLeftCyclicFor A v

/-- One transpose-companion step sends the reverse basis vector indexed by
`k` to the reverse basis vector indexed by `k+1`. -/
private theorem companion_transpose_reverseBasis_step
    {n k : ℕ} (a : ℕ → ℂ) (hk : k + 1 < n) :
    Matrix.mulVec (companionMatrix n a).transpose
        (Pi.single (Fin.rev ⟨k, by omega⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨k + 1, hk⟩ : Fin n) 1 := by
  rw [Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Matrix.transpose_apply]
  have hjpos : 0 < (Fin.rev ⟨k, by omega⟩ : Fin n).val := by
    simp [Fin.rev]
    omega
  rw [companionMatrix]
  simp only [if_neg (ne_of_gt hjpos)]
  simp only [Pi.single_apply]
  by_cases hidx : (Fin.rev ⟨k, by omega⟩ : Fin n).val = i.val + 1
  · rw [if_pos hidx]
    rw [if_pos]
    apply Fin.ext
    change i.val = n - ((k + 1) + 1)
    change n - (k + 1) = i.val + 1 at hidx
    omega
  · rw [if_neg hidx]
    rw [if_neg]
    intro hi
    apply hidx
    change n - (k + 1) = i.val + 1
    have hiv : i.val = n - ((k + 1) + 1) := by
      have := congrArg Fin.val hi
      simpa only [Fin.val_rev, Fin.val_mk] using this
    omega

private theorem companion_transpose_pow_seed_nat
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) (k : ℕ) (hk : k < n) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ k)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single (Fin.rev ⟨k, hk⟩ : Fin n) 1 := by
  induction k with
  | zero =>
      rw [pow_zero, Matrix.one_mulVec]
  | succ k ih =>
      rw [pow_succ']
      rw [← Matrix.mulVec_mulVec]
      rw [ih (by omega)]
      exact companion_transpose_reverseBasis_step a hk

/-- The entire transpose Krylov family is exactly the reversed standard
basis; no cyclicity premise is assumed. -/
theorem companion_transpose_krylov_eq_reverseBasis
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) (k : Fin n) :
    Matrix.mulVec ((companionMatrix n a).transpose ^ k.val)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1) =
      Pi.single k.rev 1 := by
  simpa using companion_transpose_pow_seed_nat hn a k.val k.isLt

theorem companion_transpose_krylov_linearIndependent
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    LinearIndependent ℂ (fun k : Fin n =>
      Matrix.mulVec ((companionMatrix n a).transpose ^ k.val)
        (Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1)) := by
  have hstd : LinearIndependent ℂ
      (fun k : Fin n => (Pi.single k.rev (1 : ℂ) : Fin n → ℂ)) := by
    simpa [Function.comp_def] using
      (Pi.linearIndependent_single_one (Fin n) ℂ).comp Fin.rev
        Fin.revPerm.injective
  convert hstd using 1
  funext k
  exact companion_transpose_krylov_eq_reverseBasis hn a k

/-- Every positive-order companion matrix has the explicit left cyclic vector
`e_n`.  This is the genuine finite construction behind nonderogatoriness. -/
theorem companion_hasLeftCyclicVector
    {n : ℕ} (hn : 0 < n) (a : ℕ → ℂ) :
    HasLeftCyclicVector (companionMatrix n a) := by
  refine ⟨Pi.single (Fin.rev ⟨0, hn⟩ : Fin n) 1, ?_⟩
  exact companion_transpose_krylov_linearIndependent hn a

/-- The square minor obtained from rows `1,...,n` and columns `0,...,n-1`
of the scalar-shifted order-`n+1` companion matrix. -/
noncomputable def companionRankMinor
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (companionMatrix (n + 1) a - lambda •
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))
      i.succ j.castSucc

theorem companionRankMinor_apply
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) (i j : Fin n) :
    companionRankMinor n a lambda i j =
      if i = j then 1 else if i.val + 1 = j.val then -lambda else 0 := by
  simp only [companionRankMinor, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, Fin.val_succ, Fin.val_castSucc, companionMatrix]
  simp only [Nat.succ_ne_zero, ↓reduceIte]
  by_cases hij : i = j
  · subst j
    have hne : i.succ ≠ i.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    simp [hne]
  · have hvals : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp only [hij, if_false]
    by_cases hnext : i.val + 1 = j.val
    · have hfin : i.succ = j.castSucc := Fin.ext hnext
      simp [hnext, hfin]
    · have hfin : i.succ ≠ j.castSucc := by
        intro h
        exact hnext (congrArg Fin.val h)
      simp [hnext, hfin, hvals]

theorem companionRankMinor_upperTriangular
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    Matrix.BlockTriangular (companionRankMinor n a lambda) id := by
  intro i j hji
  rw [companionRankMinor_apply]
  have hij : i ≠ j := by
    intro h
    subst j
    exact lt_irrefl _ hji
  have hnext : i.val + 1 ≠ j.val := by
    have hv : j.val < i.val := hji
    omega
  simp [hij, hnext]

/-- The explicit rank minor is upper triangular with unit diagonal. -/
theorem companionRankMinor_det
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    Matrix.det (companionRankMinor n a lambda) = 1 := by
  rw [Matrix.det_of_upperTriangular
    (companionRankMinor_upperTriangular n a lambda)]
  simp [companionRankMinor_apply]

private theorem companionMatrix_sub_scalar_rank_ge_succ
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    n ≤ Matrix.rank
      (companionMatrix (n + 1) a -
        lambda • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) := by
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    companionMatrix (n + 1) a - lambda • 1
  let B : Matrix (Fin n) (Fin (n + 1)) ℂ :=
    A.submatrix Fin.succ (Equiv.refl _)
  have hrows : Matrix.rank B ≤ Matrix.rank A := by
    exact Matrix.rank_submatrix_le Fin.succ (Equiv.refl _) A
  have hcols :
      Matrix.rank
          (B.transpose.submatrix Fin.castSucc (Equiv.refl (Fin n))) ≤
        Matrix.rank B.transpose := by
    exact Matrix.rank_submatrix_le Fin.castSucc (Equiv.refl (Fin n)) B.transpose
  have hminor :
      B.transpose.submatrix Fin.castSucc (Equiv.refl (Fin n)) =
        (companionRankMinor n a lambda).transpose := by
    ext i j
    rfl
  rw [hminor, Matrix.rank_transpose, Matrix.rank_transpose] at hcols
  have hunit : IsUnit (companionRankMinor n a lambda) := by
    rw [Matrix.isUnit_iff_isUnit_det, companionRankMinor_det]
    exact isUnit_one
  have hrank := Matrix.rank_of_isUnit (companionRankMinor n a lambda) hunit
  have hrank' : Matrix.rank (companionRankMinor n a lambda) = n := by
    simpa using hrank
  change n ≤ Matrix.rank A
  calc
    n = Matrix.rank (companionRankMinor n a lambda) := hrank'.symm
    _ ≤ Matrix.rank B := hcols
    _ ≤ Matrix.rank A := hrows

/-- Higham, p. 523: every scalar shift of a companion matrix has rank at
least `n - 1`, the printed rank characterization of nonderogatoriness. -/
theorem companionMatrix_sub_scalar_rank_ge
    (n : ℕ) (a : ℕ → ℂ) (lambda : ℂ) :
    n - 1 ≤ Matrix.rank
      (companionMatrix n a -
        lambda • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using
        companionMatrix_sub_scalar_rank_ge_succ n a lambda

/-- `1 + sum |a_k|^2`, the trace parameter in the two exceptional squared
singular values of a companion matrix. -/
noncomputable def companionSingularAlpha (n : ℕ) (a : ℕ → ℂ) : ℝ :=
  1 + ∑ k ∈ Finset.range n, ‖a k‖ ^ 2

/-- The exact Gram matrix of the companion matrix: a rank-one outer product
of the reversed coefficient vector plus `diag(1,...,1,0)`. -/
noncomputable def companionGramFormula
    (n : ℕ) (a : ℕ → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    star (a (n - 1 - i.val)) * a (n - 1 - j.val) +
      if i = j ∧ i.val + 1 < n then 1 else 0

/-- Direct entrywise calculation of `Cᴴ C`.  This is the genuine low-rank
producer needed by the singular-value argument. -/
theorem companion_conjTranspose_mul_self
    (n : ℕ) (a : ℕ → ℂ) :
    (companionMatrix n a).conjTranspose * companionMatrix n a =
      companionGramFormula n a := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    companionGramFormula]
  let z : Fin n := ⟨0, Nat.zero_lt_of_lt i.isLt⟩
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ z)]
  have hz : z.val = 0 := rfl
  simp only [companionMatrix, hz, if_pos]
  have hclean :
      (∑ x ∈ Finset.univ.erase z,
          star (if x.val = 0 then a (n - 1 - i.val)
            else if x.val = i.val + 1 then 1 else 0) *
          (if x.val = 0 then a (n - 1 - j.val)
            else if x.val = j.val + 1 then 1 else 0)) =
        ∑ x ∈ Finset.univ.erase z,
          (if x.val = i.val + 1 then 1 else 0) *
          (if x.val = j.val + 1 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    have hxne : x.val ≠ 0 := by
      intro hx0
      have hxz : x = z := Fin.ext (by simpa [hz] using hx0)
      exact (Finset.mem_erase.mp hx).1 hxz
    simp [hxne]
  rw [hclean]
  have hsum :
      (∑ x ∈ Finset.univ.erase z,
          (if x.val = i.val + 1 then 1 else 0) *
          (if x.val = j.val + 1 then 1 else 0) : ℂ) =
        if i = j ∧ i.val + 1 < n then 1 else 0 := by
    by_cases hi : i.val + 1 < n
    · let ip : Fin n := ⟨i.val + 1, hi⟩
      have hip : ∀ x : Fin n, x.val = i.val + 1 ↔ x = ip := by
        intro x
        constructor
        · intro h
          exact Fin.ext h
        · rintro rfl
          rfl
      simp_rw [hip]
      by_cases hj : j.val + 1 < n
      · let jp : Fin n := ⟨j.val + 1, hj⟩
        have hjp : ∀ x : Fin n, x.val = j.val + 1 ↔ x = jp := by
          intro x
          constructor
          · intro h
            exact Fin.ext h
          · rintro rfl
            rfl
        simp_rw [hjp]
        by_cases hij : i = j
        · subst j
          simp [hi, ip, jp, z]
        · have hval : j.val ≠ i.val := by
            intro h
            exact hij (Fin.ext h.symm)
          simp [hij, hi, ip, jp, z, hval]
      · have hjnone : ∀ x : Fin n, x.val ≠ j.val + 1 := by
          intro x h
          omega
        simp_rw [if_neg (hjnone _)]
        have hij : i ≠ j := by
          intro h
          subst j
          exact hj hi
        simp [hij]
    · have hinone : ∀ x : Fin n, x.val ≠ i.val + 1 := by
        intro x h
        omega
      simp_rw [if_neg (hinone _)]
      simp [hi]
  rw [hsum]
  ring

/-- The printed target polynomial for the two exceptional squared singular
values in the source domain `2 ≤ n`; in that domain the other `n-2` Gram roots
are one. The definition is algebraically meaningful outside that domain, but
no singular-value interpretation is claimed there. -/
noncomputable def companionExceptionalSingularSqPolynomial
    (n : ℕ) (a : ℕ → ℂ) : Polynomial ℂ :=
  Polynomial.X ^ 2 -
    Polynomial.C (companionSingularAlpha n a : ℂ) * Polynomial.X +
    Polynomial.C ((‖a 0‖ ^ 2 : ℝ) : ℂ)

end NumStability
