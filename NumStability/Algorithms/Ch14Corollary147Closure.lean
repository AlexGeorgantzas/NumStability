/-
Copyright (c) 2026 NumStability contributors. All rights reserved.
Released under Apache 2.0 license.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
-/
import NumStability.Algorithms.Ch14Corollary147
import NumStability.Algorithms.Ch14GaussJordanQConstruction

/-!
# Corollary 14.7: the structural closure

This file supplies the exact Gaussian-elimination fact used in Higham's
one-line proof of Corollary 14.7: if a nonsingular matrix is row diagonally
dominant, exact elimination without pivoting has a row diagonally dominant
upper factor.

The distinction between exact and rounded elimination is essential. Weak row
diagonal dominance has zero margin on boundary rows and is not an open
property, so an arbitrarily small rounding perturbation can destroy it. The
rounded producer below therefore uses the precise row-margin hypothesis that
is sufficient. The concrete GJE endpoints still require the separate
first-order identifications

* `X_abs = |U_hat| |U_hat_inv| + O(u)` for (14.31), and
* `P_abs = |U_hat_inv| + O(u)` for (14.32).

Those two family-level obligations are recorded explicitly at the end of the
file; neither is replaced by an assumption named as a final residual or
forward-error conclusion.
-/

namespace NumStability.Ch14Ext

open scoped BigOperators
open NumStability

/-! ## Exact no-pivot elimination preserves row diagonal dominance -/

/-- A first exact no-pivot Schur-complement step preserves row diagonal
dominance.

For the trailing row `i`, the proof retains the diagonal correction
`|a_i0/a_00| |a_0i|`. The other pivot-row corrections plus this term consume
at most `|a_i0|`, while the reverse triangle inequality for the new diagonal
cancels the retained term. -/
theorem ch14ext_rowDiagDominant_firstSchurComplement {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hDD : IsRowDiagDominant (m + 1) A)
    (hpivot : A 0 0 ≠ 0) :
    IsRowDiagDominant m (luFirstSchurComplement A) := by
  classical
  intro i
  let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
  let offS : ℝ := ∑ j : Fin m, if i = j then 0 else |S i j|
  let offA : ℝ := ∑ j : Fin m, if i = j then 0 else |A i.succ j.succ|
  let pivotTail : ℝ := ∑ j : Fin m, |A 0 j.succ|
  let ratio : ℝ := |A i.succ 0 / A 0 0|
  let diagCorrection : ℝ := ratio * |A 0 i.succ|
  have hsourceRow : |A i.succ 0| + offA ≤ |A i.succ i.succ| := by
    have h := hDD i.succ
    rw [Fin.sum_univ_succ] at h
    simpa [offA, Fin.succ_inj] using h
  have hpivotRow : pivotTail ≤ |A 0 0| := by
    have h := hDD (0 : Fin (m + 1))
    rw [Fin.sum_univ_succ] at h
    simpa [pivotTail] using h
  have hratioTail : ratio * pivotTail ≤ |A i.succ 0| := by
    calc
      ratio * pivotTail ≤ ratio * |A 0 0| :=
        mul_le_mul_of_nonneg_left hpivotRow (abs_nonneg _)
      _ = |A i.succ 0| := by
        dsimp [ratio]
        rw [abs_div]
        field_simp [abs_ne_zero.mpr hpivot]
  have hentry : ∀ j : Fin m, i ≠ j →
      |S i j| ≤ |A i.succ j.succ| + ratio * |A 0 j.succ| := by
    intro j _hij
    have hfactor :
        A i.succ 0 * A 0 j.succ / A 0 0 =
          (A i.succ 0 / A 0 0) * A 0 j.succ := by
      ring
    calc
      |S i j| =
          |A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0| := rfl
      _ ≤ |A i.succ j.succ| +
          |A i.succ 0 * A 0 j.succ / A 0 0| := by
        simpa [abs_neg] using
          (abs_sub_le (A i.succ j.succ) 0
            (A i.succ 0 * A 0 j.succ / A 0 0))
      _ = |A i.succ j.succ| + ratio * |A 0 j.succ| := by
        rw [hfactor, abs_mul]
  have hoffWithCorrection :
      offS + diagCorrection ≤ offA + ratio * pivotTail := by
    calc
      offS + diagCorrection =
          ∑ j : Fin m,
            ((if i = j then 0 else |S i j|) +
              if i = j then diagCorrection else 0) := by
        rw [Finset.sum_add_distrib]
        simp [offS]
      _ ≤ ∑ j : Fin m,
            ((if i = j then 0 else |A i.succ j.succ|) +
              ratio * |A 0 j.succ|) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hij : i = j
        · subst j
          simp [diagCorrection]
        · simpa [hij] using hentry j hij
      _ = offA + ratio * pivotTail := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hoffToOldDiag : offS + diagCorrection ≤ |A i.succ i.succ| := by
    calc
      offS + diagCorrection ≤ offA + ratio * pivotTail := hoffWithCorrection
      _ ≤ offA + |A i.succ 0| := by linarith
      _ = |A i.succ 0| + offA := by ring
      _ ≤ |A i.succ i.succ| := hsourceRow
  have holdDiagToNew :
      |A i.succ i.succ| ≤ |S i i| + diagCorrection := by
    have heq :
        A i.succ i.succ =
          S i i + (A i.succ 0 / A 0 0) * A 0 i.succ := by
      dsimp [S]
      simp only [luFirstSchurComplement]
      ring
    calc
      |A i.succ i.succ| =
          |S i i + (A i.succ 0 / A 0 0) * A 0 i.succ| := by rw [heq]
      _ ≤ |S i i| + |(A i.succ 0 / A 0 0) * A 0 i.succ| :=
        abs_add_le _ _
      _ = |S i i| + diagCorrection := by
        rw [abs_mul]
  change offS ≤ |S i i|
  linarith

/-- Assembling the source pivot row over a row-dominant trailing upper factor
preserves row diagonal dominance of the complete upper factor. -/
theorem ch14ext_luFirstStepU_rowDiagDominant {m : ℕ}
    {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    {U₁ : Fin m → Fin m → ℝ}
    (hA : IsRowDiagDominant (m + 1) A)
    (hU₁ : IsRowDiagDominant m U₁) :
    IsRowDiagDominant (m + 1) (luFirstStepU A U₁) := by
  intro i
  refine Fin.cases ?_ (fun q => ?_) i
  · simpa [luFirstStepU] using hA (0 : Fin (m + 1))
  · have h := hU₁ q
    rw [Fin.sum_univ_succ]
    simpa [luFirstStepU, Fin.succ_inj] using h

/-- For an upper-triangular matrix, the full off-diagonal row sum is exactly
its strict-upper row sum. -/
theorem ch14ext_upper_offdiag_sum_eq_strictUpper {n : ℕ}
    (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (i : Fin n) :
    (∑ j : Fin n, if i = j then 0 else |U i j|) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j| := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j.val < i.val
  · have hij : i ≠ j := Fin.ne_of_val_ne (by omega)
    simp [hij, hUT i j hji]
  · by_cases hij : i = j
    · subst j
      simp
    · have hijv : i.val < j.val := by
        have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
        omega
      simp [hij, hijv]

/-- An upper-triangular, nonsingular, row diagonally dominant matrix has the
exact corrected Lemma 8.8 predicate used by Chapter 14. -/
theorem ch14ext_higham8_8_of_upper_rowDiagDominant {n : ℕ}
    (U : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U i j = 0)
    (hdiag : ∀ i : Fin n, U i i ≠ 0)
    (hRow : IsRowDiagDominant n U) :
    higham8_8_rowDiagDominantUpper n U := by
  refine ⟨hUT, hdiag, ?_⟩
  intro i
  rw [← ch14ext_upper_offdiag_sum_eq_strictUpper U hUT i]
  exact hRow i

/-- Exact GE without pivoting can be constructed on every nonsingular row
diagonally dominant matrix, and its upper factor is row diagonally dominant.

This is the source-level structural producer behind Corollary 14.7. -/
theorem ch14ext_rowDiagDominant_exists_exactNoPivotLU_rowUpper :
    ∀ n : ℕ, ∀ A : Fin n → Fin n → ℝ,
      IsRowDiagDominant n A →
      Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0 →
      ∃ L U : Fin n → Fin n → ℝ,
        LUFactSpec n A L U ∧ IsRowDiagDominant n U := by
  intro n
  induction n with
  | zero =>
      intro A _hDD _hdet
      refine ⟨A, A, ?_, ?_⟩
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro i
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
        · intro i _j
          exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m ih =>
      intro A hDD hdet
      have hpivot : A 0 0 ≠ 0 :=
        (higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero hDD hdet) 0
      let S : Fin m → Fin m → ℝ := luFirstSchurComplement A
      have hSDD : IsRowDiagDominant m S := by
        simpa [S] using ch14ext_rowDiagDominant_firstSchurComplement hDD hpivot
      have hSdet :
          Matrix.det (Matrix.of S : Matrix (Fin m) (Fin m) ℝ) ≠ 0 := by
        simpa [S, higham9_1_firstSchurComplement] using
          higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero hpivot hdet
      obtain ⟨L₁, U₁, hLU₁, hU₁Row⟩ := ih S hSDD hSdet
      refine ⟨luFirstStepL A L₁, luFirstStepU A U₁, ?_, ?_⟩
      · exact LUFactSpec.of_firstSchurComplement_explicit hpivot hLU₁
      · exact ch14ext_luFirstStepU_rowDiagDominant hDD hU₁Row

/-- Every exact unit-lower/upper factorization of a nonsingular row
diagonally dominant matrix has a row diagonally dominant upper factor.

The recursive producer gives one such factorization; exact-LU uniqueness
transfers the property to the supplied no-pivot factors. -/
theorem ch14ext_exactNoPivotLU_upper_rowDiagDominant {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U) :
    IsRowDiagDominant n U := by
  obtain ⟨L₀, U₀, hLU₀, hU₀Row⟩ :=
    ch14ext_rowDiagDominant_exists_exactNoPivotLU_rowUpper n A hRow hdet
  have huniq := higham9_1_lu_unique_of_pivots_ne_zero hLU hLU₀
    ((higham9_1_det_ne_zero_iff_pivots_ne_zero hLU).mp hdet)
  rw [huniq.2]
  exact hU₀Row

/-- Source-facing exact-GE producer in the corrected Lemma 8.8 shape consumed
by the existing Corollary 14.7 endpoint theorems. -/
theorem ch14ext_exactNoPivotLU_upper_higham8_8 {n : ℕ}
    (A L U : Fin n → Fin n → ℝ)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L U) :
    higham8_8_rowDiagDominantUpper n U := by
  exact ch14ext_higham8_8_of_upper_rowDiagDominant U hLU.U_lower_zero
    ((hLU.det_ne_zero_iff_U_diag_ne_zero).mp hdet)
    (ch14ext_exactNoPivotLU_upper_rowDiagDominant A L U hRow hdet hLU)

/-! ## Rounded preservation needs a positive margin -/

/-- The strict-upper row diagonal-dominance margin
`|U_ii| - sum_{j>i} |U_ij|`. Boundary rows of a weakly dominant matrix have
zero margin. -/
noncomputable def ch14ext_upperRowDiagMargin (n : ℕ)
    (U : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  |U i i| -
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j|

/-- Total perturbation budget relevant to row `i`: the diagonal perturbation
plus all strict-upper perturbations in that row. -/
noncomputable def ch14ext_upperRowPerturbationMass (n : ℕ)
    (U U_hat : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  |U_hat i i - U i i| +
    ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
      |U_hat i j - U i j|

/-- The exact open condition under which a rounded upper matrix remains row
diagonally dominant. The strict inequality is necessary to guarantee both
dominance and nonzero rounded pivots. -/
def Ch14Cor147RoundedUpperWithinMargin (n : ℕ)
    (U U_hat : Fin n → Fin n → ℝ) : Prop :=
  ∀ i : Fin n,
    ch14ext_upperRowPerturbationMass n U U_hat i <
      ch14ext_upperRowDiagMargin n U i

/-- A rounded upper factor whose row perturbations fit strictly inside the
exact factor's dominance margins satisfies the corrected Lemma 8.8 predicate.

No unconditional rounded-preservation theorem can replace this hypothesis:
when a source row has zero margin, increasing one strict-upper entry by any
positive amount destroys row dominance. -/
theorem ch14ext_roundedUpper_higham8_8_of_withinMargin {n : ℕ}
    (U U_hat : Fin n → Fin n → ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hmargin : Ch14Cor147RoundedUpperWithinMargin n U U_hat) :
    higham8_8_rowDiagDominantUpper n U_hat := by
  classical
  have hstrict : ∀ i : Fin n,
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          |U_hat i j|) < |U_hat i i| := by
    intro i
    let oldOff : ℝ :=
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U i j|
    let newOff : ℝ :=
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), |U_hat i j|
    let deltaOff : ℝ :=
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U_hat i j - U i j|
    let deltaDiag : ℝ := |U_hat i i - U i i|
    have hoff : newOff ≤ oldOff + deltaOff := by
      calc
        newOff ≤
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
              (|U i j| + |U_hat i j - U i j|) := by
          apply Finset.sum_le_sum
          intro j _
          have heq : U_hat i j = U i j + (U_hat i j - U i j) := by ring
          calc
            |U_hat i j| = |U i j + (U_hat i j - U i j)| := congrArg abs heq
            _ ≤ |U i j| + |U_hat i j - U i j| :=
              abs_add_le (U i j) (U_hat i j - U i j)
        _ = oldOff + deltaOff := by
          rw [Finset.sum_add_distrib]
    have hdiag : |U i i| ≤ |U_hat i i| + deltaDiag := by
      have heq : U i i = U_hat i i + (U i i - U_hat i i) := by ring
      calc
        |U i i| = |U_hat i i + (U i i - U_hat i i)| := congrArg abs heq
        _ ≤ |U_hat i i| + |U i i - U_hat i i| := abs_add_le _ _
        _ = |U_hat i i| + deltaDiag := by
          rw [abs_sub_comm]
    have hm := hmargin i
    change deltaDiag + deltaOff < |U i i| - oldOff at hm
    change newOff < |U_hat i i|
    linarith
  refine ⟨hUT, ?_, fun i => le_of_lt (hstrict i)⟩
  intro i hii
  have hnonneg :
      0 ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
        |U_hat i j| := by positivity
  have hs := hstrict i
  rw [hii, abs_zero] at hs
  linarith

/-- Entrywise perturbation-envelope form of the rounded margin producer.

If `|U_hat-U| <= eta E` entrywise and the scaled row envelope fits inside each
exact row margin, rounded row dominance follows. Taking `eta = fp.u` exposes
the usual `O(u)` requirement precisely. -/
theorem ch14ext_roundedUpper_higham8_8_of_entrywiseEnvelope {n : ℕ}
    (U U_hat E : Fin n → Fin n → ℝ) (eta : ℝ)
    (hUT : ∀ i j : Fin n, j.val < i.val → U_hat i j = 0)
    (hErr : ∀ i j : Fin n, |U_hat i j - U i j| ≤ eta * E i j)
    (hBudget : ∀ i : Fin n,
      eta *
          (E i i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), E i j) <
        ch14ext_upperRowDiagMargin n U i) :
    higham8_8_rowDiagDominantUpper n U_hat := by
  apply ch14ext_roundedUpper_higham8_8_of_withinMargin U U_hat hUT
  intro i
  have hoff :
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val),
          |U_hat i j - U i j|) ≤
        eta *
          ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), E i j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => hErr i j
  calc
    ch14ext_upperRowPerturbationMass n U U_hat i ≤
        eta * E i i +
          eta *
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), E i j := by
      unfold ch14ext_upperRowPerturbationMass
      exact add_le_add (hErr i i) hoff
    _ = eta *
          (E i i +
            ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.val < j.val), E i j) := by
      ring
    _ < ch14ext_upperRowDiagMargin n U i := hBudget i

/-! ## Exact-GE composition with the printed Corollary 14.7 endpoints -/

/-- Corollary 14.7's printed `32 n^2` row-wise residual endpoint with the
`hURow` premise discharged from row dominance of the exact no-pivot source.

This is deliberately named as a specialization of the inherited Theorem 14.5
certificate `hRes`, not as a concrete rounded-GJE closure. -/
theorem ch14ext_cor147_rowwise_residual_printed_of_exactGE_and_theorem14_5
    (n : ℕ) (fp : FPModel)
    (A L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (b x_hat : Fin n → ℝ)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hRes : ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        8 * (n : ℝ) * fp.u *
          matMulVec n
            (matMul n
              (matMul n (absMatrix n L_hat) (absMatrix n U_hat))
              (matMul n (absMatrix n U_inv) (absMatrix n U_hat)))
            (absVec n x_hat) i) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n, A i j * x_hat j| ≤
        32 * (n : ℝ) ^ 2 * fp.u *
          (∑ j : Fin n, |A i j|) * (∑ j : Fin n, |x_hat j|) := by
  exact ch14ext_cor147_rowwise_residual_printed_of_rowDiagDominantUpper
    n fp A L_hat U_hat U_inv b x_hat hLU
    (ch14ext_exactNoPivotLU_upper_higham8_8 A L_hat U_hat hRow hdet hLU)
    hUinv hRes

/-- Corollary 14.7's printed `4 n^3` forward endpoint with `hURow` discharged
from row dominance of the exact no-pivot source.

As above, `hFwd` is the inherited leading-order Theorem 14.5 certificate, so
this theorem is an exact-GE specialization rather than a claim that all
rounded first-stage factors preserve weak dominance. -/
theorem ch14ext_cor147_forward_printed_of_exactGE_and_theorem14_5
    (n : ℕ) (fp : FPModel) (hn : 0 < n)
    (A A_inv L_hat U_hat U_inv : Fin n → Fin n → ℝ)
    (x x_hat : Fin n → ℝ)
    (hRow : IsRowDiagDominant n A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hLU : LUFactSpec n A L_hat U_hat)
    (hUinv : IsInverse n U_hat U_inv)
    (hAinv : IsLeftInverse n A A_inv)
    (hxpos : 0 < infNormVec x)
    (hFwd : ∀ i : Fin n,
      |x i - x_hat i| ≤
        2 * (n : ℝ) * fp.u *
          (matMulVec n
              (matMul n (absMatrix n A_inv)
                (matMul n (absMatrix n L_hat) (absMatrix n U_hat)))
              (absVec n x_hat) i +
            3 * matMulVec n (matMul n (absMatrix n U_inv) (absMatrix n U_hat))
                (absVec n x_hat) i)) :
    infNormVec (fun i : Fin n => x i - x_hat i) / infNormVec x ≤
      4 * (n : ℝ) ^ 3 * fp.u * (kappaInf n hn A A_inv + 3) *
        (infNormVec x_hat / infNormVec x) := by
  exact ch14ext_cor147_forward_error_relative_infNorm n fp hn
    A A_inv L_hat U_hat U_inv x x_hat hLU
    (ch14ext_exactNoPivotLU_upper_higham8_8 A L_hat U_hat hRow hdet hLU)
    hUinv hAinv hxpos hFwd

/-! ## The remaining concrete-GJE `O(u)` family bridge -/

/-- Explicit remainder data needed to identify the concrete accumulated GJE
envelopes with the inverse factors printed in Theorem 14.5.

For the residual, the concrete object is
`X_abs = |Q| (|N_hat| ... |N_hat|)` and must be compared with
`|U_hat| |U_hat_inv|`. For the forward bound, the absolute cumulative product
must be compared directly with `|U_hat_inv|`. At a fixed `fp` this structure
records the exact inequalities. To justify the notation `O(u)` for a family of
models, the two remainder matrices must additionally be uniformly bounded as
`fp.u -> 0`; that analytic family statement is not supplied by the current
concrete GJE API. -/
structure Ch14Cor147ConcreteInverseEnvelopeBridge (n : ℕ) (fp : FPModel)
    (U_hat U_inv : Fin n → Fin n → ℝ)
    (V : ℕ → Fin n → Fin n → ℝ) (start : ℕ) where
  residualRemainder : Fin n → Fin n → ℝ
  forwardRemainder : Fin n → Fin n → ℝ
  residualRemainder_nonneg :
    ∀ i j : Fin n, 0 ≤ residualRemainder i j
  forwardRemainder_nonneg :
    ∀ i j : Fin n, 0 ≤ forwardRemainder i j
  residualEnvelope : ∀ i j : Fin n,
    ch14ext_gjeXabs n (ch14ext_gjeSeqStages n V)
        (ch14ext_gjeConstructedQ n V start) start (n - 1) i j ≤
      matMul n (absMatrix n U_hat) (absMatrix n U_inv) i j +
        fp.u * residualRemainder i j
  forwardEnvelope : ∀ i j : Fin n,
    ch14ext_absCumProd n (ch14ext_gjeSeqStages n V) start (n - 1) i j ≤
      |U_inv i j| + fp.u * forwardRemainder i j

end NumStability.Ch14Ext
