/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED94 contributors
-/
import NumStability.Algorithms.HighamChapter9DoolittleClosure
import NumStability.Algorithms.Cholesky.Higham1029Source

/-!
# The rounded-LU first-breakdown reduction behind Higham--Mathias

The no-pivot success proof cannot assume a backward-error theorem that already
requires every computed pivot to be nonzero.  This file isolates the
noncircular prefix fact needed at a first zero pivot.  If all pivots before a
leading block are nonzero, the actual executable Algorithm 9.2 factors on that
block satisfy the source-shaped Theorem 9.3 backward error.  The last pivot of
the block is deliberately not assumed nonzero.

Consequently, if the current pivot is zero, the corresponding perturbed
leading block is singular.  A source-strength Mathias bootstrap must rule out
that singularity from `24 * n^(3/2) * chi(A) * u < 1`; that analytic estimate is
separate from this executable first-breakdown reduction.
-/

namespace NumStability

open scoped BigOperators

/-- Restrict a square matrix to its leading `r x r` block. -/
def higham10_mathiasLeadingBlock {n r : Nat} (hr : r ≤ n)
    (M : Fin n → Fin n → Real) : Fin r → Fin r → Real :=
  fun i j => M (Fin.castLE hr i) (Fin.castLE hr j)

/-- The actual rounded Doolittle factors restricted to a leading block have a
source-shaped backward error as soon as the pivots needed to compute entries
strictly below that block's last diagonal position are nonzero.  In
particular, no hypothesis is made about the last pivot of the block. -/
theorem higham10_mathias_roundedLoop_leadingBlock_source_backward_error
    {n r : Nat} (fp : FPModel) (A : Fin n → Fin n → Real) (hr : r ≤ n)
    (hproper : ∀ q : Fin n, q.val + 1 < r →
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A q q ≠ 0)
    (hn : gammaValid fp n) :
    let L := higham10_mathiasLeadingBlock hr
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
    let U := higham10_mathiasLeadingBlock hr
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
    let Ar := higham10_mathiasLeadingBlock hr A
    ∃ ΔA : Fin r → Fin r → Real,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ s : Fin r, |L i s| * |U s j|) ∧
      LUFactSpec r (fun i j => Ar i j + ΔA i j) L U := by
  classical
  let e : Fin r → Fin n := Fin.castLE hr
  let Lhat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
  let Uhat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
  let L : Fin r → Fin r → Real := higham10_mathiasLeadingBlock hr Lhat
  let U : Fin r → Fin r → Real := higham10_mathiasLeadingBlock hr Uhat
  let Ar : Fin r → Fin r → Real := higham10_mathiasLeadingBlock hr A
  let ΔA : Fin r → Fin r → Real := fun i j => rectMatMul L U i j - Ar i j
  have hLdiag : ∀ i : Fin r, L i i = 1 := by
    intro i
    simpa [L, Lhat, higham10_mathiasLeadingBlock, higham9_2_rectRow] using
      (higham9_2_rectRoundedLoopL_diag fp (Nat.le_refl n) A (e i))
  have hLupper : ∀ i j : Fin r, i.val < j.val → L i j = 0 := by
    intro i j hij
    exact higham9_2_rectRoundedLoopL_upper_zero fp (Nat.le_refl n) A
      (e i) (e j) (by simpa [e] using hij)
  have hUlower : ∀ i j : Fin r, j.val < i.val → U i j = 0 := by
    intro i j hij
    exact higham9_2_rectRoundedLoopU_lower_zero fp (Nat.le_refl n) A
      (e i) (e j) (by simpa [e] using hij)
  have hUres : ∀ i j : Fin r, i.val ≤ j.val →
      |(Ar i j - higham9_2_rectPrefixDot L U i j i) - U i j| ≤
        gamma fp n *
          ((∑ s : Fin i.val,
              |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ j|) + |U i j|) := by
    intro i j hij
    have hentry : Uhat (e i) (e j) =
        higham9_2_rectFlDoolittleUEntry fp (Nat.le_refl n)
          A Lhat Uhat (e i) (e j) :=
      higham9_2_rectRoundedLoopU_stage_eq A (e i) (e j)
        (by simpa [e] using hij)
    have hres := higham9_2_rectFlDoolittleUEntry_source_residual_abs_le
      fp (Nat.le_refl n) A Lhat Uhat (e i) (e j) hn hentry
    simp only [higham9_2_rectRow] at hres
    have hprefBig := finMaskedPrefixSum_eq_finSum (e i)
      (fun s : Fin n => Lhat (e i) s * Uhat s (e j))
    have hprefSmall := finMaskedPrefixSum_eq_finSum i
      (fun s : Fin r => L i s * U s j)
    unfold higham9_2_rectPrefixDot at hres ⊢
    rw [hprefBig] at hres
    rw [hprefSmall]
    simpa [Ar, L, U, Lhat, Uhat, e, higham10_mathiasLeadingBlock,
      higham9_2_rectRow, Fin.castLE] using hres
  have hLres : ∀ i j : Fin r, j.val < i.val →
      |(Ar i j - higham9_2_rectPrefixDot L U i j j) - L i j * U j j| ≤
        gamma fp n *
          ((∑ s : Fin j.val,
              |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ j|) +
            |L i j * U j j|) := by
    intro i j hji
    have hjproper : (e j).val + 1 < r := by
      simpa [e] using (show j.val + 1 < r by omega)
    have hentry : Lhat (e i) (e j) =
        higham9_2_rectFlDoolittleLEntry fp A Lhat Uhat (e i) (e j) :=
      higham9_2_rectRoundedLoopL_stage_eq A (e i) (e j)
        (by simpa [e] using hji)
    have hres := higham9_2_rectFlDoolittleLEntry_source_residual_abs_le
      fp A Lhat Uhat (e i) (e j) hn (hproper (e j) hjproper) hentry
    have hprefBig := finMaskedPrefixSum_eq_finSum (e j)
      (fun s : Fin n => Lhat (e i) s * Uhat s (e j))
    have hprefSmall := finMaskedPrefixSum_eq_finSum j
      (fun s : Fin r => L i s * U s j)
    unfold higham9_2_rectPrefixDot at hres ⊢
    rw [hprefBig] at hres
    rw [hprefSmall]
    simpa [Ar, L, U, Lhat, Uhat, e, higham10_mathiasLeadingBlock,
      Fin.castLE] using hres
  refine ⟨ΔA, ?_, ?_⟩
  · intro i j
    by_cases hij : i.val ≤ j.val
    · have hprod := higham9_2_rectMatMul_eq_prefix_add_upper
        (hmn := Nat.le_refl r) (L := L) (U := U)
        hLdiag hLupper i j hij
      have habs := higham9_2_rectAbsProductSum_eq_prefix_add_upper
        (hmn := Nat.le_refl r) (L := L) (U := U)
        hLdiag hLupper i j hij
      simp only [higham9_2_rectRow] at hprod habs
      calc
        |ΔA i j| = |rectMatMul L U i j - Ar i j| := rfl
        _ = |(higham9_2_rectPrefixDot L U i j i + U i j) - Ar i j| := by
          rw [hprod]
        _ = |(Ar i j - higham9_2_rectPrefixDot L U i j i) - U i j| := by
          rw [show (higham9_2_rectPrefixDot L U i j i + U i j) - Ar i j =
              -((Ar i j - higham9_2_rectPrefixDot L U i j i) - U i j) by ring,
            abs_neg]
        _ ≤ gamma fp n *
            ((∑ s : Fin i.val,
                |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ j|) + |U i j|) :=
          hUres i j hij
        _ = gamma fp n * ∑ s : Fin r, |L i s| * |U s j| := by
          rw [habs]
    · have hji : j.val < i.val := lt_of_not_ge hij
      have hprod := higham9_2_rectMatMul_eq_prefix_add_lower
        (L := L) (U := U) hUlower i j
      have habs := higham9_2_rectAbsProductSum_eq_prefix_add_lower
        (L := L) (U := U) hUlower i j
      calc
        |ΔA i j| = |rectMatMul L U i j - Ar i j| := rfl
        _ = |(higham9_2_rectPrefixDot L U i j j + L i j * U j j) - Ar i j| := by
          rw [hprod]
        _ = |(Ar i j - higham9_2_rectPrefixDot L U i j j) - L i j * U j j| := by
          rw [show (higham9_2_rectPrefixDot L U i j j + L i j * U j j) - Ar i j =
              -((Ar i j - higham9_2_rectPrefixDot L U i j j) - L i j * U j j) by
                ring,
            abs_neg]
        _ ≤ gamma fp n *
            ((∑ s : Fin j.val,
                |L i ⟨s.val, by omega⟩ * U ⟨s.val, by omega⟩ j|) +
              |L i j * U j j|) := hLres i j hji
        _ = gamma fp n * ∑ s : Fin r, |L i s| * |U s j| := by
          rw [habs]
  · refine
      { L_diag := hLdiag
        L_upper_zero := hLupper
        U_lower_zero := hUlower
        product_eq := ?_ }
    intro i j
    simp only [ΔA]
    unfold rectMatMul
    ring

/-- At a first zero pivot, the source-shaped perturbation of the corresponding
leading principal block supplied by the actual rounded loop is singular. -/
theorem higham10_mathias_first_zero_pivot_has_singular_leading_perturbation
    {n : Nat} (fp : FPModel) (A : Fin n → Fin n → Real) (k : Fin n)
    (hprior : ∀ q : Fin n, q.val < k.val →
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A q q ≠ 0)
    (hzero : higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k = 0)
    (hn : gammaValid fp n) :
    let r := k.val + 1
    let hr : r ≤ n := by omega
    let L := higham10_mathiasLeadingBlock hr
      (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
    let U := higham10_mathiasLeadingBlock hr
      (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
    let Ar := higham10_mathiasLeadingBlock hr A
    ∃ ΔA : Fin r → Fin r → Real,
      (∀ i j, |ΔA i j| ≤ gamma fp n *
        ∑ s : Fin r, |L i s| * |U s j|) ∧
      LUFactSpec r (fun i j => Ar i j + ΔA i j) L U ∧
      Matrix.det (Matrix.of (fun i j => Ar i j + ΔA i j)) = 0 := by
  classical
  let r := k.val + 1
  let hr : r ≤ n := by omega
  let L := higham10_mathiasLeadingBlock hr
    (higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A)
  let U := higham10_mathiasLeadingBlock hr
    (higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A)
  let Ar := higham10_mathiasLeadingBlock hr A
  have hproper : ∀ q : Fin n, q.val + 1 < r →
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A q q ≠ 0 := by
    intro q hq
    exact hprior q (by simpa [r] using hq)
  obtain ⟨ΔA, hΔA, hLU⟩ :=
    higham10_mathias_roundedLoop_leadingBlock_source_backward_error
      fp A hr hproper hn
  refine ⟨ΔA, hΔA, hLU, ?_⟩
  rw [LUFactSpec.det_eq_prod_U_diag hLU]
  let last : Fin r := ⟨k.val, by simp [r]⟩
  have hlast : Fin.castLE hr last = k := by
    apply Fin.ext
    rfl
  have hUlast : U last last = 0 := by
    simpa [U, higham10_mathiasLeadingBlock, hlast] using hzero
  exact Finset.prod_eq_zero (Finset.mem_univ last) hUlast

end NumStability
