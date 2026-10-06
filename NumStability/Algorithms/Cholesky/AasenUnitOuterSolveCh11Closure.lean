/-
Copyright (c) 2026. Released under Apache 2.0.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.

# Support-aware outer solves for Aasen's method

The computed Aasen lower factor has first column `e₁`.  Together with lower
triangularity this makes it a direct sum `1 ⊕ Ltail`.  A source-faithful
outer solve therefore does not execute arithmetic against the structural-zero
off-block entries: it solves the scalar head and the `(n-1)`-dimensional tail
separately.  The ordinary Chapter-8 backward-error theorem applied to the tail
then gives the printed `gamma_(n-1)` coefficient.
-/
import NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenDirect

open NumStability

/-! ## One-plus-tail block constructors -/

noncomputable def aasenConsOneMatrix {m : ℕ} (a : ℝ)
    (A : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun i j => Fin.cases (Fin.cases a (fun _ => 0) j)
    (fun p => Fin.cases 0 (fun q => A p q) j) i

noncomputable def aasenConsOneVec {m : ℕ} (x0 : ℝ)
    (x : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  fun i => Fin.cases x0 x i

@[simp] theorem aasenConsOneMatrix_00 {m : ℕ} (a : ℝ)
    (A : Fin m → Fin m → ℝ) :
    aasenConsOneMatrix a A 0 0 = a := by
  simp [aasenConsOneMatrix]

@[simp] theorem aasenConsOneMatrix_0s {m : ℕ} (a : ℝ)
    (A : Fin m → Fin m → ℝ) (j : Fin m) :
    aasenConsOneMatrix a A 0 j.succ = 0 := by
  simp [aasenConsOneMatrix]

@[simp] theorem aasenConsOneMatrix_s0 {m : ℕ} (a : ℝ)
    (A : Fin m → Fin m → ℝ) (i : Fin m) :
    aasenConsOneMatrix a A i.succ 0 = 0 := by
  simp [aasenConsOneMatrix]

@[simp] theorem aasenConsOneMatrix_ss {m : ℕ} (a : ℝ)
    (A : Fin m → Fin m → ℝ) (i j : Fin m) :
    aasenConsOneMatrix a A i.succ j.succ = A i j := by
  simp [aasenConsOneMatrix]

@[simp] theorem aasenConsOneVec_zero {m : ℕ} (x0 : ℝ) (x : Fin m → ℝ) :
    aasenConsOneVec x0 x 0 = x0 := by
  simp [aasenConsOneVec]

@[simp] theorem aasenConsOneVec_succ {m : ℕ} (x0 : ℝ) (x : Fin m → ℝ)
    (i : Fin m) : aasenConsOneVec x0 x i.succ = x i := by
  simp [aasenConsOneVec]

/-! ## The actual support-aware computed outer solves -/

/-- Forward solve of a matrix known to have the Aasen `1 ⊕ Ltail` support.
The scalar call is kept as a real floating-point solve; the tail is the actual
`fl_forwardSub` executor in dimension `m`. -/
noncomputable def flAasenUnitForwardSub (fp : FPModel) (m : ℕ)
    (L : Fin (m + 1) → Fin (m + 1) → ℝ) (b : Fin (m + 1) → ℝ) :
    Fin (m + 1) → ℝ :=
  aasenConsOneVec
    (fl_forwardSub fp 1 (fun _ _ : Fin 1 => L 0 0) (fun _ : Fin 1 => b 0) 0)
    (fl_forwardSub fp m (fun i j => L i.succ j.succ) (fun i => b i.succ))

/-- Back solve with the transpose of an Aasen lower factor.  Again the
structural scalar/tail split is executed literally. -/
noncomputable def flAasenUnitTransposeBackSub (fp : FPModel) (m : ℕ)
    (L : Fin (m + 1) → Fin (m + 1) → ℝ) (b : Fin (m + 1) → ℝ) :
    Fin (m + 1) → ℝ :=
  aasenConsOneVec
    (fl_backSub fp 1 (fun _ _ : Fin 1 => L 0 0) (fun _ : Fin 1 => b 0) 0)
    (fl_backSub fp m (fun i j => L j.succ i.succ) (fun i => b i.succ))

/-! ## Sharp `gamma_m = gamma_(N-1)` backward errors -/

theorem flAasenUnitForwardSub_backward_error (fp : FPModel) (m : ℕ)
    (hm : 1 ≤ m) (L : Fin (m + 1) → Fin (m + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (hdiag : ∀ i : Fin (m + 1), L i i = 1)
    (hlower : ∀ i j : Fin (m + 1), i.val < j.val → L i j = 0)
    (hfirst : ∀ i : Fin m, L i.succ 0 = 0)
    (hval : gammaValid fp m) :
    ∃ DeltaL : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j, |DeltaL i j| ≤ gamma fp m * |L i j|) ∧
      ∀ i, ∑ j : Fin (m + 1),
        (L i j + DeltaL i j) * flAasenUnitForwardSub fp m L b j = b i := by
  have hval1 : gammaValid fp 1 := gammaValid_mono fp hm hval
  let L0 : Fin 1 → Fin 1 → ℝ := fun _ _ => L 0 0
  let b0 : Fin 1 → ℝ := fun _ => b 0
  let Lt : Fin m → Fin m → ℝ := fun i j => L i.succ j.succ
  let bt : Fin m → ℝ := fun i => b i.succ
  obtain ⟨Delta0, hDelta0, heq0⟩ :=
    forwardSub_backward_error fp 1 L0 b0
      (fun _ => by simp [L0, hdiag])
      (fun i j hij => by omega) hval1
  obtain ⟨DeltaT, hDeltaT, heqT⟩ :=
    forwardSub_backward_error fp m Lt bt
      (fun i => by simp [Lt, hdiag])
      (fun i j hij => by
        exact hlower i.succ j.succ (by simpa using hij)) hval
  let DeltaL : Fin (m + 1) → Fin (m + 1) → ℝ :=
    aasenConsOneMatrix (Delta0 0 0) DeltaT
  refine ⟨DeltaL, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero =>
            simp only [DeltaL, aasenConsOneMatrix_00]
            exact (hDelta0 0 0).trans (mul_le_mul_of_nonneg_right
              (gamma_mono fp hm hval) (abs_nonneg (L 0 0)))
        | succ j =>
            simp only [DeltaL, aasenConsOneMatrix_0s, abs_zero]
            exact mul_nonneg (gamma_nonneg fp hval) (abs_nonneg _)
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            simp only [DeltaL, aasenConsOneMatrix_s0, abs_zero]
            exact mul_nonneg (gamma_nonneg fp hval) (abs_nonneg _)
        | succ j =>
            simpa only [DeltaL, aasenConsOneMatrix_ss, Lt] using hDeltaT i j
  · intro i
    cases i using Fin.cases with
    | zero =>
        rw [Fin.sum_univ_succ]
        have hhead := heq0 0
        rw [Fin.sum_univ_one] at hhead
        have htail :
            (∑ j : Fin m,
              (L 0 j.succ + DeltaL 0 j.succ) *
                flAasenUnitForwardSub fp m L b j.succ) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [hlower 0 j.succ (by simp)]
          simp [DeltaL]
        rw [htail, add_zero]
        simpa [DeltaL, flAasenUnitForwardSub, L0, b0] using hhead
    | succ i =>
        rw [Fin.sum_univ_succ]
        rw [hfirst i]
        simp only [DeltaL, aasenConsOneMatrix_s0, add_zero, zero_mul, zero_add]
        have htail := heqT i
        simpa [DeltaL, flAasenUnitForwardSub, Lt, bt] using htail

theorem flAasenUnitTransposeBackSub_backward_error (fp : FPModel) (m : ℕ)
    (hm : 1 ≤ m) (L : Fin (m + 1) → Fin (m + 1) → ℝ)
    (b : Fin (m + 1) → ℝ)
    (hdiag : ∀ i : Fin (m + 1), L i i = 1)
    (hlower : ∀ i j : Fin (m + 1), i.val < j.val → L i j = 0)
    (hfirst : ∀ i : Fin m, L i.succ 0 = 0)
    (hval : gammaValid fp m) :
    let U : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j => L j i
    ∃ DeltaU : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j, |DeltaU i j| ≤ gamma fp m * |U i j|) ∧
      ∀ i, ∑ j : Fin (m + 1),
        (U i j + DeltaU i j) * flAasenUnitTransposeBackSub fp m L b j = b i := by
  intro U
  have hval1 : gammaValid fp 1 := gammaValid_mono fp hm hval
  let U0 : Fin 1 → Fin 1 → ℝ := fun _ _ => L 0 0
  let b0 : Fin 1 → ℝ := fun _ => b 0
  let Ut : Fin m → Fin m → ℝ := fun i j => L j.succ i.succ
  let bt : Fin m → ℝ := fun i => b i.succ
  obtain ⟨Delta0, hDelta0, heq0⟩ :=
    backSub_backward_error fp 1 U0 b0
      (fun _ => by simp [U0, hdiag])
      (fun i j hij => by omega) hval1
  obtain ⟨DeltaT, hDeltaT, heqT⟩ :=
    backSub_backward_error fp m Ut bt
      (fun i => by simp [Ut, hdiag])
      (fun i j hij => by
        exact hlower j.succ i.succ (by simpa using hij)) hval
  let DeltaU : Fin (m + 1) → Fin (m + 1) → ℝ :=
    aasenConsOneMatrix (Delta0 0 0) DeltaT
  refine ⟨DeltaU, ?_, ?_⟩
  · intro i j
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero =>
            simp only [DeltaU, aasenConsOneMatrix_00, U]
            exact (hDelta0 0 0).trans (mul_le_mul_of_nonneg_right
              (gamma_mono fp hm hval) (abs_nonneg (L 0 0)))
        | succ j =>
            simp only [DeltaU, aasenConsOneMatrix_0s, abs_zero, U]
            exact mul_nonneg (gamma_nonneg fp hval) (abs_nonneg _)
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            simp only [DeltaU, aasenConsOneMatrix_s0, abs_zero, U]
            exact mul_nonneg (gamma_nonneg fp hval) (abs_nonneg _)
        | succ j =>
            simpa only [DeltaU, aasenConsOneMatrix_ss, Ut, U] using hDeltaT i j
  · intro i
    cases i using Fin.cases with
    | zero =>
        rw [Fin.sum_univ_succ]
        have hhead := heq0 0
        rw [Fin.sum_univ_one] at hhead
        have htail :
            (∑ j : Fin m,
              (U 0 j.succ + DeltaU 0 j.succ) *
                flAasenUnitTransposeBackSub fp m L b j.succ) = 0 := by
          apply Finset.sum_eq_zero
          intro j _
          rw [show U 0 j.succ = L j.succ 0 by rfl, hfirst j]
          simp [DeltaU]
        rw [htail, add_zero]
        simpa [DeltaU, flAasenUnitTransposeBackSub, U0, b0, U] using hhead
    | succ i =>
        rw [Fin.sum_univ_succ]
        rw [show U i.succ 0 = L 0 i.succ by rfl, hlower 0 i.succ (by simp)]
        simp only [DeltaU, aasenConsOneMatrix_s0, add_zero, zero_mul, zero_add]
        have htail := heqT i
        simpa [DeltaU, flAasenUnitTransposeBackSub, Ut, bt, U] using htail

/-! ## Equation-(11.15) outer-solve package -/

/-- The two support-aware outer solves for an `(m+1)`-by-`(m+1)` Aasen factor.
Thus the displayed coefficient is literally `gamma_m = gamma_(N-1)`. -/
theorem higham11_15_fl_aasen_unit_outer_triangular_solves_backward_error
    (fp : FPModel) (m : ℕ) (hm : 1 ≤ m)
    (Pmat L : Fin (m + 1) → Fin (m + 1) → ℝ)
    (b y : Fin (m + 1) → ℝ)
    (hdiag : ∀ i : Fin (m + 1), L i i = 1)
    (hlower : ∀ i j : Fin (m + 1), i.val < j.val → L i j = 0)
    (hfirst : ∀ i : Fin m, L i.succ 0 = 0)
    (hval : gammaValid fp m) :
    let rhs : Fin (m + 1) → ℝ := fun i => ∑ j, Pmat i j * b j
    let U : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j => L j i
    let z := flAasenUnitForwardSub fp m L rhs
    let w := flAasenUnitTransposeBackSub fp m L y
    ∃ DeltaL DeltaU : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j, |DeltaL i j| ≤ gamma fp m * |L i j|) ∧
      (∀ i j, |DeltaU i j| ≤ gamma fp m * |U i j|) ∧
      (∀ i, ∑ j, (L i j + DeltaL i j) * z j = rhs i) ∧
      (∀ i, ∑ j, (U i j + DeltaU i j) * w j = y i) := by
  intro rhs U z w
  obtain ⟨DeltaL, hDeltaL, hforward⟩ :=
    flAasenUnitForwardSub_backward_error fp m hm L rhs hdiag hlower hfirst hval
  obtain ⟨DeltaU, hDeltaU, hback⟩ :=
    flAasenUnitTransposeBackSub_backward_error fp m hm L y hdiag hlower hfirst hval
  exact ⟨DeltaL, DeltaU, hDeltaL, hDeltaU, hforward, hback⟩

/-- Computed-factor specialization: all support hypotheses are discharged by
the structural theorems for `flAasen`. -/
theorem higham11_15_fl_computed_aasen_unit_outer_triangular_solves_backward_error
    (fp : FPModel) (m : ℕ) (hm : 1 ≤ m)
    (A Pmat : Fin (m + 1) → Fin (m + 1) → ℝ)
    (b y : Fin (m + 1) → ℝ) (hval : gammaValid fp m) :
    let L := (flAasen fp (m + 1) A).Lhat
    let rhs : Fin (m + 1) → ℝ := fun i => ∑ j, Pmat i j * b j
    let U : Fin (m + 1) → Fin (m + 1) → ℝ := fun i j => L j i
    let z := flAasenUnitForwardSub fp m L rhs
    let w := flAasenUnitTransposeBackSub fp m L y
    ∃ DeltaL DeltaU : Fin (m + 1) → Fin (m + 1) → ℝ,
      (∀ i j, |DeltaL i j| ≤ gamma fp m * |L i j|) ∧
      (∀ i j, |DeltaU i j| ≤ gamma fp m * |U i j|) ∧
      (∀ i, ∑ j, (L i j + DeltaL i j) * z j = rhs i) ∧
      (∀ i, ∑ j, (U i j + DeltaU i j) * w j = y i) := by
  intro L rhs U z w
  apply higham11_15_fl_aasen_unit_outer_triangular_solves_backward_error
    fp m hm Pmat L b y
  · exact flAasen_L_unit_diag fp (m + 1) A
  · exact flAasen_L_upper_zero fp (m + 1) A
  · intro i
    exact flAasen_L_first_col fp (m + 1) A i.succ 0 rfl (by simp)
  · exact hval

end NumStability.Ch11Closure.AasenDirect
