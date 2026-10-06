import NumStability.Analysis.HighamChapter7

namespace NumStability

open scoped BigOperators

/-!
# Higham Chapter 7: rectangular source statements

The printed statements of Theorems 7.1 and 7.3 allow an `m × n` data
matrix.  The older public wrappers used one dimension for both the residual
and solution spaces.  This file restores the two independent dimensions.
-/

/-- Residual `b - A y` for a real `m × n` system. -/
def higham7RectResidual {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b : Fin m → ℝ) : Fin m → ℝ :=
  fun i => b i - ∑ j : Fin n, A i j * y j

private lemma higham7_rect_div_abs_le_of_bound {r s ε : ℝ}
    (hε : 0 ≤ ε) (hs : 0 ≤ s) (hbound : |r| ≤ ε * s) :
    |if s = 0 then 0 else r / s| ≤ ε := by
  split_ifs with hs0
  · simpa using hε
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    rw [abs_div, abs_of_pos hspos]
    exact (div_le_iff₀ hspos).2 (by simpa [mul_comm] using hbound)

/-- **Theorem 7.3 (Oettli--Prager), necessary direction, rectangular form.**

For an `m × n` system, componentwise admissible perturbations imply
`|b - A y| ≤ ε (E |y| + f)`. -/
theorem higham7_3_rectangular_necessary {m n : ℕ}
    (A ΔA E : Fin m → Fin n → ℝ)
    (y : Fin n → ℝ) (b Δb f : Fin m → ℝ) (ε : ℝ)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hperturbed : ∀ i,
      ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |higham7RectResidual A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i) := by
  intro i
  have hres : higham7RectResidual A y b i =
      ∑ j : Fin n, ΔA i j * y j - Δb i := by
    unfold higham7RectResidual
    have hp := hperturbed i
    simp_rw [add_mul, Finset.sum_add_distrib] at hp
    linarith
  rw [hres]
  calc
    |∑ j : Fin n, ΔA i j * y j - Δb i|
        ≤ |∑ j : Fin n, ΔA i j * y j| + |Δb i| := by
          simpa [sub_eq_add_neg] using
            (abs_add_le (∑ j : Fin n, ΔA i j * y j) (-Δb i))
    _ ≤ (∑ j : Fin n, |ΔA i j| * |y j|) + |Δb i| := by
          apply add_le_add
          · calc
            |∑ j : Fin n, ΔA i j * y j|
                ≤ ∑ j : Fin n, |ΔA i j * y j| :=
                  Finset.abs_sum_le_sum_abs _ _
            _ = ∑ j : Fin n, |ΔA i j| * |y j| := by
                  apply Finset.sum_congr rfl
                  intro j _
                  rw [abs_mul]
          · exact le_rfl
    _ ≤ (∑ j : Fin n, (ε * E i j) * |y j|) + ε * f i := by
          exact add_le_add
            (Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _))
            (hΔb i)
    _ = ε * (∑ j : Fin n, E i j * |y j| + f i) := by
          rw [mul_add, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring

/-- **Theorem 7.3 (Oettli--Prager), sufficient direction, rectangular form.**

The proof is constructive, row by row.  It builds perturbations with the
printed componentwise budgets and proves the perturbed `m × n` system exactly.
-/
theorem higham7_3_rectangular_sufficient {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b f : Fin m → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hbound : ∀ i, |higham7RectResidual A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i)) :
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * E i j) ∧
      (∀ i, |Δb i| ≤ ε * f i) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  let r : Fin m → ℝ := higham7RectResidual A y b
  let s : Fin m → ℝ := fun i => ∑ j : Fin n, E i j * |y j| + f i
  let t : Fin m → ℝ := fun i => if s i = 0 then 0 else r i / s i
  let ΔA : Fin m → Fin n → ℝ :=
    fun i j => t i * E i j * signInd (y j)
  let Δb : Fin m → ℝ := fun i => -(t i * f i)
  have hs : ∀ i, 0 ≤ s i := by
    intro i
    exact add_nonneg
      (Finset.sum_nonneg fun j _ => mul_nonneg (hE i j) (abs_nonneg _))
      (hf i)
  have ht : ∀ i, |t i| ≤ ε := by
    intro i
    exact higham7_rect_div_abs_le_of_bound hε (hs i) (hbound i)
  refine ⟨ΔA, Δb, ?_, ?_, ?_⟩
  · intro i j
    show |t i * E i j * signInd (y j)| ≤ ε * E i j
    rw [abs_mul, abs_mul, abs_signInd, mul_one, abs_of_nonneg (hE i j)]
    exact mul_le_mul_of_nonneg_right (ht i) (hE i j)
  · intro i
    show |-(t i * f i)| ≤ ε * f i
    rw [abs_neg, abs_mul, abs_of_nonneg (hf i)]
    exact mul_le_mul_of_nonneg_right (ht i) (hf i)
  · intro i
    have hΔAy : ∀ j, ΔA i j * y j = t i * E i j * |y j| := by
      intro j
      show t i * E i j * signInd (y j) * y j = t i * E i j * |y j|
      rw [mul_assoc (t i * E i j), signInd_mul_eq_abs]
    have hsum : ∑ j : Fin n, t i * E i j * |y j| =
        t i * ∑ j : Fin n, E i j * |y j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hts : t i * s i = r i := by
      dsimp [t]
      split_ifs with hs0
      · have hr0 : r i = 0 := by
          apply abs_eq_zero.mp
          apply le_antisymm
          · calc
              |r i| ≤ ε * s i := hbound i
              _ = 0 := by rw [hs0, mul_zero]
          · exact abs_nonneg _
        simp [hs0, hr0]
      · exact div_mul_cancel₀ (r i) hs0
    simp_rw [add_mul, hΔAy, Finset.sum_add_distrib]
    rw [hsum]
    change (∑ j : Fin n, A i j * y j) +
        t i * (∑ j : Fin n, E i j * |y j|) = b i - t i * f i
    have hr : r i = b i - ∑ j : Fin n, A i j * y j := rfl
    have hsdef : s i = ∑ j : Fin n, E i j * |y j| + f i := rfl
    rw [hsdef] at hts
    linarith

/-- **Theorem 7.3 (Oettli--Prager), full rectangular characterization.**

This is the literal `m × n` equivalence printed in the chapter. -/
theorem higham7_3_rectangular {m n : ℕ}
    (A E : Fin m → Fin n → ℝ) (y : Fin n → ℝ) (b f : Fin m → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i) :
    (∀ i, |higham7RectResidual A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i)) ↔
    ∃ (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * E i j) ∧
      (∀ i, |Δb i| ≤ ε * f i) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  constructor
  · exact higham7_3_rectangular_sufficient A E y b f ε hε hE hf
  · rintro ⟨ΔA, Δb, hΔA, hΔb, hperturbed⟩
    exact higham7_3_rectangular_necessary A ΔA E y b Δb f ε
      hΔA hΔb hperturbed

/-! ## Theorem 7.1 (Rigal--Gaches), rectangular subordinate-norm form -/

/-- **Theorem 7.1, necessary direction, rectangular form.** -/
theorem higham7_1_rectangular_necessary
    {m n : ℕ} {νx : CVec n → ℝ} {νr : CVec m → ℝ}
    (_hνx : IsComplexVectorNorm νx) (hνr : IsComplexVectorNorm νr)
    {A E ΔA : CMatrix m n} {y : CVec n} {b f Δb : CVec m}
    {e ε : ℝ} (_hε : 0 ≤ ε)
    (_hE : IsMixedSubordinateMatrixNormValue νx νr E e)
    (hΔA : MixedSubordinateMatrixBound νx νr ΔA (ε * e))
    (hΔb : νr Δb ≤ ε * νr f)
    (hperturbed : complexMatrixVecMul (fun i j => A i j + ΔA i j) y =
      fun i => b i + Δb i) :
    νr (fun i => b i - complexMatrixVecMul A y i) ≤
      ε * (e * νx y + νr f) := by
  have hres :
      (fun i => b i - complexMatrixVecMul A y i) =
        (fun i => complexMatrixVecMul ΔA y i - Δb i) := by
    ext i
    have hp := congrFun hperturbed i
    unfold complexMatrixVecMul at hp ⊢
    simp_rw [add_mul, Finset.sum_add_distrib] at hp
    have hb :
        b i = (∑ j : Fin n, A i j * y j) +
          (∑ j : Fin n, ΔA i j * y j) - Δb i := by
      calc
        b i = (b i + Δb i) - Δb i := by ring
        _ = (∑ j : Fin n, A i j * y j) +
            (∑ j : Fin n, ΔA i j * y j) - Δb i := by rw [← hp]
    rw [hb]
    ring
  have htriangle :
      νr (fun i => complexMatrixVecMul ΔA y i - Δb i) ≤
        νr (complexMatrixVecMul ΔA y) + νr Δb := by
    have heq :
        (fun i => complexMatrixVecMul ΔA y i - Δb i) =
          complexVecAdd (complexMatrixVecMul ΔA y)
            (complexVecSMul (-1 : ℂ) Δb) := by
      ext i
      simp [complexVecAdd, complexVecSMul, sub_eq_add_neg]
    rw [heq]
    calc
      νr (complexVecAdd (complexMatrixVecMul ΔA y)
          (complexVecSMul (-1 : ℂ) Δb))
          ≤ νr (complexMatrixVecMul ΔA y) +
              νr (complexVecSMul (-1 : ℂ) Δb) := hνr.add_le _ _
      _ = νr (complexMatrixVecMul ΔA y) + νr Δb := by
            rw [hνr.smul (-1 : ℂ) Δb]
            norm_num
  rw [hres]
  calc
    νr (fun i => complexMatrixVecMul ΔA y i - Δb i)
        ≤ νr (complexMatrixVecMul ΔA y) + νr Δb := htriangle
    _ ≤ (ε * e) * νx y + ε * νr f := add_le_add (hΔA y) hΔb
    _ = ε * (e * νx y + νr f) := by ring

/-- Equation `(7.3)`, rectangular norm-attaining perturbations in the
positive-denominator case.  The perturbation matrix is genuinely `m × n`:
its rows live in the residual space and its columns in the solution space. -/
theorem higham7_1_rectangular_attaining_perturbations
    {m n : ℕ} (hn : 0 < n)
    {νx : CVec n → ℝ} {νr : CVec m → ℝ}
    (hνx : IsComplexVectorNorm νx) (hνr : IsComplexVectorNorm νr)
    {A E : CMatrix m n} {y : CVec n} {b f : CVec m} {e : ℝ}
    (hE : IsMixedSubordinateMatrixNormValue νx νr E e)
    (hy : 0 < νx y) (hd : 0 < e * νx y + νr f) :
    let r : CVec m := fun i => b i - complexMatrixVecMul A y i
    let d : ℝ := e * νx y + νr f
    ∃ φ : CVec n → ℂ, ∃ ΔAmin : CMatrix m n, ∃ Δbmin : CVec m,
      IsDualFunctionalNormValue νx φ 1 ∧
      φ y = (νx y : ℂ) ∧
      ΔAmin = (fun i j =>
        (((e / d) : ℝ) : ℂ) * rankOneCMatrixFromFunctional φ r i j) ∧
      Δbmin = complexVecSMul (-((νr f / d : ℝ) : ℂ)) r ∧
      MixedSubordinateMatrixBound νx νr ΔAmin ((νr r / d) * e) ∧
      νr Δbmin ≤ (νr r / d) * νr f ∧
      complexMatrixVecMul (fun i j => A i j + ΔAmin i j) y =
        fun i => b i + Δbmin i := by
  intro r d
  have he : 0 ≤ e :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hνx hνr hE
  have hd0 : d ≠ 0 := ne_of_gt hd
  obtain ⟨φ, hφ, hφy⟩ :=
    exists_dualFunctionalNormValue_one_of_pos_vector hνx hy
  let ΔAmin : CMatrix m n := fun i j =>
    (((e / d : ℝ) : ℂ)) * rankOneCMatrixFromFunctional φ r i j
  let Δbmin : CVec m := complexVecSMul (-((νr f / d : ℝ) : ℂ)) r
  refine ⟨φ, ΔAmin, Δbmin, hφ, hφy, rfl, rfl, ?_, ?_, ?_⟩
  · intro v
    have hcoef : 0 ≤ e / d := div_nonneg he (le_of_lt hd)
    calc
      νr (complexMatrixVecMul ΔAmin v)
          = νr (complexVecSMul (((e / d : ℝ) : ℂ))
              (complexMatrixVecMul (rankOneCMatrixFromFunctional φ r) v)) := by
                congr 1
                ext i
                dsimp [ΔAmin, complexMatrixVecMul, complexVecSMul]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
      _ = (e / d) *
          νr (complexMatrixVecMul (rankOneCMatrixFromFunctional φ r) v) := by
            rw [hνr.smul (((e / d : ℝ) : ℂ))
              (complexMatrixVecMul (rankOneCMatrixFromFunctional φ r) v)]
            rw [Complex.norm_of_nonneg hcoef]
      _ = (e / d) * (‖φ v‖ * νr r) := by
            rw [complexMatrixVecMul_rankOneCMatrixFromFunctional hφ.linear]
            rw [rankOneOperator_apply_norm hνr φ r v]
      _ ≤ (e / d) * (νx v * νr r) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            exact mul_le_mul_of_nonneg_right
              (by simpa using hφ.bound v) (hνr.nonneg r)
      _ = ((νr r / d) * e) * νx v := by ring_nf
  · have hcoef : 0 ≤ νr f / d :=
      div_nonneg (hνr.nonneg f) (le_of_lt hd)
    calc
      νr Δbmin = (νr f / d) * νr r := by
        dsimp [Δbmin]
        rw [hνr.smul (-((νr f / d : ℝ) : ℂ)) r]
        rw [norm_neg, Complex.norm_of_nonneg hcoef]
      _ ≤ (νr r / d) * νr f := by
            rw [show (νr f / d) * νr r = (νr r / d) * νr f by ring]
  · have hΔAy :
        complexMatrixVecMul ΔAmin y =
          complexVecSMul ((((e * νx y) / d : ℝ) : ℂ)) r := by
      calc
        complexMatrixVecMul ΔAmin y =
            complexVecSMul (((e / d : ℝ) : ℂ))
              (complexMatrixVecMul (rankOneCMatrixFromFunctional φ r) y) := by
                ext i
                dsimp [ΔAmin, complexMatrixVecMul, complexVecSMul]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = complexVecSMul (((e / d : ℝ) : ℂ)) (rankOneOperator φ r y) := by
              rw [complexMatrixVecMul_rankOneCMatrixFromFunctional hφ.linear]
        _ = complexVecSMul ((((e * νx y) / d : ℝ) : ℂ)) r := by
              ext i
              simp [rankOneOperator, hφy, complexVecSMul]
              ring_nf
    have hsplit : 1 - (e * νx y) / d = νr f / d := by
      field_simp [hd0]
      ring
    ext i
    have hΔAyi := congrFun hΔAy i
    have hri : r i = b i - complexMatrixVecMul A y i := rfl
    have hΔbi : Δbmin i = -((νr f / d : ℝ) : ℂ) * r i := by
      simp [Δbmin, complexVecSMul]
    calc
      complexMatrixVecMul (fun i j => A i j + ΔAmin i j) y i
          = complexMatrixVecMul A y i + complexMatrixVecMul ΔAmin y i := by
              simp [complexMatrixVecMul, Finset.sum_add_distrib, add_mul]
      _ = complexMatrixVecMul A y i +
          (((e * νx y) / d : ℝ) : ℂ) * r i := by
            rw [hΔAyi]
            simp [complexVecSMul]
      _ = complexMatrixVecMul A y i +
          (((e * νx y) / d : ℝ) : ℂ) *
            (b i - complexMatrixVecMul A y i) := by rw [hri]
      _ = b i + (-((νr f / d : ℝ) : ℂ)) *
          (b i - complexMatrixVecMul A y i) := by
            have hsplitC :
                (1 : ℂ) - ((((e * νx y) / d : ℝ) : ℂ)) =
                  ((νr f / d : ℝ) : ℂ) := by exact_mod_cast hsplit
            rw [← hsplitC]
            ring
      _ = b i + Δbmin i := by rw [hΔbi]

/-- **Theorem 7.1, sufficient direction, rectangular form.** -/
theorem higham7_1_rectangular_sufficient
    {m n : ℕ} (hn : 0 < n)
    {νx : CVec n → ℝ} {νr : CVec m → ℝ}
    (hνx : IsComplexVectorNorm νx) (hνr : IsComplexVectorNorm νr)
    {A E : CMatrix m n} {y : CVec n} {b f : CVec m} {e ε : ℝ}
    (hε : 0 ≤ ε)
    (hE : IsMixedSubordinateMatrixNormValue νx νr E e)
    (hbound : νr (fun i => b i - complexMatrixVecMul A y i) ≤
      ε * (e * νx y + νr f)) :
    ∃ ΔA : CMatrix m n, ∃ Δb : CVec m,
      MixedSubordinateMatrixBound νx νr ΔA (ε * e) ∧
      νr Δb ≤ ε * νr f ∧
      complexMatrixVecMul (fun i j => A i j + ΔA i j) y =
        fun i => b i + Δb i := by
  have he : 0 ≤ e :=
    mixedSubordinateMatrixNormValue_nonneg_of_nonempty hn hνx hνr hE
  let ΔA0 : CMatrix m n := fun _ _ => 0
  have hΔA0 : MixedSubordinateMatrixBound νx νr ΔA0 (ε * e) := by
    intro v
    have hz : complexMatrixVecMul ΔA0 v = 0 := by
      ext i
      simp [ΔA0, complexMatrixVecMul]
    rw [hz, (hνr.eq_zero_iff (0 : CVec m)).2 rfl]
    exact mul_nonneg (mul_nonneg hε he) (hνx.nonneg v)
  by_cases hy0 : νx y = 0
  · let r : CVec m := fun i => b i - complexMatrixVecMul A y i
    let Δb0 : CVec m := complexVecSMul (-1 : ℂ) r
    refine ⟨ΔA0, Δb0, hΔA0, ?_, ?_⟩
    · calc
        νr Δb0 = νr r := by
          dsimp [Δb0]
          rw [hνr.smul (-1 : ℂ) r]
          norm_num
        _ ≤ ε * (e * νx y + νr f) := by simpa [r] using hbound
        _ = ε * νr f := by rw [hy0]; ring
    · have hyvec : y = 0 := (hνx.eq_zero_iff y).1 hy0
      subst y
      ext i
      simp [ΔA0, Δb0, r, complexMatrixVecMul, complexVecSMul]
  · have hy : 0 < νx y :=
      lt_of_le_of_ne (hνx.nonneg y) (Ne.symm hy0)
    let r : CVec m := fun i => b i - complexMatrixVecMul A y i
    let d : ℝ := e * νx y + νr f
    by_cases hd0 : d = 0
    · have hr0 : νr r = 0 := by
        apply le_antisymm
        · have h := hbound
          simpa [r, d, hd0] using h
        · exact hνr.nonneg r
      have hrvec : r = 0 := (hνr.eq_zero_iff r).1 hr0
      refine ⟨ΔA0, 0, hΔA0, ?_, ?_⟩
      · rw [(hνr.eq_zero_iff (0 : CVec m)).2 rfl]
        exact mul_nonneg hε (hνr.nonneg f)
      · have hAy : complexMatrixVecMul A y = b := by
          ext i
          have hi := congrFun hrvec i
          exact (sub_eq_zero.mp (by simpa [r] using hi)).symm
        ext i
        simpa [ΔA0, complexMatrixVecMul] using congrFun hAy i
    · have hd : 0 < d :=
        lt_of_le_of_ne
          (add_nonneg (mul_nonneg he (le_of_lt hy)) (hνr.nonneg f))
          (Ne.symm hd0)
      have hatt := higham7_1_rectangular_attaining_perturbations
        (m := m) (n := n) (A := A) (E := E) (y := y)
        (b := b) (f := f) (e := e) hn hνx hνr hE hy hd
      dsimp [r, d] at hatt
      obtain ⟨φ, ΔAmin, Δbmin, hφ, hφy, hΔAdef, hΔbdef,
        hΔAη, hΔbη, hexact⟩ := hatt
      have hη : νr r / d ≤ ε := by
        apply (div_le_iff₀ hd).2
        simpa [r, d] using hbound
      refine ⟨ΔAmin, Δbmin, ?_, ?_, hexact⟩
      · intro v
        calc
          νr (complexMatrixVecMul ΔAmin v)
              ≤ ((νr r / d) * e) * νx v := hΔAη v
          _ ≤ (ε * e) * νx v := by
                apply mul_le_mul_of_nonneg_right
                · exact mul_le_mul_of_nonneg_right hη he
                · exact hνx.nonneg v
      · exact hΔbη.trans
          (mul_le_mul_of_nonneg_right hη (hνr.nonneg f))

/-- **Theorem 7.1 (Rigal--Gaches), full rectangular characterization.**

Unlike the older square wrapper, this preserves the PDF's independent row
and column dimensions and its source/target subordinate norms. -/
theorem higham7_1_rectangular
    {m n : ℕ} (hn : 0 < n)
    {νx : CVec n → ℝ} {νr : CVec m → ℝ}
    (hνx : IsComplexVectorNorm νx) (hνr : IsComplexVectorNorm νr)
    {A E : CMatrix m n} {y : CVec n} {b f : CVec m} {e ε : ℝ}
    (hε : 0 ≤ ε)
    (hE : IsMixedSubordinateMatrixNormValue νx νr E e) :
    (νr (fun i => b i - complexMatrixVecMul A y i) ≤
      ε * (e * νx y + νr f)) ↔
    ∃ ΔA : CMatrix m n, ∃ Δb : CVec m,
      MixedSubordinateMatrixBound νx νr ΔA (ε * e) ∧
      νr Δb ≤ ε * νr f ∧
      complexMatrixVecMul (fun i j => A i j + ΔA i j) y =
        fun i => b i + Δb i := by
  constructor
  · exact higham7_1_rectangular_sufficient hn hνx hνr hε hE
  · rintro ⟨ΔA, Δb, hΔA, hΔb, hexact⟩
    exact higham7_1_rectangular_necessary hνx hνr hε hE hΔA hΔb hexact

end NumStability
