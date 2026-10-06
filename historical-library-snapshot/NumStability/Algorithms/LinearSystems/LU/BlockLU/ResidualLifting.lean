import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum

/-!
# Block LU residual lifting

Reusable rank-one and block-row constructions that lift max-norm residual
bounds to entrywise perturbation matrices.
-/

namespace NumStability

open scoped BigOperators
open scoped Matrix

/-- Max-norm residual lifting used by the DHS block-back-substitution proof.

    If a vector residual `f` is at most `eta * ‖x‖∞`, it can be represented as
    `F x` by a rank-one coefficient perturbation with
    `‖F‖max <= eta`.  The proof places the residual in a column where `x`
    attains its infinity norm.  This is the dimension-free bridge specific to
    the max-entry/max-vector norm pairing in the source analysis. -/
theorem higham13_maxNorm_vecResidual_lift {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (x : Fin k → ℝ) (f : Fin m → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hres : infNormVec f ≤ eta * infNormVec x) :
    ∃ F : Matrix (Fin m) (Fin k) ℝ,
      Matrix.mulVec F x = f ∧ maxEntryNormRect hm hk F ≤ eta := by
  by_cases hxzero : infNormVec x = 0
  · have hfnorm : infNormVec f = 0 := by
      apply le_antisymm
      · calc
          infNormVec f ≤ eta * infNormVec x := hres
          _ = 0 := by rw [hxzero, mul_zero]
      · exact infNormVec_nonneg f
    have hfzero : f = 0 := by
      funext i
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hfnorm] using abs_le_infNormVec f i
      · exact abs_nonneg (f i)
    refine ⟨0, ?_, ?_⟩
    · simp [hfzero]
    · exact le_trans
        (maxEntryNormRect_le_of_entry_abs_le hm hk 0 0 (by simp)) heta
  · have hxpos : 0 < infNormVec x :=
      lt_of_le_of_ne (infNormVec_nonneg x) (Ne.symm hxzero)
    obtain ⟨j0, hj0⟩ := infNormVec_exists_abs_eq hk x
    have hxj0 : x j0 ≠ 0 := by
      intro hx
      rw [hx, abs_zero] at hj0
      linarith
    let F : Matrix (Fin m) (Fin k) ℝ := fun i j =>
      if j = j0 then f i / x j0 else 0
    refine ⟨F, ?_, ?_⟩
    · ext i
      simp [Matrix.mulVec, dotProduct, F, hxj0]
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      by_cases hj : j = j0
      · subst j
        have hfi : |f i| ≤ eta * infNormVec x :=
          le_trans (abs_le_infNormVec f i) hres
        simp only [F, if_pos, abs_div]
        rw [← hj0]
        exact (div_le_iff₀ hxpos).2 (by simpa [hj0] using hfi)
      · simp [F, hj, heta]

/-- Support-preserving form of the max-norm residual lift.

    In addition to the residual equation and max-entry bound, the constructed
    rank-one perturbation has a zero column wherever the supplied vector is
    zero.  This lets a block-back-substitution row mask all diagonal and lower
    block columns before lifting its residual. -/
theorem higham13_maxNorm_vecResidual_lift_zero_columns {m k : ℕ}
    (hm : 0 < m) (hk : 0 < k)
    (x : Fin k → ℝ) (f : Fin m → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hres : infNormVec f ≤ eta * infNormVec x) :
    ∃ F : Matrix (Fin m) (Fin k) ℝ,
      Matrix.mulVec F x = f ∧
      maxEntryNormRect hm hk F ≤ eta ∧
      ∀ j : Fin k, x j = 0 → ∀ i : Fin m, F i j = 0 := by
  by_cases hxzero : infNormVec x = 0
  · have hfnorm : infNormVec f = 0 := by
      apply le_antisymm
      · calc
          infNormVec f ≤ eta * infNormVec x := hres
          _ = 0 := by rw [hxzero, mul_zero]
      · exact infNormVec_nonneg f
    have hfzero : f = 0 := by
      funext i
      apply abs_eq_zero.mp
      apply le_antisymm
      · simpa [hfnorm] using abs_le_infNormVec f i
      · exact abs_nonneg (f i)
    refine ⟨0, ?_, ?_, ?_⟩
    · simp [hfzero]
    · exact le_trans
        (maxEntryNormRect_le_of_entry_abs_le hm hk 0 0 (by simp)) heta
    · simp
  · have hxpos : 0 < infNormVec x :=
      lt_of_le_of_ne (infNormVec_nonneg x) (Ne.symm hxzero)
    obtain ⟨j0, hj0⟩ := infNormVec_exists_abs_eq hk x
    have hxj0 : x j0 ≠ 0 := by
      intro hx
      rw [hx, abs_zero] at hj0
      linarith
    let F : Matrix (Fin m) (Fin k) ℝ := fun i j =>
      if j = j0 then f i / x j0 else 0
    refine ⟨F, ?_, ?_, ?_⟩
    · ext i
      simp [Matrix.mulVec, dotProduct, F, hxj0]
    · apply maxEntryNormRect_le_of_entry_abs_le
      intro i j
      by_cases hj : j = j0
      · subst j
        have hfi : |f i| ≤ eta * infNormVec x :=
          le_trans (abs_le_infNormVec f i) hres
        simp only [F, if_pos, abs_div]
        rw [← hj0]
        exact (div_le_iff₀ hxpos).2 (by simpa [hj0] using hfi)
      · simp [F, hj, heta]
    · intro j hxj i
      by_cases hj : j = j0
      · subst j
        exact (hxj0 hxj).elim
      · simp [F, hj]

/-- Lift a residual against the stacked, already computed upper tail of one
    uniform block-back-substitution row.

    The returned block coefficients vanish at the diagonal and below, their
    full block-row product equals the supplied residual, and every scalar entry
    inherits the same dimension-free `eta` bound. -/
theorem higham13_maxNorm_upperBlockRowResidual_lift {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (f : Fin r → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hres :
      infNormVec f ≤ eta * infNormVec (fun jt : Fin (m * r) =>
        if i.val < (finProdFinEquiv.symm jt).1.val then
          X (finProdFinEquiv.symm jt).1 (finProdFinEquiv.symm jt).2 0
        else 0)) :
    ∃ Delta : Fin m → Matrix (Fin r) (Fin r) ℝ,
      (∑ j : Fin m, Delta j * X j) = (fun s (_k : Fin 1) => f s) ∧
      (∀ j : Fin m, ¬i.val < j.val → Delta j = 0) ∧
      ∀ j : Fin m, ∀ s t : Fin r, |Delta j s t| ≤ eta := by
  let xTail : Fin (m * r) → ℝ := fun jt =>
    if i.val < (finProdFinEquiv.symm jt).1.val then
      X (finProdFinEquiv.symm jt).1 (finProdFinEquiv.symm jt).2 0
    else 0
  obtain ⟨F, hFmul, hFbound, hFzero⟩ :=
    higham13_maxNorm_vecResidual_lift_zero_columns
      hr (Nat.mul_pos hm hr) xTail f eta heta hres
  let Delta : Fin m → Matrix (Fin r) (Fin r) ℝ := fun j s t =>
    F s (finProdFinEquiv (j, t))
  have hInactive : ∀ j : Fin m, ¬i.val < j.val → Delta j = 0 := by
    intro j hj
    ext s t
    have hxzero : xTail (finProdFinEquiv (j, t)) = 0 := by
      rw [show xTail (finProdFinEquiv (j, t)) =
          if i.val < j.val then X j t 0 else 0 by
        simp only [xTail, Equiv.symm_apply_apply]]
      simp [hj]
    exact hFzero (finProdFinEquiv (j, t)) hxzero s
  have hEntry : ∀ j : Fin m, ∀ s t : Fin r, |Delta j s t| ≤ eta := by
    intro j s t
    exact le_trans
      (entry_le_maxEntryNormRect hr (Nat.mul_pos hm hr) F s
        (finProdFinEquiv (j, t))) hFbound
  refine ⟨Delta, ?_, hInactive, hEntry⟩
  ext s k
  fin_cases k
  have hFmul_s := congrFun hFmul s
  have hFlat :
      (∑ jt : Fin (m * r), F s jt * xTail jt) =
        ∑ jt : Fin m × Fin r,
          F s (finProdFinEquiv jt) * X jt.1 jt.2 0 := by
    rw [Fintype.sum_equiv finProdFinEquiv]
    intro jt
    have hxTailApply : xTail (finProdFinEquiv jt) =
        if i.val < jt.1.val then X jt.1 jt.2 0 else 0 := by
      simp only [xTail, Equiv.symm_apply_apply]
    rw [hxTailApply]
    by_cases hj : i.val < jt.1.val
    · simp [hj]
    · have hxzero : xTail (finProdFinEquiv jt) = 0 := by
        rw [hxTailApply]
        simp [hj]
      have hzero := hFzero (finProdFinEquiv jt) hxzero s
      simp [hj, hzero]
  calc
    (∑ j : Fin m, Delta j * X j) s 0 =
        ∑ j : Fin m, ∑ t : Fin r,
          F s (finProdFinEquiv (j, t)) * X j t 0 := by
      simp only [Matrix.sum_apply, Matrix.mul_apply, Delta]
    _ = ∑ jt : Fin m × Fin r,
          F s (finProdFinEquiv jt) * X jt.1 jt.2 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ jt : Fin (m * r), F s jt * xTail jt := hFlat.symm
    _ = f s := by
      simpa [Matrix.mulVec, dotProduct] using hFmul_s

/-- The stacked computed upper tail in a fixed block-back-substitution row. -/
noncomputable def dhsBlockBackUpperTailVector {m r : ℕ}
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    Fin (m * r) → ℝ := fun jt =>
  if i.val < (finProdFinEquiv.symm jt).1.val then
    X (finProdFinEquiv.symm jt).1 (finProdFinEquiv.symm jt).2 0
  else 0

@[simp] theorem dhsBlockBackUpperTailVector_apply {m r : ℕ}
    (i j : Fin m) (s : Fin r)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    dhsBlockBackUpperTailVector i X (finProdFinEquiv (j, s)) =
      if i.val < j.val then X j s 0 else 0 := by
  simp [dhsBlockBackUpperTailVector]

/-- Single-column matrix representation of `dhsBlockBackUpperTailVector`. -/
noncomputable def dhsBlockBackUpperTailColumn {m r : ℕ}
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    Matrix (Fin (m * r)) (Fin 1) ℝ := fun jt _k =>
  dhsBlockBackUpperTailVector i X jt

@[simp] theorem dhsBlockBackUpperTailColumn_apply {m r : ℕ}
    (i j : Fin m) (s : Fin r)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    dhsBlockBackUpperTailColumn i X (finProdFinEquiv (j, s)) 0 =
      if i.val < j.val then X j s 0 else 0 := by
  simp [dhsBlockBackUpperTailColumn]

/-- The stacked computed upper suffix in a fixed block-back-substitution row.

    Unlike the strict tail, this mask includes the current diagonal solution
    block.  It is the source-correct support for absorbing both the rounded
    tail-product residual and the following subtraction residual: the latter
    may contribute a perturbation to the diagonal coefficient as well. -/
noncomputable def dhsBlockBackUpperSuffixVector {m r : ℕ}
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    Fin (m * r) → ℝ := fun jt =>
  if i.val ≤ (finProdFinEquiv.symm jt).1.val then
    X (finProdFinEquiv.symm jt).1 (finProdFinEquiv.symm jt).2 0
  else 0

@[simp] theorem dhsBlockBackUpperSuffixVector_apply {m r : ℕ}
    (i j : Fin m) (s : Fin r)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    dhsBlockBackUpperSuffixVector i X (finProdFinEquiv (j, s)) =
      if i.val ≤ j.val then X j s 0 else 0 := by
  simp [dhsBlockBackUpperSuffixVector]

/-- Single-column matrix representation of
    `dhsBlockBackUpperSuffixVector`. -/
noncomputable def dhsBlockBackUpperSuffixColumn {m r : ℕ}
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    Matrix (Fin (m * r)) (Fin 1) ℝ := fun jt _k =>
  dhsBlockBackUpperSuffixVector i X jt

/-- The strict upper tail is entrywise masked by the full upper suffix, so its
    infinity norm is no larger. -/
theorem dhsBlockBackUpperTail_infNormVec_le_suffix {m r : ℕ}
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    infNormVec (dhsBlockBackUpperTailVector i X) ≤
      infNormVec (dhsBlockBackUpperSuffixVector i X) := by
  apply infNormVec_le_of_abs_le
  · intro jt
    let q := finProdFinEquiv.symm jt
    by_cases hq : i.val < q.1.val
    · have hle : i.val ≤ q.1.val := Nat.le_of_lt hq
      have htail : dhsBlockBackUpperTailVector i X jt = X q.1 q.2 0 := by
        change (if i.val < q.1.val then X q.1 q.2 0 else 0) = _
        rw [if_pos hq]
      have hsuffix :
          dhsBlockBackUpperSuffixVector i X jt = X q.1 q.2 0 := by
        change (if i.val ≤ q.1.val then X q.1 q.2 0 else 0) = _
        rw [if_pos hle]
      rw [htail]
      have hs := abs_le_infNormVec (dhsBlockBackUpperSuffixVector i X) jt
      rw [hsuffix] at hs
      exact hs
    · change |if i.val < q.1.val then X q.1 q.2 0 else 0| ≤ _
      simp [hq, infNormVec_nonneg]
  · exact infNormVec_nonneg _

/-- The current computed block is one active component of the full upper
    suffix, so its column infinity norm is bounded by the suffix norm. -/
theorem dhsBlockBackCurrentBlock_infNormVec_le_suffix {m r : ℕ}
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ) :
    infNormVec (fun s : Fin r => X i s 0) ≤
      infNormVec (dhsBlockBackUpperSuffixVector i X) := by
  apply infNormVec_le_of_abs_le
  · intro s
    have hs := abs_le_infNormVec
      (dhsBlockBackUpperSuffixVector i X) (finProdFinEquiv (i, s))
    simpa using hs
  · exact infNormVec_nonneg _

/-- Lift a row residual against the full computed upper suffix.

    The resulting coefficient blocks vanish strictly below the current block
    row, their product with the computed solution blocks is exactly the
    residual, and every scalar entry inherits the common dimension-free
    `eta` bound. -/
theorem higham13_maxNorm_upperBlockSuffixResidual_lift {m r : ℕ}
    (hm : 0 < m) (hr : 0 < r)
    (i : Fin m) (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (f : Fin r → ℝ) (eta : ℝ)
    (heta : 0 ≤ eta)
    (hres : infNormVec f ≤
      eta * infNormVec (dhsBlockBackUpperSuffixVector i X)) :
    ∃ Delta : Fin m → Matrix (Fin r) (Fin r) ℝ,
      (∑ j : Fin m, Delta j * X j) = (fun s (_k : Fin 1) => f s) ∧
      (∀ j : Fin m, j.val < i.val → Delta j = 0) ∧
      ∀ j : Fin m, ∀ s t : Fin r, |Delta j s t| ≤ eta := by
  let xSuffix := dhsBlockBackUpperSuffixVector i X
  obtain ⟨F, hFmul, hFbound, hFzero⟩ :=
    higham13_maxNorm_vecResidual_lift_zero_columns
      hr (Nat.mul_pos hm hr) xSuffix f eta heta hres
  let Delta : Fin m → Matrix (Fin r) (Fin r) ℝ := fun j s t =>
    F s (finProdFinEquiv (j, t))
  have hInactive : ∀ j : Fin m, j.val < i.val → Delta j = 0 := by
    intro j hji
    ext s t
    have hxzero : xSuffix (finProdFinEquiv (j, t)) = 0 := by
      rw [show xSuffix (finProdFinEquiv (j, t)) =
          if i.val ≤ j.val then X j t 0 else 0 by
        simp only [xSuffix, dhsBlockBackUpperSuffixVector_apply]]
      simp [Nat.not_le_of_lt hji]
    exact hFzero (finProdFinEquiv (j, t)) hxzero s
  have hEntry : ∀ j : Fin m, ∀ s t : Fin r, |Delta j s t| ≤ eta := by
    intro j s t
    exact le_trans
      (entry_le_maxEntryNormRect hr (Nat.mul_pos hm hr) F s
        (finProdFinEquiv (j, t))) hFbound
  refine ⟨Delta, ?_, hInactive, hEntry⟩
  ext s k
  fin_cases k
  have hFmul_s := congrFun hFmul s
  have hFlat :
      (∑ jt : Fin (m * r), F s jt * xSuffix jt) =
        ∑ jt : Fin m × Fin r,
          F s (finProdFinEquiv jt) * X jt.1 jt.2 0 := by
    rw [Fintype.sum_equiv finProdFinEquiv]
    intro jt
    have hxSuffixApply : xSuffix (finProdFinEquiv jt) =
        if i.val ≤ jt.1.val then X jt.1 jt.2 0 else 0 := by
      simpa only [xSuffix] using
        dhsBlockBackUpperSuffixVector_apply i jt.1 jt.2 X
    rw [hxSuffixApply]
    by_cases hj : i.val ≤ jt.1.val
    · simp [hj]
    · have hxzero : xSuffix (finProdFinEquiv jt) = 0 := by
        rw [hxSuffixApply]
        simp [hj]
      have hzero := hFzero (finProdFinEquiv jt) hxzero s
      simp [hj, hzero]
  calc
    (∑ j : Fin m, Delta j * X j) s 0 =
        ∑ j : Fin m, ∑ t : Fin r,
          F s (finProdFinEquiv (j, t)) * X j t 0 := by
      simp only [Matrix.sum_apply, Matrix.mul_apply, Delta]
    _ = ∑ jt : Fin m × Fin r,
          F s (finProdFinEquiv jt) * X jt.1 jt.2 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ jt : Fin (m * r), F s jt * xSuffix jt := hFlat.symm
    _ = f s := by
      simpa [Matrix.mulVec, dotProduct] using hFmul_s

/-- Flattened coefficient row containing exactly the strict upper block tail. -/
noncomputable def dhsBlockBackUpperTailRowFlat {m r : ℕ}
    (i : Fin m) (U : Fin m → Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin r) (Fin (m * r)) ℝ := fun s jt =>
  if i.val < (finProdFinEquiv.symm jt).1.val then
    U (finProdFinEquiv.symm jt).1 s (finProdFinEquiv.symm jt).2
  else 0

@[simp] theorem dhsBlockBackUpperTailRowFlat_apply {m r : ℕ}
    (i j : Fin m) (s t : Fin r)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ) :
    dhsBlockBackUpperTailRowFlat i U s (finProdFinEquiv (j, t)) =
      if i.val < j.val then U j s t else 0 := by
  simp [dhsBlockBackUpperTailRowFlat]

/-- Multiplying the flattened strict upper block row by its stacked tail is
    exactly the sum of the source block products. -/
theorem dhsBlockBackUpperTailRowFlat_mul_apply {m r : ℕ}
    (i : Fin m)
    (U : Fin m → Matrix (Fin r) (Fin r) ℝ)
    (X : Fin m → Matrix (Fin r) (Fin 1) ℝ)
    (s : Fin r) :
    (dhsBlockBackUpperTailRowFlat i U *
        dhsBlockBackUpperTailColumn i X) s 0 =
      (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
        U j * X j) s 0 := by
  calc
    (dhsBlockBackUpperTailRowFlat i U *
        dhsBlockBackUpperTailColumn i X) s 0 =
        ∑ jt : Fin (m * r),
          dhsBlockBackUpperTailRowFlat i U s jt *
            dhsBlockBackUpperTailColumn i X jt 0 := by
      rw [Matrix.mul_apply]
    _ = ∑ jt : Fin m × Fin r,
          (if i.val < jt.1.val then U jt.1 s jt.2 else 0) *
            X jt.1 jt.2 0 := by
      rw [Fintype.sum_equiv finProdFinEquiv]
      intro jt
      rw [dhsBlockBackUpperTailRowFlat_apply,
        dhsBlockBackUpperTailColumn_apply]
      by_cases hj : i.val < jt.1.val <;> simp [hj]
    _ = ∑ j : Fin m, ∑ t : Fin r,
          (if i.val < j.val then U j s t else 0) * X j t 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ j : Fin m,
          if i.val < j.val then (U j * X j) s 0 else 0 := by
      apply Finset.sum_congr rfl
      intro j _hjmem
      by_cases hj : i.val < j.val
      · simp [hj, Matrix.mul_apply]
      · simp [hj]
    _ = (∑ j ∈ Finset.univ.filter (fun j : Fin m => i.val < j.val),
          U j * X j) s 0 := by
      rw [Finset.sum_filter]
      simp only [Matrix.sum_apply]
      apply Finset.sum_congr rfl
      intro j _hjmem
      by_cases hj : i.val < j.val <;> simp [hj]

end NumStability
