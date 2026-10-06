import Mathlib.Analysis.Normed.Operator.Banach
import NumStability.Algorithms.LinearSystems.LU.BlockLU.DiagonalDominance
import NumStability.Analysis.MatrixAlgebra

/-!
  Algorithms/LinearSystems/LU/BlockLU/ArbitraryNorm.lean

  Reusable arbitrary-subordinate-norm block-LU foundations.

  Blocks are continuous linear endomorphisms of an arbitrary finite-
  dimensional normed real space. Their Mathlib operator norm is therefore
  the subordinate norm induced by that chosen vector norm.
-/

namespace NumStability

open scoped BigOperators

/-- Action of a square block table of continuous linear endomorphisms. -/
noncomputable def higham13_clmBlockAction {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → Fin m → E →L[ℝ] E) (x : Fin m → E) : Fin m → E :=
  fun i => ∑ j : Fin m, A i j (x j)

/-- Linear-map packaging of `higham13_clmBlockAction`, used to transport
injectivity to surjectivity in the finite-dimensional row-BDD argument. -/
noncomputable def higham13_clmBlockActionLinear {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → Fin m → E →L[ℝ] E) :
    (Fin m → E) →ₗ[ℝ] (Fin m → E) where
  toFun := higham13_clmBlockAction A
  map_add' := by
    intro x y
    funext i
    simp [higham13_clmBlockAction, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    funext i
    simp [higham13_clmBlockAction, Finset.smul_sum]

/-- Full block nonsingularity, without selecting coordinates or a Euclidean
norm: the induced block action has trivial kernel. -/
def Higham13CLMBlockNonsingular {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin m → Fin m → E →L[ℝ] E) : Prop :=
  Function.Injective (higham13_clmBlockAction A)

/-- Schur complement of the first continuous-linear block. -/
noncomputable def higham13_clmBlockSchur {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin (m + 1) → Fin (m + 1) → E →L[ℝ] E)
    (A11inv : E →L[ℝ] E) : Fin m → Fin m → E →L[ℝ] E :=
  fun i j => A i.succ j.succ - A i.succ 0 * A11inv * A 0 j.succ

/-- A nonzero kernel vector forces the attained lower norm to vanish. -/
theorem continuousLinearMapLowerNorm_eq_zero_of_exists_kernel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (T : E →L[ℝ] E) {x : E} (hx : x ≠ 0) (hTx : T x = 0) :
    continuousLinearMapLowerNorm T hunit = 0 := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let y : E := (‖x‖)⁻¹ • x
  have hy : ‖y‖ = 1 := by
    simp [y, norm_smul, hxnorm.ne']
  have hTy : T y = 0 := by
    simp [y, hTx]
  apply le_antisymm
  · simpa [hTy] using continuousLinearMapLowerNorm_le T hunit y hy
  · unfold continuousLinearMapLowerNorm
    exact norm_nonneg _

/-- Full block nonsingularity plus column BDD makes every diagonal block
injective, for any subordinate operator norm. -/
theorem higham13_clm_diag_injective_of_blockNonsingular_blockDiagDomCol
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (hA : Higham13CLMBlockNonsingular A)
    (hDom : IsBlockDiagDomCol m
      (fun i j => ‖A i j‖)
      (fun j => continuousLinearMapLowerNorm (A j j) hunit)) :
    ∀ j : Fin m, Function.Injective (A j j) := by
  intro j x y hxy
  apply sub_eq_zero.mp
  let z : E := x - y
  have hzker : A j j z = 0 := by
    dsimp [z]
    simpa using sub_eq_zero.mpr hxy
  by_contra hz
  have hlower : continuousLinearMapLowerNorm (A j j) hunit = 0 :=
    continuousLinearMapLowerNorm_eq_zero_of_exists_kernel
      hunit (A j j) hz hzker
  have hsum :
      ∑ i : Fin m, (if i = j then 0 else ‖A i j‖) ≤ 0 := by
    simpa [hlower] using hDom j
  have hoff : ∀ i : Fin m, i ≠ j → A i j = 0 := by
    intro i hij
    have hterm : ‖A i j‖ ≤
        ∑ q : Fin m, (if q = j then 0 else ‖A q j‖) := by
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun q : Fin m => if q = j then 0 else ‖A q j‖)
        (fun q _ => by positivity) (Finset.mem_univ i)
      simpa [hij] using hsingle
    have hnorm : ‖A i j‖ = 0 := by
      apply le_antisymm
      · exact le_trans hterm hsum
      · exact norm_nonneg _
    exact norm_eq_zero.mp hnorm
  let v : Fin m → E := fun q => if q = j then z else 0
  have hAv : higham13_clmBlockAction A v = 0 := by
    funext i
    by_cases hij : i = j
    · subst i
      unfold higham13_clmBlockAction
      rw [Finset.sum_eq_single j]
      · simpa [v] using hzker
      · intro q _hq hqj
        simp [v, hqj]
      · simp
    · have hijzero := hoff i hij
      unfold higham13_clmBlockAction
      rw [Finset.sum_eq_single j]
      · simp [v, hijzero]
      · intro q _hq hqj
        simp [v, hqj]
      · simp
  have hA0 : higham13_clmBlockAction A (0 : Fin m → E) = 0 := by
    funext i
    simp [higham13_clmBlockAction]
  have hvzero : v = 0 := hA (hAv.trans hA0.symm)
  have hzzero := congrFun hvzero j
  exact hz (by simpa [v] using hzzero)

/-- Full block nonsingularity plus row BDD makes every diagonal block
injective for any subordinate norm.  The proof uses finite-dimensional
surjectivity of the full block action: if a diagonal block had a nonzero
kernel, row BDD would annihilate its whole off-diagonal row, contradicting
surjectivity onto a vector outside that diagonal block's range. -/
theorem higham13_clm_diag_injective_of_blockNonsingular_blockDiagDomRow
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    [FiniteDimensional ℝ E]
    (hunit : ({x : E | ‖x‖ = 1} : Set E).Nonempty)
    (A : Fin m → Fin m → E →L[ℝ] E)
    (hA : Higham13CLMBlockNonsingular A)
    (hDom : IsBlockDiagDomRow m
      (fun i j => ‖A i j‖)
      (fun i => continuousLinearMapLowerNorm (A i i) hunit)) :
    ∀ i : Fin m, Function.Injective (A i i) := by
  intro i x y hxy
  apply sub_eq_zero.mp
  let z : E := x - y
  have hzker : A i i z = 0 := by
    dsimp [z]
    simpa using sub_eq_zero.mpr hxy
  by_contra hz
  have hlower : continuousLinearMapLowerNorm (A i i) hunit = 0 :=
    continuousLinearMapLowerNorm_eq_zero_of_exists_kernel
      hunit (A i i) hz hzker
  have hsum :
      ∑ j : Fin m, (if i = j then 0 else ‖A i j‖) ≤ 0 := by
    simpa [hlower] using hDom i
  have hoff : ∀ j : Fin m, j ≠ i → A i j = 0 := by
    intro j hji
    have hterm : ‖A i j‖ ≤
        ∑ q : Fin m, (if i = q then 0 else ‖A i q‖) := by
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset (Fin m)))
        (f := fun q : Fin m => if i = q then 0 else ‖A i q‖)
        (fun q _ => by positivity) (Finset.mem_univ j)
      simpa [hji.symm] using hsingle
    have hnorm : ‖A i j‖ = 0 := by
      apply le_antisymm
      · exact le_trans hterm hsum
      · exact norm_nonneg _
    exact norm_eq_zero.mp hnorm
  have hDiagNotInj : ¬ Function.Injective (A i i) := by
    intro hinj
    have : z = 0 := hinj (by simpa using hzker)
    exact hz this
  have hDiagNotSurj : ¬ Function.Surjective (A i i) := by
    intro hsurj
    exact hDiagNotInj (LinearMap.injective_iff_surjective.mpr hsurj)
  simp only [Function.Surjective] at hDiagNotSurj
  push_neg at hDiagNotSurj
  obtain ⟨target, htarget⟩ := hDiagNotSurj
  have hFullSurj : Function.Surjective (higham13_clmBlockAction A) := by
    have hLinearInj : Function.Injective (higham13_clmBlockActionLinear A) := hA
    have hLinearSurj : Function.Surjective (higham13_clmBlockActionLinear A) :=
      LinearMap.injective_iff_surjective.mp hLinearInj
    exact hLinearSurj
  let rhs : Fin m → E := fun q => if q = i then target else 0
  obtain ⟨preimage, hpreimage⟩ := hFullSurj rhs
  have hi := congrFun hpreimage i
  have hrow : higham13_clmBlockAction A preimage i = A i i (preimage i) := by
    unfold higham13_clmBlockAction
    apply Finset.sum_eq_single i
    · intro q _hq hqi
      simp [hoff q hqi]
    · simp
  have : A i i (preimage i) = target := by
    rw [← hrow, hi]
    simp [rhs]
  exact htarget (preimage i) this

/-- Canonical continuous-linear inverse selected from injectivity in finite
dimension. -/
noncomputable def higham13_clmInverseOfInjective
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : Function.Injective T) : E →L[ℝ] E :=
  let hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hT
  let hsurj : T.range = ⊤ := LinearMap.range_eq_top.mpr
    (LinearMap.injective_iff_surjective.mp hT)
  (ContinuousLinearEquiv.ofBijective T hker hsurj).symm.toContinuousLinearMap

theorem higham13_clmInverseOfInjective_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : Function.Injective T) (x : E) :
    higham13_clmInverseOfInjective T hT (T x) = x := by
  let hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hT
  let hsurj : T.range = ⊤ := LinearMap.range_eq_top.mpr
    (LinearMap.injective_iff_surjective.mp hT)
  exact ContinuousLinearEquiv.ofBijective_symm_apply_apply T hker hsurj x

theorem higham13_clmInverseOfInjective_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E]
    (T : E →L[ℝ] E) (hT : Function.Injective T) (x : E) :
    T (higham13_clmInverseOfInjective T hT x) = x := by
  let hker : T.ker = ⊥ := LinearMap.ker_eq_bot.mpr hT
  let hsurj : T.range = ⊤ := LinearMap.range_eq_top.mpr
    (LinearMap.injective_iff_surjective.mp hT)
  exact ContinuousLinearEquiv.ofBijective_apply_symm_apply T hker hsurj x

/-- A first Schur complement remains fully block nonsingular. -/
theorem higham13_clmBlockSchur_nonsingular
    {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Fin (m + 1) → Fin (m + 1) → E →L[ℝ] E)
    (P : E →L[ℝ] E)
    (hRight : ∀ x : E, A 0 0 (P x) = x)
    (hA : Higham13CLMBlockNonsingular A) :
    Higham13CLMBlockNonsingular (higham13_clmBlockSchur A P) := by
  intro x y hxy
  apply funext
  intro i
  let rhs : E := ∑ j : Fin m, A 0 j.succ (x j - y j)
  let z : Fin (m + 1) → E := Fin.cases (-P rhs) (fun j => x j - y j)
  have hAz : higham13_clmBlockAction A z = 0 := by
    funext q
    refine Fin.cases ?_ (fun i => ?_) q
    · simp [higham13_clmBlockAction, z, rhs, Fin.sum_univ_succ,
        map_sum, hRight]
    · have htail := congrFun hxy i
      simp only [higham13_clmBlockAction] at htail
      simp [higham13_clmBlockAction, z, rhs, higham13_clmBlockSchur,
        Fin.sum_univ_succ, map_sum] at htail ⊢
      have htailZero := sub_eq_zero.mpr htail
      abel_nf at htailZero ⊢
      exact htailZero
  have hA0 : higham13_clmBlockAction A (0 : Fin (m + 1) → E) = 0 := by
    funext i
    simp [higham13_clmBlockAction]
  have hzzero : z = 0 := hA (hAz.trans hA0.symm)
  have hzi := congrFun hzzero i.succ
  have hsub : x i - y i = 0 := by simpa [z] using hzi
  exact sub_eq_zero.mp hsub

end NumStability
