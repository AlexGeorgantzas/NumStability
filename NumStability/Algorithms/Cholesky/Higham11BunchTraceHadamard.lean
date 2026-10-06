import NumStability.Algorithms.Cholesky.Higham11BunchActualSharpGrowthClosure
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Algorithm 11.1: determinant/Hadamard facts derived from the exact trace

This module removes the last structural input from the sharp Bunch growth
adapter. A nonempty whole-block prefix of an exact Algorithm 11.1 trace is
realized as a principal submatrix of the active matrix at the beginning of
that prefix. Its determinant is exactly the product of the accepted pivot
block determinants. Since the complete search bounds every entry of that
selected submatrix by the first stage maximum, Hadamard's inequality gives
`Higham11WholeBlockHadamard` without a caller-supplied certificate.

The two-by-two step remains atomic: its selected source minor is decomposed
with `Matrix.det_fromBlocks₁₁`, using the literal inverse that occurs in
`higham11_1_bunchSchurTwo`. No scalar midpoint is introduced.

Finally, symmetry and nonsingularity construct an exact trace recursively:
the selected block determinant identities show that the Schur tail remains
nonsingular in either printed branch. Thus the source-level sharp growth
endpoint has no hidden trace-existence or structural-Hadamard premise.
-/

namespace NumStability

open Higham11BunchSharpBlockCertificate

private def onePivotBlock {n : ℕ} (A : Higham11BunchMatrix (n + 1)) :
    Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => A 0 0

private noncomputable def onePivotInv {n : ℕ} (A : Higham11BunchMatrix (n + 1)) :
    Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => (A 0 0)⁻¹

private def oneTopRight {n k : ℕ} (A : Higham11BunchMatrix (n + 1))
    (e : Fin k → Fin n) : Matrix (Fin 1) (Fin k) ℝ :=
  fun _ j => A 0 (e j).succ

private def oneBottomLeft {n k : ℕ} (A : Higham11BunchMatrix (n + 1))
    (e : Fin k → Fin n) : Matrix (Fin k) (Fin 1) ℝ :=
  fun i _ => A (e i).succ 0

private def oneTailMinor {n k : ℕ} (A : Higham11BunchMatrix (n + 1))
    (e : Fin k → Fin n) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => A (e i).succ (e j).succ

private def oneLiftSum {n k : ℕ} (e : Fin k → Fin n) :
    Fin 1 ⊕ Fin k → Fin (n + 1)
  | .inl _ => 0
  | .inr i => (e i).succ

private def oneLift {n k : ℕ} (e : Fin k → Fin n) :
    Fin (1 + k) → Fin (n + 1) :=
  oneLiftSum e ∘ finSumFinEquiv.symm

private theorem oneLiftSum_injective {n k : ℕ} {e : Fin k → Fin n}
    (he : Function.Injective e) : Function.Injective (oneLiftSum e) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subsingleton.elim i j)
      | inr j =>
          exfalso
          have := congrArg Fin.val hij
          simp [oneLiftSum] at this
  | inr i =>
      cases j with
      | inl j =>
          exfalso
          have := congrArg Fin.val hij
          simp [oneLiftSum] at this
      | inr j =>
          simp only [oneLiftSum, Fin.succ_inj] at hij
          exact congrArg Sum.inr (he hij)

private theorem oneLift_injective {n k : ℕ} {e : Fin k → Fin n}
    (he : Function.Injective e) : Function.Injective (oneLift e) :=
  (oneLiftSum_injective he).comp finSumFinEquiv.symm.injective

private theorem one_selected_block_eq {n k : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (e : Fin k → Fin n) :
    ((Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
      (oneLift e) (oneLift e)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (onePivotBlock A) (oneTopRight A e)
        (oneBottomLeft A e) (oneTailMinor A e) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [oneLift, oneLiftSum, onePivotBlock, oneTopRight,
      oneBottomLeft, oneTailMinor, Matrix.submatrix_apply]

private theorem onePivotBlock_det {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) :
    Matrix.det (onePivotBlock A) = A 0 0 := by
  simp [onePivotBlock]

private theorem one_schur_selected_eq {n k : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (e : Fin k → Fin n)
    (hA : IsSymmetricFiniteMatrix A)
    (h00 : A 0 0 ≠ 0) :
    let B := oneTopRight A e
    let C := oneBottomLeft A e
    let D := oneTailMinor A e
    D - C * onePivotInv A * B =
      (Matrix.of (higham11_1_bunchSchurOne A) : Matrix (Fin n) (Fin n) ℝ).submatrix e e := by
  classical
  dsimp only
  ext i j
  simp [oneTailMinor, oneBottomLeft, oneTopRight,
    onePivotInv, higham11_1_bunchSchurOne, Matrix.mul_apply, div_eq_mul_inv,
    hA 0 (e j).succ]
  ring

private theorem one_selected_det_step {n k : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (e : Fin k → Fin n)
    (hA : IsSymmetricFiniteMatrix A)
    (h00 : A 0 0 ≠ 0) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
          (oneLift e) (oneLift e)) =
      A 0 0 * Matrix.det
        ((Matrix.of (higham11_1_bunchSchurOne A) : Matrix (Fin n) (Fin n) ℝ).submatrix e e) := by
  classical
  let P := onePivotBlock A
  let B := oneTopRight A e
  let C := oneBottomLeft A e
  let D := oneTailMinor A e
  have hPdet : Matrix.det P ≠ 0 := by
    simpa [P, onePivotBlock_det] using h00
  letI : Invertible P :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hPdet)
  have hPinv : ⅟P = onePivotInv A := by
    apply invOf_eq_left_inv
    ext i j
    fin_cases i
    fin_cases j
    simp [P, onePivotBlock, onePivotInv, Matrix.mul_apply, h00]
  calc
    _ = Matrix.det (Matrix.fromBlocks P B C D) := by
      rw [← one_selected_block_eq A e, Matrix.det_submatrix_equiv_self]
    _ = Matrix.det P * Matrix.det (D - C * ⅟P * B) :=
      Matrix.det_fromBlocks₁₁ P B C D
    _ = _ := by
      rw [hPinv, one_schur_selected_eq A e hA h00]
      rw [show Matrix.det P = A 0 0 by simp [P, onePivotBlock]]

private def twoHead {n : ℕ} (i : Fin 2) : Fin (n + 2) :=
  Fin.castLE (by omega) i

private def twoPivotBlock {n : ℕ} (A : Higham11BunchMatrix (n + 2)) :
    Matrix (Fin 2) (Fin 2) ℝ := fun i j => A (twoHead i) (twoHead j)

private def twoTopRight {n k : ℕ} (A : Higham11BunchMatrix (n + 2))
    (e : Fin k → Fin n) : Matrix (Fin 2) (Fin k) ℝ :=
  fun i j => A (twoHead i) (e j).succ.succ

private def twoBottomLeft {n k : ℕ} (A : Higham11BunchMatrix (n + 2))
    (e : Fin k → Fin n) : Matrix (Fin k) (Fin 2) ℝ :=
  fun i j => A (e i).succ.succ (twoHead j)

private def twoTailMinor {n k : ℕ} (A : Higham11BunchMatrix (n + 2))
    (e : Fin k → Fin n) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j => A (e i).succ.succ (e j).succ.succ

private def twoLiftSum {n k : ℕ} (e : Fin k → Fin n) :
    Fin 2 ⊕ Fin k → Fin (n + 2)
  | .inl i => twoHead i
  | .inr i => (e i).succ.succ

private def twoLift {n k : ℕ} (e : Fin k → Fin n) :
    Fin (2 + k) → Fin (n + 2) :=
  twoLiftSum e ∘ finSumFinEquiv.symm

private theorem twoLiftSum_injective {n k : ℕ} {e : Fin k → Fin n}
    (he : Function.Injective e) : Function.Injective (twoLiftSum e) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          change twoHead i = twoHead j at hij
          exact congrArg Sum.inl (Fin.castLE_injective (by omega) hij)
      | inr j =>
          exfalso
          have hval := congrArg Fin.val hij
          simp [twoLiftSum, twoHead] at hval
          omega
  | inr i =>
      cases j with
      | inl j =>
          exfalso
          have hval := congrArg Fin.val hij
          simp [twoLiftSum, twoHead] at hval
          omega
      | inr j =>
          simp only [twoLiftSum, Fin.succ_inj] at hij
          exact congrArg Sum.inr (he hij)

private theorem twoLift_injective {n k : ℕ} {e : Fin k → Fin n}
    (he : Function.Injective e) : Function.Injective (twoLift e) :=
  (twoLiftSum_injective he).comp finSumFinEquiv.symm.injective

private theorem two_selected_block_eq {n k : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (e : Fin k → Fin n) :
    ((Matrix.of A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ).submatrix
      (twoLift e) (twoLift e)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (twoPivotBlock A) (twoTopRight A e)
        (twoBottomLeft A e) (twoTailMinor A e) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [twoLift, twoLiftSum, twoPivotBlock, twoTopRight,
      twoBottomLeft, twoTailMinor, Matrix.submatrix_apply]

private noncomputable def twoPivotInv {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) : Matrix (Fin 2) (Fin 2) ℝ :=
  let d := A 0 0 * A 1 1 - A 1 0 ^ 2
  !![A 1 1 / d, -(A 1 0 / d);
     -(A 1 0 / d), A 0 0 / d]

private theorem twoHead_zero {n : ℕ} : twoHead (n := n) 0 = 0 := by
  rfl

private theorem twoHead_one {n : ℕ} : twoHead (n := n) 1 = 1 := by
  rfl

private theorem twoPivotBlock_det {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A) :
    Matrix.det (twoPivotBlock A) = A 0 0 * A 1 1 - A 1 0 ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [twoPivotBlock, twoHead_zero, twoHead_one, hA 0 1]
  ring

private theorem twoPivotBlock_mul_inv {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (hdet : A 0 0 * A 1 1 - A 1 0 ^ 2 ≠ 0) :
    twoPivotInv A * twoPivotBlock A = 1 := by
  have hdet' : A 1 1 * A 0 0 - A 1 0 ^ 2 ≠ 0 := by
    simpa [mul_comm] using hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoPivotInv, twoPivotBlock, twoHead_zero, twoHead_one,
      Matrix.mul_apply, Fin.sum_univ_two, hA 0 1] <;>
    field_simp [hdet, hdet'] <;> ring

private theorem two_schur_selected_eq {n k : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (e : Fin k → Fin n)
    (hA : IsSymmetricFiniteMatrix A) :
    let B := twoTopRight A e
    let C := twoBottomLeft A e
    let D := twoTailMinor A e
    D - C * twoPivotInv A * B =
      (Matrix.of (higham11_1_bunchSchurTwo A) : Matrix (Fin n) (Fin n) ℝ).submatrix e e := by
  classical
  dsimp only
  ext i j
  simp [twoTailMinor, twoBottomLeft, twoTopRight, twoPivotInv,
    twoHead_zero, twoHead_one, higham11_1_bunchSchurTwo,
    Matrix.mul_apply, Fin.sum_univ_two,
    hA 0 (e j).succ.succ, hA 1 (e j).succ.succ]

private theorem two_selected_det_step {n k : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (e : Fin k → Fin n)
    (hA : IsSymmetricFiniteMatrix A)
    (hdet : A 0 0 * A 1 1 - A 1 0 ^ 2 ≠ 0) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ).submatrix
          (twoLift e) (twoLift e)) =
      (A 0 0 * A 1 1 - A 1 0 ^ 2) * Matrix.det
        ((Matrix.of (higham11_1_bunchSchurTwo A) : Matrix (Fin n) (Fin n) ℝ).submatrix e e) := by
  classical
  let P := twoPivotBlock A
  let B := twoTopRight A e
  let C := twoBottomLeft A e
  let D := twoTailMinor A e
  have hPdet : Matrix.det P ≠ 0 := by
    simpa [P, twoPivotBlock_det A hA] using hdet
  letI : Invertible P :=
    Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hPdet)
  have hPinv : ⅟P = twoPivotInv A := by
    apply invOf_eq_left_inv
    exact twoPivotBlock_mul_inv A hA hdet
  calc
    _ = Matrix.det (Matrix.fromBlocks P B C D) := by
      rw [← two_selected_block_eq A e, Matrix.det_submatrix_equiv_self]
    _ = Matrix.det P * Matrix.det (D - C * ⅟P * B) :=
      Matrix.det_fromBlocks₁₁ P B C D
    _ = _ := by
      rw [hPinv, two_schur_selected_eq A e hA]
      rw [show Matrix.det P = A 0 0 * A 1 1 - A 1 0 ^ 2 by
        simpa [P] using twoPivotBlock_det A hA]

theorem abs_det_principal_submatrix_le_hadamard {n k : ℕ}
    (hk : 0 < k) (A : Higham11BunchMatrix n) (e : Fin k → Fin n)
    {M : ℝ} (hentry : ∀ i j, |A i j| ≤ M) :
    |Matrix.det
        ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix e e)| ≤
      Real.sqrt ((k : ℝ) ^ k) * M ^ k := by
  let B : Matrix (Fin k) (Fin k) ℝ :=
    (Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix e e
  have hM : 0 ≤ M :=
    le_trans (abs_nonneg (A (e ⟨0, hk⟩) (e ⟨0, hk⟩)))
      (hentry (e ⟨0, hk⟩) (e ⟨0, hk⟩))
  have hmax : maxEntryNorm hk B ≤ M := by
    refine maxEntryNorm_le_of_entry_le_bound hk B M ?_
    intro i j
    simpa [B, Matrix.submatrix_apply, Matrix.of_apply] using hentry (e i) (e j)
  have hhad := higham9_hadamard_det_sq_le_pow_maxEntryNorm hk B
  have hpow : (maxEntryNorm hk B) ^ (2 * k) ≤ M ^ (2 * k) :=
    pow_le_pow_left₀ (maxEntryNorm_nonneg hk B) hmax (2 * k)
  have hstep : (B.det) ^ 2 ≤ (k : ℝ) ^ k * M ^ (2 * k) :=
    hhad.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have habs : |B.det| ≤ Real.sqrt ((k : ℝ) ^ k * M ^ (2 * k)) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt hstep
  have hrhs : Real.sqrt ((k : ℝ) ^ k * M ^ (2 * k)) =
      Real.sqrt ((k : ℝ) ^ k) * M ^ k := by
    rw [Real.sqrt_mul (by positivity), show 2 * k = k * 2 from by ring,
      pow_mul, Real.sqrt_sq (pow_nonneg hM k)]
  simpa [B, hrhs] using habs

private def oneSourceLift {n k : ℕ} (r : Fin (n + 1))
    (e : Fin k → Fin n) : Fin (1 + k) → Fin (n + 1) :=
  higham11_1_bunchOnePerm r ∘ oneLift e

private theorem oneSourceLift_injective {n k : ℕ} (r : Fin (n + 1))
    {e : Fin k → Fin n} (he : Function.Injective e) :
    Function.Injective (oneSourceLift r e) :=
  (higham11_1_bunchOnePerm r).injective.comp (oneLift_injective he)

private theorem one_source_selected_det_step {n k : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (r : Fin (n + 1)) (e : Fin k → Fin n) (hrr : A r r ≠ 0) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ).submatrix
          (oneSourceLift r e) (oneSourceLift r e)) =
      A r r * Matrix.det
        ((Matrix.of (higham11_1_bunchSchurOne
          (higham11_1_bunchOneActive A r)) : Matrix (Fin n) (Fin n) ℝ).submatrix e e) := by
  let A' := higham11_1_bunchOneActive A r
  have hA' : IsSymmetricFiniteMatrix A' :=
    higham11_1_bunchSymmetricPermute_symmetric A _ hA
  have h00 : A' 0 0 ≠ 0 := by
    simpa [A', higham11_1_bunchOneActive,
      higham11_1_bunchSymmetricPermute] using hrr
  have hstep := one_selected_det_step A' e hA' h00
  simpa [A', oneSourceLift, higham11_1_bunchOneActive,
    higham11_1_bunchSymmetricPermute, Function.comp_def] using hstep

private def twoSourceLift {n k : ℕ} (p q : Fin (n + 2))
    (e : Fin k → Fin n) : Fin (2 + k) → Fin (n + 2) :=
  higham11_1_bunchTwoPerm p q ∘ twoLift e

private theorem twoSourceLift_injective {n k : ℕ} (p q : Fin (n + 2))
    {e : Fin k → Fin n} (he : Function.Injective e) :
    Function.Injective (twoSourceLift p q e) :=
  (higham11_1_bunchTwoPerm p q).injective.comp (twoLift_injective he)

private theorem two_source_selected_det_step {n k : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (p q : Fin (n + 2)) (hpq : p ≠ q) (e : Fin k → Fin n)
    (hdet : A p p * A q q - A p q ^ 2 ≠ 0) :
    Matrix.det
        ((Matrix.of A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ).submatrix
          (twoSourceLift p q e) (twoSourceLift p q e)) =
      (A p p * A q q - A p q ^ 2) * Matrix.det
        ((Matrix.of (higham11_1_bunchSchurTwo
          (higham11_1_bunchTwoActive A p q)) : Matrix (Fin n) (Fin n) ℝ).submatrix e e) := by
  let A' := higham11_1_bunchTwoActive A p q
  have hA' : IsSymmetricFiniteMatrix A' :=
    higham11_1_bunchSymmetricPermute_symmetric A _ hA
  have h00 : A' 0 0 = A p p := by
    simp [A', higham11_1_bunchTwoActive,
      higham11_1_bunchSymmetricPermute,
      higham11_1_bunchTwoPerm_zero p q hpq]
  have h11 : A' 1 1 = A q q := by
    simp [A', higham11_1_bunchTwoActive,
      higham11_1_bunchSymmetricPermute]
  have h10 : A' 1 0 = A p q := by
    rw [hA' 1 0]
    simp [A', higham11_1_bunchTwoActive,
      higham11_1_bunchSymmetricPermute,
      higham11_1_bunchTwoPerm_zero p q hpq]
  have hdet' : A' 0 0 * A' 1 1 - A' 1 0 ^ 2 ≠ 0 := by
    simpa [h00, h11, h10] using hdet
  have hstep := two_selected_det_step A' e hA' hdet'
  rw [h00, h11, h10] at hstep
  simpa [A', twoSourceLift, higham11_1_bunchTwoActive,
    higham11_1_bunchSymmetricPermute, Function.comp_def] using hstep

theorem bunchSharpGrowthBound_le_of_le {k n : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    higham11_1_bunchSharpGrowthBound k ≤
      higham11_1_bunchSharpGrowthBound n := by
  have hsub : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hkn 1
  have hcast : ((k - 1 : ℕ) : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsub
  have hrpow :
      Real.rpow ((k - 1 : ℕ) : ℝ) ((223 : ℝ) / 500) ≤
        Real.rpow ((n - 1 : ℕ) : ℝ) ((223 : ℝ) / 500) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hcast (by norm_num)
  have hmult : higham11_1_bunchSharpGrowthMultiplier k ≤
      higham11_1_bunchSharpGrowthMultiplier n := by
    unfold higham11_1_bunchSharpGrowthMultiplier
    exact mul_le_mul_of_nonneg_left hrpow (by norm_num)
  have hW := higham9_14_completePivotWilkinsonBound_le_of_le hkn
  unfold higham11_1_bunchSharpGrowthBound
  exact mul_le_mul hmult hW
    (higham9_14_completePivotWilkinsonBound_nonneg k)
    (higham11_1_bunchSharpGrowthMultiplier_nonneg n)

theorem one_le_bunchSharpGrowthBound {n : ℕ} (hn : 2 ≤ n) :
    (1 : ℝ) ≤ higham11_1_bunchSharpGrowthBound n := by
  have hmono := bunchSharpGrowthBound_le_of_le (k := 2) (n := n) (by omega) hn
  have htwo : (1 : ℝ) ≤ higham11_1_bunchSharpGrowthBound 2 := by
    rw [higham11_1_bunchSharpGrowthBound_eq_multiplier_mul_higham9_14]
    rw [higham9_14_completePivotWilkinsonBound_two]
    norm_num
  exact htwo.trans hmono

structure PrefixPrincipalMinor {n : ℕ} (A : Higham11BunchMatrix n)
    (blocks : List Higham11BunchSharpBlock) where
  e : Fin (totalWidth blocks) → Fin n
  injective : Function.Injective e
  detProduct_eq : detProduct blocks =
    |Matrix.det ((Matrix.of A : Matrix (Fin n) (Fin n) ℝ).submatrix e e)|

private noncomputable def emptyPrefixPrincipalMinor {n : ℕ}
    (A : Higham11BunchMatrix n) : PrefixPrincipalMinor A [] where
  e := Fin.elim0
  injective := fun i => Fin.elim0 i
  detProduct_eq := by simp [detProduct, totalWidth]

open Higham11ExactBunchTrace

noncomputable def prefixPrincipalMinor_of_isPrefix :
    {n : ℕ} → {A : Higham11BunchMatrix n} →
      (trace : Higham11ExactBunchTrace A) →
      {blocks : List Higham11BunchSharpBlock} →
      blocks <+: trace.toSharpBlocks → PrefixPrincipalMinor A blocks
  | _, _, .nil A, blocks, hprefix => by
      have hnil : blocks = [] := by
        simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix
      subst blocks
      exact emptyPrefixPrincipalMinor A
  | _, _, .one A hA p q r hentry hdiag hmaxPos hchoice tail,
      blocks, hprefix => by
      cases blocks with
      | nil => exact emptyPrefixPrincipalMinor A
      | cons b rest =>
          have hcons : b :: rest <+:
              oneSharpBlock A p q r hmaxPos hchoice :: tail.toSharpBlocks := by
            simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix
          obtain ⟨rfl, hrest⟩ := List.cons_prefix_cons.mp hcons
          let tailMinor := prefixPrincipalMinor_of_isPrefix tail hrest
          have hrr : A r r ≠ 0 := by
            exact abs_pos.mp (oneSharpBlock A p q r hmaxPos hchoice).detAbs_pos
          let E : Fin (totalWidth
              (oneSharpBlock A p q r hmaxPos hchoice :: rest)) → Fin (Nat.succ _) :=
            oneSourceLift r tailMinor.e
          have hEinj : Function.Injective E := by
            exact oneSourceLift_injective r tailMinor.injective
          have hstep := one_source_selected_det_step A hA r tailMinor.e hrr
          refine { e := E, injective := hEinj, detProduct_eq := ?_ }
          dsimp [E]
          rw [detProduct, List.map_cons, List.prod_cons]
          change |A r r| * detProduct rest = _
          rw [tailMinor.detProduct_eq, ← abs_mul, ← hstep]
          rfl
  | _, _, .two A hA p q r hentry hdiag hmaxPos hchoice tail,
      blocks, hprefix => by
      cases blocks with
      | nil => exact emptyPrefixPrincipalMinor A
      | cons b rest =>
          have hcons : b :: rest <+:
              twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice ::
                tail.toSharpBlocks := by
            simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix
          obtain ⟨rfl, hrest⟩ := List.cons_prefix_cons.mp hcons
          let tailMinor := prefixPrincipalMinor_of_isPrefix tail hrest
          have hpq := two_indices_ne A hA p q r hentry hdiag hmaxPos hchoice
          have hdet : A p p * A q q - A p q ^ 2 ≠ 0 := by
            exact abs_pos.mp
              (twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice).detAbs_pos
          let E : Fin (totalWidth
              (twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice :: rest)) →
                Fin (_ + 2) :=
            twoSourceLift p q tailMinor.e
          have hEinj : Function.Injective E := by
            exact twoSourceLift_injective p q tailMinor.injective
          have hstep := two_source_selected_det_step A hA p q hpq tailMinor.e hdet
          refine { e := E, injective := hEinj, detProduct_eq := ?_ }
          dsimp [E]
          rw [detProduct, List.map_cons, List.prod_cons]
          change |A p p * A q q - A p q ^ 2| * detProduct rest = _
          rw [tailMinor.detProduct_eq, ← abs_mul, ← hstep]
          rfl

theorem wholeBlockHadamard_of_isPrefix :
    {n : ℕ} → {A : Higham11BunchMatrix n} →
      (trace : Higham11ExactBunchTrace A) →
      {blocks : List Higham11BunchSharpBlock} →
      blocks ≠ [] → blocks <+: trace.toSharpBlocks →
      Higham11WholeBlockHadamard blocks
  | _, _, .nil A, blocks, hnonempty, hprefix => by
      have hnil : blocks = [] := by
        simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix
      exact False.elim (hnonempty hnil)
  | _, _, .one A hA p q r hentry hdiag hmaxPos hchoice tail,
      blocks, hnonempty, hprefix => by
      cases blocks with
      | nil => exact False.elim (hnonempty rfl)
      | cons b rest =>
          have hcons : b :: rest <+:
              oneSharpBlock A p q r hmaxPos hchoice :: tail.toSharpBlocks := by
            simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix
          obtain ⟨rfl, hrest⟩ := List.cons_prefix_cons.mp hcons
          let minor := prefixPrincipalMinor_of_isPrefix
            (.one A hA p q r hentry hdiag hmaxPos hchoice tail) hprefix
          have hd : 0 < totalWidth
              (oneSharpBlock A p q r hmaxPos hchoice :: rest) := by
            simp only [totalWidth, List.map_cons, List.sum_cons]
            exact Nat.add_pos_left
              (oneSharpBlock A p q r hmaxPos hchoice).width_pos _
          have hhad := abs_det_principal_submatrix_le_hadamard
            hd A minor.e hentry
          rw [← minor.detProduct_eq] at hhad
          simpa [Higham11WholeBlockHadamard, firstMax] using hhad
  | _, _, .two A hA p q r hentry hdiag hmaxPos hchoice tail,
      blocks, hnonempty, hprefix => by
      cases blocks with
      | nil => exact False.elim (hnonempty rfl)
      | cons b rest =>
          have hcons : b :: rest <+:
              twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice ::
                tail.toSharpBlocks := by
            simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix
          obtain ⟨rfl, hrest⟩ := List.cons_prefix_cons.mp hcons
          let minor := prefixPrincipalMinor_of_isPrefix
            (.two A hA p q r hentry hdiag hmaxPos hchoice tail) hprefix
          have hd : 0 < totalWidth
              (twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice :: rest) := by
            simp only [totalWidth, List.map_cons, List.sum_cons]
            exact Nat.add_pos_left
              (twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice).width_pos _
          have hhad := abs_det_principal_submatrix_le_hadamard
            hd A minor.e hentry
          rw [← minor.detProduct_eq] at hhad
          simpa [Higham11WholeBlockHadamard, firstMax] using hhad

theorem wholeBlockHadamard_of_isInfix :
    {n : ℕ} → {A : Higham11BunchMatrix n} →
      (trace : Higham11ExactBunchTrace A) →
      {blocks : List Higham11BunchSharpBlock} →
      blocks ≠ [] → blocks <:+: trace.toSharpBlocks →
      Higham11WholeBlockHadamard blocks
  | _, _, .nil A, blocks, hnonempty, hinfix => by
      have hnil : blocks = [] := by
        simpa [Higham11ExactBunchTrace.toSharpBlocks] using hinfix
      exact False.elim (hnonempty hnil)
  | _, _, .one A hA p q r hentry hdiag hmaxPos hchoice tail,
      blocks, hnonempty, hinfix => by
      have hsplit : blocks <+:
            oneSharpBlock A p q r hmaxPos hchoice :: tail.toSharpBlocks ∨
          blocks <:+: tail.toSharpBlocks := by
        rw [← List.infix_cons_iff]
        simpa [Higham11ExactBunchTrace.toSharpBlocks] using hinfix
      rcases hsplit with hprefix | htail
      · exact wholeBlockHadamard_of_isPrefix
          (.one A hA p q r hentry hdiag hmaxPos hchoice tail) hnonempty (by
          simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix)
      · exact wholeBlockHadamard_of_isInfix tail hnonempty htail
  | _, _, .two A hA p q r hentry hdiag hmaxPos hchoice tail,
      blocks, hnonempty, hinfix => by
      have hsplit : blocks <+:
            twoSharpBlock A hA p q r hentry hdiag hmaxPos hchoice ::
              tail.toSharpBlocks ∨ blocks <:+: tail.toSharpBlocks := by
        rw [← List.infix_cons_iff]
        simpa [Higham11ExactBunchTrace.toSharpBlocks] using hinfix
      rcases hsplit with hprefix | htail
      · exact wholeBlockHadamard_of_isPrefix
          (.two A hA p q r hentry hdiag hmaxPos hchoice tail) hnonempty (by
          simpa [Higham11ExactBunchTrace.toSharpBlocks] using hprefix)
      · exact wholeBlockHadamard_of_isInfix tail hnonempty htail

noncomputable def certifiedExecutionOfTrace {n : ℕ}
    {A : Higham11BunchMatrix n} (trace : Higham11ExactBunchTrace A) :
    Higham11BunchCertifiedExecution A where
  trace := trace
  wholeBlockSegmentHadamard := fun segment hnonempty hinfix =>
    wholeBlockHadamard_of_isInfix trace hnonempty hinfix

private theorem det_submatrix_self_of_injective {m n : ℕ}
    (hmn : m = n) (A : Matrix (Fin n) (Fin n) ℝ) (e : Fin m → Fin n)
    (he : Function.Injective e) :
    Matrix.det (A.submatrix e e) = Matrix.det A := by
  let E : Fin m ≃ Fin n := Equiv.ofBijective e
    ((Fintype.bijective_iff_injective_and_card e).2 ⟨he, by simp [hmn]⟩)
  change Matrix.det (A.submatrix E E) = Matrix.det A
  exact Matrix.det_submatrix_equiv_self E A

private theorem one_source_full_det_step {n : ℕ}
    (A : Higham11BunchMatrix (n + 1)) (hA : IsSymmetricFiniteMatrix A)
    (r : Fin (n + 1)) (hrr : A r r ≠ 0) :
    Matrix.det (Matrix.of A) = A r r * Matrix.det
      (Matrix.of (higham11_1_bunchSchurOne
        (higham11_1_bunchOneActive A r))) := by
  have hstep := one_source_selected_det_step A hA r (fun i : Fin n => i) hrr
  have hleft := det_submatrix_self_of_injective
    (by omega) (Matrix.of A) (oneSourceLift r (fun i : Fin n => i))
    (oneSourceLift_injective r Function.injective_id)
  rw [hleft] at hstep
  simpa using hstep

private theorem two_source_full_det_step {n : ℕ}
    (A : Higham11BunchMatrix (n + 2)) (hA : IsSymmetricFiniteMatrix A)
    (p q : Fin (n + 2)) (hpq : p ≠ q)
    (hdet : A p p * A q q - A p q ^ 2 ≠ 0) :
    Matrix.det (Matrix.of A) =
      (A p p * A q q - A p q ^ 2) * Matrix.det
        (Matrix.of (higham11_1_bunchSchurTwo
          (higham11_1_bunchTwoActive A p q))) := by
  have hstep := two_source_selected_det_step A hA p q hpq
    (fun i : Fin n => i) hdet
  have hleft := det_submatrix_self_of_injective
    (by omega) (Matrix.of A) (twoSourceLift p q (fun i : Fin n => i))
    (twoSourceLift_injective p q Function.injective_id)
  rw [hleft] at hstep
  simpa using hstep

private theorem exists_diagonal_max {n : ℕ} (hn : 0 < n)
    (A : Higham11BunchMatrix n) :
    ∃ r : Fin n, ∀ i : Fin n, |A i i| ≤ |A r r| := by
  classical
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  obtain ⟨r, _hrmem, hrmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin n))
      (fun i : Fin n => |A i i|) huniv
  exact ⟨r, fun i => hrmax i (Finset.mem_univ i)⟩

theorem higham11_1_exists_exactBunchTrace_of_symmetric_det_ne_zero
    {n : ℕ} (A : Higham11BunchMatrix n)
    (hA : IsSymmetricFiniteMatrix A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    Nonempty (Higham11ExactBunchTrace A) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          exact ⟨Higham11ExactBunchTrace.nil A⟩
      | succ m =>
          cases m with
          | zero =>
              have h00 : A 0 0 ≠ 0 := by
                intro hz
                apply hdet
                simpa [Matrix.det_fin_one, hz]
              have hmaxPos : 0 < |A 0 0| := abs_pos.mpr h00
              have hentry : ∀ i j : Fin 1, |A i j| ≤ |A 0 0| := by
                intro i j
                simpa [Subsingleton.elim i 0, Subsingleton.elim j 0]
              have hdiag : ∀ i : Fin 1, |A i i| ≤ |A 0 0| := by
                intro i
                simpa [Subsingleton.elim i 0]
              have hchoice : higham11_1_BunchParlettCompletePivotChoice
                  higham11_1_bunchParlettAlpha |A 0 0| |A 0 0|
                    PivotSize.one := by
                simp only [higham11_1_BunchParlettCompletePivotChoice,
                  BunchParlettCompletePivotChoice]
                have ha : higham11_1_bunchParlettAlpha < 1 := by
                  simpa [higham11_1_bunchParlettAlpha] using
                    bunch_parlett_alpha_lt_one
                nlinarith [abs_nonneg (A 0 0)]
              exact ⟨Higham11ExactBunchTrace.one A hA 0 0 0
                hentry hdiag hmaxPos hchoice (.nil _)⟩
          | succ k =>
              obtain ⟨p, q, hpqMax, hpq0⟩ :=
                higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero
                  A hdet
              have hentry : ∀ i j : Fin (k + 2), |A i j| ≤ |A p q| := by
                intro i j
                exact hpqMax.2.2 i j (Nat.zero_le i.val) (Nat.zero_le j.val)
              obtain ⟨r, hdiag⟩ := exists_diagonal_max (by omega) A
              have hmaxPos : 0 < |A p q| := abs_pos.mpr hpq0
              by_cases hbranch :
                  higham11_1_bunchParlettAlpha * |A p q| ≤ |A r r|
              · have hchoice : higham11_1_BunchParlettCompletePivotChoice
                    higham11_1_bunchParlettAlpha |A p q| |A r r|
                      PivotSize.one := hbranch
                have ha : 0 < higham11_1_bunchParlettAlpha := by
                  simpa [higham11_1_bunchParlettAlpha] using
                    bunch_parlett_alpha_pos
                have hrr : A r r ≠ 0 := by
                  apply abs_ne_zero.mp
                  nlinarith
                let A₁ := higham11_1_bunchSchurOne
                  (higham11_1_bunchOneActive A r)
                have hAactive : IsSymmetricFiniteMatrix
                    (higham11_1_bunchOneActive A r) :=
                  higham11_1_bunchSymmetricPermute_symmetric A _ hA
                have hA₁ : IsSymmetricFiniteMatrix A₁ :=
                  higham11_1_bunchSchurOne_symmetric _ hAactive
                have hfactor := one_source_full_det_step A hA r hrr
                have hdet₁ : Matrix.det
                    (Matrix.of A₁ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
                  intro hz
                  apply hdet
                  rw [hfactor]
                  simpa [A₁, hz]
                obtain ⟨tail⟩ := ih (k + 1) (by omega) A₁ hA₁ hdet₁
                exact ⟨.one A hA p q r hentry hdiag hmaxPos hchoice tail⟩
              · have hchoice : higham11_1_BunchParlettCompletePivotChoice
                    higham11_1_bunchParlettAlpha |A p q| |A r r|
                      PivotSize.two := by
                  simpa [higham11_1_BunchParlettCompletePivotChoice,
                    BunchParlettCompletePivotChoice] using lt_of_not_ge hbranch
                have hpq : p ≠ q :=
                  Higham11ExactBunchTrace.two_indices_ne A hA p q r
                    hentry hdiag hmaxPos hchoice
                have hpivotPos := Higham11ExactBunchTrace.two_pivot_pos
                  A hA p q r hentry hdiag hmaxPos hchoice
                have hpivot : A p p * A q q - A p q ^ 2 ≠ 0 :=
                  abs_ne_zero.mp (ne_of_gt hpivotPos)
                let A₂ := higham11_1_bunchSchurTwo
                  (higham11_1_bunchTwoActive A p q)
                have hAactive : IsSymmetricFiniteMatrix
                    (higham11_1_bunchTwoActive A p q) :=
                  higham11_1_bunchSymmetricPermute_symmetric A _ hA
                have hA₂ : IsSymmetricFiniteMatrix A₂ :=
                  higham11_1_bunchSchurTwo_symmetric _ hAactive
                have hfactor := two_source_full_det_step A hA p q hpq hpivot
                have hdet₂ : Matrix.det
                    (Matrix.of A₂ : Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
                  intro hz
                  apply hdet
                  rw [hfactor]
                  simpa [A₂, hz]
                obtain ⟨tail⟩ := ih k (by omega) A₂ hA₂ hdet₂
                exact ⟨.two A hA p q r hentry hdiag hmaxPos hchoice tail⟩

/-- Every active-matrix maximum in an exact Algorithm 11.1 trace satisfies
the sharp Bunch bound against the original matrix maximum. No structural
Hadamard hypothesis remains: it is constructed from the trace above. -/
theorem higham11_1_exactBunchTrace_all_stageMax_le_maxEntryNorm
    {n : ℕ} {A : Higham11BunchMatrix n}
    (trace : Higham11ExactBunchTrace A) (hn : 2 ≤ n) :
    ∀ mu ∈ trace.stageMaxes,
      mu ≤ higham11_1_bunchSharpGrowthBound n *
        maxEntryNorm (by omega : 0 < n)
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← Higham11ExactBunchTrace.firstMax_toSharpBlocks_eq_maxEntryNorm
    trace (by omega)]
  exact Higham11BunchCertifiedExecution.all_stageMax_le_original_bound_of_structural_hadamard
    (certifiedExecutionOfTrace trace) hn

/-- Ratio form matching Higham's element-growth definition, now derived
directly from an exact trace with no caller-supplied Hadamard certificate. -/
theorem higham11_1_exactBunchTrace_all_stageRatio_le_maxEntryNorm
    {n : ℕ} {A : Higham11BunchMatrix n}
    (trace : Higham11ExactBunchTrace A) (hn : 2 ≤ n) :
    ∀ mu ∈ trace.stageMaxes,
      mu / maxEntryNorm (by omega : 0 < n)
          (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
        higham11_1_bunchSharpGrowthBound n := by
  exact Higham11BunchCertifiedExecution.all_stageRatio_le_maxEntryNorm_of_structural_hadamard
      (certifiedExecutionOfTrace trace) hn

/-- Source-domain maximum-form endpoint. Every real symmetric nonsingular
matrix of order at least two admits an exact Algorithm 11.1 execution whose
original and reduced active maxima satisfy the sharp displayed bound. -/
theorem higham11_1_exists_exactBunchTrace_all_stageMax_le_maxEntryNorm
    {n : ℕ} (hn : 2 ≤ n) (A : Higham11BunchMatrix n)
    (hA : IsSymmetricFiniteMatrix A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ trace : Higham11ExactBunchTrace A,
      ∀ mu ∈ trace.stageMaxes,
        mu ≤ higham11_1_bunchSharpGrowthBound n *
          maxEntryNorm (by omega : 0 < n)
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨trace⟩ :=
    higham11_1_exists_exactBunchTrace_of_symmetric_det_ne_zero A hA hdet
  exact ⟨trace,
    higham11_1_exactBunchTrace_all_stageMax_le_maxEntryNorm trace hn⟩

/-- Source-domain ratio endpoint matching Higham's growth-factor
normalization. Trace existence and the determinant/Hadamard invariant are
both discharged internally. -/
theorem higham11_1_exists_exactBunchTrace_all_stageRatio_le_maxEntryNorm
    {n : ℕ} (hn : 2 ≤ n) (A : Higham11BunchMatrix n)
    (hA : IsSymmetricFiniteMatrix A)
    (hdet : Matrix.det (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≠ 0) :
    ∃ trace : Higham11ExactBunchTrace A,
      ∀ mu ∈ trace.stageMaxes,
        mu / maxEntryNorm (by omega : 0 < n)
            (Matrix.of A : Matrix (Fin n) (Fin n) ℝ) ≤
          higham11_1_bunchSharpGrowthBound n := by
  obtain ⟨trace⟩ :=
    higham11_1_exists_exactBunchTrace_of_symmetric_det_ne_zero A hA hdet
  exact ⟨trace,
    higham11_1_exactBunchTrace_all_stageRatio_le_maxEntryNorm trace hn⟩

end NumStability
