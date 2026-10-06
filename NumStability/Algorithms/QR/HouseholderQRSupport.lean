-- Algorithms/QR/HouseholderQRSupport.lean
--
-- Compatibility/support layer for rectangular and stored Householder QR helper theorems.
-- Extracted from the main-branch Chapter 18 helper layer so downstream least-squares proofs can reuse it alongside the implementation-backed QR API.

import NumStability.Algorithms.QR.HouseholderApplySupport
import NumStability.Algorithms.QR.HouseholderMatrixStep

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-- The compact panel update and the rectangular matrix update use the same
rounded Householder kernel column by column. -/
theorem fl_householderApplyCompactPanel_eq_applyMatrixRect
    (fp : FPModel) (m n : Nat) (v : Fin m -> Real) (beta : Real)
    (A : Fin m -> Fin n -> Real) :
    fl_householderApplyCompactPanel fp m n v beta A =
      fl_householderApplyMatrixRect fp m n v beta A := by
  rfl

/-- On active nonzero-stored entries, one stored panel step is exactly the
ordinary rectangular Householder panel update with the same reflector data.

The hypotheses say that the queried column is active and, if it is the pivot
column, that the queried row is not below the pivot where QR storage inserts a
structural zero. -/
theorem fl_householderStoredPanelStep_eq_applyMatrixRect_of_active_not_below
    (fp : FPModel) (m n k : Nat) (v : Fin m -> Real) (beta : Real)
    (A : Fin m -> Fin n -> Real) (i : Fin m) (j : Fin n)
    (hactive : k <= j.val)
    (hnotBelowPivot : j.val = k -> Not (k < i.val)) :
    fl_householderStoredPanelStep fp m n k v beta A i j =
      fl_householderApplyMatrixRect fp m n v beta A i j := by
  have hnotPrev : Not (j.val < k) := Nat.not_lt.mpr hactive
  by_cases hpivot : j.val = k
  case pos =>
    have hnotBelow : Not (k < i.val) := hnotBelowPivot hpivot
    simp [fl_householderStoredPanelStep, fl_householderApplyCompactPanel,
      fl_householderApplyMatrixRect, fl_householderApplyCompact,
      fl_householderApply, hpivot, hnotBelow]
  case neg =>
    simp [fl_householderStoredPanelStep, fl_householderApplyCompactPanel,
      fl_householderApplyMatrixRect, fl_householderApplyCompact,
      fl_householderApply, hnotPrev, hpivot]

/-- Rectangular one-step version of `orthogonal_sequence_one_step`.

    This is the algebraic accumulation step needed for a tall/rectangular
    Householder QR route: if the current rectangular matrix is
    `Qᵀ (A + ΔA)` and the next computed transformation is `(P + ΔP)`, then
    the result is again represented as `Q'ᵀ (A + ΔA')`, with the perturbation
    radius growing by at most `‖ΔP‖_F ‖A + ΔA‖_F`. -/
theorem rect_orthogonal_sequence_one_step (m n : ℕ)
    (A A_hat : Fin m → Fin n → ℝ)
    (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin n → ℝ)
    (hQ : IsOrthogonal m Q)
    (hAhat : ∀ i j, A_hat i j =
      matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (P : Fin m → Fin m → ℝ) (ΔP : Fin m → Fin m → ℝ)
    (hP : IsOrthogonal m P)
    (c_step : ℝ)
    (hΔP : frobNorm ΔP ≤ c_step)
    (A_next : Fin m → Fin n → ℝ)
    (hNext : ∀ i j, A_next i j =
      matMulRectLeft (fun a b => P a b + ΔP a b) A_hat i j) :
    ∃ (Q' : Fin m → Fin m → ℝ) (ΔA' : Fin m → Fin n → ℝ),
      IsOrthogonal m Q' ∧
      (∀ i j, A_next i j =
        matMulRectLeft (matTranspose Q') (fun a b => A a b + ΔA' a b) i j) ∧
      frobNormRect ΔA' ≤
        frobNormRect ΔA +
          c_step * frobNormRect (fun a b => A a b + ΔA a b) := by
  let Q' := matMul m Q (matTranspose P)
  let B : Fin m → Fin n → ℝ := fun a b => A a b + ΔA a b
  let E : Fin m → Fin n → ℝ := matMulRectLeft (matMul m Q' ΔP) A_hat
  let ΔA' : Fin m → Fin n → ℝ := fun a b => ΔA a b + E a b
  have hQ' : IsOrthogonal m Q' := hQ.mul hP.transpose
  have hÂ : A_hat = matMulRectLeft (matTranspose Q) B :=
    funext fun k => funext fun l => hAhat k l
  have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
    show matTranspose (matMul m Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have eq1 : matMulRectLeft (matTranspose Q') B = matMulRectLeft P A_hat := by
    rw [hQ'T, matMulRectLeft_assoc, ← hÂ]
  have eq2 : matMulRectLeft (matTranspose Q') E =
      matMulRectLeft ΔP A_hat := by
    show matMulRectLeft (matTranspose Q')
        (matMulRectLeft (matMul m Q' ΔP) A_hat) = _
    rw [← matMulRectLeft_assoc, ← matMul_assoc, hQ'inv, matMul_id_left]
  use Q', ΔA'
  refine ⟨hQ', ?_, ?_⟩
  · have hBE : (fun a b => A a b + ΔA' a b) = fun a b => B a b + E a b :=
      funext fun a => funext fun b =>
        show A a b + (ΔA a b + E a b) = (A a b + ΔA a b) + E a b from by ring
    intro i j
    rw [hNext i j, hBE]
    calc matMulRectLeft (fun a b => P a b + ΔP a b) A_hat i j
        = matMulRectLeft P A_hat i j + matMulRectLeft ΔP A_hat i j :=
          congr_fun (congr_fun (matMulRectLeft_add_left P ΔP A_hat) i) j
      _ = matMulRectLeft (matTranspose Q') B i j +
            matMulRectLeft (matTranspose Q') E i j := by
          rw [← congr_fun (congr_fun eq1 i) j,
            ← congr_fun (congr_fun eq2 i) j]
      _ = matMulRectLeft (matTranspose Q') (fun a b => B a b + E a b) i j :=
          (congr_fun
            (congr_fun (matMulRectLeft_add_right (matTranspose Q') B E) i) j).symm
  · show frobNormRect (fun a b => ΔA a b + E a b) ≤
        frobNormRect ΔA + c_step * frobNormRect B
    have hfE :
        frobNormRect E =
          frobNormRect (matMulRectLeft ΔP A_hat) := by
      show frobNormRect (matMulRectLeft (matMul m Q' ΔP) A_hat) = _
      rw [matMulRectLeft_assoc]
      exact frobNormRect_orthogonal_left Q' (matMulRectLeft ΔP A_hat) hQ'
    have hfÂ :
        frobNormRect A_hat =
          frobNormRect B := by
      rw [hÂ]
      exact frobNormRect_orthogonal_left (matTranspose Q) B hQ.transpose
    calc frobNormRect (fun a b => ΔA a b + E a b)
        ≤ frobNormRect ΔA + frobNormRect E :=
          frobNormRect_add_le ΔA E
      _ = frobNormRect ΔA +
            frobNormRect (matMulRectLeft ΔP A_hat) := by
          rw [hfE]
      _ ≤ frobNormRect ΔA +
            frobNorm ΔP * frobNormRect A_hat := by
          exact add_le_add (le_refl (frobNormRect ΔA))
            (frobNormRect_matMulRectLeft_le ΔP A_hat)
      _ = frobNormRect ΔA +
            frobNorm ΔP * frobNormRect B := by rw [hfÂ]
      _ ≤ frobNormRect ΔA +
            c_step * frobNormRect B := by
          exact add_le_add (le_refl (frobNormRect ΔA))
            (mul_le_mul_of_nonneg_right hΔP (frobNormRect_nonneg B))

/-- Rectangular multi-step accumulation with a rigorous geometric radius.

    This iterates `rect_orthogonal_sequence_one_step` for `r` perturbed
    orthogonal transformations.  Unlike the informal first-order statement
    `r*c*‖A‖_F`, the formalized bound keeps the higher-order accumulation as
    `((1+c)^r-1)‖A‖_F`. -/
theorem rect_orthogonal_sequence_geometric (m n r : ℕ)
    (A : Fin m → Fin n → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (P ΔP : ℕ → Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hInit : A_hat 0 = A)
    (hP : ∀ k, k < r → IsOrthogonal m (P k))
    (hΔP : ∀ k, k < r → frobNorm (ΔP k) ≤ c)
    (hNext : ∀ k, k < r →
      A_hat (k + 1) = matMulRectLeft (fun a b => P k a b + ΔP k a b) (A_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin n → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      frobNormRect ΔA ≤ ((1 + c) ^ r - 1) * frobNormRect A := by
  let M := frobNormRect A
  have hbase :
      ∀ k, k ≤ r →
        ∃ (Q : Fin m → Fin m → ℝ) (ΔA : Fin m → Fin n → ℝ),
          IsOrthogonal m Q ∧
          (∀ i j, A_hat k i j =
            matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
          frobNormRect ΔA ≤ ((1 + c) ^ k - 1) * M := by
    intro k
    induction k with
    | zero =>
        intro _hk
        refine ⟨idMatrix m, (fun _ _ => 0), IsOrthogonal.id m, ?_, ?_⟩
        · intro i j
          rw [hInit, matTranspose_id, matMulRectLeft_id]
          simp
        · have hzero : frobNormRect (fun _ : Fin m => fun _ : Fin n => 0) = 0 := by
            unfold frobNormRect frobNormSqRect
            simp
          rw [hzero]
          simp
    | succ k ih =>
        intro hk_succ
        have hk_lt : k < r := Nat.lt_of_succ_le hk_succ
        obtain ⟨Q, ΔA, hQ, hrep, hbound⟩ := ih (Nat.le_of_lt hk_lt)
        have hNextPoint : ∀ i j, A_hat (k + 1) i j =
            matMulRectLeft (fun a b => P k a b + ΔP k a b) (A_hat k) i j := by
          intro i j
          rw [hNext k hk_lt]
        obtain ⟨Q', ΔA', hQ', hrep', hstep⟩ :=
          rect_orthogonal_sequence_one_step m n A (A_hat k) Q ΔA hQ hrep
            (P k) (ΔP k) (hP k hk_lt) c (hΔP k hk_lt)
            (A_hat (k + 1)) hNextPoint
        refine ⟨Q', ΔA', hQ', hrep', ?_⟩
        have htri :
            frobNormRect (fun a b => A a b + ΔA a b) ≤ M + frobNormRect ΔA := by
          exact frobNormRect_add_le A ΔA
        have hmul :
            c * frobNormRect (fun a b => A a b + ΔA a b) ≤
              c * (M + frobNormRect ΔA) :=
          mul_le_mul_of_nonneg_left htri hc
        have hrec :
            frobNormRect ΔA' ≤
              (1 + c) * frobNormRect ΔA + c * M := by
          calc frobNormRect ΔA'
              ≤ frobNormRect ΔA +
                  c * frobNormRect (fun a b => A a b + ΔA a b) := hstep
            _ ≤ frobNormRect ΔA + c * (M + frobNormRect ΔA) := by
                  exact add_le_add (le_refl (frobNormRect ΔA)) hmul
            _ = (1 + c) * frobNormRect ΔA + c * M := by ring
        have hone : 0 ≤ 1 + c := by linarith
        have hrec_bound :
            (1 + c) * frobNormRect ΔA + c * M ≤
              (1 + c) * (((1 + c) ^ k - 1) * M) + c * M := by
          exact add_le_add (mul_le_mul_of_nonneg_left hbound hone)
            (le_refl (c * M))
        have hgeom :
            (1 + c) * (((1 + c) ^ k - 1) * M) + c * M =
              ((1 + c) ^ (k + 1) - 1) * M := by
          rw [pow_succ]
          ring
        exact le_trans hrec (by simpa [hgeom] using hrec_bound)
  simpa [M] using hbase r le_rfl

/-- Vector one-step version of `rect_orthogonal_sequence_one_step`.

    A rectangular QR solve route applies the same perturbed orthogonal
    transformations to the right-hand side.  This theorem records the matching
    source-style representation and Euclidean-norm perturbation growth for a
    single vector update. -/
theorem orthogonal_vector_sequence_one_step (m : ℕ)
    (b b_hat : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ) (Δb : Fin m → ℝ)
    (hQ : IsOrthogonal m Q)
    (hbhat : ∀ i, b_hat i =
      matMulVec m (matTranspose Q) (fun a => b a + Δb a) i)
    (P : Fin m → Fin m → ℝ) (ΔP : Fin m → Fin m → ℝ)
    (hP : IsOrthogonal m P)
    (c_step : ℝ)
    (hΔP : frobNorm ΔP ≤ c_step)
    (b_next : Fin m → ℝ)
    (hNext : ∀ i, b_next i =
      matMulVec m (fun a b => P a b + ΔP a b) b_hat i) :
    ∃ (Q' : Fin m → Fin m → ℝ) (Δb' : Fin m → ℝ),
      IsOrthogonal m Q' ∧
      (∀ i, b_next i =
        matMulVec m (matTranspose Q') (fun a => b a + Δb' a) i) ∧
      vecNorm2 Δb' ≤
        vecNorm2 Δb + c_step * vecNorm2 (fun a => b a + Δb a) := by
  let Q' := matMul m Q (matTranspose P)
  let B : Fin m → ℝ := fun a => b a + Δb a
  let E : Fin m → ℝ := matMulVec m (matMul m Q' ΔP) b_hat
  let Δb' : Fin m → ℝ := fun a => Δb a + E a
  have hQ' : IsOrthogonal m Q' := hQ.mul hP.transpose
  have hb : b_hat = matMulVec m (matTranspose Q) B :=
    funext fun k => hbhat k
  have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
    show matTranspose (matMul m Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have eq1 : matMulVec m (matTranspose Q') B = matMulVec m P b_hat := by
    rw [hQ'T]
    ext i
    rw [matMulVec_matMul, ← hb]
  have eq2 : matMulVec m (matTranspose Q') E = matMulVec m ΔP b_hat := by
    ext i
    show matMulVec m (matTranspose Q')
        (matMulVec m (matMul m Q' ΔP) b_hat) i =
      matMulVec m ΔP b_hat i
    rw [← matMulVec_matMul, ← matMul_assoc, hQ'inv, matMul_id_left]
  use Q', Δb'
  refine ⟨hQ', ?_, ?_⟩
  · have hBE : (fun a => b a + Δb' a) = fun a => B a + E a :=
      funext fun a =>
        show b a + (Δb a + E a) = (b a + Δb a) + E a from by ring
    intro i
    rw [hNext i, hBE]
    calc matMulVec m (fun a b => P a b + ΔP a b) b_hat i
        = matMulVec m P b_hat i + matMulVec m ΔP b_hat i :=
          congr_fun (matMulVec_add_left m P ΔP b_hat) i
      _ = matMulVec m (matTranspose Q') B i +
            matMulVec m (matTranspose Q') E i := by
          rw [← congr_fun eq1 i, ← congr_fun eq2 i]
      _ = matMulVec m (matTranspose Q') (fun a => B a + E a) i :=
          (congr_fun (matMulVec_add_right m (matTranspose Q') B E) i).symm
  · show vecNorm2 (fun a => Δb a + E a) ≤
        vecNorm2 Δb + c_step * vecNorm2 B
    have hEfun : E = matMulVec m Q' (matMulVec m ΔP b_hat) := by
      ext i
      exact matMulVec_matMul m Q' ΔP b_hat i
    have hfE :
        vecNorm2 E =
          vecNorm2 (matMulVec m ΔP b_hat) := by
      rw [hEfun]
      exact vecNorm2_orthogonal Q' (matMulVec m ΔP b_hat) hQ'
    have hfhat :
        vecNorm2 b_hat =
          vecNorm2 B := by
      rw [hb]
      exact vecNorm2_orthogonal (matTranspose Q) B hQ.transpose
    calc vecNorm2 (fun a => Δb a + E a)
        ≤ vecNorm2 Δb + vecNorm2 E :=
          vecNorm2_add_le Δb E
      _ = vecNorm2 Δb + vecNorm2 (matMulVec m ΔP b_hat) := by rw [hfE]
      _ ≤ vecNorm2 Δb + frobNorm ΔP * vecNorm2 b_hat := by
          exact add_le_add (le_refl (vecNorm2 Δb))
            (vecNorm2_matMulVec_le_frobNorm_mul ΔP b_hat)
      _ = vecNorm2 Δb + frobNorm ΔP * vecNorm2 B := by rw [hfhat]
      _ ≤ vecNorm2 Δb + c_step * vecNorm2 B := by
          exact add_le_add (le_refl (vecNorm2 Δb))
            (mul_le_mul_of_nonneg_right hΔP (vecNorm2_nonneg B))

/-- Fixed-`Q'` version of `orthogonal_vector_sequence_one_step`.

    The existential theorem above is convenient for a single vector.  A
    columnwise Householder QR route needs to apply the one-step argument to
    many columns while keeping the same exact accumulated orthogonal factor
    `Q' = Q Pᵀ`.  This version exposes that fixed factor and returns only the
    updated vector perturbation. -/
theorem orthogonal_vector_sequence_one_step_fixedQ (m : ℕ)
    (b b_hat : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ) (Δb : Fin m → ℝ)
    (hQ : IsOrthogonal m Q)
    (hbhat : ∀ i, b_hat i =
      matMulVec m (matTranspose Q) (fun a => b a + Δb a) i)
    (P : Fin m → Fin m → ℝ) (ΔP : Fin m → Fin m → ℝ)
    (hP : IsOrthogonal m P)
    (c_step : ℝ)
    (hΔP : frobNorm ΔP ≤ c_step)
    (b_next : Fin m → ℝ)
    (hNext : ∀ i, b_next i =
      matMulVec m (fun a b => P a b + ΔP a b) b_hat i) :
    ∃ Δb' : Fin m → ℝ,
      (∀ i, b_next i =
        matMulVec m (matTranspose (matMul m Q (matTranspose P)))
          (fun a => b a + Δb' a) i) ∧
      vecNorm2 Δb' ≤
        vecNorm2 Δb + c_step * vecNorm2 (fun a => b a + Δb a) := by
  let Q' := matMul m Q (matTranspose P)
  let B : Fin m → ℝ := fun a => b a + Δb a
  let E : Fin m → ℝ := matMulVec m (matMul m Q' ΔP) b_hat
  let Δb' : Fin m → ℝ := fun a => Δb a + E a
  have hQ' : IsOrthogonal m Q' := hQ.mul hP.transpose
  have hb : b_hat = matMulVec m (matTranspose Q) B :=
    funext fun k => hbhat k
  have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
    show matTranspose (matMul m Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have eq1 : matMulVec m (matTranspose Q') B = matMulVec m P b_hat := by
    rw [hQ'T]
    ext i
    rw [matMulVec_matMul, ← hb]
  have eq2 : matMulVec m (matTranspose Q') E = matMulVec m ΔP b_hat := by
    ext i
    show matMulVec m (matTranspose Q')
        (matMulVec m (matMul m Q' ΔP) b_hat) i =
      matMulVec m ΔP b_hat i
    rw [← matMulVec_matMul, ← matMul_assoc, hQ'inv, matMul_id_left]
  refine ⟨Δb', ?_, ?_⟩
  · have hBE : (fun a => b a + Δb' a) = fun a => B a + E a :=
      funext fun a =>
        show b a + (Δb a + E a) = (b a + Δb a) + E a from by ring
    intro i
    rw [hNext i, hBE]
    calc matMulVec m (fun a b => P a b + ΔP a b) b_hat i
        = matMulVec m P b_hat i + matMulVec m ΔP b_hat i :=
          congr_fun (matMulVec_add_left m P ΔP b_hat) i
      _ = matMulVec m (matTranspose Q') B i +
            matMulVec m (matTranspose Q') E i := by
          rw [← congr_fun eq1 i, ← congr_fun eq2 i]
      _ = matMulVec m (matTranspose Q') (fun a => B a + E a) i :=
          (congr_fun (matMulVec_add_right m (matTranspose Q') B E) i).symm
  · show vecNorm2 (fun a => Δb a + E a) ≤
        vecNorm2 Δb + c_step * vecNorm2 B
    have hEfun : E = matMulVec m Q' (matMulVec m ΔP b_hat) := by
      ext i
      exact matMulVec_matMul m Q' ΔP b_hat i
    have hfE :
        vecNorm2 E =
          vecNorm2 (matMulVec m ΔP b_hat) := by
      rw [hEfun]
      exact vecNorm2_orthogonal Q' (matMulVec m ΔP b_hat) hQ'
    have hfhat :
        vecNorm2 b_hat =
          vecNorm2 B := by
      rw [hb]
      exact vecNorm2_orthogonal (matTranspose Q) B hQ.transpose
    calc vecNorm2 (fun a => Δb a + E a)
        ≤ vecNorm2 Δb + vecNorm2 E :=
          vecNorm2_add_le Δb E
      _ = vecNorm2 Δb + vecNorm2 (matMulVec m ΔP b_hat) := by rw [hfE]
      _ ≤ vecNorm2 Δb + frobNorm ΔP * vecNorm2 b_hat := by
          exact add_le_add (le_refl (vecNorm2 Δb))
            (vecNorm2_matMulVec_le_frobNorm_mul ΔP b_hat)
      _ = vecNorm2 Δb + frobNorm ΔP * vecNorm2 B := by rw [hfhat]
      _ ≤ vecNorm2 Δb + c_step * vecNorm2 B := by
          exact add_le_add (le_refl (vecNorm2 Δb))
            (mul_le_mul_of_nonneg_right hΔP (vecNorm2_nonneg B))

/-- Vector multi-step accumulation with a rigorous geometric radius.

    This is the right-hand-side companion to
    `rect_orthogonal_sequence_geometric`; it closes the vector perturbation
    dependency needed before a concrete rectangular QR/preconditioner solve
    theorem can feed the least-squares normal-equation handoff. -/
theorem orthogonal_vector_sequence_geometric (m r : ℕ)
    (b : Fin m → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (P ΔP : ℕ → Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hInit : b_hat 0 = b)
    (hP : ∀ k, k < r → IsOrthogonal m (P k))
    (hΔP : ∀ k, k < r → frobNorm (ΔP k) ≤ c)
    (hNext : ∀ k, k < r →
      b_hat (k + 1) = matMulVec m (fun a b => P k a b + ΔP k a b) (b_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b := by
  let M := vecNorm2 b
  have hbase :
      ∀ k, k ≤ r →
        ∃ (Q : Fin m → Fin m → ℝ) (Δb : Fin m → ℝ),
          IsOrthogonal m Q ∧
          (∀ i, b_hat k i =
            matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
          vecNorm2 Δb ≤ ((1 + c) ^ k - 1) * M := by
    intro k
    induction k with
    | zero =>
        intro _hk
        refine ⟨idMatrix m, (fun _ => 0), IsOrthogonal.id m, ?_, ?_⟩
        · intro i
          rw [hInit, matTranspose_id, matMulVec_id]
          simp
        · rw [vecNorm2_zero]
          simp
    | succ k ih =>
        intro hk_succ
        have hk_lt : k < r := Nat.lt_of_succ_le hk_succ
        obtain ⟨Q, Δb, hQ, hrep, hbound⟩ := ih (Nat.le_of_lt hk_lt)
        have hNextPoint : ∀ i, b_hat (k + 1) i =
            matMulVec m (fun a b => P k a b + ΔP k a b) (b_hat k) i := by
          intro i
          rw [hNext k hk_lt]
        obtain ⟨Q', Δb', hQ', hrep', hstep⟩ :=
          orthogonal_vector_sequence_one_step m b (b_hat k) Q Δb hQ hrep
            (P k) (ΔP k) (hP k hk_lt) c (hΔP k hk_lt)
            (b_hat (k + 1)) hNextPoint
        refine ⟨Q', Δb', hQ', hrep', ?_⟩
        have htri :
            vecNorm2 (fun a => b a + Δb a) ≤ M + vecNorm2 Δb := by
          exact vecNorm2_add_le b Δb
        have hmul :
            c * vecNorm2 (fun a => b a + Δb a) ≤
              c * (M + vecNorm2 Δb) :=
          mul_le_mul_of_nonneg_left htri hc
        have hrec :
            vecNorm2 Δb' ≤
              (1 + c) * vecNorm2 Δb + c * M := by
          calc vecNorm2 Δb'
              ≤ vecNorm2 Δb +
                  c * vecNorm2 (fun a => b a + Δb a) := hstep
            _ ≤ vecNorm2 Δb + c * (M + vecNorm2 Δb) := by
                  exact add_le_add (le_refl (vecNorm2 Δb)) hmul
            _ = (1 + c) * vecNorm2 Δb + c * M := by ring
        have hone : 0 ≤ 1 + c := by linarith
        have hrec_bound :
            (1 + c) * vecNorm2 Δb + c * M ≤
              (1 + c) * (((1 + c) ^ k - 1) * M) + c * M := by
          exact add_le_add (mul_le_mul_of_nonneg_left hbound hone)
            (le_refl (c * M))
        have hgeom :
            (1 + c) * (((1 + c) ^ k - 1) * M) + c * M =
              ((1 + c) ^ (k + 1) - 1) * M := by
          rw [pow_succ]
          ring
        exact le_trans hrec (by simpa [hgeom] using hrec_bound)
  simpa [M] using hbase r le_rfl

/-- Columnwise rectangular matrix plus right-hand-side accumulation.

    This is the source-faithful Householder QR shape: each matrix column, and
    the right-hand side, may have its own rounded perturbation matrix at each
    step.  The exact reflector sequence `P k` is common, so the final
    representation still uses one theoretical orthogonal factor `Q`, while
    the perturbation bounds are columnwise. -/
theorem rect_orthogonal_columnwise_vector_sequence_geometric (m n r : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (P : ℕ → Fin m → Fin m → ℝ)
    (ΔPA : ℕ → Fin n → Fin m → Fin m → ℝ)
    (ΔPb : ℕ → Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hP : ∀ k, k < r → IsOrthogonal m (P k))
    (hΔPA : ∀ k, k < r → ∀ j : Fin n, frobNorm (ΔPA k j) ≤ c)
    (hΔPb : ∀ k, k < r → frobNorm (ΔPb k) ≤ c)
    (hNextA : ∀ k, k < r → ∀ i j,
      A_hat (k + 1) i j =
        matMulVec m (fun a b => P k a b + ΔPA k j a b)
          (fun a => A_hat k a j) i)
    (hNextb : ∀ k, k < r →
      b_hat (k + 1) =
        matMulVec m (fun a b => P k a b + ΔPb k a b) (b_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ r - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b := by
  let MA : Fin n → ℝ := fun j => vecNorm2 (fun i => A i j)
  let Mb := vecNorm2 b
  have hbase :
      ∀ k, k ≤ r →
        ∃ (Q : Fin m → Fin m → ℝ)
            (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
          IsOrthogonal m Q ∧
          (∀ i j, A_hat k i j =
            matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
          (∀ i, b_hat k i =
            matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
          (∀ j : Fin n,
            vecNorm2 (fun i => ΔA i j) ≤
              ((1 + c) ^ k - 1) * MA j) ∧
          vecNorm2 Δb ≤ ((1 + c) ^ k - 1) * Mb := by
    intro k
    induction k with
    | zero =>
        intro _hk
        refine ⟨idMatrix m, (fun _ _ => 0), (fun _ => 0),
          IsOrthogonal.id m, ?_, ?_, ?_, ?_⟩
        · intro i j
          rw [hInitA, matTranspose_id]
          simp [matMulRectLeft, idMatrix]
        · intro i
          rw [hInitb, matTranspose_id, matMulVec_id]
          simp
        · intro j
          rw [vecNorm2_zero]
          simp
        · rw [vecNorm2_zero]
          simp
    | succ k ih =>
        intro hk_succ
        have hk_lt : k < r := Nat.lt_of_succ_le hk_succ
        obtain ⟨Q, ΔA, Δb, hQ, hrepA, hrepb, hboundA, hboundb⟩ :=
          ih (Nat.le_of_lt hk_lt)
        let Qnext := matMul m Q (matTranspose (P k))
        have hQnext : IsOrthogonal m Qnext := hQ.mul (hP k hk_lt).transpose
        have hCol :
            ∀ j : Fin n, ∃ Δcol : Fin m → ℝ,
              (∀ i, A_hat (k + 1) i j =
                matMulVec m (matTranspose Qnext)
                  (fun a => A a j + Δcol a) i) ∧
              vecNorm2 Δcol ≤
                vecNorm2 (fun i => ΔA i j) +
                  c * vecNorm2 (fun i => A i j + ΔA i j) := by
          intro j
          have hrepCol : ∀ i, A_hat k i j =
              matMulVec m (matTranspose Q)
                (fun a => A a j + ΔA a j) i := by
            intro i
            simpa [matMulRectLeft, matMulVec] using hrepA i j
          have hNextCol : ∀ i, A_hat (k + 1) i j =
              matMulVec m (fun a b => P k a b + ΔPA k j a b)
                (fun a => A_hat k a j) i := by
            intro i
            exact hNextA k hk_lt i j
          simpa [Qnext] using
            orthogonal_vector_sequence_one_step_fixedQ m
              (fun i => A i j) (fun i => A_hat k i j)
              Q (fun i => ΔA i j) hQ hrepCol
              (P k) (ΔPA k j) (hP k hk_lt) c (hΔPA k hk_lt j)
              (fun i => A_hat (k + 1) i j) hNextCol
        let ΔA' : Fin m → Fin n → ℝ :=
          fun i j => Classical.choose (hCol j) i
        have hRhs :
            ∃ Δb' : Fin m → ℝ,
              (∀ i, b_hat (k + 1) i =
                matMulVec m (matTranspose Qnext)
                  (fun a => b a + Δb' a) i) ∧
              vecNorm2 Δb' ≤
                vecNorm2 Δb + c * vecNorm2 (fun a => b a + Δb a) := by
          have hNextPoint : ∀ i, b_hat (k + 1) i =
              matMulVec m (fun a b => P k a b + ΔPb k a b) (b_hat k) i := by
            intro i
            rw [hNextb k hk_lt]
          simpa [Qnext] using
            orthogonal_vector_sequence_one_step_fixedQ m
              b (b_hat k) Q Δb hQ hrepb
              (P k) (ΔPb k) (hP k hk_lt) c (hΔPb k hk_lt)
              (b_hat (k + 1)) hNextPoint
        let Δb' : Fin m → ℝ := Classical.choose hRhs
        have hRhsSpec := Classical.choose_spec hRhs
        refine ⟨Qnext, ΔA', Δb', hQnext, ?_, hRhsSpec.1, ?_, ?_⟩
        · intro i j
          have hs := Classical.choose_spec (hCol j)
          simpa [ΔA', matMulRectLeft, matMulVec] using hs.1 i
        · intro j
          have hs := Classical.choose_spec (hCol j)
          have hstep :
              vecNorm2 (fun i => ΔA' i j) ≤
                vecNorm2 (fun i => ΔA i j) +
                  c * vecNorm2 (fun i => A i j + ΔA i j) := by
            simpa [ΔA'] using hs.2
          have htri :
              vecNorm2 (fun i => A i j + ΔA i j) ≤
                MA j + vecNorm2 (fun i => ΔA i j) := by
            exact vecNorm2_add_le (fun i => A i j) (fun i => ΔA i j)
          have hmul :
              c * vecNorm2 (fun i => A i j + ΔA i j) ≤
                c * (MA j + vecNorm2 (fun i => ΔA i j)) :=
            mul_le_mul_of_nonneg_left htri hc
          have hrec :
              vecNorm2 (fun i => ΔA' i j) ≤
                (1 + c) * vecNorm2 (fun i => ΔA i j) + c * MA j := by
            calc vecNorm2 (fun i => ΔA' i j)
                ≤ vecNorm2 (fun i => ΔA i j) +
                    c * vecNorm2 (fun i => A i j + ΔA i j) := hstep
              _ ≤ vecNorm2 (fun i => ΔA i j) +
                    c * (MA j + vecNorm2 (fun i => ΔA i j)) := by
                    exact add_le_add (le_refl (vecNorm2 (fun i => ΔA i j))) hmul
              _ = (1 + c) * vecNorm2 (fun i => ΔA i j) + c * MA j := by ring
          have hone : 0 ≤ 1 + c := by linarith
          have hrec_bound :
              (1 + c) * vecNorm2 (fun i => ΔA i j) + c * MA j ≤
                (1 + c) * (((1 + c) ^ k - 1) * MA j) + c * MA j := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left (hboundA j) hone)
              (le_refl (c * MA j))
          have hgeom :
              (1 + c) * (((1 + c) ^ k - 1) * MA j) + c * MA j =
                ((1 + c) ^ (k + 1) - 1) * MA j := by
            rw [pow_succ]
            ring
          exact le_trans hrec (by simpa [hgeom] using hrec_bound)
        · have hstep :
              vecNorm2 Δb' ≤
                vecNorm2 Δb + c * vecNorm2 (fun a => b a + Δb a) :=
            hRhsSpec.2
          have htri :
              vecNorm2 (fun a => b a + Δb a) ≤ Mb + vecNorm2 Δb := by
            exact vecNorm2_add_le b Δb
          have hmul :
              c * vecNorm2 (fun a => b a + Δb a) ≤
                c * (Mb + vecNorm2 Δb) :=
            mul_le_mul_of_nonneg_left htri hc
          have hrec :
              vecNorm2 Δb' ≤ (1 + c) * vecNorm2 Δb + c * Mb := by
            calc vecNorm2 Δb'
                ≤ vecNorm2 Δb + c * vecNorm2 (fun a => b a + Δb a) := hstep
              _ ≤ vecNorm2 Δb + c * (Mb + vecNorm2 Δb) := by
                    exact add_le_add (le_refl (vecNorm2 Δb)) hmul
              _ = (1 + c) * vecNorm2 Δb + c * Mb := by ring
          have hone : 0 ≤ 1 + c := by linarith
          have hrec_bound :
              (1 + c) * vecNorm2 Δb + c * Mb ≤
                (1 + c) * (((1 + c) ^ k - 1) * Mb) + c * Mb := by
            exact add_le_add (mul_le_mul_of_nonneg_left hboundb hone)
              (le_refl (c * Mb))
          have hgeom :
              (1 + c) * (((1 + c) ^ k - 1) * Mb) + c * Mb =
                ((1 + c) ^ (k + 1) - 1) * Mb := by
            rw [pow_succ]
            ring
          exact le_trans hrec (by simpa [hgeom] using hrec_bound)
  simpa [MA, Mb] using hbase r le_rfl

/-- Simultaneous rectangular matrix/vector one-step accumulation with a
    common orthogonal factor.

    The separate matrix and right-hand-side accumulation theorems are useful
    independently, but the rectangular QR least-squares route needs the same
    accumulated orthogonal matrix for both transformed data blocks. -/
theorem rect_orthogonal_matrix_vector_sequence_one_step (m n : ℕ)
    (A A_hat : Fin m → Fin n → ℝ)
    (b b_hat : Fin m → ℝ)
    (Q : Fin m → Fin m → ℝ)
    (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ)
    (hQ : IsOrthogonal m Q)
    (hAhat : ∀ i j, A_hat i j =
      matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j)
    (hbhat : ∀ i, b_hat i =
      matMulVec m (matTranspose Q) (fun a => b a + Δb a) i)
    (P : Fin m → Fin m → ℝ) (ΔP : Fin m → Fin m → ℝ)
    (hP : IsOrthogonal m P)
    (c_step : ℝ)
    (hΔP : frobNorm ΔP ≤ c_step)
    (A_next : Fin m → Fin n → ℝ) (b_next : Fin m → ℝ)
    (hNextA : ∀ i j, A_next i j =
      matMulRectLeft (fun a b => P a b + ΔP a b) A_hat i j)
    (hNextb : ∀ i, b_next i =
      matMulVec m (fun a b => P a b + ΔP a b) b_hat i) :
    ∃ (Q' : Fin m → Fin m → ℝ)
        (ΔA' : Fin m → Fin n → ℝ) (Δb' : Fin m → ℝ),
      IsOrthogonal m Q' ∧
      (∀ i j, A_next i j =
        matMulRectLeft (matTranspose Q') (fun a b => A a b + ΔA' a b) i j) ∧
      (∀ i, b_next i =
        matMulVec m (matTranspose Q') (fun a => b a + Δb' a) i) ∧
      frobNormRect ΔA' ≤
        frobNormRect ΔA +
          c_step * frobNormRect (fun a b => A a b + ΔA a b) ∧
      vecNorm2 Δb' ≤
        vecNorm2 Δb + c_step * vecNorm2 (fun a => b a + Δb a) := by
  let Q' := matMul m Q (matTranspose P)
  let B : Fin m → Fin n → ℝ := fun a b => A a b + ΔA a b
  let y : Fin m → ℝ := fun a => b a + Δb a
  let EA : Fin m → Fin n → ℝ := matMulRectLeft (matMul m Q' ΔP) A_hat
  let Eb : Fin m → ℝ := matMulVec m (matMul m Q' ΔP) b_hat
  let ΔA' : Fin m → Fin n → ℝ := fun a b => ΔA a b + EA a b
  let Δb' : Fin m → ℝ := fun a => Δb a + Eb a
  have hQ' : IsOrthogonal m Q' := hQ.mul hP.transpose
  have hÂ : A_hat = matMulRectLeft (matTranspose Q) B :=
    funext fun k => funext fun l => hAhat k l
  have hb : b_hat = matMulVec m (matTranspose Q) y :=
    funext fun k => hbhat k
  have hQ'inv : matMul m (matTranspose Q') Q' = idMatrix m :=
    funext fun a => funext fun b => hQ'.left_inv a b
  have hQ'T : matTranspose Q' = matMul m P (matTranspose Q) := by
    show matTranspose (matMul m Q (matTranspose P)) = _
    rw [matTranspose_matMul, matTranspose_involutive]
  have hA1 : matMulRectLeft (matTranspose Q') B =
      matMulRectLeft P A_hat := by
    rw [hQ'T, matMulRectLeft_assoc, ← hÂ]
  have hA2 : matMulRectLeft (matTranspose Q') EA =
      matMulRectLeft ΔP A_hat := by
    show matMulRectLeft (matTranspose Q')
        (matMulRectLeft (matMul m Q' ΔP) A_hat) = _
    rw [← matMulRectLeft_assoc, ← matMul_assoc, hQ'inv, matMul_id_left]
  have hb1 : matMulVec m (matTranspose Q') y = matMulVec m P b_hat := by
    rw [hQ'T]
    ext i
    rw [matMulVec_matMul, ← hb]
  have hb2 : matMulVec m (matTranspose Q') Eb = matMulVec m ΔP b_hat := by
    ext i
    show matMulVec m (matTranspose Q')
        (matMulVec m (matMul m Q' ΔP) b_hat) i =
      matMulVec m ΔP b_hat i
    rw [← matMulVec_matMul, ← matMul_assoc, hQ'inv, matMul_id_left]
  use Q', ΔA', Δb'
  refine ⟨hQ', ?_, ?_, ?_, ?_⟩
  · have hBE :
        (fun a b => A a b + ΔA' a b) = fun a b => B a b + EA a b :=
      funext fun a => funext fun b =>
        show A a b + (ΔA a b + EA a b) = (A a b + ΔA a b) + EA a b from by
          ring
    intro i j
    rw [hNextA i j, hBE]
    calc matMulRectLeft (fun a b => P a b + ΔP a b) A_hat i j
        = matMulRectLeft P A_hat i j + matMulRectLeft ΔP A_hat i j :=
          congr_fun (congr_fun (matMulRectLeft_add_left P ΔP A_hat) i) j
      _ = matMulRectLeft (matTranspose Q') B i j +
            matMulRectLeft (matTranspose Q') EA i j := by
          rw [← congr_fun (congr_fun hA1 i) j,
            ← congr_fun (congr_fun hA2 i) j]
      _ = matMulRectLeft (matTranspose Q') (fun a b => B a b + EA a b) i j :=
          (congr_fun
            (congr_fun (matMulRectLeft_add_right (matTranspose Q') B EA) i) j).symm
  · have hyE : (fun a => b a + Δb' a) = fun a => y a + Eb a :=
      funext fun a =>
        show b a + (Δb a + Eb a) = (b a + Δb a) + Eb a from by ring
    intro i
    rw [hNextb i, hyE]
    calc matMulVec m (fun a b => P a b + ΔP a b) b_hat i
        = matMulVec m P b_hat i + matMulVec m ΔP b_hat i :=
          congr_fun (matMulVec_add_left m P ΔP b_hat) i
      _ = matMulVec m (matTranspose Q') y i +
            matMulVec m (matTranspose Q') Eb i := by
          rw [← congr_fun hb1 i, ← congr_fun hb2 i]
      _ = matMulVec m (matTranspose Q') (fun a => y a + Eb a) i :=
          (congr_fun (matMulVec_add_right m (matTranspose Q') y Eb) i).symm
  · show frobNormRect (fun a b => ΔA a b + EA a b) ≤
        frobNormRect ΔA + c_step * frobNormRect B
    have hEA :
        frobNormRect EA =
          frobNormRect (matMulRectLeft ΔP A_hat) := by
      show frobNormRect (matMulRectLeft (matMul m Q' ΔP) A_hat) = _
      rw [matMulRectLeft_assoc]
      exact frobNormRect_orthogonal_left Q' (matMulRectLeft ΔP A_hat) hQ'
    have hAhatNorm :
        frobNormRect A_hat =
          frobNormRect B := by
      rw [hÂ]
      exact frobNormRect_orthogonal_left (matTranspose Q) B hQ.transpose
    calc frobNormRect (fun a b => ΔA a b + EA a b)
        ≤ frobNormRect ΔA + frobNormRect EA :=
          frobNormRect_add_le ΔA EA
      _ = frobNormRect ΔA +
            frobNormRect (matMulRectLeft ΔP A_hat) := by rw [hEA]
      _ ≤ frobNormRect ΔA +
            frobNorm ΔP * frobNormRect A_hat := by
          exact add_le_add (le_refl (frobNormRect ΔA))
            (frobNormRect_matMulRectLeft_le ΔP A_hat)
      _ = frobNormRect ΔA +
            frobNorm ΔP * frobNormRect B := by rw [hAhatNorm]
      _ ≤ frobNormRect ΔA +
            c_step * frobNormRect B := by
          exact add_le_add (le_refl (frobNormRect ΔA))
            (mul_le_mul_of_nonneg_right hΔP (frobNormRect_nonneg B))
  · show vecNorm2 (fun a => Δb a + Eb a) ≤
        vecNorm2 Δb + c_step * vecNorm2 y
    have hEbfun : Eb = matMulVec m Q' (matMulVec m ΔP b_hat) := by
      ext i
      exact matMulVec_matMul m Q' ΔP b_hat i
    have hEb :
        vecNorm2 Eb =
          vecNorm2 (matMulVec m ΔP b_hat) := by
      rw [hEbfun]
      exact vecNorm2_orthogonal Q' (matMulVec m ΔP b_hat) hQ'
    have hbhatNorm :
        vecNorm2 b_hat =
          vecNorm2 y := by
      rw [hb]
      exact vecNorm2_orthogonal (matTranspose Q) y hQ.transpose
    calc vecNorm2 (fun a => Δb a + Eb a)
        ≤ vecNorm2 Δb + vecNorm2 Eb :=
          vecNorm2_add_le Δb Eb
      _ = vecNorm2 Δb + vecNorm2 (matMulVec m ΔP b_hat) := by rw [hEb]
      _ ≤ vecNorm2 Δb + frobNorm ΔP * vecNorm2 b_hat := by
          exact add_le_add (le_refl (vecNorm2 Δb))
            (vecNorm2_matMulVec_le_frobNorm_mul ΔP b_hat)
      _ = vecNorm2 Δb + frobNorm ΔP * vecNorm2 y := by rw [hbhatNorm]
      _ ≤ vecNorm2 Δb + c_step * vecNorm2 y := by
          exact add_le_add (le_refl (vecNorm2 Δb))
            (mul_le_mul_of_nonneg_right hΔP (vecNorm2_nonneg y))

/-- Simultaneous rectangular matrix/vector accumulation with one common
    orthogonal factor and geometric perturbation radii.

    This is the rectangular QR substrate needed before the transformed
    top-block solve can be pulled back to the original least-squares data. -/
theorem rect_orthogonal_matrix_vector_sequence_geometric (m n r : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (P ΔP : ℕ → Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hP : ∀ k, k < r → IsOrthogonal m (P k))
    (hΔP : ∀ k, k < r → frobNorm (ΔP k) ≤ c)
    (hNextA : ∀ k, k < r →
      A_hat (k + 1) = matMulRectLeft (fun a b => P k a b + ΔP k a b) (A_hat k))
    (hNextb : ∀ k, k < r →
      b_hat (k + 1) = matMulVec m (fun a b => P k a b + ΔP k a b) (b_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      frobNormRect ΔA ≤ ((1 + c) ^ r - 1) * frobNormRect A ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b := by
  let MA := frobNormRect A
  let Mb := vecNorm2 b
  have hbase :
      ∀ k, k ≤ r →
        ∃ (Q : Fin m → Fin m → ℝ)
            (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
          IsOrthogonal m Q ∧
          (∀ i j, A_hat k i j =
            matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
          (∀ i, b_hat k i =
            matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
          frobNormRect ΔA ≤ ((1 + c) ^ k - 1) * MA ∧
          vecNorm2 Δb ≤ ((1 + c) ^ k - 1) * Mb := by
    intro k
    induction k with
    | zero =>
        intro _hk
        refine ⟨idMatrix m, (fun _ _ => 0), (fun _ => 0), IsOrthogonal.id m,
          ?_, ?_, ?_, ?_⟩
        · intro i j
          rw [hInitA, matTranspose_id, matMulRectLeft_id]
          simp
        · intro i
          rw [hInitb, matTranspose_id, matMulVec_id]
          simp
        · have hzero : frobNormRect (fun _ : Fin m => fun _ : Fin n => 0) = 0 := by
            unfold frobNormRect frobNormSqRect
            simp
          rw [hzero]
          simp
        · rw [vecNorm2_zero]
          simp
    | succ k ih =>
        intro hk_succ
        have hk_lt : k < r := Nat.lt_of_succ_le hk_succ
        obtain ⟨Q, ΔA, Δb, hQ, hrepA, hrepb, hboundA, hboundb⟩ :=
          ih (Nat.le_of_lt hk_lt)
        have hNextAPoint : ∀ i j, A_hat (k + 1) i j =
            matMulRectLeft (fun a b => P k a b + ΔP k a b) (A_hat k) i j := by
          intro i j
          rw [hNextA k hk_lt]
        have hNextbPoint : ∀ i, b_hat (k + 1) i =
            matMulVec m (fun a b => P k a b + ΔP k a b) (b_hat k) i := by
          intro i
          rw [hNextb k hk_lt]
        obtain ⟨Q', ΔA', Δb', hQ', hrepA', hrepb', hstepA, hstepb⟩ :=
          rect_orthogonal_matrix_vector_sequence_one_step m n
            A (A_hat k) b (b_hat k) Q ΔA Δb hQ hrepA hrepb
            (P k) (ΔP k) (hP k hk_lt) c (hΔP k hk_lt)
            (A_hat (k + 1)) (b_hat (k + 1)) hNextAPoint hNextbPoint
        refine ⟨Q', ΔA', Δb', hQ', hrepA', hrepb', ?_, ?_⟩
        · have htriA :
              frobNormRect (fun a b => A a b + ΔA a b) ≤ MA + frobNormRect ΔA := by
            exact frobNormRect_add_le A ΔA
          have hmulA :
              c * frobNormRect (fun a b => A a b + ΔA a b) ≤
                c * (MA + frobNormRect ΔA) :=
            mul_le_mul_of_nonneg_left htriA hc
          have hrecA :
              frobNormRect ΔA' ≤
                (1 + c) * frobNormRect ΔA + c * MA := by
            calc frobNormRect ΔA'
                ≤ frobNormRect ΔA +
                    c * frobNormRect (fun a b => A a b + ΔA a b) := hstepA
              _ ≤ frobNormRect ΔA + c * (MA + frobNormRect ΔA) := by
                    exact add_le_add (le_refl (frobNormRect ΔA)) hmulA
              _ = (1 + c) * frobNormRect ΔA + c * MA := by ring
          have hone : 0 ≤ 1 + c := by linarith
          have hrec_boundA :
              (1 + c) * frobNormRect ΔA + c * MA ≤
                (1 + c) * (((1 + c) ^ k - 1) * MA) + c * MA := by
            exact add_le_add (mul_le_mul_of_nonneg_left hboundA hone)
              (le_refl (c * MA))
          have hgeomA :
              (1 + c) * (((1 + c) ^ k - 1) * MA) + c * MA =
                ((1 + c) ^ (k + 1) - 1) * MA := by
            rw [pow_succ]
            ring
          exact le_trans hrecA (by simpa [hgeomA] using hrec_boundA)
        · have htrib :
              vecNorm2 (fun a => b a + Δb a) ≤ Mb + vecNorm2 Δb := by
            exact vecNorm2_add_le b Δb
          have hmulb :
              c * vecNorm2 (fun a => b a + Δb a) ≤
                c * (Mb + vecNorm2 Δb) :=
            mul_le_mul_of_nonneg_left htrib hc
          have hrecb :
              vecNorm2 Δb' ≤
                (1 + c) * vecNorm2 Δb + c * Mb := by
            calc vecNorm2 Δb'
                ≤ vecNorm2 Δb +
                    c * vecNorm2 (fun a => b a + Δb a) := hstepb
              _ ≤ vecNorm2 Δb + c * (Mb + vecNorm2 Δb) := by
                    exact add_le_add (le_refl (vecNorm2 Δb)) hmulb
              _ = (1 + c) * vecNorm2 Δb + c * Mb := by ring
          have hone : 0 ≤ 1 + c := by linarith
          have hrec_boundb :
              (1 + c) * vecNorm2 Δb + c * Mb ≤
                (1 + c) * (((1 + c) ^ k - 1) * Mb) + c * Mb := by
            exact add_le_add (mul_le_mul_of_nonneg_left hboundb hone)
              (le_refl (c * Mb))
          have hgeomb :
              (1 + c) * (((1 + c) ^ k - 1) * Mb) + c * Mb =
                ((1 + c) ^ (k + 1) - 1) * Mb := by
            rw [pow_succ]
            ring
          exact le_trans hrecb (by simpa [hgeomb] using hrec_boundb)
  simpa [MA, Mb] using hbase r le_rfl

/-- Rectangular Householder panel contracts feed the common matrix/vector
    accumulation theorem.

    Each step is required to expose a single perturbation matrix `ΔP` that
    explains the rounded application of the same reflector to both the current
    matrix panel and the current right-hand side.  This is the exact interface
    a future concrete `fl_householder_qr` implementation must discharge from
    its low-level rounded panel/update operations. -/
theorem householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric
    (m n r : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (P : ℕ → Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStep : ∀ k, k < r →
      HouseholderPanelAppError m n (P k)
        (A_hat k) (A_hat (k + 1)) (b_hat k) (b_hat (k + 1)) c) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      frobNormRect ΔA ≤ ((1 + c) ^ r - 1) * frobNormRect A ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b := by
  classical
  let ΔP : ℕ → Fin m → Fin m → ℝ := fun k =>
    if hk : k < r then Classical.choose ((hStep k hk).pert) else fun _ _ => 0
  have hP : ∀ k, k < r → IsOrthogonal m (P k) := by
    intro k hk
    exact (hStep k hk).orth
  have hΔP : ∀ k, k < r → frobNorm (ΔP k) ≤ c := by
    intro k hk
    have hs := Classical.choose_spec ((hStep k hk).pert)
    simpa [ΔP, hk] using hs.1
  have hNextA : ∀ k, k < r →
      A_hat (k + 1) =
        matMulRectLeft (fun a b => P k a b + ΔP k a b) (A_hat k) := by
    intro k hk
    have hs := Classical.choose_spec ((hStep k hk).pert)
    ext i j
    simpa [ΔP, hk] using hs.2.1 i j
  have hNextb : ∀ k, k < r →
      b_hat (k + 1) =
        matMulVec m (fun a b => P k a b + ΔP k a b) (b_hat k) := by
    intro k hk
    have hs := Classical.choose_spec ((hStep k hk).pert)
    ext i
    simpa [ΔP, hk] using hs.2.2 i
  exact
    rect_orthogonal_matrix_vector_sequence_geometric
      m n r A b A_hat b_hat P ΔP c hc hInitA hInitb
      hP hΔP hNextA hNextb

/-- Source-faithful columnwise Householder panel contracts feed the common
    exact-`Q` accumulation theorem.

    Unlike `householderPanelAppError_rect_orthogonal_matrix_vector_sequence_geometric`,
    this theorem does not require one shared rounded perturbation matrix for
    every panel column and the right-hand side.  Each column may have its own
    perturbation, matching the standard Householder QR analysis, while the
    exact reflector sequence still determines a single final orthogonal
    factor `Q`. -/
theorem householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric
    (m n r : ℕ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (P : ℕ → Fin m → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStep : ∀ k, k < r →
      HouseholderColumnwisePanelAppError m n (P k)
        (A_hat k) (A_hat (k + 1)) (b_hat k) (b_hat (k + 1)) c) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ r - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b := by
  classical
  let ΔPA : ℕ → Fin n → Fin m → Fin m → ℝ := fun k j =>
    if hk : k < r then Classical.choose ((hStep k hk).col_pert j)
    else fun _ _ => 0
  let ΔPb : ℕ → Fin m → Fin m → ℝ := fun k =>
    if hk : k < r then Classical.choose ((hStep k hk).rhs_pert)
    else fun _ _ => 0
  have hP : ∀ k, k < r → IsOrthogonal m (P k) := by
    intro k hk
    exact (hStep k hk).orth
  have hΔPA : ∀ k, k < r → ∀ j : Fin n, frobNorm (ΔPA k j) ≤ c := by
    intro k hk j
    have hs := Classical.choose_spec ((hStep k hk).col_pert j)
    simpa [ΔPA, hk] using hs.1
  have hΔPb : ∀ k, k < r → frobNorm (ΔPb k) ≤ c := by
    intro k hk
    have hs := Classical.choose_spec ((hStep k hk).rhs_pert)
    simpa [ΔPb, hk] using hs.1
  have hNextA : ∀ k, k < r → ∀ i j,
      A_hat (k + 1) i j =
        matMulVec m (fun a b => P k a b + ΔPA k j a b)
          (fun a => A_hat k a j) i := by
    intro k hk i j
    have hs := Classical.choose_spec ((hStep k hk).col_pert j)
    simpa [ΔPA, hk] using hs.2 i
  have hNextb : ∀ k, k < r →
      b_hat (k + 1) =
        matMulVec m (fun a b => P k a b + ΔPb k a b) (b_hat k) := by
    intro k hk
    have hs := Classical.choose_spec ((hStep k hk).rhs_pert)
    ext i
    simpa [ΔPb, hk] using hs.2 i
  exact
    rect_orthogonal_columnwise_vector_sequence_geometric
      m n r A b A_hat b_hat P ΔPA ΔPb c hc hInitA hInitb
      hP hΔPA hΔPb hNextA hNextb

/-- A sequence whose panel and right-hand-side updates are computed by the
    compact rounded Householder routine feeds the source-faithful columnwise
    geometric accumulation theorem.

    This is the concrete dot-scale-subtract application layer for the
    rectangular QR route.  It still assumes the exact reflector vectors and the
    shape/top-RHS invariants of the QR loop; it does not by itself prove that
    the final matrix has the `[R;0]` form. -/
theorem fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric
    (fp : FPModel) (m n r : ℕ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k, k < r →
      A_hat (k + 1) =
        fl_householderApplyCompactPanel fp m n (v k) (β k) (A_hat k))
    (hStepb : ∀ k, k < r →
      b_hat (k + 1) =
        fl_householderApplyCompact fp m (v k) (β k) (b_hat k))
    (horth : ∀ k, k < r → IsOrthogonal m (householder m (v k) (β k)))
    (hA_budget : ∀ k, k < r → ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m (v k) (β k)
          (fun a => A_hat k a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k, k < r →
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m (v k) (β k) (b_hat k) i) ≤
        c * vecNorm2 (b_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ r - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b := by
  apply
    householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric
      m n r A b A_hat b_hat (fun k => householder m (v k) (β k)) c hc
      hInitA hInitb
  intro k hk
  have hpanel :
      HouseholderColumnwisePanelAppError m n (householder m (v k) (β k))
        (A_hat k)
        (fl_householderApplyCompactPanel fp m n (v k) (β k) (A_hat k))
        (b_hat k)
        (fl_householderApplyCompact fp m (v k) (β k) (b_hat k)) c :=
    fl_householderApplyCompactPanel_HouseholderColumnwisePanelAppError_of_budget
      fp m n (v k) (β k) (A_hat k) (b_hat k)
      (horth k hk) hm hc (hA_budget k hk) (hb_budget k hk)
  simpa [hStepA k hk, hStepb k hk] using hpanel

/-- Exact lower-trapezoidal shape invariant for the trailing Householder QR
    recurrence.

    This is the first concrete loop-shape theorem in the rectangular
    Householder/preconditioner bottleneck.  If each exact step builds the
    Householder vector from the trailing segment of the current pivot column,
    then after `n` steps every entry below the diagonal is zero.  Floating-point
    perturbation and the explicit stored-`R`/RHS handoff are handled by the
    surrounding compact-sequence and solver-spec theorems; this lemma supplies
    the exact shape algebra that those theorems previously had to assume. -/
theorem exact_trailing_householder_sequence_lower_zero {m n : ℕ}
    (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        matMulRectLeft
          (householder m
            (householderTrailingActiveVector m ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun i => A_hat k i ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun i => A_hat k i ⟨k, hk⟩) (alpha k))))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0) :
    ∀ (i : Fin m) (j : Fin n), j.val < i.val → A_hat n i j = 0 := by
  classical
  have hshape :
      ∀ k, k ≤ n →
        ∀ (i : Fin m) (j : Fin n),
          j.val < k → j.val < i.val → A_hat k i j = 0 := by
    intro k
    induction k with
    | zero =>
        intro _hk i j hj _
        exact (Nat.not_lt_zero j.val hj).elim
    | succ k ih =>
        intro hk_succ i j hj_succ hji
        have hk_lt : k < n := Nat.lt_of_succ_le hk_succ
        let p : Fin m := ⟨k, lt_of_lt_of_le hk_lt hmn⟩
        let col : Fin n := ⟨k, hk_lt⟩
        let x : Fin m → ℝ := fun a => A_hat k a col
        let v : Fin m → ℝ :=
          householderTrailingActiveVector m p x (alpha k)
        let β : ℝ := householderBetaSpec m v
        have hstepPoint :
            ∀ i j, A_hat (k + 1) i j =
              matMulRectLeft (householder m v β) (A_hat k) i j := by
          intro i j
          have hs := hStep k hk_lt
          change A_hat (k + 1) i j =
            matMulRectLeft
              (householder m
                (householderTrailingActiveVector m
                  ⟨k, lt_of_lt_of_le hk_lt hmn⟩
                  (fun i => A_hat k i ⟨k, hk_lt⟩) (alpha k))
                (householderBetaSpec m
                  (householderTrailingActiveVector m
                    ⟨k, lt_of_lt_of_le hk_lt hmn⟩
                    (fun i => A_hat k i ⟨k, hk_lt⟩) (alpha k))))
              (A_hat k) i j
          rw [hs]
        rcases (Nat.lt_succ_iff_lt_or_eq.mp hj_succ) with hj_lt | hj_eq
        · let xcol : Fin m → ℝ := fun a => A_hat k a j
          have hvprefix : ∀ a : Fin m, a.val < k → v a = 0 := by
            intro a ha
            simpa [v, p, x] using
              householderTrailingActiveVector_zero_prefix m p x (alpha k) a ha
          have hsupport : ∀ a : Fin m, k ≤ a.val → xcol a = 0 := by
            intro a ha
            have hja : j.val < a.val := lt_of_lt_of_le hj_lt ha
            exact ih (Nat.le_of_lt hk_lt) a j hj_lt hja
          have hpreserve :
              matMulVec m (householder m v β) xcol = xcol := by
            exact
              matMulVec_householder_eq_self_of_zero_prefix_support
                m k v xcol β hvprefix hsupport
          calc
            A_hat (k + 1) i j
                = matMulRectLeft (householder m v β) (A_hat k) i j :=
                  hstepPoint i j
            _ = matMulVec m (householder m v β) xcol i := by
                  rfl
            _ = xcol i := congrFun hpreserve i
            _ = 0 := ih (Nat.le_of_lt hk_lt) i j hj_lt hji
        · have hj_fin : j = col := Fin.ext hj_eq
          subst j
          have hpivot_lt_i : p.val < i.val := by
            simpa [p] using hji
          calc
            A_hat (k + 1) i col
                = matMulRectLeft (householder m v β) (A_hat k) i col :=
                  hstepPoint i col
            _ = matMulVec m (householder m v β) x i := by
                  rfl
            _ = 0 := by
                  simpa [v, β, p, x] using
                    matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
                      m p x (alpha k)
                      (by simpa [p, x] using halpha k hk_lt)
                      (by simpa [p, x] using hden k hk_lt)
                      i hpivot_lt_i
  intro i j hji
  exact hshape n le_rfl i j j.is_lt hji

/-- Convert a final rectangular lower-zero pattern into the exact top-block
    facts required by the least-squares QR solver handoff.

    The square `R` and vector `cTop` are the top `n` rows of the final
    transformed matrix and right-hand side.  The only nontrivial facts are the
    zero bottom block and upper-triangularity of `R`; both follow immediately
    from the lower-trapezoidal zero pattern. -/
theorem rectangular_topBlock_shape_facts_of_lower_zero {m n : ℕ}
    (hmn : n ≤ m)
    (A_final : Fin m → Fin n → ℝ) (b_final : Fin m → ℝ)
    (hlower : ∀ (i : Fin m) (j : Fin n), j.val < i.val → A_final i j = 0) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_final ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    let cTop : Fin n → ℝ :=
      fun i => b_final ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
    (∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      A_final i j = R ⟨i.val, hi⟩ j) ∧
    (∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_final i j = 0) ∧
    (∀ (i : Fin m) (hi : i.val < n),
      b_final i = cTop ⟨i.val, hi⟩) ∧
    (∀ i j : Fin n, j.val < i.val → R i j = 0) := by
  intro R cTop
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hi
    rfl
  · intro i j hi
    exact hlower i j (lt_of_lt_of_le j.isLt hi)
  · intro i hi
    rfl
  · intro i j hji
    exact hlower ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j hji

/-- Stored rounded Householder panel steps preserve the QR lower-zero shape.

    This theorem is about the storage convention, not about the backward-error
    constant.  Each step may compute the active/trailing entries by the compact
    rounded Householder primitive, but it explicitly preserves completed
    columns and writes zeros below the current pivot.  Therefore the final
    stored matrix has exact lower-trapezoidal zeros even though the active
    floating-point update itself is inexact. -/
theorem fl_householderStoredPanel_sequence_prefix_lower_zero {m n : ℕ}
    (fp : FPModel)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k)) :
    ∀ k, k ≤ n →
      ∀ (i : Fin m) (j : Fin n),
        j.val < k → j.val < i.val → A_hat k i j = 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro _hk i j hj _
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro hk_succ i j hj_succ hji
      have hk_lt : k < n := Nat.lt_of_succ_le hk_succ
      have hstepPoint :
          A_hat (k + 1) i j =
            fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) i j := by
        have hs := hStep k hk_lt
        exact congrFun (congrFun hs i) j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj_succ with hj_lt | hj_eq
      · calc
          A_hat (k + 1) i j
              = fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) i j :=
                hstepPoint
          _ = A_hat k i j := by
                simp [fl_householderStoredPanelStep, hj_lt]
          _ = 0 := ih (Nat.le_of_lt hk_lt) i j hj_lt hji
      · let col : Fin n := ⟨k, hk_lt⟩
        have hj_fin : j = col := Fin.ext hj_eq
        subst j
        have hki : k < i.val := by
          simpa [col] using hji
        calc
          A_hat (k + 1) i col
              = fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) i col :=
                hstepPoint
          _ = 0 := by
                simp [fl_householderStoredPanelStep, col, hki]

theorem fl_householderStoredPanel_sequence_lower_zero {m n : ℕ}
    (fp : FPModel)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k)) :
    ∀ (i : Fin m) (j : Fin n), j.val < i.val → A_hat n i j = 0 := by
  classical
  intro i j hji
  exact
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v β A_hat hStep n le_rfl i j j.isLt hji

/-- Stored rounded Householder panel steps supply the final top-block QR shape
    facts required by the local least-squares solver interface.

    The theorem intentionally does not prove nonzero diagonal pivots.  That
    remains a rank/nonbreakdown assumption for triangular back substitution, or
    a separate rank theorem to be proved later. -/
theorem fl_householderStoredPanel_sequence_topBlock_shape_facts {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k)) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    let cTop : Fin n → ℝ :=
      fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
    (∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
      A_hat n i j = R ⟨i.val, hi⟩ j) ∧
    (∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat n i j = 0) ∧
    (∀ (i : Fin m) (hi : i.val < n),
      b_hat n i = cTop ⟨i.val, hi⟩) ∧
    (∀ i j : Fin n, j.val < i.val → R i j = 0) := by
  intro R cTop
  exact
    rectangular_topBlock_shape_facts_of_lower_zero hmn (A_hat n) (b_hat n)
      (fl_householderStoredPanel_sequence_lower_zero fp v β A_hat hStep)

private lemma ne_zero_of_abs_sub_lt_abs {x y : ℝ}
    (h : |y - x| < |x|) : y ≠ 0 := by
  intro hy
  subst y
  simp at h

/-- One stored trailing Householder pivot remains nonzero if its componentwise
    diagonal update error is strictly smaller than the exact pivot magnitude.

    This is a floating-point nonbreakdown condition, not a rank theorem: it
    converts a concrete local budget inequality into the diagonal hypothesis
    needed by triangular back substitution. -/
theorem fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha
    (fp : FPModel) (m n k : ℕ)
    (p : Fin m) (col : Fin n)
    (hp : p.val = k) (hcol : col.val = k)
    (A : Fin m → Fin n → ℝ) (alpha : ℝ)
    (hm : gammaValid fp m)
    (halpha :
      alpha * alpha =
        householderTrailingNorm2Sq m p (fun a => A a col))
    (hden :
      (∑ i : Fin m,
        householderTrailingActiveVector m p (fun a => A a col) alpha i *
          householderTrailingActiveVector m p (fun a => A a col) alpha i) ≠ 0)
    (hbudget :
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m p (fun a => A a col) alpha)
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun a => A a col) alpha))
          (fun a => A a col) p < |alpha|) :
    fl_householderStoredPanelStep fp m n k
        (householderTrailingActiveVector m p (fun a => A a col) alpha)
        (householderBetaSpec m
          (householderTrailingActiveVector m p (fun a => A a col) alpha))
        A p col ≠ 0 := by
  classical
  let v : Fin m → ℝ :=
    householderTrailingActiveVector m p (fun a => A a col) alpha
  let β : ℝ := householderBetaSpec m v
  have hcompleted : col.val < k →
      ∀ i : Fin m,
        matMulVec m (householder m v β) (fun a => A a col) i =
          A i col := by
    intro hlt
    omega
  have hpivot : col.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a col) i = 0 := by
    intro _h i hi
    have hpi : p.val < i.val := by omega
    simpa [v, β] using
      matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
        m p (fun a => A a col) alpha halpha hden i hpi
  have hbound :=
    fl_householderStoredPanelStep_column_componentwise_error_bound
      fp m n k v β A hm col hcompleted hpivot p
  have hexact :
      matMulVec m (householder m v β) (fun a => A a col) p = alpha := by
    have hnot_lt : ¬ p.val < p.val := Nat.lt_irrefl p.val
    simpa [v, β, hnot_lt] using
      matMulVec_householder_trailingActiveVector_eq_prefix_alpha_zero
        m p (fun a => A a col) alpha halpha hden p
  have hnot_col_lt : ¬ col.val < k := by omega
  have hsmall :
      |fl_householderStoredPanelStep fp m n k v β A p col - alpha| <
        |alpha| := by
    calc
      |fl_householderStoredPanelStep fp m n k v β A p col - alpha|
          =
        |fl_householderStoredPanelStep fp m n k v β A p col -
          matMulVec m (householder m v β) (fun a => A a col) p| := by
            rw [hexact]
      _ ≤ householderCompactComponentBudget fp m v β (fun a => A a col) p := by
            simpa [hnot_col_lt] using hbound
      _ < |alpha| := by
            simpa [v, β] using hbudget
  exact ne_zero_of_abs_sub_lt_abs hsmall

/-- A stored panel sequence has nonzero final top-block diagonal whenever every
    pivot step writes a nonzero diagonal entry.  Later stored steps preserve
    completed columns, so the pivot value written at step `i` is still the final
    diagonal entry of column `i`. -/
theorem fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k))
    (hstepDiag : ∀ k (hk : k < n),
      fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k)
        ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  intro i
  let row : Fin m := ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
  have hpres :
      ∀ k, i.val + 1 ≤ k → k ≤ n →
        A_hat k row i = A_hat (i.val + 1) row i := by
    intro k hklo hkhi
    induction k with
    | zero =>
        omega
    | succ k ih =>
        by_cases hbase : k = i.val
        · subst k
          rfl
        · have hk_lt : k < n := by omega
          have hik : i.val < k := by omega
          have hpoint :
              A_hat (k + 1) row i =
                fl_householderStoredPanelStep fp m n k
                  (v k) (β k) (A_hat k) row i := by
            have hs := hStep k hk_lt
            simpa using congrFun (congrFun hs row) i
          calc
            A_hat (k + 1) row i
                = fl_householderStoredPanelStep fp m n k
                    (v k) (β k) (A_hat k) row i := hpoint
            _ = A_hat k row i := by
                  simp [fl_householderStoredPanelStep, hik]
            _ = A_hat (i.val + 1) row i := ih (by omega) (by omega)
  have hfinal :
      A_hat n row i = A_hat (i.val + 1) row i :=
    hpres n (by omega) le_rfl
  have hpivot :
      A_hat (i.val + 1) row i =
        fl_householderStoredPanelStep fp m n i.val
          (v i.val) (β i.val) (A_hat i.val) row i := by
    have hs := hStep i.val i.isLt
    simpa using congrFun (congrFun hs row) i
  rw [hfinal, hpivot]
  exact hstepDiag i.val i.isLt

/-- Prefix version of `fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero`.

    After `k` stored panel steps, every diagonal entry written in the first
    `k` completed columns is still nonzero.  This is the local form needed by
    triangular-leading-block certificates: the previous pivots at an
    intermediate step need not be assumed again. -/
theorem fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k))
    (hstepDiag : ∀ k (hk : k < n),
      fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k)
        ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0) :
    ∀ k (hk : k ≤ n) (i : Fin k),
      A_hat k
        ⟨i.val, lt_of_lt_of_le i.isLt (le_trans hk hmn)⟩
        ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ ≠ 0 := by
  classical
  intro k hk i
  let row : Fin m := ⟨i.val, lt_of_lt_of_le i.isLt (le_trans hk hmn)⟩
  let col : Fin n := ⟨i.val, lt_of_lt_of_le i.isLt hk⟩
  have hi_lt_n : i.val < n := lt_of_lt_of_le i.isLt hk
  have hpres :
      ∀ q, i.val + 1 ≤ q → q ≤ k →
        A_hat q row col = A_hat (i.val + 1) row col := by
    intro q hqlo hqhi
    induction q with
    | zero =>
        omega
    | succ q ih =>
        by_cases hbase : q = i.val
        · subst q
          rfl
        · have hq_lt_n : q < n := by omega
          have hiq : i.val < q := by omega
          have hcol_lt : col.val < q := by
            simpa [col] using hiq
          have hpoint :
              A_hat (q + 1) row col =
                fl_householderStoredPanelStep fp m n q
                  (v q) (β q) (A_hat q) row col := by
            have hs := hStep q hq_lt_n
            simpa using congrFun (congrFun hs row) col
          calc
            A_hat (q + 1) row col
                = fl_householderStoredPanelStep fp m n q
                    (v q) (β q) (A_hat q) row col := hpoint
            _ = A_hat q row col := by
                  simp [fl_householderStoredPanelStep, hcol_lt]
            _ = A_hat (i.val + 1) row col := ih (by omega) (by omega)
  have hlocal :
      A_hat k row col = A_hat (i.val + 1) row col :=
    hpres k (by omega) le_rfl
  have hpivot :
      A_hat (i.val + 1) row col =
        fl_householderStoredPanelStep fp m n i.val
          (v i.val) (β i.val) (A_hat i.val) row col := by
    have hs := hStep i.val hi_lt_n
    simpa using congrFun (congrFun hs row) col
  rw [hlocal, hpivot]
  simpa [row, col] using hstepDiag i.val hi_lt_n

/-- The stored trailing Householder sequence has nonzero final top-block
    diagonal under a concrete per-pivot floating-point nonbreakdown condition:
    each diagonal component budget is strictly smaller than the corresponding
    exact Householder pivot magnitude `|alpha_k|`. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k|) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else
      fun _ => 0
  let β : ℕ → ℝ := fun k =>
    if hk : k < n then householderBetaSpec m (v k) else 0
  apply
    fl_householderStoredPanel_sequence_diag_nonzero_of_step_diag_nonzero
      fp hmn v β A_hat
  · intro k hk
    simpa [v, β, hk] using hStep k hk
  · intro k hk
    simpa [v, β, hk] using
      fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha
        fp m n k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ rfl rfl
        (A_hat k) (alpha k) hm (halpha k hk) (hden k hk)
        (hbudgetDiag k hk)

/-- Stored trailing Householder nonzero diagonal from concrete pivot
    nonbreakdown plus the local pivot-error budget.

    This replaces the denominator hypothesis `vᵀv ≠ 0` by the more visible
    scalar condition that the active stored pivot entry is not the chosen
    `alpha_k`. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hpivotNe : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ alpha k)
    (hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k|) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  have hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0 := by
    intro k hk
    simpa using
      householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
        (hpivotNe k hk)
  exact
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_budget_lt_abs_alpha
      fp hmn A_hat alpha hm hStep halpha hden hbudgetDiag

/-- Stored trailing Householder nonzero diagonal from the standard
    Householder sign convention, positive active trailing-column norms, and
    the local pivot-error budget.

    This removes the scalar `A_hat[k,k] != alpha_k` hypothesis from
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha`.
    A later rank/nonbreakdown theorem only has to prove the positive
    trailing-column norm and the pivot budget inequality. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k|) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  have hpivotNe : ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ alpha k := by
    intro k hk
    simpa using
      householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
        (halpha k hk) (htrailingPos k hk) (hsign k hk)
  exact
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_pivot_ne_alpha
      fp hmn A_hat alpha hm hStep halpha hpivotNe hbudgetDiag

/-- Stored trailing Householder nonzero diagonal with the standard signed
    Householder scalar made explicit.

    This closes the scalar sign-choice part of the nonbreakdown route: instead
    of assuming both `alpha_k^2 = ||x_tail||_2^2` and
    `alpha_k * x_k <= 0`, it assumes the visible source convention that
    `alpha_k` is the signed trailing norm.  The remaining obligations are the
    positive trailing norm and the square-root compact-update budget. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun i => A_hat k i ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  have halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩) := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun i => A_hat k i ⟨k, hk⟩)
  have hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
    intro k hk
    rw [hAlphaDef k hk]
    exact
      signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun i => A_hat k i ⟨k, hk⟩)
  have hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k| := by
    intro k hk
    exact
      budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun i => A_hat k i ⟨k, hk⟩) (alpha k)
        (householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩)
        (halpha k hk) (hbudgetSqrt k hk)
  exact
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos
      fp hmn A_hat alpha hm hStep halpha htrailingPos hsign hbudgetDiag

/-- Prefix-local nonzero diagonal theorem for the stored trailing Householder
    loop with the standard signed alpha rule.

    This is the intermediate-step counterpart of
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget`:
    after `k` steps, all `k` pivots already written by previous steps are
    nonzero.  It is useful for local triangular-leading-block certificates,
    where previous pivots at the current step should come from the stored loop
    rather than from fresh hypotheses. -/
theorem fl_householderStoredTrailingPanel_sequence_prefix_diag_nonzero_of_signed_alpha_trailingNorm_pos_sqrt_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hAlphaDef : ∀ k (hk : k < n),
      alpha k =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun i => A_hat k i ⟨k, hk⟩)))
          (A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩))
    (htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ k (hk : k ≤ n) (i : Fin k),
      A_hat k
        ⟨i.val, lt_of_lt_of_le i.isLt (le_trans hk hmn)⟩
        ⟨i.val, lt_of_lt_of_le i.isLt hk⟩ ≠ 0 := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else
      fun _ => 0
  let β : ℕ → ℝ := fun k =>
    if hk : k < n then householderBetaSpec m (v k) else 0
  refine
    fl_householderStoredPanel_sequence_prefix_diag_nonzero_of_step_diag_nonzero
      fp hmn v β A_hat ?_ ?_
  · intro k hk
    simpa [v, β, hk] using hStep k hk
  · intro k hk
    have halpha :
        alpha k * alpha k =
          householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩) := by
      rw [hAlphaDef k hk]
      exact
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq
          m ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩)
    have hsign :
        alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0 := by
      rw [hAlphaDef k hk]
      exact
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos
          m ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩)
    have hden :
        (∑ i : Fin m,
          householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
            householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0 := by
      simpa using
        householderTrailingActiveVector_inner_self_ne_zero_of_trailingNorm2Sq_pos_mul_nonpos
          m ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
          halpha (htrailingPos k hk) hsign
    have hbudgetDiag :
        householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k| := by
      exact
        budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
          m ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩) (alpha k)
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩)
          halpha (hbudgetSqrt k hk)
    simpa [v, β, hk] using
      fl_householderStoredTrailingPanelStep_diag_nonzero_of_budget_lt_abs_alpha
        fp m n k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ rfl rfl
        (A_hat k) (alpha k) hm halpha hden hbudgetDiag

/-- Embedding of the previous QR columns `0, ..., k-1` into the ambient
    `n` columns. -/
def qrPreviousColumn (n k : ℕ) (hk : k < n) : Fin k → Fin n :=
  fun j => ⟨j.val, Nat.lt_trans j.isLt hk⟩

/-- Embedding of the leading QR columns `0, ..., k` into the ambient
    `n` columns. -/
def qrLeadingColumn (n k : ℕ) (hk : k < n) : Fin (k + 1) → Fin n :=
  fun j => ⟨j.val, lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt hk)⟩

/-- Embedding of the previous QR rows `0, ..., k-1` into the ambient
    `m` rows. -/
def qrPrefixRow (m k : ℕ) (hkm : k ≤ m) : Fin k → Fin m :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt hkm⟩

/-- Embedding of the leading QR rows `0, ..., k` into the ambient
    `m` rows. -/
def qrLeadingRow (m k : ℕ) (hkm : k + 1 ≤ m) : Fin (k + 1) → Fin m :=
  fun i => ⟨i.val, lt_of_lt_of_le i.isLt hkm⟩

private lemma sum_qrLeadingRow_eq_sum_filter_lt {m k : ℕ}
    (hkm : k + 1 ≤ m) (f : Fin m → ℝ) :
    (∑ t : Fin (k + 1), f (qrLeadingRow m k hkm t)) =
      Finset.sum (Finset.filter (fun i : Fin m => i.val < k + 1) Finset.univ) f := by
  have hinj : ∀ a : Fin (k + 1), a ∈ Finset.univ →
      ∀ b : Fin (k + 1), b ∈ Finset.univ →
      qrLeadingRow m k hkm a = qrLeadingRow m k hkm b → a = b :=
    fun a _ b _ hab => Fin.ext (by
      simp only [qrLeadingRow, Fin.mk.injEq] at hab
      exact hab)
  have himg : Finset.image (fun t : Fin (k + 1) => qrLeadingRow m k hkm t)
      Finset.univ = Finset.filter (fun i : Fin m => i.val < k + 1) Finset.univ := by
    ext i
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩
      simpa [qrLeadingRow, Nat.lt_succ_iff] using t.isLt
    · intro hi
      exact ⟨⟨i.val, hi⟩, Fin.ext (by simp [qrLeadingRow])⟩
  rw [← himg, Finset.sum_image hinj]

/-- The current pivot column is not in the span of the previous columns.

    This is the finite-coordinate version used by the QR nonbreakdown bridge:
    no coefficient vector on columns `0, ..., k-1` reproduces column `k`. -/
def qrColumnNotInPreviousSpan {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k < n) : Prop :=
  ∀ coeff : Fin k → ℝ, ∃ i : Fin m,
    A i ⟨k, hk⟩ ≠
      ∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j)

/-- The already-finished QR columns span every vector supported on the first
    `k` rows.

    In the source Householder QR proof this comes from the nonsingular leading
    triangular block.  We keep it as the exact local invariant needed to turn
    prefix support of the pivot column into a forbidden column dependence. -/
def qrPrefixSupportSpannedByPreviousColumns {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k < n) : Prop :=
  ∀ y : Fin m → ℝ,
    (∀ i : Fin m, k ≤ i.val → y i = 0) →
      ∃ coeff : Fin k → ℝ, ∀ i : Fin m,
        y i = ∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j)

/-- A concrete coefficient matrix witnessing that the previous `k` columns
    reproduce every prefix coordinate basis vector on the first `k` rows. -/
def qrPrefixBasisCoefficientMatrix {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (C : Fin k → Fin k → ℝ) : Prop :=
  ∀ r s : Fin k,
    (∑ j : Fin k,
      C r j * A (qrPrefixRow m k hkm s) (qrPreviousColumn n k hk j)) =
        idMatrix k s r

/-- The transpose of the leading `k × k` block formed by the first `k` rows
    and previous `k` columns.  This orientation matches the repository's
    `IsLeftInverse` predicate for producing prefix-basis coefficients. -/
def qrPreviousLeadingBlockTranspose {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n) :
    Fin k → Fin k → ℝ :=
  fun j s => A (qrPrefixRow m k hkm s) (qrPreviousColumn n k hk j)

/-- The leading `(k+1) × (k+1)` block formed by the first `k+1` rows and
    leading `k+1` columns.  A local left inverse for this block can be padded
    by zeros to produce the ambient leading-column left-inverse witness. -/
def qrLeadingBlock {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n) :
    Fin (k + 1) → Fin (k + 1) → ℝ :=
  fun r q => A (qrLeadingRow m k hkm r) (qrLeadingColumn n k hk q)

/-- Last stage needed to bound an upper-triangular displayed entry.

For an entry in displayed column `j` of the `k`th leading block, the current
column case `j = k` is read before pivot `k`, while a previously completed
column `j < k` is read after its storage step `j + 1`. -/
def qrLeadingOffdiagStop {k : ℕ} (j : Fin (k + 1)) : ℕ :=
  if j.val < k then j.val + 1 else k

/-- The displayed off-diagonal stop never passes the displayed leading block. -/
theorem qrLeadingOffdiagStop_le {k : ℕ} (j : Fin (k + 1)) :
    qrLeadingOffdiagStop j ≤ k := by
  unfold qrLeadingOffdiagStop
  split_ifs with hj
  · exact Nat.succ_le_iff.mpr hj
  · rfl

/-- The concrete signed trailing Householder vector used by the stored QR
    loop at stage `t`.  Outside the panel range it is zero; this lets generic
    sequence theorems consume a total stage family while callers keep the
    source-shaped signed-pivot recurrence. -/
noncomputable def storedQRSignedStageVector
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (t : ℕ) : Fin m → ℝ :=
  if ht : t < n then
    householderTrailingActiveVector m
      ⟨t, lt_of_lt_of_le ht hmn⟩
      (fun a => A_hat t a ⟨t, ht⟩) (alpha t)
  else
    0

/-- The Householder beta corresponding to `storedQRSignedStageVector`. -/
noncomputable def storedQRSignedStageBeta
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (t : ℕ) : ℝ :=
  householderBetaSpec m (storedQRSignedStageVector hmn A_hat alpha t)

/-- Exact signed-stage Householder normalization in the form consumed by the
    compact floating-point coefficient.

    If the stored signed-stage denominator is nonzero, then the exact
    `householderBetaSpec` definition gives `|β_t| ‖v_t‖₂² = 2`. -/
theorem storedQRSignedStage_abs_beta_norm_sq_eq_two_of_den_ne_zero
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (t : ℕ)
    (hden :
      (∑ i : Fin m,
        storedQRSignedStageVector hmn A_hat alpha t i *
          storedQRSignedStageVector hmn A_hat alpha t i) ≠ 0) :
    |storedQRSignedStageBeta hmn A_hat alpha t| *
        vecNorm2 (storedQRSignedStageVector hmn A_hat alpha t) ^ 2 = 2 := by
  simpa [storedQRSignedStageBeta] using
    abs_householderBeta_mul_vecNorm2_sq_eq_two m
      (storedQRSignedStageVector hmn A_hat alpha t) hden

/-- Inequality form of
    `storedQRSignedStage_abs_beta_norm_sq_eq_two_of_den_ne_zero`. -/
theorem storedQRSignedStage_abs_beta_norm_sq_le_two_of_den_ne_zero
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (t : ℕ)
    (hden :
      (∑ i : Fin m,
        storedQRSignedStageVector hmn A_hat alpha t i *
          storedQRSignedStageVector hmn A_hat alpha t i) ≠ 0) :
    |storedQRSignedStageBeta hmn A_hat alpha t| *
        vecNorm2 (storedQRSignedStageVector hmn A_hat alpha t) ^ 2 ≤ 2 :=
  le_of_eq
    (storedQRSignedStage_abs_beta_norm_sq_eq_two_of_den_ne_zero
      hmn A_hat alpha t hden)

/-- Exact same-reflector bound for one concrete signed stored-QR stage.

    This closes the local prefix/active-row split in the Cox--Higham QR route.
    Active rows use the signed-pivot row-growth theorem.  Prefix rows are
    unchanged by the exact zero-prefix Householder reflector, so a prefix entry
    bound and `1 <= coxHighamActiveRowGrowthFactor m` supply the same estimate.
    The theorem is deliberately local: pivot maximality, positive trailing
    norm, and stage entry bounds are still source-facing obligations for the
    concrete sorted/pivoted loop. -/
theorem storedQRSignedStage_exact_same_reflector_bound_of_prefix_or_active_stage_bounds
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (t : ℕ) (ht : t < n)
    (row : Fin m) (col : Fin n) (B : ℝ)
    (hAlphaDef :
      alpha t =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨t, lt_of_lt_of_le ht hmn⟩
              (fun a => A_hat t a ⟨t, ht⟩)))
          (A_hat t ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩))
    (hcol : t ≤ col.val)
    (hB : 0 ≤ B)
    (hprefixBound : row.val < t → |A_hat t row col| ≤ B)
    (hnorm :
      0 <
        householderTrailingColumnNorm2Sq
          (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
          (A_hat t) ⟨t, ht⟩)
    (hpivotMax :
      ∀ l : Fin n, t ≤ l.val →
        householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) l ≤
          householderTrailingColumnNorm2Sq
            (m := m) (n := n) ⟨t, lt_of_lt_of_le ht hmn⟩
            (A_hat t) ⟨t, ht⟩)
    (hrowBound : ∀ l : Fin n, t ≤ l.val → |A_hat t row l| ≤ B)
    (hcolBound : ∀ i : Fin m, t ≤ i.val → |A_hat t i col| ≤ B) :
    |matMulVec m
      (householder m
        (storedQRSignedStageVector hmn A_hat alpha t)
        (storedQRSignedStageBeta hmn A_hat alpha t))
      (fun a => A_hat t a col) row| ≤
      coxHighamActiveRowGrowthFactor m * B := by
  classical
  let pivot : Fin m := ⟨t, lt_of_lt_of_le ht hmn⟩
  let pivotCol : Fin n := ⟨t, ht⟩
  by_cases hprefix : row.val < t
  · have hvprefix :
        ∀ i : Fin m, i.val < t →
          storedQRSignedStageVector hmn A_hat alpha t i = 0 := by
      intro i hi
      have hip : i.val < pivot.val := by
        simpa [pivot] using hi
      simpa [storedQRSignedStageVector, ht, pivot, pivotCol] using
        householderTrailingActiveVector_zero_prefix m pivot
          (fun a => A_hat t a pivotCol) (alpha t) i hip
    have hpres :
        matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a col) row =
          A_hat t row col :=
      matMulVec_householder_eq_self_of_zero_prefix
        m t (storedQRSignedStageVector hmn A_hat alpha t)
        (fun a => A_hat t a col)
        (storedQRSignedStageBeta hmn A_hat alpha t)
        hvprefix row hprefix
    have hscale : B ≤ coxHighamActiveRowGrowthFactor m * B := by
      simpa [one_mul] using
        mul_le_mul_of_nonneg_right
          (one_le_coxHighamActiveRowGrowthFactor m) hB
    calc
      |matMulVec m
        (householder m
          (storedQRSignedStageVector hmn A_hat alpha t)
          (storedQRSignedStageBeta hmn A_hat alpha t))
        (fun a => A_hat t a col) row|
          = |A_hat t row col| := by rw [hpres]
      _ ≤ B := hprefixBound hprefix
      _ ≤ coxHighamActiveRowGrowthFactor m * B := hscale
  · have hactive : pivot.val ≤ row.val := by
      simpa [pivot] using le_of_not_gt hprefix
    have hbound :
        |matMulVec m
          (householder m
            (householderTrailingActiveVector m pivot
              (fun r => A_hat t r pivotCol)
              (signedHouseholderAlpha
                (Real.sqrt
                  (householderTrailingColumnNorm2Sq
                    (m := m) (n := n) pivot (A_hat t) pivotCol))
                (A_hat t pivot pivotCol)))
            (householderBetaSpec m
              (householderTrailingActiveVector m pivot
                (fun r => A_hat t r pivotCol)
                (signedHouseholderAlpha
                  (Real.sqrt
                    (householderTrailingColumnNorm2Sq
                      (m := m) (n := n) pivot (A_hat t) pivotCol))
                  (A_hat t pivot pivotCol)))))
          (fun r => A_hat t r col) row| ≤
          coxHighamActiveRowGrowthFactor m * B :=
      coxHigham_exactSignedPivotPanelStep_active_entry_bound_of_stage_bounds
        pivot row pivotCol col (A_hat t) B hactive hB hnorm
        (by simpa [pivotCol] using hpivotMax) (by simpa [pivotCol] using hcol)
        (by simpa [pivotCol] using hrowBound)
        (by simpa [pivot] using hcolBound)
    simpa [storedQRSignedStageVector, storedQRSignedStageBeta, ht, pivot,
      pivotCol, hAlphaDef, householderTrailingColumnNorm2Sq] using hbound

/-- Stored panel steps preserve completed columns.

If column `j` is already completed before stage `k`, then the stored sequence
entry at stage `k` is the entry written immediately after processing column
`j`.  This is a bookkeeping lemma for translating Cox--Higham row-growth
budgets into displayed leading-block bounds. -/
theorem fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ
    {m n : ℕ} (fp : FPModel)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k)) :
    ∀ k, k ≤ n →
      ∀ (i : Fin m) (j : Fin n), j.val < k →
        A_hat k i j = A_hat (j.val + 1) i j := by
  classical
  intro k hk
  induction k with
  | zero =>
      intro i j hj
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro i j hj
      have hk_lt : k < n := Nat.lt_of_succ_le hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt | hj_eq
      · have hstepPoint :
            A_hat (k + 1) i j =
              fl_householderStoredPanelStep fp m n k
                (v k) (β k) (A_hat k) i j := by
          exact congrFun (congrFun (hStep k hk_lt) i) j
        calc
          A_hat (k + 1) i j
              = fl_householderStoredPanelStep fp m n k
                  (v k) (β k) (A_hat k) i j := hstepPoint
          _ = A_hat k i j := by
                simp [fl_householderStoredPanelStep, hj_lt]
          _ = A_hat (j.val + 1) i j := ih (Nat.le_of_lt hk_lt) i j hj_lt
      · have hsucc : j.val + 1 = k + 1 := by omega
        simp [hsucc]

/-- Signed stored-QR stages preserve already completed columns.

This packages the `hcompleted` field used by the Cox--Higham active-block
route.  The proof reuses the repository lower-zero invariant for stored panel
steps: for a completed column `j < t`, all rows in the active suffix are
already zero, while the signed Householder vector has a zero prefix before
row `t`.  The zero-prefix/support lemma therefore says that the exact
Householder reflector leaves the completed column unchanged. -/
theorem storedQRSignedStage_completed_column_preservation
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k)) :
    ∀ t (_ht : t < n), ∀ j : Fin n, j.val < t →
      ∀ i : Fin m,
        matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a j) i = A_hat t i j := by
  classical
  intro t ht j hj i
  have hStepStored : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (storedQRSignedStageVector hmn A_hat alpha k)
          (storedQRSignedStageBeta hmn A_hat alpha k)
          (A_hat k) := by
    intro k hk
    simpa [storedQRSignedStageVector, storedQRSignedStageBeta, hk] using
      hStepA k hk
  have hlower :
      ∀ (r : Fin m) (c : Fin n),
        c.val < t → c.val < r.val → A_hat t r c = 0 :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp
      (fun k => storedQRSignedStageVector hmn A_hat alpha k)
      (fun k => storedQRSignedStageBeta hmn A_hat alpha k)
      A_hat hStepStored t (Nat.le_of_lt ht)
  let v : Fin m → ℝ := storedQRSignedStageVector hmn A_hat alpha t
  let β : ℝ := storedQRSignedStageBeta hmn A_hat alpha t
  let xcol : Fin m → ℝ := fun a => A_hat t a j
  have hvprefix : ∀ r : Fin m, r.val < t → v r = 0 := by
    intro r hr
    simpa [v, storedQRSignedStageVector, ht] using
      householderTrailingActiveVector_zero_prefix m
        ⟨t, lt_of_lt_of_le ht hmn⟩
        (fun a => A_hat t a ⟨t, ht⟩) (alpha t) r hr
  have hsupport : ∀ r : Fin m, t ≤ r.val → xcol r = 0 := by
    intro r hr
    exact hlower r j hj (lt_of_lt_of_le hj hr)
  have hpreserve :
      matMulVec m (householder m v β) xcol = xcol :=
    matMulVec_householder_eq_self_of_zero_prefix_support
      m t v xcol β hvprefix hsupport
  simpa [v, β, xcol] using congrFun hpreserve i

/-- Cox--Higham stage budgets supply the displayed leading-block row-budget
    upper field.

This is the row-growth half of the source-control decomposition.  It reuses
the existing stored-panel stage-budget theorem, handles the distinction between
the current displayed column and an already completed column, and returns the
raw coordinate form of the `hoffdiagBudget` field consumed by
`StoredQRSourceOffDiagonalControl`.  Diagonal lower bounds are deliberately not
proved here; they remain the next source-control dependency. -/
theorem fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor
    {m n : ℕ} (hmn : n ≤ m) (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ) (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ t, t < n →
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t (v t) (β t) (A_hat t))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hpivot : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m (householder m (v t) (β t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m (v t) (β t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m (householder m (v t) (β t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i) :
    ∀ k (hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val →
      |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        rowBudget k hk i := by
  classical
  intro k hk i j hij
  let hkm : k + 1 ≤ m := Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)
  let row : Fin m := qrLeadingRow m k hkm i
  let col : Fin n := qrLeadingColumn n k hk j
  let stop : ℕ := qrLeadingOffdiagStop j
  have hstop_le_k : stop ≤ k := by
    by_cases hjk : j.val < k
    · have hsucc : j.val + 1 ≤ k := Nat.succ_le_iff.mpr hjk
      simp [stop, qrLeadingOffdiagStop, hjk, hsucc]
    · have hle : j.val ≤ k := Nat.le_of_lt_succ j.isLt
      have heq : j.val = k := le_antisymm hle (le_of_not_gt hjk)
      simp [stop, qrLeadingOffdiagStop, heq]
  have hactive :
      ∀ t : ℕ, t < stop → t ≤ col.val := by
    intro t ht
    by_cases hjk : j.val < k
    · have htj : t ≤ j.val := Nat.lt_succ_iff.mp
        (by simpa [stop, qrLeadingOffdiagStop, hjk] using ht)
      simpa [col, qrLeadingColumn] using htj
    · have hle : j.val ≤ k := Nat.le_of_lt_succ j.isLt
      have heq : j.val = k := le_antisymm hle (le_of_not_gt hjk)
      have htk : t < k := by
        simpa [stop, qrLeadingOffdiagStop, hjk, heq] using ht
      have htle : t ≤ j.val := by omega
      simpa [col, qrLeadingColumn] using htle
  have hcompleted :
      ∀ t : ℕ, t < stop → col.val < t →
        ∀ a : Fin m,
          matMulVec m (householder m (v t) (β t))
            (fun r => A_hat t r col) a = A_hat t a col := by
    intro t ht hcolt
    exact (Nat.not_lt_of_ge (hactive t ht) hcolt).elim
  have hseq :
      |A_hat stop row col| ≤ entryBudget k hk i j hij stop := by
    simpa [row, col, stop] using
      coxHigham_storedPanel_sequence_active_entry_bound_of_exact_stage_budgets_factor
        fp stop A_hat v β c (entryBudget k hk i j hij) hm row col
        (hinit k hk i j hij)
        (fun t ht =>
          hStep t (Nat.lt_trans (Nat.lt_of_lt_of_le ht hstop_le_k) hk))
        hactive hcompleted
        (fun t ht =>
          hpivot k hk i j hij t (by simpa [stop] using ht))
        (fun t ht =>
          hbudget k hk i j hij t (by simpa [stop] using ht))
        (fun t ht =>
          hexact k hk i j hij t (by simpa [stop] using ht))
  have htoStop :
      A_hat k row col = A_hat stop row col := by
    by_cases hjk : j.val < k
    · have hpres :=
        fl_householderStoredPanel_sequence_completed_column_eq_pivot_succ
          fp v β A_hat hStep k (Nat.le_of_lt hk) row col
          (by simpa [col, qrLeadingColumn] using hjk)
      have hstop : stop = j.val + 1 := by
        simp [stop, qrLeadingOffdiagStop, hjk]
      simpa [stop, hstop] using hpres
    · have hle : j.val ≤ k := Nat.le_of_lt_succ j.isLt
      have heq : j.val = k := le_antisymm hle (le_of_not_gt hjk)
      simp [stop, qrLeadingOffdiagStop, heq]
  have hcoord :
      qrLeadingBlock (A_hat k) hkm hk i j = A_hat k row col := by
    rfl
  calc
    |qrLeadingBlock (A_hat k) hkm hk i j|
        = |A_hat k row col| := by rw [hcoord]
    _ = |A_hat stop row col| := by rw [htoStop]
    _ ≤ entryBudget k hk i j hij stop := hseq
    _ ≤ rowBudget k hk i := by
          simpa [stop] using hrowBudget k hk i j hij

/-- Signed-stage specialization of
    `fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor`.

    This removes the generic reflector family from the row-growth bridge.  The
    recurrence is the concrete signed trailing Householder stored QR recurrence;
    the remaining hypotheses are the actual Cox--Higham stage budgets, exact
    same-reflector bounds, completed/pivot-column zeroing facts, and terminal
    row-budget domination. -/
theorem fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_signed_stage_budgets_factor
    {m n : ℕ} (hmn : n ≤ m) (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (c : ℝ)
    (rowBudget : ∀ k, k < n → Fin (k + 1) → ℝ)
    (entryBudget :
      ∀ k (_hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val → ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ t (_ht : t < n),
      A_hat (t + 1) =
        fl_householderStoredPanelStep fp m n t
          (storedQRSignedStageVector hmn A_hat alpha t)
          (storedQRSignedStageBeta hmn A_hat alpha t)
          (A_hat t))
    (hinit : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      |A_hat 0
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          (qrLeadingColumn n k hk j)| ≤
        entryBudget k hk i j hij 0)
    (hpivot : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m
              (householder m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0)
    (hbudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        c * entryBudget k hk i j hij t +
            householderCompactComponentBudget fp m
              (storedQRSignedStageVector hmn A_hat alpha t)
              (storedQRSignedStageBeta hmn A_hat alpha t)
              (fun a => A_hat t a (qrLeadingColumn n k hk j))
              (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)
          ≤ entryBudget k hk i j hij (t + 1))
    (hexact : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        |matMulVec m
          (householder m
            (storedQRSignedStageVector hmn A_hat alpha t)
            (storedQRSignedStageBeta hmn A_hat alpha t))
          (fun a => A_hat t a (qrLeadingColumn n k hk j))
          (qrLeadingRow m k (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) i)| ≤
          c * entryBudget k hk i j hij t)
    (hrowBudget : ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ hij : i.val < j.val,
      entryBudget k hk i j hij (qrLeadingOffdiagStop j) ≤
        rowBudget k hk i) :
    ∀ k (hk : k < n), ∀ i j : Fin (k + 1), i.val < j.val →
      |qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk i j| ≤
        rowBudget k hk i := by
  exact
    fl_householderStoredPanel_sequence_leadingBlock_offdiag_budget_of_exact_stage_budgets_factor
      hmn fp A_hat
      (fun t => storedQRSignedStageVector hmn A_hat alpha t)
      (fun t => storedQRSignedStageBeta hmn A_hat alpha t)
      c rowBudget entryBudget hm hStep hinit hpivot hbudget hexact hrowBudget

/-- Exact below-pivot zeroing for the concrete signed stored-QR stage.

    This packages the standard trailing Householder zeroing theorem with the
    repository's signed-alpha convention.  The remaining source condition is
    genuine nonbreakdown: the active trailing column norm at the stage is
    positive. -/
theorem storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (t : ℕ) (ht : t < n)
    (hAlphaDef :
      alpha t =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨t, lt_of_lt_of_le ht hmn⟩
              (fun a => A_hat t a ⟨t, ht⟩)))
          (A_hat t ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩))
    (htrailingPos :
      0 < householderTrailingNorm2Sq m
          ⟨t, lt_of_lt_of_le ht hmn⟩
          (fun a => A_hat t a ⟨t, ht⟩))
    (a : Fin m) (ha : t < a.val) :
    matMulVec m
      (householder m
        (storedQRSignedStageVector hmn A_hat alpha t)
        (storedQRSignedStageBeta hmn A_hat alpha t))
      (fun r => A_hat t r ⟨t, ht⟩) a = 0 := by
  classical
  let p : Fin m := ⟨t, lt_of_lt_of_le ht hmn⟩
  let x : Fin m → ℝ := fun a => A_hat t a ⟨t, ht⟩
  have halpha : alpha t * alpha t = householderTrailingNorm2Sq m p x := by
    rw [hAlphaDef]
    exact signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m p x
  have hsign : alpha t * x p ≤ 0 := by
    rw [hAlphaDef]
    exact signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m p x
  have hpivotNe : x p ≠ alpha t := by
    exact
      householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
        m p x (alpha t) halpha htrailingPos hsign
  have hden :
      (∑ i : Fin m,
        householderTrailingActiveVector m p x (alpha t) i *
          householderTrailingActiveVector m p x (alpha t) i) ≠ 0 := by
    exact
      householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
        m p x (alpha t) hpivotNe
  have hzero :=
    matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
      m p x (alpha t) halpha hden a (by simpa [p] using ha)
  simpa [storedQRSignedStageVector, storedQRSignedStageBeta, ht, p, x] using hzero

/-- The signed stored-QR stage supplies the pivot-column zeroing field required
    by the displayed row-budget bridge.

    The theorem closes one of the Cox--Higham bottleneck fields: when the
    displayed column under consideration is the active pivot column, exact
    application of the signed trailing Householder reflector zeros all rows
    below the pivot.  Positive trailing norm remains the honest nonbreakdown
    hypothesis. -/
theorem storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hAlphaDef : ∀ t (ht : t < n),
      alpha t =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨t, lt_of_lt_of_le ht hmn⟩
              (fun a => A_hat t a ⟨t, ht⟩)))
          (A_hat t ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩))
    (htrailingPos : ∀ t (ht : t < n),
      0 < householderTrailingNorm2Sq m
          ⟨t, lt_of_lt_of_le ht hmn⟩
          (fun a => A_hat t a ⟨t, ht⟩)) :
    ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m
              (householder m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0 := by
  classical
  intro k hk i j _hij t hstop hcol a ha
  have hstop_le_k : qrLeadingOffdiagStop j ≤ k := by
    unfold qrLeadingOffdiagStop
    split_ifs with hj
    · omega
    · rfl
  have ht : t < n :=
    lt_of_lt_of_le hstop (le_trans hstop_le_k (Nat.le_of_lt hk))
  have hcolFin : qrLeadingColumn n k hk j = ⟨t, ht⟩ := by
    exact Fin.ext hcol
  have hzero :=
    storedQRSignedStage_pivot_column_zero_below_of_trailingNorm_pos
      hmn A_hat alpha t ht (hAlphaDef t ht) (htrailingPos t ht) a ha
  simpa [hcolFin] using hzero

/-- The signed stored-QR stage supplies pivot-column zeroing from the same
    norm-square budget used by the source-control route.

    This removes the separate positive trailing-norm hypothesis in downstream
    Cox--Higham handoffs: the visible budget inequality already forces the
    trailing norm square to be positive. -/
theorem storedQRSignedStage_pivot_zeroing_field_of_normSqBudget
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hAlphaDef : ∀ t (ht : t < n),
      alpha t =
        signedHouseholderAlpha
          (Real.sqrt
            (householderTrailingNorm2Sq m
              ⟨t, lt_of_lt_of_le ht hmn⟩
              (fun a => A_hat t a ⟨t, ht⟩)))
          (A_hat t ⟨t, lt_of_lt_of_le ht hmn⟩ ⟨t, ht⟩))
    (hbudgetNormSq : ∀ t (ht : t < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨t, lt_of_lt_of_le ht hmn⟩
              (fun a => A_hat t a ⟨t, ht⟩) (alpha t))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨t, lt_of_lt_of_le ht hmn⟩
                (fun a => A_hat t a ⟨t, ht⟩) (alpha t)))
            (fun a => A_hat t a ⟨t, ht⟩)
            ⟨t, lt_of_lt_of_le ht hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨t, lt_of_lt_of_le ht hmn⟩
          (fun a => A_hat t a ⟨t, ht⟩)) :
    ∀ k (hk : k < n), ∀ i j : Fin (k + 1), ∀ _hij : i.val < j.val,
      ∀ t : ℕ, t < qrLeadingOffdiagStop j →
        (qrLeadingColumn n k hk j).val = t →
          ∀ a : Fin m, t < a.val →
            matMulVec m
              (householder m
                (storedQRSignedStageVector hmn A_hat alpha t)
                (storedQRSignedStageBeta hmn A_hat alpha t))
              (fun r => A_hat t r (qrLeadingColumn n k hk j)) a = 0 := by
  classical
  refine
    storedQRSignedStage_pivot_zeroing_field_of_trailingNorm_pos
      hmn A_hat alpha hAlphaDef ?_
  intro t ht
  have hleft_nonneg :
      0 ≤
        (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨t, lt_of_lt_of_le ht hmn⟩
              (fun a => A_hat t a ⟨t, ht⟩) (alpha t))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨t, lt_of_lt_of_le ht hmn⟩
                (fun a => A_hat t a ⟨t, ht⟩) (alpha t)))
            (fun a => A_hat t a ⟨t, ht⟩)
            ⟨t, lt_of_lt_of_le ht hmn⟩) ^ 2 := by
    exact mul_nonneg (Nat.cast_nonneg m) (sq_nonneg _)
  exact lt_of_le_of_lt hleft_nonneg (hbudgetNormSq t ht)

/-- A left inverse for the transposed leading block supplies the concrete
    coefficient witness used by the prefix-span bridge. -/
theorem qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (C : Fin k → Fin k → ℝ)
    (hC : IsLeftInverse k (qrPreviousLeadingBlockTranspose A hkm hk) C) :
    qrPrefixBasisCoefficientMatrix A hkm hk C := by
  intro r s
  simpa [qrPreviousLeadingBlockTranspose, idMatrix, eq_comm] using hC r s

/-- A concrete left-inverse witness for the first `k+1` columns.  Applying
    row `p` of `L` to leading column `q` returns the Kronecker delta
    `δ_{q,p}`. -/
def qrLeadingColumnLeftInverse {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k < n)
    (L : Fin (k + 1) → Fin m → ℝ) : Prop :=
  ∀ p q : Fin (k + 1),
    (∑ i : Fin m, L p i * A i (qrLeadingColumn n k hk q)) =
      idMatrix (k + 1) q p

/-- A left inverse for the concrete leading `(k+1) × (k+1)` block supplies
    the ambient left-inverse witness for the first `k+1` QR columns.

    The ambient witness is the block inverse on rows `0, ..., k` and zero on
    all later rows. -/
theorem qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C) :
    qrLeadingColumnLeftInverse A hk
      (fun p i => if hi : i.val < k + 1 then C p ⟨i.val, hi⟩ else 0) := by
  classical
  intro p q
  let L : Fin (k + 1) → Fin m → ℝ :=
    fun p i => if hi : i.val < k + 1 then C p ⟨i.val, hi⟩ else 0
  have hsum_reduce :
      (∑ i : Fin m, L p i * A i (qrLeadingColumn n k hk q)) =
        (Finset.filter (fun i : Fin m => i.val < k + 1) Finset.univ).sum
          (fun i => L p i * A i (qrLeadingColumn n k hk q)) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hnotle : ¬ i.val ≤ k := by
      intro hle
      exact hi (Nat.lt_succ_iff.mpr hle)
    simp [L, hnotle]
  calc
    (∑ i : Fin m, L p i * A i (qrLeadingColumn n k hk q)) =
        (Finset.filter (fun i : Fin m => i.val < k + 1) Finset.univ).sum
          (fun i => L p i * A i (qrLeadingColumn n k hk q)) := hsum_reduce
    _ = ∑ r : Fin (k + 1),
          L p (qrLeadingRow m k hkm r) *
            A (qrLeadingRow m k hkm r) (qrLeadingColumn n k hk q) := by
        symm
        exact sum_qrLeadingRow_eq_sum_filter_lt hkm
          (fun i => L p i * A i (qrLeadingColumn n k hk q))
    _ = ∑ r : Fin (k + 1),
          C p r * A (qrLeadingRow m k hkm r) (qrLeadingColumn n k hk q) := by
        refine Finset.sum_congr rfl ?_
        intro r _
        have hnotgt : ¬ k < r.val := by
          exact not_lt.mpr (Nat.lt_succ_iff.mp r.isLt)
        simp [L, qrLeadingRow, hnotgt]
    _ = idMatrix (k + 1) q p := by
        simpa [qrLeadingBlock, idMatrix, eq_comm] using hC p q

/-- Padding a vector on the leading QR rows by zeros preserves its squared
    Euclidean norm. -/
theorem vecNorm2Sq_qrLeadingRow_padded_eq {m k : ℕ}
    (hkm : k + 1 ≤ m) (v : Fin (k + 1) → ℝ) :
    vecNorm2Sq
        (fun i : Fin m =>
          if hi : i.val < k + 1 then v ⟨i.val, hi⟩ else 0) =
      vecNorm2Sq v := by
  classical
  let padded : Fin m → ℝ :=
    fun i : Fin m =>
      if hi : i.val < k + 1 then v ⟨i.val, hi⟩ else 0
  have hsum_reduce :
      (∑ i : Fin m, padded i ^ 2) =
        (Finset.filter (fun i : Fin m => i.val < k + 1) Finset.univ).sum
          (fun i => padded i ^ 2) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    have hzero : padded i = 0 := by
      exact dif_neg hi
    simp [hzero]
  calc
    vecNorm2Sq
        (fun i : Fin m =>
          if hi : i.val < k + 1 then v ⟨i.val, hi⟩ else 0) =
        ∑ i : Fin m, padded i ^ 2 := by
          rfl
    _ =
        (Finset.filter (fun i : Fin m => i.val < k + 1) Finset.univ).sum
          (fun i => padded i ^ 2) := hsum_reduce
    _ = ∑ r : Fin (k + 1), padded (qrLeadingRow m k hkm r) ^ 2 := by
          symm
          exact sum_qrLeadingRow_eq_sum_filter_lt hkm
            (fun i => padded i ^ 2)
    _ = ∑ r : Fin (k + 1), v r ^ 2 := by
          refine Finset.sum_congr rfl ?_
          intro r _
          have hlt : (qrLeadingRow m k hkm r).val < k + 1 := by
            simpa [qrLeadingRow] using r.isLt
          have hrow :
              (⟨(qrLeadingRow m k hkm r).val, hlt⟩ : Fin (k + 1)) = r := by
            apply Fin.ext
            simp [qrLeadingRow]
          have hpad : padded (qrLeadingRow m k hkm r) = v r := by
            dsimp [padded]
            rw [dif_pos hlt]
            rw [hrow]
          rw [hpad]
    _ = vecNorm2Sq v := by
          rfl

/-- The specific padded dual row constructed from a leading-block left inverse
    has the same squared norm as the corresponding local inverse row. -/
theorem qrLeadingColumnLeftInverse_padded_row_norm_sq_eq
    {m k : ℕ}
    (hkm : k + 1 ≤ m)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (p : Fin (k + 1)) :
    vecNorm2Sq
        (fun i : Fin m =>
          if hi : i.val < k + 1 then C p ⟨i.val, hi⟩ else 0) =
      vecNorm2Sq (fun r : Fin (k + 1) => C p r) := by
  simpa using
    (vecNorm2Sq_qrLeadingRow_padded_eq (m := m) (k := k) hkm
      (fun r : Fin (k + 1) => C p r))

/-- A nonsingular previous leading block supplies the concrete coefficient
    witness used by the prefix-span bridge.

    This removes the raw inverse witness from the QR nonbreakdown route:
    it is enough to expose the determinant/rank condition on the local block. -/
theorem qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (hdet : Matrix.det
      (qrPreviousLeadingBlockTranspose A hkm hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0) :
    ∃ C : Fin k → Fin k → ℝ,
      qrPrefixBasisCoefficientMatrix A hkm hk C := by
  classical
  obtain ⟨C, hC⟩ :=
    exists_isLeftInverse_of_det_ne_zero k
      (qrPreviousLeadingBlockTranspose A hkm hk) hdet
  exact
    ⟨C,
      qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose
        A hkm hk C hC⟩

/-- A nonsingular leading `(k+1) × (k+1)` block supplies the ambient
    leading-column left-inverse witness. -/
theorem qrLeadingColumnLeftInverse_of_det_ne_zero_leadingBlock
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (hdet : Matrix.det
      (qrLeadingBlock A hkm hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) :
    ∃ L : Fin (k + 1) → Fin m → ℝ,
      qrLeadingColumnLeftInverse A hk L := by
  classical
  obtain ⟨D, hD⟩ :=
    exists_isLeftInverse_of_det_ne_zero (k + 1)
      (qrLeadingBlock A hkm hk) hdet
  exact
    ⟨fun p i => if hi : i.val < k + 1 then D p ⟨i.val, hi⟩ else 0,
      qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
        A hkm hk D hD⟩

/-- If the previous transposed leading block is locally lower triangular with
    nonzero diagonal, then it is nonsingular.

    This local version avoids requiring the whole ambient panel to be
    lower-trapezoidal; only the entries that actually occur in the previous
    `k × k` block are needed. -/
theorem qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (hlower : ∀ i j : Fin k, i.val < j.val →
      qrPreviousLeadingBlockTranspose A hkm hk i j = 0)
    (hdiag : ∀ r : Fin k,
      A (qrPrefixRow m k hkm r) (qrPreviousColumn n k hk r) ≠ 0) :
    Matrix.det
      (qrPreviousLeadingBlockTranspose A hkm hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
  classical
  apply det_ne_zero_of_lower_triangular_diag_ne_zero k
    (qrPreviousLeadingBlockTranspose A hkm hk)
  · exact hlower
  · intro i
    simpa [qrPreviousLeadingBlockTranspose] using hdiag i

/-- If the current leading block is locally upper triangular with nonzero
    diagonal, then it is nonsingular.

    This is the principal-minor determinant bridge needed by the no-pivot QR
    route; the triangular shape is only requested on the displayed leading
    block. -/
theorem qrLeadingBlock_det_ne_zero_of_local_upper_triangular_diag_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (hupper : ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock A hkm hk i j = 0)
    (hdiag : ∀ r : Fin (k + 1),
      A (qrLeadingRow m k hkm r) (qrLeadingColumn n k hk r) ≠ 0) :
    Matrix.det
      (qrLeadingBlock A hkm hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
  classical
  apply det_ne_zero_of_upper_triangular_diag_ne_zero (k + 1)
    (qrLeadingBlock A hkm hk)
  · exact hupper
  · intro i
    simpa [qrLeadingBlock] using hdiag i

/-- If the ambient QR panel has the lower-zero shape and the previous leading
    diagonal entries are nonzero, then the transposed previous leading block is
    nonsingular.

    This is a triangular determinant bridge.  It does not prove the diagonal
    nonzero facts; those remain the rank/nonbreakdown input. -/
theorem qrPreviousLeadingBlockTranspose_det_ne_zero_of_upper_triangular_diag_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (hupper : ∀ (i : Fin m) (j : Fin n), j.val < i.val → A i j = 0)
    (hdiag : ∀ r : Fin k,
      A (qrPrefixRow m k hkm r) (qrPreviousColumn n k hk r) ≠ 0) :
    Matrix.det
      (qrPreviousLeadingBlockTranspose A hkm hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0 := by
  classical
  apply
    qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
      A hkm hk
  · intro i j hij
    exact hupper
      (qrPrefixRow m k hkm j)
      (qrPreviousColumn n k hk i)
      (by simpa [qrPrefixRow, qrPreviousColumn] using hij)
  · exact hdiag

/-- If the ambient QR panel has the lower-zero shape on the leading block and
    every leading diagonal entry is nonzero, then the current leading block is
    nonsingular.

    This is the local principal-minor route.  For no-pivot Householder QR it is
    stronger than mere full column rank, because it asks for a nonzero current
    leading diagonal entry before the current reflector is applied. -/
theorem qrLeadingBlock_det_ne_zero_of_upper_triangular_diag_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (hupper : ∀ (i : Fin m) (j : Fin n), j.val < i.val → A i j = 0)
    (hdiag : ∀ r : Fin (k + 1),
      A (qrLeadingRow m k hkm r) (qrLeadingColumn n k hk r) ≠ 0) :
    Matrix.det
      (qrLeadingBlock A hkm hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0 := by
  classical
  apply qrLeadingBlock_det_ne_zero_of_local_upper_triangular_diag_ne_zero
      A hkm hk
  · intro i j hji
    exact hupper
      (qrLeadingRow m k hkm i)
      (qrLeadingColumn n k hk j)
      (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
  · exact hdiag

/-- A nonsingular locally upper-triangular leading block has a nonzero current
    pivot.  This is the structured replacement for the false route ruled out by
    `not_forall_det_ne_zero_implies_first_pivot_ne_zero`: the determinant
    hypothesis is used together with the QR lower-zero shape of the displayed
    leading block. -/
theorem qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (hupper : ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock A hkm hk i j = 0)
    (hdet : Matrix.det
      (qrLeadingBlock A hkm hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) :
    A ⟨k, lt_of_lt_of_le (Nat.lt_succ_self k) hkm⟩ ⟨k, hk⟩ ≠ 0 := by
  classical
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hdiag :
      qrLeadingBlock A hkm hk last last ≠ 0 :=
    diag_ne_zero_of_upper_triangular_det_ne_zero
      (k + 1) (qrLeadingBlock A hkm hk) hupper hdet last
  simpa [qrLeadingBlock, qrLeadingRow, qrLeadingColumn, last] using hdiag

/-- In the stored trailing Householder loop, a nonsingular local leading block
    supplies the current pivot nonzero condition because the stored loop has an
    exact lower-zero shape on all completed columns.

    This closes a structured no-pivot route: ordinary full rank is not enough,
    but determinant nonzeroness of the displayed leading principal block plus
    the stored QR shape is enough to recover the current pivot needed by the
    triangular solve certificate. -/
theorem fl_householderStoredTrailingPanel_sequence_current_pivot_ne_zero_of_leadingBlock_det_ne_zero
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) :
    ∀ k (hk : k < n),
      A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≠ 0 := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else 0
  let β : ℕ → ℝ := fun k => householderBetaSpec m (v k)
  have hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) := by
    intro k hk
    simpa [v, β, hk] using hStepA k hk
  have hprefix :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v β A_hat hStep
  intro k hk
  let hkm : k + 1 ≤ m :=
    Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)
  have hupper : ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock (A_hat k) hkm hk i j = 0 := by
    intro i j hji
    have hjk : j.val < k := by omega
    exact
      hprefix k (Nat.le_of_lt hk)
        (qrLeadingRow m k hkm i)
        (qrLeadingColumn n k hk j)
        (by simpa [qrLeadingColumn] using hjk)
        (by simpa [qrLeadingRow, qrLeadingColumn] using hji)
  simpa [hkm] using
    qrLeadingBlock_current_pivot_ne_zero_of_local_upper_triangular_det_ne_zero
      (A_hat k) hkm hk hupper (hdetLead k hk)

/-- The `2 × 2` column-swap matrix used to rule out a false no-pivot QR route:
    it is nonsingular, but its first leading pivot is zero. -/
noncomputable def qrPivotCounterexample2 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i.val + j.val = 1 then 1 else 0

theorem qrPivotCounterexample2_first_pivot_zero :
    qrPivotCounterexample2 (0 : Fin 2) (0 : Fin 2) = 0 := by
  simp [qrPivotCounterexample2]

theorem qrPivotCounterexample2_det_ne_zero :
    Matrix.det (qrPivotCounterexample2 : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 := by
  norm_num [qrPivotCounterexample2, Matrix.det_fin_two]

/-- Route-elimination theorem for the rectangular QR bottleneck: nonsingularity
    of a matrix alone does not imply that the first unpivoted Householder pivot
    is nonzero.  A no-pivot QR theorem therefore needs an explicit
    nonbreakdown/leading-pivot condition, pivoting, or a stronger structured
    invariant. -/
theorem not_forall_det_ne_zero_implies_first_pivot_ne_zero :
    ¬ (∀ A : Fin 2 → Fin 2 → ℝ,
      Matrix.det (A : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 →
        A (0 : Fin 2) (0 : Fin 2) ≠ 0) := by
  intro h
  have hpivot :=
    h qrPivotCounterexample2 qrPivotCounterexample2_det_ne_zero
  exact hpivot qrPivotCounterexample2_first_pivot_zero

theorem qrPivotCounterexample2_first_leadingBlock_det_zero :
    Matrix.det
      (qrLeadingBlock qrPivotCounterexample2
        (by norm_num : 0 + 1 ≤ 2) (by norm_num : 0 < 2) :
        Matrix (Fin (0 + 1)) (Fin (0 + 1)) ℝ) = 0 := by
  rw [Matrix.det_fin_one]
  norm_num [qrLeadingBlock, qrLeadingRow, qrLeadingColumn,
    qrPivotCounterexample2]

/-- Route-elimination theorem for the rectangular QR bottleneck:
    nonsingularity of the whole unpivoted square matrix does not imply that all
    leading principal QR blocks are nonsingular.  The `2 × 2` column-swap matrix
    has nonzero determinant, but its first `1 × 1` leading block has zero
    determinant.  Therefore the stored QR/preconditioner theorem cannot derive
    its per-pivot leading-block determinant assumptions from whole-matrix
    nonsingularity alone; it needs pivoting, structured leading-minor
    assumptions, or a stronger computed-loop invariant. -/
theorem not_forall_det_ne_zero_implies_all_leading_blocks_det_ne_zero :
    ¬ (∀ A : Fin 2 → Fin 2 → ℝ,
      Matrix.det (A : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 →
        ∀ k (hk : k < 2),
          Matrix.det
            (qrLeadingBlock A (Nat.succ_le_iff.mpr hk) hk :
              Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0) := by
  intro h
  have hlead :=
    h qrPivotCounterexample2 qrPivotCounterexample2_det_ne_zero 0
      (by norm_num)
  exact hlead qrPivotCounterexample2_first_leadingBlock_det_zero

/-- A left-inverse witness for the first `k+1` columns proves that column `k`
    is not in the span of the previous `k` columns. -/
theorem qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k < n)
    (L : Fin (k + 1) → Fin m → ℝ)
    (hL : qrLeadingColumnLeftInverse A hk L) :
    qrColumnNotInPreviousSpan A hk := by
  classical
  intro coeff
  by_contra hno
  have hall : ∀ i : Fin m,
      A i ⟨k, hk⟩ =
        ∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j) := by
    intro i
    by_contra hne
    exact hno ⟨i, hne⟩
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hcurrent :
      (∑ i : Fin m, L last i * A i ⟨k, hk⟩) = 1 := by
    have h := hL last last
    simpa [last, qrLeadingColumn, idMatrix] using h
  have hprevZero :
      ∀ j : Fin k,
        (∑ i : Fin m, L last i * A i (qrPreviousColumn n k hk j)) = 0 := by
    intro j
    let q : Fin (k + 1) := ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self k)⟩
    have hqne : q ≠ last := by
      intro hq
      have hval : j.val = k := by
        simpa [q, last] using congrArg Fin.val hq
      exact (Nat.ne_of_lt j.isLt) hval
    have h := hL last q
    simpa [q, last, qrLeadingColumn, qrPreviousColumn, idMatrix, hqne] using h
  have hdistrib :
      (∑ i : Fin m, L last i *
        (∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j))) =
      ∑ j : Fin k, coeff j *
        (∑ i : Fin m, L last i * A i (qrPreviousColumn n k hk j)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hzero :
      (∑ i : Fin m, L last i *
        (∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j))) = 0 := by
    calc
      (∑ i : Fin m, L last i *
          (∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j))) =
          ∑ j : Fin k, coeff j *
            (∑ i : Fin m, L last i * A i (qrPreviousColumn n k hk j)) :=
        hdistrib
      _ = ∑ j : Fin k, coeff j * 0 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hprevZero j]
      _ = 0 := by simp
  have hone_zero : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = ∑ i : Fin m, L last i * A i ⟨k, hk⟩ := hcurrent.symm
      _ = ∑ i : Fin m, L last i *
          (∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j)) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [hall i]
      _ = 0 := hzero
  norm_num at hone_zero

/-- A basis-coefficient witness plus the already-established QR lower-zero
    shape proves the prefix-span invariant used in the rank-route
    nonbreakdown bridge. -/
theorem qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (C : Fin k → Fin k → ℝ)
    (hC : qrPrefixBasisCoefficientMatrix A hkm hk C)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    qrPrefixSupportSpannedByPreviousColumns A hk := by
  classical
  intro y hy
  refine ⟨fun j : Fin k =>
    ∑ r : Fin k, y (qrPrefixRow m k hkm r) * C r j, ?_⟩
  intro i
  by_cases hi : i.val < k
  · let s : Fin k := ⟨i.val, hi⟩
    have hrow : qrPrefixRow m k hkm s = i := by
      ext
      rfl
    have hswap :
        (∑ j : Fin k,
          (∑ r : Fin k, y (qrPrefixRow m k hkm r) * C r j) *
            A i (qrPreviousColumn n k hk j)) =
        ∑ r : Fin k, y (qrPrefixRow m k hkm r) *
          (∑ j : Fin k, C r j * A i (qrPreviousColumn n k hk j)) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro r _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    have hbasis :
        ∀ r : Fin k,
          (∑ j : Fin k, C r j * A i (qrPreviousColumn n k hk j)) =
            idMatrix k s r := by
      intro r
      rw [← hrow]
      exact hC r s
    have hid :
        (∑ r : Fin k, y (qrPrefixRow m k hkm r) * idMatrix k s r) =
          y (qrPrefixRow m k hkm s) := by
      have hid' :=
        congrFun (idMatrix_mulVec k (fun r : Fin k =>
          y (qrPrefixRow m k hkm r))) s
      calc
        (∑ r : Fin k, y (qrPrefixRow m k hkm r) * idMatrix k s r) =
            ∑ r : Fin k, idMatrix k s r * y (qrPrefixRow m k hkm r) := by
              refine Finset.sum_congr rfl ?_
              intro r _
              ring
        _ = y (qrPrefixRow m k hkm s) := hid'
    rw [← hrow]
    symm
    calc
      (∑ j : Fin k,
          (∑ r : Fin k, y (qrPrefixRow m k hkm r) * C r j) *
            A i (qrPreviousColumn n k hk j)) =
          ∑ r : Fin k, y (qrPrefixRow m k hkm r) *
            (∑ j : Fin k, C r j * A i (qrPreviousColumn n k hk j)) := hswap
      _ = ∑ r : Fin k, y (qrPrefixRow m k hkm r) * idMatrix k s r := by
        refine Finset.sum_congr rfl ?_
        intro r _
        rw [hbasis r]
      _ = y (qrPrefixRow m k hkm s) := hid
  · have hge : k ≤ i.val := le_of_not_gt hi
    have hyi : y i = 0 := hy i hge
    rw [hyi]
    simp [hlowerPrev i, hge]

/-- A nonsingular previous leading block plus the QR lower-zero shape supplies
    the abstract prefix-span invariant.

    This is the determinant-facing version of
    `qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix`.
    It closes the prefix-span dependency whenever the previous local leading
    block is known to be nonsingular and the completed columns have the
    stored/triangular QR zero pattern. -/
theorem qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (hdet : Matrix.det
      (qrPreviousLeadingBlockTranspose A hkm hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    qrPrefixSupportSpannedByPreviousColumns A hk := by
  classical
  obtain ⟨C, hC⟩ :=
    qrPrefixBasisCoefficientMatrix_of_det_ne_zero_previousLeadingBlockTranspose
      A hkm hk hdet
  exact
    qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix
      A hkm hk C hC hlowerPrev

/-- A local left inverse for the previous leading block plus the stored QR
    lower-zero shape supplies the abstract prefix-span invariant.

    This is the left-inverse-facing version of
    `qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose`.
    It is useful for source-faithful rectangular QR routes that keep the local
    inverse witness visible rather than replacing it by a determinant. -/
theorem qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (C : Fin k → Fin k → ℝ)
    (hC : IsLeftInverse k (qrPreviousLeadingBlockTranspose A hkm hk) C)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    qrPrefixSupportSpannedByPreviousColumns A hk := by
  exact
    qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix
      A hkm hk C
      (qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose
        A hkm hk C hC)
      hlowerPrev

/-- Stored Householder panels supply prefix-span invariants from local
    previous-block left inverses.

    The completed-column lower-zero shape is derived from the actual stored
    panel recurrence, so downstream QR/least-squares wrappers no longer need to
    assume `qrPrefixSupportSpannedByPreviousColumns` separately when a previous
    leading-block left inverse is available. -/
theorem fl_householderStoredPanel_sequence_prefixSpan_of_leftInverse_previousLeadingBlockTranspose
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk)) :
    ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk := by
  classical
  let v : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else 0
  let β : ℕ → ℝ := fun k => householderBetaSpec m (v k)
  have hStep : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (v k) (β k) (A_hat k) := by
    intro k hk
    simpa [v, β, hk] using hStepA k hk
  have hlower :=
    fl_householderStoredPanel_sequence_prefix_lower_zero
      fp v β A_hat hStep
  intro k hk
  refine
    qrPrefixSupportSpannedByPreviousColumns_of_leftInverse_previousLeadingBlockTranspose
      (A_hat k) (le_trans (Nat.le_of_lt hk) hmn) hk
      (Cprev k hk) (hCprev k hk) ?_
  intro i j hij
  have hjprev : (qrPreviousColumn n k hk j).val < k := by
    simp [qrPreviousColumn]
  have hji : (qrPreviousColumn n k hk j).val < i.val := by
    simpa [qrPreviousColumn] using lt_of_lt_of_le j.isLt hij
  exact
    hlower k (Nat.le_of_lt hk) i (qrPreviousColumn n k hk j) hjprev hji

/-- A nonsingular locally upper-triangular current leading block supplies the
    prefix-span invariant for the previous columns.

    This packages the structured no-pivot route used by the rectangular QR
    bottleneck.  Nonzero determinant of the displayed `(k+1) × (k+1)` leading
    block, together with its local upper-triangular shape, forces the first
    `k` diagonal entries to be nonzero.  Hence the previous transposed
    `k × k` leading block is nonsingular, and the completed-column lower-zero
    shape gives the prefix-span witness. -/
theorem qrPrefixSupportSpannedByPreviousColumns_of_leadingBlock_upper_det_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (hupper : ∀ i j : Fin (k + 1), j.val < i.val →
      qrLeadingBlock A hkm hk i j = 0)
    (hdetLead : Matrix.det
      (qrLeadingBlock A hkm hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    qrPrefixSupportSpannedByPreviousColumns A hk := by
  classical
  let hkmPrev : k ≤ m := le_trans (Nat.le_succ k) hkm
  have hdiagLead :
      ∀ i : Fin (k + 1), qrLeadingBlock A hkm hk i i ≠ 0 :=
    diag_ne_zero_of_upper_triangular_det_ne_zero
      (k + 1) (qrLeadingBlock A hkm hk) hupper hdetLead
  have hlowerPrevBlock :
      ∀ i j : Fin k, i.val < j.val →
        qrPreviousLeadingBlockTranspose A hkmPrev hk i j = 0 := by
    intro i j hij
    let row : Fin (k + 1) :=
      ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self k)⟩
    let col : Fin (k + 1) :=
      ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self k)⟩
    have hzero : qrLeadingBlock A hkm hk row col = 0 := by
      exact hupper row col (by simpa [row, col] using hij)
    simpa [qrPreviousLeadingBlockTranspose, qrLeadingBlock,
      qrPrefixRow, qrPreviousColumn, qrLeadingRow, qrLeadingColumn,
      hkmPrev, row, col] using hzero
  have hdiagPrev :
      ∀ r : Fin k,
        A (qrPrefixRow m k hkmPrev r) (qrPreviousColumn n k hk r) ≠ 0 := by
    intro r
    let rr : Fin (k + 1) :=
      ⟨r.val, Nat.lt_trans r.isLt (Nat.lt_succ_self k)⟩
    have hrr := hdiagLead rr
    simpa [qrLeadingBlock, qrPrefixRow, qrPreviousColumn,
      qrLeadingRow, qrLeadingColumn, hkmPrev, rr] using hrr
  have hdetPrev :
      Matrix.det
        (qrPreviousLeadingBlockTranspose A hkmPrev hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0 :=
    qrPreviousLeadingBlockTranspose_det_ne_zero_of_local_lower_triangular_diag_ne_zero
      A hkmPrev hk hlowerPrevBlock hdiagPrev
  exact
    qrPrefixSupportSpannedByPreviousColumns_of_det_ne_zero_previousLeadingBlockTranspose
      A hkmPrev hk hdetPrev hlowerPrev

/-- Prefix-span nonbreakdown bridge.

    If column `k` is independent of the previous columns and the previous QR
    columns span all prefix-supported vectors, then the active trailing part of
    column `k` must contain a nonzero entry.  Otherwise column `k` itself would
    be prefix-supported and therefore lie in the previous-column span. -/
theorem exists_active_trailing_entry_ne_of_column_notInPreviousSpan
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hk : k < n)
    (hnotspan : qrColumnNotInPreviousSpan A hk)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk) :
    ∃ i : Fin m, k ≤ i.val ∧ A i ⟨k, hk⟩ ≠ 0 := by
  classical
  by_contra hno
  have hzero : ∀ i : Fin m, k ≤ i.val → A i ⟨k, hk⟩ = 0 := by
    intro i hi
    by_contra hne
    exact hno ⟨i, hi, hne⟩
  obtain ⟨coeff, hcoeff⟩ :=
    hprefixSpan (fun i : Fin m => A i ⟨k, hk⟩) hzero
  obtain ⟨i, hi⟩ := hnotspan coeff
  exact hi (hcoeff i)

/-- Prefix-span nonbreakdown supplies the positive trailing norm needed by the
    Householder sign-choice bridge. -/
theorem householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (hnotspan : qrColumnNotInPreviousSpan A hk)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk) :
    0 < householderTrailingNorm2Sq m ⟨k, hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  classical
  have hactive :
      ∃ i : Fin m, (⟨k, hkm⟩ : Fin m).val ≤ i.val ∧
        (fun i : Fin m => A i ⟨k, hk⟩) i ≠ 0 := by
    simpa using
      exists_active_trailing_entry_ne_of_column_notInPreviousSpan
        A hk hnotspan hprefixSpan
  exact
    householderTrailingNorm2Sq_pos_of_exists_ne
      m ⟨k, hkm⟩ (fun i : Fin m => A i ⟨k, hk⟩) hactive

/-- Prefix-span nonbreakdown supplies positive active-block mass.

This is the active-block form consumed by the Cox--Higham pivoted/sorted route:
the existing prefix-span bridge gives a nonzero entry in the current active
pivot column, and a nonzero active entry makes the active trailing block have
positive squared mass. -/
theorem householderActiveBlockNorm2Sq_pos_of_column_notInPreviousSpan
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (hnotspan : qrColumnNotInPreviousSpan A hk)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk) :
    0 < householderActiveBlockNorm2Sq
      ⟨k, hkm⟩ ⟨k, hk⟩ A := by
  classical
  obtain ⟨i, hi, hne⟩ :=
    exists_active_trailing_entry_ne_of_column_notInPreviousSpan
      A hk hnotspan hprefixSpan
  exact
    householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
      ⟨k, hkm⟩ ⟨k, hk⟩ A
      ⟨⟨k, hk⟩, le_rfl, i, by simpa using hi, hne⟩

/-- Prefix-span plus a bounded leading-column dual gives a quantitative
    trailing-norm lower bound.

    The row `last` of the leading-column left inverse annihilates every
    previous column and pairs to `1` with the current pivot column.  Since the
    prefix part of the current column is spanned by previous columns, the same
    dual row pairs to `1` with the active trailing part alone.  Cauchy--Schwarz
    then gives
    `1 <= ||L_last||_2^2 * ||A(k:m,k)||_2^2`; an explicit dual-norm budget
    `||L_last||_2^2 <= K` yields `1 / K <= ||A(k:m,k)||_2^2`.

    This is a genuine quantitative nonbreakdown/conditioning bridge.  It does
    not assert that such a dual row or norm budget exists; later theorems may
    supply it from a concrete inverse, determinant margin, or condition-number
    hypothesis. -/
theorem householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (L : Fin (k + 1) → Fin m → ℝ)
    (hL : qrLeadingColumnLeftInverse A hk L)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K : ℝ) (hK : 0 < K)
    (hLnorm : vecNorm2Sq (fun i : Fin m =>
      L ⟨k, Nat.lt_succ_self k⟩ i) ≤ K) :
    1 / K ≤
      householderTrailingNorm2Sq m ⟨k, hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  classical
  let col : Fin n := ⟨k, hk⟩
  let p : Fin m := ⟨k, hkm⟩
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  let x : Fin m → ℝ := fun i => A i col
  let xPrefix : Fin m → ℝ := householderPrefixPart m p x
  let xTail : Fin m → ℝ := householderTrailingPart m p x
  have hprefixSupport : ∀ i : Fin m, k ≤ i.val → xPrefix i = 0 := by
    intro i hi
    have hnot : ¬ i.val < p.val := by
      simpa [p] using Nat.not_lt.mpr hi
    simp [xPrefix, householderPrefixPart, hnot]
  obtain ⟨coeff, hcoeff⟩ := hprefixSpan xPrefix hprefixSupport
  have hprevZero :
      ∀ j : Fin k,
        (∑ i : Fin m, L last i * A i (qrPreviousColumn n k hk j)) = 0 := by
    intro j
    let q : Fin (k + 1) :=
      ⟨j.val, Nat.lt_trans j.isLt (Nat.lt_succ_self k)⟩
    have hqne : q ≠ last := by
      intro hq
      have hval : j.val = k := by
        simpa [q, last] using congrArg Fin.val hq
      exact (Nat.ne_of_lt j.isLt) hval
    have h := hL last q
    simpa [q, last, qrLeadingColumn, qrPreviousColumn, idMatrix, hqne] using h
  have hdistrib :
      (∑ i : Fin m, L last i *
        (∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j))) =
      ∑ j : Fin k, coeff j *
        (∑ i : Fin m, L last i * A i (qrPreviousColumn n k hk j)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro i _
    ring
  have hprefixZero :
      (∑ i : Fin m, L last i * xPrefix i) = 0 := by
    calc
      (∑ i : Fin m, L last i * xPrefix i) =
          ∑ i : Fin m, L last i *
            (∑ j : Fin k, coeff j * A i (qrPreviousColumn n k hk j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hcoeff i]
      _ = ∑ j : Fin k, coeff j *
            (∑ i : Fin m, L last i * A i (qrPreviousColumn n k hk j)) :=
        hdistrib
      _ = ∑ j : Fin k, coeff j * 0 := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [hprevZero j]
      _ = 0 := by simp
  have hcurrent :
      (∑ i : Fin m, L last i * x i) = 1 := by
    have h := hL last last
    simpa [x, col, last, qrLeadingColumn, idMatrix] using h
  have hsplit :
      (∑ i : Fin m, L last i * x i) =
        (∑ i : Fin m, L last i * xPrefix i) +
          ∑ i : Fin m, L last i * xTail i := by
    calc
      (∑ i : Fin m, L last i * x i) =
          ∑ i : Fin m, L last i * (xPrefix i + xTail i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have hi :=
              congrFun (householderPrefixPart_add_trailingPart m p x) i
            rw [← hi]
      _ = ∑ i : Fin m,
            (L last i * xPrefix i + L last i * xTail i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ = (∑ i : Fin m, L last i * xPrefix i) +
            ∑ i : Fin m, L last i * xTail i := by
            rw [Finset.sum_add_distrib]
  have htailDot : (∑ i : Fin m, L last i * xTail i) = 1 := by
    nlinarith [hcurrent, hprefixZero, hsplit]
  have hcauchy := vecInnerProduct_sq_le (fun i : Fin m => L last i) xTail
  have hdotSq :
      (∑ i : Fin m, L last i * xTail i) ^ 2 = 1 := by
    rw [htailDot]
    norm_num
  have hone_le :
      1 ≤ vecNorm2Sq (fun i : Fin m => L last i) * vecNorm2Sq xTail := by
    simpa [hdotSq] using hcauchy
  have htail_nonneg : 0 ≤ vecNorm2Sq xTail := vecNorm2Sq_nonneg xTail
  have hmul_le :
      vecNorm2Sq (fun i : Fin m => L last i) * vecNorm2Sq xTail ≤
        K * vecNorm2Sq xTail :=
    mul_le_mul_of_nonneg_right hLnorm htail_nonneg
  have hone_K : 1 ≤ K * vecNorm2Sq xTail := le_trans hone_le hmul_le
  have hone_K_comm : 1 ≤ vecNorm2Sq xTail * K := by
    simpa [mul_comm] using hone_K
  have hdiv : 1 / K ≤ vecNorm2Sq xTail :=
    (div_le_iff₀ hK).2 hone_K_comm
  simpa [householderTrailingNorm2Sq, xTail, x, p] using hdiv

/-- A leading dual norm budget supplies the dimensioned norm-square margin
    required by the stored QR norm-budget route. -/
theorem dim_mul_budget_sq_lt_trailingNorm2Sq_of_leading_dual_norm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (L : Fin (k + 1) → Fin m → ℝ)
    (hL : qrLeadingColumnLeftInverse A hk L)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K budget : ℝ) (hK : 0 < K)
    (hLnorm : vecNorm2Sq (fun i : Fin m =>
      L ⟨k, Nat.lt_succ_self k⟩ i) ≤ K)
    (hbudget : (m : ℝ) * budget ^ 2 < 1 / K) :
    (m : ℝ) * budget ^ 2 <
      householderTrailingNorm2Sq m ⟨k, hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) :=
  lt_of_lt_of_le hbudget
    (householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget
      A hkm hk L hL hprefixSpan K hK hLnorm)

/-- A local left inverse for the leading `(k+1) × (k+1)` block, together
    with a row-norm budget for its last row, supplies the leading-dual
    trailing-norm lower bound.

    This instantiates the padded-dual construction
    `qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock` and uses
    `qrLeadingColumnLeftInverse_padded_row_norm_sq_eq` to turn the local
    inverse row norm into the ambient dual-row norm. -/
theorem householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_row_norm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K : ℝ) (hK : 0 < K)
    (hCnorm : vecNorm2Sq (fun r : Fin (k + 1) =>
      C ⟨k, Nat.lt_succ_self k⟩ r) ≤ K) :
    1 / K ≤
      householderTrailingNorm2Sq m ⟨k, Nat.lt_of_succ_le hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  classical
  let L : Fin (k + 1) → Fin m → ℝ :=
    fun p i => if hi : i.val < k + 1 then C p ⟨i.val, hi⟩ else 0
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hL : qrLeadingColumnLeftInverse A hk L :=
    qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
      A hkm hk C hC
  have hLnorm : vecNorm2Sq (fun i : Fin m => L last i) ≤ K := by
    calc
      vecNorm2Sq (fun i : Fin m => L last i) =
          vecNorm2Sq (fun r : Fin (k + 1) => C last r) := by
            simpa [L] using
              (qrLeadingColumnLeftInverse_padded_row_norm_sq_eq
                (m := m) (k := k) hkm C last)
      _ ≤ K := hCnorm
  exact
    householderTrailingNorm2Sq_ge_inv_leading_dual_norm_budget
      A (Nat.lt_of_succ_le hkm) hk L hL hprefixSpan K hK hLnorm

/-- A local leading-block left inverse with an explicit row-norm budget supplies
    the dimensioned norm-square margin required by the stored QR route. -/
theorem dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_row_norm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K budget : ℝ) (hK : 0 < K)
    (hCnorm : vecNorm2Sq (fun r : Fin (k + 1) =>
      C ⟨k, Nat.lt_succ_self k⟩ r) ≤ K)
    (hbudget : (m : ℝ) * budget ^ 2 < 1 / K) :
    (m : ℝ) * budget ^ 2 <
      householderTrailingNorm2Sq m ⟨k, Nat.lt_of_succ_le hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) :=
  lt_of_lt_of_le hbudget
    (householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_row_norm_budget
      A hkm hk C hC hprefixSpan K hK hCnorm)

/-- A Frobenius-norm budget for a local leading-block left inverse supplies the
    local inverse row-norm budget used by the quantitative QR route. -/
theorem householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_frobNorm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K : ℝ) (hK : 0 < K)
    (hCfrob : frobNorm C ^ 2 ≤ K) :
    1 / K ≤
      householderTrailingNorm2Sq m ⟨k, Nat.lt_of_succ_le hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  have hCnorm : vecNorm2Sq (fun r : Fin (k + 1) => C last r) ≤ K :=
    (vecNorm2Sq_row_le_frobNorm_sq C last).trans hCfrob
  exact
    householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_row_norm_budget
      A hkm hk C hC hprefixSpan K hK hCnorm

/-- A Frobenius-norm budget for the local leading-block inverse supplies the
    dimensioned norm-square margin required by the stored QR route. -/
theorem dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_frobNorm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K budget : ℝ) (hK : 0 < K)
    (hCfrob : frobNorm C ^ 2 ≤ K)
    (hbudget : (m : ℝ) * budget ^ 2 < 1 / K) :
    (m : ℝ) * budget ^ 2 <
      householderTrailingNorm2Sq m ⟨k, Nat.lt_of_succ_le hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) :=
  lt_of_lt_of_le hbudget
    (householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_frobNorm_budget
      A hkm hk C hC hprefixSpan K hK hCfrob)

/-- An infinity-norm budget for a local leading-block left inverse supplies the
    Frobenius budget used by the quantitative QR route. -/
theorem householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_infNorm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K : ℝ) (hK : 0 < K)
    (hCinf : ((k + 1 : ℕ) : ℝ) * infNorm C ^ 2 ≤ K) :
    1 / K ≤
      householderTrailingNorm2Sq m ⟨k, Nat.lt_of_succ_le hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  have hCfrob : frobNorm C ^ 2 ≤ K :=
    (frobNorm_sq_le_nat_mul_infNorm_sq C).trans hCinf
  exact
    householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_frobNorm_budget
      A hkm hk C hC hprefixSpan K hK hCfrob

/-- An infinity-norm budget for the local leading-block inverse supplies the
    dimensioned norm-square margin required by the stored QR route. -/
theorem dim_mul_budget_sq_lt_trailingNorm2Sq_of_leadingBlock_leftInverse_infNorm_budget
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (C : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hC : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) C)
    (hprefixSpan : qrPrefixSupportSpannedByPreviousColumns A hk)
    (K budget : ℝ) (hK : 0 < K)
    (hCinf : ((k + 1 : ℕ) : ℝ) * infNorm C ^ 2 ≤ K)
    (hbudget : (m : ℝ) * budget ^ 2 < 1 / K) :
    (m : ℝ) * budget ^ 2 <
      householderTrailingNorm2Sq m ⟨k, Nat.lt_of_succ_le hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) :=
  lt_of_lt_of_le hbudget
    (householderTrailingNorm2Sq_ge_inv_leadingBlock_leftInverse_infNorm_budget
      A hkm hk C hC hprefixSpan K hK hCinf)

/-- Concrete leading-block witnesses imply that the active trailing part of the
    current pivot column contains a nonzero entry.

    This combines the coefficient-matrix prefix-span bridge with the
    leading-column left-inverse independence bridge. -/
theorem exists_active_trailing_entry_ne_of_leading_witnesses
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k ≤ m) (hk : k < n)
    (C : Fin k → Fin k → ℝ)
    (L : Fin (k + 1) → Fin m → ℝ)
    (hC : qrPrefixBasisCoefficientMatrix A hkm hk C)
    (hL : qrLeadingColumnLeftInverse A hk L)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    ∃ i : Fin m, k ≤ i.val ∧ A i ⟨k, hk⟩ ≠ 0 := by
  classical
  exact
    exists_active_trailing_entry_ne_of_column_notInPreviousSpan
      A hk
      (qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse A hk L hL)
      (qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix
        A hkm hk C hC hlowerPrev)

/-- Concrete leading-block witnesses supply the positive trailing norm needed
    by the Householder sign-choice nonbreakdown bridge. -/
theorem householderTrailingNorm2Sq_pos_of_leading_witnesses
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (C : Fin k → Fin k → ℝ)
    (L : Fin (k + 1) → Fin m → ℝ)
    (hC : qrPrefixBasisCoefficientMatrix A (le_of_lt hkm) hk C)
    (hL : qrLeadingColumnLeftInverse A hk L)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    0 < householderTrailingNorm2Sq m ⟨k, hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  classical
  have hactive :
      ∃ i : Fin m, (⟨k, hkm⟩ : Fin m).val ≤ i.val ∧
        (fun i : Fin m => A i ⟨k, hk⟩) i ≠ 0 := by
    simpa using
      exists_active_trailing_entry_ne_of_leading_witnesses
        A (le_of_lt hkm) hk C L hC hL hlowerPrev
  exact
    householderTrailingNorm2Sq_pos_of_exists_ne
      m ⟨k, hkm⟩ (fun i : Fin m => A i ⟨k, hk⟩) hactive

/-- Concrete leading-block witnesses supply positive active-block mass. -/
theorem householderActiveBlockNorm2Sq_pos_of_leading_witnesses
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (C : Fin k → Fin k → ℝ)
    (L : Fin (k + 1) → Fin m → ℝ)
    (hC : qrPrefixBasisCoefficientMatrix A (le_of_lt hkm) hk C)
    (hL : qrLeadingColumnLeftInverse A hk L)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    0 < householderActiveBlockNorm2Sq
      ⟨k, hkm⟩ ⟨k, hk⟩ A := by
  classical
  obtain ⟨i, hi, hne⟩ :=
    exists_active_trailing_entry_ne_of_leading_witnesses
      A (le_of_lt hkm) hk C L hC hL hlowerPrev
  exact
    householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
      ⟨k, hkm⟩ ⟨k, hk⟩ A
      ⟨⟨k, hk⟩, le_rfl, i, by simpa using hi, hne⟩

/-- Local left inverses for the previous and leading QR blocks supply a
    nonzero active trailing pivot entry.

    This composes the two `IsLeftInverse` adapters with the concrete
    leading-witness nonbreakdown theorem.  It still assumes the local block
    inverse witnesses; it does not prove them from rank or determinant data. -/
theorem exists_active_trailing_entry_ne_of_leading_block_leftInverses
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (Cprev : Fin k → Fin k → ℝ)
    (Dlead : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hCprev : IsLeftInverse k
      (qrPreviousLeadingBlockTranspose A (le_trans (Nat.le_succ k) hkm) hk)
      Cprev)
    (hDlead : IsLeftInverse (k + 1) (qrLeadingBlock A hkm hk) Dlead)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    ∃ i : Fin m, k ≤ i.val ∧ A i ⟨k, hk⟩ ≠ 0 := by
  classical
  let L : Fin (k + 1) → Fin m → ℝ :=
    fun p i => if hi : i.val < k + 1 then Dlead p ⟨i.val, hi⟩ else 0
  have hC :
      qrPrefixBasisCoefficientMatrix A (le_trans (Nat.le_succ k) hkm) hk Cprev :=
    qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose
      A (le_trans (Nat.le_succ k) hkm) hk Cprev hCprev
  have hL : qrLeadingColumnLeftInverse A hk L :=
    qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
      A hkm hk Dlead hDlead
  exact
    exists_active_trailing_entry_ne_of_leading_witnesses
      A (le_trans (Nat.le_succ k) hkm) hk Cprev L hC hL hlowerPrev

/-- Local left inverses for the previous and leading QR blocks supply the
    positive trailing norm needed by the sign-choice nonbreakdown bridge. -/
theorem householderTrailingNorm2Sq_pos_of_leading_block_leftInverses
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (Cprev : Fin k → Fin k → ℝ)
    (Dlead : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hCprev : IsLeftInverse k
      (qrPreviousLeadingBlockTranspose A (le_of_lt hkm) hk) Cprev)
    (hDlead : IsLeftInverse (k + 1)
      (qrLeadingBlock A (Nat.succ_le_iff.mpr hkm) hk) Dlead)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    0 < householderTrailingNorm2Sq m ⟨k, hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  classical
  have hactive :
      ∃ i : Fin m, (⟨k, hkm⟩ : Fin m).val ≤ i.val ∧
        (fun i : Fin m => A i ⟨k, hk⟩) i ≠ 0 := by
    simpa using
      exists_active_trailing_entry_ne_of_leading_block_leftInverses
        A (Nat.succ_le_iff.mpr hkm) hk Cprev Dlead hCprev hDlead hlowerPrev
  exact
    householderTrailingNorm2Sq_pos_of_exists_ne
      m ⟨k, hkm⟩ (fun i : Fin m => A i ⟨k, hk⟩) hactive

/-- Local left inverses for the previous and leading QR blocks supply positive
    active-block mass. -/
theorem householderActiveBlockNorm2Sq_pos_of_leading_block_leftInverses
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (Cprev : Fin k → Fin k → ℝ)
    (Dlead : Fin (k + 1) → Fin (k + 1) → ℝ)
    (hCprev : IsLeftInverse k
      (qrPreviousLeadingBlockTranspose A (le_of_lt hkm) hk) Cprev)
    (hDlead : IsLeftInverse (k + 1)
      (qrLeadingBlock A (Nat.succ_le_iff.mpr hkm) hk) Dlead)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    0 < householderActiveBlockNorm2Sq
      ⟨k, hkm⟩ ⟨k, hk⟩ A := by
  classical
  obtain ⟨i, hi, hne⟩ :=
    exists_active_trailing_entry_ne_of_leading_block_leftInverses
      A (Nat.succ_le_iff.mpr hkm) hk Cprev Dlead hCprev hDlead hlowerPrev
  exact
    householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
      ⟨k, hkm⟩ ⟨k, hk⟩ A
      ⟨⟨k, hk⟩, le_rfl, i, by simpa using hi, hne⟩

/-- Determinant/rank form of the leading-block nonbreakdown bridge.

    Nonzero determinants for the previous transposed leading block and the
    current leading block produce the local left-inverse witnesses needed by
    `exists_active_trailing_entry_ne_of_leading_block_leftInverses`.  The
    theorem still keeps the QR lower-zero shape visible. -/
theorem exists_active_trailing_entry_ne_of_leading_block_det_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k + 1 ≤ m) (hk : k < n)
    (hdetPrev : Matrix.det
      (qrPreviousLeadingBlockTranspose A
        (le_trans (Nat.le_succ k) hkm) hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : Matrix.det
      (qrLeadingBlock A hkm hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    ∃ i : Fin m, k ≤ i.val ∧ A i ⟨k, hk⟩ ≠ 0 := by
  classical
  obtain ⟨Cprev, hCprev⟩ :=
    exists_isLeftInverse_of_det_ne_zero k
      (qrPreviousLeadingBlockTranspose A
        (le_trans (Nat.le_succ k) hkm) hk)
      hdetPrev
  obtain ⟨Dlead, hDlead⟩ :=
    exists_isLeftInverse_of_det_ne_zero (k + 1)
      (qrLeadingBlock A hkm hk) hdetLead
  exact
    exists_active_trailing_entry_ne_of_leading_block_leftInverses
      A hkm hk Cprev Dlead hCprev hDlead hlowerPrev

/-- Determinant/rank form of the positive trailing-norm bridge. -/
theorem householderTrailingNorm2Sq_pos_of_leading_block_det_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (hdetPrev : Matrix.det
      (qrPreviousLeadingBlockTranspose A (le_of_lt hkm) hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : Matrix.det
      (qrLeadingBlock A (Nat.succ_le_iff.mpr hkm) hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    0 < householderTrailingNorm2Sq m ⟨k, hkm⟩
        (fun i : Fin m => A i ⟨k, hk⟩) := by
  classical
  have hactive :
      ∃ i : Fin m, (⟨k, hkm⟩ : Fin m).val ≤ i.val ∧
        (fun i : Fin m => A i ⟨k, hk⟩) i ≠ 0 := by
    simpa using
      exists_active_trailing_entry_ne_of_leading_block_det_ne_zero
        A (Nat.succ_le_iff.mpr hkm) hk hdetPrev hdetLead hlowerPrev
  exact
    householderTrailingNorm2Sq_pos_of_exists_ne
      m ⟨k, hkm⟩ (fun i : Fin m => A i ⟨k, hk⟩) hactive

/-- Determinant/rank form of the positive active-block mass bridge. -/
theorem householderActiveBlockNorm2Sq_pos_of_leading_block_det_ne_zero
    {m n k : ℕ}
    (A : Fin m → Fin n → ℝ) (hkm : k < m) (hk : k < n)
    (hdetPrev : Matrix.det
      (qrPreviousLeadingBlockTranspose A (le_of_lt hkm) hk :
        Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : Matrix.det
      (qrLeadingBlock A (Nat.succ_le_iff.mpr hkm) hk :
        Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ (i : Fin m) (j : Fin k), k ≤ i.val →
      A i (qrPreviousColumn n k hk j) = 0) :
    0 < householderActiveBlockNorm2Sq
      ⟨k, hkm⟩ ⟨k, hk⟩ A := by
  classical
  obtain ⟨i, hi, hne⟩ :=
    exists_active_trailing_entry_ne_of_leading_block_det_ne_zero
      A (Nat.succ_le_iff.mpr hkm) hk hdetPrev hdetLead hlowerPrev
  exact
    householderActiveBlockNorm2Sq_pos_of_exists_active_entry_ne
      ⟨k, hkm⟩ ⟨k, hk⟩ A
      ⟨⟨k, hk⟩, le_rfl, i, by simpa using hi, hne⟩

/-- Sequence form of the determinant/rank active-block mass bridge.

For each stored QR stage `k`, nonsingular previous/current leading blocks plus
the stored lower-zero shape imply positive active-block mass at the raw stage.
This is the direct nonbreakdown field required by the Cox--Higham
raw-to-swapped active-block sequence theorem. -/
theorem householderActiveBlockNorm2Sq_pos_sequence_of_leading_block_det_ne_zero
    {m n : ℕ} (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_of_lt (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0) :
    ∀ k (hk : k < n),
      0 < householderActiveBlockNorm2Sq
        ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ (A_hat k) := by
  intro k hk
  exact
    householderActiveBlockNorm2Sq_pos_of_leading_block_det_ne_zero
      (A_hat k) (lt_of_lt_of_le hk hmn) hk
      (hdetPrev k hk) (hdetLead k hk) (hlowerPrev k hk)

/-- Cox--Higham swapped active max-pivot sequence with active-block
nonbreakdown supplied by leading-block determinant data.

This composes the determinant/lower-zero active-mass bridge with the swapped
active max-pivot route.  The exact sequence still exposes the sorting policy,
stage monotonicity, determinant/lower-zero hypotheses, and initial block bound,
but no longer needs a separate raw-stage active-block-mass hypothesis. -/
theorem coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_leading_block_det_ne_zero
    {m n : ℕ} (hmn : n ≤ m) {steps : ℕ} (hsteps : steps ≤ n)
    (Araw Astage : ℕ → Fin m → Fin n → ℝ)
    (p : ℕ → Fin m) (pivotCol : ℕ → Fin n)
    (B0 : ℝ)
    (hinitBlock : ∀ i : Fin m, ∀ l : Fin n, |Astage 0 i l| ≤ B0)
    (hB0 : 0 ≤ B0)
    (hstep : ∀ t : ℕ, t < steps →
      Astage (t + 1) =
        exactSignedPivotHouseholderPanelStep m n (p t) (pivotCol t) (Astage t))
    (hpMono : ∀ u t : ℕ, u ≤ t → t ≤ steps → (p u).val ≤ (p t).val)
    (hkMono : ∀ u t : ℕ, u ≤ t → t ≤ steps →
      (pivotCol u).val ≤ (pivotCol t).val)
    (hstageRow : ∀ t : ℕ, t < steps → (p t).val = t)
    (hstageCol : ∀ t : ℕ, t < steps → (pivotCol t).val = t)
    (hsorted : ∀ t : ℕ, t < steps →
      Astage t =
        householderSwapColumns (Araw t) (pivotCol t)
          (householderActiveMaxPivotColumn (p t) (pivotCol t) (Araw t)))
    (hdetPrev : ∀ t (ht : t < steps),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (Araw t)
          (le_of_lt (lt_of_lt_of_le (lt_of_lt_of_le ht hsteps) hmn))
          (lt_of_lt_of_le ht hsteps) :
          Matrix (Fin t) (Fin t) ℝ) ≠ 0)
    (hdetLead : ∀ t (ht : t < steps),
      Matrix.det
        (qrLeadingBlock (Araw t)
          (Nat.succ_le_iff.mpr
            (lt_of_lt_of_le (lt_of_lt_of_le ht hsteps) hmn))
          (lt_of_lt_of_le ht hsteps) :
          Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ t (ht : t < steps) (i : Fin m) (j : Fin t),
      t ≤ i.val →
        Araw t i (qrPreviousColumn n t (lt_of_lt_of_le ht hsteps) j) = 0) :
    ∀ t : ℕ, t ≤ steps →
      ∀ i : Fin m, (p t).val ≤ i.val →
        ∀ l : Fin n, (pivotCol t).val ≤ l.val →
          |Astage t i l| ≤ coxHighamActiveRowGrowthFactor m ^ t * B0 := by
  refine
    coxHigham_exactSignedPivotPanel_sequence_active_block_bound_of_initial_block_bound_of_swapped_active_max_pivot_of_raw_active_block_norm_pos
      steps Araw Astage p pivotCol B0 hinitBlock hB0 hstep hpMono hkMono
      hsorted ?_
  intro t ht
  have hk : t < n := lt_of_lt_of_le ht hsteps
  have hkm : t < m := lt_of_lt_of_le hk hmn
  have hrow : p t = ⟨t, hkm⟩ := by
    apply Fin.ext
    simpa using hstageRow t ht
  have hcol : pivotCol t = ⟨t, hk⟩ := by
    apply Fin.ext
    simpa using hstageCol t ht
  have hpos :
      0 < householderActiveBlockNorm2Sq
        ⟨t, hkm⟩ ⟨t, hk⟩ (Araw t) :=
    householderActiveBlockNorm2Sq_pos_of_leading_block_det_ne_zero
      (Araw t) hkm hk (hdetPrev t ht) (hdetLead t ht) (hlowerPrev t ht)
  simpa [hrow, hcol] using hpos

/-- Stored trailing QR nonzero diagonal from a prefix-span nonbreakdown
    invariant and a square-root trailing-norm pivot budget.

    This is the next rank-route bridge after the scalar lower-bound lemmas:
    the positive trailing norm is proved from column independence plus the
    prefix-span invariant, while the per-pivot floating-point budget
    `budget < |alpha|` is obtained from the explicit square-root lower bound. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hnotspan : ∀ k (hk : k < n),
      qrColumnNotInPreviousSpan (A_hat k) hk)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  have htrailingPos : ∀ k (hk : k < n),
      0 < householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩) := by
    intro k hk
    exact
      householderTrailingNorm2Sq_pos_of_column_notInPreviousSpan
        (A_hat k) (lt_of_lt_of_le hk hmn) hk
        (hnotspan k hk) (hprefixSpan k hk)
  have hbudgetDiag : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ < |alpha k| := by
    intro k hk
    exact
      budget_lt_abs_alpha_of_lt_sqrt_trailingNorm2Sq
        m ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun i => A_hat k i ⟨k, hk⟩) (alpha k)
        (householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩)
        (halpha k hk) (hbudgetSqrt k hk)
  exact
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_trailingNorm_pos_mul_nonpos
      fp hmn A_hat alpha hm hStep halpha htrailingPos hsign hbudgetDiag

/-- Stored trailing QR nonzero diagonal from a prefix-span nonbreakdown
    invariant and a concrete active-entry pivot budget.

    This wrapper removes the square-root expression from the budget side
    condition.  It is still a visible quantitative assumption: for every pivot,
    the compact-update diagonal budget must be strictly below the magnitude of
    some active trailing entry in the current pivot column. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_active_entry_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hnotspan : ∀ k (hk : k < n),
      qrColumnNotInPreviousSpan (A_hat k) hk)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetEntry : ∀ k (hk : k < n),
      ∃ i : Fin m, k ≤ i.val ∧
        householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩ < |A_hat k i ⟨k, hk⟩|) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha hnotspan hprefixSpan hsign ?_
  intro k hk
  rcases hbudgetEntry k hk with ⟨i, hki, hbudget⟩
  exact
    budget_lt_sqrt_householderTrailingNorm2Sq_of_lt_abs_active_entry
      m ⟨k, lt_of_lt_of_le hk hmn⟩ i
      (fun a => A_hat k a ⟨k, hk⟩)
      (householderCompactComponentBudget fp m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
        (fun a => A_hat k a ⟨k, hk⟩)
        ⟨k, lt_of_lt_of_le hk hmn⟩)
      hki hbudget

/-- Stored trailing QR nonzero diagonal from prefix-span nonbreakdown and a
    dimensioned trailing-norm budget.

    This wrapper replaces the square-root side condition by the stronger but
    often more conditioning-friendly margin
    `m * budget_k^2 < ||A_k(k:m,k)||_2^2`.  The shared Householder-spec bridge
    converts that norm-square margin directly into the square-root budget
    consumed by the stored QR nonbreakdown theorem. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hnotspan : ∀ k (hk : k < n),
      qrColumnNotInPreviousSpan (A_hat k) hk)
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetNormSq : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩)) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha hnotspan hprefixSpan hsign ?_
  intro k hk
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let v :=
    householderTrailingActiveVector m p
      (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
  let beta := householderBetaSpec m v
  let budget :=
    householderCompactComponentBudget fp m v beta
      (fun a => A_hat k a ⟨k, hk⟩) p
  have hbudget_nonneg : 0 ≤ budget := by
    simpa [budget, beta, v, p] using
      householderCompactComponentBudget_nonneg fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) hm p
  have hmargin :
      (m : ℝ) * budget ^ 2 <
        householderTrailingNorm2Sq m p
          (fun a => A_hat k a ⟨k, hk⟩) := by
    simpa [budget, beta, v, p] using hbudgetNormSq k hk
  simpa [budget, beta, v, p] using
    budget_lt_sqrt_householderTrailingNorm2Sq_of_dim_mul_budget_sq_lt_trailingNorm2Sq
      m p (fun a => A_hat k a ⟨k, hk⟩) budget
      hbudget_nonneg hmargin

/-- Stored trailing QR nonzero diagonal from prefix-span and a bounded
    leading-column dual.

    This is the conditioning-oriented version of the norm-square budget route:
    a dual row for the current leading column whose squared norm is at most
    `K k`, together with
    `m * budget_k^2 < 1 / K k`, supplies the dimensioned trailing-norm margin
    used by
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget`.
    The theorem still exposes the dual and its norm budget; it does not prove
    them from a concrete inverse or condition number. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hL : ∀ k (hk : k < n),
      qrLeadingColumnLeftInverse (A_hat k) hk (L k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hLnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun i : Fin m =>
        L k hk ⟨k, Nat.lt_succ_self k⟩ i) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_trailingNorm2Sq_budget
      fp hmn A_hat alpha hm hStep halpha ?_ hprefixSpan hsign ?_
  · intro k hk
    exact qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse
      (A_hat k) hk (L k hk) (hL k hk)
  · intro k hk
    let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
    let v :=
      householderTrailingActiveVector m p
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    let beta := householderBetaSpec m v
    let budget :=
      householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a ⟨k, hk⟩) p
    have hbudget :
        (m : ℝ) * budget ^ 2 < 1 / K k := by
      simpa [budget, beta, v, p] using hbudgetDual k hk
    simpa [budget, beta, v, p] using
      dim_mul_budget_sq_lt_trailingNorm2Sq_of_leading_dual_norm_budget
        (A_hat k) (lt_of_lt_of_le hk hmn) hk (L k hk)
        (hL k hk) (hprefixSpan k hk) (K k) budget
        (hK k hk) (hLnorm k hk) hbudget

/-- Stored trailing QR nonzero diagonal from prefix-span and a local
    leading-block left inverse with a row-norm budget.

    This removes the ambient dual witness from
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget`:
    the dual is the zero-padded row of the local leading-block left inverse.
    The theorem still exposes the local left inverse and its last-row norm
    budget. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCnorm : ∀ k (hk : k < n),
      vecNorm2Sq (fun r : Fin (k + 1) =>
        C k hk ⟨k, Nat.lt_succ_self k⟩ r) ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  let L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ :=
    fun k hk p i =>
      if hi : i.val < k + 1 then C k hk p ⟨i.val, hi⟩ else 0
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leading_dual_norm_budget
      fp hmn A_hat alpha L K hm hStep halpha ?_ hprefixSpan hK ?_
      hsign hbudgetDual
  · intro k hk
    exact
      qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
        (A_hat k) (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn))
        hk (C k hk) (hC k hk)
  · intro k hk
    let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
    calc
      vecNorm2Sq (fun i : Fin m => L k hk last i) =
          vecNorm2Sq (fun r : Fin (k + 1) => C k hk last r) := by
            simpa [L, last] using
              (qrLeadingColumnLeftInverse_padded_row_norm_sq_eq
                (m := m) (k := k)
                (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn))
                (C k hk) last)
      _ ≤ K k := hCnorm k hk

/-- Stored trailing QR nonzero diagonal from prefix-span and a local
    leading-block inverse Frobenius-norm budget.

    This is the inverse-norm version of the row-budget theorem: the last row of
    the local inverse is bounded by the whole local inverse's Frobenius norm. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCfrob : ∀ k (hk : k < n), frobNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_norm_budget
      fp hmn A_hat alpha C K hm hStep halpha hC hprefixSpan hK ?_
      hsign hbudgetDual
  intro k hk
  let last : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
  exact (vecNorm2Sq_row_le_frobNorm_sq (C k hk) last).trans (hCfrob k hk)

/-- Stored trailing QR nonzero diagonal from prefix-span and a local
    leading-block inverse infinity-norm budget.

    The shared norm bridge `frobNorm_sq_le_nat_mul_infNorm_sq` turns the
    per-prefix infinity-norm estimate into the Frobenius budget required by the
    stored-loop theorem. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_infNorm_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (C : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (K : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hC : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (Nat.succ_le_iff.mpr (lt_of_lt_of_le hk hmn)) hk)
        (C k hk))
    (hprefixSpan : ∀ k (hk : k < n),
      qrPrefixSupportSpannedByPreviousColumns (A_hat k) hk)
    (hK : ∀ k (_hk : k < n), 0 < K k)
    (hCinf : ∀ k (hk : k < n),
      ((k + 1 : ℕ) : ℝ) * infNorm (C k hk) ^ 2 ≤ K k)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetDual : ∀ k (hk : k < n),
      (m : ℝ) *
          (householderCompactComponentBudget fp m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
            (householderBetaSpec m
              (householderTrailingActiveVector m
                ⟨k, lt_of_lt_of_le hk hmn⟩
                (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
            (fun a => A_hat k a ⟨k, hk⟩)
            ⟨k, lt_of_lt_of_le hk hmn⟩) ^ 2 <
        1 / K k) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_leadingBlock_leftInverse_frobNorm_budget
      fp hmn A_hat alpha C K hm hStep halpha hC hprefixSpan hK ?_
      hsign hbudgetDual
  intro k hk
  exact (frobNorm_sq_le_nat_mul_infNorm_sq (C k hk)).trans (hCinf k hk)

/-- Stored trailing QR nonzero diagonal from concrete leading-block witnesses
    and a square-root trailing-norm pivot budget.

    Compared with
    `fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget`,
    this theorem no longer assumes the abstract prefix-span and
    column-independence invariants.  It derives them from explicit
    leading-block coefficient and left-inverse witnesses plus the QR lower-zero
    shape.  The quantitative square-root budget lower bound remains visible. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (C : ∀ k, k < n → Fin k → Fin k → ℝ)
    (L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ)
    (hC : ∀ k (hk : k < n),
      qrPrefixBasisCoefficientMatrix (A_hat k)
        (le_trans (Nat.le_of_lt hk) hmn) hk (C k hk))
    (hL : ∀ k (hk : k < n),
      qrLeadingColumnLeftInverse (A_hat k) hk (L k hk))
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_span_nonbreakdown_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha ?_ ?_ hsign hbudgetSqrt
  · intro k hk
    exact
      qrColumnNotInPreviousSpan_of_leadingColumnLeftInverse
        (A_hat k) hk (L k hk) (hL k hk)
  · intro k hk
    exact
      qrPrefixSupportSpannedByPreviousColumns_of_prefixBasisCoefficientMatrix
        (A_hat k) (le_trans (Nat.le_of_lt hk) hmn) hk
        (C k hk) (hC k hk) (hlowerPrev k hk)

/-- Stored trailing QR nonzero diagonal from local leading-block left inverses
    and a square-root trailing-norm pivot budget.

    This version composes the local `IsLeftInverse` adapters directly into the
    stored-loop nonbreakdown theorem.  The existence of the local inverses and
    the quantitative square-root budget lower bound remain explicit. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (Cprev : ∀ k, k < n → Fin k → Fin k → ℝ)
    (Dlead : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ)
    (hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk))
    (hDlead : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk)
        (Dlead k hk))
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  let L : ∀ k, k < n → Fin (k + 1) → Fin m → ℝ :=
    fun k hk p i =>
      if hi : i.val < k + 1 then Dlead k hk p ⟨i.val, hi⟩ else 0
  refine
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_witnesses_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha Cprev L ?_ ?_
      hlowerPrev hsign hbudgetSqrt
  · intro k hk
    exact
      qrPrefixBasisCoefficientMatrix_of_leftInverse_previousLeadingBlockTranspose
        (A_hat k) (le_trans (Nat.le_of_lt hk) hmn) hk
        (Cprev k hk) (hCprev k hk)
  · intro k hk
    exact
      qrLeadingColumnLeftInverse_of_leftInverse_leadingBlock
        (A_hat k) (le_trans (Nat.succ_le_of_lt hk) hmn) hk
        (Dlead k hk) (hDlead k hk)

/-- Stored trailing QR nonzero diagonal from nonsingular local leading blocks
    and a square-root trailing-norm pivot budget.

    This determinant/rank-style variant removes the explicit local
    `IsLeftInverse` witnesses from the previous theorem.  The remaining visible
    algebraic assumptions are exactly the nonzero determinants of the local
    leading blocks, the QR lower-zero shape, sign choice, and the quantitative
    floating-point square-root budget. -/
theorem fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_det_ne_zero_sqrt_budget
    {m n : ℕ}
    (fp : FPModel) (hmn : n ≤ m)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hStep : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun i => A_hat k i ⟨k, hk⟩))
    (hdetPrev : ∀ k (hk : k < n),
      Matrix.det
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk :
          Matrix (Fin k) (Fin k) ℝ) ≠ 0)
    (hdetLead : ∀ k (hk : k < n),
      Matrix.det
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk :
          Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ) ≠ 0)
    (hlowerPrev : ∀ k (hk : k < n) (i : Fin m) (j : Fin k),
      k ≤ i.val → A_hat k i (qrPreviousColumn n k hk j) = 0)
    (hsign : ∀ k (hk : k < n),
      alpha k * A_hat k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ ≤ 0)
    (hbudgetSqrt : ∀ k (hk : k < n),
      householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a ⟨k, hk⟩)
          ⟨k, lt_of_lt_of_le hk hmn⟩ <
        Real.sqrt
          (householderTrailingNorm2Sq m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun i => A_hat k i ⟨k, hk⟩))) :
    ∀ i : Fin n, A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ i ≠ 0 := by
  classical
  let Cprev : ∀ k, k < n → Fin k → Fin k → ℝ :=
    fun k hk => Classical.choose
      (exists_isLeftInverse_of_det_ne_zero k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (hdetPrev k hk))
  let Dlead : ∀ k, k < n → Fin (k + 1) → Fin (k + 1) → ℝ :=
    fun k hk => Classical.choose
      (exists_isLeftInverse_of_det_ne_zero (k + 1)
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk)
        (hdetLead k hk))
  have hCprev : ∀ k (hk : k < n),
      IsLeftInverse k
        (qrPreviousLeadingBlockTranspose (A_hat k)
          (le_trans (Nat.le_of_lt hk) hmn) hk)
        (Cprev k hk) := by
    intro k hk
    exact
      Classical.choose_spec
        (exists_isLeftInverse_of_det_ne_zero k
          (qrPreviousLeadingBlockTranspose (A_hat k)
            (le_trans (Nat.le_of_lt hk) hmn) hk)
          (hdetPrev k hk))
  have hDlead : ∀ k (hk : k < n),
      IsLeftInverse (k + 1)
        (qrLeadingBlock (A_hat k)
          (le_trans (Nat.succ_le_of_lt hk) hmn) hk)
        (Dlead k hk) := by
    intro k hk
    exact
      Classical.choose_spec
        (exists_isLeftInverse_of_det_ne_zero (k + 1)
          (qrLeadingBlock (A_hat k)
            (le_trans (Nat.succ_le_of_lt hk) hmn) hk)
          (hdetLead k hk))
  exact
    fl_householderStoredTrailingPanel_sequence_diag_nonzero_of_leading_block_leftInverses_sqrt_budget
      fp hmn A_hat alpha hm hStep halpha Cprev Dlead
      hCprev hDlead hlowerPrev hsign hbudgetSqrt

/-- A concrete trailing Householder stored step satisfies the source-faithful
    columnwise perturbation contract.

    This discharges the preservation and pivot-zeroing hypotheses of
    `fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget`
    from the exact trailing-reflector algebra.  The remaining visible
    hypotheses are the pre-step lower-zero invariant and the compact
    budget-domination inequalities. -/
theorem fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget
    (fp : FPModel) (m n k : ℕ)
    (p : Fin m) (col : Fin n)
    (hp : p.val = k) (hcol : col.val = k)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (alpha : ℝ) {c : ℝ}
    (hm : gammaValid fp m) (hc : 0 ≤ c)
    (halpha :
      alpha * alpha =
        householderTrailingNorm2Sq m p (fun a => A a col))
    (hden :
      (∑ i : Fin m,
        householderTrailingActiveVector m p (fun a => A a col) alpha i *
          householderTrailingActiveVector m p (fun a => A a col) alpha i) ≠ 0)
    (hlower : ∀ (i : Fin m) (j : Fin n),
      j.val < k → j.val < i.val → A i j = 0)
    (hA_budget : ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m p (fun a => A a col) alpha)
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun a => A a col) alpha))
          (fun a => A a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A i j))
    (hb_budget :
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m p (fun a => A a col) alpha)
          (householderBetaSpec m
            (householderTrailingActiveVector m p (fun a => A a col) alpha))
          b i) ≤
        c * vecNorm2 b) :
    HouseholderColumnwisePanelAppError m n
      (householder m
        (householderTrailingActiveVector m p (fun a => A a col) alpha)
        (householderBetaSpec m
          (householderTrailingActiveVector m p (fun a => A a col) alpha)))
      A
      (fl_householderStoredPanelStep fp m n k
        (householderTrailingActiveVector m p (fun a => A a col) alpha)
        (householderBetaSpec m
          (householderTrailingActiveVector m p (fun a => A a col) alpha))
        A)
      b
      (fl_householderStoredRhsStep fp m k
        (householderTrailingActiveVector m p (fun a => A a col) alpha)
        (householderBetaSpec m
          (householderTrailingActiveVector m p (fun a => A a col) alpha))
        b)
      c := by
  classical
  let x : Fin m → ℝ := fun a => A a col
  let v : Fin m → ℝ := householderTrailingActiveVector m p x alpha
  let β : ℝ := householderBetaSpec m v
  have hvprefix : ∀ i : Fin m, i.val < k → v i = 0 := by
    intro i hi
    have hip : i.val < p.val := by
      simpa [hp] using hi
    simpa [v, x] using
      householderTrailingActiveVector_zero_prefix m p x alpha i hip
  have hβ : β * (∑ i : Fin m, v i * v i) = 2 := by
    have hsum_ne : (∑ i : Fin m, v i * v i) ≠ 0 := by
      simpa [v, x] using hden
    dsimp [β, householderBetaSpec]
    exact div_mul_cancel₀ 2 hsum_ne
  have horth : IsOrthogonal m (householder m v β) :=
    householder_orthogonal m v β hβ
  have hcompleted : ∀ j : Fin n, j.val < k →
      ∀ i : Fin m, matMulVec m (householder m v β)
        (fun a => A a j) i = A i j := by
    intro j hj i
    let xcol : Fin m → ℝ := fun a => A a j
    have hsupport : ∀ a : Fin m, k ≤ a.val → xcol a = 0 := by
      intro a ha
      have hja : j.val < a.val := lt_of_lt_of_le hj ha
      exact hlower a j hj hja
    have hpreserve :
        matMulVec m (householder m v β) xcol = xcol :=
      matMulVec_householder_eq_self_of_zero_prefix_support
        m k v xcol β hvprefix hsupport
    exact congrFun hpreserve i
  have hpivot : ∀ j : Fin n, j.val = k →
      ∀ i : Fin m, k < i.val →
        matMulVec m (householder m v β) (fun a => A a j) i = 0 := by
    intro j hj i hi
    have hjcol : j = col := Fin.ext (hj.trans hcol.symm)
    subst j
    have hpi : p.val < i.val := by
      simpa [hp] using hi
    simpa [v, β, x] using
      matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
        m p x alpha halpha hden i hpi
  have hrhs_prefix : ∀ i : Fin m, i.val < k →
      matMulVec m (householder m v β) b i = b i := by
    intro i hi
    exact matMulVec_householder_eq_self_of_zero_prefix
      m k v b β hvprefix i hi
  change
    HouseholderColumnwisePanelAppError m n (householder m v β) A
      (fl_householderStoredPanelStep fp m n k v β A)
      b (fl_householderStoredRhsStep fp m k v β b) c
  exact
    fl_householderStoredPanelStep_HouseholderColumnwisePanelAppError_of_budget
      fp m n k v β A b horth hm hc hcompleted hpivot hrhs_prefix
      (by simpa [v, β, x] using hA_budget)
      (by simpa [v, β, x] using hb_budget)

/-- Stored trailing Householder QR steps feed the source-faithful columnwise
    common-`Q` accumulation theorem.

    This is the multi-step concrete-loop version of the previous theorem.  It
    builds the exact trailing reflector at each pivot from the current stored
    pivot column, proves the lower-zero invariant needed by the one-step
    theorem, and accumulates the columnwise perturbations with the existing
    geometric bound.  Nonzero diagonal pivots for the later triangular solve
    are intentionally not part of this theorem. -/
theorem fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        c * vecNorm2 (b_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat n i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat n i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ n - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ n - 1) * vecNorm2 b := by
  classical
  let vStep : (k : ℕ) → k < n → Fin m → ℝ := fun k hk =>
    householderTrailingActiveVector m
      ⟨k, lt_of_lt_of_le hk hmn⟩
      (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
  let βStep : (k : ℕ) → k < n → ℝ := fun k hk =>
    householderBetaSpec m (vStep k hk)
  have hshape :
      ∀ k, k ≤ n →
        ∀ (i : Fin m) (j : Fin n),
          j.val < k → j.val < i.val → A_hat k i j = 0 := by
    intro k
    induction k with
    | zero =>
        intro _hk i j hj _
        exact (Nat.not_lt_zero j.val hj).elim
    | succ k ih =>
        intro hk_succ i j hj_succ hji
        have hk_lt : k < n := Nat.lt_of_succ_le hk_succ
        have hstepPoint :
            A_hat (k + 1) i j =
              fl_householderStoredPanelStep fp m n k
                (vStep k hk_lt) (βStep k hk_lt) (A_hat k) i j := by
          have hs := hStepA k hk_lt
          simpa [vStep, βStep] using congrFun (congrFun hs i) j
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj_succ with hj_lt | hj_eq
        · calc
            A_hat (k + 1) i j
                = fl_householderStoredPanelStep fp m n k
                    (vStep k hk_lt) (βStep k hk_lt) (A_hat k) i j :=
                  hstepPoint
            _ = A_hat k i j := by
                  simp [fl_householderStoredPanelStep, hj_lt]
            _ = 0 := ih (Nat.le_of_lt hk_lt) i j hj_lt hji
        · let col : Fin n := ⟨k, hk_lt⟩
          have hj_fin : j = col := Fin.ext hj_eq
          subst j
          have hki : k < i.val := by
            simpa [col] using hji
          calc
            A_hat (k + 1) i col
                = fl_householderStoredPanelStep fp m n k
                    (vStep k hk_lt) (βStep k hk_lt) (A_hat k) i col :=
                  hstepPoint
            _ = 0 := by
                  simp [fl_householderStoredPanelStep, col, hki]
  let P : ℕ → Fin m → Fin m → ℝ := fun k =>
    if hk : k < n then
      householder m (vStep k hk) (βStep k hk)
    else
      idMatrix m
  apply
    householderColumnwisePanelAppError_rect_orthogonal_columnwise_vector_sequence_geometric
      m n n A b A_hat b_hat P c hc hInitA hInitb
  intro k hk
  have hpanel :
      HouseholderColumnwisePanelAppError m n
        (householder m (vStep k hk) (βStep k hk))
        (A_hat k)
        (fl_householderStoredPanelStep fp m n k
          (vStep k hk) (βStep k hk) (A_hat k))
        (b_hat k)
        (fl_householderStoredRhsStep fp m k
          (vStep k hk) (βStep k hk) (b_hat k)) c := by
    exact
      fl_householderStoredTrailingPanelStep_HouseholderColumnwisePanelAppError_of_budget
        fp m n k ⟨k, lt_of_lt_of_le hk hmn⟩ ⟨k, hk⟩ rfl rfl
        (A_hat k) (b_hat k) (alpha k) hm hc
        (by simpa [vStep] using halpha k hk)
        (by simpa [vStep] using hden k hk)
        (hshape k (Nat.le_of_lt hk))
        (by simpa [vStep, βStep] using hA_budget k hk)
        (by simpa [vStep, βStep] using hb_budget k hk)
  simpa [P, hk, vStep, βStep, hStepA k hk, hStepb k hk] using hpanel

/-- Stored trailing Householder QR gives the final columnwise Higham-style
    factorization and top-block shape in one theorem.

    This is the source-faithful QR-factorization assembly for the active route:
    the compact stored loop produces one exact orthogonal factor `Q`,
    columnwise perturbations `ΔA`, an RHS perturbation `Δb`, and a final stored
    matrix with `[R;0]` shape.  It intentionally does not assert that the
    diagonal of `R` is nonzero; that triangular-solve/nonbreakdown condition is
    a separate least-squares-solver dependency. -/
theorem fl_householderStoredTrailingPanel_higham_columnwise_factorization
    {m n : ℕ} (fp : FPModel) (hmn : n ≤ m)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k (hk : k < n),
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k))
    (hStepb : ∀ k (hk : k < n),
      b_hat (k + 1) =
        fl_householderStoredRhsStep fp m k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k))
    (halpha : ∀ k (hk : k < n),
      alpha k * alpha k =
        householderTrailingNorm2Sq m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩))
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0)
    (hA_budget : ∀ k (hk : k < n), ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k (hk : k < n),
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        c * vecNorm2 (b_hat k)) :
    let R : Fin n → Fin n → ℝ :=
      fun i j => A_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩ j
    let cTop : Fin n → ℝ :=
      fun i => b_hat n ⟨i.val, lt_of_lt_of_le i.isLt hmn⟩
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat n i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat n i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ n - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ n - 1) * vecNorm2 b ∧
      (∀ (i : Fin m) (j : Fin n) (hi : i.val < n),
        A_hat n i j = R ⟨i.val, hi⟩ j) ∧
      (∀ (i : Fin m) (j : Fin n), n ≤ i.val → A_hat n i j = 0) ∧
      (∀ (i : Fin m) (hi : i.val < n),
        b_hat n i = cTop ⟨i.val, hi⟩) ∧
      (∀ i j : Fin n, j.val < i.val → R i j = 0) := by
  classical
  let vStep : ℕ → Fin m → ℝ := fun k =>
    if hk : k < n then
      householderTrailingActiveVector m
        ⟨k, lt_of_lt_of_le hk hmn⟩
        (fun a => A_hat k a ⟨k, hk⟩) (alpha k)
    else
      0
  let βStep : ℕ → ℝ := fun k =>
    if hk : k < n then
      householderBetaSpec m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
    else
      0
  have hStepShape : ∀ k, k < n →
      A_hat (k + 1) =
        fl_householderStoredPanelStep fp m n k (vStep k) (βStep k) (A_hat k) := by
    intro k hk
    simpa [vStep, βStep, hk] using hStepA k hk
  rcases
    fl_householderStoredPanel_sequence_topBlock_shape_facts
      (m := m) (n := n) fp hmn vStep βStep A_hat b_hat hStepShape with
    ⟨hA_top, hA_bottom, hb_top, hupper⟩
  rcases
    fl_householderStoredTrailingPanel_rect_orthogonal_columnwise_vector_sequence_geometric
      fp hmn A b A_hat b_hat alpha c hc hm
      hInitA hInitb hStepA hStepb halpha hden hA_budget hb_budget with
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA_cols, hΔb⟩
  exact
    ⟨Q, ΔA, Δb, hQ, hArep, hbrep, hΔA_cols, hΔb,
      hA_top, hA_bottom, hb_top, hupper⟩

/-- The deterministic compact-update relative budget for one stored QR step,
    specialized to the reflector constructed from the current active column. -/
noncomputable def storedQRCompactStepRelativeBudget
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (k : Fin n) : ℝ :=
  let km : Fin m := ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
  let v :=
    householderTrailingActiveVector m km
      (fun a => A_hat k.val a k) (alpha k.val)
  let β := householderBetaSpec m v
  householderCompactPanelRelativeBudget fp m n v β
    (A_hat k.val) (b_hat k.val)

/-- Reflector-dependent normwise compact budget coefficient for one stored QR
    step.  It is the canonical coefficient produced by the explicit compact
    dot/scale/subtract Householder arithmetic at the signed stage. -/
noncomputable def storedQRCompactStepNormBudgetCoeff
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (k : Fin n) : ℝ :=
  householderCompactNormBudgetCoeff fp m
    (storedQRSignedStageVector hmn A_hat alpha k.val)
    (storedQRSignedStageBeta hmn A_hat alpha k.val)

/-- The reflector-dependent compact norm coefficient for a stored QR stage is
    nonnegative whenever the ambient Householder dot-product gamma budget is
    valid. -/
theorem storedQRCompactStepNormBudgetCoeff_nonneg
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m) (k : Fin n) :
    0 ≤ storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k := by
  simpa [storedQRCompactStepNormBudgetCoeff] using
    householderCompactNormBudgetCoeff_nonneg fp m
      (storedQRSignedStageVector hmn A_hat alpha k.val)
      (storedQRSignedStageBeta hmn A_hat alpha k.val) hm

/-- A pivot-local bound on `|β_k| * ‖v_k‖₂^2` bounds the explicit compact
    Householder norm coefficient for one stored QR stage. -/
theorem storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (B : ℝ)
    (hm : gammaValid fp m) (k : Fin n)
    (hB :
      |storedQRSignedStageBeta hmn A_hat alpha k.val| *
          vecNorm2 (storedQRSignedStageVector hmn A_hat alpha k.val) ^ 2 ≤
        B) :
    storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
      fp.u + B * householderCompactNormBudgetCoeffFactor fp m := by
  simpa [storedQRCompactStepNormBudgetCoeff] using
    householderCompactNormBudgetCoeff_le_of_abs_beta_norm_sq_le
      fp m
      (storedQRSignedStageVector hmn A_hat alpha k.val)
      (storedQRSignedStageBeta hmn A_hat alpha k.val)
      B hm hB

/-- Uniform version of
    `storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le`.

    This is a finite-stage handoff for the compact-product route: a single
    pivot-local estimate on every signed stage gives a uniform coefficient
    bound with the explicit machine/dimension factor. -/
theorem storedQRCompactStepNormBudgetCoeff_le_of_forall_abs_beta_norm_sq_le
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ) (B : ℝ)
    (hm : gammaValid fp m)
    (hB : ∀ k : Fin n,
      |storedQRSignedStageBeta hmn A_hat alpha k.val| *
          vecNorm2 (storedQRSignedStageVector hmn A_hat alpha k.val) ^ 2 ≤
        B) :
    ∀ k : Fin n,
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
        fp.u + B * householderCompactNormBudgetCoeffFactor fp m := by
  intro k
  exact storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le
    hmn fp A_hat alpha B hm k (hB k)

/-- Concrete coefficient estimate for one nonzero signed Householder stage.

    The previous theorem leaves the scalar `B` abstract.  For the exact
    Householder normalization used by the stored signed QR stage, nonzero
    denominator gives the concrete value `B = 2`. -/
theorem storedQRCompactStepNormBudgetCoeff_le_of_den_ne_zero
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m) (k : Fin n)
    (hden :
      (∑ i : Fin m,
        storedQRSignedStageVector hmn A_hat alpha k.val i *
          storedQRSignedStageVector hmn A_hat alpha k.val i) ≠ 0) :
    storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
      fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
  exact
    storedQRCompactStepNormBudgetCoeff_le_of_abs_beta_norm_sq_le
      hmn fp A_hat alpha 2 hm k
      (storedQRSignedStage_abs_beta_norm_sq_le_two_of_den_ne_zero
        hmn A_hat alpha k.val hden)

/-- Uniform concrete coefficient estimate for nonzero signed Householder
    stages. -/
theorem storedQRCompactStepNormBudgetCoeff_le_of_forall_den_ne_zero
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hden : ∀ k : Fin n,
      (∑ i : Fin m,
        storedQRSignedStageVector hmn A_hat alpha k.val i *
          storedQRSignedStageVector hmn A_hat alpha k.val i) ≠ 0) :
    ∀ k : Fin n,
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
        fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
  intro k
  exact
    storedQRCompactStepNormBudgetCoeff_le_of_den_ne_zero
      hmn fp A_hat alpha hm k (hden k)

/-- Source-shaped version of
    `storedQRCompactStepNormBudgetCoeff_le_of_forall_den_ne_zero`.

    Existing stored-QR loop theorems usually expose nonbreakdown using the
    active trailing vector written directly from `A_hat`, not through
    `storedQRSignedStageVector`.  This adapter closes that definitional gap. -/
theorem storedQRCompactStepNormBudgetCoeff_le_of_forall_source_den_ne_zero
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hden : ∀ k (hk : k < n),
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i *
          householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k) i) ≠ 0) :
    ∀ k : Fin n,
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
        fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
  intro k
  exact
    storedQRCompactStepNormBudgetCoeff_le_of_den_ne_zero
      hmn fp A_hat alpha hm k
      (by
        simpa [storedQRSignedStageVector, k.isLt] using hden k.val k.isLt)

/-- One stored QR compact-step relative budget is bounded by the explicit
    reflector-dependent normwise compact coefficient for that stage. -/
theorem storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m) (k : Fin n) :
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
      (n : ℝ) *
          storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k +
        storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k := by
  let v := storedQRSignedStageVector hmn A_hat alpha k.val
  let β := storedQRSignedStageBeta hmn A_hat alpha k.val
  have hpanel :
      householderCompactPanelRelativeBudget fp m n v β
          (A_hat k.val) (b_hat k.val) ≤
        (n : ℝ) * householderCompactNormBudgetCoeff fp m v β +
          householderCompactNormBudgetCoeff fp m v β :=
    householderCompactPanelRelativeBudget_le_mul_add_normBudgetCoeff
      fp m n v β (A_hat k.val) (b_hat k.val) hm
  simpa [storedQRCompactStepRelativeBudget,
    storedQRCompactStepNormBudgetCoeff, v, β,
    storedQRSignedStageVector, storedQRSignedStageBeta, k.isLt] using hpanel

/-- Operation-count comparison for one deterministic stored QR compact-step
    budget.

    If the current signed Householder stage has a nonzero source denominator
    and the displayed operation index `stepOps` dominates
    `31 * (n + 1) * m`, then the computed one-step panel relative budget is
    bounded by `gamma fp stepOps`.  This packages the explicit compact
    Householder coefficient estimate into the source-facing one-step gamma
    comparison consumed by the least-squares QR theorem. -/
theorem storedQRCompactStepRelativeBudget_le_gamma_of_source_den_ne_zero_operation_count
    {m n stepOps : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ)
    (hm : gammaValid fp m)
    (hγstep : gammaValid fp stepOps)
    (hstepOps : 31 * (n + 1) * m ≤ stepOps)
    (k : Fin n)
    (hden :
      (∑ i : Fin m,
        householderTrailingActiveVector m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (fun a => A_hat k.val a k) (alpha k.val) i *
          householderTrailingActiveVector m
            ⟨k.val, lt_of_lt_of_le k.isLt hmn⟩
            (fun a => A_hat k.val a k) (alpha k.val) i) ≠ 0) :
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
      gamma fp stepOps := by
  have hn_pos : 0 < n := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
  have hm_pos : 0 < m := lt_of_lt_of_le hn_pos hmn
  have hfactorNat : 2 ≤ 31 * (n + 1) := by omega
  have h2m_le_index : 2 * m ≤ (31 * (n + 1)) * m :=
    Nat.mul_le_mul_right m hfactorNat
  have hindex_eq : (31 * (n + 1)) * m = 31 * (n + 1) * m := by rfl
  have h2m_le_stepOps : 2 * m ≤ stepOps := by
    exact le_trans (by simpa [hindex_eq] using h2m_le_index) hstepOps
  have hvalid2m : gammaValid fp (2 * m) :=
    gammaValid_mono fp h2m_le_stepOps hγstep
  have hfactor :
      householderCompactNormBudgetCoeffFactor fp m ≤ 15 * gamma fp m :=
    householderCompactNormBudgetCoeffFactor_le_fifteen_gamma
      fp m hm_pos hvalid2m
  have hm_from_step : gammaValid fp m :=
    gammaValid_mono fp (by omega) hvalid2m
  have hu_le_gamma : fp.u ≤ gamma fp m :=
    u_le_gamma fp hm_pos hm_from_step
  have hcoeff :
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
        fp.u + 2 * householderCompactNormBudgetCoeffFactor fp m := by
    exact
      storedQRCompactStepNormBudgetCoeff_le_of_den_ne_zero
        hmn fp A_hat alpha hm k
        (by simpa [storedQRSignedStageVector, k.isLt] using hden)
  have hcoeff_gamma :
      storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
        31 * gamma fp m := by
    nlinarith [hcoeff, hfactor, hu_le_gamma]
  have hstep_local :
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
        (n : ℝ) * storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k +
          storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k :=
    storedQRCompactStepRelativeBudget_le_mul_add_normBudgetCoeff
      hmn fp A_hat b_hat alpha hm k
  have hstep_gamma_m :
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
        ((31 * (n + 1) : ℕ) : ℝ) * gamma fp m := by
    have hn_nonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hcap1 :
        (n : ℝ) * storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
          (n : ℝ) * (31 * gamma fp m) :=
      mul_le_mul_of_nonneg_left hcoeff_gamma hn_nonneg
    have hcap2 :
        (n : ℝ) * storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k +
            storedQRCompactStepNormBudgetCoeff hmn fp A_hat alpha k ≤
          (n : ℝ) * (31 * gamma fp m) + 31 * gamma fp m :=
      add_le_add hcap1 hcoeff_gamma
    have hcap3 :
        (n : ℝ) * (31 * gamma fp m) + 31 * gamma fp m =
          ((31 * (n + 1) : ℕ) : ℝ) * gamma fp m := by
      norm_num
      ring
    exact hstep_local.trans (hcap2.trans_eq hcap3)
  have hi : 1 ≤ 31 * (n + 1) := by omega
  have hvalid_index : gammaValid fp ((31 * (n + 1)) * m) := by
    apply gammaValid_mono fp ?_ hγstep
    simpa [hindex_eq] using hstepOps
  have hgamma_index :
      ((31 * (n + 1) : ℕ) : ℝ) * gamma fp m ≤
        gamma fp ((31 * (n + 1)) * m) :=
    gamma_nsmul_le fp (31 * (n + 1)) m hi hvalid_index
  have hindex_le_step :
      gamma fp ((31 * (n + 1)) * m) ≤ gamma fp stepOps :=
    gamma_mono fp (by simpa [hindex_eq] using hstepOps) hγstep
  exact hstep_gamma_m.trans (hgamma_index.trans hindex_le_step)

/-- A single deterministic compact-update relative budget for the whole stored
    QR loop, obtained by summing the one-step relative budgets. -/
noncomputable def storedQRCompactSequenceRelativeBudget
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) : ℝ :=
  ∑ k : Fin n,
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k

/-- Nonnegativity of the one-step stored QR compact-update budget. -/
theorem storedQRCompactStepRelativeBudget_nonneg
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m) (k : Fin n) :
    0 ≤ storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k := by
  unfold storedQRCompactStepRelativeBudget
  exact householderCompactPanelRelativeBudget_nonneg fp m n _ _
    (A_hat k.val) (b_hat k.val) hm

/-- Nonnegativity of the summed stored QR compact-update budget. -/
theorem storedQRCompactSequenceRelativeBudget_nonneg
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m) :
    0 ≤ storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha := by
  unfold storedQRCompactSequenceRelativeBudget
  exact Finset.sum_nonneg
    (fun k _ => storedQRCompactStepRelativeBudget_nonneg
      hmn fp A_hat b_hat alpha hm k)

/-- Each stored QR step budget is bounded by the summed sequence budget. -/
theorem storedQRCompactStepRelativeBudget_le_sequence
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m) (k : Fin n) :
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha := by
  unfold storedQRCompactSequenceRelativeBudget
  exact Finset.single_le_sum
    (fun q _ => storedQRCompactStepRelativeBudget_nonneg
      hmn fp A_hat b_hat alpha hm q)
    (Finset.mem_univ k)

/-- If every stored QR compact step has relative budget at most `cStep`,
    then the summed sequence budget is at most `n * cStep`.

    This is a finite-sum cap, not a proof that a concrete computed loop has a
    small per-step budget.  It is useful for reducing the global product
    smallness condition to explicit one-step panel budget estimates. -/
theorem storedQRCompactSequenceRelativeBudget_le_mul_of_step_le
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (cStep : ℝ)
    (hStep : ∀ k : Fin n,
      storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤ cStep) :
    storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha ≤
      (n : ℝ) * cStep := by
  calc
    storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha
        = ∑ k : Fin n,
            storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k := rfl
    _ ≤ ∑ _k : Fin n, cStep := by
      exact Finset.sum_le_sum (fun k _ => hStep k)
    _ = (n : ℝ) * cStep := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- A stored QR compact-step relative budget is bounded by uniform vector-level
    compact-budget caps for that stage's panel columns and RHS.

    This reduces the one-step panel-cap obligation to vector-level compact
    Householder budget estimates for the concrete signed stage reflector. -/
theorem storedQRCompactStepRelativeBudget_le_mul_add_of_column_rhs_le
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (k : Fin n)
    (cCol cRhs : ℝ)
    (hCol : ∀ j : Fin n,
      householderCompactRelativeBudget fp m
        (storedQRSignedStageVector hmn A_hat alpha k.val)
        (storedQRSignedStageBeta hmn A_hat alpha k.val)
        (fun i : Fin m => A_hat k.val i j) ≤ cCol)
    (hRhs :
      householderCompactRelativeBudget fp m
        (storedQRSignedStageVector hmn A_hat alpha k.val)
        (storedQRSignedStageBeta hmn A_hat alpha k.val)
        (b_hat k.val) ≤ cRhs) :
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
      (n : ℝ) * cCol + cRhs := by
  let v := storedQRSignedStageVector hmn A_hat alpha k.val
  let β := storedQRSignedStageBeta hmn A_hat alpha k.val
  have hpanel :
      householderCompactPanelRelativeBudget fp m n v β
          (A_hat k.val) (b_hat k.val) ≤
        (n : ℝ) * cCol + cRhs :=
    householderCompactPanelRelativeBudget_le_mul_add_of_column_rhs_le
      fp m n v β (A_hat k.val) (b_hat k.val) cCol cRhs
      (fun j => by simpa [v, β] using hCol j)
      (by simpa [v, β] using hRhs)
  simpa [storedQRCompactStepRelativeBudget, v, β,
    storedQRSignedStageVector, storedQRSignedStageBeta, k.isLt] using hpanel

/-- A stored QR compact-step relative budget is bounded by primitive normwise
    compact-budget caps for that stage's panel columns and RHS.

    This is the stored-loop version of
    `householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul`:
    vector-level norm-budget estimates imply the relative caps consumed by the
    one-step panel budget. -/
theorem storedQRCompactStepRelativeBudget_le_mul_add_of_normBudget_le_mul
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (k : Fin n)
    (cCol cRhs : ℝ)
    (hcCol : 0 ≤ cCol) (hcRhs : 0 ≤ cRhs)
    (hCol : ∀ j : Fin n,
      householderCompactNormBudget fp m
        (storedQRSignedStageVector hmn A_hat alpha k.val)
        (storedQRSignedStageBeta hmn A_hat alpha k.val)
        (fun i : Fin m => A_hat k.val i j) ≤
          cCol * vecNorm2 (fun i : Fin m => A_hat k.val i j))
    (hRhs :
      householderCompactNormBudget fp m
        (storedQRSignedStageVector hmn A_hat alpha k.val)
        (storedQRSignedStageBeta hmn A_hat alpha k.val)
        (b_hat k.val) ≤ cRhs * vecNorm2 (b_hat k.val)) :
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
      (n : ℝ) * cCol + cRhs := by
  let v := storedQRSignedStageVector hmn A_hat alpha k.val
  let β := storedQRSignedStageBeta hmn A_hat alpha k.val
  have hpanel :
      householderCompactPanelRelativeBudget fp m n v β
          (A_hat k.val) (b_hat k.val) ≤
        (n : ℝ) * cCol + cRhs :=
    householderCompactPanelRelativeBudget_le_mul_add_of_normBudget_le_mul
      fp m n v β (A_hat k.val) (b_hat k.val) cCol cRhs
      hcCol hcRhs
      (fun j => by simpa [v, β] using hCol j)
      (by simpa [v, β] using hRhs)
  simpa [storedQRCompactStepRelativeBudget, v, β,
    storedQRSignedStageVector, storedQRSignedStageBeta, k.isLt] using hpanel

/-- A stored QR compact-step relative budget is bounded by componentwise
    compact-budget caps for that stage's panel columns and RHS.

    This is one level closer to the explicit dot-scale-subtract arithmetic:
    componentwise bounds `budget_i <= c * |input_i|` imply the norm-budget
    hypotheses used by the stored-loop norm-budget adapter. -/
theorem storedQRCompactStepRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (k : Fin n)
    (cCol cRhs : ℝ)
    (hm : gammaValid fp m)
    (hcCol : 0 ≤ cCol) (hcRhs : 0 ≤ cRhs)
    (hCol : ∀ j : Fin n, ∀ i : Fin m,
      householderCompactComponentBudget fp m
        (storedQRSignedStageVector hmn A_hat alpha k.val)
        (storedQRSignedStageBeta hmn A_hat alpha k.val)
        (fun a : Fin m => A_hat k.val a j) i ≤
          cCol * |A_hat k.val i j|)
    (hRhs : ∀ i : Fin m,
      householderCompactComponentBudget fp m
        (storedQRSignedStageVector hmn A_hat alpha k.val)
        (storedQRSignedStageBeta hmn A_hat alpha k.val)
        (b_hat k.val) i ≤ cRhs * |b_hat k.val i|) :
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha k ≤
      (n : ℝ) * cCol + cRhs := by
  let v := storedQRSignedStageVector hmn A_hat alpha k.val
  let β := storedQRSignedStageBeta hmn A_hat alpha k.val
  have hpanel :
      householderCompactPanelRelativeBudget fp m n v β
          (A_hat k.val) (b_hat k.val) ≤
        (n : ℝ) * cCol + cRhs :=
    householderCompactPanelRelativeBudget_le_mul_add_of_componentBudget_le_mul_abs
      fp m n v β (A_hat k.val) (b_hat k.val) cCol cRhs
      hm hcCol hcRhs
      (fun j i => by simpa [v, β] using hCol j i)
      (fun i => by simpa [v, β] using hRhs i)
  simpa [storedQRCompactStepRelativeBudget, v, β,
    storedQRSignedStageVector, storedQRSignedStageBeta, k.isLt] using hpanel

/-- The summed stored QR compact-update budget dominates every masked panel
    column budget in the stored loop. -/
theorem storedQRCompactSequenceRelativeBudget_column_bound
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m)
    (k : ℕ) (hk : k < n) (j : Fin n) :
    vecNorm2 (fun i : Fin m =>
      if j.val < k then 0
      else householderCompactComponentBudget fp m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
        (fun a => A_hat k a j) i) ≤
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
        vecNorm2 (fun i : Fin m => A_hat k i j) := by
  let kf : Fin n := ⟨k, hk⟩
  let stepBudget :=
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha kf
  have hstep :
      stepBudget ≤
        storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha := by
    simpa [stepBudget] using
      storedQRCompactStepRelativeBudget_le_sequence
        hmn fp A_hat b_hat alpha hm kf
  have hcol :
      vecNorm2 (fun i : Fin m =>
        if j.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (fun a => A_hat k a j) i) ≤
        stepBudget * vecNorm2 (fun i : Fin m => A_hat k i j) := by
    simpa [stepBudget, storedQRCompactStepRelativeBudget, kf]
      using
        householderCompactPanelRelativeBudget_stored_column_bound
          fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k) (b_hat k) hm j
  exact le_trans hcol
    (mul_le_mul_of_nonneg_right hstep
      (vecNorm2_nonneg (fun i : Fin m => A_hat k i j)))

/-- The pivot compact component is controlled by the deterministic stored-loop
    sequence budget times the current pivot-column norm.

    This scalar form is useful for downstream least-squares certificates whose
    compact-smallness side condition is expressed in terms of the single active
    pivot component rather than the whole masked panel vector. -/
theorem storedQRCompactPivotBudget_le_sequence_column_norm
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m)
    (k : ℕ) (hk : k < n) :
    householderCompactComponentBudget fp m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
        (fun a => A_hat k a ⟨k, hk⟩)
        ⟨k, lt_of_lt_of_le hk hmn⟩ ≤
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
        vecNorm2 (fun i : Fin m => A_hat k i ⟨k, hk⟩) := by
  let p : Fin m := ⟨k, lt_of_lt_of_le hk hmn⟩
  let j : Fin n := ⟨k, hk⟩
  let v :=
    householderTrailingActiveVector m p
      (fun a => A_hat k a j) (alpha k)
  let beta := householderBetaSpec m v
  let x : Fin m → ℝ :=
    fun i =>
      if j.val < k then 0
      else householderCompactComponentBudget fp m v beta
        (fun a => A_hat k a j) i
  let budget :=
    householderCompactComponentBudget fp m v beta
      (fun a => A_hat k a j) p
  have hbudget_nonneg : 0 ≤ budget := by
    simpa [budget, beta, v, p, j] using
      householderCompactComponentBudget_nonneg fp m v beta
        (fun a => A_hat k a j) hm p
  have hx_p : x p = budget := by
    simp [x, budget, j]
  have hcoord : |x p| ≤ vecNorm2 x :=
    abs_coord_le_vecNorm2 x p
  have hcol :
      vecNorm2 x ≤
        storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i j) := by
    simpa [x, v, beta, j] using
      storedQRCompactSequenceRelativeBudget_column_bound
        hmn fp A_hat b_hat alpha hm k hk j
  have hbudget_le :
      budget ≤
        storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i j) := by
    calc
      budget = |x p| := by
        rw [hx_p, abs_of_nonneg hbudget_nonneg]
      _ ≤ vecNorm2 x := hcoord
      _ ≤ storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
          vecNorm2 (fun i : Fin m => A_hat k i j) := hcol
  simpa [budget, v, beta, p, j] using hbudget_le

/-- The summed stored QR compact-update budget dominates every masked RHS
    budget in the stored loop. -/
theorem storedQRCompactSequenceRelativeBudget_rhs_bound
    {m n : ℕ} (hmn : n ≤ m)
    (fp : FPModel)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (alpha : ℕ → ℝ) (hm : gammaValid fp m)
    (k : ℕ) (hk : k < n) :
    vecNorm2 (fun i : Fin m =>
      if i.val < k then 0
      else householderCompactComponentBudget fp m
        (householderTrailingActiveVector m
          ⟨k, lt_of_lt_of_le hk hmn⟩
          (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
        (householderBetaSpec m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
        (b_hat k) i) ≤
      storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha *
        vecNorm2 (b_hat k) := by
  let kf : Fin n := ⟨k, hk⟩
  let stepBudget :=
    storedQRCompactStepRelativeBudget hmn fp A_hat b_hat alpha kf
  have hstep :
      stepBudget ≤
        storedQRCompactSequenceRelativeBudget hmn fp A_hat b_hat alpha := by
    simpa [stepBudget] using
      storedQRCompactStepRelativeBudget_le_sequence
        hmn fp A_hat b_hat alpha hm kf
  have hrhs :
      vecNorm2 (fun i : Fin m =>
        if i.val < k then 0
        else householderCompactComponentBudget fp m
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (b_hat k) i) ≤
        stepBudget * vecNorm2 (b_hat k) := by
    simpa [stepBudget, storedQRCompactStepRelativeBudget, kf]
      using
        householderCompactPanelRelativeBudget_stored_rhs_bound
          fp m n k
          (householderTrailingActiveVector m
            ⟨k, lt_of_lt_of_le hk hmn⟩
            (fun a => A_hat k a ⟨k, hk⟩) (alpha k))
          (householderBetaSpec m
            (householderTrailingActiveVector m
              ⟨k, lt_of_lt_of_le hk hmn⟩
              (fun a => A_hat k a ⟨k, hk⟩) (alpha k)))
          (A_hat k) (b_hat k) hm
  exact le_trans hrhs
    (mul_le_mul_of_nonneg_right hstep (vecNorm2_nonneg (b_hat k)))

-- ============================================================

end NumStability
