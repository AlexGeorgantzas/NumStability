-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Componentwise QR-action estimates for the signed SNE analysis.

import NumStability.Algorithms.Underdetermined.Higham21SNESigned

namespace NumStability

open scoped BigOperators

/-!
# QR perturbation action without an aggregate Gram envelope

The Householder backward-error theorem supplies

`|F i p| <= rho * sum_s G p s * |A i s|`,

where `G` is nonnegative and has operator norm at most one.  The lemmas below
keep this action on the dual vector.  This is the cancellation-compatible
route used by Demmel--Higham; it does not introduce `|(A A^T)⁻¹|`.
-/

/-- A componentwise Householder QR perturbation controls its transposed action
by the nonnegative QR majorant acting on `|A|ᵀ |y|`. -/
theorem higham21_sne_qr_error_transpose_action_le_majorant
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hG : forall p s, 0 <= G p s)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (y : Fin m -> Real) :
    vecNorm2 (rectTransposeMulVec F y) <=
      rho * vecNorm2
        (rectMatMulVec G
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) := by
  let w : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)
  let Gw : Fin n -> Real := rectMatMulVec G w
  have hw : forall s, 0 <= w s := by
    intro s
    dsimp [w, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hGw : forall p, 0 <= Gw p := by
    intro p
    dsimp [Gw, rectMatMulVec]
    exact Finset.sum_nonneg (fun s _ => mul_nonneg (hG p s) (hw s))
  have hpoint : forall p,
      |rectTransposeMulVec F y p| <= rho * Gw p := by
    intro p
    calc
      |rectTransposeMulVec F y p| <=
          ∑ i : Fin m, |F i p| * |y i| := by
        simpa [rectTransposeMulVec, finiteTranspose] using
          (abs_rectMatMulVec_le (finiteTranspose F) y p)
      _ <= ∑ i : Fin m,
          (rho * ∑ s : Fin n, G p s * |A i s|) * |y i| := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hF p i) (abs_nonneg _)
      _ = ∑ i : Fin m, ∑ s : Fin n,
          rho * (G p s * |A i s|) * |y i| := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        rw [Finset.sum_mul]
      _ = ∑ s : Fin n, ∑ i : Fin m,
          rho * (G p s * |A i s|) * |y i| := Finset.sum_comm
      _ = rho * ∑ s : Fin n,
          G p s * (∑ i : Fin m, |A i s| * |y i|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s _
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = rho * Gw p := by rfl
  calc
    vecNorm2 (rectTransposeMulVec F y) <=
        vecNorm2 (fun p => rho * Gw p) := by
      apply vecNorm2_le_of_abs_le
      intro p
      simpa [abs_of_nonneg (mul_nonneg hrho (hGw p))] using hpoint p
    _ = rho * vecNorm2 Gw := by
      rw [vecNorm2_smul, abs_of_nonneg hrho]
    _ = rho * vecNorm2
        (rectMatMulVec G
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) := by
      rfl

/-- If the nonnegative QR majorant has operator norm at most one, the QR
perturbation action is at most `rho * || |A|ᵀ |y| ||₂`. -/
theorem higham21_sne_qr_error_transpose_action_le_source
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (y : Fin m -> Real) :
    vecNorm2 (rectTransposeMulVec F y) <=
      rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) := by
  have hmajorant :=
    higham21_sne_qr_error_transpose_action_le_majorant
      A F G rho hrho hG hF y
  calc
    vecNorm2 (rectTransposeMulVec F y) <=
        rho * vecNorm2
          (rectMatMulVec G
            (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) :=
      hmajorant
    _ <= rho *
        (1 * vecNorm2
          (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|))) :=
      mul_le_mul_of_nonneg_left (hGop _) hrho
    _ = rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) := by ring

/-- The same componentwise QR certificate controls the absolute action
`|F|ᵀ |y|`, which is the quantity needed before the signed cancellation. -/
theorem higham21_sne_qr_abs_error_transpose_action_le_source
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (y : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)) <=
      rho * vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) := by
  have hFabs : forall p i,
      |absMatrixRect F i p| <=
        rho * ∑ s : Fin n, G p s * |A i s| := by
    intro p i
    simpa [absMatrixRect] using hF p i
  simpa [absMatrixRect] using
    (higham21_sne_qr_error_transpose_action_le_source
      A (absMatrixRect F) G rho hrho hG hGop hFabs (fun i => |y i|))

/-- For `B = A + F`, the exact source action is bounded by the nearby action
plus the QR perturbation action. -/
theorem higham21_sne_source_dual_action_le_nearby_add_error
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real) (y : Fin m -> Real) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) <=
      vecNorm2
          (rectTransposeMulVec
            (absMatrixRect (fun i j => A i j + F i j))
            (fun i => |y i|)) +
        vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)) := by
  let wA : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)
  let wB : Fin n -> Real :=
    rectTransposeMulVec
      (absMatrixRect (fun i j => A i j + F i j)) (fun i => |y i|)
  let wF : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)
  have hwA : forall j, 0 <= wA j := by
    intro j
    dsimp [wA, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwB : forall j, 0 <= wB j := by
    intro j
    dsimp [wB, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hwF : forall j, 0 <= wF j := by
    intro j
    dsimp [wF, rectTransposeMulVec, absMatrixRect]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have hpoint : forall j, |wA j| <= wB j + wF j := by
    intro j
    rw [abs_of_nonneg (hwA j)]
    dsimp [wA, wB, wF, rectTransposeMulVec, absMatrixRect]
    calc
      ∑ i : Fin m, |A i j| * |y i| <=
          ∑ i : Fin m,
            (|A i j + F i j| + |F i j|) * |y i| := by
        apply Finset.sum_le_sum
        intro i _
        have hi : |A i j| <= |A i j + F i j| + |F i j| := by
          calc
            |A i j| = |(A i j + F i j) - F i j| := by ring_nf
            _ <= |A i j + F i j| + |F i j| := abs_sub _ _
        exact mul_le_mul_of_nonneg_right hi (abs_nonneg _)
      _ = (∑ i : Fin m, |A i j + F i j| * |y i|) +
          ∑ i : Fin m, |F i j| * |y i| := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hnorm : vecNorm2 wA <= vecNorm2 (fun j => wB j + wF j) := by
    apply vecNorm2_le_of_abs_le
    intro j
    simpa [abs_of_nonneg (add_nonneg (hwB j) (hwF j))] using hpoint j
  calc
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |y i|)) =
        vecNorm2 wA := by rfl
    _ <= vecNorm2 (fun j => wB j + wF j) := hnorm
    _ <= vecNorm2 wB + vecNorm2 wF := vecNorm2_add_le wB wF
    _ = vecNorm2
          (rectTransposeMulVec
            (absMatrixRect (fun i j => A i j + F i j))
            (fun i => |y i|)) +
        vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |y i|)) := by rfl

/-- Absorb the QR action into the nearby dual condition expression.  This is
the finite form of the first-order step
`|| |A|ᵀ |ybar| || <= cond₂(B)||xbar|| + O(rho)`.

The hypotheses are local: a componentwise QR perturbation, a norm-one
majorant, the canonical nearby dual relation, and `rho < 1`. -/
theorem higham21_sne_source_dual_action_absorbed_by_nearby_cond2
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho) (hrho_lt : rho < 1)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (Bplus : Fin n -> Fin m -> Real)
    (ybar : Fin m -> Real) (xbar : Fin n -> Real)
    (hybar : ybar = rectTransposeMulVec Bplus xbar) :
    vecNorm2
        (rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)) <=
      (higham21Cond2With (fun i j => A i j + F i j) Bplus *
          vecNorm2 xbar) / (1 - rho) := by
  let wA : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wB : Fin n -> Real :=
    rectTransposeMulVec
      (absMatrixRect (fun i j => A i j + F i j)) (fun i => |ybar i|)
  let q : Real :=
    higham21Cond2With (fun i j => A i j + F i j) Bplus * vecNorm2 xbar
  have hWF :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) <=
        rho * vecNorm2 wA := by
    simpa [wA] using
      higham21_sne_qr_abs_error_transpose_action_le_source
        A F G rho hrho hG hGop hF ybar
  have hAB : vecNorm2 wA <= vecNorm2 wB +
      vecNorm2
        (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) := by
    simpa [wA, wB] using
      higham21_sne_source_dual_action_le_nearby_add_error A F ybar
  have hBq : vecNorm2 wB <= q := by
    simpa [wB, q, hybar] using
      higham21_sne_dual_majorant_le_cond2
        (fun i j => A i j + F i j) Bplus xbar
  have hWA : vecNorm2 wA <= q + rho * vecNorm2 wA :=
    hAB.trans (add_le_add hBq hWF)
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hscaled : (1 - rho) * vecNorm2 wA <= q := by
    nlinarith
  have hdiv : vecNorm2 wA <= q / (1 - rho) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
  simpa [wA, q] using hdiv

theorem higham21_sne_qr_action_absorbed_by_nearby_cond2
    {m n : Nat}
    (A F : Fin m -> Fin n -> Real)
    (G : Fin n -> Fin n -> Real) (rho : Real)
    (hrho : 0 <= rho) (hrho_lt : rho < 1)
    (hG : forall p s, 0 <= G p s)
    (hGop : rectOpNorm2Le G 1)
    (hF : forall p i,
      |F i p| <= rho * ∑ s : Fin n, G p s * |A i s|)
    (Bplus : Fin n -> Fin m -> Real)
    (ybar : Fin m -> Real) (xbar : Fin n -> Real)
    (hybar : ybar = rectTransposeMulVec Bplus xbar) :
    vecNorm2 (rectTransposeMulVec F ybar) <=
      rho / (1 - rho) *
        higham21Cond2With (fun i j => A i j + F i j) Bplus *
          vecNorm2 xbar := by
  let wA : Fin n -> Real :=
    rectTransposeMulVec (absMatrixRect A) (fun i => |ybar i|)
  let wB : Fin n -> Real :=
    rectTransposeMulVec
      (absMatrixRect (fun i j => A i j + F i j)) (fun i => |ybar i|)
  let q : Real :=
    higham21Cond2With (fun i j => A i j + F i j) Bplus * vecNorm2 xbar
  have hq : 0 <= q :=
    mul_nonneg (higham21Cond2With_nonneg _ _) (vecNorm2_nonneg _)
  have hFB : vecNorm2 (rectTransposeMulVec F ybar) <= rho * vecNorm2 wA := by
    simpa [wA] using
      higham21_sne_qr_error_transpose_action_le_source
        A F G rho hrho hG hGop hF ybar
  have hWF :
      vecNorm2
          (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) <=
        rho * vecNorm2 wA := by
    simpa [wA] using
      higham21_sne_qr_abs_error_transpose_action_le_source
        A F G rho hrho hG hGop hF ybar
  have hAB : vecNorm2 wA <= vecNorm2 wB +
      vecNorm2
        (rectTransposeMulVec (absMatrixRect F) (fun i => |ybar i|)) := by
    simpa [wA, wB] using
      higham21_sne_source_dual_action_le_nearby_add_error A F ybar
  have hBq : vecNorm2 wB <= q := by
    simpa [wB, q, hybar] using
      higham21_sne_dual_majorant_le_cond2
        (fun i j => A i j + F i j) Bplus xbar
  have hWA : vecNorm2 wA <= q + rho * vecNorm2 wA :=
    hAB.trans (add_le_add hBq hWF)
  have hden : 0 < 1 - rho := sub_pos.mpr hrho_lt
  have hscaled : (1 - rho) * vecNorm2 wA <= q := by
    nlinarith
  have hWAdiv : vecNorm2 wA <= q / (1 - rho) :=
    (le_div_iff₀ hden).2 (by simpa [mul_comm] using hscaled)
  calc
    vecNorm2 (rectTransposeMulVec F ybar) <= rho * vecNorm2 wA := hFB
    _ <= rho * (q / (1 - rho)) := mul_le_mul_of_nonneg_left hWAdiv hrho
    _ = rho / (1 - rho) *
        higham21Cond2With (fun i j => A i j + F i j) Bplus *
          vecNorm2 xbar := by
      simp [q]
      ring

end NumStability
