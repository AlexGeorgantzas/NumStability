import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderSpec
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Source.Higham.Chapter19.Theorem06.Pivoted
import NumStability.Analysis.MatrixAlgebra

namespace NumStability

open scoped BigOperators

/-!
# RowSorting

Canonical reusable module extracted without change from Higham20EliminationActual.
-/

namespace Higham20EliminationActual

/-- Exact active-max, column-pivoted signed-Householder trace through `s`
stages.  After the horizon the state is held fixed. -/
noncomputable def exactPivotedQRMatrixSeq {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ) :
    ℕ → Fin m → Fin n → ℝ
  | 0 => A
  | k + 1 =>
      if hk : k < s then
        let Aprev := exactPivotedQRMatrixSeq hsm hsn A k
        let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
        let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
        let pivot := householderActiveMaxPivotColumn row col Aprev
        let S : Equiv.Perm (Fin n) := Equiv.swap col pivot
        let As := Wave13.columnPermuteMatrix Aprev S
        let x : Fin m → ℝ := fun i => As i col
        let alpha := signedHouseholderAlpha
          (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row)
        let v := householderTrailingActiveVector m row x alpha
        let beta := householderBetaSpec m v
        matMulRect m m n (householder m v beta) As
      else
        exactPivotedQRMatrixSeq hsm hsn A k
/-- Executed active-max column exchange at a generic-horizon exact stage. -/
noncomputable def exactPivotedQRSwapSeq {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Equiv.Perm (Fin n) :=
  if hk : k < s then
    let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    Equiv.swap col
      (householderActiveMaxPivotColumn row col
        (exactPivotedQRMatrixSeq hsm hsn A k))
  else
    Equiv.refl _
/-- Panel after the actually executed exact-stage exchange. -/
noncomputable def exactPivotedQRSwappedPanel {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin n → ℝ :=
  Wave13.columnPermuteMatrix (exactPivotedQRMatrixSeq hsm hsn A k)
    (exactPivotedQRSwapSeq hsm hsn A k)
/-- Raw signed reflector vector actually constructed at exact stage `k`. -/
noncomputable def exactPivotedQRRawVector {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → ℝ :=
  if hk : k < s then
    let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    let As := exactPivotedQRSwappedPanel hsm hsn A k
    let x : Fin m → ℝ := fun i => As i col
    householderTrailingActiveVector m row x
      (signedHouseholderAlpha
        (Real.sqrt (householderTrailingNorm2Sq m row x)) (x row))
  else
    0
/-- Exact beta paired with the constructed raw vector. -/
noncomputable def exactPivotedQRBeta {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : ℝ :=
  householderBetaSpec m (exactPivotedQRRawVector hsm hsn A k)
/-- Exact reflector sequence of the constructed wide/tall prefix trace. -/
noncomputable def exactPivotedQRPseq {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) : Fin m → Fin m → ℝ :=
  householder m (exactPivotedQRRawVector hsm hsn A k)
    (exactPivotedQRBeta hsm hsn A k)
theorem exactPivotedQRMatrixSeq_succ_of_lt {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) :
    exactPivotedQRMatrixSeq hsm hsn A (k + 1) =
      matMulRect m m n (exactPivotedQRPseq hsm hsn A k)
        (exactPivotedQRSwappedPanel hsm hsn A k) := by
  simp [exactPivotedQRMatrixSeq, exactPivotedQRPseq,
    exactPivotedQRRawVector, exactPivotedQRBeta,
    exactPivotedQRSwappedPanel, exactPivotedQRSwapSeq, hk]
/-- Executed exact-stage swaps fix all completed column positions. -/
theorem exactPivotedQRSwapSeq_fix_prefix {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin n) (hj : j.val < k) :
    exactPivotedQRSwapSeq hsm hsn A k j = j := by
  by_cases hk : k < s
  · let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    let pivot := householderActiveMaxPivotColumn row col
      (exactPivotedQRMatrixSeq hsm hsn A k)
    have hjc : j ≠ col := by
      intro h
      subst j
      exact (Nat.lt_irrefl k hj)
    have hpge : k ≤ pivot.val := by
      simpa [pivot, col] using
        householderActiveMaxPivotColumn_ge row col
          (exactPivotedQRMatrixSeq hsm hsn A k)
    have hjp : j ≠ pivot := by
      intro h
      subst j
      omega
    simp only [exactPivotedQRSwapSeq, dif_pos hk]
    exact Equiv.swap_apply_of_ne_of_ne hjc hjp
  · simp [exactPivotedQRSwapSeq, hk]
/-- Executed exact-stage swaps map the active column suffix to itself. -/
theorem exactPivotedQRSwapSeq_maps_active {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (j : Fin n) (hj : k ≤ j.val) :
    k ≤ (exactPivotedQRSwapSeq hsm hsn A k j).val := by
  by_cases hk : k < s
  · let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
    let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
    let pivot := householderActiveMaxPivotColumn row col
      (exactPivotedQRMatrixSeq hsm hsn A k)
    have hpge : k ≤ pivot.val := by
      simpa [pivot, col] using
        householderActiveMaxPivotColumn_ge row col
          (exactPivotedQRMatrixSeq hsm hsn A k)
    simp only [exactPivotedQRSwapSeq, dif_pos hk]
    by_cases hjc : j = col
    · subst j
      rw [Equiv.swap_apply_left]
      exact hpge
    · by_cases hjp : j = pivot
      · subst j
        rw [Equiv.swap_apply_right]
      · rw [Equiv.swap_apply_of_ne_of_ne hjc hjp]
        exact hj
  · simp [exactPivotedQRSwapSeq, hk]
    exact hj
/-- The raw vector of an executed generic-horizon stage has a zero prefix. -/
theorem exactPivotedQRRawVector_zero_prefix {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) (i : Fin m) (hi : i.val < k) :
    exactPivotedQRRawVector hsm hsn A k i = 0 := by
  simp only [exactPivotedQRRawVector, dif_pos hk]
  exact householderTrailingActiveVector_zero_prefix m
    ⟨k, lt_of_lt_of_le hk hsm⟩
    (fun r => exactPivotedQRSwappedPanel hsm hsn A k r
      ⟨k, lt_of_lt_of_le hk hsn⟩)
    (signedHouseholderAlpha
      (Real.sqrt
        (householderTrailingNorm2Sq m ⟨k, lt_of_lt_of_le hk hsm⟩
          (fun r => exactPivotedQRSwappedPanel hsm hsn A k r
            ⟨k, lt_of_lt_of_le hk hsn⟩)))
      (exactPivotedQRSwappedPanel hsm hsn A k
        ⟨k, lt_of_lt_of_le hk hsm⟩ ⟨k, lt_of_lt_of_le hk hsn⟩)) i hi
/-- The exact signed reflector annihilates the displayed pivot-column tail.
The zero-trailing-norm branch is handled directly, so this algebraic theorem
has no nonbreakdown hypothesis. -/
theorem exactPivotedQRPseq_pivot_column_zero_below {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ)
    (k : ℕ) (hk : k < s) (i : Fin m) (hi : k < i.val) :
    matMulVec m (exactPivotedQRPseq hsm hsn A k)
        (fun r => exactPivotedQRSwappedPanel hsm hsn A k r
          ⟨k, lt_of_lt_of_le hk hsn⟩) i = 0 := by
  let row : Fin m := ⟨k, lt_of_lt_of_le hk hsm⟩
  let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
  let As := exactPivotedQRSwappedPanel hsm hsn A k
  let x : Fin m → ℝ := fun r => As r col
  let T := householderTrailingNorm2Sq m row x
  let alpha := signedHouseholderAlpha (Real.sqrt T) (x row)
  let v := householderTrailingActiveVector m row x alpha
  have hTnonneg : 0 ≤ T := by
    exact householderTrailingNorm2Sq_nonneg m row x
  by_cases hTpos : 0 < T
  · have halpha : alpha * alpha = T := by
      simpa [alpha, T] using
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_sq m row x
    have hsign : alpha * x row ≤ 0 := by
      simpa [alpha, T] using
        signedHouseholderAlpha_sqrt_trailingNorm2Sq_mul_pivot_nonpos m row x
    have hpivot_ne : x row ≠ alpha :=
      householder_pivot_ne_alpha_of_trailingNorm2Sq_pos_mul_nonpos
        m row x alpha halpha hTpos hsign
    have hden : (∑ r : Fin m, v r * v r) ≠ 0 := by
      simpa [v] using
        householderTrailingActiveVector_inner_self_ne_zero_of_pivot_ne_alpha
          m row x alpha hpivot_ne
    have hzero :=
      matMulVec_householder_trailingActiveVector_eq_zero_of_pivot_lt
        m row x alpha halpha hden i (by simpa [row] using hi)
    simpa [exactPivotedQRPseq, exactPivotedQRRawVector,
      exactPivotedQRBeta, hk, row, col, As, x, T, alpha, v] using hzero
  · have hTzero : T = 0 := le_antisymm (le_of_not_gt hTpos) hTnonneg
    have hx_active : ∀ r : Fin m, k ≤ r.val → x r = 0 := by
      intro r hr
      by_contra hne
      have hpos := householderTrailingNorm2Sq_pos_of_exists_ne
        m row x ⟨r, by simpa [row] using hr, hne⟩
      change 0 < T at hpos
      linarith
    have hxrow : x row = 0 := hx_active row (by simp [row])
    have halpha : alpha = 0 := by
      simp [alpha, hTzero, hxrow, signedHouseholderAlpha]
    have hvzero : v = 0 := by
      funext r
      by_cases hr : r.val < k
      · simpa [v, row] using
          householderTrailingActiveVector_zero_prefix m row x alpha r
            (by simpa [row] using hr)
      · have hxr : x r = 0 := hx_active r (Nat.le_of_not_gt hr)
        simp [v, householderTrailingActiveVector, householderActiveVector,
          householderTrailingPart, row, hr, hxr, halpha]
    have hxi : x i = 0 := hx_active i (le_of_lt hi)
    have hraw : exactPivotedQRRawVector hsm hsn A k = 0 := by
      simpa [exactPivotedQRRawVector, hk, row, col, As, x, T, alpha, v]
        using hvzero
    have hP : exactPivotedQRPseq hsm hsn A k = idMatrix m := by
      ext a b
      simp [exactPivotedQRPseq, exactPivotedQRBeta, hraw,
        householderBetaSpec, householder]
    rw [hP, matMulVec_id]
    simpa [x, As, col] using hxi
/-- Exact active-max pivoting plus signed Householder application preserves the
completed lower-zero shape through every prefix of the chosen horizon. -/
theorem exactPivotedQRMatrixSeq_prefix_lower_zero {m n s : ℕ}
    (hsm : s ≤ m) (hsn : s ≤ n) (A : Fin m → Fin n → ℝ) :
    ∀ k, k ≤ s → ∀ (i : Fin m) (j : Fin n),
      j.val < k → j.val < i.val →
        exactPivotedQRMatrixSeq hsm hsn A k i j = 0 := by
  intro k
  induction k with
  | zero =>
      intro _hk i j hj _
      exact (Nat.not_lt_zero j.val hj).elim
  | succ k ih =>
      intro hkSucc i j hjSucc hji
      have hk : k < s := Nat.lt_of_succ_le hkSucc
      have hstepPoint :
          exactPivotedQRMatrixSeq hsm hsn A (k + 1) i j =
            matMulRect m m n (exactPivotedQRPseq hsm hsn A k)
              (exactPivotedQRSwappedPanel hsm hsn A k) i j := by
        exact congrFun (congrFun
          (exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk) i) j
      rcases Nat.lt_succ_iff_lt_or_eq.mp hjSucc with hj | hj
      · let v := exactPivotedQRRawVector hsm hsn A k
        let beta := exactPivotedQRBeta hsm hsn A k
        let As := exactPivotedQRSwappedPanel hsm hsn A k
        let xcol : Fin m → ℝ := fun r => As r j
        have hfix := exactPivotedQRSwapSeq_fix_prefix hsm hsn A k j hj
        have hxcol : xcol = fun r => exactPivotedQRMatrixSeq hsm hsn A k r j := by
          funext r
          simp [xcol, As, exactPivotedQRSwappedPanel,
            Wave13.columnPermuteMatrix, hfix]
        have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
          intro r hr
          exact exactPivotedQRRawVector_zero_prefix hsm hsn A k hk r hr
        have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
          intro r hr
          rw [hxcol]
          exact ih (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
        have hpres :
            matMulVec m (householder m v beta) xcol = xcol :=
          matMulVec_householder_eq_self_of_zero_prefix_support
            m k v xcol beta hvprefix hsupport
        rw [hstepPoint]
        change matMulVec m (householder m v beta) xcol i = 0
        rw [congrFun hpres i, hxcol]
        exact ih (Nat.le_of_lt hk) i j hj hji
      · let col : Fin n := ⟨k, lt_of_lt_of_le hk hsn⟩
        have hjfin : j = col := Fin.ext hj
        subst j
        have hki : k < i.val := by simpa [col] using hji
        rw [hstepPoint]
        change
          matMulVec m (exactPivotedQRPseq hsm hsn A k)
            (fun r => exactPivotedQRSwappedPanel hsm hsn A k r col) i = 0
        exact exactPivotedQRPseq_pivot_column_zero_below
          hsm hsn A k hk i hki
/-- At the full row horizon, the exact wide active-max trace is upper
trapezoidal. -/
theorem exactPivotedQRMatrixSeq_upperTrapezoidal_fullRowHorizon
    {m n : ℕ} (hmn : m ≤ n) (A : Fin m → Fin n → ℝ) :
    IsUpperTrapezoidal m n
      (exactPivotedQRMatrixSeq (s := m) le_rfl hmn A m) := by
  intro i j hji
  exact exactPivotedQRMatrixSeq_prefix_lower_zero
    (s := m) le_rfl hmn A m le_rfl i j
      (lt_trans hji i.isLt) hji
/-- Once column `j` is completed, every later exact stage preserves it. -/
theorem exactPivotedQRMatrixSeq_completed_column_stable_step
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (k : ℕ) (hk : k < s)
    (i : Fin m) (j : Fin n) (hj : j.val < k) :
    exactPivotedQRMatrixSeq hsm hsn A (k + 1) i j =
      exactPivotedQRMatrixSeq hsm hsn A k i j := by
  let v := exactPivotedQRRawVector hsm hsn A k
  let beta := exactPivotedQRBeta hsm hsn A k
  let As := exactPivotedQRSwappedPanel hsm hsn A k
  let xcol : Fin m → ℝ := fun r => As r j
  have hfix := exactPivotedQRSwapSeq_fix_prefix hsm hsn A k j hj
  have hxcol : xcol = fun r => exactPivotedQRMatrixSeq hsm hsn A k r j := by
    funext r
    simp [xcol, As, exactPivotedQRSwappedPanel,
      Wave13.columnPermuteMatrix, hfix]
  have hvprefix : ∀ r : Fin m, r.val < k → v r = 0 := by
    intro r hr
    exact exactPivotedQRRawVector_zero_prefix hsm hsn A k hk r hr
  have hsupport : ∀ r : Fin m, k ≤ r.val → xcol r = 0 := by
    intro r hr
    rw [hxcol]
    exact exactPivotedQRMatrixSeq_prefix_lower_zero hsm hsn A
      k (Nat.le_of_lt hk) r j hj (lt_of_lt_of_le hj hr)
  have hpres : matMulVec m (householder m v beta) xcol = xcol :=
    matMulVec_householder_eq_self_of_zero_prefix_support
      m k v xcol beta hvprefix hsupport
  rw [show exactPivotedQRMatrixSeq hsm hsn A (k + 1) =
      matMulRect m m n (exactPivotedQRPseq hsm hsn A k) As from
    exactPivotedQRMatrixSeq_succ_of_lt hsm hsn A k hk]
  change matMulVec m (householder m v beta) xcol i =
    exactPivotedQRMatrixSeq hsm hsn A k i j
  rw [congrFun hpres i, hxcol]
/-- A completed column is unchanged from its completion stage through any
later prefix. -/
theorem exactPivotedQRMatrixSeq_completed_column_stable
    {m n s : ℕ} (hsm : s ≤ m) (hsn : s ≤ n)
    (A : Fin m → Fin n → ℝ) (k t : ℕ) (hk : k < s)
    (hkt : k + 1 ≤ t) (ht : t ≤ s) (i : Fin m) :
    exactPivotedQRMatrixSeq hsm hsn A t i ⟨k, lt_of_lt_of_le hk hsn⟩ =
      exactPivotedQRMatrixSeq hsm hsn A (k + 1) i
        ⟨k, lt_of_lt_of_le hk hsn⟩ := by
  induction t with
  | zero => omega
  | succ t ih =>
      by_cases htk : t = k
      · subst t
        rfl
      · have hkt' : k + 1 ≤ t := by omega
        have htlt : t < s := Nat.lt_of_succ_le ht
        calc
          exactPivotedQRMatrixSeq hsm hsn A (t + 1) i
              ⟨k, lt_of_lt_of_le hk hsn⟩ =
              exactPivotedQRMatrixSeq hsm hsn A t i
                ⟨k, lt_of_lt_of_le hk hsn⟩ :=
            exactPivotedQRMatrixSeq_completed_column_stable_step
              hsm hsn A t htlt i _ (by simp; omega)
          _ = exactPivotedQRMatrixSeq hsm hsn A (k + 1) i
                ⟨k, lt_of_lt_of_le hk hsn⟩ :=
            ih hkt' (Nat.le_of_lt htlt)
/-- An orthogonal row factor in the constraint matrix changes only the
constraint coordinates, not the feasible set. -/
theorem isLSEMinimizer_of_orthogonal_constraint_factor
    {m p n : ℕ} (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (B R : Fin p → Fin n → ℝ) (d qtd : Fin p → ℝ)
    (Q : Fin p → Fin p → ℝ) (x : Fin n → ℝ)
    (hQ : IsOrthogonal p Q)
    (hB : B = matMulRect p p n Q R)
    (hqtd : qtd = matMulVec p (matTranspose Q) d)
    (hmin : IsLSEMinimizer A b R qtd x) :
    IsLSEMinimizer A b B d x := by
  have hQQT : matMul p Q (matTranspose Q) = idMatrix p :=
    funext fun i => funext fun j => hQ.right_inv i j
  have hQTQ : matMul p (matTranspose Q) Q = idMatrix p :=
    funext fun i => funext fun j => hQ.left_inv i j
  refine ⟨?_, ?_⟩
  · have hRx : rectMatMulVec R x = qtd := funext hmin.1
    have hBx : rectMatMulVec B x = matMulVec p Q (rectMatMulVec R x) := by
      rw [hB]
      exact rectMatMulVec_matMulRectLeft Q R x
    intro i
    rw [congrFun hBx i, hRx, hqtd]
    rw [← matMulVec_matMul, hQQT, matMulVec_id]
  · intro y hy
    apply hmin.2 y
    have hyB : rectMatMulVec B y = d := funext hy
    have hQRY : matMulVec p Q (rectMatMulVec R y) = d := by
      have hB' : B = matMulRectLeft Q R := hB
      rw [← rectMatMulVec_matMulRectLeft, ← hB']
      exact hyB
    have hleft := congrArg (matMulVec p (matTranspose Q)) hQRY
    have hRy : rectMatMulVec R y = matMulVec p (matTranspose Q) d := by
      calc
        rectMatMulVec R y = matMulVec p (idMatrix p) (rectMatMulVec R y) := by
          rw [matMulVec_id]
        _ = matMulVec p (matMul p (matTranspose Q) Q)
            (rectMatMulVec R y) := by rw [hQTQ]
        _ = matMulVec p (matTranspose Q)
            (matMulVec p Q (rectMatMulVec R y)) := by
          ext i
          exact matMulVec_matMul p (matTranspose Q) Q
            (rectMatMulVec R y) i
        _ = matMulVec p (matTranspose Q) d := hleft
    intro i
    rw [congrFun hRy i, hqtd]

end Higham20EliminationActual

end NumStability
