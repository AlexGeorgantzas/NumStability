import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Basic
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method1B.BlockResidual.WholeMatrixBounds
import NumStability.Source.Higham.Chapter14.Section02.TriangularInversion.Method2C.WholeMatrixResidual.LeftResidualBounds

/-!
# Derivations

Canonical destination for the Chapter14.Problem02 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Problem142` during wave R08.
Holds 8 declaration(s): 6 public and 2 authored-private.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open scoped BigOperators

namespace NumStability

namespace Ch14Ext

private theorem higham14_problem14_2_castAdd_ne_natAdd {r m : ℕ}
    (i : Fin r) (j : Fin m) :
    (Fin.castAdd m i : Fin (r + m)) ≠ Fin.natAdd r j := by
  intro h
  have hval := congrArg Fin.val h
  simp at hval
  omega

private theorem higham14_problem14_2_natAdd_ne_castAdd {r m : ℕ}
    (i : Fin m) (j : Fin r) :
    (Fin.natAdd r i : Fin (r + m)) ≠ Fin.castAdd m j :=
  Ne.symm (higham14_problem14_2_castAdd_ne_natAdd j i)

/-- The lower-block constructor maps block identities to the full identity. -/
theorem higham14_problem14_2_lowerBlock_one {r m : ℕ} :
    higham14_problem14_2_lowerBlock
        (1 : Matrix (Fin r) (Fin r) ℝ)
        (0 : Matrix (Fin m) (Fin r) ℝ)
        (1 : Matrix (Fin m) (Fin m) ℝ) =
      (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ) := by
  ext i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [Matrix.one_apply]
    · intro d
      simp [higham14_problem14_2_castAdd_ne_natAdd]
  · intro c
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [higham14_problem14_2_natAdd_ne_castAdd]
    · intro d
      simp [Matrix.one_apply]

/-- The residual of two lower block matrices is assembled from the two
    diagonal residuals and the off-diagonal residual. -/
theorem higham14_problem14_2_lowerBlock_mul_sub_one {r m : ℕ}
    (A11 B11 : Matrix (Fin r) (Fin r) ℝ)
    (A21 B21 : Matrix (Fin m) (Fin r) ℝ)
    (A22 B22 : Matrix (Fin m) (Fin m) ℝ) :
    (higham14_problem14_2_lowerBlock A11 A21 A22 :
        Matrix (Fin (r + m)) (Fin (r + m)) ℝ) *
        higham14_problem14_2_lowerBlock B11 B21 B22 - 1 =
      higham14_problem14_2_lowerBlock
        (A11 * B11 - (1 : Matrix (Fin r) (Fin r) ℝ))
        (A21 * B11 + A22 * B21)
        (A22 * B22 - (1 : Matrix (Fin m) (Fin m) ℝ)) := by
  rw [higham14_problem14_2_lowerBlock_mul]
  ext i j
  refine Fin.addCases ?_ ?_ i
  · intro a
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [Matrix.one_apply]
    · intro d
      simp [higham14_problem14_2_castAdd_ne_natAdd]
  · intro c
    refine Fin.addCases ?_ ?_ j
    · intro b
      simp [higham14_problem14_2_natAdd_ne_castAdd]
    · intro d
      simp [Matrix.one_apply]

/-- Method 1B right residual for an arbitrary split.  The diagonal estimates
    may come from a leaf solve or from recursively composed block partitions;
    the off-diagonal estimate is derived from (13.4)/(13.5). -/
theorem higham14_problem14_2_method1B_twoBlock_right_firstOrder {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (u cMul cSolve leading11 leading22 : ℝ)
    (L11 X11 : Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ)
    (h11 : FirstOrderLe u leading11
      (maxEntryNormRect hr hr
        (L11 * X11 - (1 : Matrix (Fin r) (Fin r) ℝ))))
    (h22 : FirstOrderLe u leading22
      (maxEntryNormRect hm hm
        (L22 * X22 - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hstep : Higham14Problem142Method1BStepSpec hr hm u cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) :
    FirstOrderLe u
      (max leading11
        (max
          (cMul * u * maxEntryNormRect hm hr L21 * maxEntryNormRect hr hr X11 +
            cSolve * u * maxEntryNormRect hm hm L22 * maxEntryNormRect hm hr X21)
          leading22))
      (maxEntryNormRect (Nat.add_pos_left hr m) (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock L11 L21 L22 *
          higham14_problem14_2_lowerBlock X11 X21 X22 -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  rw [higham14_problem14_2_lowerBlock_mul_sub_one]
  exact higham14_problem14_2_lowerBlock_residual_firstOrder hr hm u
    leading11
    (cMul * u * maxEntryNormRect hm hr L21 * maxEntryNormRect hr hr X11 +
      cSolve * u * maxEntryNormRect hm hm L22 * maxEntryNormRect hm hr X21)
    leading22
    (L11 * X11 - (1 : Matrix (Fin r) (Fin r) ℝ))
    (L21 * X11 + L22 * X21)
    (L22 * X22 - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 hstep.offdiag_firstOrder h22

/-- Method 2C left residual for an arbitrary split, with the same recursive
    interface and operation-derived off-diagonal block. -/
theorem higham14_problem14_2_method2C_twoBlock_left_firstOrder {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m) (u cMul cSolve leading11 leading22 : ℝ)
    (L11 X11 : Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : Matrix (Fin m) (Fin r) ℝ)
    (h11 : FirstOrderLe u leading11
      (maxEntryNormRect hr hr
        (X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ))))
    (h22 : FirstOrderLe u leading22
      (maxEntryNormRect hm hm
        (X22 * L22 - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hstep : Higham14Problem142Method2CStepSpec hr hm u cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) :
    FirstOrderLe u
      (max leading11
        (max
          (cMul * u * maxEntryNormRect hm hm X22 * maxEntryNormRect hm hr L21 +
            cSolve * u * maxEntryNormRect hr hr L11 * maxEntryNormRect hm hr X21)
          leading22))
      (maxEntryNormRect (Nat.add_pos_left hr m) (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock X11 X21 X22 *
          higham14_problem14_2_lowerBlock L11 L21 L22 -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  rw [higham14_problem14_2_lowerBlock_mul_sub_one]
  exact higham14_problem14_2_lowerBlock_residual_firstOrder hr hm u
    leading11
    (cMul * u * maxEntryNormRect hm hm X22 * maxEntryNormRect hm hr L21 +
      cSolve * u * maxEntryNormRect hr hr L11 * maxEntryNormRect hm hr X21)
    leading22
    (X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ))
    (X21 * L11 + X22 * L21)
    (X22 * L22 - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 hstep.offdiag_firstOrder h22

/-- Recursive Problem 14.2 conclusion for Method 1B over any partition encoded
    by `Higham14Problem142Method1BDerivation`. -/
theorem Higham14Problem142Method1BDerivation.right_residual_firstOrder
    {u : ℝ} {n : ℕ} {L X : Matrix (Fin n) (Fin n) ℝ} {leading : ℝ}
    (h : Higham14Problem142Method1BDerivation u L X leading) :
    ∀ hn : 0 < n,
      FirstOrderLe u leading
        (maxEntryNormRect hn hn
          (L * X - (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  induction h with
  | leaf hn cSolve L X Delta solve =>
      intro hn'
      have heq : L * X - (1 : Matrix _ _ ℝ) = Delta := by
        rw [solve.equation]
        abel
      rw [heq]
      simpa using solve.norm_bound
  | split hr hm cMul cSolve leading11 leading22 L11 X11 L21 X21 L22 X22
      That DeltaMul DeltaSolve head tail step ihHead ihTail =>
      intro _hsum
      exact higham14_problem14_2_method1B_twoBlock_right_firstOrder
        hr hm u cMul cSolve leading11 leading22
        L11 X11 L21 X21 L22 X22 That DeltaMul DeltaSolve
        (ihHead hr) (ihTail hm) step

/-- Recursive Problem 14.2 conclusion for Method 2C over an arbitrary finite
    binary block partition. -/
theorem Higham14Problem142Method2CDerivation.left_residual_firstOrder
    {u : ℝ} {n : ℕ} {L X : Matrix (Fin n) (Fin n) ℝ} {leading : ℝ}
    (h : Higham14Problem142Method2CDerivation u L X leading) :
    ∀ hn : 0 < n,
      FirstOrderLe u leading
        (maxEntryNormRect hn hn
          (X * L - (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  induction h with
  | leaf hn cSolve L X Delta solve =>
      intro hn'
      have heq : X * L - (1 : Matrix _ _ ℝ) = Delta := by
        rw [solve.equation]
        abel
      rw [heq]
      simpa using solve.norm_bound
  | split hr hm cMul cSolve leading11 leading22 L11 X11 L21 X21 L22 X22
      That DeltaMul DeltaSolve head tail step ihHead ihTail =>
      intro _hsum
      exact higham14_problem14_2_method2C_twoBlock_left_firstOrder
        hr hm u cMul cSolve leading11 leading22
        L11 X11 L21 X21 L22 X22 That DeltaMul DeltaSolve
        (ihHead hr) (ihTail hm) step

end Ch14Ext
end NumStability
