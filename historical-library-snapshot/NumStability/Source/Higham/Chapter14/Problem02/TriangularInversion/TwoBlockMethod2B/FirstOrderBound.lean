import NumStability.Algorithms.LinearSystems.LU.BlockLU.FirstOrderModels
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Basic
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Method2B
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations

/-!
# FirstOrderBound

Canonical destination for the Chapter14.Problem02 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Problem142Method2B` during wave R08.
Holds 1 declaration(s): 1 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

namespace NumStability

namespace Ch14Ext

/-- Two-block integration with the recursive composer from
`Ch14Problem142`.  The diagonal and off-diagonal estimates are operation
derived; only the trailing recursive estimate is supplied. -/
theorem higham14_problem14_2_method2B_twoBlock_left_firstOrder
    {r m : ℕ}
    (hr : 0 < r) (hm : 0 < m)
    (u cFirst cSecond cDiag leading22 : ℝ)
    (L11 X11 Delta11 : Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : Matrix (Fin m) (Fin m) ℝ)
    (That Phat DeltaFirst DeltaSecond : Matrix (Fin m) (Fin r) ℝ)
    (hStep : Higham14Problem142Method2BStepSpec hr hm u cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : RightTriangularSolveFirstOrderSpec u cDiag
      (maxEntryNormRect hr hr L11) (maxEntryNormRect hr hr X11)
      (maxEntryNormRect hr hr Delta11)
      L11 (1 : Matrix (Fin r) (Fin r) ℝ) Delta11 X11)
    (h22 : FirstOrderLe u leading22
      (maxEntryNormRect hm hm
        (X22 * L22 - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hcFirst : 0 ≤ cFirst) (hcSecond : 0 ≤ cSecond)
    (hcDiag : 0 ≤ cDiag) :
    FirstOrderLe u
      (max
        (cDiag * u * maxEntryNormRect hr hr L11 *
          maxEntryNormRect hr hr X11)
        (max
          (higham14_problem14_2_method2B_uncontrolledLeading (r := r) (m := m)
            u cFirst cSecond cDiag
            (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
            (maxEntryNormRect hr hr X11) (maxEntryNormRect hr hr L11))
          leading22))
      (maxEntryNormRect (Nat.add_pos_left hr m) (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock X11 X21 X22 *
          higham14_problem14_2_lowerBlock L11 L21 L22 -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have h11 : FirstOrderLe u
      (cDiag * u * maxEntryNormRect hr hr L11 *
        maxEntryNormRect hr hr X11)
      (maxEntryNormRect hr hr
        (X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ))) := by
    have hEq : X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ) = Delta11 := by
      rw [hDiag.equation]
      abel
    rw [hEq]
    exact hDiag.norm_bound
  have h21 := hStep.offdiag_residual_firstOrder hDiag hu0 hu1
    hcFirst hcSecond hcDiag
  rw [higham14_problem14_2_lowerBlock_mul_sub_one]
  exact higham14_problem14_2_lowerBlock_residual_firstOrder hr hm u
    (cDiag * u * maxEntryNormRect hr hr L11 *
      maxEntryNormRect hr hr X11)
    (higham14_problem14_2_method2B_uncontrolledLeading (r := r) (m := m)
      u cFirst cSecond cDiag
      (maxEntryNormRect hm hm X22) (maxEntryNormRect hm hr L21)
      (maxEntryNormRect hr hr X11) (maxEntryNormRect hr hr L11))
    leading22
    (X11 * L11 - (1 : Matrix (Fin r) (Fin r) ℝ))
    (X21 * L11 + X22 * L21)
    (X22 * L22 - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 h21 h22

end Ch14Ext
end NumStability
