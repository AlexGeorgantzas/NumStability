import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Basic
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.Families
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockFirstOrder.Derivations
import NumStability.Source.Higham.Chapter14.Problem02.TriangularInversion.TwoBlockMethod2B.FirstOrderBound
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ComposedCoefficientFamilies.RemainderAsymptotics

/-!
# Derivations

Canonical destination for the Chapter14.Problem02 declarations relocated from the
historical path `NumStability.Algorithms.Ch14Problem142Families` during wave R08.
Holds 5 declaration(s): 5 public.

Declaration names, kinds, signatures and visibilities are unchanged; the
authored-private declarations keep their names and change only their
mangled module owner, per the reviewed R08 private-normalization map.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace NumStability

namespace Ch14Ext

theorem ch14ext_problem14_2_method1B_twoBlock_right_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (cMul cSolve : ℝ)
    (leading11 leading22 : ι → ℝ)
    (L11 X11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ)
    (h11 : Ch14FamilyFirstOrderLe l U.unit leading11
      (fun t => maxEntryNormRect hr hr
        (L11 t * X11 t - (1 : Matrix (Fin r) (Fin r) ℝ))))
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm
        (L22 t * X22 t - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hstep : Ch14Problem142Method1BStepFamily U hr hm cMul cSolve
      L21 L22 X11 X21 That DeltaMul DeltaSolve) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max (leading11 t)
        (max
          (cMul * U.unit t * maxEntryNormRect hm hr (L21 t) *
              maxEntryNormRect hr hr (X11 t) +
            cSolve * U.unit t * maxEntryNormRect hm hm (L22 t) *
              maxEntryNormRect hm hr (X21 t))
          (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t) *
          higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t) -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have hblocks := ch14ext_problem14_2_lowerBlock_residual_family hr hm
    leading11
    (fun t =>
      cMul * U.unit t * maxEntryNormRect hm hr (L21 t) *
          maxEntryNormRect hr hr (X11 t) +
        cSolve * U.unit t * maxEntryNormRect hm hm (L22 t) *
          maxEntryNormRect hm hr (X21 t))
    leading22
    (fun t => L11 t * X11 t - (1 : Matrix (Fin r) (Fin r) ℝ))
    (fun t => L21 t * X11 t + L22 t * X21 t)
    (fun t => L22 t * X22 t - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 hstep.offdiag_family h22
  exact hblocks.mono_value (fun t => by
    rw [higham14_problem14_2_lowerBlock_mul_sub_one])

theorem ch14ext_problem14_2_method2C_twoBlock_left_family
    {ι : Type*} {l : Filter ι} {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m) (cMul cSolve : ℝ)
    (leading11 leading22 : ι → ℝ)
    (L11 X11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That DeltaMul DeltaSolve : ι → Matrix (Fin m) (Fin r) ℝ)
    (h11 : Ch14FamilyFirstOrderLe l U.unit leading11
      (fun t => maxEntryNormRect hr hr
        (X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ))))
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm
        (X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ))))
    (hstep : Ch14Problem142Method2CStepFamily U hr hm cMul cSolve
      L11 L21 X21 X22 That DeltaMul DeltaSolve) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max (leading11 t)
        (max
          (cMul * U.unit t * maxEntryNormRect hm hm (X22 t) *
              maxEntryNormRect hm hr (L21 t) +
            cSolve * U.unit t * maxEntryNormRect hr hr (L11 t) *
              maxEntryNormRect hm hr (X21 t))
          (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t) *
          higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t) -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have hblocks := ch14ext_problem14_2_lowerBlock_residual_family hr hm
    leading11
    (fun t =>
      cMul * U.unit t * maxEntryNormRect hm hm (X22 t) *
          maxEntryNormRect hm hr (L21 t) +
        cSolve * U.unit t * maxEntryNormRect hr hr (L11 t) *
          maxEntryNormRect hm hr (X21 t))
    leading22
    (fun t => X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ))
    (fun t => X21 t * L11 t + X22 t * L21 t)
    (fun t => X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 hstep.offdiag_family h22
  exact hblocks.mono_value (fun t => by
    rw [higham14_problem14_2_lowerBlock_mul_sub_one])

/-- Method 1B recursive closure with one filter-uniform `O(u²)` remainder.
No residual bound appears in the derivation constructors. -/
theorem Ch14Problem142Method1BFamilyDerivation.right_residual_family
    {ι : Type*} {l : Filter ι} [NeBot l] {U : Ch14RoundoffFamily ι l}
    {n : ℕ} {L X : ι → Matrix (Fin n) (Fin n) ℝ}
    {leading : ι → ℝ}
    (h : Ch14Problem142Method1BFamilyDerivation U L X leading) :
    ∀ hn : 0 < n,
      Ch14FamilyFirstOrderLe l U.unit leading
        (fun t => maxEntryNormRect hn hn
          (L t * X t - (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  induction h with
  | leaf hn cSolve L X Delta solve =>
      intro _hn'
      exact solve.norm_bound.mono_value (fun t => by
        have heq : L t * X t - (1 : Matrix (Fin _ ) (Fin _) ℝ) = Delta t := by
          rw [solve.equation t]
          abel
        rw [heq])
  | split hr hm cMul cSolve leading11 leading22 L11 X11 L21 X21 L22 X22
      That DeltaMul DeltaSolve head tail step ihHead ihTail =>
      intro _hsum
      exact ch14ext_problem14_2_method1B_twoBlock_right_family
        hr hm cMul cSolve leading11 leading22
        L11 X11 L21 X21 L22 X22 That DeltaMul DeltaSolve
        (ihHead hr) (ihTail hm) step

/-- Method 2C recursive closure with a uniform quadratic remainder. -/
theorem Ch14Problem142Method2CFamilyDerivation.left_residual_family
    {ι : Type*} {l : Filter ι} [NeBot l] {U : Ch14RoundoffFamily ι l}
    {n : ℕ} {L X : ι → Matrix (Fin n) (Fin n) ℝ}
    {leading : ι → ℝ}
    (h : Ch14Problem142Method2CFamilyDerivation U L X leading) :
    ∀ hn : 0 < n,
      Ch14FamilyFirstOrderLe l U.unit leading
        (fun t => maxEntryNormRect hn hn
          (X t * L t - (1 : Matrix (Fin n) (Fin n) ℝ))) := by
  induction h with
  | leaf hn cSolve L X Delta solve =>
      intro _hn'
      exact solve.norm_bound.mono_value (fun t => by
        have heq : X t * L t - (1 : Matrix (Fin _) (Fin _) ℝ) = Delta t := by
          rw [solve.equation t]
          abel
        rw [heq])
  | split hr hm cMul cSolve leading11 leading22 L11 X11 L21 X21 L22 X22
      That DeltaMul DeltaSolve head tail step ihHead ihTail =>
      intro _hsum
      exact ch14ext_problem14_2_method2C_twoBlock_left_family
        hr hm cMul cSolve leading11 leading22
        L11 X11 L21 X21 L22 X22 That DeltaMul DeltaSolve
        (ihHead hr) (ihTail hm) step

/-- Two-block integration of the Method 2B family obstruction with a
recursively obtained trailing-block estimate. -/
theorem ch14ext_problem14_2_method2B_twoBlock_left_family
    {ι : Type*} {l : Filter ι} [NeBot l] {U : Ch14RoundoffFamily ι l}
    {r m : ℕ} (hr : 0 < r) (hm : 0 < m)
    (cFirst cSecond cDiag : ℝ) (leading22 : ι → ℝ)
    (L11 X11 Delta11 : ι → Matrix (Fin r) (Fin r) ℝ)
    (L21 X21 : ι → Matrix (Fin m) (Fin r) ℝ)
    (L22 X22 : ι → Matrix (Fin m) (Fin m) ℝ)
    (That Phat DeltaFirst DeltaSecond : ι → Matrix (Fin m) (Fin r) ℝ)
    (hStep : Ch14Problem142Method2BStepFamily U hr hm cFirst cSecond
      X22 L21 X11 That Phat X21 DeltaFirst DeltaSecond)
    (hDiag : Ch14RightTriangularSolveFamilySpec U hr hr cDiag
      L11 (fun _ => (1 : Matrix (Fin r) (Fin r) ℝ)) Delta11 X11)
    (h22 : Ch14FamilyFirstOrderLe l U.unit leading22
      (fun t => maxEntryNormRect hm hm
        (X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ)))) :
    Ch14FamilyFirstOrderLe l U.unit
      (fun t => max
        (cDiag * U.unit t * maxEntryNormRect hr hr (L11 t) *
          maxEntryNormRect hr hr (X11 t))
        (max
          (ch14ext_problem14_2_method2B_familyUncontrolledLeading
            (r := r) (m := m) U.unit cFirst cSecond cDiag hm hr
            X22 L21 That X11 L11 t)
          (leading22 t)))
      (fun t => maxEntryNormRect (Nat.add_pos_left hr m)
        (Nat.add_pos_left hr m)
        (higham14_problem14_2_lowerBlock (X11 t) (X21 t) (X22 t) *
          higham14_problem14_2_lowerBlock (L11 t) (L21 t) (L22 t) -
            (1 : Matrix (Fin (r + m)) (Fin (r + m)) ℝ))) := by
  have h11 := Ch14FamilyFirstOrderLe.mono_value
    (value₁ := fun t => maxEntryNormRect hr hr
      (X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ)))
    hDiag.norm_bound (fun t => by
    have heq : X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ) =
        Delta11 t := by
      rw [hDiag.equation t]
      abel
    change maxEntryNormRect hr hr
      (X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ)) ≤ _
    rw [heq])
  have h21 := hStep.offdiag_residual_family hDiag
  have hblocks := ch14ext_problem14_2_lowerBlock_residual_family hr hm
    (fun t => cDiag * U.unit t * maxEntryNormRect hr hr (L11 t) *
      maxEntryNormRect hr hr (X11 t))
    (ch14ext_problem14_2_method2B_familyUncontrolledLeading
      (r := r) (m := m) U.unit cFirst cSecond cDiag hm hr
      X22 L21 That X11 L11)
    leading22
    (fun t => X11 t * L11 t - (1 : Matrix (Fin r) (Fin r) ℝ))
    (fun t => X21 t * L11 t + X22 t * L21 t)
    (fun t => X22 t * L22 t - (1 : Matrix (Fin m) (Fin m) ℝ))
    h11 h21 h22
  exact hblocks.mono_value (fun t => by
    rw [higham14_problem14_2_lowerBlock_mul_sub_one])

end Ch14Ext
end NumStability
