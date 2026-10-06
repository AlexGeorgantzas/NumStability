-- NumStability/Source/Higham/Chapter08/Equation18/FanInExecutor/FirstOrderForwardError.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Algorithms.HighamChapters1To9SourceClosure`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter04.Algorithm03.SourceClosure.Basic
import NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic
import NumStability.Source.Higham.Chapter07.Equation25.SourceEndpoint.Basic
import NumStability.Source.Higham.Chapter07.Equation26.ComponentwiseDistance.Basic
import NumStability.Source.Higham.Chapter08.Equation10.ColumnPivotedQR.Basic
import NumStability.Source.Higham.Chapter08.Equation14.FanInProduct.Basic
import NumStability.Source.Higham.Chapter08.Section03.BidiagonalComparison.Basic
import NumStability.Source.Higham.Chapter08.Section04.FanInAsymptotics.Basic
import NumStability.Source.Higham.Chapter08.Section04.FanInCore.ResidualForwardBounds
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter09.Theorem15.Barrlund.Basic
import NumStability.Source.Higham.Chapter09.Theorem15.Sun.Basic
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# FirstOrderForwardError

Relocated from `NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


/-!
# HighamChapters1To9SourceClosure (compatibility module)

Historical path, retained so existing imports of `NumStability.Algorithms.HighamChapters1To9SourceClosure`
keep resolving. Most of its declarations moved unchanged to the
canonical modules imported above.

The declarations still defined below are private declarations and
their users. Lean mangles a private name to
`_private.<module>.<n>.<name>`, so relocating one renames it and
breaks the frozen declaration graph; anything referring to one must
therefore stay with it. This module is a declaration-bearing facade,
not a pure import shim.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

private theorem higham8_18_fanIn7AbsApply_nonneg (n : ℕ)
    (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) :
    ∀ i, 0 ≤ higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i := by
  have hmul (A B : Fin n → Fin n → ℝ)
      (hA : ∀ i j, 0 ≤ A i j) (hB : ∀ i j, 0 ≤ B i j) :
      ∀ i j, 0 ≤ matMul n A B i j := by
    intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hB k j))
  have hmulVec (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ)
      (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ i, 0 ≤ x i) :
      ∀ i, 0 ≤ matMulVec n A x i := by
    intro i
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hx k))
  have habs (A : Fin n → Fin n → ℝ) :
      ∀ i j, 0 ≤ absMatrix n A i j := fun i j => abs_nonneg (A i j)
  have h76 := hmul (absMatrix n M7) (absMatrix n M6) (habs M7) (habs M6)
  have h54 := hmul (absMatrix n M5) (absMatrix n M4) (habs M5) (habs M4)
  have h7654 := hmul
    (matMul n (absMatrix n M7) (absMatrix n M6))
    (matMul n (absMatrix n M5) (absMatrix n M4)) h76 h54
  have h32 := hmul (absMatrix n M3) (absMatrix n M2) (habs M3) (habs M2)
  have h321 := hmul
    (matMul n (absMatrix n M3) (absMatrix n M2))
    (absMatrix n M1) h32 (habs M1)
  have hall := hmul
    (matMul n
      (matMul n (absMatrix n M7) (absMatrix n M6))
      (matMul n (absMatrix n M5) (absMatrix n M4)))
    (matMul n
      (matMul n (absMatrix n M3) (absMatrix n M2))
      (absMatrix n M1)) h7654 h321
  exact hmulVec _ (absVec n b) hall (fun i => abs_nonneg (b i))

/-- Family-level `(8.18)` for the literal rounded fan-in executor.  Unlike a
pointwise existential `O(u²)`, this statement has one uniform Landau constant
along the family and therefore records a genuine first-order expansion. -/
theorem higham8_18_fanIn7Executor_family_firstOrder
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hvalid : ∀ t, gammaValid (fp t) n)
    (i : Fin n) :
    FamilyFirstOrderLe l (fun t => (fp t).u)
      (fun t => (7 * (n : ℝ) * (fp t).u) *
        higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i)
      (fun t =>
        |higham8_14_fanIn7Executor (fp t) n M1 M2 M3 M4 M5 M6 M7 b i -
          higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b i|) := by
  let E := higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b i
  refine ⟨fun t => E * higham8_18_fanIn7CoefficientRemainder (fp t) n,
    ?_, ?_, ?_⟩
  · intro t
    exact mul_nonneg
      (higham8_18_fanIn7AbsApply_nonneg n M1 M2 M3 M4 M5 M6 M7 b i)
      (higham8_18_fanIn7CoefficientRemainder_nonneg (fp t) n (hvalid t))
  · intro t
    have h := higham8_18_fanIn7Executor_forward_first_order_remainder_bound
      (fp t) n M1 M2 M3 M4 M5 M6 M7 b (hvalid t) i
    simpa only [E, mul_comm E] using h
  · simpa only [E] using
      (higham8_18_fanIn7CoefficientRemainder_isBigO_unit_sq fp n hu).const_mul_left E

/-- Family-level `(8.15)` for the literal executor.  It upgrades the existing
named remainder split to an actual `O(u²)` residual statement.  Its leading
matrix is intentionally the honest global raw envelope; the source's sharper
five-factor leading term is obtained below from the local perturbation tree. -/
theorem higham8_15_fanIn7Executor_residual_family_firstOrder
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0))
    (n : ℕ) (L M1 M2 M3 M4 M5 M6 M7 : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ) (hvalid : ∀ t, gammaValid (fp t) n)
    (hsolve :
      matMulVec n L (higham8_13_fanIn7Apply n M1 M2 M3 M4 M5 M6 M7 b) = b)
    (i : Fin n) :
    FamilyFirstOrderLe l (fun t => (fp t).u)
      (fun t => (7 * (n : ℝ) * (fp t).u) *
        matMulVec n (absMatrix n L)
          (higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b) i)
      (fun t =>
        |b i - matMulVec n L
          (higham8_14_fanIn7Executor (fp t) n
            M1 M2 M3 M4 M5 M6 M7 b) i|) := by
  let E : Fin n → ℝ :=
    higham8_18_fanIn7AbsApply n M1 M2 M3 M4 M5 M6 M7 b
  let R : ℝ := matMulVec n (absMatrix n L) E i
  have hR : 0 ≤ R := by
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (abs_nonneg (L i j))
        (higham8_18_fanIn7AbsApply_nonneg n M1 M2 M3 M4 M5 M6 M7 b j))
  refine ⟨fun t => R * higham8_18_fanIn7CoefficientRemainder (fp t) n,
    ?_, ?_, ?_⟩
  · intro t
    exact mul_nonneg hR
      (higham8_18_fanIn7CoefficientRemainder_nonneg (fp t) n (hvalid t))
  · intro t
    have h := higham8_15_fanIn7Executor_residual_first_order_remainder_bound
      (fp t) n L M1 M2 M3 M4 M5 M6 M7 b (hvalid t) hsolve i
    let a : ℝ := 7 * (n : ℝ) * (fp t).u
    let r : ℝ := higham8_18_fanIn7CoefficientRemainder (fp t) n
    have hexpand :
        matMulVec n (absMatrix n L) (fun j => a * E j + r * E j) i =
          a * R + R * r := by
      calc
        matMulVec n (absMatrix n L) (fun j => a * E j + r * E j) i =
            matMulVec n (absMatrix n L) (fun j => a * E j) i +
              matMulVec n (absMatrix n L) (fun j => r * E j) i := by
                exact congrFun
                  (matMulVec_add_right n (absMatrix n L)
                    (fun j => a * E j) (fun j => r * E j)) i
        _ = a * R + r * R := by
              rw [congrFun (matMulVec_const_mul_right n (absMatrix n L) a E) i,
                congrFun (matMulVec_const_mul_right n (absMatrix n L) r E) i]
        _ = a * R + R * r := by ring
    change |b i - matMulVec n L
        (higham8_14_fanIn7Executor (fp t) n M1 M2 M3 M4 M5 M6 M7 b) i| ≤
      (7 * (n : ℝ) * (fp t).u) * R +
        R * higham8_18_fanIn7CoefficientRemainder (fp t) n
    exact le_trans h (by simpa [a, r, E, R] using le_of_eq hexpand)
  · simpa only [R] using
      (higham8_18_fanIn7CoefficientRemainder_isBigO_unit_sq fp n hu).const_mul_left R

end NumStability
