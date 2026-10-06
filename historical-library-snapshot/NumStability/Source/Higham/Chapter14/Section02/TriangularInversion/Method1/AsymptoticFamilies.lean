import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Orthogonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Algorithms.MatMul
import NumStability.Algorithms.MatVec
import NumStability.Algorithms.TestMatrices.UpperTriangularStress
import NumStability.Analysis.Error.RoundingProducts.Core
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.MatrixNorms.HadamardDeterminant
import NumStability.Analysis.Perturbation.LeastSquares.Wedin
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.AsymptoticFamilies
import NumStability.Source.Higham.Chapter14.Section01.InverseErrorAnalysis.ForwardErrorEndpoint

/-!
# Chapter14 Section02 TriangularInversion Method1 AsymptoticFamilies

Canonical destination for material split out of
`NumStability.Algorithms.Ch14AsymptoticFamilies` by wave W08 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators Topology
open NumStability

namespace NumStability

namespace Ch14Ext

/-- The Method 1 inverse produced at one member of a family. -/
noncomputable def ch14ext_eq14_6_familyX {ι : Type*} {l : Filter ι}
    (n : ℕ) (L : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (t : ι) : Fin n → Fin n → ℝ :=
  fun i j => fl_forwardSub (F.model t) n L
    (fun k => if k = j then 1 else 0) i

/-- The actual varying quadratic remainder in the Method 1 endpoint. -/
noncomputable def ch14ext_eq14_6_familyRemainder {ι : Type*} {l : Filter ι}
    (n : ℕ) (L L_inv : Fin n → Fin n → ℝ)
    (F : Ch14Eq146Family ι l n L) (i j : Fin n) (t : ι) : ℝ :=
  (F.model t).u ^ 2 *
    (ch14ext_gammaQuadraticCoefficient (F.model t) n *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| * |L_inv k₂ j|)) +
      (ch14ext_gammaUnitCoefficient (F.model t) n) ^ 2 *
        (∑ k₁ : Fin n, |L_inv i k₁| *
          (∑ k₂ : Fin n, |L k₁ k₂| *
            ch14ext_rightResidualEnvelopeRemainder n L L_inv
              (ch14ext_eq14_6_familyX n L F t) k₂ j)))

/-- The matrix product defining `cond(L⁻¹)` has infinity norm at most the
repository Skeel condition number. -/
theorem ch14ext_eq14_7_inverseProduct_infNorm_le_condSkeel
    (n : ℕ) (hn : 0 < n) (L L_inv : Fin n → Fin n → ℝ) :
    infNorm (matMul n (absMatrix n L) (absMatrix n L_inv)) ≤
      condSkeel n hn L_inv L := by
  apply infNorm_le_of_row_sum_le
  · intro i
    have hentry : ∀ j : Fin n,
        |matMul n (absMatrix n L) (absMatrix n L_inv) i j| =
          ∑ k : Fin n, |L i k| * |L_inv k j| := by
      intro j
      rw [abs_of_nonneg]
      · rfl
      · exact Finset.sum_nonneg
          (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
    calc
      ∑ j : Fin n,
          |matMul n (absMatrix n L) (absMatrix n L_inv) i j| =
          ∑ j : Fin n, ∑ k : Fin n, |L i k| * |L_inv k j| :=
        Finset.sum_congr rfl (fun j _ => hentry j)
      _ = ∑ k : Fin n, ∑ j : Fin n, |L i k| * |L_inv k j| :=
        Finset.sum_comm
      _ = ∑ k : Fin n, |L i k| * ∑ j : Fin n, |L_inv k j| := by
        apply Finset.sum_congr rfl
        intro k _hk
        rw [Finset.mul_sum]
      _ ≤ condSkeel n hn L_inv L := by
        unfold condSkeel
        exact Finset.le_sup'
          (fun a => ∑ k : Fin n, |L a k| * ∑ j : Fin n, |L_inv k j|)
          (Finset.mem_univ i)
  · unfold condSkeel
    let i : Fin n := ⟨0, hn⟩
    exact le_trans
      (Finset.sum_nonneg (fun k _ =>
        mul_nonneg (abs_nonneg _) (Finset.sum_nonneg
          (fun j _ => abs_nonneg (L_inv k j)))))
      (Finset.le_sup'
        (fun a => ∑ k : Fin n, |L a k| * ∑ j : Fin n, |L_inv k j|)
        (Finset.mem_univ i))

/-- The fixed leading matrix in (14.6), normalized by `||L⁻¹||∞`, is bounded
by the printed `cond(L⁻¹)`. -/
theorem ch14ext_eq14_7_leading_infNorm_le
    (n : ℕ) (hn : 0 < n) (L L_inv : Fin n → Fin n → ℝ) :
    infNorm
        (matMul n (absMatrix n L_inv)
          (matMul n (absMatrix n L) (absMatrix n L_inv))) ≤
      infNorm L_inv * condSkeel n hn L_inv L := by
  calc
    infNorm
        (matMul n (absMatrix n L_inv)
          (matMul n (absMatrix n L) (absMatrix n L_inv))) ≤
        infNorm (absMatrix n L_inv) *
          infNorm (matMul n (absMatrix n L) (absMatrix n L_inv)) :=
      infNorm_matMul_le hn _ _
    _ = infNorm L_inv *
          infNorm (matMul n (absMatrix n L) (absMatrix n L_inv)) := by
      rw [infNorm_absMatrix hn]
    _ ≤ infNorm L_inv * condSkeel n hn L_inv L :=
      mul_le_mul_of_nonneg_left
        (ch14ext_eq14_7_inverseProduct_infNorm_le_condSkeel n hn L L_inv)
        (infNorm_nonneg L_inv)

/-- Matrix of explicit entrywise remainders used by the normwise endpoint. -/
noncomputable def ch14ext_eq14_7_familyRemainderMatrix
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (t : ι) : Fin n → Fin n → ℝ :=
  fun i j => ch14ext_eq14_6_familyRemainder n L L_inv F i j t

/-- The normalized normwise remainder in equation (14.7). -/
noncomputable def ch14ext_eq14_7_familyRemainder
    {ι : Type*} {l : Filter ι} (n : ℕ)
    (L L_inv : Fin n → Fin n → ℝ) (F : Ch14Eq146Family ι l n L)
    (t : ι) : ℝ :=
  infNorm (ch14ext_eq14_7_familyRemainderMatrix n L L_inv F t) /
    infNorm L_inv

end Ch14Ext
end NumStability
