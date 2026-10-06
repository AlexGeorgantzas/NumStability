import NumStability.Algorithms.Summation.Compensated.FiniteFormat
import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Source.Higham.Chapter09.DoolittleClosure
import NumStability.Source.Higham.Chapter19.Theorem06.ColumnPivot

/-!
# Chapter08 Section04 FanInAsymptotics Basic

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapters1To9SourceClosure` by wave W12 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open Filter Asymptotics
open scoped BigOperators
open scoped Topology
open scoped Matrix.Norms.Operator

namespace NumStability

/-- The bounded coefficient in the identity
`gamma_n(u) = u * higham8_18_gammaUnitCoefficient n u`. -/
noncomputable def higham8_18_gammaUnitCoefficient (n : ℕ) (u : ℝ) : ℝ :=
  (n : ℝ) / (1 - (n : ℝ) * u)

theorem higham8_18_gamma_eq_unit_mul_coefficient (fp : FPModel) (n : ℕ) :
    gamma fp n = fp.u * higham8_18_gammaUnitCoefficient n fp.u := by
  unfold gamma higham8_18_gammaUnitCoefficient
  ring

theorem higham8_18_gammaUnitCoefficient_continuousAt_zero (n : ℕ) :
    ContinuousAt (higham8_18_gammaUnitCoefficient n) 0 := by
  unfold higham8_18_gammaUnitCoefficient
  exact continuousAt_const.div
    (continuousAt_const.sub (continuousAt_const.mul continuousAt_id))
    (by norm_num)

/-- With the operation count fixed, `gamma_n` is uniformly `O(u)` along a
vanishing-roundoff family. -/
theorem higham8_18_gamma_family_isBigO_unit
    {ι : Type*} {l : Filter ι} (fp : ι → FPModel) (n : ℕ)
    (hu : Tendsto (fun t => (fp t).u) l (𝓝 0)) :
    (fun t => gamma (fp t) n) =O[l] (fun t => (fp t).u) := by
  have hu_refl := Asymptotics.isBigO_refl (fun t => (fp t).u) l
  have hcoeff :
      (fun t => higham8_18_gammaUnitCoefficient n (fp t).u) =O[l]
        (fun _ : ι => (1 : ℝ)) := by
    simpa only [Function.comp_apply] using
      (higham8_18_gammaUnitCoefficient_continuousAt_zero n).tendsto.isBigO_one
        ℝ |>.comp_tendsto hu
  simpa only [higham8_18_gamma_eq_unit_mul_coefficient, mul_one] using
    hu_refl.mul hcoeff

/-- Entrywise asymptotic comparison for a family of fixed-size matrices. -/
def Higham8MatrixFamilyIsBigO {ι : Type*} {n : ℕ} (l : Filter ι)
    (scale : ι → ℝ) (X : ι → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, (fun t => X t i j) =O[l] scale

end NumStability
