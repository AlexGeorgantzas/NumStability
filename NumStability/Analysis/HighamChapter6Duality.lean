-- Analysis/HighamChapter6Duality.lean
--
-- The duality theorem used in Higham, Chapter 6, equation (6.2).

import Mathlib.Analysis.Normed.Module.Dual
import NumStability.Analysis.Norms

namespace NumStability

noncomputable section

/-!
# Higham Chapter 6: the dual of the dual norm

Higham states after (6.2) that the dual of the dual norm is the original
norm.  The first theorem below exposes Mathlib's general Hahn--Banach
isometry into the continuous double dual.  The second theorem specializes
the statement to the source-facing `CVec`/`IsComplexVectorNorm` interface
used throughout this repository: evaluation at `x` has maximum `ν x` over
all complex-linear functionals of dual norm at most one.
-/

/-- General normed-space form of Higham's duality theorem: the canonical
embedding into the continuous double dual preserves the norm. -/
theorem higham6_dual_of_dual_norm_eq_original
    {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (x : E) :
    ‖NormedSpace.inclusionInDoubleDual 𝕜 E x‖ = ‖x‖ := by
  exact (NormedSpace.inclusionInDoubleDualLi (E := E) 𝕜).norm_map x

/-- Values obtained by evaluating `x` with a complex-linear functional
whose source-facing dual norm is at most one. -/
def HighamDoubleDualEvaluationSet {n : ℕ} (ν : CVec n → ℝ) (x : CVec n) :
    Set ℝ :=
  {r | ∃ (φ : CVec n → ℂ) (d : ℝ),
      IsDualFunctionalNormValue ν φ d ∧ d ≤ 1 ∧ r = ‖φ x‖}

/-- Source-facing finite-dimensional form of the duality theorem following
Higham (6.2).  For every nontrivial `C^n`, the maximum of `|φ(x)|` over
complex-linear functionals with dual norm at most one is exactly `ν x`.

The maximizing functional is constructed by the repository's Hahn--Banach
norming-functional bridge; the upper bound follows from the defining dual
norm inequality. -/
theorem higham6_doubleDualEvaluation_isGreatest
    {n : ℕ} {ν : CVec n → ℝ} (hν : IsComplexVectorNorm ν) (hn : 0 < n)
    (x : CVec n) :
    IsGreatest (HighamDoubleDualEvaluationSet ν x) (ν x) := by
  constructor
  · by_cases hx : x = 0
    · subst x
      obtain ⟨u, hu⟩ := exists_unit_complexVectorNorm hν hn
      obtain ⟨φ, hφ, _hφu⟩ :=
        exists_dualFunctionalNormValue_one_of_unit_vector hν hu
      refine ⟨φ, 1, hφ, le_rfl, ?_⟩
      rw [hφ.linear.map_zero, norm_zero]
      exact (hν.eq_zero_iff (0 : CVec n)).mpr rfl
    · have hνx_ne : ν x ≠ 0 := by
        intro hzero
        exact hx ((hν.eq_zero_iff x).mp hzero)
      have hνx_pos : 0 < ν x :=
        lt_of_le_of_ne (hν.nonneg x) (Ne.symm hνx_ne)
      obtain ⟨φ, hφ, hφx⟩ :=
        exists_dualFunctionalNormValue_one_of_pos_vector hν hνx_pos
      refine ⟨φ, 1, hφ, le_rfl, ?_⟩
      rw [hφx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hνx_pos]
  · intro r hr
    obtain ⟨φ, d, hφ, hd, rfl⟩ := hr
    calc
      ‖φ x‖ ≤ d * ν x := hφ.bound x
      _ ≤ 1 * ν x := mul_le_mul_of_nonneg_right hd (hν.nonneg x)
      _ = ν x := one_mul _

end

end NumStability
