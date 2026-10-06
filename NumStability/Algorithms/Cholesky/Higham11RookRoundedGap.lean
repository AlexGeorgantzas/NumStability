/-
Formal boundary for the rounded mixed-pivot executor.

The first witness shows that `FlMixedPivots` alone does not encode the rook
selection schedule.  The second is an aligned, small-unit-roundoff execution
whose rounded scalar Schur update exceeds the exact printed rook-growth cap.
Thus the rounded endpoint needs an explicitly rounding-aware recurrence rather
than the exact source exponent.
-/

import NumStability.Algorithms.Cholesky.Higham11RookExecutorAdapter

namespace NumStability
namespace Higham11RookExecutorAdapter

open Ch11Closure.Mixed

noncomputable def rookGapIdentity2 : Fin 2 → Fin 2 → ℝ :=
  fun i j => if i = j then 1 else 0

theorem rookGapIdentity2_symmetric :
    IsSymmetricFiniteMatrix rookGapIdentity2 := by
  intro i j
  simp only [rookGapIdentity2]
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

theorem rookGapIdentity2_terminalTwo_vacuous (fp : FPModel)
    (cSolve cStage : ℝ) :
    FlMixedPivots fp cSolve cStage (.consTwo .nil) rookGapIdentity2 := by
  simp [FlMixedPivots]

theorem rookGapIdentity2_columnMax_zero :
    higham11_5_rookColumnMax rookGapIdentity2 (0 : Fin 2) = 0 := by
  unfold higham11_5_rookColumnMax
  split_ifs with h
  · simp
  · simp [rookGapIdentity2, h]

theorem rookGapIdentity2_rook_selects_one :
    higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
      rookGapIdentity2 (0 : Fin 2) = PivotSize.one := by
  simp [higham11_5_rookPivotSize, rookGapIdentity2_columnMax_zero,
    rookGapIdentity2]

theorem flMixedPivots_does_not_determine_rook_schedule :
    ∃ fp : FPModel, ∃ cSolve cStage : ℝ,
      IsSymmetricFiniteMatrix rookGapIdentity2 ∧
      FlMixedPivots fp cSolve cStage (.consTwo .nil) rookGapIdentity2 ∧
      higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
        rookGapIdentity2 (0 : Fin 2) = PivotSize.one := by
  refine ⟨FPModel.exactWithUnitRoundoff 0 (by norm_num), 0, 0,
    rookGapIdentity2_symmetric, ?_, rookGapIdentity2_rook_selects_one⟩
  exact rookGapIdentity2_terminalTwo_vacuous _ _ _

noncomputable def rookGapRoundedDivFP : FPModel where
  u := 1 / 200
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => (x / y) * (1 + 1 / 200)
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_div := by
    intro x y _hy
    refine ⟨1 / 200, by norm_num, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, by ring⟩

noncomputable def rookGapRoundedA2 : Fin 2 → Fin 2 → ℝ :=
  fun i j =>
    if i = 0 ∧ j = 0 then -higham11_1_bunchParlettAlpha
    else 1

theorem rookGapRoundedA2_symmetric :
    IsSymmetricFiniteMatrix rookGapRoundedA2 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [rookGapRoundedA2]

theorem rookGapRoundedA2_columnMax_one :
    higham11_5_rookColumnMax rookGapRoundedA2 (0 : Fin 2) = 1 := by
  unfold higham11_5_rookColumnMax
  split_ifs with h
  · have hspec := higham11_5_rookColumnMax_spec rookGapRoundedA2
        (0 : Fin 2) (1 : Fin 2)
    simp [higham11_5_rookColumnMax, h, rookGapRoundedA2] at hspec
    norm_num at hspec
  · simp [rookGapRoundedA2, h]

theorem rookGapRoundedA2_first_rook_scalar :
    higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
      rookGapRoundedA2 (0 : Fin 2) = PivotSize.one := by
  have hα0 : 0 ≤ higham11_1_bunchParlettAlpha :=
    le_of_lt (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  simp [higham11_5_rookPivotSize, rookGapRoundedA2_columnMax_one,
    rookGapRoundedA2,
    abs_of_nonneg hα0]

theorem rookGapRoundedA2_search_stops_at_zero :
    higham11_5_rookSearchStops higham11_1_bunchParlettAlpha
      rookGapRoundedA2 (0 : Fin 2) := by
  left
  have hα0 : 0 ≤ higham11_1_bunchParlettAlpha :=
    le_of_lt (by simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos)
  simp [rookGapRoundedA2_columnMax_one, rookGapRoundedA2,
    abs_of_nonneg hα0]

theorem rookGapRoundedA2_terminalStep_zero :
    higham11_5_rookTerminalStep higham11_1_bunchParlettAlpha
      rookGapRoundedA2 rookGapRoundedA2_symmetric (0 : Fin 2) = 0 := by
  classical
  unfold higham11_5_rookTerminalStep
  apply (Nat.find_eq_zero _).2
  refine ⟨by omega, ?_⟩
  simpa [higham11_5_rookSearchPath] using
    rookGapRoundedA2_search_stops_at_zero

theorem rookGapRoundedDivFP_small :
    ((2 : ℕ) : ℝ) * rookGapRoundedDivFP.u = 1 / 100 := by
  norm_num [rookGapRoundedDivFP]

theorem rookGapRoundedDivFP_gammaValid :
    gammaValid rookGapRoundedDivFP 3 := by
  norm_num [gammaValid, rookGapRoundedDivFP]

theorem rookGapRoundedA2_flSchur_value :
    flSchurCompl 1 rookGapRoundedDivFP rookGapRoundedA2 0 0 =
      1 + (1 + 1 / 200) / higham11_1_bunchParlettAlpha := by
  simp [flSchurCompl, rookGapRoundedDivFP, rookGapRoundedA2]
  ring

theorem rookGapRoundedA2_recursive_rook_scalar :
    higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
      (flSchurCompl 1 rookGapRoundedDivFP rookGapRoundedA2) (0 : Fin 1) =
        PivotSize.one := by
  have hcol : higham11_5_rookColumnMax
      (flSchurCompl 1 rookGapRoundedDivFP rookGapRoundedA2) (0 : Fin 1) = 0 := by
    unfold higham11_5_rookColumnMax
    rw [if_pos (Subsingleton.elim _ _)]
    simp
  simp [higham11_5_rookPivotSize, hcol]

theorem rookGapRoundedA2_growth_violation :
    (1 + higham11_1_bunchParlettAlpha⁻¹) <
      |flSchurCompl 1 rookGapRoundedDivFP rookGapRoundedA2 0 0| := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  rw [rookGapRoundedA2_flSchur_value]
  have hpos : 0 < 1 + (1 + 1 / 200) / higham11_1_bunchParlettAlpha := by
    positivity
  rw [abs_of_pos hpos]
  rw [inv_eq_one_div]
  rw [add_lt_add_iff_left]
  apply (div_lt_div_iff_of_pos_right hα).2
  norm_num

theorem rookGapRoundedA2_mixedPivots
    (cSolve cStage : ℝ) :
    FlMixedPivots rookGapRoundedDivFP cSolve cStage
      (.consOne (.consOne .nil)) rookGapRoundedA2 := by
  have hα : 0 < higham11_1_bunchParlettAlpha := by
    simpa [higham11_1_bunchParlettAlpha] using bunch_parlett_alpha_pos
  simp only [FlMixedPivots]
  refine ⟨?_, ?_, ?_, ?_, trivial⟩
  · simpa [rookGapRoundedA2] using hα.ne'
  · intro i
    fin_cases i
    simp [rookGapRoundedA2]
  · rw [rookGapRoundedA2_flSchur_value]
    positivity
  · intro i
    exact Fin.elim0 i

theorem rookGapRoundedA2_flMixedD_last :
    flMixedD rookGapRoundedDivFP (.consOne (.consOne .nil))
        rookGapRoundedA2 (1 : Fin 2) (1 : Fin 2) =
      flSchurCompl 1 rookGapRoundedDivFP rookGapRoundedA2 0 0 := by
  rfl

theorem rookGapRoundedA2_no_printed_D_growth :
    ¬ ∀ k₁ k₂ : Fin 2,
      |flMixedD rookGapRoundedDivFP (.consOne (.consOne .nil))
          rookGapRoundedA2 k₁ k₂| ≤
        (1 + higham11_1_bunchParlettAlpha⁻¹) * 1 := by
  intro h
  have hlast := h (1 : Fin 2) (1 : Fin 2)
  rw [rookGapRoundedA2_flMixedD_last] at hlast
  have hviol := rookGapRoundedA2_growth_violation
  norm_num at hlast
  linarith

theorem exists_aligned_small_mixedExecutor_without_printed_growth :
    ∃ fp : FPModel, ∃ A : Fin 2 → Fin 2 → ℝ,
      ∃ hA : IsSymmetricFiniteMatrix A,
      gammaValid fp 3 ∧
      ((2 : ℕ) : ℝ) * fp.u ≤ 1 / 100 ∧
      higham11_5_rookTerminalStep higham11_1_bunchParlettAlpha
        A hA (0 : Fin 2) = 0 ∧
      higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
        A (0 : Fin 2) = PivotSize.one ∧
      higham11_5_rookPivotSize higham11_1_bunchParlettAlpha
        (flSchurCompl 1 fp A) (0 : Fin 1) = PivotSize.one ∧
      FlMixedPivots fp 0 0 (.consOne (.consOne .nil)) A ∧
      ¬ ∀ k₁ k₂ : Fin 2,
        |flMixedD fp (.consOne (.consOne .nil)) A k₁ k₂| ≤
          (1 + higham11_1_bunchParlettAlpha⁻¹) * 1 := by
  refine ⟨rookGapRoundedDivFP, rookGapRoundedA2,
    rookGapRoundedA2_symmetric, rookGapRoundedDivFP_gammaValid, ?_,
    rookGapRoundedA2_terminalStep_zero,
    rookGapRoundedA2_first_rook_scalar,
    rookGapRoundedA2_recursive_rook_scalar,
    rookGapRoundedA2_mixedPivots 0 0,
    rookGapRoundedA2_no_printed_D_growth⟩
  rw [rookGapRoundedDivFP_small]

end Higham11RookExecutorAdapter
end NumStability
