/-
Algorithms/Cholesky/AasenAdjacentPivotTridiagForwardCounterexampleCh11.lean

A concrete obstruction to the dimension-independent `gamma_1` forward premise
in the printed tridiagonal-GEPP `gamma_6` assembly.  The literal three-by-three
executor below takes two consecutive adjacent pivots.  Its conventional
accumulated lower factor has last row `[1/2, -101/400, 1]`, while the associated
RHS accumulator passes through two rounded subtractions.  The final theorem
proves that no perturbation bounded by `gamma_1 |M|` can satisfy the accumulated
forward equation.  The model also satisfies `gammaValid fp 6`.
-/
import NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagExecutorCh11Closure

open scoped BigOperators

namespace NumStability.Ch11Closure.AasenAdjacentGEPP

open NumStability
open NumStability.Ch11Closure.SparseFactor

set_option maxRecDepth 20000

/-- Exact arithmetic except that every subtraction is biased upward by one
unit roundoff. -/
noncomputable def forwardCounterFP : FPModel where
  u := 1 / 100
  u_nonneg := by norm_num
  fl_add := fun x y => x + y
  fl_sub := fun x y => (x - y) * (1 + 1 / 100)
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; ring
  model_add := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_sub := by
    intro x y
    refine ⟨1 / 100, by norm_num, ?_⟩
    ring
  model_mul := by
    intro x y
    refine ⟨0, by norm_num, by ring⟩
  model_div := by
    intro x y _
    refine ⟨0, by norm_num, by ring⟩
  model_sqrt := by
    intro x _
    refine ⟨0, by norm_num, by ring⟩

noncomputable def forwardCounterT : Fin 3 → Fin 3 → ℝ :=
  fun i j => if i = j then 1 / 2 else if i.val = j.val + 1 then 1 else 0

noncomputable def forwardCounterZ : Fin 3 → ℝ :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then 1 / 100 else -(1 / 100)

noncomputable def forwardCounterS0 : DGTTRFData 3 :=
  dgttrfInit 3 forwardCounterT

noncomputable def forwardCounterS1 : DGTTRFData 3 :=
  flDGTTRFStepAt forwardCounterFP forwardCounterS0 0 (by omega)

noncomputable def forwardCounterS2 : DGTTRFData 3 :=
  flDGTTRFStepAt forwardCounterFP forwardCounterS1 1 (by omega)

theorem forwardCounter_run_eq :
    flDGTTRF forwardCounterFP 3 forwardCounterT = forwardCounterS2 := by
  rfl

theorem forwardCounterS0_d0 : forwardCounterS0.d 0 = 1 / 2 := by
  rfl

theorem forwardCounterS0_d1 : forwardCounterS0.d 1 = 1 / 2 := by
  rfl

theorem forwardCounterS0_dl0 : forwardCounterS0.dl 0 = 1 := by
  rfl

theorem forwardCounterS0_dl1 : forwardCounterS0.dl 1 = 1 := by
  rfl

theorem forwardCounterS0_du0 : forwardCounterS0.du 0 = 0 := by
  rfl

theorem forwardCounterS0_ipiv0 : forwardCounterS0.ipiv 0 = false := by
  rfl

theorem forwardCounterS0_ipiv1 : forwardCounterS0.ipiv 1 = false := by
  rfl

theorem forwardCounterS0_choice0 :
    ¬ |forwardCounterS0.d 0| ≥ |forwardCounterS0.dl 0| := by
  rw [forwardCounterS0_d0, forwardCounterS0_dl0]
  norm_num

theorem forwardCounterS1_ipiv0 : forwardCounterS1.ipiv 0 = true := by
  simp [forwardCounterS1, flDGTTRFStepAt, forwardCounterS0_choice0,
    finReplace]

theorem forwardCounterS1_ipiv1 : forwardCounterS1.ipiv 1 = false := by
  simp [forwardCounterS1, flDGTTRFStepAt, forwardCounterS0_choice0,
    finReplace, forwardCounterS0_ipiv1]

theorem forwardCounterS1_dl0 : forwardCounterS1.dl 0 = 1 / 2 := by
  simp [forwardCounterS1, flDGTTRFStepAt, forwardCounterS0_choice0,
    finReplace, forwardCounterS0_d0, forwardCounterS0_dl0,
    forwardCounterFP, skipZeroSubFP]
  norm_num

theorem forwardCounterS1_dl1 : forwardCounterS1.dl 1 = 1 := by
  simp [forwardCounterS1, flDGTTRFStepAt, forwardCounterS0_choice0,
    finReplace, forwardCounterS0_dl1]

theorem forwardCounterS1_d1 : forwardCounterS1.d 1 = -(101 / 400) := by
  simp [forwardCounterS1, flDGTTRFStepAt, forwardCounterS0_choice0,
    finReplace, forwardCounterS0_d0, forwardCounterS0_dl0,
    forwardCounterS0_d1, forwardCounterS0_du0,
    forwardCounterFP, skipZeroSubFP]
  norm_num

theorem forwardCounter_ipiv0 :
    (flDGTTRF forwardCounterFP 3 forwardCounterT).ipiv 0 = true := by
  rw [forwardCounter_run_eq]
  norm_num [forwardCounterS2, flDGTTRFStepAt, forwardCounterS1_d1,
    forwardCounterS1_dl1, forwardCounterS1_ipiv0, forwardCounterFP,
    skipZeroSubFP, finReplace, finSwap]

theorem forwardCounter_ipiv1 :
    (flDGTTRF forwardCounterFP 3 forwardCounterT).ipiv 1 = true := by
  rw [forwardCounter_run_eq]
  norm_num [forwardCounterS2, flDGTTRFStepAt, forwardCounterS1_d1,
    forwardCounterS1_dl1, forwardCounterFP, skipZeroSubFP, finReplace, finSwap]

theorem forwardCounter_dl0 :
    (flDGTTRF forwardCounterFP 3 forwardCounterT).dl 0 = 1 / 2 := by
  rw [forwardCounter_run_eq]
  norm_num [forwardCounterS2, flDGTTRFStepAt, forwardCounterS1_d1,
    forwardCounterS1_dl1, forwardCounterS1_dl0, forwardCounterFP,
    skipZeroSubFP, finReplace, finSwap]

theorem forwardCounter_dl1 :
    (flDGTTRF forwardCounterFP 3 forwardCounterT).dl 1 = -(101 / 400) := by
  rw [forwardCounter_run_eq]
  norm_num [forwardCounterS2, flDGTTRFStepAt, forwardCounterS1_d1,
    forwardCounterS1_dl1, forwardCounterFP, skipZeroSubFP, finReplace, finSwap]

theorem forwardCounter_M_row :
    (fun j => dgttrfM (flDGTTRF forwardCounterFP 3 forwardCounterT) 2 j) =
      fun j => if j.val = 0 then 1 / 2 else if j.val = 1 then -(101 / 400) else 1 := by
  funext j
  fin_cases j <;>
    simp [dgttrfM, dgttrfMRun, dgttrfMStepAt, dgttrfMInit,
      forwardCounter_ipiv0, forwardCounter_ipiv1,
      forwardCounter_dl0, forwardCounter_dl1]

noncomputable def forwardCounterX1 : Fin 3 → ℝ :=
  flDGTTRSForwardStepAt forwardCounterFP
    (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterZ 0 (by omega)

theorem forwardCounterX1_0 : forwardCounterX1 0 = 1 / 100 := by
  simp [forwardCounterX1, flDGTTRSForwardStepAt, forwardCounter_ipiv0,
    forwardCounterZ, finReplace]

theorem forwardCounterX1_1 : forwardCounterX1 1 = 20099 / 20000 := by
  simp [forwardCounterX1, flDGTTRSForwardStepAt, forwardCounter_ipiv0,
    forwardCounter_dl0, forwardCounterZ, finReplace]
  norm_num [forwardCounterFP, skipZeroSubFP]

theorem forwardCounterX1_2 : forwardCounterX1 2 = -(1 / 100) := by
  simp [forwardCounterX1, flDGTTRSForwardStepAt, forwardCounter_ipiv0,
    forwardCounterZ, finReplace]

noncomputable def forwardCounterX2 : Fin 3 → ℝ :=
  flDGTTRSForwardStepAt forwardCounterFP
    (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterX1 1 (by omega)

theorem forwardCounterX2_0 : forwardCounterX2 0 = 1 / 100 := by
  simp [forwardCounterX2, flDGTTRSForwardStepAt, forwardCounter_ipiv1,
    forwardCounterX1_0, finReplace]

theorem forwardCounterX2_1 : forwardCounterX2 1 = -(1 / 100) := by
  simp [forwardCounterX2, flDGTTRSForwardStepAt, forwardCounter_ipiv1,
    forwardCounterX1_2, finReplace]

theorem forwardCounterX2_2 : forwardCounterX2 2 = 4049797 / 4000000 := by
  simp [forwardCounterX2, flDGTTRSForwardStepAt, forwardCounter_ipiv1,
    forwardCounter_dl1, forwardCounterX1_1, forwardCounterX1_2,
    finReplace]
  norm_num [forwardCounterFP, skipZeroSubFP]

theorem forwardCounter_forward_run_eq :
    flDGTTRSForward forwardCounterFP
      (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterZ =
      forwardCounterX2 := by
  rfl

theorem forwardCounter_q :
    flDGTTRSForward forwardCounterFP
      (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterZ =
      fun i => if i.val = 0 then 1 / 100 else if i.val = 1 then -(1 / 100)
        else 4049797 / 4000000 := by
  rw [forwardCounter_forward_run_eq]
  funext i
  fin_cases i <;> simp [forwardCounterX2_0, forwardCounterX2_1,
    forwardCounterX2_2]

theorem forwardCounter_perm_last :
    dgttrfPermEquiv (flDGTTRF forwardCounterFP 3 forwardCounterT) 2 = 0 := by
  norm_num [dgttrfPermEquiv, dgttrfPermEquivRun, forwardCounter_ipiv0,
    forwardCounter_ipiv1, Equiv.swap_apply_def, Fin.ext_iff]

theorem forwardCounter_gammaValid_six : gammaValid forwardCounterFP 6 := by
  norm_num [gammaValid, forwardCounterFP]

/-- Two consecutive adjacent pivots already refute a global `gamma_1`
componentwise forward certificate against the conventional accumulated lower
factor. -/
theorem forwardCounter_not_factor_forward_certificate :
    ¬ DGTTRFFactorForwardCertificate forwardCounterFP 3
      forwardCounterT forwardCounterZ := by
  intro hcert
  dsimp only [DGTTRFFactorForwardCertificate] at hcert
  rcases hcert with ⟨DeltaF, DeltaM, _hfactor, _hDeltaF, hforward, hDeltaM⟩
  have hM0 :
      dgttrfM (flDGTTRF forwardCounterFP 3 forwardCounterT) 2 0 = 1 / 2 := by
    simpa using congrFun forwardCounter_M_row (0 : Fin 3)
  have hM1 :
      dgttrfM (flDGTTRF forwardCounterFP 3 forwardCounterT) 2 1 =
        -(101 / 400) := by
    simpa using congrFun forwardCounter_M_row (1 : Fin 3)
  have hM2 :
      dgttrfM (flDGTTRF forwardCounterFP 3 forwardCounterT) 2 2 = 1 := by
    simpa using congrFun forwardCounter_M_row (2 : Fin 3)
  have hq0 :
      flDGTTRSForward forwardCounterFP
        (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterZ 0 =
          1 / 100 := by
    simpa using congrFun forwardCounter_q (0 : Fin 3)
  have hq1 :
      flDGTTRSForward forwardCounterFP
        (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterZ 1 =
          -(1 / 100) := by
    simpa using congrFun forwardCounter_q (1 : Fin 3)
  have hq2 :
      flDGTTRSForward forwardCounterFP
        (flDGTTRF forwardCounterFP 3 forwardCounterT) forwardCounterZ 2 =
          4049797 / 4000000 := by
    simpa using congrFun forwardCounter_q (2 : Fin 3)
  have hrow := hforward (2 : Fin 3)
  rw [Fin.sum_univ_three, hM0, hM1, hM2, hq0, hq1, hq2,
    forwardCounter_perm_last] at hrow
  norm_num [forwardCounterZ] at hrow
  have hb0 := hDeltaM (2 : Fin 3) (0 : Fin 3)
  have hb1 := hDeltaM (2 : Fin 3) (1 : Fin 3)
  have hb2 := hDeltaM (2 : Fin 3) (2 : Fin 3)
  rw [hM0] at hb0
  rw [hM1] at hb1
  rw [hM2] at hb2
  norm_num [gamma, forwardCounterFP] at hb0 hb1 hb2
  rcases abs_le.mp hb0 with ⟨hb0lo, hb0hi⟩
  rcases abs_le.mp hb1 with ⟨hb1lo, hb1hi⟩
  rcases abs_le.mp hb2 with ⟨hb2lo, hb2hi⟩
  linarith

end NumStability.Ch11Closure.AasenAdjacentGEPP
