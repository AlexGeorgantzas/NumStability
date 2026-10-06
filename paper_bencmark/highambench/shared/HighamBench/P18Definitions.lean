import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace HighamBench

open scoped BigOperators

noncomputable def p18VecNorm2Sq {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i ^ 2

noncomputable def p18VecNorm2 {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (p18VecNorm2Sq x)

def p18Add {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i + y i

def p18Sub {n : ℕ} (x y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => x i - y i

def p18Scale {n : ℕ} (a : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => a * x i

noncomputable def p18StageSum {n s : ℕ}
    (weights : Fin s → ℝ) (values : Fin s → Fin n → ℝ) : Fin n → ℝ :=
  fun k => ∑ j : Fin s, weights j * values j k

noncomputable def p18ModuleStageSum {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ} (weights : Fin s → ℝ)
    (values : Fin s → State) : State :=
  ∑ j : Fin s, weights j • values j

structure P18AdditiveRKOneStepRun (State : Type*) [AddCommGroup State]
    [Module ℝ State] (s : ℕ) where
  stage_count_pos : 0 < s
  step : ℝ
  epsilon : ℝ
  epsilon_ne_zero : epsilon ≠ 0
  initial : State
  referenceNext : State
  F : State → State
  FEpsilon : State → State
  tau : State → State
  operator_perturbation : ∀ y,
    epsilon • tau y = F y - FEpsilon y
  a : Fin s → Fin s → ℝ
  aPerturbation : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  bPerturbation : Fin s → ℝ
  schemeStages : Fin s → State
  perturbedStages : Fin s → State
  schemeNext : State
  perturbedNext : State
  scheme_stage_equation : ∀ i,
    schemeStages i =
      initial +
        step • p18ModuleStageSum (a i) (fun j => F (schemeStages j)) +
        step • p18ModuleStageSum (aPerturbation i)
          (fun j => F (schemeStages j))
  scheme_output_equation :
    schemeNext =
      initial +
        step • p18ModuleStageSum b (fun j => F (schemeStages j)) +
        step • p18ModuleStageSum bPerturbation
          (fun j => F (schemeStages j))
  perturbed_stage_equation : ∀ i,
    perturbedStages i =
      initial +
        step • p18ModuleStageSum (a i) (fun j => F (perturbedStages j)) +
        step • p18ModuleStageSum (aPerturbation i)
          (fun j => FEpsilon (perturbedStages j))
  perturbed_output_equation :
    perturbedNext =
      initial +
        step • p18ModuleStageSum b (fun j => F (perturbedStages j)) +
        step • p18ModuleStageSum bPerturbation
          (fun j => FEpsilon (perturbedStages j))

def p18TotalOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.referenceNext - run.perturbedNext

def p18SchemeOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.referenceNext - run.schemeNext

def p18PerturbationOneStepError {State : Type*} [AddCommGroup State]
    [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  run.schemeNext - run.perturbedNext

noncomputable def p18PerturbationOutputExpansion {State : Type*}
    [AddCommGroup State] [Module ℝ State] {s : ℕ}
    (run : P18AdditiveRKOneStepRun State s) : State :=
  (run.step •
      p18ModuleStageSum run.b (fun j => run.F (run.schemeStages j)) +
    run.step •
      p18ModuleStageSum run.bPerturbation
        (fun j => run.F (run.schemeStages j))) -
  (run.step •
      p18ModuleStageSum run.b (fun j => run.F (run.perturbedStages j)) +
    run.step •
      p18ModuleStageSum run.bPerturbation
        (fun j => run.FEpsilon (run.perturbedStages j)))

noncomputable def p18CoeffDot {s : ℕ}
    (x y : Fin s → ℝ) : ℝ :=
  ∑ i : Fin s, x i * y i

noncomputable def p18CoeffMatVec {s : ℕ}
    (A : Fin s → Fin s → ℝ) (x : Fin s → ℝ) : Fin s → ℝ :=
  fun i => ∑ j : Fin s, A i j * x j

def p18CoeffMatAdd {s : ℕ}
    (A B : Fin s → Fin s → ℝ) : Fin s → Fin s → ℝ :=
  fun i j => A i j + B i j

noncomputable def p18CoeffAbsDot {s : ℕ}
    (x y : Fin s → ℝ) : ℝ :=
  ∑ i : Fin s, |x i| * |y i|

def p18CoeffHadamard {s : ℕ}
    (x y : Fin s → ℝ) : Fin s → ℝ :=
  fun i => x i * y i

structure P18AdditiveRKTableau (s : ℕ) where
  A : Fin s → Fin s → ℝ
  APerturbation : Fin s → Fin s → ℝ
  b : Fin s → ℝ
  bPerturbation : Fin s → ℝ

noncomputable def p18TableauE {s : ℕ} : Fin s → ℝ :=
  fun _ ↦ 1

noncomputable def p18TableauATilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → Fin s → ℝ :=
  p18CoeffMatAdd tableau.A tableau.APerturbation

noncomputable def p18TableauBTilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18Add tableau.b tableau.bPerturbation

noncomputable def p18TableauC {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18CoeffMatVec tableau.A p18TableauE

noncomputable def p18TableauCPerturbation {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18CoeffMatVec tableau.APerturbation p18TableauE

noncomputable def p18TableauCTilde {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Fin s → ℝ :=
  p18Add (p18TableauC tableau) (p18TableauCPerturbation tableau)

def p18ThirdOrderConsistency {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Prop :=
  p18CoeffDot (p18TableauBTilde tableau) p18TableauE = 1 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18TableauCTilde tableau) = 1 / 2 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCTilde tableau)) = 1 / 3 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCTilde tableau)) = 1 / 6

def p18SmoothPerturbationOrderThree {s : ℕ}
    (tableau : P18AdditiveRKTableau s) : Prop :=
  p18CoeffDot tableau.bPerturbation p18TableauE = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18TableauCTilde tableau) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18TableauCPerturbation tableau) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18TableauCPerturbation tableau) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCTilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec (p18TableauATilde tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCTilde tableau)) = 0 ∧
    p18CoeffDot (p18TableauBTilde tableau)
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffMatVec tableau.APerturbation
          (p18TableauCPerturbation tableau)) = 0 ∧
    p18CoeffDot tableau.bPerturbation
        (p18CoeffHadamard (p18TableauCPerturbation tableau)
          (p18TableauCPerturbation tableau)) = 0

structure P18Method4s3pCSourceModel where
  tableau : P18AdditiveRKTableau 4
  perturbation_weights_zero : tableau.bPerturbation = fun _ ↦ 0
  third_order_consistency : p18ThirdOrderConsistency tableau
  smooth_perturbation_order_three :
    p18SmoothPerturbationOrderThree tableau

inductive P18TauRegime where
  | wellBehaved
  | notWellBehaved
  deriving DecidableEq

def p18UniformTwoTermGlobalOrder {ι : Type*}
    (error schemeError perturbationError step : ι → ℝ)
    (epsilon : ℝ) (p m : ℕ) : Prop :=
  (∀ t, error t = schemeError t + perturbationError t) ∧
    ∃ schemeConstant perturbationConstant : ℝ,
      0 ≤ schemeConstant ∧ 0 ≤ perturbationConstant ∧
        ∀ t,
          |schemeError t| ≤ schemeConstant * step t ^ p ∧
            |perturbationError t| ≤
              perturbationConstant * |epsilon| * step t ^ m

structure P18StableMethod4s3pCBranch
    (State : Type*) [NormedAddCommGroup State] [NormedSpace ℝ State]
    (ι : Type*) (method : P18Method4s3pCSourceModel)
    (localPerturbationPower : ℕ) where
  tauRegime : P18TauRegime
  step : ι → ℝ
  epsilon : ℝ
  stepCount : ι → ℕ
  horizon : ℝ
  localSchemeConstant : ℝ
  localPerturbationConstant : ℝ
  stabilityConstant : ℝ
  step_nonneg : ∀ t, 0 ≤ step t
  epsilon_pos : 0 < epsilon
  step_count_pos : ∀ t, 0 < stepCount t
  horizon_nonneg : 0 ≤ horizon
  local_scheme_constant_nonneg : 0 ≤ localSchemeConstant
  local_perturbation_constant_nonneg : 0 ≤ localPerturbationConstant
  stability_constant_nonneg : 0 ≤ stabilityConstant
  F : State → State
  FEpsilon : State → State
  tau : State → State
  computedState : ∀ t, Fin (stepCount t + 1) → State
  exactState : ∀ t, Fin (stepCount t + 1) → State
  oneStep : ∀ t, Fin (stepCount t) →
    P18AdditiveRKOneStepRun State 4
  run_step : ∀ t j, (oneStep t j).step = step t
  run_epsilon : ∀ t j, (oneStep t j).epsilon = epsilon
  run_F : ∀ t j, (oneStep t j).F = F
  run_FEpsilon : ∀ t j, (oneStep t j).FEpsilon = FEpsilon
  run_tau : ∀ t j, (oneStep t j).tau = tau
  run_A : ∀ t j, (oneStep t j).a = method.tableau.A
  run_APerturbation : ∀ t j,
    (oneStep t j).aPerturbation = method.tableau.APerturbation
  run_b : ∀ t j, (oneStep t j).b = method.tableau.b
  run_bPerturbation : ∀ t j,
    (oneStep t j).bPerturbation = method.tableau.bPerturbation
  run_initial : ∀ t j,
    (oneStep t j).initial = computedState t j.castSucc
  run_perturbed_next : ∀ t j,
    (oneStep t j).perturbedNext = computedState t j.succ
  run_reference_next : ∀ t j,
    (oneStep t j).referenceNext = exactState t j.succ
  schemeLocalError : ∀ t, Fin (stepCount t) → ℝ
  perturbationLocalError : ∀ t, Fin (stepCount t) → ℝ
  scheme_local_error_eq : ∀ t j,
    schemeLocalError t j = ‖p18SchemeOneStepError (oneStep t j)‖
  perturbation_local_error_eq : ∀ t j,
    perturbationLocalError t j =
      ‖p18PerturbationOneStepError (oneStep t j)‖
  scheme_local_bound : ∀ t j,
    schemeLocalError t j ≤ localSchemeConstant * step t ^ 4
  perturbation_local_bound : ∀ t j,
    perturbationLocalError t j ≤
      localPerturbationConstant * |epsilon| *
        step t ^ localPerturbationPower
  globalSchemeError : ι → ℝ
  globalPerturbationError : ι → ℝ
  globalError : ι → ℝ
  global_error_eq : ∀ t,
    globalError t =
      ‖exactState t (Fin.last (stepCount t)) -
        computedState t (Fin.last (stepCount t))‖
  global_split : ∀ t,
    globalError t = globalSchemeError t + globalPerturbationError t
  stable_scheme_accumulation : ∀ t,
    |globalSchemeError t| ≤
      stabilityConstant * ∑ j, schemeLocalError t j
  stable_perturbation_accumulation : ∀ t,
    |globalPerturbationError t| ≤
      stabilityConstant * ∑ j, perturbationLocalError t j
  finite_time_horizon : ∀ t,
    (stepCount t : ℝ) * step t ≤ horizon

end HighamBench
