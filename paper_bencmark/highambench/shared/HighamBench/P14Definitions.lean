import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Asymptotics.Lemmas

namespace HighamBench

open scoped BigOperators

structure StandardAddModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add :
    ∀ x y : ℝ, ∃ δ : ℝ,
      |δ| ≤ u ∧
      fl_add x y = (x + y) * (1 + δ)

noncomputable def gamma (u : ℝ) (n : ℕ) : ℝ :=
  ((n : ℝ) * u) / (1 - (n : ℝ) * u)

def GammaValid (u : ℝ) (n : ℕ) : Prop :=
  (n : ℝ) * u < 1

noncomputable def recursiveSum (flAdd : ℝ → ℝ → ℝ) :
    (n : ℕ) → (Fin n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, v =>
      if h : n = 0 then
        v ⟨0, by omega⟩
      else
        flAdd
          (recursiveSum flAdd n (fun i => v i.castSucc))
          (v (Fin.last n))

noncomputable def p14ExpSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, Real.exp (x i)

structure P14BasicSumExecution {n : ℕ} (x : Fin n → ℝ) (u : ℝ) where
  fp : StandardAddModel
  unit_eq : fp.u = u
  expError : Fin n → ℝ
  expError_le : ∀ i, |expError i| ≤ u

noncomputable def p14ComputedExp {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) (i : Fin n) : ℝ :=
  Real.exp (x i) * (1 + run.expError i)

noncomputable def p14ExactComputedExpSum {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) : ℝ :=
  ∑ i, p14ComputedExp run i

noncomputable def p14RecursiveComputedExpSum {n : ℕ}
    {x : Fin n → ℝ} {u : ℝ} (run : P14BasicSumExecution x u) : ℝ :=
  recursiveSum run.fp.fl_add n (p14ComputedExp run)

noncomputable def p14BasicSumDelta {n : ℕ} {x : Fin n → ℝ} {u : ℝ}
    (run : P14BasicSumExecution x u) : ℝ :=
  p14RecursiveComputedExpSum run - p14ExpSum x

end HighamBench
