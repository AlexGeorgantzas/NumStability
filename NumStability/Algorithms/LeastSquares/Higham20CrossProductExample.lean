-- Higham20CrossProductExample.lean
--
-- Executed floating-point form of the normal-equations cross-product example
-- on printed p. 387 of Higham, 2nd ed.

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import NumStability.Algorithms.LeastSquares.LSNormalEquations

namespace NumStability

/-- The source inequality `0 < epsilon < sqrt u` implies `epsilon^2 < u`. -/
theorem higham20CrossProductExample_epsilon_sq_lt_u
    {epsilon u : ℝ} (hepsilon : 0 < epsilon)
    (hepsilon_u : epsilon < Real.sqrt u) :
    epsilon ^ 2 < u := by
  have hsqrt_pos : 0 < Real.sqrt u := lt_trans hepsilon hepsilon_u
  have hu_pos : 0 < u := Real.sqrt_pos.mp hsqrt_pos
  have hsq : epsilon * epsilon < Real.sqrt u * Real.sqrt u :=
    mul_self_lt_mul_self hepsilon.le hepsilon_u
  rw [show Real.sqrt u * Real.sqrt u = u by
    nlinarith [Real.sq_sqrt hu_pos.le]] at hsq
  simpa [pow_two] using hsq

/-- A symbolic standard-model execution for Higham's p. 387 example.

For arbitrary `epsilon` and `u` satisfying `epsilon^2 < u`, the only
potentially inexact primitive operation is the sensitive addition
`1 + epsilon^2`, which is rounded back to `1`.  Its relative-error witness is
`-epsilon^2 / (1 + epsilon^2)`; the model budget is proved from
`epsilon^2 < u`.  All other additions and every subtraction, multiplication,
division, and square root are exact.

This is an executable `FPModel`, not a separately postulated rounded Gram
matrix. -/
noncomputable def higham20CrossProductExampleFP
    (epsilon u : ℝ) (hepsilon_sq : epsilon ^ 2 < u) : FPModel where
  u := u
  u_nonneg := (sq_nonneg epsilon).trans hepsilon_sq.le
  fl_add := fun x y =>
    if x = 1 ∧ y = epsilon ^ 2 then 1 else x + y
  fl_sub := fun x y => x - y
  fl_mul := fun x y => x * y
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by
    intro x
    simp
  model_add := by
    intro x y
    have hu : 0 ≤ u := (sq_nonneg epsilon).trans hepsilon_sq.le
    have hden_pos : 0 < 1 + epsilon ^ 2 := by
      nlinarith [sq_nonneg epsilon]
    by_cases h : x = 1 ∧ y = epsilon ^ 2
    · refine ⟨-(epsilon ^ 2) / (1 + epsilon ^ 2), ?_, ?_⟩
      · calc
          |-(epsilon ^ 2) / (1 + epsilon ^ 2)| =
              epsilon ^ 2 / (1 + epsilon ^ 2) := by
                rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg epsilon),
                  abs_of_pos hden_pos]
          _ ≤ epsilon ^ 2 := by
                apply div_le_self (sq_nonneg epsilon)
                nlinarith [sq_nonneg epsilon]
          _ ≤ u := hepsilon_sq.le
      change (if x = 1 ∧ y = epsilon ^ 2 then 1 else x + y) =
        (x + y) * (1 + (-(epsilon ^ 2) / (1 + epsilon ^ 2)))
      rw [if_pos h, h.1, h.2]
      field_simp [ne_of_gt hden_pos]
      ring
    · refine ⟨0, by simpa using hu, ?_⟩
      change (if x = 1 ∧ y = epsilon ^ 2 then 1 else x + y) =
        (x + y) * (1 + 0)
      rw [if_neg h]
      ring
  model_sub := by
    intro x y
    refine ⟨0, by simpa using (sq_nonneg epsilon).trans hepsilon_sq.le, by ring⟩
  model_mul := by
    intro x y
    refine ⟨0, by simpa using (sq_nonneg epsilon).trans hepsilon_sq.le, by ring⟩
  model_div := by
    intro x y _hy
    refine ⟨0, by simpa using (sq_nonneg epsilon).trans hepsilon_sq.le, by ring⟩
  model_sqrt := by
    intro x _hx
    refine ⟨0, by simpa using (sq_nonneg epsilon).trans hepsilon_sq.le, by ring⟩

/-- The symbolic model carries exactly the requested unit roundoff. -/
theorem higham20CrossProductExampleFP_u
    (epsilon u : ℝ) (hepsilon_sq : epsilon ^ 2 < u) :
    (higham20CrossProductExampleFP epsilon u hepsilon_sq).u = u := rfl

/-- The actual `fl_matMul` path computes the all-ones Gram matrix for every
positive `epsilon` satisfying the model budget `epsilon^2 < u`. -/
theorem higham20CrossProductExample_fl_gram_eq_of_sq_lt_u
    (epsilon u : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_sq : epsilon ^ 2 < u) :
    fl_matMul (higham20CrossProductExampleFP epsilon u hepsilon_sq) 2 2 2
        (fun i k => normalEquationsCrossProductExampleA epsilon k i)
        (normalEquationsCrossProductExampleA epsilon) =
      normalEquationsCrossProductExampleRoundedGram := by
  have hepsilon_ne : epsilon ≠ 0 := ne_of_gt hepsilon
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fl_matMul, fl_matVec, fl_dotProduct,
      normalEquationsCrossProductExampleA,
      normalEquationsCrossProductExampleRoundedGram,
      higham20CrossProductExampleFP, Fin.foldl_succ, pow_two,
      hepsilon_ne]

/-- Higham, 2nd ed., p. 387: for the printed symbolic family
`0 < epsilon < sqrt u`, the executed floating-point Gram product is the
singular all-ones matrix. -/
theorem higham20CrossProductExample_fl_gram_eq
    (epsilon u : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_u : epsilon < Real.sqrt u) :
    fl_matMul
        (higham20CrossProductExampleFP epsilon u
          (higham20CrossProductExample_epsilon_sq_lt_u hepsilon hepsilon_u))
        2 2 2
        (fun i k => normalEquationsCrossProductExampleA epsilon k i)
        (normalEquationsCrossProductExampleA epsilon) =
      normalEquationsCrossProductExampleRoundedGram := by
  exact higham20CrossProductExample_fl_gram_eq_of_sq_lt_u epsilon u hepsilon
    (higham20CrossProductExample_epsilon_sq_lt_u hepsilon hepsilon_u)

/-- Consequently, the matrix produced by the actual rounded product kernel is
singular throughout the printed symbolic family. -/
theorem higham20CrossProductExample_fl_gram_singular
    (epsilon u : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_u : epsilon < Real.sqrt u) :
    ∃ x : Fin 2 → ℝ,
      x ≠ 0 ∧
      matMulVec 2
        (fl_matMul
          (higham20CrossProductExampleFP epsilon u
            (higham20CrossProductExample_epsilon_sq_lt_u hepsilon hepsilon_u))
          2 2 2
          (fun i k => normalEquationsCrossProductExampleA epsilon k i)
          (normalEquationsCrossProductExampleA epsilon)) x = 0 := by
  rw [higham20CrossProductExample_fl_gram_eq epsilon u hepsilon hepsilon_u]
  exact normalEquationsCrossProductExampleRoundedGram_singular

/-- Bundled source-facing form: `0 < epsilon < sqrt u` constructs an explicit
`FPModel` with unit roundoff `u`, an actual all-ones `fl(AᵀA)`, and a nonzero
null vector for that computed Gram matrix. -/
theorem higham20CrossProductExample_symbolic_family
    (epsilon u : ℝ) (hepsilon : 0 < epsilon)
    (hepsilon_u : epsilon < Real.sqrt u) :
    ∃ fp : FPModel,
      fp.u = u ∧
      fl_matMul fp 2 2 2
          (fun i k => normalEquationsCrossProductExampleA epsilon k i)
          (normalEquationsCrossProductExampleA epsilon) =
        normalEquationsCrossProductExampleRoundedGram ∧
      ∃ x : Fin 2 → ℝ,
        x ≠ 0 ∧
        matMulVec 2
          (fl_matMul fp 2 2 2
            (fun i k => normalEquationsCrossProductExampleA epsilon k i)
            (normalEquationsCrossProductExampleA epsilon)) x = 0 := by
  let hepsilon_sq :=
    higham20CrossProductExample_epsilon_sq_lt_u hepsilon hepsilon_u
  let fp := higham20CrossProductExampleFP epsilon u hepsilon_sq
  refine ⟨fp, rfl, ?_, ?_⟩
  · exact higham20CrossProductExample_fl_gram_eq_of_sq_lt_u
      epsilon u hepsilon hepsilon_sq
  · rw [higham20CrossProductExample_fl_gram_eq_of_sq_lt_u
      epsilon u hepsilon hepsilon_sq]
    exact normalEquationsCrossProductExampleRoundedGram_singular

/-- The original concrete `epsilon = 1/4`, `u = 1/10` witness, retained as a
specialization of the symbolic construction. -/
noncomputable def higham20CrossProductExampleFixedFP : FPModel :=
  higham20CrossProductExampleFP (1 / 4) (1 / 10) (by norm_num)

theorem higham20CrossProductExample_epsilon_pos : (0 : ℝ) < 1 / 4 := by
  norm_num

theorem higham20CrossProductExample_epsilon_lt_sqrt_u :
    (1 / 4 : ℝ) < Real.sqrt higham20CrossProductExampleFixedFP.u := by
  change (1 / 4 : ℝ) < Real.sqrt (1 / 10)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (1 / 10 : ℝ) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (1 / 10 : ℝ)) ^ 2 = 1 / 10 :=
    Real.sq_sqrt (by norm_num)
  nlinarith

/-- Fixed-witness specialization of the symbolic Gram theorem. -/
theorem higham20CrossProductExample_fixed_fl_gram_eq :
    fl_matMul higham20CrossProductExampleFixedFP 2 2 2
        (fun i k => normalEquationsCrossProductExampleA (1 / 4) k i)
        (normalEquationsCrossProductExampleA (1 / 4)) =
      normalEquationsCrossProductExampleRoundedGram := by
  exact higham20CrossProductExample_fl_gram_eq_of_sq_lt_u
    (1 / 4) (1 / 10) (by norm_num) (by norm_num)

/-- Fixed-witness specialization of symbolic singularity. -/
theorem higham20CrossProductExample_fixed_fl_gram_singular :
    ∃ x : Fin 2 → ℝ,
      x ≠ 0 ∧
      matMulVec 2
        (fl_matMul higham20CrossProductExampleFixedFP 2 2 2
          (fun i k => normalEquationsCrossProductExampleA (1 / 4) k i)
          (normalEquationsCrossProductExampleA (1 / 4))) x = 0 := by
  rw [higham20CrossProductExample_fixed_fl_gram_eq]
  exact normalEquationsCrossProductExampleRoundedGram_singular

end NumStability
