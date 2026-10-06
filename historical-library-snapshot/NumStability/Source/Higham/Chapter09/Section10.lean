import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Order.Interval.Finset.Nat
import NumStability.Algorithms.LinearSystems.LU.BlockLU.BlockMatrices
import NumStability.Algorithms.LinearSystems.LU.BlockLU.PositiveDefinite
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LU.SpecialMatrices
import NumStability.Algorithms.LU.Tridiagonal
import NumStability.Algorithms.LU.TridiagonalCond
import NumStability.Algorithms.LU.TridiagonalRecurrence
import NumStability.Analysis.FirstOrder.FixedPrecision
import NumStability.Analysis.MatrixNorms.EntrywiseMaximum
import NumStability.Source.Higham.Chapter09.Section08

/-!
# Higham Chapter 9: Section10

Canonical source-correspondence owner from Chapter 9 destination-DAG layer 7.
-/

namespace NumStability

open scoped BigOperators
open ComplexConjugate
open Matrix

/-- **Equation (9.26)**, Holder bound for the prefix dot product in the update
formula. -/
theorem higham9_26_holder_prefix_dot_abs_le {k : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (x y : Fin k → ℝ) :
    |∑ r : Fin k, x r * y r| ≤
      higham9_26_prefixLpNorm p x * higham9_26_prefixLpNorm q y := by
  have hholder := complexVecLpNorm_holder hpq
    (fun r : Fin k => (y r : ℂ)) (fun r : Fin k => (x r : ℂ))
  have hholder' : ‖∑ r : Fin k, (x r : ℂ) * (y r : ℂ)‖ ≤
      higham9_26_prefixLpNorm p x * higham9_26_prefixLpNorm q y := by
    simpa [higham9_26_prefixLpNorm, mul_comm] using hholder
  let S : ℝ := ∑ r : Fin k, x r * y r
  have hcast : (S : ℂ) = ∑ r : Fin k, (x r : ℂ) * (y r : ℂ) := by
    simp [S]
  have habs_eq : |S| = ‖∑ r : Fin k, (x r : ℂ) * (y r : ℂ)‖ := by
    calc
      |S| = ‖S‖ := (Real.norm_eq_abs S).symm
      _ = ‖(S : ℂ)‖ := (Complex.norm_real S).symm
      _ = ‖∑ r : Fin k, (x r : ℂ) * (y r : ℂ)‖ := by rw [hcast]
  simpa [S] using habs_eq.trans_le hholder'

/-- **Equation (9.26)**, first displayed inequality for one stage-entry update:
if `stage = a - l · u`, Holder controls the eliminated prefix contribution. -/
theorem higham9_26_stage_entry_abs_le {k : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (a stage : ℝ) (l u : Fin k → ℝ)
    (hstage : stage = a - ∑ r : Fin k, l r * u r) :
    |stage| ≤ |a| + higham9_26_prefixLpNorm p l * higham9_26_prefixLpNorm q u := by
  let S : ℝ := ∑ r : Fin k, l r * u r
  have hstage_abs : |stage| = |a - S| := by
    simpa [S] using congrArg abs hstage
  have htri : |a - S| ≤ |a| + |S| := by
    have h := norm_add_le (a : ℝ) (-S)
    simpa [Real.norm_eq_abs, sub_eq_add_neg, abs_neg] using h
  have hholder := higham9_26_holder_prefix_dot_abs_le hpq l u
  have hstep : |a| + |S| ≤
      |a| + higham9_26_prefixLpNorm p l * higham9_26_prefixLpNorm q u := by
    linarith
  calc
    |stage| = |a - S| := hstage_abs
    _ ≤ |a| + |S| := htri
    _ ≤ |a| + higham9_26_prefixLpNorm p l * higham9_26_prefixLpNorm q u := hstep

/-- **Equation (9.26)**, Euclidean-prefix specialization of the stage-entry
Holder bound. -/
theorem higham9_26_stage_entry_abs_le_two_norm {k : ℕ}
    (a stage : ℝ) (l u : Fin k → ℝ)
    (hstage : stage = a - ∑ r : Fin k, l r * u r) :
    |stage| ≤ |a| +
      higham9_26_prefixLpNorm (2 : ℝ) l *
        higham9_26_prefixLpNorm (2 : ℝ) u :=
  higham9_26_stage_entry_abs_le
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two a stage l u hstage

/-- **Equation (9.26)**, source-style second inequality with explicit uniform
budgets for the original entry, row-prefix norm, and column-prefix norm. -/
theorem higham9_26_stage_entry_abs_le_of_uniform_bounds {k : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q) (a stage Amax Lmax Umax : ℝ)
    (l u : Fin k → ℝ)
    (hstage : stage = a - ∑ r : Fin k, l r * u r)
    (hA : |a| ≤ Amax)
    (hL : higham9_26_prefixLpNorm p l ≤ Lmax)
    (hU : higham9_26_prefixLpNorm q u ≤ Umax)
    (hLmax : 0 ≤ Lmax) :
    |stage| ≤ Amax + Lmax * Umax := by
  have hbase := higham9_26_stage_entry_abs_le hpq a stage l u hstage
  have hprod :
      higham9_26_prefixLpNorm p l * higham9_26_prefixLpNorm q u ≤ Lmax * Umax := by
    exact mul_le_mul hL hU (complexVecLpNorm_ofReal_nonneg hpq.symm.pos _) hLmax
  exact hbase.trans (add_le_add hA hprod)

/-- **Equation (9.26)**, Euclidean-prefix specialization of the source-style
uniform-budget stage-entry bound. -/
theorem higham9_26_stage_entry_abs_le_of_two_norm_uniform_bounds {k : ℕ}
    (a stage Amax Lmax Umax : ℝ) (l u : Fin k → ℝ)
    (hstage : stage = a - ∑ r : Fin k, l r * u r)
    (hA : |a| ≤ Amax)
    (hL : higham9_26_prefixLpNorm (2 : ℝ) l ≤ Lmax)
    (hU : higham9_26_prefixLpNorm (2 : ℝ) u ≤ Umax)
    (hLmax : 0 ≤ Lmax) :
    |stage| ≤ Amax + Lmax * Umax :=
  higham9_26_stage_entry_abs_le_of_uniform_bounds
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two a stage Amax Lmax Umax l u
    hstage hA hL hU hLmax

/-- **Equation (9.26)**, the eliminated row prefix `lᵢ,1:k` as a finite
vector. -/
def higham9_26_rowPrefix {n k : ℕ}
    (L : Matrix (Fin n) (Fin k) ℝ) (i : Fin n) : Fin k → ℝ :=
  fun r => L i r

/-- **Equation (9.26)**, the eliminated column prefix `u₁:k,j` as a finite
vector. -/
def higham9_26_colPrefix {n k : ℕ}
    (U : Matrix (Fin k) (Fin n) ℝ) (j : Fin n) : Fin k → ℝ :=
  fun r => U r j

/-- **Equation (9.26)**, Matrix-facing stage-entry Holder bound for the update
`aᵢⱼ^(k) = aᵢⱼ - Σᵣ lᵢᵣ uᵣⱼ`. -/
theorem higham9_26_matrix_stage_entry_abs_le {n k : ℕ} {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A Astage : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin k) (Fin n) ℝ)
    (i j : Fin n)
    (hstage :
      Astage i j = A i j - ∑ r : Fin k, L i r * U r j) :
    |Astage i j| ≤ |A i j| +
      higham9_26_prefixLpNorm p (higham9_26_rowPrefix L i) *
        higham9_26_prefixLpNorm q (higham9_26_colPrefix U j) := by
  exact higham9_26_stage_entry_abs_le hpq
    (A i j) (Astage i j)
    (higham9_26_rowPrefix L i) (higham9_26_colPrefix U j)
    (by simpa [higham9_26_rowPrefix, higham9_26_colPrefix] using hstage)

/-- **Equation (9.26)**, Matrix-facing Euclidean-prefix specialization of the
stage-entry Holder bound. -/
theorem higham9_26_matrix_stage_entry_abs_le_two_norm {n k : ℕ}
    (A Astage : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin k) (Fin n) ℝ)
    (i j : Fin n)
    (hstage :
      Astage i j = A i j - ∑ r : Fin k, L i r * U r j) :
    |Astage i j| ≤ |A i j| +
      higham9_26_prefixLpNorm (2 : ℝ) (higham9_26_rowPrefix L i) *
        higham9_26_prefixLpNorm (2 : ℝ) (higham9_26_colPrefix U j) :=
  higham9_26_matrix_stage_entry_abs_le
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two A Astage L U i j hstage

/-- **Equation (9.26)**, Matrix-facing source-style second inequality with
explicit uniform bounds for the original entry, row prefix, and column prefix. -/
theorem higham9_26_matrix_stage_entry_abs_le_of_uniform_bounds {n k : ℕ}
    {p q : ℝ}
    (hpq : p.HolderConjugate q)
    (A Astage : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin k) (Fin n) ℝ)
    (i j : Fin n) (Amax Lmax Umax : ℝ)
    (hstage :
      Astage i j = A i j - ∑ r : Fin k, L i r * U r j)
    (hA : |A i j| ≤ Amax)
    (hL : higham9_26_prefixLpNorm p (higham9_26_rowPrefix L i) ≤ Lmax)
    (hU : higham9_26_prefixLpNorm q (higham9_26_colPrefix U j) ≤ Umax)
    (hLmax : 0 ≤ Lmax) :
    |Astage i j| ≤ Amax + Lmax * Umax := by
  exact higham9_26_stage_entry_abs_le_of_uniform_bounds hpq
    (A i j) (Astage i j) Amax Lmax Umax
    (higham9_26_rowPrefix L i) (higham9_26_colPrefix U j)
    (by simpa [higham9_26_rowPrefix, higham9_26_colPrefix] using hstage)
    hA hL hU hLmax

/-- **Equation (9.26)**, Matrix-facing Euclidean-prefix specialization of the
source-style uniform-budget stage-entry bound. -/
theorem higham9_26_matrix_stage_entry_abs_le_of_two_norm_uniform_bounds
    {n k : ℕ}
    (A Astage : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin k) ℝ)
    (U : Matrix (Fin k) (Fin n) ℝ)
    (i j : Fin n) (Amax Lmax Umax : ℝ)
    (hstage :
      Astage i j = A i j - ∑ r : Fin k, L i r * U r j)
    (hA : |A i j| ≤ Amax)
    (hL :
      higham9_26_prefixLpNorm (2 : ℝ) (higham9_26_rowPrefix L i) ≤ Lmax)
    (hU :
      higham9_26_prefixLpNorm (2 : ℝ) (higham9_26_colPrefix U j) ≤ Umax)
    (hLmax : 0 ≤ Lmax) :
    |Astage i j| ≤ Amax + Lmax * Umax :=
  higham9_26_matrix_stage_entry_abs_le_of_uniform_bounds
    (p := (2 : ℝ)) (q := (2 : ℝ))
    Real.HolderConjugate.two_two A Astage L U i j Amax Lmax Umax
    hstage hA hL hU hLmax

/-- **Equation (9.27)**, the perturbation matrix
`G = L⁻¹ ΔA U⁻¹` in the normwise sensitivity theorem. -/
noncomputable def higham9_27_GMatrix {n : ℕ}
    (Linv ΔA Uinv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  rectMatMul (rectMatMul Linv ΔA) Uinv

end NumStability
