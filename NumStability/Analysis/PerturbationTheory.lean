-- Analysis/PerturbationTheory.lean
--
-- Perturbation theory for linear systems Ax = b (Higham §7).
--
-- Core results:
--   forward_error_from_residual: |x − y| ≤ |A⁻¹| |r|  (§7.1)
--   normwise_perturbation_bound: Theorem 7.2 componentwise form
--   oettli_prager_necessary: Theorem 7.3 (⇒ direction)
--   oettli_prager_sufficient: Theorem 7.3 (⇐ direction, constructive)
--   componentwise_forward_error: Theorem 7.4
--   Condition numbers: cond(A) ≤ κ_∞(A) (§7.2)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.Analysis.ForwardError

/-!
# Perturbation theory for linear systems

Reusable residual, componentwise perturbation, and condition-number bounds for
exact and approximate solutions of linear systems.
-/

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §7.1  Residual
-- ============================================================

/-- Residual vector r = b − Ay for the system Ax = b. -/
noncomputable def residualVec (n : ℕ) (A : Fin n → Fin n → ℝ)
    (y b : Fin n → ℝ) : Fin n → ℝ :=
  fun i => b i - ∑ j : Fin n, A i j * y j

/-- Scaled/relative residual `||b - Ay||₂ / (||A||₂ ||y||₂)`, with the
matrix norm value supplied explicitly.  This is the scaled residual used in
Higham Chapter 1 and Lemma 1.1, represented through the repository's
operator-2-norm predicate surface. -/
noncomputable def relativeResidual2 (n : ℕ) (A : Fin n → Fin n → ℝ)
    (y b : Fin n → ℝ) (matrixNormA : ℝ) : ℝ :=
  vecNorm2 (residualVec n A y b) / (matrixNormA * vecNorm2 y)

-- ============================================================
-- Chapter 1 residual/backward-error bridge
-- ============================================================

/-- Rank-one perturbation used in Higham Lemma 1.1's proof route:
`ΔA = r yᵀ / (yᵀ y)`, represented with the repository's finite vectors. -/
noncomputable def residualRankOnePerturbation (n : ℕ)
    (r y : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => (1 / vecNorm2Sq y) * (r i * y j)

/-- The rank-one residual perturbation maps `y` back to `r`, provided
`y` has nonzero Euclidean norm. -/
theorem residualRankOnePerturbation_mul_vec (n : ℕ)
    (r y : Fin n → ℝ) (hy : vecNorm2 y ≠ 0) :
    matMulVec n (residualRankOnePerturbation n r y) y = r := by
  have hsq : vecNorm2Sq y ≠ 0 := by
    intro hzero
    have hnormsq : vecNorm2 y ^ 2 = 0 := by
      rw [vecNorm2_sq, hzero]
    exact hy (sq_eq_zero_iff.mp hnormsq)
  have hsq' : (∑ i : Fin n, y i ^ 2) ≠ 0 := by
    simpa [vecNorm2Sq] using hsq
  ext i
  unfold residualRankOnePerturbation matMulVec vecNorm2Sq
  calc
    (∑ j : Fin n, (1 / ∑ i : Fin n, y i ^ 2) * (r i * y j) * y j)
        = ∑ j : Fin n, ((1 / ∑ i : Fin n, y i ^ 2) * r i) * y j ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ((1 / ∑ j : Fin n, y j ^ 2) * r i) *
            (∑ j : Fin n, y j ^ 2) := by
          rw [Finset.mul_sum]
    _ = r i := by
          field_simp [hsq']

/-- The rank-one perturbation makes the approximate solution `y` exact for
the perturbed system `(A + ΔA)y = b`, where `ΔA = r yᵀ/(yᵀy)` and
`r = b - Ay`. -/
theorem residualRankOnePerturbation_solves (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (hy : vecNorm2 y ≠ 0) :
    let ΔA := residualRankOnePerturbation n (residualVec n A y b) y
    ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i := by
  intro ΔA i
  have hmul :=
    congrFun (residualRankOnePerturbation_mul_vec n (residualVec n A y b) y hy) i
  unfold matMulVec at hmul
  have hmul' :
      ∑ j : Fin n,
        residualRankOnePerturbation n (fun i => b i - ∑ j, A i j * y j) y i j *
          y j = residualVec n A y b i := by
    simpa [residualVec] using hmul
  unfold ΔA
  calc
    (∑ j : Fin n,
        (A i j + residualRankOnePerturbation n (fun i => b i - ∑ j, A i j * y j) y i j) *
          y j)
        = ∑ j : Fin n,
            (A i j * y j +
              residualRankOnePerturbation n (fun i => b i - ∑ j, A i j * y j) y i j *
                y j) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
    _ = ∑ j : Fin n, A i j * y j +
          ∑ j : Fin n,
            residualRankOnePerturbation n (fun i => b i - ∑ j, A i j * y j) y i j *
              y j := by
              rw [Finset.sum_add_distrib]
    _ = ∑ j : Fin n, A i j * y j + residualVec n A y b i := by
          rw [hmul']
    _ = b i := by
          unfold residualVec
          ring

/-- Frobenius norm of the rank-one residual perturbation.  This is the exact
Frobenius analogue of the rank-one norm computation used in Higham Lemma 1.1. -/
theorem frobNorm_residualRankOnePerturbation (n : ℕ)
    (r y : Fin n → ℝ) (hy : vecNorm2 y ≠ 0) :
    frobNorm (residualRankOnePerturbation n r y) =
      vecNorm2 r / vecNorm2 y := by
  change frobNorm (fun i j => (1 / vecNorm2Sq y) * (r i * y j)) =
    vecNorm2 r / vecNorm2 y
  simpa [one_div] using
    frobNorm_rankOne_div_vecNorm2Sq r y hy

/-- The rank-one residual perturbation has operator 2-norm at most
`||r||₂ / ||y||₂`, stated using the repository's predicate-style
`opNorm2Le`. -/
theorem opNorm2Le_residualRankOnePerturbation (n : ℕ)
    (r y : Fin n → ℝ) (hy : vecNorm2 y ≠ 0) :
    opNorm2Le (residualRankOnePerturbation n r y) (vecNorm2 r / vecNorm2 y) := by
  have hypos : 0 < vecNorm2 y :=
    lt_of_le_of_ne (vecNorm2_nonneg y) (Ne.symm hy)
  have hden_pos : 0 < vecNorm2Sq y := by
    rw [← vecNorm2_sq]
    exact sq_pos_of_pos hypos
  intro x
  let inner : ℝ := ∑ j : Fin n, y j * x j
  let scalar : ℝ := (1 / vecNorm2Sq y) * inner
  have hMx :
      matMulVec n (residualRankOnePerturbation n r y) x =
        fun i : Fin n => scalar * r i := by
    ext i
    unfold residualRankOnePerturbation matMulVec scalar inner
    calc
      (∑ j : Fin n, (1 / vecNorm2Sq y) * (r i * y j) * x j)
          = ∑ j : Fin n, ((1 / vecNorm2Sq y) * (y j * x j)) * r i := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (∑ j : Fin n, (1 / vecNorm2Sq y) * (y j * x j)) * r i := by
              rw [← Finset.sum_mul]
      _ = ((1 / vecNorm2Sq y) * ∑ j : Fin n, y j * x j) * r i := by
              rw [← Finset.mul_sum]
  rw [hMx, vecNorm2_smul]
  have hinner : |inner| ≤ vecNorm2 y * vecNorm2 x := by
    simpa [inner] using abs_vecInnerProduct_le_vecNorm2_mul y x
  have hscalar : |scalar| ≤ vecNorm2 x / vecNorm2 y := by
    unfold scalar
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hden_pos)]
    calc
      (1 / vecNorm2Sq y) * |inner|
          ≤ (1 / vecNorm2Sq y) * (vecNorm2 y * vecNorm2 x) :=
            mul_le_mul_of_nonneg_left hinner (le_of_lt (one_div_pos.mpr hden_pos))
      _ = vecNorm2 x / vecNorm2 y := by
            rw [← vecNorm2_sq]
            field_simp [hypos.ne']
  calc
    |scalar| * vecNorm2 r
        ≤ (vecNorm2 x / vecNorm2 y) * vecNorm2 r :=
          mul_le_mul_of_nonneg_right hscalar (vecNorm2_nonneg r)
    _ = (vecNorm2 r / vecNorm2 y) * vecNorm2 x := by
          field_simp [hypos.ne']

/-- If a perturbation makes `y` solve `(A + ΔA)y = b`, then the residual is
exactly `ΔA y`. -/
theorem residualVec_eq_matMulVec_of_perturbed_solve (n : ℕ)
    (A ΔA : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (hPerturbed : ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i) :
    residualVec n A y b = matMulVec n ΔA y := by
  ext i
  unfold residualVec matMulVec
  have h := hPerturbed i
  have hsplit :
      ∑ j : Fin n, (A i j + ΔA i j) * y j =
        ∑ j : Fin n, A i j * y j + ∑ j : Fin n, ΔA i j * y j := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsplit] at h
  linarith

/-- Any perturbation that makes `y` solve `(A + ΔA)y = b` must have Frobenius
norm large enough to account for the residual.  Together with
`frobNorm_residualRankOnePerturbation`, this gives the Frobenius-norm version
of the Lemma 1.1 rank-one construction. -/
theorem residual_norm_le_frobNorm_mul_solution_norm_of_perturbed_solve
    (n : ℕ) (A ΔA : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (hPerturbed : ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i) :
    vecNorm2 (residualVec n A y b) ≤ frobNorm ΔA * vecNorm2 y := by
  have hres := residualVec_eq_matMulVec_of_perturbed_solve n A ΔA y b hPerturbed
  rw [hres]
  exact vecNorm2_matMulVec_le_frobNorm_mul ΔA y

/-- Any perturbation with an operator-2 bound that makes `y` solve the
perturbed system must have budget at least `||r||₂ / ||y||₂`. -/
theorem residual_norm_div_solution_norm_le_of_opNorm2Le_perturbed_solve
    (n : ℕ) (A ΔA : Fin n → Fin n → ℝ) (y b : Fin n → ℝ) (c : ℝ)
    (hy : vecNorm2 y ≠ 0)
    (hPerturbed : ∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i)
    (hΔA : opNorm2Le ΔA c) :
    vecNorm2 (residualVec n A y b) / vecNorm2 y ≤ c := by
  have hypos : 0 < vecNorm2 y :=
    lt_of_le_of_ne (vecNorm2_nonneg y) (Ne.symm hy)
  have hres := residualVec_eq_matMulVec_of_perturbed_solve n A ΔA y b hPerturbed
  have hle : vecNorm2 (residualVec n A y b) ≤ c * vecNorm2 y := by
    rw [hres]
    exact hΔA y
  rw [div_le_iff₀ hypos]
  simpa [mul_comm] using hle

/-- Higham §1.10.1 rounded-exact-solution residual identity.  If `x` solves
`A*x=b` exactly and `z=x+Δx`, then the residual of `z` is `-A*Δx`. -/
theorem residualVec_add_error_eq_neg_matMulVec
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x Δx b : Fin n → ℝ)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i) :
    residualVec n A (fun i => x i + Δx i) b =
      fun i => -matMulVec n A Δx i := by
  ext i
  unfold residualVec matMulVec
  rw [← hAx i]
  simp_rw [mul_add, Finset.sum_add_distrib]
  ring

/-- Norm form of the rounded-exact-solution residual identity:
`||b - A(x+Δx)||₂ = ||AΔx||₂`. -/
theorem residual_norm_add_error_eq_matMulVec_norm
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x Δx b : Fin n → ℝ)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i) :
    vecNorm2 (residualVec n A (fun i => x i + Δx i) b) =
      vecNorm2 (matMulVec n A Δx) := by
  rw [residualVec_add_error_eq_neg_matMulVec n A x Δx b hAx]
  exact vecNorm2_neg (matMulVec n A Δx)

/-- If `||A||₂ ≤ A_norm`, then the residual of the rounded exact solution is
controlled by the matrix action on the rounding error. -/
theorem roundedExactSolution_residual_norm_le_opNorm2
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x Δx b : Fin n → ℝ)
    (A_norm : ℝ)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hA : opNorm2Le A A_norm) :
    vecNorm2 (residualVec n A (fun i => x i + Δx i) b) ≤
      A_norm * vecNorm2 Δx := by
  rw [residual_norm_add_error_eq_matMulVec_norm n A x Δx b hAx]
  exact hA Δx

/-- Higham §1.10.1 rounded-exact-solution residual comparison: if
`||Δx||₂ ≤ u ||x||₂` and `||A||₂ ≤ A_norm`, then
`||b - A(x+Δx)||₂ ≤ A_norm * u * ||x||₂`. -/
theorem roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x Δx b : Fin n → ℝ)
    (A_norm u : ℝ)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hA : opNorm2Le A A_norm) (hA_nonneg : 0 ≤ A_norm)
    (hΔx : vecNorm2 Δx ≤ u * vecNorm2 x) :
    vecNorm2 (residualVec n A (fun i => x i + Δx i) b) ≤
      A_norm * u * vecNorm2 x := by
  calc
    vecNorm2 (residualVec n A (fun i => x i + Δx i) b)
        ≤ A_norm * vecNorm2 Δx :=
          roundedExactSolution_residual_norm_le_opNorm2 n A x Δx b A_norm hAx hA
    _ ≤ A_norm * (u * vecNorm2 x) :=
          mul_le_mul_of_nonneg_left hΔx hA_nonneg
    _ = A_norm * u * vecNorm2 x := by ring

/-- Uncancelled scaled-residual version of the rounded-exact-solution bound:
`||b-Az||₂/(||A||₂||z||₂) ≤ (||A||₂ u ||x||₂)/(||A||₂||z||₂)`,
for `z = x + Δx`. -/
theorem roundedExactSolution_relativeResidual2_le_uncancelled
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x Δx b : Fin n → ℝ)
    (A_norm u : ℝ)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hA : opNorm2Le A A_norm) (hA_nonneg : 0 ≤ A_norm)
    (hden : 0 < A_norm * vecNorm2 (fun i => x i + Δx i))
    (hΔx : vecNorm2 Δx ≤ u * vecNorm2 x) :
    relativeResidual2 n A (fun i => x i + Δx i) b A_norm ≤
      (A_norm * u * vecNorm2 x) /
        (A_norm * vecNorm2 (fun i => x i + Δx i)) := by
  unfold relativeResidual2
  exact div_le_div_of_nonneg_right
    (roundedExactSolution_residual_norm_le_opNorm2_mul_relative_error
      n A x Δx b A_norm u hAx hA hA_nonneg hΔx)
    (le_of_lt hden)

/-- Cancelled scaled-residual comparison for the rounded exact solution:
if `||A||₂ ≤ A_norm`, `A_norm > 0`, and `||Δx||₂ ≤ u||x||₂`, then
`relativeResidual2(A, x+Δx, b) ≤ u ||x||₂ / ||x+Δx||₂`. -/
theorem roundedExactSolution_relativeResidual2_le_relative_error_factor
    (n : ℕ) (A : Fin n → Fin n → ℝ) (x Δx b : Fin n → ℝ)
    (A_norm u : ℝ)
    (hAx : ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i)
    (hA : opNorm2Le A A_norm) (hApos : 0 < A_norm)
    (hz : vecNorm2 (fun i => x i + Δx i) ≠ 0)
    (hΔx : vecNorm2 Δx ≤ u * vecNorm2 x) :
    relativeResidual2 n A (fun i => x i + Δx i) b A_norm ≤
      u * vecNorm2 x / vecNorm2 (fun i => x i + Δx i) := by
  have hzpos : 0 < vecNorm2 (fun i => x i + Δx i) :=
    lt_of_le_of_ne (vecNorm2_nonneg _) (Ne.symm hz)
  have hden : 0 < A_norm * vecNorm2 (fun i => x i + Δx i) :=
    mul_pos hApos hzpos
  calc
    relativeResidual2 n A (fun i => x i + Δx i) b A_norm
        ≤ (A_norm * u * vecNorm2 x) /
            (A_norm * vecNorm2 (fun i => x i + Δx i)) :=
          roundedExactSolution_relativeResidual2_le_uncancelled
            n A x Δx b A_norm u hAx hA (le_of_lt hApos) hden hΔx
    _ = u * vecNorm2 x / vecNorm2 (fun i => x i + Δx i) := by
          field_simp [ne_of_gt hApos, ne_of_gt hzpos]

/-- Absolute matrix-only backward-error predicate for Higham Lemma 1.1,
using `opNorm2Le` as the repository's operator-2-norm surface. -/
def matrixOnlyBackwardError2Le (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ) (η : ℝ) : Prop :=
  ∃ ΔA : Fin n → Fin n → ℝ,
    (∀ i : Fin n, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i) ∧
    opNorm2Le ΔA η

/-- Relative matrix-only backward-error predicate, where `matrixNormA` is the
positive matrix norm value used for scaling.  For Higham Lemma 1.1 this value is
`||A||₂`; the repository currently supplies it as an explicit positive scalar
rather than a supremum-valued matrix norm definition. -/
def relativeMatrixOnlyBackwardError2Le (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (matrixNormA η : ℝ) : Prop :=
  matrixOnlyBackwardError2Le n A y b (η * matrixNormA)

/-- Higham Lemma 1.1, predicate form: among all perturbations to `A` that make
`y` an exact solution, the optimal operator-2 perturbation budget is
`||b - Ay||₂ / ||y||₂`, and it is attained by the rank-one perturbation
`(b - Ay)yᵀ/(yᵀy)`. -/
theorem higham_lemma_1_1_operator2_predicate (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (hy : vecNorm2 y ≠ 0) :
    let η := vecNorm2 (residualVec n A y b) / vecNorm2 y
    matrixOnlyBackwardError2Le n A y b η ∧
      ∀ c : ℝ, matrixOnlyBackwardError2Le n A y b c → η ≤ c := by
  intro η
  constructor
  · refine ⟨residualRankOnePerturbation n (residualVec n A y b) y, ?_, ?_⟩
    · exact residualRankOnePerturbation_solves n A y b hy
    · simpa [η] using
        opNorm2Le_residualRankOnePerturbation n (residualVec n A y b) y hy
  · intro c hc
    obtain ⟨ΔA, hPerturbed, hΔA⟩ := hc
    simpa [η] using
      residual_norm_div_solution_norm_le_of_opNorm2Le_perturbed_solve
        n A ΔA y b c hy hPerturbed hΔA

/-- Higham Lemma 1.1, relative-residual predicate form.  If `matrixNormA` is
the positive value of `||A||₂`, then the relative residual
`||b - Ay||₂ / (||A||₂ ||y||₂)` is exactly the optimal relative matrix-only
backward-error budget. -/
theorem higham_lemma_1_1_relativeResidual2_predicate (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (matrixNormA : ℝ) (hy : vecNorm2 y ≠ 0) (hApos : 0 < matrixNormA) :
    let η := vecNorm2 (residualVec n A y b) / (matrixNormA * vecNorm2 y)
    relativeMatrixOnlyBackwardError2Le n A y b matrixNormA η ∧
      ∀ c : ℝ, relativeMatrixOnlyBackwardError2Le n A y b matrixNormA c → η ≤ c := by
  intro η
  have hypos : 0 < vecNorm2 y :=
    lt_of_le_of_ne (vecNorm2_nonneg y) (Ne.symm hy)
  have habs := higham_lemma_1_1_operator2_predicate n A y b hy
  constructor
  · obtain ⟨ΔA, hPerturbed, hOp⟩ := habs.1
    refine ⟨ΔA, hPerturbed, ?_⟩
    have hη :
        η * matrixNormA =
          vecNorm2 (residualVec n A y b) / vecNorm2 y := by
      dsimp [η]
      field_simp [hApos.ne', hypos.ne']
    simpa [relativeMatrixOnlyBackwardError2Le, matrixOnlyBackwardError2Le, hη] using hOp
  · intro c hc
    have habsLower := habs.2 (c * matrixNormA) hc
    have hη :
        η * matrixNormA =
          vecNorm2 (residualVec n A y b) / vecNorm2 y := by
      dsimp [η]
      field_simp [hApos.ne', hypos.ne']
    have hmul : η * matrixNormA ≤ c * matrixNormA := by
      simpa [hη] using habsLower
    exact (mul_le_mul_iff_of_pos_right hApos).mp hmul

/-- Direct use form of Higham Lemma 1.1: any relative matrix-only backward
error certificate with operator-2 budget `η * ||A||₂` bounds the displayed
scaled residual by `η`. -/
theorem relativeResidual2_le_of_relativeMatrixOnlyBackwardError2Le (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (matrixNormA η : ℝ) (hy : vecNorm2 y ≠ 0) (hApos : 0 < matrixNormA)
    (hback : relativeMatrixOnlyBackwardError2Le n A y b matrixNormA η) :
    relativeResidual2 n A y b matrixNormA ≤ η := by
  have hlemma :=
    higham_lemma_1_1_relativeResidual2_predicate n A y b matrixNormA hy hApos
  simpa [relativeResidual2] using hlemma.2 η hback

/-- For a 2-by-2 matrix, the infinity-norm bound implies an operator-2 bound
after the elementary `sqrt 2` Frobenius comparison. -/
theorem opNorm2Le_of_sqrt_two_infNorm_le
    (M : Fin 2 → Fin 2 → ℝ) {c : ℝ}
    (hM : Real.sqrt (2 : ℝ) * infNorm M ≤ c) :
    opNorm2Le M c := by
  apply opNorm2Le_of_frobNorm_le
  have hsq :
      frobNorm M ^ 2 ≤ (Real.sqrt (2 : ℝ) * infNorm M) ^ 2 := by
    have hbase := frobNorm_sq_le_nat_mul_infNorm_sq (n := 2) M
    have hscale :
        (Real.sqrt (2 : ℝ) * infNorm M) ^ 2 =
          (2 : ℝ) * infNorm M ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    simpa [hscale] using hbase
  have hF_nonneg : 0 ≤ frobNorm M := frobNorm_nonneg M
  have hscale_nonneg : 0 ≤ Real.sqrt (2 : ℝ) * infNorm M :=
    mul_nonneg (Real.sqrt_nonneg _) (infNorm_nonneg M)
  have hF_le_scale : frobNorm M ≤ Real.sqrt (2 : ℝ) * infNorm M := by
    have habs : |frobNorm M| ≤ |Real.sqrt (2 : ℝ) * infNorm M| :=
      (sq_le_sq).mp hsq
    simpa [abs_of_nonneg hF_nonneg, abs_of_nonneg hscale_nonneg] using habs
  exact le_trans hF_le_scale hM

-- ============================================================
-- §7.1  Forward error from residual
-- ============================================================

/-- **Forward error from residual** (Higham §7.1).

    If Ax = b and A_inv is a left inverse of A, then
      |x_i − y_i| ≤ (|A⁻¹| · |r|)_i
    where r = b − Ay.  This is the componentwise form of x − y = A⁻¹r. -/
theorem forward_error_from_residual (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i) :
    ∀ i, |x i - y i| ≤
      ∑ j : Fin n, |A_inv i j| * |residualVec n A y b j| := by
  intro i
  -- r_j = ∑_k A_{jk}(x_k − y_k)
  have hR : ∀ j, residualVec n A y b j =
      ∑ k : Fin n, A j k * (x k - y k) := by
    intro j; unfold residualVec
    simp_rw [mul_sub, Finset.sum_sub_distrib]; linarith [hAx j]
  -- x_i − y_i = ∑_j A_inv_{ij} r_j  (multiply by A⁻¹)
  have hSol : x i - y i =
      ∑ j : Fin n, A_inv i j * residualVec n A y b j := by
    simp_rw [hR, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ k : Fin n,
        ∑ j : Fin n, A_inv i j * (A j k * (x k - y k)) =
        (∑ j : Fin n, A_inv i j * A j k) * (x k - y k) := by
      intro k; rw [Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    simp_rw [this, hInv i]; simp
  rw [hSol]
  calc |∑ j, A_inv i j * residualVec n A y b j|
      ≤ ∑ j, |A_inv i j * residualVec n A y b j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, |A_inv i j| * |residualVec n A y b j| := by
        apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _

-- ============================================================
-- §7.2  Normwise perturbation bound (Theorem 7.2)
-- ============================================================

/-- **Normwise perturbation bound** (Higham Theorem 7.2, componentwise form).

    If Ax = b, (A + ΔA)y = b + Δb, and A_inv is a left inverse of A, then
      |x_i − y_i| ≤ ∑_j |A⁻¹_{ij}| · (∑_k |ΔA_{jk}| · |y_k| + |Δb_j|)

    This follows from x − y = A⁻¹(ΔAy − Δb). -/
theorem normwise_perturbation_bound (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |x i - y i| ≤
      ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |ΔA j k| * |y k| + |Δb j|) := by
  -- r_j = ∑_k ΔA_{jk} y_k − Δb_j
  have hRes : ∀ j, residualVec n A y b j =
      ∑ k : Fin n, ΔA j k * y k - Δb j := by
    intro j; unfold residualVec
    have h := hPerturbed j
    have h' : ∑ k : Fin n, A j k * y k + ∑ k : Fin n, ΔA j k * y k =
        b j + Δb j := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  -- |r_j| ≤ ∑_k |ΔA_{jk}| |y_k| + |Δb_j|
  have hResBound : ∀ j, |residualVec n A y b j| ≤
      ∑ k : Fin n, |ΔA j k| * |y k| + |Δb j| := by
    intro j; rw [hRes j]
    calc |∑ k, ΔA j k * y k - Δb j|
        = |(∑ k, ΔA j k * y k) + (-Δb j)| := by ring_nf
      _ ≤ |∑ k, ΔA j k * y k| + |-Δb j| := abs_add_le _ _
      _ ≤ (∑ k, |ΔA j k * y k|) + |Δb j| := by
          rw [abs_neg]
          exact add_le_add (Finset.abs_sum_le_sum_abs _ _) (le_refl _)
      _ = (∑ k, |ΔA j k| * |y k|) + |Δb j| := by
          congr 1; apply Finset.sum_congr rfl; intro k _; exact abs_mul _ _
  -- Combine with forward_error_from_residual
  have hFwd := forward_error_from_residual n A A_inv x y b hInv hAx
  intro i
  calc |x i - y i|
      ≤ ∑ j, |A_inv i j| * |residualVec n A y b j| := hFwd i
    _ ≤ ∑ j, |A_inv i j| * (∑ k, |ΔA j k| * |y k| + |Δb j|) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hResBound j) (abs_nonneg _)

-- ============================================================
-- §7.2  Oettli–Prager necessary direction (Theorem 7.3 ⇒)
-- ============================================================

/-- **Oettli–Prager, necessary direction** (Higham Theorem 7.3 ⇒).

    If (A + ΔA)y = b + Δb with |ΔA_{ij}| ≤ ε E_{ij} and |Δb_i| ≤ ε f_i,
    then the residual r = b − Ay satisfies:
      |r_i| ≤ ε (∑_j E_{ij} |y_j| + f_i) -/
theorem oettli_prager_necessary (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (_hE : ∀ i j, 0 ≤ E i j) (_hf : ∀ i, 0 ≤ f i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |residualVec n A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i) := by
  intro i
  -- r_i = ∑_j ΔA_{ij} y_j − Δb_i
  have hRes : residualVec n A y b i =
      ∑ j : Fin n, ΔA i j * y j - Δb i := by
    unfold residualVec
    have h := hPerturbed i
    have h' : ∑ k : Fin n, A i k * y k + ∑ k : Fin n, ΔA i k * y k =
        b i + Δb i := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hRes]
  calc |∑ j, ΔA i j * y j - Δb i|
      ≤ |∑ j, ΔA i j * y j| + |Δb i| := by
        calc |∑ j, ΔA i j * y j - Δb i|
            = |(∑ j, ΔA i j * y j) + (-Δb i)| := by ring_nf
          _ ≤ |∑ j, ΔA i j * y j| + |-Δb i| := abs_add_le _ _
          _ = |∑ j, ΔA i j * y j| + |Δb i| := by rw [abs_neg]
    _ ≤ (∑ j, |ΔA i j| * |y j|) + |Δb i| := by
        apply add_le_add _ (le_refl _)
        calc |∑ j, ΔA i j * y j|
            ≤ ∑ j, |ΔA i j * y j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, |ΔA i j| * |y j| := by
              apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ (∑ j, ε * E i j * |y j|) + ε * f i := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro j _
          exact mul_le_mul_of_nonneg_right (hΔA i j) (abs_nonneg _)
        · exact hΔb i
    _ = ε * (∑ j, E i j * |y j| + f i) := by
        have : ∑ j : Fin n, ε * E i j * |y j| =
            ε * ∑ j : Fin n, E i j * |y j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        linarith

-- ============================================================
-- §7.2  Componentwise forward error (Theorem 7.4)
-- ============================================================

/-- **Componentwise forward error** (Higham Theorem 7.4).

    If Ax = b, (A + ΔA)y = b + Δb with |ΔA| ≤ ε E and |Δb| ≤ ε f,
    and A_inv is a left inverse of A, then:
      |x_i − y_i| ≤ ε · ∑_j |A⁻¹_{ij}| (∑_k E_{jk} |y_k| + f_j)

    This combines Theorem 7.3 (necessary direction) with |x − y| ≤ |A⁻¹||r|. -/
theorem componentwise_forward_error (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |x i - y i| ≤
      ε * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, E j k * |y k| + f j) := by
  have hOP := oettli_prager_necessary n A y b ΔA Δb E f ε hε hΔA hΔb hE hf hPerturbed
  have hFwd := forward_error_from_residual n A A_inv x y b hInv hAx
  intro i
  calc |x i - y i|
      ≤ ∑ j, |A_inv i j| * |residualVec n A y b j| := hFwd i
    _ ≤ ∑ j, |A_inv i j| * (ε * (∑ k, E j k * |y k| + f j)) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hOP j) (abs_nonneg _)
    _ = ε * ∑ j, |A_inv i j| * (∑ k, E j k * |y k| + f j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring

-- ============================================================
-- §7.2  Standard specialization: E = |A|, f = |b|
-- ============================================================

/-- **Standard componentwise forward error** (Higham §7.2, eq. 7.14).

    Specialization of Theorem 7.4 with E = |A| and f = |b|:
      |x_i − y_i| ≤ ε · ∑_j |A⁻¹_{ij}| (∑_k |A_{jk}| |y_k| + |b_j|)

    This is the bound in terms of the componentwise backward error ω(y). -/
theorem componentwise_forward_error_standard (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hΔb : ∀ i, |Δb i| ≤ ε * |b i|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |x i - y i| ≤
      ε * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k| * |y k| + |b j|) :=
  componentwise_forward_error n A A_inv x y b ΔA Δb
    (absMatrix n A) (absVec n b) ε hε hΔA hΔb
    (fun _ _ => abs_nonneg _) (fun _ => abs_nonneg _)
    hInv hAx hPerturbed

-- ============================================================
-- §7.2  Condition numbers
-- ============================================================

/-- **Componentwise condition number** cond(A, x) (Higham §7.2, eq. 7.17).

    For the system Ax = b, the componentwise condition number at solution x is:
      cond(A, x)_i = (|A⁻¹|(|A||x| + |b|))_i / |x_i|

    This measures the sensitivity of component x_i to componentwise perturbations
    of A and b of relative size ε.  The forward error satisfies
      |Δx_i| / |x_i| ≤ cond(A, x)_i · ε + O(ε²). -/
noncomputable def condComp (n : ℕ) (A A_inv : Fin n → Fin n → ℝ)
    (x b : Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j : Fin n, |A_inv i j| *
    (∑ k : Fin n, |A j k| * |x k| + |b j|)) / |x i|

/-- **Skeel condition number** cond(A) (Higham §7.2, eq. 7.18).

    cond(A) = max_i ∑_j (|A⁻¹| |A|)_{ij}

    This is the infinity norm of the matrix |A⁻¹||A| and satisfies
    cond(A) ≥ cond(A, x) for all x.  It is computable without knowing x. -/
noncomputable def condSkeel (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|))

/-- **Standard infinity-norm condition number** κ_∞(A) (Higham §7.2, eq. 7.19).

    κ_∞(A) = ‖A‖_∞ · ‖A⁻¹‖_∞

    where ‖M‖_∞ = max_i ∑_j |M_{ij}|.  Satisfies cond(A) ≤ κ_∞(A). -/
noncomputable def kappaInf (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) : ℝ :=
  (Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => ∑ j : Fin n, |A i j|)) *
  (Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
    (fun i => ∑ j : Fin n, |A_inv i j|))

-- ============================================================
-- §7.2  cond(A) ≤ κ_∞(A)
-- ============================================================

/-- **Skeel ≤ standard condition number** (Higham §7.2, eq. 7.19).

    cond(A) = ‖|A⁻¹||A|‖_∞ ≤ ‖A⁻¹‖_∞ · ‖A‖_∞ = κ_∞(A).

    Proof: for each row i,
      ∑_j |A⁻¹_{ij}| · (∑_k |A_{jk}|) ≤ (∑_j |A⁻¹_{ij}|) · max_j(∑_k |A_{jk}|)
    ≤ ‖A⁻¹‖_∞ · ‖A‖_∞. -/
theorem condSkeel_le_kappaInf (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    condSkeel n hn A A_inv ≤ kappaInf n hn A A_inv := by
  unfold condSkeel kappaInf
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  apply Finset.sup'_le _ _ (fun i _ => ?_)
  -- For each row i: ∑_j |A⁻¹_{ij}| (∑_k |A_{jk}|) ≤ (∑_j |A⁻¹_{ij}|) · ‖A‖_∞
  have hA_norm : ∀ j : Fin n, ∑ k : Fin n, |A j k| ≤
      Finset.sup' Finset.univ hne (fun i' => ∑ k : Fin n, |A i' k|) :=
    fun j => Finset.le_sup' (fun i' => ∑ k : Fin n, |A i' k|) (Finset.mem_univ j)
  have hAinv_norm : ∑ j : Fin n, |A_inv i j| ≤
      Finset.sup' Finset.univ hne (fun i' => ∑ j : Fin n, |A_inv i' j|) :=
    Finset.le_sup' (fun i' => ∑ j : Fin n, |A_inv i' j|) (Finset.mem_univ i)
  have hnormA_nn : 0 ≤
      Finset.sup' Finset.univ hne (fun i' => ∑ k : Fin n, |A i' k|) :=
    le_trans (Finset.sum_nonneg (fun j _ => abs_nonneg _))
      (Finset.le_sup' (fun i' => ∑ k : Fin n, |A i' k|) (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
  calc ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|)
      ≤ ∑ j : Fin n, |A_inv i j| *
        Finset.sup' Finset.univ hne (fun i' => ∑ k : Fin n, |A i' k|) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hA_norm j) (abs_nonneg _)
    _ = (∑ j : Fin n, |A_inv i j|) *
        Finset.sup' Finset.univ hne (fun i' => ∑ k : Fin n, |A i' k|) := by
        rw [Finset.sum_mul]
    _ ≤ Finset.sup' Finset.univ hne (fun i' => ∑ j : Fin n, |A_inv i' j|) *
        Finset.sup' Finset.univ hne (fun i' => ∑ k : Fin n, |A i' k|) := by
        exact mul_le_mul_of_nonneg_right hAinv_norm hnormA_nn
    _ = Finset.sup' Finset.univ hne (fun i' => ∑ j : Fin n, |A i' j|) *
        Finset.sup' Finset.univ hne (fun i' => ∑ j : Fin n, |A_inv i' j|) := by
        ring

/-- The repository `infNorm` agrees with the explicit finite row-sum maximum
    used in Higham's \(\kappa_\infty\) definition. -/
theorem infNorm_eq_sup_row_sum (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) :
    infNorm A =
      Finset.sup' Finset.univ
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i => ∑ j : Fin n, |A i j|) := by
  let s : Finset (Fin n) := Finset.univ
  have hne : s.Nonempty := Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  have hsup_nonneg :
      0 ≤ Finset.sup' s hne (fun i => ∑ j : Fin n, |A i j|) := by
    have hrow0 : 0 ≤ ∑ j : Fin n, |A ⟨0, hn⟩ j| :=
      Finset.sum_nonneg (fun j _ => abs_nonneg (A ⟨0, hn⟩ j))
    exact le_trans hrow0
      (Finset.le_sup' (fun i => ∑ j : Fin n, |A i j|)
        (Finset.mem_univ ⟨0, hn⟩))
  apply le_antisymm
  · apply infNorm_le_of_row_sum_le
    · intro i
      exact Finset.le_sup' (fun i => ∑ j : Fin n, |A i j|)
        (Finset.mem_univ i)
    · exact hsup_nonneg
  · apply Finset.sup'_le
    intro i _
    exact row_sum_le_infNorm A i

/-- Higham's `kappaInf` is exactly the product of the repository infinity
    norms. -/
theorem kappaInf_eq_infNorm_mul_infNorm (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    kappaInf n hn A A_inv = infNorm A * infNorm A_inv := by
  unfold kappaInf
  rw [← infNorm_eq_sup_row_sum n hn A,
    ← infNorm_eq_sup_row_sum n hn A_inv]

/-- Nonnegativity of Higham's infinity-norm condition number. -/
lemma kappaInf_nonneg (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) :
    0 ≤ kappaInf n hn A A_inv := by
  rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]
  exact mul_nonneg (infNorm_nonneg A) (infNorm_nonneg A_inv)

/-- A \(\kappa_\infty\) bound and a positive lower bound on `‖A‖∞` give an
    upper bound on `‖A⁻¹‖∞`. -/
theorem infNorm_inv_le_of_kappaInf_le_and_norm_lower (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (κ ρ : ℝ)
    (hρ : 0 < ρ)
    (hρ_le : ρ ≤ infNorm A)
    (hκ : kappaInf n hn A A_inv ≤ κ) :
    infNorm A_inv ≤ κ / ρ := by
  have hprod : ρ * infNorm A_inv ≤ κ := by
    calc ρ * infNorm A_inv
        ≤ infNorm A * infNorm A_inv :=
          mul_le_mul_of_nonneg_right hρ_le (infNorm_nonneg A_inv)
      _ = kappaInf n hn A A_inv := by
          rw [kappaInf_eq_infNorm_mul_infNorm n hn A A_inv]
      _ ≤ κ := hκ
  exact (le_div_iff₀ hρ).mpr (by simpa [mul_comm] using hprod)

/-- A \(\kappa_\infty\) bound for a nonsingular matrix bounds
    `‖A_inv‖∞` with the actual denominator `‖A‖∞`.

    This removes the auxiliary lower-bound parameter `ρ` when a determinant
    certificate is already available. -/
theorem infNorm_inv_le_of_kappaInf_le_and_det_ne_zero (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (κ : ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hκ : kappaInf n hn A A_inv ≤ κ) :
    infNorm A_inv ≤ κ / infNorm A :=
  infNorm_inv_le_of_kappaInf_le_and_norm_lower n hn A A_inv κ (infNorm A)
    (infNorm_pos_of_det_ne_zero hn A hdet) (le_rfl) hκ

/-- Squared-budget form of the \(\kappa_\infty\)-to-inverse-norm bridge.
    This is the shape needed by the QR nonbreakdown route. -/
theorem infNorm_sq_budget_of_kappaInf_le_and_norm_lower (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (κ ρ K : ℝ)
    (hρ : 0 < ρ)
    (hρ_le : ρ ≤ infNorm A)
    (hκ : kappaInf n hn A A_inv ≤ κ)
    (hbudget : (n : ℝ) * (κ / ρ) ^ 2 ≤ K) :
    (n : ℝ) * infNorm A_inv ^ 2 ≤ K := by
  have hle :
      infNorm A_inv ≤ κ / ρ :=
    infNorm_inv_le_of_kappaInf_le_and_norm_lower n hn A A_inv κ ρ hρ hρ_le hκ
  have hκ_nonneg : 0 ≤ κ := le_trans (kappaInf_nonneg n hn A A_inv) hκ
  have hdiv_nonneg : 0 ≤ κ / ρ := div_nonneg hκ_nonneg (le_of_lt hρ)
  have hinv_nonneg : 0 ≤ infNorm A_inv := infNorm_nonneg A_inv
  have hsquare : infNorm A_inv ^ 2 ≤ (κ / ρ) ^ 2 := by
    nlinarith
  exact
    (mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg n)).trans hbudget

/-- Squared-budget form of the determinant-based
    \(\kappa_\infty\)-to-inverse-norm bridge. -/
theorem infNorm_sq_budget_of_kappaInf_le_and_det_ne_zero (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (κ K : ℝ)
    (hdet : Matrix.det (A : Matrix (Fin n) (Fin n) ℝ) ≠ 0)
    (hκ : kappaInf n hn A A_inv ≤ κ)
    (hbudget : (n : ℝ) * (κ / infNorm A) ^ 2 ≤ K) :
    (n : ℝ) * infNorm A_inv ^ 2 ≤ K := by
  exact
    infNorm_sq_budget_of_kappaInf_le_and_norm_lower n hn A A_inv κ
      (infNorm A) K (infNorm_pos_of_det_ne_zero hn A hdet) (le_rfl) hκ
      hbudget

-- ============================================================
-- §7.3  Oettli–Prager sufficient direction (Theorem 7.3 ⇐)
-- ============================================================

/-- Sign indicator: +1 if x ≥ 0, −1 if x < 0.
    Used in the Oettli–Prager construction to build ΔA such that
    ΔA_{ij} y_j = t_i E_{ij} |y_j|. -/
noncomputable def signInd (x : ℝ) : ℝ :=
  if 0 ≤ x then 1 else -1

lemma signInd_mul_eq_abs (x : ℝ) : signInd x * x = |x| := by
  unfold signInd
  split_ifs with h
  · simp [abs_of_nonneg h]
  · push_neg at h; simp [abs_of_neg h]

lemma abs_signInd (x : ℝ) : |signInd x| = 1 := by
  unfold signInd
  split_ifs <;> simp

/-- Helper: |t| ≤ ε when t = r/s and |r| ≤ ε * s with s ≥ 0. -/
private lemma div_abs_le_of_bound {r s ε : ℝ} (hε : 0 ≤ ε)
    (hs_nn : 0 ≤ s) (hBound : |r| ≤ ε * s) :
    |if s = 0 then 0 else r / s| ≤ ε := by
  split_ifs with hs
  · rw [abs_zero]; exact hε
  · have hs_pos : 0 < s := lt_of_le_of_ne hs_nn (Ne.symm hs)
    rw [abs_div, abs_of_pos hs_pos]
    -- |r| / s ≤ ε  ⟸  |r| ≤ ε * s (since s > 0)
    have hsi : 0 < (s : ℝ)⁻¹ := inv_pos.mpr hs_pos
    rw [div_eq_mul_inv]
    calc |r| * s⁻¹ ≤ (ε * s) * s⁻¹ :=
          mul_le_mul_of_nonneg_right hBound (le_of_lt hsi)
      _ = ε := by field_simp

/-- **Oettli–Prager, sufficient direction** (Higham Theorem 7.3 ⇐).

    If |r_i| ≤ ε (∑_j E_{ij} |y_j| + f_i) for all i, then there exist
    ΔA, Δb with |ΔA_{ij}| ≤ ε E_{ij}, |Δb_i| ≤ ε f_i,
    and (A + ΔA)y = b + Δb.

    Construction: let s_i = ∑_j E_{ij}|y_j| + f_i. If s_i > 0, set
    t_i = r_i/s_i; otherwise t_i = 0.  Then:
      ΔA_{ij} = t_i · E_{ij} · sign(y_j)
      Δb_i = −t_i · f_i -/
theorem oettli_prager_sufficient (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hBound : ∀ i, |residualVec n A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i)) :
    ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * E i j) ∧
      (∀ i, |Δb i| ≤ ε * f i) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  set r := residualVec n A y b with hr_def
  set s := fun i => ∑ j : Fin n, E i j * |y j| + f i with hs_def
  set t := fun i => if s i = 0 then 0 else r i / s i with ht_def
  set ΔA := fun i j => t i * E i j * signInd (y j)
  set Δb := fun i => -(t i * f i)
  have hs_nn : ∀ i, 0 ≤ s i := fun i =>
    add_nonneg (Finset.sum_nonneg (fun j _ => mul_nonneg (hE i j) (abs_nonneg _))) (hf i)
  have ht_bound : ∀ i, |t i| ≤ ε := fun i =>
    div_abs_le_of_bound hε (hs_nn i) (hBound i)
  refine ⟨ΔA, Δb, ?_, ?_, ?_⟩
  -- Bound on ΔA: |ΔA_{ij}| ≤ ε E_{ij}
  · intro i j
    show |t i * E i j * signInd (y j)| ≤ ε * E i j
    rw [abs_mul, abs_mul, abs_signInd, mul_one]
    calc |t i| * |E i j| ≤ ε * |E i j| :=
          mul_le_mul_of_nonneg_right (ht_bound i) (abs_nonneg _)
      _ = ε * E i j := by rw [abs_of_nonneg (hE i j)]
  -- Bound on Δb: |Δb_i| ≤ ε f_i
  · intro i
    show |-(t i * f i)| ≤ ε * f i
    rw [abs_neg, abs_mul]
    calc |t i| * |f i| ≤ ε * |f i| :=
          mul_le_mul_of_nonneg_right (ht_bound i) (abs_nonneg _)
      _ = ε * f i := by rw [abs_of_nonneg (hf i)]
  -- Exactness: (A + ΔA)y = b + Δb
  · intro i
    have hΔA_y : ∀ j, ΔA i j * y j = t i * E i j * |y j| := by
      intro j
      show t i * E i j * signInd (y j) * y j = t i * E i j * |y j|
      rw [mul_assoc (t i * E i j), signInd_mul_eq_abs]
    rw [Finset.sum_congr rfl (fun j _ => by rw [add_mul, hΔA_y j])]
    rw [Finset.sum_add_distrib]
    show ∑ j, A i j * y j + ∑ j, t i * E i j * |y j| = b i + -(t i * f i)
    have hsum : ∑ j : Fin n, t i * E i j * |y j| =
        t i * ∑ j : Fin n, E i j * |y j| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hsum]
    -- t_i * s_i = r_i
    have hts : t i * s i = r i := by
      simp only [ht_def, hs_def]
      split_ifs with hs
      · -- s_i = 0 implies r_i = 0
        simp only [zero_mul]
        have h_zero : |r i| ≤ 0 := by
          calc |r i| ≤ ε * (∑ j, E i j * |y j| + f i) := hBound i
            _ = ε * 0 := by rw [hs]
            _ = 0 := by ring
        symm; exact abs_eq_zero.mp (le_antisymm h_zero (abs_nonneg _))
      · exact div_mul_cancel₀ (r i) hs
    have hr_eq : r i = b i - ∑ j : Fin n, A i j * y j := rfl
    linarith [hts, hr_eq]

-- ============================================================
-- §7.3  Full Oettli–Prager characterization (Theorem 7.3)
-- ============================================================

/-- **Oettli–Prager theorem** (Higham Theorem 7.3, full characterization).

    The componentwise backward error ω(y) := min{ε : ∃ ΔA, Δb with
    |ΔA| ≤ εE, |Δb| ≤ εf, (A+ΔA)y = b+Δb} satisfies:
      ω(y) = max_i |r_i| / (E|y| + f)_i

    Here we state the equivalence: |r| ≤ ε(E|y| + f) if and only if
    such ΔA, Δb exist. -/
theorem oettli_prager (n : ℕ)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i) :
    (∀ i, |residualVec n A y b i| ≤
      ε * (∑ j : Fin n, E i j * |y j| + f i)) ↔
    (∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i j, |ΔA i j| ≤ ε * E i j) ∧
      (∀ i, |Δb i| ≤ ε * f i) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)) := by
  constructor
  · exact oettli_prager_sufficient n A y b E f ε hε hE hf
  · intro ⟨ΔA, Δb, hΔA, hΔb, hExact⟩
    exact oettli_prager_necessary n A y b ΔA Δb E f ε hε hΔA hΔb hE hf hExact

-- ============================================================
-- §7.4  Backward error contraction via forward error
-- ============================================================

/-- **Componentwise forward error with explicit backward error**
    (Higham §7.2, combining Theorems 7.3 and 7.4).

    If ω(y) ≤ ε (the componentwise backward error), then the forward error
    satisfies:
      |x_i − y_i| ≤ ε · (|A⁻¹|(|A||y| + |b|))_i

    Stated without dividing by |x_i| (to avoid division by zero). -/
theorem forward_error_from_backward_error (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hResBound : ∀ i, |residualVec n A y b i| ≤
      ε * (∑ j : Fin n, |A i j| * |y j| + |b i|)) :
    ∀ i, |x i - y i| ≤
      ε * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k| * |y k| + |b j|) := by
  have hFwd := forward_error_from_residual n A A_inv x y b hInv hAx
  intro i
  calc |x i - y i|
      ≤ ∑ j, |A_inv i j| * |residualVec n A y b j| := hFwd i
    _ ≤ ∑ j, |A_inv i j| *
        (ε * (∑ k, |A j k| * |y k| + |b j|)) := by
        apply Finset.sum_le_sum; intro j _
        exact mul_le_mul_of_nonneg_left (hResBound j) (abs_nonneg _)
    _ = ε * ∑ j, |A_inv i j| * (∑ k, |A j k| * |y k| + |b j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _; ring

-- ============================================================
-- §7.2  Normwise forward error with perturbation bounds
-- ============================================================

/-- **Normwise forward error with perturbation bounds** (Higham Theorem 7.2).

    If (A + ΔA)y = b + Δb with |ΔA_{ij}| ≤ ε|A_{ij}|, |Δb_i| ≤ ε|b_i|,
    then:
      |x_i − y_i| ≤ ε · (|A⁻¹|(|A||y| + |b|))_i

    This is the normwise-to-componentwise bridge: starting from a normwise
    backward error bound, we get a componentwise forward error. -/
theorem normwise_to_componentwise_forward (n : ℕ)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hΔb : ∀ i, |Δb i| ≤ ε * |b i|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    ∀ i, |x i - y i| ≤
      ε * ∑ j : Fin n, |A_inv i j| *
        (∑ k : Fin n, |A j k| * |y k| + |b j|) := by
  have h := normwise_perturbation_bound n A A_inv x y b ΔA Δb hInv hAx hPerturbed
  intro i
  calc |x i - y i|
      ≤ ∑ j, |A_inv i j| * (∑ k, |ΔA j k| * |y k| + |Δb j|) := h i
    _ ≤ ∑ j, |A_inv i j| * (∑ k, ε * |A j k| * |y k| + ε * |b j|) := by
        apply Finset.sum_le_sum; intro j _
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply add_le_add
        · apply Finset.sum_le_sum; intro k _
          exact mul_le_mul_of_nonneg_right (hΔA j k) (abs_nonneg _)
        · exact hΔb j
    _ = ε * ∑ j, |A_inv i j| * (∑ k, |A j k| * |y k| + |b j|) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        have : ∑ k : Fin n, ε * |A j k| * |y k| + ε * |b j| =
            ε * (∑ k : Fin n, |A j k| * |y k| + |b j|) := by
          rw [mul_add, Finset.mul_sum]
          congr 1; apply Finset.sum_congr rfl; intro k _; ring
        rw [this]; ring

-- ============================================================
-- §7.2  Linear contraction lemma
-- ============================================================

/-- If a ≤ b + c · a with c < 1 then a ≤ b / (1 − c). -/
private lemma le_div_one_sub_of_le_add_mul {a b c : ℝ}
    (hc1 : c < 1) (h : a ≤ b + c * a) :
    a ≤ b / (1 - c) := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have h1c_ne : (1 - c : ℝ) ≠ 0 := ne_of_gt h1c
  have hac : a * (1 - c) ≤ b := by nlinarith
  have hinv : (0 : ℝ) ≤ (1 - c)⁻¹ := le_of_lt (inv_pos.mpr h1c)
  calc a = a * (1 - c) / (1 - c) := by field_simp
    _ ≤ b / (1 - c) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hac hinv

-- ============================================================
-- §7.2  Exact componentwise forward error (Theorem 7.4, eq. 7.9)
-- ============================================================

/-- **Exact componentwise forward error** (Higham Theorem 7.4, eq. 7.9).

    If Ax = b, (A + ΔA)y = b + Δb with |ΔA| ≤ εE, |Δb| ≤ εf,
    and εM < 1 where M ≥ ‖|A⁻¹|E‖_∞, then:
      |x_i − y_i| ≤ (ε / (1 − εM)) · ‖|A⁻¹|(E|x| + f)‖_∞

    This is the exact form of eq. (7.9), with the 1/(1 − ε‖|A⁻¹|E‖)
    denominator, expressed in terms of the true solution |x|. -/
theorem componentwise_forward_error_exact (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (E : Fin n → Fin n → ℝ) (f : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * E i j)
    (hΔb : ∀ i, |Δb i| ≤ ε * f i)
    (hE : ∀ i j, 0 ≤ E i j) (hf : ∀ i, 0 ≤ f i)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (M : ℝ) (hM : ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k) ≤ M)
    (hεM : ε * M < 1) :
    ∀ i, |x i - y i| ≤
      ε / (1 - ε * M) *
      Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i => ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, E j k * |x k| + f j)) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  -- Abbreviations (transparent via let)
  let ef := fun i : Fin n =>
    ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k * |x k| + f j)
  let C := Finset.sup' Finset.univ hne ef
  let δ := Finset.sup' Finset.univ hne (fun i => |x i - y i|)
  -- Nonnegativity
  have hef_nn : ∀ i, 0 ≤ ef i := fun i =>
    Finset.sum_nonneg fun j _ =>
      mul_nonneg (abs_nonneg _) (add_nonneg
        (Finset.sum_nonneg fun k _ => mul_nonneg (hE j k) (abs_nonneg _)) (hf j))
  have hC_nn : 0 ≤ C :=
    le_trans (hef_nn ⟨0, hn⟩) (Finset.le_sup' ef (Finset.mem_univ _))
  have hδ_nn : 0 ≤ δ :=
    le_trans (abs_nonneg (x ⟨0, hn⟩ - y ⟨0, hn⟩))
      (Finset.le_sup' (fun i : Fin n => |x i - y i|) (Finset.mem_univ _))
  -- From componentwise_forward_error (first-order, with |y|)
  have hCFE := componentwise_forward_error n A A_inv x y b ΔA Δb E f ε hε
    hΔA hΔb hE hf hInv hAx hPerturbed
  -- |y_k| ≤ |x_k| + δ
  have h_yk : ∀ k : Fin n, |y k| ≤ |x k| + δ := by
    intro k
    have hle : |x k - y k| ≤ δ :=
      Finset.le_sup' (fun i : Fin n => |x i - y i|) (Finset.mem_univ k)
    calc |y k| = |(x k) + (y k - x k)| := by ring_nf
      _ ≤ |x k| + |y k - x k| := abs_add_le _ _
      _ = |x k| + |x k - y k| := by rw [abs_sub_comm]
      _ ≤ |x k| + δ := add_le_add (le_refl _) hle
  -- Row bound: ∑_j |A⁻¹_{ij}|(∑_k E_{jk}|y_k| + f_j) ≤ C + δ · M
  have h_row : ∀ i : Fin n,
      ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k * |y k| + f j) ≤
      C + δ * M := by
    intro i
    have h1 : ∀ j : Fin n,
        ∑ k : Fin n, E j k * |y k| ≤
        ∑ k : Fin n, E j k * |x k| + δ * ∑ k : Fin n, E j k := by
      intro j
      calc ∑ k : Fin n, E j k * |y k|
          ≤ ∑ k : Fin n, E j k * (|x k| + δ) := by
            apply Finset.sum_le_sum; intro k _
            exact mul_le_mul_of_nonneg_left (h_yk k) (hE j k)
        _ = ∑ k : Fin n, E j k * |x k| + δ * ∑ k : Fin n, E j k := by
            simp_rw [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
            congr 1; apply Finset.sum_congr rfl; intro k _; ring
    calc ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k * |y k| + f j)
        ≤ ∑ j : Fin n, |A_inv i j| *
          ((∑ k : Fin n, E j k * |x k| + f j) +
            δ * ∑ k : Fin n, E j k) := by
          apply Finset.sum_le_sum; intro j _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          linarith [h1 j]
      _ = (∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, E j k * |x k| + f j)) +
          δ * (∑ j : Fin n, |A_inv i j| * ∑ k : Fin n, E j k) := by
          have h_dist : ∀ j : Fin n,
              |A_inv i j| * ((∑ k : Fin n, E j k * |x k| + f j) +
                δ * ∑ k : Fin n, E j k) =
              |A_inv i j| * (∑ k : Fin n, E j k * |x k| + f j) +
              δ * (|A_inv i j| * ∑ k : Fin n, E j k) := by
            intro j; ring
          simp_rw [h_dist, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ C + δ * M := by
          apply add_le_add
          · exact Finset.le_sup' ef (Finset.mem_univ i)
          · exact mul_le_mul_of_nonneg_left (hM i) hδ_nn
  -- Contraction: δ ≤ εC + εMδ → δ ≤ εC/(1-εM)
  have hδ_bound : δ ≤ ε * C / (1 - ε * M) := by
    apply le_div_one_sub_of_le_add_mul hεM
    apply Finset.sup'_le _ _ (fun i' _ => ?_)
    calc |x i' - y i'|
        ≤ ε * ∑ j : Fin n, |A_inv i' j| *
          (∑ k : Fin n, E j k * |y k| + f j) := hCFE i'
      _ ≤ ε * (C + δ * M) := mul_le_mul_of_nonneg_left (h_row i') hε
      _ = ε * C + ε * M * δ := by ring
  -- Conclude: for each i, |x_i - y_i| ≤ ε/(1-εM) · C
  intro i
  calc |x i - y i|
      ≤ δ := Finset.le_sup' (fun i : Fin n => |x i - y i|) (Finset.mem_univ i)
    _ ≤ ε * C / (1 - ε * M) := hδ_bound
    _ = ε / (1 - ε * M) * C := by ring

-- ============================================================
-- §7.1  Rigal–Gaches backward error (Theorem 7.1)
-- ============================================================

/-- **Rigal–Gaches, necessary direction** (Higham Theorem 7.1 ⇒).

    If (A + ΔA)y = b + Δb with ∀ i, ∑_j |ΔA_{ij}| ≤ ε α and
    ∀ i, |Δb_i| ≤ ε β, then:
      |r_i| ≤ ε (α ‖y‖_∞ + β)  for all i

    where r = b − Ay and ‖y‖_∞ = max_j |y_j|. -/
theorem rigal_gaches_necessary (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (α β ε : ℝ) (_hε : 0 ≤ ε)
    (hΔA : ∀ i, ∑ j : Fin n, |ΔA i j| ≤ ε * α)
    (hΔb : ∀ i, |Δb i| ≤ ε * β)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) :
    let yNorm := Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|)
    ∀ i, |residualVec n A y b i| ≤ ε * (α * yNorm + β) := by
  intro yNorm i
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  -- r_i = ∑_j ΔA_{ij} y_j − Δb_i
  have hRes : residualVec n A y b i =
      ∑ j : Fin n, ΔA i j * y j - Δb i := by
    unfold residualVec
    have h := hPerturbed i
    have h' : ∑ k : Fin n, A i k * y k + ∑ k : Fin n, ΔA i k * y k =
        b i + Δb i := by
      rw [← Finset.sum_add_distrib]
      convert h using 1
      apply Finset.sum_congr rfl; intro k _; ring
    linarith
  rw [hRes]
  -- |r_i| ≤ ∑_j |ΔA_{ij}| · ‖y‖_∞ + |Δb_i|
  have hy_le : ∀ j : Fin n, |y j| ≤ yNorm :=
    fun j => Finset.le_sup' (fun j => |y j|) (Finset.mem_univ j)
  calc |∑ j, ΔA i j * y j - Δb i|
      ≤ |∑ j, ΔA i j * y j| + |Δb i| := by
        calc |∑ j, ΔA i j * y j - Δb i|
            = |(∑ j, ΔA i j * y j) + (-Δb i)| := by ring_nf
          _ ≤ |∑ j, ΔA i j * y j| + |-Δb i| := abs_add_le _ _
          _ = |∑ j, ΔA i j * y j| + |Δb i| := by rw [abs_neg]
    _ ≤ (∑ j, |ΔA i j| * |y j|) + |Δb i| := by
        apply add_le_add _ (le_refl _)
        calc |∑ j, ΔA i j * y j|
            ≤ ∑ j, |ΔA i j * y j| := Finset.abs_sum_le_sum_abs _ _
          _ = ∑ j, |ΔA i j| * |y j| := by
              apply Finset.sum_congr rfl; intro j _; exact abs_mul _ _
    _ ≤ (∑ j, |ΔA i j|) * yNorm + |Δb i| := by
        apply add_le_add _ (le_refl _)
        calc ∑ j, |ΔA i j| * |y j|
            ≤ ∑ j, |ΔA i j| * yNorm := by
              apply Finset.sum_le_sum; intro j _
              exact mul_le_mul_of_nonneg_left (hy_le j) (abs_nonneg _)
          _ = (∑ j, |ΔA i j|) * yNorm := by rw [Finset.sum_mul]
    _ ≤ ε * α * yNorm + ε * β := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (hΔA i)
            (le_trans (abs_nonneg _) (hy_le ⟨0, hn⟩))
        · exact hΔb i
    _ = ε * (α * yNorm + β) := by ring

/-- **Rigal–Gaches, sufficient direction** (Higham Theorem 7.1 ⇐).

    If |r_i| ≤ ε (α ‖y‖_∞ + β) for all i, with α ≥ 0, β ≥ 0,
    then there exist ΔA, Δb with ∑_j |ΔA_{ij}| ≤ ε α, |Δb_i| ≤ ε β,
    and (A + ΔA)y = b + Δb.

    Construction: let j* achieve ‖y‖_∞, s = α|y_{j*}| + β,
    t_i = r_i/s (0 if s = 0). Set ΔA_{ij} = t_i α δ_{j,j*} sign(y_{j*}),
    Δb_i = −t_i β. -/
theorem rigal_gaches_sufficient (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε)
    (hBound : ∀ i, |residualVec n A y b i| ≤
      ε * (α * Finset.sup' Finset.univ
        (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|) + β)) :
    ∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, |ΔA i j| ≤ ε * α) ∧
      (∀ i, |Δb i| ≤ ε * β) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i) := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩
  -- Find j* achieving ‖y‖_∞
  obtain ⟨j_star, _, hj_star⟩ :=
    Finset.exists_max_image Finset.univ (fun j => |y j|) hne
  -- ‖y‖_∞ = |y j*|
  have hyNorm : Finset.sup' Finset.univ hne (fun j => |y j|) = |y j_star| := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun j hj => hj_star j hj)
    · exact Finset.le_sup' (fun j => |y j|) (Finset.mem_univ j_star)
  set r := residualVec n A y b with hr_def
  set s := α * |y j_star| + β with hs_def
  set t := fun i => if s = 0 then 0 else r i / s with ht_def
  set ΔA := fun i j => if j = j_star then t i * α * signInd (y j_star) else 0
  set Δb := fun i => -(t i * β)
  have hs_nn : 0 ≤ s := add_nonneg (mul_nonneg hα (abs_nonneg _)) hβ
  -- |t_i| ≤ ε
  have ht_bound : ∀ i, |t i| ≤ ε := by
    intro i
    simp only [ht_def]
    rw [hyNorm] at hBound
    exact div_abs_le_of_bound hε hs_nn (hBound i)
  refine ⟨ΔA, Δb, ?_, ?_, ?_⟩
  -- Bound on ΔA: ∑_j |ΔA_{ij}| ≤ ε α
  · intro i
    have hsum : ∑ j : Fin n, |ΔA i j| = |t i| * α := by
      have : ∀ j : Fin n, |ΔA i j| =
          if j = j_star then |t i| * α else 0 := by
        intro j
        show |if j = j_star then t i * α * signInd (y j_star) else 0| =
            if j = j_star then |t i| * α else 0
        split_ifs with hj
        · rw [abs_mul, abs_mul, abs_signInd, mul_one, abs_of_nonneg hα]
        · exact abs_zero
      rw [Finset.sum_congr rfl (fun j _ => this j)]
      rw [Finset.sum_ite_eq']
      simp [Finset.mem_univ]
    rw [hsum]
    exact mul_le_mul_of_nonneg_right (ht_bound i) hα
  -- Bound on Δb: |Δb_i| ≤ ε β
  · intro i
    show |-(t i * β)| ≤ ε * β
    rw [abs_neg, abs_mul]
    calc |t i| * |β| ≤ ε * |β| :=
          mul_le_mul_of_nonneg_right (ht_bound i) (abs_nonneg _)
      _ = ε * β := by rw [abs_of_nonneg hβ]
  -- Exactness: (A + ΔA)y = b + Δb
  · intro i
    -- ΔA_{ij} y_j is nonzero only for j = j*
    have hΔA_sum : ∑ j : Fin n, ΔA i j * y j =
        t i * α * signInd (y j_star) * y j_star := by
      have : ∀ j : Fin n, ΔA i j * y j =
          if j = j_star then t i * α * signInd (y j_star) * y j_star else 0 := by
        intro j
        show (if j = j_star then t i * α * signInd (y j_star) else 0) * y j =
            if j = j_star then t i * α * signInd (y j_star) * y j_star else 0
        split_ifs with hj
        · rw [hj]
        · ring
      rw [Finset.sum_congr rfl (fun j _ => this j), Finset.sum_ite_eq']
      simp [Finset.mem_univ]
    have hsplit : ∀ j : Fin n, (A i j + ΔA i j) * y j =
        A i j * y j + ΔA i j * y j := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
    rw [Finset.sum_add_distrib, hΔA_sum]
    -- sign(y_{j*}) · y_{j*} = |y_{j*}|
    rw [mul_assoc (t i * α), signInd_mul_eq_abs]
    -- t_i · (α · |y_{j*}| + β) = r_i
    have hts : t i * s = r i := by
      simp only [ht_def, hs_def]
      split_ifs with hs
      · simp only [zero_mul]
        have h_zero : |r i| ≤ 0 := by
          rw [hyNorm] at hBound
          calc |r i| ≤ ε * (α * |y j_star| + β) := hBound i
            _ = ε * 0 := by rw [hs]
            _ = 0 := by ring
        symm; exact abs_eq_zero.mp (le_antisymm h_zero (abs_nonneg _))
      · exact div_mul_cancel₀ (r i) hs
    have hr_eq : r i = b i - ∑ j : Fin n, A i j * y j := rfl
    show ∑ j, A i j * y j + t i * α * |y j_star| = b i + -(t i * β)
    linarith [hts, hr_eq]

/-- **Rigal–Gaches theorem** (Higham Theorem 7.1, full characterization).

    The normwise backward error η(y) := min{ε : ∃ ΔA, Δb with
    ‖ΔA‖_∞ ≤ εα, ‖Δb‖_∞ ≤ εβ, (A+ΔA)y = b+Δb} satisfies:
      η(y) = ‖r‖_∞ / (α‖y‖_∞ + β)

    Here we state the equivalence: |r_i| ≤ ε(α‖y‖_∞ + β) for all i
    if and only if such ΔA, Δb exist (with row-sum bound ∑_j|ΔA_{ij}|
    and entrywise |Δb_i| bound). -/
theorem rigal_gaches (n : ℕ) (hn : 0 < n)
    (A : Fin n → Fin n → ℝ) (y b : Fin n → ℝ)
    (α β ε : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hε : 0 ≤ ε) :
    let yNorm := Finset.sup' Finset.univ
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩) (fun j => |y j|)
    (∀ i, |residualVec n A y b i| ≤ ε * (α * yNorm + β)) ↔
    (∃ (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, |ΔA i j| ≤ ε * α) ∧
      (∀ i, |Δb i| ≤ ε * β) ∧
      (∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)) := by
  intro yNorm
  constructor
  · exact rigal_gaches_sufficient n hn A y b α β ε hα hβ hε
  · intro ⟨ΔA, Δb, hΔA, hΔb, hExact⟩
    exact rigal_gaches_necessary n hn A y b ΔA Δb α β ε hε hΔA hΔb hExact

-- ============================================================
-- §7.1  Exact normwise forward error (Theorem 7.2, eq. 7.4)
-- ============================================================

/-- **Exact normwise forward error** (Higham Theorem 7.2, eq. 7.4).

    If Ax = b, (A + ΔA)y = b + Δb with |ΔA_{ij}| ≤ ε|A_{ij}|,
    |Δb_i| ≤ ε|b_i|, and εM < 1 where
    M ≥ ‖|A⁻¹||A|‖_∞ = max_i ∑_j |A⁻¹_{ij}| ∑_k |A_{jk}|, then:
      |x_i − y_i| ≤ (ε / (1 − εM)) · ‖|A⁻¹|(|A||x| + |b|)‖_∞

    This is the exact normwise form with the 1/(1 − εM) denominator,
    specializing Theorem 7.4 to E = |A|, f = |b|.  The parameter M
    is the Skeel condition number cond(A) = ‖|A⁻¹||A|‖_∞. -/
theorem normwise_forward_error_exact (n : ℕ) (hn : 0 < n)
    (A A_inv : Fin n → Fin n → ℝ) (x y b : Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ) (Δb : Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hΔA : ∀ i j, |ΔA i j| ≤ ε * |A i j|)
    (hΔb : ∀ i, |Δb i| ≤ ε * |b i|)
    (hInv : IsLeftInverse n A A_inv)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hPerturbed : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * y j = b i + Δb i)
    (M : ℝ) (hM : ∀ i, ∑ j : Fin n, |A_inv i j| * (∑ k : Fin n, |A j k|) ≤ M)
    (hεM : ε * M < 1) :
    ∀ i, |x i - y i| ≤
      ε / (1 - ε * M) *
      Finset.sup' Finset.univ (Finset.univ_nonempty_iff.mpr ⟨⟨0, hn⟩⟩)
        (fun i => ∑ j : Fin n, |A_inv i j| *
          (∑ k : Fin n, |A j k| * |x k| + |b j|)) :=
  componentwise_forward_error_exact n hn A A_inv x y b ΔA Δb
    (fun i j => |A i j|) (fun i => |b i|) ε hε hΔA hΔb
    (fun _ _ => abs_nonneg _) (fun _ => abs_nonneg _) hInv hAx hPerturbed M hM hεM

end NumStability
