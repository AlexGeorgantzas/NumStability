/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Source.Higham.Chapter24.CirculantSystems

namespace NumStability

open scoped Matrix.Norms.L2Operator

/-!
# Literal rounded stages for the Chapter 24 circulant solver

This file supplies producers for the rounded stages that are deliberately not
fields of the abstract contracts in `Circulant.Higham24`.  In particular, the
diagonal solve below is the componentwise Chapter 3 complex-division executor,
and its perturbation matrix is constructed from the primitive relative-error
theorem rather than assumed.
-/

/-- Literal rounded diagonal solve used in step (3) on printed page 455. -/
noncomputable def higham24RoundedDiagonalSolve (fp : FPModel) {n : ℕ}
    (d g : Fin n → ℂ) : Fin n → ℂ :=
  fun i => fl_complexDiv fp (g i) (d i)

/-- The relative-error coefficient selected from the proved complex-division
model at one diagonal entry. -/
noncomputable def higham24DiagonalSolveRelativeError
    (fp : FPModel) (hgamma4 : gammaValid fp 4) {n : ℕ}
    (d g : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) (i : Fin n) : ℂ :=
  Classical.choose (fl_complexDiv_rel_error_model fp hgamma4 (g i) (d i) (hd i))

/-- The selected scalar coefficient has the Chapter 3 `sqrt(2) gamma_4`
bound and represents the literal computed quotient. -/
theorem higham24_diagonalSolveRelativeError_spec
    (fp : FPModel) (hgamma4 : gammaValid fp 4) {n : ℕ}
    (d g : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) (i : Fin n) :
    ‖higham24DiagonalSolveRelativeError fp hgamma4 d g hd i‖ ≤
        Real.sqrt 2 * gamma fp 4 ∧
      higham24RoundedDiagonalSolve fp d g i =
        (g i / d i) *
          (1 + higham24DiagonalSolveRelativeError fp hgamma4 d g hd i) := by
  exact Classical.choose_spec
    (fl_complexDiv_rel_error_model fp hgamma4 (g i) (d i) (hd i))

/-- Diagonal perturbation matrix produced by the literal componentwise solve. -/
noncomputable def higham24DiagonalSolvePerturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4) {n : ℕ}
    (d g : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (higham24DiagonalSolveRelativeError fp hgamma4 d g hd)

/-- Exact inverse diagonal in the four-stage solver. -/
noncomputable def higham24InverseDiagonal {n : ℕ}
    (d : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (d i)⁻¹)

/-- The literal rounded diagonal solve has exactly the `(I+E)D⁻¹g` form used
between (24.7) and (24.8). -/
theorem higham24_roundedDiagonalSolve_representation
    (fp : FPModel) (hgamma4 : gammaValid fp 4) {n : ℕ}
    (d g : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) :
    higham24RoundedDiagonalSolve fp d g =
      ((1 + higham24DiagonalSolvePerturbation fp hgamma4 d g hd) *
        higham24InverseDiagonal d).mulVec g := by
  funext i
  rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply]
  unfold higham24DiagonalSolvePerturbation higham24InverseDiagonal
  rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal,
    Matrix.mulVec_diagonal]
  rw [(higham24_diagonalSolveRelativeError_spec fp hgamma4 d g hd i).2]
  ring

/-- The produced diagonal perturbation has the spectral-norm budget printed
after (24.7). -/
theorem higham24_diagonalSolvePerturbation_norm_le
    (fp : FPModel) (hgamma4 : gammaValid fp 4) {n : ℕ}
    (d g : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) :
    ‖higham24DiagonalSolvePerturbation fp hgamma4 d g hd‖ ≤
      Real.sqrt 2 * gamma fp 4 := by
  rw [higham24DiagonalSolvePerturbation, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (gamma_nonneg fp hgamma4))).2
  intro i
  exact (higham24_diagonalSolveRelativeError_spec fp hgamma4 d g hd i).1

/-- Producer form of the complete rounded diagonal-scaling line: both its
matrix equation and its norm bound are consequences of the literal executor. -/
theorem higham24_roundedDiagonalSolve_exists_perturbation
    (fp : FPModel) (hgamma4 : gammaValid fp 4) {n : ℕ}
    (d g : Fin n → ℂ) (hd : ∀ i, d i ≠ 0) :
    ∃ E : Matrix (Fin n) (Fin n) ℂ,
      higham24RoundedDiagonalSolve fp d g =
          ((1 + E) * higham24InverseDiagonal d).mulVec g ∧
        ‖E‖ ≤ Real.sqrt 2 * gamma fp 4 := by
  exact ⟨higham24DiagonalSolvePerturbation fp hgamma4 d g hd,
    higham24_roundedDiagonalSolve_representation fp hgamma4 d g hd,
    higham24_diagonalSolvePerturbation_norm_le fp hgamma4 d g hd⟩

end NumStability
