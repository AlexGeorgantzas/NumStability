import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.Basic
import NumStability.Algorithms.LinearSystems.LeastSquares.Equality.GQR
import NumStability.Algorithms.LinearSystems.QR.HouseholderQR
import NumStability.Algorithms.LinearSystems.QR.QRSolve
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Equality.Perturbation
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter19.Core

namespace NumStability

open scoped BigOperators
open scoped BigOperators Matrix.Norms.Frobenius

/-!
# MixedStability

Canonical reusable module extracted without change from Higham20Theorem20_10, LSE.
-/

/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, exact perturbed-data
    GQR core for the same-constraint-right-hand-side branch.

    The finite-precision theorem says the computed GQR method produces
    perturbations `DeltaA`, `DeltaB`, `Deltab` for which the computed vector is
    the exact solution of the perturbed LSE problem with the original `d`.
    This theorem isolates the exact algebra behind that sentence: once such
    perturbed data satisfy the source rank conditions, exact GQR constructs the
    method factors, unique triangular coordinates, and unique minimizer for the
    perturbed problem.  It does not prove the floating-point algorithm supplies
    these perturbations or the norm bounds. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_same_d
    {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (b Deltab : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hB :
      LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (hstack :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + Deltab i
    ∃ h : GeneralizedQRFactorization r p q Apert Bpert,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = d ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer Apert bpert Bpert d
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer Apert bpert Bpert d x) := by
  dsimp
  exact
    GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      (b := fun i => b i + Deltab i) (d := d) hB hstack
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, exact perturbed-data
    GQR core for the perturbed-constraint-right-hand-side branch.

    This is the exact algebraic counterpart of the second formulation in
    Theorem 20.10, where the computed vector solves a perturbed LSE problem
    with `d + Deltad`.  The theorem reuses the constructed exact GQR method
    package for the perturbed `A` and `B`; the remaining finite-precision work
    is to derive the displayed norm bounds for `DeltaA`, `DeltaB`, `Deltab`,
    and `Deltad` from the computed GQR algorithm. -/
theorem GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
    {r p q : ℕ}
    (A DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (b Deltab : Fin (r + q) → ℝ) (d Deltad : Fin p → ℝ)
    (hB :
      LSEFullRowRank (fun i j => B i j + DeltaB i j))
    (hstack :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + Deltab i
    let dpert : Fin p → ℝ := fun i => d i + Deltad i
    ∃ h : GeneralizedQRFactorization r p q Apert Bpert,
      (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
        rectMatMulVec h.S yz.1 = dpert ∧
        rectMatMulVec h.L22 yz.2 =
          (fun i : Fin q =>
            matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
              rectMatMulVec h.L21 yz.1 i) ∧
        IsLSEMinimizer Apert bpert Bpert dpert
          (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
      (∃! x : Fin (p + q) → ℝ, IsLSEMinimizer Apert bpert Bpert dpert x) := by
  dsimp
  exact
    GeneralizedQRFactorization.exists_unique_method_solution_of_fullRowRank_stackedFullColumnRank
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      (b := fun i => b i + Deltab i)
      (d := fun i => d i + Deltad i) hB hstack
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, triangular-solve component:
    the two lower-triangular solves in the exact GQR method have concrete
    finite-precision perturbation witnesses for the actual `fl_forwardSub`
    calls.

    This is a computed-path dependency for Theorem 20.10.  It instantiates the
    already proved forward-substitution backward-error theorem on the displayed
    `S y₁ = d` and `L₂₂ y₂ = Uᵀb - L₂₁y₁` solves.  It does not yet transport
    these factor perturbations back to a final `DeltaX` bound or identify the
    computed `xhat` with the GQR output vector. -/
theorem theorem20_10_gqr_forwardSub_triangular_solve_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    let y1hat : Fin p → ℝ := fl_forwardSub fp p h.S d
    let rhs : Fin q → ℝ :=
      fun i : Fin q =>
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
          rectMatMulVec h.L21 y1hat i
    let y2hat : Fin q → ℝ := fl_forwardSub fp q h.L22 rhs
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j) y1hat = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat = rhs := by
  dsimp
  let y1hat : Fin p → ℝ := fl_forwardSub fp p h.S d
  let rhs : Fin q → ℝ :=
    fun i : Fin q =>
      matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
        rectMatMulVec h.L21 y1hat i
  let y2hat : Fin q → ℝ := fl_forwardSub fp q h.L22 rhs
  rcases forwardSub_backward_error fp p h.S d hSdiag h.lowerS hvalidS with
    ⟨DeltaS, hDeltaSbound, hSeq⟩
  rcases forwardSub_backward_error fp q h.L22 rhs hL22diag h.lowerL22
      hvalidL22 with
    ⟨DeltaL22, hDeltaL22bound, hL22eq⟩
  refine ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, ?_, ?_⟩
  · ext i
    simpa [rectMatMulVec, y1hat] using hSeq i
  · ext i
    simpa [rectMatMulVec, y2hat, rhs] using hL22eq i
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, triangular-solve component:
    Frobenius-norm version of the concrete GQR triangular-solve perturbation
    witnesses.

    The underlying forward-substitution theorem gives componentwise relative
    bounds for the two lower-triangular solves.  This wrapper converts those
    entrywise bounds into source-shaped Frobenius bounds for the perturbations
    of `S` and `L₂₂`, while preserving the exact perturbed triangular
    equations for the actual `fl_forwardSub` calls. -/
theorem theorem20_10_gqr_forwardSub_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    let y1hat : Fin p → ℝ := fl_forwardSub fp p h.S d
    let rhs : Fin q → ℝ :=
      fun i : Fin q =>
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) -
          rectMatMulVec h.L21 y1hat i
    let y2hat : Fin q → ℝ := fl_forwardSub fp q h.L22 rhs
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j) y1hat = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat = rhs := by
  dsimp
  rcases theorem20_10_gqr_forwardSub_triangular_solve_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, hSeq, hL22eq⟩
  have hDeltaSfrob :
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaS h.S (gamma_nonneg fp hvalidS) hDeltaSbound)
  have hDeltaL22frob :
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaL22 h.L22 (gamma_nonneg fp hvalidL22) hDeltaL22bound)
  exact
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    the named computed vector carries the same Frobenius-bounded triangular
    perturbation witnesses as the raw `fl_forwardSub` calls.

    This closes the bookkeeping step that identifies the local computed
    `xhat` expression used by the triangular-solve analysis.  It still does
    not prove the final `DeltaX` bound, rank preservation for perturbed source
    data, or exact-minimizer status of the computed vector. -/
theorem theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d ∧
      theorem20_10_gqr_xhat fp h b d =
        matMulVec (p + q) h.Q
          (Fin.append
            (theorem20_10_gqr_y1hat fp h d)
            (theorem20_10_gqr_y2hat fp h b d)) := by
  rcases theorem20_10_gqr_forwardSub_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_, ?_, rfl⟩
  · simpa [theorem20_10_gqr_y1hat] using hSeq
  · simpa [theorem20_10_gqr_y1hat, theorem20_10_gqr_rhs2hat,
      theorem20_10_gqr_y2hat] using hL22eq
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    triangular-solve perturbation witnesses for the supplied-trailing-RHS
    path.

    The proof is the same forward-substitution backward-error argument as for
    `theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound`, but it
    leaves the transformed trailing right-hand side as an explicit `beta`.
    This is a computed-path dependency for routing the rounded Householder RHS
    transform through the GQR certificate. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d ∧
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d ∧
      theorem20_10_gqr_xhat_of_transformed_tail fp h beta d =
        matMulVec (p + q) h.Q
          (Fin.append
            (theorem20_10_gqr_y1hat fp h d)
            (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d)) := by
  let y1hat : Fin p → ℝ := theorem20_10_gqr_y1hat fp h d
  let rhs : Fin q → ℝ :=
    theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d
  let y2hat : Fin q → ℝ :=
    theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d
  rcases forwardSub_backward_error fp p h.S d hSdiag h.lowerS hvalidS with
    ⟨DeltaS, hDeltaSbound, hSeq⟩
  rcases forwardSub_backward_error fp q h.L22 rhs hL22diag h.lowerL22
      hvalidL22 with
    ⟨DeltaL22, hDeltaL22bound, hL22eq⟩
  have hDeltaSfrob :
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaS h.S (gamma_nonneg fp hvalidS) hDeltaSbound)
  have hDeltaL22frob :
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 := by
    simpa [frobNormRect_eq_frobNormFn] using
      (frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
        DeltaL22 h.L22 (gamma_nonneg fp hvalidL22) hDeltaL22bound)
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_, ?_, rfl⟩
  · ext i
    simpa [rectMatMulVec, y1hat, theorem20_10_gqr_y1hat] using hSeq i
  · ext i
    simpa [rectMatMulVec, rhs, y2hat,
      theorem20_10_gqr_y2hat_of_transformed_tail] using hL22eq i
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    exact-minimizer handoff from supplied perturbed triangular factors.

    If a supplied perturbed GQR factorization has the same recovery `Q`, the
    same lower-left coupling block `L₂₁`, triangular blocks equal to the
    finite-precision backward-error witnesses `S + ΔS` and `L₂₂ + ΔL₂₂`, and
    the trailing transformed right-hand side agrees with the computed one, then
    the named computed vector `xhat = Q [y₁hat; y₂hat]` is an exact LSE
    minimizer for that supplied perturbed problem.  This bridge does not prove
    that such a perturbed source factorization exists; it isolates the exact
    algebra needed once the finite-precision GQR perturbation construction
    supplies those identities. -/
theorem theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i))
    (hS_inj : Function.Injective (rectMatMulVec hpert.S))
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d) :
    IsLSEMinimizer Apert bpert Bpert dpert
      (theorem20_10_gqr_xhat fp h b d) := by
  let y1hat : Fin p → ℝ := theorem20_10_gqr_y1hat fp h d
  let y2hat : Fin q → ℝ := theorem20_10_gqr_y2hat fp h b d
  have hy1 : rectMatMulVec hpert.S y1hat = dpert := by
    rw [hS, hd]
    exact hSeq
  have hy2 :
      rectMatMulVec hpert.L22 y2hat =
        fun i : Fin q =>
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
    ext i
    calc
      rectMatMulVec hpert.L22 y2hat i
          = rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat i := by
              rw [hL22]
      _ = theorem20_10_gqr_rhs2hat fp h b d i := by
              simpa [y2hat] using congrFun hL22eq i
      _ = matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
              simp [theorem20_10_gqr_rhs2hat, y1hat, hL21, hb_tail i]
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (matMulVec (p + q) hpert.Q (Fin.append y1hat y2hat)) :=
    hpert.isLSEMinimizer_of_triangular_solve hS_inj hy1 hy2
  simpa [theorem20_10_gqr_xhat, y1hat, y2hat, hQ] using hmin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    exact-minimizer handoff for the supplied-trailing-RHS path.

    This is the rounded-RHS analogue of
    `theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors`.
    The transformed trailing right-hand side is supplied as `beta`, so the
    perturbed-factor matching hypothesis asks for `Uᵀ(b + Δb)` to equal `beta`
    on the trailing block instead of the exact source vector `Uᵀ b`. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_isLSEMinimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        beta i)
    (hS_inj : Function.Injective (rectMatMulVec hpert.S))
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d) :
    IsLSEMinimizer Apert bpert Bpert dpert
      (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d) := by
  let y1hat : Fin p → ℝ := theorem20_10_gqr_y1hat fp h d
  let y2hat : Fin q → ℝ :=
    theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d
  have hy1 : rectMatMulVec hpert.S y1hat = dpert := by
    rw [hS, hd]
    exact hSeq
  have hy2 :
      rectMatMulVec hpert.L22 y2hat =
        fun i : Fin q =>
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
    ext i
    calc
      rectMatMulVec hpert.L22 y2hat i
          = rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j) y2hat i := by
              rw [hL22]
      _ = theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d i := by
              simpa [y2hat] using congrFun hL22eq i
      _ = matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
            rectMatMulVec hpert.L21 y1hat i := by
              simp [theorem20_10_gqr_rhs2hat_of_transformed_tail, y1hat,
                hL21, hb_tail i]
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (matMulVec (p + q) hpert.Q (Fin.append y1hat y2hat)) :=
    hpert.isLSEMinimizer_of_triangular_solve hS_inj hy1 hy2
  simpa [theorem20_10_gqr_xhat_of_transformed_tail, y1hat, y2hat, hQ]
    using hmin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    supplied-trailing-RHS rank and minimizer handoff.

    Nonzero diagonals of the supplied perturbed triangular blocks give the
    perturbed rank assumptions, while the transformed-tail minimizer handoff
    identifies the supplied-trailing-RHS computed vector as an exact minimizer
    of that perturbed problem. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_rank_and_minimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        beta i)
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d) :
    LSEFullRowRank Bpert ∧
      LSEStackedFullColumnRank Apert Bpert ∧
        IsLSEMinimizer Apert bpert Bpert dpert
          (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d) := by
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  have hS_inj : Function.Injective (rectMatMulVec hpert.S) :=
    (hpert.s_bijective_of_diag_ne_zero hSdiag_pert).1
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d) :=
    theorem20_10_gqr_xhat_of_transformed_tail_isLSEMinimizer_of_supplied_perturbed_triangular_factors
      fp h hpert beta d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hS_inj hSeq hL22eq
  exact ⟨hrank.1, hrank.2, hmin⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), computed GQR method:
    zero forward-error witness for the supplied-trailing-RHS path.

    Once the supplied-trailing-RHS computed vector is known to be the unique
    exact minimizer of the perturbed problem, any exact minimizer `x` equals it,
    so the mixed-stability `DeltaX` witness may again be chosen as zero. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (gammaB : ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        beta i)
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat_of_transformed_tail fp h beta d) =
          theorem20_10_gqr_rhs2hat_of_transformed_tail fp h beta d)
    (hgammaB_nonneg : 0 ≤ gammaB)
    {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer Apert bpert Bpert dpert x) :
    ∃ DeltaX : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat_of_transformed_tail fp h beta d j =
          x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x := by
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert beta d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq with
    ⟨_hBpert, hstack, hxhat_min⟩
  have hx_eq :
      x = theorem20_10_gqr_xhat_of_transformed_tail fp h beta d :=
    IsLSEMinimizer.eq_of_lseStackedFullColumnRank hstack hx hxhat_min
  refine ⟨(fun _ : Fin (p + q) => 0), ?_, ?_⟩
  · intro j
    simp [hx_eq]
  · rw [vecNorm2_zero]
    exact mul_nonneg hgammaB_nonneg (vecNorm2_nonneg x)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    bounded triangular-solve witnesses plus exact-minimizer handoff.

    This packages the existing forward-substitution backward-error witnesses
    `ΔS` and `ΔL₂₂`, their componentwise and Frobenius bounds, and the exact
    minimizer bridge for any supplied perturbed GQR factorization whose
    triangular blocks match those witnesses.  It advances the computed-vector
    side of Theorem 20.10 while leaving the genuine remaining obligations
    explicit: constructing matching perturbed source factors, proving
    perturbed rank/nonsingularity, and sharpening the printed RHS coefficient. -/
theorem theorem20_10_gqr_xhat_supplied_perturbed_factor_minimizer_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        Function.Injective (rectMatMulVec hpert.S) →
        IsLSEMinimizer Apert bpert Bpert dpert
          (theorem20_10_gqr_xhat fp h b d)) := by
  rcases theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert hQ hS hL21 hL22 hd hb_tail hS_inj
  exact
    theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hS_inj hSeq hL22eq
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    supplied perturbed-factor rank and minimizer handoff.

    Nonzero diagonals of the supplied perturbed triangular blocks `S` and
    `L₂₂` imply the perturbed source rank assumptions, and the same hypotheses
    used by `theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors`
    identify the named computed `xhat` as an exact minimizer for that perturbed
    problem.  This does not prove that finite-precision perturbations preserve
    the diagonals; it isolates the exact GQR algebra once those perturbed
    blocks have been supplied. -/
theorem theorem20_10_gqr_xhat_rank_and_minimizer_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i))
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d) :
    LSEFullRowRank Bpert ∧
      LSEStackedFullColumnRank Apert Bpert ∧
        IsLSEMinimizer Apert bpert Bpert dpert
          (theorem20_10_gqr_xhat fp h b d) := by
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  have hS_inj : Function.Injective (rectMatMulVec hpert.S) :=
    (hpert.s_bijective_of_diag_ne_zero hSdiag_pert).1
  have hmin :
      IsLSEMinimizer Apert bpert Bpert dpert
        (theorem20_10_gqr_xhat fp h b d) :=
    theorem20_10_gqr_xhat_isLSEMinimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hS_inj hSeq hL22eq
  exact ⟨hrank.1, hrank.2, hmin⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, computed GQR method:
    bounded triangular-solve witnesses plus supplied-factor rank/minimizer
    handoff.

    This strengthens
    `theorem20_10_gqr_xhat_supplied_perturbed_factor_minimizer_certificate` by
    also returning the perturbed source rank conditions when the supplied
    perturbed triangular factors have nonzero diagonals. -/
theorem theorem20_10_gqr_xhat_supplied_perturbed_factor_rank_minimizer_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        LSEFullRowRank Bpert ∧
          LSEStackedFullColumnRank Apert Bpert ∧
            IsLSEMinimizer Apert bpert Bpert dpert
              (theorem20_10_gqr_xhat fp h b d)) := by
  rcases theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert hQ hS hL21 hL22 hd hb_tail
    hSdiag_pert hL22diag_pert
  exact
    theorem20_10_gqr_xhat_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), computed GQR method:
    zero forward-error witness from supplied perturbed factors.

    Under the supplied perturbed-factor hypotheses, the named computed `xhat`
    is the unique exact minimizer of the supplied perturbed problem.  Therefore
    for any exact minimizer `x`, the mixed-stability `DeltaX` witness may be
    chosen as zero, giving the source-shaped `||DeltaX||₂ <= gammaB ||x||₂`
    bound for every nonnegative `gammaB`. -/
theorem theorem20_10_gqr_xhat_zero_deltaX_of_supplied_perturbed_triangular_factors
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    {Apert : Fin (r + q) → Fin (p + q) → ℝ}
    {Bpert : Fin p → Fin (p + q) → ℝ}
    (hpert : GeneralizedQRFactorization r p q Apert Bpert)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
    (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ)
    (gammaB : ℝ)
    (hQ : hpert.Q = h.Q)
    (hS : hpert.S = fun i j => h.S i j + DeltaS i j)
    (hL21 : hpert.L21 = h.L21)
    (hL22 : hpert.L22 = fun i j => h.L22 i j + DeltaL22 i j)
    (hd : dpert = d)
    (hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i))
    (hSdiag_pert : ∀ i : Fin p, hpert.S i i ≠ 0)
    (hL22diag_pert : ∀ i : Fin q, hpert.L22 i i ≠ 0)
    (hSeq :
      rectMatMulVec (fun i j => h.S i j + DeltaS i j)
        (theorem20_10_gqr_y1hat fp h d) = d)
    (hL22eq :
      rectMatMulVec (fun i j => h.L22 i j + DeltaL22 i j)
        (theorem20_10_gqr_y2hat fp h b d) =
          theorem20_10_gqr_rhs2hat fp h b d)
    (hgammaB_nonneg : 0 ≤ gammaB)
    {x : Fin (p + q) → ℝ}
    (hx : IsLSEMinimizer Apert bpert Bpert dpert x) :
    ∃ DeltaX : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x := by
  rcases
    theorem20_10_gqr_xhat_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq with
    ⟨_hBpert, hstack, hxhat_min⟩
  have hx_eq :
      x = theorem20_10_gqr_xhat fp h b d :=
    IsLSEMinimizer.eq_of_lseStackedFullColumnRank hstack hx hxhat_min
  refine ⟨(fun _ : Fin (p + q) => 0), ?_, ?_⟩
  · intro j
    simp [hx_eq]
  · rw [vecNorm2_zero]
    exact mul_nonneg hgammaB_nonneg (vecNorm2_nonneg x)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), computed GQR method:
    bounded triangular-solve witnesses plus zero-`DeltaX` handoff.

    This packages the actual `fl_forwardSub` perturbation witnesses with the
    exact uniqueness argument showing that, for any supplied perturbed GQR
    factorization satisfying the matching and diagonal hypotheses, the mixed
    forward-error relation can use `DeltaX = 0`. -/
theorem theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
          (gammaB : ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        0 ≤ gammaB →
        ∀ x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x →
            ∃ DeltaX : Fin (p + q) → ℝ,
              (∀ j : Fin (p + q),
                theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
              vecNorm2 DeltaX ≤ gammaB * vecNorm2 x) := by
  rcases theorem20_10_gqr_xhat_triangular_solve_frob_perturbation_bound
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert gammaB hQ hS hL21 hL22 hd
    hb_tail hSdiag_pert hL22diag_pert hgammaB_nonneg x hx
  exact
    theorem20_10_gqr_xhat_zero_deltaX_of_supplied_perturbed_triangular_factors
      fp h hpert b d bpert dpert DeltaS DeltaL22 gammaB hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq hgammaB_nonneg hx
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, transformed-tail computed
    GQR method: bounded triangular-solve witnesses plus supplied-factor
    rank/minimizer handoff.

    This is the transformed-RHS analogue of
    `theorem20_10_gqr_xhat_supplied_perturbed_factor_rank_minimizer_certificate`.
    It packages the actual `fl_forwardSub` perturbation witnesses for a supplied
    trailing transformed vector `beta`, then exposes the exact perturbed
    rank/minimizer conclusion for any matching perturbed GQR factorization. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_supplied_perturbed_factor_rank_minimizer_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            beta i) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        LSEFullRowRank Bpert ∧
          LSEStackedFullColumnRank Apert Bpert ∧
            IsLSEMinimizer Apert bpert Bpert dpert
              (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)) := by
  rcases theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp h beta d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert hQ hS hL21 hL22 hd hb_tail
    hSdiag_pert hL22diag_pert
  exact
    theorem20_10_gqr_xhat_of_transformed_tail_rank_and_minimizer_of_supplied_perturbed_triangular_factors
      fp h hpert beta d bpert dpert DeltaS DeltaL22 hQ hS hL21 hL22 hd
      hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), transformed-tail computed
    GQR method: bounded triangular-solve witnesses plus zero-`DeltaX` handoff.

    This mirrors
    `theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate`
    for the rounded/supplied transformed-tail path.  Once a matching perturbed
    GQR factorization is supplied and its triangular blocks have nonzero
    diagonals, uniqueness of the perturbed LSE minimizer again lets the mixed
    stability witness be `DeltaX = 0`. -/
theorem theorem20_10_gqr_xhat_of_transformed_tail_supplied_perturbed_factor_zero_deltaX_certificate
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ {Apert : Fin (r + q) → Fin (p + q) → ℝ}
          {Bpert : Fin p → Fin (p + q) → ℝ}
          (hpert : GeneralizedQRFactorization r p q Apert Bpert)
          (bpert : Fin (r + q) → ℝ) (dpert : Fin p → ℝ)
          (gammaB : ℝ),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        dpert = d →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) =
            beta i) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        0 ≤ gammaB →
        ∀ x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x →
            ∃ DeltaX : Fin (p + q) → ℝ,
              (∀ j : Fin (p + q),
                theorem20_10_gqr_xhat_of_transformed_tail fp h beta d j =
                  x j + DeltaX j) ∧
              vecNorm2 DeltaX ≤ gammaB * vecNorm2 x) := by
  rcases theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp h beta d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro Apert Bpert hpert bpert dpert gammaB hQ hS hL21 hL22 hd
    hb_tail hSdiag_pert hL22diag_pert hgammaB_nonneg x hx
  exact
    theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
      fp h hpert beta d bpert dpert DeltaS DeltaL22 gammaB hQ hS hL21
      hL22 hd hb_tail hSdiag_pert hL22diag_pert hSeq hL22eq
      hgammaB_nonneg hx
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), finite-precision
    perturbation certificate for the mixed-stability branch.

    This is the part of the computed GQR proof that remains to be supplied by
    the floating-point algorithm: concrete perturbations with source-shaped
    norm bounds, perturbed rank assumptions, and a forward-error relation from
    the computed vector to any exact minimizer of the perturbed problem.  The
    exact GQR/minimizer algebra is proved separately below, so this certificate
    deliberately does not assume that the displayed perturbed LSE problem has a
    solution. -/
structure Theorem20_10PartAPerturbationCertificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (gammaA gammaB : ℝ) : Type where
  /-- Perturbation of the least-squares matrix `A`. -/
  DeltaA : Fin (r + q) → Fin (p + q) → ℝ
  /-- Perturbation of the constraint matrix `B`. -/
  DeltaB : Fin p → Fin (p + q) → ℝ
  /-- Perturbation of the least-squares right-hand side `b`. -/
  Deltab : Fin (r + q) → ℝ
  /-- The perturbed constraint matrix keeps the source full-row-rank condition. -/
  hB : LSEFullRowRank (fun i j => B i j + DeltaB i j)
  /-- The perturbed stacked matrix keeps the source uniqueness condition. -/
  hstack :
    LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)
  /-- The computed vector is close to every exact minimizer of the perturbed
      problem, with the source `gamma_np`-style coefficient `gammaB`. -/
  near_exact_solution :
    ∀ x : Fin (p + q) → ℝ,
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x →
      ∃ DeltaX : Fin (p + q) → ℝ,
        (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
        vecNorm2 DeltaX ≤ gammaB * vecNorm2 x
  /-- Source-shaped Frobenius bound for `DeltaA`. -/
  hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A
  /-- Source-shaped vector bound for `Deltab`. -/
  hDeltab : vecNorm2 Deltab ≤ gammaA * vecNorm2 b
  /-- Source-shaped Frobenius bound for `DeltaB`. -/
  hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), perturbation-budget
    composition for Part A certificates.

    This is the algebraic bridge that collapses a two-layer certificate for
    `(A + DeltaA0, B + DeltaB0, b + Deltab0)` back to an original-source
    certificate.  The final coefficients are supplied by dominance hypotheses,
    so callers can choose either printed constants or conservative intermediate
    budgets without reproving the triangle-inequality bookkeeping. -/
def theorem20_10_partA_certificate_compose_source_perturbations
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB0 : Fin p → Fin (p + q) → ℝ)
    (Deltab0 : Fin (r + q) → ℝ)
    {gammaA0 gammaB0 gammaRhs0 gammaA2 gammaB2 gammaA gammaB : ℝ}
    (hgammaA2_nonneg : 0 ≤ gammaA2)
    (hgammaB2_nonneg : 0 ≤ gammaB2)
    (hDeltaA0 :
      frobNormRect DeltaA0 ≤ gammaA0 * frobNormRect A)
    (hDeltaB0 :
      frobNormRect DeltaB0 ≤ gammaB0 * frobNormRect B)
    (hDeltab0 :
      vecNorm2 Deltab0 ≤ gammaRhs0 * vecNorm2 b)
    (hgammaA_matrix :
      gammaA0 + gammaA2 * (1 + gammaA0) ≤ gammaA)
    (hgammaA_rhs :
      gammaRhs0 + gammaA2 * (1 + gammaRhs0) ≤ gammaA)
    (hgammaB_matrix :
      gammaB0 + gammaB2 * (1 + gammaB0) ≤ gammaB)
    (hgammaB_solution : gammaB2 ≤ gammaB)
    (cert :
      Theorem20_10PartAPerturbationCertificate
        (fun i j => A i j + DeltaA0 i j)
        (fun i j => B i j + DeltaB0 i j)
        (fun i => b i + Deltab0 i) d xhat gammaA2 gammaB2) :
    Theorem20_10PartAPerturbationCertificate A B b d xhat
      gammaA gammaB := by
  let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => DeltaA0 i j + cert.DeltaA i j
  let DeltaB : Fin p → Fin (p + q) → ℝ :=
    fun i j => DeltaB0 i j + cert.DeltaB i j
  let Deltab : Fin (r + q) → ℝ :=
    fun i => Deltab0 i + cert.Deltab i
  have hApert_norm :
      frobNormRect (fun i j => A i j + DeltaA0 i j) ≤
        (1 + gammaA0) * frobNormRect A := by
    calc
      frobNormRect (fun i j => A i j + DeltaA0 i j)
          ≤ frobNormRect A + frobNormRect DeltaA0 :=
            frobNormRect_add_le A DeltaA0
      _ ≤ frobNormRect A + gammaA0 * frobNormRect A :=
            add_le_add_right hDeltaA0 (frobNormRect A)
      _ = (1 + gammaA0) * frobNormRect A := by ring
  have hBpert_norm :
      frobNormRect (fun i j => B i j + DeltaB0 i j) ≤
        (1 + gammaB0) * frobNormRect B := by
    calc
      frobNormRect (fun i j => B i j + DeltaB0 i j)
          ≤ frobNormRect B + frobNormRect DeltaB0 :=
            frobNormRect_add_le B DeltaB0
      _ ≤ frobNormRect B + gammaB0 * frobNormRect B :=
            add_le_add_right hDeltaB0 (frobNormRect B)
      _ = (1 + gammaB0) * frobNormRect B := by ring
  have hbpert_norm :
      vecNorm2 (fun i => b i + Deltab0 i) ≤
        (1 + gammaRhs0) * vecNorm2 b := by
    calc
      vecNorm2 (fun i => b i + Deltab0 i)
          ≤ vecNorm2 b + vecNorm2 Deltab0 :=
            vecNorm2_add_le b Deltab0
      _ ≤ vecNorm2 b + gammaRhs0 * vecNorm2 b :=
            add_le_add_right hDeltab0 (vecNorm2 b)
      _ = (1 + gammaRhs0) * vecNorm2 b := by ring
  have hDeltaA :
      frobNormRect DeltaA ≤ gammaA * frobNormRect A := by
    have hsecond :
        frobNormRect cert.DeltaA ≤
          gammaA2 * ((1 + gammaA0) * frobNormRect A) := by
      exact le_trans cert.hDeltaA
        (mul_le_mul_of_nonneg_left hApert_norm hgammaA2_nonneg)
    have hpre :
        frobNormRect DeltaA ≤
          (gammaA0 + gammaA2 * (1 + gammaA0)) * frobNormRect A := by
      calc
        frobNormRect DeltaA
            ≤ frobNormRect DeltaA0 + frobNormRect cert.DeltaA := by
              simpa [DeltaA] using frobNormRect_add_le DeltaA0 cert.DeltaA
        _ ≤ gammaA0 * frobNormRect A +
              gammaA2 * ((1 + gammaA0) * frobNormRect A) :=
              add_le_add hDeltaA0 hsecond
        _ = (gammaA0 + gammaA2 * (1 + gammaA0)) * frobNormRect A := by
              ring
    exact le_trans hpre
      (mul_le_mul_of_nonneg_right hgammaA_matrix (frobNormRect_nonneg A))
  have hDeltaB :
      frobNormRect DeltaB ≤ gammaB * frobNormRect B := by
    have hsecond :
        frobNormRect cert.DeltaB ≤
          gammaB2 * ((1 + gammaB0) * frobNormRect B) := by
      exact le_trans cert.hDeltaB
        (mul_le_mul_of_nonneg_left hBpert_norm hgammaB2_nonneg)
    have hpre :
        frobNormRect DeltaB ≤
          (gammaB0 + gammaB2 * (1 + gammaB0)) * frobNormRect B := by
      calc
        frobNormRect DeltaB
            ≤ frobNormRect DeltaB0 + frobNormRect cert.DeltaB := by
              simpa [DeltaB] using frobNormRect_add_le DeltaB0 cert.DeltaB
        _ ≤ gammaB0 * frobNormRect B +
              gammaB2 * ((1 + gammaB0) * frobNormRect B) :=
              add_le_add hDeltaB0 hsecond
        _ = (gammaB0 + gammaB2 * (1 + gammaB0)) * frobNormRect B := by
              ring
    exact le_trans hpre
      (mul_le_mul_of_nonneg_right hgammaB_matrix (frobNormRect_nonneg B))
  have hDeltab :
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b := by
    have hsecond :
        vecNorm2 cert.Deltab ≤
          gammaA2 * ((1 + gammaRhs0) * vecNorm2 b) := by
      exact le_trans cert.hDeltab
        (mul_le_mul_of_nonneg_left hbpert_norm hgammaA2_nonneg)
    have hpre :
        vecNorm2 Deltab ≤
          (gammaRhs0 + gammaA2 * (1 + gammaRhs0)) * vecNorm2 b := by
      calc
        vecNorm2 Deltab
            ≤ vecNorm2 Deltab0 + vecNorm2 cert.Deltab := by
              simpa [Deltab] using vecNorm2_add_le Deltab0 cert.Deltab
        _ ≤ gammaRhs0 * vecNorm2 b +
              gammaA2 * ((1 + gammaRhs0) * vecNorm2 b) :=
              add_le_add hDeltab0 hsecond
        _ = (gammaRhs0 + gammaA2 * (1 + gammaRhs0)) * vecNorm2 b := by
              ring
    exact le_trans hpre
      (mul_le_mul_of_nonneg_right hgammaA_rhs (vecNorm2_nonneg b))
  have hBcert :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) := by
    simpa [DeltaB, add_assoc] using cert.hB
  have hstackcert :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) := by
    simpa [DeltaA, DeltaB, add_assoc] using cert.hstack
  exact
    { DeltaA := DeltaA
      DeltaB := DeltaB
      Deltab := Deltab
      hB := hBcert
      hstack := hstackcert
      near_exact_solution := by
        intro x hx
        have hx' :
            IsLSEMinimizer
              (fun i j => (A i j + DeltaA0 i j) + cert.DeltaA i j)
              (fun i => (b i + Deltab0 i) + cert.Deltab i)
              (fun i j => (B i j + DeltaB0 i j) + cert.DeltaB i j)
              d x := by
          simpa [DeltaA, DeltaB, Deltab, add_assoc] using hx
        rcases cert.near_exact_solution x hx' with
          ⟨DeltaX, hDeltaX, hDeltaXnorm⟩
        refine ⟨DeltaX, hDeltaX, ?_⟩
        exact le_trans hDeltaXnorm
          (mul_le_mul_of_nonneg_right hgammaB_solution (vecNorm2_nonneg x))
      hDeltaA := hDeltaA
      hDeltab := hDeltab
      hDeltaB := hDeltaB }
/-- Nonempty wrapper for
    `theorem20_10_partA_certificate_compose_source_perturbations`. -/
theorem theorem20_10_nonempty_partA_certificate_compose_source_perturbations
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB0 : Fin p → Fin (p + q) → ℝ)
    (Deltab0 : Fin (r + q) → ℝ)
    {gammaA0 gammaB0 gammaRhs0 gammaA2 gammaB2 gammaA gammaB : ℝ}
    (hgammaA2_nonneg : 0 ≤ gammaA2)
    (hgammaB2_nonneg : 0 ≤ gammaB2)
    (hDeltaA0 :
      frobNormRect DeltaA0 ≤ gammaA0 * frobNormRect A)
    (hDeltaB0 :
      frobNormRect DeltaB0 ≤ gammaB0 * frobNormRect B)
    (hDeltab0 :
      vecNorm2 Deltab0 ≤ gammaRhs0 * vecNorm2 b)
    (hgammaA_matrix :
      gammaA0 + gammaA2 * (1 + gammaA0) ≤ gammaA)
    (hgammaA_rhs :
      gammaRhs0 + gammaA2 * (1 + gammaRhs0) ≤ gammaA)
    (hgammaB_matrix :
      gammaB0 + gammaB2 * (1 + gammaB0) ≤ gammaB)
    (hgammaB_solution : gammaB2 ≤ gammaB)
    (hcert :
      Nonempty
        (Theorem20_10PartAPerturbationCertificate
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j)
          (fun i => b i + Deltab0 i) d xhat gammaA2 gammaB2)) :
    Nonempty
      (Theorem20_10PartAPerturbationCertificate A B b d xhat
        gammaA gammaB) := by
  rcases hcert with ⟨cert⟩
  exact
    ⟨theorem20_10_partA_certificate_compose_source_perturbations
      A B b d xhat DeltaA0 DeltaB0 Deltab0
      hgammaA2_nonneg hgammaB2_nonneg
      hDeltaA0 hDeltaB0 hDeltab0
      hgammaA_matrix hgammaA_rhs hgammaB_matrix hgammaB_solution cert⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), supplied-factor
    constructor for the mixed-stability perturbation certificate with a
    supplied transformed trailing right-hand side.

    This is the certificate-level bridge for the rounded Householder RHS route.
    The vector `beta` represents the computed trailing transformed RHS; callers
    must prove that the perturbed source RHS satisfies
    `Uᵀ(b + Deltab) = beta` on the trailing block.  The theorem therefore
    avoids assuming the exact transformed RHS while also not claiming the
    printed `Deltab` coefficient. -/
theorem theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX_of_transformed_tail
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB : Fin p → Fin (p + q) → ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A)
    (hDeltab : vecNorm2 Deltab ≤ gammaA * vecNorm2 b)
    (hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ (hpert :
          GeneralizedQRFactorization r p q
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j)),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            beta i) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        Nonempty
          (Theorem20_10PartAPerturbationCertificate A B b d
            (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)
            gammaA gammaB)) := by
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp h beta d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro hpert hQ hS hL21 hL22 hb_tail hSdiag_pert hL22diag_pert
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  exact
    ⟨{ DeltaA := DeltaA
       DeltaB := DeltaB
       Deltab := Deltab
       hB := hrank.1
       hstack := hrank.2
       near_exact_solution := by
         intro x hx
         exact
           theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
             fp h hpert beta d (fun i => b i + Deltab i) d DeltaS DeltaL22
             gammaB hQ hS hL21 hL22 rfl hb_tail hSdiag_pert hL22diag_pert
             hSeq hL22eq hgammaB_nonneg hx
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    transformed-tail version of the supplied-factor Part A certificate.

    This removes the external `hpert` input from
    `theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX_of_transformed_tail`.
    It is the algebraic bridge needed by the rounded RHS path: the trailing
    transformed vector is an explicit `beta`, and the remaining RHS obligation
    is the honest equality `Uᵀ(b + Deltab) = beta` on the trailing block. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_transformed_tail
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       IsLowerTriangular Spert →
       IsLowerTriangular L22pert →
       (∀ i : Fin p, Spert i i ≠ 0) →
       (∀ i : Fin q, L22pert i i ≠ 0) →
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            beta i) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)
          gammaA gammaB)) := by
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp h beta d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeq, hL22eq, _hxhat⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp
  intro hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
    hDeltaA hDeltab hDeltaB hb_tail
  let Spert : Fin p → Fin p → ℝ := fun i j => h.S i j + DeltaS i j
  let L22pert : Fin q → Fin q → ℝ := fun i j => h.L22 i j + DeltaL22 i j
  let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
  let Bpert : Fin p → Fin (p + q) → ℝ :=
    gqrSourceBFromBlocks h.Q Spert
  let DeltaA_src : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => Apert i j - A i j
  let DeltaB_src : Fin p → Fin (p + q) → ℝ :=
    fun i j => Bpert i j - B i j
  let hpert : GeneralizedQRFactorization r p q Apert Bpert :=
    GeneralizedQRFactorization.of_source_blocks
      h.Q h.U h.L11 h.L21 L22pert Spert
      h.orthQ h.orthU hL22pert_lower hSpert_lower
  have hApert_src :
      (fun i j => A i j + DeltaA_src i j) = Apert := by
    ext i j
    dsimp [DeltaA_src]
    ring
  have hBpert_src :
      (fun i j => B i j + DeltaB_src i j) = Bpert := by
    ext i j
    dsimp [DeltaB_src]
    ring
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨fun i => by simpa [hpert, Spert] using hSpert_diag i,
       fun i => by simpa [hpert, L22pert] using hL22pert_diag i⟩
  have hBcert :
      LSEFullRowRank (fun i j => B i j + DeltaB_src i j) := by
    rw [hBpert_src]
    exact hrank.1
  have hstackcert :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA_src i j)
        (fun i j => B i j + DeltaB_src i j) := by
    rw [hApert_src, hBpert_src]
    exact hrank.2
  exact
    ⟨{ DeltaA := DeltaA_src
       DeltaB := DeltaB_src
       Deltab := Deltab
       hB := hBcert
       hstack := hstackcert
       near_exact_solution := by
         intro x hx
         have hx' : IsLSEMinimizer Apert
             (fun i => b i + Deltab i) Bpert d x := by
           rw [hApert_src, hBpert_src] at hx
           exact hx
         exact
           theorem20_10_gqr_xhat_of_transformed_tail_zero_deltaX_of_supplied_perturbed_triangular_factors
             fp h hpert beta d (fun i => b i + Deltab i) d DeltaS DeltaL22
             gammaB rfl rfl rfl rfl rfl hb_tail
             (fun i => by simpa [hpert, Spert] using hSpert_diag i)
             (fun i => by simpa [hpert, L22pert] using hL22pert_diag i)
             hSeq hL22eq hgammaB_nonneg hx'
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), transformed-tail
    constructed-source certificate with triangular preservation and the induced
    source `DeltaA`/`DeltaB` bounds discharged.

    This is the rounded-RHS counterpart of
    `theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds`.
    The only remaining RHS-specific obligations are the source-shaped bound for
    `Deltab` and the transformed-tail equality
    `Uᵀ(b + Deltab) = beta`. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (beta : Fin q → ℝ) (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            beta i) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat_of_transformed_tail fp h beta d)
          gammaA gammaB)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_transformed_tail
      fp h beta b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      (gammaValid_mono fp (by omega) hvalid2S)
      (gammaValid_mono fp (by omega) hvalid2L22) with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp at hcert ⊢
  intro hDeltab hb_tail
  have hSpert_lower :
      IsLowerTriangular (fun i j => h.S i j + DeltaS i j) :=
    h.lowerS.add_of_entrywise_abs_le_mul_abs hDeltaSbound
  have hL22pert_lower :
      IsLowerTriangular (fun i j => h.L22 i j + DeltaL22 i j) :=
    h.lowerL22.add_of_entrywise_abs_le_mul_abs hDeltaL22bound
  have hSpert_diag :
      ∀ i : Fin p, h.S i i + DeltaS i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hSdiag (gamma_lt_one fp p hvalid2S) hDeltaSbound
  have hL22pert_diag :
      ∀ i : Fin q, h.L22 i i + DeltaL22 i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hL22diag (gamma_lt_one fp q hvalid2L22) hDeltaL22bound
  have hgammaq_nonneg : 0 ≤ gamma fp q :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid2L22)
  have hDeltaA_base :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gamma fp q * frobNormRect A :=
    h.constructed_sourceA_L22_perturbation_frobNorm_bound
      (gamma fp q) DeltaL22 hgammaq_nonneg hDeltaL22frob
  have hDeltaA :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gammaA * frobNormRect A := by
    exact le_trans hDeltaA_base
      (mul_le_mul_of_nonneg_right hgammaA_ge (frobNormRect_nonneg A))
  have hDeltaB_base :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gamma fp p * frobNormRect B :=
    h.constructed_sourceB_perturbation_frobNorm_bound
      (gamma fp p) DeltaS hDeltaSfrob
  have hDeltaB :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gammaB * frobNormRect B := by
    exact le_trans hDeltaB_base
      (mul_le_mul_of_nonneg_right hgammaB_ge (frobNormRect_nonneg B))
  exact
    hcert hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
      hDeltaA hDeltab hDeltaB hb_tail
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), supplied-factor
    constructor for the mixed-stability perturbation certificate.

    This is the certificate-level handoff for the currently verified supplied
    perturbed-factor boundary.  If separate work supplies source perturbations
    `DeltaA`, `DeltaB`, and `Deltab` with the required norm bounds and a
    perturbed GQR factorization whose displayed triangular blocks match the
    forward-substitution perturbation witnesses, then the named computed GQR
    vector has a full `Theorem20_10PartAPerturbationCertificate`.  The theorem
    deliberately leaves the matching-factor construction as an explicit
    hypothesis rather than claiming the floating-point GQR algorithm already
    supplies it. -/
theorem theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB : Fin p → Fin (p + q) → ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A)
    (hDeltab : vecNorm2 Deltab ≤ gammaA * vecNorm2 b)
    (hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (∀ (hpert :
          GeneralizedQRFactorization r p q
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j)),
        hpert.Q = h.Q →
        hpert.S = (fun i j => h.S i j + DeltaS i j) →
        hpert.L21 = h.L21 →
        hpert.L22 = (fun i j => h.L22 i j + DeltaL22 i j) →
        (∀ i : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
        (∀ i : Fin p, hpert.S i i ≠ 0) →
        (∀ i : Fin q, hpert.L22 i i ≠ 0) →
        Nonempty
          (Theorem20_10PartAPerturbationCertificate A B b d
            (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hzero⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  intro hpert hQ hS hL21 hL22 hb_tail hSdiag_pert hL22diag_pert
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag_pert, hL22diag_pert⟩
  exact
    ⟨{ DeltaA := DeltaA
       DeltaB := DeltaB
       Deltab := Deltab
       hB := hrank.1
       hstack := hrank.2
       near_exact_solution := by
         intro x hx
         exact
           hzero hpert (fun i => b i + Deltab i) d gammaB
             hQ hS hL21 hL22 rfl hb_tail hSdiag_pert hL22diag_pert
             hgammaB_nonneg x hx
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    version of the supplied-factor Part A certificate.

    This removes the external `hpert` input from
    `theorem20_10_partA_certificate_of_supplied_perturbed_factor_zero_deltaX`.
    The perturbed source matrices are constructed directly by transporting the
    perturbed triangular blocks `S + DeltaS` and `L22 + DeltaL22` back through
    the original orthogonal factors.  The remaining hypotheses are exactly the
    ones not proved by this algebraic construction: lower-triangularity of the
    perturbed blocks, source-shaped bounds for the induced source
    perturbations, and the transformed right-hand-side matching condition. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       IsLowerTriangular Spert →
       IsLowerTriangular L22pert →
       (∀ i : Fin p, Spert i i ≠ 0) →
       (∀ i : Fin q, L22pert i i ≠ 0) →
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases theorem20_10_gqr_xhat_supplied_perturbed_factor_zero_deltaX_certificate
      fp h b d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hzero⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp
  intro hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
    hDeltaA hDeltab hDeltaB hb_tail
  let Spert : Fin p → Fin p → ℝ := fun i j => h.S i j + DeltaS i j
  let L22pert : Fin q → Fin q → ℝ := fun i j => h.L22 i j + DeltaL22 i j
  let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
  let Bpert : Fin p → Fin (p + q) → ℝ :=
    gqrSourceBFromBlocks h.Q Spert
  let DeltaA_src : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => Apert i j - A i j
  let DeltaB_src : Fin p → Fin (p + q) → ℝ :=
    fun i j => Bpert i j - B i j
  let hpert : GeneralizedQRFactorization r p q Apert Bpert :=
    GeneralizedQRFactorization.of_source_blocks
      h.Q h.U h.L11 h.L21 L22pert Spert
      h.orthQ h.orthU hL22pert_lower hSpert_lower
  have hApert_src :
      (fun i j => A i j + DeltaA_src i j) = Apert := by
    ext i j
    dsimp [DeltaA_src]
    ring
  have hBpert_src :
      (fun i j => B i j + DeltaB_src i j) = Bpert := by
    ext i j
    dsimp [DeltaB_src]
    ring
  have hrank :
      LSEFullRowRank Bpert ∧ LSEStackedFullColumnRank Apert Bpert :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨fun i => by simpa [hpert, Spert] using hSpert_diag i,
       fun i => by simpa [hpert, L22pert] using hL22pert_diag i⟩
  have hBcert :
      LSEFullRowRank (fun i j => B i j + DeltaB_src i j) := by
    rw [hBpert_src]
    exact hrank.1
  have hstackcert :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA_src i j)
        (fun i j => B i j + DeltaB_src i j) := by
    rw [hApert_src, hBpert_src]
    exact hrank.2
  exact
    ⟨{ DeltaA := DeltaA_src
       DeltaB := DeltaB_src
       Deltab := Deltab
       hB := hBcert
       hstack := hstackcert
       near_exact_solution := by
         intro x hx
         have hx' : IsLSEMinimizer Apert
             (fun i => b i + Deltab i) Bpert d x := by
           rw [hApert_src, hBpert_src] at hx
           exact hx
         exact
           hzero hpert (fun i => b i + Deltab i) d gammaB
             rfl rfl rfl rfl rfl hb_tail
             (fun i => by simpa [hpert, Spert] using hSpert_diag i)
             (fun i => by simpa [hpert, L22pert] using hL22pert_diag i)
             hgammaB_nonneg x hx'
       hDeltaA := hDeltaA
       hDeltab := hDeltab
       hDeltaB := hDeltaB }⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    certificate with perturbed triangular nonsingularity discharged by
    `gamma < 1`.

    The forward-substitution perturbation bounds are relative entrywise bounds.
    Therefore the perturbed `S + DeltaS` and `L22 + DeltaL22` blocks remain
    lower triangular; if the relative factors are strictly below one, their
    nonzero diagonals are preserved.  This theorem removes those hypotheses
    from `theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks`,
    leaving only the induced source perturbation bounds and transformed-RHS
    matching condition. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_gamma_lt_one
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidS : gammaValid fp p)
    (hvalidL22 : gammaValid fp q)
    (hgammaS_lt : gamma fp p < 1)
    (hgammaL22_lt : gamma fp q < 1) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks
      fp h b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp at hcert ⊢
  intro hDeltaA hDeltab hDeltaB hb_tail
  have hSpert_lower :
      IsLowerTriangular (fun i j => h.S i j + DeltaS i j) :=
    h.lowerS.add_of_entrywise_abs_le_mul_abs hDeltaSbound
  have hL22pert_lower :
      IsLowerTriangular (fun i j => h.L22 i j + DeltaL22 i j) :=
    h.lowerL22.add_of_entrywise_abs_le_mul_abs hDeltaL22bound
  have hSpert_diag :
      ∀ i : Fin p, h.S i i + DeltaS i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hSdiag hgammaS_lt hDeltaSbound
  have hL22pert_diag :
      ∀ i : Fin q, h.L22 i i + DeltaL22 i i ≠ 0 :=
    diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hL22diag hgammaL22_lt hDeltaL22bound
  exact
    hcert hSpert_lower hL22pert_lower hSpert_diag hL22pert_diag
      hDeltaA hDeltab hDeltaB hb_tail
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    certificate with the `gamma < 1` triangular preservation guards derived
    from doubled `gammaValid` hypotheses.

    This is the same certificate surface as
    `theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_gamma_lt_one`,
    but exposes the standard floating-point smallness assumptions
    `gammaValid fp (2*p)` and `gammaValid fp (2*q)` instead of explicit
    inequalities on `gamma`. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (let Spert : Fin p → Fin p → ℝ :=
          fun i j => h.S i j + DeltaS i j
       let L22pert : Fin q → Fin q → ℝ :=
          fun i j => h.L22 i j + DeltaL22 i j
       let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21 L22pert
       let Bpert : Fin p → Fin (p + q) → ℝ :=
          gqrSourceBFromBlocks h.Q Spert
       let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
          fun i j => Apert i j - A i j
       let DeltaB : Fin p → Fin (p + q) → ℝ :=
          fun i j => Bpert i j - B i j
       frobNormRect DeltaA ≤ gammaA * frobNormRect A →
       vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       frobNormRect DeltaB ≤ gammaB * frobNormRect B →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  exact
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_gamma_lt_one
      fp h b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      (gammaValid_mono fp (by omega) hvalid2S)
      (gammaValid_mono fp (by omega) hvalid2L22)
      (gamma_lt_one fp p hvalid2S)
      (gamma_lt_one fp q hvalid2L22)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), constructed-source
    certificate with the induced source `DeltaA` and `DeltaB` Frobenius bounds
    discharged from the triangular-solve perturbation bounds.

    The remaining visible finite-precision obligations are the source-shaped
    right-hand-side perturbation bound for `Deltab` and the transformed trailing
    right-hand-side matching condition.  The matrix perturbation bounds are
    proved internally using the transported `L22` and `S` perturbations. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      (vecNorm2 Deltab ≤ gammaA * vecNorm2 b →
       (∀ i : Fin q,
          matMulVec (r + q) (matTranspose h.U)
              (fun i => b i + Deltab i) (Fin.natAdd r i) =
            matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i)) →
       Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid
      fp h b d gammaA gammaB Deltab hgammaB_nonneg hSdiag hL22diag
      hvalid2S hvalid2L22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  dsimp at hcert ⊢
  intro hDeltab hb_tail
  have hgammaq_nonneg : 0 ≤ gamma fp q :=
    gamma_nonneg fp (gammaValid_mono fp (by omega) hvalid2L22)
  have hDeltaA_base :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gamma fp q * frobNormRect A :=
    h.constructed_sourceA_L22_perturbation_frobNorm_bound
      (gamma fp q) DeltaL22 hgammaq_nonneg hDeltaL22frob
  have hDeltaA :
      frobNormRect
        (fun i j =>
          gqrSourceAFromBlocks h.Q h.U h.L11 h.L21
              (fun i j => h.L22 i j + DeltaL22 i j) i j -
            A i j) ≤
        gammaA * frobNormRect A := by
    exact le_trans hDeltaA_base
      (mul_le_mul_of_nonneg_right hgammaA_ge (frobNormRect_nonneg A))
  have hDeltaB_base :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gamma fp p * frobNormRect B :=
    h.constructed_sourceB_perturbation_frobNorm_bound
      (gamma fp p) DeltaS hDeltaSfrob
  have hDeltaB :
      frobNormRect
        (fun i j =>
          gqrSourceBFromBlocks h.Q (fun i j => h.S i j + DeltaS i j) i j -
            B i j) ≤
        gammaB * frobNormRect B := by
    exact le_trans hDeltaB_base
      (mul_le_mul_of_nonneg_right hgammaB_ge (frobNormRect_nonneg B))
  exact hcert hDeltaA hDeltab hDeltaB hb_tail
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), exact transformed-RHS
    specialization of the constructed-source certificate.

    The named supplied-GQR path computes the trailing triangular right-hand side
    from the exact transformed vector `Uᵀ b`, so choosing `Deltab = 0` discharges
    both the source-shaped RHS perturbation bound and the transformed-tail
    matching condition.  This closes the exact-transform certificate branch; the
    separate rounded Householder RHS-transform bridge remains a distinct
    computed-path obligation. -/
theorem theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_exact_rhs
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hgammaA_nonneg : 0 ≤ gammaA)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d) gammaA gammaB) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds
      fp h b d gammaA gammaB (0 : Fin (r + q) → ℝ)
      hgammaB_nonneg hgammaA_ge hgammaB_ge hSdiag hL22diag
      hvalid2S hvalid2L22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  refine
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, ?_⟩
  have hDeltab0 :
      vecNorm2 (0 : Fin (r + q) → ℝ) ≤ gammaA * vecNorm2 b := by
    change vecNorm2 (fun _ : Fin (r + q) => 0) ≤ gammaA * vecNorm2 b
    rw [vecNorm2_zero]
    exact mul_nonneg hgammaA_nonneg (vecNorm2_nonneg b)
  have hb_tail0 : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose h.U)
          (fun i => b i + (0 : Fin (r + q) → ℝ) i) (Fin.natAdd r i) =
        matMulVec (r + q) (matTranspose h.U) b (Fin.natAdd r i) := by
    intro i
    simp
  exact hcert hDeltab0 hb_tail0
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), certificate-to-exact-core
    handoff.

    A verified finite-precision GQR perturbation certificate yields an exact
    perturbed LSE minimizer, exact GQR method coordinates for that perturbed
    problem, the mixed forward-error relation for the computed vector, and the
    displayed perturbation bounds.  The only remaining work for the full
    theorem is to prove the certificate from the concrete computed GQR path and
    to instantiate the source `gamma_tilde` coefficients. -/
theorem theorem20_10_partA_mixed_stability_of_perturbation_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat gammaA gammaB) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer Apert bpert Bpert d x ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = d ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert d
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert d x0)) := by
  dsimp
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_same_d
      A cert.DeltaA B cert.DeltaB b cert.Deltab d cert.hB cert.hstack with
    ⟨h, hyz, hxuniq⟩
  rcases hxuniq with ⟨x, hx, huniq⟩
  rcases cert.near_exact_solution x hx with ⟨DeltaX, hxhat, hDeltaX⟩
  refine ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x, rfl, rfl, rfl,
    hxhat, hDeltaX, cert.hDeltaA, cert.hDeltab, cert.hDeltaB, hx, ?_⟩
  exact ⟨h, hyz, ⟨x, hx, huniq⟩⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), exact transformed-RHS
    mixed-stability theorem for the constructed-source supplied-GQR path.

    This combines the constructed-source exact-RHS certificate with the generic
    certificate-to-core handoff.  The conclusion exposes the perturbations and
    exact perturbed minimizer directly, without requiring callers to unpack the
    intermediate certificate. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hgammaA_nonneg : 0 ≤ gammaA)
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge : gamma fp q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_exact_rhs
      fp h b d gammaA gammaB hgammaA_nonneg hgammaB_nonneg
      hgammaA_ge hgammaB_ge hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨_DeltaS, _DeltaL22, _hDeltaSbound, _hDeltaL22bound,
      _hDeltaSfrob, _hDeltaL22frob, hcert⟩
  rcases hcert with ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d (theorem20_10_gqr_xhat fp h b d) cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x,
      hDeltaAeq, hDeltaBeq, hDeltabeq, hxhat, hDeltaX,
      hDeltaA, hDeltab, hDeltaB, hx, hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x,
      hxhat, hDeltaX, ?_, ?_, ?_, hx, hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltaBeq] using hDeltaB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), finite-precision
    perturbation certificate for the fully backward-stable branch.

    The certificate records the perturbations and the displayed norm bounds
    for the perturbed problem with right-hand side `d + Deltad`.  It does not
    assume that the computed vector is the minimizer; the theorem below proves
    the exact perturbed GQR/minimizer core, leaving the computed-vector
    identification as the remaining algorithmic obligation. -/
structure Theorem20_10PartBPerturbationCertificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (gammaA gammaB : ℝ) : Type where
  /-- Perturbation of the least-squares matrix `A`. -/
  DeltaA : Fin (r + q) → Fin (p + q) → ℝ
  /-- Perturbation of the constraint matrix `B`. -/
  DeltaB : Fin p → Fin (p + q) → ℝ
  /-- Perturbation of the least-squares right-hand side `b`. -/
  Deltab : Fin (r + q) → ℝ
  /-- Perturbation of the constraint right-hand side `d`. -/
  Deltad : Fin p → ℝ
  /-- The perturbed constraint matrix keeps the source full-row-rank condition. -/
  hB : LSEFullRowRank (fun i j => B i j + DeltaB i j)
  /-- The perturbed stacked matrix keeps the source uniqueness condition. -/
  hstack :
    LSEStackedFullColumnRank
      (fun i j => A i j + DeltaA i j)
      (fun i j => B i j + DeltaB i j)
  /-- Source-shaped Frobenius bound for `DeltaA`. -/
  hDeltaA : frobNormRect DeltaA ≤ gammaA * frobNormRect A
  /-- Source-shaped Frobenius bound for `DeltaB`. -/
  hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B
  /-- Source-shaped right-hand-side perturbation bound for `Deltab`. -/
  hDeltab :
    vecNorm2 Deltab ≤
      gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat
  /-- Source-shaped constraint right-hand-side perturbation bound. -/
  hDeltad : vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), certificate-to-exact-core
    handoff.

    A verified finite-precision GQR perturbation certificate gives exact GQR
    method coordinates and a unique exact minimizer for the perturbed problem
    with right-hand side `d + Deltad`, together with the displayed perturbation
    bounds.  The remaining computed-algorithm theorem must prove this
    certificate and identify the actual computed vector with the unique
    minimizer. -/
theorem theorem20_10_partB_backward_error_of_perturbation_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (cert :
      Theorem20_10PartBPerturbationCertificate A B b d xhat gammaA gammaB) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    let dpert : Fin p → ℝ := fun i => d i + cert.Deltad i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      Deltad = cert.Deltad ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = dpert ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert dpert
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x)) := by
  dsimp
  rcases
    GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
      A cert.DeltaA B cert.DeltaB b cert.Deltab d cert.Deltad
      cert.hB cert.hstack with
    ⟨h, hyz, hxuniq⟩
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, cert.Deltad, rfl, rfl, rfl, rfl,
      cert.hDeltaA, cert.hDeltaB, cert.hDeltab, cert.hDeltad,
      ⟨h, hyz, hxuniq⟩⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder QR perturbation bound for the smaller `A Q₂`
    triangularization step in the GQR path.

    The block later instantiated as `A Q₂` has dimensions `(r+q) × q`, so the
    Chapter 19 Householder QR theorem applies without requiring the full `A`
    matrix to be tall.  The resulting `gamma_tilde_(r+q),q` bound is absorbed
    into the source-facing `gamma_tilde_(r+q),(p+q)` coefficient by gamma
    monotonicity.  This is a computed-path dependency only; it does not yet
    transport the perturbation back through the already computed `Q₂` factor or
    prove the triangular-solve perturbations. -/
theorem theorem20_10_householder_AQ2_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (C : Fin (r + q) → Fin q → ℝ)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    ∃ DeltaC : Fin (r + q) → Fin q → ℝ,
      (∀ i j,
        C i j + DeltaC i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q C)
            (fl_householderQRPanel_R fp (r + q) q C) i j) ∧
      frobNormRect DeltaC ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect C := by
  let K : ℕ := householderConstructApplyGammaIndex (r + q)
  have hvalid_full : gammaValid fp ((p + q) * K) := by
    simpa [K] using hvalid
  have hq_le_pq : q ≤ p + q := by omega
  have hidx_le : q * K ≤ (p + q) * K :=
    Nat.mul_le_mul_right K hq_le_pq
  have hvalid_q : gammaValid fp (q * K) :=
    gammaValid_mono fp hidx_le hvalid_full
  have hqr :
      H19.Theorem19_4.HouseholderQRBackwardError (r + q) q C
        (fl_householderQRPanel_Q fp (r + q) q C)
        (fl_householderQRPanel_R fp (r + q) q C)
        (H19.Theorem19_4.gamma_tilde fp (r + q) q) := by
    exact
      H19.Theorem19_4.householder_qr_backward_error fp (r + q) q C hq
        (by omega) hvalid_q
  have hgamma_nonneg :
      0 ≤ H19.Theorem19_4.gamma_tilde fp (r + q) q :=
    H19.Theorem19_4.gamma_tilde_nonneg fp hvalid_q
  have hgamma_le :
      H19.Theorem19_4.gamma_tilde fp (r + q) q ≤
        theorem20_10_householder_gammaA fp r p q := by
    simpa [H19.Theorem19_4.gamma_tilde, theorem20_10_householder_gammaA, K]
      using gamma_mono fp hidx_le hvalid_full
  rcases hqr.exists_frobNormRect_perturbation_bound hgamma_nonneg with
    ⟨DeltaC, hrep, hbound⟩
  refine ⟨DeltaC, hrep, le_trans hbound ?_⟩
  exact mul_le_mul_of_nonneg_right hgamma_le (frobNormRect_nonneg C)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    rounded Householder QR perturbation bound for the column-reversed
    `A Q₂` block.

    The exact GQR construction uses a QR of the column-reversed trailing block
    to obtain a lower-triangular `L22`.  This theorem names the corresponding
    rounded finite-precision dependency and records the actual computed
    Householder `Q`/`R` shape facts for that reversed block.  The bound is still
    relative to the reversed trailing block; transporting it back to a
    source-shaped `DeltaA` is the next assembly step. -/
theorem theorem20_10_householder_reversed_AQ2_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    let Crev : Fin (r + q) → Fin q → ℝ :=
      rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
    let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
      fl_householderQRPanel_Q fp (r + q) q Crev
    let Rrev : Fin (r + q) → Fin q → ℝ :=
      fl_householderQRPanel_R fp (r + q) q Crev
    ∃ DeltaC : Fin (r + q) → Fin q → ℝ,
      (∀ i j,
        Crev i j + DeltaC i j =
          matMulRect (r + q) (r + q) q Urev Rrev i j) ∧
      IsOrthogonal (r + q) Urev ∧
      IsUpperTrapezoidal (r + q) q Rrev ∧
      frobNormRect DeltaC ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect Crev := by
  dsimp
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
  rcases theorem20_10_householder_AQ2_frob_perturbation_bound
      fp Crev hq hvalid with
    ⟨DeltaC, hDeltaCrep, hDeltaCbound⟩
  let K : ℕ := householderConstructApplyGammaIndex (r + q)
  have hbase_valid : gammaValid fp (11 * (r + q) + 23) := by
    have hbase_le_K : 11 * (r + q) + 23 ≤ K := by
      dsimp [K, householderConstructApplyGammaIndex]
      omega
    have hpq : 0 < p + q := by omega
    have hK_le_pqK : K ≤ (p + q) * K := by
      calc
        K = 1 * K := by omega
        _ ≤ (p + q) * K := Nat.mul_le_mul_right K hpq
    exact gammaValid_mono fp (le_trans hbase_le_K hK_le_pqK) (by
      simpa [K] using hvalid)
  have hready :
      HouseholderQRPanelReady fp (r + q) q Crev :=
    HouseholderQRPanelReady_of_global_gammaValid
      fp (r + q) q (r + q) Crev le_rfl hbase_valid
  have hUrev : IsOrthogonal (r + q)
      (fl_householderQRPanel_Q fp (r + q) q Crev) :=
    fl_householderQRPanel_Q_orthogonal fp (r + q) q Crev hready
  have hRrev : IsUpperTrapezoidal (r + q) q
      (fl_householderQRPanel_R fp (r + q) q Crev) :=
      fl_householderQRPanel_R_upper_trapezoidal fp (r + q) q Crev
  exact ⟨DeltaC, hDeltaCrep, hUrev, hRrev, hDeltaCbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    source-coordinate perturbation for the column-reversed `A Q₂`
    Householder QR step.

    This transports the reversed trailing-block perturbation back through the
    full orthogonal `Q` factor, producing a source-shaped `DeltaA`.  The
    resulting perturbed trailing block, after reversing columns, is exactly the
    computed rounded Householder product for the column-reversed `A Q₂` panel.
    This is the A-side analogue of the concrete B-side factor-identification
    theorem; assembling the full rounded GQR record remains a separate step. -/
theorem theorem20_10_householder_reversed_AQ2_full_A_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    let Crev : Fin (r + q) → Fin q → ℝ :=
      rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
    let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
      fl_householderQRPanel_Q fp (r + q) q Crev
    let Rrev : Fin (r + q) → Fin q → ℝ :=
      fl_householderQRPanel_R fp (r + q) q Crev
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      (∀ i j,
        rectPermuteCols Fin.revPerm
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) Q) i j =
          matMulRect (r + q) (r + q) q Urev Rrev i j) ∧
      IsOrthogonal (r + q) Urev ∧
      IsUpperTrapezoidal (r + q) q Rrev ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect Crev := by
  dsimp
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
  rcases theorem20_10_householder_reversed_AQ2_frob_perturbation_bound
      fp A Q hq hvalid with
    ⟨DeltaCrev, hDeltaCrevRep, hUrev, hRrev, hDeltaCrevBound⟩
  let DeltaC : Fin (r + q) → Fin q → ℝ :=
    fun i j => DeltaCrev i (Fin.rev j)
  rcases gqrAQ2Block_exists_full_perturbation_of_trailing_delta
      Q DeltaC hQ with
    ⟨DeltaA, hDeltaAtrail, hDeltaAnorm⟩
  refine ⟨DeltaA, ?_, hUrev, hRrev, ?_⟩
  · intro i j
    have htrail := hDeltaAtrail A i (Fin.rev j)
    have hrev :
        rectPermuteCols Fin.revPerm
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) Q) i j =
          gqrAQ2Block A Q i (Fin.rev j) + DeltaCrev i j := by
      simpa [rectPermuteCols, DeltaC] using htrail
    calc
      rectPermuteCols Fin.revPerm
          (gqrAQ2Block (fun i j => A i j + DeltaA i j) Q) i j =
          gqrAQ2Block A Q i (Fin.rev j) + DeltaCrev i j := hrev
      _ = Crev i j + DeltaCrev i j := by
          rfl
      _ = matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q Crev)
            (fl_householderQRPanel_R fp (r + q) q Crev) i j := by
          simpa [Crev] using hDeltaCrevRep i j
  · have hpad :
        frobNormRect (fun i : Fin (r + q) =>
          Fin.append (fun _ : Fin p => 0) (DeltaC i)) =
            frobNormRect DeltaCrev := by
      calc
        frobNormRect (fun i : Fin (r + q) =>
            Fin.append (fun _ : Fin p => 0) (DeltaC i))
            = frobNormRect DeltaC := frobNormRect_zeroLeftCols_append DeltaC
        _ = frobNormRect (rectPermuteCols Fin.revPerm DeltaCrev) := by
          rfl
        _ = frobNormRect DeltaCrev :=
          frobNormRect_permuteCols Fin.revPerm DeltaCrev
    have hDeltaAeq : frobNormRect DeltaA = frobNormRect DeltaCrev := by
      rw [hDeltaAnorm, hpad]
    exact le_trans (le_of_eq hDeltaAeq) hDeltaCrevBound
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    source-shaped Frobenius bound for the column-reversed `A Q₂`
    Householder perturbation.

    This strengthens
    `theorem20_10_householder_reversed_AQ2_full_A_frob_perturbation_bound`
    by absorbing the reversed trailing-panel norm into the original source
    matrix norm.  It uses only orthogonality of the GQR `Q` factor and
    permutation invariance of the Frobenius norm, so the computed product and
    shape facts are unchanged. -/
theorem theorem20_10_householder_reversed_AQ2_full_A_source_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    let Crev : Fin (r + q) → Fin q → ℝ :=
      rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
    let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
      fl_householderQRPanel_Q fp (r + q) q Crev
    let Rrev : Fin (r + q) → Fin q → ℝ :=
      fl_householderQRPanel_R fp (r + q) q Crev
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      (∀ i j,
        rectPermuteCols Fin.revPerm
            (gqrAQ2Block (fun i j => A i j + DeltaA i j) Q) i j =
          matMulRect (r + q) (r + q) q Urev Rrev i j) ∧
      IsOrthogonal (r + q) Urev ∧
      IsUpperTrapezoidal (r + q) q Rrev ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A := by
  dsimp
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
  rcases theorem20_10_householder_reversed_AQ2_full_A_frob_perturbation_bound
      fp A Q hQ hq hvalid with
    ⟨DeltaA, hDeltaArep, hUrev, hRrev, hDeltaAraw⟩
  have hCrev_le_A : frobNormRect Crev ≤ frobNormRect A := by
    calc
      frobNormRect Crev =
          frobNormRect (gqrAQ2Block A Q) := by
            simpa [Crev] using
              frobNormRect_permuteCols Fin.revPerm (gqrAQ2Block A Q)
      _ ≤ frobNormRect A := frobNormRect_gqrAQ2Block_le A Q hQ
  have hgamma_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalid
  have hDeltaA :
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A :=
    le_trans hDeltaAraw
      (mul_le_mul_of_nonneg_left hCrev_le_A hgamma_nonneg)
  exact ⟨DeltaA, hDeltaArep, hUrev, hRrev, hDeltaA⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete full-`A` perturbation obtained from the smaller `A Q₂`
    Householder QR backward error.

    This combines the smaller-block QR perturbation theorem with the exact
    back-transport through an orthogonal `Q`: the constructed source-coordinate
    `DeltaA` makes the trailing block of `(A + DeltaA)Q` match the computed
    Householder QR product for `A Q₂`, and it satisfies the advertised
    `gamma_tilde_mn * ||A||_F` source-shaped bound.  It is still only the
    `A`-side component of the full Theorem 20.10 certificate. -/
theorem theorem20_10_householder_AQ2_full_A_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hq : 0 < q)
    (hvalid :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A := by
  let C : Fin (r + q) → Fin q → ℝ := gqrAQ2Block A Q
  rcases theorem20_10_householder_AQ2_frob_perturbation_bound
      fp C hq hvalid with
    ⟨DeltaC, hrep, hDeltaC⟩
  rcases gqrAQ2Block_exists_full_perturbation_of_trailing_delta
      Q DeltaC hQ with
    ⟨DeltaA, hDeltaAtrail, hDeltaAnorm⟩
  refine ⟨DeltaA, ?_, ?_⟩
  · intro i j
    calc
      gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j
          = gqrAQ2Block A Q i j + DeltaC i j := hDeltaAtrail A i j
      _ = matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j := by
          simpa [C] using hrep i j
  · have hpad :
        frobNormRect (fun i : Fin (r + q) =>
          Fin.append (fun _ : Fin p => 0) (DeltaC i)) =
            frobNormRect DeltaC :=
      frobNormRect_zeroLeftCols_append DeltaC
    have hDeltaA_le_C :
        frobNormRect DeltaA ≤
          theorem20_10_householder_gammaA fp r p q * frobNormRect C := by
      rwa [hDeltaAnorm, hpad]
    have hC_le_A : frobNormRect C ≤ frobNormRect A := by
      simpa [C] using frobNormRect_gqrAQ2Block_le A Q hQ
    have hgamma_nonneg :
        0 ≤ theorem20_10_householder_gammaA fp r p q := by
      simpa [theorem20_10_householder_gammaA] using
        H19.Theorem19_4.gamma_tilde_nonneg fp hvalid
    exact le_trans hDeltaA_le_C
      (mul_le_mul_of_nonneg_left hC_le_A hgamma_nonneg)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    generic right-hand-side perturbation for a rectangular Householder panel,
    with the conservative accumulated RHS gamma factor exposed.

    This is the orientation-independent RHS component used by the `A Q₂` and
    column-reversed `A Q₂` paths.  It packages the QR module's explicit
    Householder RHS backward-error theorem with the closed-growth gamma budget
    already used in the source-facing Theorem 20.10 routes. -/
theorem theorem20_10_householder_panel_rhs_vecNorm2_perturbation_bound_of_gammaFactor
    {m p : ℕ} (fp : FPModel)
    (C : Fin m → Fin p → ℝ)
    (b : Fin m → ℝ)
    (hpm : p ≤ m)
    (hp : 0 < p) (hm : 0 < m)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex m p : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ Deltab : Fin m → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp m p C b i =
          matMulVec m
            (matTranspose (fl_householderQRPanel_Q fp m p C))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (m : ℝ) *
          (((2 : ℝ) *
              (householderQRRhsPanelGammaClosedGrowthFactor m p : ℝ) *
              gamma fp (p * householderConstructApplyGammaIndex m)) *
            vecNorm2 b) := by
  let idx : ℕ := householderQRRhsPanelGammaClosedGrowthIndex m p
  let K : ℕ := householderConstructApplyGammaIndex m
  let gammaCoeff : ℝ :=
    (2 : ℝ) *
      (householderQRRhsPanelGammaClosedGrowthFactor m p : ℝ) *
      gamma fp (p * K)
  have hidx_valid : gammaValid fp idx := by
    unfold gammaValid
    exact lt_of_le_of_lt (by simpa [idx] using hhalf) (by norm_num)
  have hprinted_le_idx : p * K ≤ idx := by
    change p * householderConstructApplyGammaIndex m ≤
      householderQRRhsPanelGammaClosedGrowthIndex m p
    rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
    exact Nat.le_mul_of_pos_left _
      (householderQRRhsPanelGammaClosedGrowthFactor_pos
        (m := m) (p := p) hm)
  have hprinted_valid : gammaValid fp (p * K) :=
    gammaValid_mono fp hprinted_le_idx hidx_valid
  have hbase_le_K : 11 * m + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hK_le_pK : K ≤ p * K :=
    Nat.le_mul_of_pos_left K hp
  have hbase_valid : gammaValid fp (11 * m + 23) :=
    gammaValid_mono fp
      (le_trans hbase_le_K (le_trans hK_le_pK hprinted_le_idx))
      hidx_valid
  have hready : HouseholderQRPanelReady fp m p C :=
    HouseholderQRPanelReady_of_global_gammaValid fp m p m C le_rfl
      hbase_valid
  rcases fl_householderQRPanel_rhs_explicit_vecNorm2_perturbation_bound
      fp m p C b hready with
    ⟨Deltab, hrep, hbound⟩
  have hraw_le_inf :
      householderQRRhsPanelBackwardBound fp m p C b ≤
        gammaCoeff * infNormVec b := by
    simpa [gammaCoeff, K] using
      householderQRRhsPanelBackwardBound_le_gammaClosedGrowthFactor
        fp m p C b hpm hm hhalf hready
  have hsqrt_nonneg : 0 ≤ Real.sqrt (m : ℝ) :=
    Real.sqrt_nonneg _
  have hto_inf :
      vecNorm2 Deltab ≤
        Real.sqrt (m : ℝ) * (gammaCoeff * infNormVec b) := by
    exact le_trans hbound
      (mul_le_mul_of_nonneg_left hraw_le_inf hsqrt_nonneg)
  have hgamma_nonneg : 0 ≤ gamma fp (p * K) :=
    gamma_nonneg fp hprinted_valid
  have hfactor_nonneg :
      0 ≤ (householderQRRhsPanelGammaClosedGrowthFactor m p : ℝ) := by
    positivity
  have hgammaCoeff_nonneg : 0 ≤ gammaCoeff := by
    dsimp [gammaCoeff]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hfactor_nonneg) hgamma_nonneg
  have hinf_le_vec : infNormVec b ≤ vecNorm2 b :=
    infNormVec_le_of_abs_le b
      (fun i => abs_coord_le_vecNorm2 b i) (vecNorm2_nonneg b)
  have hcoeff_inf_le_vec :
      gammaCoeff * infNormVec b ≤ gammaCoeff * vecNorm2 b :=
    mul_le_mul_of_nonneg_left hinf_le_vec hgammaCoeff_nonneg
  refine ⟨Deltab, hrep, ?_⟩
  exact le_trans hto_inf
    (by
      simpa [gammaCoeff, K] using
        mul_le_mul_of_nonneg_left hcoeff_inf_le_vec hsqrt_nonneg)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete right-hand-side perturbation for the smaller `A Q₂`
    Householder transform used in the GQR path.

    This is the source-facing specialization of the QR module's explicit
    RHS-transform certificate to the trailing block `A Q₂`.  The bound is the
    verified recursive implementation budget for that transform; the later
    source-facing `gamma_tilde_mn * ||b||₂` absorption remains a separate
    obligation. -/
theorem theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hready :
      HouseholderQRPanelReady fp (r + q) q (gqrAQ2Block A Q)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          householderQRRhsPanelBackwardBound fp (r + q) q
            (gqrAQ2Block A Q) b := by
  simpa using
    fl_householderQRPanel_rhs_explicit_vecNorm2_perturbation_bound
      fp (r + q) q (gqrAQ2Block A Q) b hready
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    global-gamma wrapper for the `A Q₂` RHS perturbation certificate.

    A single row-count validity hypothesis supplies the readiness obligations
    for the zero-aware Householder QR panel implementation.  The norm bound is
    still the concrete recursive RHS budget, not the final printed
    `gamma_tilde_mn * ||b||₂` coefficient. -/
theorem theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_global_gammaValid
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hvalid : gammaValid fp (11 * (r + q) + 23)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          householderQRRhsPanelBackwardBound fp (r + q) q
            (gqrAQ2Block A Q) b := by
  exact
    theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound
      fp A Q b
      (HouseholderQRPanelReady_of_global_gammaValid
        fp (r + q) q (r + q) (gqrAQ2Block A Q) le_rfl hvalid)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative source-norm bound for the `A Q₂` RHS perturbation.

    The half-radius guard for the verified recursive RHS index supplies both
    the Householder panel readiness condition and the accumulated gamma
    comparison.  The result exposes the remaining gap to the printed
    `gamma_tilde_mn * ||b||₂` coefficient as the visible dimension-only factor
    `2 * householderQRRhsPanelGammaClosedGrowthFactor (r+q) q`. -/
theorem theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_gammaFactor
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          (((2 : ℝ) *
              (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
              gamma fp (q * householderConstructApplyGammaIndex (r + q))) *
            vecNorm2 b) := by
  let idx : ℕ := householderQRRhsPanelGammaClosedGrowthIndex (r + q) q
  let K : ℕ := householderConstructApplyGammaIndex (r + q)
  let C : ℝ :=
    (2 : ℝ) *
      (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
      gamma fp (q * K)
  have hidx_valid : gammaValid fp idx := by
    unfold gammaValid
    exact lt_of_le_of_lt (by simpa [idx] using hhalf) (by norm_num)
  have hprinted_le_idx : q * K ≤ idx := by
    change q * householderConstructApplyGammaIndex (r + q) ≤
      householderQRRhsPanelGammaClosedGrowthIndex (r + q) q
    rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
    exact Nat.le_mul_of_pos_left _
      (householderQRRhsPanelGammaClosedGrowthFactor_pos
        (m := r + q) (p := q) (by omega))
  have hprinted_valid : gammaValid fp (q * K) :=
    gammaValid_mono fp hprinted_le_idx hidx_valid
  have hbase_le_K :
      11 * (r + q) + 23 ≤ K := by
    dsimp [K, householderConstructApplyGammaIndex]
    omega
  have hK_le_qK : K ≤ q * K :=
    Nat.le_mul_of_pos_left K hq
  have hbase_valid : gammaValid fp (11 * (r + q) + 23) :=
    gammaValid_mono fp
      (le_trans hbase_le_K (le_trans hK_le_qK hprinted_le_idx))
      hidx_valid
  let Cmat : Fin (r + q) → Fin q → ℝ := gqrAQ2Block A Q
  have hready :
      HouseholderQRPanelReady fp (r + q) q Cmat :=
    HouseholderQRPanelReady_of_global_gammaValid
      fp (r + q) q (r + q) Cmat le_rfl hbase_valid
  rcases
    theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound
      fp A Q b (by simpa [Cmat] using hready) with
    ⟨Deltab, hrep, hbound⟩
  have hm : 0 < r + q := by omega
  have hraw_le_inf :
      householderQRRhsPanelBackwardBound fp (r + q) q Cmat b ≤
        C * infNormVec b := by
    simpa [C, Cmat, K] using
      householderQRRhsPanelBackwardBound_le_gammaClosedGrowthFactor
        fp (r + q) q Cmat b (by omega) hm hhalf hready
  have hsqrt_nonneg : 0 ≤ Real.sqrt (r + q : ℝ) :=
    Real.sqrt_nonneg _
  have hto_inf :
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) * (C * infNormVec b) := by
    exact le_trans hbound
      (mul_le_mul_of_nonneg_left (by simpa [Cmat] using hraw_le_inf)
        hsqrt_nonneg)
  have hgamma_nonneg : 0 ≤ gamma fp (q * K) :=
    gamma_nonneg fp hprinted_valid
  have hfactor_nonneg :
      0 ≤ (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) := by
    positivity
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg
      (mul_nonneg (by norm_num) hfactor_nonneg) hgamma_nonneg
  have hinf_le_vec : infNormVec b ≤ vecNorm2 b :=
    infNormVec_le_of_abs_le b
      (fun i => abs_coord_le_vecNorm2 b i) (vecNorm2_nonneg b)
  have hC_inf_le_vec :
      C * infNormVec b ≤ C * vecNorm2 b :=
    mul_le_mul_of_nonneg_left hinf_le_vec hC_nonneg
  refine ⟨Deltab, hrep, ?_⟩
  exact le_trans hto_inf
    (by
      simpa [C, K] using
        mul_le_mul_of_nonneg_left hC_inf_le_vec hsqrt_nonneg)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    conservative perturbation certificate for the column-reversed `A Q₂`
    Householder RHS tail.

    The returned equality is oriented as a transformed RHS identity for the
    active columns that become the bottom `q` columns of the constructed GQR
    left factor. -/
theorem theorem20_10_householder_reversed_AQ2_rhs_tail_vecNorm2_perturbation_bound_of_gammaFactor
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ j : Fin q,
        matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q
                (rectPermuteCols Fin.revPerm (gqrAQ2Block A Q))))
            (fun k => b k + Deltab k)
            (Fin.cast (Nat.add_comm q r) (Fin.castAdd r (Fin.rev j))) =
          theorem20_10_householder_reversed_AQ2_rhs_tail fp A Q b j) ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b := by
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Q)
  rcases
    theorem20_10_householder_panel_rhs_vecNorm2_perturbation_bound_of_gammaFactor
      fp Crev b (by omega) hq (by omega) hhalf with
    ⟨Deltab, hrep, hDeltab_raw⟩
  refine ⟨Deltab, ?_, ?_⟩
  · intro j
    have h :=
      hrep
        (Fin.cast (Nat.add_comm q r) (Fin.castAdd r (Fin.rev j)))
    simpa [theorem20_10_householder_reversed_AQ2_rhs_tail, Crev] using h.symm
  · simpa [theorem20_10_householder_rhs_conservative_gamma, mul_assoc]
      using hDeltab_raw
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), rounded Householder RHS
    certificate route with the currently proved conservative RHS coefficient.

    If the supplied GQR factor's `U` is the rounded Householder panel `Q` for
    `A Q₂`, then the verified RHS transform theorem supplies a `Deltab` whose
    transformed trailing block is exactly the computed RHS tail.  The matrix
    perturbation bounds and triangular preservation are discharged by the
    transformed-tail constructed-source wrapper; the RHS coefficient remains
    the explicit conservative bound
    `theorem20_10_householder_rhs_conservative_gamma`. -/
theorem theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge_matrix : gamma fp q ≤ gammaA)
    (hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i : Fin q,
        matMulVec (r + q) (matTranspose h.U)
            (fun k => b k + Deltab k) (Fin.natAdd r i) =
          theorem20_10_householder_AQ2_rhs_tail fp A h.Q b i) ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
        (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
        (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
        frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
        frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
        Nonempty
          (Theorem20_10PartAPerturbationCertificate A B b d
            (theorem20_10_gqr_xhat_of_transformed_tail fp h
              (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
            gammaA gammaB) := by
  rcases
    theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_gammaFactor
      fp A h.Q b hq hhalf with
    ⟨Deltab, hrep, hDeltab_raw⟩
  have hDeltab_conservative :
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b := by
    simpa [theorem20_10_householder_rhs_conservative_gamma, mul_assoc]
      using hDeltab_raw
  have hDeltab :
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b :=
    le_trans hDeltab_conservative
      (mul_le_mul_of_nonneg_right hgammaA_ge_rhs (vecNorm2_nonneg b))
  have hb_tail : ∀ i : Fin q,
      matMulVec (r + q) (matTranspose h.U)
          (fun k => b k + Deltab k) (Fin.natAdd r i) =
        theorem20_10_householder_AQ2_rhs_tail fp A h.Q b i := by
    intro i
    simpa [theorem20_10_householder_AQ2_rhs_tail, hUfl] using
      (hrep (Fin.natAdd r i)).symm
  rcases
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
      fp h (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) b d
      gammaA gammaB Deltab hgammaB_nonneg hgammaA_ge_matrix hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hcert⟩
  exact
    ⟨Deltab, hb_tail, hDeltab, DeltaS, DeltaL22,
      hDeltaSbound, hDeltaL22bound, hDeltaSfrob, hDeltaL22frob,
      hcert hDeltab hb_tail⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), rounded Householder RHS
    mixed-stability route with the currently proved conservative RHS
    coefficient.

    This unwraps
    `theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound`
    through the generic Part A certificate-to-core theorem.  The result is an
    honest computed-RHS Part A surface: the computed vector uses the rounded
    Householder RHS tail, while the `Deltab` coefficient is the explicit
    conservative coefficient supplied through `gammaA`. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge_matrix : gamma fp q ≤ gammaA)
    (hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat_of_transformed_tail fp h
            (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d j =
          x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound
      fp h b d gammaA gammaB hUfl hq hhalf hgammaB_nonneg
      hgammaA_ge_matrix hgammaA_ge_rhs hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨_Deltab, _hb_tail, _hDeltab, _DeltaS, _DeltaL22,
      _hDeltaSbound, _hDeltaL22bound, _hDeltaSfrob, _hDeltaL22frob,
      hcert⟩
  rcases hcert with ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d
      (theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
      cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x,
      hDeltaAeq, hDeltaBeq, hDeltabeq, hxhat, hDeltaX,
      hDeltaA, hDeltab, hDeltaB, hx, hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x,
      hxhat, hDeltaX, ?_, ?_, ?_, hx, hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltaBeq] using hDeltaB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a), rounded Householder RHS
    mixed-stability route with source-facing conservative gamma coefficients.

    Compared with
    `theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_bound`,
    this theorem derives the matrix and triangular-solve gamma side conditions
    from the standard Householder validity hypotheses.  The `A`/`b`
    coefficient is
    `theorem20_10_householder_gammaA_conservativeRhs`, the maximum of the
    printed matrix coefficient and the verified conservative RHS coefficient. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat_of_transformed_tail fp h
            (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d j =
          x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) := by
    exact le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hidxB_ge_p :
      p ≤ p * householderConstructApplyGammaIndex (p + q) :=
    Nat.le_mul_of_pos_right p hKB_pos
  have hgammaA_printed_ge :
      gamma fp q ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxA_ge_q hvalidA
  have hgammaA_ge_matrix :
      gamma fp q ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    le_trans hgammaA_printed_ge
      (le_max_left _ _)
  have hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    le_max_right _ _
  have hgammaB_ge :
      gamma fp p ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxB_ge_p hvalidB
  exact
    theorem20_10_partA_mixed_stability_of_constructed_source_householder_rhs_conservative_bound
      fp h b d
      (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
      (theorem20_10_householder_gammaB fp r p q)
      hUfl hq hhalf hgammaB_nonneg hgammaA_ge_matrix hgammaA_ge_rhs
      hgammaB_ge hSdiag hL22diag hvalid2S hvalid2L22
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder QR perturbation bound for the `Bᵀ` triangularization
    step in the GQR path.

    Applying the Chapter 19 Householder QR backward-error theorem to
    `Bᵀ : R^((p+q)×p)` gives a perturbation of `B` with the advertised
    `gamma_tilde_np` Frobenius bound.  This is a genuine computed-path
    dependency for the Theorem 20.10 certificates; it does not yet prove the
    downstream triangular-solve perturbations or rank preservation. -/
theorem theorem20_10_householder_B_transpose_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (B : Fin p → Fin (p + q) → ℝ)
    (hp : 0 < p)
    (hvalid :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B := by
  have hqr :
      H19.Theorem19_4.HouseholderQRBackwardError (p + q) p (finiteTranspose B)
        (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
        (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B))
        (theorem20_10_householder_gammaB fp r p q) := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.householder_qr_backward_error
        fp (p + q) p (finiteTranspose B) hp (Nat.le_add_right p q) hvalid
  have hgamma_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalid
  rcases
    hqr.exists_frobNormRect_perturbation_bound hgamma_nonneg with
    ⟨DeltaBT, hrep, hbound⟩
  refine ⟨finiteTranspose DeltaBT, ?_, ?_⟩
  · intro i j
    simpa [finiteTranspose] using hrep j i
  · simpa [theorem20_10_householder_gammaB, frobNormRect_finiteTranspose]
      using hbound
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, concrete rounded `Bᵀ`
    Householder QR constraint block.

    The computed Householder panel for `Bᵀ` gives explicit factors `Q_B` and
    `R_B`.  After taking the transpose of the computed product, the perturbed
    constraint matrix satisfies the exact GQR block identity
    `(B + DeltaB) Q_B = [S,0]`, where `S` is the transpose of the top square
    block of `R_B`.  This closes the concrete `B`-side factor-identification
    dependency; rank preservation remains a separate source perturbation
    obligation. -/
theorem theorem20_10_householder_B_transpose_perturbed_constraint_block
    {r p q : ℕ} (fp : FPModel)
    (B : Fin p → Fin (p + q) → ℝ)
    (hp : 0 < p)
    (hvalid :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rhat : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rhat (Fin.castAdd q i) j)
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rhat j i) ∧
      IsOrthogonal (p + q) Qb ∧
      IsLowerTriangular S ∧
      matMulRect p (p + q) (p + q)
        (fun i j => B i j + DeltaB i j) Qb = gqrBQBlock S ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B := by
  dsimp
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let Rhat : Fin (p + q) → Fin p → ℝ :=
    fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ :=
    matTranspose (fun i : Fin p => fun j : Fin p =>
      Rhat (Fin.castAdd q i) j)
  have hbase_valid : gammaValid fp (11 * (p + q) + 23) := by
    let K : ℕ := householderConstructApplyGammaIndex (p + q)
    have hbase_le_K : 11 * (p + q) + 23 ≤ K := by
      dsimp [K, householderConstructApplyGammaIndex]
      omega
    have hK_le_pK : K ≤ p * K :=
      Nat.le_mul_of_pos_left K hp
    exact gammaValid_mono fp (le_trans hbase_le_K hK_le_pK) (by
      simpa [K] using hvalid)
  have hready :
      HouseholderQRPanelReady fp (p + q) p (finiteTranspose B) :=
    HouseholderQRPanelReady_of_global_gammaValid
      fp (p + q) p (p + q) (finiteTranspose B) le_rfl hbase_valid
  have hQb : IsOrthogonal (p + q) Qb := by
    simpa [Qb] using
      fl_householderQRPanel_Q_orthogonal
        fp (p + q) p (finiteTranspose B) hready
  have hRupper : IsUpperTrapezoidal (p + q) p Rhat := by
    simpa [Rhat] using
      fl_householderQRPanel_R_upper_trapezoidal
        fp (p + q) p (finiteTranspose B)
  have hconstraint :=
    gqrBQBlock_eq_of_transpose_product_tall_qr Qb Rhat hQb hRupper
  dsimp [S] at hconstraint
  rcases theorem20_10_householder_B_transpose_frob_perturbation_bound
      fp B hp hvalid with
    ⟨DeltaB, hDeltaBrep, hDeltaB⟩
  have hBpert_eq :
      (fun i j => B i j + DeltaB i j) =
        fun i j => matMulRect (p + q) (p + q) p Qb Rhat j i := by
    ext i j
    simpa [Qb, Rhat] using hDeltaBrep i j
  refine ⟨DeltaB, ?_, hQb, hconstraint.1, ?_, hDeltaB⟩
  · intro i j
    exact congrFun (congrFun hBpert_eq i) j
  · rw [hBpert_eq]
    exact hconstraint.2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, rounded `Bᵀ`
    Householder panel inserted into a GQR record.

    The `A` side is still represented by transported supplied/computed blocks,
    but the constraint side is now the concrete perturbed matrix coming from
    the rounded Householder QR of `Bᵀ`.  This is the algebraic bridge needed to
    replace a supplied `BQ=[S,0]` hypothesis by the actual computed B-side
    panel in later rounded-GQR assembly theorems. -/
theorem theorem20_10_householder_B_transpose_constructed_sourceA_gqr_factorization
    {r p q : ℕ} (fp : FPModel)
    (B : Fin p → Fin (p + q) → ℝ)
    (U : Fin (r + q) → Fin (r + q) → ℝ)
    (L11 : Fin r → Fin p → ℝ)
    (L21 : Fin q → Fin p → ℝ)
    (L22 : Fin q → Fin q → ℝ)
    (hp : 0 < p)
    (hU : IsOrthogonal (r + q) U)
    (hL22 : IsLowerTriangular L22)
    (hvalid :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rhat : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rhat (Fin.castAdd q i) j)
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rhat j i) ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (gqrSourceAFromBlocks Qb U L11 L21 L22)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧
        hpert.U = U ∧
        hpert.S = S ∧
        hpert.L11 = L11 ∧
        hpert.L21 = L21 ∧
        hpert.L22 = L22 ∧
        frobNormRect DeltaB ≤
          theorem20_10_householder_gammaB fp r p q * frobNormRect B) := by
  dsimp
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let Rhat : Fin (p + q) → Fin p → ℝ :=
    fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ :=
    matTranspose (fun i : Fin p => fun j : Fin p =>
      Rhat (Fin.castAdd q i) j)
  rcases theorem20_10_householder_B_transpose_perturbed_constraint_block
      fp B hp hvalid with
    ⟨DeltaB, hDeltaBrep, hQb, hS, hBQ, hDeltaBbound⟩
  let hpert : GeneralizedQRFactorization r p q
      (gqrSourceAFromBlocks Qb U L11 L21 L22)
      (fun i j => B i j + DeltaB i j) :=
    GeneralizedQRFactorization.of_sourceA_blocks_and_constraint_block
      Qb U L11 L21 L22 S (fun i j => B i j + DeltaB i j)
      hQb hU hL22 hS hBQ
  refine ⟨DeltaB, hDeltaBrep, hpert, ?_, ?_, ?_, ?_, ?_, ?_, hDeltaBbound⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, rounded Householder
    `Bᵀ`/`A Q₂` perturbations assembled into one perturbed GQR record.

    The concrete `Bᵀ` Householder panel supplies the GQR `Q` and `S` fields for
    the perturbed constraint matrix.  The source-shaped reversed `A Q₂`
    Householder perturbation is then converted to the tall `[0;L]` associated
    shape by `GQRAQTallCase.exists_of_square_qr_reversed_cols`, producing a
    genuine GQR factorization for `(A + DeltaA, B + DeltaB)`.  Rank preservation
    and returned-vector identification remain separate obligations. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_factorization
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S := by
  dsimp
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let Rb : Fin (p + q) → Fin p → ℝ :=
    fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ :=
    matTranspose (fun i : Fin p => fun j : Fin p =>
      Rb (Fin.castAdd q i) j)
  rcases theorem20_10_householder_B_transpose_perturbed_constraint_block
      fp B hp hvalidB with
    ⟨DeltaB, hDeltaBrep, hQb, hS, hBQ, hDeltaB⟩
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Qb)
  let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
    fl_householderQRPanel_Q fp (r + q) q Crev
  let Rrev : Fin (r + q) → Fin q → ℝ :=
    fl_householderQRPanel_R fp (r + q) q Crev
  rcases theorem20_10_householder_reversed_AQ2_full_A_source_frob_perturbation_bound
      fp A Qb hQb hq hvalidA with
    ⟨DeltaA, hDeltaArep, hUrev, hRrev, hDeltaA⟩
  have hfactor :
      rectPermuteCols Fin.revPerm
          (gqrAQ2Block (fun i j => A i j + DeltaA i j) Qb) =
        matMulRect (r + q) (r + q) q Urev Rrev := by
    ext i j
    simpa [Crev, Urev, Rrev] using hDeltaArep i j
  rcases GQRAQTallCase.exists_of_square_qr_reversed_cols
      (gqrAQ2Block (fun i j => A i j + DeltaA i j) Qb)
      Urev Rrev hUrev hRrev hfactor with
    ⟨U, hU, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  rcases GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      Qb S U hQb hS hBQ hU hCase with
    ⟨hpert, hQeq, _hUeq, hSeq, _hL22eq⟩
  exact ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB, hpert, hQeq, hSeq⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10, rounded Householder
    `Bᵀ`/`A Q₂` perturbations assembled into one perturbed GQR record, retaining
    the concrete bottom-column placement of the constructed `U` factor.

    This is the same constructed perturbed GQR route as
    `theorem20_10_householder_constructed_perturbed_gqr_factorization`, but it
    also exposes the relation between the bottom `q` columns of the GQR
    left-factor and the active columns of the rounded Householder panel for the
    column-reversed `A Q₂` block.  That relation is the local bridge needed for
    the later transformed-RHS and returned-vector identification steps. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_factorization_with_U_tail
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let Crev : Fin (r + q) → Fin q → ℝ :=
      rectPermuteCols Fin.revPerm (gqrAQ2Block A Qb)
    let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
      fl_householderQRPanel_Q fp (r + q) q Crev
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
          (∀ i j, hpert.U i (Fin.natAdd r j) =
            Urev i
              (Fin.cast (Nat.add_comm q r) (Fin.castAdd r (Fin.rev j)))) := by
  dsimp
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let Rb : Fin (p + q) → Fin p → ℝ :=
    fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ :=
    matTranspose (fun i : Fin p => fun j : Fin p =>
      Rb (Fin.castAdd q i) j)
  rcases theorem20_10_householder_B_transpose_perturbed_constraint_block
      fp B hp hvalidB with
    ⟨DeltaB, hDeltaBrep, hQb, hS, hBQ, hDeltaB⟩
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Qb)
  let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
    fl_householderQRPanel_Q fp (r + q) q Crev
  let Rrev : Fin (r + q) → Fin q → ℝ :=
    fl_householderQRPanel_R fp (r + q) q Crev
  rcases theorem20_10_householder_reversed_AQ2_full_A_source_frob_perturbation_bound
      fp A Qb hQb hq hvalidA with
    ⟨DeltaA, hDeltaArep, hUrev, hRrev, hDeltaA⟩
  have hfactor :
      rectPermuteCols Fin.revPerm
          (gqrAQ2Block (fun i j => A i j + DeltaA i j) Qb) =
        matMulRect (r + q) (r + q) q Urev Rrev := by
    ext i j
    simpa [Crev, Urev, Rrev] using hDeltaArep i j
  rcases
    GQRAQTallCase.exists_of_square_qr_reversed_cols_with_bottom_reversed_columns
      (gqrAQ2Block (fun i j => A i j + DeltaA i j) Qb)
      Urev Rrev hUrev hRrev hfactor with
    ⟨U, hU, hUbottom, hCaseNonempty⟩
  rcases hCaseNonempty with ⟨hCase⟩
  rcases GeneralizedQRFactorization.exists_of_constraint_and_A_Q2_tall_case
      (A := fun i j => A i j + DeltaA i j)
      (B := fun i j => B i j + DeltaB i j)
      Qb S U hQb hS hBQ hU hCase with
    ⟨hpert, hQeq, hUeq, hSeq, _hL22eq⟩
  refine
    ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB, hpert,
      hQeq, hSeq, ?_⟩
  intro i j
  simpa [hUeq] using hUbottom i j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    constructed rounded Householder GQR record with a matching reversed-panel
    transformed RHS tail.

    The constructed `A Q₂` factorization uses the column-reversed panel, so the
    matching computed RHS tail is
    `theorem20_10_householder_reversed_AQ2_rhs_tail`.  This theorem combines
    the concrete perturbed GQR record, its bottom-column `U` placement, and the
    rounded Householder RHS perturbation to expose the exact trailing
    transformed-RHS identity for that constructed record.  Perturbed diagonal
    nonzeroness/rank preservation remains a separate obligation. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
          (∀ j : Fin q,
            matMulVec (r + q) (matTranspose hpert.U)
                (fun k => b k + Deltab k) (Fin.natAdd r j) =
              theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b j) := by
  dsimp
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let Rb : Fin (p + q) → Fin p → ℝ :=
    fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
  let S : Fin p → Fin p → ℝ :=
    matTranspose (fun i : Fin p => fun j : Fin p =>
      Rb (Fin.castAdd q i) j)
  let Crev : Fin (r + q) → Fin q → ℝ :=
    rectPermuteCols Fin.revPerm (gqrAQ2Block A Qb)
  let Urev : Fin (r + q) → Fin (r + q) → ℝ :=
    fl_householderQRPanel_Q fp (r + q) q Crev
  rcases
    theorem20_10_householder_constructed_perturbed_gqr_factorization_with_U_tail
      fp A B hp hq hvalidA hvalidB with
    ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB,
      hpert, hQeq, hSeq, hUtail⟩
  rcases
    theorem20_10_householder_reversed_AQ2_rhs_tail_vecNorm2_perturbation_bound_of_gammaFactor
      fp A Qb b hq hhalf with
    ⟨Deltab, hDeltab_tail, hDeltab⟩
  refine
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, ?_⟩
  intro j
  calc
    matMulVec (r + q) (matTranspose hpert.U)
        (fun k => b k + Deltab k) (Fin.natAdd r j)
        = matMulVec (r + q) (matTranspose Urev)
            (fun k => b k + Deltab k)
            (Fin.cast (Nat.add_comm q r) (Fin.castAdd r (Fin.rev j))) := by
          unfold matMulVec matTranspose
          apply Finset.sum_congr rfl
          intro k _
          rw [hUtail k j]
    _ = theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b j := by
          simpa [Urev, Crev] using hDeltab_tail j
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    exact method handoff for the constructed rounded Householder GQR record,
    stated with the matching reversed-panel transformed RHS tail.

    This is the diagonal-conditioned exact-method counterpart of
    `theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail`.
    The exact triangular coordinate equation uses the computed reversed RHS
    tail `beta`, while the minimizer statement is for the perturbed right-hand
    side `b + Deltab` certified by the Householder RHS backward error. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_exact_method_of_diagonal_reversed_rhs_tail
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
            rectMatMulVec hpert.S yz.1 = d ∧
            rectMatMulVec hpert.L22 yz.2 =
              (fun i : Fin q => beta i - rectMatMulVec hpert.L21 yz.1 i) ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j) d
              (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j) d x)) := by
  dsimp
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail
      fp A B b hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail⟩
  refine
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, ?_⟩
  intro hSdiag hL22diag
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag, hL22diag⟩
  let bpert : Fin (r + q) → ℝ := fun i => b i + Deltab i
  rcases
    hpert.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank
      (b := bpert) (d := d) hrank.1 hrank.2 with
    ⟨yz, hyz, hyz_unique⟩
  have hyz_beta :
      rectMatMulVec hpert.S yz.1 = d ∧
        rectMatMulVec hpert.L22 yz.2 =
          (fun i : Fin q => beta i - rectMatMulVec hpert.L21 yz.1 i) ∧
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          bpert
          (fun i j => B i j + DeltaB i j) d
          (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2)) := by
    rcases hyz with ⟨hSyz, hL22yz, hmin⟩
    refine ⟨hSyz, ?_, hmin⟩
    ext i
    calc
      rectMatMulVec hpert.L22 yz.2 i
          = matMulVec (r + q) (matTranspose hpert.U) bpert
              (Fin.natAdd r i) - rectMatMulVec hpert.L21 yz.1 i := by
              exact congrFun hL22yz i
      _ = beta i - rectMatMulVec hpert.L21 yz.1 i := by
              rw [hb_tail i]
  have hyz_beta_unique :
      ∀ yz' : (Fin p → ℝ) × (Fin q → ℝ),
        (rectMatMulVec hpert.S yz'.1 = d ∧
          rectMatMulVec hpert.L22 yz'.2 =
            (fun i : Fin q => beta i - rectMatMulVec hpert.L21 yz'.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            bpert
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz'.1 yz'.2))) →
          yz' = yz := by
    intro yz' hyz'
    apply hyz_unique yz'
    rcases hyz' with ⟨hSyz', hL22yz', hmin'⟩
    refine ⟨hSyz', ?_, hmin'⟩
    ext i
    calc
      rectMatMulVec hpert.L22 yz'.2 i
          = beta i - rectMatMulVec hpert.L21 yz'.1 i := by
              exact congrFun hL22yz' i
      _ = matMulVec (r + q) (matTranspose hpert.U) bpert
              (Fin.natAdd r i) - rectMatMulVec hpert.L21 yz'.1 i := by
              dsimp [beta]
              rw [← hb_tail i]
  exact
    ⟨⟨yz, hyz_beta, hyz_beta_unique⟩,
      hpert.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
        (b := bpert) (d := d) hrank.1 hrank.2⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    triangular-solve backward-error witnesses for the constructed rounded
    Householder GQR record and its matching reversed-panel transformed RHS.

    This connects the concrete `Bᵀ`/reversed-`A Q₂` perturbation construction to
    the actual `fl_forwardSub` calls in the GQR method.  Under the remaining
    constructed diagonal nonzero conditions, it returns the `DeltaS` and
    `DeltaL22` witnesses for the computed
    `theorem20_10_gqr_xhat_of_transformed_tail` path. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail_triangular_solve_frob_perturbation_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          ∃ (DeltaS : Fin p → Fin p → ℝ)
            (DeltaL22 : Fin q → Fin q → ℝ),
            (∀ i j, |DeltaS i j| ≤ gamma fp p * |hpert.S i j|) ∧
            (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |hpert.L22 i j|) ∧
            frobNormRect DeltaS ≤ gamma fp p * frobNormRect hpert.S ∧
            frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect hpert.L22 ∧
            rectMatMulVec (fun i j => hpert.S i j + DeltaS i j)
              (theorem20_10_gqr_y1hat fp hpert d) = d ∧
            rectMatMulVec (fun i j => hpert.L22 i j + DeltaL22 i j)
              (theorem20_10_gqr_y2hat_of_transformed_tail fp hpert beta d) =
                theorem20_10_gqr_rhs2hat_of_transformed_tail fp hpert beta d ∧
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d =
              matMulVec (p + q) hpert.Q
                (Fin.append
                  (theorem20_10_gqr_y1hat fp hpert d)
                  (theorem20_10_gqr_y2hat_of_transformed_tail
                    fp hpert beta d))) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail
      fp A B b hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail⟩
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hvalidS : gammaValid fp p := by
    exact gammaValid_mono fp
      (Nat.le_mul_of_pos_right p hKB_pos) hvalidB
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
    le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hvalidL22 : gammaValid fp q :=
    gammaValid_mono fp hidxA_ge_q hvalidA
  refine
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, ?_, ?_⟩
  · intro j
    exact hb_tail j
  · intro hSdiag hL22diag
    exact
      theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
        fp hpert beta d hSdiag hL22diag hvalidS hvalidL22
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    second-layer Part A certificate for the constructed rounded Householder GQR
    record with the matching reversed-panel transformed RHS.

    The first layer constructs concrete `DeltaA`, `DeltaB`, and `Deltab` from
    the rounded `Bᵀ` and reversed-`A Q₂` Householder panels.  Under the remaining
    nonzero diagonal conditions on that constructed GQR record, this theorem
    adds the triangular-solve backward-error layer and returns a
    `Theorem20_10PartAPerturbationCertificate` for the already perturbed source
    `(A + DeltaA, B + DeltaB, b + Deltab)`.  Combining this second layer back
    into a single original-source perturbation remains a separate bound
    composition step. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          ∃ (DeltaS : Fin p → Fin p → ℝ)
            (DeltaL22 : Fin q → Fin q → ℝ),
            (∀ i j, |DeltaS i j| ≤ gamma fp p * |hpert.S i j|) ∧
            (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |hpert.L22 i j|) ∧
            frobNormRect DeltaS ≤ gamma fp p * frobNormRect hpert.S ∧
            frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect hpert.L22 ∧
            Nonempty
              (Theorem20_10PartAPerturbationCertificate
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j)
                (fun i => b i + Deltab i) d
                (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
                (gamma fp q) (gamma fp p))) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail
      fp A B b hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail⟩
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hvalidS : gammaValid fp p := by
    exact gammaValid_mono fp
      (Nat.le_mul_of_pos_right p hKB_pos) hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
    le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hvalidL22 : gammaValid fp q :=
    gammaValid_mono fp hidxA_ge_q hvalidA
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidS
  have hgammaq_nonneg : 0 ≤ gamma fp q := gamma_nonneg fp hvalidL22
  refine
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, ?_, ?_⟩
  · intro j
    exact hb_tail j
  · intro hSdiag hL22diag
    rcases
      theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_source_bounds_transformed_tail
        fp hpert beta (fun i => b i + Deltab i) d
        (gamma fp q) (gamma fp p) (0 : Fin (r + q) → ℝ)
        hgammap_nonneg (le_rfl : gamma fp q ≤ gamma fp q)
        (le_rfl : gamma fp p ≤ gamma fp p)
        hSdiag hL22diag hvalid2S hvalid2L22 with
      ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
        hDeltaSfrob, hDeltaL22frob, hcert⟩
    have hDeltab0 :
        vecNorm2 (0 : Fin (r + q) → ℝ) ≤
          gamma fp q * vecNorm2 (fun i : Fin (r + q) => b i + Deltab i) := by
      change vecNorm2 (fun _ : Fin (r + q) => 0) ≤
        gamma fp q * vecNorm2 (fun i : Fin (r + q) => b i + Deltab i)
      rw [vecNorm2_zero]
      exact mul_nonneg hgammaq_nonneg
        (vecNorm2_nonneg (fun i : Fin (r + q) => b i + Deltab i))
    have hb_tail0 : ∀ i : Fin q,
        matMulVec (r + q) (matTranspose hpert.U)
            (fun k => (b k + Deltab k) + (0 : Fin (r + q) → ℝ) k)
            (Fin.natAdd r i) =
          beta i := by
      intro i
      simpa using hb_tail i
    exact
      ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
        hDeltaSfrob, hDeltaL22frob, hcert hDeltab0 hb_tail0⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    original-source Part A certificate for the constructed rounded Householder
    GQR record with the matching reversed-panel transformed RHS.

    This composes the concrete Householder perturbation layer with the
    triangular-solve perturbation layer.  The final source coefficients are
    supplied by explicit dominance hypotheses, leaving the remaining work as
    constant simplification/rank preservation rather than a hidden second
    perturbation layer. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal_composed
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (gammaA gammaB : ℝ)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaA_matrix :
      theorem20_10_householder_gammaA fp r p q +
          gamma fp q * (1 + theorem20_10_householder_gammaA fp r p q) ≤
        gammaA)
    (hgammaA_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q +
          gamma fp q *
            (1 + theorem20_10_householder_rhs_conservative_gamma fp r p q) ≤
        gammaA)
    (hgammaB_matrix :
      theorem20_10_householder_gammaB fp r p q +
          gamma fp p * (1 + theorem20_10_householder_gammaB fp r p q) ≤
        gammaB) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          Nonempty
            (Theorem20_10PartAPerturbationCertificate A B b d
              (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
              gammaA gammaB)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail, hdiag_cert⟩
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hvalidS : gammaValid fp p := by
    exact gammaValid_mono fp
      (Nat.le_mul_of_pos_right p hKB_pos) hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
    le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hvalidL22 : gammaValid fp q :=
    gammaValid_mono fp hidxA_ge_q hvalidA
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidS
  have hgammaq_nonneg : 0 ≤ gamma fp q := gamma_nonneg fp hvalidL22
  have hgammaB0_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hgammaB_solution : gamma fp p ≤ gammaB := by
    have hpre :
        gamma fp p ≤
          theorem20_10_householder_gammaB fp r p q +
            gamma fp p * (1 + theorem20_10_householder_gammaB fp r p q) := by
      nlinarith [hgammap_nonneg, hgammaB0_nonneg]
    exact le_trans hpre hgammaB_matrix
  refine
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro hSdiag hL22diag
  rcases hdiag_cert hSdiag hL22diag with
    ⟨_DeltaS, _DeltaL22, _hDeltaSbound, _hDeltaL22bound,
      _hDeltaSfrob, _hDeltaL22frob, hcert⟩
  exact
    theorem20_10_nonempty_partA_certificate_compose_source_perturbations
      A B b d (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
      DeltaA DeltaB Deltab hgammaq_nonneg hgammap_nonneg
      hDeltaA hDeltaB hDeltab
      hgammaA_matrix hgammaA_rhs hgammaB_matrix hgammaB_solution hcert
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    constructed rounded Householder GQR Part A certificate with named
    conservative composed coefficients.

    This specializes
    `theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal_composed`
    to the local composite `gamma` budgets, removing the caller-facing
    dominance hypotheses.  The theorem is still conditional on the constructed
    perturbed `S` and `L22` nonzero diagonals. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          Nonempty
            (Theorem20_10PartAPerturbationCertificate A B b d
              (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
              (theorem20_10_householder_composed_partA_gammaA fp r p q)
              (theorem20_10_householder_composed_partA_gammaB fp r p q))) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal_composed
      fp A B b d hp hq
      (theorem20_10_householder_composed_partA_gammaA fp r p q)
      (theorem20_10_householder_composed_partA_gammaB fp r p q)
      hvalidA hvalidB hhalf
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_left _ _)
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_right _ _)
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaB]
        exact le_rfl)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(a):
    constructed rounded Householder GQR Part A mixed-stability core with named
    conservative composed coefficients.

    This unwraps the constructed original-source Part A certificate through the
    generic mixed-stability certificate handoff.  Under the remaining
    nonzero-diagonal branch, it exposes the `DeltaX` relation between the
    computed transformed-tail vector and an exact minimizer of the perturbed
    source problem. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_mixed_stability_of_diagonal_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ DeltaX : Fin (p + q) → ℝ,
          ∃ x : Fin (p + q) → ℝ,
            (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
            vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j) d x ∧
            (∃ hcore : GeneralizedQRFactorization r p q
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
              (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
                rectMatMulVec hcore.S yz.1 = d ∧
                rectMatMulVec hcore.L22 yz.2 =
                  (fun i : Fin q =>
                    matMulVec (r + q) (matTranspose hcore.U)
                      (fun i => b i + Deltab i) (Fin.natAdd r i) -
                      rectMatMulVec hcore.L21 yz.1 i) ∧
                IsLSEMinimizer
                  (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i)
                  (fun i j => B i j + DeltaB i j) d
                  (matMulVec (p + q) hcore.Q (Fin.append yz.1 yz.2))) ∧
              (∃! x0 : Fin (p + q) → ℝ,
                IsLSEMinimizer
                  (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i)
                  (fun i j => B i j + DeltaB i j) d x0))) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0, hDeltab0,
      hpert, hQeq, hSeq, hb_tail, hcertA⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro hSdiag hL22diag
  rcases hcertA hSdiag hL22diag with ⟨cert⟩
  have hcore :=
    theorem20_10_partA_mixed_stability_of_perturbation_certificate
      A B b d (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
      cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x, hDeltaAeq, hDeltaBeq,
      hDeltabeq, hxhat, hDeltaX, hDeltaA, hDeltab, hDeltaB, hx,
      hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x, hxhat, hDeltaX,
      ?_, ?_, ?_, hx, hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltaBeq] using hDeltaB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    rank obstruction for the rounded Householder perturbed GQR record.

    After `theorem20_10_householder_constructed_perturbed_gqr_factorization`
    constructs the concrete perturbed GQR record, the remaining perturbed source
    rank assumptions are exactly the nonzero diagonal conditions on that record's
    `S` and `L22` blocks. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_rank_iff_diagonal
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        ((LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
          LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA i j)
            (fun i j => B i j + DeltaB i j)) ↔
          (∀ i : Fin p, hpert.S i i ≠ 0) ∧
            (∀ i : Fin q, hpert.L22 i i ≠ 0)) := by
  dsimp
  rcases theorem20_10_householder_constructed_perturbed_gqr_factorization
      fp A B hp hq hvalidA hvalidB with
    ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB, hpert, hQeq, hSeq⟩
  exact
    ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB, hpert, hQeq, hSeq,
      hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    exact method handoff for the rounded Householder perturbed GQR record.

    The concrete `Bᵀ` and reversed `A Q₂` Householder perturbations construct a
    genuine GQR factorization for `(A + DeltaA, B + DeltaB)`.  If the resulting
    triangular blocks keep nonzero diagonals, the exact GQR triangular systems
    have unique coordinates and the perturbed equality-constrained least-squares
    problem has a unique minimizer.  Thus the remaining rank-preservation
    obligation is isolated to the displayed diagonal conditions for the
    constructed record. -/
theorem theorem20_10_householder_constructed_perturbed_gqr_exact_method_of_diagonal
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
            rectMatMulVec hpert.S yz.1 = d ∧
            rectMatMulVec hpert.L22 yz.2 =
              (fun i : Fin q =>
                matMulVec (r + q) (matTranspose hpert.U) b (Fin.natAdd r i) -
                  rectMatMulVec hpert.L21 yz.1 i) ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j) b
              (fun i j => B i j + DeltaB i j) d
              (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j) b
              (fun i j => B i j + DeltaB i j) d x)) := by
  dsimp
  rcases theorem20_10_householder_constructed_perturbed_gqr_factorization
      fp A B hp hq hvalidA hvalidB with
    ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB, hpert, hQeq, hSeq⟩
  refine
    ⟨DeltaA, DeltaB, hDeltaBrep, hDeltaA, hDeltaB, hpert, hQeq, hSeq, ?_⟩
  intro hSdiag hL22diag
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).2
      ⟨hSdiag, hL22diag⟩
  exact
    ⟨hpert.exists_unique_solve_coordinates_of_fullRowRank_stackedFullColumnRank
        (b := b) (d := d) hrank.1 hrank.2,
      hpert.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
        (b := b) (d := d) hrank.1 hrank.2⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    a constraint-matrix perturbation gives the corresponding constraint
    right-hand-side perturbation at a proposed computed vector.

    Taking `Deltad = DeltaB * xhat` gives the exact action identity for
    `(B + DeltaB) xhat` and the displayed Frobenius/vector norm bound used in
    the backward-error branch. -/
theorem theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
    {p q : ℕ}
    (B DeltaB : Fin p → Fin (p + q) → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaB : ℝ}
    (hDeltaB : frobNormRect DeltaB ≤ gammaB * frobNormRect B) :
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat := by
  refine ⟨rectMatMulVec DeltaB xhat, ?_, ?_⟩
  · intro i
    unfold rectMatMulVec
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · exact le_trans
      (vecNorm2_rectMatMulVec_le_frobNormRect_mul DeltaB xhat)
      (mul_le_mul_of_nonneg_right hDeltaB (vecNorm2_nonneg xhat))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), Part A certificate to
    Part B certificate bridge.

    A Part A mixed-stability certificate already supplies the source-shaped
    `DeltaA`, `DeltaB`, and `Deltab` bounds and the perturbed rank hypotheses.
    For the Part B backward-error certificate, the only additional perturbation
    component is the constraint right-hand side.  Taking
    `Deltad = DeltaB * xhat` gives the required source-shaped `Deltad` bound;
    the `Deltab` bound is weakened by adding the nonnegative
    `gammaB * ||A||_F * ||xhat||_2` term from the Part B statement. -/
theorem theorem20_10_partB_certificate_of_partA_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (hgammaB_nonneg : 0 ≤ gammaB)
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat gammaA gammaB) :
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + cert.DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      Nonempty
        (Theorem20_10PartBPerturbationCertificate A B b d xhat
          gammaA gammaB) := by
  rcases theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
      B cert.DeltaB xhat cert.hDeltaB with
    ⟨Deltad, hDeltad_action, hDeltad⟩
  have htail_nonneg :
      0 ≤ gammaB * frobNormRect A * vecNorm2 xhat := by
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg A))
      (vecNorm2_nonneg xhat)
  have hDeltab :
      vecNorm2 cert.Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat :=
    le_trans cert.hDeltab (le_add_of_nonneg_right htail_nonneg)
  refine ⟨Deltad, hDeltad_action, hDeltad, ?_⟩
  exact
    ⟨{ DeltaA := cert.DeltaA
       DeltaB := cert.DeltaB
       Deltab := cert.Deltab
       Deltad := Deltad
       hB := cert.hB
       hstack := cert.hstack
       hDeltaA := cert.hDeltaA
       hDeltaB := cert.hDeltaB
       hDeltab := hDeltab
       hDeltad := hDeltad }⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), Part A certificate to
    exact Part B backward-error core.

    This skips the intermediate Part B certificate object for callers that
    already have a Part A mixed-stability certificate.  The constraint
    right-hand-side perturbation is the explicit action `Deltad = DeltaB*xhat`,
    and the exact perturbed GQR/minimizer package is obtained directly for
    the problem with right-hand side `d + Deltad`. -/
theorem theorem20_10_partB_backward_error_of_partA_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (hgammaB_nonneg : 0 ≤ gammaB)
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat gammaA gammaB) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec Bpert xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect cert.DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect cert.DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 cert.Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U) bpert (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
      B cert.DeltaB xhat cert.hDeltaB with
    ⟨Deltad, hDeltad_action, hDeltad⟩
  have htail_nonneg :
      0 ≤ gammaB * frobNormRect A * vecNorm2 xhat := by
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg A))
      (vecNorm2_nonneg xhat)
  have hDeltab :
      vecNorm2 cert.Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat :=
    le_trans cert.hDeltab (le_add_of_nonneg_right htail_nonneg)
  refine
    ⟨Deltad, hDeltad_action, cert.hDeltaA, cert.hDeltaB, hDeltab,
      hDeltad, ?_⟩
  exact
    GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
      A cert.DeltaA B cert.DeltaB b cert.Deltab d Deltad cert.hB cert.hstack
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), nonempty Part A
    certificate to exact Part B backward-error core.

    This is the certificate-free form for routes that produce a nonempty
    Part A certificate package.  It returns concrete perturbations, records
    the constraint right-hand-side action identity for `Deltad`, and exposes
    the exact perturbed GQR/minimizer core for the Part B problem. -/
theorem theorem20_10_partB_backward_error_of_nonempty_partA_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hcert :
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d xhat
          gammaA gammaB)) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  rcases hcert with ⟨cert⟩
  rcases theorem20_10_partB_backward_error_of_partA_certificate
      A B b d xhat hgammaB_nonneg cert with
    ⟨Deltad, hDeltad_action, hDeltaA, hDeltaB, hDeltab,
      hDeltad, hmethod⟩
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, Deltad,
      hDeltad_action, hDeltaA, hDeltaB, hDeltab, hDeltad, hmethod⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), nonempty Part A
    certificate to nonempty Part B certificate bridge.

    This is the form consumed by constructed-source certificate theorems, which
    usually return `Nonempty` certificates. -/
theorem theorem20_10_partB_certificate_of_nonempty_partA_certificate
    {r p q : ℕ}
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    {gammaA gammaB : ℝ}
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hcert :
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d xhat
          gammaA gammaB)) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d xhat
        gammaA gammaB) := by
  rcases hcert with ⟨cert⟩
  rcases theorem20_10_partB_certificate_of_partA_certificate
      A B b d xhat hgammaB_nonneg cert with
    ⟨_Deltad, _hDeltad_action, _hDeltad, hcertB⟩
  exact hcertB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B certificate with named
    conservative composed coefficients.

    This pushes the composed Part A certificate through the generic Part A to
    Part B bridge.  It keeps the concrete rounded `Bᵀ`/reversed-`A Q₂`
    perturbation witnesses and the remaining nonzero-diagonal branch visible. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_certificate_of_diagonal_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          Nonempty
            (Theorem20_10PartBPerturbationCertificate A B b d
              (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
              (theorem20_10_householder_composed_partA_gammaA fp r p q)
              (theorem20_10_householder_composed_partA_gammaB fp r p q))) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partA_certificate_of_diagonal_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail, hcertA⟩
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hvalidS : gammaValid fp p := by
    exact gammaValid_mono fp
      (Nat.le_mul_of_pos_right p hKB_pos) hvalidB
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidS
  have hgammaB0_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_composed_partA_gammaB fp r p q := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    have hone_plus :
        0 ≤ 1 + theorem20_10_householder_gammaB fp r p q := by
      nlinarith [hgammaB0_nonneg]
    exact add_nonneg hgammaB0_nonneg
      (mul_nonneg hgammap_nonneg hone_plus)
  refine
    ⟨DeltaA, DeltaB, Deltab, hDeltaBrep, hDeltaA, hDeltaB, hDeltab,
      hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro hSdiag hL22diag
  exact
    theorem20_10_partB_certificate_of_nonempty_partA_certificate
      A B b d (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
      hgammaB_nonneg (hcertA hSdiag hL22diag)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B exact core with named
    conservative composed coefficients.

    This unwraps the constructed reversed-RHS Part B certificate through the
    generic certificate-to-core theorem.  The remaining nonzero-diagonal branch
    is still explicit; deriving it from source rank hypotheses and identifying
    the final returned computed vector remain the next computed-GQR tasks. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_backward_error_of_diagonal_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ Deltad : Fin p → ℝ,
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            vecNorm2 Deltab ≤
              gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
            vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
            (∃ hcore : GeneralizedQRFactorization r p q
                (fun i j => A i j + DeltaA i j)
                (fun i j => B i j + DeltaB i j),
              (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
                rectMatMulVec hcore.S yz.1 = (fun i => d i + Deltad i) ∧
                rectMatMulVec hcore.L22 yz.2 =
                  (fun i : Fin q =>
                    matMulVec (r + q) (matTranspose hcore.U)
                      (fun i => b i + Deltab i) (Fin.natAdd r i) -
                      rectMatMulVec hcore.L21 yz.1 i) ∧
                IsLSEMinimizer
                  (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i)
                  (fun i j => B i j + DeltaB i j)
                  (fun i => d i + Deltad i)
                  (matMulVec (p + q) hcore.Q (Fin.append yz.1 yz.2))) ∧
              (∃! x : Fin (p + q) → ℝ,
                IsLSEMinimizer
                  (fun i j => A i j + DeltaA i j)
                  (fun i => b i + Deltab i)
                  (fun i j => B i j + DeltaB i j)
                  (fun i => d i + Deltad i) x))) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_certificate_of_diagonal_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0, hDeltab0,
      hpert, hQeq, hSeq, hb_tail, hcertB⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro hSdiag hL22diag
  rcases hcertB hSdiag hL22diag with ⟨cert⟩
  have hcore :=
    theorem20_10_partB_backward_error_of_perturbation_certificate
      A B b d (theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d)
      cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaAeq, hDeltaBeq,
      hDeltabeq, hDeltadeq, hDeltaA, hDeltaB, hDeltab, hDeltad,
      hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, cert.Deltad, ?_, ?_, ?_, ?_,
      hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltaBeq] using hDeltaB
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltadeq] using hDeltad
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B theorem with the returned
    transformed-tail vector identified as the exact perturbed minimizer.

    This is the returned-vector counterpart of
    `theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_backward_error_of_diagonal_composed_conservative_gamma`.
    Under the same constructed nonzero-diagonal branch, it keeps the concrete
    rounded `Bᵀ`/reversed-`A Q₂` path, composes the triangular-solve
    perturbations back to the original source, and chooses `Deltad = 0`.
    Thus the named computed vector itself solves the displayed perturbed LSE
    problem; the remaining full-source gap is still deriving the diagonal
    branch from source rank/smallness hypotheses and sharpening the conservative
    RHS coefficient if required. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_diagonal_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ Deltad : Fin p → ℝ,
            Deltad = (0 : Fin p → ℝ) ∧
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            vecNorm2 Deltab ≤
              gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
            vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) xhat ∧
            (∃! x : Fin (p + q) → ℝ,
              IsLSEMinimizer
                (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i)
                (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_perturbed_gqr_reversed_rhs_tail_triangular_solve_frob_perturbation_bound
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, htri⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro hSdiag hL22diag
  rcases htri hSdiag hL22diag with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeqSolve, hL22Solve, _hxhat_eq⟩
  let Spert : Fin p → Fin p → ℝ := fun i j => hpert.S i j + DeltaS i j
  let L22pert : Fin q → Fin q → ℝ :=
    fun i j => hpert.L22 i j + DeltaL22 i j
  let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
    gqrSourceAFromBlocks hpert.Q hpert.U hpert.L11 hpert.L21 L22pert
  let Bpert : Fin p → Fin (p + q) → ℝ :=
    gqrSourceBFromBlocks hpert.Q Spert
  let DeltaA2 : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => Apert i j - (A i j + DeltaA0 i j)
  let DeltaB2 : Fin p → Fin (p + q) → ℝ :=
    fun i j => Bpert i j - (B i j + DeltaB0 i j)
  let DeltaA : Fin (r + q) → Fin (p + q) → ℝ :=
    fun i j => Apert i j - A i j
  let DeltaB : Fin p → Fin (p + q) → ℝ :=
    fun i j => Bpert i j - B i j
  let Deltab : Fin (r + q) → ℝ := Deltab0
  let Deltad : Fin p → ℝ := fun _ => 0
  let xhat : Fin (p + q) → ℝ :=
    theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hvalidS : gammaValid fp p := by
    exact gammaValid_mono fp
      (Nat.le_mul_of_pos_right p hKB_pos) hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
    le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hvalidL22 : gammaValid fp q :=
    gammaValid_mono fp hidxA_ge_q hvalidA
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammap_nonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidS
  have hgammaq_nonneg : 0 ≤ gamma fp q := gamma_nonneg fp hvalidL22
  have hgammaA0_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hgammaB0_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidx_rhs_le :
      q * householderConstructApplyGammaIndex (r + q) ≤
        (p + q) * householderConstructApplyGammaIndex (r + q) :=
    Nat.mul_le_mul_right _ (by omega)
  have hvalid_rhs :
      gammaValid fp
        (q * householderConstructApplyGammaIndex (r + q)) :=
    gammaValid_mono fp hidx_rhs_le hvalidA
  have hrhs_nonneg :
      0 ≤ theorem20_10_householder_rhs_conservative_gamma fp r p q := by
    have hfactor_nonneg :
        0 ≤ (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) := by
      positivity
    have hgamma_nonneg :
        0 ≤ gamma fp (q * householderConstructApplyGammaIndex (r + q)) :=
      gamma_nonneg fp hvalid_rhs
    dsimp [theorem20_10_householder_rhs_conservative_gamma]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num) hfactor_nonneg) hgamma_nonneg)
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_composed_partA_gammaB fp r p q := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    have hone_plus :
        0 ≤ 1 + theorem20_10_householder_gammaB fp r p q := by
      nlinarith [hgammaB0_nonneg]
    exact add_nonneg hgammaB0_nonneg
      (mul_nonneg hgammap_nonneg hone_plus)
  have hSpert_lower : IsLowerTriangular Spert := by
    dsimp [Spert]
    exact hpert.lowerS.add_of_entrywise_abs_le_mul_abs hDeltaSbound
  have hL22pert_lower : IsLowerTriangular L22pert := by
    dsimp [L22pert]
    exact hpert.lowerL22.add_of_entrywise_abs_le_mul_abs hDeltaL22bound
  have hSpert_diag : ∀ i : Fin p, Spert i i ≠ 0 := by
    dsimp [Spert]
    exact diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hSdiag (gamma_lt_one fp p hvalid2S) hDeltaSbound
  have hL22pert_diag : ∀ i : Fin q, L22pert i i ≠ 0 := by
    dsimp [L22pert]
    exact diag_ne_zero_add_of_entrywise_abs_le_mul_abs_of_factor_lt_one
      hL22diag (gamma_lt_one fp q hvalid2L22) hDeltaL22bound
  let hcore : GeneralizedQRFactorization r p q Apert Bpert :=
    GeneralizedQRFactorization.of_source_blocks
      hpert.Q hpert.U hpert.L11 hpert.L21 L22pert Spert
      hpert.orthQ hpert.orthU hL22pert_lower hSpert_lower
  have hrank_min :
      LSEFullRowRank Bpert ∧
        LSEStackedFullColumnRank Apert Bpert ∧
          IsLSEMinimizer Apert (fun i => b i + Deltab0 i) Bpert d xhat := by
    simpa [hcore, xhat, Spert, L22pert] using
      theorem20_10_gqr_xhat_of_transformed_tail_rank_and_minimizer_of_supplied_perturbed_triangular_factors
        fp hpert hcore beta d (fun i => b i + Deltab0 i) d DeltaS DeltaL22
        rfl rfl rfl rfl rfl hb_tail hSpert_diag hL22pert_diag
        hSeqSolve hL22Solve
  have huniq_core :
      ∃! x : Fin (p + q) → ℝ,
        IsLSEMinimizer Apert (fun i => b i + Deltab0 i) Bpert d x :=
    hcore.exists_unique_lse_minimizer_of_fullRowRank_stackedFullColumnRank
      (b := fun i => b i + Deltab0 i) (d := d) hrank_min.1
      hrank_min.2.1
  have hApert_src :
      (fun i j => A i j + DeltaA i j) = Apert := by
    ext i j
    dsimp [DeltaA]
    ring
  have hBpert_src :
      (fun i j => B i j + DeltaB i j) = Bpert := by
    ext i j
    dsimp [DeltaB]
    ring
  have hdpert_src :
      (fun i => d i + Deltad i) = d := by
    ext i
    simp [Deltad]
  have hxhat_min :
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j)
        (fun i => d i + Deltad i) xhat := by
    rw [hApert_src, hBpert_src, hdpert_src]
    simpa [Deltab] using hrank_min.2.2
  have huniq_final :
      ∃! x : Fin (p + q) → ℝ,
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) x := by
    rw [hApert_src, hBpert_src, hdpert_src]
    simpa [Deltab] using huniq_core
  have hA0_norm :
      frobNormRect (fun i j => A i j + DeltaA0 i j) ≤
        (1 + theorem20_10_householder_gammaA fp r p q) * frobNormRect A := by
    calc
      frobNormRect (fun i j => A i j + DeltaA0 i j)
          ≤ frobNormRect A + frobNormRect DeltaA0 :=
            frobNormRect_add_le A DeltaA0
      _ ≤ frobNormRect A +
            theorem20_10_householder_gammaA fp r p q * frobNormRect A :=
            add_le_add_right hDeltaA0 (frobNormRect A)
      _ = (1 + theorem20_10_householder_gammaA fp r p q) *
            frobNormRect A := by ring
  have hDeltaA2 :
      frobNormRect DeltaA2 ≤
        gamma fp q *
          frobNormRect (fun i j => A i j + DeltaA0 i j) := by
    simpa [DeltaA2, Apert, L22pert] using
      hpert.constructed_sourceA_L22_perturbation_frobNorm_bound
        (gamma fp q) DeltaL22 hgammaq_nonneg hDeltaL22frob
  have hDeltaA2_source :
      frobNormRect DeltaA2 ≤
        gamma fp q *
          ((1 + theorem20_10_householder_gammaA fp r p q) *
            frobNormRect A) :=
    le_trans hDeltaA2
      (mul_le_mul_of_nonneg_left hA0_norm hgammaq_nonneg)
  have hDeltaA_sum :
      DeltaA = fun i j => DeltaA0 i j + DeltaA2 i j := by
    ext i j
    dsimp [DeltaA, DeltaA2]
    ring
  have hDeltaA_pre :
      frobNormRect DeltaA ≤
        (theorem20_10_householder_gammaA fp r p q +
            gamma fp q *
              (1 + theorem20_10_householder_gammaA fp r p q)) *
          frobNormRect A := by
    calc
      frobNormRect DeltaA =
          frobNormRect (fun i j => DeltaA0 i j + DeltaA2 i j) := by
            rw [hDeltaA_sum]
      _ ≤ frobNormRect DeltaA0 + frobNormRect DeltaA2 :=
            frobNormRect_add_le DeltaA0 DeltaA2
      _ ≤ theorem20_10_householder_gammaA fp r p q * frobNormRect A +
            gamma fp q *
              ((1 + theorem20_10_householder_gammaA fp r p q) *
                frobNormRect A) :=
            add_le_add hDeltaA0 hDeltaA2_source
      _ = (theorem20_10_householder_gammaA fp r p q +
            gamma fp q *
              (1 + theorem20_10_householder_gammaA fp r p q)) *
          frobNormRect A := by ring
  have hDeltaA :
      frobNormRect DeltaA ≤
        theorem20_10_householder_composed_partA_gammaA fp r p q *
          frobNormRect A := by
    exact le_trans hDeltaA_pre
      (mul_le_mul_of_nonneg_right
        (by
          dsimp [theorem20_10_householder_composed_partA_gammaA]
          exact le_max_left _ _)
        (frobNormRect_nonneg A))
  have hB0_norm :
      frobNormRect (fun i j => B i j + DeltaB0 i j) ≤
        (1 + theorem20_10_householder_gammaB fp r p q) * frobNormRect B := by
    calc
      frobNormRect (fun i j => B i j + DeltaB0 i j)
          ≤ frobNormRect B + frobNormRect DeltaB0 :=
            frobNormRect_add_le B DeltaB0
      _ ≤ frobNormRect B +
            theorem20_10_householder_gammaB fp r p q * frobNormRect B :=
            add_le_add_right hDeltaB0 (frobNormRect B)
      _ = (1 + theorem20_10_householder_gammaB fp r p q) *
            frobNormRect B := by ring
  have hDeltaB2 :
      frobNormRect DeltaB2 ≤
        gamma fp p *
          frobNormRect (fun i j => B i j + DeltaB0 i j) := by
    simpa [DeltaB2, Bpert, Spert] using
      hpert.constructed_sourceB_perturbation_frobNorm_bound
        (gamma fp p) DeltaS hDeltaSfrob
  have hDeltaB2_source :
      frobNormRect DeltaB2 ≤
        gamma fp p *
          ((1 + theorem20_10_householder_gammaB fp r p q) *
            frobNormRect B) :=
    le_trans hDeltaB2
      (mul_le_mul_of_nonneg_left hB0_norm hgammap_nonneg)
  have hDeltaB_sum :
      DeltaB = fun i j => DeltaB0 i j + DeltaB2 i j := by
    ext i j
    dsimp [DeltaB, DeltaB2]
    ring
  have hDeltaB :
      frobNormRect DeltaB ≤
        theorem20_10_householder_composed_partA_gammaB fp r p q *
          frobNormRect B := by
    have hpre :
        frobNormRect DeltaB ≤
          (theorem20_10_householder_gammaB fp r p q +
              gamma fp p *
                (1 + theorem20_10_householder_gammaB fp r p q)) *
            frobNormRect B := by
      calc
        frobNormRect DeltaB =
            frobNormRect (fun i j => DeltaB0 i j + DeltaB2 i j) := by
              rw [hDeltaB_sum]
        _ ≤ frobNormRect DeltaB0 + frobNormRect DeltaB2 :=
              frobNormRect_add_le DeltaB0 DeltaB2
        _ ≤ theorem20_10_householder_gammaB fp r p q * frobNormRect B +
              gamma fp p *
                ((1 + theorem20_10_householder_gammaB fp r p q) *
                  frobNormRect B) :=
              add_le_add hDeltaB0 hDeltaB2_source
        _ = (theorem20_10_householder_gammaB fp r p q +
              gamma fp p *
                (1 + theorem20_10_householder_gammaB fp r p q)) *
            frobNormRect B := by ring
    simpa [theorem20_10_householder_composed_partA_gammaB] using hpre
  have hrhs_le_gammaA :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
        theorem20_10_householder_composed_partA_gammaA fp r p q := by
    have hterm_nonneg :
        0 ≤ gamma fp q *
          (1 + theorem20_10_householder_rhs_conservative_gamma fp r p q) := by
      have hone_plus :
          0 ≤ 1 + theorem20_10_householder_rhs_conservative_gamma fp r p q := by
        nlinarith [hrhs_nonneg]
      exact mul_nonneg hgammaq_nonneg hone_plus
    have hpre :
        theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
          theorem20_10_householder_rhs_conservative_gamma fp r p q +
            gamma fp q *
              (1 + theorem20_10_householder_rhs_conservative_gamma fp r p q) :=
      le_add_of_nonneg_right hterm_nonneg
    exact le_trans hpre
      (by
        dsimp [theorem20_10_householder_composed_partA_gammaA]
        exact le_max_right _ _)
  have hDeltab :
      vecNorm2 Deltab ≤
        theorem20_10_householder_composed_partA_gammaA fp r p q *
          vecNorm2 b := by
    exact le_trans hDeltab0
      (mul_le_mul_of_nonneg_right hrhs_le_gammaA (vecNorm2_nonneg b))
  have htail_nonneg :
      0 ≤ theorem20_10_householder_composed_partA_gammaB fp r p q *
        frobNormRect A * vecNorm2 xhat := by
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg A))
      (vecNorm2_nonneg xhat)
  have hDeltab_partB :
      vecNorm2 Deltab ≤
        theorem20_10_householder_composed_partA_gammaA fp r p q *
            vecNorm2 b +
          theorem20_10_householder_composed_partA_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat :=
    le_trans hDeltab (le_add_of_nonneg_right htail_nonneg)
  have hDeltad :
      vecNorm2 Deltad ≤
        theorem20_10_householder_composed_partA_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat := by
    change vecNorm2 (fun _ : Fin p => 0) ≤
      theorem20_10_householder_composed_partA_gammaB fp r p q *
        frobNormRect B * vecNorm2 xhat
    rw [vecNorm2_zero]
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg B))
      (vecNorm2_nonneg xhat)
  exact
    ⟨DeltaA, DeltaB, Deltab, Deltad, rfl, hDeltaA, hDeltaB,
      hDeltab_partB, hDeltad, hxhat_min, huniq_final⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B theorem with the returned
    transformed-tail vector identified under perturbed rank assumptions.

    This is the rank-surface wrapper for
    `theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_diagonal_composed_conservative_gamma`.
    The constructed GQR record already proves that perturbed full row rank and
    stacked full column rank are equivalent to nonzero diagonals of its `S` and
    `L22` blocks, so callers can now supply the natural perturbed-rank
    hypotheses instead of the lower-level diagonal branch. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_perturbed_rank_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        ((LSEFullRowRank (fun i j => B i j + DeltaB0 i j) ∧
          LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA0 i j)
            (fun i j => B i j + DeltaB0 i j)) →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ Deltad : Fin p → ℝ,
            Deltad = (0 : Fin p → ℝ) ∧
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            vecNorm2 Deltab ≤
              gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
            vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) xhat ∧
            (∃! x : Fin (p + q) → ℝ,
              IsLSEMinimizer
                (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i)
                (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_diagonal_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hdiag_branch⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro hrank
  have hdiag :
      (∀ i : Fin p, hpert.S i i ≠ 0) ∧
        (∀ i : Fin q, hpert.L22 i i ≠ 0) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1 hrank
  exact hdiag_branch hdiag.1 hdiag.2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B theorem with stacked-rank
    preservation derived from a source lower-bound margin.

    Compared with
    `theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_perturbed_rank_composed_conservative_gamma`,
    this theorem removes the direct perturbed stacked-full-column-rank
    hypothesis from the branch.  Callers may instead supply a lower bound for
    the exact source stack `[A; B]` and an operator-2 bound on the constructed
    stacked perturbation whose radius is strictly below that margin. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_stacked_lower_bound_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        (∀ {mu eta : ℝ},
          LSEFullRowRank (fun i j => B i j + DeltaB0 i j) →
          (∀ x : Fin (p + q) → ℝ,
            mu * vecNorm2 x ≤ vecNorm2 (rectMatMulVec (lseStackedMatrix A B) x)) →
          rectOpNorm2Le (lseStackedMatrix DeltaA0 DeltaB0) eta →
          eta < mu →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ Deltad : Fin p → ℝ,
            Deltad = (0 : Fin p → ℝ) ∧
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            vecNorm2 Deltab ≤
              gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
            vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) xhat ∧
            (∃! x : Fin (p + q) → ℝ,
              IsLSEMinimizer
                (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i)
                (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_perturbed_rank_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hrank_branch⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro mu eta hB hlower hDeltaStack heta
  have hstack :
      LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA0 i j)
        (fun i j => B i j + DeltaB0 i j) :=
    LSEStackedFullColumnRank.of_lower_bound_and_rectOpNorm2Le_lt
      (A := A) (DeltaA := DeltaA0)
      (B := B) (DeltaB := DeltaB0)
      hlower hDeltaStack heta
  exact hrank_branch ⟨hB, hstack⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B theorem whose rank branch is
    expressed only through quantitative source lower bounds and strict
    perturbation-size hypotheses.

    This combines the full-row-rank preservation bridge for `Bᵀ` with the
    stacked-rank preservation bridge for `[A; B]`.  The branch no longer asks
    callers to provide either perturbed rank predicate directly; it remains
    conditional on instantiating the source lower-bound margins and operator-2
    perturbation bounds for the concrete constructed perturbations. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_rank_lower_bounds_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        (∀ {muB etaB muStack etaStack : ℝ},
          (∀ y : Fin p → ℝ,
            muB * vecNorm2 y ≤
              vecNorm2
                (rectMatMulVec
                  (fun j : Fin (p + q) => fun i : Fin p => B i j) y)) →
          rectOpNorm2Le
            (fun j : Fin (p + q) => fun i : Fin p => DeltaB0 i j) etaB →
          etaB < muB →
          (∀ x : Fin (p + q) → ℝ,
            muStack * vecNorm2 x ≤
              vecNorm2 (rectMatMulVec (lseStackedMatrix A B) x)) →
          rectOpNorm2Le (lseStackedMatrix DeltaA0 DeltaB0) etaStack →
          etaStack < muStack →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ Deltad : Fin p → ℝ,
            Deltad = (0 : Fin p → ℝ) ∧
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            vecNorm2 Deltab ≤
              gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
            vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) xhat ∧
            (∃! x : Fin (p + q) → ℝ,
              IsLSEMinimizer
                (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i)
                (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_stacked_lower_bound_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hstack_branch⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro muB etaB muStack etaStack hBLower hBDelta hBEta
    hStackLower hStackDelta hStackEta
  have hB :
      LSEFullRowRank (fun i j => B i j + DeltaB0 i j) :=
    LSEFullRowRank.of_transpose_lower_bound_and_rectOpNorm2Le_lt
      (B := B) (DeltaB := DeltaB0) hBLower hBDelta hBEta
  exact hstack_branch hB hStackLower hStackDelta hStackEta
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B theorem with rank preservation
    reduced to source lower bounds dominating the already proved Frobenius
    perturbation budgets.

    The branch no longer exposes either direct perturbed rank predicates or
    separate operator-norm perturbation certificates.  It uses the constructed
    `DeltaA0`/`DeltaB0` Frobenius bounds to instantiate conservative
    operator-2 radii for `DeltaB0ᵀ` and `[DeltaA0; DeltaB0]`; callers supply
    only source lower-bound margins that strictly dominate those radii. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_frobenius_rank_margins_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        (∀ {muB muStack : ℝ},
          (∀ y : Fin p → ℝ,
            muB * vecNorm2 y ≤
              vecNorm2
                (rectMatMulVec
                  (fun j : Fin (p + q) => fun i : Fin p => B i j) y)) →
          theorem20_10_householder_gammaB fp r p q * frobNormRect B < muB →
          (∀ x : Fin (p + q) → ℝ,
            muStack * vecNorm2 x ≤
              vecNorm2 (rectMatMulVec (lseStackedMatrix A B) x)) →
          theorem20_10_householder_gammaA fp r p q * frobNormRect A +
              theorem20_10_householder_gammaB fp r p q * frobNormRect B < muStack →
          let xhat : Fin (p + q) → ℝ :=
            theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
          let gammaA : ℝ :=
            theorem20_10_householder_composed_partA_gammaA fp r p q
          let gammaB : ℝ :=
            theorem20_10_householder_composed_partA_gammaB fp r p q
          ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
          ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
          ∃ Deltab : Fin (r + q) → ℝ,
          ∃ Deltad : Fin p → ℝ,
            Deltad = (0 : Fin p → ℝ) ∧
            frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
            frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
            vecNorm2 Deltab ≤
              gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
            vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) xhat ∧
            (∃! x : Fin (p + q) → ℝ,
              IsLSEMinimizer
                (fun i j => A i j + DeltaA i j)
                (fun i => b i + Deltab i)
                (fun i j => B i j + DeltaB i j)
                (fun i => d i + Deltad i) x)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_rank_lower_bounds_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hrank_branch⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  intro muB muStack hBLower hBMargin hStackLower hStackMargin
  have hDeltaBTransposeFrob :
      frobNormRect (fun j : Fin (p + q) => fun i : Fin p => DeltaB0 i j) ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B := by
    have htrans :
        frobNormRect (finiteTranspose DeltaB0) ≤
          theorem20_10_householder_gammaB fp r p q * frobNormRect B := by
      simpa [frobNormRect_finiteTranspose] using hDeltaB0
    simpa [finiteTranspose] using htrans
  have hDeltaBOp :
      rectOpNorm2Le
        (fun j : Fin (p + q) => fun i : Fin p => DeltaB0 i j)
        (theorem20_10_householder_gammaB fp r p q * frobNormRect B) :=
    rectOpNorm2Le_of_frobNormRect_le
      (fun j : Fin (p + q) => fun i : Fin p => DeltaB0 i j)
      hDeltaBTransposeFrob
  have hStackOp :
      rectOpNorm2Le (lseStackedMatrix DeltaA0 DeltaB0)
        (theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B) :=
    rectOpNorm2Le_lseStackedMatrix_of_frobNormRect_bounds
      hDeltaA0 hDeltaB0
  exact
    hrank_branch hBLower hDeltaBOp hBMargin hStackLower hStackOp hStackMargin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder GQR Part B theorem with rank preservation
    reduced to source rank plus strict smallness against the induced
    finite-dimensional lower-bound margins.

    Compared with the Frobenius rank-margin branch, this theorem derives the
    `Bᵀ` and stacked lower-bound predicates from `LSEFullRowRank B` and
    `LSEStackedFullColumnRank A B`.  The only remaining rank-preservation
    side conditions are strict dominance of the concrete Householder
    Frobenius budgets by those source margins. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_frobenius_margins_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBMargin :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        LSEFullRowRank.transposeVecNorm2LowerMargin hB)
    (hStackMargin :
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        LSEStackedFullColumnRank.vecNorm2LowerMargin hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_frobenius_rank_margins_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hmargin_branch⟩
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, ?_⟩
  exact
    hmargin_branch
      (LSEFullRowRank.transposeVecNorm2LowerMargin_lower_bound hB)
      hBMargin
      (LSEStackedFullColumnRank.vecNorm2LowerMargin_lower_bound hStack)
      hStackMargin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    combined Householder Frobenius budget that controls the rank-preservation
    perturbation radius in the source-rank branch. -/
noncomputable def theorem20_10_householder_sourceRankBudget
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) : ℝ :=
  theorem20_10_householder_gammaA fp r p q * frobNormRect A +
    theorem20_10_householder_gammaB fp r p q * frobNormRect B
/-- Nonnegativity of the combined Householder Frobenius rank budget used in
    the Theorem 20.10(b) source-rank branch. -/
theorem theorem20_10_householder_sourceRankBudget_nonneg
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    0 ≤ theorem20_10_householder_sourceRankBudget fp A B := by
  dsimp [theorem20_10_householder_sourceRankBudget]
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  exact add_nonneg
    (mul_nonneg hgammaA_nonneg (frobNormRect_nonneg A))
    (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg B))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank radius induced by the `Bᵀ` and stacked `[A; B]`
    finite-dimensional lower-bound margins. -/
noncomputable def theorem20_10_householder_sourceRankRadius
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  min (LSEFullRowRank.transposeVecNorm2LowerMargin hB)
    (LSEStackedFullColumnRank.vecNorm2LowerMargin hStack)
/-- Positivity of the noncomputable source-rank radius used in the
    Theorem 20.10(b) source-rank branch. -/
theorem theorem20_10_householder_sourceRankRadius_pos
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) :
    0 < theorem20_10_householder_sourceRankRadius hB hStack := by
  exact lt_min
    (LSEFullRowRank.transposeVecNorm2LowerMargin_pos hB)
    (LSEStackedFullColumnRank.vecNorm2LowerMargin_pos hStack)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    a practical sufficient split of the rank-preservation smallness condition.
    If the `A` and `B` Householder rank budgets are each below half of the
    source-rank radius, then their combined budget satisfies the single
    rank-radius hypothesis used by the returned-vector theorem. -/
theorem theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_half_bounds
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hAhalf :
      theorem20_10_householder_gammaA fp r p q * frobNormRect A <
        theorem20_10_householder_sourceRankRadius hB hStack / 2)
    (hBhalf :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        theorem20_10_householder_sourceRankRadius hB hStack / 2) :
    theorem20_10_householder_sourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  dsimp [theorem20_10_householder_sourceRankBudget]
  nlinarith
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    a compact sufficient condition for the rank-preservation smallness
    hypothesis.  If the larger of the two Householder gamma coefficients times
    `||A||_F + ||B||_F` is below the source-rank radius, then the combined
    Householder rank budget is below that radius. -/
theorem theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    theorem20_10_householder_sourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  dsimp [theorem20_10_householder_sourceRankBudget]
  have hA :
      theorem20_10_householder_gammaA fp r p q * frobNormRect A ≤
        max (theorem20_10_householder_gammaA fp r p q)
            (theorem20_10_householder_gammaB fp r p q) *
          frobNormRect A :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (frobNormRect_nonneg A)
  have hBterm :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B ≤
        max (theorem20_10_householder_gammaA fp r p q)
            (theorem20_10_householder_gammaB fp r p q) *
          frobNormRect B :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (frobNormRect_nonneg B)
  have hbudget_le :
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B ≤
        max (theorem20_10_householder_gammaA fp r p q)
            (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) := by
    calc
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B
          ≤ max (theorem20_10_householder_gammaA fp r p q)
                (theorem20_10_householder_gammaB fp r p q) *
              frobNormRect A +
            max (theorem20_10_householder_gammaA fp r p q)
                (theorem20_10_householder_gammaB fp r p q) *
              frobNormRect B :=
            add_le_add hA hBterm
      _ = max (theorem20_10_householder_gammaA fp r p q)
              (theorem20_10_householder_gammaB fp r p q) *
            (frobNormRect A + frobNormRect B) := by ring
  exact lt_of_le_of_lt hbudget_le hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    positive source-rank gamma threshold for the constructed Householder GQR
    rank-preservation branch.  The `max 1` scale keeps the threshold meaningful
    even when the source Frobenius scale is zero. -/
noncomputable def theorem20_10_householder_sourceRankGammaThreshold
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  theorem20_10_householder_sourceRankRadius hB hStack /
    max (1 : ℝ) (frobNormRect A + frobNormRect B)
/-- Positivity of the source-rank gamma threshold used to state a nonvacuous
    roundoff-smallness condition for Theorem 20.10(b). -/
theorem theorem20_10_householder_sourceRankGammaThreshold_pos
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) :
    0 < theorem20_10_householder_sourceRankGammaThreshold hB hStack := by
  have hRadius : 0 < theorem20_10_householder_sourceRankRadius hB hStack :=
    theorem20_10_householder_sourceRankRadius_pos hB hStack
  have hScale : 0 < max (1 : ℝ) (frobNormRect A + frobNormRect B) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact div_pos hRadius hScale
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the source-rank gamma threshold implies the compact max-gamma product
    smallness condition. -/
theorem theorem20_10_householder_max_gamma_sum_bound_of_max_gamma_lt_sourceRankGammaThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    max (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q) *
        (frobNormRect A + frobNormRect B) <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hgammaMax_nonneg :
      0 ≤ max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) :=
    le_trans hgammaA_nonneg (le_max_left _ _)
  have hScale_pos :
      0 < max (1 : ℝ) (frobNormRect A + frobNormRect B) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hNorm_le_scale :
      frobNormRect A + frobNormRect B ≤
        max (1 : ℝ) (frobNormRect A + frobNormRect B) :=
    le_max_right _ _
  have hscaled :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          max (1 : ℝ) (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack := by
    exact (lt_div_iff₀ hScale_pos).mp
      (by simpa [theorem20_10_householder_sourceRankGammaThreshold]
        using hsmall)
  exact
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hNorm_le_scale hgammaMax_nonneg)
      hscaled
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank budget smallness follows from the positive gamma-threshold
    condition. -/
theorem theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    theorem20_10_householder_sourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  exact
    theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
      fp A B hB hStack
      (theorem20_10_householder_max_gamma_sum_bound_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hB hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative Householder Frobenius budget for the concrete component route.

    This is the source-rank budget after replacing the printed `A` coefficient
    by the verified conservative maximum of the matrix and RHS coefficients. -/
noncomputable def theorem20_10_householder_componentSourceRankBudget
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) : ℝ :=
  theorem20_10_householder_gammaA_conservativeRhs fp r p q * frobNormRect A +
    theorem20_10_householder_gammaB fp r p q * frobNormRect B
/-- Nonnegativity of the conservative Householder component rank budget used
    by the Theorem 20.10(b) source-rank branch. -/
theorem theorem20_10_householder_componentSourceRankBudget_nonneg
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    0 ≤ theorem20_10_householder_componentSourceRankBudget fp A B := by
  dsimp [theorem20_10_householder_componentSourceRankBudget]
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    theorem20_10_householder_gammaA_conservativeRhs_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  exact add_nonneg
    (mul_nonneg hgammaA_nonneg (frobNormRect_nonneg A))
    (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg B))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the printed Householder source-rank budget is dominated by the conservative
    component budget that uses the rounded-RHS `A` coefficient. -/
theorem theorem20_10_householder_sourceRankBudget_le_componentSourceRankBudget
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ) :
    theorem20_10_householder_sourceRankBudget fp A B ≤
      theorem20_10_householder_componentSourceRankBudget fp A B := by
  dsimp [theorem20_10_householder_sourceRankBudget,
    theorem20_10_householder_componentSourceRankBudget]
  exact add_le_add
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (frobNormRect_nonneg A))
    le_rfl
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the conservative component budget is a sufficient rank-radius smallness
    condition for the printed Householder source-rank budget. -/
theorem theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_componentSourceRankBudget_lt
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      theorem20_10_householder_componentSourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    theorem20_10_householder_sourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  exact lt_of_le_of_lt
    (theorem20_10_householder_sourceRankBudget_le_componentSourceRankBudget
      fp A B)
    hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    compact sufficient smallness condition for the conservative concrete
    Householder component rank budget. -/
theorem theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    theorem20_10_householder_componentSourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  dsimp [theorem20_10_householder_componentSourceRankBudget]
  have hA :
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A ≤
        max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
            (theorem20_10_householder_gammaB fp r p q) *
          frobNormRect A :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (frobNormRect_nonneg A)
  have hBterm :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B ≤
        max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
            (theorem20_10_householder_gammaB fp r p q) *
          frobNormRect B :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (frobNormRect_nonneg B)
  have hbudget_le :
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B ≤
        max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
            (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) := by
    calc
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B
          ≤ max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
                (theorem20_10_householder_gammaB fp r p q) *
              frobNormRect A +
            max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
                (theorem20_10_householder_gammaB fp r p q) *
              frobNormRect B :=
            add_le_add hA hBterm
      _ = max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
              (theorem20_10_householder_gammaB fp r p q) *
            (frobNormRect A + frobNormRect B) := by ring
  exact lt_of_le_of_lt hbudget_le hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the existing source-rank gamma threshold also implies the conservative
    component-route max-gamma product smallness condition. -/
theorem theorem20_10_householder_component_max_gamma_sum_bound_of_max_gamma_lt_sourceRankGammaThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q) *
        (frobNormRect A + frobNormRect B) <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    theorem20_10_householder_gammaA_conservativeRhs_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hgammaMax_nonneg :
      0 ≤ max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) :=
    le_trans hgammaA_nonneg (le_max_left _ _)
  have hScale_pos :
      0 < max (1 : ℝ) (frobNormRect A + frobNormRect B) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hNorm_le_scale :
      frobNormRect A + frobNormRect B ≤
        max (1 : ℝ) (frobNormRect A + frobNormRect B) :=
    le_max_right _ _
  have hscaled :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          max (1 : ℝ) (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack := by
    exact (lt_div_iff₀ hScale_pos).mp
      (by simpa [theorem20_10_householder_sourceRankGammaThreshold]
        using hsmall)
  exact
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hNorm_le_scale hgammaMax_nonneg)
      hscaled
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank budget smallness for the conservative concrete component route
    follows from the positive gamma-threshold condition. -/
theorem theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    theorem20_10_householder_componentSourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hB hStack := by
  exact
    theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
      fp A B hB hStack
      (theorem20_10_householder_component_max_gamma_sum_bound_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hB hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    a single conservative component source-rank budget below the radius implies
    both strict margin hypotheses consumed by the component source-rank theorem. -/
theorem theorem20_10_householder_componentSourceRankMargins_of_budget_lt_sourceRankRadius
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hsmall :
      theorem20_10_householder_componentSourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hB.transposeVecNorm2LowerMargin ∧
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin := by
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    theorem20_10_householder_gammaA_conservativeRhs_nonneg fp hvalidA
  have hAterm_nonneg :
      0 ≤ theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A :=
    mul_nonneg hgammaA_nonneg (frobNormRect_nonneg A)
  constructor
  · calc
      theorem20_10_householder_gammaB fp r p q * frobNormRect B
          ≤ theorem20_10_householder_componentSourceRankBudget fp A B := by
            dsimp [theorem20_10_householder_componentSourceRankBudget]
            linarith
      _ < theorem20_10_householder_sourceRankRadius hB hStack := hsmall
      _ ≤ hB.transposeVecNorm2LowerMargin := by
            exact min_le_left _ _
  · calc
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B
          = theorem20_10_householder_componentSourceRankBudget fp A B := by
            rfl
      _ < theorem20_10_householder_sourceRankRadius hB hStack := hsmall
      _ ≤ hStack.vecNorm2LowerMargin := by
            exact min_le_right _ _
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the compact max-gamma product condition directly supplies the two strict
    source-rank margins needed by the conservative component route. -/
theorem theorem20_10_householder_componentSourceRankMargins_of_max_gamma_sum_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hB.transposeVecNorm2LowerMargin ∧
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin := by
  exact
    theorem20_10_householder_componentSourceRankMargins_of_budget_lt_sourceRankRadius
      fp A B hB hStack hvalidA
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
        fp A B hB hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the positive source-rank gamma threshold directly supplies the two strict
    source-rank margins needed by the conservative component route. -/
theorem theorem20_10_householder_componentSourceRankMargins_of_max_gamma_lt_sourceRankGammaThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hB.transposeVecNorm2LowerMargin ∧
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin := by
  exact
    theorem20_10_householder_componentSourceRankMargins_of_budget_lt_sourceRankRadius
      fp A B hB hStack hvalidA
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hB hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    one source-rank-dependent unit-roundoff cap that implies the three
    half-radius gamma guards and the conservative source-rank gamma threshold.

    This packages the current fully verified smallness assumptions into a
    single positive scalar depending only on dimensions and the induced
    source-rank margins. -/
noncomputable def theorem20_10_householder_componentUnitRoundoffSmallnessThreshold
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  min
    (((1 : ℝ) / 2) /
      (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ))
    (min
      (((1 : ℝ) / 2) /
        (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)))
      (min
        (((1 : ℝ) / 2) /
          ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℕ) : ℝ))
        (theorem20_10_householder_sourceRankGammaThreshold hB hStack /
          theorem20_10_householder_componentUnitRoundoffCoefficient r p q)))
/-- Positivity of the combined unit-roundoff smallness threshold used by the
    Theorem 20.10(b) source-rank wrappers. -/
theorem theorem20_10_householder_componentUnitRoundoffSmallnessThreshold_pos
    {r p q : ℕ}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hp : 0 < p) (hq : 0 < q) :
    0 <
      theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack := by
  have hpq_pos : 0 < p + q := by omega
  have hrq_pos : 0 < r + q := by omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hidxA_nat :
      0 < (p + q) * householderConstructApplyGammaIndex (r + q) :=
    Nat.mul_pos hpq_pos hKA_pos
  have hidxB_nat :
      0 < p * householderConstructApplyGammaIndex (p + q) :=
    Nat.mul_pos hp hKB_pos
  have hfactor_pos :
      0 < householderQRRhsPanelGammaClosedGrowthFactor (r + q) q :=
    householderQRRhsPanelGammaClosedGrowthFactor_pos hrq_pos
  have hidxRhs_nat :
      0 < householderQRRhsPanelGammaClosedGrowthIndex (r + q) q := by
    rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
    exact Nat.mul_pos hfactor_pos (Nat.mul_pos hq hKA_pos)
  have hidxA :
      0 <
        (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) := by
    exact_mod_cast hidxA_nat
  have hidxB :
      0 <
        (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)) := by
    exact_mod_cast hidxB_nat
  have hidxRhs :
      0 <
        ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℕ) : ℝ) := by
    exact_mod_cast hidxRhs_nat
  have hcapA :
      0 <
        (((1 : ℝ) / 2) /
          (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)) :=
    div_pos (by norm_num) hidxA
  have hcapB :
      0 <
        (((1 : ℝ) / 2) /
          (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ))) :=
    div_pos (by norm_num) hidxB
  have hcapRhs :
      0 <
        (((1 : ℝ) / 2) /
          ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℕ) : ℝ)) :=
    div_pos (by norm_num) hidxRhs
  have hGammaThreshold :
      0 < theorem20_10_householder_sourceRankGammaThreshold hB hStack :=
    theorem20_10_householder_sourceRankGammaThreshold_pos hB hStack
  have hCoeff :
      0 < theorem20_10_householder_componentUnitRoundoffCoefficient r p q :=
    theorem20_10_householder_componentUnitRoundoffCoefficient_pos hp
  have hSourceCap :
      0 <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack /
          theorem20_10_householder_componentUnitRoundoffCoefficient r p q :=
    div_pos hGammaThreshold hCoeff
  dsimp [theorem20_10_householder_componentUnitRoundoffSmallnessThreshold]
  exact lt_min hcapA (lt_min hcapB (lt_min hcapRhs hSourceCap))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the combined unit-roundoff threshold implies the half-radius guards and
    the linear source-rank gamma threshold used by the conservative component
    route. -/
theorem theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hp : 0 < p) (hq : 0 < q)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
          fp.u ≤ 1 / 2) ∧
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
          fp.u) ≤ 1 / 2) ∧
      (((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
          fp.u) ≤ 1 / 2) ∧
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q *
          fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack := by
  have hpq_pos : 0 < p + q := by omega
  have hrq_pos : 0 < r + q := by omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hidxA_nat :
      0 < (p + q) * householderConstructApplyGammaIndex (r + q) :=
    Nat.mul_pos hpq_pos hKA_pos
  have hidxB_nat :
      0 < p * householderConstructApplyGammaIndex (p + q) :=
    Nat.mul_pos hp hKB_pos
  have hfactor_pos :
      0 < householderQRRhsPanelGammaClosedGrowthFactor (r + q) q :=
    householderQRRhsPanelGammaClosedGrowthFactor_pos hrq_pos
  have hidxRhs_nat :
      0 < householderQRRhsPanelGammaClosedGrowthIndex (r + q) q := by
    rw [householderQRRhsPanelGammaClosedGrowthIndex_eq_factor_mul_printedIndex]
    exact Nat.mul_pos hfactor_pos (Nat.mul_pos hq hKA_pos)
  have hidxA :
      0 <
        (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) := by
    exact_mod_cast hidxA_nat
  have hidxB :
      0 <
        (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)) := by
    exact_mod_cast hidxB_nat
  have hidxRhs :
      0 <
        ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℕ) : ℝ) := by
    exact_mod_cast hidxRhs_nat
  have hCoeff :
      0 < theorem20_10_householder_componentUnitRoundoffCoefficient r p q :=
    theorem20_10_householder_componentUnitRoundoffCoefficient_pos hp
  have huA :
      fp.u <
        (((1 : ℝ) / 2) /
          (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ)) := by
    exact lt_of_lt_of_le hu
      (by
        dsimp [theorem20_10_householder_componentUnitRoundoffSmallnessThreshold]
        exact min_le_left _ _)
  have huB :
      fp.u <
        (((1 : ℝ) / 2) /
          (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ))) := by
    exact lt_of_lt_of_le hu
      (by
        dsimp [theorem20_10_householder_componentUnitRoundoffSmallnessThreshold]
        exact le_trans (min_le_right _ _) (min_le_left _ _))
  have huRhs :
      fp.u <
        (((1 : ℝ) / 2) /
          ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℕ) : ℝ)) := by
    exact lt_of_lt_of_le hu
      (by
        dsimp [theorem20_10_householder_componentUnitRoundoffSmallnessThreshold]
        exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _)))
  have huSource :
      fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack /
          theorem20_10_householder_componentUnitRoundoffCoefficient r p q := by
    exact lt_of_lt_of_le hu
      (by
        dsimp [theorem20_10_householder_componentUnitRoundoffSmallnessThreshold]
        exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hA_lt :
      fp.u *
          (((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) <
        1 / 2 :=
    (lt_div_iff₀ hidxA).mp huA
  have hB_lt :
      fp.u *
          (((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ)) <
        1 / 2 :=
    (lt_div_iff₀ hidxB).mp huB
  have hRhs_lt :
      fp.u *
          ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℕ) : ℝ) <
        1 / 2 :=
    (lt_div_iff₀ hidxRhs).mp huRhs
  have hSource_lt :
      fp.u * theorem20_10_householder_componentUnitRoundoffCoefficient r p q <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack :=
    (lt_div_iff₀ hCoeff).mp huSource
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith [hA_lt]
  · nlinarith [hB_lt]
  · nlinarith [hRhs_lt]
  · nlinarith [hSource_lt]
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    explicit linear unit-roundoff threshold implies the conservative component
    gamma-threshold condition used by the source-rank branch. -/
theorem theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hm : 0 < r + q)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2))
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hunit :
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q *
          fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q) <
      theorem20_10_householder_sourceRankGammaThreshold hB hStack := by
  exact lt_of_le_of_lt
    (theorem20_10_householder_component_max_gamma_le_componentUnitRoundoffCoefficient_mul_u_of_small
      fp hm hsmallA hsmallB hhalf)
    hunit
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the single combined unit-roundoff smallness threshold implies the
    conservative component max-gamma source-rank threshold. -/
theorem theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hp : 0 < p) (hq : 0 < q)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q) <
      theorem20_10_householder_sourceRankGammaThreshold hB hStack := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hB hStack hp hq hu with
    ⟨hsmallA, hsmallB, hhalf, hunit⟩
  exact
    theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_bound
      fp hB hStack (by omega) hsmallA hsmallB hhalf hunit
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the single combined unit-roundoff smallness threshold supplies the
    conservative component source-rank budget condition. -/
theorem theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hp : 0 < p) (hq : 0 < q)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    theorem20_10_householder_componentSourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hBsrc hStack := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  exact
    theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
      fp A B hBsrc hStack hvalidA hvalidB
      (theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_smallnessThreshold
        fp hBsrc hStack hp hq hu)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the same combined unit-roundoff threshold also supplies the printed
    Householder source-rank budget condition.

This is the non-conservative-budget companion to
`theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_unit_roundoff_smallnessThreshold`.
It uses the existing domination of the printed source-rank budget by the
conservative component budget. -/
theorem theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hp : 0 < p) (hq : 0 < q)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    theorem20_10_householder_sourceRankBudget fp A B <
      theorem20_10_householder_sourceRankRadius hBsrc hStack := by
  exact
    theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_componentSourceRankBudget_lt
      fp A B hBsrc hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_unit_roundoff_smallnessThreshold
        fp A B hBsrc hStack hp hq hu)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    the single combined unit-roundoff smallness threshold directly supplies
    both strict source-rank margin hypotheses for the conservative component
    route. -/
theorem theorem20_10_householder_componentSourceRankMargins_of_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hp : 0 < p) (hq : 0 < q)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hBsrc.transposeVecNorm2LowerMargin ∧
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  exact
    theorem20_10_householder_componentSourceRankMargins_of_max_gamma_lt_sourceRankGammaThreshold
      fp A B hBsrc hStack hvalidA hvalidB
      (theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_smallnessThreshold
        fp hBsrc hStack hp hq hu)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank margin-radius wrapper for the constructed rounded Householder
    GQR Part B returned-vector theorem.

    This replaces the two explicit strict margin hypotheses of
    `..._of_source_ranks_frobenius_margins_composed_conservative_gamma` by one
    canonical condition: the combined Householder Frobenius rank budget is
    strictly below the minimum of the `Bᵀ` and stacked source margins. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hMargin :
      theorem20_10_householder_sourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hAterm_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q * frobNormRect A :=
    mul_nonneg hgammaA_nonneg (frobNormRect_nonneg A)
  have hBMargin :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        LSEFullRowRank.transposeVecNorm2LowerMargin hB := by
    calc
      theorem20_10_householder_gammaB fp r p q * frobNormRect B
          ≤ theorem20_10_householder_sourceRankBudget fp A B := by
            dsimp [theorem20_10_householder_sourceRankBudget]
            linarith
      _ < theorem20_10_householder_sourceRankRadius hB hStack := hMargin
      _ ≤ LSEFullRowRank.transposeVecNorm2LowerMargin hB := by
            exact min_le_left _ _
  have hStackMargin :
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        LSEStackedFullColumnRank.vecNorm2LowerMargin hStack := by
    calc
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B
          = theorem20_10_householder_sourceRankBudget fp A B := by
            rfl
      _ < theorem20_10_householder_sourceRankRadius hB hStack := hMargin
      _ ≤ LSEStackedFullColumnRank.vecNorm2LowerMargin hStack := by
            exact min_le_right _ _
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_frobenius_margins_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack hBMargin
      hStackMargin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative component-budget wrapper for the constructed rounded
    Householder GQR Part B returned-vector theorem.

    The constructed returned-vector branch uses the printed `A` matrix budget.
    This wrapper lets callers supply the stronger conservative component budget
    that also dominates the rounded-RHS `A` coefficient. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_rank_budget_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      theorem20_10_householder_componentSourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_componentSourceRankBudget_lt
        fp A B hB hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative max-gamma wrapper for the constructed rounded Householder GQR
    Part B returned-vector theorem.

    This is the conservative returned-vector branch under the compact condition
    `max(conservativeGammaA, gammaB) * (||A||_F + ||B||_F) < sourceRankRadius`. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_max_gamma_sum_bound_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_rank_budget_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
        fp A B hB hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative gamma-threshold wrapper for the constructed rounded
    Householder GQR Part B returned-vector theorem.

    The positive threshold is stated for the larger of the conservative
    rounded-RHS-aware `A` coefficient and the Householder `B` coefficient. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_gamma_threshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_rank_budget_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hB hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    unit-roundoff threshold wrapper for the constructed rounded Householder
    GQR Part B returned-vector theorem.

    This replaces the raw conservative max-gamma source-rank threshold by
    explicit half-radius guards for the `A`, RHS, and `Bᵀ` Householder gamma
    terms plus the linear unit-roundoff source-rank threshold. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_unit_roundoff_threshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2))
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hunit :
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q *
          fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack :=
    theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_bound
      fp hB hStack (by omega) hsmallA hsmallB hhalf hunit
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_gamma_threshold_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed returned-vector GQR Part B wrapper from one combined
    unit-roundoff smallness threshold.

    This is the same returned-vector surface as
    `..._component_unit_roundoff_threshold_composed_conservative_gamma`, but the
    caller supplies only `fp.u < componentUnitRoundoffSmallnessThreshold`; the
    three half-radius guards and the source-rank gamma cap are derived
    internally. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hB hStack hp hq hu with
    ⟨hsmallA, hsmallB, hhalf, hunit⟩
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_unit_roundoff_threshold_composed_conservative_gamma
      fp A B b d hp hq hsmallA hsmallB hhalf hB hStack hunit
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    compact source-rank smallness wrapper for the constructed rounded
    Householder GQR Part B returned-vector theorem.

    This exposes the practical sufficient condition
    `max(gammaA, gammaB) * (||A||_F + ||B||_F) < sourceRankRadius` directly on
    the returned-vector surface, deriving the canonical combined rank-budget
    hypothesis internally. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_max_gamma_sum_bound_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
        fp A B hB hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank gamma-threshold wrapper for the constructed rounded
    Householder GQR Part B returned-vector theorem.

    Since the threshold is strictly positive whenever the source rank
    hypotheses hold, this states the rank-preservation branch as an explicit
    roundoff-smallness condition on the larger of the two Householder gamma
    coefficients. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_gamma_threshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        let xhat : Fin (p + q) → ℝ :=
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hB hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank-radius returned-vector wrapper for the constructed rounded
    Householder GQR Part B theorem.

    This is the explicit-witness companion to
    `..._xhat_minimizer_of_source_ranks_rank_radius...`: it exposes the
    constructed transformed-tail vector as an existential `xhat` while keeping
    the equality that identifies it with the rounded Householder path. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      theorem20_10_householder_sourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack hsmall with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hbranch⟩
  let xhat : Fin (p + q) → ℝ :=
    theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
  refine
    ⟨xhat, DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0,
      hDeltaB0, hDeltab0, hpert, hQeq, hSeq, hb_tail, rfl, ?_⟩
  simpa [xhat] using hbranch
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    compact source-rank returned-vector witness wrapper for the constructed
    rounded Householder GQR Part B theorem.

    This exposes the practical sufficient condition
    `max(gammaA, gammaB) * (||A||_F + ||B||_F) < sourceRankRadius` on the
    explicit `xhat` witness surface. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_max_gamma_sum_bound_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
        fp A B hB hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative compact source-rank returned-vector witness wrapper for the
    constructed rounded Householder GQR Part B theorem.

    This is the explicit-witness form of the component max-gamma sufficient
    condition, using the conservative rounded-RHS-aware `A` coefficient. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_max_gamma_sum_bound_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_componentSourceRankBudget_lt
        fp A B hB hStack
        (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
          fp A B hB hStack hsmall))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative source-rank gamma-threshold returned-vector witness wrapper
    for the constructed rounded Householder GQR Part B theorem.

    This exposes the conservative component threshold directly on the explicit
    `xhat` witness surface. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_gamma_threshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_rank_radius_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack
      (theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_componentSourceRankBudget_lt
        fp A B hB hStack
        (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
          fp A B hB hStack hvalidA hvalidB hsmall))
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    explicit returned-vector wrapper under component unit-roundoff threshold
    premises.

    This exposes the half-radius guards and linear unit-roundoff source-rank
    threshold directly on the `exists xhat` witness surface. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_unit_roundoff_threshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2))
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hunit :
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q *
          fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack :=
    theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_bound
      fp hB hStack (by omega) hsmallA hsmallB hhalf hunit
  exact
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_gamma_threshold_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-facing returned-vector wrapper for the constructed rounded
    Householder GQR Part B theorem.

    The lower-level returned-vector theorem keeps the constructed GQR record
    and transformed tail inside nested `let` bindings.  This wrapper exposes the
    returned vector as an explicit witness while retaining the equality that it
    is exactly the transformed-tail GQR vector for the constructed rounded
    Householder path.  It is still a constructed-path theorem, not a
    deterministic implementation identity for an externally specified GQR
    routine. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_gamma_threshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_gamma_threshold_composed_conservative_gamma
      fp A B b d hp hq hvalidA hvalidB hhalf hB hStack hsmall with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hbranch⟩
  let xhat : Fin (p + q) → ℝ :=
    theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
  refine
    ⟨xhat, DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0,
      hDeltaB0, hDeltab0, hpert, hQeq, hSeq, hb_tail, rfl, ?_⟩
  simpa [xhat] using hbranch
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    explicit returned-vector wrapper under the combined unit-roundoff
    smallness threshold.

    This is the same source-facing witness surface as
    `..._exists_xhat_minimizer_of_source_ranks_gamma_threshold...`, but the
    caller supplies only the positive source-rank-dependent unit-roundoff
    threshold.  The half-radius guards, gamma-validity facts, and conservative
    source-rank gamma cap are discharged by the existing threshold theorem. -/
theorem theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ xhat : Fin (p + q) → ℝ,
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        let gammaA : ℝ :=
          theorem20_10_householder_composed_partA_gammaA fp r p q
        let gammaB : ℝ :=
          theorem20_10_householder_composed_partA_gammaB fp r p q
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
        ∃ Deltad : Fin p → ℝ,
          Deltad = (0 : Fin p → ℝ) ∧
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j)
              (fun i => d i + Deltad i) x) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  let beta : Fin q → ℝ :=
    theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
  rcases
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_xhat_minimizer_of_source_ranks_component_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, hb_tail, hbranch⟩
  let xhat : Fin (p + q) → ℝ :=
    theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d
  refine
    ⟨xhat, DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0,
      hDeltaB0, hDeltab0, hpert, hQeq, hSeq, hb_tail, rfl, ?_⟩
  simpa [xhat] using hbranch
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), rounded Householder RHS
    Part B certificate route with the currently proved conservative RHS
    coefficient.

    This reuses the constructed-source rounded-RHS Part A certificate and
    constructs the Part B constraint perturbation `Deltad = DeltaB*xhat`.
    It therefore does not add new rank assumptions beyond the Part A route;
    the remaining full computed-path work is still the identification of the
    complete rounded GQR factors and final computed vector. -/
theorem theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge_matrix : gamma fp q ≤ gammaA)
    (hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d
        (theorem20_10_gqr_xhat_of_transformed_tail fp h
          (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
        gammaA gammaB) := by
  rcases
    theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound
      fp h b d gammaA gammaB hUfl hq hhalf hgammaB_nonneg
      hgammaA_ge_matrix hgammaA_ge_rhs hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨_Deltab, _hb_tail, _hDeltab, _DeltaS, _DeltaL22,
      _hDeltaSbound, _hDeltaL22bound, _hDeltaSfrob, _hDeltaL22frob,
      hcertA⟩
  exact
    theorem20_10_partB_certificate_of_nonempty_partA_certificate
      A B b d
      (theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
      hgammaB_nonneg hcertA
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), rounded Householder RHS
    Part B backward-error core with generic conservative bounds.

    This unwraps the constructed-source rounded-RHS Part A certificate through
    the generic nonempty Part A-to-Part B core bridge.  Compared with the
    certificate theorem above, it exposes concrete perturbations, the
    constraint right-hand-side action identity, and the exact perturbed
    GQR/minimizer package. -/
theorem theorem20_10_partB_backward_error_of_constructed_source_householder_rhs_conservative_bound
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (gammaA gammaB : ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hgammaB_nonneg : 0 ≤ gammaB)
    (hgammaA_ge_matrix : gamma fp q ≤ gammaA)
    (hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤ gammaA)
    (hgammaB_ge : gamma fp p ≤ gammaB)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalid2S : gammaValid fp (2 * p))
    (hvalid2L22 : gammaValid fp (2 * q)) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases
    theorem20_10_partA_certificate_of_constructed_source_householder_rhs_conservative_bound
      fp h b d gammaA gammaB hUfl hq hhalf hgammaB_nonneg
      hgammaA_ge_matrix hgammaA_ge_rhs hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22 with
    ⟨_Deltab, _hb_tail, _hDeltab, _DeltaS, _DeltaL22,
      _hDeltaSbound, _hDeltaL22bound, _hDeltaSfrob, _hDeltaL22frob,
      hcertA⟩
  exact
    theorem20_10_partB_backward_error_of_nonempty_partA_certificate
      A B b d
      (theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
      hgammaB_nonneg hcertA
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), rounded Householder RHS
    Part B certificate route with source-facing conservative gamma
    coefficients.

    This derives the side conditions of
    `theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_bound`
    from the standard Householder validity hypotheses, mirroring the Part A
    conservative-gamma theorem.  The result is still a certificate theorem:
    full computed-path closure additionally requires identification of the
    rounded GQR factors and the returned computed vector. -/
theorem theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d
        (theorem20_10_gqr_xhat_of_transformed_tail fp h
          (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
        (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) := by
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) := by
    exact le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hidxB_ge_p :
      p ≤ p * householderConstructApplyGammaIndex (p + q) :=
    Nat.le_mul_of_pos_right p hKB_pos
  have hgammaA_printed_ge :
      gamma fp q ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxA_ge_q hvalidA
  have hgammaA_ge_matrix :
      gamma fp q ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    le_trans hgammaA_printed_ge
      (le_max_left _ _)
  have hgammaA_ge_rhs :
      theorem20_10_householder_rhs_conservative_gamma fp r p q ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q :=
    le_max_right _ _
  have hgammaB_ge :
      gamma fp p ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxB_ge_p hvalidB
  exact
    theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_bound
      fp h b d
      (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
      (theorem20_10_householder_gammaB fp r p q)
      hUfl hq hhalf hgammaB_nonneg hgammaA_ge_matrix hgammaA_ge_rhs
      hgammaB_ge hSdiag hL22diag hvalid2S hvalid2L22
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), rounded Householder RHS
    Part B backward-error core with source-facing conservative gamma
    coefficients.

    This unwraps
    `theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_gamma`
    through the generic Part B certificate-to-core theorem, exposing the
    perturbation witnesses, source-shaped norm bounds, and exact perturbed GQR
    minimizer structure.  It still leaves the final computed-path obligation:
    identifying the implementation's returned vector with this exact perturbed
    minimizer. -/
theorem theorem20_10_partB_backward_error_of_constructed_source_householder_rhs_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases
    theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_gamma
      fp h b d hUfl hq hhalf hSdiag hL22diag hvalidA hvalidB with
    ⟨cert⟩
  have hcore :=
    theorem20_10_partB_backward_error_of_perturbation_certificate
      A B b d
      (theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
      cert
  dsimp at hcore
  rcases hcore with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaAeq, hDeltaBeq,
      hDeltabeq, hDeltadeq, hDeltaA, hDeltaB, hDeltab, hDeltad,
      hmethod⟩
  refine
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, cert.Deltad, ?_, ?_, ?_, ?_,
      hmethod⟩
  · simpa [hDeltaAeq] using hDeltaA
  · simpa [hDeltaBeq] using hDeltaB
  · simpa [hDeltabeq] using hDeltab
  · simpa [hDeltadeq] using hDeltad
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), rounded Householder RHS
    Part B certificate route with source rank hypotheses instead of supplied
    triangular diagonal nonzero hypotheses.

    The supplied GQR factorization converts source full row rank of `B` and
    full column rank of `[A; B]` into nonzero diagonals of `S` and `L22`, so
    callers no longer need to expose those factor-level side conditions for
    this constructed-source certificate branch. -/
theorem theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_gamma_of_source_ranks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d
        (theorem20_10_gqr_xhat_of_transformed_tail fp h
          (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d)
        (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hBsrc, hStack⟩
  exact
    theorem20_10_partB_certificate_of_constructed_source_householder_rhs_conservative_gamma
      fp h b d hUfl hq hhalf hdiag.1 hdiag.2 hvalidA hvalidB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), rounded Householder RHS
    Part B backward-error core with source rank hypotheses instead of supplied
    triangular diagonal nonzero hypotheses.

    This is the source-facing version of
    `theorem20_10_partB_backward_error_of_constructed_source_householder_rhs_conservative_gamma`
    for an already supplied exact GQR factorization.  It removes the
    caller-facing `S`/`L22` diagonal side conditions by deriving them from
    `LSEFullRowRank B` and `LSEStackedFullColumnRank A B`. -/
theorem theorem20_10_partB_backward_error_of_constructed_source_householder_rhs_conservative_gamma_of_source_ranks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hUfl :
      h.U =
        fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A h.Q))
    (hq : 0 < q)
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_gqr_xhat_of_transformed_tail fp h
        (theorem20_10_householder_AQ2_rhs_tail fp A h.Q b) d
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hBsrc, hStack⟩
  exact
    theorem20_10_partB_backward_error_of_constructed_source_householder_rhs_conservative_gamma
      fp h b d hUfl hq hhalf hdiag.1 hdiag.2 hvalidA hvalidB
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder `Bᵀ` perturbation together with the induced
    constraint right-hand-side perturbation bound.

    This packages the already proved `DeltaB` Frobenius bound with
    `Deltad = DeltaB * xhat`, giving the source-shaped
    `||Deltad||₂ <= gamma_tilde_np ||B||_F ||xhat||₂` component needed by the
    backward-error certificate.  It still does not identify the computed
    `xhat` or prove perturbed rank preservation. -/
theorem theorem20_10_householder_B_transpose_Deltad_bound
    {r p q : ℕ} (fp : FPModel)
    (B : Fin p → Fin (p + q) → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hp : 0 < p)
    (hvalid :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ (DeltaB : Fin p → Fin (p + q) → ℝ) (Deltad : Fin p → ℝ),
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat := by
  rcases theorem20_10_householder_B_transpose_frob_perturbation_bound
      fp B hp hvalid with
    ⟨DeltaB, hDeltaBrep, hDeltaBbound⟩
  rcases theorem20_10_constraint_rhs_perturbation_bound_of_DeltaB
      B DeltaB xhat hDeltaBbound with
    ⟨Deltad, hDeltadrep, hDeltadbound⟩
  exact ⟨DeltaB, Deltad, hDeltaBrep, hDeltadrep,
    hDeltaBbound, hDeltadbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    concrete Householder perturbation components for the computed GQR path.

    This packages the four currently verified component perturbations:
    the full-source `DeltaA` transported from the trailing `A Q₂` QR step,
    the `DeltaB` perturbation from the `Bᵀ` QR step, the concrete RHS
    perturbation `Deltab` for the `A Q₂` Householder transform, and the induced
    constraint perturbation `Deltad = DeltaB*xhat`.  The `Deltab` coefficient is
    still the conservative recursive RHS factor, so this theorem is a concrete
    component package, not yet the final printed Theorem 20.10 certificate. -/
theorem theorem20_10_householder_concrete_perturbation_components_bound
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        Real.sqrt (r + q : ℝ) *
          (((2 : ℝ) *
              (householderQRRhsPanelGammaClosedGrowthFactor (r + q) q : ℝ) *
              gamma fp (q * householderConstructApplyGammaIndex (r + q))) *
            vecNorm2 b) ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat := by
  rcases theorem20_10_householder_AQ2_full_A_frob_perturbation_bound
      fp A Q hQ hq hvalidA with
    ⟨DeltaA, hDeltaArep, hDeltaAbound⟩
  rcases theorem20_10_householder_AQ2_rhs_vecNorm2_perturbation_bound_of_gammaFactor
      fp A Q b hq hhalf with
    ⟨Deltab, hDeltabrep, hDeltabbound⟩
  rcases theorem20_10_householder_B_transpose_Deltad_bound
      fp B xhat hp hvalidB with
    ⟨DeltaB, Deltad, hDeltaBrep, hDeltadrep, hDeltaBbound, hDeltadbound⟩
  exact
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaAbound, hDeltaBbound,
      hDeltabbound, hDeltadbound⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package promoted to the backward-error certificate boundary.

    The verified Householder QR perturbation components already provide
    `DeltaA`, `DeltaB`, `Deltab`, and `Deltad` with source-shaped bounds.  This
    theorem packages those witnesses into the Part B certificate as soon as the
    induced perturbed matrices are known to keep the source rank assumptions.
    Thus the remaining Part B obstruction is isolated to rank preservation and
    computed-vector identification, not to the four finite-precision component
    bounds. -/
theorem theorem20_10_partB_certificate_of_householder_components_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat ∧
      (LSEFullRowRank (fun i j => B i j + DeltaB i j) →
       LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) →
       Nonempty
        (Theorem20_10PartBPerturbationCertificate A B b d xhat
          (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q))) := by
  rcases theorem20_10_householder_concrete_perturbation_components_bound
      fp A B Q b xhat hQ hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaAraw, hDeltaB, hDeltabraw,
      hDeltad⟩
  have hDeltaA :
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A := by
    exact le_trans hDeltaAraw
      (mul_le_mul_of_nonneg_right
        (le_max_left
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_rhs_conservative_gamma fp r p q))
        (frobNormRect_nonneg A))
  have hDeltab_conservative :
      vecNorm2 Deltab ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b := by
    simpa [theorem20_10_householder_rhs_conservative_gamma, mul_assoc]
      using hDeltabraw
  have hDeltab_first :
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          vecNorm2 b := by
    exact le_trans hDeltab_conservative
      (mul_le_mul_of_nonneg_right
        (le_max_right
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_rhs_conservative_gamma fp r p q))
        (vecNorm2_nonneg b))
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have htail_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q *
          frobNormRect A * vecNorm2 xhat := by
    exact mul_nonneg
      (mul_nonneg hgammaB_nonneg (frobNormRect_nonneg A))
      (vecNorm2_nonneg xhat)
  have hDeltab :
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat :=
    le_trans hDeltab_first (le_add_of_nonneg_right htail_nonneg)
  refine
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad, ?_⟩
  intro hB hstack
  exact
    ⟨{ DeltaA := DeltaA
       DeltaB := DeltaB
       Deltab := Deltab
       Deltad := Deltad
       hB := hB
       hstack := hstack
       hDeltaA := hDeltaA
       hDeltaB := hDeltaB
       hDeltab := hDeltab
       hDeltad := hDeltad }⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package promoted directly to the exact perturbed GQR core.

    Compared with
    `theorem20_10_partB_certificate_of_householder_components_conservative_gamma`,
    this unwraps the certificate boundary: once the concrete Householder
    perturbations preserve the source full-row-rank and stacked full-column-rank
    hypotheses, the theorem returns the exact perturbed GQR method coordinates
    and unique perturbed minimizer.  The remaining full computed-path work is
    still rank preservation and identification of the implementation's returned
    vector with this exact perturbed problem. -/
theorem theorem20_10_partB_backward_error_of_householder_components_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2)) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (LSEFullRowRank (fun i j => B i j + DeltaB i j) →
       LSEStackedFullColumnRank
        (fun i j => A i j + DeltaA i j)
        (fun i j => B i j + DeltaB i j) →
       ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases theorem20_10_partB_certificate_of_householder_components_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad,
      _hcert⟩
  refine
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad, ?_⟩
  intro hB hstack
  exact
    GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
      A DeltaA B DeltaB b Deltab d Deltad hB hstack
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package promoted to the certificate boundary with source-rank
    margin preservation.

This is the certificate-level companion to
`theorem20_10_partB_backward_error_of_householder_components_source_ranks_conservative_gamma`:
the concrete Householder perturbation components are packaged into a reusable
`Theorem20_10PartBPerturbationCertificate` after the source rank margins prove
that the perturbed matrices keep full row rank and stacked full column rank. -/
theorem theorem20_10_partB_certificate_of_householder_components_source_ranks_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBMargin :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hBsrc.transposeVecNorm2LowerMargin)
    (hStackMargin :
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin) :
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA_conservativeRhs fp r p q *
            vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat ∧
      Nonempty
        (Theorem20_10PartBPerturbationCertificate A B b d xhat
          (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q)) := by
  rcases theorem20_10_partB_certificate_of_householder_components_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad,
      hcert⟩
  have hcond :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    theorem20_8_conditions20_24_of_frobNormRect_bounds_lt_margins
      (A := A) (DeltaA := DeltaA) (B := B) (DeltaB := DeltaB)
      (cA := theorem20_10_householder_gammaA_conservativeRhs fp r p q *
        frobNormRect A)
      (cB := theorem20_10_householder_gammaB fp r p q * frobNormRect B)
      hBsrc hStack hDeltaA hDeltaB hBMargin hStackMargin
  exact
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad,
      hcert hcond.1 hcond.2⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    named proposition for the concrete Householder component certificate route.

This is the certificate-boundary analogue of
`Theorem20_10HouseholderComponentPartBRoute`: it records the concrete `A Q₂`,
`Bᵀ`, transformed RHS, and constraint-RHS perturbation identities together with
the conservative source-shaped norm bounds, but stops at the reusable
`Theorem20_10PartBPerturbationCertificate` rather than immediately unpacking the
exact GQR/minimizer method conclusion. -/
def Theorem20_10HouseholderComponentPartBCertificateRoute
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ) : Prop :=
  let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
  let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
  ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
    (DeltaB : Fin p → Fin (p + q) → ℝ)
    (Deltab : Fin (r + q) → ℝ)
    (Deltad : Fin p → ℝ),
    (∀ i j,
      gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
        matMulRect (r + q) (r + q) q
          (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
          (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
    (∀ i j,
      B i j + DeltaB i j =
        matMulRect (p + q) (p + q) p
          (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
          (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
    (∀ i,
      fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
        matMulVec (r + q)
          (matTranspose
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
          (fun k => b k + Deltab k) i) ∧
    (∀ i,
      rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
        rectMatMulVec B xhat i + Deltad i) ∧
    frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
    frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
    vecNorm2 Deltab ≤
      gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
    vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
    Nonempty (Theorem20_10PartBPerturbationCertificate A B b d xhat gammaA gammaB)
/-- Extract the reusable Part B perturbation certificate from the named
    component certificate route, discarding the concrete Householder component
    identities and norm bounds. -/
theorem Theorem20_10HouseholderComponentPartBCertificateRoute.partB_certificate
    {r p q : ℕ} {fp : FPModel}
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    {Q : Fin (p + q) → Fin (p + q) → ℝ}
    {b : Fin (r + q) → ℝ} {d : Fin p → ℝ}
    {xhat : Fin (p + q) → ℝ}
    (hroute :
      Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d xhat
        (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) := by
  dsimp [Theorem20_10HouseholderComponentPartBCertificateRoute] at hroute
  rcases hroute with
    ⟨_DeltaA, _DeltaB, _Deltab, _Deltad, _hAQ, _hB, _hrhs, _hd,
      _hDeltaA, _hDeltaB, _hDeltab, _hDeltad, hcert⟩
  exact hcert
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    explicit-margin wrapper for the named component certificate route. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_source_ranks_margins_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBMargin :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hBsrc.transposeVecNorm2LowerMargin)
    (hStackMargin :
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin) :
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat := by
  dsimp [Theorem20_10HouseholderComponentPartBCertificateRoute]
  exact
    theorem20_10_partB_certificate_of_householder_components_source_ranks_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      hBMargin hStackMargin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-rank radius wrapper for the component certificate route. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_source_ranks_rank_radius_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hMargin :
      theorem20_10_householder_componentSourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hBsrc hStack) :
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat := by
  rcases
    theorem20_10_householder_componentSourceRankMargins_of_budget_lt_sourceRankRadius
      fp A B hBsrc hStack hvalidA hMargin with
    ⟨hBMargin, hStackMargin⟩
  exact
    theorem20_10_householder_component_partB_certificate_route_of_source_ranks_margins_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      hBMargin hStackMargin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    max-gamma source-rank radius wrapper for the component certificate route. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_source_ranks_max_gamma_sum_bound_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hBsrc hStack) :
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat := by
  exact
    theorem20_10_householder_component_partB_certificate_route_of_source_ranks_rank_radius_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
        fp A B hBsrc hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    conservative source-rank gamma-threshold wrapper for the component
    certificate route. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_source_ranks_gamma_threshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hBsrc hStack) :
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat := by
  exact
    theorem20_10_householder_component_partB_certificate_route_of_source_ranks_rank_radius_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hBsrc hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    linear unit-roundoff threshold wrapper for the component certificate route. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_source_ranks_unit_roundoff_threshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2))
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hunit :
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q *
          fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hBsrc hStack) :
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat := by
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hBsrc hStack :=
    theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_bound
      fp hBsrc hStack (by omega) hsmallA hsmallB hhalf hunit
  exact
    theorem20_10_householder_component_partB_certificate_route_of_source_ranks_gamma_threshold_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    combined unit-roundoff smallness-threshold wrapper for the component
    certificate route. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Q b d xhat := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, hhalf, hunit⟩
  exact
    theorem20_10_householder_component_partB_certificate_route_of_source_ranks_unit_roundoff_threshold_conservative_gamma
      fp A B Q b d xhat hQ hp hq hsmallA hsmallB hhalf hBsrc hStack hunit
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    computed-`Bᵀ` specialization of the component certificate route.

This is the certificate-boundary analogue of
`theorem20_10_partB_backward_error_of_householder_components_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma`.
It fixes the abstract orthogonal factor in the component route to the rounded
Householder panel actually computed from `Bᵀ`, deriving its orthogonality from
the concrete `Bᵀ` block theorem. -/
theorem theorem20_10_householder_component_partB_certificate_route_of_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Qb b d xhat := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨_hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hQb : IsOrthogonal (p + q) Qb := by
    rcases
      theorem20_10_householder_B_transpose_perturbed_constraint_block
        (r := r) fp B hp hvalidB with
      ⟨_DeltaB, _hDeltaBrep, hQb, _hS, _hblock, _hDeltaB⟩
    simpa [Qb] using hQb
  exact
    theorem20_10_householder_component_partB_certificate_route_of_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B Qb b d xhat hQb hp hq hBsrc hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package with source-rank margin preservation.

    This strengthens
    `theorem20_10_partB_backward_error_of_householder_components_conservative_gamma`
    by deriving the perturbed full-row-rank and stacked-full-column-rank
    assumptions from the source rank hypotheses and strict lower-bound margins
    for the concrete Householder Frobenius perturbation bounds.  It still leaves
    the computed-vector identification and any concrete roundoff-smallness
    proof for these margins as separate obligations. -/
theorem theorem20_10_partB_backward_error_of_householder_components_source_ranks_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hBMargin :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hBsrc.transposeVecNorm2LowerMargin)
    (hStackMargin :
      theorem20_10_householder_gammaA_conservativeRhs fp r p q *
          frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases theorem20_10_partB_backward_error_of_householder_components_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad,
      hmethod⟩
  have hcond :
      LSEFullRowRank (fun i j => B i j + DeltaB i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j) :=
    theorem20_8_conditions20_24_of_frobNormRect_bounds_lt_margins
      (A := A) (DeltaA := DeltaA) (B := B) (DeltaB := DeltaB)
      (cA := theorem20_10_householder_gammaA_conservativeRhs fp r p q *
        frobNormRect A)
      (cB := theorem20_10_householder_gammaB fp r p q * frobNormRect B)
      hBsrc hStack hDeltaA hDeltaB hBMargin hStackMargin
  refine
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltaArep, hDeltaBrep,
      hDeltabrep, hDeltadrep, hDeltaA, hDeltaB, hDeltab, hDeltad,
      ?_⟩
  exact hmethod hcond.1 hcond.2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package with source-rank radius preservation.

    This packages
    `theorem20_10_partB_backward_error_of_householder_components_source_ranks_conservative_gamma`
    behind one conservative rank-budget condition: the sum of the verified
    conservative `A` component budget and the Householder `B` component budget
    is strictly below the minimum source rank margin.  It still leaves the
    concrete roundoff-smallness proof for this radius and the final
    computed-vector identification as separate obligations. -/
theorem theorem20_10_partB_backward_error_of_householder_components_source_ranks_rank_radius_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hMargin :
      theorem20_10_householder_componentSourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hBsrc hStack) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  rcases
    theorem20_10_householder_componentSourceRankMargins_of_budget_lt_sourceRankRadius
      fp A B hBsrc hStack hvalidA hMargin with
    ⟨hBMargin, hStackMargin⟩
  exact
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      hBMargin hStackMargin
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package from a compact max-gamma source-rank radius condition.

    This is the same conservative component route as
    `theorem20_10_partB_backward_error_of_householder_components_source_ranks_rank_radius_conservative_gamma`,
    but the caller supplies the readable sufficient condition
    `max(gammaA, gammaB) * (||A||_F + ||B||_F) < sourceRankRadius` directly. -/
theorem theorem20_10_partB_backward_error_of_householder_components_source_ranks_max_gamma_sum_bound_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) *
          (frobNormRect A + frobNormRect B) <
        theorem20_10_householder_sourceRankRadius hBsrc hStack) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  exact
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_rank_radius_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_sum_bound
        fp A B hBsrc hStack hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package from the conservative source-rank gamma threshold.

    This wrapper exposes the compact positive threshold condition on the larger
    of the conservative `A` and `B` coefficients.  The threshold expands to the
    source-rank radius divided by `max(1, ||A||_F + ||B||_F)`, so the resulting
    theorem retains the same perturbation and minimizer conclusion as the
    rank-radius package. -/
theorem theorem20_10_partB_backward_error_of_householder_components_source_ranks_gamma_threshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hBsrc hStack) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  exact
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_rank_radius_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack
      (theorem20_10_householder_componentSourceRankBudget_lt_sourceRankRadius_of_max_gamma_lt_sourceRankGammaThreshold
        fp A B hBsrc hStack hvalidA hvalidB hsmall)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package from a linear unit-roundoff source-rank threshold.

    This is the component-route analogue of the constructed returned-vector
    unit-roundoff wrapper: it derives the conservative max-gamma source-rank
    threshold from explicit half-radius guards and the dimension-only
    `theorem20_10_householder_componentUnitRoundoffCoefficient`. -/
theorem theorem20_10_partB_backward_error_of_householder_components_source_ranks_unit_roundoff_threshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hsmallA :
      ((((p + q) * householderConstructApplyGammaIndex (r + q) : ℕ) : ℝ) *
        fp.u ≤ 1 / 2))
    (hsmallB :
      ((((p * householderConstructApplyGammaIndex (p + q) : ℕ) : ℝ) *
        fp.u) ≤ 1 / 2))
    (hhalf :
      ((householderQRRhsPanelGammaClosedGrowthIndex (r + q) q : ℝ) *
        fp.u ≤ 1 / 2))
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hunit :
      theorem20_10_householder_componentUnitRoundoffCoefficient r p q *
          fp.u <
        theorem20_10_householder_sourceRankGammaThreshold hBsrc hStack) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hsmall :
      max (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
          (theorem20_10_householder_gammaB fp r p q) <
        theorem20_10_householder_sourceRankGammaThreshold hBsrc hStack :=
    theorem20_10_householder_component_max_gamma_lt_sourceRankGammaThreshold_of_unit_roundoff_bound
      fp hBsrc hStack (by omega) hsmallA hsmallB hhalf hunit
  exact
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_gamma_threshold_conservative_gamma
      fp A B Q b d xhat hQ hp hq hvalidA hvalidB hhalf hBsrc hStack hsmall
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package from one combined unit-roundoff smallness threshold.

    This is the component-route analogue of
    `..._component_unit_roundoff_smallnessThreshold_composed_conservative_gamma`:
    it derives the three half-radius guards and linear source-rank cap from
    `fp.u < theorem20_10_householder_componentUnitRoundoffSmallnessThreshold`.
    The conclusion is the same concrete component Part B route as the
    four-condition unit-roundoff wrapper. -/
theorem theorem20_10_partB_backward_error_of_householder_components_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Q i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Q)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Q) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Q)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, hhalf, hunit⟩
  exact
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_unit_roundoff_threshold_conservative_gamma
      fp A B Q b d xhat hQ hp hq hsmallA hsmallB hhalf hBsrc hStack hunit
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b), concrete Householder
    component package with the `Bᵀ` Householder factor fixed to the actual
    rounded panel `Qb`.

    This is the source-rank/unit-roundoff component route with the abstract
    orthogonal `Q` input specialized to
    `fl_householderQRPanel_Q fp (p+q) p (Bᵀ)`.  Orthogonality of this computed
    `Qb` is derived from the existing concrete `Bᵀ` Householder block theorem,
    so callers no longer supply an arbitrary exact orthogonal factor for the
    constraint side.  The theorem still leaves the final returned-vector
    identification separate: `xhat` is an explicit input to the component
    package. -/
theorem theorem20_10_partB_backward_error_of_householder_components_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Qb i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Qb))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Qb)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Qb) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Qb)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
    fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨_hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hQb : IsOrthogonal (p + q) Qb := by
    rcases
      theorem20_10_householder_B_transpose_perturbed_constraint_block
        (r := r) fp B hp hvalidB with
      ⟨_DeltaB, _hDeltaBrep, hQb, _hS, _hblock, _hDeltaB⟩
    simpa [Qb] using hQb
  exact
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B Qb b d xhat hQb hp hq hBsrc hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    named component-route wrapper for the source-rank/unit-roundoff theorem. -/
theorem theorem20_10_householder_component_partB_route_of_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (Q : Fin (p + q) → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hQ : IsOrthogonal (p + q) Q)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    Theorem20_10HouseholderComponentPartBRoute fp A B Q b d xhat := by
  simpa [Theorem20_10HouseholderComponentPartBRoute] using
    theorem20_10_partB_backward_error_of_householder_components_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B Q b d xhat hQ hp hq hBsrc hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    component-route wrapper with `Q` fixed to the computed `Bᵀ` Householder
    panel. -/
theorem theorem20_10_householder_component_partB_route_of_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    Theorem20_10HouseholderComponentPartBRoute fp A B Qb b d xhat := by
  dsimp
  simpa [Theorem20_10HouseholderComponentPartBRoute] using
    theorem20_10_partB_backward_error_of_householder_components_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B b d xhat hp hq hBsrc hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    constructed rounded Householder returned-vector route under the combined
    unit-roundoff smallness threshold, stated via the named route predicate. -/
theorem theorem20_10_constructed_householder_returned_vector_partB_route_exists_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    ∃ xhat : Fin (p + q) → ℝ,
      Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute
        fp A B b d xhat := by
  simpa [Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute] using
    theorem20_10_householder_constructed_gqr_reversed_rhs_tail_partB_exists_xhat_minimizer_of_source_ranks_component_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    returned-vector bridge between the constructed rounded Householder GQR path
    and the computed-`Bᵀ` concrete component route.

    The theorem produces the same `xhat` from the constructed transformed-tail
    GQR returned-vector theorem, then attaches the concrete Householder
    component Part B route with `Q` fixed to
    `fl_householderQRPanel_Q fp (p+q) p (Bᵀ)`.  This removes the free `xhat`
    from the computed-`Bᵀ` component API at the existential returned-vector
    level; a deterministic external implementation identity is still separate. -/
theorem theorem20_10_constructed_returned_vector_with_computed_B_transpose_Q_component_partB_route_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    ∃ xhat : Fin (p + q) → ℝ,
      Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute
        fp A B b d xhat ∧
      Theorem20_10HouseholderComponentPartBRoute
        fp A B Qb b d xhat := by
  dsimp
  rcases
    theorem20_10_constructed_householder_returned_vector_partB_route_exists_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu with
    ⟨xhat, hconstructed⟩
  refine ⟨xhat, hconstructed, ?_⟩
  simpa [Theorem20_10HouseholderComponentPartBRoute] using
    theorem20_10_partB_backward_error_of_householder_components_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B b d xhat hp hq hB hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    returned-vector bridge between the constructed rounded Householder GQR path
    and the computed-`Bᵀ` concrete component certificate route.

This is the certificate-boundary companion to
`theorem20_10_constructed_returned_vector_with_computed_B_transpose_Q_component_partB_route_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma`:
it produces the constructed transformed-tail returned vector and attaches the
reusable `Theorem20_10HouseholderComponentPartBCertificateRoute` with `Q` fixed
to the computed `Bᵀ` Householder panel. -/
theorem theorem20_10_constructed_returned_vector_with_computed_B_transpose_Q_component_partB_certificate_route_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    ∃ xhat : Fin (p + q) → ℝ,
      Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute
        fp A B b d xhat ∧
      Theorem20_10HouseholderComponentPartBCertificateRoute
        fp A B Qb b d xhat := by
  dsimp
  rcases
    theorem20_10_constructed_householder_returned_vector_partB_route_exists_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu with
    ⟨xhat, hconstructed⟩
  refine ⟨xhat, hconstructed, ?_⟩
  exact
    theorem20_10_householder_component_partB_certificate_route_of_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B b d xhat hp hq hB hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    a named constructed returned vector for the rounded Householder GQR route.

    This is a noncomputable choice from the proved existential bridge above.
    It is useful for downstream theorem statements that should not keep an
    explicit free `xhat` argument.  It is not an executable identity for an
    external implementation of GQR. -/
noncomputable def theorem20_10_constructed_householder_returned_xhat
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    Fin (p + q) → ℝ :=
  Classical.choose
    (theorem20_10_constructed_returned_vector_with_computed_B_transpose_Q_component_partB_route_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B b d hp hq hB hStack hu)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    specification of the named constructed returned vector.

    The chosen vector satisfies both the constructed rounded Householder
    returned-vector route and the concrete component Part B route with `Q`
    fixed to the computed `Bᵀ` Householder panel. -/
theorem theorem20_10_constructed_householder_returned_xhat_spec
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute
        fp A B b d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu) ∧
      Theorem20_10HouseholderComponentPartBRoute
        fp A B Qb b d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu) := by
  simpa [theorem20_10_constructed_householder_returned_xhat] using
    Classical.choose_spec
      (theorem20_10_constructed_returned_vector_with_computed_B_transpose_Q_component_partB_route_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
        fp A B b d hp hq hB hStack hu)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    transformed-tail identity for the named constructed rounded Householder
    returned vector.

    The full named-vector spec packages both the constructed returned-vector
    route and the computed-`Bᵀ` component route.  This lemma extracts the
    implementation-facing equality from the constructed route: for the
    constructed rounded `Bᵀ`/reversed-`AQ2` GQR record, the named vector is
    exactly `theorem20_10_gqr_xhat_of_transformed_tail`. -/
theorem theorem20_10_constructed_householder_returned_xhat_eq_transformed_tail_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        theorem20_10_constructed_householder_returned_xhat
            fp A B b d hp hq hB hStack hu =
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d := by
  have hspec :=
    theorem20_10_constructed_householder_returned_xhat_spec
      fp A B b d hp hq hB hStack hu
  dsimp [Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute] at hspec
  rcases hspec.1 with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat, _hrest⟩
  exact
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    triangular-solve perturbation witnesses for the named constructed rounded
    Householder returned vector.

    The previous lemma identifies the named proof-level vector with the
    transformed-tail GQR vector for the constructed perturbed record.  This
    wrapper transports the existing `DeltaS`/`DeltaL22` forward-substitution
    backward-error certificate to that named vector under the same single
    source-rank unit-roundoff threshold. -/
theorem theorem20_10_constructed_householder_returned_xhat_triangular_solve_frob_perturbation_bound_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        theorem20_10_constructed_householder_returned_xhat
            fp A B b d hp hq hB hStack hu =
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        ((∀ i : Fin p, hpert.S i i ≠ 0) →
          (∀ i : Fin q, hpert.L22 i i ≠ 0) →
          ∃ (DeltaS : Fin p → Fin p → ℝ)
            (DeltaL22 : Fin q → Fin q → ℝ),
            (∀ i j, |DeltaS i j| ≤ gamma fp p * |hpert.S i j|) ∧
            (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |hpert.L22 i j|) ∧
            frobNormRect DeltaS ≤ gamma fp p * frobNormRect hpert.S ∧
            frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect hpert.L22 ∧
            rectMatMulVec (fun i j => hpert.S i j + DeltaS i j)
              (theorem20_10_gqr_y1hat fp hpert d) = d ∧
            rectMatMulVec (fun i j => hpert.L22 i j + DeltaL22 i j)
              (theorem20_10_gqr_y2hat_of_transformed_tail fp hpert beta d) =
                theorem20_10_gqr_rhs2hat_of_transformed_tail fp hpert beta d ∧
            theorem20_10_constructed_householder_returned_xhat
                fp A B b d hp hq hB hStack hu =
              matMulVec (p + q) hpert.Q
                (Fin.append
                  (theorem20_10_gqr_y1hat fp hpert d)
                  (theorem20_10_gqr_y2hat_of_transformed_tail
                    fp hpert beta d))) := by
  rcases
    theorem20_10_constructed_householder_returned_xhat_eq_transformed_tail_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat⟩
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hB hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hvalidS : gammaValid fp p := by
    exact gammaValid_mono fp
      (Nat.le_mul_of_pos_right p hKB_pos) hvalidB
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
    le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hvalidL22 : gammaValid fp q :=
    gammaValid_mono fp hidxA_ge_q hvalidA
  refine
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat, ?_⟩
  intro hSdiag hL22diag
  rcases
    theorem20_10_gqr_xhat_of_transformed_tail_triangular_solve_frob_perturbation_bound
      fp hpert _ d hSdiag hL22diag hvalidS hvalidL22 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeqTri, hL22eq, hxhatTail⟩
  exact
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeqTri, hL22eq,
      hxhat.trans hxhatTail⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10:
    rank-preserved triangular-solve perturbation witnesses for the named
    constructed rounded Householder returned vector.

    This strengthens
    `theorem20_10_constructed_householder_returned_xhat_triangular_solve_frob_perturbation_bound_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma`
    by deriving the constructed perturbed rank assumptions, and hence the
    `S`/`L22` diagonal conditions, from the same source-rank unit-roundoff
    threshold. -/
theorem theorem20_10_constructed_householder_returned_xhat_triangular_solve_frob_perturbation_bound_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma_rank_preserved
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        theorem20_10_constructed_householder_returned_xhat
            fp A B b d hp hq hB hStack hu =
          theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        (LSEFullRowRank (fun i j => B i j + DeltaB0 i j) ∧
          LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA0 i j)
            (fun i j => B i j + DeltaB0 i j)) ∧
        ∃ (DeltaS : Fin p → Fin p → ℝ)
          (DeltaL22 : Fin q → Fin q → ℝ),
          (∀ i j, |DeltaS i j| ≤ gamma fp p * |hpert.S i j|) ∧
          (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |hpert.L22 i j|) ∧
          frobNormRect DeltaS ≤ gamma fp p * frobNormRect hpert.S ∧
          frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect hpert.L22 ∧
          rectMatMulVec (fun i j => hpert.S i j + DeltaS i j)
            (theorem20_10_gqr_y1hat fp hpert d) = d ∧
          rectMatMulVec (fun i j => hpert.L22 i j + DeltaL22 i j)
            (theorem20_10_gqr_y2hat_of_transformed_tail fp hpert beta d) =
              theorem20_10_gqr_rhs2hat_of_transformed_tail fp hpert beta d ∧
          theorem20_10_constructed_householder_returned_xhat
              fp A B b d hp hq hB hStack hu =
            matMulVec (p + q) hpert.Q
              (Fin.append
                (theorem20_10_gqr_y1hat fp hpert d)
                (theorem20_10_gqr_y2hat_of_transformed_tail
                  fp hpert beta d)) := by
  rcases
    theorem20_10_constructed_householder_returned_xhat_triangular_solve_frob_perturbation_bound_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat, htri⟩
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hB hStack hp hq hu with
    ⟨hsmallA, _hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hAterm_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q * frobNormRect A :=
    mul_nonneg hgammaA_nonneg (frobNormRect_nonneg A)
  have hRankBudget :
      theorem20_10_householder_sourceRankBudget fp A B <
        theorem20_10_householder_sourceRankRadius hB hStack :=
    theorem20_10_householder_sourceRankBudget_lt_sourceRankRadius_of_unit_roundoff_smallnessThreshold
      fp A B hB hStack hp hq hu
  have hBMargin :
      theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hB.transposeVecNorm2LowerMargin := by
    calc
      theorem20_10_householder_gammaB fp r p q * frobNormRect B
          ≤ theorem20_10_householder_sourceRankBudget fp A B := by
            dsimp [theorem20_10_householder_sourceRankBudget]
            linarith
      _ < theorem20_10_householder_sourceRankRadius hB hStack := hRankBudget
      _ ≤ hB.transposeVecNorm2LowerMargin := by
            exact min_le_left _ _
  have hStackMargin :
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B <
        hStack.vecNorm2LowerMargin := by
    calc
      theorem20_10_householder_gammaA fp r p q * frobNormRect A +
          theorem20_10_householder_gammaB fp r p q * frobNormRect B
          = theorem20_10_householder_sourceRankBudget fp A B := by
            rfl
      _ < theorem20_10_householder_sourceRankRadius hB hStack := hRankBudget
      _ ≤ hStack.vecNorm2LowerMargin := by
            exact min_le_right _ _
  have hrank :
      LSEFullRowRank (fun i j => B i j + DeltaB0 i j) ∧
        LSEStackedFullColumnRank
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j) :=
    theorem20_8_conditions20_24_of_frobNormRect_bounds_lt_margins
      hB hStack hDeltaA0 hDeltaB0 hBMargin hStackMargin
  have hdiag :
      (∀ i : Fin p, hpert.S i i ≠ 0) ∧
        (∀ i : Fin q, hpert.L22 i i ≠ 0) :=
    (hpert.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1 hrank
  rcases htri hdiag.1 hdiag.2 with
    ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound,
      hDeltaSfrob, hDeltaL22frob, hSeqTri, hL22eq, hxhatTail⟩
  exact
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat, hrank,
      DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, hDeltaSfrob,
      hDeltaL22frob, hSeqTri, hL22eq, hxhatTail⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    named returned-vector triangular-solve and exact perturbed-minimizer
    package under the single source-rank unit-roundoff threshold.

    The constructed GQR/triangular-solve witnesses and the source-facing exact
    perturbed LSE minimizer witnesses are kept separate: the former expose the
    computed triangular solves for the constructed rounded GQR record, while
    the latter provide the backward-error/minimizer conclusion for the same
    named returned vector. -/
theorem theorem20_10_constructed_householder_returned_xhat_rank_preserved_triangular_solve_and_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let Rb : Fin (p + q) → Fin p → ℝ :=
      fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)
    let S : Fin p → Fin p → ℝ :=
      matTranspose (fun i : Fin p => fun j : Fin p =>
        Rb (Fin.castAdd q i) j)
    let beta : Fin q → ℝ :=
      theorem20_10_householder_reversed_AQ2_rhs_tail fp A Qb b
    let gammaA : ℝ :=
      theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB : ℝ :=
      theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ DeltaA0 : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB0 : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab0 : Fin (r + q) → ℝ,
      (∀ i j,
        B i j + DeltaB0 i j =
          matMulRect (p + q) (p + q) p Qb Rb j i) ∧
      frobNormRect DeltaA0 ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB0 ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab0 ≤
        theorem20_10_householder_rhs_conservative_gamma fp r p q *
          vecNorm2 b ∧
      ∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA0 i j)
          (fun i j => B i j + DeltaB0 i j),
        hpert.Q = Qb ∧ hpert.S = S ∧
        (∀ j : Fin q,
          matMulVec (r + q) (matTranspose hpert.U)
              (fun k => b k + Deltab0 k) (Fin.natAdd r j) =
            beta j) ∧
        xhat = theorem20_10_gqr_xhat_of_transformed_tail fp hpert beta d ∧
        (LSEFullRowRank (fun i j => B i j + DeltaB0 i j) ∧
          LSEStackedFullColumnRank
            (fun i j => A i j + DeltaA0 i j)
            (fun i j => B i j + DeltaB0 i j)) ∧
        (∃ (DeltaS : Fin p → Fin p → ℝ)
          (DeltaL22 : Fin q → Fin q → ℝ),
          (∀ i j, |DeltaS i j| ≤ gamma fp p * |hpert.S i j|) ∧
          (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |hpert.L22 i j|) ∧
          frobNormRect DeltaS ≤ gamma fp p * frobNormRect hpert.S ∧
          frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect hpert.L22 ∧
          rectMatMulVec (fun i j => hpert.S i j + DeltaS i j)
            (theorem20_10_gqr_y1hat fp hpert d) = d ∧
          rectMatMulVec (fun i j => hpert.L22 i j + DeltaL22 i j)
            (theorem20_10_gqr_y2hat_of_transformed_tail fp hpert beta d) =
              theorem20_10_gqr_rhs2hat_of_transformed_tail fp hpert beta d ∧
          xhat =
            matMulVec (p + q) hpert.Q
              (Fin.append
                (theorem20_10_gqr_y1hat fp hpert d)
                (theorem20_10_gqr_y2hat_of_transformed_tail
                  fp hpert beta d))) ∧
        ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
        ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
        ∃ Deltab : Fin (r + q) → ℝ,
          frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
          frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
          vecNorm2 Deltab ≤
            gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d xhat ∧
          (∃! x : Fin (p + q) → ℝ,
            IsLSEMinimizer
              (fun i j => A i j + DeltaA i j)
              (fun i => b i + Deltab i)
              (fun i j => B i j + DeltaB i j) d x) := by
  dsimp
  rcases
    theorem20_10_constructed_householder_returned_xhat_triangular_solve_frob_perturbation_bound_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma_rank_preserved
      fp A B b d hp hq hB hStack hu with
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat, hrank,
      DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, hDeltaSfrob,
      hDeltaL22frob, hSeqTri, hL22eq, hxhatTail⟩
  have hspec :=
    theorem20_10_constructed_householder_returned_xhat_spec
      fp A B b d hp hq hB hStack hu
  dsimp [Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute] at hspec
  rcases hspec.1 with
    ⟨_DeltaA0_spec, _DeltaB0_spec, _Deltab0_spec, _hDeltaBrep_spec,
      _hDeltaA0_spec, _hDeltaB0_spec, _hDeltab0_spec, _hpert_spec,
      _hQeq_spec, _hSeq_spec, _htail_spec, _hxhat_spec, hminRaw⟩
  rcases hminRaw with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltad, hDeltaA, hDeltaB,
      hDeltab, _hDeltadBound, hxhatMinRaw, huniqueRaw⟩
  have hxhatMin :
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu) := by
    simpa [hDeltad] using hxhatMinRaw
  have hunique :
      ∃! x : Fin (p + q) → ℝ,
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j) d x := by
    rcases huniqueRaw with ⟨x, hx, huniq⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [hDeltad] using hx
    · intro y hy
      exact huniq y (by simpa [hDeltad] using hy)
  exact
    ⟨DeltaA0, DeltaB0, Deltab0, hDeltaBrep, hDeltaA0, hDeltaB0,
      hDeltab0, hpert, hQeq, hSeq, htail, hxhat, hrank,
      ⟨DeltaS, DeltaL22, hDeltaSbound, hDeltaL22bound, hDeltaSfrob,
        hDeltaL22frob, hSeqTri, hL22eq, hxhatTail⟩,
      DeltaA, DeltaB, Deltab, hDeltaA, hDeltaB, hDeltab, hxhatMin,
      hunique⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    certificate specification of the named constructed returned vector.

The chosen proof-level returned vector satisfies the constructed rounded
Householder route and, independently, the concrete computed-`Bᵀ` component
certificate route.  This keeps the reusable Part B perturbation certificate
available for downstream wrappers without unpacking the full exact method
package. -/
theorem theorem20_10_constructed_householder_returned_xhat_certificate_spec
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    Theorem20_10ConstructedHouseholderReturnedVectorPartBRoute
        fp A B b d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu) ∧
      Theorem20_10HouseholderComponentPartBCertificateRoute
        fp A B Qb b d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu) := by
  dsimp
  constructor
  · exact
      (theorem20_10_constructed_householder_returned_xhat_spec
        fp A B b d hp hq hB hStack hu).1
  · exact
      theorem20_10_householder_component_partB_certificate_route_of_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
        fp A B b d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu)
        hp hq hB hStack hu
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    direct reusable Part B perturbation certificate for the named constructed
    rounded Householder returned vector. -/
theorem theorem20_10_constructed_householder_returned_xhat_partB_certificate_of_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d
        (theorem20_10_constructed_householder_returned_xhat
          fp A B b d hp hq hB hStack hu)
        (theorem20_10_householder_gammaA_conservativeRhs fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) := by
  exact
    Theorem20_10HouseholderComponentPartBCertificateRoute.partB_certificate
      (Q := fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
      (theorem20_10_constructed_householder_returned_xhat_certificate_spec
        fp A B b d hp hq hB hStack hu).2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    concise backward-error package for the named constructed rounded
    Householder returned vector.

This is the certificate-free companion to
`theorem20_10_constructed_householder_returned_xhat_partB_certificate_of_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma`.
It hides the reusable Part B certificate object and exposes directly the
source-shaped perturbation bounds and exact perturbed GQR/minimizer core for the
chosen proof-level returned vector. -/
theorem theorem20_10_partB_backward_error_of_constructed_householder_returned_xhat_certificate_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases
    theorem20_10_constructed_householder_returned_xhat_partB_certificate_of_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
      fp A B b d hp hq hB hStack hu with
    ⟨cert⟩
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, cert.Deltad, cert.hDeltaA,
      cert.hDeltaB, cert.hDeltab, cert.hDeltad,
      GeneralizedQRFactorization.exists_unique_method_solution_of_theorem20_10_perturbed_d
        A cert.DeltaA B cert.DeltaB b cert.Deltab d cert.Deltad
        cert.hB cert.hstack⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    computed-`Bᵀ` concrete component Part B route for the named constructed
    returned vector.

    This is the concrete perturbation/minimizer package of
    `theorem20_10_partB_backward_error_of_householder_components_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma`,
    with the free `xhat` specialized to
    `theorem20_10_constructed_householder_returned_xhat`.  It is still a
    constructed proof-level returned vector rather than an executable identity
    for an external GQR implementation. -/
theorem theorem20_10_partB_backward_error_of_constructed_householder_returned_xhat_computed_B_transpose_Q_source_ranks_unit_roundoff_smallnessThreshold_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let gammaA : ℝ := theorem20_10_householder_gammaA_conservativeRhs fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ (DeltaA : Fin (r + q) → Fin (p + q) → ℝ)
      (DeltaB : Fin p → Fin (p + q) → ℝ)
      (Deltab : Fin (r + q) → ℝ)
      (Deltad : Fin p → ℝ),
      (∀ i j,
        gqrAQ2Block (fun i j => A i j + DeltaA i j) Qb i j =
          matMulRect (r + q) (r + q) q
            (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Qb))
            (fl_householderQRPanel_R fp (r + q) q (gqrAQ2Block A Qb)) i j) ∧
      (∀ i j,
        B i j + DeltaB i j =
          matMulRect (p + q) (p + q) p
            (fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B))
            (fl_householderQRPanel_R fp (p + q) p (finiteTranspose B)) j i) ∧
      (∀ i,
        fl_householderQRPanel_rhs fp (r + q) q (gqrAQ2Block A Qb) b i =
          matMulVec (r + q)
            (matTranspose
              (fl_householderQRPanel_Q fp (r + q) q (gqrAQ2Block A Qb)))
            (fun k => b k + Deltab k) i) ∧
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  have hspec :=
    theorem20_10_constructed_householder_returned_xhat_spec
      fp A B b d hp hq hB hStack hu
  dsimp at hspec
  simpa [Theorem20_10HouseholderComponentPartBRoute] using hspec.2
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    exact perturbed minimizer package for the named constructed returned
    vector.

    This unwraps the constructed returned-vector route for
    `theorem20_10_constructed_householder_returned_xhat`, exposing directly
    that the named vector is an exact minimizer of a perturbed LSE problem with
    the composed conservative bounds.  The route used here keeps the final
    constraint right-hand side unperturbed (`Deltad = 0`). -/
theorem theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let gammaA : ℝ :=
      theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB : ℝ :=
      theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      Deltad = (0 : Fin p → ℝ) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j)
        (fun i => d i + Deltad i) xhat ∧
      (∃! x : Fin (p + q) → ℝ,
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j)
          (fun i => d i + Deltad i) x) := by
  have hspec :=
    theorem20_10_constructed_householder_returned_xhat_spec
      fp A B b d hp hq hB hStack hu
  dsimp at hspec ⊢
  rcases hspec.1 with
    ⟨_DeltaA0, _DeltaB0, _Deltab0, _hDeltaB0rep, _hDeltaA0,
      _hDeltaB0, _hDeltab0, _hpert, _hQeq, _hSeq, _hb_tail, _hxhat,
      htail⟩
  dsimp at htail
  exact htail
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    source-facing exact perturbed minimizer package for the named constructed
    returned vector.

    This is the previous theorem with the zero constraint perturbation removed
    from the statement: the exact perturbed LSE problem uses the original
    constraint right-hand side `d`. -/
theorem theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_unperturbed_constraint_rhs_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let gammaA : ℝ :=
      theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB : ℝ :=
      theorem20_10_householder_composed_partA_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d xhat ∧
      (∃! x : Fin (p + q) → ℝ,
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j) d x) := by
  have hraw :=
    theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu
  dsimp at hraw ⊢
  rcases hraw with
    ⟨DeltaA, DeltaB, Deltab, Deltad, hDeltad, hDeltaA, hDeltaB,
      hDeltab, _hDeltad, hxhat, hunique⟩
  refine ⟨DeltaA, DeltaB, Deltab, hDeltaA, hDeltaB, hDeltab, ?_, ?_⟩
  · simpa [hDeltad] using hxhat
  · rcases hunique with ⟨x, hx, huniq⟩
    refine ⟨x, ?_, ?_⟩
    · simpa [hDeltad] using hx
    · intro y hy
      exact huniq y (by simpa [hDeltad] using hy)
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    combined source-rank/unit-roundoff surface for the named constructed
    returned vector.

    The same proof-level `xhat` both satisfies the concrete computed-`B^T`
    Householder component route and has a source-facing exact perturbed LSE
    minimizer package with the original constraint right-hand side `d`. -/
theorem theorem20_10_constructed_householder_returned_xhat_component_route_and_unperturbed_constraint_rhs_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let gammaA : ℝ :=
      theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB : ℝ :=
      theorem20_10_householder_composed_partA_gammaB fp r p q
    Theorem20_10HouseholderComponentPartBRoute fp A B Qb b d xhat ∧
      ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      ∃ Deltab : Fin (r + q) → ℝ,
        frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
        frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
        vecNorm2 Deltab ≤
          gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j) d xhat ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x) := by
  have hspec :=
    theorem20_10_constructed_householder_returned_xhat_spec
      fp A B b d hp hq hB hStack hu
  have hclean :=
    theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_unperturbed_constraint_rhs_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu
  dsimp at hspec hclean ⊢
  exact ⟨hspec.2, hclean⟩
/-- Higham, 2nd ed., Chapter 20, Theorem 20.10(b):
    certificate-route and unperturbed-constraint package for the named
    constructed returned vector.

    This is the certificate-route analogue of
    `theorem20_10_constructed_householder_returned_xhat_component_route_and_unperturbed_constraint_rhs_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma`.
    It keeps the reusable Part B perturbation certificate route available while
    pairing it with the cleaner exact perturbed minimizer statement whose
    constraint right-hand side is the original `d`. -/
theorem theorem20_10_constructed_householder_returned_xhat_component_certificate_route_and_unperturbed_constraint_rhs_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
    {r p q : ℕ} (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hB hStack) :
    let xhat : Fin (p + q) → ℝ :=
      theorem20_10_constructed_householder_returned_xhat
        fp A B b d hp hq hB hStack hu
    let Qb : Fin (p + q) → Fin (p + q) → ℝ :=
      fl_householderQRPanel_Q fp (p + q) p (finiteTranspose B)
    let gammaA : ℝ :=
      theorem20_10_householder_composed_partA_gammaA fp r p q
    let gammaB : ℝ :=
      theorem20_10_householder_composed_partA_gammaB fp r p q
    Theorem20_10HouseholderComponentPartBCertificateRoute fp A B Qb b d xhat ∧
      ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
      ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
      ∃ Deltab : Fin (r + q) → ℝ,
        frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
        frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
        vecNorm2 Deltab ≤
          gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
        IsLSEMinimizer
          (fun i j => A i j + DeltaA i j)
          (fun i => b i + Deltab i)
          (fun i j => B i j + DeltaB i j) d xhat ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x) := by
  have hspec :=
    theorem20_10_constructed_householder_returned_xhat_certificate_spec
      fp A B b d hp hq hB hStack hu
  have hclean :=
    theorem20_10_constructed_householder_returned_xhat_exact_perturbed_minimizer_unperturbed_constraint_rhs_of_source_ranks_unit_roundoff_smallnessThreshold_composed_conservative_gamma
      fp A B b d hp hq hB hStack hu
  dsimp at hspec hclean ⊢
  exact ⟨hspec.2, hclean⟩
/-- Theorem 20.10(a) certificate handoff specialized to the Householder
    `gamma_tilde_mn` and `gamma_tilde_np` coefficients. -/
theorem theorem20_10_partA_mixed_stability_of_householder_gamma_certificate
    {r p q : ℕ}
    (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (cert :
      Theorem20_10PartAPerturbationCertificate A B b d xhat
        (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer Apert bpert Bpert d x ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = d ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert d
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert d x0)) :=
  theorem20_10_partA_mixed_stability_of_perturbation_certificate
    A B b d xhat cert
/-- Theorem 20.10(a), exact transformed-RHS constructed-source route specialized
    to the Householder `gamma_tilde_mn` and `gamma_tilde_np` coefficients.

    This is the strongest currently proved source-facing Part A theorem for the
    supplied-GQR path: the matrix perturbations and triangular-solve effects are
    constructed and bounded with the printed coefficient names.  The rounded
    Householder RHS-transform bridge remains separate, so this theorem uses the
    exact transformed RHS named by `theorem20_10_gqr_xhat`. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) := by
    exact le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hidxB_ge_p :
      p ≤ p * householderConstructApplyGammaIndex (p + q) :=
    Nat.le_mul_of_pos_right p hKB_pos
  have hgammaA_ge :
      gamma fp q ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxA_ge_q hvalidA
  have hgammaB_ge :
      gamma fp p ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxB_ge_p hvalidB
  exact
    theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs
      fp h b d
      (theorem20_10_householder_gammaA fp r p q)
      (theorem20_10_householder_gammaB fp r p q)
      hgammaA_nonneg hgammaB_nonneg hgammaA_ge hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22
/-- Theorem 20.10(a), exact transformed-RHS constructed-source certificate
    specialized to the Householder `gamma_tilde_mn` and `gamma_tilde_np`
    coefficients.

    This certificate form is the reusable handoff into the Part B backward-error
    bridge: it keeps the exact transformed right-hand side
    `theorem20_10_gqr_xhat` and the printed Householder gamma coefficients,
    without claiming the rounded RHS-transform or final computed-vector path. -/
theorem theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d)
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q)) := by
  have hKA_ge_two : 2 ≤ householderConstructApplyGammaIndex (r + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKB_ge_two : 2 ≤ householderConstructApplyGammaIndex (p + q) := by
    dsimp [householderConstructApplyGammaIndex]
    omega
  have hKA_pos : 0 < householderConstructApplyGammaIndex (r + q) := by
    omega
  have hKB_pos : 0 < householderConstructApplyGammaIndex (p + q) := by
    omega
  have hvalid2S : gammaValid fp (2 * p) := by
    apply gammaValid_mono fp _ hvalidB
    calc
      2 * p = p * 2 := by omega
      _ ≤ p * householderConstructApplyGammaIndex (p + q) :=
          Nat.mul_le_mul_left p hKB_ge_two
  have hvalid2L22 : gammaValid fp (2 * q) := by
    apply gammaValid_mono fp _ hvalidA
    calc
      2 * q ≤ 2 * (p + q) := Nat.mul_le_mul_left 2 (by omega)
      _ = (p + q) * 2 := by omega
      _ ≤ (p + q) * householderConstructApplyGammaIndex (r + q) :=
          Nat.mul_le_mul_left (p + q) hKA_ge_two
  have hgammaA_nonneg :
      0 ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidA
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  have hidxA_ge_q :
      q ≤ (p + q) * householderConstructApplyGammaIndex (r + q) := by
    exact le_trans (by omega)
      (Nat.le_mul_of_pos_right (p + q) hKA_pos)
  have hidxB_ge_p :
      p ≤ p * householderConstructApplyGammaIndex (p + q) :=
    Nat.le_mul_of_pos_right p hKB_pos
  have hgammaA_ge :
      gamma fp q ≤ theorem20_10_householder_gammaA fp r p q := by
    simpa [theorem20_10_householder_gammaA, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxA_ge_q hvalidA
  have hgammaB_ge :
      gamma fp p ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB, H19.Theorem19_4.gamma_tilde] using
      gamma_mono fp hidxB_ge_p hvalidB
  exact
    theorem20_10_partA_certificate_of_constructed_perturbed_source_blocks_of_double_gammaValid_exact_rhs
      fp h b d
      (theorem20_10_householder_gammaA fp r p q)
      (theorem20_10_householder_gammaB fp r p q)
      hgammaA_nonneg hgammaB_nonneg hgammaA_ge hgammaB_ge
      hSdiag hL22diag hvalid2S hvalid2L22
/-- Theorem 20.10(b), exact transformed-RHS constructed-source
    backward-error core specialized to the Householder `gamma_tilde_mn` and
    `gamma_tilde_np` coefficients.

    This feeds the exact transformed-RHS Part A certificate through the generic
    Part A-to-Part B bridge, exposing concrete perturbations, the constraint
    right-hand-side action identity, and the exact perturbed GQR/minimizer core.
    It is still an exact transformed-RHS branch; the rounded RHS-transform and
    final computed-vector identification remain separate obligations. -/
theorem theorem20_10_partB_backward_error_of_constructed_source_exact_rhs_householder_gamma
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hSdiag : ∀ i : Fin p, h.S i i ≠ 0)
    (hL22diag : ∀ i : Fin q, h.L22 i i ≠ 0)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let xhat : Fin (p + q) → ℝ := theorem20_10_gqr_xhat fp h b d
    let gammaA : ℝ := theorem20_10_householder_gammaA fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  rcases
    theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma
      fp h b d hSdiag hL22diag hvalidA hvalidB with
    ⟨_DeltaS, _DeltaL22, _hDeltaSbound, _hDeltaL22bound,
      _hDeltaSfrob, _hDeltaL22frob, hcertA⟩
  exact
    theorem20_10_partB_backward_error_of_nonempty_partA_certificate
      A B b d (theorem20_10_gqr_xhat fp h b d)
      hgammaB_nonneg hcertA
/-- Theorem 20.10(a), exact transformed-RHS constructed-source route with
    source rank hypotheses instead of supplied triangular diagonal hypotheses.

For supplied exact GQR data, source full row rank of `B` and full column rank
of `[A; B]` imply the nonzero `S` and `L22` diagonal conditions needed by the
printed Householder-gamma mixed-stability branch.  The theorem remains an
exact transformed-RHS result: it does not claim the rounded RHS-transform or
final computed-vector path. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hBsrc, hStack⟩
  exact
    theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma
      fp h b d hdiag.1 hdiag.2 hvalidA hvalidB
/-- Theorem 20.10(a), exact transformed-RHS constructed-source certificate
    with source rank hypotheses instead of supplied triangular diagonal
    hypotheses.

This is the nonempty-certificate form of
`theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks`. -/
theorem theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d)
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q)) := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hBsrc, hStack⟩
  exact
    theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma
      fp h b d hdiag.1 hdiag.2 hvalidA hvalidB
/-- Theorem 20.10(b), exact transformed-RHS constructed-source Part B
    certificate with source rank hypotheses.

This is the certificate-level companion to
`theorem20_10_partB_backward_error_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks`.
It removes the supplied triangular diagonal hypotheses for the exact-RHS
Householder-gamma branch while keeping the result at the reusable certificate
boundary.  The rounded RHS-transform and external computed-vector identity
remain separate obligations. -/
theorem theorem20_10_partB_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d
        (theorem20_10_gqr_xhat fp h b d)
        (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) := by
  have hgammaB_nonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p q := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidB
  rcases
    theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
      fp h b d hBsrc hStack hvalidA hvalidB with
    ⟨_DeltaS, _DeltaL22, _hDeltaSbound, _hDeltaL22bound,
      _hDeltaSfrob, _hDeltaL22frob, hcertA⟩
  exact
    theorem20_10_partB_certificate_of_nonempty_partA_certificate
      A B b d (theorem20_10_gqr_xhat fp h b d) hgammaB_nonneg hcertA
/-- Theorem 20.10(b), exact transformed-RHS constructed-source
    backward-error core with source rank hypotheses instead of supplied
    triangular diagonal hypotheses.

For supplied exact GQR data, this removes the caller-facing `S`/`L22`
diagonal side conditions from the printed Householder-gamma Part B core by
deriving them from `LSEFullRowRank B` and `LSEStackedFullColumnRank A B`. -/
theorem theorem20_10_partB_backward_error_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)))
    (hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q))) :
    let xhat : Fin (p + q) → ℝ := theorem20_10_gqr_xhat fp h b d
    let gammaA : ℝ := theorem20_10_householder_gammaA fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  have hdiag :
      (∀ i : Fin p, h.S i i ≠ 0) ∧
        (∀ i : Fin q, h.L22 i i ≠ 0) :=
    (h.fullRowRank_stackedFullColumnRank_iff_s_l22_diag_ne_zero).1
      ⟨hBsrc, hStack⟩
  exact
    theorem20_10_partB_backward_error_of_constructed_source_exact_rhs_householder_gamma
      fp h b d hdiag.1 hdiag.2 hvalidA hvalidB
/-- Theorem 20.10(a), exact transformed-RHS constructed-source mixed
    stability under the combined source-rank unit-roundoff threshold.

This is the one-line-threshold version of
`theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks`:
it derives the two Householder `gammaValid` premises from
`fp.u < theorem20_10_householder_componentUnitRoundoffSmallnessThreshold`.
The result is still the exact transformed-RHS branch; it does not identify the
rounded RHS-transform or an external computed GQR returned vector. -/
theorem theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q),
        theorem20_10_gqr_xhat fp h b d j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤
        theorem20_10_householder_gammaB fp r p q * vecNorm2 x ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = d ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  exact
    theorem20_10_partA_mixed_stability_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
      fp h b d hBsrc hStack hvalidA hvalidB
/-- Theorem 20.10(a), exact transformed-RHS constructed-source certificate
    under the combined source-rank unit-roundoff threshold.

This is the one-line-threshold version of
`theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks`:
it derives the two Householder `gammaValid` premises from
`fp.u < theorem20_10_householder_componentUnitRoundoffSmallnessThreshold`.
The result is still the exact transformed-RHS branch; it does not identify the
rounded RHS-transform or an external computed GQR returned vector. -/
theorem theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    ∃ (DeltaS : Fin p → Fin p → ℝ) (DeltaL22 : Fin q → Fin q → ℝ),
      (∀ i j, |DeltaS i j| ≤ gamma fp p * |h.S i j|) ∧
      (∀ i j, |DeltaL22 i j| ≤ gamma fp q * |h.L22 i j|) ∧
      frobNormRect DeltaS ≤ gamma fp p * frobNormRect h.S ∧
      frobNormRect DeltaL22 ≤ gamma fp q * frobNormRect h.L22 ∧
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d
          (theorem20_10_gqr_xhat fp h b d)
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q)) := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  exact
    theorem20_10_partA_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
      fp h b d hBsrc hStack hvalidA hvalidB
/-- Theorem 20.10(b), exact transformed-RHS constructed-source Part B
    certificate under the combined source-rank unit-roundoff threshold.

This removes the explicit Householder `gammaValid` assumptions from the
exact-RHS certificate boundary, replacing them with the same source-rank
unit-roundoff threshold used by the rounded component route. -/
theorem theorem20_10_partB_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    Nonempty
      (Theorem20_10PartBPerturbationCertificate A B b d
        (theorem20_10_gqr_xhat fp h b d)
        (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  exact
    theorem20_10_partB_certificate_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
      fp h b d hBsrc hStack hvalidA hvalidB
/-- Theorem 20.10(b), exact transformed-RHS constructed-source backward-error
    core under the combined source-rank unit-roundoff threshold.

This is the source-rank/unit-roundoff wrapper for the exact-RHS
Householder-gamma branch.  It keeps the exact transformed right-hand side
`theorem20_10_gqr_xhat`; the rounded RHS-transform and final executable
returned-vector identity remain separate obligations. -/
theorem theorem20_10_partB_backward_error_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks_unit_roundoff_smallnessThreshold
    {r p q : ℕ} (fp : FPModel)
    {A : Fin (r + q) → Fin (p + q) → ℝ}
    {B : Fin p → Fin (p + q) → ℝ}
    (h : GeneralizedQRFactorization r p q A B)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hBsrc : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu :
      fp.u <
        theorem20_10_householder_componentUnitRoundoffSmallnessThreshold hBsrc hStack) :
    let xhat : Fin (p + q) → ℝ := theorem20_10_gqr_xhat fp h b d
    let gammaA : ℝ := theorem20_10_householder_gammaA fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      (∀ i,
        rectMatMulVec (fun i j => B i j + DeltaB i j) xhat i =
          rectMatMulVec B xhat i + Deltad i) ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ hpert : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec hpert.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec hpert.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose hpert.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec hpert.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) hpert.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  rcases
    theorem20_10_householder_component_unit_roundoff_conditions_of_lt_smallnessThreshold
      fp hBsrc hStack hp hq hu with
    ⟨hsmallA, hsmallB, _hhalf, _hunit⟩
  have hvalidA :
      gammaValid fp ((p + q) * householderConstructApplyGammaIndex (r + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallA (by norm_num)
  have hvalidB :
      gammaValid fp (p * householderConstructApplyGammaIndex (p + q)) := by
    unfold gammaValid
    exact lt_of_le_of_lt hsmallB (by norm_num)
  exact
    theorem20_10_partB_backward_error_of_constructed_source_exact_rhs_householder_gamma_of_source_ranks
      fp h b d hBsrc hStack hvalidA hvalidB
/-- Theorem 20.10(b) certificate handoff specialized to the Householder
    `gamma_tilde_mn` and `gamma_tilde_np` coefficients. -/
theorem theorem20_10_partB_backward_error_of_householder_gamma_certificate
    {r p q : ℕ}
    (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (cert :
      Theorem20_10PartBPerturbationCertificate A B b d xhat
        (theorem20_10_householder_gammaA fp r p q)
        (theorem20_10_householder_gammaB fp r p q)) :
    let Apert : Fin (r + q) → Fin (p + q) → ℝ :=
      fun i j => A i j + cert.DeltaA i j
    let Bpert : Fin p → Fin (p + q) → ℝ :=
      fun i j => B i j + cert.DeltaB i j
    let bpert : Fin (r + q) → ℝ := fun i => b i + cert.Deltab i
    let dpert : Fin p → ℝ := fun i => d i + cert.Deltad i
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      DeltaA = cert.DeltaA ∧
      DeltaB = cert.DeltaB ∧
      Deltab = cert.Deltab ∧
      Deltad = cert.Deltad ∧
      frobNormRect DeltaA ≤
        theorem20_10_householder_gammaA fp r p q * frobNormRect A ∧
      frobNormRect DeltaB ≤
        theorem20_10_householder_gammaB fp r p q * frobNormRect B ∧
      vecNorm2 Deltab ≤
        theorem20_10_householder_gammaA fp r p q * vecNorm2 b +
          theorem20_10_householder_gammaB fp r p q *
            frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤
        theorem20_10_householder_gammaB fp r p q *
          frobNormRect B * vecNorm2 xhat ∧
      (∃ h : GeneralizedQRFactorization r p q Apert Bpert,
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = dpert ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U) bpert (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer Apert bpert Bpert dpert
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer Apert bpert Bpert dpert x)) :=
  theorem20_10_partB_backward_error_of_perturbation_certificate
    A B b d xhat cert
/-- Theorem 20.10(a), nonempty Householder-gamma certificate handoff.

This certificate-free form consumes a nonempty Part A perturbation certificate
with the source-facing Householder `gamma_tilde_mn` and `gamma_tilde_np`
coefficients and returns the corresponding mixed-stability conclusion. -/
theorem theorem20_10_partA_mixed_stability_of_nonempty_householder_gamma_certificate
    {r p q : ℕ}
    (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hcert :
      Nonempty
        (Theorem20_10PartAPerturbationCertificate A B b d xhat
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q))) :
    let gammaA : ℝ := theorem20_10_householder_gammaA fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ DeltaX : Fin (p + q) → ℝ,
    ∃ x : Fin (p + q) → ℝ,
      (∀ j : Fin (p + q), xhat j = x j + DeltaX j) ∧
      vecNorm2 DeltaX ≤ gammaB * vecNorm2 x ∧
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      vecNorm2 Deltab ≤ gammaA * vecNorm2 b ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      IsLSEMinimizer
        (fun i j => A i j + DeltaA i j)
        (fun i => b i + Deltab i)
        (fun i j => B i j + DeltaB i j) d x ∧
      (∃ h : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = d ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x0 : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j) d x0)) := by
  dsimp
  rcases hcert with ⟨cert⟩
  rcases
    theorem20_10_partA_mixed_stability_of_householder_gamma_certificate
      fp A B b d xhat cert with
    ⟨DeltaA, DeltaB, Deltab, DeltaX, x, _hDeltaAeq, _hDeltaBeq,
      _hDeltabeq, hxhat, hDeltaX, hDeltaA, hDeltab, hDeltaB,
      hx, hmethod⟩
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, DeltaX, x, hxhat, hDeltaX,
      cert.hDeltaA, cert.hDeltab, cert.hDeltaB, hx, hmethod⟩
/-- Theorem 20.10(b), nonempty Householder-gamma certificate handoff.

This certificate-free form consumes a nonempty Part B perturbation certificate
with the source-facing Householder `gamma_tilde_mn` and `gamma_tilde_np`
coefficients and returns the exact perturbed GQR/minimizer core. -/
theorem theorem20_10_partB_backward_error_of_nonempty_householder_gamma_certificate
    {r p q : ℕ}
    (fp : FPModel)
    (A : Fin (r + q) → Fin (p + q) → ℝ)
    (B : Fin p → Fin (p + q) → ℝ)
    (b : Fin (r + q) → ℝ) (d : Fin p → ℝ)
    (xhat : Fin (p + q) → ℝ)
    (hcert :
      Nonempty
        (Theorem20_10PartBPerturbationCertificate A B b d xhat
          (theorem20_10_householder_gammaA fp r p q)
          (theorem20_10_householder_gammaB fp r p q))) :
    let gammaA : ℝ := theorem20_10_householder_gammaA fp r p q
    let gammaB : ℝ := theorem20_10_householder_gammaB fp r p q
    ∃ DeltaA : Fin (r + q) → Fin (p + q) → ℝ,
    ∃ DeltaB : Fin p → Fin (p + q) → ℝ,
    ∃ Deltab : Fin (r + q) → ℝ,
    ∃ Deltad : Fin p → ℝ,
      frobNormRect DeltaA ≤ gammaA * frobNormRect A ∧
      frobNormRect DeltaB ≤ gammaB * frobNormRect B ∧
      vecNorm2 Deltab ≤
        gammaA * vecNorm2 b + gammaB * frobNormRect A * vecNorm2 xhat ∧
      vecNorm2 Deltad ≤ gammaB * frobNormRect B * vecNorm2 xhat ∧
      (∃ h : GeneralizedQRFactorization r p q
          (fun i j => A i j + DeltaA i j)
          (fun i j => B i j + DeltaB i j),
        (∃! yz : (Fin p → ℝ) × (Fin q → ℝ),
          rectMatMulVec h.S yz.1 = (fun i => d i + Deltad i) ∧
          rectMatMulVec h.L22 yz.2 =
            (fun i : Fin q =>
              matMulVec (r + q) (matTranspose h.U)
                (fun i => b i + Deltab i) (Fin.natAdd r i) -
                rectMatMulVec h.L21 yz.1 i) ∧
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i)
            (matMulVec (p + q) h.Q (Fin.append yz.1 yz.2))) ∧
        (∃! x : Fin (p + q) → ℝ,
          IsLSEMinimizer
            (fun i j => A i j + DeltaA i j)
            (fun i => b i + Deltab i)
            (fun i j => B i j + DeltaB i j)
            (fun i => d i + Deltad i) x)) := by
  dsimp
  rcases hcert with ⟨cert⟩
  rcases
    theorem20_10_partB_backward_error_of_householder_gamma_certificate
      fp A B b d xhat cert with
    ⟨DeltaA, DeltaB, Deltab, Deltad, _hDeltaAeq, _hDeltaBeq,
      _hDeltabeq, _hDeltadeq, hDeltaA, hDeltaB, hDeltab, hDeltad,
      hmethod⟩
  exact
    ⟨cert.DeltaA, cert.DeltaB, cert.Deltab, cert.Deltad,
      cert.hDeltaA, cert.hDeltaB, cert.hDeltab, cert.hDeltad, hmethod⟩
namespace Theorem20_10

/-- A single gamma horizon for the square constraint panel and its rounded
forward solve. -/
def fullConstraintGammaIndex (p : ℕ) : ℕ :=
  max p (p * householderConstructApplyGammaIndex p)
/-- The source rank radius used by the `q = 0` branch.  Retaining both source
margins mirrors the two assumptions in (20.24), even though square full row
rank alone already implies stacked full column rank. -/
noncomputable def fullConstraintSourceRankRadius
    {r p : ℕ} {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  min hB.transposeVecNorm2LowerMargin hStack.vecNorm2LowerMargin
/-- Positive unit-roundoff threshold for the square constraint-only branch.
The first cap validates the panel and solve gamma indices; the second keeps
the composed constraint perturbation below both source rank margins. -/
noncomputable def fullConstraintUnitRoundoffSmallnessThreshold
    {r p : ℕ} {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hB : LSEFullRowRank B) (hStack : LSEStackedFullColumnRank A B) : ℝ :=
  let N := fullConstraintGammaIndex p
  min
    (((1 : ℝ) / 2) / (N : ℝ))
    (fullConstraintSourceRankRadius hB hStack /
      ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)))
/-- Positivity of the full-constraint threshold for `p > 0`. -/
theorem fullConstraintUnitRoundoffSmallnessThreshold_pos
    {r p : ℕ} {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B) :
    0 < fullConstraintUnitRoundoffSmallnessThreshold hB hStack := by
  let N := fullConstraintGammaIndex p
  have hpN : p ≤ N := by simp [N, fullConstraintGammaIndex]
  have hNnat : 0 < N := lt_of_lt_of_le hp hpN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hradius : 0 < fullConstraintSourceRankRadius hB hStack := by
    dsimp [fullConstraintSourceRankRadius]
    exact lt_min hB.transposeVecNorm2LowerMargin_pos
      hStack.vecNorm2LowerMargin_pos
  have hden : 0 < (6 : ℝ) * (N : ℝ) * (1 + frobNormRect B) := by
    have hnorm := frobNormRect_nonneg B
    positivity
  dsimp [fullConstraintUnitRoundoffSmallnessThreshold]
  exact lt_min (div_pos (by norm_num) hN) (div_pos hradius hden)
/-- The full-constraint threshold validates the literal panel/solve path and
bounds the composed matrix perturbation strictly below both source margins. -/
theorem fullConstraint_unit_roundoff_conditions_of_lt_smallnessThreshold
    {r p : ℕ} (fp : FPModel)
    {A : Fin r → Fin p → ℝ} {B : Fin p → Fin p → ℝ}
    (hp : 0 < p) (hB : LSEFullRowRank B)
    (hStack : LSEStackedFullColumnRank A B)
    (hu : fp.u < fullConstraintUnitRoundoffSmallnessThreshold hB hStack) :
    gammaValid fp (p * householderConstructApplyGammaIndex p) ∧
      gammaValid fp p ∧
      theorem20_10_householder_composed_partA_gammaB fp r p 0 *
          frobNormRect B < fullConstraintSourceRankRadius hB hStack := by
  let N := fullConstraintGammaIndex p
  let idx := p * householderConstructApplyGammaIndex p
  have hpN : p ≤ N := by simp [N, fullConstraintGammaIndex]
  have hidxN : idx ≤ N := by simp [N, idx, fullConstraintGammaIndex]
  have hNnat : 0 < N := lt_of_lt_of_le hp hpN
  have hN : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hnorm : 0 ≤ frobNormRect B := frobNormRect_nonneg B
  have hden : 0 < (6 : ℝ) * (N : ℝ) * (1 + frobNormRect B) := by
    positivity
  have huHalf : fp.u < ((1 : ℝ) / 2) / (N : ℝ) :=
    lt_of_lt_of_le hu (by
      dsimp [fullConstraintUnitRoundoffSmallnessThreshold]
      exact min_le_left _ _)
  have huRank :
      fp.u < fullConstraintSourceRankRadius hB hStack /
        ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)) :=
    lt_of_lt_of_le hu (by
      dsimp [fullConstraintUnitRoundoffSmallnessThreshold]
      exact min_le_right _ _)
  have hNu_lt : (N : ℝ) * fp.u < 1 / 2 := by
    have := (lt_div_iff₀ hN).mp huHalf
    nlinarith
  have hhalfN : (N : ℝ) * fp.u ≤ 1 / 2 := le_of_lt hNu_lt
  have hvalidN : gammaValid fp N := by
    unfold gammaValid
    linarith
  have hvalidIdx : gammaValid fp idx := gammaValid_mono fp hidxN hvalidN
  have hvalidp : gammaValid fp p := gammaValid_mono fp hpN hvalidN
  have hhalfIdx : (idx : ℝ) * fp.u ≤ 1 / 2 := by
    have hcast : (idx : ℝ) ≤ N := by exact_mod_cast hidxN
    exact le_trans (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hhalfN
  have hhalfp : (p : ℝ) * fp.u ≤ 1 / 2 := by
    have hcast : (p : ℝ) ≤ N := by exact_mod_cast hpN
    exact le_trans (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) hhalfN
  have hgammaPanel :
      theorem20_10_householder_gammaB fp r p 0 ≤
        2 * ((N : ℝ) * fp.u) := by
    calc
      theorem20_10_householder_gammaB fp r p 0
          ≤ 2 * ((idx : ℝ) * fp.u) := by
              simpa [idx, mul_assoc] using
                theorem20_10_householder_gammaB_le_linear_unit_roundoff_of_small
                  (r := r) (p := p) (q := 0) fp hhalfIdx
      _ ≤ 2 * ((N : ℝ) * fp.u) := by
              have hcast : (idx : ℝ) ≤ N := by exact_mod_cast hidxN
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) (by norm_num)
  have hgammap : gamma fp p ≤ 2 * ((N : ℝ) * fp.u) := by
    calc
      gamma fp p ≤ 2 * ((p : ℝ) * fp.u) :=
        gamma_le_two_mul_n_u_of_nu_le_half fp p hhalfp
      _ ≤ 2 * ((N : ℝ) * fp.u) := by
        have hcast : (p : ℝ) ≤ N := by exact_mod_cast hpN
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hcast fp.u_nonneg) (by norm_num)
  have hpanelNonneg :
      0 ≤ theorem20_10_householder_gammaB fp r p 0 := by
    simpa [theorem20_10_householder_gammaB] using
      H19.Theorem19_4.gamma_tilde_nonneg fp hvalidIdx
  have hgammapNonneg : 0 ≤ gamma fp p := gamma_nonneg fp hvalidp
  have ht : 0 ≤ 2 * ((N : ℝ) * fp.u) := by
    exact mul_nonneg (by norm_num) (mul_nonneg (le_of_lt hN) fp.u_nonneg)
  have ht_one : 2 * ((N : ℝ) * fp.u) ≤ 1 := by nlinarith
  have hcomposed :
      theorem20_10_householder_composed_partA_gammaB fp r p 0 ≤
        6 * (N : ℝ) * fp.u := by
    dsimp [theorem20_10_householder_composed_partA_gammaB]
    nlinarith
  have hRankProduct :
      fp.u * ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)) <
        fullConstraintSourceRankRadius hB hStack :=
    (lt_div_iff₀ hden).mp huRank
  refine ⟨by simpa [idx] using hvalidIdx, hvalidp, ?_⟩
  calc
    theorem20_10_householder_composed_partA_gammaB fp r p 0 *
          frobNormRect B
        ≤ (6 * (N : ℝ) * fp.u) * frobNormRect B :=
          mul_le_mul_of_nonneg_right hcomposed hnorm
    _ ≤ fp.u * ((6 : ℝ) * (N : ℝ) * (1 + frobNormRect B)) := by
          nlinarith [fp.u_nonneg, hN, hnorm]
    _ < fullConstraintSourceRankRadius hB hStack := hRankProduct

end Theorem20_10

end NumStability
