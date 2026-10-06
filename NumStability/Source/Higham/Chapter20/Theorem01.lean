import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 20, Theorem 20.1

Canonical source-correspondence module for the one-right-hand-side Wedin solution and residual bounds.
-/

/-- Higham, 2nd ed., Chapter 20, Theorem 20.1, equations (20.1)-(20.2):
    one-right-hand-side-budget wrapper for the proved full-column Wedin route.

The single source budget `||Delta b||₂ ≤ eps ||b||₂` supplies the residual
estimate directly.  For the solution estimate, `b = A x + r` and the supplied
operator bound for `A` imply
`||Delta b||₂ ≤ eps (A_norm ||x||₂ + ||r||₂)`.  The matrix-difference radius
is also derived from `B = A + DeltaA`, so neither of those two handoff facts is
duplicated in the public assumptions. -/
theorem higham20_theorem20_1_solution_and_residualRelativeRHS_le_of_one_rhs_budget
    {m k : ℕ} (hm : 0 < m) (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (DeltaA : Fin m → Fin (k + 1) → ℝ)
    (b Deltab r s : Fin m → ℝ) (x y : Fin (k + 1) → ℝ)
    {Aplus_norm delta eta DeltaA_norm Deltab_norm kappa eps A_norm : ℝ}
    (hb_norm_pos : 0 < vecNorm2 b)
    (hAplus_pos : 0 < Aplus_norm)
    (hA_norm_pos : 0 < A_norm)
    (heps_nonneg : 0 ≤ eps)
    (hx_norm_pos : 0 < vecNorm2 x)
    (hkappa : kappa = Aplus_norm * A_norm)
    (hdelta : delta = eps * A_norm)
    (heta : eta = Aplus_norm * delta)
    (hsmall_eta : eta < 1)
    (hleftA : rectMatMul Aplus A = idMatrix (k + 1))
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hSymA : IsSymmetricFiniteMatrix (rectMatMul A Aplus))
    (hSymB : IsSymmetricFiniteMatrix (rectMatMul B Bplus))
    (hA : rectOpNorm2Le A A_norm)
    (hAplus : rectOpNorm2Le Aplus Aplus_norm)
    (hDeltaA : rectOpNorm2Le DeltaA DeltaA_norm)
    (hDeltab : vecNorm2 Deltab ≤ Deltab_norm)
    (hDeltaA_norm_budget : DeltaA_norm ≤ eps * A_norm)
    (hDeltab_norm_budget : Deltab_norm ≤ eps * vecNorm2 b)
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0)
    (hB : B = fun i j => A i j + DeltaA i j)
    (hr : r = fun i => b i - rectMatMulVec A x i)
    (hs : s = fun i => (b i + Deltab i) - rectMatMulVec B y i)
    (horth_s : ∀ j : Fin (k + 1), ∑ i : Fin m, B i j * s i = 0) :
    (vecNorm2 (fun j => y j - x j) / vecNorm2 x ≤
        wedinTheorem20_1SolutionRelativeRHS
          kappa eps A_norm (vecNorm2 x) (vecNorm2 r)) ∧
      (vecNorm2 (fun i => r i - s i) / vecNorm2 b ≤
        wedinTheorem20_1ResidualRelativeRHS kappa eps) := by
  have hBA : (fun i j => B i j - A i j) = DeltaA := by
    ext i j
    rw [hB]
    ring
  have hDeltaA_norm_le_delta : DeltaA_norm ≤ delta := by
    rw [hdelta]
    exact hDeltaA_norm_budget
  have hDelta : rectOpNorm2Le (fun i j => B i j - A i j) delta := by
    rw [hBA]
    intro z
    exact (hDeltaA z).trans
      (mul_le_mul_of_nonneg_right hDeltaA_norm_le_delta (vecNorm2_nonneg z))
  have hb_decomp : b = fun i => rectMatMulVec A x i + r i := by
    ext i
    have hri := congrFun hr i
    change r i = b i - rectMatMulVec A x i at hri
    linarith
  have hb_norm_le :
      vecNorm2 b ≤ A_norm * vecNorm2 x + vecNorm2 r := by
    calc
      vecNorm2 b =
          vecNorm2 (fun i => rectMatMulVec A x i + r i) := by
            rw [hb_decomp]
      _ ≤ vecNorm2 (rectMatMulVec A x) + vecNorm2 r :=
            vecNorm2_add_le (rectMatMulVec A x) r
      _ ≤ A_norm * vecNorm2 x + vecNorm2 r :=
            add_le_add (hA x) le_rfl
  have hDeltab_norm_budget_solution :
      Deltab_norm ≤ eps * (A_norm * vecNorm2 x + vecNorm2 r) :=
    hDeltab_norm_budget.trans
      (mul_le_mul_of_nonneg_left hb_norm_le heps_nonneg)
  exact
    wedinTheorem20_1_solution_and_residualRelativeRHS_le_of_residual_definitions_min_surface_geometry_column_orthogonal
      hm A B Aplus Bplus DeltaA b Deltab r s x y hb_norm_pos
      hAplus_pos hA_norm_pos heps_nonneg hx_norm_pos hkappa hdelta heta
      hsmall_eta hleftA hleftB hSymA hSymB hDelta hAplus hDeltaA
      hDeltab hDeltaA_norm_budget hDeltab_norm_budget_solution
      hDeltab_norm_budget hrangeA_residual hB hr hs horth_s

end NumStability
