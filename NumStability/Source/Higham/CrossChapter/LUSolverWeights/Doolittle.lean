-- Higham/CrossChapter/Chapter09To12Solver.lean
--
-- The literal Chapter 9 -> Chapter 12 handoff for equation (12.6).

import NumStability.Algorithms.HighamChapter9DoolittleClosure
import NumStability.Source.Higham.Chapter12.IterativeRefinement

namespace NumStability

open scoped BigOperators

/-! All source references are to N. J. Higham, *Accuracy and Stability of
Numerical Algorithms*, 2nd ed. (SIAM, 2002), Theorem 9.4 and Chapter 12,
equations (12.1) and (12.6), printed p. 234. -/

/-- **Equation (12.6)**, the concrete solver weight associated with the
rounded Doolittle factors from Algorithm 9.2:

`W = 3n / (1 - 3nu) * |L_hat| |U_hat|`.

Writing the coefficient without division by `u` keeps the definition valid
also for an exact model with `u = 0`. -/
noncomputable def higham12_6_rectRoundedLoopW {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    (((3 * n : ℕ) : ℝ) /
        (1 - ((3 * n : ℕ) : ℝ) * fp.u)) *
      ∑ k : Fin n,
        |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
          |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j|

/-- **Equation (12.6)** literally: multiplying the concrete weight by the
unit roundoff gives the `gamma_(3n) |L_hat| |U_hat|` envelope produced by
Theorem 9.4. -/
theorem higham12_6_u_mul_rectRoundedLoopW_eq {n : ℕ}
    (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (hn3 : gammaValid fp (3 * n)) (i j : Fin n) :
    fp.u * higham12_6_rectRoundedLoopW fp A i j =
      gamma fp (3 * n) *
        ∑ k : Fin n,
          |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
            |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| := by
  have hden : 1 - ((3 * n : ℕ) : ℝ) * fp.u ≠ 0 := by
    apply ne_of_gt
    exact sub_pos.mpr hn3
  simp only [higham12_6_rectRoundedLoopW, gamma]
  field_simp [hden]

/-- **Theorem 9.4 -> equation (12.6) -> equation (12.1).**

Run the literal rounded square Doolittle loop, followed by the repository's
actual rounded forward and backward substitutions.  Theorem 9.4 constructs
the perturbation for that computed solution; equation (12.6) above rewrites
its envelope as `u W`.  Hence the actual solver satisfies Chapter 12's
`higham12_1_SolverWBound` with the displayed concrete `W`.

No residual, execution, backward-error, or solver-bound conclusion is a
hypothesis of this endpoint. -/
theorem higham12_6_rectRoundedLoop_lu_solve_SolverWBound_source
    {n : ℕ} (fp : FPModel) (A : Fin n → Fin n → ℝ)
    (b : Fin n → ℝ)
    (hU_diag : ∀ k : Fin n,
      higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k k ≠ 0)
    (hn : gammaValid fp n)
    (hn3 : gammaValid fp (3 * n)) :
    let L_hat := higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A
    let U_hat := higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A
    let y_hat := fl_forwardSub fp n L_hat b
    let x_hat := fl_backSub fp n U_hat y_hat
    higham12_1_SolverWBound n A
      (higham12_6_rectRoundedLoopW fp A) fp.u b x_hat := by
  dsimp only
  have hsource :=
    higham9_4_rectRoundedLoop_square_lu_solve_backward_error_source
      fp A b hU_diag hn hn3
  dsimp only at hsource
  obtain ⟨DeltaA, hDeltaA, hsolve⟩ := hsource
  refine ⟨DeltaA, ?_, hsolve⟩
  intro i j
  calc
    |DeltaA i j| ≤
        gamma fp (3 * n) *
          ∑ k : Fin n,
            |higham9_2_rectRoundedLoopL fp (Nat.le_refl n) A i k| *
              |higham9_2_rectRoundedLoopU fp (Nat.le_refl n) A k j| :=
      hDeltaA i j
    _ = fp.u * higham12_6_rectRoundedLoopW fp A i j :=
      (higham12_6_u_mul_rectRoundedLoopW_eq fp A hn3 i j).symm

end NumStability
