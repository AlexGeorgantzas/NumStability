-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., Chapter 21.
-- Concrete forward-error closure for the seminormal-equations solve.

import NumStability.Algorithms.Underdetermined.UnderdeterminedSolve

namespace NumStability

open scoped BigOperators

/-- The actual normal-equation vector returned by the two rounded triangular
solves in the SNE method. -/
noncomputable def higham21SNEComputedNormalSolution
    (fp : FPModel) (m : ℕ) (R_hat : Fin m → Fin m → ℝ)
    (b : Fin m → ℝ) : Fin m → ℝ :=
  fl_backSub fp m R_hat
    (fl_forwardSub fp m (fun i j : Fin m => R_hat j i) b)

/-- The finite coefficient in the componentwise Cholesky/triangular-solve
backward error used by the SNE method. -/
noncomputable def Higham21SNEBackwardCoefficient
    (fp : FPModel) (m : ℕ) : ℝ :=
  gamma fp (m + 1) + 2 * gamma fp m + gamma fp m ^ 2

/-- The entrywise `|R_hat^T| |R_hat|` backward-error envelope, including the
coefficient from the two rounded triangular solves.  Unfolding this definition
gives exactly the bound returned by `sne_backward_error`. -/
noncomputable def higham21SNERHatGramEnvelope
    (fp : FPModel) (m : ℕ) (R_hat : Fin m → Fin m → ℝ)
    (i j : Fin m) : ℝ :=
  Higham21SNEBackwardCoefficient fp m *
    ∑ k : Fin m, |R_hat k i| * |R_hat k j|

/-- The fully instantiated finite componentwise forward-error envelope for the
computed SNE normal-equation vector. -/
noncomputable def higham21SNEForwardEnvelope
    (fp : FPModel) (m : ℕ)
    (AAT_inv R_hat : Fin m → Fin m → ℝ)
    (y_hat : Fin m → ℝ) : Fin m → ℝ :=
  fun i =>
    ∑ j : Fin m, |AAT_inv i j| *
      ∑ k : Fin m,
        higham21SNERHatGramEnvelope fp m R_hat j k * |y_hat k|

/-- A named, exact finite coefficient for the relative Euclidean SNE forward
bound, expressed entirely by finite sums and Euclidean norms. -/
noncomputable def Higham21SNEForwardCoefficient
    (fp : FPModel) (m : ℕ)
    (AAT_inv R_hat : Fin m → Fin m → ℝ)
    (y y_hat : Fin m → ℝ) : ℝ :=
  vecNorm2 (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) /
    vecNorm2 y

/-- Aggregate a componentwise forward-error envelope into a Euclidean norm
bound. -/
theorem higham21_sne_vecNorm2_forward_error_of_componentwise
    {m : ℕ} (y y_hat envelope : Fin m → ℝ)
    (hcomponentwise : ∀ i : Fin m, |y_hat i - y i| ≤ envelope i) :
    vecNorm2 (fun i : Fin m => y_hat i - y i) ≤ vecNorm2 envelope :=
  vecNorm2_le_of_abs_le
    (fun i : Fin m => y_hat i - y i) envelope hcomponentwise

/-- Substitute the concrete SNE `DeltaC` estimate into the generic
componentwise forward perturbation bound. -/
theorem higham21_sne_forward_error_le_computed_envelope
    (fp : FPModel) (m : ℕ)
    (AAT_inv R_hat DeltaC : Fin m → Fin m → ℝ)
    (y y_hat : Fin m → ℝ)
    (hDeltaC : ∀ i j : Fin m,
      |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j)
    (hforward : ∀ i : Fin m,
      |y_hat i - y i| ≤
        ∑ j : Fin m, |AAT_inv i j| *
          ∑ k : Fin m, |DeltaC j k| * |y_hat k|) :
    ∀ i : Fin m,
      |y_hat i - y i| ≤
        higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i := by
  intro i
  refine (hforward i).trans ?_
  simp only [higham21SNEForwardEnvelope]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left
  · apply Finset.sum_le_sum
    intro k hk
    exact mul_le_mul_of_nonneg_right (hDeltaC j k) (abs_nonneg (y_hat k))
  · exact abs_nonneg (AAT_inv i j)

/-- Concrete source-facing SNE forward theorem.  The witness `DeltaC`, the
perturbed equation, and the forward inequality all concern the actual
`fl_forwardSub`/`fl_backSub` output, rather than an uninstantiated vector.

Besides retaining the exact `DeltaC`-dependent componentwise inequality, the
theorem substitutes its proved backward-error bound and aggregates the result
in the Euclidean norm. -/
theorem higham21_sne_computed_forward_error
    (fp : FPModel) (m : ℕ)
    (AAT AAT_inv R_hat : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1)) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    ∃ DeltaC : Fin m → Fin m → ℝ,
      (∀ i j : Fin m,
        |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j) ∧
      (∀ i : Fin m,
        ∑ j : Fin m, (AAT i j + DeltaC i j) * y_hat j = b i) ∧
      (∀ i : Fin m,
        |y_hat i - y i| ≤
          ∑ j : Fin m, |AAT_inv i j| *
            ∑ k : Fin m, |DeltaC j k| * |y_hat k|) ∧
      (∀ i : Fin m,
        |y_hat i - y i| ≤
          higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i) ∧
      vecNorm2 (fun i : Fin m => y_hat i - y i) ≤
        vecNorm2 (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) := by
  dsimp only
  obtain ⟨DeltaC, hDeltaC, hPerturbed⟩ :
      ∃ DeltaC : Fin m → Fin m → ℝ,
        (∀ i j : Fin m,
          |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j) ∧
        (∀ i : Fin m,
          ∑ j : Fin m, (AAT i j + DeltaC i j) *
            higham21SNEComputedNormalSolution fp m R_hat b j = b i) := by
    simpa only [higham21SNEComputedNormalSolution,
      higham21SNERHatGramEnvelope, Higham21SNEBackwardCoefficient] using
      (sne_backward_error fp m AAT R_hat b hR_diag hChol hm1)
  have hForward : ∀ i : Fin m,
      |higham21SNEComputedNormalSolution fp m R_hat b i - y i| ≤
        ∑ j : Fin m, |AAT_inv i j| *
          ∑ k : Fin m, |DeltaC j k| *
            |higham21SNEComputedNormalSolution fp m R_hat b k| := by
    exact
      higham21_sne_gram_forward_error_matches_q_method
        m AAT AAT_inv hInv b y
          (higham21SNEComputedNormalSolution fp m R_hat b)
          hExact DeltaC hPerturbed
  have hEnvelope : ∀ i : Fin m,
      |higham21SNEComputedNormalSolution fp m R_hat b i - y i| ≤
        higham21SNEForwardEnvelope fp m AAT_inv R_hat
          (higham21SNEComputedNormalSolution fp m R_hat b) i :=
    higham21_sne_forward_error_le_computed_envelope
      fp m AAT_inv R_hat DeltaC y
        (higham21SNEComputedNormalSolution fp m R_hat b)
        hDeltaC hForward
  have hNorm :
      vecNorm2 (fun i : Fin m =>
        higham21SNEComputedNormalSolution fp m R_hat b i - y i) ≤
        vecNorm2
          (higham21SNEForwardEnvelope fp m AAT_inv R_hat
            (higham21SNEComputedNormalSolution fp m R_hat b)) :=
    higham21_sne_vecNorm2_forward_error_of_componentwise
      y (higham21SNEComputedNormalSolution fp m R_hat b)
        (higham21SNEForwardEnvelope fp m AAT_inv R_hat
          (higham21SNEComputedNormalSolution fp m R_hat b)) hEnvelope
  exact ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩

/-- Equation (21.11), SNE side, for the actually computed normal-equation
vector.  For a nonzero exact solution this packages the concrete witness and
both the exact componentwise and relative Euclidean forward bounds in one
statement.

The coefficient is the finite envelope justified by the currently available
SNE backward-error theorem.  Reducing it to the printed `cond2(A)` expression
would additionally require a proved source-level relation between `R_hat` and
the rectangular input matrix; that relation is not an assumption hidden here. -/
theorem higham21_eq21_11_sne_computed_relative_forward_error
    (fp : FPModel) (m : ℕ)
    (AAT AAT_inv R_hat : Fin m → Fin m → ℝ)
    (b y : Fin m → ℝ)
    (hInv : IsInverse m AAT AAT_inv)
    (hExact : ∀ i, matMulVec m AAT y i = b i)
    (hR_diag : ∀ i : Fin m, R_hat i i ≠ 0)
    (hChol : CholeskyBackwardError m AAT R_hat (gamma fp (m + 1)))
    (hm1 : gammaValid fp (m + 1))
    (hy : 0 < vecNorm2 y) :
    let y_hat := higham21SNEComputedNormalSolution fp m R_hat b
    ∃ DeltaC : Fin m → Fin m → ℝ,
      (∀ i j : Fin m,
        |DeltaC i j| ≤ higham21SNERHatGramEnvelope fp m R_hat i j) ∧
      (∀ i : Fin m,
        ∑ j : Fin m, (AAT i j + DeltaC i j) * y_hat j = b i) ∧
      (∀ i : Fin m,
        |y_hat i - y i| ≤
          ∑ j : Fin m, |AAT_inv i j| *
            ∑ k : Fin m, |DeltaC j k| * |y_hat k|) ∧
      (∀ i : Fin m,
        |y_hat i - y i| ≤
          higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat i) ∧
      vecNorm2 (fun i : Fin m => y_hat i - y i) ≤
        vecNorm2 (higham21SNEForwardEnvelope fp m AAT_inv R_hat y_hat) ∧
      vecNorm2 (fun i : Fin m => y_hat i - y i) / vecNorm2 y ≤
        Higham21SNEForwardCoefficient fp m AAT_inv R_hat y y_hat := by
  dsimp only
  have hCore :=
    higham21_sne_computed_forward_error
      fp m AAT AAT_inv R_hat b y hInv hExact hR_diag hChol hm1
  dsimp only at hCore
  obtain ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm⟩ := hCore
  have hRelative :
      vecNorm2 (fun i : Fin m =>
        higham21SNEComputedNormalSolution fp m R_hat b i - y i) /
          vecNorm2 y ≤
        Higham21SNEForwardCoefficient fp m AAT_inv R_hat y
          (higham21SNEComputedNormalSolution fp m R_hat b) := by
    simpa only [Higham21SNEForwardCoefficient] using
      (div_le_div_of_nonneg_right hNorm (le_of_lt hy))
  exact
    ⟨DeltaC, hDeltaC, hPerturbed, hForward, hEnvelope, hNorm, hRelative⟩

end NumStability
