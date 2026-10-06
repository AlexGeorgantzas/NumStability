import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Convergence.Singular.FixedSubspaces
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Forward.ComplementDecomposition
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Local.OneStep
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.ErrorAnalysis.Residual.Identities
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Execution.Computed.Model
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Projectors.Drazin.Algebra
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Recurrences.Affine.Unrolling
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Core.Definitions
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Splittings.Scaling.Diagonal
import NumStability.Analysis.Conditioning.LinearSystems.SubordinatePerturbation
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealDiagonal
import NumStability.Analysis.MatrixAlgebra
import NumStability.Source.Higham.Chapter17.Equation01.ComputedIteration.Results
import NumStability.Source.Higham.Chapter17.Equation02.LocalError.Results
import NumStability.Source.Higham.Chapter17.Equation03.ComputedRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation04.FixedPoint.Results
import NumStability.Source.Higham.Chapter17.Equation05.ErrorExpansion.Results
import NumStability.Source.Higham.Chapter17.Equation06.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation07.NormwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation08.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation09.ComponentwiseGrowth.Results
import NumStability.Source.Higham.Chapter17.Equation10.LocalErrorSimplification.Results
import NumStability.Source.Higham.Chapter17.Equation12.PartialSumBound.Results
import NumStability.Source.Higham.Chapter17.Equation13.ComponentwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation15.NormwiseForward.Results
import NumStability.Source.Higham.Chapter17.Equation16.Jacobi.Results
import NumStability.Source.Higham.Chapter17.Equation17.SOR.Results
import NumStability.Source.Higham.Chapter17.Equation18.ResidualRecurrence.Results
import NumStability.Source.Higham.Chapter17.Equation19.ResidualBound.Results
import NumStability.Source.Higham.Chapter17.Equation20.ResidualSigma.Results
import NumStability.Source.Higham.Chapter17.Equation21.SingularIteration.Results
import NumStability.Source.Higham.Chapter17.Equation27.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation28.SingularErrorSplit.Results
import NumStability.Source.Higham.Chapter17.Equation29.SingularSource.Results
import NumStability.Source.Higham.Chapter17.Equation33.StoppingTests.Results
import NumStability.Source.Higham.Chapter17.Section02.ScaleIndependence.Results
import NumStability.Source.Higham.Chapter17.Section04.PrintedConclusions.Results
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.BlockForm.Existence
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.BlockForm.ProjectorLimit
import NumStability.Algorithms.LinearSystems.Iterative.Stationary.Semiconvergence.Projectors.FixedRange

/-!
# Higham Chapter 17, Equation 17.27: singular error splits

Canonical source-facing error-split consequences for Drazin and semiconvergent
stationary-iteration projectors.
-/

namespace NumStability

open scoped BigOperators

/-- Higham, 2nd ed., Chapter 17, Section 17.4, equations (17.24), (17.27),
    and (17.28): finite singular-system error split with the source Drazin
    projector `E = (I - G)(I - G)^D`.

    Compared with `singular_error_split_finite`, this wrapper no longer asks
    for the fixed-null hypothesis separately: it is supplied by the
    index-one Drazin inverse certificate for `I - G`.  The limiting
    semiconvergence and infinite-sum bounds remain separate obligations. -/
theorem singular_error_split_finite_of_indexOneDrazin_projector (n : ℕ)
    (A M N M_inv D : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (hD : IndexOneDrazinInverse n (matSub_id n (iterMatrix n M_inv N)) D)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (xi : ℕ → Fin n → ℝ)
    (hIter : SourceComputedIteration n M N b x_hat xi)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N)
        (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D)
        M_inv xi m i +
      matMulVec n
        (stationaryDrazinFixedProjector n (iterMatrix n M_inv N) D)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), xi (m - k) j)) i := by
  intro i
  have hNull :
      ∀ t r,
        matMulVec n (iterMatrix n M_inv N)
          (matMulVec n
            (matSub_id n
              (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D))
            (matMulVec n M_inv (xi t))) r =
        matMulVec n
          (matSub_id n
            (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D))
          (matMulVec n M_inv (xi t)) r := by
    intro t r
    exact stationaryDrazinRangeProjector_null_component_fixed
      n (iterMatrix n M_inv N) D M_inv xi hD t r
  have hsplit := singular_error_split_finite n A M N M_inv
    (stationaryDrazinRangeProjector n (iterMatrix n M_inv N) D)
    hS b x hAx x_hat xi hIter hNull m i
  simpa [stationaryDrazinFixedProjector] using hsplit
/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.27): the finite three-term error split (17.27) for a
    consistent singular system, with the projector built from the
    semiconvergent block form of (17.22).  This closes the ledger's "proof
    that the source projector `E` supplies the fixed-null hypothesis" row at
    the printed (17.22) data level: the abstract projector `E` and the
    `hNull` hypothesis of `singular_error_split_finite` are replaced by
    block-form data `(r, J, X, X⁻¹)` for the iteration matrix
    `G = M⁻¹N`, and the fixed-subspace property is PROVED from that data
    (for all vectors, not just the specific `M⁻¹ξ_t`).

    Honest scope notes: the semiconvergent block form is taken as data, as
    in the printed (17.22); the existence of that form for an arbitrary
    semiconvergent matrix — Jordan-form background — is not formalized.
    The contraction certificate `q < 1` for the `Γ` rows (an ∞-norm
    row-sum strengthening of the printed spectral condition `ρ(Γ) < 1`) is
    carried so that the hypothesis package is the full printed
    semiconvergent form, but the finite split itself needs only the block
    structure; the certificate becomes load-bearing in the companion limit
    theorem `matPow_G_tendsto_oneEigenProjector`. -/
theorem singular_error_split_semiconvergent (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (r : ℕ) (J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1)
    (_hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n (iterMatrix n M_inv N) X) = J)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N)
        (semiconvergentE n r X X_inv) M_inv ξ m i +
      matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
  have hNull : ∀ t i,
      matMulVec n (iterMatrix n M_inv N)
        (matMulVec n (matSub_id n (semiconvergentE n r X X_inv))
          (matMulVec n M_inv (ξ t))) i =
      matMulVec n (matSub_id n (semiconvergentE n r X X_inv))
        (matMulVec n M_inv (ξ t)) i := by
    intro t i
    rw [matSub_id_semiconvergentE n r X X_inv]
    exact G_fixes_oneEigenProjector_apply n r (iterMatrix n M_inv N) J
      X X_inv hJtop hJcross hXr hXl hsim (matMulVec n M_inv (ξ t)) i
  intro i
  have h := singular_error_split_finite n A M N M_inv
    (semiconvergentE n r X X_inv) hS b x hAx x_hat ξ hIter hNull m i
  rw [matSub_id_semiconvergentE n r X X_inv] at h
  exact h
/-- **The semiconvergent finite error split (17.27), with the block form
    supplied by existence.**  Combining
    `semiconvergent_block_form_exists` with the companion module's
    `singular_error_split_semiconvergent`, we obtain the three-term error
    split of eq (17.27) for a consistent singular system *without assuming*
    the block-form data: the `(r, J, X, X⁻¹, q)` package is CONSTRUCTED from
    the semiconvergence encoding of `G := M⁻¹N`.

    The projector `E` and its complement `I − E` are built from the produced
    block form via `semiconvergentE`/`oneEigenProjector`, and the error at
    step `m + 1` decomposes into the transient power term, the accumulating
    source term, and the fixed eigenvalue-`1` component. -/
theorem singular_error_split_semiconvergent_of_block_data (n r : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (X X_inv Γ : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hGcolTop : ∀ (k : Fin n), (k : ℕ) < r →
      ∀ i : Fin n, matMul n (iterMatrix n M_inv N) X i k = X i k)
    (hGcolBot : ∀ (k : Fin n), ¬(k : ℕ) < r →
      ∀ i : Fin n, matMul n (iterMatrix n M_inv N) X i k =
        ∑ l ∈ Finset.univ.filter (fun l : Fin n => ¬(l : ℕ) < r),
          X i l * Γ l k)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hΓrows : ∀ i : Fin n, ¬(i : ℕ) < r →
      (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬(j : ℕ) < r),
        |Γ i j|) ≤ q)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N)
        (semiconvergentE n r X X_inv) M_inv ξ m i +
      matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
  obtain ⟨J, hJtop, hJcross, ⟨hq0', hq1', hGamma⟩, hXr', hXl', hsim⟩ :=
    semiconvergent_block_form_exists n r (iterMatrix n M_inv N) X X_inv Γ
      hXr hXl hGcolTop hGcolBot q hq0 hq1 hΓrows
  exact singular_error_split_semiconvergent n A M N M_inv hS b x hAx x_hat ξ
    hIter r J X X_inv hJtop hJcross q hq0' hq1' hGamma hXr' hXl' hsim m


end NumStability
