import NumStability.Algorithms.LinearSystems.LeastSquares.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Perturbation.LeastSquares.Normwise

namespace NumStability

/-!
# MinimumNorm

Canonical reusable module extracted without change from Higham20MinimumNormBackwardError.
-/

/-- A least-squares minimizer that has minimum Euclidean norm among all
    least-squares minimizers for the same data. -/
def IsMinimumNormLeastSquaresMinimizer {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Prop :=
  IsLeastSquaresMinimizer A b y ∧
    ∀ z : Fin n → ℝ, IsLeastSquaresMinimizer A b z →
      vecNorm2 y ≤ vecNorm2 z
/-- Strengthened feasibility from the precise p. 404 literature remark:
    `y` must be a minimum-2-norm least-squares solution of the perturbed
    problem, rather than merely an arbitrary least-squares minimizer. -/
def LSMinimumNormBackwardErrorFeasible {m n : ℕ}
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ) : Prop :=
  IsMinimumNormLeastSquaresMinimizer
    (fun i j => A i j + DeltaA i j)
    (fun i => b i + Deltab i) y
/-- A strengthened feasible perturbation is feasible for the original
    normwise backward-error problem (20.20). -/
theorem LSMinimumNormBackwardErrorFeasible.to_normwise
    {m n : ℕ} {A : Fin m → Fin n → ℝ} {b : Fin m → ℝ}
    {y : Fin n → ℝ} {DeltaA : Fin m → Fin n → ℝ}
    {Deltab : Fin m → ℝ}
    (h : LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab) :
    LSNormwiseBackwardErrorFeasible A b y DeltaA Deltab :=
  h.1
/-- Attainable weighted costs when the perturbed problem is additionally
    required to have `y` as its minimum-2-norm least-squares solution. -/
noncomputable def lsMinimumNormBackwardErrorValuesF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : Set ℝ :=
  {eta | ∃ (DeltaA : Fin m → Fin n → ℝ) (Deltab : Fin m → ℝ),
    LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab ∧
      eta = lsNormwiseBackwardErrorCostF theta DeltaA Deltab}
/-- Infimum of the strengthened p. 404 attainable-cost set. -/
noncomputable def lsMinimumNormBackwardErrorEtaF {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  sInf (lsMinimumNormBackwardErrorValuesF theta A b y)
theorem lsMinimumNormBackwardErrorValuesF.bddBelow {m n : ℕ} (theta : ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ) :
    BddBelow (lsMinimumNormBackwardErrorValuesF theta A b y) := by
  refine ⟨0, ?_⟩
  intro eta heta
  rcases heta with ⟨DeltaA, Deltab, _hfeas, rfl⟩
  exact lsNormwiseBackwardErrorCostF_nonneg theta DeltaA Deltab
theorem lsMinimumNormBackwardErrorValuesF.mem_of_feasible {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ)
    (Deltab : Fin m → ℝ)
    (hfeas : LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab) :
    lsNormwiseBackwardErrorCostF theta DeltaA Deltab ∈
      lsMinimumNormBackwardErrorValuesF theta A b y := by
  exact ⟨DeltaA, Deltab, hfeas, rfl⟩
/-- The strengthened infimum is no larger than the cost of any strengthened
    feasible perturbation. -/
theorem lsMinimumNormBackwardErrorEtaF_le_costF_of_feasible {m n : ℕ}
    (theta : ℝ) (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (y : Fin n → ℝ) (DeltaA : Fin m → Fin n → ℝ)
    (Deltab : Fin m → ℝ)
    (hfeas : LSMinimumNormBackwardErrorFeasible A b y DeltaA Deltab) :
    lsMinimumNormBackwardErrorEtaF theta A b y ≤
      lsNormwiseBackwardErrorCostF theta DeltaA Deltab := by
  unfold lsMinimumNormBackwardErrorEtaF
  exact csInf_le
    (lsMinimumNormBackwardErrorValuesF.bddBelow theta A b y)
    (lsMinimumNormBackwardErrorValuesF.mem_of_feasible
      theta A b y DeltaA Deltab hfeas)

end NumStability
