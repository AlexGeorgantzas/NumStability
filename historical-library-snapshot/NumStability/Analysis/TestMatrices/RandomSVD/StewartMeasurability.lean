import NumStability.Analysis.FirstOrder.AsymptoticFamilies
import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Source.Higham.Chapter28.Section03.Theorem01.StewartHaar.Stewart
import NumStability.Upstream.Lindemann.MonoidAlgebraCompat

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28Stewart under the R09/R10 completion waves; reusable-tier destination per the reviewed route ledger.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

local instance instMeasurableSpaceRSqMat (n : ℕ) : MeasurableSpace (RSqMat n) := MeasurableSpace.pi

theorem measurable_stewartEmbeddedHouseholder
    {n : ℕ} (i : Fin n) :
    Measurable (stewartEmbeddedHouseholder i) := by
  unfold stewartEmbeddedHouseholder
  exact measurable_stewartHouseholder.comp
    (measurable_stewartEmbeddedHouseholderVector i)

theorem measurable_stewartSignDiagonal {n : ℕ} :
    Measurable (stewartSignDiagonal : StewartGaussianInputs n → RSqMat n) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  by_cases hij : i = j
  · subst j
    simp only [stewartSignDiagonal, diagMatrix, ↓reduceIte]
    exact measurable_householderSign.comp (measurable_stewartRDiagonal i)
  · simp [stewartSignDiagonal, diagMatrix, hij]

theorem measurable_matMul_of_measurable
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    {A B : α → RSqMat n} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x => matMul n (A x) (B x) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  exact Finset.measurable_fun_sum Finset.univ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hA)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hB))

theorem measurable_matrixListProduct_eval
    {α : Type*} [MeasurableSpace α] {n : ℕ}
    (Ps : List (α → RSqMat n))
    (hPs : ∀ P ∈ Ps, Measurable P) :
    Measurable fun x => matrixListProduct (Ps.map fun P => P x) := by
  induction Ps with
  | nil =>
      change Measurable fun _ : α => idMatrix n
      exact measurable_const
  | cons P Ps ih =>
      simp only [List.map_cons, matrixListProduct]
      exact measurable_matMul_of_measurable
        (hPs P (by simp))
        (ih fun Q hQ => hPs Q (by simp [hQ]))

theorem stewartHouseholderFunctionList_measurable {n : ℕ} :
    ∀ P ∈ (stewartHouseholderFunctionList :
      List (StewartGaussianInputs n → RSqMat n)), Measurable P := by
  intro P hP
  rcases List.mem_ofFn.mp hP with ⟨k, rfl⟩
  dsimp
  exact (measurable_stewartEmbeddedHouseholder _).comp
    (measurable_pi_apply _)

theorem measurable_stewartHouseholderListProduct {n : ℕ} :
    Measurable fun z : StewartGaussianInputs n =>
      matrixListProduct (stewartHouseholderList z) := by
  have h := measurable_matrixListProduct_eval
    (stewartHouseholderFunctionList :
      List (StewartGaussianInputs n → RSqMat n))
    stewartHouseholderFunctionList_measurable
  convert h using 1
  funext z
  exact congrArg matrixListProduct
    (stewartHouseholderFunctionList_map_apply z).symm

theorem measurable_stewartOrthogonalMatrix {n : ℕ} :
    Measurable (stewartOrthogonalMatrix :
      StewartGaussianInputs n → RSqMat n) := by
  unfold stewartOrthogonalMatrix stewartOrthogonalProduct
  exact measurable_matMul_of_measurable measurable_stewartSignDiagonal
    measurable_stewartHouseholderListProduct

theorem measurable_stewartOrthogonalGroupOutput {n : ℕ} :
    Measurable (stewartOrthogonalGroupOutput (n := n)) := by
  unfold stewartOrthogonalGroupOutput
  exact measurable_stewartOrthogonalMatrix.subtype_mk

/-- The exact push-forward law of Stewart's Gaussian-tail producer. -/
noncomputable def stewartOrthogonalGroupLaw (n : ℕ) :
    Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Measure.map (stewartOrthogonalGroupOutput (n := n))
    (stewartGaussianInputMeasure n)

/-- Once measurability of the explicit producer is supplied, normalization of
its push-forward follows from the proved product-Gaussian normalization. -/
theorem stewartOrthogonalGroupLaw_univ_of_measurable (n : ℕ)
    (hmeas : Measurable (stewartOrthogonalGroupOutput (n := n))) :
    stewartOrthogonalGroupLaw n Set.univ = 1 := by
  rw [stewartOrthogonalGroupLaw, Measure.map_apply hmeas MeasurableSet.univ]
  exact stewartGaussianInputMeasure_univ n

/-- The concrete Stewart push-forward is normalized. -/
theorem stewartOrthogonalGroupLaw_univ (n : ℕ) :
    stewartOrthogonalGroupLaw n Set.univ = 1 :=
  stewartOrthogonalGroupLaw_univ_of_measurable n
    measurable_stewartOrthogonalGroupOutput

end NumStability
