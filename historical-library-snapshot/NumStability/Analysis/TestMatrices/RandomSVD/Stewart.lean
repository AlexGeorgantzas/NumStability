import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import NumStability.Algorithms.LinearSystems.QR.HouseholderReflector
import NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.TestMatrices.Orthogonal.Basic
import NumStability.Analysis.TestMatrices.RandomSVD.Basic

/-!
# NumStability Analysis TestMatrices RandomSVD Stewart

Canonical destination for material split out of
`NumStability.Algorithms.TestMatrices.Higham28Stewart` by wave W09 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

namespace NumStability

open MeasureTheory ProbabilityTheory

open scoped BigOperators

/-- Stewart's independent tail vectors in zero-based form: stage `i` has
dimension `n - i`, corresponding to the source's `x_{i+1} ∈ ℝ^{n-i}`. -/
abbrev StewartGaussianInputs (n : ℕ) :=
  ∀ i : Fin n, Fin (n - i.val) → ℝ

/-- The exact product law of the independent `N(0,1)` tail entries. -/
noncomputable def stewartGaussianInputMeasure (n : ℕ) :
    Measure (StewartGaussianInputs n) :=
  Measure.pi (fun i : Fin n =>
    Measure.pi (fun _ : Fin (n - i.val) => gaussianReal 0 1))

/-- Stewart's input law is a probability measure in every dimension. -/
theorem stewartGaussianInputMeasure_univ (n : ℕ) :
    stewartGaussianInputMeasure n Set.univ = 1 := by
  unfold stewartGaussianInputMeasure
  calc
    (Measure.pi (fun i : Fin n =>
        Measure.pi (fun _ : Fin (n - i.val) => gaussianReal 0 1))) Set.univ =
      ∏ i : Fin n,
        Measure.pi (fun _ : Fin (n - i.val) => gaussianReal 0 1) Set.univ :=
      MeasureTheory.Measure.pi_univ _
    _ = 1 := by simp

instance stewartGaussianInputMeasure_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (stewartGaussianInputMeasure n) :=
  ⟨stewartGaussianInputMeasure_univ n⟩

/-- A total `2/(vᵀv)` coefficient.  The zero-vector branch produces the
identity reflector; standard Gaussian inputs reach that branch only on the
later null-event obligation. -/
noncomputable def stewartHouseholderBeta {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  let s := ∑ i : Fin n, v i * v i
  if s = 0 then 0 else 2 / s

/-- The total coefficient always produces an orthogonal Householder matrix. -/
theorem stewartHouseholder_orthogonal {n : ℕ} (v : Fin n → ℝ) :
    IsOrthogonal n (householder n v (stewartHouseholderBeta v)) := by
  by_cases hs : (∑ i : Fin n, v i * v i) = 0
  · have hmatrix : householder n v (stewartHouseholderBeta v) = idMatrix n := by
      ext i j
      simp [householder, stewartHouseholderBeta, hs]
    rw [hmatrix]
    exact IsOrthogonal.id n
  · apply householder_orthogonal
    simp [stewartHouseholderBeta, hs]

/-- The exact local reflector used by the producer really reduces its input
tail to the signed norm on the first coordinate.  This is the source's
`Pbar_i x_i = r_ii e₁`, not merely an orthogonality contract. -/
theorem stewartLocalHouseholder_reduces {d : ℕ} (hd : 0 < d)
    (x : Fin d → ℝ) (j : Fin d) :
    matMulVec d
        (householder d (householderVector hd x)
          (stewartHouseholderBeta (householderVector hd x))) x j =
      if j = ⟨0, hd⟩ then householderAlpha hd x else 0 := by
  by_cases hx : x = 0
  · subst x
    simp [matMulVec, householder, stewartHouseholderBeta, householderVector,
      householderScale, householderAlpha, idMatrix]
  · let p : Fin d := ⟨0, hd⟩
    let v := householderVector hd x
    let alpha := householderAlpha hd x
    have hv : v = householderActiveVector d p x alpha := by
      funext k
      by_cases hkp : k = p
      · subst k
        simp [v, p, alpha, householderActiveVector, householderAlpha]
      · simp [v, p, alpha, householderVector, householderActiveVector, hkp]
    have halpha : alpha * alpha = vecNorm2Sq x := by
      unfold alpha householderAlpha
      rw [neg_mul_neg, householderScale_mul_self]
      simp [vecNorm2Sq, pow_two]
    have hv_ne : v ≠ 0 := by
      intro hvzero
      have hv0 := householderVector_zero_ne_zero_of_ne_zero hd x hx
      apply hv0
      simpa [v, p] using congrFun hvzero p
    have hden : (∑ k : Fin d, v k * v k) ≠ 0 := by
      have hpos : 0 < ∑ k : Fin d, v k * v k := by
        simpa [dotProduct] using (dotProduct_self_pos_iff_real d v).2 hv_ne
      exact ne_of_gt hpos
    have hbeta : stewartHouseholderBeta v = householderBetaSpec d v := by
      simp [stewartHouseholderBeta, householderBetaSpec, hden]
    rw [show householderVector hd x = v from rfl, hbeta, hv]
    exact matMulVec_householder_activeVector_eq_alpha_basis
      d p x alpha halpha (by simpa [← hv] using hden) j

theorem measurable_householderSign : Measurable householderSign := by
  unfold householderSign
  exact Measurable.ite measurableSet_Iio measurable_const measurable_const

theorem measurable_householderScale {d : ℕ} (hd : 0 < d) :
    Measurable (householderScale hd) := by
  unfold householderScale
  apply Measurable.mul
  · exact measurable_householderSign.comp
      (measurable_pi_apply (⟨0, hd⟩ : Fin d))
  · apply Measurable.sqrt
    exact Finset.measurable_fun_sum Finset.univ fun k _ =>
      (measurable_pi_apply k).mul (measurable_pi_apply k)

theorem measurable_householderAlpha {d : ℕ} (hd : 0 < d) :
    Measurable (householderAlpha hd) := by
  change Measurable fun x => -householderScale hd x
  exact (measurable_householderScale hd).neg

theorem measurable_householderVector {d : ℕ} (hd : 0 < d) :
    Measurable (householderVector hd) := by
  refine measurable_pi_lambda _ fun k => ?_
  by_cases hk : k = ⟨0, hd⟩
  · subst k
    simp only [householderVector, ↓reduceIte]
    exact (measurable_pi_apply (⟨0, hd⟩ : Fin d)).add
      (measurable_householderScale hd)
  · simpa [householderVector, hk] using (measurable_pi_apply k)

theorem measurable_stewartHouseholderBeta {d : ℕ} :
    Measurable (stewartHouseholderBeta : (Fin d → ℝ) → ℝ) := by
  let s : (Fin d → ℝ) → ℝ := fun v => ∑ k : Fin d, v k * v k
  have hs : Measurable s :=
    Finset.measurable_fun_sum Finset.univ fun k _ =>
      (measurable_pi_apply k).mul (measurable_pi_apply k)
  unfold stewartHouseholderBeta
  exact Measurable.ite (measurableSet_eq_fun hs measurable_const)
    measurable_const (measurable_const.div hs)

theorem measurable_stewartHouseholder {d : ℕ} :
    Measurable fun v : Fin d → ℝ =>
      householder d v (stewartHouseholderBeta v) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  unfold householder
  exact measurable_const.sub
    ((measurable_stewartHouseholderBeta.mul (measurable_pi_apply i)).mul
      (measurable_pi_apply j))

/-- Embed the local Householder vector for stage `i` into the final `n`
coordinates, with an identically zero prefix. -/
noncomputable def stewartEmbeddedHouseholderVector {n : ℕ} (i : Fin n)
    (x : Fin (n - i.val) → ℝ) : Fin n → ℝ :=
  fun j =>
    if h : i.val ≤ j.val then
      householderVector (by omega : 0 < n - i.val) x
        ⟨j.val - i.val, by omega⟩
    else 0

@[simp] theorem stewartEmbeddedHouseholderVector_of_lt
    {n : ℕ} (i j : Fin n) (x : Fin (n - i.val) → ℝ)
    (hji : j.val < i.val) :
    stewartEmbeddedHouseholderVector i x j = 0 := by
  simp [stewartEmbeddedHouseholderVector, not_le_of_gt hji]

/-- The full stage reflector `P_i = diag(I_i, Pbar_i)`. -/
noncomputable def stewartEmbeddedHouseholder {n : ℕ} (i : Fin n)
    (x : Fin (n - i.val) → ℝ) : RSqMat n :=
  let v := stewartEmbeddedHouseholderVector i x
  householder n v (stewartHouseholderBeta v)

theorem stewartEmbeddedHouseholder_orthogonal
    {n : ℕ} (i : Fin n) (x : Fin (n - i.val) → ℝ) :
    IsOrthogonal n (stewartEmbeddedHouseholder i x) := by
  exact stewartHouseholder_orthogonal (stewartEmbeddedHouseholderVector i x)

theorem measurable_stewartEmbeddedHouseholderVector
    {n : ℕ} (i : Fin n) :
    Measurable (stewartEmbeddedHouseholderVector i) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases hij : i.val ≤ j.val
  · let k : Fin (n - i.val) := ⟨j.val - i.val, by omega⟩
    simpa [stewartEmbeddedHouseholderVector, hij, k] using
      (measurable_pi_apply k).comp
        (measurable_householderVector (by omega : 0 < n - i.val))
  · simp [stewartEmbeddedHouseholderVector, hij]

/-- The diagonal quantity `r_ii` used by Stewart.  At the first `n - 1`
stages it is the signed norm to which the Householder transformation reduces
the local Gaussian tail.  The source specifies the final scalar separately as
`r_nn = sign(x_n)`. -/
noncomputable def stewartRDiagonal {n : ℕ} (z : StewartGaussianInputs n)
    (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    householderAlpha (by omega : 0 < n - i.val) (z i)
  else
    householderSign (z i ⟨0, by omega⟩)

/-- Stewart's `D = diag(sign(r_ii))`, with the stable convention `sign(0)=1`. -/
noncomputable def stewartSignDiagonal {n : ℕ}
    (z : StewartGaussianInputs n) : RSqMat n :=
  diagMatrix (fun i => householderSign (stewartRDiagonal z i))

theorem stewartSignDiagonal_orthogonal {n : ℕ}
    (z : StewartGaussianInputs n) :
    IsOrthogonal n (stewartSignDiagonal z) := by
  apply IsOrthogonal.diagMatrix_of_sq_eq_one
  intro i
  unfold householderSign
  by_cases h : stewartRDiagonal z i < 0 <;> simp [h]

theorem measurable_stewartRDiagonal {n : ℕ} (i : Fin n) :
    Measurable fun z : StewartGaussianInputs n => stewartRDiagonal z i := by
  unfold stewartRDiagonal
  by_cases hstage : i.val + 1 < n
  · simp only [hstage, ↓reduceDIte]
    exact (measurable_householderAlpha (by omega : 0 < n - i.val)).comp
      (measurable_pi_apply i)
  · simp only [hstage, ↓reduceDIte]
    exact measurable_householderSign.comp
      ((measurable_pi_apply (⟨0, by omega⟩ : Fin (n - i.val))).comp
        (measurable_pi_apply i))

/-- The embedded reflectors `P₁,...,P_{n-1}` in the exact source order. -/
noncomputable def stewartHouseholderList {n : ℕ}
    (z : StewartGaussianInputs n) : List (RSqMat n) :=
  List.ofFn fun k : Fin (n - 1) =>
    let i : Fin n := ⟨k.val, by omega⟩
    stewartEmbeddedHouseholder i (z i)

/-- Source stages as a fixed finite list of measurable matrix-valued
functions.  Evaluating this list gives `stewartHouseholderList`. -/
noncomputable def stewartHouseholderFunctionList {n : ℕ} :
    List (StewartGaussianInputs n → RSqMat n) :=
  List.ofFn fun k : Fin (n - 1) => fun z =>
    let i : Fin n := ⟨k.val, by omega⟩
    stewartEmbeddedHouseholder i (z i)

theorem stewartHouseholderFunctionList_map_apply {n : ℕ}
    (z : StewartGaussianInputs n) :
    stewartHouseholderFunctionList.map (fun P => P z) =
      stewartHouseholderList z := by
  simp [stewartHouseholderFunctionList, stewartHouseholderList,
    Function.comp_def]

theorem stewartHouseholderList_orthogonal {n : ℕ}
    (z : StewartGaussianInputs n) :
    ∀ P ∈ stewartHouseholderList z, IsOrthogonal n P := by
  intro P hP
  rcases List.mem_ofFn.mp hP with ⟨k, rfl⟩
  dsimp
  exact stewartEmbeddedHouseholder_orthogonal _ _

/-- The executable sample-path map in Theorem 28.1,
`Q = D P₁ ⋯ P_{n-1}`. -/
noncomputable def stewartOrthogonalMatrix {n : ℕ}
    (z : StewartGaussianInputs n) : RSqMat n :=
  stewartOrthogonalProduct (stewartSignDiagonal z) (stewartHouseholderList z)

/-- Every sample path of the total Stewart producer is orthogonal. -/
theorem stewartOrthogonalMatrix_orthogonal {n : ℕ}
    (z : StewartGaussianInputs n) :
    IsOrthogonal n (stewartOrthogonalMatrix z) := by
  exact higham28_theorem28_1_product_orthogonal
    (stewartSignDiagonal z) (stewartHouseholderList z)
    (stewartSignDiagonal_orthogonal z)
    (stewartHouseholderList_orthogonal z)

/-- The same producer, with its codomain strengthened from ambient matrices to
Mathlib's exact orthogonal group. -/
noncomputable def stewartOrthogonalGroupOutput {n : ℕ}
    (z : StewartGaussianInputs n) : Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨stewartOrthogonalMatrix z, by
    rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    simpa [Matrix.mul_apply, matTranspose, Matrix.one_apply, idMatrix] using
      (stewartOrthogonalMatrix_orthogonal z).right_inv i j⟩

end NumStability
