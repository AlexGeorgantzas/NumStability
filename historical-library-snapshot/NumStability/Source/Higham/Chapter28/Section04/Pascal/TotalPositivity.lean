import NumStability.Analysis.LinearOperators.Jordan.NormalForm.PrimaryDecomposition
import NumStability.Analysis.TestMatrices.Cauchy.Contracts
import NumStability.Analysis.TestMatrices.Pascal.PascalTotalPositivity

/-!
Relocated from the historical wave owners NumStability.Algorithms.TestMatrices.Higham28PascalTotalPositivity under the R09/R10 completion waves; source-tier destination per the reviewed route ledger.
-/

namespace NumStability

open scoped BigOperators

open Set

private theorem det_eval_descPochhammer_eq_factorial_mul_choose
    {k : ℕ} (v : Fin k → ℕ) :
    Matrix.det (fun i j : Fin k =>
      (descPochhammer ℝ j).eval (v i : ℝ)) =
      (∏ j : Fin k, (Nat.factorial j : ℝ)) *
        Matrix.det (fun i j : Fin k => (Nat.choose (v i) j : ℝ)) := by
  convert Matrix.det_mul_row
    (fun j : Fin k => (Nat.factorial j : ℝ))
    (fun i j : Fin k => (Nat.choose (v i) j : ℝ))
  · rw [Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
    congr
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose _ _

private theorem det_choose_initial_columns_pos
    {n k : ℕ} (r : Fin k → Fin n) (hr : StrictMono r) :
    0 < Matrix.det (fun i j : Fin k =>
      (Nat.choose (r i).val j.val : ℝ)) := by
  let v : Fin k → ℝ := fun i => (r i).val
  have heval := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    v (fun j : Fin k => descPochhammer ℝ j)
    (fun j => descPochhammer_natDegree ℝ j)
    (fun j => monic_descPochhammer ℝ j)
  have hvand : 0 < Matrix.det (Matrix.vandermonde v) := by
    rw [Matrix.det_vandermonde]
    apply Finset.prod_pos
    intro i _
    apply Finset.prod_pos
    intro j hj
    have hij : i < j := Finset.mem_Ioi.mp hj
    have hrij : (r i).val < (r j).val := hr hij
    dsimp [v]
    exact sub_pos.mpr (by exact_mod_cast hrij)
  have hfac : 0 < ∏ j : Fin k, (Nat.factorial j : ℝ) := by
    positivity
  have hscale := det_eval_descPochhammer_eq_factorial_mul_choose
    (fun i : Fin k => (r i).val)
  have hcombined : Matrix.det (Matrix.vandermonde v) =
      (∏ j : Fin k, (Nat.factorial j : ℝ)) *
        Matrix.det (fun i j : Fin k => (Nat.choose (r i).val j.val : ℝ)) := by
    rw [heval]
    simpa [v, Matrix.of_apply] using hscale
  nlinarith [hcombined]

theorem pascalLower_initial_minor_pos
    {n k : ℕ} (r : Fin k → Fin n) (hr : StrictMono r) :
    0 < Matrix.det (fun i j : Fin k =>
      pascalLower n (r i)
        (Fin.castLE (by
          simpa using Fintype.card_le_of_injective r hr.injective) j)) := by
  simpa [pascalLower] using det_choose_initial_columns_pos r hr

/-- Higham, Section 28.4, p. 520: every square minor of positive order of
the symmetric Pascal matrix is strictly positive. -/
theorem pascalMatrix_isStrictlyTotallyPositive (n : ℕ) :
    IsStrictlyTotallyPositive (pascalMatrix n) := by
  intro k hk r c hr hc
  have hkn : k ≤ n := by
    simpa using Fintype.card_le_of_injective r hr.injective
  let rz : Fin k → Fin n := Fin.castLE hkn
  have hrz : StrictMono rz := Fin.strictMono_castLE hkn
  let sr : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono r hr)
  let sc : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono c hc)
  let sz : Set.powersetCard (Fin n) k :=
    Set.powersetCard.ofFinEmbEquiv (OrderEmbedding.ofStrictMono rz hrz)
  have hdet : Matrix.det (fun i j => pascalMatrix n (r i) (c j)) =
      compoundMatrix n k (pascalMatrix n) sr sc := by
    rw [compoundMatrix_apply]
    congr 1
    funext i j
    simp [sr, sc]
  rw [hdet, pascalMatrix_eq_lower_mul_transpose, compoundMatrix_mul,
    Matrix.mul_apply]
  have hL := pascalLower_isTotallyNonnegative n
  have hLT := isTotallyNonnegative_transpose hL
  apply Finset.sum_pos'
  · intro s _
    apply mul_nonneg
    · rw [compoundMatrix_apply]
      simpa [sr] using hL k r (Set.powersetCard.ofFinEmbEquiv.symm s)
        hr (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono
    · rw [compoundMatrix_apply]
      simpa [sc] using hLT k (Set.powersetCard.ofFinEmbEquiv.symm s) c
        (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono hc
  · refine ⟨sz, Finset.mem_univ _, ?_⟩
    apply mul_pos
    · rw [compoundMatrix_apply]
      simpa [sr, sz, rz] using pascalLower_initial_minor_pos r hr
    · rw [compoundMatrix_apply]
      have hcp := pascalLower_initial_minor_pos c hc
      let M : Matrix (Fin k) (Fin k) ℝ := fun i j =>
        pascalLower n (c i) (rz j)
      have hcpM : 0 < Matrix.det M := by
        simpa [M, rz] using hcp
      have ht : 0 < Matrix.det M.transpose := by
        rw [Matrix.det_transpose]
        exact hcpM
      have hgoal : 0 < Matrix.det (fun i j : Fin k =>
          (pascalLower n).transpose (rz i) (c j)) := by
        simpa only [Matrix.transpose_apply] using ht
      simpa [sc, sz] using hgoal

end NumStability
