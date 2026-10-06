-- Algorithms/Cholesky/AasenPermutationSourceCorrectionCh11.lean
--
-- Equation (11.15) prints `x = P w` after `P A P^T = L T L^T`.
-- For an accumulated permutation this is wrong: the coordinate return must
-- be `x = P^T w`.  This module gives a finite 3-cycle counterexample and the
-- corrected general solve bridge.

import NumStability.Algorithms.HighamChapter11

namespace NumStability

open scoped BigOperators Matrix

/-- Corrected Equation (11.15): the last coordinate change is `x = P^T w`. -/
def higham11_15_aasenSolveChainCorrected (n : ℕ)
    (Pmat L T : Fin n → Fin n → ℝ)
    (b z y w x : Fin n → ℝ) : Prop :=
  (∀ i : Fin n, ∑ j : Fin n, L i j * z j = ∑ j : Fin n, Pmat i j * b j) ∧
  (∀ i : Fin n, ∑ j : Fin n, T i j * y j = z i) ∧
  (∀ i : Fin n, ∑ j : Fin n, L j i * w j = y i) ∧
  (∀ i : Fin n, x i = ∑ j : Fin n, Pmat j i * w j)

/-- Orthogonal unpermutation: a solution of
`(P A P^T)w = P b`, returned as `x=P^T w`, solves `A x=b`. -/
theorem higham11_15_unpermute_corrected_matrix
    {n : ℕ} (P A Aperm : Matrix (Fin n) (Fin n) ℝ)
    (b w x : Fin n → ℝ)
    (horth : P.transpose * P = 1)
    (hperm : P * A * P.transpose = Aperm)
    (hsolve : Aperm *ᵥ w = P *ᵥ b)
    (hx : x = P.transpose *ᵥ w) :
    A *ᵥ x = b := by
  have hP : P *ᵥ (A *ᵥ x) = P *ᵥ b := by
    calc
      P *ᵥ (A *ᵥ x) = (P * A) *ᵥ x := Matrix.mulVec_mulVec x P A
      _ = (P * A) *ᵥ (P.transpose *ᵥ w) := by rw [hx]
      _ = (P * A * P.transpose) *ᵥ w :=
        Matrix.mulVec_mulVec w (P * A) P.transpose
      _ = Aperm *ᵥ w := by rw [hperm]
      _ = P *ᵥ b := hsolve
  calc
    A *ᵥ x = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ (A *ᵥ x) := by simp
    _ = (P.transpose * P) *ᵥ (A *ᵥ x) := by rw [horth]
    _ = P.transpose *ᵥ (P *ᵥ (A *ᵥ x)) :=
      (Matrix.mulVec_mulVec (A *ᵥ x) P.transpose P).symm
    _ = P.transpose *ᵥ (P *ᵥ b) := by rw [hP]
    _ = (P.transpose * P) *ᵥ b :=
      Matrix.mulVec_mulVec b P.transpose P
    _ = b := by rw [horth]; simp

/-- The corrected raw solve chain, an exact congruence factorization, and
orthogonality of `P` imply the original-coordinate system `A x=b`. -/
theorem higham11_15_aasenSolveChainCorrected_solve_of_product
    (n : ℕ) (Pmat A L T : Fin n → Fin n → ℝ)
    (b z y w x : Fin n → ℝ)
    (horth : (Matrix.of Pmat).transpose * Matrix.of Pmat = 1)
    (hprod : ∀ i j : Fin n,
      (∑ k₁ : Fin n, ∑ k₂ : Fin n, L i k₁ * T k₁ k₂ * L j k₂) =
        ∑ r : Fin n, ∑ s : Fin n, Pmat i r * A r s * Pmat j s)
    (hchain : higham11_15_aasenSolveChainCorrected n Pmat L T b z y w x) :
    ∀ i : Fin n, ∑ j : Fin n, A i j * x j = b i := by
  let Aperm : Fin n → Fin n → ℝ := fun i j =>
    ∑ r : Fin n, ∑ s : Fin n, Pmat i r * A r s * Pmat j s
  let rhs : Fin n → ℝ := fun i => ∑ j : Fin n, Pmat i j * b j
  have hidentityChain : higham11_15_aasenSolveChain n
      (fun i j => if i = j then 1 else 0) L T rhs z y w w := by
    rcases hchain with ⟨hLz, hTy, hLtw, _hx⟩
    refine ⟨?_, hTy, hLtw, ?_⟩
    · intro i
      simpa [rhs] using hLz i
    · intro i
      simp
  have hpermuted : ∀ i : Fin n,
      ∑ j : Fin n, Aperm i j * w j = rhs i :=
    higham11_15_aasenSolveChain_identity_solve_of_product
      n Aperm L T rhs z y w w (by
        intro i j
        simpa [Aperm] using hprod i j) hidentityChain
  have hpermMatrix : Matrix.of Pmat * Matrix.of A * (Matrix.of Pmat).transpose =
      Matrix.of Aperm := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Aperm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.sum_mul]
  have hsolveMatrix : Matrix.of Aperm *ᵥ w = Matrix.of Pmat *ᵥ b := by
    funext i
    exact hpermuted i
  have hxMatrix : x = (Matrix.of Pmat).transpose *ᵥ w := by
    funext i
    exact hchain.2.2.2 i
  have hsource := higham11_15_unpermute_corrected_matrix
    (Matrix.of Pmat) (Matrix.of A) (Matrix.of Aperm)
    b w x horth hpermMatrix hsolveMatrix hxMatrix
  intro i
  exact congrFun hsource i

/-! ## Finite witness for the printed `x = P w` error -/

private def higham11_15_cycleP (i j : Fin 3) : ℝ :=
  if (i.val = 0 && j.val = 1) ||
      (i.val = 1 && j.val = 2) ||
      (i.val = 2 && j.val = 0) then 1 else 0

private def higham11_15_identity3 (i j : Fin 3) : ℝ :=
  if i = j then 1 else 0

private def higham11_15_basis0 (i : Fin 3) : ℝ :=
  if i.val = 0 then 1 else 0

private noncomputable def higham11_15_cycleZ : Fin 3 → ℝ := fun i =>
  ∑ j : Fin 3, higham11_15_cycleP i j * higham11_15_basis0 j

private noncomputable def higham11_15_cycleY : Fin 3 → ℝ :=
  higham11_15_cycleZ

private noncomputable def higham11_15_cycleW : Fin 3 → ℝ :=
  higham11_15_cycleY

private noncomputable def higham11_15_printedX : Fin 3 → ℝ := fun i =>
  ∑ j : Fin 3, higham11_15_cycleP i j * higham11_15_cycleW j

/-- A genuine 3-cycle permutation has `P I P^T=I`; the first three exact
solves in printed (11.15) hold, but the printed return `x=P w` gives `P^2 b`
and does not solve `I x=b`. -/
theorem higham11_15_printed_coordinate_return_is_false :
    (∀ i j : Fin 3,
      (∑ r : Fin 3, ∑ s : Fin 3,
        higham11_15_cycleP i r * higham11_15_identity3 r s *
          higham11_15_cycleP j s) = higham11_15_identity3 i j) ∧
    higham11_15_aasenSolveChain 3 higham11_15_cycleP
      higham11_15_identity3 higham11_15_identity3 higham11_15_basis0
      higham11_15_cycleZ higham11_15_cycleY higham11_15_cycleW
      higham11_15_printedX ∧
    ¬ (∀ i : Fin 3, ∑ j : Fin 3,
      higham11_15_identity3 i j * higham11_15_printedX j =
        higham11_15_basis0 i) := by
  constructor
  · intro i j
    fin_cases i <;> fin_cases j <;>
      norm_num [higham11_15_cycleP, higham11_15_identity3, Fin.sum_univ_three] <;>
      omega
  constructor
  · simp [higham11_15_aasenSolveChain, higham11_15_identity3,
      higham11_15_cycleY, higham11_15_cycleW, higham11_15_printedX,
      higham11_15_cycleZ]
  · intro h
    have h0 := h (0 : Fin 3)
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h02 : (0 : Fin 3) ≠ 2 := by decide
    norm_num [higham11_15_cycleP, higham11_15_identity3,
      higham11_15_basis0, higham11_15_cycleY, higham11_15_cycleW,
      higham11_15_printedX, higham11_15_cycleZ,
      Fin.sum_univ_three, h20, h02] at h0

end NumStability
