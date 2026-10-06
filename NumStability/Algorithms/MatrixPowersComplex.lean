-- Algorithms/MatrixPowersComplex.lean
--
-- Higham Chapter 18: Error analysis of matrix powers — the GENERAL
-- (complex-spectrum, possibly defective) case of Theorem 18.1
-- (Higham–Knight) for a REAL input matrix `A` with COMPLEX Jordan-form
-- similarity data (Higham, Accuracy and Stability of Numerical Algorithms,
-- 2nd ed., §18.2, Theorem 18.1, pp. 347–348).
--
-- The computed iteration `v_{k+1} = fl(A v_k)` is real (a floating-point
-- object), matching the book's computational setting; the Jordan data
-- `X⁻¹ A X = J` lives over ℂ, which is the full generality of the printed
-- statement for real `A`.  The δ-scaling construction of the book's proof
-- is transported verbatim from the real-spectrum case
-- (`MatrixPowersJordan.lean`): the moduli arguments are identical because
-- `‖·‖` on ℂ is multiplicative and satisfies the triangle inequality.
--
-- Complex matrix infrastructure is REUSED from `Analysis/Norms.lean`
-- (source traceability):
--   `CVec`, `CMatrix`                  — Norms.lean (abbrevs)
--   `complexVecInfNorm` (+ nonneg / coord_le / le_of_coord_le)
--                                      — Norms.lean ~1580
--   `complexMatrixInfNorm` (+ nonneg / row_sum_le / le_of_row_sum_le)
--                                      — Norms.lean ~3379  («cInfNorm»:
--                                        max row sum of entry norms)
--   `complexMatrixMul`, `complexMatrixMul_assoc`
--                                      — Norms.lean ~3068
--   `complexMatrixVecMul`, `complexMatrixVecMul_mul`
--                                      — Norms.lean ~3022
--   `IsComplexMatrixRightInverse`      — Norms.lean ~3033
-- Scalar margin lemmas are REUSED from `MatrixPowersJordan.lean`
-- (`jordanBeta`, `jordanBeta_pos`, `jordanBeta_lt_one`, `jordanBeta_add_eq`,
-- `higham_scaling_margin`) and the run-length machinery from the same file
-- (`jordanRunLength`, `exists_jordan_scaling_vector`) via a norm-matrix
-- wrapper.  Only what is missing over ℂ is defined here.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import NumStability.Analysis.Norms
import NumStability.Algorithms.MatrixPowersJordan

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Missing pieces of the complex ∞-norm lemma suite
-- (complexMatrixInfNorm = the max-row-sum «cInfNorm»; the definition and
--  the nonneg / row_sum_le / le_of_row_sum_le lemmas are reused from
--  Analysis/Norms.lean)
-- ============================================================

/-- Matrix–vector ∞-norm bound over ℂ:
    `‖A x‖∞ ≤ ‖A‖∞ · ‖x‖∞` for the concrete complex row-sum norm. -/
theorem complexVecInfNorm_vecMul_le {m n : ℕ} (A : CMatrix m n) (x : CVec n) :
    complexVecInfNorm (complexMatrixVecMul A x) ≤
      complexMatrixInfNorm A * complexVecInfNorm x := by
  apply complexVecInfNorm_le_of_coord_le
  · exact mul_nonneg (complexMatrixInfNorm_nonneg A) (complexVecInfNorm_nonneg x)
  · intro i
    calc ‖complexMatrixVecMul A x i‖
        = ‖∑ j : Fin n, A i j * x j‖ := rfl
      _ ≤ ∑ j : Fin n, ‖A i j * x j‖ := norm_sum_le _ _
      _ = ∑ j : Fin n, ‖A i j‖ * ‖x j‖ :=
          Finset.sum_congr rfl (fun j _ => norm_mul _ _)
      _ ≤ ∑ j : Fin n, ‖A i j‖ * complexVecInfNorm x := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_left (complexVecInfNorm_coord_le x j)
            (norm_nonneg _)
      _ = (∑ j : Fin n, ‖A i j‖) * complexVecInfNorm x :=
          (Finset.sum_mul ..).symm
      _ ≤ complexMatrixInfNorm A * complexVecInfNorm x :=
          mul_le_mul_of_nonneg_right (complexMatrixInfNorm_row_sum_le A i)
            (complexVecInfNorm_nonneg x)

/-- Submultiplicativity of the complex matrix ∞-norm over `complexMatrixMul`:
    `‖A·B‖∞ ≤ ‖A‖∞ · ‖B‖∞`.  The proof only uses `‖ab‖ = ‖a‖‖b‖` and the
    triangle inequality, exactly as in the real case. -/
theorem complexMatrixInfNorm_mul_le {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixInfNorm (complexMatrixMul A B) ≤
      complexMatrixInfNorm A * complexMatrixInfNorm B := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact mul_nonneg (complexMatrixInfNorm_nonneg A)
      (complexMatrixInfNorm_nonneg B)
  · intro i
    calc ∑ j : Fin p, ‖complexMatrixMul A B i j‖
        = ∑ j : Fin p, ‖∑ k : Fin n, A i k * B k j‖ := rfl
      _ ≤ ∑ j : Fin p, ∑ k : Fin n, ‖A i k * B k j‖ :=
          Finset.sum_le_sum (fun j _ => norm_sum_le _ _)
      _ = ∑ k : Fin n, ∑ j : Fin p, ‖A i k * B k j‖ := by
          rw [Finset.sum_comm]
      _ = ∑ k : Fin n, ‖A i k‖ * ∑ j : Fin p, ‖B k j‖ := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => norm_mul _ _)
      _ ≤ ∑ k : Fin n, ‖A i k‖ * complexMatrixInfNorm B := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left
            (complexMatrixInfNorm_row_sum_le B k) (norm_nonneg _)
      _ = (∑ k : Fin n, ‖A i k‖) * complexMatrixInfNorm B :=
          (Finset.sum_mul ..).symm
      _ ≤ complexMatrixInfNorm A * complexMatrixInfNorm B :=
          mul_le_mul_of_nonneg_right (complexMatrixInfNorm_row_sum_le A i)
            (complexMatrixInfNorm_nonneg B)

/-- Triangle inequality for the complex matrix ∞-norm (entrywise sum). -/
theorem complexMatrixInfNorm_add_le {m n : ℕ} (M N : CMatrix m n) :
    complexMatrixInfNorm (fun i j => M i j + N i j) ≤
      complexMatrixInfNorm M + complexMatrixInfNorm N := by
  apply complexMatrixInfNorm_le_of_row_sum_le
  · exact add_nonneg (complexMatrixInfNorm_nonneg M)
      (complexMatrixInfNorm_nonneg N)
  · intro i
    calc ∑ j : Fin n, ‖M i j + N i j‖
        ≤ ∑ j : Fin n, (‖M i j‖ + ‖N i j‖) :=
          Finset.sum_le_sum (fun j _ => norm_add_le _ _)
      _ = (∑ j : Fin n, ‖M i j‖) + ∑ j : Fin n, ‖N i j‖ :=
          Finset.sum_add_distrib
      _ ≤ complexMatrixInfNorm M + complexMatrixInfNorm N :=
          add_le_add (complexMatrixInfNorm_row_sum_le M i)
            (complexMatrixInfNorm_row_sum_le N i)

/-- A diagonal complex matrix with entries of modulus at most `ρ ≥ 0` has
    ∞-norm at most `ρ`. -/
theorem complexMatrixInfNorm_diagonal_le {n : ℕ} (M : CMatrix n n) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hdiag : ∀ i j, i ≠ j → M i j = 0)
    (hlam : ∀ i, ‖M i i‖ ≤ ρ) : complexMatrixInfNorm M ≤ ρ := by
  apply complexMatrixInfNorm_le_of_row_sum_le hρ0
  intro i
  have hsingle : ∑ j : Fin n, ‖M i j‖ = ‖M i i‖ := by
    refine Finset.sum_eq_single i (fun b _ hb => ?_) (fun h => ?_)
    · rw [hdiag i b (Ne.symm hb), norm_zero]
    · exact absurd (Finset.mem_univ i) h
  rw [hsingle]
  exact hlam i

-- ============================================================
-- Real-cast bridges: embedding ℝ-vectors and ℝ-matrices into ℂ
-- preserves the ∞-norms (via ‖(x : ℂ)‖ = ‖x‖ = |x|)
-- ============================================================

/-- The complex ∞-norm of a real-cast vector equals the real ∞-norm. -/
theorem complexVecInfNorm_ofReal {n : ℕ} (x : Fin n → ℝ) :
    complexVecInfNorm (fun i => ((x i : ℝ) : ℂ)) = infNormVec x := by
  apply le_antisymm
  · apply complexVecInfNorm_le_of_coord_le _ (infNormVec_nonneg x)
    intro i
    show ‖((x i : ℝ) : ℂ)‖ ≤ infNormVec x
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_le_infNormVec x i
  · apply infNormVec_le_of_abs_le
    · intro i
      have h := complexVecInfNorm_coord_le (fun k => ((x k : ℝ) : ℂ)) i
      simp only [Complex.norm_real, Real.norm_eq_abs] at h
      exact h
    · exact complexVecInfNorm_nonneg _

/-- The complex matrix ∞-norm of a real-cast matrix equals the real matrix
    ∞-norm: `‖Â‖∞ = ‖A‖∞` for `Â i j := ((A i j : ℝ) : ℂ)`. -/
theorem complexMatrixInfNorm_ofReal {n : ℕ} (M : Fin n → Fin n → ℝ) :
    complexMatrixInfNorm (fun i j => ((M i j : ℝ) : ℂ)) = infNorm M := by
  apply le_antisymm
  · apply complexMatrixInfNorm_le_of_row_sum_le (infNorm_nonneg M)
    intro i
    calc ∑ j : Fin n, ‖((M i j : ℝ) : ℂ)‖
        = ∑ j : Fin n, |M i j| :=
          Finset.sum_congr rfl (fun j _ => by
            rw [Complex.norm_real, Real.norm_eq_abs])
      _ ≤ infNorm M := row_sum_le_infNorm M i
  · apply infNorm_le_of_row_sum_le
    · intro i
      calc ∑ j : Fin n, |M i j|
          = ∑ j : Fin n, ‖((M i j : ℝ) : ℂ)‖ :=
            Finset.sum_congr rfl (fun j _ => by
              rw [Complex.norm_real, Real.norm_eq_abs])
        _ ≤ complexMatrixInfNorm (fun i j => ((M i j : ℝ) : ℂ)) :=
            complexMatrixInfNorm_row_sum_le
              (fun i j => ((M i j : ℝ) : ℂ)) i
    · exact complexMatrixInfNorm_nonneg _

/-- Perturbation-to-complex norm transfer: a real componentwise bound
    `|ΔA| ≤ η|A|` gives `‖ΔÂ‖∞ ≤ η·‖A‖∞` for the real-cast matrix `ΔÂ`.
    (Combined with `complexMatrixInfNorm_ofReal`, this is
    `‖ΔÂ‖∞ ≤ η·‖Â‖∞`.) -/
theorem complexMatrixInfNorm_ofReal_le_mul {n : ℕ}
    (ΔA A : Fin n → Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η)
    (hΔ : ∀ i j, |ΔA i j| ≤ η * |A i j|) :
    complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) ≤ η * infNorm A := by
  rw [complexMatrixInfNorm_ofReal]
  exact infNorm_le_mul_of_abs_le_mul_abs ΔA A hη hΔ

-- ============================================================
-- Entrywise addition distributes over complexMatrixMul
-- ============================================================

/-- Left distributivity of `complexMatrixMul` over entrywise addition. -/
theorem complexMatrixMul_add_left {m n p : ℕ}
    (A B : CMatrix m n) (C : CMatrix n p) :
    complexMatrixMul (fun i j => A i j + B i j) C
      = fun i j => complexMatrixMul A C i j + complexMatrixMul B C i j := by
  funext i j
  unfold complexMatrixMul
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => add_mul _ _ _)

/-- Right distributivity of `complexMatrixMul` over entrywise addition. -/
theorem complexMatrixMul_add_right {m n p : ℕ}
    (A : CMatrix m n) (B C : CMatrix n p) :
    complexMatrixMul A (fun i j => B i j + C i j)
      = fun i j => complexMatrixMul A B i j + complexMatrixMul A C i j := by
  funext i j
  unfold complexMatrixMul
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => mul_add _ _ _)

-- ============================================================
-- §18.2  Complex similarity-based convergence engine (eq 18.14)
-- for a REAL computed-power sequence, embedded into ℂ
-- ============================================================

/-- **Complex similarity product bound** (eq 18.14 of Theorem 18.1's proof,
    transported to a complex similarity `S`): if the real computed-power
    sequence `v` satisfies the perturbed recurrence (18.10)–(18.11) with
    budget `c`, and the complex similarity `S` absorbs every admissible
    perturbation, `‖S⁻¹(Â+ΔÂ)S‖∞ ≤ q`, then the transformed embedded
    vectors decay geometrically:
    `‖S⁻¹ v̂_m‖∞ ≤ q^m · ‖S⁻¹ v̂_0‖∞`, where `v̂_m i := ((v m i : ℝ) : ℂ)`.

    Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.1 (pp. 347–348) — the telescoping step of the proof. -/
theorem complex_similarity_product_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : CMatrix n n)
    (hSr : IsComplexMatrixRightInverse S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
        (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) ≤ q) :
    ∀ m, complexVecInfNorm
        (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) ≤
      q ^ m * complexVecInfNorm
        (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ))) := by
  intro m
  induction m with
  | zero => simp [pow_zero, one_mul]
  | succ m ih =>
    obtain ⟨ΔA, hΔ, hstep⟩ := hComp.step m
    have hBk := hBound ΔA hΔ
    -- Embed the real perturbed step into ℂ: v̂_{m+1} = (Â+ΔÂ)·v̂_m.
    have hstepC : (fun i => ((v (m + 1) i : ℝ) : ℂ)) =
        complexMatrixVecMul (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
          (fun i => ((v m i : ℝ) : ℂ)) := by
      funext i
      show ((v (m + 1) i : ℝ) : ℂ) =
        ∑ j : Fin n, ((A i j + ΔA i j : ℝ) : ℂ) * ((v m j : ℝ) : ℂ)
      rw [hstep i, Complex.ofReal_sum]
      exact Finset.sum_congr rfl (fun j _ => Complex.ofReal_mul _ _)
    -- Key: S⁻¹ v̂_{m+1} = (S⁻¹(Â+ΔÂ)S)(S⁻¹ v̂_m).
    have key : complexMatrixVecMul S_inv (fun i => ((v (m + 1) i : ℝ) : ℂ)) =
        complexMatrixVecMul
          (complexMatrixMul S_inv (complexMatrixMul
            (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S))
          (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) := by
      rw [complexMatrixVecMul_mul, complexMatrixVecMul_mul, hSr, ← hstepC]
    calc complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v (m + 1) i : ℝ) : ℂ)))
        = complexVecInfNorm (complexMatrixVecMul
            (complexMatrixMul S_inv (complexMatrixMul
              (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S))
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ)))) := by
          rw [key]
      _ ≤ complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
            (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) *
          complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
          complexVecInfNorm_vecMul_le _ _
      _ ≤ q * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
          mul_le_mul_of_nonneg_right hBk (complexVecInfNorm_nonneg _)
      _ ≤ q * (q ^ m * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ)))) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (m + 1) * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ))) := by
          ring

/-- **Complex normwise bound via similarity**:
    `‖v_m‖∞ ≤ κ∞(S) · q^m · ‖v_0‖∞` with `κ∞(S) = ‖S‖∞·‖S⁻¹‖∞` over ℂ,
    for a real computed-power sequence `v` and complex absorbing
    similarity `S`.  Uses `v̂ = S(S⁻¹ v̂)` and the real-cast norm equality
    `‖v̂_m‖∞ = ‖v_m‖∞`. -/
theorem complex_similarity_normwise_bound (n : ℕ)
    (A : Fin n → Fin n → ℝ)
    (S S_inv : CMatrix n n)
    (hSr : IsComplexMatrixRightInverse S S_inv)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ)
    (hComp : ComputedMatPowVec n A v c)
    (q : ℝ) (hq : 0 ≤ q)
    (hBound : ∀ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ c * |A i j|) →
      complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
        (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) ≤ q)
    (m : ℕ) :
    infNormVec (v m) ≤
      complexMatrixInfNorm S * complexMatrixInfNorm S_inv * q ^ m *
        infNormVec (v 0) := by
  have hprod := complex_similarity_product_bound n A S S_inv hSr v c hComp
    q hq hBound m
  have hrecover : (fun i => ((v m i : ℝ) : ℂ)) =
      complexMatrixVecMul S
        (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
    (hSr _).symm
  have h1 : infNormVec (v m) ≤
      complexMatrixInfNorm S * complexVecInfNorm
        (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) := by
    calc infNormVec (v m)
        = complexVecInfNorm (fun i => ((v m i : ℝ) : ℂ)) :=
          (complexVecInfNorm_ofReal (v m)).symm
      _ = complexVecInfNorm (complexMatrixVecMul S
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ)))) :=
          congrArg complexVecInfNorm hrecover
      _ ≤ complexMatrixInfNorm S * complexVecInfNorm
            (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) :=
          complexVecInfNorm_vecMul_le _ _
  have h3 : complexVecInfNorm
      (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ))) ≤
      complexMatrixInfNorm S_inv * infNormVec (v 0) := by
    calc complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ)))
        ≤ complexMatrixInfNorm S_inv *
            complexVecInfNorm (fun i => ((v 0 i : ℝ) : ℂ)) :=
          complexVecInfNorm_vecMul_le _ _
      _ = complexMatrixInfNorm S_inv * infNormVec (v 0) := by
          rw [complexVecInfNorm_ofReal]
  calc infNormVec (v m)
      ≤ complexMatrixInfNorm S * complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v m i : ℝ) : ℂ))) := h1
    _ ≤ complexMatrixInfNorm S * (q ^ m * complexVecInfNorm
          (complexMatrixVecMul S_inv (fun i => ((v 0 i : ℝ) : ℂ)))) :=
        mul_le_mul_of_nonneg_left hprod (complexMatrixInfNorm_nonneg S)
    _ ≤ complexMatrixInfNorm S *
          (q ^ m * (complexMatrixInfNorm S_inv * infNormVec (v 0))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h3 (pow_nonneg hq m))
          (complexMatrixInfNorm_nonneg S)
    _ = complexMatrixInfNorm S * complexMatrixInfNorm S_inv * q ^ m *
          infNormVec (v 0) := by
        ring

-- ============================================================
-- Complex diagonal scaling matrices
-- ============================================================

/-- Diagonal complex matrix with prescribed diagonal `d`. -/
noncomputable def cDiagMatrix {n : ℕ} (d : Fin n → ℂ) : CMatrix n n :=
  fun i j => if i = j then d i else 0

/-- Action of a complex diagonal matrix on a vector. -/
theorem cDiagMatrix_vecMul {n : ℕ} (d : Fin n → ℂ) (x : CVec n) :
    complexMatrixVecMul (cDiagMatrix d) x = fun i => d i * x i := by
  funext i
  unfold complexMatrixVecMul cDiagMatrix
  simp [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]

/-- Entrywise formula for the two-sided diagonal conjugation over ℂ:
    `(diag(q) · J · diag(p))_{ij} = q_i · J_{ij} · p_j`. -/
theorem cDiagMatrix_conj_entry {n : ℕ} (J : CMatrix n n)
    (p q : Fin n → ℂ) (i j : Fin n) :
    complexMatrixMul (cDiagMatrix q) (complexMatrixMul J (cDiagMatrix p)) i j
      = q i * J i j * p j := by
  have hleft : ∀ (M : CMatrix n n) (a : Fin n) (b : Fin n),
      complexMatrixMul (cDiagMatrix q) M a b = q a * M a b := by
    intro M a b
    unfold complexMatrixMul cDiagMatrix
    simp [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ]
  have hright : ∀ (a : Fin n) (b : Fin n),
      complexMatrixMul J (cDiagMatrix p) a b = J a b * p b := by
    intro a b
    unfold complexMatrixMul cDiagMatrix
    simp [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hleft, hright]
  ring

/-- ∞-norm bound for a complex diagonal matrix from an entrywise bound. -/
theorem complexMatrixInfNorm_cDiagMatrix_le {n : ℕ} (d : Fin n → ℂ) {c : ℝ}
    (hc : 0 ≤ c) (hd : ∀ i, ‖d i‖ ≤ c) :
    complexMatrixInfNorm (cDiagMatrix d) ≤ c := by
  apply complexMatrixInfNorm_diagonal_le _ hc
  · intro i j hij
    show (if i = j then d i else 0) = 0
    rw [if_neg hij]
  · intro i
    show ‖if i = i then d i else 0‖ ≤ c
    rw [if_pos rfl]
    exact hd i

-- ============================================================
-- The scaled bidiagonal row-sum bound ‖D⁻¹ J D‖∞ ≤ ρ + β over ℂ
-- ============================================================

/-- **Row sums of the scaled complex Jordan matrix** (Higham, 2nd ed., §18.2,
    Theorem 18.1 proof, pp. 347–348, moduli argument over ℂ): with `p` a real
    positive scaling vector satisfying the run-step law `p_j = β·p_i` across
    nonzero superdiagonal entries, each row sum of `|D⁻¹ J D|` (entries
    `(p_i)⁻¹ J_{ij} p_j`) is at most `ρ + β`.  Identical to the real proof
    with `|·|` replaced by `‖·‖` on ℂ. -/
theorem cJordan_conj_row_sum_le (n : ℕ) (J : CMatrix n n)
    (p : Fin n → ℝ) (ρ β : ℝ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (hp0 : ∀ i, 0 < p i)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      p j = β * p i)
    (i : Fin n) :
    ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖ ≤ ρ + β := by
  have hpne : p i ≠ 0 := (hp0 i).ne'
  have hpc : (((p i)⁻¹ : ℝ) : ℂ) * ((p i : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ hpne, Complex.ofReal_one]
  have hdiagentry : (((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ) = J i i := by
    calc (((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ)
        = J i i * ((((p i)⁻¹ : ℝ) : ℂ) * ((p i : ℝ) : ℂ)) := by ring
      _ = J i i := by rw [hpc, mul_one]
  by_cases hi : (i : ℕ) + 1 < n
  · -- A successor index exists: at most two nonzero entries in row i.
    have hii' : i ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
      intro h
      have h1 : (i : ℕ) = (i : ℕ) + 1 := congrArg Fin.val h
      omega
    have hzero : ∀ j : Fin n, j ≠ i → j ≠ (⟨(i : ℕ) + 1, hi⟩ : Fin n) →
        J i j = 0 := by
      intro j hj1 hj2
      apply hshape i j
      · exact fun h => hj1 (Fin.eq_of_val_eq h)
      · exact fun h => hj2 (Fin.eq_of_val_eq h)
    have hsub : ∑ j ∈ ({i, ⟨(i : ℕ) + 1, hi⟩} : Finset (Fin n)),
          ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖
        = ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖ := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      rw [hzero j hj.1 hj.2, mul_zero, zero_mul, norm_zero]
    rw [← hsub, Finset.sum_pair hii']
    have hd : ‖(((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ)‖ ≤ ρ := by
      rw [hdiagentry]
      exact hdiagbd i
    have hs : ‖(((p i)⁻¹ : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
        ((p (⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℝ) : ℂ)‖ ≤ β := by
      by_cases hJ : J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) = 0
      · rw [hJ, mul_zero, zero_mul, norm_zero]
        exact hβ0
      · have hstep := hpstep i (⟨(i : ℕ) + 1, hi⟩ : Fin n) rfl hJ
        have hentry : (((p i)⁻¹ : ℝ) : ℂ) *
            J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
            ((p (⟨(i : ℕ) + 1, hi⟩ : Fin n) : ℝ) : ℂ)
            = ((β : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
          rw [hstep, Complex.ofReal_mul]
          calc (((p i)⁻¹ : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
                (((β : ℝ) : ℂ) * ((p i : ℝ) : ℂ))
              = ((β : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) *
                ((((p i)⁻¹ : ℝ) : ℂ) * ((p i : ℝ) : ℂ)) := by ring
            _ = ((β : ℝ) : ℂ) * J i (⟨(i : ℕ) + 1, hi⟩ : Fin n) := by
                rw [hpc, mul_one]
        rw [hentry, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hβ0]
        have hJb := hsup i (⟨(i : ℕ) + 1, hi⟩ : Fin n) rfl
        calc β * ‖J i (⟨(i : ℕ) + 1, hi⟩ : Fin n)‖
            ≤ β * 1 := mul_le_mul_of_nonneg_left hJb hβ0
          _ = β := mul_one β
    exact add_le_add hd hs
  · -- Last row: only the diagonal entry survives.
    have hzero : ∀ j : Fin n, j ≠ i → J i j = 0 := by
      intro j hj
      apply hshape i j
      · exact fun h => hj (Fin.eq_of_val_eq h)
      · intro h
        have hlt := j.isLt
        omega
    have hsingle : ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖
        = ‖(((p i)⁻¹ : ℝ) : ℂ) * J i i * ((p i : ℝ) : ℂ)‖ := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [hzero j hj, mul_zero, zero_mul, norm_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [hsingle, hdiagentry]
    have h1 := hdiagbd i
    linarith

/-- **The contraction bound ‖D⁻¹ J D‖∞ ≤ ρ + β** for the δ-scaled complex
    Jordan matrix (Higham, 2nd ed., §18.2, Theorem 18.1 proof,
    pp. 347–348). -/
theorem complexMatrixInfNorm_cJordan_conj_le (n : ℕ) (J : CMatrix n n)
    (p : Fin n → ℝ) (ρ β : ℝ) (hρ0 : 0 ≤ ρ) (hβ0 : 0 ≤ β)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (hp0 : ∀ i, 0 < p i)
    (hpstep : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 →
      p j = β * p i) :
    complexMatrixInfNorm (complexMatrixMul
        (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
        (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
      ≤ ρ + β := by
  apply complexMatrixInfNorm_le_of_row_sum_le (add_nonneg hρ0 hβ0)
  intro i
  calc ∑ j : Fin n, ‖complexMatrixMul
        (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
        (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) i j‖
      = ∑ j : Fin n, ‖(((p i)⁻¹ : ℝ) : ℂ) * J i j * ((p j : ℝ) : ℂ)‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [cDiagMatrix_conj_entry]
    _ ≤ ρ + β := cJordan_conj_row_sum_le n J p ρ β hβ0 hshape hdiagbd hsup
        hp0 hpstep i

-- ============================================================
-- Run lengths of superdiagonal chains for a ℂ-entry Jordan matrix
-- ============================================================

/-- Length of the run of consecutive nonzero superdiagonal entries of the
    complex matrix `J` ending at position `k`, encoded by reusing the real
    run-length function on the entry-norm matrix (`J i j ≠ 0 ↔ ‖J i j‖ ≠ 0`).
    A maximal Jordan block size of `t` corresponds to
    `cJordanRunLength n J k ≤ t − 1` for all `k`. -/
noncomputable def cJordanRunLength (n : ℕ) (J : CMatrix n n) : ℕ → ℕ :=
  jordanRunLength n (fun i j => ‖J i j‖)

/-- Step law of the complex run length across a nonzero superdiagonal
    entry. -/
theorem cJordanRunLength_succ (n : ℕ) (J : CMatrix n n) (k : ℕ)
    (h : k + 1 < n) (hJ : J ⟨k, Nat.lt_of_succ_lt h⟩ ⟨k + 1, h⟩ ≠ 0) :
    cJordanRunLength n J (k + 1) = cJordanRunLength n J k + 1 := by
  unfold cJordanRunLength
  exact jordanRunLength_succ n (fun i j => ‖J i j‖) k h
    (norm_ne_zero_iff.mpr hJ)

/-- **Existence of the δ-scaling vector for complex Jordan data** (Higham,
    Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.1 proof, pp. 347–348): when every run of consecutive nonzero
    superdiagonal entries of the complex `J` has length at most `t − 1`
    (max Jordan block size ≤ `t`, via `cJordanRunLength`), the REAL positive
    vector `p_i = β^(run length at i)` satisfies `β^(t−1) ≤ p ≤ 1` and the
    run-step law `p_j = β·p_i` across nonzero superdiagonal entries.
    Obtained from the real-spectrum `exists_jordan_scaling_vector` applied
    to the entry-norm matrix. -/
theorem exists_cJordan_scaling_vector (n : ℕ) (J : CMatrix n n)
    (t : ℕ) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1) :
    ∃ p : Fin n → ℝ,
      (∀ i, 0 < p i) ∧ (∀ i, β ^ (t - 1) ≤ p i) ∧ (∀ i, p i ≤ 1) ∧
      (∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → J i j ≠ 0 → p j = β * p i) := by
  obtain ⟨p, hp0, hp1, hp2, hpstep⟩ :=
    exists_jordan_scaling_vector n (fun i j => ‖J i j‖) t β hβ0 hβ1 hrun
  exact ⟨p, hp0, hp1, hp2, fun i j hji hJ =>
    hpstep i j hji (norm_ne_zero_iff.mpr hJ)⟩

-- ============================================================
-- Theorem 18.1: the absorbing similarity over ℂ (all t ≥ 1)
-- ============================================================

/-- **The perturbation-absorbing complex similarity of Theorem 18.1's proof**
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    Theorem 18.1, pp. 347–348), complex Jordan data, all `1 ≤ t`.

    Given complex Jordan-form-like data for the real matrix `A` —
    `X·X⁻¹ = I` over ℂ, `X⁻¹ Â X = J` with `Â i j = ((A i j : ℝ) : ℂ)`,
    `J` upper bidiagonal with `‖J_{ii}‖ ≤ ρ < 1`, superdiagonal moduli ≤ 1,
    all other entries zero, and every run of consecutive nonzero
    superdiagonal entries of length ≤ `t − 1` — and the Higham–Knight
    condition (18.13)

      `4t·η·κ∞(X)·‖A‖∞ < (1−ρ)^t`,  `κ∞(X) = ‖X‖∞·‖X⁻¹‖∞` over ℂ,

    there exists a complex similarity `S` (namely `S = X·D` with
    `D = diag(p)`, `p` the real δ-scaling vector; `S = X` when `t = 1`)
    and `q < 1` absorbing every admissible real perturbation:
    `‖S⁻¹(Â+ΔÂ)S‖∞ ≤ q` whenever `|ΔA| ≤ η|A|` componentwise.

    PROVED from the Jordan data (no assumed contraction/absorption
    hypothesis): `t = 1` dispatches to the diagonal argument, `t ≥ 2` to the
    δ-scaling construction with the `t^t ≤ 4t(t−1)^(t−1)` (i.e.
    `(1+1/m)^m < e < 4`) optimisation, reusing `higham_scaling_margin`. -/
theorem complex_jordan_similarity_absorbs (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1)
    (η : ℝ) (hη : 0 ≤ η)
    (hcond : 4 * (t : ℝ) * η *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    ∃ S S_inv : CMatrix n n, ∃ q : ℝ,
      IsComplexMatrixRightInverse S S_inv ∧ 0 ≤ q ∧ q < 1 ∧
      (∀ ΔA : Fin n → Fin n → ℝ,
        (∀ i j, |ΔA i j| ≤ η * |A i j|) →
        complexMatrixInfNorm (complexMatrixMul S_inv (complexMatrixMul
          (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) S)) ≤ q) := by
  rcases Nat.lt_or_ge t 2 with ht | ht2
  · -- t = 1: the run bound forces J diagonal; S = X directly.
    have ht1' : t = 1 := by omega
    subst ht1'
    have hdiag : ∀ i j : Fin n, i ≠ j → J i j = 0 := by
      intro i j hij
      by_cases hj : (j : ℕ) = (i : ℕ) + 1
      · by_contra hJ
        have hlt : (i : ℕ) + 1 < n := by
          have hjn := j.isLt
          omega
        have hieq : (⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩ : Fin n) = i :=
          Fin.eq_of_val_eq rfl
        have hjeq : (⟨(i : ℕ) + 1, hlt⟩ : Fin n) = j :=
          Fin.eq_of_val_eq hj.symm
        have hJ' : J ⟨(i : ℕ), Nat.lt_of_succ_lt hlt⟩
            ⟨(i : ℕ) + 1, hlt⟩ ≠ 0 := by
          rw [hieq, hjeq]
          exact hJ
        have hstep := cJordanRunLength_succ n J (i : ℕ) hlt hJ'
        have hbound := hrun ((i : ℕ) + 1)
        omega
      · apply hshape i j _ hj
        exact fun h => hij (Fin.eq_of_val_eq h.symm)
    set K : ℝ := η * (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) *
      infNorm A with hK
    have hK0 : 0 ≤ K := by
      rw [hK]
      exact mul_nonneg (mul_nonneg hη
        (mul_nonneg (complexMatrixInfNorm_nonneg X)
          (complexMatrixInfNorm_nonneg X_inv)))
        (infNorm_nonneg A)
    have hcond' : 4 * K < 1 - ρ := by
      have h := hcond
      rw [pow_one, Nat.cast_one] at h
      have hre : 4 * (1 : ℝ) * η *
          (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
          = 4 * K := by
        rw [hK]; ring
      rw [hre] at h
      exact h
    have hKlt : K < 1 - ρ := by linarith
    refine ⟨X, X_inv, ρ + K, hXr, by linarith, by linarith, ?_⟩
    intro ΔA hΔ
    -- X⁻¹(Â+ΔÂ)X = J + X⁻¹ΔÂX, entrywise.
    have hofReal : (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
        = (fun i j => ((A i j : ℝ) : ℂ) + ((ΔA i j : ℝ) : ℂ)) := by
      funext i j
      exact Complex.ofReal_add _ _
    have hsplit : complexMatrixMul X_inv (complexMatrixMul
          (fun i j => ((A i j + ΔA i j : ℝ) : ℂ)) X)
        = fun i j => J i j + complexMatrixMul X_inv (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ)) X) i j := by
      rw [hofReal, complexMatrixMul_add_left, complexMatrixMul_add_right,
        hsim]
    rw [hsplit]
    have hΔn : complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) ≤
        η * infNorm A :=
      complexMatrixInfNorm_ofReal_le_mul ΔA A hη hΔ
    have hE : complexMatrixInfNorm (complexMatrixMul X_inv (complexMatrixMul
          (fun i j => ((ΔA i j : ℝ) : ℂ)) X)) ≤ K := by
      calc complexMatrixInfNorm (complexMatrixMul X_inv (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ)) X))
          ≤ complexMatrixInfNorm X_inv * complexMatrixInfNorm
              (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ)) X) :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ complexMatrixInfNorm X_inv *
              (complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) *
                complexMatrixInfNorm X) :=
            mul_le_mul_of_nonneg_left (complexMatrixInfNorm_mul_le _ _)
              (complexMatrixInfNorm_nonneg X_inv)
        _ ≤ complexMatrixInfNorm X_inv *
              ((η * infNorm A) * complexMatrixInfNorm X) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hΔn (complexMatrixInfNorm_nonneg X))
              (complexMatrixInfNorm_nonneg X_inv)
        _ = K := by rw [hK]; ring
    calc complexMatrixInfNorm (fun i j => J i j +
          complexMatrixMul X_inv (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ)) X) i j)
        ≤ complexMatrixInfNorm J + complexMatrixInfNorm
            (complexMatrixMul X_inv (complexMatrixMul
              (fun i j => ((ΔA i j : ℝ) : ℂ)) X)) :=
          complexMatrixInfNorm_add_le _ _
      _ ≤ ρ + K := add_le_add
          (complexMatrixInfNorm_diagonal_le J hρ0 hdiag hdiagbd) hE
  · -- t ≥ 2: δ-scaling construction S = X·D, D = diag(p).
    have hβpos : 0 < jordanBeta ρ t := jordanBeta_pos ρ t hρ1 ht2
    have hβlt : jordanBeta ρ t < 1 := jordanBeta_lt_one ρ t hρ0 ht2
    obtain ⟨p, hp0, hp1, hp2, hpstep⟩ :=
      exists_cJordan_scaling_vector n J t (jordanBeta ρ t) hβpos hβlt.le hrun
    have hβt : 0 < jordanBeta ρ t ^ (t - 1) := pow_pos hβpos _
    set K : ℝ := η * (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) *
      infNorm A with hKdef
    have hK0 : 0 ≤ K := by
      rw [hKdef]
      exact mul_nonneg (mul_nonneg hη
        (mul_nonneg (complexMatrixInfNorm_nonneg X)
          (complexMatrixInfNorm_nonneg X_inv)))
        (infNorm_nonneg A)
    have hcond' : 4 * (t : ℝ) * K < (1 - ρ) ^ t := by
      have hre : 4 * (t : ℝ) * K
          = 4 * (t : ℝ) * η *
            (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) *
            infNorm A := by
        rw [hKdef]; ring
      rw [hre]
      exact hcond
    have hKlt : K < (1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1) :=
      higham_scaling_margin t ht2 ρ K hρ1 hK0 hcond'
    -- The right-inverse pair S = X·D, S⁻¹ = D⁻¹·X⁻¹ (vector action).
    have hSr : IsComplexMatrixRightInverse
        (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))
        (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
          X_inv) := by
      intro x
      rw [complexMatrixVecMul_mul, complexMatrixVecMul_mul]
      have hDD : complexMatrixVecMul (cDiagMatrix fun a => ((p a : ℝ) : ℂ))
          (complexMatrixVecMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixVecMul X_inv x)) = complexMatrixVecMul X_inv x := by
        rw [cDiagMatrix_vecMul, cDiagMatrix_vecMul]
        funext i
        show ((p i : ℝ) : ℂ) * ((((p i)⁻¹ : ℝ) : ℂ) *
          complexMatrixVecMul X_inv x i) = complexMatrixVecMul X_inv x i
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (hp0 i).ne',
          Complex.ofReal_one, one_mul]
      rw [hDD]
      exact hXr x
    -- Norm bounds for D and D⁻¹.
    have hDn : complexMatrixInfNorm
        (cDiagMatrix fun a => ((p a : ℝ) : ℂ)) ≤ 1 :=
      complexMatrixInfNorm_cDiagMatrix_le _ zero_le_one (fun a => by
        show ‖((p a : ℝ) : ℂ)‖ ≤ 1
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hp0 a)]
        exact hp2 a)
    have hDin : complexMatrixInfNorm
        (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ :=
      complexMatrixInfNorm_cDiagMatrix_le _ (inv_nonneg.mpr hβt.le)
        (fun a => by
          show ‖(((p a)⁻¹ : ℝ) : ℂ)‖ ≤ (jordanBeta ρ t ^ (t - 1))⁻¹
          rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr (hp0 a))]
          exact inv_anti₀ hβt (hp1 a))
    -- The scaled Jordan contraction.
    have hJconj : complexMatrixInfNorm (complexMatrixMul
          (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
          (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        ≤ ρ + jordanBeta ρ t :=
      complexMatrixInfNorm_cJordan_conj_le n J p ρ (jordanBeta ρ t) hρ0
        hβpos.le hshape hdiagbd hsup hp0 hpstep
    -- The Jordan part of the conjugated similarity: S⁻¹ Â S = D⁻¹ J D.
    have hterm1 : complexMatrixMul
          (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          (complexMatrixMul (fun i j => ((A i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        = complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) := by
      rw [complexMatrixMul_assoc
            (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv
            (complexMatrixMul (fun i j => ((A i j : ℝ) : ℂ))
              (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))),
          ← complexMatrixMul_assoc (fun i j => ((A i j : ℝ) : ℂ)) X
            (cDiagMatrix fun a => ((p a : ℝ) : ℂ)),
          ← complexMatrixMul_assoc X_inv
            (complexMatrixMul (fun i j => ((A i j : ℝ) : ℂ)) X)
            (cDiagMatrix fun a => ((p a : ℝ) : ℂ)),
          hsim]
    -- q = (ρ + β) + β^(1−t)·K, with 0 ≤ q < 1.
    have hq0 : 0 ≤ ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
      have h1 : 0 ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * K :=
        mul_nonneg (inv_nonneg.mpr hβt.le) hK0
      linarith [hβpos.le]
    have hq1 : ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K < 1 := by
      have hsum1 : ρ + jordanBeta ρ t = 1 - (1 - ρ) / (t : ℝ) :=
        jordanBeta_add_eq ρ t ht2
      have hlt2 : (jordanBeta ρ t ^ (t - 1))⁻¹ * K
          < (jordanBeta ρ t ^ (t - 1))⁻¹ *
            ((1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1)) :=
        mul_lt_mul_of_pos_left hKlt (inv_pos.mpr hβt)
      have heq3 : (jordanBeta ρ t ^ (t - 1))⁻¹ *
            ((1 - ρ) / (t : ℝ) * jordanBeta ρ t ^ (t - 1))
          = (1 - ρ) / (t : ℝ) := by
        rw [mul_comm ((1 - ρ) / (t : ℝ)) (jordanBeta ρ t ^ (t - 1)),
          ← mul_assoc, inv_mul_cancel₀ hβt.ne', one_mul]
      rw [heq3] at hlt2
      rw [hsum1]
      linarith
    refine ⟨complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)),
      complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv,
      ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K,
      hSr, hq0, hq1, ?_⟩
    intro ΔA hΔ
    -- S⁻¹(Â+ΔÂ)S = D⁻¹JD + S⁻¹·ΔÂ·S, entrywise.
    have hofReal : (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
        = (fun i j => ((A i j : ℝ) : ℂ) + ((ΔA i j : ℝ) : ℂ)) := by
      funext i j
      exact Complex.ofReal_add _ _
    have hsplit : complexMatrixMul
          (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          (complexMatrixMul (fun i j => ((A i j + ΔA i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        = fun i j =>
            complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              (complexMatrixMul J
                (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) i j +
            complexMatrixMul
              (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
                X_inv)
              (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
                (complexMatrixMul X
                  (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) i j := by
      rw [hofReal, complexMatrixMul_add_left, complexMatrixMul_add_right,
        hterm1]
    rw [hsplit]
    -- ‖S⁻¹·ΔÂ·S‖∞ ≤ β^(1−t)·η·κ∞(X)·‖A‖∞ = β^(1−t)·K.
    have hΔn : complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) ≤
        η * infNorm A :=
      complexMatrixInfNorm_ofReal_le_mul ΔA A hη hΔ
    have hXD : complexMatrixInfNorm (complexMatrixMul X
          (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))
        ≤ complexMatrixInfNorm X := by
      calc complexMatrixInfNorm (complexMatrixMul X
            (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))
          ≤ complexMatrixInfNorm X * complexMatrixInfNorm
              (cDiagMatrix fun a => ((p a : ℝ) : ℂ)) :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ complexMatrixInfNorm X * 1 :=
            mul_le_mul_of_nonneg_left hDn (complexMatrixInfNorm_nonneg X)
        _ = complexMatrixInfNorm X := mul_one _
    have hDX : complexMatrixInfNorm (complexMatrixMul
          (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv := by
      calc complexMatrixInfNorm (complexMatrixMul
            (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          ≤ complexMatrixInfNorm
              (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) *
            complexMatrixInfNorm X_inv :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv :=
            mul_le_mul_of_nonneg_right hDin
              (complexMatrixInfNorm_nonneg X_inv)
    have hMid : complexMatrixInfNorm (complexMatrixMul
          (fun i j => ((ΔA i j : ℝ) : ℂ))
          (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
        ≤ η * infNorm A * complexMatrixInfNorm X := by
      calc complexMatrixInfNorm (complexMatrixMul
            (fun i j => ((ΔA i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))
          ≤ complexMatrixInfNorm (fun i j => ((ΔA i j : ℝ) : ℂ)) *
            complexMatrixInfNorm (complexMatrixMul X
              (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) :=
            complexMatrixInfNorm_mul_le _ _
        _ ≤ η * infNorm A * complexMatrixInfNorm X :=
            mul_le_mul hΔn hXD (complexMatrixInfNorm_nonneg _)
              (mul_nonneg hη (infNorm_nonneg A))
    have hE : complexMatrixInfNorm (complexMatrixMul
          (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv)
          (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
            (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))))
        ≤ (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
      have h1 : complexMatrixInfNorm (complexMatrixMul
            (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              X_inv)
            (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
              (complexMatrixMul X (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))))
          ≤ ((jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv) *
            (η * infNorm A * complexMatrixInfNorm X) := by
        calc complexMatrixInfNorm (complexMatrixMul
              (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
                X_inv)
              (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
                (complexMatrixMul X
                  (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))))
            ≤ complexMatrixInfNorm (complexMatrixMul
                (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ)) X_inv) *
              complexMatrixInfNorm (complexMatrixMul
                (fun i j => ((ΔA i j : ℝ) : ℂ))
                (complexMatrixMul X
                  (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) :=
              complexMatrixInfNorm_mul_le _ _
          _ ≤ ((jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv) *
              (η * infNorm A * complexMatrixInfNorm X) :=
              mul_le_mul hDX hMid (complexMatrixInfNorm_nonneg _)
                (mul_nonneg (inv_nonneg.mpr hβt.le)
                  (complexMatrixInfNorm_nonneg X_inv))
      have h2 : ((jordanBeta ρ t ^ (t - 1))⁻¹ * complexMatrixInfNorm X_inv) *
            (η * infNorm A * complexMatrixInfNorm X)
          = (jordanBeta ρ t ^ (t - 1))⁻¹ * K := by
        rw [hKdef]; ring
      rw [h2] at h1
      exact h1
    calc complexMatrixInfNorm (fun i j =>
          complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ))) i j +
          complexMatrixMul
            (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              X_inv)
            (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
              (complexMatrixMul X
                (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) i j)
        ≤ complexMatrixInfNorm (complexMatrixMul
            (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
            (complexMatrixMul J (cDiagMatrix fun a => ((p a : ℝ) : ℂ)))) +
          complexMatrixInfNorm (complexMatrixMul
            (complexMatrixMul (cDiagMatrix fun a => (((p a)⁻¹ : ℝ) : ℂ))
              X_inv)
            (complexMatrixMul (fun i j => ((ΔA i j : ℝ) : ℂ))
              (complexMatrixMul X
                (cDiagMatrix fun a => ((p a : ℝ) : ℂ))))) :=
          complexMatrixInfNorm_add_le _ _
      _ ≤ ρ + jordanBeta ρ t + (jordanBeta ρ t ^ (t - 1))⁻¹ * K :=
          add_le_add hJconj hE

-- ============================================================
-- Theorem 18.1: axiom-free end-to-end forms (complex Jordan data)
-- ============================================================

/-- **Theorem 18.1 (Higham–Knight), complex Jordan data, limit form,
    abstract error model** — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    Let `A` be a REAL `n×n` matrix (the computed iteration is a
    floating-point object, hence real, matching the book's setting) with
    COMPLEX Jordan-form similarity data: `X·X⁻¹ = I` over ℂ (as the vector
    action `IsComplexMatrixRightInverse`), `X⁻¹ Â X = J` for the real-cast
    `Â i j = ((A i j : ℝ) : ℂ)`, `J` upper bidiagonal with `‖J_{ii}‖ ≤ ρ < 1`,
    superdiagonal moduli ≤ 1, all other entries zero, and every run of
    consecutive nonzero superdiagonal entries of length ≤ `t − 1`
    (max Jordan block size ≤ `t`, via `cJordanRunLength`); all `1 ≤ t`.
    Under the Higham–Knight condition (18.13)

      `4t·c·κ∞(X)·‖A‖∞ < (1−ρ)^t`,
      `κ∞(X) := complexMatrixInfNorm X * complexMatrixInfNorm X_inv`,

    every real computed-power sequence `v` with per-step componentwise
    budget `c` (`ComputedMatPowVec`, eqs (18.10)–(18.11)) satisfies
    `‖v_m‖∞ → 0`.

    Scope: complex Jordan data as hypothesis (every complex matrix has one;
    JNF existence itself is not formalized — Mathlib lacks it); this is the
    full generality of the printed statement for a real input matrix `A`.
    No assumed contraction/absorption hypothesis: the absorbing similarity
    is PROVED from the Jordan data (`complex_jordan_similarity_absorbs`,
    δ-scaling construction with the `(1+1/m)^m < e < 4` optimisation). -/
theorem higham_18_1_complex_jordan_tendsto (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1)
    (v : ℕ → (Fin n → ℝ)) (c : ℝ) (hc : 0 ≤ c)
    (hComp : ComputedMatPowVec n A v c)
    (hCond : 4 * (t : ℝ) * c *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    Filter.Tendsto (fun m => infNormVec (v m)) Filter.atTop (nhds 0) := by
  obtain ⟨S, S_inv, q, hSr, hq0, hq1, hAbsorb⟩ :=
    complex_jordan_similarity_absorbs n A X X_inv J hXr hsim hshape
      ρ hρ0 hρ1 hdiagbd hsup t ht1 hrun c hc hCond
  have hbound : ∀ m, infNormVec (v m) ≤
      complexMatrixInfNorm S * complexMatrixInfNorm S_inv * q ^ m *
        infNormVec (v 0) :=
    fun m => complex_similarity_normwise_bound n A S S_inv hSr v c hComp
      q hq0 hAbsorb m
  exact computedMatPow_tendsto_zero_of_geometric n v
    (complexMatrixInfNorm S * complexMatrixInfNorm S_inv) q hq0 hq1 hbound

/-- **Theorem 18.1 (Higham–Knight), complex Jordan data, for the actual
    floating-point iteration** — Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, Theorem 18.1 (pp. 347–348).

    With complex Jordan data for the real matrix `A` as in
    `higham_18_1_complex_jordan_tendsto` and the printed condition (18.13)
    with the book's constant `γ_{n+2}`,

      `4t·γ_{n+2}·κ∞(X)·‖A‖∞ < (1−ρ)^t`,

    the computed vectors `fl(Aᵐ v₀)` (repeated `fl_matVec`) satisfy
    `‖fl(Aᵐ v₀)‖∞ → 0`.  Fully end-to-end: concrete algorithm, concrete
    rounding model, no assumed construction.

    Scope: complex Jordan data as hypothesis (every complex matrix has one;
    JNF existence itself is not formalized — Mathlib lacks it); this is the
    full generality of the printed statement for a real input matrix `A`. -/
theorem higham_18_1_complex_jordan_fl_tendsto (fp : FPModel) (n : ℕ)
    (A : Fin n → Fin n → ℝ) (X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hsim : complexMatrixMul X_inv (complexMatrixMul
      (fun i j => ((A i j : ℝ) : ℂ)) X) = J)
    (hshape : ∀ i j : Fin n, (j : ℕ) ≠ (i : ℕ) → (j : ℕ) ≠ (i : ℕ) + 1 →
      J i j = 0)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hdiagbd : ∀ i, ‖J i i‖ ≤ ρ)
    (hsup : ∀ i j : Fin n, (j : ℕ) = (i : ℕ) + 1 → ‖J i j‖ ≤ 1)
    (t : ℕ) (ht1 : 1 ≤ t)
    (hrun : ∀ k, cJordanRunLength n J k ≤ t - 1)
    (v0 : Fin n → ℝ) (hval : gammaValid fp (n + 2))
    (hCond : 4 * (t : ℝ) * gamma fp (n + 2) *
      (complexMatrixInfNorm X * complexMatrixInfNorm X_inv) * infNorm A
      < (1 - ρ) ^ t) :
    Filter.Tendsto
      (fun m => infNormVec (fl_matPowVecSeq fp n A v0 m))
      Filter.atTop (nhds 0) :=
  higham_18_1_complex_jordan_tendsto n A X X_inv J hXr hsim hshape
    ρ hρ0 hρ1 hdiagbd hsup t ht1 hrun (fl_matPowVecSeq fp n A v0)
    (gamma fp (n + 2)) (gamma_nonneg fp hval)
    (computedMatPowVec_fl_matVec_gamma_add_two fp n A v0 hval) hCond

end NumStability
