import NumStability.Analysis.SingularValues.Basic

/-!
# Higham Chapter 6: max-norm inconsistency

Source correspondence for the entrywise max-norm product bound, its all-ones
sharpness witness, and the resulting failure of unscaled consistency.
-/

namespace NumStability

open scoped BigOperators

/-! ### (iii) The max-norm is not consistent -/

/-- **Best consistency bound for the max-norm** (Higham §6.2, p. 108: "The best
    bound that holds for all `A ∈ Cᵐˣⁿ` and `B ∈ Cⁿˣᵖ` is
    `‖AB‖_M ≤ n‖A‖_M‖B‖_M`").  Here `‖A‖_M := maxᵢⱼ|aᵢⱼ|`. -/
theorem ch6aside_maxNorm_mul_le {m n p : ℕ}
    (A : CMatrix m n) (B : CMatrix n p) :
    complexMatrixEntrywiseMaxNorm (complexMatrixMul A B) ≤
      (n : ℝ) * complexMatrixEntrywiseMaxNorm A *
        complexMatrixEntrywiseMaxNorm B := by
  apply complexMatrixEntrywiseMaxNorm_le_of_coord_le
  · exact mul_nonneg
      (mul_nonneg (Nat.cast_nonneg n) (complexMatrixEntrywiseMaxNorm_nonneg A))
      (complexMatrixEntrywiseMaxNorm_nonneg B)
  · intro i j
    have hbound : ‖complexMatrixMul A B i j‖ ≤
        ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := by
      unfold complexMatrixMul
      calc ‖∑ k : Fin n, A i k * B k j‖
          ≤ ∑ k : Fin n, ‖A i k * B k j‖ := norm_sum_le _ _
        _ = ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := by simp
    have hterm : ∀ k : Fin n, ‖A i k‖ * ‖B k j‖ ≤
        complexMatrixEntrywiseMaxNorm A * complexMatrixEntrywiseMaxNorm B := by
      intro k
      exact mul_le_mul (complexMatrixEntrywiseMaxNorm_coord_le A i k)
        (complexMatrixEntrywiseMaxNorm_coord_le B k j) (norm_nonneg _)
        (complexMatrixEntrywiseMaxNorm_nonneg A)
    calc ‖complexMatrixMul A B i j‖
        ≤ ∑ k : Fin n, ‖A i k‖ * ‖B k j‖ := hbound
      _ ≤ ∑ _k : Fin n, complexMatrixEntrywiseMaxNorm A *
            complexMatrixEntrywiseMaxNorm B :=
          Finset.sum_le_sum (fun k _ => hterm k)
      _ = (n : ℝ) * complexMatrixEntrywiseMaxNorm A *
            complexMatrixEntrywiseMaxNorm B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          rw [nsmul_eq_mul]; ring

/-- Max-norm of the all-ones `n × n` matrix `J` is `1` (`n ≥ 1`). -/
theorem ch6aside_maxNorm_allOnes {n : ℕ} (hn : 0 < n) :
    complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (1 : ℂ)) = 1 := by
  refine le_antisymm ?_ ?_
  · exact complexMatrixEntrywiseMaxNorm_le_of_coord_le _ (by norm_num)
      (fun i j => by simp)
  · have := complexMatrixEntrywiseMaxNorm_coord_le
      (fun _ _ : Fin n => (1 : ℂ)) ⟨0, hn⟩ ⟨0, hn⟩
    simpa using this

/-- The all-ones product: `J·J = n·J` (each entry equals `n`). -/
theorem ch6aside_maxNorm_allOnes_mul {n : ℕ} :
    complexMatrixMul (fun _ _ : Fin n => (1 : ℂ)) (fun _ _ : Fin n => (1 : ℂ)) =
      (fun _ _ : Fin n => (n : ℂ)) := by
  funext i j
  simp [complexMatrixMul, Finset.card_univ]

/-- **Equality in the max-norm bound at `A = B = J` (all ones)** (Higham §6.2,
    p. 108: "with equality when `aᵢⱼ ≡ 1` and `bᵢⱼ ≡ 1`"):
    `‖J·J‖_M = n·‖J‖_M·‖J‖_M`. -/
theorem ch6aside_maxNorm_equality_allOnes {n : ℕ} (hn : 0 < n) :
    complexMatrixEntrywiseMaxNorm
        (complexMatrixMul (fun _ _ : Fin n => (1 : ℂ))
          (fun _ _ : Fin n => (1 : ℂ))) =
      (n : ℝ) * complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (1 : ℂ)) *
        complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (1 : ℂ)) := by
  rw [ch6aside_maxNorm_allOnes_mul, ch6aside_maxNorm_allOnes hn]
  have hconst : complexMatrixEntrywiseMaxNorm (fun _ _ : Fin n => (n : ℂ)) =
      (n : ℝ) := by
    refine le_antisymm ?_ ?_
    · exact complexMatrixEntrywiseMaxNorm_le_of_coord_le _ (Nat.cast_nonneg n)
        (fun i j => by simp)
    · have := complexMatrixEntrywiseMaxNorm_coord_le
        (fun _ _ : Fin n => (n : ℂ)) ⟨0, hn⟩ ⟨0, hn⟩
      simpa using this
  rw [hconst]; ring

/-- **The max-norm is not consistent** (Higham §6.2, p. 108: "An example of a
    norm that is not consistent is the max norm").  For `n ≥ 2` there exist
    matrices (`A = B = J`, all ones) with `‖A‖_M·‖B‖_M < ‖AB‖_M`, so
    `‖AB‖_M ≤ ‖A‖_M‖B‖_M` fails. -/
theorem ch6aside_maxNorm_not_consistent {n : ℕ} (hn : 2 ≤ n) :
    ∃ A B : CMatrix n n,
      complexMatrixEntrywiseMaxNorm A * complexMatrixEntrywiseMaxNorm B <
        complexMatrixEntrywiseMaxNorm (complexMatrixMul A B) := by
  have h0 : 0 < n := by omega
  refine ⟨(fun _ _ => 1), (fun _ _ => 1), ?_⟩
  rw [ch6aside_maxNorm_equality_allOnes h0, ch6aside_maxNorm_allOnes h0]
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

end NumStability
