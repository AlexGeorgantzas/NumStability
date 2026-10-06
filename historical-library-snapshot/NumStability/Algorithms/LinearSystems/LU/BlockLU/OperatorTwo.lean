import NumStability.Analysis.MatrixAlgebra

/-!
  Algorithms/LinearSystems/LU/BlockLU/OperatorTwo.lean

  Reusable Euclidean operator-norm entry and lower-norm bounds for block LU.
-/

namespace NumStability

/-- Every matrix entry is bounded by the exact Euclidean operator norm. -/
theorem higham13_abs_entry_le_opNorm2 {r : ℕ}
    (B : Fin r → Fin r → ℝ) (s t : Fin r) :
    |B s t| ≤ opNorm2 B := by
  have hcert := opNorm2Le_opNorm2 B
  have hcol := hcert (finiteBasisVec t)
  have hbasis : vecNorm2 (finiteBasisVec t : Fin r → ℝ) = 1 :=
    vecNorm2_finiteBasisVec t
  have hmatvec : matMulVec r B (finiteBasisVec t) = fun i => B i t := by
    simpa [matMulVec, finiteMatVec] using finiteMatVec_finiteBasisVec B t
  have hcolnorm : vecNorm2 (fun i => B i t) ≤ opNorm2 B := by
    simpa [hmatvec, hbasis] using hcol
  exact (abs_coord_le_vecNorm2 (fun i => B i t) s).trans hcolnorm

/-- Zero Euclidean operator norm forces every entry of a finite matrix to
    vanish. -/
theorem higham13_block_entries_zero_of_opNorm2_eq_zero {r : ℕ}
    (B : Fin r → Fin r → ℝ) (hB : opNorm2 B = 0) :
    ∀ s t : Fin r, B s t = 0 := by
  intro s t
  have habs : |B s t| = 0 :=
    le_antisymm
      (by simpa [hB] using higham13_abs_entry_le_opNorm2 B s t)
      (abs_nonneg _)
  exact abs_eq_zero.mp habs
/-- The attained Euclidean lower norm is bounded by the corresponding
    operator norm. -/
theorem matMulVecLowerNorm2_le_opNorm2 {r : ℕ} (hr : 0 < r)
    (B : Fin r → Fin r → ℝ) :
    matMulVecLowerNorm2 hr B ≤ opNorm2 B := by
  let e : Fin r → ℝ := finiteBasisVec ⟨0, hr⟩
  have he : vecNorm2 e = 1 := by
    simpa [e] using vecNorm2_finiteBasisVec (⟨0, hr⟩ : Fin r)
  calc
    matMulVecLowerNorm2 hr B ≤ vecNorm2 (matMulVec r B e) :=
      matMulVecLowerNorm2_le hr B e he
    _ ≤ opNorm2 B * vecNorm2 e := opNorm2Le_opNorm2 B e
    _ = opNorm2 B := by rw [he, mul_one]

end NumStability
