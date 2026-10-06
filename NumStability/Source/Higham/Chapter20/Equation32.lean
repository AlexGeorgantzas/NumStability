import NumStability.Algorithms.LeastSquares.LSQRSolve

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

/-!
# Higham Chapter 20, Equation 20.32

Canonical source-correspondence module for the exact cross-projection residual identity.
-/

/-- Higham, 2nd ed., Chapter 20, equation (20.32):
    `B⁺ r = B⁺ P_B (I - P_A) r`.

Here `P_A = A A⁺` and `P_B = B B⁺`.  The identity only needs the
left-inverse relation for `B⁺` and the source-residual relation `P_A r = 0`;
the symmetry and norm hypotheses used in the following estimate (20.33) are
not needed for this exact algebraic proof line. -/
theorem higham20_eq20_32_Bplus_residual_eq_crossProjection
    {m k : ℕ} (A B : Fin m → Fin (k + 1) → ℝ)
    (Aplus Bplus : Fin (k + 1) → Fin m → ℝ)
    (r : Fin m → ℝ)
    (hleftB : rectMatMul Bplus B = idMatrix (k + 1))
    (hrangeA_residual : rectMatMulVec (rectMatMul A Aplus) r = 0) :
    rectMatMulVec Bplus r =
      rectMatMulVec Bplus
        (rectMatMulVec
          (rectMatMul (rectMatMul B Bplus)
            (fun i j => idMatrix m i j - rectMatMul A Aplus i j)) r) := by
  let PA : Fin m → Fin m → ℝ := rectMatMul A Aplus
  let PB : Fin m → Fin m → ℝ := rectMatMul B Bplus
  let IPA : Fin m → Fin m → ℝ := fun i j => idMatrix m i j - PA i j
  have hBplusPB : rectMatMul Bplus PB = Bplus := by
    calc
      rectMatMul Bplus PB = rectMatMul Bplus (rectMatMul B Bplus) := by
        rfl
      _ = rectMatMul (rectMatMul Bplus B) Bplus := by
        rw [rectMatMul_assoc]
      _ = rectMatMul (idMatrix (k + 1)) Bplus := by
        rw [hleftB]
      _ = Bplus := rectMatMul_id_left Bplus
  have hIPA_r : rectMatMulVec IPA r = r := by
    rw [show IPA =
        (fun i j => idMatrix m i j - rectMatMul A Aplus i j) by
      ext i j
      rfl]
    rw [wedinLemma20_12_rectMatMulVec_projectionComplement]
    rw [hrangeA_residual]
    ext i
    simp
  change rectMatMulVec Bplus r =
    rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
  symm
  calc
    rectMatMulVec Bplus (rectMatMulVec (rectMatMul PB IPA) r)
        = rectMatMulVec Bplus
            (rectMatMulVec PB (rectMatMulVec IPA r)) := by
            rw [rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus (rectMatMulVec PB r) := by
            rw [hIPA_r]
    _ = rectMatMulVec (rectMatMul Bplus PB) r := by
            rw [← rectMatMulVec_rectMatMul]
    _ = rectMatMulVec Bplus r := by
            rw [hBplusPB]

end NumStability
