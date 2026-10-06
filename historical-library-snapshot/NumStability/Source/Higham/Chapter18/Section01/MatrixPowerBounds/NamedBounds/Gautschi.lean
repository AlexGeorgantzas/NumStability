import NumStability.Analysis.LinearOperators.MatrixPowers.Gautschi.Bounds
import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.Complex
import NumStability.Analysis.LinearOperators.MatrixPowers.LpBounds.ComplexDiagonal
import NumStability.Analysis.MatrixNorms.Basic
import NumStability.Analysis.MatrixNorms.Comparisons
import NumStability.Analysis.MatrixNorms.Lp
import NumStability.Analysis.SingularValues.Basic
import NumStability.Source.Higham.Chapter18.Section01.MatrixPowerBounds.Equations04And05.LpJordan

/-!
# Source.Higham.Chapter18.Section01.MatrixPowerBounds.NamedBounds.Gautschi

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Analysis/MatrixPowersGautschi.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, equation (18.6): Gautschi's polynomial-geometric bound.





namespace NumStability











































/-- **Gautschi's matrix-power bound (Higham (18.6)), complex Jordan form.**

Let `A = X J X⁻¹`, where `J` is in upper-bidiagonal Jordan form, its diagonal
entries have modulus at most the positive spectral radius `rho < 1`, and every
run of nonzero superdiagonal entries has length at most `p-1`.  Then, for every
positive power `k`,

`||A^k||_F <= c * k^(p-1) * rho^k`,

with the explicit constant

`c = 4 * sqrt(n) * ||X||_2 * ||X⁻¹||_2 / rho^(p-1)`.

Thus `c` depends only on the fixed matrix/Jordan data and not on `k`, which is
the precise existential content of the book's phrase "a constant depending
only on A".  Taking `p` to be the largest nonzero-eigenvalue Jordan block size
gives the printed equation. -/
theorem higham18_eq18_6_gautschi_complexJordan
    (n : Nat) (hn : 0 < n)
    (A X X_inv J : CMatrix n n)
    (hXr : IsComplexMatrixRightInverse X X_inv)
    (hXl : IsComplexMatrixRightInverse X_inv X)
    (hsim : complexMatrixMul X_inv (complexMatrixMul A X) = J)
    (hshape : forall i j : Fin n,
      (j : Nat) ≠ (i : Nat) -> (j : Nat) ≠ (i : Nat) + 1 -> J i j = 0)
    (rho : Real) (hrho : 0 < rho) (hrho1 : rho < 1)
    (hdiagbd : forall i, ‖J i i‖ <= rho)
    (hsup : forall i j : Fin n,
      (j : Nat) = (i : Nat) + 1 -> ‖J i j‖ <= 1)
    (p : Nat)
    (hrun : forall r, cJordanRunLength n J r <= p - 1)
    (k : Nat) (hk : 1 <= k) :
    complexMatrixFrobenius (cMatPow n A k) <=
      (4 * Real.sqrt (n : Real) *
          (complexMatrixOp2 X * complexMatrixOp2 X_inv) *
          (rho ^ (p - 1))⁻¹) *
        (k : Real) ^ (p - 1) * rho ^ k := by
  let beta : Real := rho / (k : Real)
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hbeta0 : 0 < beta := by
    dsimp [beta]
    exact div_pos hrho hkR
  have hbeta1 : beta <= 1 := by
    dsimp [beta]
    rw [div_le_one hkR]
    have hk_one : (1 : Real) <= (k : Real) := by exact_mod_cast hk
    exact hrho1.le.trans hk_one
  obtain ⟨q, hq0, hqLower, hqUpper, hqStep⟩ :=
    exists_cJordan_scaling_vector n J p beta hbeta0 hbeta1 hrun
  have hop :=
    higham_eq_18_5_alt_lp_jordan n hn A X X_inv J hXr hXl hsim
      hshape rho hrho.le hdiagbd hsup beta hbeta0 (p - 1) q
      hqLower hqUpper hqStep (2 : Real) (by norm_num) k
  rw [complexMatrixLpNormOfReal_two_eq_complexMatrixOp2,
    complexMatrixLpNormOfReal_two_eq_complexMatrixOp2,
    complexMatrixLpNormOfReal_two_eq_complexMatrixOp2] at hop
  have hscalar := gautschi_scaled_geometric_le rho (p - 1) k hrho hk
  have hkappa0 :
      0 <= complexMatrixOp2 X * complexMatrixOp2 X_inv :=
    mul_nonneg (complexMatrixOp2_nonneg X) (complexMatrixOp2_nonneg X_inv)
  have hop' :
      complexMatrixOp2 (cMatPow n A k) <=
        (complexMatrixOp2 X * complexMatrixOp2 X_inv) *
          (4 * (rho ^ (p - 1))⁻¹ *
            (k : Real) ^ (p - 1) * rho ^ k) := by
    dsimp [beta] at hop
    calc
      complexMatrixOp2 (cMatPow n A k) <=
          (complexMatrixOp2 X * complexMatrixOp2 X_inv) *
            ((rho / (k : Real)) ^ (p - 1))⁻¹ *
              (rho + rho / (k : Real)) ^ k := hop
      _ = (complexMatrixOp2 X * complexMatrixOp2 X_inv) *
            ((((rho / (k : Real)) ^ (p - 1))⁻¹) *
              (rho + rho / (k : Real)) ^ k) := by ring
      _ <= (complexMatrixOp2 X * complexMatrixOp2 X_inv) *
            (4 * (rho ^ (p - 1))⁻¹ *
              (k : Real) ^ (p - 1) * rho ^ k) :=
        mul_le_mul_of_nonneg_left hscalar hkappa0
  have hfrob :=
    complexMatrixFrobenius_le_sqrt_card_mul_complexMatrixOp2
      (cMatPow n A k)
  calc
    complexMatrixFrobenius (cMatPow n A k)
        <= Real.sqrt (n : Real) * complexMatrixOp2 (cMatPow n A k) := hfrob
    _ <= Real.sqrt (n : Real) *
          ((complexMatrixOp2 X * complexMatrixOp2 X_inv) *
            (4 * (rho ^ (p - 1))⁻¹ *
              (k : Real) ^ (p - 1) * rho ^ k)) :=
      mul_le_mul_of_nonneg_left hop' (Real.sqrt_nonneg _)
    _ = (4 * Real.sqrt (n : Real) *
          (complexMatrixOp2 X * complexMatrixOp2 X_inv) *
          (rho ^ (p - 1))⁻¹) *
        (k : Real) ^ (p - 1) * rho ^ k := by ring

/-- Nilpotent correction to the literal wording surrounding Higham (18.6).
When the set of nonzero-eigenvalue Jordan blocks is empty, the displayed
`rho^k` right-hand side is identically zero and cannot bound the initial
nonzero powers.  The correct statement is eventual extinction. -/
theorem higham18_eq18_6_nilpotent_eventual_correction
    {n : Nat} (A : Matrix (Fin n) (Fin n) Complex)
    (hA : IsNilpotent A) :
    ∃ K : Nat, ∀ k : Nat, K <= k -> A ^ k = 0 := by
  rcases hA with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  intro k hk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [pow_add, hK, zero_mul]

end NumStability
