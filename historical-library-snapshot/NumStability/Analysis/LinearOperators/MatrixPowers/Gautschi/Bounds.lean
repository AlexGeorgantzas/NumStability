import NumStability.Analysis.LinearOperators.MatrixPowers.JordanScaling.RealJordan
import NumStability.Analysis.MatrixNorms.Comparisons

/-!
# Analysis.LinearOperators.MatrixPowers.Gautschi.Bounds

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

-- Analysis/MatrixPowersGautschi.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, equation (18.6): Gautschi's polynomial-geometric bound.





namespace NumStability

/-- Scalar optimization behind Gautschi's bound.  Choosing the Jordan scaling
margin `beta = rho/k` converts the shifted geometric estimate into a
`k^s * rho^k` estimate, with the harmless explicit constant `4/rho^s`.

The positive-radius hypothesis is essential.  The printed definition of the
largest block belonging to a nonzero eigenvalue is empty for a nilpotent
matrix; that case is handled separately below. -/
theorem gautschi_scaled_geometric_le
    (rho : Real) (s k : Nat) (hrho : 0 < rho) (hk : 1 <= k) :
    (((rho / (k : Real)) ^ s)⁻¹) *
        (rho + rho / (k : Real)) ^ k <=
      4 * (rho ^ s)⁻¹ * (k : Real) ^ s * rho ^ k := by
  have hkR : (0 : Real) < (k : Real) := by exact_mod_cast hk
  have hEuler : (1 + 1 / (k : Real)) ^ k <= 4 :=
    (one_add_one_div_pow_lt_four k hk).le
  have hrho0 : 0 <= rho := hrho.le
  have hks0 : 0 <= (k : Real) ^ s := pow_nonneg hkR.le s
  have hrhos0 : 0 <= (rho ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg hrho0 s)
  have hrhok0 : 0 <= rho ^ k := pow_nonneg hrho0 k
  have hfactor0 :
      0 <= (rho ^ s)⁻¹ * (k : Real) ^ s * rho ^ k := by positivity
  have hscale :
      (((rho / (k : Real)) ^ s)⁻¹) =
        (rho ^ s)⁻¹ * (k : Real) ^ s := by
    rw [div_pow]
    field_simp
  have hshift :
      (rho + rho / (k : Real)) ^ k =
        rho ^ k * (1 + 1 / (k : Real)) ^ k := by
    have hbase : rho + rho / (k : Real) =
        rho * (1 + 1 / (k : Real)) := by ring
    rw [hbase, mul_pow]
  rw [hscale, hshift]
  calc
    ((rho ^ s)⁻¹ * (k : Real) ^ s) *
          (rho ^ k * (1 + 1 / (k : Real)) ^ k)
        = ((rho ^ s)⁻¹ * (k : Real) ^ s * rho ^ k) *
            (1 + 1 / (k : Real)) ^ k := by ring
    _ <= ((rho ^ s)⁻¹ * (k : Real) ^ s * rho ^ k) * 4 :=
      mul_le_mul_of_nonneg_left hEuler hfactor0
    _ = 4 * (rho ^ s)⁻¹ * (k : Real) ^ s * rho ^ k := by ring













































































































end NumStability
