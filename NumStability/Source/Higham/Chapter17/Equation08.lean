import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import NumStability.Algorithms.StationaryIteration

/-!
# Higham Chapter 17, Equation 17.8

Canonical source-correspondence owner for the geometric matrix-power summability and `tsum` bound used in Higham's normwise forward-error series.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eq (17.8): the norms `‖G^k‖∞` of the iteration-matrix powers appearing in
    the infinite error series are summable under the norm certificate
    `‖G‖∞ ≤ q < 1`.  Scope: this is the standard geometric-majorant argument
    `‖G^k‖∞ ≤ ‖G‖∞^k ≤ q^k`; it does not use the weaker spectral condition
    (for that see `summable_infNorm_matPow_of_spectralRadius`). -/
theorem summable_infNorm_matPow (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) :
    Summable (fun k => infNorm (matPow n G k)) :=
  Summable.of_nonneg_of_le (fun _ => infNorm_nonneg _)
    (fun k => (infNorm_matPow_le hn G k).trans
      (pow_le_pow_left₀ (infNorm_nonneg G) hG k))
    (summable_geometric_of_lt_one hq0 hq1)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.2,
    eqs (17.8)/(17.12): the summed norms of the iteration-matrix powers are
    bounded by the geometric series value `(1 - q)⁻¹` under the norm
    certificate `‖G‖∞ ≤ q < 1`. -/
theorem tsum_infNorm_matPow_le (n : ℕ) (hn : 0 < n)
    (G : Fin n → Fin n → ℝ)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hG : infNorm G ≤ q) :
    ∑' k : ℕ, infNorm (matPow n G k) ≤ (1 - q)⁻¹ :=
  calc ∑' k : ℕ, infNorm (matPow n G k)
      ≤ ∑' k : ℕ, q ^ k :=
        Summable.tsum_le_tsum
          (fun k => (infNorm_matPow_le hn G k).trans
            (pow_le_pow_left₀ (infNorm_nonneg G) hG k))
          (summable_infNorm_matPow n hn G q hq0 hq1 hG)
          (summable_geometric_of_lt_one hq0 hq1)
    _ = (1 - q)⁻¹ := tsum_geometric_of_lt_one hq0 hq1

end NumStability
