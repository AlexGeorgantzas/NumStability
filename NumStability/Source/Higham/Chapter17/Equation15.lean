import NumStability.Algorithms.StationaryIteration
import NumStability.Source.Higham.Chapter17.Equation12

/-!
# Higham Chapter 17, Equation 17.15

Canonical source-correspondence owner for the literal uniform-in-horizon norm-form forward-error bound obtained from the attained `c(A)` certificate.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Literal uniform-in-m norm-form forward bound** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eqs (17.13)-(17.15)):
    the finite norm-form forward bound holds with the SINGLE literal
    constant `c(A) = cALiteral` for ALL horizons `m` simultaneously, exactly
    as printed — the constant no longer depends on the horizon of the
    certificate.  Obtained by instantiating the finite theorem with
    `partialSumBound_cALiteral`. -/
theorem literal_norm_form_forward_bound (n : ℕ)
    (G M_inv A_inv M N : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M N x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          infNormVec (mainForwardBoundVector n A_inv M N x) :=
  finite_norm_form_forward_bound n G M_inv A_inv M N e₀ x cn_u θ_x
    (cALiteral n G M_inv A_inv) hcn (cALiteral_nonneg n G M_inv A_inv hne)
    hθ m (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

end NumStability
