import NumStability.Algorithms.StationaryIteration
import NumStability.Source.Higham.Chapter17.Equation12

/-!
# Higham Chapter 17, Equation 17.16

Canonical source-correspondence owner for the literal Jacobi specialization of the stationary-iteration forward-error bound.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Literal uniform-in-m Jacobi forward bound** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eq (17.16)): the
    Jacobi specialization `|M| + |N| = |A|` of the norm-form forward bound
    with the literal constant `c(A)`, valid for all horizons `m`
    simultaneously. -/
theorem literal_norm_form_jacobi_forward_bound (n : ℕ)
    (A G M_inv A_inv M N : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hM : ∀ i j, M i j = if i = j then A i i else 0)
    (hN : ∀ i j, N i j = M i j - A i j)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M N x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          infNormVec (jacobiForwardBoundVector n A_inv A x) :=
  finite_norm_form_jacobi_forward_bound n A G M_inv A_inv M N e₀ x cn_u θ_x
    (cALiteral n G M_inv A_inv) hcn (cALiteral_nonneg n G M_inv A_inv hne)
    hθ hM hN m (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

end NumStability
