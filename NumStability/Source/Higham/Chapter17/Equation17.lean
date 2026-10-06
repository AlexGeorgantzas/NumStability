import NumStability.Algorithms.StationaryIteration
import NumStability.Source.Higham.Chapter17.Equation12

/-!
# Higham Chapter 17, Equation 17.17

Canonical source-correspondence owner for the literal SOR forward-error bound and its Gauss--Seidel specialization from the prose immediately following Equation 17.17.
-/

namespace NumStability

open scoped BigOperators

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- **Literal uniform-in-m SOR forward bound** (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.2, eq (17.17)): the SOR
    specialization with multiplier `f(ω) = (1 + |1 - ω|)/ω` of the norm-form
    forward bound with the literal constant `c(A)`, valid for all horizons
    `m` simultaneously. -/
theorem literal_norm_form_sor_forward_bound (n : ℕ)
    (A G M_inv A_inv D L U M_sor N_sor : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (ω cn_u θ_x : ℝ) (hω_pos : 0 < ω) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_sor i j = (1 / ω) * (D i j + ω * L i j))
    (hN : ∀ i j, N_sor i j = (1 / ω) * ((1 - ω) * D i j - ω * U i j))
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M_sor N_sor x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          (sorForwardFactor ω *
            infNormVec (jacobiForwardBoundVector n A_inv A x)) :=
  finite_norm_form_sor_forward_bound n A G M_inv A_inv D L U M_sor N_sor e₀ x
    ω cn_u θ_x (cALiteral n G M_inv A_inv) hω_pos hcn
    (cALiteral_nonneg n G M_inv A_inv hne) hθ hDecomp hD hL hU hM hN m
    (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

/-- **Literal uniform-in-m Gauss-Seidel forward bound** (Higham, Accuracy
    and Stability of Numerical Algorithms, 2nd ed., §17.2.2, following
    eq (17.17): Gauss-Seidel is SOR with `ω = 1`, so `f(1) = 1`): the
    Gauss-Seidel specialization of the norm-form forward bound with the
    literal constant `c(A)`, valid for all horizons `m` simultaneously. -/
theorem literal_norm_form_gaussSeidel_forward_bound (n : ℕ)
    (A G M_inv A_inv D L U M_gs N_gs : Fin n → Fin n → ℝ) (e₀ x : Fin n → ℝ)
    (cn_u θ_x : ℝ) (hcn : 0 ≤ cn_u) (hθ : 0 ≤ θ_x)
    (hDecomp : ∀ i j, A i j = D i j + L i j + U i j)
    (hD : ∀ i j, i ≠ j → D i j = 0)
    (hL : ∀ i j, j.val ≥ i.val → L i j = 0)
    (hU : ∀ i j, j.val ≤ i.val → U i j = 0)
    (hM : ∀ i j, M_gs i j = D i j + L i j)
    (hN : ∀ i j, N_gs i j = -U i j)
    (hsum : ∀ i j, Summable
      (fun k => ∑ l : Fin n, |matPow n G k i l| * |M_inv l j|))
    (hne : (CAValues n G M_inv A_inv).Nonempty) (m : ℕ) :
    infNormVec (fun i =>
      matMulVec n (matPow n G (m + 1)) e₀ i +
        finiteForwardCorrection n G M_inv M_gs N_gs x cn_u θ_x m i) ≤
      infNormVec (matMulVec n (matPow n G (m + 1)) e₀) +
        cn_u * (1 + θ_x) * cALiteral n G M_inv A_inv *
          infNormVec (jacobiForwardBoundVector n A_inv A x) :=
  finite_norm_form_gaussSeidel_forward_bound n A G M_inv A_inv D L U M_gs N_gs
    e₀ x cn_u θ_x (cALiteral n G M_inv A_inv) hcn
    (cALiteral_nonneg n G M_inv A_inv hne) hθ hDecomp hD hL hU hM hN m
    (partialSumBound_cALiteral n G M_inv A_inv hsum hne m)

end NumStability
