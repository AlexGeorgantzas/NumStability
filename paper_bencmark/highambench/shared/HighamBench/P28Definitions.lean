import Mathlib

namespace HighamBench

open scoped BigOperators Matrix.Norms.Frobenius

/-! Definitions for the Newton--Schulz error calculation in Section 6.3. -/

structure P28FPModel where
  u : ℝ
  u_nonneg : 0 ≤ u
  fl_add : ℝ → ℝ → ℝ
  fl_mul : ℝ → ℝ → ℝ
  fl_add_zero : ∀ x : ℝ, fl_add 0 x = x
  model_add : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_add x y = (x + y) * (1 + δ)
  model_mul : ∀ x y : ℝ, ∃ δ : ℝ,
    |δ| ≤ u ∧ fl_mul x y = (x * y) * (1 + δ)

abbrev P28RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

noncomputable def p28MatMul {n : ℕ}
    (A B : P28RealMatrix n) : P28RealMatrix n :=
  fun i j ↦ ∑ k : Fin n, A i k * B k j

noncomputable def p28Transpose {n : ℕ}
    (A : P28RealMatrix n) : P28RealMatrix n :=
  fun i j ↦ A j i

noncomputable def p28Gamma (u : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) * u) / (1 - (k : ℝ) * u)

def P28GammaValid (u : ℝ) (k : ℕ) : Prop :=
  (k : ℝ) * u < 1

noncomputable def p28RoundedDotProduct (fp : P28FPModel) (n : ℕ)
    (x y : Fin n → ℝ) : ℝ :=
  match n with
  | 0 => 0
  | n' + 1 =>
      Fin.foldl n'
        (fun acc i ↦ fp.fl_add acc (fp.fl_mul (x i.succ) (y i.succ)))
        (fp.fl_mul (x 0) (y 0))

noncomputable def p28RoundedMatMul (fp : P28FPModel) {n : ℕ}
    (A B : P28RealMatrix n) : P28RealMatrix n :=
  fun i j ↦ p28RoundedDotProduct fp n (A i) (fun k ↦ B k j)

/-- The two rounded products used to form `XXᵀX` in equation (6.6). -/
noncomputable def p28RoundedGramTriple (fp : P28FPModel) {n : ℕ}
    (X : P28RealMatrix n) : P28RealMatrix n :=
  p28RoundedMatMul fp (p28RoundedMatMul fp X (p28Transpose X)) X

noncomputable def p28ExactGramTriple {n : ℕ}
    (X : P28RealMatrix n) : P28RealMatrix n :=
  p28MatMul (p28MatMul X (p28Transpose X)) X

/-- The componentwise majorant for the forward error `ε₁` in equation (6.6). -/
noncomputable def p28GramTripleErrorMajorant (fp : P28FPModel) {n : ℕ}
    (X : P28RealMatrix n) (i j : Fin n) : ℝ :=
  p28Gamma fp.u n *
      (∑ k : Fin n,
        |p28RoundedMatMul fp X (p28Transpose X) i k| * |X k j|) +
    p28Gamma fp.u n *
      (∑ k : Fin n,
        (∑ l : Fin n, |X i l| * |X k l|) * |X k j|)

/-! Definitions for the square-matrix error-transport core of Lemma 4.1. -/

abbrev P28ComplexMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

noncomputable def p28Sym {n : ℕ}
    (A : P28ComplexMatrix n) : P28ComplexMatrix n :=
  (2 : ℂ)⁻¹ • (A + star A)

noncomputable def p28HermitianEstimate {n : ℕ}
    (U X : P28ComplexMatrix n) : P28ComplexMatrix n :=
  p28Sym (star U * X)

noncomputable def p28CoreCoefficient (eps d : ℝ) : ℝ :=
  (2 * d + 1) * eps

/-- The identities and quantitative bounds established in the square-case proof
of Lemma 4.1 before the final residual and Hermitian-factor estimates. -/
structure P28Lemma41CoreData (n : ℕ) where
  X : P28ComplexMatrix n
  Xbar : P28ComplexMatrix n
  Yhat : P28ComplexMatrix n
  fXbar : P28ComplexMatrix n
  P : P28ComplexMatrix n
  Q : P28ComplexMatrix n
  Sigma : P28ComplexMatrix n
  fSigma : P28ComplexMatrix n
  recoveryDiagonal : P28ComplexMatrix n
  U : P28ComplexMatrix n
  HY : P28ComplexMatrix n
  Hbar : P28ComplexMatrix n
  H : P28ComplexMatrix n
  fHbar : P28ComplexMatrix n
  Z : P28ComplexMatrix n
  EX : P28ComplexMatrix n
  EY : P28ComplexMatrix n
  EH : P28ComplexMatrix n
  eps : ℝ
  d : ℝ
  xScale : ℝ
  fScale : ℝ
  eps_nonneg : 0 ≤ eps
  d_nonneg : 0 ≤ d
  xScale_nonneg : 0 ≤ xScale
  fScale_pos : 0 < fScale
  xbar_eq : Xbar = X + EX
  y_forward : Yhat = fXbar + EY
  y_polar : Yhat = U * HY
  hy_perturbed : HY = fHbar + EH
  xbar_svd : Xbar = P * Sigma * star Q
  fxbar_svd : fXbar = P * fSigma * star Q
  hbar_svd : Hbar = Q * Sigma * star Q
  fhbar_svd : fHbar = Q * fSigma * star Q
  z_svd : Z = Q * recoveryDiagonal * star Q
  q_unitary_left : star Q * Q = 1
  singular_recovery : fSigma * recoveryDiagonal = Sigma
  unitary_left : star U * U = 1
  U_left_isometry : ∀ W : P28ComplexMatrix n, ‖U * W‖ = ‖W‖
  Ustar_left_isometry : ∀ W : P28ComplexMatrix n, ‖star U * W‖ = ‖W‖
  hbar_selfadjoint : star Hbar = Hbar
  h_selfadjoint : star H = H
  ex_bound : ‖EX‖ ≤ eps * xScale
  ey_bound : ‖EY‖ ≤ eps * fScale
  eh_bound : ‖EH‖ ≤ eps * fScale
  z_scaled_bound : fScale * ‖Z‖ ≤ d * xScale
  hermitian_polar_bound : ‖Hbar - H‖ ≤ eps * xScale

end HighamBench
