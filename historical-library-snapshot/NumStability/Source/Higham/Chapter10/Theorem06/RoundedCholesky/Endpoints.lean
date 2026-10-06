import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.LU.LUSolve
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Certificates
import NumStability.Algorithms.LinearSystems.Cholesky.ErrorAnalysis.Demmel
import NumStability.Algorithms.LinearSystems.Cholesky.Factorization.Spec
import NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution
import NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution
import NumStability.Analysis.MatrixNorms.EntrywiseAbsolute.Basic
import NumStability.Analysis.MatrixSpectral
import NumStability.Analysis.Rounding
import NumStability.Analysis.SubtractionFold
import NumStability.Analysis.Summation.ErrorBounds
import NumStability.FloatingPoint.Model
import NumStability.Source.Higham.Chapter09.Problems
import NumStability.Source.Higham.Chapter09.Section01
import NumStability.Source.Higham.Chapter09.Section02
import NumStability.Source.Higham.Chapter09.Section03
import NumStability.Source.Higham.Chapter09.Section04
import NumStability.Source.Higham.Chapter09.Section05
import NumStability.Source.Higham.Chapter09.Section06
import NumStability.Source.Higham.Chapter09.Section08
import NumStability.Source.Higham.Chapter09.Section10
import NumStability.Source.Higham.Chapter09.Section11

/-!
# Chapter10 Theorem06 RoundedCholesky Endpoints

Canonical destination for material split out of
`NumStability.Algorithms.HighamChapter10` by wave W03 of the August 2026 repository reorganization.
Declaration names, statements and proofs are unchanged; only the
module they live in has changed. The historical module still
resolves and re-exports this one.
-/

open scoped BigOperators

namespace NumStability

/-- **Theorem 10.6 / equation (10.10)**:
Demmel-Wilkinson scaled forward-error interface.  The perturbation and scaling
argument is supplied as `hscaled_err`, matching the focused Cholesky module. -/
theorem higham10_6_scaled_forward_error (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ)
    (κH f_n : ℝ)
    (hscaled_err : ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * fp.u * (|x i| / D i)) :
    ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * fp.u * (|x i| / D i) :=
  cholesky_scaled_forward_error n fp A D κH f_n hscaled_err

/-- **Standard 2-norm perturbation bound** (the "standard perturbation
theory" step in the proof of Theorem 10.6, Higham p. 199): if `A x = b`,
`(A + ΔA) x̂ = b`, and `A⁻¹ ΔA` carries an operator-2-norm certificate
`c < 1`, then `‖x̂ − x‖₂ ≤ c/(1−c) · ‖x‖₂`. -/
theorem higham10_6_perturbed_solve_forward_error (n : ℕ)
    (A Ainv ΔA : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hInv : ∀ v : Fin n → ℝ, matMulVec n Ainv (matMulVec n A v) = v)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (c : ℝ) (hc : opNorm2Le (matMul n Ainv ΔA) c) (hc1 : c < 1) :
    vecNorm2 (fun i => xhat i - x i) ≤ c / (1 - c) * vecNorm2 x := by
  have h1c : (0:ℝ) < 1 - c := by linarith
  have hAdiff : matMulVec n A (fun k => xhat k - x k) =
      fun i => -(matMulVec n ΔA xhat i) := by
    funext i
    have hsub : matMulVec n A (fun k => xhat k - x k) i =
        matMulVec n A xhat i - matMulVec n A x i := by
      unfold matMulVec
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hbx : matMulVec n A x i = b i := congrFun hAx i
    have hb := hAhat i
    rw [hsub, hbx]
    linarith
  have hdiff : (fun k => xhat k - x k) =
      fun i => -(matMulVec n (matMul n Ainv ΔA) xhat i) := by
    have h2 := hInv (fun k => xhat k - x k)
    rw [hAdiff] at h2
    rw [← h2]
    rw [show matMulVec n Ainv (fun i => -(matMulVec n ΔA xhat i)) =
        fun i => -(matMulVec n Ainv (matMulVec n ΔA xhat) i) from
      matMulVec_neg n Ainv (matMulVec n ΔA xhat)]
    funext i
    rw [matMulVec_matMul n Ainv ΔA xhat i]
  have hnorm_diff : vecNorm2 (fun i => xhat i - x i) ≤ c * vecNorm2 xhat := by
    rw [hdiff, vecNorm2_neg (matMulVec n (matMul n Ainv ΔA) xhat)]
    exact hc xhat
  have hxhat : vecNorm2 xhat ≤
      vecNorm2 x + vecNorm2 (fun i => xhat i - x i) := by
    have := vecNorm2_add_le x (fun i => xhat i - x i)
    have hxx : (fun i => x i + (xhat i - x i)) = xhat := by
      funext i; ring
    rwa [hxx] at this
  have hkey : vecNorm2 (fun i => xhat i - x i) * (1 - c) ≤
      c * vecNorm2 x := by
    have h0x : 0 ≤ c * vecNorm2 x := le_trans (vecNorm2_nonneg _) (hc x)
    have he0 : 0 ≤ vecNorm2 (fun i => xhat i - x i) := vecNorm2_nonneg _
    rcases le_total 0 c with hc0 | hc0
    · have hchain := le_trans hnorm_diff
        (mul_le_mul_of_nonneg_left hxhat hc0)
      nlinarith
    · have hh0 : 0 ≤ vecNorm2 xhat := vecNorm2_nonneg _
      have hch : c * vecNorm2 xhat ≤ 0 := by nlinarith
      have hez : vecNorm2 (fun i => xhat i - x i) = 0 :=
        le_antisymm (by linarith) he0
      rw [hez, zero_mul]
      exact h0x
  rw [div_mul_eq_mul_div, le_div_iff₀ h1c]
  linarith [hkey]

/-- **Theorem 10.6 (Demmel–Wilkinson), certificate assembly** (Higham
§10.1, equation (10.10)): scaling the perturbed Cholesky solve by
`D = diag(a_ii^{1/2})` and applying the standard perturbation bound.  With
`H = D⁻¹AD⁻¹`, exact solve `A x = b`, perturbed solve `(A + ΔA) x̂ = b`,
an inverse-action certificate for `H`, and an operator-2-norm certificate
`c < 1` for `H⁻¹ (D⁻¹ ΔA D⁻¹)` — the `κ₂(H) ε` of the source display —
the `D`-scaled error satisfies `‖D(x̂ − x)‖₂ ≤ c/(1−c) ‖Dx‖₂`.  This
replaces the previously assumed-hypothesis interface
`higham10_6_scaled_forward_error` with a proved assembly; the remaining
source gap is producing the `c` certificate from `κ₂(H)` and the concrete
`fl_cholesky` solve (Theorem 10.4 + equation (10.8) + `‖eeᵀ‖₂ = n`). -/
theorem higham10_6_scaled_forward_error_assembled (n : ℕ)
    (A ΔA H Hinv : Fin n → Fin n → ℝ) (D : Fin n → ℝ)
    (x xhat b : Fin n → ℝ)
    (hD : ∀ i, D i ≠ 0)
    (hH : ∀ i j, H i j = A i j / (D i * D j))
    (hInv : ∀ v : Fin n → ℝ, matMulVec n Hinv (matMulVec n H v) = v)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (c : ℝ)
    (hc : opNorm2Le (matMul n Hinv
      (fun i j => ΔA i j / (D i * D j))) c)
    (hc1 : c < 1) :
    vecNorm2 (fun i => D i * xhat i - D i * x i) ≤
      c / (1 - c) * vecNorm2 (fun i => D i * x i) := by
  have hscale : ∀ (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n),
      matMulVec n (fun i' j' => M i' j' / (D i' * D j'))
        (fun k => D k * v k) i = matMulVec n M v i / D i := by
    intro M v i
    unfold matMulVec
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hD i, hD j]
  have hHDx : matMulVec n H (fun k => D k * x k) =
      fun i => b i / D i := by
    funext i
    have hHs : matMulVec n H (fun k => D k * x k) i =
        matMulVec n (fun i' j' => A i' j' / (D i' * D j'))
          (fun k => D k * x k) i := by
      unfold matMulVec
      exact Finset.sum_congr rfl fun j _ => by rw [hH i j]
    rw [hHs, hscale A x i, congrFun hAx i]
  have hHDxhat : ∀ i : Fin n,
      matMulVec n H (fun k => D k * xhat k) i +
        matMulVec n (fun i' j' => ΔA i' j' / (D i' * D j'))
          (fun k => D k * xhat k) i = b i / D i := by
    intro i
    have hHs : matMulVec n H (fun k => D k * xhat k) i =
        matMulVec n (fun i' j' => A i' j' / (D i' * D j'))
          (fun k => D k * xhat k) i := by
      unfold matMulVec
      exact Finset.sum_congr rfl fun j _ => by rw [hH i j]
    rw [hHs, hscale A xhat i, hscale ΔA xhat i, ← add_div, hAhat i]
  have hmain := higham10_6_perturbed_solve_forward_error n H Hinv
    (fun i' j' => ΔA i' j' / (D i' * D j'))
    (fun k => D k * x k) (fun k => D k * xhat k) (fun i => b i / D i)
    hInv hHDx hHDxhat c hc hc1
  exact hmain

/-- **Theorem 10.6 (Demmel–Wilkinson) for the concrete solve chain**
(Higham §10.1, equation (10.10)): with the Theorem 10.3 certificate for
`R̂`, a solve-chain perturbation `ΔA` bounded by `ε_tot·|R̂ᵀ||R̂|`
(supplied by `cholesky_solve_backward_error_expanded`), an inverse-action
certificate for `H = D⁻¹AD⁻¹` and a `κ₂(H)`-style operator certificate
for `H⁻¹`, the `D`-scaled forward error satisfies
`‖D(x̂−x)‖₂ ≤ c/(1−c)·‖Dx‖₂` with the explicit
`c = κ·n·ε_tot/(1−γ_{n+1})` — the source display (10.10) with
`ε_tot = γ_{n+1} + 2γ_n + γ_n²` in place of `γ_{3n+1}`. -/
theorem higham10_6_fl_scaled_forward_error (fp : FPModel) (n : ℕ)
    (A R Hinv ΔA : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hγ1 : gamma fp (n + 1) < 1)
    (hChol : CholeskyBackwardError n A R (gamma fp (n + 1)))
    (εtot : ℝ) (hε : 0 ≤ εtot)
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤
      εtot * ∑ k : Fin n, |R k i| * |R k j|)
    (hInv : ∀ v : Fin n → ℝ,
      matMulVec n Hinv (matMulVec n (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) v) = v)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : opNorm2Le Hinv κ)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (hc1 : κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) < 1) :
    vecNorm2 (fun i => Real.sqrt (A i i) * xhat i -
        Real.sqrt (A i i) * x i) ≤
      κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) /
        (1 - κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1))))) *
      vecNorm2 (fun i => Real.sqrt (A i i) * x i) := by
  have hscaled := scaled_opNorm2Le_of_factor_bound fp n A R hAdiag hγ1
    hChol ΔA εtot hε hΔA
  have hcomp := opNorm2Le_matMul n Hinv
    (fun i j => ΔA i j / (Real.sqrt (A i i) * Real.sqrt (A j j)))
    κ ((n : ℝ) * (εtot / (1 - gamma fp (n + 1)))) hκ0 hκ hscaled
  exact higham10_6_scaled_forward_error_assembled n A ΔA
    (fun i l : Fin n => A i l / (Real.sqrt (A i i) * Real.sqrt (A l l)))
    Hinv (fun i => Real.sqrt (A i i)) x xhat b
    (fun i => (Real.sqrt_pos.mpr (hAdiag i)).ne')
    (fun i j => rfl) hInv hAx hAhat
    (κ * ((n : ℝ) * (εtot / (1 - gamma fp (n + 1))))) hcomp hc1

/-- **Theorem 10.6 / display (10.10) with the source constant**: the
    scaled forward-error bound of `higham10_6_fl_scaled_forward_error`
    with the composite solve-chain constant absorbed into Higham's
    `γ_{3n+1}` — `c = κ n γ_{3n+1}/(1 − γ_{n+1})` exactly as printed. -/
theorem higham10_6_fl_scaled_forward_error_source (fp : FPModel) (n : ℕ)
    (A R Hinv ΔA : Fin n → Fin n → ℝ) (x xhat b : Fin n → ℝ)
    (hAdiag : ∀ i : Fin n, 0 < A i i)
    (hγ1 : gamma fp (n + 1) < 1)
    (hn3 : gammaValid fp (3 * n + 1))
    (hChol : CholeskyBackwardError n A R (gamma fp (n + 1)))
    (hΔA : ∀ i j : Fin n, |ΔA i j| ≤
      (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
        ∑ k : Fin n, |R k i| * |R k j|)
    (hInv : ∀ v : Fin n → ℝ,
      matMulVec n Hinv (matMulVec n (fun i l : Fin n =>
        A i l / (Real.sqrt (A i i) * Real.sqrt (A l l))) v) = v)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : opNorm2Le Hinv κ)
    (hAx : matMulVec n A x = b)
    (hAhat : ∀ i : Fin n,
      matMulVec n A xhat i + matMulVec n ΔA xhat i = b i)
    (hc1 : κ * ((n : ℝ) *
      (gamma fp (3 * n + 1) / (1 - gamma fp (n + 1)))) < 1) :
    vecNorm2 (fun i => Real.sqrt (A i i) * xhat i -
        Real.sqrt (A i i) * x i) ≤
      κ * ((n : ℝ) * (gamma fp (3 * n + 1) / (1 - gamma fp (n + 1)))) /
        (1 - κ * ((n : ℝ) *
          (gamma fp (3 * n + 1) / (1 - gamma fp (n + 1))))) *
      vecNorm2 (fun i => Real.sqrt (A i i) * x i) := by
  have habsorb := eps_tot_le_gamma_3n1 fp n hn3
  refine higham10_6_fl_scaled_forward_error fp n A R Hinv ΔA x xhat b
    hAdiag hγ1 hChol (gamma fp (3 * n + 1))
    (gamma_nonneg fp hn3) (fun i j => ?_) hInv κ hκ0 hκ hAx hAhat hc1
  calc |ΔA i j|
      ≤ (gamma fp (n + 1) + 2 * gamma fp n + gamma fp n ^ 2) *
          ∑ k : Fin n, |R k i| * |R k j| := hΔA i j
    _ ≤ gamma fp (3 * n + 1) * ∑ k : Fin n, |R k i| * |R k j| :=
        mul_le_mul_of_nonneg_right habsorb
          (absRT_R_product_nonneg n R i j)

end NumStability
