-- NumStability/Source/Higham/Chapter12/IterativeRefinement/ForwardErrorBounds/Results.lean
--
-- Canonical destination introduced by reorganization wave R03
-- (phase branch B0005, projection P0005).
--
-- Whole-owner block relocation.
-- Historical owner: `NumStability.Source.Higham.Chapter12.IterativeRefinement.Chapter12Bounds`. Public names, namespaces, kinds, visibility,
-- types, attributes and proofs are preserved exactly; private names carry
-- only the approved P0005 module-prefix normalization.

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.Algorithms.DotProduct
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LinearSystems.IterativeRefinement.Core
import NumStability.Algorithms.MatVec
import NumStability.Analysis.ForwardError
import NumStability.Analysis.MatrixAlgebra
import NumStability.Analysis.Rounding
import NumStability.FloatingPoint.Model

/-!
# Results

Relocated from `NumStability.Source.Higham.Chapter12.IterativeRefinement.Chapter12Bounds` by wave R03 under the frozen B0005 declaration
route and the P0005 baseline projection.
-/


-- Algorithms/IterativeRefinement.lean
--
-- §11: Iterative refinement for Ax = b.
--
-- Algorithm: given an approximate solver, compute x₀, then iterate:
--   r = b − Ax₀       (residual)
--   solve Ad = r       (correction)
--   x₁ = x₀ + d       (update)
--
-- Key results:
-- Theorem 11.3: One step of refinement contracts the forward error
--   A·e₁ = ΔA·d̂ + (r − r̂), so |e₁| ≤ |A⁻¹|(μ|A||d̂| + ν|r| + ω)
-- Theorem 11.4: If σ = μ(1+ν)/(1−μ) + ν < 1, backward error improves
--   |r₁| ≤ μ·|A|·|d̂| + ν·|r| + ω















namespace NumStability

open scoped BigOperators

-- ============================================================
-- §11.1  Componentwise ordering helpers
-- ============================================================









-- ============================================================
-- §11.1  Solver specification (equation 11.5)
-- ============================================================




















-- ============================================================
-- §11.1  Residual computation error (equation 11.6)
-- ============================================================













-- ============================================================
-- §11.1  Conventional residual computation (equation 11.7)
-- ============================================================






























































































































































-- ============================================================
-- §11.2  One-step refinement: forward error identity (Theorem 11.3)
-- ============================================================














































-- ============================================================
-- §11.2  One-step refinement: residual contraction
-- ============================================================


































































-- ============================================================
-- §11.2  Theorem 11.4: Backward stability of one refinement step
-- ============================================================

























































-- ============================================================
-- §11.3  LU-based iterative refinement
-- ============================================================







































































-- ============================================================
-- §11.2  Correction vector bound
-- ============================================================











-- ============================================================
-- §11.2  Residual bound in terms of x₁ (Theorem 11.3, assembled)
-- ============================================================


























































-- ============================================================
-- §11.2  Theorem 11.3: Forward error bound (equation 11.8)
-- ============================================================











































































-- ============================================================
-- §11.1  Linear contraction (Theorems 11.1–11.2 core)
-- ============================================================











































-- ============================================================
-- §11.1  Computed residual absolute bound
-- ============================================================
















-- ============================================================
-- §11.2  Theorem 11.4: Full backward error contraction with σ
-- ============================================================




















































-- ============================================================
-- §11.2  Backward error relative to |A||x₁| (equation 11.20)
-- ============================================================








































-- ============================================================
-- §11.3  LU solve to solver bound (GE specialization)
-- ============================================================































-- ============================================================
-- §11.2  Three-term triangle inequality helper
-- ============================================================







-- ============================================================
-- §11.2  Theorem 11.3: Three-term identity (equation 11.12)
-- ============================================================
























































-- ============================================================
-- §11.2  Solver perturbation to residual form
-- ============================================================































-- ============================================================
-- §11.2  Three-term bound with explicit bounds substituted
-- ============================================================































-- ============================================================
-- §11.2  Theorem 11.3: GE + standard residual (eq. 11.12 concrete)
-- ============================================================










































-- ============================================================
-- §11.2  Theorem 11.4: Backward error with rounded update
-- ============================================================



























-- ============================================================
-- §11.2  Skewness ratio σ(B,x) (Higham §11.2)
-- ============================================================






































-- ============================================================
-- §11.2  Equation (11.15): |x̂| bound from rounded update
-- ============================================================













































-- ============================================================
-- §11.2  Equation (11.16): |r̂| bound
-- ============================================================


































-- ============================================================
-- §11.2  Equation (11.17): combined three-term bound with coefficients
-- ============================================================













































-- ============================================================
-- §11.2  Identity matrix definition
-- ============================================================









-- ============================================================
-- §11.2  Eq (11.18)–(11.19): solving for |A||d̂| via Neumann bound
-- ============================================================































-- ============================================================
-- §11.2  Solver correction via inverse (eq. 11.18, with A⁻¹)
-- ============================================================




































































-- ============================================================
-- §11.2  Assembled Theorem 11.4: full backward error bound
-- ============================================================







































-- ============================================================
-- §11.2  Substitution lemma: bound |A||x₀| via |A||ŷ| and |A||d̂|
-- ============================================================






















-- ============================================================
-- §11.2  Self-contained Theorem 11.4
-- ============================================================




































































































































-- ============================================================
-- §11.3  LU instantiation of Theorem 11.4
-- ============================================================






































-- ============================================================
-- §12.2  Nonnegative resolvent ∞-norm bound (Neumann inversion, eqns 12.20–12.21)
-- ============================================================

/-- **Nonnegative resolvent ∞-norm bound** — the Neumann-series consequence used
    in Higham §12.2, eqns (12.20)–(12.21) (2nd ed., Chapter 12 "Iterative
    Refinement"; the file's earlier `11.x` docstrings predate the 2nd-edition
    renumbering, in which iterative refinement is Chapter 12).

    If `M` is entrywise nonnegative with every row sum `≤ c < 1`, `v ≥ 0`
    componentwise, and `(I − M) v ≤ w` componentwise (`v_i ≤ (M v)_i + w_i`),
    then `‖v‖∞ ≤ ‖w‖∞ / (1 − c)`.

    This is the honest content of "`(I − M)` has a nonnegative inverse with
    `‖(I − M)⁻¹‖∞ ≤ 1/(1−c)`" without constructing the inverse: it is exactly the
    scalar bound Higham uses at (12.20)–(12.21) (with `c = 1/2`, giving the
    factor `2` in `‖(I − uM₃)⁻¹‖∞ ≤ 2`). -/
theorem nonneg_resolvent_infNormVec_bound {n : ℕ} (hn : 0 < n)
    (M : Fin n → Fin n → ℝ) (v w : Fin n → ℝ)
    (hM : ∀ i j : Fin n, 0 ≤ M i j)
    (hv : ∀ i : Fin n, 0 ≤ v i)
    (c : ℝ) (hc_lt : c < 1)
    (hrow : ∀ i : Fin n, ∑ j : Fin n, M i j ≤ c)
    (hstep : ∀ i : Fin n, v i ≤ (∑ j : Fin n, M i j * v j) + w i) :
    infNormVec v ≤ infNormVec w / (1 - c) := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  obtain ⟨i, hi⟩ := infNormVec_exists_le_abs hn v
  have hnv_le_vi : infNormVec v ≤ v i := by
    rw [abs_of_nonneg (hv i)] at hi; exact hi
  have hMv : (∑ j : Fin n, M i j * v j) ≤ c * infNormVec v := by
    calc (∑ j : Fin n, M i j * v j)
        ≤ ∑ j : Fin n, M i j * infNormVec v :=
          Finset.sum_le_sum (fun j _ => by
            have hvj : v j ≤ infNormVec v := by
              have := abs_le_infNormVec v j
              rwa [abs_of_nonneg (hv j)] at this
            exact mul_le_mul_of_nonneg_left hvj (hM i j))
      _ = (∑ j : Fin n, M i j) * infNormVec v := by rw [Finset.sum_mul]
      _ ≤ c * infNormVec v :=
          mul_le_mul_of_nonneg_right (hrow i) (infNormVec_nonneg v)
  have hwi : w i ≤ infNormVec w :=
    le_trans (le_abs_self (w i)) (abs_le_infNormVec w i)
  have hchain : infNormVec v ≤ c * infNormVec v + infNormVec w := by
    calc infNormVec v ≤ v i := hnv_le_vi
      _ ≤ (∑ j : Fin n, M i j * v j) + w i := hstep i
      _ ≤ c * infNormVec v + infNormVec w := by linarith [hMv, hwi]
  rw [le_div_iff₀ h1c]
  have hrw : infNormVec v * (1 - c) = infNormVec v - c * infNormVec v := by ring
  linarith [hchain, hrw]

-- ============================================================
-- §12.1  Exact forward-error identity/bound for one step (eqns 12.4–12.5)
-- ============================================================

/-- **Exact forward-error identity for one refinement step** (Higham §12.1, the
    exact core of eq. (12.5) with all three rounding sources).

    Let `x` be the exact solution (`A x = b`).  With computed residual
    `rc = (b − A x_i) + Δr` (residual-computation error `Δr`), computed correction
    `d` solving the perturbed system `(A + ΔA) d = rc`, and rounded update
    `y = x_i + d + Δx`, the forward error of the corrected iterate obeys the exact
    identity
      `A (y − x) = Δr − ΔA·d + A·Δx`.
    No inverse and no first-order truncation are used; this is the exact residual
    of the new forward error, from which the (12.5) recurrence follows by applying
    `|A⁻¹|`. -/
theorem forward_error_step_identity (n : ℕ)
    (A ΔA : Fin n → Fin n → ℝ)
    (x x_i d Δr Δx rc y b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hrc : ∀ i, rc i = (b i - ∑ j : Fin n, A i j * x_i j) + Δr i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d j = rc i)
    (hy : ∀ i, y i = x_i i + d i + Δx i) :
    ∀ i : Fin n,
      ∑ j : Fin n, A i j * (y j - x j) =
        Δr i - (∑ j : Fin n, ΔA i j * d j) + (∑ j : Fin n, A i j * Δx j) := by
  intro i
  have hAd : ∑ j : Fin n, A i j * d j =
      rc i - ∑ j : Fin n, ΔA i j * d j := by
    have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  have hexp : ∑ j : Fin n, A i j * (y j - x j) =
      (∑ j : Fin n, A i j * x_i j) + (∑ j : Fin n, A i j * d j)
        + (∑ j : Fin n, A i j * Δx j) - ∑ j : Fin n, A i j * x j := by
    have h1 : ∀ j : Fin n, A i j * (y j - x j)
        = A i j * x_i j + A i j * d j + A i j * Δx j - A i j * x j :=
      fun j => by rw [hy]; ring
    simp_rw [h1]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hexp, hAd, hrc i, hAx i]
  ring

/-- **Forward-error bound for one refinement step** (Higham §12.1, eq. (12.5)).

    Applying a componentwise `|A⁻¹|` resolver (`Ainv ≥ 0`, resolving `A v = w ⇒
    |v| ≤ Ainv |w|`) to `forward_error_step_identity` gives the componentwise
    forward-error bound
      `|y − x|_i ≤ ∑_j Ainv_ij (|Δr|_j + (|ΔA||d|)_j + (|A||Δx|)_j)`,
    the three-source form of Higham's `G_i|x − x_i| + g_i` recurrence: `Δr` carries
    the (12.2) residual term (which contains the contracting `|A||x − x_i|` part),
    `ΔA` the solver backward error `≤ uW`, and `Δx` the update rounding. -/
theorem forward_error_step_bound (n : ℕ)
    (A ΔA : Fin n → Fin n → ℝ)
    (x x_i d Δr Δx rc y b : Fin n → ℝ)
    (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (hrc : ∀ i, rc i = (b i - ∑ j : Fin n, A i j * x_i j) + Δr i)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d j = rc i)
    (hy : ∀ i, y i = x_i i + d i + Δx i)
    (Ainv : Fin n → Fin n → ℝ)
    (hAinv_nn : ∀ i j, 0 ≤ Ainv i j)
    (hAinv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, Ainv i j * |w j|) :
    ∀ i : Fin n,
      |y i - x i| ≤
        ∑ j : Fin n, Ainv i j *
          (|Δr j| + (∑ k : Fin n, |ΔA j k| * |d k|)
            + (∑ k : Fin n, |A j k| * |Δx k|)) := by
  intro i
  have hid := forward_error_step_identity n A ΔA x x_i d Δr Δx rc y b
    hAx hrc hsolve hy
  have hstep := hAinv (fun j => y j - x j)
    (fun j => Δr j - (∑ k : Fin n, ΔA j k * d k) + (∑ k : Fin n, A j k * Δx k))
    hid i
  refine le_trans hstep ?_
  apply Finset.sum_le_sum
  intro j _
  apply mul_le_mul_of_nonneg_left _ (hAinv_nn i j)
  have hΔAd : |∑ k : Fin n, ΔA j k * d k| ≤ ∑ k : Fin n, |ΔA j k| * |d k| := by
    calc |∑ k, ΔA j k * d k| ≤ ∑ k, |ΔA j k * d k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |ΔA j k| * |d k| := by congr 1; ext k; exact abs_mul _ _
  have hAΔx : |∑ k : Fin n, A j k * Δx k| ≤ ∑ k : Fin n, |A j k| * |Δx k| := by
    calc |∑ k, A j k * Δx k| ≤ ∑ k, |A j k * Δx k| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k, |A j k| * |Δx k| := by congr 1; ext k; exact abs_mul _ _
  have htri : |Δr j - (∑ k, ΔA j k * d k) + (∑ k, A j k * Δx k)|
      ≤ |Δr j| + |∑ k, ΔA j k * d k| + |∑ k, A j k * Δx k| := by
    have h := abs_add_three_le (Δr j) (-(∑ k, ΔA j k * d k)) (∑ k, A j k * Δx k)
    simp only [abs_neg] at h
    have heq : Δr j - (∑ k, ΔA j k * d k) + (∑ k, A j k * Δx k)
        = Δr j + -(∑ k, ΔA j k * d k) + (∑ k, A j k * Δx k) := by ring
    rw [heq]; exact h
  linarith [htri, hΔAd, hAΔx]

-- ============================================================
-- §12.2  Norm-to-componentwise correction bound (σ/cond step for Thm 12.4)
-- ============================================================

/-- **Norm-to-componentwise correction bound** (scalar form of the σ/cond step
    discharging the correction hypothesis of Theorem 12.4).

    If the nonnegative correction-magnitude vector `dvec` has `‖dvec‖∞ ≤ ρ₀`, the
    target vector `t` is bounded below by `m > 0`, and `ρ₀ ≤ ρ·m`, then
    `dvec_i ≤ ρ · t_i` for every `i`.  Here `m` is a positive lower bound on the
    scaled data `|A||ŷ| + |b|`; `ρ = ρ₀/m` is the explicit correction constant —
    the exact, non-asymptotic content of Higham's `cond(A⁻¹)σ(A,ŷ)` condition. -/
theorem correction_componentwise_of_infNorm {n : ℕ}
    (dvec t : Fin n → ℝ) (rho0 ρ m : ℝ)
    (hnorm : infNormVec dvec ≤ rho0)
    (_hm_pos : 0 < m) (ht_lb : ∀ i, m ≤ t i)
    (hρ_nn : 0 ≤ ρ) (hcond : rho0 ≤ ρ * m) :
    ∀ i, dvec i ≤ ρ * t i := by
  intro i
  have hdi : dvec i ≤ rho0 :=
    le_trans (le_trans (le_abs_self _) (abs_le_infNormVec dvec i)) hnorm
  have h2 : ρ * m ≤ ρ * t i := mul_le_mul_of_nonneg_left (ht_lb i) hρ_nn
  linarith [hdi, hcond, h2]

-- ============================================================
-- §12.2  Correction Neumann inequality from the solver (eqns 12.18–12.20)
-- ============================================================

/-- **Correction Neumann inequality** (Higham §12.2, eqns (12.18)–(12.20), exact form).

    From the solver `(A + ΔA) d̂ = r̂` with `|ΔA| ≤ μ|A|` and a nonnegative resolver
    `Ainv` for `A` (`A v = w ⇒ |v_i| ≤ ∑_j Ainv_ij |w_j|`), the correction magnitude
    vector `|A||d̂|` satisfies the componentwise Neumann inequality
      `(|A||d̂|)_i ≤ ∑_k P_{ik} |r̂_k| + μ ∑_k P_{ik} (|A||d̂|)_k`,   `P := |A|·Ainv`,
    i.e. `(I − μ|A|Ainv)(|A||d̂|) ≤ (|A|Ainv)|r̂|`.  This is Higham's (12.18)/(12.20)
    with `M₃ = |A||A⁻¹|`, derived **exactly** (no `O(u²)`): the input consumed by
    `nonneg_resolvent_infNormVec_bound` / `higham12_21_correction_infNorm_bound`
    with `M := μ|A|Ainv` (`≥ 0`) and `w := (|A|Ainv)|r̂|`. -/
theorem correction_neumann_inequality (n : ℕ)
    (A Ainv ΔA : Fin n → Fin n → ℝ) (d_hat r_hat : Fin n → ℝ)
    (μ : ℝ) (_hμ_nn : 0 ≤ μ)
    (hAinv_nn : ∀ i j, 0 ≤ Ainv i j)
    (hAinv : ∀ (v w : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * v j = w i) →
      ∀ i, |v i| ≤ ∑ j : Fin n, Ainv i j * |w j|)
    (hΔA : ∀ i j, |ΔA i j| ≤ μ * |A i j|)
    (hsolve : ∀ i, ∑ j : Fin n, (A i j + ΔA i j) * d_hat j = r_hat i) :
    ∀ i : Fin n,
      (∑ j : Fin n, |A i j| * |d_hat j|) ≤
        (∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * |r_hat k|)
          + μ * ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k)
              * (∑ l : Fin n, |A k l| * |d_hat l|) := by
  -- A d̂ = r̂ − ΔA d̂
  have hAd : ∀ i, ∑ j : Fin n, A i j * d_hat j
      = r_hat i - ∑ j : Fin n, ΔA i j * d_hat j := by
    intro i; have := hsolve i; simp_rw [add_mul] at this
    rw [Finset.sum_add_distrib] at this; linarith
  -- resolver on d̂ with w_k = r̂_k − (ΔA d̂)_k
  have hdj := hAinv d_hat (fun k => r_hat k - ∑ l : Fin n, ΔA k l * d_hat l) hAd
  -- |w_k| ≤ |r̂_k| + μ (|A||d̂|)_k
  have hwk : ∀ k : Fin n, |r_hat k - ∑ l : Fin n, ΔA k l * d_hat l|
      ≤ |r_hat k| + μ * ∑ l : Fin n, |A k l| * |d_hat l| := by
    intro k
    have h1 : |r_hat k - ∑ l, ΔA k l * d_hat l| ≤ |r_hat k| + |∑ l, ΔA k l * d_hat l| :=
      abs_sub (r_hat k) (∑ l, ΔA k l * d_hat l)
    have h2 : |∑ l, ΔA k l * d_hat l| ≤ μ * ∑ l, |A k l| * |d_hat l| := by
      calc |∑ l, ΔA k l * d_hat l| ≤ ∑ l, |ΔA k l * d_hat l| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ l, |ΔA k l| * |d_hat l| := by congr 1; ext l; exact abs_mul _ _
        _ ≤ ∑ l, (μ * |A k l|) * |d_hat l| :=
            Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_right (hΔA k l) (abs_nonneg _))
        _ = μ * ∑ l, |A k l| * |d_hat l| := by rw [Finset.mul_sum]; congr 1; ext l; ring
    linarith
  -- |d̂_j| ≤ ∑_k Ainv_jk (|r̂_k| + μ (|A||d̂|)_k)
  have hdj2 : ∀ j : Fin n, |d_hat j| ≤
      ∑ k : Fin n, Ainv j k * (|r_hat k| + μ * ∑ l : Fin n, |A k l| * |d_hat l|) := by
    intro j
    refine le_trans (hdj j) ?_
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hwk k) (hAinv_nn j k))
  intro i
  -- abbreviation X k = |r̂_k| + μ (|A||d̂|)_k
  set X : Fin n → ℝ := fun k => |r_hat k| + μ * ∑ l : Fin n, |A k l| * |d_hat l| with hX
  have hswap : ∑ j : Fin n, |A i j| * (∑ k : Fin n, Ainv j k * X k)
      = ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * X k := by
    calc ∑ j, |A i j| * (∑ k, Ainv j k * X k)
        = ∑ j, ∑ k, |A i j| * (Ainv j k * X k) := by
          apply Finset.sum_congr rfl; intro j _; rw [Finset.mul_sum]
      _ = ∑ k, ∑ j, |A i j| * (Ainv j k * X k) := Finset.sum_comm
      _ = ∑ k, (∑ j, |A i j| * Ainv j k) * X k := by
          apply Finset.sum_congr rfl; intro k _
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro j _; ring
  have hsplit : ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * X k
      = (∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k) * |r_hat k|)
          + μ * ∑ k : Fin n, (∑ j : Fin n, |A i j| * Ainv j k)
              * (∑ l : Fin n, |A k l| * |d_hat l|) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro k _; simp only [hX]; ring
  calc ∑ j, |A i j| * |d_hat j|
      ≤ ∑ j, |A i j| * (∑ k, Ainv j k * X k) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hdj2 j) (abs_nonneg _))
    _ = ∑ k, (∑ j, |A i j| * Ainv j k) * X k := hswap
    _ = _ := hsplit

end NumStability
