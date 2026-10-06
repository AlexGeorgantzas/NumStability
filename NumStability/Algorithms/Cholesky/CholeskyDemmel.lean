-- Algorithms/Cholesky/CholeskyDemmel.lean
--
-- Demmel's results on Cholesky factorization (Higham §10.1):
-- - Theorem 10.5: |ΔA| ≤ (1−γ_{n+1})⁻¹ γ_{n+1} dd^T (column norm bound)
-- - Theorem 10.6: Scaled forward error via DHD decomposition
-- - Theorem 10.7: Success condition for Cholesky

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.Cholesky.CholeskySpec

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §10.1  Column norms and Cauchy-Schwarz
-- ============================================================

/-- **Column norm squared** of R at column i: d_i² = ∑_k R_{ki}². -/
noncomputable def colNormSq (n : ℕ) (R : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ k : Fin n, R k i ^ 2

/-- Column norm squared is nonneg. -/
lemma colNormSq_nonneg (n : ℕ) (R : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ colNormSq n R i :=
  Finset.sum_nonneg (fun k _ => sq_nonneg (R k i))

/-- **Column 2-norm** of R at column i: `d_i = √(∑_k R_{ki}²)`. -/
noncomputable def colNorm (n : ℕ) (R : Fin n → Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.sqrt (colNormSq n R i)

/-- Column 2-norm is nonneg. -/
lemma colNorm_nonneg (n : ℕ) (R : Fin n → Fin n → ℝ) (i : Fin n) :
    0 ≤ colNorm n R i :=
  Real.sqrt_nonneg _

/-- **Cauchy-Schwarz for Cholesky columns** (Higham §10.1, proof of Theorem
10.5): the componentwise absolute factor product is bounded by the product of
column 2-norms, `∑_k |R_{ki}||R_{kj}| ≤ d_i d_j`.  This is the estimate the
source proof invokes; here it is proved rather than assumed. -/
lemma colNorm_cauchy_schwarz (n : ℕ) (R : Fin n → Fin n → ℝ) (i j : Fin n) :
    ∑ k : Fin n, |R k i| * |R k j| ≤ colNorm n R i * colNorm n R j := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k => |R k i|) (fun k => |R k j|)
  have hi_eq : (∑ k : Fin n, |R k i| ^ 2) = colNormSq n R i := by
    unfold colNormSq; exact Finset.sum_congr rfl (fun k _ => sq_abs (R k i))
  have hj_eq : (∑ k : Fin n, |R k j| ^ 2) = colNormSq n R j := by
    unfold colNormSq; exact Finset.sum_congr rfl (fun k _ => sq_abs (R k j))
  rw [hi_eq, hj_eq] at hcs
  have hsum_nonneg : 0 ≤ ∑ k : Fin n, |R k i| * |R k j| :=
    Finset.sum_nonneg (fun k _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
  calc ∑ k : Fin n, |R k i| * |R k j|
      = Real.sqrt ((∑ k : Fin n, |R k i| * |R k j|) ^ 2) := by
        rw [Real.sqrt_sq hsum_nonneg]
    _ ≤ Real.sqrt (colNormSq n R i * colNormSq n R j) := Real.sqrt_le_sqrt hcs
    _ = colNorm n R i * colNorm n R j := by
        rw [colNorm, colNorm, Real.sqrt_mul (colNormSq_nonneg n R i)]

-- ============================================================
-- §10.1  Theorem 10.5: Demmel column norm bound
-- ============================================================

/-- **Demmel column norm bound** (Higham §10.1, Theorem 10.5).

    If Cholesky factorization applied to SPD A runs to completion,
    then the computed R̂ satisfies:
      R̂^T R̂ = A + ΔA  with  |ΔA_{ij}| ≤ ε/(1−ε) · d_i · d_j

    where d_i = ‖R̂_{:,i}‖₂ (column 2-norm of R̂) and ε = γ_{n+1}.

    The proof uses Cauchy-Schwarz: ∑_k |R̂_{ki}||R̂_{kj}| ≤ d_i d_j,
    combined with the nonneg factor bound |R̂^T||R̂| ≤ |A|/(1−ε).

    We state this with the Cauchy-Schwarz bound as a hypothesis `hCS`
    to avoid introducing sqrt. The bound follows from:
    (∑_k |a_k||b_k|)² ≤ (∑_k a_k²)(∑_k b_k²) = d_i² · d_j². -/
theorem cholesky_demmel_bound (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (hd : ∀ i, 0 ≤ d i)
    (hCS : ∀ i j, ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ d i * d j)
    (ε : ℝ) (hε : 0 ≤ ε) (hε_lt : ε < 1)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) * (d i * d j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  refine ⟨ΔA, fun i j => ?_, hΔA_eq⟩
  have h1_ε_pos : (0 : ℝ) < 1 - ε := by linarith
  -- The direct Cauchy-Schwarz estimate gives |ΔA_ij| ≤ ε d_i d_j.
  -- Since 0 ≤ ε < 1, this immediately weakens to ε/(1-ε) d_i d_j.
  calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
    _ ≤ ε * (d i * d j) := by
        apply mul_le_mul_of_nonneg_left (hCS i j) hε
    _ ≤ ε / (1 - ε) * (d i * d j) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (hd i) (hd j))
        rw [le_div_iff₀ h1_ε_pos]
        nlinarith [sq_nonneg ε]

/-- **Demmel column norm bound, closed form** (Higham §10.1, Theorem 10.5).

    Instantiates `cholesky_demmel_bound` with the actual computed-factor column
    2-norms `d_i = ‖R̂(:,i)‖₂` and the *proved* Cauchy-Schwarz estimate
    `colNorm_cauchy_schwarz`.  Consequently this depends only on the backward-error
    certificate `CholeskyBackwardError` (Theorem 10.3) and `0 ≤ ε < 1`; the
    Cauchy-Schwarz step is no longer an assumed hypothesis.

      R̂^T R̂ = A + ΔA  with  |ΔA_{ij}| ≤ ε/(1−ε) · d_i · d_j. -/
theorem cholesky_demmel_bound_colNorm (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) (hε_lt : ε < 1)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε / (1 - ε) *
        (colNorm n R_hat i * colNorm n R_hat j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) :=
  cholesky_demmel_bound n A R_hat (colNorm n R_hat)
    (colNorm_nonneg n R_hat) (colNorm_cauchy_schwarz n R_hat) ε hε hε_lt hChol

/-- **Demmel column norm bound (direct form)** (Higham §10.1, Theorem 10.5).

    The direct Cauchy-Schwarz bound without the (1−ε)⁻¹ factor:
      |ΔA_{ij}| ≤ ε · d_i · d_j -/
theorem cholesky_demmel_bound_direct (n : ℕ)
    (A R_hat : Fin n → Fin n → ℝ)
    (d : Fin n → ℝ)
    (hCS : ∀ i j, ∑ k : Fin n, |R_hat k i| * |R_hat k j| ≤ d i * d j)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hChol : CholeskyBackwardError n A R_hat ε) :
    ∃ ΔA : Fin n → Fin n → ℝ,
      (∀ i j, |ΔA i j| ≤ ε * (d i * d j)) ∧
      (∀ i j, ∑ k : Fin n, R_hat k i * R_hat k j = A i j + ΔA i j) := by
  obtain ⟨ΔA, hΔA_bound, hΔA_eq⟩ :=
    cholesky_backward_error_perturbation n A R_hat ε hε hChol
  exact ⟨ΔA, fun i j => by
    calc |ΔA i j| ≤ ε * ∑ k : Fin n, |R_hat k i| * |R_hat k j| := hΔA_bound i j
      _ ≤ ε * (d i * d j) := by
          apply mul_le_mul_of_nonneg_left (hCS i j) hε,
    hΔA_eq⟩

-- ============================================================
-- §10.1  Theorem 10.6: Demmel-Wilkinson scaled error
-- ============================================================

-- Diagonal scaling for SPD matrices: D = diag(a_{ii}^{1/2}), H = D⁻¹AD⁻¹.
-- The scaled matrix H has unit diagonal (h_{ii} = 1) and satisfies
-- κ₂(H) ≤ nκ₂(A) (van der Sluis, Corollary 7.6).
-- We represent D as a vector of positive reals. The scaling is passed as
-- a hypothesis `hDHD` rather than computed, avoiding the need for Real.sqrt.

/-- **Abstract Demmel-Wilkinson scaled forward-error interface**
    (Higham §10.1, Theorem 10.6).

    Let A = DHD where D = diag(a_{ii}^{1/2}). Then:
      ‖D⁻¹(x − x̂)‖₂ / ‖D⁻¹x‖₂ ≤ f(n) · κ₂(H) · u

    where f(n) = 2n(1 − γ_{n+1})⁻¹ γ_{n+1}.

    This bound replaces κ₂(A) with the potentially much smaller κ₂(H),
    which captures only the "intrinsic" conditioning, not bad scaling.

    We formalize this with κ₂(H) as a hypothesis. The proof combines
    Theorem 10.5's dd^T bound with the scaling D:
    - |ΔA₁| ≤ (1−γ)⁻¹ γ dd^T (factorization, from Theorem 10.5)
    - |ΔA₂| ≤ diag(γ_i) |R̂^T| (forward sub)
    - |ΔA₃| ≤ diag(γ_{n-i+1}) |R̂| (back sub)
    - Scaling: D⁻¹ dd^T D⁻¹ = ee^T where e_i = d_i/√(a_{ii})
    - ‖D⁻¹ dd^T D⁻¹‖₂ ≤ n (since d_i² ≤ a_{ii}/(1−γ))

    The hypothesis `hscaled_err` supplies this combined perturbation/scaling
    argument; the theorem records the reusable named contract. -/
theorem cholesky_scaled_forward_error (n : ℕ) (_fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ)
    (κH f_n : ℝ)
    -- Scaled error hypothesis: combines perturbation theory with
    -- the Demmel dd^T bound. This is the core inequality from the proof.
    (hscaled_err : ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * _fp.u * (|x i| / D i)) :
    -- The conclusion: scaled error is bounded by f(n) κ₂(H) u
    ∀ (x x_hat : Fin n → ℝ),
      (∀ i, ∑ j : Fin n, A i j * x j = ∑ j : Fin n, A i j * x_hat j) →
      ∀ i, |x i - x_hat i| / D i ≤ f_n * κH * _fp.u * (|x i| / D i) :=
  hscaled_err

-- ============================================================
-- §10.1  Theorem 10.7: Cholesky success condition
-- ============================================================

/-- **Cholesky success-condition threshold consequence**
    (Higham §10.1, Theorem 10.7).

    Let A = DHD where D = diag(a_{ii}^{1/2}).
    - If lam_min(H) > nγ_{n+1}/(1−γ_{n+1}), then Cholesky succeeds.
    - If lam_min(H) < −nγ_{n+1}/(1−γ_{n+1}), then Cholesky fails.

    The threshold nγ_{n+1}/(1−γ_{n+1}) arises because Theorem 10.5 shows
    the backward error satisfies D⁻¹ΔAD⁻¹ ≤ n·γ_{n+1}/(1−γ_{n+1}) · I
    (using ‖ee^T‖₂ = n and d_i²/a_{ii} ≤ 1/(1−γ_{n+1})).

    If the minimum eigenvalue of H exceeds this threshold, then
    H + D⁻¹ΔAD⁻¹ is positive definite, ensuring the factorization
    of A + ΔA = D(H + D⁻¹ΔAD⁻¹)D succeeds.

    This theorem formalizes the sign consequence of the Higham threshold:
    the full spectral success theorem is represented by the eigenvalue-bound
    hypotheses rather than derived from a concrete factorization loop. -/
theorem cholesky_success_condition (n : ℕ) (fp : FPModel)
    (A : Fin n → Fin n → ℝ)
    (D : Fin n → ℝ) (H : Fin n → Fin n → ℝ)
    (_hD_pos : ∀ i : Fin n, 0 < D i)
    (_hDHD : ∀ i j : Fin n, A i j = D i * H i j * D j)
    (lam_min : ℝ)
    (_hH_diag : ∀ i : Fin n, H i i = 1)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    -- The eigenvalue condition: lam_min(H) > threshold
    (hlam_min : lam_min > ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))
    -- This minimum eigenvalue is a true lower bound on the spectrum
    (_hLam_bound : ∀ x : Fin n → ℝ,
      (∃ i, x i ≠ 0) →
      lam_min * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) :
    -- Conclusion: the threshold is positive, confirming success is possible
    0 < lam_min := by
  have hγ_nn : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1_γ_pos : (0 : ℝ) < 1 - gamma fp (n + 1) := by linarith
  have h_threshold_nn : 0 ≤ ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg n) hγ_nn
    · linarith
  linarith

/-- **Cholesky failure-condition threshold consequence**
    (Higham §10.1, Theorem 10.7, second part).

    This theorem formalizes the sign consequence `lam_min < 0`; the full
    algorithmic failure result is not derived here from a concrete Cholesky
    execution. -/
theorem cholesky_failure_condition (n : ℕ) (fp : FPModel)
    (lam_min : ℝ)
    (hn1 : gammaValid fp (n + 1))
    (hγ_lt : gamma fp (n + 1) < 1)
    (hLam_neg : lam_min < -(↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)))) :
    lam_min < 0 := by
  have hγ_nn : 0 ≤ gamma fp (n + 1) := gamma_nonneg fp hn1
  have h1_γ_pos : (0 : ℝ) < 1 - gamma fp (n + 1) := by linarith
  have h_threshold_nn : 0 ≤ ↑n * gamma fp (n + 1) / (1 - gamma fp (n + 1)) := by
    apply div_nonneg
    · exact mul_nonneg (Nat.cast_nonneg n) hγ_nn
    · linarith
  linarith

-- ============================================================
-- §10.1  Theorem 10.7: min-eigenvalue → positive definiteness
--        (genuine spectral-perturbation core, Rayleigh-quotient form)
-- ============================================================

/-- Sum of squares is strictly positive when some coordinate is nonzero. -/
lemma sum_sq_pos_of_exists_ne (n : ℕ) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    0 < ∑ i : Fin n, x i ^ 2 := by
  obtain ⟨i, hi⟩ := hx
  refine Finset.sum_pos' (fun k _ => sq_nonneg (x k)) ?_
  exact ⟨i, Finset.mem_univ i, (sq_nonneg (x i)).lt_of_ne (Ne.symm (pow_ne_zero 2 hi))⟩

/-- **Perturbed positive definiteness via quadratic forms**
    (Higham §10.1, Theorem 10.7 spectral core; "min-eigenvalue → PD").

    If the symmetric quadratic form of `H` is bounded below by `lam‖x‖²`
    (Rayleigh lower bound: `lam` is a lower bound on the spectrum of `H`),
    and the symmetric perturbation `E` has quadratic form bounded by
    `t‖x‖²` in absolute value (so `‖E‖₂ ≤ t` in the spectral sense),
    then for `t < lam` the quadratic form of `H + E` is strictly positive
    on nonzero vectors, i.e. `H + E` is positive definite.

    This is the eigenvalue-perturbation step underlying Cholesky's success
    condition and is stated with quadratic-form bounds so it needs no
    eigenvalue-decomposition machinery. -/
theorem quadForm_add_pos_of_perturbation (n : ℕ)
    (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hlam : ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        lam * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        0 < ∑ i : Fin n, ∑ j : Fin n, x i * (H i j + E i j) * x j := by
  intro x hx
  have hS : 0 < ∑ i : Fin n, x i ^ 2 := sum_sq_pos_of_exists_ne n x hx
  have hsplit : ∑ i : Fin n, ∑ j : Fin n, x i * (H i j + E i j) * x j
      = (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
        + (∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hH := hlam x hx
  have hE_lb : -(t * ∑ i : Fin n, x i ^ 2)
      ≤ ∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j := (abs_le.mp (hE x)).1
  have hpos : 0 < (lam - t) * (∑ i : Fin n, x i ^ 2) := mul_pos (by linarith) hS
  rw [hsplit]
  nlinarith [hH, hE_lb, hpos]

/-- **Congruence by a positive diagonal preserves positive definiteness.**

    If `M` is symmetric positive definite and `D` has strictly positive
    entries, then `D M D` (entrywise `D_i M_{ij} D_j`) is symmetric positive
    definite. This is the scaling step `A = D H D` used throughout §10.1. -/
theorem isSymPosDef_diagCongr (n : ℕ) (D : Fin n → ℝ) (M : Fin n → Fin n → ℝ)
    (hD : ∀ i, 0 < D i) (hM : IsSymPosDef n M) :
    IsSymPosDef n (fun i j => D i * M i j * D j) := by
  refine ⟨?_, ?_⟩
  · intro i j
    show D i * M i j * D j = D j * M j i * D i
    rw [hM.1 i j]; ring
  · intro y hy
    obtain ⟨i, hi⟩ := hy
    have hz : ∃ k, (fun k => D k * y k) k ≠ 0 :=
      ⟨i, by simpa using mul_ne_zero (ne_of_gt (hD i)) hi⟩
    have hpos := hM.2 (fun k => D k * y k) hz
    show 0 < ∑ p : Fin n, ∑ q : Fin n, y p * (D p * M p q * D q) * y q
    have heq : ∑ p : Fin n, ∑ q : Fin n, y p * (D p * M p q * D q) * y q
        = ∑ p : Fin n, ∑ q : Fin n, (D p * y p) * M p q * (D q * y q) := by
      refine Finset.sum_congr rfl (fun p _ => ?_)
      exact Finset.sum_congr rfl (fun q _ => by ring)
    rw [heq]; exact hpos

/-- **Cholesky success under a scaled spectral gap** (Higham §10.1, Theorem 10.7).

    Let `A + ΔA = D (H + E) D` be the scaled, perturbed matrix, where `D`
    is the positive diagonal scaling, `H` is the scaled matrix with
    Rayleigh lower bound `lam`, and `E = D⁻¹ ΔA D⁻¹` is the scaled backward
    error with quadratic form bounded by `t‖x‖²`. If the spectral gap
    `t < lam` holds, then the perturbed scaled matrix is SPD and therefore
    has a genuine Cholesky factorization: the algorithm succeeds.

    This closes the "min-eigenvalue → PD" step of Theorem 10.7 as an honest
    theorem (previously only the sign consequence `0 < lam_min` was proved).
    The remaining upstream obligation is the derivation of the concrete
    threshold `t = n γ_{n+1}/(1-γ_{n+1})` from the componentwise backward
    error, which is supplied here as the hypothesis `hE`. -/
theorem cholesky_succeeds_of_scaled_perturbation (n : ℕ)
    (D : Fin n → ℝ) (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hD_pos : ∀ i, 0 < D i)
    (hH_sym : ∀ i j, H i j = H j i)
    (hE_sym : ∀ i j, E i j = E j i)
    (hlam : ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
        lam * ∑ i : Fin n, x i ^ 2 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : t < lam) :
    ∃ R : Fin n → Fin n → ℝ,
      CholeskyFactSpec n (fun i j => D i * (H i j + E i j) * D j) R := by
  have hHE_spd : IsSymPosDef n (fun i j => H i j + E i j) := by
    refine ⟨fun i j => ?_, ?_⟩
    · show H i j + E i j = H j i + E j i
      rw [hH_sym i j, hE_sym i j]
    exact quadForm_add_pos_of_perturbation n H E lam t hlam hE hlt
  have hDHED_spd : IsSymPosDef n (fun i j => D i * (H i j + E i j) * D j) :=
    isSymPosDef_diagCongr n D (fun i j => H i j + E i j) hD_pos hHE_spd
  exact cholesky_existence n _ hDHED_spd

-- ============================================================
-- §10.1  Theorem 10.7: failure direction (negative curvature)
-- ============================================================

/-- The quadratic form of a matrix admitting a Cholesky factorization
    `A = R^T R` equals `∑_k (∑_i R_{ki} x_i)²`. -/
theorem cholesky_quadForm_eq_sq_sum (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (hR : CholeskyFactSpec n A R) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      = ∑ k : Fin n, (∑ i : Fin n, R k i * x i) ^ 2 := by
  have hLHS : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (R k i * x i) * (R k j * x j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hR.product_eq i j, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have hRHS : ∑ k : Fin n, (∑ i : Fin n, R k i * x i) ^ 2
      = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n,
          (R k i * x i) * (R k j * x j) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [sq, Finset.sum_mul_sum]
  rw [hLHS, hRHS]
  calc ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (R k i * x i) * (R k j * x j)
      = ∑ i : Fin n, ∑ k : Fin n, ∑ j : Fin n, (R k i * x i) * (R k j * x j) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
    _ = ∑ k : Fin n, ∑ i : Fin n, ∑ j : Fin n, (R k i * x i) * (R k j * x j) :=
        Finset.sum_comm

/-- A matrix admitting a Cholesky factorization has nonnegative quadratic form
    (it is positive semidefinite): `0 ≤ xᵀ A x`. -/
theorem cholesky_quadForm_nonneg (n : ℕ) (A R : Fin n → Fin n → ℝ)
    (hR : CholeskyFactSpec n A R) (x : Fin n → ℝ) :
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  rw [cholesky_quadForm_eq_sq_sum n A R hR x]
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

/-- If some direction has strictly negative quadratic form, then `A` has no
    Cholesky factorization — the Cholesky algorithm cannot succeed. -/
theorem no_choleskyFactSpec_of_neg_quadForm (n : ℕ) (A : Fin n → Fin n → ℝ)
    (x : Fin n → ℝ)
    (hneg : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j < 0) :
    ¬ ∃ R : Fin n → Fin n → ℝ, CholeskyFactSpec n A R := by
  rintro ⟨R, hR⟩
  exact absurd (cholesky_quadForm_nonneg n A R hR x) (not_le.mpr hneg)

/-- **Perturbed negative curvature via quadratic forms**
    (Higham §10.1, Theorem 10.7 failure core).

    If `H` has a direction whose quadratic form is at most `lam‖x‖²`
    (a Rayleigh upper witness for the minimum eigenvalue), and the symmetric
    perturbation `E` has quadratic form bounded by `t‖x‖²`, then for
    `lam < -t` there is a direction on which `H + E` has strictly negative
    quadratic form: `H + E` is not positive definite. -/
theorem quadForm_add_neg_of_perturbation (n : ℕ)
    (H E : Fin n → Fin n → ℝ) (lam t : ℝ)
    (hlam_dir : ∃ x : Fin n → ℝ, (∃ i, x i ≠ 0) ∧
        (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j) ≤ lam * ∑ i : Fin n, x i ^ 2)
    (hE : ∀ x : Fin n → ℝ,
        |∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j| ≤ t * ∑ i : Fin n, x i ^ 2)
    (hlt : lam < -t) :
    ∃ x : Fin n → ℝ, (∃ i, x i ≠ 0) ∧
        ∑ i : Fin n, ∑ j : Fin n, x i * (H i j + E i j) * x j < 0 := by
  obtain ⟨x, hx_ne, hHle⟩ := hlam_dir
  refine ⟨x, hx_ne, ?_⟩
  have hS : 0 < ∑ i : Fin n, x i ^ 2 := sum_sq_pos_of_exists_ne n x hx_ne
  have hsplit : ∑ i : Fin n, ∑ j : Fin n, x i * (H i j + E i j) * x j
      = (∑ i : Fin n, ∑ j : Fin n, x i * H i j * x j)
        + (∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hE_ub : ∑ i : Fin n, ∑ j : Fin n, x i * E i j * x j
      ≤ t * ∑ i : Fin n, x i ^ 2 := (abs_le.mp (hE x)).2
  have hneg : 0 < (-(lam + t)) * (∑ i : Fin n, x i ^ 2) := mul_pos (by linarith) hS
  rw [hsplit]
  nlinarith [hHle, hE_ub, hneg]

-- ============================================================
-- §10.1  Algorithm 10.2 / Theorem 10.3 foundation:
--        computed-diagonal (square-root) backward error
-- ============================================================

/-- **Computed Cholesky diagonal-pivot backward error** (Higham §10.1,
    foundation for Algorithm 10.2 / Theorem 10.3).

    Each Cholesky diagonal entry is `r̂_{jj} = fl(√s)` for a nonnegative
    partial pivot `s = a_{jj} − ∑_{k<j} r̂_{kj}²`. Squaring the rounded
    square root recovers `s` with a first-order relative error:
    `r̂_{jj}² = s·(1 + η)` with `|η| ≤ 2u + u²`.

    This is the scalar rounding fact underlying the diagonal recurrence of
    the concrete floating-point Cholesky factorization; it depends only on
    the standard `model_sqrt` and `(√s)² = s` for `s ≥ 0`. -/
theorem fl_sqrt_sq_backward_error (fp : FPModel) (s : ℝ) (hs : 0 ≤ s) :
    ∃ η : ℝ, |η| ≤ 2 * fp.u + fp.u ^ 2 ∧ (fp.fl_sqrt s) ^ 2 = s * (1 + η) := by
  obtain ⟨δ, hδ, heq⟩ := fp.model_sqrt s hs
  refine ⟨2 * δ + δ ^ 2, ?_, ?_⟩
  · rw [abs_le] at hδ ⊢
    constructor <;> nlinarith [hδ.1, hδ.2, sq_nonneg δ, sq_nonneg fp.u]
  · rw [heq, mul_pow, Real.sq_sqrt hs]; ring

/-- **Computed Cholesky diagonal-pivot backward error, `γ₂` form.**

    Restates `fl_sqrt_sq_backward_error` with the certificate-compatible
    bound `|η| ≤ γ₂ = 2u/(1−2u)`, valid whenever `gammaValid fp 2`. -/
theorem fl_sqrt_sq_backward_error_gamma (fp : FPModel) (s : ℝ) (hs : 0 ≤ s)
    (h2 : gammaValid fp 2) :
    ∃ η : ℝ, |η| ≤ gamma fp 2 ∧ (fp.fl_sqrt s) ^ 2 = s * (1 + η) := by
  obtain ⟨η, hη, heq⟩ := fl_sqrt_sq_backward_error fp s hs
  refine ⟨η, le_trans hη ?_, heq⟩
  have hu : 0 ≤ fp.u := fp.u_nonneg
  have hden : 0 < 1 - 2 * fp.u := by
    unfold gammaValid at h2; push_cast at h2; linarith
  unfold gamma
  push_cast
  rw [le_div_iff₀ hden]
  nlinarith [hu, sq_nonneg fp.u, mul_nonneg (mul_nonneg hu hu) hu]

end NumStability
