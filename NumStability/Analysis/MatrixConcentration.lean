-- Analysis/MatrixConcentration.lean
--
-- Generic finite-dimensional trace-exponential interfaces for future matrix
-- concentration arguments.

import NumStability.Analysis.FiniteProbability
import NumStability.Analysis.MatrixSpectral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace NumStability

open scoped BigOperators

/-- Algebraic tail-budget simplification used by two-sided trace-exponential
    high-probability bounds.  Choosing `T = log (2 B / δ)` makes the two equal
    failure terms `exp (-T) B` sum to exactly `δ`. -/
lemma real_exp_neg_log_two_mul_div_mul_self_add
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) :
    Real.exp (-Real.log ((2 * B) / δ)) * B +
      Real.exp (-Real.log ((2 * B) / δ)) * B = δ := by
  have hx_pos : 0 < (2 * B) / δ := by
    exact div_pos (mul_pos (by norm_num) hB) hδ
  calc
    Real.exp (-Real.log ((2 * B) / δ)) * B +
        Real.exp (-Real.log ((2 * B) / δ)) * B
        = ((2 * B) / δ)⁻¹ * B + ((2 * B) / δ)⁻¹ * B := by
            rw [Real.exp_neg, Real.exp_log hx_pos]
    _ = δ := by
            field_simp [hB.ne', hδ.ne']
            ring

/-- Positivity of the logarithmic radius used to make
`B * exp (-(B * t^2 / 8))` equal to a target failure budget `δ`.

This is the scalar preprocessing-budget choice for the SRHT row-norm tail. -/
lemma real_sqrt_eight_log_div_pos_of_pos_lt
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδB : δ < B) :
    0 < Real.sqrt (8 * Real.log (B / δ) / B) := by
  have hratio_gt_one : 1 < B / δ := by
    rw [lt_div_iff₀ hδ]
    simpa [one_mul] using hδB
  have hlog_pos : 0 < Real.log (B / δ) :=
    Real.log_pos hratio_gt_one
  have harg_pos : 0 < 8 * Real.log (B / δ) / B := by
    positivity
  exact Real.sqrt_pos.2 harg_pos

/-- Exact logarithmic simplification of the SRHT preprocessing failure budget.

Choosing
\[
  t=\sqrt{\frac{8\log(B/\delta)}{B}}
\]
makes `B * exp (-(B * t^2 / 8)) = δ`, assuming `0 < δ < B`. -/
lemma real_mul_exp_neg_mul_sqrt_eight_log_div_sq_div_eight_eq
    {B δ : ℝ} (hB : 0 < B) (hδ : 0 < δ) (hδB : δ < B) :
    B * Real.exp
        (-(B * (Real.sqrt (8 * Real.log (B / δ) / B)) ^ 2 / 8)) = δ := by
  have hratio_pos : 0 < B / δ := div_pos hB hδ
  have hratio_gt_one : 1 < B / δ := by
    rw [lt_div_iff₀ hδ]
    simpa [one_mul] using hδB
  have hlog_pos : 0 < Real.log (B / δ) :=
    Real.log_pos hratio_gt_one
  have harg_nonneg : 0 ≤ 8 * Real.log (B / δ) / B := by
    positivity
  have hsqrt_sq :
      (Real.sqrt (8 * Real.log (B / δ) / B)) ^ 2 =
        8 * Real.log (B / δ) / B :=
    Real.sq_sqrt harg_nonneg
  calc
    B * Real.exp
        (-(B * (Real.sqrt (8 * Real.log (B / δ) / B)) ^ 2 / 8))
        = B * Real.exp (-(B * (8 * Real.log (B / δ) / B) / 8)) := by
            rw [hsqrt_sq]
    _ = B * Real.exp (-Real.log (B / δ)) := by
            congr 1
            field_simp [hB.ne']
    _ = δ := by
            rw [Real.exp_neg, Real.exp_log hratio_pos]
            field_simp [hB.ne', hδ.ne']

/-- Exact scalar Bennett optimization for the trace-exponential radius.

If a tail bound has radius
`(q + W * beta theta) / theta`, with
`beta theta = (exp (theta * L) - theta * L - 1) / L^2`, then the usual
choice `theta = log (1 + L*r/W) / L` makes that radius at most `r` whenever
`q` is bounded by the Bennett transform
`(W/L^2) * ((1 + L*r/W) * log (1 + L*r/W) - L*r/W)`.

This is a scalar algebra lemma: it does not assume or prove any probability
statement.  It is used after the matrix trace-MGF theorem has already supplied
the high-probability event. -/
theorem real_bernstein_exact_radius_le_of_log_le
    {q W L r : ℝ} (hL : 0 < L) (hW : 0 < W) (hr : 0 < r)
    (hq : q ≤ (W / L ^ 2) *
      ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
        (L * r / W))) :
    let theta : ℝ := Real.log (1 + L * r / W) / L
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    (q + W * beta) / theta ≤ r := by
  intro theta beta
  have harg_pos : 0 < 1 + L * r / W := by positivity
  have harg_gt_one : 1 < 1 + L * r / W := by
    have hpos : 0 < L * r / W := by positivity
    linarith
  have hlog_pos : 0 < Real.log (1 + L * r / W) :=
    Real.log_pos harg_gt_one
  have htheta_pos : 0 < theta := by
    dsimp [theta]
    positivity
  have htheta_mul_L :
      theta * L = Real.log (1 + L * r / W) := by
    dsimp [theta]
    field_simp [hL.ne']
  have hexp : Real.exp (theta * L) = 1 + L * r / W := by
    rw [htheta_mul_L, Real.exp_log harg_pos]
  have hqbeta : q + W * beta ≤ theta * r := by
    calc
      q + W * beta ≤
          (W / L ^ 2) *
            ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
              (L * r / W)) + W * beta := by
            linarith
      _ = theta * r := by
            dsimp [beta]
            rw [hexp, htheta_mul_L]
            rw [show theta = Real.log (1 + L * r / W) / L by rfl]
            field_simp [hL.ne', hW.ne']
            ring
  exact (div_le_iff₀ htheta_pos).mpr (by simpa [mul_comm] using hqbeta)

/-- Elementary conservative lower bound for Bennett's scalar transform.

For `x >= 0`,
`(1 + x) log (1 + x) - x` dominates `x^2 / (2 + x)`.  This is weaker than
the sharp Bernstein denominator `2 + 2*x/3`, but it is fully proved from
mathlib's logarithm lower bound and is useful as a no-hidden-assumption bridge
from explicit sample-size denominators to the Bennett budget. -/
theorem real_bennett_transform_lower_bound_two_add
    {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / (2 + x) ≤ (1 + x) * Real.log (1 + x) - x := by
  let y : ℝ := x / (2 + x)
  have hden_pos : 0 < 2 + x := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_lt_one : y < 1 := by
    dsimp [y]
    exact (div_lt_one hden_pos).mpr (by linarith)
  have hlog_series := Real.sum_range_le_log_div hy_nonneg hy_lt_one 1
  have hlog_y :
      2 * y ≤ Real.log ((1 + y) / (1 - y)) := by
    have hsum : (∑ i ∈ Finset.range 1, y ^ (2 * i + 1) / (2 * i + 1)) = y := by
      simp
    have hhalf :
        y ≤ (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)) := by
      simpa [hsum] using hlog_series
    nlinarith
  have hratio : (1 + y) / (1 - y) = 1 + x := by
    dsimp [y]
    field_simp [hden_pos.ne']
    ring
  have hlog :
      2 * x / (2 + x) ≤ Real.log (1 + x) := by
    have hy_eq : 2 * y = 2 * x / (2 + x) := by
      dsimp [y]
      ring
    simpa [hratio, hy_eq] using hlog_y
  have hmul :
      (1 + x) * (2 * x / (2 + x)) ≤
        (1 + x) * Real.log (1 + x) := by
    exact mul_le_mul_of_nonneg_left hlog (by linarith)
  have halg :
      (1 + x) * (2 * x / (2 + x)) - x = x ^ 2 / (2 + x) := by
    field_simp [hden_pos.ne']
    ring
  calc
    x ^ 2 / (2 + x)
        = (1 + x) * (2 * x / (2 + x)) - x := halg.symm
    _ ≤ (1 + x) * Real.log (1 + x) - x := sub_le_sub_right hmul x

/-- Conservative Bernstein-style sufficient condition for the exact Bennett
budget.

If the logarithmic tail budget `q` is at most `r^2 / (2W + Lr)`, then it is
also at most Bennett's optimized transform.  The sharper source denominator
`2W + (2/3)Lr` remains a separate bottleneck; this lemma closes the weaker
fully formalized bridge needed by fallback sample-size corollaries. -/
theorem real_bennett_budget_of_quadratic_denominator_two_add
    {q W L r : ℝ} (hL : 0 < L) (hW : 0 < W) (hr : 0 < r)
    (hq : q ≤ r ^ 2 / (2 * W + L * r)) :
    q ≤ (W / L ^ 2) *
      ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
        (L * r / W)) := by
  let x : ℝ := L * r / W
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hscale_nonneg : 0 ≤ W / L ^ 2 := by
    positivity
  have hlower := real_bennett_transform_lower_bound_two_add hx_nonneg
  have hscaled :
      (W / L ^ 2) * (x ^ 2 / (2 + x)) ≤
        (W / L ^ 2) *
          ((1 + x) * Real.log (1 + x) - x) :=
    mul_le_mul_of_nonneg_left hlower hscale_nonneg
  have hden_pos : 0 < 2 * W + L * r := by positivity
  have heq :
      (W / L ^ 2) * (x ^ 2 / (2 + x)) =
        r ^ 2 / (2 * W + L * r) := by
    dsimp [x]
    field_simp [hL.ne', hW.ne', hden_pos.ne']
  calc
    q ≤ r ^ 2 / (2 * W + L * r) := hq
    _ = (W / L ^ 2) * (x ^ 2 / (2 + x)) := heq.symm
    _ ≤ (W / L ^ 2) *
        ((1 + x) * Real.log (1 + x) - x) := hscaled
    _ = (W / L ^ 2) *
        ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
          (L * r / W)) := by
          simp [x]

/-- Sharp Bernstein-denominator lower bound for Bennett's scalar transform.

For `x >= 0`,
`(1 + x) log (1 + x) - x` dominates `x^2 / (2 + (2/3) x)`.  The proof uses
the first two positive terms in mathlib's logarithm series lower bound after
the substitution `y = x/(2+x)`, so no calculus or external analytic
assumption is hidden here. -/
theorem real_bennett_transform_lower_bound_two_add_two_thirds
    {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / (2 + (2 / 3) * x) ≤ (1 + x) * Real.log (1 + x) - x := by
  let y : ℝ := x / (2 + x)
  have hden_pos : 0 < 2 + x := by linarith
  have hy_nonneg : 0 ≤ y := by
    dsimp [y]
    positivity
  have hy_lt_one : y < 1 := by
    dsimp [y]
    exact (div_lt_one hden_pos).mpr (by linarith)
  have hlog_series := Real.sum_range_le_log_div hy_nonneg hy_lt_one 2
  have hsum :
      (∑ i ∈ Finset.range 2, y ^ (2 * i + 1) / (2 * i + 1)) =
        y + y ^ 3 / 3 := by
    norm_num [Finset.sum_range_succ, pow_succ]
  have hlog_y :
      2 * (y + y ^ 3 / 3) ≤ Real.log ((1 + y) / (1 - y)) := by
    have hhalf :
        y + y ^ 3 / 3 ≤
          (1 / 2 : ℝ) * Real.log ((1 + y) / (1 - y)) := by
      simpa [hsum] using hlog_series
    nlinarith
  have hratio : (1 + y) / (1 - y) = 1 + x := by
    dsimp [y]
    field_simp [hden_pos.ne']
    ring
  have hlog :
      2 * (y + y ^ 3 / 3) ≤ Real.log (1 + x) := by
    simpa [hratio] using hlog_y
  have hmul :
      (1 + x) * (2 * (y + y ^ 3 / 3)) ≤
        (1 + x) * Real.log (1 + x) := by
    exact mul_le_mul_of_nonneg_left hlog (by linarith)
  have hden2_pos : 0 < 2 + (2 / 3 : ℝ) * x := by positivity
  have halg :
      x ^ 2 / (2 + (2 / 3 : ℝ) * x) ≤
        (1 + x) * (2 * (y + y ^ 3 / 3)) - x := by
    rw [← sub_nonneg]
    have hdiff :
        (1 + x) * (2 * (y + y ^ 3 / 3)) - x -
            x ^ 2 / (2 + (2 / 3 : ℝ) * x) =
          x ^ 4 * (x + 4) / (6 * (2 + x) ^ 3 * (x + 3)) := by
      dsimp [y]
      field_simp [hden_pos.ne', hden2_pos.ne']
      ring
    rw [hdiff]
    positivity
  exact halg.trans (sub_le_sub_right hmul x)

/-- Sharp Bernstein-denominator sufficient condition for the exact Bennett
budget.

If the logarithmic tail budget `q` is at most
`r^2 / (2W + (2/3)Lr)`, then it is also at most Bennett's optimized transform.
This is the scalar denominator used by the Drineas--Zouzias/CACM final
constant simplification. -/
theorem real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
    {q W L r : ℝ} (hL : 0 < L) (hW : 0 < W) (hr : 0 < r)
    (hq : q ≤ r ^ 2 / (2 * W + (2 / 3) * L * r)) :
    q ≤ (W / L ^ 2) *
      ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
        (L * r / W)) := by
  let x : ℝ := L * r / W
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    positivity
  have hscale_nonneg : 0 ≤ W / L ^ 2 := by
    positivity
  have hlower := real_bennett_transform_lower_bound_two_add_two_thirds hx_nonneg
  have hscaled :
      (W / L ^ 2) * (x ^ 2 / (2 + (2 / 3) * x)) ≤
        (W / L ^ 2) *
          ((1 + x) * Real.log (1 + x) - x) :=
    mul_le_mul_of_nonneg_left hlower hscale_nonneg
  have hden_pos : 0 < 2 * W + (2 / 3 : ℝ) * L * r := by positivity
  have heq :
      (W / L ^ 2) * (x ^ 2 / (2 + (2 / 3) * x)) =
        r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    dsimp [x]
    field_simp [hL.ne', hW.ne', hden_pos.ne']
  calc
    q ≤ r ^ 2 / (2 * W + (2 / 3) * L * r) := hq
    _ = (W / L ^ 2) * (x ^ 2 / (2 + (2 / 3) * x)) := heq.symm
    _ ≤ (W / L ^ 2) *
        ((1 + x) * Real.log (1 + x) - x) := hscaled
    _ = (W / L ^ 2) *
        ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
          (L * r / W)) := by
          simp [x]

/-- Scalar tail-budget form of the Bernstein/Bennett optimization.

If the sample budget implies
`log (2B/δ) / s <= r^2 / (2W+(2/3)Lr)`, then the standard optimized choice
`theta = log (1+Lr/W)/L` makes the corresponding one-sided trace-exponential
tail at most `δ/2`.  This lemma is purely real algebra; the matrix probability
theorem supplies the tail expression separately. -/
theorem real_bernstein_tail_le_half_delta_of_quadratic_budget
    {B W L r s δ : ℝ}
    (hB : 0 < B) (hW : 0 < W) (hL : 0 < L) (hr : 0 < r)
    (hs : 0 < s) (hδ : 0 < δ)
    (hbudget :
      Real.log ((2 * B) / δ) ≤
        s * (r ^ 2 / (2 * W + (2 / 3) * L * r))) :
    let theta : ℝ := Real.log (1 + L * r / W) / L
    let beta : ℝ := (Real.exp (theta * L) - theta * L - 1) / L ^ 2
    Real.exp (-(theta * s * r)) *
        (B * Real.exp (s * (beta * W))) ≤ δ / 2 := by
  intro theta beta
  let q : ℝ := Real.log ((2 * B) / δ)
  have hbudget_div :
      q ≤ s * (r ^ 2 / (2 * W + (2 / 3) * L * r)) := by
    simpa [q] using hbudget
  have hq_div :
      q / s ≤ r ^ 2 / (2 * W + (2 / 3) * L * r) := by
    exact (div_le_iff₀ hs).mpr (by simpa [mul_comm] using hbudget_div)
  have hbennett :
      q / s ≤
        (W / L ^ 2) *
          ((1 + (L * r / W)) * Real.log (1 + (L * r / W)) -
            (L * r / W)) :=
    real_bennett_budget_of_quadratic_denominator_two_add_two_thirds
      hL hW hr hq_div
  have htheta_pos : 0 < theta := by
    have hquot : 0 < L * r / W := by positivity
    have harg : 1 < 1 + L * r / W := by linarith
    dsimp [theta]
    exact div_pos (Real.log_pos harg) hL
  have hradius :
      (q / s + W * beta) / theta ≤ r := by
    simpa [q, theta, beta] using
      real_bernstein_exact_radius_le_of_log_le
        hL hW hr hbennett
  have hcore : q / s + W * beta ≤ theta * r := by
    simpa [mul_comm] using (div_le_iff₀ htheta_pos).mp hradius
  have hmul_radius :
      q + s * (W * beta) ≤ theta * s * r := by
    have hmul :
        s * (q / s + W * beta) ≤ s * (theta * r) :=
      mul_le_mul_of_nonneg_left hcore (le_of_lt hs)
    have hleft :
        s * (q / s + W * beta) = q + s * (W * beta) := by
      field_simp [ne_of_gt hs]
    have hright : s * (theta * r) = theta * s * r := by ring
    simpa [hleft, hright]
      using hmul
  have hexp_arg :
      -(theta * s * r) + s * (beta * W) ≤ -q := by
    have hrewrite :
        s * (beta * W) = s * (W * beta) := by ring
    rw [hrewrite]
    linarith
  have htail :
      Real.exp (-(theta * s * r)) *
          (B * Real.exp (s * (beta * W))) ≤ B * Real.exp (-q) := by
    calc
      Real.exp (-(theta * s * r)) *
          (B * Real.exp (s * (beta * W)))
          = B *
              (Real.exp (-(theta * s * r)) *
                Real.exp (s * (beta * W))) := by ring
      _ = B * Real.exp (-(theta * s * r) + s * (beta * W)) := by
              rw [Real.exp_add]
      _ ≤ B * Real.exp (-q) := by
              exact mul_le_mul_of_nonneg_left
                (Real.exp_le_exp.mpr hexp_arg) (le_of_lt hB)
  have hq_pos : 0 < (2 * B) / δ :=
    div_pos (mul_pos (by norm_num) hB) hδ
  have hhalf : B * Real.exp (-q) = δ / 2 := by
    dsimp [q]
    rw [Real.exp_neg, Real.exp_log hq_pos]
    field_simp [hB.ne', hδ.ne']
  exact htail.trans_eq hhalf

/-- If one Hermitian eigenvalue of a local finite symmetric matrix is at least
    `T`, then `exp T` is bounded by the trace of the matrix exponential.
    This is the deterministic witness used by trace-exponential tail bounds. -/
theorem exp_le_finiteTrace_finiteMatrixExp_of_finiteHermitianEigenvalue_ge
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : ι) {T : ℝ}
    (hT : T ≤ finiteHermitianEigenvalues M hM a) :
    Real.exp T ≤ finiteTrace (finiteMatrixExp M) := by
  rw [finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues M hM]
  exact le_trans (Real.exp_le_exp.mpr hT)
    (Finset.single_le_sum (fun i _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ a))

/-- The trace of the matrix exponential of a local finite symmetric matrix is
    nonnegative. -/
theorem finiteTrace_finiteMatrixExp_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    0 ≤ finiteTrace (finiteMatrixExp M) := by
  rw [finiteTrace_finiteMatrixExp_eq_sum_exp_finiteHermitianEigenvalues M hM]
  exact Finset.sum_nonneg fun i _ => le_of_lt (Real.exp_pos _)

/-- If one Hermitian eigenvalue of a local finite symmetric matrix is at most
    `T`, then `exp (-T)` is bounded by the trace of the matrix exponential of
    `-M`.  This is the deterministic lower-tail witness for
    trace-exponential concentration arguments. -/
theorem exp_neg_le_finiteTrace_finiteMatrixExp_neg_of_finiteHermitianEigenvalue_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) (a : ι) {T : ℝ}
    (hT : finiteHermitianEigenvalues M hM a ≤ T) :
    Real.exp (-T) ≤ finiteTrace (finiteMatrixExp (fun i j => -M i j)) := by
  rw [finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues M hM]
  exact le_trans (Real.exp_le_exp.mpr (neg_le_neg hT))
    (Finset.single_le_sum
      (fun i _ => le_of_lt (Real.exp_pos (-(finiteHermitianEigenvalues M hM i))))
      (Finset.mem_univ a))

/-- The trace of the matrix exponential of `-M` is nonnegative for a local finite
    symmetric matrix `M`. -/
theorem finiteTrace_finiteMatrixExp_neg_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (hM : IsSymmetricFiniteMatrix M) :
    0 ≤ finiteTrace (finiteMatrixExp (fun i j => -M i j)) := by
  rw [finiteTrace_finiteMatrixExp_neg_eq_sum_exp_neg_finiteHermitianEigenvalues M hM]
  exact Finset.sum_nonneg fun i _ => le_of_lt (Real.exp_pos _)

/-- Exponential-Markov trace tail for a supplied finite family of symmetric
    matrices.  If the random matrix `M ω` has an eigenvalue at least `T`, then
    `exp T <= tr(exp(M ω))`; scalar Markov on this nonnegative trace gives the
    stated probability bound.

    This is a genuine MGF-to-eigenvalue interface, but it is not yet a matrix
    Bernstein theorem: the trace-exponential expectation on the right still has
    to be bounded for the random matrix sum under study. -/
theorem FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T : ℝ) :
    P.eventProb {ω | ∃ a : ι, T ≤ finiteHermitianEigenvalues (M ω) (hM ω) a} ≤
      Real.exp (-T) * P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) := by
  let traceExp : Ω → ℝ := fun ω => finiteTrace (finiteMatrixExp (M ω))
  let eigEvent : Set Ω := {ω | ∃ a : ι, T ≤ finiteHermitianEigenvalues (M ω) (hM ω) a}
  let traceEvent : Set Ω := {ω | Real.exp T ≤ traceExp ω}
  have hsubset : eigEvent ⊆ traceEvent := by
    intro ω hω
    rcases hω with ⟨a, ha⟩
    exact exp_le_finiteTrace_finiteMatrixExp_of_finiteHermitianEigenvalue_ge
      (M ω) (hM ω) a ha
  have hmarkov :=
    P.eventProb_real_ge_le_expectationReal_div traceExp
      (hX := fun ω => finiteTrace_finiteMatrixExp_nonneg (M ω) (hM ω))
      (hT := Real.exp_pos T)
  have hmono := P.eventProb_mono hsubset
  have hdiv :
      P.expectationReal traceExp / Real.exp T =
        Real.exp (-T) * P.expectationReal traceExp := by
    rw [div_eq_mul_inv, ← Real.exp_neg, mul_comm]
  exact le_trans hmono (by simpa [traceEvent, traceExp, hdiv] using hmarkov)

/-- Trace-exponential eigenvalue tail with a supplied scalar bound on the
    trace-MGF.  This is the reusable last-mile form of the Markov interface:
    a future trace-MGF domination theorem can feed the scalar bound `B` here
    without changing the event statement. -/
theorem FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_trace_bound
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T B : ℝ)
    (hTrace :
      P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) ≤ B) :
    P.eventProb {ω | ∃ a : ι, T ≤ finiteHermitianEigenvalues (M ω) (hM ω) a} ≤
      Real.exp (-T) * B := by
  have htail :=
    P.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp
      M hM T
  exact htail.trans
    (mul_le_mul_of_nonneg_left hTrace (le_of_lt (Real.exp_pos _)))

/-- High-probability complement of the trace-exponential eigenvalue tail:
    all named Hermitian eigenvalues are strictly below `T` except with the
    trace-exponential tail probability. -/
theorem FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T : ℝ) :
    1 - Real.exp (-T) *
        P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) ≤
      P.eventProb
        {ω | ∀ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a < T} := by
  classical
  let E : Set Ω :=
    {ω | ∀ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a < T}
  have htail :=
    P.eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp
      M hM T
  have hcompl_subset :
      Eᶜ ⊆
        {ω | ∃ a : ι, T ≤ finiteHermitianEigenvalues (M ω) (hM ω) a} := by
    intro ω hω
    simp [E] at hω
    rcases hω with ⟨a, ha⟩
    exact ⟨a, ha⟩
  have htailE :
      P.eventProb Eᶜ ≤
        Real.exp (-T) *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) :=
    (P.eventProb_mono hcompl_subset).trans htail
  have hsplit := P.eventProb_add_eventProb_compl E
  linarith

/-- High-probability all-eigenvalues-below-threshold form with a supplied
    scalar trace-MGF bound. -/
theorem FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T B : ℝ)
    (hTrace :
      P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) ≤ B) :
    1 - Real.exp (-T) * B ≤
      P.eventProb
        {ω | ∀ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a < T} := by
  have hhp :=
    P.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp
      M hM T
  have hmul :
      Real.exp (-T) *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) ≤
        Real.exp (-T) * B :=
    mul_le_mul_of_nonneg_left hTrace (le_of_lt (Real.exp_pos _))
  linarith

/-- Lower-tail exponential-Markov trace tail for a supplied finite family of
    symmetric matrices.  If the random matrix `M ω` has an eigenvalue at most
    `T`, then `exp (-T) <= tr(exp(-M ω))`; scalar Markov on this nonnegative
    trace gives the stated probability bound.

    This is the lower-tail companion to
    `eventProb_exists_finiteHermitianEigenvalue_ge_le_exp_neg_mul_expected_trace_exp`;
    the trace-exponential expectation on the right is the part that a future
    matrix Bernstein proof has to dominate. -/
theorem FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T : ℝ) :
    P.eventProb {ω | ∃ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a ≤ T} ≤
      Real.exp T *
        P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) := by
  let traceExpNeg : Ω → ℝ :=
    fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))
  let eigEvent : Set Ω := {ω | ∃ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a ≤ T}
  let traceEvent : Set Ω := {ω | Real.exp (-T) ≤ traceExpNeg ω}
  have hsubset : eigEvent ⊆ traceEvent := by
    intro ω hω
    rcases hω with ⟨a, ha⟩
    exact exp_neg_le_finiteTrace_finiteMatrixExp_neg_of_finiteHermitianEigenvalue_le
      (M ω) (hM ω) a ha
  have hmarkov :=
    P.eventProb_real_ge_le_expectationReal_div traceExpNeg
      (hX := fun ω => finiteTrace_finiteMatrixExp_neg_nonneg (M ω) (hM ω))
      (hT := Real.exp_pos (-T))
  have hmono := P.eventProb_mono hsubset
  have hdiv :
      P.expectationReal traceExpNeg / Real.exp (-T) =
        Real.exp T * P.expectationReal traceExpNeg := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg, mul_comm]
  exact le_trans hmono (by simpa [traceEvent, traceExpNeg, hdiv] using hmarkov)

/-- Lower-tail trace-exponential eigenvalue tail with a supplied scalar bound on
    the negative trace-MGF. -/
theorem FiniteProbability.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_trace_bound
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T B : ℝ)
    (hTrace :
      P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) ≤ B) :
    P.eventProb {ω | ∃ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a ≤ T} ≤
      Real.exp T * B := by
  have htail :=
    P.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg
      M hM T
  exact htail.trans
    (mul_le_mul_of_nonneg_left hTrace (le_of_lt (Real.exp_pos _)))

/-- High-probability lower-tail complement: all named Hermitian eigenvalues are
    strictly above `T` except with the negative trace-exponential tail
    probability. -/
theorem FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T : ℝ) :
    1 - Real.exp T *
        P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) ≤
      P.eventProb
        {ω | ∀ a : ι, T < finiteHermitianEigenvalues (M ω) (hM ω) a} := by
  classical
  let E : Set Ω :=
    {ω | ∀ a : ι, T < finiteHermitianEigenvalues (M ω) (hM ω) a}
  have htail :=
    P.eventProb_exists_finiteHermitianEigenvalue_le_le_exp_mul_expected_trace_exp_neg
      M hM T
  have hcompl_subset :
      Eᶜ ⊆
        {ω | ∃ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a ≤ T} := by
    intro ω hω
    simp [E] at hω
    rcases hω with ⟨a, ha⟩
    exact ⟨a, ha⟩
  have htailE :
      P.eventProb Eᶜ ≤
        Real.exp T *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) :=
    (P.eventProb_mono hcompl_subset).trans htail
  have hsplit := P.eventProb_add_eventProb_compl E
  linarith

/-- High-probability all-eigenvalues-above-threshold form with a supplied scalar
    negative trace-MGF bound. -/
theorem FiniteProbability.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_trace_bound
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T B : ℝ)
    (hTrace :
      P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) ≤ B) :
    1 - Real.exp T * B ≤
      P.eventProb
        {ω | ∀ a : ι, T < finiteHermitianEigenvalues (M ω) (hM ω) a} := by
  have hhp :=
    P.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg
      M hM T
  have hmul :
      Real.exp T *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) ≤
        Real.exp T * B :=
    mul_le_mul_of_nonneg_left hTrace (le_of_lt (Real.exp_pos _))
  linarith

/-- Two-sided trace-exponential eigenvalue interface.  Positive and negative
    trace-MGF controls imply a high-probability event where every Hermitian
    eigenvalue has absolute value below `T`.  This is still a final-mile
    interface: a matrix Bernstein proof must supply the two trace-MGF bounds. -/
theorem FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp_add
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T : ℝ) :
    1 - (Real.exp (-T) *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) +
        Real.exp (-T) *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω)))) ≤
      P.eventProb
        {ω | ∀ a : ι, |finiteHermitianEigenvalues (M ω) (hM ω) a| < T} := by
  classical
  let ELower : Set Ω :=
    {ω | ∀ a : ι, -T < finiteHermitianEigenvalues (M ω) (hM ω) a}
  let EUpper : Set Ω :=
    {ω | ∀ a : ι, finiteHermitianEigenvalues (M ω) (hM ω) a < T}
  let EAbs : Set Ω :=
    {ω | ∀ a : ι, |finiteHermitianEigenvalues (M ω) (hM ω) a| < T}
  have hLower :=
    P.eventProb_forall_finiteHermitianEigenvalue_gt_ge_one_sub_exp_mul_expected_trace_exp_neg
      M hM (-T)
  have hUpper :=
    P.eventProb_forall_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp
      M hM T
  have hinter :=
    P.eventProb_inter_ge_one_sub_add ELower EUpper
      (Real.exp (-T) *
        P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))))
      (Real.exp (-T) *
        P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))))
      (by simpa [ELower] using hLower)
      (by simpa [EUpper] using hUpper)
  have hsubset : ELower ∩ EUpper ⊆ EAbs := by
    intro ω hω
    rcases hω with ⟨hlo, hhi⟩
    intro a
    exact abs_lt.mpr ⟨hlo a, hhi a⟩
  exact le_trans (by simpa [ELower, EUpper] using hinter) (P.eventProb_mono hsubset)

/-- Two-sided trace-exponential eigenvalue interface with supplied scalar
    bounds for the positive and negative trace-MGFs. -/
theorem FiniteProbability.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_trace_bound_add
    {Ω ι : Type*} [Fintype Ω] [Fintype ι] [DecidableEq ι]
    (P : FiniteProbability Ω) (M : Ω → ι → ι → ℝ)
    (hM : ∀ ω, IsSymmetricFiniteMatrix (M ω)) (T Bneg Bpos : ℝ)
    (hTraceNeg :
      P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) ≤ Bneg)
    (hTracePos :
      P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) ≤ Bpos) :
    1 - (Real.exp (-T) * Bneg + Real.exp (-T) * Bpos) ≤
      P.eventProb
        {ω | ∀ a : ι, |finiteHermitianEigenvalues (M ω) (hM ω) a| < T} := by
  have hhp :=
    P.eventProb_forall_abs_finiteHermitianEigenvalue_lt_ge_one_sub_exp_neg_mul_expected_trace_exp_add
      M hM T
  have hmulNeg :
      Real.exp (-T) *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (fun i j => -M ω i j))) ≤
        Real.exp (-T) * Bneg :=
    mul_le_mul_of_nonneg_left hTraceNeg (le_of_lt (Real.exp_pos _))
  have hmulPos :
      Real.exp (-T) *
          P.expectationReal (fun ω => finiteTrace (finiteMatrixExp (M ω))) ≤
        Real.exp (-T) * Bpos :=
    mul_le_mul_of_nonneg_left hTracePos (le_of_lt (Real.exp_pos _))
  linarith

end NumStability
