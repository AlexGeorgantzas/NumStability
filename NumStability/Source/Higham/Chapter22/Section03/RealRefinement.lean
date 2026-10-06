/-
Copyright (c) 2026 QED. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/Apache-2.0.txt.
SPDX-License-Identifier: Apache-2.0
See LICENSES/Apache-2.0.txt.
Authors: QED
-/
import NumStability.Algorithms.Horner
import NumStability.Source.Higham.Chapter12.IterativeRefinement
import NumStability.Source.Higham.Chapter22.Section03.ComplexConfluentRefinement
import NumStability.Source.Higham.Chapter22.VandermondeSystems

/-! # Bridge B4: Chapter 12 iterative refinement → Chapter 22 Vandermonde

Higham, 2nd ed., §22.3 (printed p. 428) says that, for a standard Vandermonde
system, Horner residual formation supplies (12.9), so Theorem 12.3 gives an
*asymptotic componentwise backward-stability* result after one refinement step.
It does not assert geometric convergence of the refinement residuals.

The source-facing bridge below therefore has two finite parts.  First, the
Chapter 5 Horner producer is identified with an actual row of the standard
Vandermonde matrix and proves the residual-accuracy premise.  Second, that
actual residual is passed to the exact finite `(12.10)` form of Theorem 12.3.
No contraction or backward-stability conclusion is assumed.

The source leaves its final asymptotic predicate, constants, threshold, and
regularity family unspecified, so that literal asymptotic sentence remains
`DEFER-MISSING-PRECISE-STATEMENT`.  A historical conditional convergence lemma
is retained at the end of this file, but it explicitly assumes a complete
per-step contraction and is not evidence for the printed p. 428 claim. -/

namespace NumStability.Ch22B

open scoped BigOperators Topology
open Filter

/-! ## The genuine (5.3)/(5.7) → corrected (12.8) residual-formation edge -/

/-- A standard Vandermonde residual component formed by evaluating the
coefficient vector with rounded Horner and then performing one rounded
subtraction from the right-hand side. -/
noncomputable def ch22bHornerResidual
    (fp : FPModel) (x b : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  fp.fl_sub b (fl_hornerDesc fp x coeffsDesc)

/-- Finite residual-formation budget obtained from Higham (5.3), including
the final rounded subtraction.  This is the standard-Vandermonde instance of
the residual-accuracy shape used in (12.8).  The literal (12.9) coefficient is
refuted by the compiled source-discrepancy theorem below. -/
noncomputable def ch22bHornerResidualBudget
    (fp : FPModel) (x b : ℝ) (coeffsDesc : List ℝ) : ℝ :=
  let g := gamma fp (2 * (coeffsDesc.length - 1))
  let m := polyDescAbs x coeffsDesc
  g * m + fp.u * (|b| + (1 + g) * m)

/-- The faithful residual-accuracy consequence of printed p. 428, derived
directly from the Chapter 5 producer (5.3) and the standard model for the final
subtraction.  This proves the needed (12.8) shape; it does not assert the
literal (and formally refuted below) conventional `γ_(n+1)` coefficient. -/
theorem ch22b_horner_residual_error_via_higham5_3
    (fp : FPModel) (x b : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |ch22bHornerResidual fp x b coeffsDesc -
        (b - polyDesc x coeffsDesc)| ≤
      ch22bHornerResidualBudget fp x b coeffsDesc := by
  let phat := fl_hornerDesc fp x coeffsDesc
  let p := polyDesc x coeffsDesc
  let m := polyDescAbs x coeffsDesc
  let g := gamma fp (2 * (coeffsDesc.length - 1))
  have hg : 0 ≤ g := by
    exact gamma_nonneg fp hvalid
  have hm : 0 ≤ m := by
    exact polyDescAbs_nonneg x coeffsDesc
  have heval : |phat - p| ≤ g * m := by
    simpa [phat, p, g, m] using
      fl_hornerDesc_forward_error_bound fp x coeffsDesc hvalid
  have hp : |p| ≤ m := by
    simpa [p, m] using abs_polyDesc_le_polyDescAbs x coeffsDesc
  have hphat : |phat| ≤ (1 + g) * m := by
    calc
      |phat| = |(phat - p) + p| := by ring_nf
      _ ≤ |phat - p| + |p| := abs_add_le _ _
      _ ≤ g * m + m := add_le_add heval hp
      _ = (1 + g) * m := by ring
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub b phat
  have hbp : |b - phat| ≤ |b| + (1 + g) * m := by
    exact (abs_sub b phat).trans (add_le_add (le_refl |b|) hphat)
  have hround : |δ| * |b - phat| ≤
      fp.u * (|b| + (1 + g) * m) := by
    exact mul_le_mul hδ hbp (abs_nonneg _) fp.u_nonneg
  change |fp.fl_sub b phat - (b - p)| ≤ _
  rw [hsub]
  have hid : (b - phat) * (1 + δ) - (b - p) =
      (p - phat) + δ * (b - phat) := by ring
  rw [hid]
  calc
    |(p - phat) + δ * (b - phat)| ≤
        |p - phat| + |δ * (b - phat)| := abs_add_le _ _
    _ = |p - phat| + |δ| * |b - phat| := by rw [abs_mul]
    _ ≤ g * m + fp.u * (|b| + (1 + g) * m) :=
      add_le_add (by simpa [abs_sub_comm] using heval) hround
    _ = ch22bHornerResidualBudget fp x b coeffsDesc := by
      simp [ch22bHornerResidualBudget, g, m]

/-- Confluent rows use the first-derivative Horner recurrence.  This is the
corresponding residual-accuracy contribution derived from Higham (5.7).  The
final subtraction can be added exactly as in
`ch22b_horner_residual_error_via_higham5_3`. -/
theorem ch22b_horner_derivative_error_via_higham5_7
    (fp : FPModel) (x : ℝ) (coeffsDesc : List ℝ)
    (hvalid : gammaValid fp (2 * (coeffsDesc.length - 1))) :
    |(fl_hornerDerivativeDesc fp x coeffsDesc).2 -
        polyDescDeriv x coeffsDesc| ≤
      gamma fp (2 * (coeffsDesc.length - 1)) *
        polyDescDerivAbs x coeffsDesc :=
  fl_hornerDerivativeDesc_snd_forward_error_bound_coupled
    fp x coeffsDesc hvalid

/-! ### Arbitrary-order confluent residuals from rounded Algorithm 5.2 -/

/-- The actual rounded order-`r` differentiated-Horner output followed by the
rounded subtraction that forms one real confluent residual component. -/
noncomputable def ch22bHornerHigherDerivativeResidual
    (fp : FPModel) (alpha b : ℝ) (coeffsDesc : List ℝ) (r : ℕ) : ℝ :=
  fp.fl_sub b (fl_hornerHigherDerivativeOutput fp alpha coeffsDesc r)

/-- End-to-end finite budget for the order-`r` residual.  Its first two terms
are exactly the all-order Algorithm 5.2 budget from `Horner.lean`; the final
term is the one rounded subtraction used by residual formation. -/
noncomputable def ch22bHornerHigherDerivativeResidualBudget
    (fp : FPModel) (alpha b : ℝ) (coeffsDesc : List ℝ) (r : ℕ) : ℝ :=
  let pHat := fl_hornerHigherDerivativeOutput fp alpha coeffsDesc r
  fp.u * |(Nat.factorial r : ℝ) *
      fl_hornerTaylorFunctionDesc fp alpha coeffsDesc r| +
    (Nat.factorial r : ℝ) *
      fl_hornerTaylorFunctionForwardBudgetDesc fp alpha coeffsDesc r +
    fp.u * (|b| + |pHat|)

/-- Arbitrary-order `(5.7) → (12.8)` residual-formation bound over the real
subdomain.  Unlike the former first-derivative-only bridge, `r` is unrestricted
and the computed quantity is the literal all-order Algorithm 5.2 executor. -/
theorem ch22b_horner_higher_derivative_residual_error
    (fp : FPModel) (alpha b : ℝ) (coeffsDesc : List ℝ) (r : ℕ) :
    |ch22bHornerHigherDerivativeResidual fp alpha b coeffsDesc r -
        (b - hornerFormalDerivativeFunctionDesc alpha coeffsDesc r)| ≤
      ch22bHornerHigherDerivativeResidualBudget
        fp alpha b coeffsDesc r := by
  let pHat := fl_hornerHigherDerivativeOutput fp alpha coeffsDesc r
  let p := hornerFormalDerivativeFunctionDesc alpha coeffsDesc r
  let evalBudget :=
    fp.u * |(Nat.factorial r : ℝ) *
        fl_hornerTaylorFunctionDesc fp alpha coeffsDesc r| +
      (Nat.factorial r : ℝ) *
        fl_hornerTaylorFunctionForwardBudgetDesc fp alpha coeffsDesc r
  have heval : |pHat - p| ≤ evalBudget := by
    simpa [pHat, p, evalBudget] using
      fl_hornerHigherDerivativeOutput_error_bound fp alpha coeffsDesc r
  obtain ⟨δ, hδ, hsub⟩ := fp.model_sub b pHat
  have hround : |δ| * |b - pHat| ≤ fp.u * (|b| + |pHat|) := by
    exact mul_le_mul hδ (abs_sub b pHat) (abs_nonneg _) fp.u_nonneg
  change |fp.fl_sub b pHat - (b - p)| ≤ _
  rw [hsub]
  have hid : (b - pHat) * (1 + δ) - (b - p) =
      (p - pHat) + δ * (b - pHat) := by ring
  rw [hid]
  calc
    |(p - pHat) + δ * (b - pHat)| ≤
        |p - pHat| + |δ * (b - pHat)| := abs_add_le _ _
    _ = |p - pHat| + |δ| * |b - pHat| := by rw [abs_mul]
    _ ≤ evalBudget + fp.u * (|b| + |pHat|) :=
      add_le_add (by simpa [abs_sub_comm] using heval) hround
    _ = ch22bHornerHigherDerivativeResidualBudget
        fp alpha b coeffsDesc r := by
      simp [ch22bHornerHigherDerivativeResidualBudget, pHat, evalBudget]

/-- Literal `(12.8)` packaging of the arbitrary-order real residual bound.
The compiled theorem `ch22b_literal12_9_gamma5_counterexample` below refutes
the p. 428 claim when (12.9)'s conventional `γ_(n+1)` coefficient is read
verbatim.  The corrected `t` here is the exact generated finite Algorithm 5.2
budget divided by positive unit roundoff. -/
theorem ch22b_horner_higher_derivative_higham12_8_certificate
    (fp : FPModel) (alpha b : ℝ) (coeffsDesc : List ℝ) (r : ℕ)
    (hu : 0 < fp.u) :
    |ch22bHornerHigherDerivativeResidual fp alpha b coeffsDesc r -
        (b - hornerFormalDerivativeFunctionDesc alpha coeffsDesc r)| ≤
      fp.u *
        (ch22bHornerHigherDerivativeResidualBudget
          fp alpha b coeffsDesc r / fp.u) := by
  calc
    |ch22bHornerHigherDerivativeResidual fp alpha b coeffsDesc r -
        (b - hornerFormalDerivativeFunctionDesc alpha coeffsDesc r)| ≤
      ch22bHornerHigherDerivativeResidualBudget fp alpha b coeffsDesc r :=
        ch22b_horner_higher_derivative_residual_error
          fp alpha b coeffsDesc r
    _ = fp.u *
        (ch22bHornerHigherDerivativeResidualBudget
          fp alpha b coeffsDesc r / fp.u) := by field_simp

/-! ### SOURCE-DISCREPANCY: p. 428 cannot inherit literal γ_(n+1)

For `n = 4`, the first-derivative row at `alpha = 1` is `[0,1,2,3]`.
With coefficients `[0,0,0,1]`, its exact absolute row product is `3`.  The
following concrete valid floating-point model rounds every nontrivial add,
multiply, and subtraction upward with `u = 1/100`.  The compiled theorem
proves that the actual rounded Algorithm 5.2 derivative residual error is
strictly greater than `gamma_5 * 3`.  Thus p. 428's reference to (12.9)
cannot soundly retain that numbered formula's conventional-dot-product
`gamma_(n+1)` coefficient.  The faithful terminal correction is the generated
finite budget and exact (12.8) packaging proved immediately above. -/

/-- A valid boundary-inclusive standard model used only to test the literal
`γ_(n+1)` claim: all nontrivial relevant operations round upward by `u`. -/
noncomputable def ch22bLiteral129CounterexampleModel : FPModel where
  u := (1 : ℝ) / 100
  u_nonneg := by norm_num
  fl_add := fun x y => if x = 0 then y else (x + y) * (1 + (1 : ℝ) / 100)
  fl_sub := fun x y => (x - y) * (1 + (1 : ℝ) / 100)
  fl_mul := fun x y => (x * y) * (1 + (1 : ℝ) / 100)
  fl_div := fun x y => x / y
  fl_sqrt := fun x => Real.sqrt x
  fl_add_zero := by intro x; simp
  model_add := by
    intro x y
    by_cases hx : x = 0
    · refine ⟨0, by norm_num, ?_⟩
      simp [hx]
    · refine ⟨(1 : ℝ) / 100, by norm_num, ?_⟩
      simp [hx]
  model_sub := by
    intro x y
    refine ⟨(1 : ℝ) / 100, by norm_num, ?_⟩
    rfl
  model_mul := by
    intro x y
    refine ⟨(1 : ℝ) / 100, by norm_num, ?_⟩
    rfl
  model_div := by
    intro x y _hy
    refine ⟨0, by norm_num, ?_⟩
    ring
  model_sqrt := by
    intro x _hx
    refine ⟨0, by norm_num, ?_⟩
    ring

/-- Compiled terminal counterexample to the literal p. 428 → (12.9)
coefficient, including its `gammaValid` guard and the exact absolute row
product for the selected derivative row. -/
theorem ch22b_literal12_9_gamma5_counterexample :
    gammaValid ch22bLiteral129CounterexampleModel 5 ∧
    gamma ch22bLiteral129CounterexampleModel 5 *
        (|0| + ∑ j : Fin 4,
          |![0, 1, 2, (3 : ℝ)] j| * |![0, 0, 0, (1 : ℝ)] j|) <
      |ch22bHornerHigherDerivativeResidual
          ch22bLiteral129CounterexampleModel 1 0 [1, 0, 0, 0] 1 -
        (0 - hornerFormalDerivativeFunctionDesc 1 [1, 0, 0, 0] 1)| := by
  constructor
  · norm_num [gammaValid, ch22bLiteral129CounterexampleModel]
  · norm_num [Fin.sum_univ_succ, gamma, ch22bLiteral129CounterexampleModel,
      ch22bHornerHigherDerivativeResidual,
      fl_hornerHigherDerivativeOutput, fl_hornerTaylorFunctionDesc,
      fl_hornerTaylorFunctionStep, fl_hornerStep,
      hornerFormalDerivativeFunctionDesc, hornerFormalDerivativeFunctionStep]


/-! ## Exact standard-Vandermonde specialization of Theorem 12.3 -/

private theorem ch22b_polyDesc_append (x : ℝ) :
    ∀ l r : List ℝ,
      polyDesc x (l ++ r) = polyDesc x l * x ^ r.length + polyDesc x r := by
  intro l r
  induction l with
  | nil => simp [polyDesc]
  | cons a l ih =>
      simp [polyDesc, ih, pow_add]
      ring

/-- Ascending vector coefficients become the descending list consumed by
Horner.  This is the representation identity needed to identify Horner
evaluation with a standard Vandermonde row. -/
theorem ch22b_polyDesc_reverse_ofFn_eq_sum {n : ℕ}
    (a : Fin n → ℝ) (x : ℝ) :
    polyDesc x (List.ofFn a).reverse =
      ∑ j : Fin n, a j * x ^ (j : ℕ) := by
  induction n with
  | zero => simp [polyDesc]
  | succ n ih =>
      rw [List.ofFn_succ, List.reverse_cons, ch22b_polyDesc_append]
      rw [ih]
      rw [Fin.sum_univ_succ]
      simp [polyDesc, pow_succ]
      rw [Finset.sum_mul, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Real standard Vandermonde orientation used when solving for polynomial
coefficients: row `i` evaluates the coefficient vector at node `nodes i`. -/
def ch22bStandardVandermonde {n : ℕ} (nodes : Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => nodes i ^ (j : ℕ)

/-- Actual working-precision Horner residual for one row of the standard
Vandermonde system. -/
noncomputable def ch22bStandardComputedResidual {n : ℕ}
    (fp : FPModel) (nodes b xHat : Fin n → ℝ) (i : Fin n) : ℝ :=
  ch22bHornerResidual fp (nodes i) (b i) (List.ofFn xHat).reverse

/-- The finite Chapter 5 budget for the standard Vandermonde residual. -/
noncomputable def ch22bStandardResidualBudget {n : ℕ}
    (fp : FPModel) (nodes b xHat : Fin n → ℝ) (i : Fin n) : ℝ :=
  ch22bHornerResidualBudget fp (nodes i) (b i) (List.ofFn xHat).reverse

/-- Printed p. 428's corrected `(5.3) → (12.8)` step for every row of the
standard Vandermonde system.  The left side is the error of the actual rounded
Horner evaluation followed by one rounded subtraction; the literal (12.9)
coefficient is handled by the source-discrepancy theorem above. -/
theorem ch22b_standard_vandermonde_horner_residual_error {n : ℕ}
    (fp : FPModel) (nodes b xHat : Fin n → ℝ)
    (hvalid : gammaValid fp (2 * (n - 1))) :
    ∀ i : Fin n,
      |ch22bStandardComputedResidual fp nodes b xHat i -
          (b i - ∑ j : Fin n, ch22bStandardVandermonde nodes i j * xHat j)| ≤
        ch22bStandardResidualBudget fp nodes b xHat i := by
  intro i
  have h := ch22b_horner_residual_error_via_higham5_3
    fp (nodes i) (b i) (List.ofFn xHat).reverse (by simpa using hvalid)
  simpa [ch22bStandardComputedResidual, ch22bStandardResidualBudget,
    ch22bStandardVandermonde, ch22b_polyDesc_reverse_ofFn_eq_sum, mul_comm] using h

/-- **Source-facing Chapter 12 → Chapter 22 bridge.**

For the actual rounded Horner residual of a standard Vandermonde system, one
refinement step satisfies the exact finite `(12.10)` conclusion of Theorem 12.3.
The correction-solve and rounded-update hypotheses are precisely the source
models `(12.12)` and `(12.13)`.  Residual accuracy is a conclusion of the
Chapter 5 producer above; there is no contraction or backward-stability target
among the premises.

The quotient by `fp.u` is the source's finite `t(A,b,xHat)` corresponding to
the proved absolute Horner budget.  Positivity of unit roundoff makes this an
exact reparameterization. -/
theorem ch22b_standard_vandermonde_theorem12_3_exact_q_bound {n : ℕ}
    (fp : FPModel) (nodes b xHat dHat rHat f2 y : Fin n → ℝ)
    (gTerm hTerm tAtY : Fin n → ℝ)
    (hvalid : gammaValid fp (2 * (n - 1))) (hu : 0 < fp.u)
    (hrHat : ∀ i : Fin n,
      rHat i = ch22bStandardComputedResidual fp nodes b xHat i)
    (hy : ∀ i : Fin n, y i = xHat i + dHat i + f2 i)
    (hf1 : ∀ i : Fin n,
      |rHat i - ∑ j : Fin n,
          ch22bStandardVandermonde nodes i j * dHat j| ≤
        fp.u * (gTerm i + hTerm i))
    (hf2 : ∀ j : Fin n,
      |f2 j| ≤ fp.u * (|xHat j| + |dHat j|)) :
    ∀ i : Fin n,
      |b i - ∑ j : Fin n,
          ch22bStandardVandermonde nodes i j * y j| ≤
        fp.u * (hTerm i + tAtY i +
          ∑ j : Fin n, |ch22bStandardVandermonde nodes i j| * |y j|) +
        fp.u * (ch22bStandardResidualBudget fp nodes b xHat i / fp.u -
          tAtY i + gTerm i +
          ∑ j : Fin n, |ch22bStandardVandermonde nodes i j| *
            (|xHat j| - |y j| + |dHat j|)) := by
  let A := ch22bStandardVandermonde nodes
  let r : Fin n → ℝ := fun i => b i - ∑ j : Fin n, A i j * xHat j
  let tAtX : Fin n → ℝ := fun i =>
    ch22bStandardResidualBudget fp nodes b xHat i / fp.u
  have hr : ∀ i : Fin n, r i = b i - ∑ j : Fin n, A i j * xHat j := by
    intro i
    rfl
  have hDeltaR : ∀ i : Fin n, |rHat i - r i| ≤ fp.u * tAtX i := by
    intro i
    calc
      |rHat i - r i| =
          |ch22bStandardComputedResidual fp nodes b xHat i -
            (b i - ∑ j : Fin n, A i j * xHat j)| := by
              rw [hrHat i]
      _ ≤ ch22bStandardResidualBudget fp nodes b xHat i := by
            exact ch22b_standard_vandermonde_horner_residual_error
              fp nodes b xHat hvalid i
      _ = fp.u * tAtX i := by
            dsimp [tAtX]
            field_simp
  have h12 := higham12_10_exact_q_bound n A xHat dHat b r rHat f2 y
    fp.u gTerm hTerm tAtX tAtY hr hy hf1 hDeltaR hf2
  simpa [A, tAtX] using h12

/-- Residual formation can be exact while a bad correction leaves a nonzero
residual unchanged.  Thus (5.3)/(5.7), which control residual formation, cannot
by themselves produce the geometric contraction hypothesis used below; a
correction-solve hypothesis is mathematically necessary. -/
theorem ch22b_residual_accuracy_alone_not_contraction :
    ¬ ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ |(1 : ℝ)| ≤ q * |(1 : ℝ)| := by
  rintro ⟨q, _hq0, hq1, hq⟩
  norm_num at hq
  linarith

/-- Optional conditional convergence corollary, retained for clients that
already possess a complete per-step contraction certificate.  This is not the
source-facing p. 428 bridge: `hcontract` assumes the contraction that drives
the conclusion, while Theorem 12.3 itself only supplies the finite envelope.

`xseq k` is the `k`-th computed iterate, `dseq k` its correction, `rseq k` /
`rhatseq k` the exact / computed residuals, `f2seq k` the update-rounding error,
and `gseq/hseq/tseq k` the Chapter 12 residual/solver terms at step `k`.  The
hypotheses `hr, hy, hf1, hDeltaR, hf2` are the per-step Chapter 12 models of
Theorem 12.3.  `hcontract` records the separate requirement that the complete
Theorem 12.3 residual envelope at step `k` is at most `q` times the residual at
step `k`.  The Horner theorems above produce residual-formation accuracy, but
not this correction-solve contraction.

The conclusion is that the tracked residual component tends to `0`.  The proof
applies `higham12_3_exact_one_step_residual_bound` at each step to obtain
`e (k+1) ≤ q · e k`, and closes via the Chapter 22 geometric-decay convergence
`higham22_refinement_converges`. -/
theorem ch22b_refinement_converges_via_ch12
    (n : ℕ) (i : Fin n)
    (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (xseq dseq rseq rhatseq f2seq : ℕ → Fin n → ℝ)
    (gseq hseq tseq : ℕ → Fin n → ℝ)
    (u q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr : ∀ k, ∀ i' : Fin n,
      rseq k i' = b i' - ∑ j : Fin n, A i' j * xseq k j)
    (hy : ∀ k, ∀ i' : Fin n,
      xseq (k + 1) i' = xseq k i' + dseq k i' + f2seq k i')
    (hf1 : ∀ k, ∀ i' : Fin n,
      |rhatseq k i' - ∑ j : Fin n, A i' j * dseq k j| ≤
        u * (gseq k i' + hseq k i'))
    (hDeltaR : ∀ k, ∀ i' : Fin n,
      |rhatseq k i' - rseq k i'| ≤ u * tseq k i')
    (hf2 : ∀ k, ∀ j : Fin n,
      |f2seq k j| ≤ u * (|xseq k j| + |dseq k j|))
    (hcontract : ∀ k,
      u * (gseq k i + hseq k i) + u * tseq k i +
          u * ∑ j : Fin n, |A i j| * (|xseq k j| + |dseq k j|) ≤
        q * |b i - ∑ j : Fin n, A i j * xseq k j|) :
    Tendsto (fun k => |b i - ∑ j : Fin n, A i j * xseq k j|) atTop (𝓝 0) := by
  set e : ℕ → ℝ := fun k => |b i - ∑ j : Fin n, A i j * xseq k j| with he
  -- Per-step contraction of the *actual* residual, produced by Theorem 12.3.
  have hstep : ∀ k, e (k + 1) ≤ q * e k := by
    intro k
    have hch12 := higham12_3_exact_one_step_residual_bound n A
      (xseq k) (dseq k) b (rseq k) (rhatseq k) (f2seq k) (xseq (k + 1))
      u (gseq k) (hseq k) (tseq k)
      (fun i' => hr k i') (fun i' => hy k i')
      (fun i' => hf1 k i') (fun i' => hDeltaR k i')
      (fun j => hf2 k j) i
    exact le_trans hch12 (hcontract k)
  -- The residual is dominated by the Chapter 22 geometric-decay majorant.
  have hmaj : ∀ k, e k ≤ higham22RefinementError q (e 0) k := by
    intro k
    induction k with
    | zero => simp [higham22RefinementError]
    | succ k ih =>
        calc
          e (k + 1) ≤ q * e k := hstep k
          _ ≤ q * higham22RefinementError q (e 0) k :=
                mul_le_mul_of_nonneg_left ih hq0
          _ = higham22RefinementError q (e 0) (k + 1) := by
                rw [higham22RefinementError]
  have hnn : ∀ k, 0 ≤ e k := fun _ => abs_nonneg _
  have hconv : Tendsto (higham22RefinementError q (e 0)) atTop (𝓝 0) :=
    higham22_refinement_converges q (e 0) hq0 hq1
  exact squeeze_zero hnn hmaj hconv

end NumStability.Ch22B
