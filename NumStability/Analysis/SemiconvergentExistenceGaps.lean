-- Analysis/SemiconvergentExistenceGaps.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems",
-- eq (17.22) / Householder `[106, Lem 6.9]`: closing as much as possible of the
-- FULL semiconvergent-existence spectral substance itemized as GAPS (1)-(4) in
-- the OBSTRUCTIONS block of `Analysis/SemiconvergentSpectral.lean`.
--
-- This module is IMPORT-ONLY: it never edits any existing file.  It contributes
-- the following genuinely new, UNCONDITIONAL sub-results, going strictly beyond
-- `SemiconvergentSpectral.lean` (which only proved the closed-disk necessity
-- `‖μ‖ ≤ 1` and the algebraic collapse skeleton):
--
--   GAP (2) SCALAR DICHOTOMY — CLOSED unconditionally.  For `μ` in any
--     nontrivially normed field, if the power sequence `μ^m` CONVERGES then
--     `μ = 1 ∨ ‖μ‖ < 1`.  Lifted to eigenvectors over `ℝ`/`ℂ` (`RCLike`): a
--     convergent eigenvector orbit forces `μ = 1 ∨ ‖μ‖ < 1`.  This is exactly
--     the strengthening from the closed disk `‖μ‖ ≤ 1` (all that
--     `SemiconvergentSpectral.lean` had) to the printed condition
--     "`μ = 1` or `|μ| < 1`" of eq (17.22) — the crux of GAP (2).
--
--   GAP (4) DIAGONAL-SIMILARITY CONTRACTION — CLOSED unconditionally for the
--     upper-triangular normal form (Householder's actual construction).  For a
--     real upper-triangular `T` with `|T i i| ≤ ρ < 1`, an explicit geometric
--     diagonal `D = diag(δ^·)` gives `‖D⁻¹ T D‖∞ < 1`.  This is precisely the
--     δ-scaling of the strict-upper part named in the GAP (4) route; it reuses
--     the repository's `matMul`/`infNorm`/`diagMatrix` machinery and the row-sum
--     bound API of `MatrixPowersJordan`.  It closes GAP (4) DOWNSTREAM of a
--     Schur/real-triangular normal form (the residual reduction being GAP (3)).
--
--   GAP (1) SEMISIMPLE-AT-1 — SUBSTANTIVE PARTIAL.  The exact "reverse
--     quantitative lower bound" that `SemiconvergentSpectral.lean` flagged as
--     missing is here proved unconditionally: a length-2 Jordan chain at
--     eigenvalue `1` (`f w = w`, `f v = v + w`, `w ≠ 0`, equivalently a rank-2
--     generalized eigenvector) yields `f^m v = v + m • w`, whose norm DIVERGES
--     `‖f^m v‖ → ∞`.  Hence a bounded/convergent orbit admits NO rank-2 Jordan
--     chain at `1`.  This is the analytic heart of "eigenvalue 1 semisimple";
--     the full collapse `maxGenEigenspace 1 = eigenspace 1` from boundedness
--     needs the structural step (every rank-≥2 chain embeds a rank-2 chain +
--     the nilpotent-part-vanishes packaging), still absent from Mathlib.
--
--   GAP (3) ℂ→ℝ DESCENT — EVIDENCED OBSTRUCTION (no code).  See the closing
--     comment: Mathlib v4.29 has no real-primary-decomposition / conjugate-pair
--     recombination / complexification-descent API, so the real invariant basis
--     `X` cannot be produced.
--
-- No `sorry`/`admit`/`axiom`.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.MatrixPowersJordan

namespace NumStability

open scoped BigOperators Topology
open Module

-- ============================================================
-- §17.4  GAP (2).  The scalar power-convergence dichotomy
--            μ^m converges  ⟹  μ = 1 ∨ ‖μ‖ < 1
-- ============================================================

section ScalarDichotomy

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — the SCALAR DICHOTOMY (GAP (2)).

    If the power sequence `m ↦ μ^m` converges to some limit `c` (i.e.
    `Tendsto (μ^·) atTop (𝓝 c)`), then `μ = 1 ∨ ‖μ‖ < 1`.

    Proof.  First `‖μ‖ ≤ 1`, else `‖μ‖^m = ‖μ^m‖ → ∞` contradicts convergence.
    If `‖μ‖ < 1` we are done.  If `‖μ‖ = 1` then `‖μ^m‖ = 1` for all `m`, so the
    limit has `‖c‖ = 1 ≠ 0`; the shifted sequence `μ^{m+1}` tends to `c` and
    also to `μ·c`, whence `μ·c = c`, i.e. `(μ-1)·c = 0`, and `c ≠ 0` forces
    `μ = 1`.  This is the exact upgrade from the closed disk `‖μ‖ ≤ 1` to the
    printed spectral condition of eq (17.22).  Unconditional. -/
theorem scalar_pow_tendsto_dichotomy {μ : 𝕜} {c : 𝕜}
    (h : Filter.Tendsto (fun m : ℕ => μ ^ m) Filter.atTop (𝓝 c)) :
    μ = 1 ∨ ‖μ‖ < 1 := by
  -- Step 1: ‖μ‖ ≤ 1.
  have hle : ‖μ‖ ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    have hnorm : Filter.Tendsto (fun m : ℕ => ‖μ ^ m‖) Filter.atTop (𝓝 ‖c‖) :=
      (continuous_norm.tendsto c).comp h
    have hnorm' : Filter.Tendsto (fun m : ℕ => ‖μ‖ ^ m) Filter.atTop (𝓝 ‖c‖) := by
      simpa [norm_pow] using hnorm
    have hdiv : Filter.Tendsto (fun m : ℕ => ‖μ‖ ^ m) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hgt
    exact (Filter.not_bddAbove_of_tendsto_atTop hdiv) hnorm'.isBoundedUnder_le.bddAbove_range
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inr hlt
  · -- Step 2: ‖μ‖ = 1 ⟹ μ = 1.
    left
    have hshift : Filter.Tendsto (fun m : ℕ => μ ^ (m + 1)) Filter.atTop (𝓝 c) :=
      (Filter.tendsto_add_atTop_iff_nat 1).2 h
    have hmul : Filter.Tendsto (fun m : ℕ => μ ^ (m + 1)) Filter.atTop (𝓝 (μ * c)) := by
      have hstep : Filter.Tendsto (fun m : ℕ => μ * μ ^ m) Filter.atTop (𝓝 (μ * c)) :=
        h.const_mul μ
      refine hstep.congr ?_
      intro m; rw [pow_succ, mul_comm]
    have huniq : μ * c = c := tendsto_nhds_unique hmul hshift
    have hc : ‖c‖ = 1 := by
      have hnorm : Filter.Tendsto (fun m : ℕ => ‖μ ^ m‖) Filter.atTop (𝓝 ‖c‖) :=
        (continuous_norm.tendsto c).comp h
      have hconst : (fun m : ℕ => ‖μ ^ m‖) = fun _ : ℕ => (1 : ℝ) := by
        funext m; rw [norm_pow, heq, one_pow]
      rw [hconst] at hnorm
      exact tendsto_nhds_unique hnorm tendsto_const_nhds
    have hcne : c ≠ 0 := by
      intro h0; rw [h0, norm_zero] at hc; norm_num at hc
    have hzero : (μ - 1) * c = 0 := by rw [sub_mul, one_mul, huniq, sub_self]
    rcases mul_eq_zero.1 hzero with h1 | h2
    · exact sub_eq_zero.1 h1
    · exact absurd h2 hcne

end ScalarDichotomy

section EigenvalueLift

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — GAP (2) LIFTED to eigenvectors.

    Over `ℝ`/`ℂ` (`RCLike`), if `v` is an eigenvector of `f` for eigenvalue `μ`
    and the orbit `n ↦ f^n v` converges, then `μ = 1 ∨ ‖μ‖ < 1`.

    Proof.  The orbit is `μ^n • v`.  A Hahn–Banach functional `φ` with
    `φ v = ‖v‖ ≠ 0` turns operator convergence into scalar convergence of
    `μ^n`, and the scalar dichotomy finishes.  For a semiconvergent iteration
    matrix `G` every eigenvector orbit `G^m v` converges, so every eigenvalue
    satisfies `μ = 1 ∨ |μ| < 1` — precisely the printed condition of eq (17.22).
    Unconditional. -/
theorem eigenvalue_dichotomy_of_orbit_tendsto
    {f : End 𝕜 V} {μ : 𝕜} {v : V} (hv : f.HasEigenvector μ v)
    {w : V} (hw : Filter.Tendsto (fun n : ℕ => (f ^ n) v) Filter.atTop (𝓝 w)) :
    μ = 1 ∨ ‖μ‖ < 1 := by
  have horbit : (fun n : ℕ => (f ^ n) v) = fun n : ℕ => μ ^ n • v := by
    funext n; rw [hv.pow_apply n]
  rw [horbit] at hw
  have hvne : (‖v‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hv.2
  obtain ⟨φ, _hφnorm, hφv⟩ := exists_dual_vector 𝕜 v hvne
  have hscal : Filter.Tendsto (fun n : ℕ => μ ^ n * (‖v‖ : 𝕜)) Filter.atTop (𝓝 (φ w)) := by
    have hcont : Filter.Tendsto (fun n : ℕ => φ (μ ^ n • v)) Filter.atTop (𝓝 (φ w)) :=
      (φ.continuous.tendsto w).comp hw
    refine hcont.congr ?_
    intro n
    rw [map_smul, smul_eq_mul, hφv]
  have hvne' : (‖v‖ : 𝕜) ≠ 0 := (RCLike.ofReal_ne_zero (K := 𝕜)).mpr hvne
  have hscal' : Filter.Tendsto (fun n : ℕ => μ ^ n) Filter.atTop (𝓝 (φ w * ((‖v‖ : 𝕜))⁻¹)) := by
    have hmul := hscal.mul_const (((‖v‖ : 𝕜))⁻¹)
    refine hmul.congr ?_
    intro n
    rw [mul_assoc, mul_inv_cancel₀ hvne', mul_one]
  exact scalar_pow_tendsto_dichotomy hscal'

end EigenvalueLift

-- ============================================================
-- §17.4  GAP (1).  Reverse quantitative bound: a rank-2 Jordan
--            chain at eigenvalue 1 makes the orbit diverge.
-- ============================================================

section JordanChainDivergence

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22) — a fixed vector stays fixed under all powers: `f w = w`
    implies `f^m w = w`.  Auxiliary to the GAP (1) divergence bound. -/
theorem pow_apply_of_fixed {f : End 𝕜 V} {w : V} (hw : f w = w) (m : ℕ) :
    (f ^ m) w = w := by
  induction m with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, hw, ih]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — the ORBIT of a length-2 Jordan
    chain at eigenvalue `1` (GAP (1) core).

    If `f w = w` and `f v = v + w`, then `f^m v = v + (m : 𝕜) • w`.  The linear
    growth in `m` is the exact quantitative mechanism by which a nontrivial
    Jordan block at `1` breaks power-boundedness — the "reverse lower bound"
    that `SemiconvergentSpectral.lean` flagged as missing.  Unconditional. -/
theorem jordanChain2_pow_apply {f : End 𝕜 V} {v w : V}
    (hw : f w = w) (hv : f v = v + w) (m : ℕ) :
    (f ^ m) v = v + (m : 𝕜) • w := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hv, map_add, ih, pow_apply_of_fixed hw]
      push_cast
      module

end JordanChainDivergence

section JordanChainUnbounded

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — a length-2 Jordan chain at
    eigenvalue `1` yields a NORM-DIVERGENT orbit (GAP (1)).

    Over `ℝ`/`ℂ`, if `f w = w`, `f v = v + w` and `w ≠ 0`, then
    `‖f^m v‖ → ∞`.  Consequently a bounded (in particular convergent) orbit
    admits no such chain — the analytic core of "eigenvalue `1` is semisimple"
    for a semiconvergent matrix.  Unconditional. -/
theorem jordanChain2_orbit_norm_tendsto_atTop {f : End 𝕜 V} {v w : V}
    (hw : f w = w) (hv : f v = v + w) (hwne : w ≠ 0) :
    Filter.Tendsto (fun m : ℕ => ‖(f ^ m) v‖) Filter.atTop Filter.atTop := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hlb : ∀ m : ℕ, (m : ℝ) * ‖w‖ - ‖v‖ ≤ ‖(f ^ m) v‖ := by
    intro m
    have hval : (f ^ m) v = v + (m : 𝕜) • w := jordanChain2_pow_apply hw hv m
    have hnm : ‖(m : 𝕜) • w‖ = (m : ℝ) * ‖w‖ := by
      rw [norm_smul, RCLike.norm_natCast]
    have h1 : ‖(m : 𝕜) • w‖ - ‖v‖ ≤ ‖v + (m : 𝕜) • w‖ := by
      have htri : ‖(m : 𝕜) • w‖ ≤ ‖v + (m : 𝕜) • w‖ + ‖v‖ := by
        have := norm_add_le (v + (m : 𝕜) • w) (-v)
        simpa [add_comm, add_left_comm, add_assoc] using this
      linarith
    rw [hval]
    calc (m : ℝ) * ‖w‖ - ‖v‖ = ‖(m : 𝕜) • w‖ - ‖v‖ := by rw [hnm]
      _ ≤ ‖v + (m : 𝕜) • w‖ := h1
  have hdiv : Filter.Tendsto (fun m : ℕ => (m : ℝ) * ‖w‖ - ‖v‖) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_add_const_right
    exact Filter.Tendsto.atTop_mul_const hwpos tendsto_natCast_atTop_atTop
  exact Filter.tendsto_atTop_mono hlb hdiv

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]` — GAP (1) via the generalized
    eigenspace at `1`.

    A rank-2 generalized eigenvector `x` at `1` (`(f - 1)² x = 0`) that is not
    an ordinary eigenvector (`(f - 1) x ≠ 0`) has a norm-divergent orbit
    `‖f^m x‖ → ∞`.  Hence a bounded/convergent orbit forces the eigenvalue-`1`
    generalized eigenspace to have no rank-≥2 Jordan chains — the honest,
    unconditional analytic content of the semisimplicity of `1`.  Unconditional. -/
theorem genEigenvector_one_rank_two_orbit_norm_tendsto_atTop
    {f : End 𝕜 V} {x : V}
    (hx2 : ((f - (1 : End 𝕜 V)) ^ 2) x = 0)
    (hx1 : (f - (1 : End 𝕜 V)) x ≠ 0) :
    Filter.Tendsto (fun m : ℕ => ‖(f ^ m) x‖) Filter.atTop Filter.atTop := by
  set w : V := (f - (1 : End 𝕜 V)) x with hwdef
  have hv : f x = x + w := by
    rw [hwdef, LinearMap.sub_apply, Module.End.one_apply]; abel
  have hw0 : (f - (1 : End 𝕜 V)) w = 0 := by
    rw [hwdef, ← Module.End.mul_apply, ← sq]; exact hx2
  have hw : f w = w := by
    have hthis := hw0
    rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hthis
    exact hthis
  exact jordanChain2_orbit_norm_tendsto_atTop hw hv hx1

end JordanChainUnbounded

-- ============================================================
-- §17.4  GAP (4).  Householder diagonal-similarity contraction
--            for the upper-triangular normal form.
-- ============================================================

section TriangularContraction

variable {n : ℕ}

/-- The conjugation entry `(D⁻¹ T D)_{ij} = (δ^i)⁻¹ · T_{ij} · δ^j` for the
    geometric diagonal `D = diag(δ^·)`.  Auxiliary to the GAP (4) contraction. -/
private theorem geom_conj_entry (T : Fin n → Fin n → ℝ) (δ : ℝ) (i j : Fin n) :
    matMul n (diagMatrix fun a => (δ ^ (a : ℕ))⁻¹)
        (matMul n T (diagMatrix fun a => δ ^ (a : ℕ))) i j
      = (δ ^ (i : ℕ))⁻¹ * T i j * δ ^ (j : ℕ) :=
  diagMatrix_conj_entry T (fun a => δ ^ (a : ℕ)) (fun a => (δ ^ (a : ℕ))⁻¹) i j

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22); Householder `[106, Lem 6.9]`; cf. §18.2 Thm 18.1 (pp. 347–348)
    — the DIAGONAL-SIMILARITY CONTRACTION for an upper-triangular matrix
    (GAP (4)).

    For a real upper-triangular `T` (`T i j = 0` whenever `j < i`) whose diagonal
    entries all satisfy `|T i i| ≤ ρ` with `ρ < 1`, the geometric diagonal
    `D = diag(δ^·)` with a suitably small `δ ∈ (0,1]` scales every row sum of
    `|D⁻¹ T D|` strictly below `1`, so `‖D⁻¹ T D‖∞ < 1`.  The returned `p`
    (`p i = δ^i > 0`) is the diagonal of `D`; its pointwise inverse is the
    diagonal of `D⁻¹` (see `diagMatrix_isRightInverse`), so `D` is invertible.

    Proof.  The conjugation entry is `δ^{j-i} T_{ij}`: below the diagonal it
    vanishes; on the diagonal it is `T_{ii}` (`|·| ≤ ρ`); above the diagonal
    `δ^{j-i} ≤ δ` (as `j - i ≥ 1`, `δ ≤ 1`), so each strict-upper term is
    `≤ δ · |T_{ij}|`.  Thus every row sum is `≤ ρ + δ · M` where `M` bounds the
    off-diagonal absolute row sums, and `δ` is chosen so `ρ + δ·M < 1`.  This is
    Householder's δ-scaling of the strict-upper part named in the GAP (4) route.
    Unconditional. -/
theorem exists_diag_infNorm_conj_lt_one_of_upperTriangular
    (T : Fin n → Fin n → ℝ) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hupper : ∀ i j : Fin n, (j : ℕ) < (i : ℕ) → T i j = 0)
    (hdiag : ∀ i : Fin n, |T i i| ≤ ρ) :
    ∃ p : Fin n → ℝ, (∀ i, 0 < p i) ∧
      infNorm (matMul n (diagMatrix fun a => (p a)⁻¹)
        (matMul n T (diagMatrix p))) < 1 := by
  set M : ℝ := 1 + ∑ i : Fin n, ∑ j : Fin n, |T i j| with hM
  have hMpos : 0 < M := by
    have hnn : (0 : ℝ) ≤ ∑ i : Fin n, ∑ j : Fin n, |T i j| :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
    simp only [hM]; linarith
  have hρpos : 0 < 1 - ρ := sub_pos.mpr hρ1
  set δ : ℝ := min 1 ((1 - ρ) / (2 * M)) with hδ
  have hδpos : 0 < δ := by
    apply lt_min
    · norm_num
    · apply div_pos hρpos; positivity
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδMpos : 0 < δ * M := mul_pos hδpos hMpos
  have hδM : δ * M < 1 - ρ := by
    have hle : δ ≤ (1 - ρ) / (2 * M) := min_le_right _ _
    have h2M : 0 < 2 * M := by positivity
    calc δ * M ≤ ((1 - ρ) / (2 * M)) * M :=
          mul_le_mul_of_nonneg_right hle hMpos.le
      _ = (1 - ρ) / 2 := by field_simp
      _ < 1 - ρ := by linarith
  refine ⟨fun a => δ ^ (a : ℕ), fun i => pow_pos hδpos _, ?_⟩
  apply lt_of_le_of_lt (b := ρ + δ * M)
  · apply infNorm_le_of_row_sum_le _ _ (by linarith)
    intro i
    have hrow : (∑ j : Fin n, |matMul n (diagMatrix fun a => (δ ^ (a : ℕ))⁻¹)
          (matMul n T (diagMatrix fun a => δ ^ (a : ℕ))) i j|)
        = ∑ j : Fin n, |(δ ^ (i : ℕ))⁻¹ * T i j * δ ^ (j : ℕ)| := by
      apply Finset.sum_congr rfl
      intro j _; rw [geom_conj_entry]
    rw [hrow]
    have hterm : ∀ j : Fin n,
        |(δ ^ (i : ℕ))⁻¹ * T i j * δ ^ (j : ℕ)|
          ≤ δ * |T i j| + (if j = i then ρ else 0) := by
      intro j
      by_cases hji : (j : ℕ) < (i : ℕ)
      · rw [hupper i j hji, mul_zero, zero_mul, abs_zero]
        have h1 : 0 ≤ δ * |T i j| := by positivity
        have h2 : 0 ≤ (if j = i then ρ else (0:ℝ)) := by split; exacts [hρ0, le_refl 0]
        linarith
      · by_cases heq : j = i
        · have hnej : δ ^ (i : ℕ) ≠ 0 := (pow_pos hδpos _).ne'
          rw [heq]
          have hval : (δ ^ (i : ℕ))⁻¹ * T i i * δ ^ (i : ℕ) = T i i := by
            rw [mul_comm ((δ ^ (i : ℕ))⁻¹) (T i i), mul_assoc, inv_mul_cancel₀ hnej,
              mul_one]
          rw [hval, if_pos rfl]
          have hd : |T i i| ≤ ρ := hdiag i
          nlinarith [abs_nonneg (T i i)]
        · have hgt : (i : ℕ) < (j : ℕ) := by
            rcases lt_trichotomy (j : ℕ) (i : ℕ) with hh | hh | hh
            · exact absurd hh hji
            · exact absurd (Fin.eq_of_val_eq hh) heq
            · exact hh
          rw [if_neg heq, add_zero]
          have hne : δ ^ (i : ℕ) ≠ 0 := (pow_pos hδpos _).ne'
          have hfac : (δ ^ (i : ℕ))⁻¹ * T i j * δ ^ (j : ℕ)
              = δ ^ ((j : ℕ) - (i : ℕ)) * T i j := by
            have hsplit : δ ^ (j : ℕ) = δ ^ ((j : ℕ) - (i : ℕ)) * δ ^ (i : ℕ) := by
              rw [← pow_add]; congr 1; omega
            rw [hsplit,
              show (δ ^ (i : ℕ))⁻¹ * T i j * (δ ^ ((j : ℕ) - (i : ℕ)) * δ ^ (i : ℕ))
                  = δ ^ ((j : ℕ) - (i : ℕ)) * T i j * ((δ ^ (i : ℕ))⁻¹ * δ ^ (i : ℕ)) by ring,
              inv_mul_cancel₀ hne, mul_one]
          rw [hfac, abs_mul, abs_of_pos (pow_pos hδpos _)]
          have hexp : δ ^ ((j : ℕ) - (i : ℕ)) ≤ δ := by
            have h1 : 1 ≤ (j : ℕ) - (i : ℕ) := by omega
            calc δ ^ ((j : ℕ) - (i : ℕ)) ≤ δ ^ 1 :=
                  pow_le_pow_of_le_one hδpos.le hδ1 h1
              _ = δ := pow_one δ
          exact mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    calc ∑ j : Fin n, |(δ ^ (i : ℕ))⁻¹ * T i j * δ ^ (j : ℕ)|
        ≤ ∑ j : Fin n, (δ * |T i j| + (if j = i then ρ else 0)) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = δ * ∑ j : Fin n, |T i j| + ρ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum,
            Finset.sum_ite_eq' Finset.univ i (fun _ => ρ), if_pos (Finset.mem_univ i)]
      _ ≤ ρ + δ * M := by
          have hle : ∑ j : Fin n, |T i j| ≤ M := by
            rw [hM]
            have hsingle : ∑ j : Fin n, |T i j| ≤ ∑ i' : Fin n, ∑ j : Fin n, |T i' j| :=
              Finset.single_le_sum (f := fun i' => ∑ j : Fin n, |T i' j|)
                (fun i' _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
            linarith
          have hmul : δ * ∑ j : Fin n, |T i j| ≤ δ * M :=
            mul_le_mul_of_nonneg_left hle hδpos.le
          linarith
  · linarith

end TriangularContraction

-- ============================================================
-- §17.4  RESIDUAL OBSTRUCTION for the FULL [106, Lem 6.9].
-- ============================================================
--
-- After this module, the four itemized gaps stand as follows.
--
-- GAP (2) — CLOSED.  `scalar_pow_tendsto_dichotomy` and
--   `eigenvalue_dichotomy_of_orbit_tendsto` upgrade the closed disk `‖μ‖ ≤ 1`
--   of `SemiconvergentSpectral.lean` to the printed `μ = 1 ∨ ‖μ‖ < 1` of
--   eq (17.22), unconditionally.
--
-- GAP (4) — CLOSED for the triangular normal form.
--   `exists_diag_infNorm_conj_lt_one_of_upperTriangular` delivers the explicit
--   invertible diagonal similarity `D` with `‖D⁻¹ T D‖∞ < 1` for any
--   upper-triangular `T` with `|diag| ≤ ρ < 1`.  The only residue is the
--   reduction "`spectralRadius Γ < 1` ⟹ `Γ` is similar to such a triangular
--   `T`", which is the Schur/real-triangular normal form — i.e. exactly GAP (3).
--
-- GAP (1) — SUBSTANTIVE PARTIAL.
--   `jordanChain2_pow_apply` / `jordanChain2_orbit_norm_tendsto_atTop` /
--   `genEigenvector_one_rank_two_orbit_norm_tendsto_atTop` prove, without any
--   hypothesis, the reverse quantitative lower bound that
--   `SemiconvergentSpectral.lean` recorded as missing: a rank-2 Jordan chain at
--   `1` makes `‖f^m v‖` diverge.  The remaining step to the full collapse
--   `maxGenEigenspace 1 = eigenspace 1` from mere power-boundedness is the
--   STRUCTURAL packaging — that any rank-≥2 generalized eigenvector at `1`
--   contains a rank-2 sub-chain (so the nilpotent part `(f-1)` restricted to the
--   generalized eigenspace vanishes).  Mathlib v4.29 has no lemma of the form
--   `IsPowerBounded f → f.maxGenEigenspace 1 = f.eigenspace 1`, nor a
--   "nilpotent restriction has a rank-2 chain generator" lemma to assemble it
--   from the bound above; that assembly is the residual obstruction.
--
-- GAP (3) — EVIDENCED OBSTRUCTION.  Producing the REAL invariant basis `X`
--   requires recombining each conjugate pair of complex generalized-eigenspaces
--   into a single real invariant subspace (real primary / real-Jordan
--   decomposition) and reindexing the `1`-summand into coordinates `< r`.
--   Concrete Mathlib search (v4.29) finds NO such API:
--     • no `Module.End.exists_real_invariant_complement` or real-block-diagonal
--       normal form for a real endomorphism with complex spectrum;
--     • no conjugate-pair recombination of `maxGenEigenspace` over ℂ back to ℝ;
--     • the complexification API (`Complexification`, base change) does not run
--       in the descent direction needed here.
--   Because both the triangular contraction (GAP (4)) and the eigenvalue
--   dichotomy (GAP (2)) are now closed, GAP (3) — the ℂ→ℝ Schur/real-triangular
--   normal form — is the single genuine bottleneck to the full existence, and it
--   is not bridgeable from Mathlib v4.29 + this repository as-is.

end NumStability
