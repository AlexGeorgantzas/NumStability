/-
Analysis/BergerResolvent.lean

The GENERAL (non-Hermitian) Berger power inequality for the numerical radius,
`r(A^k) ≤ r(A)^k`, from Higham, *Accuracy and Stability of Numerical Algorithms*,
2nd ed., Section 18.1 (Matrix Powers), p. 345 — attacked via the
resolvent / numerical-range **positivity** route (NOT the unitary-dilation route,
which a prior wave found blocked and which `BergerInequality.lean` records as
absent from Mathlib).

`NumericalRadius.lean` develops `r(A) = ⨆ x, ‖⟪Ax, x⟫‖/‖x‖²`, the sandwich
`‖A‖₂/2 ≤ r(A) ≤ ‖A‖₂`, and closes the §18.1 power bound `‖A^k‖₂ ≤ 2·r(A)^k`
*conditionally* on Berger `r(A^k) ≤ r(A)^k`.  `BergerInequality.lean` discharges
Berger **on the Hermitian subclass** (there `r = ‖·‖`, so Berger is
submultiplicativity).  This file goes strictly beyond Hermitian.

# What is proved here (all over `ℂ`, unconditional, no `sorry`/`axiom`)

  * `numericalRadiusCLM_smul` / `numericalRadius_smul`
        -- **Scaling homogeneity** `r(c·A) = |c|·r(A)`.  This is ingredient (i) of
           the Berger–Kato programme (the WLOG-`r(A)=1` normalization), and it is
           genuinely new (absent from the two existing files).

  * `norm_apply_sq_add_norm_inner_sq_le`
        -- **The `k = 2` positivity lemma (core).** For every operator `T` and
           every vector `x`,
             `‖T x‖² + ‖⟪T² x, x⟫‖ ≤ r(T)·(‖x‖² + ‖T x‖²)`.
           Proof: rotate `T` by a unit phase `μ` (chosen via a complex square
           root so that `μ²⟪T²x,x⟫ = |⟪T²x,x⟫|`), expand
           `⟪T up,up⟫ − ⟪T um,um⟫` for `u± = x ± μ T x`, bound each diagonal term
           by `r(T)‖u±‖²`, and collapse `‖up‖²+‖um‖²` with the parallelogram law.
           This is exactly the numerical-range positivity that the Berger–Kato
           route runs on, made elementary at `k = 2`.

  * `numericalRadiusCLM_pow_two_le` / **`numericalRadius_pow_two_le`**
        -- **Berger for `k = 2`, GENERAL matrices, UNCONDITIONAL:**
           `r(A²) ≤ r(A)²`.  A genuine new theorem beyond the Hermitian case.
           Obtained from the core lemma (normalized form `r(T)≤1 ⇒ r(T²)≤1`) and
           the scaling homogeneity above.

  * `numericalRadiusCLM_pow_two_pow_le` / **`numericalRadius_pow_two_pow_le`**
        -- **Berger for every power of two, GENERAL, UNCONDITIONAL:**
           `r(A^(2^m)) ≤ r(A)^(2^m)`.  Iterating `r(B²) ≤ r(B)²` along
           `A^(2^(m+1)) = (A^(2^m))²`.  An infinite family strictly beyond
           Hermitian.

  * `norm_pow_two_le_two_mul_numericalRadius_sq`
        -- the resulting §18.1 power bound at `k = 2`, `‖A²‖₂ ≤ 2·r(A)²`,
           UNCONDITIONALLY for general `A` (discharging `hBerger` at `k = 2`).

# The resolvent-positivity route: exact identity and its honest obstruction

  * `two_re_inner_sub_apply_sub_normSq`
        -- **Exact resolvent real-part identity (invertibility-free).** For every
           operator `T` and vector `w`,
             `2·Re⟪w, w − T w⟫ − ‖w − T w‖² = ‖w‖² − ‖T w‖²`.
           Putting `x = w − T w = (I − T) w` (so `w = (I − T)⁻¹ x` when `I − T` is
           invertible) turns the left side into `2·Re⟪(I − T)⁻¹ x, x⟫ − ‖x‖²`, the
           quantity the Berger–Kato route inspects; the identity itself needs no
           invertibility.

  * `resolvent_positive_iff_opContraction`
        -- **Evidenced obstruction.** The positive-real-part condition
           `‖(I − T)w‖² ≤ 2·Re⟪w,(I − T)w⟫` for all `w` (i.e.
           `Re⟪(I − T)⁻¹x,x⟫ ≥ ½‖x‖²`) is *equivalent to* `‖T w‖ ≤ ‖w‖` for all
           `w`, i.e. `‖T‖ ≤ 1`.

    So the positive-real-part condition the naive route reads off the resolvent
    Neumann series `(I − zA)⁻¹ = Σ zⁿ Aⁿ` characterizes the **operator norm**, not
    the numerical radius: a Carathéodory/Herglotz coefficient bound built on it
    reproduces only submultiplicativity `‖A^k‖ ≤ ‖A‖^k`, NOT Berger
    `r(A^k) ≤ r(A)^k`.  (Counterexample witnessing the gap: the `2×2` nilpotent
    `A = [[0,2],[0,0]]` has `r(A) = 1` yet `‖A w‖ = 2‖w‖` on `w = e₂`, so
    `Re⟪(I−zA)⁻¹e₂,e₂⟫ < ½` for `|z|` near `1`.)  Genuine numerical-radius control
    requires the non-analytic `ρ = 2` unitary-dilation criterion, which needs the
    dilation machinery Mathlib lacks; the `k = 2` chain above sidesteps it with
    the elementary rotation/parallelogram positivity instead.

# HONEST SCOPE / residual for general `k`

Berger for a general (non-power-of-two) exponent `k` is NOT proved here.  The
elementary `k = 2` positivity lemma generalizes to Pearcy's `n`-th roots-of-unity
identity: with `ω = e^{2πi/n}` and `u_j = Σ_l ω^{-jl} A^l x`, the same averaging
isolates `⟪A^n x,x⟫` against a positive combination of diagonal forms
`⟪A u_j,u_j⟫`.  Formalizing the general-`n` step needs exactly that `n`-point
discrete-Fourier identity (an `n`-fold parallelogram / character-orthogonality
computation) — a finite but genuinely longer algebraic identity than the two-term
`n = 2` case closed here.  It is the single missing lemma; nothing is smuggled
into a hypothesis.
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Pointwise
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import NumStability.Analysis.NumericalRadius

open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-!
### Scaling homogeneity of the numerical radius (Berger–Kato ingredient (i))
-/

/-- **Scaling homogeneity (operator form).** `r(c·T) = ‖c‖·r(T)` for `c : ℂ`.

Higham §18.1, p. 345: the numerical radius is absolutely homogeneous,
`r(cA) = |c|·r(A)`.  This is the normalization ingredient of the Berger–Kato
programme (WLOG `r(A) = 1`).  Since `⟪(c•T)x,x⟫ = c̄·⟪Tx,x⟫` has norm
`‖c‖·‖⟪Tx,x⟫‖`, the defining supremum family scales by the nonnegative factor
`‖c‖`, and `Real.mul_iSup_of_nonneg` pushes the constant through the `⨆`. -/
theorem numericalRadiusCLM_smul (c : ℂ) (T : 𝔼 →L[ℂ] 𝔼) :
    numericalRadiusCLM (c • T) = ‖c‖ * numericalRadiusCLM T := by
  rw [numericalRadiusCLM, numericalRadiusCLM, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  refine congrArg _ (funext fun x => ?_)
  have hxx : ((c • T) x) = c • (T x) := ContinuousLinearMap.smul_apply c T x
  rw [hxx, inner_smul_left, norm_mul, RCLike.norm_conj, mul_div_assoc]

/-!
### The `k = 2` positivity core lemma
-/

/-- A unit-modulus complex number `μ` with `μ² · c = ‖c‖` (as a complex number),
for any `c : ℂ`.  For `c = 0` take `μ = 1`; for `c ≠ 0` take `μ = s̄/‖s‖` where
`s² = c` (a square root, which exists as `ℂ` is algebraically closed), so
`μ² = s̄²/‖s‖² = c̄/‖c‖` and `μ²·c = |c|²/‖c‖ = ‖c‖`.  Auxiliary rotation used to
make the quadratic form `⟪T²x,x⟫` real and nonnegative in the core lemma. -/
private theorem exists_unit_sq_mul (c : ℂ) :
    ∃ μ : ℂ, ‖μ‖ = 1 ∧ μ ^ 2 * c = (‖c‖ : ℂ) := by
  rcases eq_or_ne c 0 with hc | hc
  · exact ⟨1, by simp, by simp [hc]⟩
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq c (n := 2) (by norm_num)
    have hs0 : s ≠ 0 := by
      rintro rfl; simp at hs; exact hc hs.symm
    have hsnorm0 : (‖s‖ : ℝ) ≠ 0 := by positivity
    refine ⟨conj s / (‖s‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg s), div_self hsnorm0]
    · have hcs : (‖c‖ : ℂ) = (‖s‖ : ℂ) ^ 2 := by
        rw [← hs, norm_pow]; push_cast; ring
      have hss : conj s * s = (‖s‖ : ℂ) ^ 2 := RCLike.conj_mul s
      have hne : ((‖s‖ : ℂ)) ^ 2 ≠ 0 := by
        simpa using pow_ne_zero 2 (by exact_mod_cast hsnorm0 : (‖s‖ : ℂ) ≠ 0)
      have hnum : conj s ^ 2 * c = (‖s‖ : ℂ) ^ 2 * (‖s‖ : ℂ) ^ 2 := by
        rw [← hs, show conj s ^ 2 * s ^ 2 = (conj s * s) ^ 2 by ring, hss]; ring
      rw [div_pow, hcs, div_mul_eq_mul_div, hnum, mul_div_assoc, div_self hne, mul_one]

/-- Bilinear expansion of the "diagonal difference" of the quadratic form
`v ↦ ⟪T v, v⟫`: for any operator `T` and vectors `x, w`,
`⟪T (x+w), x+w⟫ − ⟪T (x−w), x−w⟫ = 2·⟪T x, w⟫ + 2·⟪T w, x⟫`.
Pure sesquilinear bookkeeping (the cross terms `⟪Tx,x⟫`, `⟪Tw,w⟫` cancel), used to
isolate `⟪T² x, x⟫` in the `k = 2` positivity lemma. -/
private theorem inner_diag_diff (T : 𝔼 →L[ℂ] 𝔼) (x w : 𝔼) :
    (inner ℂ (T (x + w)) (x + w) : ℂ) - inner ℂ (T (x - w)) (x - w)
      = 2 * inner ℂ (T x) w + 2 * inner ℂ (T w) x := by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right]
  ring

/-- **The `k = 2` positivity lemma (core).**  For every operator `T` on complex
Euclidean space and every vector `x`,
`‖T x‖² + ‖⟪T² x, x⟫‖ ≤ r(T)·(‖x‖² + ‖T x‖²)`.

Higham §18.1, p. 345 (the numerical-range positivity underlying Berger at `k = 2`).
Rotate by a unit phase: pick `ν` with `‖ν‖ = 1` and `ν²·⟪T²x,x⟫ = ‖⟪T²x,x⟫‖`
(`exists_unit_sq_mul`), set `w = conj ν • T x` and `u± = x ± w`.  By
`inner_diag_diff`, `⟪T up,up⟫ − ⟪T um,um⟫ = 2·⟪Tx,w⟫ + 2·⟪Tw,x⟫`, and multiplying
by `ν` gives `2·‖Tx‖² + 2·‖⟪T²x,x⟫‖` on the nose.  Bounding each diagonal term by
`r(T)‖u±‖²` (`norm_inner_apply_self_le`) and collapsing `‖up‖² + ‖um‖²` with the
parallelogram law yields the claim.  This is exactly the elementary case of the
Berger–Kato positivity route, avoiding the (Mathlib-absent) dilation machinery. -/
theorem norm_apply_sq_add_norm_inner_sq_le (T : 𝔼 →L[ℂ] 𝔼) (x : 𝔼) :
    ‖T x‖ ^ 2 + ‖(inner ℂ ((T ^ 2) x) x : ℂ)‖
      ≤ numericalRadiusCLM T * (‖x‖ ^ 2 + ‖T x‖ ^ 2) := by
  set c : ℂ := inner ℂ ((T ^ 2) x) x with hc
  obtain ⟨ν, hν1, hν2⟩ := exists_unit_sq_mul c
  set μ : ℂ := conj ν with hμ
  set w : 𝔼 := μ • T x with hw
  set up : 𝔼 := x + w with hup
  set um : 𝔼 := x - w with hum
  -- `T²x = T (T x)`
  have hT2 : (T ^ 2) x = T (T x) := by
    rw [pow_two, ContinuousLinearMap.mul_apply]
  -- the two cross inner products
  have hTxw : (inner ℂ (T x) w : ℂ) = μ * (‖T x‖ ^ 2 : ℝ) := by
    rw [hw, inner_smul_right, inner_self_eq_norm_sq_to_K]; norm_cast
  have hTwx : (inner ℂ (T w) x : ℂ) = conj μ * c := by
    have hTw : T w = μ • (T ^ 2) x := by rw [hw, map_smul, hT2]
    rw [hTw, inner_smul_left, ← hc]
  -- `μ = conj ν`, so `ν·μ = ‖ν‖² = 1` and `ν·conj μ = ν² `
  have hνμ : ν * μ = 1 := by
    rw [hμ, RCLike.mul_conj, hν1]; norm_num
  have hνcμ : ν * conj μ = ν ^ 2 := by rw [hμ, Complex.conj_conj]; ring
  -- diagonal difference identity
  have hdiff : (inner ℂ (T up) up : ℂ) - inner ℂ (T um) um
      = 2 * (μ * (‖T x‖ ^ 2 : ℝ)) + 2 * (conj μ * c) := by
    rw [hup, hum, inner_diag_diff T x w, hTxw, hTwx]
  -- multiplying by ν collapses to the real quantity `2‖Tx‖² + 2‖c‖`
  have hkey : ν * ((inner ℂ (T up) up : ℂ) - inner ℂ (T um) um)
      = ((2 * ‖T x‖ ^ 2 + 2 * ‖c‖ : ℝ) : ℂ) := by
    rw [hdiff]
    have hrw : ν * (2 * (μ * (‖T x‖ ^ 2 : ℝ)) + 2 * (conj μ * c))
        = 2 * ((ν * μ) * (‖T x‖ ^ 2 : ℝ)) + 2 * ((ν * conj μ) * c) := by ring
    rw [hrw, hνμ, hνcμ, hν2]; push_cast; ring
  -- real part bound: LHS is real, bounded by |⟪Tup,up⟫| + |⟪Tum,um⟫|
  have hboundp : ‖(inner ℂ (T up) up : ℂ)‖ ≤ numericalRadiusCLM T * ‖up‖ ^ 2 :=
    norm_inner_apply_self_le T up
  have hboundm : ‖(inner ℂ (T um) um : ℂ)‖ ≤ numericalRadiusCLM T * ‖um‖ ^ 2 :=
    norm_inner_apply_self_le T um
  -- parallelogram: ‖up‖² + ‖um‖² = 2‖x‖² + 2‖Tx‖²
  have hwnorm : ‖w‖ = ‖T x‖ := by rw [hw, norm_smul, hμ, RCLike.norm_conj, hν1, one_mul]
  have hpar : ‖up‖ ^ 2 + ‖um‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖T x‖ ^ 2 := by
    rw [hup, hum, parallelogram_law_with_norm ℂ x w, hwnorm]; ring
  -- assemble via the norm: the collapsed value is a nonnegative real, so it
  -- equals the norm of `ν·(diff)`, which the triangle inequality bounds.
  have hRnn : (0 : ℝ) ≤ 2 * ‖T x‖ ^ 2 + 2 * ‖c‖ := by positivity
  have hnormS : (2 * ‖T x‖ ^ 2 + 2 * ‖c‖ : ℝ)
      = ‖ν * ((inner ℂ (T up) up : ℂ) - inner ℂ (T um) um)‖ := by
    rw [hkey, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hRnn]
  have htri : ‖ν * ((inner ℂ (T up) up : ℂ) - inner ℂ (T um) um)‖
      ≤ ‖(inner ℂ (T up) up : ℂ)‖ + ‖(inner ℂ (T um) um : ℂ)‖ := by
    rw [norm_mul, hν1, one_mul]
    exact norm_sub_le _ _
  -- final chain
  have hchain : 2 * ‖T x‖ ^ 2 + 2 * ‖c‖
      ≤ numericalRadiusCLM T * (2 * ‖x‖ ^ 2 + 2 * ‖T x‖ ^ 2) := by
    calc 2 * ‖T x‖ ^ 2 + 2 * ‖c‖
        = ‖ν * ((inner ℂ (T up) up : ℂ) - inner ℂ (T um) um)‖ := hnormS
      _ ≤ ‖(inner ℂ (T up) up : ℂ)‖ + ‖(inner ℂ (T um) um : ℂ)‖ := htri
      _ ≤ numericalRadiusCLM T * ‖up‖ ^ 2 + numericalRadiusCLM T * ‖um‖ ^ 2 := by
            linarith [hboundp, hboundm]
      _ = numericalRadiusCLM T * (‖up‖ ^ 2 + ‖um‖ ^ 2) := by ring
      _ = numericalRadiusCLM T * (2 * ‖x‖ ^ 2 + 2 * ‖T x‖ ^ 2) := by rw [hpar]
  -- divide by 2
  nlinarith [hchain, numericalRadiusCLM_nonneg T]

/-!
### Berger for `k = 2`: `r(A²) ≤ r(A)²` (general, unconditional)
-/

/-- **Normalized `k = 2` Berger (operator form).** If `r(T) ≤ 1` then `r(T²) ≤ 1`.

Higham §18.1, p. 345.  From the core positivity lemma
`norm_apply_sq_add_norm_inner_sq_le`, when `r(T) ≤ 1` the term `(r(T)−1)‖Tx‖²` is
`≤ 0`, so `‖⟪T²x,x⟫‖ ≤ r(T)‖x‖² ≤ ‖x‖²`; dividing by `‖x‖²` and taking the
supremum gives `r(T²) ≤ 1`.  This is the WLOG-normalized Berger inequality at
`k = 2`, which the scaling homogeneity then upgrades to the homogeneous form. -/
theorem numericalRadiusCLM_pow_two_le_one_of_le_one {T : 𝔼 →L[ℂ] 𝔼}
    (hT : numericalRadiusCLM T ≤ 1) : numericalRadiusCLM (T ^ 2) ≤ 1 := by
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · have hpos : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    have hcore := norm_apply_sq_add_norm_inner_sq_le T x
    have hTxnn : (0 : ℝ) ≤ ‖T x‖ ^ 2 := by positivity
    -- `‖⟪T²x,x⟫‖ ≤ r(T)‖x‖² + (r(T)−1)‖Tx‖² ≤ ‖x‖²`
    have hbnd : ‖(inner ℂ ((T ^ 2) x) x : ℂ)‖ ≤ ‖x‖ ^ 2 := by
      nlinarith [hcore, numericalRadiusCLM_nonneg T, mul_nonneg (numericalRadiusCLM_nonneg T) hTxnn]
    rw [div_le_one hpos]
    exact hbnd

/-- **Berger's power inequality at `k = 2`, GENERAL operators, UNCONDITIONAL.**
`r(T²) ≤ r(T)²` for every continuous linear operator `T` on `ℂⁿ`.

Higham §18.1, p. 345.  A genuine new sub-result beyond the Hermitian case of
`BergerInequality.lean`.  Proof: if `r(T) = 0` the core lemma forces `T x = 0` for
all `x`, so `T² = 0` and both sides vanish.  Otherwise scale `B = r(T)⁻¹ • T`, so
`r(B) = 1` by homogeneity; the normalized bound gives `r(B²) ≤ 1`; and
`B² = r(T)⁻² • T²` with homogeneity turns this into `r(T²) ≤ r(T)²`. -/
theorem numericalRadiusCLM_pow_two_le (T : 𝔼 →L[ℂ] 𝔼) :
    numericalRadiusCLM (T ^ 2) ≤ numericalRadiusCLM T ^ 2 := by
  set r := numericalRadiusCLM T with hr
  rcases eq_or_lt_of_le (numericalRadiusCLM_nonneg T) with hr0 | hrpos
  · -- `r = 0`: the core lemma kills every `T x`, so `T² x` and its form vanish
    have hzero : ∀ x : 𝔼, ‖(inner ℂ ((T ^ 2) x) x : ℂ)‖ = 0 := by
      intro x
      have hcore := norm_apply_sq_add_norm_inner_sq_le T x
      rw [show numericalRadiusCLM T = 0 from hr0.symm, zero_mul] at hcore
      have h1 : (0 : ℝ) ≤ ‖T x‖ ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ ‖(inner ℂ ((T ^ 2) x) x : ℂ)‖ := norm_nonneg _
      linarith
    have : numericalRadiusCLM (T ^ 2) ≤ 0 := by
      refine ciSup_le fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · rw [hzero x, zero_div]
    calc numericalRadiusCLM (T ^ 2) ≤ 0 := this
      _ ≤ r ^ 2 := by positivity
  · -- `r > 0`: scale to `B = r⁻¹ • T`, so `r(B) = 1`
    have hrne : r ≠ 0 := ne_of_gt hrpos
    set B : 𝔼 →L[ℂ] 𝔼 := (r⁻¹ : ℂ) • T with hB
    have hnorm_inv : ‖(r⁻¹ : ℂ)‖ = r⁻¹ := by
      rw [show ((r⁻¹ : ℂ)) = ((r⁻¹ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hrB : numericalRadiusCLM B = 1 := by
      rw [hB, numericalRadiusCLM_smul, hnorm_inv, ← hr, inv_mul_cancel₀ hrne]
    -- `B² = r⁻² • T²` (proved pointwise; the CLM smul is not the algebra smul)
    have hBsq : B ^ 2 = ((r⁻¹ : ℂ) ^ 2) • T ^ 2 := by
      ext x
      simp only [hB, pow_two, ContinuousLinearMap.mul_apply,
        ContinuousLinearMap.smul_apply, map_smul, smul_smul]
    have hnorm_inv_sq : ‖((r⁻¹ : ℂ) ^ 2)‖ = (r ^ 2)⁻¹ := by
      rw [norm_pow, hnorm_inv]; rw [← inv_pow]
    -- normalized Berger applied to `B`
    have hB2le1 : numericalRadiusCLM (B ^ 2) ≤ 1 :=
      numericalRadiusCLM_pow_two_le_one_of_le_one (le_of_eq hrB)
    rw [hBsq, numericalRadiusCLM_smul, hnorm_inv_sq] at hB2le1
    -- `(r²)⁻¹ · r(T²) ≤ 1`  ⇒  `r(T²) ≤ r²`
    have hr2pos : (0 : ℝ) < r ^ 2 := by positivity
    rw [inv_mul_le_iff₀ hr2pos, mul_one] at hB2le1
    exact hB2le1

/-- **Scaling homogeneity (matrix form).** `r(c·A) = ‖c‖·r(A)` for a complex
matrix `A` and `c : ℂ`.

Higham §18.1, p. 345.  Transports `numericalRadiusCLM_smul` through the
`ℂ`-linear star-algebra map `Matrix.toEuclideanCLM` (`map_smul`). -/
theorem numericalRadius_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius (c • A) = ‖c‖ * numericalRadius A := by
  rw [numericalRadius, numericalRadius, map_smul, numericalRadiusCLM_smul]

/-- **Berger's power inequality at `k = 2`, GENERAL matrices, UNCONDITIONAL.**
`r(A²) ≤ r(A)²` for every complex `n × n` matrix `A`.

Higham §18.1, p. 345.  This is the central new theorem of this file: Berger's
inequality at `k = 2` for arbitrary (not necessarily Hermitian) `A`, which
`BergerInequality.lean` could only supply on the Hermitian subclass.  Transports
`numericalRadiusCLM_pow_two_le` through `Matrix.toEuclideanCLM` (`map_pow`). -/
theorem numericalRadius_pow_two_le (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius (A ^ 2) ≤ numericalRadius A ^ 2 := by
  rw [numericalRadius, numericalRadius, map_pow]
  exact numericalRadiusCLM_pow_two_le _

/-- **Berger's power inequality for every power of two, GENERAL, UNCONDITIONAL.**
`r(A^(2^m)) ≤ r(A)^(2^m)` for every complex matrix `A` and every `m : ℕ`.

Higham §18.1, p. 345.  An infinite family strictly beyond the Hermitian case.
Iterate the `k = 2` inequality: `A^(2^(m+1)) = (A^(2^m))²`, so
`r(A^(2^(m+1))) ≤ r(A^(2^m))² ≤ (r(A)^(2^m))² = r(A)^(2^(m+1))`. -/
theorem numericalRadius_pow_two_pow_le (A : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) :
    numericalRadius (A ^ 2 ^ m) ≤ numericalRadius A ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hpowA : A ^ 2 ^ (k + 1) = (A ^ 2 ^ k) ^ 2 := by
        rw [← pow_mul, pow_succ, mul_comm]
      have hpowr : numericalRadius A ^ 2 ^ (k + 1)
          = (numericalRadius A ^ 2 ^ k) ^ 2 := by
        rw [← pow_mul, pow_succ, mul_comm]
      rw [hpowA, hpowr]
      calc numericalRadius ((A ^ 2 ^ k) ^ 2)
          ≤ numericalRadius (A ^ 2 ^ k) ^ 2 := numericalRadius_pow_two_le _
        _ ≤ (numericalRadius A ^ 2 ^ k) ^ 2 := by
              gcongr
              exact numericalRadius_nonneg _

/-- **Berger for every power of two (operator form), UNCONDITIONAL.**
`r(T^(2^m)) ≤ r(T)^(2^m)` for every operator `T` and `m : ℕ`.  Operator-level
companion of `numericalRadius_pow_two_pow_le`, by the same iteration of
`numericalRadiusCLM_pow_two_le`. -/
theorem numericalRadiusCLM_pow_two_pow_le (T : 𝔼 →L[ℂ] 𝔼) (m : ℕ) :
    numericalRadiusCLM (T ^ 2 ^ m) ≤ numericalRadiusCLM T ^ 2 ^ m := by
  induction m with
  | zero => simp
  | succ k ih =>
      have hpowT : T ^ 2 ^ (k + 1) = (T ^ 2 ^ k) ^ 2 := by
        rw [← pow_mul, pow_succ, mul_comm]
      have hpowr : numericalRadiusCLM T ^ 2 ^ (k + 1)
          = (numericalRadiusCLM T ^ 2 ^ k) ^ 2 := by
        rw [← pow_mul, pow_succ, mul_comm]
      rw [hpowT, hpowr]
      calc numericalRadiusCLM ((T ^ 2 ^ k) ^ 2)
          ≤ numericalRadiusCLM (T ^ 2 ^ k) ^ 2 := numericalRadiusCLM_pow_two_le _
        _ ≤ (numericalRadiusCLM T ^ 2 ^ k) ^ 2 := by
              gcongr
              exact numericalRadiusCLM_nonneg _

/-- **The §18.1 power bound at `k = 2`, GENERAL matrices, UNCONDITIONAL.**
`‖A²‖₂ ≤ 2·r(A)²` for every complex matrix `A`.

Higham §18.1, p. 345 (`‖A^k‖₂ ≤ 2·r(A)^k` at `k = 2`).  Feeds the general
`k = 2` Berger inequality `numericalRadius_pow_two_le` into the conditional
closure `norm_pow_le_two_mul_numericalRadius_pow_of_le` of `NumericalRadius.lean`;
this discharges its `hBerger` hypothesis at `k = 2` for arbitrary `A`, without the
Hermitian restriction of `BergerInequality.lean`. -/
theorem norm_pow_two_le_two_mul_numericalRadius_sq (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖A ^ 2‖ ≤ 2 * numericalRadius A ^ 2 :=
  norm_pow_le_two_mul_numericalRadius_pow_of_le A 2 (numericalRadius_pow_two_le A)

/-!
### The resolvent-positivity route: exact identity and evidenced obstruction

The task specified attacking general Berger through the Berger–Kato positivity of
the resolvent `(I − zA)⁻¹`.  The following identity is the exact computation that
route rests on — and it pins down precisely why the *naive* form of the route
cannot reach the numerical radius.
-/

/-- **Exact resolvent real-part identity (invertibility-free form).**
For every operator `T` on `ℂⁿ` and every vector `w`,
`2·Re⟪w, w − T w⟫ − ‖w − T w‖² = ‖w‖² − ‖T w‖²`.

Higham §18.1–§18.2 (the real part of the resolvent quadratic form).  Setting
`x = w − T w = (I − T) w` (so `w = (I − T)⁻¹ x` when `I − T` is invertible) turns
the left-hand side into `2·Re⟪(I − T)⁻¹ x, x⟫ − ‖x‖²`, the quantity whose sign the
Berger–Kato route inspects.  The identity holds with NO invertibility hypothesis,
by pure inner-product expansion. -/
theorem two_re_inner_sub_apply_sub_normSq (T : 𝔼 →L[ℂ] 𝔼) (w : 𝔼) :
    2 * re (inner ℂ w (w - T w) : ℂ) - ‖w - T w‖ ^ 2 = ‖w‖ ^ 2 - ‖T w‖ ^ 2 := by
  have hnorm : ‖w - T w‖ ^ 2
      = ‖w‖ ^ 2 - 2 * re (inner ℂ w (T w) : ℂ) + ‖T w‖ ^ 2 := norm_sub_sq w (T w)
  have hre : re (inner ℂ w (w - T w) : ℂ) = ‖w‖ ^ 2 - re (inner ℂ w (T w) : ℂ) := by
    rw [inner_sub_right, map_sub, inner_self_eq_norm_sq]
  rw [hre, hnorm]; ring

/-- **Evidenced obstruction: resolvent positivity ⇔ operator-norm contraction.**
The Berger–Kato positive-real-part condition
`‖(I − T) w‖² ≤ 2·Re⟪w, (I − T) w⟫` for all `w` (equivalently, after
`x = (I − T) w`, `Re⟪(I − T)⁻¹ x, x⟫ ≥ ½‖x‖²` for all `x`) is **equivalent to**
`‖T w‖ ≤ ‖w‖` for all `w`, i.e. to `‖T‖ ≤ 1`.

Higham §18.1, p. 345.  This makes precise why the *naive* resolvent-positivity
route cannot reach the numerical radius: the positivity of the real part of the
resolvent power series `(I − zA)⁻¹ = Σ zⁿ Aⁿ` measures the **operator norm**, so
a Carathéodory/Herglotz coefficient bound built on it yields only the (trivial)
submultiplicativity `‖A^k‖ ≤ ‖A‖^k`, never Berger `r(A^k) ≤ r(A)^k`.  Genuine
numerical-radius control requires the non-analytic `ρ = 2` unitary-dilation
criterion (dilation machinery absent from Mathlib) — which is exactly why the
`k = 2` result above is instead obtained by the elementary rotation/parallelogram
positivity `norm_apply_sq_add_norm_inner_sq_le`, not by this resolvent route. -/
theorem resolvent_positive_iff_opContraction (T : 𝔼 →L[ℂ] 𝔼) :
    (∀ w : 𝔼, ‖w - T w‖ ^ 2 ≤ 2 * re (inner ℂ w (w - T w) : ℂ))
      ↔ ∀ w : 𝔼, ‖T w‖ ≤ ‖w‖ := by
  have hiff : ∀ w : 𝔼, ‖T w‖ ≤ ‖w‖ ↔ ‖T w‖ ^ 2 ≤ ‖w‖ ^ 2 := fun w =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).symm
  constructor
  · intro h w
    have hid := two_re_inner_sub_apply_sub_normSq T w
    rw [hiff w]; linarith [h w]
  · intro h w
    have hid := two_re_inner_sub_apply_sub_normSq T w
    have := (hiff w).1 (h w); linarith
