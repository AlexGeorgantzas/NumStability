import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Data.Real.Pointwise
import Mathlib.FieldTheory.IsAlgClosed.Basic
import NumStability.Analysis.LinearOperators.NumericalRadius.Core.Basic

/-!
# Analysis.LinearOperators.NumericalRadius.Berger.PowerTwo

W06 semantic leaf. Whole declaration commands are copied from the frozen C0005 owners; local private notations are expanded at their use sites.
-/

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









open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}



/-!
### Scaling homogeneity of the numerical radius (Berger–Kato ingredient (i))
-/

/-- **Scaling homogeneity (operator form).** `r(c·T) = ‖c‖·r(T)` for `c : ℂ`.

Higham §18.1, p. 345: the numerical radius is absolutely homogeneous,
`r(cA) = |c|·r(A)`.  This is the normalization ingredient of the Berger–Kato
programme (WLOG `r(A) = 1`).  Since `⟪(c•T)x,x⟫ = c̄·⟪Tx,x⟫` has norm
`‖c‖·‖⟪Tx,x⟫‖`, the defining supremum family scales by the nonnegative factor
`‖c‖`, and `Real.mul_iSup_of_nonneg` pushes the constant through the `⨆`. -/
theorem numericalRadiusCLM_smul (c : ℂ) (T : (EuclideanSpace ℂ (Fin n)) →L[ℂ] (EuclideanSpace ℂ (Fin n))) :
    numericalRadiusCLM (c • T) = ‖c‖ * numericalRadiusCLM T := by
  rw [numericalRadiusCLM, numericalRadiusCLM, Real.mul_iSup_of_nonneg (norm_nonneg c)]
  refine congrArg _ (funext fun x => ?_)
  have hxx : ((c • T) x) = c • (T x) := ContinuousLinearMap.smul_apply c T x
  rw [hxx, inner_smul_left, norm_mul, RCLike.norm_conj, mul_div_assoc]

/-!
### The `k = 2` positivity core lemma
-/



















































































































/-!
### Berger for `k = 2`: `r(A²) ≤ r(A)²` (general, unconditional)
-/









































































/-- **Scaling homogeneity (matrix form).** `r(c·A) = ‖c‖·r(A)` for a complex
matrix `A` and `c : ℂ`.

Higham §18.1, p. 345.  Transports `numericalRadiusCLM_smul` through the
`ℂ`-linear star-algebra map `Matrix.toEuclideanCLM` (`map_smul`). -/
theorem numericalRadius_smul (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) :
    numericalRadius (c • A) = ‖c‖ * numericalRadius A := by
  rw [numericalRadius, numericalRadius, map_smul, numericalRadiusCLM_smul]





































































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
theorem two_re_inner_sub_apply_sub_normSq (T : (EuclideanSpace ℂ (Fin n)) →L[ℂ] (EuclideanSpace ℂ (Fin n))) (w : (EuclideanSpace ℂ (Fin n))) :
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
theorem resolvent_positive_iff_opContraction (T : (EuclideanSpace ℂ (Fin n)) →L[ℂ] (EuclideanSpace ℂ (Fin n))) :
    (∀ w : (EuclideanSpace ℂ (Fin n)), ‖w - T w‖ ^ 2 ≤ 2 * re (inner ℂ w (w - T w) : ℂ))
      ↔ ∀ w : (EuclideanSpace ℂ (Fin n)), ‖T w‖ ≤ ‖w‖ := by
  have hiff : ∀ w : (EuclideanSpace ℂ (Fin n)), ‖T w‖ ≤ ‖w‖ ↔ ‖T w‖ ^ 2 ≤ ‖w‖ ^ 2 := fun w =>
    (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).symm
  constructor
  · intro h w
    have hid := two_re_inner_sub_apply_sub_normSq T w
    rw [hiff w]; linarith [h w]
  · intro h w
    have hid := two_re_inner_sub_apply_sub_normSq T w
    have := (hiff w).1 (h w); linarith
