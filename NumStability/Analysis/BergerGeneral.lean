/-
Analysis/BergerGeneral.lean

The FULL general-`k` Berger power inequality for the numerical radius,
`r(A^k) ≤ r(A)^k` for ALL `k ≥ 1` and ARBITRARY complex square `A`, from Higham,
*Accuracy and Stability of Numerical Algorithms*, 2nd ed., Section 18.1 (Matrix
Powers), p. 345, Berger's power inequality [59].

`NumericalRadius.lean` develops `r(A) = ⨆ x, ‖⟪Ax,x⟫‖/‖x‖²`, the sandwich
`‖A‖₂/2 ≤ r(A) ≤ ‖A‖₂`, and closes the §18.1 power bound `‖A^k‖₂ ≤ 2·r(A)^k`
*conditionally* on Berger `r(A^k) ≤ r(A)^k`.  `BergerInequality.lean` discharges
Berger on the Hermitian subclass.  `BergerResolvent.lean` closes Berger at `k = 2`
and (by iteration) at every power of two for general `A` via elementary
rotation/parallelogram positivity, and records that the resolvent/Berger–Kato
positivity route reaches only the operator norm `‖A‖`, not `r(A)`.

This file closes the **full** Berger inequality for **every** `k` and **arbitrary**
`A`, via the elementary roots-of-unity route of

  C. Pearcy, *An elementary proof of the power inequality for the numerical
  radius*, Michigan Math. J. 13 (1966) 289–291,

which avoids unitary dilation entirely.

# The Pearcy argument (as formalized here)

Normalize `r(T) ≤ 1` (scaling homogeneity `numericalRadiusCLM_smul` upgrades the
result to the homogeneous form).  Fix a unit vector `x` and let
`ω = exp(2πi/k)` be a primitive `k`-th root of unity.  For a unit-modulus scalar
`ξ` put `ζⱼ = ξ·ωʲ` and define the *geometric-sum vectors*

      `pⱼ = Σ_{l=0}^{k-1} ζⱼ^l · (Tˡ x)`.

Two finite identities drive the proof:

  * **Telescoping** (`bergerGeneral_telescoping`):
        `pⱼ − ζⱼ · T pⱼ = x − ζⱼ^k · (Tᵏ x)`,
    the operator geometric series `Σ (ζⱼT)ˡ (I − ζⱼT) = I − (ζⱼT)ᵏ`.  Since
    `ωʲᵏ = 1`, `ζⱼ^k = ξ^k` is **independent of `j`**, so the right-hand side is a
    single vector `g = x − ξ^k·(Tᵏ x)`.

  * **Character orthogonality** (`bergerGeneral_sum_p`):
        `Σ_{j=0}^{k-1} pⱼ = k · x`,
    because `Σⱼ ζⱼ^l = ξ^l Σⱼ (ωˡ)ʲ = 0` for `1 ≤ l ≤ k-1` (geometric sum of a
    nontrivial root of unity) and `= k` for `l = 0`.

Numerical-range positivity from `r(T) ≤ 1` gives, for every `j`,
`Re⟪pⱼ − ζⱼ·T pⱼ, pⱼ⟫ = ‖pⱼ‖² − Re(ζ̄ⱼ⟪T pⱼ, pⱼ⟫) ≥ (1 − r(T))‖pⱼ‖² ≥ 0`, i.e.
`Re⟪g, pⱼ⟫ ≥ 0`.  Summing over `j` and using `Σⱼ pⱼ = k·x`,
`k·Re⟪g, x⟫ ≥ 0`, hence `Re(ξ̄^k ⟪Tᵏ x, x⟫) ≤ ‖x‖²`.  Choosing (via a unit-modulus
`k`-th root, `bergerGeneral_unit_root`) the phase `ξ` making
`Re(ξ̄^k ⟪Tᵏ x, x⟫) = |⟪Tᵏ x, x⟫|` yields `|⟪Tᵏ x, x⟫| ≤ ‖x‖²`, i.e. `r(Tᵏ) ≤ 1`.

# Main results (all over `ℂ`, unconditional, no `sorry`/`axiom`)

  * `numericalRadiusCLM_pow_le` / **`numericalRadius_pow_le`**
        -- **Berger's power inequality, FULL general form:** `r(A^k) ≤ r(A)^k`
           for every complex `n × n` matrix `A` and every `k : ℕ`.  This is the
           theorem that was left open (beyond powers of two) by the prior wave.

  * `norm_pow_le_two_mul_numericalRadius_pow`
        -- the resulting **unconditional §18.1 power bound (18.7)**
           `‖A^k‖₂ ≤ 2·r(A)^k` for ALL `A` and ALL `k`, discharging the `hBerger`
           hypothesis of `NumericalRadius.norm_pow_le_two_mul_numericalRadius_pow_of_le`
           with no Hermitian or power-of-two restriction.

Nothing is smuggled: `numericalRadius_pow_le` has no side hypothesis on `A` or
`k`; the conclusion is the printed §18.1 inequality at full strength.
-/

import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import NumStability.Analysis.NumericalRadius
import NumStability.Analysis.BergerResolvent

open scoped Matrix.Norms.L2Operator InnerProductSpace BigOperators
open RCLike ComplexConjugate Finset

namespace NumStability

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

/-!
### Finite algebraic ingredients of the Pearcy identity
-/

/-- **Unit-modulus `k`-th root selecting a phase (Pearcy phase chooser).**  For
any `c : ℂ` and `k ≥ 1` there is a unit-modulus `ξ` with
`Re(ξ̄^k · c) = ‖c‖`.  Take `ξ` a `k`-th root of `c/‖c‖` (which exists as `ℂ` is
algebraically closed); it has unit modulus since `‖c/‖c‖‖ = 1`, and then
`ξ̄^k · c = (c̄/‖c‖)·c = |c|²/‖c‖ = ‖c‖`, real.

Higham §18.1, p. 345 (Berger [59]): the phase choice that turns the real-part
bound `Re(ξ̄^k ⟪Aᵏx,x⟫) ≤ ‖x‖²` into the modulus bound `|⟪Aᵏx,x⟫| ≤ ‖x‖²`. -/
private theorem bergerGeneral_unit_root (c : ℂ) (k : ℕ) (hk : 0 < k) :
    ∃ ξ : ℂ, ‖ξ‖ = 1 ∧ (conj (ξ ^ k) * c).re = ‖c‖ := by
  rcases eq_or_ne c 0 with hc | hc
  · exact ⟨1, by simp, by simp [hc]⟩
  · have hcnorm : (‖c‖ : ℝ) ≠ 0 := by positivity
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_pow_nat_eq (c / (‖c‖ : ℂ)) hk
    have hnorm_target : ‖c / (‖c‖ : ℂ)‖ = 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg c),
        div_self (by exact_mod_cast hcnorm)]
    have hξnorm : ‖ξ‖ = 1 :=
      (pow_eq_one_iff_of_nonneg (norm_nonneg ξ) hk.ne').mp
        (by rw [← norm_pow, hξ, hnorm_target])
    refine ⟨ξ, hξnorm, ?_⟩
    rw [hξ]
    have hcc : conj c * c = ((‖c‖ : ℝ) : ℂ) ^ 2 := by
      have := RCLike.conj_mul (K := ℂ) c; rw [this]; norm_cast
    have hval : conj (c / (‖c‖ : ℂ)) * c = ((‖c‖ : ℝ) : ℂ) := by
      rw [map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, hcc,
        show ((‖c‖ : ℝ) : ℂ) ^ 2 = ((‖c‖ : ℝ) : ℂ) * ((‖c‖ : ℝ) : ℂ) by ring,
        mul_div_assoc, div_self (by exact_mod_cast hcnorm), mul_one]
    rw [hval, Complex.ofReal_re]

/-- **Operator geometric-series telescoping.**  For an operator `T`, a vector `x`,
`k : ℕ` and a scalar `ζ`, with `pₖ(x) = Σ_{l<k} ζ^l · (Tˡ x)`,
`pₖ(x) − ζ · T (pₖ(x)) = x − ζ^k · (Tᵏ x)`.

This is `(I − ζT) Σ_{l<k}(ζT)ˡ = I − (ζT)ᵏ` evaluated at `x`, proved by the
telescoping sum `Σ_{l<k}(f l − f (l+1)) = f 0 − f k` with `f l = ζ^l·(Tˡ x)`.
Higham §18.1, p. 345 (Berger [59]); the `j`-independence of the right side (once
`ζ = ξωʲ` with `ωᵏ = 1`) is what lets the averaging isolate `⟪Tᵏ x, x⟫`. -/
private theorem bergerGeneral_telescoping (T : 𝔼 →L[ℂ] 𝔼) (x : 𝔼) (k : ℕ) (ζ : ℂ) :
    (∑ l ∈ range k, ζ ^ l • ((T ^ l) x))
      - ζ • (T (∑ l ∈ range k, ζ ^ l • ((T ^ l) x)))
      = x - ζ ^ k • ((T ^ k) x) := by
  set f : ℕ → 𝔼 := fun l => ζ ^ l • ((T ^ l) x) with hf
  have hTpow : ∀ l, T ((T ^ l) x) = (T ^ (l + 1)) x := fun l => by rw [pow_succ']; rfl
  have hTsum : T (∑ l ∈ range k, ζ ^ l • ((T ^ l) x))
      = ∑ l ∈ range k, ζ ^ l • ((T ^ (l + 1)) x) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hTpow l]
  rw [hTsum, Finset.smul_sum]
  have hstep : ∀ l, ζ • (ζ ^ l • ((T ^ (l + 1)) x)) = f (l + 1) := fun l => by
    rw [hf]; simp only; rw [smul_smul, ← pow_succ']
  simp_rw [hstep]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub' f k, hf]
  simp only
  rw [pow_zero, one_smul]
  rfl

/-- **Character-orthogonality averaging of the geometric-sum vectors.**  With
`ω = exp(2πi/k)` a primitive `k`-th root of unity and any `ξ : ℂ`,
`Σ_{j<k} Σ_{l<k} (ξ·ωʲ)^l · (Tˡ x) = k · x`.

Swapping the sums, the `l`-th coefficient is `Σⱼ (ξωʲ)^l = ξ^l Σⱼ (ωˡ)ʲ`, which is
`0` for `1 ≤ l ≤ k-1` (geometric sum of the nontrivial root `ωˡ ≠ 1`) and `k` for
`l = 0`; only the `l = 0`, `T⁰ x = x` term survives.
Higham §18.1, p. 345 (Berger [59]). -/
private theorem bergerGeneral_sum_p (T : 𝔼 →L[ℂ] 𝔼) (x : 𝔼) (k : ℕ) (hk : 0 < k) (ξ : ℂ) :
    (∑ j ∈ range k, ∑ l ∈ range k,
      (ξ * Complex.exp (2 * Real.pi * Complex.I / k) ^ j) ^ l • ((T ^ l) x))
      = (k : ℂ) • x := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / k) with hω
  have hprim := Complex.isPrimitiveRoot_exp k hk.ne'
  rw [Finset.sum_comm]
  have hcoef : ∀ l ∈ range k,
      (∑ j ∈ range k, (ξ * ω ^ j) ^ l • ((T ^ l) x))
        = (if l = 0 then (k : ℂ) • x else 0) := by
    intro l hl
    rw [mem_range] at hl
    rw [← Finset.sum_smul]
    have hcoef2 : (∑ j ∈ range k, (ξ * ω ^ j) ^ l) = ξ ^ l * ∑ j ∈ range k, (ω ^ l) ^ j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by
        rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j l]
    rw [hcoef2]
    by_cases hl0 : l = 0
    · subst hl0
      simp only [pow_zero, one_pow, if_true, one_mul]
      rw [Finset.sum_const, card_range, nsmul_eq_mul, mul_one, ContinuousLinearMap.one_apply]
    · simp only [hl0, if_false]
      have hne : ω ^ l ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hl0 hl
      have hgeom : (∑ j ∈ range k, (ω ^ l) ^ j) = 0 := by
        rw [geom_sum_eq hne k]
        have hlk1 : (ω ^ l) ^ k = 1 := by
          rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
        rw [hlk1]; simp
      rw [hgeom, mul_zero, zero_smul]
  rw [Finset.sum_congr rfl hcoef, Finset.sum_ite_eq' (range k) 0 (fun _ => (k : ℂ) • x),
    if_pos (mem_range.mpr hk)]

/-- **`(c • T)^k = c^k • T^k`** at the level of continuous linear operators.  The
`ℂ`-scalar action on the composition monoid is not literally the algebra `smul`
that `smul_pow` needs, so this is proved by induction, pushing the scalar through
composition pointwise.  Auxiliary to the scaling step of the homogeneous form. -/
private theorem bergerGeneral_smul_pow (c : ℂ) (T : 𝔼 →L[ℂ] 𝔼) (k : ℕ) :
    (c • T) ^ k = (c ^ k) • (T ^ k) := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [pow_succ, pow_succ, ih, pow_succ]
      ext x
      simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, map_smul,
        smul_smul]
      ring_nf

/-!
### The normalized Pearcy bound and its consequences
-/

/-- **The Pearcy pointwise bound (normalized).**  If `r(T) ≤ 1` then for every
`k ≥ 1` and every vector `x`, `‖⟪Tᵏ x, x⟫‖ ≤ ‖x‖²`.

This is the heart of Pearcy's elementary proof (Higham §18.1, p. 345, Berger
[59]).  For the phase `ξ` from `bergerGeneral_unit_root`, the geometric-sum
vectors `pⱼ = Σ_{l<k}(ξωʲ)^l·(Tˡ x)` satisfy the telescoping
`pⱼ − (ξωʲ)·T pⱼ = g := x − ξ^k·(Tᵏ x)` (`bergerGeneral_telescoping`, using
`ωʲᵏ = 1`), so numerical-range positivity `r(T) ≤ 1` gives
`Re⟪g, pⱼ⟫ = ‖pⱼ‖² − Re((ξ̄ω̄ʲ)⟪T pⱼ, pⱼ⟫) ≥ (1 − r(T))‖pⱼ‖² ≥ 0`.  Summing over
`j` and collapsing `Σⱼ pⱼ = k·x` (`bergerGeneral_sum_p`) yields
`Re(ξ̄^k ⟪Tᵏ x, x⟫) ≤ ‖x‖²`, and the phase choice makes the left side equal to
`‖⟪Tᵏ x, x⟫‖`. -/
theorem numericalRadiusCLM_pow_pointwise_le_of_le_one {T : 𝔼 →L[ℂ] 𝔼}
    (hT : numericalRadiusCLM T ≤ 1) (k : ℕ) (hk : 0 < k) (x : 𝔼) :
    ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ ≤ ‖x‖ ^ 2 := by
  set ω := Complex.exp (2 * Real.pi * Complex.I / k) with hω
  set c : ℂ := inner ℂ ((T ^ k) x) x with hc
  obtain ⟨ξ, hξ1, hξ2⟩ := bergerGeneral_unit_root c k hk
  set p : ℕ → 𝔼 := fun j => ∑ l ∈ range k, (ξ * ω ^ j) ^ l • ((T ^ l) x) with hp
  set g : 𝔼 := x - (ξ ^ k) • ((T ^ k) x) with hg
  -- Telescoping identity, with `(ξωʲ)^k = ξ^k` since `(ωʲ)^k = 1`.
  have htele : ∀ j, p j - (ξ * ω ^ j) • (T (p j)) = g := by
    intro j
    have hbase := bergerGeneral_telescoping T x k (ξ * ω ^ j)
    rw [hp, hg]
    have hωk : (ω ^ j) ^ k = 1 := by
      have hprim := Complex.isPrimitiveRoot_exp k hk.ne'
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [mul_pow, hωk, mul_one] at hbase
    exact hbase
  -- Numerical-range positivity: `Re⟪g, pⱼ⟫ ≥ 0`.
  have hpos : ∀ j, 0 ≤ (inner ℂ g (p j) : ℂ).re := by
    intro j
    have htj := htele j
    have hexp : (inner ℂ g (p j) : ℂ)
        = ((‖p j‖ : ℂ)) ^ 2 - conj (ξ * ω ^ j) * (inner ℂ (T (p j)) (p j) : ℂ) := by
      rw [← htj, inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [hexp, Complex.sub_re]
    have hpospart : (conj (ξ * ω ^ j) * (inner ℂ (T (p j)) (p j) : ℂ)).re
        ≤ numericalRadiusCLM T * ‖p j‖ ^ 2 := by
      calc (conj (ξ * ω ^ j) * (inner ℂ (T (p j)) (p j) : ℂ)).re
          ≤ ‖conj (ξ * ω ^ j) * (inner ℂ (T (p j)) (p j) : ℂ)‖ := Complex.re_le_norm _
        _ = ‖(inner ℂ (T (p j)) (p j) : ℂ)‖ := by
            have hωn : ‖ω‖ = 1 :=
              (Complex.isPrimitiveRoot_exp k hk.ne').norm'_eq_one hk.ne'
            rw [norm_mul, RCLike.norm_conj, norm_mul, hξ1, one_mul, norm_pow, hωn,
              one_pow, one_mul]
        _ ≤ numericalRadiusCLM T * ‖p j‖ ^ 2 := norm_inner_apply_self_le T (p j)
    have hpjnn : (0 : ℝ) ≤ ‖p j‖ ^ 2 := by positivity
    have hle : numericalRadiusCLM T * ‖p j‖ ^ 2 ≤ ‖p j‖ ^ 2 := by nlinarith [hT, hpjnn]
    have hre_sq : (((‖p j‖ : ℂ)) ^ 2).re = ‖p j‖ ^ 2 := by norm_cast
    rw [hre_sq]
    linarith [hpospart, hle]
  -- Sum over `j`; collapse `Σⱼ pⱼ = k·x`.
  have hsum_g : (0 : ℝ) ≤ (inner ℂ g (∑ j ∈ range k, p j) : ℂ).re := by
    rw [inner_sum, Complex.re_sum]
    exact Finset.sum_nonneg fun j _ => hpos j
  have hsumpx : (∑ j ∈ range k, p j) = (k : ℂ) • x := by
    rw [hp]; exact bergerGeneral_sum_p T x k hk ξ
  rw [hsumpx] at hsum_g
  have hkx : (inner ℂ g ((k : ℂ) • x) : ℂ) = (k : ℂ) * inner ℂ g x := inner_smul_right g x (k : ℂ)
  have hkxre : (inner ℂ g ((k : ℂ) • x) : ℂ).re = (k : ℝ) * (inner ℂ g x : ℂ).re := by
    rw [hkx]; simp [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  rw [hkxre] at hsum_g
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hgx : 0 ≤ (inner ℂ g x : ℂ).re := by
    by_contra h
    push_neg at h
    nlinarith [hsum_g, hkpos, h]
  -- Expand `Re⟪g, x⟫` and feed in the phase choice.
  have hgxexp : (inner ℂ g x : ℂ) = ((‖x‖ : ℂ)) ^ 2 - conj (ξ ^ k) * c := by
    rw [hg, inner_sub_left, inner_smul_left, ← hc, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hxre_sq : (((‖x‖ : ℂ)) ^ 2).re = ‖x‖ ^ 2 := by norm_cast
  rw [hgxexp, Complex.sub_re, hxre_sq] at hgx
  rw [hξ2] at hgx
  linarith [hgx]

/-- **Normalized Berger (operator form).**  If `r(T) ≤ 1` then `r(Tᵏ) ≤ 1` for
every `k ≥ 1`.  Clearing the denominator in the supremum and applying the Pearcy
pointwise bound `‖⟪Tᵏx,x⟫‖ ≤ ‖x‖²`.  Higham §18.1, p. 345 (Berger [59]). -/
theorem numericalRadiusCLM_pow_le_one_of_le_one {T : 𝔼 →L[ℂ] 𝔼}
    (hT : numericalRadiusCLM T ≤ 1) (k : ℕ) (hk : 0 < k) :
    numericalRadiusCLM (T ^ k) ≤ 1 := by
  refine ciSup_le fun x => ?_
  by_cases hx : x = 0
  · simp [hx]
  · rw [div_le_one (by positivity)]
    exact numericalRadiusCLM_pow_pointwise_le_of_le_one hT k hk x

/-- **Berger's power inequality, general `k`, operator form, UNCONDITIONAL.**
`r(Tᵏ) ≤ r(T)^k` for every continuous linear operator `T` on `ℂⁿ` and every
`k : ℕ`.

Higham §18.1, p. 345 (Berger [59]).  The `k = 0` case is `r(I) ≤ 1`.  For `k ≥ 1`:
if `r(T) = 0`, scaling `M·T` (any real `M ≥ 0`) still has `r ≤ 1`, so the Pearcy
pointwise bound gives `Mᵏ·‖⟪Tᵏx,x⟫‖ ≤ ‖x‖²` for all `M`, forcing `⟪Tᵏx,x⟫ = 0` and
`r(Tᵏ) = 0`.  If `r(T) > 0`, set `B = r(T)⁻¹·T` so `r(B) = 1`
(`numericalRadiusCLM_smul`); the normalized bound gives `r(Bᵏ) ≤ 1`, and
`Bᵏ = r(T)^{-k}·Tᵏ` (`bergerGeneral_smul_pow`) turns this into `r(Tᵏ) ≤ r(T)^k`. -/
theorem numericalRadiusCLM_pow_le (T : 𝔼 →L[ℂ] 𝔼) (k : ℕ) :
    numericalRadiusCLM (T ^ k) ≤ numericalRadiusCLM T ^ k := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · -- `k = 0`: `r(T⁰) = r(I) ≤ ‖I‖ ≤ 1 = r(T)⁰`.
    subst hk0
    simp only [pow_zero]
    calc numericalRadiusCLM (1 : 𝔼 →L[ℂ] 𝔼)
        ≤ ‖(1 : 𝔼 →L[ℂ] 𝔼)‖ := numericalRadiusCLM_le_opNorm _
      _ ≤ 1 := ContinuousLinearMap.norm_id_le
  set r := numericalRadiusCLM T with hr
  rcases eq_or_lt_of_le (numericalRadiusCLM_nonneg T) with hr0 | hrpos
  · -- `r = 0`: `r(Tᵏ) ≤ 0` via unbounded scaling.
    have hzero : ∀ x : 𝔼, ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ = 0 := by
      intro x
      by_contra hne
      have hcpos : 0 < ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      -- for all `M ≥ 0`, `Mᵏ · ‖⟪Tᵏx,x⟫‖ ≤ ‖x‖²`
      have hbound : ∀ M : ℝ, 0 ≤ M →
          M ^ k * ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ ≤ ‖x‖ ^ 2 := by
        intro M hM
        have hr_eq : r = 0 := hr.trans hr0.symm
        have hrS : numericalRadiusCLM ((M : ℂ) • T) ≤ 1 := by
          rw [numericalRadiusCLM_smul, ← hr, hr_eq, mul_zero]; norm_num
        have hpt := numericalRadiusCLM_pow_pointwise_le_of_le_one hrS k hk x
        rw [bergerGeneral_smul_pow, ContinuousLinearMap.smul_apply, inner_smul_left,
          norm_mul] at hpt
        have hMk : ‖conj ((M : ℂ) ^ k)‖ = M ^ k := by
          rw [RCLike.norm_conj, norm_pow,
            show ((M : ℂ)) = ((M : ℝ) : ℂ) by norm_cast, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hM]
        rw [hMk] at hpt
        exact hpt
      -- pick `M` large: `M := ‖x‖²/c + 1`, then `M ≤ Mᵏ` and `M·c > ‖x‖²`
      set M := ‖x‖ ^ 2 / ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ + 1 with hM
      have hM1 : 1 ≤ M := by
        have : 0 ≤ ‖x‖ ^ 2 / ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ := by positivity
        rw [hM]; linarith
      have hMk : M ≤ M ^ k := le_self_pow₀ hM1 hk.ne'
      have h1 : M ^ k * ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ ≤ ‖x‖ ^ 2 :=
        hbound M (by linarith)
      have h2 : M * ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ ≤ M ^ k * ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ := by
        nlinarith [hMk, hcpos.le]
      have h3 : M * ‖(inner ℂ ((T ^ k) x) x : ℂ)‖
          = ‖x‖ ^ 2 + ‖(inner ℂ ((T ^ k) x) x : ℂ)‖ := by
        rw [hM]; field_simp
      linarith
    have hTkle : numericalRadiusCLM (T ^ k) ≤ 0 := by
      refine ciSup_le fun x => ?_
      by_cases hx : x = 0
      · simp [hx]
      · rw [hzero x, zero_div]
    calc numericalRadiusCLM (T ^ k) ≤ 0 := hTkle
      _ ≤ r ^ k := by positivity
  · -- `r > 0`: scale to `B = r⁻¹ • T`, `r(B) = 1`.
    have hrne : r ≠ 0 := ne_of_gt hrpos
    set B : 𝔼 →L[ℂ] 𝔼 := (r⁻¹ : ℂ) • T with hB
    have hnorm_inv : ‖(r⁻¹ : ℂ)‖ = r⁻¹ := by
      rw [show ((r⁻¹ : ℂ)) = ((r⁻¹ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hrB : numericalRadiusCLM B = 1 := by
      rw [hB, numericalRadiusCLM_smul, hnorm_inv, ← hr, inv_mul_cancel₀ hrne]
    have hBk : B ^ k = ((r⁻¹ : ℂ) ^ k) • T ^ k := bergerGeneral_smul_pow (r⁻¹ : ℂ) T k
    have hnorm_inv_k : ‖((r⁻¹ : ℂ) ^ k)‖ = (r ^ k)⁻¹ := by
      rw [norm_pow, hnorm_inv, ← inv_pow]
    have hBkle1 : numericalRadiusCLM (B ^ k) ≤ 1 :=
      numericalRadiusCLM_pow_le_one_of_le_one (le_of_eq hrB) k hk
    rw [hBk, numericalRadiusCLM_smul, hnorm_inv_k] at hBkle1
    have hrkpos : (0 : ℝ) < r ^ k := by positivity
    rw [inv_mul_le_iff₀ hrkpos, mul_one] at hBkle1
    exact hBkle1

/-!
### Transport to matrices and the §18.1 payoff
-/

/-- **Berger's power inequality, FULL general form (matrix form), UNCONDITIONAL.**
`r(A^k) ≤ r(A)^k` for every complex `n × n` matrix `A` and every `k : ℕ`.

Higham §18.1, p. 345, Berger's power inequality [59].  This is the full result for
arbitrary `A` and arbitrary `k`, closing the gap left by the Hermitian case of
`BergerInequality.lean` and the powers-of-two case of `BergerResolvent.lean`.
Transports the operator-level `numericalRadiusCLM_pow_le` through the star-algebra
map `Matrix.toEuclideanCLM` (`map_pow`), obtained via Pearcy's elementary
roots-of-unity argument (no unitary dilation). -/
theorem numericalRadius_pow_le (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    numericalRadius (A ^ k) ≤ numericalRadius A ^ k := by
  rw [numericalRadius, numericalRadius, map_pow]
  exact numericalRadiusCLM_pow_le _ k

/-- **The §18.1 power bound (18.7), FULL general form, UNCONDITIONAL.**
`‖A^k‖₂ ≤ 2·r(A)^k` for every complex `n × n` matrix `A` and every `k : ℕ`.

Higham §18.1, p. 345, eq. (18.7).  Feeds the full Berger inequality
`numericalRadius_pow_le` into the conditional closure
`NumericalRadius.norm_pow_le_two_mul_numericalRadius_pow_of_le`, discharging its
`hBerger` hypothesis for ALL `A` and ALL `k` — no Hermitian restriction (cf.
`BergerInequality.norm_pow_le_two_mul_numericalRadius_pow_of_isHermitian`) and no
power-of-two restriction (cf. `BergerResolvent.norm_pow_two_le_two_mul_numericalRadius_sq`).
This is the unconditional §18.1 numerical-radius power bound. -/
theorem norm_pow_le_two_mul_numericalRadius_pow (A : Matrix (Fin n) (Fin n) ℂ) (k : ℕ) :
    ‖A ^ k‖ ≤ 2 * numericalRadius A ^ k :=
  norm_pow_le_two_mul_numericalRadius_pow_of_le A k (numericalRadius_pow_le A k)

end

end NumStability
