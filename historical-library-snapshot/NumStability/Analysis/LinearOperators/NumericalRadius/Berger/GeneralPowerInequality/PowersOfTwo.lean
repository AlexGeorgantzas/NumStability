import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Data.Real.Pointwise
import Mathlib.FieldTheory.IsAlgClosed.Basic
import NumStability.Analysis.LinearOperators.NumericalRadius.Berger.PowerTwo
import NumStability.Analysis.LinearOperators.NumericalRadius.Core.Basic

/-!
# Analysis.LinearOperators.NumericalRadius.Berger.GeneralPowerInequality.PowersOfTwo

R07 canonical `reusable` leaf. Reusable Berger k=2 and powers-of-two numerical-radius inequalities (`NumStability.norm_apply_sq_add_norm_inner_sq_le`, `NumStability.norm_pow_two_le_two_mul_numericalRadius_sq`, `NumStability.numericalRadiusCLM_pow_two_le`); declaration review found no resolvent statement in this group.

Whole declaration commands are copied byte-for-byte from `NumStability.Analysis.BergerResolvent`. Declaration names, visibility, namespaces, signatures, and proofs are unchanged; authored-private names are re-mangled only by their reviewed destination module.
-/


open scoped Matrix.Norms.L2Operator InnerProductSpace
open RCLike ComplexConjugate

namespace NumStability

noncomputable section

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin n)

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
