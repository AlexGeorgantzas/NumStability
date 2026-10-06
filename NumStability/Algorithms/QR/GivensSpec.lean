-- Algorithms/QR/GivensSpec.lean
--
-- Givens rotation definition and algebraic properties (Higham §18.5),
-- plus backward error model for Givens application (Lemma 18.7).
--
-- A Givens rotation G(p,q,c,s) ∈ ℝⁿˣⁿ differs from the identity only
-- at entries (p,p)=c, (q,q)=c, (p,q)=s, (q,p)=-s.
-- When c² + s² = 1, G is orthogonal. Applying G in floating-point
-- yields ŷ = (G + ΔG)x with ‖ΔG‖_F ≤ c (Lemma 18.7).

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.Norm2

namespace NumStability

open scoped BigOperators Matrix.Norms.Frobenius

-- ============================================================
-- §18.5  Givens rotation definition
-- ============================================================

/-- **Givens rotation** G(p,q,c,s) ∈ ℝⁿˣⁿ (§18.5).

    Differs from the identity only at entries
    (p,p)=c, (q,q)=c, (p,q)=s, (q,p)=−s.
    When c² + s² = 1, G is orthogonal. -/
noncomputable def givensRotation (n : ℕ) (p q : Fin n) (c s : ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i = p ∧ j = p then c
    else if i = q ∧ j = q then c
    else if i = p ∧ j = q then s
    else if i = q ∧ j = p then -s
    else if i = j then 1
    else 0

-- ============================================================
-- §18.5  Givens coefficient construction
-- ============================================================

/-- Exact denominator in Higham equation (18.14):
    `sqrt(x_i^2 + x_j^2)`. -/
noncomputable def givensDenom (xi xj : ℝ) : ℝ :=
  Real.sqrt (xi ^ 2 + xj ^ 2)

/-- Exact cosine coefficient in Higham equation (18.14). -/
noncomputable def givensC (xi xj : ℝ) : ℝ :=
  xi / givensDenom xi xj

/-- Exact sine coefficient in Higham equation (18.14). -/
noncomputable def givensS (xi xj : ℝ) : ℝ :=
  xj / givensDenom xi xj

/-- Two-vector used to reuse the existing rounded 2-norm kernel for Givens
    coefficient construction. -/
noncomputable def givensCoeffVector (xi xj : ℝ) : Fin 2 → ℝ :=
  fun k => if k = 0 then xi else xj

/-- Rounded denominator for Givens coefficient construction.  This deliberately
    reuses `fl_norm2`, so the square-root/domain analysis is shared with the
    lower-level norm kernel instead of being duplicated in the Givens file. -/
noncomputable def fl_givensDenom (fp : FPModel) (xi xj : ℝ) : ℝ :=
  fl_norm2 fp 2 (givensCoeffVector xi xj)

/-- Rounded cosine coefficient using the rounded denominator. -/
noncomputable def fl_givensC (fp : FPModel) (xi xj : ℝ) : ℝ :=
  fp.fl_div xi (fl_givensDenom fp xi xj)

/-- Rounded sine coefficient using the rounded denominator. -/
noncomputable def fl_givensS (fp : FPModel) (xi xj : ℝ) : ℝ :=
  fp.fl_div xj (fl_givensDenom fp xi xj)

@[simp] theorem givensCoeffVector_zero (xi xj : ℝ) :
    givensCoeffVector xi xj 0 = xi := by
  simp [givensCoeffVector]

@[simp] theorem givensCoeffVector_one (xi xj : ℝ) :
    givensCoeffVector xi xj 1 = xj := by
  simp [givensCoeffVector]

theorem givensCoeffVector_sum_sq (xi xj : ℝ) :
    (∑ k : Fin 2, givensCoeffVector xi xj k * givensCoeffVector xi xj k) =
      xi ^ 2 + xj ^ 2 := by
  rw [Fin.sum_univ_two]
  simp [pow_two]

theorem givensDenom_sq (xi xj : ℝ) :
    givensDenom xi xj ^ 2 = xi ^ 2 + xj ^ 2 := by
  unfold givensDenom
  rw [Real.sq_sqrt]
  exact add_nonneg (sq_nonneg xi) (sq_nonneg xj)

theorem givensDenom_ne_zero {xi xj : ℝ}
    (h : xi ^ 2 + xj ^ 2 ≠ 0) :
    givensDenom xi xj ≠ 0 := by
  intro hd
  have hsq := givensDenom_sq xi xj
  rw [hd] at hsq
  have hzero : xi ^ 2 + xj ^ 2 = 0 := by
    nlinarith
  exact h hzero

/-- Exact coefficients from (18.14) satisfy `c^2+s^2=1` whenever the source
    two-vector is nonzero. -/
theorem givensCoeff_norm_sq (xi xj : ℝ)
    (h : xi ^ 2 + xj ^ 2 ≠ 0) :
    givensC xi xj ^ 2 + givensS xi xj ^ 2 = 1 := by
  let d := givensDenom xi xj
  have hd : d ≠ 0 := givensDenom_ne_zero (xi := xi) (xj := xj) h
  have hd_sq : d ^ 2 = xi ^ 2 + xj ^ 2 := givensDenom_sq xi xj
  unfold givensC givensS
  change (xi / d) ^ 2 + (xj / d) ^ 2 = 1
  field_simp [hd]
  nlinarith

/-- The constructed exact rotation zeros the second component. -/
theorem givensCoeff_zero_second (xi xj : ℝ) :
    -givensS xi xj * xi + givensC xi xj * xj = 0 := by
  unfold givensS givensC
  by_cases hd : givensDenom xi xj = 0
  · rw [hd]
    simp
  · field_simp [hd]
    ring

/-- The first transformed component is the exact Givens denominator. -/
theorem givensCoeff_first_component (xi xj : ℝ)
    (h : xi ^ 2 + xj ^ 2 ≠ 0) :
    givensC xi xj * xi + givensS xi xj * xj = givensDenom xi xj := by
  let d := givensDenom xi xj
  have hd : d ≠ 0 := givensDenom_ne_zero (xi := xi) (xj := xj) h
  have hd_sq : d ^ 2 = xi ^ 2 + xj ^ 2 := givensDenom_sq xi xj
  unfold givensC givensS
  change xi / d * xi + xj / d * xj = d
  field_simp [hd]
  nlinarith

@[simp] theorem fl_givensDenom_unroll (fp : FPModel) (xi xj : ℝ) :
    fl_givensDenom fp xi xj = fl_norm2 fp 2 (givensCoeffVector xi xj) := rfl

@[simp] theorem fl_givensC_unroll (fp : FPModel) (xi xj : ℝ) :
    fl_givensC fp xi xj = fp.fl_div xi (fl_givensDenom fp xi xj) := rfl

@[simp] theorem fl_givensS_unroll (fp : FPModel) (xi xj : ℝ) :
    fl_givensS fp xi xj = fp.fl_div xj (fl_givensDenom fp xi xj) := rfl

/-- Conservative implementation-backed coefficient division bridge.

    This proves the shared denominator/division part for `fl_givensC` and
    `fl_givensS` from the concrete kernels.  It reuses `fl_norm2` for the
    denominator, then combines the denominator perturbation with the final
    rounded division.  The resulting `gamma fp 6` bound is intentionally
    conservative; Higham Lemma 18.6 states the sharper `gamma_4` coefficient
    bound, whose proof is omitted in the text and remains a separate target. -/
theorem fl_givensCoeff_div_relative_error_conservative (fp : FPModel)
    (xi xj z : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 6 ∧
      fp.fl_div z (fl_givensDenom fp xi xj) =
        (z / givensDenom xi xj) * (1 + θ) := by
  obtain ⟨θd, hθd, hden⟩ :=
    fl_norm2_relative_error fp 2 (givensCoeffVector xi xj) hvalid
  have hsqrt :
      Real.sqrt (∑ i : Fin 2,
        givensCoeffVector xi xj i * givensCoeffVector xi xj i) =
        givensDenom xi xj := by
    rw [givensCoeffVector_sum_sq]
    rfl
  have hden_rel :
      fl_givensDenom fp xi xj = givensDenom xi xj * (1 + θd) := by
    unfold fl_givensDenom
    rw [hden, hsqrt]
  have hθd2 : |θd| ≤ gamma fp 3 := by
    simpa using hθd
  have hγ3_lt : gamma fp 3 < 1 := by
    have hvalid6 : gammaValid fp (2 * 3) := by
      simpa using hvalid
    exact gamma_lt_one fp 3 hvalid6
  have hpos : 0 < 1 + θd := by
    linarith [neg_abs_le θd, hθd2, hγ3_lt]
  have hd_ne : givensDenom xi xj ≠ 0 :=
    givensDenom_ne_zero (xi := xi) (xj := xj) h
  have hfl_den_ne : fl_givensDenom fp xi xj ≠ 0 := by
    rw [hden_rel]
    exact mul_ne_zero hd_ne hpos.ne'
  obtain ⟨δ, hδ, hdiv⟩ :=
    fp.model_div z (fl_givensDenom fp xi xj) hfl_den_ne
  obtain ⟨ψ, hψ, hcollapse⟩ :=
    gamma_inv_mul_roundoff fp 3 θd δ (by decide) hθd2 hδ hpos (by simpa using hvalid)
  refine ⟨ψ, hψ, ?_⟩
  rw [hdiv, hden_rel]
  calc
    z / (givensDenom xi xj * (1 + θd)) * (1 + δ)
        = (z / givensDenom xi xj) * ((1 / (1 + θd)) * (1 + δ)) := by
            field_simp [hd_ne, hpos.ne']
    _ = (z / givensDenom xi xj) * (1 + ψ) := by
            rw [hcollapse]

/-- Conservative relative-error theorem for the concrete rounded Givens
    cosine coefficient. -/
theorem fl_givensC_relative_error_conservative (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 6 ∧
      fl_givensC fp xi xj = givensC xi xj * (1 + θ) := by
  simpa [fl_givensC, givensC] using
    fl_givensCoeff_div_relative_error_conservative fp xi xj xi h hvalid

/-- Conservative relative-error theorem for the concrete rounded Givens
    sine coefficient. -/
theorem fl_givensS_relative_error_conservative (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    ∃ θ : ℝ,
      |θ| ≤ gamma fp 6 ∧
      fl_givensS fp xi xj = givensS xi xj * (1 + θ) := by
  simpa [fl_givensS, givensS] using
    fl_givensCoeff_div_relative_error_conservative fp xi xj xj h hvalid

/-- Relative-error contract for computed Givens coefficients.

    Higham Lemma 18.6 supplies this contract with `μ = γ₄`.  The concrete
    theorem below currently supplies a conservative `μ = γ₆`, derived from the
    existing rounded norm and division infrastructure. -/
structure GivensCoeffError (c s c_hat s_hat μ : ℝ) : Prop where
  /-- Computed cosine is a relative perturbation of exact cosine. -/
  c_rel : ∃ θ : ℝ, |θ| ≤ μ ∧ c_hat = c * (1 + θ)
  /-- Computed sine is a relative perturbation of exact sine. -/
  s_rel : ∃ θ : ℝ, |θ| ≤ μ ∧ s_hat = s * (1 + θ)

/-- The concrete rounded Givens coefficient kernels satisfy the coefficient
    contract with a conservative `gamma fp 6` bound. -/
theorem fl_givensCoeffError_conservative (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    GivensCoeffError (givensC xi xj) (givensS xi xj)
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (gamma fp 6) := by
  constructor
  · exact fl_givensC_relative_error_conservative fp xi xj h hvalid
  · exact fl_givensS_relative_error_conservative fp xi xj h hvalid

/-- Concrete floating-point application of a Givens rotation with supplied
    exact parameters `c` and `s`.

    Only the two affected components are rounded:

    * `y_p = fl_add (fl_mul c x_p) (fl_mul s x_q)`;
    * `y_q = fl_sub (fl_mul c x_q) (fl_mul s x_p)`;
    * all other entries are copied exactly.

    This is the low-level algorithmic object needed before rebuilding
    Givens QR end-to-end.  It assumes `c` and `s` have already been supplied;
    a separate rotation-construction kernel is still needed for full Givens QR. -/
noncomputable def fl_givensApply (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if i = p then
      fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q))
    else if i = q then
      fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p))
    else
      x i

-- ============================================================
-- Point-value lemmas for givensRotation
-- ============================================================

-- Row p: G(p, j) = if j=p then c else if j=q then s else 0
private lemma giv_row_p (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (j : Fin n) :
    givensRotation n p q c s p j =
    if j = p then c else if j = q then s else 0 := by
  unfold givensRotation
  by_cases h1 : j = p
  · simp [h1]
  · by_cases h2 : j = q
    · simp [h1, h2, hpq]
    · simp [h1, h2, hpq, Ne.symm h1]

-- Row q: G(q, j) = if j=p then -s else if j=q then c else 0
private lemma giv_row_q (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (j : Fin n) :
    givensRotation n p q c s q j =
    if j = p then -s else if j = q then c else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : j = p
  · simp [h1, hqp, hpq]
  · by_cases h2 : j = q
    · simp [h1, h2, hqp, hpq]
    · simp [h1, h2, hqp, Ne.symm h2]

-- Column k (k ∉ {p,q}): G(i, k) = if i=k then 1 else 0 for any i
-- (The column index k≠p,q means all ∧-branches checking j=p or j=q are false)
private lemma giv_col_other (n : ℕ) (p q : Fin n) (c s : ℝ)
    (i k : Fin n) (hkp : k ≠ p) (hkq : k ≠ q) :
    givensRotation n p q c s i k = if i = k then 1 else 0 := by
  unfold givensRotation
  simp [hkp, hkq, Ne.symm hkp, Ne.symm hkq]

-- Row k (k ∉ {p,q}): G(k, j) = if k=j then 1 else 0 for any j
private lemma giv_row_other (n : ℕ) (p q : Fin n) (c s : ℝ)
    (k j : Fin n) (hkp : k ≠ p) (hkq : k ≠ q) :
    givensRotation n p q c s k j = if k = j then 1 else 0 := by
  unfold givensRotation; simp [hkp, hkq]

-- Column p: G(i, p) = if i=p then c else if i=q then -s else 0
private lemma giv_col_p (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (i : Fin n) :
    givensRotation n p q c s i p =
    if i = p then c else if i = q then -s else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : i = p
  · simp [h1, hqp]
  · by_cases h2 : i = q
    · simp [h1, h2, hqp, hpq]
    · simp [h1, h2, Ne.symm h1]

-- Column q: G(i, q) = if i=p then s else if i=q then c else 0
private lemma giv_col_q (n : ℕ) (p q : Fin n) (c s : ℝ) (hpq : p ≠ q) (i : Fin n) :
    givensRotation n p q c s i q =
    if i = p then s else if i = q then c else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : i = p
  · simp [h1, hpq, hqp]
  · by_cases h2 : i = q
    · simp [h1, h2, hqp]
    · simp [h1, h2, Ne.symm h2]

@[simp] theorem fl_givensApply_p (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ) :
    fl_givensApply fp n p q c s x p =
      fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q)) := by
  simp [fl_givensApply]

@[simp] theorem fl_givensApply_q (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q) :
    fl_givensApply fp n p q c s x q =
      fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p)) := by
  simp [fl_givensApply, hpq.symm]

@[simp] theorem fl_givensApply_other (fp : FPModel) (n : ℕ)
    (p q i : Fin n) (c s : ℝ) (x : Fin n → ℝ)
    (hip : i ≠ p) (hiq : i ≠ q) :
    fl_givensApply fp n p q c s x i = x i := by
  simp [fl_givensApply, hip, hiq]

private lemma sum_two_point (n : ℕ) (p q : Fin n) (a b : ℝ)
    (x : Fin n → ℝ) (hpq : p ≠ q) :
    (∑ j : Fin n, (if j = p then a else if j = q then b else 0) * x j) =
      a * x p + b * x q := by
  let f : Fin n → ℝ := fun j =>
    (if j = p then a else if j = q then b else 0) * x j
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [f, hjp, hjq]
  calc
    (∑ j : Fin n, (if j = p then a else if j = q then b else 0) * x j)
        = ∑ j : Fin n, f j := rfl
    _ = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
        rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]
        ring
    _ = a * x p + b * x q := by
        rw [hrest]
        simp [f, hpq.symm]

/-- Exact `p`-component of applying a Givens rotation to a vector. -/
theorem givensRotation_matMulVec_p (n : ℕ) (p q : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q) :
    matMulVec n (givensRotation n p q c s) x p =
      c * x p + s * x q := by
  let f : Fin n → ℝ := fun j =>
    (if j = p then c else if j = q then s else 0) * x j
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [f, hjp, hjq]
  unfold matMulVec
  calc
    (∑ j : Fin n, givensRotation n p q c s p j * x j)
        = ∑ j : Fin n, f j := by
        apply Finset.sum_congr rfl
        intro j _
        simp [f, giv_row_p n p q c s hpq j]
    _ = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
        rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]
        ring
    _ = c * x p + s * x q := by
        rw [hrest]
        simp [f, hpq.symm]

/-- Exact `q`-component of applying a Givens rotation to a vector. -/
theorem givensRotation_matMulVec_q (n : ℕ) (p q : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q) :
    matMulVec n (givensRotation n p q c s) x q =
      c * x q - s * x p := by
  let f : Fin n → ℝ := fun j =>
    (if j = p then -s else if j = q then c else 0) * x j
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [f, hjp, hjq]
  unfold matMulVec
  calc
    (∑ j : Fin n, givensRotation n p q c s q j * x j)
        = ∑ j : Fin n, f j := by
        apply Finset.sum_congr rfl
        intro j _
        simp [f, giv_row_q n p q c s hpq j]
    _ = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
        rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]
        ring
    _ = c * x q - s * x p := by
        rw [hrest]
        simp [f, hpq.symm]
        ring

/-- Unaffected components of an exact Givens application are copied. -/
theorem givensRotation_matMulVec_other (n : ℕ) (p q i : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hip : i ≠ p) (hiq : i ≠ q) :
    matMulVec n (givensRotation n p q c s) x i = x i := by
  unfold matMulVec
  rw [show (∑ j : Fin n, givensRotation n p q c s i j * x j) =
      ∑ j : Fin n, (if i = j then 1 else 0) * x j from by
        apply Finset.sum_congr rfl
        intro j _
        rw [giv_row_other n p q c s i j hip hiq]]
  simp [Finset.sum_ite_eq, Finset.mem_univ]

/-- If the two affected entries are both zero, an exact Givens application
    leaves the vector unchanged. -/
theorem givensRotation_matMulVec_pair_zero (n : ℕ) (p q : Fin n)
    (c s : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q)
    (hxp : x p = 0) (hxq : x q = 0) :
    ∀ i : Fin n, matMulVec n (givensRotation n p q c s) x i = x i := by
  intro i
  by_cases hip : i = p
  · subst i
    rw [givensRotation_matMulVec_p n p q c s x hpq, hxp, hxq]
    ring
  · by_cases hiq : i = q
    · subst i
      rw [givensRotation_matMulVec_q n p q c s x hpq, hxp, hxq]
      ring
    · exact givensRotation_matMulVec_other n p q i c s x hip hiq

/-- The exact Givens rotation constructed from entries `x p` and `x q` zeros
    the `q` component. -/
theorem givensRotation_constructed_matMulVec_q_zero (n : ℕ) (p q : Fin n)
    (xi xj : ℝ) (x : Fin n → ℝ) (hpq : p ≠ q)
    (hxp : x p = xi) (hxq : x q = xj) :
    matMulVec n
      (givensRotation n p q (givensC xi xj) (givensS xi xj)) x q = 0 := by
  calc
    matMulVec n
        (givensRotation n p q (givensC xi xj) (givensS xi xj)) x q
        = givensC xi xj * x q - givensS xi xj * x p := by
          rw [givensRotation_matMulVec_q n p q
            (givensC xi xj) (givensS xi xj) x hpq]
    _ = givensC xi xj * xj - givensS xi xj * xi := by rw [hxp, hxq]
    _ = -givensS xi xj * xi + givensC xi xj * xj := by ring
    _ = 0 := givensCoeff_zero_second xi xj

/-- G(p,q,c,s) is orthogonal when c² + s² = 1 and p ≠ q.

    Proof: GᵀG and GGᵀ both equal I. For each (i,j), the sum ∑_k G_{ki}G_{kj}
    has at most 3 nonzero terms (k=p, k=q, k=i or k=j), which collapse
    using c²+s²=1. -/
theorem givensRotation_orthogonal (n : ℕ) (p q : Fin n) (c s : ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1) :
    IsOrthogonal n (givensRotation n p q c s) := by
  have hqp : q ≠ p := hpq.symm
  have hcs' : c * c + s * s = 1 := by nlinarith [hcs]
  -- Sum splitting: extract k=p and k=q terms
  have sum_split : ∀ f : Fin n → ℝ,
      ∑ k, f k = f p + f q + ∑ k ∈ (Finset.univ.erase p).erase q, f k := by
    intro f
    have hp := Finset.mem_univ p
    have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
      Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩
    rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]; ring
  -- Membership in the erased set
  have mem_rest : ∀ k : Fin n, k ∈ (Finset.univ.erase p).erase q ↔ k ≠ q ∧ k ≠ p := by
    intro k; simp [Finset.mem_erase]
  -- p and q are not in the rest set
  have hpnr : p ∉ (Finset.univ.erase p).erase q := by simp [Finset.mem_erase]
  have hqnr : q ∉ (Finset.univ.erase p).erase q := by simp [Finset.mem_erase]
  -- ∑ k ∈ rest, (if k=a then 1 else 0) * (if k=b then 1 else 0)
  --   = if a ∈ rest then (if a=b then 1 else 0) else 0
  have delta_sum : ∀ (a b : Fin n),
      ∑ k ∈ (Finset.univ.erase p).erase q,
        (if k = a then (1:ℝ) else 0) * (if k = b then 1 else 0) =
      if a ∈ (Finset.univ.erase p).erase q then (if a = b then 1 else 0) else 0 := by
    intro a b
    by_cases ha : a ∈ (Finset.univ.erase p).erase q
    · rw [if_pos ha]
      trans ∑ k ∈ (Finset.univ.erase p).erase q,
          if k = a then (if a = b then (1:ℝ) else 0) else 0
      · apply Finset.sum_congr rfl; intro k _
        by_cases hka : k = a
        · subst hka; simp
        · simp [hka]
      · simp [ha]
    · rw [if_neg ha]
      apply Finset.sum_eq_zero; intro k hk
      have hka : k ≠ a := fun heq => ha (heq ▸ hk)
      simp [hka]
  constructor <;> intro i j
  · -- GᵀG = I: ∑_k G_{ki}·G_{kj} = δ_{ij}
    show ∑ k, givensRotation n p q c s k i * givensRotation n p q c s k j = _
    rw [sum_split,
        giv_row_p n p q c s hpq i, giv_row_p n p q c s hpq j,
        giv_row_q n p q c s hpq i, giv_row_q n p q c s hpq j]
    conv_lhs =>
      rw [show ∑ k ∈ (Finset.univ.erase p).erase q,
          givensRotation n p q c s k i * givensRotation n p q c s k j =
          ∑ k ∈ (Finset.univ.erase p).erase q,
            (if k = i then (1:ℝ) else 0) * (if k = j then 1 else 0) from by
        apply Finset.sum_congr rfl; intro k hk
        rw [mem_rest] at hk
        rw [giv_row_other n p q c s k i hk.2 hk.1,
            giv_row_other n p q c s k j hk.2 hk.1]]
    rw [delta_sum i j]
    by_cases hip : i = p
    · by_cases hjp : j = p
      · -- (p,p): c*c + (-s)*(-s) + 0 = 1
        subst hip; subst hjp
        simp only [if_true, if_neg hpq, if_neg hpnr]
        nlinarith
      · by_cases hjq : j = q
        · -- (p,q): c*s + (-s)*c + 0 = 0 ≠ 1
          subst hip; subst hjq
          simp only [if_true, if_neg hpq, if_neg hqp, if_neg hpnr]
          ring
        · -- (p, other j): 0 + 0 + 0 = 0 ≠ 1
          subst hip
          simp only [if_true, if_neg hjp, if_neg hjq, if_neg hpnr]
          simp [Ne.symm hjp, Ne.symm hjq]
    · by_cases hiq : i = q
      · by_cases hjp : j = p
        · -- (q,p): s*c + c*(-s) + 0 = 0 ≠ 1
          subst hiq; subst hjp
          simp only [if_neg hqp, if_true, if_neg hpq, if_neg hqnr]
          ring
        · by_cases hjq : j = q
          · -- (q,q): s*s + c*c + 0 = 1
            subst hiq; subst hjq
            simp only [if_neg hqp, if_true, if_neg hqnr]
            nlinarith
          · -- (q, other j): 0
            subst hiq
            simp only [if_neg hqp, if_true, if_neg hjp, if_neg hjq, if_neg hqnr]
            simp [Ne.symm hjp, Ne.symm hjq]
      · -- i ∉ {p,q}
        have hir : i ∈ (Finset.univ.erase p).erase q := by
          rw [mem_rest]; exact ⟨hiq, hip⟩
        simp only [if_neg hip, if_neg hiq, if_pos hir]
        by_cases hjp : j = p
        · subst hjp; simp [Ne.symm hip]
        · by_cases hjq : j = q
          · subst hjq; simp [Ne.symm hiq]
          · simp [Ne.symm hip, Ne.symm hiq]
  · -- GGᵀ = I: ∑_k G_{ik}·G_{jk} = δ_{ij}
    show ∑ k, givensRotation n p q c s i k * givensRotation n p q c s j k = _
    rw [sum_split,
        giv_col_p n p q c s hpq i, giv_col_p n p q c s hpq j,
        giv_col_q n p q c s hpq i, giv_col_q n p q c s hpq j]
    conv_lhs =>
      rw [show ∑ k ∈ (Finset.univ.erase p).erase q,
          givensRotation n p q c s i k * givensRotation n p q c s j k =
          ∑ k ∈ (Finset.univ.erase p).erase q,
            (if k = i then (1:ℝ) else 0) * (if k = j then 1 else 0) from by
        apply Finset.sum_congr rfl; intro k hk
        rw [mem_rest] at hk
        rw [giv_col_other n p q c s i k hk.2 hk.1,
            giv_col_other n p q c s j k hk.2 hk.1]
        simp only [eq_comm]]
    rw [delta_sum i j]
    by_cases hip : i = p
    · by_cases hjp : j = p
      · -- (p,p): c*c + s*s + 0 = 1
        subst hip; subst hjp
        simp only [if_true, if_neg hpq, if_neg hpnr]
        nlinarith
      · by_cases hjq : j = q
        · -- (p,q): c*(-s) + s*c + 0 = 0 ≠ 1
          subst hip; subst hjq
          simp only [if_true, if_neg hpq, if_neg hqp, if_neg hpnr]
          ring
        · -- (p, other j): 0
          subst hip
          simp only [if_true, if_neg hjp, if_neg hjq, if_neg hpnr]
          simp [Ne.symm hjp, Ne.symm hjq]
    · by_cases hiq : i = q
      · by_cases hjp : j = p
        · -- (q,p): (-s)*c + c*s + 0 = 0 ≠ 1
          subst hiq; subst hjp
          simp only [if_neg hqp, if_true, if_neg hpq, if_neg hqnr]
          ring
        · by_cases hjq : j = q
          · -- (q,q): (-s)*(-s) + c*c + 0 = 1
            subst hiq; subst hjq
            simp only [if_neg hqp, if_true, if_neg hqnr]
            nlinarith
          · -- (q, other j): 0
            subst hiq
            simp only [if_neg hqp, if_true, if_neg hjp, if_neg hjq, if_neg hqnr]
            simp [Ne.symm hjp, Ne.symm hjq]
      · -- i ∉ {p,q}
        have hir : i ∈ (Finset.univ.erase p).erase q := by
          rw [mem_rest]; exact ⟨hiq, hip⟩
        simp only [if_neg hip, if_neg hiq, if_pos hir]
        by_cases hjp : j = p
        · subst hjp; simp [Ne.symm hip]
        · by_cases hjq : j = q
          · subst hjq; simp [Ne.symm hiq]
          · simp [Ne.symm hip, Ne.symm hiq]

/-- The exact coefficients from (18.14) produce an orthogonal rotation. -/
theorem givensRotation_constructed_orthogonal (n : ℕ) (p q : Fin n)
    (xi xj : ℝ) (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0) :
    IsOrthogonal n (givensRotation n p q (givensC xi xj) (givensS xi xj)) :=
  givensRotation_orthogonal n p q (givensC xi xj) (givensS xi xj) hpq
    (givensCoeff_norm_sq xi xj h)

-- ============================================================
-- §18.5  Lemma 18.7: Givens application backward error
-- ============================================================

/-- **Backward error model for Givens application** (Lemma 18.7).

    When a Givens rotation G is applied to a vector x in
    floating-point arithmetic, the computed result ŷ satisfies
    ŷ = (G + ΔG)x where ‖ΔG‖_F ≤ c.

    This records the result of Lemma 18.7 as a reusable contract. The bound c
    is typically √2·γ₆ (6 flops per affected component). -/
structure GivensAppError (n : ℕ) (G : Fin n → Fin n → ℝ)
    (x y_hat : Fin n → ℝ) (c : ℝ) : Prop where
  /-- G is orthogonal. -/
  orth : IsOrthogonal n G
  /-- The computed result satisfies ŷ = (G + ΔG)x with ‖ΔG‖_F ≤ c. -/
  pert : ∃ ΔG : Fin n → Fin n → ℝ,
    frobNorm ΔG ≤ c ∧
    ∀ i, y_hat i = matMulVec n (fun a b => G a b + ΔG a b) x i

/-- A matrix perturbation is supported only on rows/columns `p` and `q`. -/
def PairBlockSupported {n : ℕ} (p q : Fin n)
    (E : Fin n → Fin n → ℝ) : Prop :=
  ∀ i j,
    ((Not (i = p) ∧ Not (i = q)) ∨ (Not (j = p) ∧ Not (j = q))) →
      E i j = 0

/-- A pair-supported perturbation has zero rows outside the active pair. -/
theorem PairBlockSupported.row_zero {n : ℕ} {p q : Fin n}
    {E : Fin n → Fin n → ℝ} (hE : PairBlockSupported p q E)
    {i : Fin n} (hip : i ≠ p) (hiq : i ≠ q) :
    ∀ j : Fin n, E i j = 0 := by
  intro j
  exact hE i j (Or.inl ⟨hip, hiq⟩)

/-- A pair-supported perturbation has zero columns outside the active pair. -/
theorem PairBlockSupported.col_zero {n : ℕ} {p q : Fin n}
    {E : Fin n → Fin n → ℝ} (hE : PairBlockSupported p q E)
    {j : Fin n} (hjp : j ≠ p) (hjq : j ≠ q) :
    ∀ i : Fin n, E i j = 0 := by
  intro i
  exact hE i j (Or.inr ⟨hjp, hjq⟩)

/-- Sparse form of `GivensAppError`, retaining the support of the local
    perturbation produced by one Givens application. -/
structure SparseGivensAppError (n : ℕ) (p q : Fin n)
    (G : Fin n → Fin n → ℝ) (x y_hat : Fin n → ℝ) (c : ℝ) : Prop where
  /-- G is orthogonal. -/
  orth : IsOrthogonal n G
  /-- The perturbation is norm-bounded and supported on the selected row pair. -/
  pert : ∃ ΔG : Fin n → Fin n → ℝ,
    frobNorm ΔG ≤ c ∧
    PairBlockSupported p q ΔG ∧
    ∀ i, y_hat i = matMulVec n (fun a b => G a b + ΔG a b) x i

/-- Forget the support information from a sparse Givens application error. -/
theorem SparseGivensAppError.to_app_error {n : ℕ} {p q : Fin n}
    {G : Fin n → Fin n → ℝ} {x y_hat : Fin n → ℝ} {c : ℝ}
    (h : SparseGivensAppError n p q G x y_hat c) :
    GivensAppError n G x y_hat c := by
  refine ⟨h.orth, ?_⟩
  obtain ⟨ΔG, hΔG, _hsupp, hrepr⟩ := h.pert
  exact ⟨ΔG, hΔG, hrepr⟩

/-- Concrete supplied-parameter Givens application satisfies a conservative
    backward-error contract.

    The theorem proves the bridge for the `fl_givensApply` kernel above:
    once exact `c,s` are supplied and satisfy `c^2+s^2=1`, the rounded
    application can be written as `(G + ΔG)x`.  The perturbation bound uses
    `gamma fp 2` for each affected entry because each coefficient is multiplied
    and then participates in one rounded add/sub.  This is a local bridge for
    supplied parameters, not the full Higham Lemma 18.7 constant for constructing
    and applying a Givens rotation. -/
theorem fl_givensApply_supplied_app_error (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1)
    (hvalid : gammaValid fp 2) :
    GivensAppError n (givensRotation n p q c s) x
      (fl_givensApply fp n p q c s x)
      (gamma fp 2 * frobNorm (givensRotation n p q c s)) := by
  obtain ⟨δcp, hδcp, hmul_cp⟩ := fp.model_mul c (x p)
  obtain ⟨δsp, hδsp, hmul_sp⟩ := fp.model_mul s (x q)
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q))
  obtain ⟨δcq, hδcq, hmul_cq⟩ := fp.model_mul c (x q)
  obtain ⟨δsq, hδsq, hmul_sq⟩ := fp.model_mul s (x p)
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p))
  have hvalid1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hu_le_γ1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos hvalid1
  have hδcpγ : |δcp| ≤ gamma fp 1 := le_trans hδcp hu_le_γ1
  have hδspγ : |δsp| ≤ gamma fp 1 := le_trans hδsp hu_le_γ1
  have hδaddγ : |δadd| ≤ gamma fp 1 := le_trans hδadd hu_le_γ1
  have hδcqγ : |δcq| ≤ gamma fp 1 := le_trans hδcq hu_le_γ1
  have hδsqγ : |δsq| ≤ gamma fp 1 := le_trans hδsq hu_le_γ1
  have hδsubγ : |δsub| ≤ gamma fp 1 := le_trans hδsub hu_le_γ1
  obtain ⟨θcp, hθcp, hθcp_eq⟩ :=
    gamma_mul fp 1 1 δcp δadd hδcpγ hδaddγ (by simpa using hvalid)
  obtain ⟨θsp, hθsp, hθsp_eq⟩ :=
    gamma_mul fp 1 1 δsp δadd hδspγ hδaddγ (by simpa using hvalid)
  obtain ⟨θcq, hθcq, hθcq_eq⟩ :=
    gamma_mul fp 1 1 δcq δsub hδcqγ hδsubγ (by simpa using hvalid)
  obtain ⟨θsq, hθsq, hθsq_eq⟩ :=
    gamma_mul fp 1 1 δsq δsub hδsqγ hδsubγ (by simpa using hvalid)
  have hθcp2 : |θcp| ≤ gamma fp 2 := by simpa using hθcp
  have hθsp2 : |θsp| ≤ gamma fp 2 := by simpa using hθsp
  have hθcq2 : |θcq| ≤ gamma fp 2 := by simpa using hθcq
  have hθsq2 : |θsq| ≤ gamma fp 2 := by simpa using hθsq
  let ΔG : Fin n → Fin n → ℝ := fun i j =>
    if i = p ∧ j = p then c * θcp
    else if i = p ∧ j = q then s * θsp
    else if i = q ∧ j = q then c * θcq
    else if i = q ∧ j = p then -s * θsq
    else 0
  have hγ2_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hvalid
  have hmul_bound :
      ∀ a θ : ℝ, |θ| ≤ gamma fp 2 → |a * θ| ≤ gamma fp 2 * |a| := by
    intro a θ hθ
    calc
      |a * θ| = |a| * |θ| := by rw [abs_mul]
      _ ≤ |a| * gamma fp 2 := mul_le_mul_of_nonneg_left hθ (abs_nonneg a)
      _ = gamma fp 2 * |a| := by ring
  have hp_alg :
      fl_givensApply fp n p q c s x p =
        c * (1 + θcp) * x p + s * (1 + θsp) * x q := by
    calc
      fl_givensApply fp n p q c s x p
          = fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q)) := by
              simp
      _ = (fp.fl_mul c (x p) + fp.fl_mul s (x q)) * (1 + δadd) := hadd
      _ = ((c * x p) * (1 + δcp) + (s * x q) * (1 + δsp)) *
            (1 + δadd) := by rw [hmul_cp, hmul_sp]
      _ = c * x p * ((1 + δcp) * (1 + δadd)) +
            s * x q * ((1 + δsp) * (1 + δadd)) := by ring
      _ = c * x p * (1 + θcp) + s * x q * (1 + θsp) := by
            rw [hθcp_eq, hθsp_eq]
      _ = c * (1 + θcp) * x p + s * (1 + θsp) * x q := by ring
  have hq_alg :
      fl_givensApply fp n p q c s x q =
        c * (1 + θcq) * x q - s * (1 + θsq) * x p := by
    calc
      fl_givensApply fp n p q c s x q
          = fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p)) := by
              exact fl_givensApply_q fp n p q c s x hpq
      _ = (fp.fl_mul c (x q) - fp.fl_mul s (x p)) * (1 + δsub) := hsub
      _ = ((c * x q) * (1 + δcq) - (s * x p) * (1 + δsq)) *
            (1 + δsub) := by rw [hmul_cq, hmul_sq]
      _ = c * x q * ((1 + δcq) * (1 + δsub)) -
            s * x p * ((1 + δsq) * (1 + δsub)) := by ring
      _ = c * x q * (1 + θcq) - s * x p * (1 + θsq) := by
            rw [hθcq_eq, hθsq_eq]
      _ = c * (1 + θcq) * x q - s * (1 + θsq) * x p := by ring
  refine ⟨givensRotation_orthogonal n p q c s hpq hcs, ?_⟩
  refine ⟨ΔG, ?_, ?_⟩
  · apply frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    · exact hγ2_nonneg
    · intro i j
      by_cases hip : i = p
      ·
        by_cases hjp : j = p
        ·
          have hΔ : ΔG i j = c * θcp := by simp [ΔG, hip, hjp]
          have hG : givensRotation n p q c s i j = c := by
            simp [givensRotation, hip, hjp]
          rw [hΔ, hG]
          exact hmul_bound c θcp hθcp2
        · by_cases hjq : j = q
          ·
            have hΔ : ΔG i j = s * θsp := by
              simp [ΔG, hip, hjq, hpq.symm]
            have hG : givensRotation n p q c s i j = s := by
              simp [givensRotation, hip, hjq, hpq, hpq.symm]
            rw [hΔ, hG]
            exact hmul_bound s θsp hθsp2
          ·
            have hΔ : ΔG i j = 0 := by simp [ΔG, hip, hjp, hjq]
            rw [hΔ, abs_zero]
            exact mul_nonneg hγ2_nonneg (abs_nonneg _)
      · by_cases hiq : i = q
        ·
          by_cases hjq : j = q
          ·
            have hΔ : ΔG i j = c * θcq := by
              simp [ΔG, hiq, hjq, hpq.symm]
            have hG : givensRotation n p q c s i j = c := by
              simp [givensRotation, hiq, hjq, hpq.symm]
            rw [hΔ, hG]
            exact hmul_bound c θcq hθcq2
          · by_cases hjp : j = p
            ·
              have hΔ : ΔG i j = -s * θsq := by
                simp [ΔG, hiq, hjp, hpq, hpq.symm]
              have hG : givensRotation n p q c s i j = -s := by
                simp [givensRotation, hiq, hjp, hpq, hpq.symm]
              have hneg : |-s * θsq| ≤ gamma fp 2 * |-s| :=
                hmul_bound (-s) θsq hθsq2
              rw [hΔ, hG]
              simpa [abs_neg] using hneg
            ·
              have hΔ : ΔG i j = 0 := by simp [ΔG, hiq, hjp, hjq]
              rw [hΔ, abs_zero]
              exact mul_nonneg hγ2_nonneg (abs_nonneg _)
        ·
          have hΔ : ΔG i j = 0 := by simp [ΔG, hip, hiq]
          rw [hΔ, abs_zero]
          exact mul_nonneg hγ2_nonneg (abs_nonneg _)
  · intro i
    by_cases hip : i = p
    · subst i
      have hrow : ∀ j : Fin n,
          givensRotation n p q c s p j + ΔG p j =
            if j = p then c * (1 + θcp)
            else if j = q then s * (1 + θsp)
            else 0 := by
        intro j
        rw [giv_row_p n p q c s hpq j]
        by_cases hjp : j = p
        · simp [ΔG, hjp]
          ring
        · by_cases hjq : j = q
          · simp [ΔG, hjq, hpq.symm]
            ring
          · simp [ΔG, hjp, hjq]
      calc
        fl_givensApply fp n p q c s x p
            = c * (1 + θcp) * x p + s * (1 + θsp) * x q := hp_alg
        _ = (∑ j : Fin n,
              (if j = p then c * (1 + θcp)
               else if j = q then s * (1 + θsp)
               else 0) * x j) := by
              rw [sum_two_point n p q (c * (1 + θcp)) (s * (1 + θsp)) x hpq]
        _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x p := by
              unfold matMulVec
              apply Finset.sum_congr rfl
              intro j _
              change (if j = p then c * (1 + θcp)
                else if j = q then s * (1 + θsp)
                else 0) * x j =
                (givensRotation n p q c s p j + ΔG p j) * x j
              rw [hrow j]
    · by_cases hiq : i = q
      · subst i
        have hrow : ∀ j : Fin n,
            givensRotation n p q c s q j + ΔG q j =
              if j = p then -s * (1 + θsq)
              else if j = q then c * (1 + θcq)
              else 0 := by
          intro j
          rw [giv_row_q n p q c s hpq j]
          by_cases hjp : j = p
          · simp [ΔG, hjp, hpq, hpq.symm]
            ring_nf
          · by_cases hjq : j = q
            · simp [ΔG, hjq, hpq.symm]
              ring
            · simp [ΔG, hjp, hjq]
        calc
          fl_givensApply fp n p q c s x q
              = c * (1 + θcq) * x q - s * (1 + θsq) * x p := hq_alg
          _ = (-s * (1 + θsq)) * x p + (c * (1 + θcq)) * x q := by ring
          _ = (∑ j : Fin n,
                (if j = p then -s * (1 + θsq)
                 else if j = q then c * (1 + θcq)
                 else 0) * x j) := by
                rw [sum_two_point n p q (-s * (1 + θsq)) (c * (1 + θcq)) x hpq]
          _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x q := by
                unfold matMulVec
                apply Finset.sum_congr rfl
                intro j _
                change (if j = p then -s * (1 + θsq)
                  else if j = q then c * (1 + θcq)
                  else 0) * x j =
                  (givensRotation n p q c s q j + ΔG q j) * x j
                rw [hrow j]
      · have hΔrow : ∀ j : Fin n, ΔG i j = 0 := by
          intro j
          simp [ΔG, hip, hiq]
        calc
          fl_givensApply fp n p q c s x i = x i := by
            simp [fl_givensApply, hip, hiq]
          _ = matMulVec n (givensRotation n p q c s) x i := by
            rw [givensRotation_matMulVec_other n p q i c s x hip hiq]
          _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x i := by
            unfold matMulVec
            apply Finset.sum_congr rfl
            intro j _
            simp [hΔrow j]

/-- Sparse conservative coefficient-plus-application Givens bridge.

    This theorem combines a coefficient relative-error contract with the
    concrete `fl_givensApply` kernel.  If the supplied rounded coefficients
    satisfy `c_hat = c(1+θ)` and `s_hat = s(1+θ')` with coefficient errors
    bounded by `gamma fp 6`, then the rounded application is a backward
    perturbation of the exact orthogonal rotation with a conservative
    `gamma fp 8` entrywise/Frobenius bound.  The perturbation is also recorded
    as supported on the two rows/columns touched by the Givens rotation.

    This is implementation-backed once paired with
    `fl_givensCoeffError_conservative`; the constant is intentionally not
    advertised as Higham's sharper Lemma 18.7 `sqrt 2 * gamma_6` bound. -/
theorem fl_givensApply_coeffError_sparse_app_error (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s c_hat s_hat μ : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1)
    (hμ : μ ≤ gamma fp 6)
    (hcoeff : GivensCoeffError c s c_hat s_hat μ)
    (hvalid : gammaValid fp 8) :
    SparseGivensAppError n p q (givensRotation n p q c s) x
      (fl_givensApply fp n p q c_hat s_hat x)
      (gamma fp 8 * frobNorm (givensRotation n p q c s)) := by
  obtain ⟨εc, hεc, hc_hat⟩ := hcoeff.c_rel
  obtain ⟨εs, hεs, hs_hat⟩ := hcoeff.s_rel
  obtain ⟨δcp, hδcp, hmul_cp⟩ := fp.model_mul c_hat (x p)
  obtain ⟨δsp, hδsp, hmul_sp⟩ := fp.model_mul s_hat (x q)
  obtain ⟨δadd, hδadd, hadd⟩ :=
    fp.model_add (fp.fl_mul c_hat (x p)) (fp.fl_mul s_hat (x q))
  obtain ⟨δcq, hδcq, hmul_cq⟩ := fp.model_mul c_hat (x q)
  obtain ⟨δsq, hδsq, hmul_sq⟩ := fp.model_mul s_hat (x p)
  obtain ⟨δsub, hδsub, hsub⟩ :=
    fp.model_sub (fp.fl_mul c_hat (x q)) (fp.fl_mul s_hat (x p))
  have hvalid1 : gammaValid fp 1 := gammaValid_mono fp (by omega) hvalid
  have hu_le_γ1 : fp.u ≤ gamma fp 1 := u_le_gamma fp one_pos hvalid1
  have hεc6 : |εc| ≤ gamma fp 6 := le_trans hεc hμ
  have hεs6 : |εs| ≤ gamma fp 6 := le_trans hεs hμ
  have hδcpγ : |δcp| ≤ gamma fp 1 := le_trans hδcp hu_le_γ1
  have hδspγ : |δsp| ≤ gamma fp 1 := le_trans hδsp hu_le_γ1
  have hδaddγ : |δadd| ≤ gamma fp 1 := le_trans hδadd hu_le_γ1
  have hδcqγ : |δcq| ≤ gamma fp 1 := le_trans hδcq hu_le_γ1
  have hδsqγ : |δsq| ≤ gamma fp 1 := le_trans hδsq hu_le_γ1
  have hδsubγ : |δsub| ≤ gamma fp 1 := le_trans hδsub hu_le_γ1
  have hvalid7 : gammaValid fp 7 := gammaValid_mono fp (by omega) hvalid
  obtain ⟨φcp, hφcp, hφcp_eq⟩ :=
    gamma_mul fp 6 1 εc δcp hεc6 hδcpγ (by simpa using hvalid7)
  obtain ⟨φsp, hφsp, hφsp_eq⟩ :=
    gamma_mul fp 6 1 εs δsp hεs6 hδspγ (by simpa using hvalid7)
  obtain ⟨φcq, hφcq, hφcq_eq⟩ :=
    gamma_mul fp 6 1 εc δcq hεc6 hδcqγ (by simpa using hvalid7)
  obtain ⟨φsq, hφsq, hφsq_eq⟩ :=
    gamma_mul fp 6 1 εs δsq hεs6 hδsqγ (by simpa using hvalid7)
  obtain ⟨θcp, hθcp, hθcp_eq⟩ :=
    gamma_mul fp 7 1 φcp δadd (by simpa using hφcp) hδaddγ (by simpa using hvalid)
  obtain ⟨θsp, hθsp, hθsp_eq⟩ :=
    gamma_mul fp 7 1 φsp δadd (by simpa using hφsp) hδaddγ (by simpa using hvalid)
  obtain ⟨θcq, hθcq, hθcq_eq⟩ :=
    gamma_mul fp 7 1 φcq δsub (by simpa using hφcq) hδsubγ (by simpa using hvalid)
  obtain ⟨θsq, hθsq, hθsq_eq⟩ :=
    gamma_mul fp 7 1 φsq δsub (by simpa using hφsq) hδsubγ (by simpa using hvalid)
  have hθcp8 : |θcp| ≤ gamma fp 8 := by simpa using hθcp
  have hθsp8 : |θsp| ≤ gamma fp 8 := by simpa using hθsp
  have hθcq8 : |θcq| ≤ gamma fp 8 := by simpa using hθcq
  have hθsq8 : |θsq| ≤ gamma fp 8 := by simpa using hθsq
  let ΔG : Fin n → Fin n → ℝ := fun i j =>
    if i = p ∧ j = p then c * θcp
    else if i = p ∧ j = q then s * θsp
    else if i = q ∧ j = q then c * θcq
    else if i = q ∧ j = p then -s * θsq
    else 0
  have hγ8_nonneg : 0 ≤ gamma fp 8 := gamma_nonneg fp hvalid
  have hmul_bound :
      ∀ a θ : ℝ, |θ| ≤ gamma fp 8 → |a * θ| ≤ gamma fp 8 * |a| := by
    intro a θ hθ
    calc
      |a * θ| = |a| * |θ| := by rw [abs_mul]
      _ ≤ |a| * gamma fp 8 := mul_le_mul_of_nonneg_left hθ (abs_nonneg a)
      _ = gamma fp 8 * |a| := by ring
  have hp_alg :
      fl_givensApply fp n p q c_hat s_hat x p =
        c * (1 + θcp) * x p + s * (1 + θsp) * x q := by
    calc
      fl_givensApply fp n p q c_hat s_hat x p
          = fp.fl_add (fp.fl_mul c_hat (x p)) (fp.fl_mul s_hat (x q)) := by
              simp
      _ = (fp.fl_mul c_hat (x p) + fp.fl_mul s_hat (x q)) * (1 + δadd) := hadd
      _ = ((c_hat * x p) * (1 + δcp) + (s_hat * x q) * (1 + δsp)) *
            (1 + δadd) := by rw [hmul_cp, hmul_sp]
      _ = ((c * (1 + εc) * x p) * (1 + δcp) +
            (s * (1 + εs) * x q) * (1 + δsp)) * (1 + δadd) := by
              rw [hc_hat, hs_hat]
      _ = c * x p * ((1 + εc) * (1 + δcp) * (1 + δadd)) +
            s * x q * ((1 + εs) * (1 + δsp) * (1 + δadd)) := by ring
      _ = c * x p * ((1 + φcp) * (1 + δadd)) +
            s * x q * ((1 + φsp) * (1 + δadd)) := by
              rw [hφcp_eq, hφsp_eq]
      _ = c * x p * (1 + θcp) + s * x q * (1 + θsp) := by
              rw [hθcp_eq, hθsp_eq]
      _ = c * (1 + θcp) * x p + s * (1 + θsp) * x q := by ring
  have hq_alg :
      fl_givensApply fp n p q c_hat s_hat x q =
        c * (1 + θcq) * x q - s * (1 + θsq) * x p := by
    calc
      fl_givensApply fp n p q c_hat s_hat x q
          = fp.fl_sub (fp.fl_mul c_hat (x q)) (fp.fl_mul s_hat (x p)) := by
              exact fl_givensApply_q fp n p q c_hat s_hat x hpq
      _ = (fp.fl_mul c_hat (x q) - fp.fl_mul s_hat (x p)) * (1 + δsub) := hsub
      _ = ((c_hat * x q) * (1 + δcq) - (s_hat * x p) * (1 + δsq)) *
            (1 + δsub) := by rw [hmul_cq, hmul_sq]
      _ = ((c * (1 + εc) * x q) * (1 + δcq) -
            (s * (1 + εs) * x p) * (1 + δsq)) * (1 + δsub) := by
              rw [hc_hat, hs_hat]
      _ = c * x q * ((1 + εc) * (1 + δcq) * (1 + δsub)) -
            s * x p * ((1 + εs) * (1 + δsq) * (1 + δsub)) := by ring
      _ = c * x q * ((1 + φcq) * (1 + δsub)) -
            s * x p * ((1 + φsq) * (1 + δsub)) := by
              rw [hφcq_eq, hφsq_eq]
      _ = c * x q * (1 + θcq) - s * x p * (1 + θsq) := by
              rw [hθcq_eq, hθsq_eq]
      _ = c * (1 + θcq) * x q - s * (1 + θsq) * x p := by ring
  refine ⟨givensRotation_orthogonal n p q c s hpq hcs, ?_⟩
  refine ⟨ΔG, ?_, ?_, ?_⟩
  · apply frobNorm_le_const_mul_frobNorm_of_entrywise_abs_le
    · exact hγ8_nonneg
    · intro i j
      by_cases hip : i = p
      · by_cases hjp : j = p
        · have hΔ : ΔG i j = c * θcp := by simp [ΔG, hip, hjp]
          have hG : givensRotation n p q c s i j = c := by
            simp [givensRotation, hip, hjp]
          rw [hΔ, hG]
          exact hmul_bound c θcp hθcp8
        · by_cases hjq : j = q
          · have hΔ : ΔG i j = s * θsp := by
              simp [ΔG, hip, hjq, hpq.symm]
            have hG : givensRotation n p q c s i j = s := by
              simp [givensRotation, hip, hjq, hpq, hpq.symm]
            rw [hΔ, hG]
            exact hmul_bound s θsp hθsp8
          · have hΔ : ΔG i j = 0 := by simp [ΔG, hip, hjp, hjq]
            rw [hΔ, abs_zero]
            exact mul_nonneg hγ8_nonneg (abs_nonneg _)
      · by_cases hiq : i = q
        · by_cases hjq : j = q
          · have hΔ : ΔG i j = c * θcq := by
              simp [ΔG, hiq, hjq, hpq.symm]
            have hG : givensRotation n p q c s i j = c := by
              simp [givensRotation, hiq, hjq, hpq.symm]
            rw [hΔ, hG]
            exact hmul_bound c θcq hθcq8
          · by_cases hjp : j = p
            · have hΔ : ΔG i j = -s * θsq := by
                simp [ΔG, hiq, hjp, hpq, hpq.symm]
              have hG : givensRotation n p q c s i j = -s := by
                simp [givensRotation, hiq, hjp, hpq, hpq.symm]
              have hneg : |-s * θsq| ≤ gamma fp 8 * |-s| :=
                hmul_bound (-s) θsq hθsq8
              rw [hΔ, hG]
              simpa [abs_neg] using hneg
            · have hΔ : ΔG i j = 0 := by simp [ΔG, hiq, hjp, hjq]
              rw [hΔ, abs_zero]
              exact mul_nonneg hγ8_nonneg (abs_nonneg _)
        · have hΔ : ΔG i j = 0 := by simp [ΔG, hip, hiq]
          rw [hΔ, abs_zero]
          exact mul_nonneg hγ8_nonneg (abs_nonneg _)
  · intro i j hsupp
    rcases hsupp with hrow | hcol
    · simp [ΔG, hrow.1, hrow.2]
    · simp [ΔG, hcol.1, hcol.2]
  · intro i
    by_cases hip : i = p
    · subst i
      have hrow : ∀ j : Fin n,
          givensRotation n p q c s p j + ΔG p j =
            if j = p then c * (1 + θcp)
            else if j = q then s * (1 + θsp)
            else 0 := by
        intro j
        rw [giv_row_p n p q c s hpq j]
        by_cases hjp : j = p
        · simp [ΔG, hjp]
          ring
        · by_cases hjq : j = q
          · simp [ΔG, hjq, hpq.symm]
            ring
          · simp [ΔG, hjp, hjq]
      calc
        fl_givensApply fp n p q c_hat s_hat x p
            = c * (1 + θcp) * x p + s * (1 + θsp) * x q := hp_alg
        _ = (∑ j : Fin n,
              (if j = p then c * (1 + θcp)
               else if j = q then s * (1 + θsp)
               else 0) * x j) := by
              rw [sum_two_point n p q (c * (1 + θcp)) (s * (1 + θsp)) x hpq]
        _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x p := by
              unfold matMulVec
              apply Finset.sum_congr rfl
              intro j _
              change (if j = p then c * (1 + θcp)
                else if j = q then s * (1 + θsp)
                else 0) * x j =
                (givensRotation n p q c s p j + ΔG p j) * x j
              rw [hrow j]
    · by_cases hiq : i = q
      · subst i
        have hrow : ∀ j : Fin n,
            givensRotation n p q c s q j + ΔG q j =
              if j = p then -s * (1 + θsq)
              else if j = q then c * (1 + θcq)
              else 0 := by
          intro j
          rw [giv_row_q n p q c s hpq j]
          by_cases hjp : j = p
          · simp [ΔG, hjp, hpq, hpq.symm]
            ring_nf
          · by_cases hjq : j = q
            · simp [ΔG, hjq, hpq.symm]
              ring
            · simp [ΔG, hjp, hjq]
        calc
          fl_givensApply fp n p q c_hat s_hat x q
              = c * (1 + θcq) * x q - s * (1 + θsq) * x p := hq_alg
          _ = (-s * (1 + θsq)) * x p + (c * (1 + θcq)) * x q := by ring
          _ = (∑ j : Fin n,
                (if j = p then -s * (1 + θsq)
                 else if j = q then c * (1 + θcq)
                 else 0) * x j) := by
                rw [sum_two_point n p q (-s * (1 + θsq)) (c * (1 + θcq)) x hpq]
          _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x q := by
                unfold matMulVec
                apply Finset.sum_congr rfl
                intro j _
                change (if j = p then -s * (1 + θsq)
                  else if j = q then c * (1 + θcq)
                  else 0) * x j =
                  (givensRotation n p q c s q j + ΔG q j) * x j
                rw [hrow j]
      · have hΔrow : ∀ j : Fin n, ΔG i j = 0 := by
          intro j
          simp [ΔG, hip, hiq]
        calc
          fl_givensApply fp n p q c_hat s_hat x i = x i := by
            simp [fl_givensApply, hip, hiq]
          _ = matMulVec n (givensRotation n p q c s) x i := by
            rw [givensRotation_matMulVec_other n p q i c s x hip hiq]
          _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x i := by
            unfold matMulVec
            apply Finset.sum_congr rfl
            intro j _
            simp [hΔrow j]

/-- Conservative coefficient-plus-application Givens bridge.

    This is the support-forgetting version of
    `fl_givensApply_coeffError_sparse_app_error`. -/
theorem fl_givensApply_coeffError_app_error (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s c_hat s_hat μ : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1)
    (hμ : μ ≤ gamma fp 6)
    (hcoeff : GivensCoeffError c s c_hat s_hat μ)
    (hvalid : gammaValid fp 8) :
    GivensAppError n (givensRotation n p q c s) x
      (fl_givensApply fp n p q c_hat s_hat x)
      (gamma fp 8 * frobNorm (givensRotation n p q c s)) := by
  exact (fl_givensApply_coeffError_sparse_app_error fp n p q
    c s c_hat s_hat μ x hpq hcs hμ hcoeff hvalid).to_app_error

/-- Concrete computed-coefficient Givens application bridge with support
    retained.

    This is the current implementation-backed version of the coefficient
    construction plus application path: coefficients are produced by
    `fl_givensC`/`fl_givensS`, then applied by `fl_givensApply`. -/
theorem fl_givensApply_computed_sparse_app_error_conservative
    (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    SparseGivensAppError n p q
      (givensRotation n p q (givensC xi xj) (givensS xi xj)) x
      (fl_givensApply fp n p q
        (fl_givensC fp xi xj) (fl_givensS fp xi xj) x)
      (gamma fp 8 *
        frobNorm (givensRotation n p q (givensC xi xj) (givensS xi xj))) := by
  have hcoeff :=
    fl_givensCoeffError_conservative fp xi xj h
      (gammaValid_mono fp (by omega) hvalid)
  exact fl_givensApply_coeffError_sparse_app_error fp n p q
    (givensC xi xj) (givensS xi xj)
    (fl_givensC fp xi xj) (fl_givensS fp xi xj) (gamma fp 6) x
    hpq (givensCoeff_norm_sq xi xj h) (le_rfl) hcoeff hvalid

/-- Concrete computed-coefficient Givens application bridge.

    This is the current implementation-backed version of the coefficient
    construction plus application path: coefficients are produced by
    `fl_givensC`/`fl_givensS`, then applied by `fl_givensApply`.  The proof
    is conservative (`gamma fp 8`) because it reuses the existing rounded norm
    plus division analysis rather than Higham's omitted sharper coefficient
    proof for Lemma 18.6. -/
theorem fl_givensApply_computed_app_error_conservative (fp : FPModel) (n : ℕ)
    (p q : Fin n) (xi xj : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 8) :
    GivensAppError n
      (givensRotation n p q (givensC xi xj) (givensS xi xj)) x
      (fl_givensApply fp n p q
        (fl_givensC fp xi xj) (fl_givensS fp xi xj) x)
      (gamma fp 8 *
        frobNorm (givensRotation n p q (givensC xi xj) (givensS xi xj))) := by
  exact (fl_givensApply_computed_sparse_app_error_conservative fp n p q
    xi xj x hpq h hvalid).to_app_error

end NumStability
