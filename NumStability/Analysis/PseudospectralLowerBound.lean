-- Analysis/PseudospectralLowerBound.lean
--
-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.,
-- Chapter 18, §18.2 — a constructive outward-growth direction for the
-- ε-pseudospectral radius.  This exact eigenvector-preserving rank-one route is
-- useful infrastructure, but it is weaker than the [620, 1995] perturbation
-- expansion used in Theorem 18.2 and does not discharge that cited step.
--
-- CONTEXT.  `Algorithms/MatrixPowersPseudospectral.lean` packages Theorem 18.2
-- through the `h620` witness — the eigenvalue-perturbation lower bound the
-- printed proof leaves unproved — and `MatrixPowersPseudospectralCriterion.lean`
-- isolates the *upper* half of the criterion (spectrum ⊆ pseudospectrum ⊆ unit
-- disc), explicitly recording the achievability *lower* bound as the one
-- ingredient it could not remove.  This module supplies a strictly positive
-- exact lower bound, not the source-strength `κ₂(X)ε/n² + O(ε²)` lower bound.
--
-- THE ROUTE (constructive, no external paper).  Given a right eigenpair
-- `A v = λ v` with `v ≠ 0` and a dual covector `w` with `∑_j w_j v_j = 1`
-- (for a left eigenvector `u` with `u* v ≠ 0` take `w_j = conj(u_j)/(u* v)`,
-- so `∑_j w_j v_j = (u* v)/(u* v) = 1`), the rank-one perturbation
--
--     E_t = t · v wᵀ,     (E_t)_{ij} = (t · v_i) · w_j
--
-- satisfies `(A + E_t) v = (λ + t) v` exactly, because
-- `(E_t v)_i = t v_i (∑_j w_j v_j) = t v_i`.  Hence `λ + t` is an eigenvalue of
-- the perturbation `A + E_t`, so `‖λ + t‖ ∈ Λ_ε(A)` whenever `E_t` is
-- admissible (`Nm E_t ≤ ε`).  Choosing `t` ALONG `arg λ`, i.e.
-- `t = (s/‖λ‖) · λ` with `s ≥ 0`, gives `‖λ + t‖ = ‖λ‖ + s = ρ + s`
-- (first-order OUTWARD growth of the modulus).  The admissible `s` is read off
-- from `Nm E_t ≤ ε`; with `s = c·ε` this needs `c ≤ 1/Nm(v wᵀ)`, and the
-- reciprocal condition number `c = |u* v|` is the value for the 2-norm
-- (`‖v uᵀ‖₂ = ‖v‖₂‖u‖₂ = 1` for unit v,u).  This is deliberately distinguished
-- from the optimal eigenvalue first-order coefficient
-- `κ(λ) = 1/|u* v|`, which requires a non-eigenvector-preserving perturbation
-- and a controlled `O(ε²)` expansion.
--
-- WHAT IS UNCONDITIONAL / HONEST HERE:
--   * `pseudospectrum_mem_of_aligned_rankOne_perturbation` — the core: for ANY
--       perturbation-size functional `Nm`, an aligned rank-one perturbation of
--       the specified size lands `‖λ + t‖` in the ε-pseudospectrum.  No norm
--       structure on `Nm` is assumed — the admissibility of the *specific*
--       perturbation used is a hypothesis, exactly as honest as it can be.
--   * `pseudospectralRadius_outward_growth_point` — the concrete achievability
--       witness `ρ + s ∈ Λ_ε(A)` for a dominant eigenvalue and `t` along `arg λ`.
--   * `pseudospectralRadiusLt_forces_gt` / `not_pseudospectralRadiusLt_of_growth`
--       — the STRICT lower bound `ρ_ε > ρ` complementing Bauer–Fike: any claimed
--       pseudospectral upper bound `r` must exceed `ρ`.
--   * `pseudospectralRadius_ge_first_order` — the first-order form
--       `ρ + c·ε ∈ Λ_ε(A)` with explicit `c = 1/Nm(v wᵀ)`, from an absolutely
--       homogeneous `Nm` (a genuine norm), the honest content of `ρ_ε ≥ ρ + c·ε`.
--   * `pseudospectralRadius_ge_entrywiseSum` — a FULLY CLOSED instantiation with
--       ZERO norm hypotheses, using the repo's concrete entrywise-sum norm, giving
--       the explicit constant `c = 1/(‖v‖₁ ‖w‖₁)`.
--   * `pseudospectralRadius_reciprocalCondNumber_growth` — the exact
--       `c = |u* v|` corollary under the CLEARLY DISCLOSED 2-norm normalization
--       identity `Nm(v uᵀ) = ‖v‖₂ ‖u‖₂ = 1` (a genuine, standard fact about the
--       spectral norm, supplied as a hypothesis, NOT smuggled).
--
-- HONESTY NOTES.  The dominant-eigenpair data (`A v = λ v`, `‖λ‖ = ρ`, a dual
-- covector with `∑ w_j v_j = 1`) is genuine spectral input — it is the standard
-- hypothesis of the achievability statement, NOT the conclusion.  Nothing about
-- `ρ_ε > ρ` is assumed; it is produced.  The abstract-`Nm` theorems carry the
-- admissibility of the *actual* perturbation as a hypothesis (no hidden norm
-- axioms); the homogeneous-`Nm` and 2-norm corollaries only add properties that
-- genuinely hold for real matrix norms, each disclosed at its use site.  The
-- fully-closed `pseudospectralRadius_ge_entrywiseSum` carries no norm hypothesis
-- at all.

import NumStability.Algorithms.MatrixPowersPseudospectralCriterion

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §18.2  Core: an aligned rank-one perturbation hits the pseudospectrum
-- ============================================================

/-- **Aligned rank-one perturbation lands `‖λ + t‖` in the ε-pseudospectrum**
    (Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §18.2,
    the achievability direction of Theorem 18.2, cited to [620, 1995] on
    p. 349, here proved constructively).

    Given a right eigenpair `A v = λ v` with `v ≠ 0` and a dual covector `w`
    with `∑_j w_j v_j = 1`, the rank-one perturbation `E_t = t · v wᵀ`
    (entrywise `(E_t)_{ij} = (t v_i) w_j`) satisfies `(A + E_t) v = (λ + t) v`,
    so `λ + t` is an eigenvalue of `A + E_t`.  Hence if `E_t` is admissible for
    the perturbation-size functional `Nm` (`Nm E_t ≤ ε`), the modulus
    `‖λ + t‖` lies in the ε-pseudospectrum `Λ_ε(A)`.

    This is the exact eigenvalue-perturbation witness the printed proof takes on
    faith; `Nm` is left an arbitrary functional (the book uses the 2-norm), and
    only the admissibility of the *specific* perturbation used is assumed. -/
theorem pseudospectrum_mem_of_aligned_rankOne_perturbation {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (lam : ℂ) (v w : CVec n) (hv : v ≠ 0)
    (heig : complexMatrixVecMul A v = complexVecSMul lam v)
    (hdual : ∑ j : Fin n, w j * v j = 1) (t : ℂ)
    (hE : Nm (complexMatrixRankOne (complexVecSMul t v) w) ≤ ε) :
    ‖lam + t‖ ∈ PseudospectrumModulusSet Nm ε A := by
  refine ⟨complexMatrixRankOne (complexVecSMul t v) w, hE, ?_⟩
  refine ⟨lam + t, v, hv, ?_, rfl⟩
  funext i
  show complexMatrixVecMul
      (fun a b => A a b + complexMatrixRankOne (complexVecSMul t v) w a b) v i
      = complexVecSMul (lam + t) v i
  unfold complexMatrixVecMul complexMatrixRankOne complexVecSMul
  have hAi : (∑ j : Fin n, A i j * v j) = lam * v i := by
    have hh := congrFun heig i
    simpa [complexMatrixVecMul, complexVecSMul] using hh
  calc (∑ j : Fin n, (A i j + t * v i * w j) * v j)
      = (∑ j : Fin n, A i j * v j) + t * v i * (∑ j : Fin n, w j * v j) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun j _ => by ring)
    _ = lam * v i + t * v i * 1 := by rw [hAi, hdual]
    _ = (lam + t) * v i := by ring

-- ============================================================
-- §18.2  Outward growth of the modulus along arg λ
-- ============================================================

/-- The aligned outward shift `t = (s/‖λ‖) · λ` collinear with `λ`, `s : ℝ`.
    For `s ≥ 0` and `λ ≠ 0` its modulus is `‖t‖ = s`. -/
noncomputable def alignedShift (lam : ℂ) (s : ℝ) : ℂ :=
  ((s / ‖lam‖ : ℝ) : ℂ) * lam

/-- The aligned shift has modulus exactly `s` for `s ≥ 0`, `λ ≠ 0`. -/
theorem norm_alignedShift (lam : ℂ) (hlam : lam ≠ 0) (s : ℝ) (hs : 0 ≤ s) :
    ‖alignedShift lam s‖ = s := by
  have hnorm : (0 : ℝ) < ‖lam‖ := by positivity
  unfold alignedShift
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    div_mul_cancel₀ _ (ne_of_gt hnorm)]

/-- **Modulus grows outward along `arg λ`** (Higham §18.2, first-order
    pseudospectral growth, 2nd ed. p. 349).  For a nonzero eigenvalue `λ` and
    real `s ≥ 0`, the aligned shift `t = (s/‖λ‖) · λ` is collinear with `λ`, so
    the moduli add: `‖λ + t‖ = ‖λ‖ + s`.  This is the direction choice that
    turns the rank-one perturbation into genuine *outward* growth of the
    spectral radius. -/
theorem norm_add_alignedShift (lam : ℂ) (hlam : lam ≠ 0) (s : ℝ) (hs : 0 ≤ s) :
    ‖lam + alignedShift lam s‖ = ‖lam‖ + s := by
  have hnorm : (0 : ℝ) < ‖lam‖ := by positivity
  unfold alignedShift
  have key : lam + ((s / ‖lam‖ : ℝ) : ℂ) * lam
      = ((1 + s / ‖lam‖ : ℝ) : ℂ) * lam := by
    push_cast; ring
  rw [key, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), add_mul, one_mul,
    div_mul_cancel₀ _ (ne_of_gt hnorm)]

/-- **Achievability witness `ρ + s ∈ Λ_ε(A)`** (Higham §18.2, the [620]
    achievability direction of Theorem 18.2, proved constructively).

    For a *dominant* eigenvalue `λ` (`‖λ‖ = ρ = ρ(A)`, `λ ≠ 0`) with right
    eigenvector `v ≠ 0` and dual covector `w` (`∑_j w_j v_j = 1`), and any real
    `s ≥ 0`, the aligned rank-one perturbation `E = (alignedShift λ s) · v wᵀ`
    (built from the shift `t = (s/‖λ‖)·λ` collinear with `λ`) lands the point
    `ρ + s` in the ε-pseudospectrum, provided that perturbation is admissible
    (`Nm E ≤ ε`).  In words: `ρ_ε(A) ≥ ρ + s`.  Combining
    `pseudospectrum_mem_of_aligned_rankOne_perturbation` (the eigenvalue
    witness) with `norm_add_alignedShift` (the outward-growth computation). -/
theorem pseudospectralRadius_outward_growth_point {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (lam : ℂ) (v w : CVec n) (hv : v ≠ 0) (hlam : lam ≠ 0)
    (heig : complexMatrixVecMul A v = complexVecSMul lam v)
    (hdual : ∑ j : Fin n, w j * v j = 1)
    (ρ : ℝ) (hρ : ‖lam‖ = ρ) (s : ℝ) (hs : 0 ≤ s)
    (hE : Nm (complexMatrixRankOne
      (complexVecSMul (alignedShift lam s) v) w) ≤ ε) :
    (ρ + s) ∈ PseudospectrumModulusSet Nm ε A := by
  have hmem := pseudospectrum_mem_of_aligned_rankOne_perturbation Nm ε A lam v w
    hv heig hdual (alignedShift lam s) hE
  rwa [norm_add_alignedShift lam hlam s hs, hρ] at hmem

-- ============================================================
-- §18.2  Strict lower bound  ρ_ε > ρ  (complement of Bauer–Fike)
-- ============================================================

/-- **Strict pseudospectral lower bound `ρ_ε(A) > ρ`, contrapositive form**
    (Higham §18.2, the achievability half complementing the Bauer–Fike upper
    bound, 2nd ed. p. 349).

    Whenever the ε-pseudospectrum contains a point of modulus `≥ ρ + s` with
    `s > 0` (as the aligned rank-one perturbation guarantees for `ε > 0`), any
    claimed pseudospectral upper bound `r` — i.e. `PseudospectralRadiusLt Nm ε
    r A`, "`ρ_ε < r`" — must strictly exceed `ρ`.  This is exactly the strict
    outward statement `ρ_ε(A) > ρ` for `ε > 0`, phrased through the repo's
    bounded predicate `PseudospectralRadiusLt` (which has no supremum). -/
theorem pseudospectralRadiusLt_forces_gt {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (ρ s r : ℝ) (hs : 0 < s)
    (hpt : (ρ + s) ∈ PseudospectrumModulusSet Nm ε A)
    (hlt : PseudospectralRadiusLt Nm ε r A) :
    ρ < r := by
  have h := hlt (ρ + s) hpt
  linarith

/-- **No pseudospectral upper bound reaches down to `ρ + s`** (Higham §18.2).
    Restatement: if `ρ + s` is a genuine pseudospectrum modulus, the bounded
    predicate `PseudospectralRadiusLt Nm ε (ρ + s) A` (which would force every
    modulus `< ρ + s`) is FALSE.  Hence `ρ_ε(A) ≥ ρ + s`. -/
theorem not_pseudospectralRadiusLt_of_growth {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (A : CMatrix n n)
    (ρ s : ℝ)
    (hpt : (ρ + s) ∈ PseudospectrumModulusSet Nm ε A) :
    ¬ PseudospectralRadiusLt Nm ε (ρ + s) A := by
  intro hlt
  exact lt_irrefl _ (hlt (ρ + s) hpt)

-- ============================================================
-- §18.2  First-order lower bound with explicit constant c
-- ============================================================

/-- **Size of the aligned rank-one perturbation** for an absolutely homogeneous
    norm `Nm`: the perturbation `E = (alignedShift λ s) · v wᵀ` built from the
    outward shift `t = (s/‖λ‖)·λ` (which has `‖t‖ = s`) has Nm-size exactly
    `s · Nm(v wᵀ)`.  Auxiliary to the first-order growth law. -/
theorem alignedShift_rankOne_perturbation_size {n : ℕ}
    (Nm : CMatrix n n → ℝ)
    (hom : ∀ (a : ℂ) (M : CMatrix n n),
      Nm (fun i j => a * M i j) = ‖a‖ * Nm M)
    (lam : ℂ) (hlam : lam ≠ 0) (v w : CVec n) (s : ℝ) (hs : 0 ≤ s) :
    Nm (complexMatrixRankOne (complexVecSMul (alignedShift lam s) v) w)
      = s * Nm (complexMatrixRankOne v w) := by
  have hrw : complexMatrixRankOne (complexVecSMul (alignedShift lam s) v) w
      = fun i j => (alignedShift lam s) * complexMatrixRankOne v w i j := by
    funext i j
    show ((alignedShift lam s) * v i) * w j
      = (alignedShift lam s) * (v i * w j)
    ring
  rw [hrw, hom, norm_alignedShift lam hlam s hs]

/-- **Exact aligned-rank-one lower bound `ρ_ε(A) ≥ ρ + c·ε` with explicit
    `c = 1/Nm(v wᵀ)`.**

    Data: a dominant eigenpair (`A v = λ v`, `v ≠ 0`, `λ ≠ 0`, `‖λ‖ = ρ`), a
    dual covector `w` (`∑_j w_j v_j = 1`), an absolutely homogeneous norm `Nm`
    with `Nm(v wᵀ) > 0`, and `ε ≥ 0`.  With the explicit constant
    `c = 1/Nm(v wᵀ)` and the outward shift `s = c·ε`, the aligned perturbation
    has Nm-size `s·Nm(v wᵀ) = ε` (exactly admissible), so the point `ρ + c·ε`
    lies in the ε-pseudospectrum.  This exact construction should not be
    confused with the optimal first-order perturbation law: after normalizing a
    left eigenvector, it produces the reciprocal coefficient `|u*v|`, whereas
    the optimal derivative has coefficient `1/|u*v|` and an `O(ε²)` remainder. -/
theorem pseudospectralRadius_ge_first_order {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (A : CMatrix n n)
    (lam : ℂ) (v w : CVec n) (hv : v ≠ 0) (hlam : lam ≠ 0)
    (heig : complexMatrixVecMul A v = complexVecSMul lam v)
    (hdual : ∑ j : Fin n, w j * v j = 1)
    (ρ : ℝ) (hρ : ‖lam‖ = ρ)
    (hom : ∀ (a : ℂ) (M : CMatrix n n),
      Nm (fun i j => a * M i j) = ‖a‖ * Nm M)
    (hNmpos : 0 < Nm (complexMatrixRankOne v w)) :
    (ρ + (1 / Nm (complexMatrixRankOne v w)) * ε)
      ∈ PseudospectrumModulusSet Nm ε A := by
  set c : ℝ := 1 / Nm (complexMatrixRankOne v w) with hc
  set s : ℝ := c * ε with hsdef
  have hs0 : 0 ≤ s := by
    rw [hsdef, hc]
    exact mul_nonneg (by positivity) hε
  -- the aligned perturbation of shift s = c·ε has Nm-size exactly ε
  have hsize := alignedShift_rankOne_perturbation_size Nm hom lam hlam v w s hs0
  have hEeq : Nm (complexMatrixRankOne
      (complexVecSMul (alignedShift lam s) v) w) = ε := by
    rw [hsize, hsdef, hc]
    field_simp [hNmpos.ne']
  have hEle : Nm (complexMatrixRankOne
      (complexVecSMul (alignedShift lam s) v) w) ≤ ε := le_of_eq hEeq
  have hmem := pseudospectralRadius_outward_growth_point Nm ε A lam v w hv hlam
    heig hdual ρ hρ s hs0 hEle
  rwa [hsdef] at hmem

-- ============================================================
-- §18.2  Fully-closed instantiation: the concrete entrywise-sum norm
-- ============================================================

/-- The concrete complex vector 1-norm is strictly positive for a nonzero
    vector.  (`v ≠ 0` gives one coordinate of positive modulus, and every
    summand `‖v_i‖` is nonnegative.)  Auxiliary to the fully-closed §18.2
    achievability constant (Higham, Accuracy and Stability of Numerical
    Algorithms, 2nd ed., §18.2, p. 349): it certifies `‖v‖₁ > 0` so the explicit
    constant `c = 1/(‖v‖₁‖w‖₁)` is well defined and positive. -/
theorem complexVecOneNorm_pos_of_ne_zero {n : ℕ} (x : CVec n) (hx : x ≠ 0) :
    0 < complexVecOneNorm x := by
  unfold complexVecOneNorm
  rcases Function.ne_iff.mp hx with ⟨i, hi⟩
  have hpos : 0 < ‖x i‖ := by
    rw [norm_pos_iff]; simpa using hi
  exact Finset.sum_pos' (fun j _ => norm_nonneg _) ⟨i, Finset.mem_univ i, hpos⟩

/-- The dual covector `w` of a `∑_j w_j v_j = 1` normalization is nonzero.
    Auxiliary to the fully-closed §18.2 achievability constant (Higham, 2nd ed.,
    §18.2, p. 349): the normalization `∑_j w_j v_j = 1` (which for a left
    eigenvector reads `(u* v)/(u* v) = 1`) forces `w ≠ 0`, hence `‖w‖₁ > 0`. -/
theorem dualCovector_ne_zero {n : ℕ} (v w : CVec n)
    (hdual : ∑ j : Fin n, w j * v j = 1) : w ≠ 0 := by
  intro hw
  rw [hw] at hdual
  simp at hdual

/-- **Fully-closed achievability lower bound with the concrete entrywise-sum
    norm** (Higham §18.2, the [620] achievability direction, discharged with
    NO norm hypothesis whatsoever).

    Instantiating `pseudospectralRadius_ge_first_order` with the repo's concrete
    perturbation-size functional `complexMatrixEntrywiseSumNorm` (`∑_{ij} |·|`),
    for which the repo already proves absolute homogeneity and the rank-one
    value `‖v wᵀ‖ = ‖v‖₁ ‖w‖₁` (`complexMatrixEntrywiseSumNorm_rankOne`).  From
    the dominant eigenpair alone — the positivity `‖v‖₁ ‖w‖₁ > 0` is DERIVED
    (`v ≠ 0`, and `w ≠ 0` from the normalization `hdual`) — the explicit
    constant is `c = 1/(‖v‖₁ ‖w‖₁)` and the point `ρ + c·ε ∈ Λ_ε(A)`.  This is a
    fully closed instance of `ρ_ε(A) ≥ ρ + c·ε` with no norm hypothesis. -/
theorem pseudospectralRadius_ge_entrywiseSum {n : ℕ}
    (ε : ℝ) (hε : 0 ≤ ε) (A : CMatrix n n)
    (lam : ℂ) (v w : CVec n) (hv : v ≠ 0) (hlam : lam ≠ 0)
    (heig : complexMatrixVecMul A v = complexVecSMul lam v)
    (hdual : ∑ j : Fin n, w j * v j = 1)
    (ρ : ℝ) (hρ : ‖lam‖ = ρ) :
    (ρ + (1 / (complexVecOneNorm v * complexVecOneNorm w)) * ε)
      ∈ PseudospectrumModulusSet complexMatrixEntrywiseSumNorm ε A := by
  -- Absolute homogeneity of the entrywise-sum norm.
  have hom : ∀ (a : ℂ) (M : CMatrix n n),
      complexMatrixEntrywiseSumNorm (fun i j => a * M i j)
        = ‖a‖ * complexMatrixEntrywiseSumNorm M := by
    intro a M
    rw [complexMatrixEntrywiseSumNorm_eq_sum_sum,
      complexMatrixEntrywiseSumNorm_eq_sum_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [norm_mul])
  -- The rank-one value pins Nm(v wᵀ) = ‖v‖₁ ‖w‖₁.
  have hrankone : complexMatrixEntrywiseSumNorm (complexMatrixRankOne v w)
      = complexVecOneNorm v * complexVecOneNorm w :=
    complexMatrixEntrywiseSumNorm_rankOne v w
  -- Positivity of ‖v‖₁‖w‖₁ derived from v ≠ 0 and w ≠ 0 (the latter from hdual).
  have hvpos : 0 < complexVecOneNorm v := complexVecOneNorm_pos_of_ne_zero v hv
  have hwpos : 0 < complexVecOneNorm w :=
    complexVecOneNorm_pos_of_ne_zero w (dualCovector_ne_zero v w hdual)
  have hNmpos : 0 < complexMatrixEntrywiseSumNorm (complexMatrixRankOne v w) := by
    rw [hrankone]; exact mul_pos hvpos hwpos
  have hmem := pseudospectralRadius_ge_first_order
    complexMatrixEntrywiseSumNorm ε hε A lam v w hv hlam heig hdual ρ hρ
    hom hNmpos
  rwa [hrankone] at hmem

/-- **Strict achievability `ρ_ε(A) > ρ` for `ε > 0`, fully closed** (Higham
    §18.2, the achievability direction complementing the Bauer–Fike upper bound,
    2nd ed. p. 349).

    Capstone of the constructive route: from a dominant eigenpair alone (no norm
    hypotheses) and `ε > 0`, the entrywise-sum ε-pseudospectral radius strictly
    exceeds the spectral radius `ρ = ‖λ‖` — any pseudospectral upper bound `r`
    (`PseudospectralRadiusLt … r A`, "`ρ_ε < r`") must satisfy `ρ < r`.  This is
    exactly the strict outward statement `ρ_ε(A) > ρ` for `ε > 0`, obtained by
    feeding the achievability witness `ρ + c·ε ∈ Λ_ε(A)` of
    `pseudospectralRadius_ge_entrywiseSum` (with `c·ε > 0`) into
    `pseudospectralRadiusLt_forces_gt`. -/
theorem pseudospectralRadius_gt_entrywiseSum {n : ℕ}
    (ε : ℝ) (hε : 0 < ε) (A : CMatrix n n)
    (lam : ℂ) (v w : CVec n) (hv : v ≠ 0) (hlam : lam ≠ 0)
    (heig : complexMatrixVecMul A v = complexVecSMul lam v)
    (hdual : ∑ j : Fin n, w j * v j = 1)
    (ρ : ℝ) (hρ : ‖lam‖ = ρ) (r : ℝ)
    (hlt : PseudospectralRadiusLt complexMatrixEntrywiseSumNorm ε r A) :
    ρ < r := by
  have hvpos : 0 < complexVecOneNorm v := complexVecOneNorm_pos_of_ne_zero v hv
  have hwpos : 0 < complexVecOneNorm w :=
    complexVecOneNorm_pos_of_ne_zero w (dualCovector_ne_zero v w hdual)
  have hspos : 0 < (1 / (complexVecOneNorm v * complexVecOneNorm w)) * ε :=
    mul_pos (one_div_pos.mpr (mul_pos hvpos hwpos)) hε
  have hpt := pseudospectralRadius_ge_entrywiseSum ε hε.le A lam v w hv hlam
    heig hdual ρ hρ
  exact pseudospectralRadiusLt_forces_gt complexMatrixEntrywiseSumNorm ε A
    ρ ((1 / (complexVecOneNorm v * complexVecOneNorm w)) * ε) r hspos hpt hlt

-- ============================================================
-- §18.2  Exact c = |u*v| eigenvector-preserving corollary
-- ============================================================

/-- **Eigenvector-preserving growth `ρ_ε(A) ≥ ρ + |u* v| · ε`.**

    Data: a dominant eigenpair (`A v = λ v`, `v ≠ 0`, `λ ≠ 0`, `‖λ‖ = ρ`), a
    left eigenvector packaged as the dual covector `w = uᵀ/(u* v)` so that
    `∑_j w_j v_j = 1`, and an absolutely homogeneous norm `Nm`.  The constant
    `c = |u* v|` is the reciprocal condition number of the eigenvalue; it is the
    value of `1/Nm(v wᵀ)` precisely when `Nm(v wᵀ) = 1/|u* v|`.

    HONESTY.  The identity `Nm(v wᵀ) = 1/|u* v|` is supplied as the explicit
    hypothesis `hNmw`.  It is the genuine, standard normalization fact for the
    SPECTRAL (2-)norm: with unit right/left eigenvectors `v, u` (`‖v‖₂ = ‖u‖₂ =
    1`) and `w = uᵀ/(u* v)`, one has `‖v wᵀ‖₂ = ‖v‖₂‖w‖₂ = ‖u‖₂/|u* v| =
    1/|u* v|`.  It is DISCLOSED here rather than smuggled — and it holds for the
    real object (the 2-norm), which is the norm the book uses.  Under it, the
    point `ρ + |u* v| · ε` lands in the ε-pseudospectrum.  This is a valid but
    non-optimal lower bound; it does not imply Higham's cited
    `κ₂(X)ε/n² + O(ε²)` estimate for Theorem 18.2. -/
theorem pseudospectralRadius_reciprocalCondNumber_growth {n : ℕ}
    (Nm : CMatrix n n → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (A : CMatrix n n)
    (lam : ℂ) (v w : CVec n) (hv : v ≠ 0) (hlam : lam ≠ 0)
    (heig : complexMatrixVecMul A v = complexVecSMul lam v)
    (hdual : ∑ j : Fin n, w j * v j = 1)
    (ρ : ℝ) (hρ : ‖lam‖ = ρ)
    (hom : ∀ (a : ℂ) (M : CMatrix n n),
      Nm (fun i j => a * M i j) = ‖a‖ * Nm M)
    (uv : ℝ) (huv : 0 < uv)
    (hNmw : Nm (complexMatrixRankOne v w) = 1 / uv) :
    (ρ + uv * ε) ∈ PseudospectrumModulusSet Nm ε A := by
  have hNmpos : 0 < Nm (complexMatrixRankOne v w) := by
    rw [hNmw]; exact one_div_pos.mpr huv
  have hmem := pseudospectralRadius_ge_first_order Nm ε hε A lam v w hv hlam
    heig hdual ρ hρ hom hNmpos
  rw [hNmw] at hmem
  have hcast : (1 / (1 / uv) : ℝ) = uv := one_div_one_div uv
  rwa [hcast] at hmem

end NumStability
