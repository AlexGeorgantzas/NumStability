-- Algorithms/QR/Higham19Labels.lean
--
-- Higham Chapter 19 "QR Factorization" (2nd ed.): source-faithful labeled
-- wrappers packaging already-proved QR mathematics under the printed
-- Lemma/Theorem numbers, following the completed Chapter 19 source-inventory
-- audit.  Each wrapper is honest about the exact constant it proves versus
-- the printed gamma-tilde class, and about which constructions are covered.

import NumStability.Algorithms.QR.HouseholderReflector
import NumStability.Algorithms.QR.HouseholderSpec
import NumStability.Algorithms.QR.HouseholderApply
import NumStability.Algorithms.QR.HouseholderOneStep
import NumStability.Algorithms.QR.HouseholderQR
import NumStability.Algorithms.QR.HouseholderQRSupport
import NumStability.Algorithms.QR.GivensSpec
import NumStability.Algorithms.QR.QRSolve
import NumStability.Analysis.Rounding

namespace NumStability

open scoped BigOperators

-- ============================================================
-- Lemma 19.1 (Householder vector construction), Construction 1
-- ============================================================

/-- **Lemma 19.1, Construction 1** (Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §19.3, p. 357): for the usual-sign
    Householder construction (eq (19.1)), the computed Householder data
    satisfy the exact-tail / relative-error-first-entry / relative-error-beta
    contract `HouseholderConstructionError`.

    The printed Lemma 19.1 states the bound for BOTH sign conventions (19.1)
    and (19.2); this wrapper is Construction 1 (usual sign, eq (19.1)).
    Construction 2 (the alternative-sign, cancellation-avoiding kernel of
    eq (19.2)) is now formalized in `HouseholderConstruction2.lean`
    (`H19_Lemma19_1_construction2_backward_error`), so the two-construction
    label is complete.  The proved constant is the `θ̃`/`γ̃_n`-class bound
    recorded in `HouseholderConstructionError` (explicit index `4n+8`). -/
theorem H19_Lemma19_1_construction1_backward_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x : Fin n → ℝ) (hx : x ≠ 0)
    (hn : gammaValid fp (4 * n + 8)) :
    HouseholderConstructionError fp hn0 x
      (fl_householderVector fp hn0 x)
      (fl_householderBeta fp hn0 x) :=
  fl_householderConstructionError fp hn0 x hx hn

-- ============================================================
-- Lemma 19.2 (backward error of applying a Householder reflector)
-- ============================================================

/-- Constants-collapse for Lemma 19.2: the two-term computed bound
    `√(n·u²) + 2·γ_{11n+23}` is dominated by the single `γ`-class constant
    `γ_{23n+46}`, under the smallness guard `gammaValid fp (23n+46)`.

    Proof: `√(n·u²) = √n·u ≤ n·u ≤ γ_n`; `2·γ_{11n+23} ≤ γ_{22n+46}` and
    `γ_n + γ_{22n+46} ≤ γ_{23n+46}` by two applications of `gamma_sum_le`. -/
theorem sqrt_u_sq_add_two_gamma_le_gamma (fp : FPModel) (n : ℕ) (hn : 0 < n)
    (hval : gammaValid fp (23 * n + 46)) :
    Real.sqrt ((n : ℝ) * fp.u ^ 2) + 2 * gamma fp (11 * n + 23) ≤
      gamma fp (23 * n + 46) := by
  have hu : (0 : ℝ) ≤ fp.u := fp.u_nonneg
  -- √(n·u²) = √n · u
  have hsqrt : Real.sqrt ((n : ℝ) * fp.u ^ 2) = Real.sqrt (n : ℝ) * fp.u := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
  -- √n ≤ n
  have hsqn : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    have : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) ^ 2) :=
      Real.sqrt_le_sqrt (by nlinarith [(by exact_mod_cast hn : (1:ℝ) ≤ (n:ℝ))])
    rwa [Real.sqrt_sq (by positivity)] at this
  -- n·u ≤ γ_n
  have hval_n : gammaValid fp n := gammaValid_mono fp (by omega) hval
  have hnu_le : (n : ℝ) * fp.u ≤ gamma fp n := by
    unfold gamma
    have hd : (0 : ℝ) < 1 - (n : ℝ) * fp.u := by
      have := hval_n; unfold gammaValid at this; linarith
    rw [le_div_iff₀ hd]
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)) hu)
      (mul_nonneg (by positivity : (0:ℝ) ≤ (n:ℝ)) hu)]
  have hsqrt_le : Real.sqrt ((n : ℝ) * fp.u ^ 2) ≤ gamma fp n := by
    rw [hsqrt]
    calc Real.sqrt (n : ℝ) * fp.u ≤ (n : ℝ) * fp.u :=
          mul_le_mul_of_nonneg_right hsqn hu
      _ ≤ gamma fp n := hnu_le
  have hval_11 : gammaValid fp (11 * n + 23) :=
    gammaValid_mono fp (by omega) hval
  have hval_22 : gammaValid fp (22 * n + 46) :=
    gammaValid_mono fp (by omega) hval
  -- 2·γ_{11n+23} ≤ γ_{22n+46}
  have h2g : 2 * gamma fp (11 * n + 23) ≤ gamma fp (22 * n + 46) := by
    have hsum := gamma_sum_le fp (11 * n + 23) (11 * n + 23)
      (by rw [show (11*n+23)+(11*n+23) = 22*n+46 by ring]; exact hval_22)
    rw [show (11*n+23)+(11*n+23) = 22*n+46 by ring] at hsum
    have hnn : 0 ≤ gamma fp (11 * n + 23) * gamma fp (11 * n + 23) :=
      mul_nonneg (gamma_nonneg fp hval_11) (gamma_nonneg fp hval_11)
    nlinarith [hsum]
  -- γ_n + γ_{22n+46} ≤ γ_{23n+46}
  have hsum2 := gamma_sum_le fp n (22 * n + 46)
    (by rw [show n + (22*n+46) = 23*n+46 by ring]; exact hval)
  rw [show n + (22*n+46) = 23*n+46 by ring] at hsum2
  have hnn2 : 0 ≤ gamma fp n * gamma fp (22 * n + 46) :=
    mul_nonneg (gamma_nonneg fp hval_n) (gamma_nonneg fp hval_22)
  calc Real.sqrt ((n : ℝ) * fp.u ^ 2) + 2 * gamma fp (11 * n + 23)
      ≤ gamma fp n + gamma fp (22 * n + 46) := by gcongr
    _ ≤ gamma fp (23 * n + 46) := by nlinarith [hsum2, hnn2]

/-- **Lemma 19.2** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.3, p. 358): applying a computed normalized Householder
    reflector `v̂` (satisfying the normalized construction of `HouseholderApply`)
    to a vector `b` gives `ŷ = (P + ΔP)b` with `P = I − vvᵀ` orthogonal and
    `‖ΔP‖_F` bounded by the single `γ`-class constant `γ_{33n+69}`.

    This packages `fl_householderConstructApply_appError` with the
    constants-collapse `sqrt_u_sq_add_two_gamma_le_gamma`, matching the
    printed backward-error shape (the printed constant is `γ̃_m`; the proved
    constant `γ_{23n+46}` is of the same class with an explicit larger
    index). -/
theorem H19_Lemma19_2_householder_apply_backward_error (fp : FPModel)
    {n : ℕ} (hn0 : 0 < n) (x b : Fin n → ℝ) (hx : x ≠ 0)
    (hvalid : gammaValid fp (23 * n + 46)) :
    HouseholderAppError n
      (householder n
        (householderNormalizedVector n
          (householderVector hn0 x) (householderBetaFromScale hn0 x)) 1)
      b
      (fl_householderApply fp n
        (fl_householderNormalizedVector fp hn0 x) 1 b)
      (gamma fp (23 * n + 46)) := by
  have hbase := fl_householderConstructApply_appError fp hn0 x b hx
    (gammaValid_mono fp (by omega) hvalid)
  obtain ⟨horth, ΔP, hΔ, heq⟩ := hbase
  refine ⟨horth, ΔP, ?_, heq⟩
  exact hΔ.trans (sqrt_u_sq_add_two_gamma_le_gamma fp n hn0 hvalid)

-- ============================================================
-- Lemma 19.3 (columnwise backward error of Householder QR), n = 1 corollary
-- ============================================================

/-- **Lemma 19.3, `(Q + ΔQ)ᵀ` vector form** (Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §19.3, p. 360): the scalar (single-column,
    `n = 1`) corollary of Lemma 19.3, packaged as a self-contained abstract
    statement.  If `â = Qᵀ(a + Δa)` for an orthogonal `Q`, with `a ≠ 0` and the
    relative perturbation bound `‖Δa‖₂ ≤ C‖a‖₂`, then there is a backward
    perturbation `ΔQ` with `â = (Q + ΔQ)ᵀ a` and `‖ΔQ‖_F ≤ C`.

    Construction (the rank-one perturbation of the printed proof):
    `ΔQ = a · (QᵀΔa)ᵀ / (aᵀa)`, so `ΔQᵀ a = QᵀΔa` (the `aᵀa` cancels) and
    `(Q + ΔQ)ᵀ a = Qᵀa + QᵀΔa = Qᵀ(a + Δa) = â`.  Its Frobenius norm is
    `‖a‖₂·‖QᵀΔa‖₂/(aᵀa) = ‖QᵀΔa‖₂/‖a‖₂ = ‖Δa‖₂/‖a‖₂ ≤ C`, using that an
    orthogonal `Qᵀ` preserves the Euclidean norm and that a rank-one outer
    product `u vᵀ` has `‖u vᵀ‖_F = ‖u‖₂‖v‖₂`.

    This is the exact-arithmetic backward-error rewriting; the constant `C`
    here is whatever relative perturbation bound is supplied, matching the
    printed statement's `γ̃`-class column bound once instantiated with the
    Householder QR column error. -/
theorem H19_Lemma19_3_vector_QplusDeltaQ_form {m : ℕ}
    (Q : Fin m → Fin m → ℝ) (hQ : IsOrthogonal m Q)
    (a â Δa : Fin m → ℝ) (ha : a ≠ 0) {C : ℝ}
    (hâ : ∀ i, â i = matMulVec m (fun p q => Q q p) (fun j => a j + Δa j) i)
    (hΔ : vecNorm2 Δa ≤ C * vecNorm2 a) :
    ∃ ΔQ : Fin m → Fin m → ℝ,
      (∀ i, â i = matMulVec m (fun p q => Q q p + ΔQ q p) a i) ∧
      frobNorm ΔQ ≤ C := by
  classical
  -- Abbreviations: `w = QᵀΔa`, `s = aᵀa = ‖a‖₂²`.
  set w : Fin m → ℝ := matMulVec m (fun p q => Q q p) Δa with hw_def
  set s : ℝ := ∑ j : Fin m, a j * a j with hs_def
  -- `Qᵀ` is orthogonal, hence norm-preserving.
  have hQt : IsOrthogonal m (matTranspose Q) := hQ.transpose
  have hw_norm : vecNorm2 w = vecNorm2 Δa := by
    have : matMulVec m (fun p q => Q q p) Δa = matMulVec m (matTranspose Q) Δa := rfl
    rw [hw_def, this]
    exact vecNorm2_orthogonal (matTranspose Q) Δa hQt
  -- `s = ‖a‖₂²` and `s > 0`.
  have hs_eq : s = vecNorm2Sq a := by
    rw [hs_def]; unfold vecNorm2Sq; simp_rw [pow_two]
  have ha_norm_pos : 0 < vecNorm2 a := by
    rcases lt_or_eq_of_le (vecNorm2_nonneg a) with h | h
    · exact h
    · exact absurd (funext ((vecNorm2_eq_zero_iff a).mp h.symm)) ha
  have hs_pos : 0 < s := by
    rw [hs_eq, ← vecNorm2_sq]; positivity
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  -- The rank-one backward perturbation.
  refine ⟨fun p q => a p * w q / s, ?_, ?_⟩
  · -- Representation: `(Q + ΔQ)ᵀ a = Qᵀa + QᵀΔa = â`.
    intro i
    show â i = matMulVec m (fun p q => Q q p + a q * w i / s) a i
    have hrep :
        matMulVec m (fun p q => Q q p + (a q * w i / s)) a i =
          matMulVec m (fun p q => Q q p) a i + w i := by
      unfold matMulVec
      have hsplit :
          (∑ j : Fin m, (Q j i + a j * w i / s) * a j) =
            (∑ j : Fin m, Q j i * a j) +
              ∑ j : Fin m, (a j * w i / s) * a j := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring
      have hcoll :
          (∑ j : Fin m, (a j * w i / s) * a j) = w i := by
        have : (∑ j : Fin m, (a j * w i / s) * a j) =
            (w i / s) * ∑ j : Fin m, a j * a j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j _; ring
        rw [this, ← hs_def]
        field_simp
      rw [hsplit, hcoll]
    -- `â i = Qᵀ(a+Δa) i = Qᵀa i + QᵀΔa i = Qᵀa i + w i`.
    have hâ_split :
        â i = matMulVec m (fun p q => Q q p) a i + w i := by
      rw [hâ i]
      unfold matMulVec
      rw [hw_def]; unfold matMulVec
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hrep, hâ_split]
  · -- Norm: `‖ΔQ‖_F = ‖a‖₂·‖w/s‖₂ = ‖a‖₂·‖w‖₂/s = ‖Δa‖₂/‖a‖₂ ≤ C`.
    have hrankone :
        (fun p q => a p * w q / s) = (fun p q => a p * (fun t => w t / s) q) := by
      funext p q; ring
    rw [← frobNormRect_eq_frobNormFn, hrankone, frobNormRect_outerProduct]
    -- `‖w/s‖₂ = ‖(1/s)·w‖₂ = |1/s|·‖w‖₂ = ‖w‖₂/s`.
    have hscale : vecNorm2 (fun t => w t / s) = vecNorm2 w / s := by
      have h1 : (fun t => w t / s) = (fun t => (1 / s) * w t) := by
        funext t; ring
      rw [h1, vecNorm2_smul, abs_of_pos (by positivity : (0:ℝ) < 1 / s)]
      rw [one_div, ← div_eq_inv_mul]
    rw [hscale, hw_norm]
    -- `‖a‖₂·(‖Δa‖₂/s) = ‖Δa‖₂/‖a‖₂` since `s = ‖a‖₂²`.
    have hs_sq : s = vecNorm2 a * vecNorm2 a := by
      rw [hs_eq, ← vecNorm2_sq, pow_two]
    have hcollapse :
        vecNorm2 a * (vecNorm2 Δa / s) = vecNorm2 Δa / vecNorm2 a := by
      rw [hs_sq]; field_simp
    rw [hcollapse, div_le_iff₀ ha_norm_pos]
    linarith [hΔ]

-- ============================================================
-- Lemma 19.7 (backward error of computed Givens coefficients)
-- ============================================================

/-- **Lemma 19.7** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.6, p. 366; eq (19.24)): the coefficients `ĉ, ŝ` computed from
    `xi, xj` by the standard floating-point Givens recipe (`fl_norm2` denominator,
    then two divisions) satisfy the relative-error contract
    `ĉ = c·(1 + θ₁)`, `ŝ = s·(1 + θ₂)` with `|θ₁|, |θ₂| ≤ μ`, where `c, s` are the
    exact Givens coefficients.

    Constant.  The printed (19.24) advertises `|θ| ≤ γ₄` (its proof is omitted in
    the text).  The concrete kernel available here rounds the shared denominator
    through `fl_norm2` (a sum of two squares, one add, one sqrt) and then a final
    division; collapsing those rounding factors yields the sharper-provable
    constant of this repository's kernel, `μ = γ₆`, which is of the same
    `γ̃`-class with a larger explicit index.  We therefore prove the (19.24)
    contract with `μ = γ fp 6`, packaged via `GivensCoeffError`, and record the
    printed-vs-proved `γ₄`-vs-`γ₆` difference here. -/
theorem H19_Lemma19_7_givens_coeff_error (fp : FPModel)
    (xi xj : ℝ) (h : xi ^ 2 + xj ^ 2 ≠ 0)
    (hvalid : gammaValid fp 6) :
    GivensCoeffError (givensC xi xj) (givensS xi xj)
      (fl_givensC fp xi xj) (fl_givensS fp xi xj) (gamma fp 6) :=
  fl_givensCoeffError_conservative fp xi xj h hvalid

-- ============================================================
-- Lemma 19.8 (backward error of applying a Givens rotation)
-- ============================================================

/-- Two-point selector sum: `∑ⱼ (if j=p then a else if j=q then b else 0) = a+b`
    when `p ≠ q`.  Local helper (the `GivensSpec` version is `private`). -/
private theorem sum_two_point_sel {n : ℕ} (p q : Fin n) (a b : ℝ)
    (hpq : p ≠ q) :
    (∑ j : Fin n, (if j = p then a else if j = q then b else 0)) = a + b := by
  classical
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  set f : Fin n → ℝ := fun j => (if j = p then a else if j = q then b else 0)
    with hf_def
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [hf_def, hjp, hjq]
  calc
    (∑ j : Fin n, f j)
        = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
          rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]; ring
    _ = a + b := by rw [hrest]; simp [hf_def, hpq.symm]

/-- Two-point selector sum weighted by a vector:
    `∑ⱼ (if j=p then a else if j=q then b else 0)·xⱼ = a·xₚ + b·x_q`. -/
private theorem sum_two_point_mul {n : ℕ} (p q : Fin n) (a b : ℝ)
    (x : Fin n → ℝ) (hpq : p ≠ q) :
    (∑ j : Fin n, (if j = p then a else if j = q then b else 0) * x j) =
      a * x p + b * x q := by
  classical
  have hp : p ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ p
  have hq : q ∈ (Finset.univ : Finset (Fin n)).erase p :=
    Finset.mem_erase.mpr ⟨hpq.symm, Finset.mem_univ q⟩
  set f : Fin n → ℝ := fun j =>
    (if j = p then a else if j = q then b else 0) * x j with hf_def
  have hrest : ∑ j ∈ (Finset.univ.erase p).erase q, f j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
    have hjq : j ≠ q := hj.1
    have hjp : j ≠ p := hj.2
    simp [hf_def, hjp, hjq]
  calc
    (∑ j : Fin n, f j)
        = f p + f q + ∑ j ∈ (Finset.univ.erase p).erase q, f j := by
          rw [← Finset.add_sum_erase _ f hp, ← Finset.add_sum_erase _ f hq]; ring
    _ = a * x p + b * x q := by rw [hrest]; simp [hf_def, hpq.symm]

/-- **Pair-block Frobenius reduction** (support lemma for Lemma 19.8): a
    perturbation supported only on the two rows/columns `p ≠ q` has squared
    Frobenius norm equal to the sum of the squares of its four active entries,
    `‖E‖²_F = E_pp² + E_pq² + E_qp² + E_qq²`.

    This is the dimension-independent core: the `n × n` sum collapses to the
    `2 × 2` active block, so the Frobenius mass of a Givens perturbation never
    grows with the ambient dimension. -/
theorem PairBlockSupported_frobNormSq_eq_block {n : ℕ} {p q : Fin n}
    (hpq : p ≠ q) {E : Fin n → Fin n → ℝ}
    (hE : PairBlockSupported p q E) :
    frobNormSq E = E p p ^ 2 + E p q ^ 2 + E q p ^ 2 + E q q ^ 2 := by
  classical
  unfold frobNormSq
  -- Row-sum function.
  set r : Fin n → ℝ := fun i => ∑ j : Fin n, E i j ^ 2 with hr_def
  -- For a pair-supported row `i ∈ {p,q}` the row sum keeps only columns p, q.
  have hrow_pq : ∀ i : Fin n,
      r i = (if i = p ∨ i = q then E i p ^ 2 + E i q ^ 2 else 0) := by
    intro i
    by_cases hi : i = p ∨ i = q
    · -- keep only j = p and j = q
      have hcol : ∀ j : Fin n, E i j ^ 2 =
          (if j = p then E i p ^ 2 else if j = q then E i q ^ 2 else 0) := by
        intro j
        by_cases hjp : j = p
        · rw [hjp]; simp
        · by_cases hjq : j = q
          · rw [hjq]; simp [hpq.symm]
          · have hz : E i j = 0 := hE i j (Or.inr ⟨hjp, hjq⟩)
            simp [hjp, hjq, hz]
      rw [hr_def]
      simp only
      rw [if_pos hi]
      calc
        (∑ j : Fin n, E i j ^ 2)
            = ∑ j : Fin n,
                (if j = p then E i p ^ 2 else if j = q then E i q ^ 2 else 0) :=
              Finset.sum_congr rfl (fun j _ => hcol j)
        _ = E i p ^ 2 + E i q ^ 2 :=
              sum_two_point_sel p q (E i p ^ 2) (E i q ^ 2) hpq
    · -- row entirely zero
      have hzero : ∀ j : Fin n, E i j ^ 2 = 0 := by
        intro j
        have hip : i ≠ p := fun h => hi (Or.inl h)
        have hiq : i ≠ q := fun h => hi (Or.inr h)
        have : E i j = 0 := hE i j (Or.inl ⟨hip, hiq⟩)
        simp [this]
      rw [hr_def]; simp only
      rw [if_neg hi]
      exact Finset.sum_eq_zero (fun j _ => hzero j)
  -- Now sum the row function over i, keeping only i = p and i = q.
  have hrow_final : ∀ i : Fin n,
      r i = (if i = p then E p p ^ 2 + E p q ^ 2
             else if i = q then E q p ^ 2 + E q q ^ 2 else 0) := by
    intro i
    rw [hrow_pq i]
    by_cases hip : i = p
    · subst hip; simp
    · by_cases hiq : i = q
      · subst hiq; simp [hpq.symm]
      · simp [hip, hiq]
  calc
    (∑ i : Fin n, r i)
        = ∑ i : Fin n,
            (if i = p then E p p ^ 2 + E p q ^ 2
             else if i = q then E q p ^ 2 + E q q ^ 2 else 0) :=
          Finset.sum_congr rfl (fun i _ => hrow_final i)
    _ = (E p p ^ 2 + E p q ^ 2) + (E q p ^ 2 + E q q ^ 2) :=
          sum_two_point_sel p q
            (E p p ^ 2 + E p q ^ 2) (E q p ^ 2 + E q q ^ 2) hpq
    _ = E p p ^ 2 + E p q ^ 2 + E q p ^ 2 + E q q ^ 2 := by ring

/-- **Dimension-independent Frobenius bound for a pair-supported
    perturbation** (support lemma for Lemma 19.8): if every active entry of a
    pair-supported `E` is bounded in absolute value by `β ≥ 0`, then
    `‖E‖_F ≤ 2β`, independent of the ambient dimension `n`. -/
theorem PairBlockSupported_frobNorm_le {n : ℕ} {p q : Fin n}
    (hpq : p ≠ q) {E : Fin n → Fin n → ℝ}
    (hE : PairBlockSupported p q E) {β : ℝ} (hβ : 0 ≤ β)
    (hpp : |E p p| ≤ β) (hpq' : |E p q| ≤ β)
    (hqp : |E q p| ≤ β) (hqq : |E q q| ≤ β) :
    frobNorm E ≤ 2 * β := by
  have hsq : frobNormSq E ≤ (2 * β) ^ 2 := by
    rw [PairBlockSupported_frobNormSq_eq_block hpq hE]
    have e1 : E p p ^ 2 ≤ β ^ 2 := by
      rw [← sq_abs (E p p)]; exact pow_le_pow_left₀ (abs_nonneg _) hpp 2
    have e2 : E p q ^ 2 ≤ β ^ 2 := by
      rw [← sq_abs (E p q)]; exact pow_le_pow_left₀ (abs_nonneg _) hpq' 2
    have e3 : E q p ^ 2 ≤ β ^ 2 := by
      rw [← sq_abs (E q p)]; exact pow_le_pow_left₀ (abs_nonneg _) hqp 2
    have e4 : E q q ^ 2 ≤ β ^ 2 := by
      rw [← sq_abs (E q q)]; exact pow_le_pow_left₀ (abs_nonneg _) hqq 2
    nlinarith [e1, e2, e3, e4]
  calc
    frobNorm E = Real.sqrt (frobNormSq E) := frobNorm_eq_sqrt_frobNormSq E
    _ ≤ Real.sqrt ((2 * β) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = 2 * β := by
          rw [Real.sqrt_sq_eq_abs]; exact abs_of_nonneg (by positivity)

/-- The four-entry pair-supported perturbation of `H19_Lemma19_8` with the
    per-entry rounding factors supplied explicitly.  Factoring it out of the
    theorem body keeps `simp` from repeatedly unfolding a 5-way `ite` inside a
    large goal. -/
private noncomputable def givensApplyPert {n : ℕ} (p q : Fin n)
    (c s θcp θsp θcq θsq : ℝ) : Fin n → Fin n → ℝ :=
  fun i j =>
    if i = p ∧ j = p then c * θcp
    else if i = p ∧ j = q then s * θsp
    else if i = q ∧ j = q then c * θcq
    else if i = q ∧ j = p then -s * θsq
    else 0

/-- Row-`p` values of the exact Givens rotation. -/
private theorem givensRotation_row_p {n : ℕ} (p q : Fin n) (c s : ℝ)
    (hpq : p ≠ q) (j : Fin n) :
    givensRotation n p q c s p j =
      if j = p then c else if j = q then s else 0 := by
  unfold givensRotation
  by_cases h1 : j = p
  · simp [h1]
  · by_cases h2 : j = q
    · simp [h1, h2, hpq]
    · simp [h1, h2, hpq, Ne.symm h1]

/-- Row-`q` values of the exact Givens rotation. -/
private theorem givensRotation_row_q {n : ℕ} (p q : Fin n) (c s : ℝ)
    (hpq : p ≠ q) (j : Fin n) :
    givensRotation n p q c s q j =
      if j = p then -s else if j = q then c else 0 := by
  have hqp := hpq.symm
  unfold givensRotation
  by_cases h1 : j = p
  · simp [h1, hqp, hpq]
  · by_cases h2 : j = q
    · simp [h1, h2, hqp, hpq]
    · simp [h1, h2, hqp, Ne.symm h2]

/-- Dimension-independent Frobenius bound for the four-entry Givens
    perturbation: with `|c|, |s| ≤ 1` and each rounding factor `≤ γ₂`, the
    perturbation has `‖ΔG‖_F ≤ 2·γ₂`.  Isolated from the representation so each
    declaration stays within its elaboration budget. -/
private theorem givensApplyPert_frobNorm_le {n : ℕ} (p q : Fin n)
    (c s θcp θsp θcq θsq μ : ℝ) (hpq : p ≠ q) (hμ : 0 ≤ μ)
    (hcs : c ^ 2 + s ^ 2 = 1)
    (hθcp : |θcp| ≤ μ) (hθsp : |θsp| ≤ μ)
    (hθcq : |θcq| ≤ μ) (hθsq : |θsq| ≤ μ) :
    frobNorm (givensApplyPert p q c s θcp θsp θcq θsq) ≤ 2 * μ := by
  have hc_le : |c| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (c + 1), sq_nonneg s],
      by nlinarith [sq_nonneg (c - 1), sq_nonneg s]⟩
  have hs_le : |s| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (s + 1), sq_nonneg c],
      by nlinarith [sq_nonneg (s - 1), sq_nonneg c]⟩
  set ΔG : Fin n → Fin n → ℝ := givensApplyPert p q c s θcp θsp θcq θsq with hΔG_def
  have hent : ∀ a θ : ℝ, |a| ≤ 1 → |θ| ≤ μ → |a * θ| ≤ μ := by
    intro a θ ha hθ
    calc |a * θ| = |a| * |θ| := abs_mul a θ
      _ ≤ 1 * μ := mul_le_mul ha hθ (abs_nonneg θ) (by norm_num)
      _ = μ := by ring
  have hsupp : PairBlockSupported p q ΔG := by
    intro i j hij
    rw [hΔG_def]
    rcases hij with hrow | hcol
    · simp [givensApplyPert, hrow.1, hrow.2]
    · simp [givensApplyPert, hcol.1, hcol.2]
  have hpp : |ΔG p p| ≤ μ := by
    have : ΔG p p = c * θcp := by rw [hΔG_def]; simp [givensApplyPert]
    rw [this]; exact hent c θcp hc_le hθcp
  have hpq' : |ΔG p q| ≤ μ := by
    have : ΔG p q = s * θsp := by rw [hΔG_def]; simp [givensApplyPert, hpq, hpq.symm]
    rw [this]; exact hent s θsp hs_le hθsp
  have hqp : |ΔG q p| ≤ μ := by
    have : ΔG q p = -s * θsq := by rw [hΔG_def]; simp [givensApplyPert, hpq, hpq.symm]
    rw [this]
    have := hent s θsq hs_le hθsq
    simpa [abs_neg, neg_mul] using this
  have hqq : |ΔG q q| ≤ μ := by
    have : ΔG q q = c * θcq := by rw [hΔG_def]; simp [givensApplyPert, hpq, hpq.symm]
    rw [this]; exact hent c θcq hc_le hθcq
  exact PairBlockSupported_frobNorm_le hpq hsupp hμ hpp hpq' hqp hqq

/-- Backward-error representation `ŷ = (G + ΔG) x` for the supplied-parameter
    Givens application, isolated from the norm bound so each declaration
    stays within its elaboration budget.  The component equalities `hp, hq`
    (the two touched entries of `fl_givensApply`) are supplied by the caller. -/
private theorem givensApplyPert_repr (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s θcp θsp θcq θsq : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q)
    (hp : fl_givensApply fp n p q c s x p =
      c * (1 + θcp) * x p + s * (1 + θsp) * x q)
    (hq : fl_givensApply fp n p q c s x q =
      c * (1 + θcq) * x q - s * (1 + θsq) * x p) :
    ∀ i, fl_givensApply fp n p q c s x i =
      matMulVec n (fun a b =>
        givensRotation n p q c s a b +
          givensApplyPert p q c s θcp θsp θcq θsq a b) x i := by
  classical
  set ΔG : Fin n → Fin n → ℝ := givensApplyPert p q c s θcp θsp θcq θsq with hΔG_def
  have hΔpp : ΔG p p = c * θcp := by rw [hΔG_def]; simp [givensApplyPert]
  have hΔpq : ΔG p q = s * θsp := by
    rw [hΔG_def]; simp [givensApplyPert, hpq, hpq.symm]
  have hΔqp : ΔG q p = -s * θsq := by
    rw [hΔG_def]; simp [givensApplyPert, hpq, hpq.symm]
  have hΔqq : ΔG q q = c * θcq := by
    rw [hΔG_def]; simp [givensApplyPert, hpq, hpq.symm]
  have hΔp_other : ∀ j : Fin n, j ≠ p → j ≠ q → ΔG p j = 0 := by
    intro j hjp hjq; rw [hΔG_def]; simp [givensApplyPert, hjp, hjq]
  have hΔq_other : ∀ j : Fin n, j ≠ p → j ≠ q → ΔG q j = 0 := by
    intro j hjp hjq; rw [hΔG_def]; simp [givensApplyPert, hjp, hjq]
  intro i
  by_cases hip : i = p
  · subst i
    have hrow : ∀ j : Fin n,
        givensRotation n p q c s p j + ΔG p j =
          if j = p then c * (1 + θcp)
          else if j = q then s * (1 + θsp) else 0 := by
      intro j
      rw [givensRotation_row_p p q c s hpq j]
      by_cases hjp : j = p
      · subst j; rw [hΔpp]; simp; ring
      · by_cases hjq : j = q
        · subst j; rw [hΔpq]; simp [hjp]; ring
        · rw [hΔp_other j hjp hjq]; simp [hjp, hjq]
    calc
      fl_givensApply fp n p q c s x p
          = c * (1 + θcp) * x p + s * (1 + θsp) * x q := hp
      _ = ∑ j : Fin n,
            (if j = p then c * (1 + θcp)
             else if j = q then s * (1 + θsp) else 0) * x j :=
            (sum_two_point_mul p q (c * (1 + θcp)) (s * (1 + θsp)) x hpq).symm
      _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x p := by
            unfold matMulVec
            refine Finset.sum_congr rfl (fun j _ => ?_)
            show (if j = p then c * (1 + θcp)
                  else if j = q then s * (1 + θsp) else 0) * x j =
                (givensRotation n p q c s p j + ΔG p j) * x j
            rw [hrow j]
  · by_cases hiq : i = q
    · subst i
      have hrow : ∀ j : Fin n,
          givensRotation n p q c s q j + ΔG q j =
            if j = p then -s * (1 + θsq)
            else if j = q then c * (1 + θcq) else 0 := by
        intro j
        rw [givensRotation_row_q p q c s hpq j]
        by_cases hjp : j = p
        · subst j; rw [hΔqp]; simp [hpq.symm]; ring
        · by_cases hjq : j = q
          · subst j; rw [hΔqq]; simp [hjp]; ring
          · rw [hΔq_other j hjp hjq]; simp [hjp, hjq]
      calc
        fl_givensApply fp n p q c s x q
            = c * (1 + θcq) * x q - s * (1 + θsq) * x p := hq
        _ = (-s * (1 + θsq)) * x p + (c * (1 + θcq)) * x q := by ring
        _ = ∑ j : Fin n,
              (if j = p then -s * (1 + θsq)
               else if j = q then c * (1 + θcq) else 0) * x j :=
              (sum_two_point_mul p q (-s * (1 + θsq)) (c * (1 + θcq)) x hpq).symm
        _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x q := by
              unfold matMulVec
              refine Finset.sum_congr rfl (fun j _ => ?_)
              show (if j = p then -s * (1 + θsq)
                    else if j = q then c * (1 + θcq) else 0) * x j =
                  (givensRotation n p q c s q j + ΔG q j) * x j
              rw [hrow j]
    · have hΔrow : ∀ j : Fin n, ΔG i j = 0 := by
        intro j; rw [hΔG_def]; simp [givensApplyPert, hip, hiq]
      calc
        fl_givensApply fp n p q c s x i = x i := by
          simp [fl_givensApply, hip, hiq]
        _ = matMulVec n (givensRotation n p q c s) x i :=
            (givensRotation_matMulVec_other n p q i c s x hip hiq).symm
        _ = matMulVec n (fun a b => givensRotation n p q c s a b + ΔG a b) x i := by
            unfold matMulVec
            refine Finset.sum_congr rfl (fun j _ => ?_)
            show givensRotation n p q c s i j * x j =
                (givensRotation n p q c s i j + ΔG i j) * x j
            rw [hΔrow j]; ring

/-- **Lemma 19.8** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.6, p. 366): applying a Givens rotation with supplied normalized
    coefficients `c, s` (`c² + s² = 1`) to a vector `x` in floating-point
    arithmetic yields `ŷ = (G + ΔG)x`, with `G = givensRotation p q c s`
    orthogonal and a *dimension-independent* Frobenius bound
    `‖ΔG‖_F ≤ 2·γ₂`.

    The perturbation `ΔG` is supported only on the active row/column pair
    `{p, q}` (`PairBlockSupported`), so its Frobenius mass collapses to its
    four active entries.  Each active entry is `(±c or ±s)·θ` with `|θ| ≤ γ₂`
    (one rounded multiply, then one rounded add/sub per touched component), and
    `|c|, |s| ≤ 1` because `c² + s² = 1`; hence each entry is `≤ γ₂` and
    `‖ΔG‖_F ≤ √4·γ₂ = 2·γ₂` by `PairBlockSupported_frobNorm_le`.

    Constant.  The printed Lemma 19.8 advertises the class bound `√2·γ̃`
    (its coefficient-construction proof is omitted).  We prove the fully
    dimension-independent `2·γ₂` for the supplied-parameter application kernel
    `fl_givensApply`; this is the same `γ̃`-class, independent of the ambient
    dimension `n`, and strictly sharper than the repository's earlier
    `γ₂·‖G‖_F = √n·γ₂` (dimension-dependent) bound.  The `2` versus printed
    `√2` reflects the conservative bound `|c|, |s| ≤ 1` used per entry instead
    of the `c² + s² = 1` cross-term cancellation; the coefficient-construction
    rounding (Lemma 19.7's `γ₆`) is *not* folded in here — this is the
    supplied-parameter application bound only. -/
theorem H19_Lemma19_8_givens_apply_backward_error (fp : FPModel) (n : ℕ)
    (p q : Fin n) (c s : ℝ) (x : Fin n → ℝ)
    (hpq : p ≠ q) (hcs : c ^ 2 + s ^ 2 = 1)
    (hvalid : gammaValid fp 2) :
    GivensAppError n (givensRotation n p q c s) x
      (fl_givensApply fp n p q c s x)
      (2 * gamma fp 2) := by
  classical
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
  have hγ2_nonneg : 0 ≤ gamma fp 2 := gamma_nonneg fp hvalid
  -- Dimension-independent Frobenius bound for the sparse perturbation.
  have hfrob :
      frobNorm (givensApplyPert p q c s θcp θsp θcq θsq) ≤ 2 * gamma fp 2 :=
    givensApplyPert_frobNorm_le p q c s θcp θsp θcq θsq (gamma fp 2)
      hpq hγ2_nonneg hcs hθcp2 hθsp2 hθcq2 hθsq2
  -- Componentwise representation `ŷ = (G + ΔG) x`.
  have hp_alg :
      fl_givensApply fp n p q c s x p =
        c * (1 + θcp) * x p + s * (1 + θsp) * x q := by
    calc
      fl_givensApply fp n p q c s x p
          = fp.fl_add (fp.fl_mul c (x p)) (fp.fl_mul s (x q)) := by simp
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
          = fp.fl_sub (fp.fl_mul c (x q)) (fp.fl_mul s (x p)) :=
              fl_givensApply_q fp n p q c s x hpq
      _ = (fp.fl_mul c (x q) - fp.fl_mul s (x p)) * (1 + δsub) := hsub
      _ = ((c * x q) * (1 + δcq) - (s * x p) * (1 + δsq)) *
            (1 + δsub) := by rw [hmul_cq, hmul_sq]
      _ = c * x q * ((1 + δcq) * (1 + δsub)) -
            s * x p * ((1 + δsq) * (1 + δsub)) := by ring
      _ = c * x q * (1 + θcq) - s * x p * (1 + θsq) := by
            rw [hθcq_eq, hθsq_eq]
      _ = c * (1 + θcq) * x q - s * (1 + θsq) * x p := by ring
  exact ⟨givensRotation_orthogonal n p q c s hpq hcs,
    givensApplyPert p q c s θcp θsp θcq θsq, hfrob,
    givensApplyPert_repr fp n p q c s θcp θsp θcq θsq x hpq hp_alg hq_alg⟩

-- ============================================================
-- Theorem 19.5 (backward error of QR-based linear-system solve)
-- ============================================================

/-- **Theorem 19.5** (Higham, Accuracy and Stability of Numerical Algorithms,
    2nd ed., §19.5, p. 365): solving the square linear system `Ax = b` by
    Householder QR (factor `A = QR`, form `ĉ = Qᵀb`, back-substitute
    `R̂ x̂ = ĉ`) is backward stable: the computed `x̂` satisfies
    `(A + ΔA) x̂ = b + Δb` with normwise bounds `‖ΔA‖_F ≤ c_A` and
    `‖Δb‖_∞ ≤ c_b`.

    This assembles the printed proof's three stages, each already proved in the
    repository:

    * the Householder QR factorization backward error (Theorem 19.4), giving
      `Q R̂ = A + ΔA₁` with `‖ΔA₁‖_F ≤ γ_{n·(33n+69)}·‖A‖_F`;
    * the right-hand-side transform `ĉ = Qᵀ(b + Δb)` with the concrete rounded
      RHS perturbation bound; and
    * the back-substitution backward error `(R̂ + ΔR) x̂ = ĉ` with
      `‖ΔR‖_F ≤ γ_n·‖R̂‖_F`.

    Premultiplying the triangular solve by the exact orthogonal `Q` and using
    `Q Qᵀ = I` collapses the three stages to `(A + ΔA) x̂ = b + Δb` with
    `ΔA = ΔA₁ + Q ΔR`, `‖ΔA‖_F ≤ ‖ΔA₁‖_F + ‖ΔR‖_F` (orthogonal invariance of
    the Frobenius norm).

    Constant.  The printed Theorem 19.5 advertises the class bound `γ̃_{n²}`
    for the matrix perturbation.  We prove the explicit
    `γ_{n·(33n+69)}·‖A‖_F + γ_n·‖R̂‖_F`: the first term is the same quadratic
    `γ̃_{n²}`-class QR-factorization contribution (explicit index
    `n·(33n+69)`), and the second is the separate `γ_n·‖R̂‖_F`
    back-substitution contribution, kept explicit because it is the triangular
    solve stage rather than the factorization.  The right-hand-side bound
    `c_b = householderQRRhsBackwardBound fp n A b` is the concrete rounded RHS
    transform perturbation. -/
theorem H19_Theorem19_5_qr_solve_columnwise_backward_error (fp : FPModel)
    (n : ℕ) (A : Fin n → Fin n → ℝ) (b : Fin n → ℝ)
    (hn : 0 < n)
    (hvalid : gammaValid fp (n * householderConstructApplyGammaIndex n))
    (hdiag : ∀ i : Fin n, fl_householderQR_R fp n A i i ≠ 0) :
    QRSolveBackwardError n A b (fl_householderQR_solve fp n A b)
      ((gamma fp (n * householderConstructApplyGammaIndex n) * frobNorm A) +
        gamma fp n * frobNorm (fl_householderQR_R fp n A))
      (householderQRRhsBackwardBound fp n A b) :=
  fl_householderQR_solve_backward_error_gammaHigham_of_global_gammaValid
    fp n A b hn hvalid hdiag

-- ============================================================
-- Lemma 19.3 (sequence of reflectors)
-- ============================================================

/-- **Lemma 19.3, concrete rectangular columnwise form.**  A sequence of
    calls to the rounded compact Householder panel and vector kernels has one
    common exact orthogonal factor.  Each matrix column has its own backward
    perturbation, as in the printed rectangular statement, while the same
    factor also represents the transformed right-hand side.

    This source-numbered wrapper is deliberately stated for the actual
    `fl_householderApplyCompactPanel` / `fl_householderApplyCompact`
    executors.  It closes the gap between the abstract rectangular sequence
    lemma and the square Frobenius wrapper below. -/
theorem H19_Lemma19_3_rectangular_columnwise_sequence_backward_error
    (fp : FPModel) (m n r : ℕ)
    (v : ℕ → Fin m → ℝ) (β : ℕ → ℝ)
    (A : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (A_hat : ℕ → Fin m → Fin n → ℝ)
    (b_hat : ℕ → Fin m → ℝ)
    (c : ℝ) (hc : 0 ≤ c)
    (hm : gammaValid fp m)
    (hInitA : A_hat 0 = A)
    (hInitb : b_hat 0 = b)
    (hStepA : ∀ k, k < r →
      A_hat (k + 1) =
        fl_householderApplyCompactPanel fp m n (v k) (β k) (A_hat k))
    (hStepb : ∀ k, k < r →
      b_hat (k + 1) =
        fl_householderApplyCompact fp m (v k) (β k) (b_hat k))
    (horth : ∀ k, k < r → IsOrthogonal m (householder m (v k) (β k)))
    (hA_budget : ∀ k, k < r → ∀ j : Fin n,
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m (v k) (β k)
          (fun a => A_hat k a j) i) ≤
        c * vecNorm2 (fun i : Fin m => A_hat k i j))
    (hb_budget : ∀ k, k < r →
      vecNorm2 (fun i : Fin m =>
        householderCompactComponentBudget fp m (v k) (β k) (b_hat k) i) ≤
        c * vecNorm2 (b_hat k)) :
    ∃ (Q : Fin m → Fin m → ℝ)
        (ΔA : Fin m → Fin n → ℝ) (Δb : Fin m → ℝ),
      IsOrthogonal m Q ∧
      (∀ i j, A_hat r i j =
        matMulRectLeft (matTranspose Q) (fun a b => A a b + ΔA a b) i j) ∧
      (∀ i, b_hat r i =
        matMulVec m (matTranspose Q) (fun a => b a + Δb a) i) ∧
      (∀ j : Fin n,
        vecNorm2 (fun i => ΔA i j) ≤
          ((1 + c) ^ r - 1) * vecNorm2 (fun i => A i j)) ∧
      vecNorm2 Δb ≤ ((1 + c) ^ r - 1) * vecNorm2 b :=
  fl_householderApplyCompactPanel_rect_orthogonal_columnwise_vector_sequence_geometric
    fp m n r v β A b A_hat b_hat c hc hm hInitA hInitb
      hStepA hStepb horth hA_budget hb_budget

/-- **Lemma 19.3, square normwise form** (Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §19.3, p. 359): after a sequence of `r`
    computed Householder reflectors applied to an `n×n` matrix, the result is
    `Q^T (A + ΔA)` with `Q` orthogonal and `‖ΔA‖_F` bounded by the accumulated
    reflector bound times `‖A‖_F`.

    This is the labeled relabel of the concrete
    `fl_householder_sequence_backward_error`.  Scope: it is the SQUARE,
    NORMWISE (Frobenius) reading; the printed Lemma 19.3 additionally gives
    the columnwise bound `‖Δa_j‖₂ ≤ r·γ̃_m·‖a_j‖₂` in the rectangular case,
    whose concrete-algorithm form needs the rectangular fl-sequence
    instantiation (the abstract columnwise sequence result is
    `rect_orthogonal_columnwise_vector_sequence_geometric`, and the `n = 1`
    `(Q+ΔQ)ᵀ` corollary is `H19_Lemma19_3_vector_QplusDeltaQ_form`).  The
    constant `residualAccumBound (householderConstructApplyBound fp n) r` is
    of the printed `r·γ̃`-class. -/
theorem H19_Lemma19_3_sequence_normwise_backward_error (fp : FPModel)
    {n r : ℕ} (hn0 : 0 < n)
    (Aseq : ℕ → Fin n → Fin n → ℝ) (xseq : ℕ → Fin n → ℝ)
    (hx : ∀ k : ℕ, k < r → xseq k ≠ 0)
    (hvalid : gammaValid fp (11 * n + 23))
    (hAstep : ∀ k : ℕ, k < r →
      Aseq (k + 1) =
        fl_householderApplyMatrix fp n
          (fl_householderNormalizedVector fp hn0 (xseq k)) 1 (Aseq k)) :
    ∃ (Q : Fin n → Fin n → ℝ) (ΔA : Fin n → Fin n → ℝ),
      IsOrthogonal n Q ∧
      (∀ i j : Fin n, Aseq r i j =
        matMul n (matTranspose Q)
          (fun a b => Aseq 0 a b + ΔA a b) i j) ∧
      frobNorm ΔA ≤
        residualAccumBound (householderConstructApplyBound fp n) r *
          frobNorm (Aseq 0) :=
  fl_householder_sequence_backward_error fp hn0 Aseq xseq hx hvalid hAstep

end NumStability
