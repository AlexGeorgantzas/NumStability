-- Algorithms/Cholesky/CholeskyPerturbation.lean
--
-- Theorem 10.8 (Sun): Perturbation sensitivity of the Cholesky factorization.
--
-- If A is SPD with Cholesky factorization A = R^T R and ΔA is symmetric
-- with ‖A⁻¹ΔA‖₂ < 1, then A + ΔA = (R + ΔR)^T (R + ΔR) and:
--   ‖ΔR‖_F / ‖R‖_F ≤ κ₂(A) / (2‖A‖₂) · ‖ΔA‖_F   (normwise)
--   |ΔR| ≤ triu(|R⁻ᵀ||ΔA||R⁻¹|) · (1 + O(‖ΔA‖))   (componentwise)

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor
import NumStability.Algorithms.Cholesky.CholeskySpec

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §10.2  Upper triangular part
-- ============================================================

/-- **Upper triangular part** of a matrix: triu(A)_{ij} = A_{ij} if i ≤ j, else 0. -/
noncomputable def triuPart {n : ℕ} (A : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => if i.val ≤ j.val then A i j else 0

lemma triuPart_upper {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, j.val < i.val → triuPart A i j = 0 := by
  intro i j hij
  unfold triuPart
  simp [show ¬(i.val ≤ j.val) from by omega]

lemma triuPart_diag_and_above {n : ℕ} (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, i.val ≤ j.val → triuPart A i j = A i j := by
  intro i j hij
  unfold triuPart
  simp [hij]

-- ============================================================
-- §10.2  The `up` operator (Theorem 10.8 proof machinery)
-- ============================================================

/-- **The `up` operator** (proof route for Theorem 10.8; Sun, BIT 31
    (1991), advisory route logged in the chapter report): the upper
    triangular part with halved diagonal,
    `up(Y)_{ij} = Y_{ij}` for `i < j`, `Y_{ii}/2` on the diagonal, `0`
    below. -/
noncomputable def upHalf {n : ℕ} (Y : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j =>
    if i.val < j.val then Y i j
    else if i = j then Y i j / 2
    else 0

lemma upHalf_strict_lower {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : j.val < i.val) : upHalf Y i j = 0 := by
  unfold upHalf
  rw [if_neg (by omega : ¬ i.val < j.val),
    if_neg (fun he : i = j => by subst he; omega)]

lemma upHalf_strict_upper {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (i j : Fin n) (hij : i.val < j.val) : upHalf Y i j = Y i j := by
  unfold upHalf
  rw [if_pos hij]

lemma upHalf_diag {n : ℕ} (Y : Fin n → Fin n → ℝ) (i : Fin n) :
    upHalf Y i i = Y i i / 2 := by
  unfold upHalf
  rw [if_neg (lt_irrefl _), if_pos rfl]

/-- **Triangular recovery** (Theorem 10.8 proof, step 1): an upper
    triangular `X` is recovered from its symmetrization,
    `up(X + Xᵀ) = X`. -/
theorem upHalf_add_transpose {n : ℕ} (X : Fin n → Fin n → ℝ)
    (hX : ∀ i j : Fin n, j.val < i.val → X i j = 0) :
    ∀ i j : Fin n, upHalf (fun p q => X p q + X q p) i j = X i j := by
  intro i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · rw [upHalf_strict_upper _ i j h]
    rw [hX j i h, add_zero]
  · have hij : i = j := Fin.ext h
    subst hij
    rw [upHalf_diag]
    ring
  · rw [upHalf_strict_lower _ i j h, hX i j h]

/-- **Frobenius halving** (Theorem 10.8 proof, step 2): for a symmetric
    matrix `Y`, `‖up(Y)‖_F² ≤ ‖Y‖_F²/2` — the strict upper part carries
    at most half of the off-diagonal mass and the halved diagonal at
    most a quarter of the diagonal mass. -/
theorem frobNormSq_upHalf_le_half {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (hY : ∀ i j : Fin n, Y i j = Y j i) :
    frobNormSq (upHalf Y) ≤ frobNormSq Y / 2 := by
  have hpoint : ∀ i j : Fin n,
      2 * upHalf Y i j ^ 2 + 2 * upHalf Y j i ^ 2 ≤
      Y i j ^ 2 + Y j i ^ 2 := by
    intro i j
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [upHalf_strict_upper Y i j h, upHalf_strict_lower Y j i h,
        hY j i]
      nlinarith [sq_nonneg (Y i j)]
    · have hij : i = j := Fin.ext h
      subst hij
      rw [upHalf_diag]
      nlinarith [sq_nonneg (Y i i)]
    · rw [upHalf_strict_lower Y i j h, upHalf_strict_upper Y j i h,
        hY j i]
      nlinarith [sq_nonneg (Y i j)]
  have hsum : ∑ i : Fin n, ∑ j : Fin n,
      (2 * upHalf Y i j ^ 2 + 2 * upHalf Y j i ^ 2) ≤
      ∑ i : Fin n, ∑ j : Fin n, (Y i j ^ 2 + Y j i ^ 2) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
  have hsplit : ∀ (M : Fin n → Fin n → ℝ) (c : ℝ),
      ∑ i : Fin n, ∑ j : Fin n, (c * M i j ^ 2 + c * M j i ^ 2) =
      c * (∑ i : Fin n, ∑ j : Fin n, M i j ^ 2) +
      c * (∑ i : Fin n, ∑ j : Fin n, M j i ^ 2) := by
    intro M c
    have inner : ∀ i : Fin n, ∑ j : Fin n,
        (c * M i j ^ 2 + c * M j i ^ 2) =
        c * (∑ j : Fin n, M i j ^ 2) +
        c * (∑ j : Fin n, M j i ^ 2) := by
      intro i
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [Finset.sum_congr rfl fun i _ => inner i,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hswapU : ∑ i : Fin n, ∑ j : Fin n, upHalf Y j i ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, upHalf Y i j ^ 2 :=
    Finset.sum_comm
  have hswapY : ∑ i : Fin n, ∑ j : Fin n, Y j i ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, Y i j ^ 2 :=
    Finset.sum_comm
  have hL := hsplit (upHalf Y) 2
  have hR := hsplit Y 1
  rw [hswapU] at hL
  rw [hswapY] at hR
  simp only [one_mul] at hR
  unfold frobNormSq
  have hsum' := hsum
  rw [hL] at hsum'
  have hRfix : ∑ i : Fin n, ∑ j : Fin n, (Y i j ^ 2 + Y j i ^ 2) =
      (∑ i : Fin n, ∑ j : Fin n, Y i j ^ 2) +
      ∑ i : Fin n, ∑ j : Fin n, Y i j ^ 2 := by
    have := hsplit Y 1
    simp only [one_mul] at this
    rw [this, hswapY]
  rw [hRfix] at hsum'
  linarith

/-- **Perturbed Gram identity** (Theorem 10.8 proof, step 3): if
    `RᵀR = A` and `(R+ΔR)ᵀ(R+ΔR) = A + ΔA` entrywise, the perturbation
    satisfies `RᵀΔR + ΔRᵀR + ΔRᵀΔR = ΔA` entrywise — the exact identity
    the `up`-operator route symmetrizes. -/
theorem cholesky_perturbation_gram_identity {n : ℕ}
    (A ΔA R ΔR : Fin n → Fin n → ℝ)
    (hA : ∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j)
    (hAΔ : ∀ i j : Fin n, ∑ k : Fin n,
      (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) :
    ∀ i j : Fin n,
      (∑ k : Fin n, R k i * ΔR k j) + (∑ k : Fin n, ΔR k i * R k j) +
      (∑ k : Fin n, ΔR k i * ΔR k j) = ΔA i j := by
  intro i j
  have h := hAΔ i j
  have hsplit : ∑ k : Fin n,
      (R k i + ΔR k i) * (R k j + ΔR k j) =
      (∑ k : Fin n, R k i * R k j) +
      ((∑ k : Fin n, R k i * ΔR k j) + (∑ k : Fin n, ΔR k i * R k j) +
       (∑ k : Fin n, ΔR k i * ΔR k j)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsplit, hA i j] at h
  linarith

/-- **Scalar absorption endgame** (Theorem 10.8 proof, step 4): from
    the quadratic self-bound `t ≤ a(δ + t²)` and the small-root
    certificate `a·t < 1`, `t ≤ aδ/(1 − a·t)`. -/
theorem cholesky_perturbation_scalar_endgame (a δ t : ℝ)
    (hquad : t ≤ a * (δ + t ^ 2)) (hat : a * t < 1) :
    t ≤ a * δ / (1 - a * t) := by
  rw [le_div_iff₀ (by linarith)]
  nlinarith

/-- **Scalar endgame, display form** (Theorem 10.8, printed display
    shape): if moreover `a·t ≤ c < 1` with `a, δ ≥ 0`, the bound takes
    the source's monotone form `t ≤ aδ/(1 − c)`. -/
theorem cholesky_perturbation_scalar_endgame_display (a δ t c : ℝ)
    (ha : 0 ≤ a) (hδ : 0 ≤ δ)
    (hquad : t ≤ a * (δ + t ^ 2))
    (hac : a * t ≤ c) (hc1 : c < 1) :
    t ≤ a * δ / (1 - c) := by
  have hat : a * t < 1 := lt_of_le_of_lt hac hc1
  have h1 := cholesky_perturbation_scalar_endgame a δ t hquad hat
  have h2 : a * δ / (1 - a * t) ≤ a * δ / (1 - c) :=
    div_le_div₀ (mul_nonneg ha hδ) le_rfl (by linarith) (by linarith)
  exact h1.trans h2

/-- **Frobenius–operator product bound, left factor** (Theorem 10.8
    proof, step 5): an operator-2-norm certificate on `M` gives
    `‖M·N‖_F² ≤ c²·‖N‖_F²`, column by column. -/
theorem frobNormSq_matMul_left_le {n : ℕ}
    (M N : Fin n → Fin n → ℝ) (c : ℝ)
    (hM : opNorm2Le M c) :
    frobNormSq (matMul n M N) ≤ c ^ 2 * frobNormSq N := by
  have hcol : ∀ j : Fin n,
      (∑ i : Fin n, matMul n M N i j ^ 2) ≤
      c ^ 2 * ∑ k : Fin n, N k j ^ 2 := by
    intro j
    have h := hM (fun k => N k j)
    have hveq : matMulVec n M (fun k => N k j) =
        fun i => matMul n M N i j := rfl
    rw [hveq] at h
    have h0 := vecNorm2_nonneg (fun i => matMul n M N i j)
    have h2 : vecNorm2 (fun i => matMul n M N i j) ^ 2 ≤
        (c * vecNorm2 (fun k => N k j)) ^ 2 := by nlinarith [h]
    rw [vecNorm2_sq, mul_pow, vecNorm2_sq] at h2
    exact h2
  calc frobNormSq (matMul n M N)
      = ∑ j : Fin n, ∑ i : Fin n, matMul n M N i j ^ 2 :=
        Finset.sum_comm
    _ ≤ ∑ j : Fin n, c ^ 2 * ∑ k : Fin n, N k j ^ 2 :=
        Finset.sum_le_sum fun j _ => hcol j
    _ = c ^ 2 * ∑ j : Fin n, ∑ k : Fin n, N k j ^ 2 := by
        rw [Finset.mul_sum]
    _ = c ^ 2 * frobNormSq N := by
        rw [show (∑ j : Fin n, ∑ k : Fin n, N k j ^ 2) = frobNormSq N from
          Finset.sum_comm]

/-- **Frobenius–operator product bound, right factor** (Theorem 10.8
    proof, step 5): an operator-2-norm certificate on `Nᵀ` gives
    `‖M·N‖_F² ≤ c²·‖M‖_F²`, row by row. -/
theorem frobNormSq_matMul_right_le {n : ℕ}
    (M N : Fin n → Fin n → ℝ) (c : ℝ)
    (hNT : opNorm2Le (fun i j => N j i) c) :
    frobNormSq (matMul n M N) ≤ c ^ 2 * frobNormSq M := by
  have hrow : ∀ i : Fin n,
      (∑ j : Fin n, matMul n M N i j ^ 2) ≤
      c ^ 2 * ∑ k : Fin n, M i k ^ 2 := by
    intro i
    have h := hNT (fun k => M i k)
    have hveq : matMulVec n (fun p q => N q p) (fun k => M i k) =
        fun j => matMul n M N i j := by
      funext j
      unfold matMulVec matMul
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hveq] at h
    have h0 := vecNorm2_nonneg (fun j => matMul n M N i j)
    have h2 : vecNorm2 (fun j => matMul n M N i j) ^ 2 ≤
        (c * vecNorm2 (fun k => M i k)) ^ 2 := by nlinarith [h]
    rw [vecNorm2_sq, mul_pow, vecNorm2_sq] at h2
    exact h2
  calc frobNormSq (matMul n M N)
      ≤ ∑ i : Fin n, c ^ 2 * ∑ k : Fin n, M i k ^ 2 :=
        Finset.sum_le_sum fun i _ => hrow i
    _ = c ^ 2 * frobNormSq M := by
        rw [← Finset.mul_sum]
        rfl

/-- **Packaged upper-triangular inverse** (Theorem 10.8 proof, step 6):
    an upper-triangular matrix with nonzero diagonal has a two-sided
    inverse that is itself upper triangular — Mathlib's
    block-triangular inverse, exported in the repository's
    function-matrix predicates. -/
theorem upperTriangular_inverse_exists (k : ℕ) (U : Fin k → Fin k → ℝ)
    (hupper : ∀ i j : Fin k, j.val < i.val → U i j = 0)
    (hdiag : ∀ i, U i i ≠ 0) :
    ∃ V : Fin k → Fin k → ℝ,
      (∀ i j : Fin k, j.val < i.val → V i j = 0) ∧
      IsRightInverse k U V ∧ IsLeftInverse k U V := by
  let M : Matrix (Fin k) (Fin k) ℝ := Matrix.of U
  have hBT : M.BlockTriangular id := fun i j hij => hupper i j hij
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hBT]
    exact isUnit_iff_ne_zero.mpr
      (Finset.prod_ne_zero_iff.mpr fun i _ => hdiag i)
  haveI : Invertible M := M.invertibleOfIsUnitDet hdet
  refine ⟨fun i j => M⁻¹ i j, ?_, ?_, ?_⟩
  · intro i j hij
    exact Matrix.blockTriangular_inv_of_blockTriangular hBT hij
  · intro i j
    have hmul := Matrix.mul_nonsing_inv M hdet
    have h := congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A i j) hmul
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    exact h
  · intro i j
    have hmul := Matrix.nonsing_inv_mul M hdet
    have h := congrArg (fun A : Matrix (Fin k) (Fin k) ℝ => A i j) hmul
    simp only [Matrix.mul_apply, Matrix.one_apply] at h
    exact h

/-- Product of upper-triangular matrices is upper triangular. -/
lemma matMul_upper_upper {n : ℕ} (M N : Fin n → Fin n → ℝ)
    (hM : ∀ i j : Fin n, j.val < i.val → M i j = 0)
    (hN : ∀ i j : Fin n, j.val < i.val → N i j = 0) :
    ∀ i j : Fin n, j.val < i.val → matMul n M N i j = 0 := by
  intro i j hij
  unfold matMul
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases Nat.lt_or_ge k.val i.val with hk | hk
  · rw [hM i k hk, zero_mul]
  · rw [hN k j (by omega), mul_zero]

/-- **Frobenius submultiplicativity for the Gram square** (Theorem 10.8
    proof, step 7): `‖MᵀM‖_F² ≤ (‖M‖_F²)²`, by per-entry Cauchy–Schwarz
    over columns. -/
theorem frobNormSq_transpose_mul_self_le {n : ℕ}
    (M : Fin n → Fin n → ℝ) :
    frobNormSq (matMul n (fun i j => M j i) M) ≤ frobNormSq M ^ 2 := by
  have hentry : ∀ i j : Fin n,
      (matMul n (fun p q => M q p) M i j) ^ 2 ≤
      (∑ k : Fin n, M k i ^ 2) * ∑ k : Fin n, M k j ^ 2 := by
    intro i j
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n)) (fun k => M k i) (fun k => M k j)
    have hsq : (matMul n (fun p q => M q p) M i j) ^ 2 =
        (∑ k : Fin n, M k i * M k j) ^ 2 := rfl
    rw [hsq]
    exact hcs
  calc frobNormSq (matMul n (fun i j => M j i) M)
      ≤ ∑ i : Fin n, ∑ j : Fin n,
        (∑ k : Fin n, M k i ^ 2) * ∑ k : Fin n, M k j ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          hentry i j
    _ = (∑ i : Fin n, ∑ k : Fin n, M k i ^ 2) *
        ∑ j : Fin n, ∑ k : Fin n, M k j ^ 2 := by
        rw [Finset.sum_mul_sum]
    _ = frobNormSq M ^ 2 := by
        rw [show (∑ i : Fin n, ∑ k : Fin n, M k i ^ 2) = frobNormSq M
          from Finset.sum_comm, sq]

/-- **Symmetrized congruence identity** (Theorem 10.8 proof, step 8):
    with `X := ΔR·R⁻¹`, congruence of the Gram identity by `R⁻ᵀ·(·)·R⁻¹`
    collapses to `X + Xᵀ = R⁻ᵀ(ΔA − ΔRᵀΔR)R⁻¹` entrywise. -/
theorem cholesky_perturbation_symmetrized {n : ℕ}
    (A ΔA R ΔR Rinv : Fin n → Fin n → ℝ)
    (hA : ∀ i j : Fin n, ∑ k : Fin n, R k i * R k j = A i j)
    (hAΔ : ∀ i j : Fin n, ∑ k : Fin n,
      (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j)
    (hRight : IsRightInverse n R Rinv) :
    ∀ i j : Fin n,
      matMul n ΔR Rinv i j + matMul n ΔR Rinv j i =
      ∑ p : Fin n, ∑ q : Fin n, Rinv p i *
        (ΔA p q - ∑ k : Fin n, ΔR k p * ΔR k q) * Rinv q j := by
  intro i j
  have hG := cholesky_perturbation_gram_identity A ΔA R ΔR hA hAΔ
  -- pointwise rearrangement of the Gram identity
  have hpt : ∀ p q : Fin n,
      ΔA p q - ∑ k : Fin n, ΔR k p * ΔR k q =
      (∑ k : Fin n, R k p * ΔR k q) + ∑ k : Fin n, ΔR k p * R k q := by
    intro p q
    have h := hG p q
    linarith
  -- split the congruence sum along hpt
  have hsplit : ∑ p : Fin n, ∑ q : Fin n, Rinv p i *
      (ΔA p q - ∑ k : Fin n, ΔR k p * ΔR k q) * Rinv q j =
      (∑ p : Fin n, ∑ q : Fin n, Rinv p i *
        (∑ k : Fin n, R k p * ΔR k q) * Rinv q j) +
      ∑ p : Fin n, ∑ q : Fin n, Rinv p i *
        (∑ k : Fin n, ΔR k p * R k q) * Rinv q j := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hpt p q]
    ring
  -- first term collapses to X i j via the right inverse at row i
  have hterm1 : ∑ p : Fin n, ∑ q : Fin n, Rinv p i *
      (∑ k : Fin n, R k p * ΔR k q) * Rinv q j =
      matMul n ΔR Rinv i j := by
    have hflat : ∀ p q : Fin n,
        Rinv p i * (∑ k : Fin n, R k p * ΔR k q) * Rinv q j =
        ∑ k : Fin n, R k p * Rinv p i * (ΔR k q * Rinv q j) := by
      intro p q
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ p : Fin n, ∑ q : Fin n,
        Rinv p i * (∑ k : Fin n, R k p * ΔR k q) * Rinv q j
        = ∑ p : Fin n, ∑ q : Fin n, ∑ k : Fin n,
            R k p * Rinv p i * (ΔR k q * Rinv q j) :=
          Finset.sum_congr rfl fun p _ =>
            Finset.sum_congr rfl fun q _ => hflat p q
      _ = ∑ q : Fin n, ∑ p : Fin n, ∑ k : Fin n,
            R k p * Rinv p i * (ΔR k q * Rinv q j) := Finset.sum_comm
      _ = ∑ q : Fin n, ∑ k : Fin n, ∑ p : Fin n,
            R k p * Rinv p i * (ΔR k q * Rinv q j) :=
          Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = ∑ q : Fin n, ∑ k : Fin n,
            (∑ p : Fin n, R k p * Rinv p i) * (ΔR k q * Rinv q j) := by
          refine Finset.sum_congr rfl fun q _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ q : Fin n, ∑ k : Fin n,
            (if k = i then (1:ℝ) else 0) * (ΔR k q * Rinv q j) := by
          refine Finset.sum_congr rfl fun q _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [hRight k i]
      _ = ∑ q : Fin n, ΔR i q * Rinv q j := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl, one_mul]
          · intro b _ hb
            rw [if_neg hb, zero_mul]
          · intro hni
            exact absurd (Finset.mem_univ i) hni
      _ = matMul n ΔR Rinv i j := rfl
  -- second term collapses to X j i via the right inverse at row j
  have hterm2 : ∑ p : Fin n, ∑ q : Fin n, Rinv p i *
      (∑ k : Fin n, ΔR k p * R k q) * Rinv q j =
      matMul n ΔR Rinv j i := by
    have hflat : ∀ p q : Fin n,
        Rinv p i * (∑ k : Fin n, ΔR k p * R k q) * Rinv q j =
        ∑ k : Fin n, R k q * Rinv q j * (ΔR k p * Rinv p i) := by
      intro p q
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    calc ∑ p : Fin n, ∑ q : Fin n,
        Rinv p i * (∑ k : Fin n, ΔR k p * R k q) * Rinv q j
        = ∑ p : Fin n, ∑ q : Fin n, ∑ k : Fin n,
            R k q * Rinv q j * (ΔR k p * Rinv p i) :=
          Finset.sum_congr rfl fun p _ =>
            Finset.sum_congr rfl fun q _ => hflat p q
      _ = ∑ p : Fin n, ∑ k : Fin n, ∑ q : Fin n,
            R k q * Rinv q j * (ΔR k p * Rinv p i) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ p : Fin n, ∑ k : Fin n,
            (∑ q : Fin n, R k q * Rinv q j) * (ΔR k p * Rinv p i) := by
          refine Finset.sum_congr rfl fun p _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_mul]
      _ = ∑ p : Fin n, ∑ k : Fin n,
            (if k = j then (1:ℝ) else 0) * (ΔR k p * Rinv p i) := by
          refine Finset.sum_congr rfl fun p _ =>
            Finset.sum_congr rfl fun k _ => ?_
          rw [hRight k j]
      _ = ∑ p : Fin n, ΔR j p * Rinv p i := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_eq_single j]
          · rw [if_pos rfl, one_mul]
          · intro b _ hb
            rw [if_neg hb, zero_mul]
          · intro hnj
            exact absurd (Finset.mem_univ j) hnj
      _ = matMul n ΔR Rinv j i := rfl
  rw [hsplit, hterm1, hterm2]

/-- Unsquared-norm form of the left Frobenius–operator bound. -/
theorem frobNorm_matMul_left_le {n : ℕ}
    (M N : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hM : opNorm2Le M c) :
    frobNorm (matMul n M N) ≤ c * frobNorm N := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq]
  calc Real.sqrt (frobNormSq (matMul n M N))
      ≤ Real.sqrt (c ^ 2 * frobNormSq N) :=
        Real.sqrt_le_sqrt (frobNormSq_matMul_left_le M N c hM)
    _ = c * Real.sqrt (frobNormSq N) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Unsquared-norm form of the right Frobenius–operator bound. -/
theorem frobNorm_matMul_right_le {n : ℕ}
    (M N : Fin n → Fin n → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hNT : opNorm2Le (fun i j => N j i) c) :
    frobNorm (matMul n M N) ≤ c * frobNorm M := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq]
  calc Real.sqrt (frobNormSq (matMul n M N))
      ≤ Real.sqrt (c ^ 2 * frobNormSq M) :=
        Real.sqrt_le_sqrt (frobNormSq_matMul_right_le M N c hNT)
    _ = c * Real.sqrt (frobNormSq M) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- Unsquared-norm form of the `up`-operator halving:
    `‖up(Y)‖_F ≤ ‖Y‖_F / √2` for symmetric `Y`. -/
theorem frobNorm_upHalf_le {n : ℕ} (Y : Fin n → Fin n → ℝ)
    (hY : ∀ i j : Fin n, Y i j = Y j i) :
    frobNorm (upHalf Y) ≤ frobNorm Y / Real.sqrt 2 := by
  rw [frobNorm_eq_sqrt_frobNormSq, frobNorm_eq_sqrt_frobNormSq]
  calc Real.sqrt (frobNormSq (upHalf Y))
      ≤ Real.sqrt (frobNormSq Y / 2) :=
        Real.sqrt_le_sqrt (frobNormSq_upHalf_le_half Y hY)
    _ = Real.sqrt (frobNormSq Y) / Real.sqrt 2 :=
        Real.sqrt_div (frobNormSq_nonneg Y) 2

/-- Unsquared-norm form of the Gram-square bound:
    `‖MᵀM‖_F ≤ ‖M‖_F²`. -/
theorem frobNorm_transpose_mul_self_le {n : ℕ}
    (M : Fin n → Fin n → ℝ) :
    frobNorm (matMul n (fun i j => M j i) M) ≤ frobNorm M ^ 2 := by
  rw [frobNorm_eq_sqrt_frobNormSq]
  calc Real.sqrt (frobNormSq (matMul n (fun i j => M j i) M))
      ≤ Real.sqrt (frobNormSq M ^ 2) :=
        Real.sqrt_le_sqrt (frobNormSq_transpose_mul_self_le M)
    _ = frobNormSq M := Real.sqrt_sq (frobNormSq_nonneg M)
    _ = frobNorm M ^ 2 := by
        rw [frobNorm_eq_sqrt_frobNormSq, Real.sq_sqrt (frobNormSq_nonneg M)]

/-- `frobNorm` equals the sum-of-squares norm entrywise, so entrywise
    equal matrices have equal Frobenius norm. -/
theorem frobNorm_congr {n : ℕ} (M N : Fin n → Fin n → ℝ)
    (h : ∀ i j : Fin n, M i j = N i j) : frobNorm M = frobNorm N := by
  have : M = N := by funext i j; exact h i j
  rw [this]

/-- **Theorem 10.8 (Sun), normwise bound — assembled proof** (Higham
    §10.2). Let `A = RᵀR` be a Cholesky factorization (`R` upper
    triangular), `Rinv` a two-sided upper-triangular inverse of `R`, and
    `R + ΔR` a perturbed factor with `(R+ΔR)ᵀ(R+ΔR) = A + ΔA`.  With
    operator-2-norm certificates `cR ≥ ‖Rᵀ‖₂` and `cinv ≥ ‖R⁻ᵀ‖₂`, and
    the small-root certificate `a·‖ΔR‖_F < 1` where
    `a := cR·cinv²/√2`, the Frobenius norm of the factor perturbation
    obeys the implicit Sun bound

      `‖ΔR‖_F ≤ a·‖ΔA‖_F / (1 − a·‖ΔR‖_F)`.

    Route (logged oracle consultation, Sun BIT 31 (1991)):
    `X := ΔR·R⁻¹` is upper triangular, `X = up(X + Xᵀ)`, and
    `X + Xᵀ = R⁻ᵀ(ΔA − ΔRᵀΔR)R⁻¹`; the Frobenius halving `‖up(Y)‖_F ≤
    ‖Y‖_F/√2`, the congruence estimates, and the Gram-square bound give
    the quadratic self-bound `t ≤ a(‖ΔA‖_F + t²)` in `t := ‖ΔR‖_F`,
    which the scalar endgame absorbs.

    Honest deltas (recorded): the smallness enters as `a·t < 1` rather
    than Sun's continuity/branch argument; `cR`, `cinv` are supplied
    operator certificates (`cR² = ‖A‖₂`, `cinv² = ‖A⁻¹‖₂`, so
    `a = ‖A‖₂^{1/2}‖A⁻¹‖₂/√2`, first-order comparable to the printed
    `2^{-1/2}κ₂(A)ε/‖A‖`). -/
theorem cholesky_perturbation_normwise_proved {n : ℕ}
    (R ΔR Rinv ΔA : Fin n → Fin n → ℝ)
    (_hR_upper : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (hΔR_upper : ∀ i j : Fin n, j.val < i.val → ΔR i j = 0)
    (hRinv_upper : ∀ i j : Fin n, j.val < i.val → Rinv i j = 0)
    (hRinvR : IsLeftInverse n R Rinv)
    (hRRinv : IsRightInverse n R Rinv)
    (hGram : ∀ i j : Fin n, ∑ k : Fin n,
      (R k i + ΔR k i) * (R k j + ΔR k j) =
      (∑ k : Fin n, R k i * R k j) + ΔA i j)
    (cR cinv : ℝ) (hcR : 0 ≤ cR) (hcinv : 0 ≤ cinv)
    (hopR : opNorm2Le (fun i j => R j i) cR)
    (hopRinv : opNorm2Le (fun i j => Rinv j i) cinv)
    (hsmall : (cR * cinv ^ 2 / Real.sqrt 2) * frobNorm ΔR < 1) :
    frobNorm ΔR ≤
      (cR * cinv ^ 2 / Real.sqrt 2) * frobNorm ΔA /
      (1 - (cR * cinv ^ 2 / Real.sqrt 2) * frobNorm ΔR) := by
  set a : ℝ := cR * cinv ^ 2 / Real.sqrt 2 with ha
  set t : ℝ := frobNorm ΔR with ht
  set δ : ℝ := frobNorm ΔA with hδ
  have hs2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hδ0 : 0 ≤ δ := frobNorm_nonneg _
  have ha0 : 0 ≤ a := by
    rw [ha]; positivity
  -- X := ΔR · Rinv, upper triangular
  set X : Fin n → Fin n → ℝ := matMul n ΔR Rinv with hX
  have hX_upper : ∀ i j : Fin n, j.val < i.val → X i j = 0 :=
    matMul_upper_upper ΔR Rinv hΔR_upper hRinv_upper
  -- ΔR = X · R  (inverse cancellation)
  have hRinvR_id : matMul n Rinv R = idMatrix n := by
    funext i j
    show (∑ k : Fin n, Rinv i k * R k j) = idMatrix n i j
    rw [hRinvR i j]; rfl
  have hXR : matMul n X R = ΔR := by
    rw [hX, matMul_assoc, hRinvR_id, matMul_id_right]
  -- step 3: t = ‖ΔR‖_F = ‖X·R‖_F ≤ cR ‖X‖_F
  have hstep3 : t ≤ cR * frobNorm X := by
    rw [ht, ← hXR]
    exact frobNorm_matMul_right_le X R cR hcR hopR
  -- step 4: ‖X‖_F ≤ ‖Y‖_F/√2, Y = X + Xᵀ symmetric, X = up(Y)
  set Y : Fin n → Fin n → ℝ := fun i j => X i j + X j i with hY
  have hY_sym : ∀ i j : Fin n, Y i j = Y j i := fun i j => by
    simp only [hY]; ring
  have hX_recover : ∀ i j : Fin n, X i j = upHalf Y i j := fun i j =>
    (upHalf_add_transpose X hX_upper i j).symm
  have hstep4 : frobNorm X ≤ frobNorm Y / Real.sqrt 2 := by
    rw [frobNorm_congr X (upHalf Y) hX_recover]
    exact frobNorm_upHalf_le Y hY_sym
  -- step 5-7: ‖Y‖_F ≤ cinv² ‖M‖_F, M = ΔA - ΔRᵀΔR
  set M : Fin n → Fin n → ℝ :=
    fun p q => ΔA p q - ∑ k : Fin n, ΔR k p * ΔR k q with hM
  have hRinvT_op : opNorm2Le (fun i j => Rinv j i) cinv := hopRinv
  have hY_eq : ∀ i j : Fin n,
      Y i j = matMul n (fun p q => Rinv q p) (matMul n M Rinv) i j := by
    intro i j
    have hsym := cholesky_perturbation_symmetrized
      (fun i j => ∑ k : Fin n, R k i * R k j) ΔA R ΔR Rinv
      (fun i j => rfl) hGram hRRinv i j
    show X i j + X j i = _
    rw [hsym]
    show (∑ p : Fin n, ∑ q : Fin n, Rinv p i *
      (ΔA p q - ∑ k : Fin n, ΔR k p * ΔR k q) * Rinv q j) = _
    unfold matMul
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    show Rinv p i * M p q * Rinv q j = Rinv p i * (M p q * Rinv q j)
    ring
  have hstep567 : frobNorm Y ≤ cinv ^ 2 * frobNorm M := by
    have h1 : frobNorm Y =
        frobNorm (matMul n (fun p q => Rinv q p) (matMul n M Rinv)) :=
      frobNorm_congr Y _ hY_eq
    have h2 : frobNorm (matMul n (fun p q => Rinv q p) (matMul n M Rinv))
        ≤ cinv * frobNorm (matMul n M Rinv) :=
      frobNorm_matMul_left_le (fun p q => Rinv q p) (matMul n M Rinv)
        cinv hcinv hRinvT_op
    have h3 : frobNorm (matMul n M Rinv) ≤ cinv * frobNorm M :=
      frobNorm_matMul_right_le M Rinv cinv hcinv hRinvT_op
    calc frobNorm Y = frobNorm (matMul n (fun p q => Rinv q p)
          (matMul n M Rinv)) := h1
      _ ≤ cinv * frobNorm (matMul n M Rinv) := h2
      _ ≤ cinv * (cinv * frobNorm M) :=
          mul_le_mul_of_nonneg_left h3 hcinv
      _ = cinv ^ 2 * frobNorm M := by ring
  -- step 8: ‖M‖_F ≤ δ + t²
  have hstep8 : frobNorm M ≤ δ + t ^ 2 := by
    set N : Fin n → Fin n → ℝ :=
      matMul n (fun i j => ΔR j i) ΔR with hN
    have htri : frobNorm M ≤ frobNorm ΔA + frobNorm N := by
      have := frobNorm_sub_le ΔA N
      have heq : frobNorm M = frobNorm (fun i j => ΔA i j - N i j) :=
        frobNorm_congr M _ (fun i j => rfl)
      rw [heq]; exact this
    have hN2 : frobNorm N ≤ t ^ 2 := by
      rw [hN, ht]
      exact frobNorm_transpose_mul_self_le ΔR
    calc frobNorm M ≤ frobNorm ΔA + frobNorm N := htri
      _ ≤ δ + t ^ 2 := by rw [hδ]; linarith
  -- assemble the quadratic self-bound t ≤ a(δ + t²)
  have hquad : t ≤ a * (δ + t ^ 2) := by
    have hchain : t ≤ cR * (cinv ^ 2 * frobNorm M / Real.sqrt 2) := by
      calc t ≤ cR * frobNorm X := hstep3
        _ ≤ cR * (frobNorm Y / Real.sqrt 2) :=
            mul_le_mul_of_nonneg_left hstep4 hcR
        _ ≤ cR * (cinv ^ 2 * frobNorm M / Real.sqrt 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hcR
            exact div_le_div_of_nonneg_right hstep567 hs2.le
    have hfM : cinv ^ 2 * frobNorm M ≤ cinv ^ 2 * (δ + t ^ 2) :=
      mul_le_mul_of_nonneg_left hstep8 (by positivity)
    calc t ≤ cR * (cinv ^ 2 * frobNorm M / Real.sqrt 2) := hchain
      _ ≤ cR * (cinv ^ 2 * (δ + t ^ 2) / Real.sqrt 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hcR
          exact div_le_div_of_nonneg_right hfM hs2.le
      _ = a * (δ + t ^ 2) := by rw [ha]; ring
  have hat : a * t < 1 := hsmall
  exact cholesky_perturbation_scalar_endgame a δ t hquad hat

-- ============================================================
-- §10.2  Theorem 10.8: Sun perturbation bound (normwise)
-- ============================================================

/-- **Abstract Cholesky perturbation normwise-bound interface**
    (Higham §10.2, Theorem 10.8, first part).

    If A is SPD with A = R^T R and ΔA is symmetric with ‖A⁻¹ΔA‖₂ < 1,
    then A + ΔA = (R + ΔR)^T(R + ΔR) where:
      frobNormSq(ΔR) ≤ (κ₂(A) / (2 · norm₂(A)))² · frobNormSq(ΔA) + O(‖ΔA‖²)

    We state the first-order bound in squared form to avoid sqrt.
    The condition number κ₂(A) = ‖A‖₂ · ‖A⁻¹‖₂ is taken as a hypothesis.
    The perturbation existence/bound itself is supplied as `hpert`. -/
theorem cholesky_perturbation_normwise (n : ℕ)
    (A R : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (_hChol : CholeskyFactSpec n A R)
    (_hSym_A : ∀ i j : Fin n, A i j = A j i)
    (_hSym_ΔA : ∀ i j : Fin n, ΔA i j = ΔA j i)
    -- Norms and condition number as hypotheses
    (norm2_A : ℝ) (_hnorm2_pos : 0 < norm2_A)
    (κ2_A : ℝ) (_hκ2_pos : 0 < κ2_A)
    -- Perturbation is small enough
    (_hSmall : frobNormSq ΔA < norm2_A ^ 2)
    -- The bound: existence of ΔR with the Frobenius norm bound
    -- This first-order perturbation result follows from implicit function
    -- theorem applied to the map R ↦ R^T R.
    (hpert : ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA) :
    ∃ ΔR : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, j.val < i.val → ΔR i j = 0) ∧
      (∀ i j, ∑ k : Fin n, (R k i + ΔR k i) * (R k j + ΔR k j) = A i j + ΔA i j) ∧
      frobNormSq ΔR ≤ κ2_A ^ 2 / (4 * norm2_A ^ 2) * frobNormSq ΔA :=
  hpert

-- ============================================================
-- §10.2  Theorem 10.8: Sun perturbation bound (componentwise)
-- ============================================================

/-- **Cholesky perturbation componentwise bound** (Higham §10.2, Theorem 10.8, second part).

    Under the conditions of the normwise bound, if ε = ‖(R+ΔR)⁻ᵀ ΔA (R+ΔR)⁻¹‖₂ < 1:
      |ΔR| ≤ triu(|R⁻ᵀ| · |ΔA| · |R⁻¹|) · (1 + O(ε))

    We take the componentwise bound as a hypothesis and express it
    using the upper triangular part and matrix inverses. -/
theorem cholesky_perturbation_componentwise (n : ℕ)
    (R ΔR R_invT R_inv : Fin n → Fin n → ℝ)
    (ΔA : Fin n → Fin n → ℝ)
    (_hChol_R : ∀ i j : Fin n, j.val < i.val → R i j = 0)
    (_hΔR_upper : ∀ i j : Fin n, j.val < i.val → ΔR i j = 0)
    -- R⁻ᵀ and R⁻¹ are the transposes/inverses
    (_hR_invT : IsLeftInverse n (fun i j => R j i) R_invT)
    (_hR_inv : IsRightInverse n R R_inv)
    -- First-order bound
    (α : ℝ) (_hα : 0 ≤ α)
    (hbound : ∀ i j : Fin n, i.val ≤ j.val →
      |ΔR i j| ≤ (1 + α) *
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|) :
    ∀ i j : Fin n, |ΔR i j| ≤ (1 + α) *
      (if i.val ≤ j.val then
        ∑ k₁ : Fin n, |R_invT i k₁| *
          ∑ k₂ : Fin n, |ΔA k₁ k₂| * |R_inv k₂ j|
       else 0) := by
  intro i j
  by_cases hij : i.val ≤ j.val
  · simp [hij]
    exact hbound i j hij
  · simp [show ¬(i.val ≤ j.val) from by omega]
    have hij' : j.val < i.val := by omega
    have hΔR_zero := _hΔR_upper i j hij'
    simp [hΔR_zero]

-- ============================================================
-- §10.2  Sensitivity of leading submatrices
-- ============================================================

/-- **Leading submatrix sensitivity** (Higham §10.2, Remark after Theorem 10.8).

    The Cholesky factor of A_k = A(1:k, 1:k) is R_k = R(1:k, 1:k).
    Since κ₂(A_{k+1}) ≥ κ₂(A_k) by eigenvalue interlacing:
    - If A is ill-conditioned but A_k is well-conditioned,
      then R_k is insensitive to perturbations but later columns
      of R are much more sensitive.

    We state this as a monotonicity property of the condition number
    along the leading submatrix chain. -/
theorem cholesky_cond_monotone
    (κ : ℕ → ℝ)
    (_hκ_mono : ∀ k : ℕ, κ k ≤ κ (k + 1))
    (k₁ k₂ : ℕ) (h : k₁ ≤ k₂) :
    κ k₁ ≤ κ k₂ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simp
  | succ d ih =>
    calc κ k₁ ≤ κ (k₁ + d) := ih (by omega)
      _ ≤ κ (k₁ + d + 1) := _hκ_mono _
      _ = κ (k₁ + (d + 1)) := by ring_nf

-- ============================================================
-- §10.4  Display (10.29): matrices with positive definite symmetric part
-- ============================================================

/-- **PSD-bilinear Cauchy–Schwarz** (Higham §10.4, the SPD step of the
    (10.29) per-stage bound; oracle-provided route): for a symmetric
    positive-semidefinite matrix `H`, the bilinear form obeys
    `(uᵀHv)² ≤ (uᵀHu)(vᵀHv)`.  Proved by the discriminant of the
    nonnegative quadratic `t ↦ (u+tv)ᵀH(u+tv)`. -/
theorem quadForm_bilinear_cauchy_schwarz {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hSym : ∀ i j : Fin n, H i j = H j i)
    (hPSD : ∀ z : Fin n → ℝ, 0 ≤ ∑ i : Fin n, ∑ j : Fin n, z i * H i j * z j)
    (u v : Fin n → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, u i * H i j * v j) ^ 2 ≤
      (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) *
      (∑ i : Fin n, ∑ j : Fin n, v i * H i j * v j) := by
  set Buu := ∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j with hBuu
  set Buv := ∑ i : Fin n, ∑ j : Fin n, u i * H i j * v j with hBuv
  set Bvv := ∑ i : Fin n, ∑ j : Fin n, v i * H i j * v j with hBvv
  -- the cross form is symmetric: ∑∑ v i H i j u j = Buv
  have hsymBil : (∑ i : Fin n, ∑ j : Fin n, v i * H i j * u j) = Buv := by
    rw [hBuv, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hSym j i]; ring
  -- quadratic expansion of the shifted PSD form
  have hexp : ∀ t : ℝ,
      (∑ i : Fin n, ∑ j : Fin n,
        (u i + t * v i) * H i j * (u j + t * v j)) =
      Bvv * (t * t) + 2 * Buv * t + Buu := by
    intro t
    have pt : ∀ i j : Fin n,
        (u i + t * v i) * H i j * (u j + t * v j) =
        u i * H i j * u j + t * (u i * H i j * v j) +
        t * (v i * H i j * u j) + (t * t) * (v i * H i j * v j) := by
      intro i j; ring
    simp_rw [pt, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hBuu, ← hBuv, ← hBvv, hsymBil]
    ring
  have hquad : ∀ t : ℝ, 0 ≤ Bvv * (t * t) + 2 * Buv * t + Buu := by
    intro t
    rw [← hexp t]
    exact hPSD _
  have hdisc := discrim_le_zero (a := Bvv) (b := 2 * Buv) (c := Buu)
    (by intro t; have := hquad t; linarith [hquad t])
  simp only [discrim] at hdisc
  nlinarith [hdisc]

/-- **SPD pivot quadratic-form bound** (Higham §10.4, the basic SPD
    lemma of the (10.29) per-stage bound; oracle route): for `H`
    symmetric with two-sided inverse `Hinv` (also symmetric, PSD),
    `(x_k)² ≤ H_kk · (xᵀ Hinv x)`.  Applying `x = Sᵀe_i` gives
    `s_{ik}²/H_kk ≤ (S Hinv Sᵀ)_ii`. -/
theorem spd_pivot_quadForm_bound {n : ℕ} (H Hinv : Fin n → Fin n → ℝ)
    (hHsym : ∀ i j : Fin n, H i j = H j i)
    (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
    (hHinvPSD : ∀ z : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, z i * Hinv i j * z j)
    (hHHinv : ∀ i k : Fin n,
      (∑ j : Fin n, H i j * Hinv j k) = if i = k then 1 else 0)
    (hHinvH : ∀ i k : Fin n,
      (∑ j : Fin n, Hinv i j * H j k) = if i = k then 1 else 0)
    (k : Fin n) (x : Fin n → ℝ) :
    (x k) ^ 2 ≤ H k k * (∑ i : Fin n, ∑ j : Fin n, x i * Hinv i j * x j) := by
  set u : Fin n → ℝ := fun i => H i k with hu
  have hcs := quadForm_bilinear_cauchy_schwarz Hinv hHinvSym hHinvPSD u x
  -- uᵀ Hinv x = x k, using H·Hinv = I and symmetry
  have hUV : (∑ i : Fin n, ∑ j : Fin n, u i * Hinv i j * x j) = x k := by
    have e1 : (∑ i : Fin n, ∑ j : Fin n, u i * Hinv i j * x j) =
        ∑ j : Fin n, (∑ i : Fin n, H k i * Hinv i j) * x j := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hu, hHsym i k]
    rw [e1, Finset.sum_congr rfl fun j _ => by rw [hHHinv k j]]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, one_mul]
    · intro b _ hb; rw [if_neg (fun h => hb h.symm), zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  -- uᵀ Hinv u = H k k, using Hinv·H = I and symmetry
  have hUU : (∑ i : Fin n, ∑ j : Fin n, u i * Hinv i j * u j) = H k k := by
    have e1 : (∑ i : Fin n, ∑ j : Fin n, u i * Hinv i j * u j) =
        ∑ i : Fin n, H k i * (∑ j : Fin n, Hinv i j * H j k) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hu]; rw [hHsym i k]; ring
    rw [e1, Finset.sum_congr rfl fun i _ => by rw [hHinvH i k]]
    rw [Finset.sum_eq_single k]
    · rw [if_pos rfl, mul_one]
    · intro b _ hb; rw [if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hUV, hUU] at hcs
  exact hcs

/-- **Sherman–Morrison quadratic-form monotonicity, scalar core**
    (Higham §10.4, the algebraic heart of the (10.29) stage Loewner
    monotonicity `Q̂ ⪯ Q₂₂`; oracle consult 4 route, hand-verified).

    After the block-inverse reduction, `yᵀ Q̂ y` equals the
    Sherman–Morrison expansion
    `qww + 2γp + γ²r − (p+γr)²/(1+r)` (rank-one update `Z + uuᵀ` of the
    SPD Schur complement `Z`, with `qww = wᵀZ⁻¹w`, `r = uᵀZ⁻¹u ≥ 0`,
    `p = uᵀZ⁻¹w`), while `yᵀ Q₂₂ y = qww + γ²`.  The exact gap is
    `(γ − p)²/(1+r) ≥ 0`, so the stage form never exceeds the trailing
    block. -/
theorem sherman_morrison_quadForm_scalar_mono
    (qww r p γ : ℝ) (hr : 0 ≤ r) :
    qww + 2 * γ * p + γ ^ 2 * r - (p + γ * r) ^ 2 / (1 + r) ≤
      qww + γ ^ 2 := by
  have h1r : (0:ℝ) < 1 + r := by linarith
  have hgap : (qww + γ ^ 2) -
      (qww + 2 * γ * p + γ ^ 2 * r - (p + γ * r) ^ 2 / (1 + r)) =
      (γ - p) ^ 2 / (1 + r) := by
    field_simp
    ring
  have hnn : 0 ≤ (γ - p) ^ 2 / (1 + r) :=
    div_nonneg (sq_nonneg _) h1r.le
  linarith [hgap, hnn]

/-- **Sherman–Morrison quadratic form, vector level** (Higham §10.4, the
    matrix step of the (10.29) crux `Q̂ ⪯ Q₂₂`; oracle consult 4 route,
    hand-verified).  For symmetric `Z` with a left inverse `Zinv`
    (symmetric), the rank-one update `Ĥ = Z + u uᵀ` with right inverse
    `Ĥinv` satisfies

      `xᵀ Ĥ⁻¹ x = xᵀ Z⁻¹ x − (uᵀ Z⁻¹ x)² / (1 + uᵀ Z⁻¹ u)`.

    Proved through the inverse-action vector `ξ = Ĥ⁻¹ x`:
    `Z ξ = x − (uᵀξ) u`, so `ξ = Z⁻¹ x − s Z⁻¹ u` with `s = (uᵀZ⁻¹x)/(1+r)`;
    no explicit Sherman–Morrison matrix identity is needed. -/
theorem rankOne_update_quadForm_eq {m : ℕ}
    (Z Zinv Hhat Hhatinv : Fin m → Fin m → ℝ) (u x : Fin m → ℝ)
    (hZinvSym : ∀ i j : Fin m, Zinv i j = Zinv j i)
    (hZinv_act : ∀ v : Fin m → ℝ,
      matMulVec m Zinv (matMulVec m Z v) = v)
    (hHhat : ∀ i j : Fin m, Hhat i j = Z i j + u i * u j)
    (hHhatinv_act : matMulVec m Hhat (matMulVec m Hhatinv x) = x)
    (hr1 : (1 : ℝ) + (∑ i : Fin m, u i * matMulVec m Zinv u i) ≠ 0) :
    (∑ i : Fin m, x i * matMulVec m Hhatinv x i) =
      (∑ i : Fin m, x i * matMulVec m Zinv x i) -
        (∑ i : Fin m, u i * matMulVec m Zinv x i) ^ 2 /
        (1 + ∑ i : Fin m, u i * matMulVec m Zinv u i) := by
  set ξ : Fin m → ℝ := matMulVec m Hhatinv x with hξ
  set s : ℝ := ∑ j : Fin m, u j * ξ j with hs
  set a : Fin m → ℝ := matMulVec m Zinv x with ha
  set e : Fin m → ℝ := matMulVec m Zinv u with he
  set p : ℝ := ∑ i : Fin m, u i * a i with hp
  set r : ℝ := ∑ i : Fin m, u i * e i with hr
  -- Z ξ = x − s • u  (pointwise)
  have hZξ : ∀ i : Fin m, matMulVec m Z ξ i = x i - s * u i := by
    intro i
    have hact : matMulVec m Hhat ξ i = x i := by rw [hξ]; exact congrFun hHhatinv_act i
    have hsplit : matMulVec m Hhat ξ i = matMulVec m Z ξ i + u i * s := by
      unfold matMulVec
      rw [hs]
      rw [show (∑ j : Fin m, Hhat i j * ξ j) =
          ∑ j : Fin m, (Z i j + u i * u j) * ξ j from
        Finset.sum_congr rfl fun j _ => by rw [hHhat i j]]
      rw [show (∑ j : Fin m, (Z i j + u i * u j) * ξ j) =
          (∑ j : Fin m, Z i j * ξ j) + u i * (∑ j : Fin m, u j * ξ j) from by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring]
    rw [hsplit] at hact
    linarith
  -- ξ = a − s • e  (apply Zinv, using Zinv ∘ Z = id)
  have hξ_eq : ∀ i : Fin m, ξ i = a i - s * e i := by
    have hZinvξ := hZinv_act ξ
    have hlin : matMulVec m Zinv (matMulVec m Z ξ) =
        fun i => a i - s * e i := by
      funext i
      have : matMulVec m Z ξ = fun i => x i - s * u i := funext hZξ
      rw [this]
      unfold matMulVec
      rw [ha, he]
      unfold matMulVec
      rw [show (∑ j : Fin m, Zinv i j * (x j - s * u j)) =
          (∑ j : Fin m, Zinv i j * x j) - s * (∑ j : Fin m, Zinv i j * u j) from by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring]
    rw [hZinvξ] at hlin
    exact congrFun hlin
  have h1r : (1 : ℝ) + r ≠ 0 := by rw [hr] at hr1 ⊢; exact hr1
  -- s (1 + r) = p
  have hs_eq : s * (1 + r) = p := by
    have hstep : s = p - s * r := by
      conv_lhs => rw [hs]
      calc (∑ j : Fin m, u j * ξ j)
          = ∑ j : Fin m, (u j * a j - s * (u j * e j)) :=
            Finset.sum_congr rfl fun j _ => by rw [hξ_eq j]; ring
        _ = (∑ j : Fin m, u j * a j) - s * ∑ j : Fin m, u j * e j := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        _ = p - s * r := by rw [← hp, ← hr]
    nlinarith [hstep]
  -- x·e = p  (symmetry of Zinv)
  have hxe : (∑ i : Fin m, x i * e i) = p := by
    have lhs : (∑ i : Fin m, x i * e i) =
        ∑ i : Fin m, ∑ j : Fin m, x i * Zinv i j * u j := by
      rw [he]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold matMulVec
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have rhs : p = ∑ i : Fin m, ∑ j : Fin m, u i * Zinv i j * x j := by
      rw [hp, ha]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold matMulVec
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hZinvSym j i]; ring
  -- assemble: xᵀĤ⁻¹x = xᵀa − s(xᵀe) = qxx − s·p = qxx − p²/(1+r)
  have hLHS : (∑ i : Fin m, x i * ξ i) =
      (∑ i : Fin m, x i * a i) - s * (∑ i : Fin m, x i * e i) := by
    rw [show (∑ i : Fin m, x i * a i) - s * (∑ i : Fin m, x i * e i) =
        ∑ i : Fin m, (x i * a i - s * (x i * e i)) from by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]]
    exact Finset.sum_congr rfl fun i _ => by rw [hξ_eq i]; ring
  rw [hξ] at hLHS
  rw [hLHS, hxe, ha]
  -- s·p = p²/(1+r)
  have hs_val : s = p / (1 + r) := by
    rw [eq_div_iff h1r]; exact hs_eq
  rw [hs_val, hr]; ring

/-- **Rank-one-update auxiliary inequality** (Higham §10.4, the complete
    abstract heart of the (10.29) stage Loewner monotonicity `Q̂ ⪯ Q₂₂`;
    oracle consult 4, hand-verified): for symmetric `Z` with symmetric
    left inverse `Zinv` that is PSD on `u`, the rank-one update
    `Ĥ = Z + u uᵀ` with right inverse `Ĥinv` satisfies

      `(w + γu)ᵀ Ĥ⁻¹ (w + γu) ≤ wᵀ Z⁻¹ w + γ²`.

    Combines the vector Sherman–Morrison identity with the scalar
    monotonicity core after expanding both `Z⁻¹` bilinear forms at
    `x = w + γu`. -/
theorem rankOne_update_auxiliary_le {m : ℕ}
    (Z Zinv Hhat Hhatinv : Fin m → Fin m → ℝ) (u w : Fin m → ℝ) (γ : ℝ)
    (hZinvSym : ∀ i j : Fin m, Zinv i j = Zinv j i)
    (hr_nonneg : 0 ≤ ∑ i : Fin m, u i * matMulVec m Zinv u i)
    (hZinv_act : ∀ v : Fin m → ℝ,
      matMulVec m Zinv (matMulVec m Z v) = v)
    (hHhat : ∀ i j : Fin m, Hhat i j = Z i j + u i * u j)
    (hHhatinv_act : matMulVec m Hhat
      (matMulVec m Hhatinv (fun i => w i + γ * u i)) =
      (fun i => w i + γ * u i)) :
    (∑ i : Fin m, (w i + γ * u i) *
        matMulVec m Hhatinv (fun i => w i + γ * u i) i) ≤
      (∑ i : Fin m, w i * matMulVec m Zinv w i) + γ ^ 2 := by
  set x : Fin m → ℝ := fun i => w i + γ * u i with hx
  set r : ℝ := ∑ i : Fin m, u i * matMulVec m Zinv u i with hr
  set qww : ℝ := ∑ i : Fin m, w i * matMulVec m Zinv w i with hqww
  set p0 : ℝ := ∑ i : Fin m, u i * matMulVec m Zinv w i with hp0
  have h1r : (1 : ℝ) + r ≠ 0 := by positivity
  -- Zinv action on x splits linearly
  have hZinvx : ∀ i : Fin m,
      matMulVec m Zinv x i =
      matMulVec m Zinv w i + γ * matMulVec m Zinv u i := by
    intro i; unfold matMulVec
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by rw [hx]; ring
  -- symmetry: ∑ w (Zinv u) = ∑ u (Zinv w) = p0
  have hsym_cross : (∑ i : Fin m, w i * matMulVec m Zinv u i) = p0 := by
    rw [hp0]
    have lhs : (∑ i : Fin m, w i * matMulVec m Zinv u i) =
        ∑ i : Fin m, ∑ j : Fin m, w i * Zinv i j * u j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold matMulVec; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have rhs : (∑ i : Fin m, u i * matMulVec m Zinv w i) =
        ∑ i : Fin m, ∑ j : Fin m, u i * Zinv i j * w j := by
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold matMulVec; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [lhs, rhs, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hZinvSym j i]; ring
  -- x·Zinv·x = qww + 2γ p0 + γ² r
  have hxZx : (∑ i : Fin m, x i * matMulVec m Zinv x i) =
      qww + 2 * γ * p0 + γ ^ 2 * r := by
    have hpt : (∑ i : Fin m, x i * matMulVec m Zinv x i) =
        ∑ i : Fin m, (w i * matMulVec m Zinv w i +
          γ * (w i * matMulVec m Zinv u i) +
          γ * (u i * matMulVec m Zinv w i) +
          γ ^ 2 * (u i * matMulVec m Zinv u i)) :=
      Finset.sum_congr rfl fun i _ => by rw [hZinvx i, hx]; ring
    rw [hpt, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hsym_cross, ← hqww, ← hr, ← hp0]
    ring
  -- u·Zinv·x = p0 + γ r
  have huZx : (∑ i : Fin m, u i * matMulVec m Zinv x i) = p0 + γ * r := by
    have hpt : (∑ i : Fin m, u i * matMulVec m Zinv x i) =
        ∑ i : Fin m, (u i * matMulVec m Zinv w i +
          γ * (u i * matMulVec m Zinv u i)) :=
      Finset.sum_congr rfl fun i _ => by rw [hZinvx i]; ring
    rw [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, ← hp0, ← hr]
  -- apply the vector Sherman–Morrison identity, then the scalar core
  have hid := rankOne_update_quadForm_eq Z Zinv Hhat Hhatinv u x
    hZinvSym hZinv_act hHhat hHhatinv_act (by rw [← hr]; exact h1r)
  rw [hid, hxZx, huZx, ← hr]
  exact sherman_morrison_quadForm_scalar_mono qww r p0 γ hr_nonneg

/-- **2×2 block-inverse quadratic form** (Higham §10.4, the `Q₂₂` side of
    the (10.29) crux; oracle consult 4, hand-verified): for a symmetric
    positive-definite `(1+m)`-block matrix
    `H = [[α, fᵀ],[f, G]]` with Schur complement `Z = G − ffᵀ/α`
    (`Zinv` its inverse), completing the square gives

      `[β; v]ᵀ H⁻¹ [β; v] = β²/α + (v − (β/α)f)ᵀ Z⁻¹ (v − (β/α)f)`.

    Proved through the inverse-action vector `ξ = H⁻¹[β;v]`: its tail
    solves `Z ξ_tail = v − (β/α)f`. -/
theorem block_quadForm_schur_eq {m : ℕ} (α : ℝ) (hα : α ≠ 0)
    (f : Fin m → ℝ) (G : Fin m → Fin m → ℝ)
    (H Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Z Zinv : Fin m → Fin m → ℝ)
    (hH00 : H 0 0 = α)
    (hH0s : ∀ j : Fin m, H 0 j.succ = f j)
    (hHs0 : ∀ i : Fin m, H i.succ 0 = f i)
    (hHss : ∀ i j : Fin m, H i.succ j.succ = G i j)
    (hZ : ∀ i j : Fin m, Z i j = G i j - f i * f j / α)
    (hZinv_act : ∀ vv : Fin m → ℝ, matMulVec m Zinv (matMulVec m Z vv) = vv)
    (β : ℝ) (v : Fin m → ℝ)
    (hHinv_act : matMulVec (m + 1) H
      (matMulVec (m + 1) Hinv (Fin.cons β v : Fin (m + 1) → ℝ)) =
      (Fin.cons β v : Fin (m + 1) → ℝ)) :
    (∑ i : Fin (m + 1),
        (Fin.cons β v : Fin (m + 1) → ℝ) i *
        matMulVec (m + 1) Hinv (Fin.cons β v : Fin (m + 1) → ℝ) i) =
      β ^ 2 / α +
        ∑ i : Fin m, (v i - β / α * f i) *
          matMulVec m Zinv (fun j => v j - β / α * f j) i := by
  set y : Fin (m + 1) → ℝ := (Fin.cons β v : Fin (m + 1) → ℝ) with hy
  set ξ : Fin (m + 1) → ℝ := matMulVec (m + 1) Hinv y with hξ
  set ξt : Fin m → ℝ := fun i => ξ i.succ with hξt
  set F : ℝ := ∑ j : Fin m, f j * ξt j with hF
  -- row 0: α·ξ₀ + ∑ f·ξt = β
  have hrow0 : α * ξ 0 + F = β := by
    have h0 : matMulVec (m + 1) H ξ 0 = β := by
      rw [hξ]; rw [hHinv_act]; rw [hy, Fin.cons_zero]
    rw [show matMulVec (m + 1) H ξ 0 = α * ξ 0 + F from by
      unfold matMulVec
      rw [Fin.sum_univ_succ, hH00, hF]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hH0s j, hξt]] at h0
    exact h0
  -- rows i.succ: f i·ξ₀ + (G·ξt) i = v i
  have hrowi : ∀ i : Fin m,
      f i * ξ 0 + matMulVec m G ξt i = v i := by
    intro i
    have hi : matMulVec (m + 1) H ξ i.succ = v i := by
      rw [hξ]; rw [hHinv_act]; rw [hy, Fin.cons_succ]
    rw [show matMulVec (m + 1) H ξ i.succ =
        f i * ξ 0 + matMulVec m G ξt i from by
      unfold matMulVec
      rw [Fin.sum_univ_succ, hHs0 i]
      congr 1
      exact Finset.sum_congr rfl fun j _ => by rw [hHss i j, hξt]] at hi
    exact hi
  -- ξ₀ = (β − F)/α
  have hξ0 : ξ 0 = (β - F) / α := by
    rw [eq_div_iff hα]; linarith [hrow0]
  -- Z·ξt = v − (β/α)·f  (pointwise)
  have hZξt : ∀ i : Fin m,
      matMulVec m Z ξt i = v i - β / α * f i := by
    intro i
    have hGi := hrowi i
    have hexp : matMulVec m Z ξt i =
        matMulVec m G ξt i - f i / α * F := by
      unfold matMulVec
      rw [show (∑ j : Fin m, Z i j * ξt j) =
          ∑ j : Fin m, (G i j * ξt j - f i / α * (f j * ξt j)) from
        Finset.sum_congr rfl fun j _ => by rw [hZ i j]; ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hF]
    rw [hexp]
    -- matMulVec G ξt i = v i − f i ξ0 = v i − f i (β−F)/α
    have hG_i : matMulVec m G ξt i = v i - f i * ξ 0 := by linarith [hGi]
    rw [hG_i, hξ0]
    field_simp
    ring
  -- ξt = Zinv (v − (β/α)f)
  have hξt_eq : ξt = matMulVec m Zinv (fun j => v j - β / α * f j) := by
    have := hZinv_act ξt
    rw [show matMulVec m Z ξt = (fun j => v j - β / α * f j) from
      funext hZξt] at this
    exact this.symm
  -- assemble the quadratic form
  have hQF : (∑ i : Fin (m + 1), y i * ξ i) =
      β * ξ 0 + ∑ i : Fin m, v i * ξt i := by
    rw [Fin.sum_univ_succ, hy]
    simp only [Fin.cons_zero, Fin.cons_succ, hξt]
  -- the algebraic identity β·ξ₀ + ∑ v·ξt = β²/α + ∑ (v − (β/α)f)·ξt
  have hfinal : β * ξ 0 + ∑ i : Fin m, v i * ξt i =
      β ^ 2 / α + ∑ i : Fin m, (v i - β / α * f i) * ξt i := by
    rw [hξ0]
    have hexpand : (∑ i : Fin m, (v i - β / α * f i) * ξt i) =
        (∑ i : Fin m, v i * ξt i) - β / α * F := by
      rw [hF, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hexpand]; field_simp; ring
  rw [hQF, hfinal, hξt_eq]

/-- **Gram-conjugation quadratic form** (Higham §10.4, the tool that
    presents a stage Gram `GᵀMG` as a matrix so `schur_gram_stage_le`
    becomes a Loewner statement): `yᵀ(GᵀMG)y = (Gy)ᵀM(Gy)`.  Proved
    through `matMulVec_matMul` (so only a single sum-swap is needed). -/
theorem quadForm_gram_conj {n : ℕ} (M G : Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) :
    (∑ i : Fin n, y i *
        matMulVec n (matMul n (matMul n (fun a b => G b a) M) G) y i) =
      ∑ p : Fin n,
        matMulVec n G y p * matMulVec n M (matMulVec n G y) p := by
  have hQy : ∀ i : Fin n,
      matMulVec n (matMul n (matMul n (fun a b => G b a) M) G) y i =
      ∑ p : Fin n, G p i * matMulVec n M (matMulVec n G y) p := by
    intro i
    rw [matMulVec_matMul n (matMul n (fun a b => G b a) M) G y i,
      matMulVec_matMul n (fun a b => G b a) M (matMulVec n G y) i]
    rfl
  simp_rw [hQy, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show (∑ i : Fin n, y i * (G p i *
        matMulVec n M (matMulVec n G y) p)) =
      (∑ i : Fin n, y i * G p i) *
        matMulVec n M (matMulVec n G y) p from by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring]
  congr 1
  unfold matMulVec
  exact Finset.sum_congr rfl fun i _ => by ring

open Matrix in
/-- **SPD matrices have a symmetric two-sided inverse** (Higham §10.4,
    the existence foundation for the stage Gram `Q(S) = SᵀH(S)⁻¹S`):
    a symmetric positive-definite `H` (repo `IsSymPosDef`) is invertible
    (trivial kernel), and its inverse is symmetric. -/
theorem spd_inverse_exists {n : ℕ} (H : Fin n → Fin n → ℝ)
    (hH : IsSymPosDef n H) :
    ∃ Hinv : Fin n → Fin n → ℝ,
      (∀ i j : Fin n, Hinv i j = Hinv j i) ∧
      IsRightInverse n H Hinv ∧ IsLeftInverse n H Hinv := by
  classical
  set M : Matrix (Fin n) (Fin n) ℝ := Matrix.of H with hM
  have hMij : ∀ i j : Fin n, M i j = H i j := fun i j => rfl
  -- trivial kernel: M.mulVec u = 0 → u = 0
  have hker : ∀ u : Fin n → ℝ, M.mulVec u = 0 → u = 0 := by
    intro u hu
    by_contra hne
    have hex : ∃ i, u i ≠ 0 := by
      by_contra h; push_neg at h; exact hne (funext h)
    have hpos := hH.2 u hex
    have hrow : ∀ i : Fin n, (∑ j : Fin n, H i j * u j) = 0 := by
      intro i
      have hi := congrFun hu i
      simpa [Matrix.mulVec, dotProduct, hMij] using hi
    have hzero : (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) = 0 := by
      rw [show (∑ i : Fin n, ∑ j : Fin n, u i * H i j * u j) =
          ∑ i : Fin n, u i * (∑ j : Fin n, H i j * u j) from
        Finset.sum_congr rfl fun i _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring]
      exact Finset.sum_eq_zero fun i _ => by rw [hrow i]; ring
    linarith
  have hunit : IsUnit M := by
    rw [← Matrix.mulVec_injective_iff_isUnit]
    intro v w hvw
    have hz : M.mulVec (v - w) = 0 := by
      rw [Matrix.mulVec_sub, hvw, sub_self]
    exact sub_eq_zero.mp (hker _ hz)
  have hdet : IsUnit M.det := M.isUnit_iff_isUnit_det.mp hunit
  haveI : Invertible M := M.invertibleOfIsUnitDet hdet
  have hMsym : Mᵀ = M := by
    funext i j; rw [Matrix.transpose_apply, hMij, hMij]; exact (hH.1 j i)
  refine ⟨fun i j => M⁻¹ i j, ?_, ?_, ?_⟩
  · intro i j
    have h2 : M⁻¹ᵀ = M⁻¹ := by rw [Matrix.transpose_nonsing_inv, hMsym]
    have h := congrFun (congrFun h2 j) i
    rw [Matrix.transpose_apply] at h
    exact h
  · intro i j
    have hmul := Matrix.mul_nonsing_inv M hdet
    have h := congrFun (congrFun hmul i) j
    simp only [Matrix.mul_apply, Matrix.one_apply, hMij] at h
    exact h
  · intro i j
    have hmul := Matrix.nonsing_inv_mul M hdet
    have h := congrFun (congrFun hmul i) j
    simp only [Matrix.mul_apply, Matrix.one_apply, hMij] at h
    exact h

/-- **Conjugated Gram is symmetric** (Higham §10.4): for symmetric `M`,
    the stage Gram `GᵀMG` is symmetric — needed so `finiteMaxEigenvalue`
    applies to the stage matrices. -/
theorem gram_conj_isSymm {n : ℕ} (M G : Fin n → Fin n → ℝ)
    (hM : ∀ i j : Fin n, M i j = M j i) :
    ∀ i j : Fin n,
      matMul n (matMul n (fun a b => G b a) M) G i j =
      matMul n (matMul n (fun a b => G b a) M) G j i := by
  have hMT : matTranspose M = M := by
    funext i j; exact (hM j i)
  have hGT : (fun a b => G b a) = matTranspose G := by funext a b; rfl
  have hGTT : matTranspose (fun a b : Fin n => G b a) = G := by
    funext i j; rfl
  have hkey : matTranspose (matMul n (matMul n (fun a b => G b a) M) G) =
      matMul n (matMul n (fun a b => G b a) M) G := by
    rw [matTranspose_matMul, matTranspose_matMul, hGTT, hMT, ← matMul_assoc,
      ← hGT]
  intro i j
  have h := congrFun (congrFun hkey i) j
  simp only [matTranspose] at h
  exact h.symm

/-- **Trailing-block quadratic form** (Higham §10.4, ties the (10.29)
    stage bound's RHS to the trailing block `Q₂₂` of the stage Gram):
    padding a vector with a leading zero selects the trailing principal
    block, `(0,y)ᵀ Q (0,y) = yᵀ Q₂₂ y` where `Q₂₂ i j = Q i.succ j.succ`. -/
theorem trailing_block_quadForm {n : ℕ}
    (Q : Fin (n + 1) → Fin (n + 1) → ℝ) (y : Fin n → ℝ) :
    (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) i * Q i j * (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) j) =
      ∑ i : Fin n, ∑ j : Fin n, y i * Q i.succ j.succ * y j := by
  rw [Fin.sum_univ_succ]
  have hrow0 : (∑ j : Fin (n + 1),
      (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) 0 * Q 0 j * (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) j) = 0 := by
    simp only [Fin.cons_zero, zero_mul, Finset.sum_const_zero]
  rw [hrow0, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_succ]
  have hcol0 : (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) i.succ * Q i.succ 0 *
      (Fin.cons (0 : ℝ) y : Fin (n + 1) → ℝ) 0 = 0 := by
    simp only [Fin.cons_zero, mul_zero]
  rw [hcol0, zero_add]
  exact Finset.sum_congr rfl fun j _ => by
    simp only [Fin.cons_succ]

/-- **Stage Loewner monotonicity `Q̂ ⪯ Q₂₂`, quadratic-form level**
    (Higham §10.4, the (10.29) crux, assembled; oracle consult 4).
    For a symmetric PD `(1+m)`-block `H = [[α, fᵀ],[f, G]]` with Schur
    complement `Z = G − ffᵀ/α`, skew data `k`, computed Schur complement
    action `Ŝy = v − (β/α)(f − k)` and its symmetric-part rank-one update
    `Ĥ = Z + kkᵀ/α`, the stage Gram form never exceeds the trailing-block
    Gram form:

      `(Ŝy)ᵀ Ĥ⁻¹ (Ŝy) ≤ [β; v]ᵀ H⁻¹ [β; v]`.

    Combines `block_quadForm_schur_eq` (`= β²/α + wᵀZ⁻¹w`) with
    `rankOne_update_auxiliary_le` (`≤ wᵀZ⁻¹w + γ²`, `γ² = β²/α`), setting
    `u = k/√α`, `γ = β/√α` so `uuᵀ = kkᵀ/α` and `Ŝy = w + γu`. -/
theorem schur_gram_stage_le {m : ℕ} (α : ℝ) (hα : 0 < α)
    (f k : Fin m → ℝ) (G : Fin m → Fin m → ℝ)
    (H Hinv : Fin (m + 1) → Fin (m + 1) → ℝ)
    (Z Zinv Hhat Hhatinv : Fin m → Fin m → ℝ)
    (hH00 : H 0 0 = α)
    (hH0s : ∀ j : Fin m, H 0 j.succ = f j)
    (hHs0 : ∀ i : Fin m, H i.succ 0 = f i)
    (hHss : ∀ i j : Fin m, H i.succ j.succ = G i j)
    (hZ : ∀ i j : Fin m, Z i j = G i j - f i * f j / α)
    (hZinvSym : ∀ i j : Fin m, Zinv i j = Zinv j i)
    (hZinv_act : ∀ vv : Fin m → ℝ, matMulVec m Zinv (matMulVec m Z vv) = vv)
    (hZinv_psd_k : 0 ≤ ∑ i : Fin m, (k i / Real.sqrt α) *
      matMulVec m Zinv (fun j => k j / Real.sqrt α) i)
    (hHhat : ∀ i j : Fin m,
      Hhat i j = Z i j + (k i / Real.sqrt α) * (k j / Real.sqrt α))
    (β : ℝ) (v : Fin m → ℝ)
    (hHinv_act : matMulVec (m + 1) H
      (matMulVec (m + 1) Hinv (Fin.cons β v : Fin (m + 1) → ℝ)) =
      (Fin.cons β v : Fin (m + 1) → ℝ))
    (hHhatinv_act : matMulVec m Hhat
      (matMulVec m Hhatinv
        (fun i => (v i - β / α * f i) + β / Real.sqrt α *
          (k i / Real.sqrt α))) =
      (fun i => (v i - β / α * f i) + β / Real.sqrt α *
        (k i / Real.sqrt α))) :
    (∑ i : Fin m, (v i - β / α * (f i - k i)) *
        matMulVec m Hhatinv
          (fun j => v j - β / α * (f j - k j)) i) ≤
      (∑ i : Fin (m + 1),
        (Fin.cons β v : Fin (m + 1) → ℝ) i *
        matMulVec (m + 1) Hinv (Fin.cons β v : Fin (m + 1) → ℝ) i) := by
  set u : Fin m → ℝ := fun i => k i / Real.sqrt α with hu
  set γ : ℝ := β / Real.sqrt α with hγ
  set w : Fin m → ℝ := fun i => v i - β / α * f i with hw
  have hsqrtα : Real.sqrt α * Real.sqrt α = α := Real.mul_self_sqrt hα.le
  have hsqrtα_ne : Real.sqrt α ≠ 0 := by positivity
  -- Ŝy = w + γ u (pointwise and as functions)
  have hŜy_pt : ∀ i : Fin m,
      v i - β / α * (f i - k i) = w i + γ * u i := by
    intro i
    simp only [hw, hu, hγ]
    rw [div_mul_div_comm, hsqrtα]
    ring
  have hŜy : (fun i => v i - β / α * (f i - k i)) =
      (fun i => w i + γ * u i) := funext hŜy_pt
  -- γ² = β²/α
  have hγ2 : γ ^ 2 = β ^ 2 / α := by
    rw [hγ, div_pow, Real.sq_sqrt hα.le]
  -- block-inverse form of the trailing quadratic form
  have hblock := block_quadForm_schur_eq α hα.ne' f G H Hinv Z Zinv
    hH00 hH0s hHs0 hHss hZ hZinv_act β v hHinv_act
  -- auxiliary inequality on the stage form
  have haux := rankOne_update_auxiliary_le Z Zinv Hhat Hhatinv u w γ
    hZinvSym hZinv_psd_k hZinv_act hHhat hHhatinv_act
  -- rewrite the goal's stage form into the (w + γu) shape
  have hLHSeq : (∑ i : Fin m, (v i - β / α * (f i - k i)) *
        matMulVec m Hhatinv (fun j => v j - β / α * (f j - k j)) i) =
      ∑ i : Fin m, (w i + γ * u i) *
        matMulVec m Hhatinv (fun j => w j + γ * u j) i := by
    rw [hŜy]
    exact Finset.sum_congr rfl fun i _ => by rw [hŜy_pt i]
  rw [hLHSeq]
  refine le_trans haux ?_
  rw [hblock, hγ2]
  have hww : (∑ i : Fin m, w i * matMulVec m Zinv w i) =
      ∑ i : Fin m, (v i - β / α * f i) *
        matMulVec m Zinv (fun j => v j - β / α * f j) i := rfl
  linarith [hww]

/-- **Scalar product step** (Higham §10.4, (10.29) per-stage): from two
    pivot bounds `p² ≤ h·a`, `q² ≤ h·b` with `h > 0` and `a, b ≥ 0`,
    `|p·q|/h ≤ √(a·b)`.  Combines the row and column instances of
    `spd_pivot_quadForm_bound` into the multiplier-product bound. -/
theorem pivot_product_le_sqrt (p q h a b : ℝ)
    (hh : 0 < h) (ha : 0 ≤ a) (_hb : 0 ≤ b)
    (hp : p ^ 2 ≤ h * a) (hq : q ^ 2 ≤ h * b) :
    |p * q| / h ≤ Real.sqrt (a * b) := by
  have hpabs : |p| ≤ Real.sqrt (h * a) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hp
  have hqabs : |q| ≤ Real.sqrt (h * b) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hq
  have hprod : |p * q| ≤ Real.sqrt (h * a) * Real.sqrt (h * b) := by
    rw [abs_mul]
    exact mul_le_mul hpabs hqabs (abs_nonneg _) (Real.sqrt_nonneg _)
  have hsplit : Real.sqrt (h * a) * Real.sqrt (h * b) =
      h * Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ h * a) (h * b)]
    rw [show (h * a) * (h * b) = h ^ 2 * (a * b) by ring]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ h ^ 2) (a * b)]
    rw [Real.sqrt_sq hh.le]
  rw [div_le_iff₀ hh]
  calc |p * q| ≤ Real.sqrt (h * a) * Real.sqrt (h * b) := hprod
    _ = h * Real.sqrt (a * b) := hsplit
    _ = Real.sqrt (a * b) * h := by ring

/-- **Diagonal entry ≤ operator-2-norm certificate** (Higham §10.4,
    (10.29) per-stage RHS): if `opNorm2Le Q c` then every diagonal entry
    `Q_ii ≤ c` — the i-th column of `Q` has 2-norm at most `c`, and
    `Q_ii` is one of its components. -/
theorem diag_le_opNorm2Le {n : ℕ} (Q : Fin n → Fin n → ℝ) (c : ℝ)
    (hQ : opNorm2Le Q c) (i : Fin n) : Q i i ≤ c := by
  set e : Fin n → ℝ := fun j => if j = i then (1:ℝ) else 0 with he
  have hmv : matMulVec n Q e = fun p => Q p i := by
    funext p
    unfold matMulVec
    rw [Finset.sum_eq_single i]
    · rw [he]; simp
    · intro b _ hb; rw [he]; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hne : vecNorm2 e = 1 := by
    unfold vecNorm2
    have hsq : vecNorm2Sq e = 1 := by
      unfold vecNorm2Sq
      rw [Finset.sum_eq_single i]
      · rw [he]; simp
      · intro b _ hb; rw [he]; simp [hb]
      · intro h; exact absurd (Finset.mem_univ i) h
    rw [hsq, Real.sqrt_one]
  have hb := hQ e
  rw [hmv, hne, mul_one] at hb
  have hcomp : (Q i i) ^ 2 ≤ vecNorm2Sq (fun p => Q p i) := by
    unfold vecNorm2Sq
    exact Finset.single_le_sum (f := fun p => (Q p i) ^ 2)
      (fun p _ => sq_nonneg _) (Finset.mem_univ i)
  have hqii_abs : |Q i i| ≤ vecNorm2 (fun p => Q p i) := by
    rw [← Real.sqrt_sq_eq_abs]
    calc Real.sqrt ((Q i i) ^ 2)
        ≤ Real.sqrt (vecNorm2Sq (fun p => Q p i)) := Real.sqrt_le_sqrt hcomp
      _ = vecNorm2 (fun p => Q p i) := rfl
  calc Q i i ≤ |Q i i| := le_abs_self _
    _ ≤ vecNorm2 (fun p => Q p i) := hqii_abs
    _ ≤ c := hb

/-- **√(diagonal product) ≤ operator-2-norm** (Higham §10.4, the (10.29)
    per-stage bound RHS): for `opNorm2Le Q c` with nonnegative diagonal,
    `√(Q_ii Q_jj) ≤ c`.  Combined with `pivot_product_le_sqrt` this gives
    `|s_i1 s_1j|/h_11 ≤ ‖Q(S)‖₂`. -/
theorem sqrt_diag_prod_le_opNorm2Le {n : ℕ} (Q : Fin n → Fin n → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hQ : opNorm2Le Q c)
    (hdiag_nonneg : ∀ i : Fin n, 0 ≤ Q i i) (i j : Fin n) :
    Real.sqrt (Q i i * Q j j) ≤ c := by
  have hi := diag_le_opNorm2Le Q c hQ i
  have hj := diag_le_opNorm2Le Q c hQ j
  calc Real.sqrt (Q i i * Q j j)
      ≤ Real.sqrt (c * c) :=
        Real.sqrt_le_sqrt (mul_le_mul hi hj (hdiag_nonneg j) hc)
    _ = c := by rw [← sq, Real.sqrt_sq hc]

/-- **Per-stage multiplier-product bound** (Higham §10.4, the assembled
    (10.29) per-stage inequality): for a GE stage matrix `S` with SPD
    symmetric part `H` (two-sided symmetric PSD inverse `Hinv`) and pivot
    `H_kk > 0`, if the row/column quadratic forms of `S` under `Hinv`
    coincide with the diagonal of a PSD matrix `Q` carrying `opNorm2Le Q c`,
    the multiplier product obeys `|S_ik · S_kj| / H_kk ≤ c`.

    (`Q = S Hinv Sᵀ = Sᵀ Hinv S = H + Kᵀ Hinv K`; the `hrow`/`hcol`
    hypotheses record the two Gram-diagonal identifications, discharged
    from `symPart_skew_inverse_identity` at instantiation.) -/
theorem stage_multiplier_product_le {n : ℕ}
    (H Hinv S Q : Fin n → Fin n → ℝ) (c : ℝ)
    (hHsym : ∀ i j : Fin n, H i j = H j i)
    (hHinvSym : ∀ i j : Fin n, Hinv i j = Hinv j i)
    (hHinvPSD : ∀ z : Fin n → ℝ,
      0 ≤ ∑ i : Fin n, ∑ j : Fin n, z i * Hinv i j * z j)
    (hHHinv : ∀ i k : Fin n,
      (∑ j : Fin n, H i j * Hinv j k) = if i = k then 1 else 0)
    (hHinvH : ∀ i k : Fin n,
      (∑ j : Fin n, Hinv i j * H j k) = if i = k then 1 else 0)
    (k : Fin n) (hk : 0 < H k k)
    (hrow : ∀ i : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, S i p * Hinv p q * S i q) = Q i i)
    (hcol : ∀ j : Fin n,
      (∑ p : Fin n, ∑ q : Fin n, S p j * Hinv p q * S q j) = Q j j)
    (hc : 0 ≤ c) (hQ : opNorm2Le Q c) (hQd : ∀ i : Fin n, 0 ≤ Q i i)
    (i j : Fin n) :
    |S i k * S k j| / H k k ≤ c := by
  have hp : (S i k) ^ 2 ≤ H k k * Q i i := by
    have h := spd_pivot_quadForm_bound H Hinv hHsym hHinvSym hHinvPSD
      hHHinv hHinvH k (fun m => S i m)
    rw [hrow i] at h
    exact h
  have hq : (S k j) ^ 2 ≤ H k k * Q j j := by
    have h := spd_pivot_quadForm_bound H Hinv hHsym hHinvSym hHinvPSD
      hHHinv hHinvH k (fun m => S m j)
    rw [hcol j] at h
    exact h
  have hpp := pivot_product_le_sqrt (S i k) (S k j) (H k k)
    (Q i i) (Q j j) hk (hQd i) (hQd j) hp hq
  exact le_trans hpp (sqrt_diag_prod_le_opNorm2Le Q c hc hQ hQd i j)

open Matrix in
/-- **The (10.29) core identity** (Higham §10.4, p. 208; proof route from
    the logged oracle consultation, Golub–Van Loan 1979):
    `Aᵀ A_S⁻¹ A = A_S + A_Kᵀ A_S⁻¹ A_K`, for any splitting `A = A_S + A_K`
    with `A_S` symmetric (`A_Sᵀ = A_S`), `A_K` skew (`A_Kᵀ = −A_K`), and
    `A_S⁻¹` a two-sided inverse of `A_S`.  This is the matrix whose
    operator norm bounds the unpivoted-LU growth in display (10.29). -/
theorem symPart_skew_inverse_identity {n : ℕ}
    (Amat AS AK ASinv : Matrix (Fin n) (Fin n) ℝ)
    (hA : Amat = AS + AK)
    (hAS_sym : ASᵀ = AS)
    (hAK_skew : AKᵀ = -AK)
    (hinv1 : AS * ASinv = 1)
    (hinv2 : ASinv * AS = 1) :
    Amatᵀ * ASinv * Amat = AS + AKᵀ * ASinv * AK := by
  have hAT : Amatᵀ = AS - AK := by
    rw [hA, Matrix.transpose_add, hAS_sym, hAK_skew]; abel
  rw [hAT, hA]
  -- expand the noncommutative product, treating AS, AK, ASinv as atoms
  have hexp : (AS - AK) * ASinv * (AS + AK) =
      (AS * ASinv) * AS + (AS * ASinv) * AK
        - AK * (ASinv * AS) - AK * ASinv * AK := by
    noncomm_ring
  rw [hexp, hinv1, hinv2, Matrix.one_mul, Matrix.mul_one]
  -- now: AS + AK - AK - AK * ASinv * AK = AS + AKᵀ * ASinv * AK
  rw [hAK_skew]
  noncomm_ring

end NumStability
