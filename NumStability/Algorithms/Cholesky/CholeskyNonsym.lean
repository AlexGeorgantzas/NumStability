-- Algorithms/Cholesky/CholeskyNonsym.lean
--
-- §10.5: Nonsymmetric positive definite matrices.
--
-- A nonsymmetric matrix is positive definite if x^T A x > 0 for all x ≠ 0.
-- This is equivalent to the symmetric part A_S = (A + A^T)/2 being SPD.
--
-- LU factorization without pivoting succeeds for nonsymmetric PD matrices,
-- with pivots u_ii > 0. The growth bound involves κ₂(A_S):
--   ‖|L||U|‖_F ≤ √(n · κ₂(A_S)) · ‖A‖_F    (Golub-Van Loan, eq 10.29)
--
-- The factorization succeeds if 24n^{3/2} χ(A) u < 1 (Mathias).

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import NumStability.FloatingPoint.Model
import NumStability.Analysis.Rounding
import NumStability.Algorithms.LU.GaussianElimination
import NumStability.Algorithms.LU.GrowthFactor

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §10.5  Nonsymmetric positive definite
-- ============================================================

/-- **Nonsymmetric positive definite matrix**.

    A (not necessarily symmetric) matrix is positive definite if
    x^T A x > 0 for all nonzero x. This is equivalent to the
    symmetric part A_S = (A + A^T)/2 being SPD. -/
def IsNonsymPosDef (n : ℕ) (A : Fin n → Fin n → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, (∃ i, x i ≠ 0) →
    0 < ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j

/-- **Symmetric part** of a matrix: A_S = (A + A^T)/2. -/
noncomputable def symmetricPart (n : ℕ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (A i j + A j i) / 2

/-- **Skew-symmetric part** of a matrix: A_K = (A − A^T)/2. -/
noncomputable def skewSymmetricPart (n : ℕ) (A : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ :=
  fun i j => (A i j - A j i) / 2

/-- The symmetric part is symmetric. -/
lemma symmetricPart_symmetric (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, symmetricPart n A i j = symmetricPart n A j i := by
  intro i j; unfold symmetricPart; ring

/-- A = A_S + A_K decomposition. -/
lemma symmetric_skew_decomposition (n : ℕ) (A : Fin n → Fin n → ℝ) :
    ∀ i j : Fin n, A i j = symmetricPart n A i j + skewSymmetricPart n A i j := by
  intro i j; unfold symmetricPart skewSymmetricPart; ring

/-- x^T A_S x = x^T A x: the skew-symmetric part vanishes in quadratic forms.

    Proof: x^T A_S x = (1/2)(x^T A x + x^T A^T x) = (1/2)(S + S) = S
    since x^T A^T x = ∑ᵢⱼ xᵢ Aⱼᵢ xⱼ = ∑ⱼᵢ xⱼ Aᵢⱼ xᵢ = x^T A x
    by swapping summation indices. -/
lemma symPart_quadForm_eq (n : ℕ) (A : Fin n → Fin n → ℝ) (x : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n, x i * symmetricPart n A i j * x j =
    ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := by
  unfold symmetricPart
  -- Step 1: split (A i j + A j i)/2 into two halved terms
  have key : ∀ (i j : Fin n),
      x i * ((A i j + A j i) / 2) * x j =
      x i * A i j * x j / 2 + x i * A j i * x j / 2 := fun i j => by ring
  simp_rw [key, Finset.sum_add_distrib]
  -- Step 2: the transposed sum equals the original by index swap
  have swap_div : ∑ i : Fin n, ∑ j : Fin n, x i * A j i * x j / 2 =
      ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j / 2 := by
    conv_lhs => rw [Finset.sum_comm]
    congr 1; ext i; congr 1; ext j; ring
  -- Step 3: S/2 + S/2 = S
  rw [swap_div, ← Finset.sum_add_distrib]
  congr 1; ext i
  rw [← Finset.sum_add_distrib]
  congr 1; ext j; ring

/-- Nonsymmetric PD is equivalent to symmetric part being SPD. -/
lemma nonsymPosDef_iff_symPartSPD (n : ℕ) (A : Fin n → Fin n → ℝ) :
    IsNonsymPosDef n A ↔ IsSymPosDef n (symmetricPart n A) := by
  constructor
  · intro hPD
    constructor
    · exact symmetricPart_symmetric n A
    · intro x hx
      rw [symPart_quadForm_eq]; exact hPD x hx
  · intro hSPD x hx
    rw [← symPart_quadForm_eq]; exact hSPD.2 x hx

-- ============================================================
-- §10.4  Exact GE on matrices with positive definite symmetric part
-- ============================================================

/-- Diagonal entries of a nonsymmetric positive definite matrix are
    positive (Higham §10.4 prose; take `x = e_i`). -/
lemma nonsymPosDef_diag_pos {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : IsNonsymPosDef n A) (i : Fin n) : 0 < A i i := by
  have h := hA (fun k => if k = i then 1 else 0) ⟨i, by simp⟩
  have hs : ∑ k₁ : Fin n, ∑ k₂ : Fin n,
      (if k₁ = i then (1:ℝ) else 0) * A k₁ k₂ *
        (if k₂ = i then 1 else 0) = A i i := by
    rw [Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp),
        Finset.sum_eq_single i (by intro b _ hb; simp [hb]) (by simp)]
    simp
  rwa [hs] at h

/-- A nonsymmetric positive definite matrix has trivial kernel: `A x ≠ 0`
    for `x ≠ 0` (Higham §10.4 prose "nonsingular"; if `A x = 0` then the
    quadratic form vanishes at `x`). -/
lemma nonsymPosDef_mulVec_ne_zero {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : IsNonsymPosDef n A) (x : Fin n → ℝ) (hx : ∃ i, x i ≠ 0) :
    ∃ i : Fin n, (∑ j : Fin n, A i j * x j) ≠ 0 := by
  by_contra hall
  push_neg at hall
  have h := hA x hx
  have hz : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j = 0 := by
    have : ∀ i : Fin n, ∑ j : Fin n, x i * A i j * x j = 0 := by
      intro i
      have : ∑ j : Fin n, x i * A i j * x j =
          x i * ∑ j : Fin n, A i j * x j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hall i, mul_zero]
    exact Finset.sum_eq_zero fun i _ => this i
  linarith

/-- A full-range sum equals the truncated sum when the summand vanishes at
    and beyond index `k`. -/
private lemma sum_zero_off_lt {n k : ℕ} (hk : k ≤ n) (g : Fin n → ℝ)
    (hg : ∀ i : Fin n, k ≤ i.val → g i = 0) :
    ∑ i : Fin n, g i = ∑ i : Fin k, g ⟨i.val, by omega⟩ := by
  have himg : Finset.image (fun (t : Fin k) => (⟨t.val, by omega⟩ : Fin n))
      Finset.univ = Finset.filter (fun j : Fin n => j.val < k) Finset.univ := by
    ext j
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨t, rfl⟩; simp
    · intro hj
      exact ⟨⟨j.val, hj⟩, Fin.ext (by simp)⟩
  have hinj : ∀ a : Fin k, a ∈ Finset.univ →
      ∀ b : Fin k, b ∈ Finset.univ →
      (⟨a.val, by omega⟩ : Fin n) = ⟨b.val, by omega⟩ → a = b :=
    fun a _ b _ hab => Fin.ext (by simp only [Fin.mk.injEq] at hab; exact hab)
  rw [show ∑ i : Fin k, g ⟨i.val, by omega⟩ =
      ∑ j ∈ Finset.filter (fun j : Fin n => j.val < k) Finset.univ, g j from by
    rw [← himg, Finset.sum_image hinj]]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i _ hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.not_lt] at hi
  exact hg i hi

/-- **Zero-padding preserves the quadratic form**: the full-matrix
quadratic form of a zero-padded vector equals the leading-principal-block
quadratic form of the original vector.  Shared engine for the
leading-principal transfer lemmas and the interlacing lower bound. -/
lemma quadForm_zero_pad_eq {n : ℕ} (M : Fin n → Fin n → ℝ)
    (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then y ⟨i.val, h⟩ else 0) * M i j *
        (if h : j.val < k then y ⟨j.val, h⟩ else 0) =
    ∑ i : Fin k, ∑ j : Fin k,
      y i * M ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j := by
  have houter : ∑ i : Fin n, ∑ j : Fin n,
      (if h : i.val < k then y ⟨i.val, h⟩ else 0) * M i j *
        (if h : j.val < k then y ⟨j.val, h⟩ else 0) =
      ∑ i : Fin k, ∑ j : Fin n,
        y i * M ⟨i.val, by omega⟩ j *
          (if h : j.val < k then y ⟨j.val, h⟩ else 0) := by
    rw [sum_zero_off_lt hk _ (fun i hi => by
      apply Finset.sum_eq_zero
      intro j _
      rw [dif_neg (Nat.not_lt.mpr hi), zero_mul, zero_mul])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [dif_pos i.isLt]
  rw [houter]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_zero_off_lt hk _ (fun j hj => by
    rw [dif_neg (Nat.not_lt.mpr hj), mul_zero])]
  apply Finset.sum_congr rfl
  intro j _
  rw [dif_pos j.isLt]

/-- Zero-padding preserves the squared Euclidean norm. -/
lemma sum_sq_zero_pad_eq {n : ℕ} (k : ℕ) (hk : k ≤ n) (y : Fin k → ℝ) :
    ∑ i : Fin n, (if h : i.val < k then y ⟨i.val, h⟩ else 0) ^ 2 =
      ∑ i : Fin k, y i ^ 2 := by
  rw [sum_zero_off_lt hk _ (fun i hi => by
    rw [dif_neg (Nat.not_lt.mpr hi)]; ring)]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]

/-- Leading principal submatrices of a nonsymmetric positive definite matrix
    are nonsymmetric positive definite (Higham §10.4 prose; zero-pad the
    test vector). -/
lemma nonsymPosDef_leading_principal {n : ℕ} {A : Fin n → Fin n → ℝ}
    (hA : IsNonsymPosDef n A) (k : ℕ) (hk : k ≤ n) :
    IsNonsymPosDef k (fun i j => A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  intro y hy
  have hxval : ∀ i : Fin k,
      (fun i : Fin n => if h : i.val < k then y ⟨i.val, h⟩ else 0)
        ⟨i.val, by omega⟩ = y i := by
    intro i
    simp [i.isLt]
  set x : Fin n → ℝ := fun i => if h : i.val < k then y ⟨i.val, h⟩ else 0
    with hx_def
  have hx : ∃ i, x i ≠ 0 := by
    obtain ⟨i, hi⟩ := hy
    refine ⟨⟨i.val, by omega⟩, ?_⟩
    rw [hx_def]
    simpa [i.isLt] using hi
  have h := hA x hx
  have houter : ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j =
      ∑ i : Fin k, ∑ j : Fin n, y i * A ⟨i.val, by omega⟩ j * x j := by
    rw [sum_zero_off_lt hk _ (fun i hi => by
      apply Finset.sum_eq_zero
      intro j _
      rw [hx_def]
      simp [Nat.not_lt.mpr hi])]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hxval i]
  have hinner : ∀ i : Fin k,
      ∑ j : Fin n, y i * A ⟨i.val, by omega⟩ j * x j =
      ∑ j : Fin k, y i * A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j := by
    intro i
    rw [sum_zero_off_lt hk _ (fun j hj => by
      rw [hx_def]
      simp [Nat.not_lt.mpr hj])]
    apply Finset.sum_congr rfl
    intro j _
    rw [hxval j]
  calc (0:ℝ) < ∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j := h
    _ = ∑ i : Fin k, ∑ j : Fin k,
        y i * A ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ * y j := by
        rw [houter]
        exact Finset.sum_congr rfl fun i _ => hinner i

/-- **Schur-complement closure for nonsymmetric positive definiteness**
    (Higham §10.4 prose): one exact unpivoted GE step on a matrix with
    positive definite symmetric part yields a reduced matrix in the same
    class.  Proof by quadratic minimization: the full form evaluated at the
    pivot-coordinate minimizer bounds the reduced form from below, and the
    gap between the minimizer value and the Schur form is `(u−v)²/(4a₁₁)`. -/
lemma nonsym_pd_first_ge_schur {m : ℕ} {A : Fin (m + 1) → Fin (m + 1) → ℝ}
    (hA : IsNonsymPosDef (m + 1) A) :
    IsNonsymPosDef m
      (fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) := by
  intro y hy
  have hA00 : 0 < A 0 0 := nonsymPosDef_diag_pos hA 0
  set u : ℝ := ∑ j : Fin m, A 0 j.succ * y j with hu
  set v : ℝ := ∑ i : Fin m, y i * A i.succ 0 with hv
  set q : ℝ := ∑ i : Fin m, ∑ j : Fin m, y i * A i.succ j.succ * y j with hq
  set ξ : ℝ := -(u + v) / (2 * A 0 0) with hξ
  have hxs : ∃ i, (Fin.cases ξ y : Fin (m + 1) → ℝ) i ≠ 0 := by
    obtain ⟨i, hi⟩ := hy
    exact ⟨i.succ, by simpa using hi⟩
  have hQ := hA (Fin.cases ξ y) hxs
  have hexp : ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
      (Fin.cases ξ y : Fin (m + 1) → ℝ) i * A i j *
        (Fin.cases ξ y : Fin (m + 1) → ℝ) j =
      A 0 0 * ξ ^ 2 + ξ * u + v * ξ + q := by
    simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ]
    have h2 : ∑ j : Fin m, ξ * A 0 j.succ * y j = ξ * u := by
      rw [hu, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h3 : ∑ i : Fin m,
        (y i * A i.succ 0 * ξ + ∑ j : Fin m, y i * A i.succ j.succ * y j) =
        v * ξ + q := by
      rw [Finset.sum_add_distrib, hv, hq, Finset.sum_mul]
    rw [h2, h3]
    ring
  rw [hexp] at hQ
  have hmin : A 0 0 * ξ ^ 2 + ξ * u + v * ξ + q =
      q - (u + v) ^ 2 / (4 * A 0 0) := by
    rw [hξ]
    field_simp
    ring
  rw [hmin] at hQ
  have hSexp : ∑ i : Fin m, ∑ j : Fin m,
      y i * (A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) * y j =
      q - v * u / A 0 0 := by
    have hsplit : ∀ i : Fin m,
        ∑ j : Fin m,
          y i * (A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0) * y j =
        (∑ j : Fin m, y i * A i.succ j.succ * y j) -
          y i * A i.succ 0 * u / A 0 0 := by
      intro i
      have hrepr : y i * A i.succ 0 * u / A 0 0 =
          ∑ j : Fin m, y i * (A i.succ 0 * A 0 j.succ / A 0 0) * y j := by
        rw [hu, Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hrepr, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib,
      ← hq]
    congr 1
    rw [hv, Finset.sum_mul, Finset.sum_div]
  rw [hSexp]
  have hvu : v * u / A 0 0 ≤ (u + v) ^ 2 / (4 * A 0 0) := by
    rw [div_le_div_iff₀ hA00 (by linarith : (0:ℝ) < 4 * A 0 0)]
    nlinarith [sq_nonneg (u - v), hA00.le]
  linarith

/-- **Section 10.4 exact unpivoted-GE positive-pivot invariant**: at every
    stage of unpivoted Gaussian elimination the current pivot is positive. -/
def nonsymPDGEPivotsPos : (n : ℕ) → (Fin n → Fin n → ℝ) → Prop
  | 0, _A => True
  | 1, A => 0 < A 0 0
  | m + 2, A =>
      0 < A 0 0 ∧
        nonsymPDGEPivotsPos (m + 1)
          (fun i j => A i.succ j.succ - A i.succ 0 * A 0 j.succ / A 0 0)

/-- **Section 10.4 prose** (Higham p. 209, Golub–Van Loan route): unpivoted
    Gaussian elimination on a matrix with positive definite symmetric part
    succeeds with positive pivots at every stage.  Together with
    `nonsymPosDef_leading_principal` and `nonsymPosDef_mulVec_ne_zero`
    this closes the "nonsingular leading principal submatrices and positive
    pivots" claim in exact arithmetic. -/
theorem nonsym_pd_unpivoted_ge_positive_pivots :
    ∀ (n : ℕ) (A : Fin n → Fin n → ℝ),
      IsNonsymPosDef n A → nonsymPDGEPivotsPos n A := by
  intro n
  induction n with
  | zero =>
      intro A _
      trivial
  | succ n ih =>
      intro A hA
      cases n with
      | zero =>
          exact nonsymPosDef_diag_pos hA 0
      | succ m =>
          dsimp [nonsymPDGEPivotsPos]
          exact ⟨nonsymPosDef_diag_pos hA 0,
            ih _ (nonsym_pd_first_ge_schur hA)⟩

-- ============================================================
-- §10.5  Chi factor
-- ============================================================

/-- **Chi factor** χ(A) for nonsymmetric PD matrices.

    χ(A) = ‖A‖₂ · ‖A_S⁻¹‖₂ where A_S = (A + A^T)/2.
    This generalizes κ₂(A) for symmetric matrices (χ = κ₂ when A = A^T).

    χ(A) measures how far A is from being symmetric relative to
    the conditioning of the symmetric part. -/
noncomputable def chiFactor {n : ℕ} (_hn : 0 < n)
    (_A : Fin n → Fin n → ℝ) (norm2_A norm2_AS_inv : ℝ) : ℝ :=
  norm2_A * norm2_AS_inv

-- ============================================================
-- §10.5  Golub-Van Loan growth bound (10.29)
-- ============================================================

/-- **Abstract Golub-Van Loan LU growth-bound interface for nonsymmetric PD**
    (Higham §10.5, eq 10.29).

    For the exact LU factors of a nonsymmetric PD matrix A:
      ‖|L||U|‖_F ≤ √(n · κ₂(A_S)) · ‖A‖_F

    In squared form (to avoid sqrt):
      frobNormSq(|L||U|) ≤ n · κ₂(A_S) · frobNormSq(A)

    This shows LU without pivoting is safe provided that the symmetric
    part is not too ill-conditioned relative to the norm of the
    skew-symmetric part.  The Frobenius growth estimate is supplied as
    `hbound`. -/
theorem nonsym_pd_lu_growth_bound (n : ℕ) (_hn : 0 < n)
    (A L U : Fin n → Fin n → ℝ)
    (_hPD : IsNonsymPosDef n A)
    (_hLU : LUFactSpec n A L U)
    (κ_AS : ℝ) (_hκ : 0 ≤ κ_AS)
    -- The bound: ‖|L||U|‖²_F ≤ n · κ₂(A_S) · ‖A‖²_F
    (hbound : frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A) :
    frobNormSq (fun i j => ∑ k : Fin n, |L i k| * |U k j|) ≤
      ↑n * κ_AS * frobNormSq A :=
  hbound

-- ============================================================
-- §10.5  Mathias success condition
-- ============================================================

/-- **Abstract Mathias success-condition interface** (Higham §10.5).

    LU factorization (without pivoting) of a nonsymmetric PD matrix A
    succeeds if 24 · n^{3/2} · χ(A) · u < 1.

    Moreover, the computed LU factors satisfy:
      ‖|L̂||Û|‖_F ≤ (1 + 30un^{3/2}χ(A)) · √(n·κ₂(A_S)) · ‖A‖_F

    This theorem records the supplied success inequality as a named contract;
    it does not derive the full LU execution result. -/
theorem mathias_lu_success (_n : ℕ) (fp : FPModel)
    (chi : ℝ) (_hchi : 0 < chi)
    -- n_three_half represents n^{3/2} (avoiding Real.rpow)
    (n_three_half : ℝ) (_hn32 : 0 ≤ n_three_half)
    -- The success condition: 24 · n^{3/2} · χ(A) · u < 1
    (hsuccess : 24 * n_three_half * chi * fp.u < 1) :
    24 * n_three_half * chi * fp.u < 1 :=
  hsuccess

end NumStability
