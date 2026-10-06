-- Algorithms/StationaryIterationSemiconvergent.lean
--
-- Higham Chapter 17 "Stationary Iterative Methods", §17.4 "Singular Systems":
-- the semiconvergent block form of eq (17.22) taken as data, its eigenvalue-1
-- projector, the discharge of the fixed-null hypothesis of the finite (17.27)
-- split in `StationaryIteration.lean`, and the semiconvergence limit
-- `G^m → X diag(I, 0) X⁻¹` behind eqs (17.22)/(17.25).
--
-- Eq (17.22) says a semiconvergent iteration matrix has the form
-- `G = X · diag(I, Γ) · X⁻¹` with `ρ(Γ) < 1`.  Throughout this file that
-- block form is HYPOTHESIS data, exactly as in the printed development: a
-- split index `r`, a matrix `J` whose top `r` rows are identity rows
-- (`hJtop`), whose bottom-left block vanishes (`hJcross`), and — where the
-- contraction matters — a row-sum certificate `q < 1` for the bottom rows
-- (an ∞-norm strengthening of the printed spectral condition `ρ(Γ) < 1`).
-- The existence of that form for an arbitrary semiconvergent matrix —
-- Jordan-form background — is not formalized.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import NumStability.Analysis.MatrixAlgebra
import NumStability.Algorithms.MatrixPowers
import NumStability.Algorithms.StationaryIteration

namespace NumStability

open scoped BigOperators

-- ============================================================
-- §17.4  A. The top-block projector diag(I_r, 0)
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22): the coordinate projector `diag(I_r, 0)` onto the top block of
    the semiconvergent form `G = X · diag(I, Γ) · X⁻¹`.  Indices `i` with
    `(i : ℕ) < r` form the eigenvalue-1 block; the rest form the `Γ` block. -/
noncomputable def topProjector (n r : ℕ) : Fin n → Fin n → ℝ :=
  fun i j => if i = j ∧ (i : ℕ) < r then 1 else 0

/-- Top rows of `topProjector` are identity rows. -/
theorem topProjector_apply_top {n r : ℕ} {k : Fin n} (hk : (k : ℕ) < r)
    (l : Fin n) : topProjector n r k l = if k = l then 1 else 0 := by
  unfold topProjector
  by_cases h : k = l
  · rw [if_pos ⟨h, hk⟩, if_pos h]
  · rw [if_neg (fun hc => h hc.1), if_neg h]

/-- Bottom rows of `topProjector` vanish. -/
theorem topProjector_apply_bottom {n r : ℕ} {k : Fin n} (hk : ¬(k : ℕ) < r)
    (l : Fin n) : topProjector n r k l = 0 := by
  unfold topProjector
  exact if_neg (fun hc => hk hc.2)

/-- A matrix whose `k`-th row is an identity row reproduces the `k`-th row of
    any right factor.  Row-level workhorse for the block-form algebra of
    Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22). -/
theorem matMul_row_id (n : ℕ) (B C : Fin n → Fin n → ℝ) (k j : Fin n)
    (hB : ∀ l : Fin n, B k l = if k = l then 1 else 0) :
    matMul n B C k j = C k j := by
  calc matMul n B C k j = ∑ l : Fin n, B k l * C l j := rfl
    _ = ∑ l : Fin n, (if k = l then 1 else 0) * C l j :=
        Finset.sum_congr rfl fun l _ => by rw [hB l]
    _ = C k j := by simp

/-- A matrix whose `k`-th row vanishes kills the `k`-th row of any product.
    Row-level workhorse for the block-form algebra of Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.4, eq (17.22). -/
theorem matMul_row_zero (n : ℕ) (B C : Fin n → Fin n → ℝ) (k j : Fin n)
    (hB : ∀ l : Fin n, B k l = 0) :
    matMul n B C k j = 0 := by
  calc matMul n B C k j = ∑ l : Fin n, B k l * C l j := rfl
    _ = ∑ l : Fin n, (0 : ℝ) * C l j :=
        Finset.sum_congr rfl fun l _ => by rw [hB l]
    _ = 0 := by simp

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22): `diag(I, Γ) · diag(I_r, 0) = diag(I_r, 0)`.  The top-block
    identity of the semiconvergent form absorbs the projector and the `Γ`
    block is killed.  The block form is taken as data via `hJtop`/`hJcross`;
    no Jordan-form existence argument is used. -/
theorem J_mul_topProjector (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0) :
    matMul n J (topProjector n r) = topProjector n r := by
  ext i j
  have hsum : (∑ k : Fin n, J i k * topProjector n r k j) =
      J i j * topProjector n r j j :=
    Finset.sum_eq_single j
      (fun k _ hk => by
        have hzero : topProjector n r k j = 0 := by
          unfold topProjector
          exact if_neg (fun hc => hk hc.1)
        rw [hzero, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)
  calc matMul n J (topProjector n r) i j
      = ∑ k : Fin n, J i k * topProjector n r k j := rfl
    _ = J i j * topProjector n r j j := hsum
    _ = topProjector n r i j := by
        by_cases hj : (j : ℕ) < r
        · have hTjj : topProjector n r j j = 1 := by
            unfold topProjector
            exact if_pos ⟨rfl, hj⟩
          rw [hTjj, mul_one]
          by_cases hi : (i : ℕ) < r
          · rw [hJtop i j hi, topProjector_apply_top hi j]
          · rw [hJcross i j hi hj, topProjector_apply_bottom hi j]
        · have hTjj : topProjector n r j j = 0 := by
            unfold topProjector
            exact if_neg (fun hc => hj hc.2)
          have hTij : topProjector n r i j = 0 := by
            unfold topProjector
            exact if_neg
              (fun hc : i = j ∧ (i : ℕ) < r => hj (hc.1 ▸ hc.2))
          rw [hTjj, mul_zero, hTij]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22): `diag(I_r, 0) · diag(I, Γ) = diag(I_r, 0)`.  Only the
    top-row-identity hypothesis is needed: the top-right block of the
    semiconvergent form is already zero because its top rows are identity
    rows. -/
theorem topProjector_mul_J (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0) :
    matMul n (topProjector n r) J = topProjector n r := by
  ext i j
  by_cases hi : (i : ℕ) < r
  · rw [matMul_row_id n (topProjector n r) J i j (topProjector_apply_top hi),
      hJtop i j hi, topProjector_apply_top hi j]
  · rw [matMul_row_zero n (topProjector n r) J i j
      (topProjector_apply_bottom hi), topProjector_apply_bottom hi j]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.22): the top-block projector `diag(I_r, 0)` is idempotent. -/
theorem topProjector_idempotent (n r : ℕ) :
    matMul n (topProjector n r) (topProjector n r) = topProjector n r :=
  topProjector_mul_J n r (topProjector n r)
    (fun _i j hi => topProjector_apply_top hi j)

-- ============================================================
-- §17.4  B. Conjugation algebra for the similarity data
-- ============================================================

/-- Reconstruction of a matrix from its similarity data: if
    `X⁻¹ G X = J` and `X X⁻¹ = I`, then `G = X J X⁻¹`.  Mirrors the
    reconstruction step inside `matPow_similarity` (Higham, Accuracy and
    Stability of Numerical Algorithms, 2nd ed., §17.4, eq (17.22)
    similarity data). -/
theorem eq_conjugate_of_similarity (n : ℕ)
    (G X X_inv J : Fin n → Fin n → ℝ)
    (hXr : IsRightInverse n X X_inv)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    G = matMul n X (matMul n J X_inv) := by
  have hXXinv : matMul n X X_inv = idMatrix n := by ext a b; exact hXr a b
  calc G = matMul n (matMul n X X_inv) (matMul n G (matMul n X X_inv)) := by
        rw [hXXinv, matMul_id_left, matMul_id_right]
    _ = matMul n X (matMul n (matMul n X_inv (matMul n G X)) X_inv) := by
        simp only [matMul_assoc]
    _ = matMul n X (matMul n J X_inv) := by rw [hsim]

/-- Conjugated matrices multiply through the similarity:
    `(X A X⁻¹)(X B X⁻¹) = X (A B) X⁻¹` given `X⁻¹ X = I`.  Conjugation
    workhorse for the projector algebra of Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §17.4, eqs (17.22)–(17.25). -/
theorem conjugate_matMul (n : ℕ) (X X_inv A B : Fin n → Fin n → ℝ)
    (hXl : IsRightInverse n X_inv X) :
    matMul n (matMul n X (matMul n A X_inv))
        (matMul n X (matMul n B X_inv)) =
      matMul n X (matMul n (matMul n A B) X_inv) := by
  have hXinvX : matMul n X_inv X = idMatrix n := by ext a b; exact hXl a b
  calc matMul n (matMul n X (matMul n A X_inv))
        (matMul n X (matMul n B X_inv))
      = matMul n X (matMul n (matMul n A X_inv)
          (matMul n X (matMul n B X_inv))) :=
        matMul_assoc n X (matMul n A X_inv) (matMul n X (matMul n B X_inv))
    _ = matMul n X (matMul n A
          (matMul n X_inv (matMul n X (matMul n B X_inv)))) := by
        rw [matMul_assoc n A X_inv (matMul n X (matMul n B X_inv))]
    _ = matMul n X (matMul n A
          (matMul n (matMul n X_inv X) (matMul n B X_inv))) := by
        rw [← matMul_assoc n X_inv X (matMul n B X_inv)]
    _ = matMul n X (matMul n A (matMul n B X_inv)) := by
        rw [hXinvX, matMul_id_left]
    _ = matMul n X (matMul n (matMul n A B) X_inv) := by
        rw [← matMul_assoc n A B X_inv]

-- ============================================================
-- §17.4  C. The eigenvalue-1 projector I − E = X diag(I_r, 0) X⁻¹
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.25): the projector `X · diag(I_r, 0) · X⁻¹` onto the
    eigenvalue-1 subspace of the semiconvergent form, i.e. the book's
    `I − E`.  The semiconvergent block form is taken as data, as in the
    printed (17.22); the existence of that form for an arbitrary
    semiconvergent matrix — Jordan-form background — is not formalized. -/
noncomputable def oneEigenProjector (n r : ℕ)
    (X X_inv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  matMul n X (matMul n (topProjector n r) X_inv)

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eq (17.25) surroundings: the eigenvalue-1 projector `I − E` is
    idempotent, `(I − E)² = I − E`. -/
theorem oneEigenProjector_idempotent (n r : ℕ)
    (X X_inv : Fin n → Fin n → ℝ)
    (hXl : IsRightInverse n X_inv X) :
    matMul n (oneEigenProjector n r X X_inv)
        (oneEigenProjector n r X X_inv) =
      oneEigenProjector n r X X_inv := by
  unfold oneEigenProjector
  rw [conjugate_matMul n X X_inv (topProjector n r) (topProjector n r) hXl,
    topProjector_idempotent]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.25): `G (I − E) = I − E` — the eigenvalue-1 projector of
    the semiconvergent form is fixed by the iteration matrix.  Stated for a
    general matrix `G` carrying the (17.22) block-form data; callers
    instantiate `G := iterMatrix n M_inv N`. -/
theorem G_mul_oneEigenProjector_eq (n r : ℕ)
    (G J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    matMul n G (oneEigenProjector n r X X_inv) =
      oneEigenProjector n r X X_inv := by
  have hG := eq_conjugate_of_similarity n G X X_inv J hXr hsim
  unfold oneEigenProjector
  rw [hG, conjugate_matMul n X X_inv J (topProjector n r) hXl,
    J_mul_topProjector n r J hJtop hJcross]

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.27): vector form of `G (I − E) = I − E` — every vector in
    the range of the eigenvalue-1 projector is fixed by `G`.  This is
    precisely the shape of the `hNull` hypothesis of
    `singular_error_split_finite`. -/
theorem G_fixes_oneEigenProjector_apply (n r : ℕ)
    (G J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    ∀ (v : Fin n → ℝ) (i : Fin n),
      matMulVec n G (matMulVec n (oneEigenProjector n r X X_inv) v) i =
        matMulVec n (oneEigenProjector n r X X_inv) v i := by
  intro v i
  calc matMulVec n G (matMulVec n (oneEigenProjector n r X X_inv) v) i
      = matMulVec n (matMul n G (oneEigenProjector n r X X_inv)) v i :=
        (matMulVec_matMul n G (oneEigenProjector n r X X_inv) v i).symm
    _ = matMulVec n (oneEigenProjector n r X X_inv) v i := by
        rw [G_mul_oneEigenProjector_eq n r G J X X_inv hJtop hJcross
          hXr hXl hsim]

-- ============================================================
-- §17.4  D. The accumulating projector E and the matSub_id bridge
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.25)–(17.27): the accumulating projector
    `E = I − X · diag(I_r, 0) · X⁻¹` of the singular-system error split,
    built from the semiconvergent block form of (17.22) taken as data. -/
noncomputable def semiconvergentE (n r : ℕ)
    (X X_inv : Fin n → Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => idMatrix n i j - oneEigenProjector n r X X_inv i j

/-- The complement `I − E` of the accumulating projector `semiconvergentE`
    is exactly the eigenvalue-1 projector, in the `matSub_id` phrasing used
    by `singular_error_split_finite` (Higham, Accuracy and Stability of
    Numerical Algorithms, 2nd ed., §17.4, eqs (17.25)–(17.27)). -/
theorem matSub_id_semiconvergentE (n r : ℕ)
    (X X_inv : Fin n → Fin n → ℝ) :
    matSub_id n (semiconvergentE n r X X_inv) =
      oneEigenProjector n r X X_inv := by
  ext i j
  unfold matSub_id semiconvergentE
  ring

-- ============================================================
-- §17.4  E. The (17.27) split with the semiconvergent projector
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.27): the finite three-term error split (17.27) for a
    consistent singular system, with the projector built from the
    semiconvergent block form of (17.22).  This closes the ledger's "proof
    that the source projector `E` supplies the fixed-null hypothesis" row at
    the printed (17.22) data level: the abstract projector `E` and the
    `hNull` hypothesis of `singular_error_split_finite` are replaced by
    block-form data `(r, J, X, X⁻¹)` for the iteration matrix
    `G = M⁻¹N`, and the fixed-subspace property is PROVED from that data
    (for all vectors, not just the specific `M⁻¹ξ_t`).

    Honest scope notes: the semiconvergent block form is taken as data, as
    in the printed (17.22); the existence of that form for an arbitrary
    semiconvergent matrix — Jordan-form background — is not formalized.
    The contraction certificate `q < 1` for the `Γ` rows (an ∞-norm
    row-sum strengthening of the printed spectral condition `ρ(Γ) < 1`) is
    carried so that the hypothesis package is the full printed
    semiconvergent form, but the finite split itself needs only the block
    structure; the certificate becomes load-bearing in the companion limit
    theorem `matPow_G_tendsto_oneEigenProjector`. -/
theorem singular_error_split_semiconvergent (n : ℕ)
    (A M N M_inv : Fin n → Fin n → ℝ)
    (hS : SplittingSpec n A M N M_inv)
    (b x : Fin n → ℝ) (hAx : ∀ i, ∑ j : Fin n, A i j * x j = b i)
    (x_hat : ℕ → (Fin n → ℝ)) (ξ : ℕ → (Fin n → ℝ))
    (hIter : SourceComputedIteration n M N b x_hat ξ)
    (r : ℕ) (J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (_hq0 : 0 ≤ q) (_hq1 : q < 1)
    (_hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n (iterMatrix n M_inv N) X) = J)
    (m : ℕ) :
    ∀ i, x i - x_hat (m + 1) i =
      matMulVec n (matPow n (iterMatrix n M_inv N) (m + 1))
        (fun j => x j - x_hat 0 j) i +
      singularErrorSourceTerm n (iterMatrix n M_inv N)
        (semiconvergentE n r X X_inv) M_inv ξ m i +
      matMulVec n (oneEigenProjector n r X X_inv)
        (matMulVec n M_inv
          (fun j => ∑ k ∈ Finset.range (m + 1), ξ (m - k) j)) i := by
  have hNull : ∀ t i,
      matMulVec n (iterMatrix n M_inv N)
        (matMulVec n (matSub_id n (semiconvergentE n r X X_inv))
          (matMulVec n M_inv (ξ t))) i =
      matMulVec n (matSub_id n (semiconvergentE n r X X_inv))
        (matMulVec n M_inv (ξ t)) i := by
    intro t i
    rw [matSub_id_semiconvergentE n r X X_inv]
    exact G_fixes_oneEigenProjector_apply n r (iterMatrix n M_inv N) J
      X X_inv hJtop hJcross hXr hXl hsim (matMulVec n M_inv (ξ t)) i
  intro i
  have h := singular_error_split_finite n A M N M_inv
    (semiconvergentE n r X X_inv) hS b x hAx x_hat ξ hIter hNull m i
  rw [matSub_id_semiconvergentE n r X X_inv] at h
  exact h

-- ============================================================
-- §17.4  F. Semiconvergence: G^m → X diag(I_r, 0) X⁻¹
-- ============================================================

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.25): the top rows of every power of the block form
    `diag(I, Γ)` are identity rows.  Only the top-row-identity data of the
    printed (17.22) is used. -/
theorem matPow_J_top_entry (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (m : ℕ) :
    ∀ i j : Fin n, (i : ℕ) < r →
      matPow n J m i j = if i = j then 1 else 0 := by
  induction m with
  | zero =>
      intro i j _hi
      rw [matPow_zero]
      rfl
  | succ m ih =>
      intro i j hi
      rw [matPow_succ]
      calc matMul n J (matPow n J m) i j
          = ∑ k : Fin n, J i k * matPow n J m k j := rfl
        _ = ∑ k : Fin n, (if i = k then 1 else 0) * matPow n J m k j :=
            Finset.sum_congr rfl fun k _ => by rw [hJtop i k hi]
        _ = matPow n J m i j := by simp
        _ = if i = j then 1 else 0 := ih i j hi

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.25): the bottom (`Γ`-block) rows of `diag(I, Γ)^m` have
    absolute row sums at most `q^m` under the row-sum contraction
    certificate `‖Γ‖∞ ≤ q` (`hGamma`, an ∞-norm strengthening of the printed
    spectral condition `ρ(Γ) < 1` of (17.22)).  The vanishing bottom-left
    block (`hJcross`) ensures bottom rows of the power only recombine bottom
    rows. -/
theorem matPow_J_bottom_row_sum (n r : ℕ) (J : Fin n → Fin n → ℝ)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (m : ℕ) :
    ∀ i : Fin n, ¬(i : ℕ) < r →
      ∑ j : Fin n, |matPow n J m i j| ≤ q ^ m := by
  induction m with
  | zero =>
      intro i _hi
      rw [matPow_zero, pow_zero]
      have hone : ∑ j : Fin n, |idMatrix n i j| = 1 := by
        calc ∑ j : Fin n, |idMatrix n i j|
            = ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) :=
              Finset.sum_congr rfl fun j _ => by
                by_cases h : i = j <;> simp [idMatrix, h]
          _ = 1 := by simp
      exact hone.le
  | succ m ih =>
      intro i hi
      rw [matPow_succ]
      calc ∑ j : Fin n, |matMul n J (matPow n J m) i j|
          = ∑ j : Fin n, |∑ k : Fin n, J i k * matPow n J m k j| := rfl
        _ ≤ ∑ j : Fin n, ∑ k : Fin n, |J i k * matPow n J m k j| :=
            Finset.sum_le_sum fun j _ => Finset.abs_sum_le_sum_abs _ _
        _ = ∑ j : Fin n, ∑ k : Fin n, |J i k| * |matPow n J m k j| :=
            Finset.sum_congr rfl fun j _ =>
              Finset.sum_congr rfl fun k _ => abs_mul _ _
        _ = ∑ k : Fin n, ∑ j : Fin n, |J i k| * |matPow n J m k j| :=
            Finset.sum_comm
        _ = ∑ k : Fin n, |J i k| * ∑ j : Fin n, |matPow n J m k j| :=
            Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
        _ ≤ ∑ k : Fin n, |J i k| * q ^ m := by
            refine Finset.sum_le_sum fun k _ => ?_
            by_cases hk : (k : ℕ) < r
            · rw [hJcross i k hi hk]
              simp
            · exact mul_le_mul_of_nonneg_left (ih k hk) (abs_nonneg _)
        _ = (∑ k : Fin n, |J i k|) * q ^ m := (Finset.sum_mul _ _ _).symm
        _ ≤ q * q ^ m :=
            mul_le_mul_of_nonneg_right (hGamma i hi) (pow_nonneg hq0 m)
        _ = q ^ (m + 1) := by ring

/-- Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed., §17.4,
    eqs (17.22)–(17.25): the literal semiconvergence statement — for an
    iteration matrix carrying the block-form data of the printed (17.22)
    (`G = X · diag(I, Γ) · X⁻¹` with a row-sum contraction certificate
    `‖Γ‖∞ ≤ q < 1`), the powers `G^m` converge entrywise to the
    eigenvalue-1 projector `X · diag(I_r, 0) · X⁻¹ = I − E`.

    Honest scope notes: the semiconvergent block form is taken as data, as
    in the printed (17.22); the existence of that form for an arbitrary
    semiconvergent matrix — Jordan-form background — is not formalized, and
    the contraction certificate is the ∞-norm row-sum strengthening of the
    printed spectral condition `ρ(Γ) < 1`.  Convergence is entrywise
    (equivalently, in any norm on a finite-dimensional space). -/
theorem matPow_G_tendsto_oneEigenProjector (n r : ℕ)
    (G J X X_inv : Fin n → Fin n → ℝ)
    (hJtop : ∀ i j : Fin n, (i : ℕ) < r → J i j = if i = j then 1 else 0)
    (hJcross : ∀ i j : Fin n, ¬(i : ℕ) < r → (j : ℕ) < r → J i j = 0)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hGamma : ∀ i : Fin n, ¬(i : ℕ) < r → ∑ j : Fin n, |J i j| ≤ q)
    (hXr : IsRightInverse n X X_inv) (hXl : IsRightInverse n X_inv X)
    (hsim : matMul n X_inv (matMul n G X) = J) :
    ∀ i j : Fin n,
      Filter.Tendsto (fun m => matPow n G m i j) Filter.atTop
        (nhds (oneEigenProjector n r X X_inv i j)) := by
  intro i j
  -- entrywise expansion of G^m through the similarity
  have hGm : ∀ m, matPow n G m i j =
      ∑ k : Fin n, X i k * matMul n (matPow n J m) X_inv k j := by
    intro m
    rw [matPow_similarity n G X X_inv J hXr hXl hsim m]
    rfl
  have hP : oneEigenProjector n r X X_inv i j =
      ∑ k : Fin n, X i k * matMul n (topProjector n r) X_inv k j := rfl
  -- per-summand limits
  have hterm : ∀ k : Fin n,
      Filter.Tendsto
        (fun m => X i k * matMul n (matPow n J m) X_inv k j)
        Filter.atTop
        (nhds (X i k * matMul n (topProjector n r) X_inv k j)) := by
    intro k
    by_cases hk : (k : ℕ) < r
    · -- top summand: constant in m
      have hconst : ∀ m, matMul n (matPow n J m) X_inv k j = X_inv k j :=
        fun m => matMul_row_id n (matPow n J m) X_inv k j
          (fun l => matPow_J_top_entry n r J hJtop m k l hk)
      have hTP : matMul n (topProjector n r) X_inv k j = X_inv k j :=
        matMul_row_id n (topProjector n r) X_inv k j
          (topProjector_apply_top hk)
      have hfun : (fun m => X i k * matMul n (matPow n J m) X_inv k j) =
          fun _ : ℕ => X i k * X_inv k j :=
        funext fun m => by rw [hconst m]
      rw [hfun, hTP]
      exact tendsto_const_nhds
    · -- bottom summand: squeezed to zero by the contraction certificate
      have hTP : matMul n (topProjector n r) X_inv k j = 0 :=
        matMul_row_zero n (topProjector n r) X_inv k j
          (topProjector_apply_bottom hk)
      rw [hTP, mul_zero]
      have hC0 : 0 ≤ ∑ l : Fin n, |X_inv l j| :=
        Finset.sum_nonneg fun l _ => abs_nonneg _
      have hbound : ∀ m,
          |X i k * matMul n (matPow n J m) X_inv k j| ≤
            |X i k| * (q ^ m * ∑ l : Fin n, |X_inv l j|) := by
        intro m
        rw [abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |matMul n (matPow n J m) X_inv k j|
            = |∑ l : Fin n, matPow n J m k l * X_inv l j| := rfl
          _ ≤ ∑ l : Fin n, |matPow n J m k l * X_inv l j| :=
              Finset.abs_sum_le_sum_abs _ _
          _ = ∑ l : Fin n, |matPow n J m k l| * |X_inv l j| :=
              Finset.sum_congr rfl fun l _ => abs_mul _ _
          _ ≤ ∑ l : Fin n,
                |matPow n J m k l| * ∑ l' : Fin n, |X_inv l' j| := by
              refine Finset.sum_le_sum fun l _ => ?_
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
              exact Finset.single_le_sum
                (fun l' _ => abs_nonneg (X_inv l' j)) (Finset.mem_univ l)
          _ = (∑ l : Fin n, |matPow n J m k l|) *
                ∑ l' : Fin n, |X_inv l' j| := (Finset.sum_mul _ _ _).symm
          _ ≤ q ^ m * ∑ l : Fin n, |X_inv l j| :=
              mul_le_mul_of_nonneg_right
                (matPow_J_bottom_row_sum n r J hJcross q hq0 hGamma m k hk)
                hC0
      have hgeo : Filter.Tendsto
          (fun m : ℕ => |X i k| * (q ^ m * ∑ l : Fin n, |X_inv l j|))
          Filter.atTop (nhds 0) := by
        have hq : Filter.Tendsto (fun m : ℕ => q ^ m)
            Filter.atTop (nhds 0) :=
          tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
        simpa using
          ((hq.mul_const (∑ l : Fin n, |X_inv l j|)).const_mul (|X i k|))
      exact squeeze_zero_norm
        (fun m => by simpa [Real.norm_eq_abs] using hbound m) hgeo
  -- assemble the finite sum of limits
  have hsum : Filter.Tendsto
      (fun m => ∑ k : Fin n, X i k * matMul n (matPow n J m) X_inv k j)
      Filter.atTop
      (nhds (∑ k : Fin n,
        X i k * matMul n (topProjector n r) X_inv k j)) :=
    tendsto_finset_sum _ (fun k _ => hterm k)
  have hfun : (fun m => matPow n G m i j) =
      fun m => ∑ k : Fin n, X i k * matMul n (matPow n J m) X_inv k j :=
    funext hGm
  rw [hfun, hP]
  exact hsum

end NumStability
